import QML.QML_v12m_SemShift
import QML.QML_v12m_SubstTwice

/-!
# QML v12m — semantics of substitution (terms)

A substitution `θ` over `Δ` and an environment over `Δ` give an environment over the source `Γ`
(`substEnv`): each address gets the value of its entry — an address its value, a term its value.
Then ⭐`interp_subst`: substituting and then evaluating is evaluating in the substituted
environment.

`Subst.Ok` only speaks about addresses whose last step is not a projection, so the source context
is required to have no such visible address (`Ctx.NoProjLast`); every context built from roots and
modal views qualifies.

The modal cases use the β laws and extensionality: the substituted environment pushed into a `□`
or `◇` view is the substituted environment of the view (`substEnv_box`, `substEnv_dia`).
-/

namespace V12M

variable [ModalSys]

/-- No visible address ends in a projection. -/
def Ctx.NoProjLast (Γ : Ctx) : Prop := ∀ v T, Γ v = some T → v.lastProj = false

theorem Ctx.noProjLast_boxIn (Γ : Ctx) : Γ.boxIn.NoProjLast := by
  intro v T hv
  match v with
  | .step _ .box => rfl
  | .step _ .keep => rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

theorem Ctx.noProjLast_diaIn (Γ : Ctx) (x : VarSymb) : (Γ.diaIn x).NoProjLast := by
  intro v T hv
  match v with
  | .step _ .dia => rfl
  | .step _ .box => rfl
  | .step _ .keep => rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-! ## Entry values and the substituted environment -/

/-- The value of a substitution entry. -/
def entryVal {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    (e : SubE σ Δ) → {T : VarType} → e.OkRef T → M.frame.Dom T w
  | .ren v, _, h => env.ref v h
  | .tm s, _, h => h ▸ interp env s
  | .hide, _, h => False.elim h

/-- The environment a substitution induces on its source. -/
def substEnv {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) : M.Env Γ w :=
  fun v T hv => entryVal env (θ v) (hθ v T (hnp v T hv) hv)

theorem entryVal_congr {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {e e' : SubE σ Δ}
    {T : VarType} (he : e = e') (h : e.OkRef T) (h' : e'.OkRef T) :
    entryVal env e h = entryVal env e' h' := by
  subst he
  rfl

theorem entryVal_proj {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {e : SubE σ Δ} {U T : VarType} {s : Step} (he : e.OkRef U) (hs : s.isProj = true)
      (hst : U.step s = some T),
      entryVal env (e.proj s) (SubE.okRef_proj he hs hst) = M.stepObj hs hst (entryVal env e he)
  | .ren v, U, T, s, he, hs, hst => by
      change env.ref (.step v s) (SubE.okRef_proj he hs hst) = M.stepObj hs hst (env.ref v he)
      rw [Env.ref, dif_pos hs]
      split
      · rename_i U' hU'
        have hUU : U' = U := Option.some.inj (hU'.symm.trans he)
        subst hUU
        rfl
      · rename_i hU'
        exfalso
        rw [he] at hU'
        cases hU'
  | .hide, _, _, _, he, _, _ => False.elim he
  | .tm (T := U') s₀, U, T, s, he, hs, hst => by
      have hU : U' = U := he
      subst hU
      cases s with
      | fst =>
          cases s₀ <;> (try cases hst)
          rfl
      | snd =>
          cases s₀ <;> (try cases hst)
          rfl
      | box => cases hs
      | dia => cases hs
      | keep => cases hs
      | here =>
          cases s₀ with
          | boxtm t =>
              obtain ⟨hT, hAT⟩ := VarType.step_here hst
              subst hAT
              rw [entryVal_congr env (SubE.proj_boxtm_here t hT) _ rfl]
              change interp env (Term.collapse _ t) =
                M.necEval (interp env (Term.boxtm t)) ⟨w, ⟨M.frame.refl hT w⟩⟩
              rw [interp_collapse (Env.collapseAgree_self hT env), box_beta]
          | _ => cases hst

/-- The substituted environment's value at any reachable address is that address's entry. -/
theorem substEnv_ref {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) :
    ∀ (v : VarSymb) {T : VarType} (hv : Γ.ref v = some T),
      (substEnv θ hθ hnp env).ref v hv = entryVal env (θ.at v) (Subst.okRef_at hθ hv)
  | .root _, _, _ => rfl
  | .step v s, T, hv => by
      by_cases hs : s.isProj = true
      · rw [Env.ref, dif_pos hs]
        split
        · rename_i U hU
          rw [substEnv_ref θ hθ hnp env v hU]
          have hat : θ.at (.step v s) = (θ.at v).proj s := by
            change (if s.isProj then _ else _) = _
            rw [if_pos hs]
          have hst : U.step s = some T := by
            rw [Ctx.ref_step_proj Γ v hs, hU] at hv
            exact hv
          rw [entryVal_congr env hat _ (SubE.okRef_proj (Subst.okRef_at hθ hU) hs hst),
            entryVal_proj]
        · rename_i hU
          exfalso
          rw [Ctx.ref_step_proj Γ v hs, hU] at hv
          cases hv
      · rw [Env.ref, dif_neg hs]
        exact entryVal_congr env (Subst.at_nonproj θ (v := .step v s)
          (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs)).symm _ _

theorem interp_toVar {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ (e : SubE σ Δ) (h : e.OkRef .Var), interp env (e.toVar h) = entryVal env e h
  | .ren _, _ => rfl
  | .tm (.var _ _), _ => rfl
  | .tm (.func _), _ => rfl
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _), h => nomatch h
  | .tm (.diatm _ _ _), h => nomatch h
  | .hide, h => False.elim h

theorem entryVal_mono {Δ Δ' : Ctx} {h : Δ.Le Δ'} {w : M.frame.W} {env : M.Env Δ w}
    {env' : M.Env Δ' w} (hag : Env.Agree h env env') :
    ∀ (e : SubE σ Δ) {T : VarType} (he : e.OkRef T),
      entryVal env' (e.mono h) (SubE.okRef_mono h he) = entryVal env e he
  | .ren v, _, he => (Env.ref_agree hag v he).symm
  | .tm s, _, he => by
      cases he
      exact interp_mono hag s
  | .hide, _, he => False.elim he

/-! ## The `□` view -/

theorem entryVal_unbox {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (w' : M.frame.Acc w) :
    ∀ {e : SubE σ Δ} {A : VarType} (he : e.OkRef (.VTypeBox A)),
      entryVal (env.boxPush w') e.unbox (SubE.okRef_unbox he) = M.necEval (entryVal env e he) w'
  | .ren _, _, he => Env.ref_inner env w' he _
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t => exact (box_beta env t w').symm
  | .hide, _, he => False.elim he

theorem entryVal_keepE {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (w' : M.frame.Acc w)
    (hF : ModalSys.Four = true) :
    ∀ {e : SubE σ Δ} {A : VarType} (he : e.OkRef (.VTypeBox A)),
      entryVal (env.boxPush w') e.keepE (SubE.okRef_keepE hF he) =
        M.necEval (M.ops.necDup hF (entryVal env e he)) w'
  | .ren _, _, _ => rfl
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          rw [entryVal_congr _ (SubE.keepE_tm t hF) _ rfl]
          apply M.nec_inj
          funext s
          change M.necEval (interp (env.boxPush w')
              (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Δ) t))) s =
            M.necEval (M.necEval (M.ops.necDup hF (interp env (Term.boxtm t))) w') s
          rw [box_beta, M.necDup_eval, box_beta]
          exact interp_shift (Env.shiftAgree_twoBox hF env w' s) t
  | .hide, _, he => False.elim he

theorem substEnv_box {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) (w' : M.frame.Acc w) :
    substEnv θ.box (Subst.ok_box hθ) (Ctx.noProjLast_boxIn Γ) (env.boxPush w') =
      (substEnv θ hθ hnp env).boxPush w' := by
  funext v T hv
  match v with
  | .step u .box =>
      change entryVal (env.boxPush w') ((θ.at u).unbox) _ =
        M.necEval ((substEnv θ hθ hnp env).ref u (Ctx.boxIn_step_box hv)) w'
      rw [substEnv_ref, entryVal_unbox env w' (Subst.okRef_at hθ (Ctx.boxIn_step_box hv))]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      change entryVal (env.boxPush w') ((θ.at u).keepE) _ =
        M.necEval (M.ops.necDup hF ((substEnv θ hθ hnp env).ref u hu)) w'
      rw [substEnv_ref, entryVal_keepE env w' hF (Subst.okRef_at hθ hu)]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

/-! ## The `◇` view -/

theorem sec_apply {A : VarType} {w : M.frame.W} {S : M.frame.PosSec A w}
    {E : Set (M.frame.Acc w)} {f : (w' : E) → M.frame.Dom A w'.1.1} (H : S = ⟨E, f⟩)
    (w₂ : S.1) (hm : w₂.1 ∈ E) : S.2 w₂ = f ⟨w₂.1, hm⟩ := by
  subst H
  rfl

theorem posSec_ext_set {A : VarType} {w : M.frame.W} {E₁ E₂ : Set (M.frame.Acc w)}
    (hE : E₁ = E₂) (f : (w' : E₁) → M.frame.Dom A w'.1.1) (g : (w' : E₂) → M.frame.Dom A w'.1.1)
    (hfg : ∀ w' : E₁, f w' = g ⟨w'.1, hE ▸ w'.2⟩) :
    (⟨E₁, f⟩ : M.frame.PosSec A w) = ⟨E₂, g⟩ := by
  subst hE
  exact congrArg (Sigma.mk _) (funext hfg)

theorem Env.box_dia_agree {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {x : VarSymb}
    {X : VarType} (hr : Δ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x hr)).1) :
    Env.Agree (Ctx.le_boxIn_diaIn Δ x) (env.boxPush w'.1) (env.diaPush x hr w') := by
  intro v T hv
  match v with
  | .step _ .box => rfl
  | .step _ .keep => rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

/-- A possible entry has the extent of the new witness. -/
theorem entryVal_dia_ext {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {ιx : VarSymb}
    {X Y : VarType} :
    ∀ {e : SubE σ Δ} (he : e.OkRef (.VTypeDia X)) (_hw : e.idxAlong [] = ιx)
      (hr₁ : Δ.ref ιx = some (.VTypeDia Y)),
      (M.posEval (entryVal env e he)).1 = (M.posEval (env.ref ιx hr₁)).1
  | .ren v, he, hw, hr₁ => by
      have hv : v = ιx := hw
      subst hv
      have hXY : X = Y := by
        rw [he] at hr₁
        cases hr₁
        rfl
      subst hXY
      rfl
  | .tm (.diatm y hy u), he, hw, hr₁ => by
      have hy' : y = ιx := hw
      subst hy'
      cases he
      exact congrArg Sigma.fst (dia_beta env hy hr₁ u)
  | .tm (.var _ _), he, _, _ => nomatch he
  | .tm (.func _), he, _, _ => nomatch he
  | .tm .unit, he, _, _ => nomatch he
  | .tm (.pair _ _), he, _, _ => nomatch he
  | .tm (.boxtm _), he, _, _ => nomatch he
  | .hide, he, _, _ => False.elim he

/-- A possible entry's content at a world of the new witness's extent. -/
theorem entryVal_dia_content {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {ιx : VarSymb}
    {X Y : VarType} :
    ∀ {e : SubE σ Δ} (he : e.OkRef (.VTypeDia X)) (hw : e.idxAlong [] = ιx)
      (hr₁ : Δ.ref ιx = some (.VTypeDia Y)) (w' : (M.posEval (env.ref ιx hr₁)).1),
      entryVal (env.diaPush ιx hr₁ w') (e.diaBody ιx) (SubE.okRef_diaBody he hw) =
        (M.posEval (entryVal env e he)).2
          ⟨w'.1, by rw [entryVal_dia_ext env he hw hr₁]; exact w'.2⟩
  | .ren v, he, hw, hr₁, w' => by
      have hv : v = ιx := hw
      subst hv
      have hXY : X = Y := by
        rw [he] at hr₁
        cases hr₁
        rfl
      subst hXY
      rfl
  | .tm (.diatm y hy u), he, hw, hr₁, w' => by
      have hy' : y = ιx := hw
      subst hy'
      cases he
      rw [entryVal_congr _ (SubE.diaBody_diatm y hy u) _ rfl]
      symm
      exact sec_apply (dia_beta env hy hr₁ u) _ w'.2
  | .tm (.var _ _), he, _, _, _ => nomatch he
  | .tm (.func _), he, _, _, _ => nomatch he
  | .tm .unit, he, _, _, _ => nomatch he
  | .tm (.pair _ _), he, _, _, _ => nomatch he
  | .tm (.boxtm _), he, _, _, _ => nomatch he
  | .hide, he, _, _, _ => False.elim he

theorem substEnv_dia {Γ Δ : Ctx} {ι : VarSymb → VarSymb} {w : M.frame.W} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hnp : Γ.NoProjLast) (env : M.Env Δ w) {x : VarSymb} {X Y : VarType}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hr : Γ.ref x = some (.VTypeDia X))
    (hr₁ : Δ.ref (ι x) = some (.VTypeDia Y)) (hw : (θ.at x).idxAlong [] = ι x)
    (w' : (M.posEval (env.ref (ι x) hr₁)).1)
    (hm : w'.1 ∈ (M.posEval ((substEnv θ hθ hnp env).ref x hr)).1) :
    substEnv (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Ctx.noProjLast_diaIn Γ x)
        (env.diaPush (ι x) hr₁ w') =
      (substEnv θ hθ hnp env).diaPush x hr ⟨w'.1, hm⟩ := by
  funext v T hv
  match v with
  | .step u .dia =>
      have hux : u = x := by
        change (if u = x then _ else none) = some T at hv
        split_ifs at hv with h
        exact h
      subst hux
      have hXT := Ctx.diaIn_step_dia hr hv
      subst hXT
      change entryVal (env.diaPush (ι u) hr₁ w')
        (if u = u then (θ.at u).diaBody (ι u) else .hide) _ = _
      rw [entryVal_congr _ (if_pos rfl) _ (SubE.okRef_diaBody (Subst.okRef_at hθ hr) hw),
        entryVal_dia_content env (Subst.okRef_at hθ hr) hw hr₁ w']
      exact posEval_snd_congr (substEnv_ref θ hθ hnp env u hr).symm _ hm
  | .step u .box =>
      change entryVal (env.diaPush (ι x) hr₁ w') (((θ.at u).unbox).mono _) _ =
        M.necEval ((substEnv θ hθ hnp env).ref u (Ctx.boxIn_step_box hv)) w'.1
      rw [entryVal_mono (Env.box_dia_agree env hr₁ w') _
          (SubE.okRef_unbox (Subst.okRef_at hθ (Ctx.boxIn_step_box hv))),
        entryVal_unbox, substEnv_ref]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      change entryVal (env.diaPush (ι x) hr₁ w') (((θ.at u).keepE).mono _) _ =
        M.necEval (M.ops.necDup hF ((substEnv θ hθ hnp env).ref u hu)) w'.1
      rw [entryVal_mono (Env.box_dia_agree env hr₁ w') _
          (SubE.okRef_keepE hF (Subst.okRef_at hθ hu)),
        entryVal_keepE, substEnv_ref]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

/-! ## The substitution lemma for terms -/

mutual
  theorem interpFunc_subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
      (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hnp : Γ.NoProjLast) {w : M.frame.W}
      (env : M.Env Δ w) :
      ∀ {n : ℕ} (g : Func σ Γ n) (args : Fin n → M.frame.D w),
        interpFunc env (Func.subst ι θ hθ hc g) args =
          interpFunc (substEnv θ hθ hnp env) g args
    | _, .F _, _ => rfl
    | _, .eval g t, args => by
        change interpFunc env (Func.subst ι θ hθ hc g)
            (Fin.cons (interp env (Term.subst ι θ hθ hc t)) args) =
          interpFunc (substEnv θ hθ hnp env) g (Fin.cons (interp (substEnv θ hθ hnp env) t) args)
        rw [interp_subst θ hθ hc hnp env t, interpFunc_subst θ hθ hc hnp env g]

  /-- ⭐**Substitution lemma** for terms. -/
  theorem interp_subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
      (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hnp : Γ.NoProjLast) {w : M.frame.W}
      (env : M.Env Δ w) :
      ∀ {T : VarType} {a : Ann T} (t : Term σ Γ T a),
        interp env (Term.subst ι θ hθ hc t) = interp (substEnv θ hθ hnp env) t
    | _, _, .var v hv =>
        (interp_toVar env _ _).trans (substEnv_ref θ hθ hnp env v hv).symm
    | _, _, .func f => interpFunc_subst θ hθ hc hnp env f Fin.elim0
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change (interp env (Term.subst ι θ hθ hc s), interp env (Term.subst ι θ hθ hc t)) =
          (interp (substEnv θ hθ hnp env) s, interp (substEnv θ hθ hnp env) t)
        rw [interp_subst θ hθ hc hnp env s, interp_subst θ hθ hc hnp env t]
    | _, _, .boxtm t => by
        apply M.nec_inj
        funext w'
        change M.necEval (interp env (Term.boxtm
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) t))) w' = _
        rw [box_beta, box_beta,
          interp_subst θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) (Ctx.noProjLast_boxIn Γ)
            (env.boxPush w') t,
          substEnv_box θ hθ hnp env w']
    | _, _, .diatm x hx t => by
        have hx' := hx
        obtain ⟨X, hr⟩ := hx'
        have hw : (θ.at x).idxAlong [] = ι x := hc x _ hr []
        obtain ⟨Y, hr₁⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hw
        apply M.pos_inj
        change M.posEval (interp env (Term.diatm (ι x) _ (Term.subst ι (θ.dia x (ι x))
          (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) t))) = _
        rw [dia_beta env _ hr₁, dia_beta (substEnv θ hθ hnp env) hx hr]
        have hE : (M.posEval (env.ref (ι x) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref x hr)).1 := by
          rw [substEnv_ref θ hθ hnp env x hr, entryVal_dia_ext env _ hw hr₁]
        refine posSec_ext_set hE
          (fun w' => interp (env.diaPush (ι x) hr₁ w') (Term.subst ι (θ.dia x (ι x))
            (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) t))
          (fun w₂ => interp ((substEnv θ hθ hnp env).diaPush x hr w₂) t) (fun w' => ?_)
        dsimp only
        rw [interp_subst (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
            (Ctx.noProjLast_diaIn Γ x) (env.diaPush (ι x) hr₁ w') t,
          substEnv_dia θ hθ hnp env hx hr hr₁ hw w' _]
end

end Model

end V12M
