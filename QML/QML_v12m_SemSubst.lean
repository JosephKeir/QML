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

/-- ⭐Under 4, the `◇_y` view at the end of a composite arrow agrees, across the shift, with
    the `◇_{y.keep}` view through the intermediate world: `y.dia` is the content of `y`'s
    restriction there (`Model.posKeep_full`), and the `□` part is `Env.shiftAgree_twoBox`. -/
theorem Env.shiftAgree_diaKeep (hF : ModalSys.Four = true) (hnS : ModalSys.shaped = false)
    {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {y : VarSymb} {Y : VarType}
    (hy : Γ.ref y = some (.VTypeDia Y)) (v : M.frame.Acc w) (b : M.frame.Acc v.1)
    (hb : (⟨b.1, ⟨M.frame.trans hF v.2.down b.2.down⟩⟩ : M.frame.Acc w) ∈
      (M.posEval (env.ref y hy)).1)
    (hyk : Γ.boxIn.ref (.step y .keep) = some (.VTypeDia Y))
    (hb' : b ∈ (M.posEval ((env.boxPush v).ref (.step y .keep) hyk)).1) :
    Env.ShiftAgree (Ctx.shifts_diaIn_keep hF hnS Γ y)
      (env.diaPush y hy ⟨_, hb⟩) ((env.boxPush v).diaPush (.step y .keep) hyk ⟨b, hb'⟩) := by
  refine Env.ShiftAgree.of_raw ?_
  intro x T hlp hx
  match x with
  | .step u .dia =>
      have hu : u = y := by
        change (if u = y then _ else none) = some T at hx
        split_ifs at hx with h
        exact h
      subst hu
      have hXT := Ctx.diaIn_step_dia hy hx
      subst hXT
      rw [Env.ref_congr _ (VarSymb.shift_level_zero (s := .dia) rfl) _ (Ctx.ref_diaIn_of hyk),
        Env.ref, dif_neg (by decide : ¬ Step.dia.isProj = true)]
      simp only [Env.diaPush]
      have H := congrArg Prod.fst (M.posKeep_full hF hnS (env.ref u hy) v)
      exact (sec_apply H ⟨b, hb'⟩ hb).symm
  | .step u .box =>
      exact Env.shiftAgree_twoBox hF env v b (.step u .box) T ((Ctx.ref_nonproj _ hlp).trans hx)
  | .step u .keep =>
      exact Env.shiftAgree_twoBox hF env v b (.step u .keep) T ((Ctx.ref_nonproj _ hlp).trans hx)
  | .root _ => cases hx
  | .step _ .fst => cases hx
  | .step _ .snd => cases hx
  | .step _ .here => cases hx

/-- ⭐**Substituting a kept possible entry** (unshaped, docs §3 4): the entry's restriction along
    the arrow — for a term `◇_y t`, the term `◇_{y.keep}(shift t)` denotes it. -/
theorem entryVal_keepE_dia {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (w' : M.frame.Acc w)
    (hF : ModalSys.Four = true) (hnS : ModalSys.shaped = false) :
    ∀ {e : SubE σ Δ} {X : VarType} (he : e.OkRef (.VTypeDia X)),
      entryVal (env.boxPush w') e.keepE
          (SubE.okRef_keepE' hF (VarType.keepable_dia hnS) he) =
        M.necEval (M.ops.posKeep hF hnS (entryVal env e he)) w'
  | .ren _, _, _ => rfl
  | .tm (T := U) s, X, he => by
      have hU : U = .VTypeDia X := he
      subst hU
      cases s with
      | diatm y hy t =>
          have hy' := hy
          obtain ⟨Y, hr⟩ := hy'
          have hyk : Δ.boxIn.ref (.step y .keep) = some (.VTypeDia Y) :=
            Ctx.ref_keep_of' hF hr (VarType.keepable_dia hnS)
          rw [entryVal_congr _ (SubE.keepE_dia y hy t hF hnS) _ rfl]
          change interp (env.boxPush w') (Term.diatm (.step y .keep) _
              (Term.shift (Ctx.shifts_diaIn_keep hF hnS Δ y) t)) =
            M.necEval (M.ops.posKeep hF hnS (interp env (Term.diatm y hy t))) w'
          refine M.pos_inj ?_ fun hSh => absurd hSh (by rw [hnS]; decide)
          have H₁ : M.posEval (M.necEval (M.ops.posKeep hF hnS (env.ref y hr)) w') = _ :=
            congrArg Prod.fst (M.posKeep_full hF hnS (env.ref y hr) w')
          have H₂ : M.posEval (M.necEval (M.ops.posKeep hF hnS
              (interp env (Term.diatm y hy t))) w') = _ :=
            congrArg Prod.fst (M.posKeep_full hF hnS (interp env (Term.diatm y hy t)) w')
          dsimp only at H₁ H₂
          have H₃ := dia_beta env hy hr t
          rw [dia_beta (env.boxPush w') _ hyk]
          change (⟨(M.posEval (M.necEval (M.ops.posKeep hF hnS (env.ref y hr)) w')).1, _⟩ :
            M.frame.PosSec _ _) = _
          rw [H₂]
          have hE : (M.posEval (M.necEval (M.ops.posKeep hF hnS (env.ref y hr)) w')).1 =
              {b : M.frame.Acc w'.1 | (⟨b.1, ⟨M.frame.trans hF w'.2.down b.2.down⟩⟩ :
                M.frame.Acc w) ∈ (M.posEval (interp env (Term.diatm y hy t))).1} := by
            rw [H₁, H₃]
          refine posSec_ext_set hE _ _ (fun b => ?_)
          have hm : (⟨b.1.1, ⟨M.frame.trans hF w'.2.down b.1.2.down⟩⟩ : M.frame.Acc w) ∈
              (M.posEval (env.ref y hr)).1 :=
            (congrArg (fun S : M.frame.PosSec _ _ => (b.1 : M.frame.Acc w'.1) ∈ S.1) H₁).mp b.2
          rw [sec_apply H₃ _ hm]
          exact interp_shift (Env.shiftAgree_diaKeep hF hnS env hr w' b.1 hm hyk b.2) t
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
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      cases T with
      | VTypeBox A =>
          change entryVal (env.boxPush w') ((θ.at u).keepE) _ =
            M.necEval (M.ops.necDup hF ((substEnv θ hθ hnp env).ref u hu)) w'
          rw [substEnv_ref, entryVal_keepE env w' hF (Subst.okRef_at hθ hu)]
      | VTypeDia A =>
          have hnS := VarType.noShaped_of_keepable_dia hk
          change entryVal (env.boxPush w') ((θ.at u).keepE) _ =
            M.necEval (M.ops.posKeep hF hnS ((substEnv θ hθ hnp env).ref u hu)) w'
          rw [substEnv_ref, entryVal_keepE_dia env w' hF hnS (Subst.okRef_at hθ hu)]
      | _ => cases hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

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
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      cases T with
      | VTypeBox A =>
          change entryVal (env.diaPush (ι x) hr₁ w') (((θ.at u).keepE).mono _) _ =
            M.necEval (M.ops.necDup hF ((substEnv θ hθ hnp env).ref u hu)) w'.1
          rw [entryVal_mono (Env.box_dia_agree env hr₁ w') _
              (SubE.okRef_keepE hF (Subst.okRef_at hθ hu)),
            entryVal_keepE, substEnv_ref]
      | VTypeDia A =>
          have hnS := VarType.noShaped_of_keepable_dia hk
          change entryVal (env.diaPush (ι x) hr₁ w') (((θ.at u).keepE).mono _) _ =
            M.necEval (M.ops.posKeep hF hnS ((substEnv θ hθ hnp env).ref u hu)) w'.1
          rw [entryVal_mono (Env.box_dia_agree env hr₁ w') _
              (SubE.okRef_keepE' hF hk (Subst.okRef_at hθ hu)),
            entryVal_keepE_dia env w'.1 hF hnS, substEnv_ref]
      | _ => cases hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

end Model

namespace Model

variable {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}
  [Arrows.RootKeep F Root]

/-! ## Shapes: reading a `□` view at the current world, and keeping it -/

/-- Under T, the `□` view collapsed at the current level agrees with the environment across the
    collapse — the shape counterpart of `Env.collapseAgree_self`. -/
theorem ShEnv.collapseAgree_self (hT : ModalSys.T = true) {Γ : Ctx} {w : F.W}
    (ρ : ShEnv F Root Γ w) (j : ℕ) :
    ShEnv.CollapseAgree (Ctx.collapses_boxIn_self hT Γ)
      ((ρ.boxPush j).mapLeaves (Arrows.Leaf.collapse hT j)) ρ j := by
  refine ShEnv.CollapseAgree.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      rw [ShEnv.ref_congr ρ j (VarSymb.collapse_level_zero (s := .box) rfl (by decide)) _
        (Ctx.ref_here_of hT hu), ShEnv.ref_proj ρ j (rfl : Step.here.isProj = true) hu]
      rfl
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep_T hT hv
      rw [ShEnv.ref_congr ρ j (VarSymb.collapse_keep_zero (v := u)) _ hu]
      change Shp.map (Arrows.Leaf.collapse hT j)
          (Shp.box ((ρ.ref j u hu).inner.map (Arrows.Leaf.shift hF j))) = ρ.ref j u hu
      simp only [Shp.map, Shp.map_map]
      rw [Shp.map_congr (g := Arrows.Leaf.collapse hT j ∘ Arrows.Leaf.shift hF j) (g' := id)
        (fun ℓ => Arrows.Leaf.collapse_shift_self hT hF j ℓ), Shp.map_id]
      exact (Shp.box_eta _).symm
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- Under 4, the `□` view kept and pushed once more agrees, across the shift, with the `□` view
    shifted at its level — the shape counterpart of `Env.shiftAgree_twoBox`. -/
theorem ShEnv.shiftAgree_twoBox [Arrows.RootKeepLaws F Root] (hF : ModalSys.Four = true)
    {Γ : Ctx} {w : F.W}
    (ρ : ShEnv F Root Γ w) (j : ℕ) :
    ShEnv.ShiftAgree (Ctx.shifts_boxIn_boxIn hF Γ)
      ((ρ.boxPush j).mapLeaves (Arrows.Leaf.shift hF j)) ((ρ.boxPush j).boxPush (j + 1))
      (j + 2) := by
  refine ShEnv.ShiftAgree.of_raw ?_
  intro x T _ hx
  match x with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hx
      rw [ShEnv.ref_congr _ _ (VarSymb.shift_level_zero (s := .box) rfl) _
        (Ctx.ref_boxIn_of hk (Ctx.ref_keep_of hF hu)),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.box.isProj = true)]
      change (ρ.ref j u hu).inner.map (Arrows.Leaf.shift hF j) =
        ((ρ.boxPush j).ref (j + 1) (.step u .keep) (Ctx.ref_keep_of hF hu)).inner
      rw [ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
      rfl
  | .step u .keep =>
      obtain ⟨_, hu, hk⟩ := Ctx.boxIn_keep hx
      cases T with
      | VTypeDia A =>
          -- ⭐A kept possibility kept again: `shift_dk`, by the root action's composition law.
          rw [ShEnv.ref_congr _ _ (VarSymb.shift_level_zero (s := .keep) rfl) _
            (Ctx.ref_keep_of' hF (Ctx.ref_keep_of' hF hu hk) hk),
            ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
          change Shp.map (Arrows.Leaf.shift hF j) ((ρ.ref j u hu).map (Arrows.Leaf.dk hF j)) =
            (GFunc.shp (GFunc.keep (σ := σ) hF hk) (j + 1)
              ((ρ.boxPush j).ref (j + 1) (.step u .keep) (Ctx.ref_keep_of' hF hu hk))).inner
          rw [ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
          change _ = ((ρ.ref j u hu).map (Arrows.Leaf.dk hF j)).map (Arrows.Leaf.dk hF (j + 1))
          rw [Shp.map_map, Shp.map_map]
          exact Shp.map_congr (fun ℓ => Arrows.Leaf.shift_dk hF j ℓ) _
      | VTypeBox A =>
      rw [ShEnv.ref_congr _ _ (VarSymb.shift_level_zero (s := .keep) rfl) _
        (Ctx.ref_keep_of hF (Ctx.ref_keep_of hF hu)),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
      change Shp.map (Arrows.Leaf.shift hF j)
          (Shp.box ((ρ.ref j u hu).inner.map (Arrows.Leaf.shift hF j))) =
        (GFunc.shp (GFunc.dup (σ := σ) hF) (j + 1)
          ((ρ.boxPush j).ref (j + 1) (.step u .keep) (Ctx.ref_keep_of hF hu))).inner
      rw [ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
      change Shp.box (((ρ.ref j u hu).inner.map (Arrows.Leaf.shift hF j)).map
          (Arrows.Leaf.shift hF j)) =
        Shp.box (((ρ.ref j u hu).inner.map (Arrows.Leaf.shift hF j)).map
          (Arrows.Leaf.shift hF (j + 1)))
      rw [Shp.map_map, Shp.map_map]
      exact congrArg Shp.box
        (Shp.map_congr (fun ℓ => (Arrows.Leaf.shift_shift_self hF j ℓ).symm) _)
      | _ => cases hk
  | .root _ => cases hx
  | .step _ .fst => cases hx
  | .step _ .snd => cases hx
  | .step _ .dia => cases hx
  | .step _ .here => cases hx

/-- ⭐A term read in the `□` view and collapsed to the current level has the view's shape,
    collapsed at the current level. -/
theorem termShp_collapse_self (hT : ModalSys.T = true) {Γ : Ctx} {w : F.W}
    (ρ : ShEnv F Root Γ w) (j : ℕ) {A : VarType} {a : Ann A} (t : Term σ Γ.boxIn A a) :
    termShp ρ j (Term.collapse (Ctx.collapses_boxIn_self hT Γ) t) =
      (termShp (ρ.boxPush j) (j + 1) t).map (Arrows.Leaf.collapse hT j) := by
  rw [termShp_collapse (ShEnv.collapseAgree_self hT ρ j)]
  exact termShp_mapCollapse hT j (ρ.boxPush j) 0 t

/-- ⭐A term of the `□` view, shifted into the `□□` view, has the view's shape shifted at its
    level. -/
theorem termShp_shift_twoBox [Arrows.RootKeepLaws F Root] (hF : ModalSys.Four = true)
    {Γ : Ctx} {w : F.W}
    (ρ : ShEnv F Root Γ w) (j : ℕ) {A : VarType} {a : Ann A} (t : Term σ Γ.boxIn A a) :
    termShp ((ρ.boxPush j).boxPush (j + 1)) (j + 2)
        (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) t) =
      (termShp (ρ.boxPush j) (j + 1) t).map (Arrows.Leaf.shift hF j) := by
  rw [termShp_shift (ShEnv.shiftAgree_twoBox hF ρ j)]
  exact termShp_mapShift hF j (ρ.boxPush j) 0 t

/-! ## Shapes under substitution -/

/-- The shape of a substitution entry. -/
def entryShp {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) :
    (e : SubE σ Δ) → {T : VarType} → e.OkRef T → Shape F Root w T
  | .ren v, _, h => ρ.ref j v h
  | .tm s, _, h => h ▸ termShp ρ j s
  | .hide, _, h => False.elim h

/-- The shape environment a substitution induces on its source. -/
def substShEnv {Γ Δ : Ctx} {w : F.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (ρ : ShEnv F Root Δ w) (j : ℕ)
    : ShEnv F Root Γ w :=
  fun v T hv => entryShp ρ j (θ v) (hθ v T (hnp v T hv) hv)

theorem entryShp_congr {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ)
    {e e' : SubE σ Δ}
    {T : VarType} (he : e = e') (h : e.OkRef T) (h' : e'.OkRef T) :
    entryShp ρ j e h = entryShp ρ j e' h' := by
  subst he
  rfl

theorem entryShp_proj {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ) :
    ∀ {e : SubE σ Δ} {U T : VarType} {s : Step} (he : e.OkRef U) (hs : s.isProj = true)
      (hst : U.step s = some T),
      entryShp ρ j (e.proj s) (SubE.okRef_proj he hs hst) =
        GFunc.shp (GFunc.proj (σ := σ) hs hst) j (entryShp ρ j e he)
  | .ren v, U, T, s, he, hs, hst => by
      change ρ.ref j (.step v s) (SubE.okRef_proj he hs hst) = _
      rw [ShEnv.ref_proj ρ j hs he]
      rfl
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
              rw [entryShp_congr ρ j (SubE.proj_boxtm_here t hT) _ rfl]
              change termShp ρ j (Term.collapse _ t) =
                (termShp (ρ.boxPush j) (j + 1) t).map (Arrows.Leaf.collapse hT j)
              exact termShp_collapse_self hT ρ j t
          | _ => cases hst

/-- The substituted shape environment at any reachable address is that address's entry. -/
theorem substShEnv_ref {Γ Δ : Ctx} {w : F.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (ρ : ShEnv F Root Δ w) (j : ℕ) :
    ∀ (v : VarSymb) {T : VarType} (hv : Γ.ref v = some T),
      (substShEnv θ hθ hnp ρ j).ref j v hv = entryShp ρ j (θ.at v) (Subst.okRef_at hθ hv)
  | .root _, _, _ => rfl
  | .step v s, T, hv => by
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at hv
          cases hU : Γ.ref v with
          | none => rw [hU] at hv; cases hv
          | some U => exact ⟨U, rfl⟩
        rw [ShEnv.ref_proj _ j hs hU hv, substShEnv_ref θ hθ hnp ρ j v hU]
        have hat : θ.at (.step v s) = (θ.at v).proj s := by
          change (if s.isProj then _ else _) = _
          rw [if_pos hs]
        have hst : U.step s = some T := by
          rw [Ctx.ref_step_proj Γ v hs, hU] at hv
          exact hv
        rw [entryShp_congr ρ j hat _ (SubE.okRef_proj (Subst.okRef_at hθ hU) hs hst),
          entryShp_proj]
      · rw [ShEnv.ref_nonproj _ j hs hv]
        exact entryShp_congr ρ j (Subst.at_nonproj θ (v := .step v s)
          (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs)).symm _ _

theorem entryShp_mono {Δ Δ' : Ctx} {h : Δ.Le Δ'} {w : F.W} {ρ : ShEnv F Root Δ w}
    {ρ' : ShEnv F Root Δ' w} (hag : ShEnv.Agree h ρ ρ') (j : ℕ) :
    ∀ (e : SubE σ Δ) {T : VarType} (he : e.OkRef T),
      entryShp ρ' j (e.mono h) (SubE.okRef_mono h he) = entryShp ρ j e he
  | .ren v, _, he => (ShEnv.ref_agree hag j v he).symm
  | .tm s, _, he => by
      cases he
      exact termShp_mono hag j s
  | .hide, _, he => False.elim he

theorem entryShp_unbox {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ)
    (hk : ModalSys.keepOnly = false) :
    ∀ {e : SubE σ Δ} {A : VarType} (he : e.OkRef (.VTypeBox A)),
      entryShp (ρ.boxPush j) (j + 1) e.unbox (SubE.okRef_unbox he) = (entryShp ρ j e he).inner
  | .ren u, _, he => by
      change (ρ.boxPush j).ref (j + 1) u.inner _ = (ρ.ref j u he).inner
      rw [ShEnv.ref_congr _ _ (VarSymb.inner_box hk) _ (Ctx.ref_boxIn_of hk he),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.box.isProj = true)]
      rfl
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t => rfl
  | .hide, _, he => False.elim he

theorem entryShp_keepE [Arrows.RootKeepLaws F Root] {Δ : Ctx} {w : F.W}
    (ρ : ShEnv F Root Δ w) (j : ℕ) (hF : ModalSys.Four = true) :
    ∀ {e : SubE σ Δ} {A : VarType} (he : e.OkRef (.VTypeBox A)),
      entryShp (ρ.boxPush j) (j + 1) e.keepE (SubE.okRef_keepE hF he) =
        (GFunc.shp (GFunc.dup (σ := σ) hF) j (entryShp ρ j e he)).inner
  | .ren u, _, he => by
      change (ρ.boxPush j).ref (j + 1) (.step u .keep) (SubE.okRef_keepE hF he) = _
      rw [ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
      rfl
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          rw [entryShp_congr _ _ (SubE.keepE_tm t hF) _ rfl]
          change Shp.box (termShp ((ρ.boxPush j).boxPush (j + 1)) (j + 2)
              (Term.shift (Ctx.shifts_boxIn_boxIn hF Δ) t)) =
            Shp.box ((termShp (ρ.boxPush j) (j + 1) t).map (Arrows.Leaf.shift hF j))
          rw [termShp_shift_twoBox hF ρ j t]
  | .hide, _, he => False.elim he

theorem substShEnv_box [Arrows.RootKeepLaws F Root] {Γ Δ : Ctx} {w : F.W} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hnp : Γ.NoProjLast) (ρ : ShEnv F Root Δ w) (j : ℕ)
    (hnd : ModalSys.NoDiaKeep) :
    substShEnv θ.box (Subst.ok_box hθ) (Ctx.noProjLast_boxIn Γ) (ρ.boxPush j) (j + 1) =
      (substShEnv θ hθ hnp ρ j).boxPush j := by
  funext v T hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      change entryShp (ρ.boxPush j) (j + 1) ((θ.at u).unbox) _ =
        ((substShEnv θ hθ hnp ρ j).ref j u (Ctx.boxIn_step_box hv)).inner
      rw [substShEnv_ref, entryShp_unbox ρ j hk (Subst.okRef_at hθ (Ctx.boxIn_step_box hv))]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep_nd hnd hv
      change entryShp (ρ.boxPush j) (j + 1) ((θ.at u).keepE) _ =
        (GFunc.shp (GFunc.dup (σ := σ) hF) j ((substShEnv θ hθ hnp ρ j).ref j u hu)).inner
      rw [substShEnv_ref, entryShp_keepE ρ j hF (Subst.okRef_at hθ hu)]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem ShEnv.box_dia_agree {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ)
    {x : VarSymb}
    {X : VarType} (hr : Δ.ref x = some (.VTypeDia X)) :
    ShEnv.Agree (Ctx.le_boxIn_diaIn Δ x) (ρ.boxPush j) (ρ.diaPush j x hr) := by
  intro v T hv
  match v with
  | .step _ .box => rfl
  | .step _ .keep => rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- A possible entry has the label of the new witness. -/
theorem entryShp_dia_label {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ)
    {ιx : VarSymb}
    {X Y : VarType} :
    ∀ {e : SubE σ Δ} (he : e.OkRef (.VTypeDia X)) (_hw : e.idxAlong [] = ιx)
      (hr₁ : Δ.ref ιx = some (.VTypeDia Y)),
      (entryShp ρ j e he).label = (ρ.ref j ιx hr₁).label
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
      change (termShp ρ j (Term.diatm y hy u)).label = _
      rw [termShp_diatm ρ j hr₁]
      rfl
  | .tm (.var _ _), he, _, _ => nomatch he
  | .tm (.func _), he, _, _ => nomatch he
  | .tm .unit, he, _, _ => nomatch he
  | .tm (.pair _ _), he, _, _ => nomatch he
  | .tm (.boxtm _), he, _, _ => nomatch he
  | .hide, he, _, _ => False.elim he

/-- A possible entry's content shape is its body's. -/
theorem entryShp_dia_body {Δ : Ctx} {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ)
    {ιx : VarSymb}
    {X Y : VarType} :
    ∀ {e : SubE σ Δ} (he : e.OkRef (.VTypeDia X)) (hw : e.idxAlong [] = ιx)
      (hr₁ : Δ.ref ιx = some (.VTypeDia Y)),
      entryShp (ρ.diaPush j ιx hr₁) (j + 1) (e.diaBody ιx) (SubE.okRef_diaBody he hw) =
        (entryShp ρ j e he).body
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
      rw [entryShp_congr _ _ (SubE.diaBody_diatm y hy u) _ rfl]
      change termShp (ρ.diaPush j y hr₁) (j + 1) u = (termShp ρ j (Term.diatm y hy u)).body
      rw [termShp_diatm ρ j hr₁]
      rfl
  | .tm (.var _ _), he, _, _ => nomatch he
  | .tm (.func _), he, _, _ => nomatch he
  | .tm .unit, he, _, _ => nomatch he
  | .tm (.pair _ _), he, _, _ => nomatch he
  | .tm (.boxtm _), he, _, _ => nomatch he
  | .hide, he, _, _ => False.elim he

theorem substShEnv_dia [Arrows.RootKeepLaws F Root] {Γ Δ : Ctx} {ι : VarSymb → VarSymb}
    {w : F.W} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hnp : Γ.NoProjLast) (ρ : ShEnv F Root Δ w) (j : ℕ)
    (hnd : ModalSys.NoDiaKeep)
    {x : VarSymb}
    {X Y : VarType} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hr : Γ.ref x = some (.VTypeDia X))
    (hr₁ : Δ.ref (ι x) = some (.VTypeDia Y)) (hw : (θ.at x).idxAlong [] = ι x) :
    substShEnv (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Ctx.noProjLast_diaIn Γ x)
        (ρ.diaPush j (ι x) hr₁) (j + 1) =
      (substShEnv θ hθ hnp ρ j).diaPush j x hr := by
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
      change entryShp (ρ.diaPush j (ι u) hr₁) (j + 1)
        (if u = u then (θ.at u).diaBody (ι u) else .hide) _ = _
      rw [entryShp_congr _ _ (if_pos rfl) _ (SubE.okRef_diaBody (Subst.okRef_at hθ hr) hw),
        entryShp_dia_body ρ j (Subst.okRef_at hθ hr) hw hr₁]
      simp only [ShEnv.diaPush]
      rw [substShEnv_ref θ hθ hnp ρ j u hr]
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ) hv
      change entryShp (ρ.diaPush j (ι x) hr₁) (j + 1) (((θ.at u).unbox).mono _) _ =
        ((substShEnv θ hθ hnp ρ j).ref j u (Ctx.boxIn_step_box hv)).inner
      rw [entryShp_mono (ShEnv.box_dia_agree ρ j hr₁) _ _
          (SubE.okRef_unbox (Subst.okRef_at hθ (Ctx.boxIn_step_box hv))),
        entryShp_unbox ρ j hk, substShEnv_ref]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep_nd hnd (Γ := Γ) hv
      change entryShp (ρ.diaPush j (ι x) hr₁) (j + 1) (((θ.at u).keepE).mono _) _ =
        (GFunc.shp (GFunc.dup (σ := σ) hF) j ((substShEnv θ hθ hnp ρ j).ref j u hu)).inner
      rw [entryShp_mono (ShEnv.box_dia_agree ρ j hr₁) _ _
          (SubE.okRef_keepE hF (Subst.okRef_at hθ hu)),
        entryShp_keepE ρ j hF, substShEnv_ref]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- ⭐**Substitution lemma for shapes.** -/
theorem termShp_subst [Arrows.RootKeepLaws F Root] {ι : VarSymb → VarSymb}
    (hnd : ModalSys.NoDiaKeep) :
    ∀ {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
      (hnp : Γ.NoProjLast) {w : F.W} (ρ : ShEnv F Root Δ w) (j : ℕ)
      {T : VarType} {a : Ann T} (t : Term σ Γ T a),
      termShp ρ j (Term.subst ι θ hθ hc t) = termShp (substShEnv θ hθ hnp ρ j) j t
  | _, _, _, _, _, _, _, _, _, _, _, .var _ _ => shp_var_eq _ _
  | _, _, _, _, _, _, _, _, _, _, _, .func _ => shp_var_eq _ _
  | _, _, _, _, _, _, _, _, _, _, _, .unit => rfl
  | _, _, θ, hθ, hc, hnp, _, ρ, j, _, _, .pair s t => by
      change Shp.prod (termShp ρ j (Term.subst ι θ hθ hc s))
          (termShp ρ j (Term.subst ι θ hθ hc t)) = _
      rw [termShp_subst hnd θ hθ hc hnp ρ j s, termShp_subst hnd θ hθ hc hnp ρ j t]
      rfl
  | Γ, _, θ, hθ, hc, hnp, _, ρ, j, _, _, .boxtm t => by
      change Shp.box (termShp (ρ.boxPush j) (j + 1)
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) t)) = _
      rw [termShp_subst hnd θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
          (Ctx.noProjLast_boxIn Γ) (ρ.boxPush j) (j + 1) t, substShEnv_box θ hθ hnp ρ j hnd]
      rfl
  | Γ, _, θ, hθ, hc, hnp, _, ρ, j, _, _, .diatm x hx t => by
      have hx' := hx
      obtain ⟨X, hr⟩ := hx'
      have hw : (θ.at x).idxAlong [] = ι x := hc x _ hr []
      obtain ⟨Y, hr₁⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hw
      change termShp ρ j (Term.diatm (ι x) _ (Term.subst ι (θ.dia x (ι x))
        (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) t)) = _
      rw [termShp_diatm ρ j hr₁, termShp_diatm _ j hr,
        termShp_subst hnd (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (Ctx.noProjLast_diaIn Γ x) (ρ.diaPush j (ι x) hr₁) (j + 1) t,
        substShEnv_dia θ hθ hnp ρ j hnd hx hr hr₁ hw, substShEnv_ref θ hθ hnp ρ j x hr,
        entryShp_dia_label ρ j (Subst.okRef_at hθ hr) hw hr₁]

end Model

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-- The shape of an entry's value is the entry's shape. -/
theorem domSh_entryVal (hSh : ModalSys.shaped = true) {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ (e : SubE σ Δ) {T : VarType} (he : e.OkRef T),
      domSh hSh (entryVal env e he) = entryShp (envShape hSh env) 0 e he
  | .ren v, _, he => (ref_envShape hSh env v he).symm
  | .tm s, _, he => by
      cases he
      exact domSh_interp hSh env s
  | .hide, _, he => False.elim he

/-- The shapes of a substituted environment are the substituted shapes. -/
theorem envShape_substEnv (hSh : ModalSys.shaped = true) {Γ Δ : Ctx} {w : M.frame.W}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hnp : Γ.NoProjLast) (env : M.Env Δ w) :
    envShape hSh (substEnv θ hθ hnp env) = substShEnv θ hθ hnp (envShape hSh env) 0 := by
  funext v T hv
  exact domSh_entryVal hSh env (θ v) _

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
        refine M.pos_inj ?_ fun hSh => ?_
        swap
        · change domSh hSh (interp env (Term.subst ι θ hθ hc (Term.diatm x hx t))) =
            domSh hSh (interp (substEnv θ hθ hnp env) (Term.diatm x hx t))
          rw [domSh_interp, domSh_interp, termShp_subst (Or.inr hSh) θ hθ hc hnp,
            envShape_substEnv]
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
