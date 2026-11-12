import QML.QML_v12m_OCanonModel
import QML.QML_v12m_CanonTerm

/-!
# QML v12m — the canonical tree with `Opt` on: the truth lemma for terms

The **canonical environment** at stage `i` of a world gives every visible address the frame object
of its η-expansion, and a witness is **present exactly when its content is declared** at the stage,
with that content as its value (`canonEnvO`).  Stages add only the world's own roots, so a content
is declared at a stage exactly when it is in the base (`Ctx.stage_step`); for a world that decides
its witnesses, changing the stage keeps the witnesses (`canonEnvO_le_wit`, by `DecidesO.stable`).

Entering a modality at a child agrees with the child's canonical environment, in objects and in
witnesses (`boxPush_agree_canonO`, `boxPush_witAgree_canonO`, `diaPush_agree_canonO`): a witness
read along the arrow to a child is present exactly when the child opened it.

⭐`interp_canonO`: in any environment agreeing with the canonical one, a term's value is its
denotation.  T and 4 are off, so every successor is a child and the induction is on terms alone.
-/

namespace V12M

variable [ModalSys]

omit [ModalSys] in
/-- Stages add only roots: a step address reads as in the base. -/
theorem Ctx.stage_step {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} :
    ∀ (k : ℕ) (v : VarSymb) (s : Step), B.stage τ ρ k (.step v s) = B (.step v s)
  | 0, _, _ => rfl
  | k + 1, v, s => by
      change (Ctx.insert (B.stage τ ρ k) (.free (ρ k)) (τ k)) (.step v s) = _
      rw [Ctx.insert_ne (fun h => by cases h)]
      exact Ctx.stage_step k v s

omit [ModalSys] in
/-- Stages keep the witnesses. -/
theorem Ctx.stage_wit {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} :
    ∀ (k : ℕ) (y : VarSymb), (B.stage τ ρ k).wit y = B.wit y
  | 0, _ => rfl
  | k + 1, y => Ctx.stage_wit k y

namespace OCanon

open Canon

variable {σ : Signature} {N₀ : ℕ}

theorem ctx_step (w : World σ N₀) (i : ℕ × ℕ) (v : VarSymb) (s : Step) :
    w.L.ctx i (.step v s) = w.L.base i.1 (.step v s) :=
  Ctx.stage_step _ v s

theorem ctx_wit (w : World σ N₀) (i : ℕ × ℕ) (y : VarSymb) :
    (w.L.ctx i).wit y = (w.L.base i.1).wit y :=
  Ctx.stage_wit _ y

/-- ⭐**Declared at one stage, declared at all**, in a world deciding its witnesses: a witness's
    content declared at a later stage is declared already. -/
theorem DecidesO.ctx_stable {hO : ModalSys.Opt = true} {w : World σ N₀} (hdec : DecidesO hO w)
    {i j : ℕ × ℕ} {y : VarSymb} {X : VarType} (hy : (w.L.ctx i).wit y = some X)
    (h : w.L.ctx j (.step y .dia) = some X) : w.L.ctx i (.step y .dia) = some X := by
  rw [ctx_step] at h ⊢
  rw [ctx_wit] at hy
  exact hdec.stable h hy

variable (hO : ModalSys.Opt = true)

theorem rdenO_sigma {A : VarType} {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i))
    {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) :
    rdenO hO w i e p.2 = rdenO hO w i e q.2 := by
  subst h
  rfl

/-- The denotations of the η-expansions of an address in two nested contexts agree. -/
theorem rdenO_eta_le {Γ₁ Γ₂ : Ctx} (h : Γ₁.Le Γ₂) {w : World σ N₀} {i j : ℕ × ℕ}
    (e₁ : Γ₁.Le (w.L.ctx i)) (e₂ : Γ₂.Le (w.L.ctx j)) (v : VarSymb) (T : VarType)
    (p₁ : Γ₁.ref v = some T) (p₂ : Γ₂.ref v = some T) :
    rdenO hO w i e₁ (Term.eta (σ := σ) v T p₁) = rdenO hO w j e₂ (Term.eta v T p₂) := by
  rw [show Term.eta (σ := σ) v T p₂ = Term.mono h (Term.eta v T p₁) from
    (Term.mono_eta h v T p₁).symm, rdenO_mono]
  exact rdenO_congr _ _ _ _ _ _

variable [Countable σ.FuncSyms] [Countable σ.RelSyms] (w₀ : World σ N₀)

/-- The canonical value of a visible address: its η-expansion's denotation. -/
noncomputable def canonVal (w : World σ N₀) (i : ℕ × ℕ) (v : VarSymb) (T : VarType)
    (hv : w.L.ctx i v = some T) : (frameO hO w₀).Dom T w :=
  toDomO hO w₀ T w (rdenO hO w i (Ctx.Le.refl _)
    (Term.eta v T ((Ctx.ref_nonproj _ (w.noProjLast i v T hv)).trans hv))) (definableO_rden _ _)

/-- ⭐**The canonical environment**: every visible address denotes its η-expansion, and a witness
    is present exactly when its content is declared, with that content as its value. -/
noncomputable def canonEnvO (w : World σ N₀) (i : ℕ × ℕ) :
    (model hO w₀).Env (w.L.ctx i) w where
  val := canonVal hO w₀ w i
  wit y X _ := ⟨w.L.ctx i (.step y .dia) = some X, fun hv => canonVal hO w₀ w i _ X hv⟩
  opened _ _ _ hv := ⟨hv, rfl⟩

/-- Every reachable address reads as its η-expansion. -/
theorem canonEnvO_ref (w : World σ N₀) (i : ℕ × ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : (w.L.ctx i).ref v = some T),
      (canonEnvO hO w₀ w i).ref v h =
        toDomO hO w₀ T w (rdenO hO w i (Ctx.Le.refl _) (Term.eta v T h)) (definableO_rden _ _)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isStruct = true
      · rw [Model.Env.ref, dif_pos hs]
        split
        · rename_i U hU
          rw [canonEnvO_ref w i v hU]
          have hT : U.step s = some T := by
            rw [Ctx.ref_step_proj _ _ hs, hU] at h
            exact h
          cases s with
          | fst =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              rfl
          | snd =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              rfl
          | here =>
              cases U <;> simp only [VarType.step, reduceCtorEq] at hT
              exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T (VarType.step_here hT).1)).elim
          | box => cases hs
          | dia => cases hs
          | keep => cases hs
          | «at» => cases hs
        · rename_i hU
          rw [Ctx.ref_step_proj _ _ hs, hU] at h
          cases h
      · rw [Model.Env.ref, dif_neg hs]
        rfl

/-- The extent of a canonical possible address is the children that opened it. -/
theorem canonEnvO_extent (w : World σ N₀) (i : ℕ × ℕ) {x : VarSymb} {X : VarType}
    (hr : (w.L.ctx i).ref x = some (.VTypeDia X)) :
    ((model hO w₀).posEval ((canonEnvO hO w₀ w i).ref x hr)).1 = extentO w x := by
  rw [canonEnvO_ref]
  rfl

/-- The canonical environment at a later stage agrees with the one at an earlier stage. -/
theorem canonEnvO_le (w : World σ N₀) {i j : ℕ × ℕ} (hij : i ≤ j) :
    Model.Env.Agree (w.L.ctx_le hij) (canonEnvO hO w₀ w i) (canonEnvO hO w₀ w j) :=
  fun _ _ _ => toDomO_congr hO w₀ (rdenO_eta_le hO (w.L.ctx_le hij) _ _ _ _ _ _) _ _

/-- … and, in a world deciding its witnesses, in witnesses. -/
theorem canonEnvO_le_wit {w : World σ N₀} (hdec : DecidesO hO w) {i j : ℕ × ℕ} (hij : i ≤ j) :
    Model.Env.WitAgree (w.L.ctx_le hij) (canonEnvO hO w₀ w i) (canonEnvO hO w₀ w j) := by
  intro y X hy
  refine Part.ext' ⟨fun h => w.L.ctx_le hij _ _ h, fun h => hdec.ctx_stable hy h⟩
    fun _ _ => toDomO_congr hO w₀ (rdenO_eta_le hO (w.L.ctx_le hij) _ _ _ _ _ _) _ _

/-- Pushing the canonical environment into `□` at a child agrees with the child's. -/
theorem boxPush_agree_canonO (w : World σ N₀) (i : ℕ × ℕ) (a : SuccO hO w) :
    Model.Env.Agree (a.2.down.boxIn_le i) ((canonEnvO hO w₀ w i).boxPush a)
      (canonEnvO hO w₀ a.1 (childStage i)) := by
  intro v T hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      change (model hO w₀).necEval ((canonEnvO hO w₀ w i).ref u (Ctx.boxIn_step_box hv)) a = _
      rw [canonEnvO_ref]
      exact toDomO_congr hO w₀ ((rdenO_sigma hO _
        (Term.eta_congr (VarSymb.inner_box hk) T _ (Ctx.ref_boxIn_of hk hu))).trans
          (rdenO_eta_le hO (a.2.down.boxIn_le i) _ _ _ _ _ _)) _ _
  | .step _ .keep =>
      exact (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four (Ctx.boxIn_keep hv).1)).elim
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- ⭐**A witness read along the arrow to a child is present exactly when the child opened it**,
    with its content there. -/
theorem boxPush_witAgree_canonO (w : World σ N₀) (i : ℕ × ℕ) (a : SuccO hO w) :
    Model.Env.WitAgree (a.2.down.boxIn_le i) ((canonEnvO hO w₀ w i).boxPush a)
      (canonEnvO hO w₀ a.1 (childStage i)) := by
  intro y X hy
  have hr : (w.L.ctx i).ref y = some (.VTypeDia X) := (Ctx.boxIn_wit.mp hy).2
  have hM : (w.L.ctx i).boxIn.Le (bview w (max i.1 i.2)) := (le_diag_max w i).boxIn
  change (⟨a ∈ ((model hO w₀).posEval ((canonEnvO hO w₀ w i).ref y hr)).1,
    fun hm => ((model hO w₀).posEval ((canonEnvO hO w₀ w i).ref y hr)).2 ⟨a, hm⟩⟩ :
      Part ((frameO hO w₀).Dom X a.1)) = _
  rw [Model.posPart_congr (canonEnvO_ref hO w₀ w i y hr) a]
  refine Part.ext' ⟨fun hm => a.2.down.opened_at hm (hM.wit y X hy),
    fun hd => ⟨max i.1 i.2, X, hM.wit y X hy, hd⟩⟩ fun hm _ =>
      toDomO_congr hO w₀ (rdenO_eta_le hO (extentO_le hm (Ctx.Le.refl _) ⟨X, hr⟩) _ _ _ _ _ _) _ _

/-- Pushing the canonical environment into `◇_x` at a member of `x`'s extent agrees with the
    child's. -/
theorem diaPush_agree_canonO (w : World σ N₀) (i : ℕ × ℕ) {x : VarSymb} {X : VarType}
    (hr : (w.L.ctx i).ref x = some (.VTypeDia X))
    (a : ((model hO w₀).posEval ((canonEnvO hO w₀ w i).ref x hr)).1) :
    Model.Env.Agree (extentO_le (canonEnvO_extent hO w₀ w i hr ▸ a.2) (Ctx.Le.refl _) ⟨X, hr⟩)
      ((canonEnvO hO w₀ w i).diaPush x hr a) (canonEnvO hO w₀ a.1.1 (childStage i)) := by
  have hw : a.1 ∈ extentO w x := canonEnvO_extent hO w₀ w i hr ▸ a.2
  intro v T hv
  match v with
  | .step u .dia =>
      have hux : u = x := by
        change (if u = x then (match (w.L.ctx i).ref x with
          | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
        split_ifs at hv with hux
        exact hux
      subst hux
      have hTX : X = T := Ctx.diaIn_step_dia hr hv
      subst hTX
      have hpq := canonEnvO_ref hO w₀ w i u hr
      have hm : a.1 ∈ ((model hO w₀).posEval (toDomO hO w₀ (.VTypeDia X) w
          (rdenO hO w i (Ctx.Le.refl _) (Term.eta u (.VTypeDia X) hr)) (definableO_rden _ _))).1 :=
        hpq ▸ a.2
      change ((model hO w₀).posEval ((canonEnvO hO w₀ w i).ref u hr)).2 a = _
      rw [Model.posEval_snd_congr hpq a hm]
      exact toDomO_congr hO w₀ (rdenO_eta_le hO (extentO_le hw (Ctx.Le.refl _) ⟨X, hr⟩)
        _ _ _ _ _ _) _ _
  | .step u .box => exact boxPush_agree_canonO hO w₀ w i a.1 (.step u .box) T hv
  | .step u .keep => exact boxPush_agree_canonO hO w₀ w i a.1 (.step u .keep) T hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-! ## The truth lemma for terms -/

mutual
  theorem interpFunc_canonO : ∀ {Γ : Ctx} {n : ℕ} (g : Func σ Γ n) {w : World σ N₀}
      {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model hO w₀).Env Γ w},
      Model.Env.Agree e env (canonEnvO hO w₀ w i) →
      ∀ (args : Fin n → w.D) (ts : Fin n → Term σ Γ .Var .var),
        (∀ k, args k = w.cls i (Term.mono e (ts k))) →
        Model.interpFunc env g args = w.cls i (Term.mono e (.func ((Spine.ofFn ts).fill g)))
    | _, _, .F ⟨f, rfl⟩, w, i, e, env, _, args, ts, hts => by
        change canonFunc w f (fun k => args (Fin.cast rfl k)) = _
        rw [Term.mono_fill, Spine.mono_ofFn,
          show (fun k => args (Fin.cast rfl k)) = fun k => w.cls i (Term.mono e (ts k)) from
            funext fun k => hts k,
          canonFunc_cls]
        rfl
    | _, _, .eval g t, w, i, e, env, hag, args, ts, hts => by
        change Model.interpFunc env g (Fin.cons (Model.interp env t) args) = _
        have h0 : Model.interp env t = w.cls i (Term.mono e t) :=
          (interp_canon_baseO t hag).trans (rdenO_var_mono e t)
        rw [interpFunc_canonO g hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
          (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
        rfl
    termination_by _ _ g => g.size
    decreasing_by
      all_goals simp only [Func.size]
      all_goals omega

  /-- The truth lemma for base terms. -/
  theorem interp_canon_baseO : ∀ {Γ : Ctx} (t : Term σ Γ .Var .var) {w : World σ N₀}
      {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model hO w₀).Env Γ w},
      Model.Env.Agree e env (canonEnvO hO w₀ w i) →
      Model.interp env t = toDomO hO w₀ .Var w (rdenO hO w i e t) (definableO_rden e t)
    | _, .var v hv, w, i, e, env, hag => by
        change env.ref v hv = _
        rw [Model.Env.ref_agree hag v hv, canonEnvO_ref]
        rfl
    | _, .func f, _, _, _, env, hag => by
        change Model.interpFunc env f Fin.elim0 = _
        exact interpFunc_canonO f hag Fin.elim0 Fin.elim0 (fun k => k.elim0)
    termination_by _ t => t.size
    decreasing_by
      all_goals simp only [Term.size]
      all_goals omega
end

/-- ⭐**The truth lemma for terms**: in an environment agreeing with the canonical one, a term's
    value is its denotation. -/
theorem interp_canonO : ∀ {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {w : World σ N₀} {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model hO w₀).Env Γ w},
    Model.Env.Agree e env (canonEnvO hO w₀ w i) →
    Model.interp env t = toDomO hO w₀ A w (rdenO hO w i e t) (definableO_rden e t)
  | _, _, _, .var v hv, _, _, _, _, hag => interp_canon_baseO hO w₀ (Term.var v hv) hag
  | _, _, _, .func f, _, _, _, _, hag => interp_canon_baseO hO w₀ (Term.func f) hag
  | _, _, _, .unit, _, _, _, _, _ => rfl
  | _, _, _, .pair s t, _, _, _, _, hag => Prod.ext (interp_canonO s hag) (interp_canonO t hag)
  | _, _, _, .boxtm t, w, i, _, env, hag => by
      apply (model hO w₀).nec_inj
      funext a
      rw [Model.box_beta]
      exact interp_canonO t ((Model.Env.boxPush_agree hag a).trans
        (boxPush_agree_canonO hO w₀ w i a))
  | _, _, _, .diatm x hx t, w, i, e, env, hag => by
      obtain ⟨X, hr⟩ := hx
      refine (model hO w₀).pos_inj ?_
        fun hS => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_shaped hS)).elim
      rw [Model.dia_beta env ⟨X, hr⟩ hr t]
      have hpq₀ : env.ref x hr = (canonEnvO hO w₀ w i).ref x (e.ref hr) :=
        Model.Env.ref_agree hag x hr
      have hpq := hpq₀.trans (canonEnvO_ref hO w₀ w i x (e.ref hr))
      refine Model.posSec_ext hpq _ _ fun a => ?_
      have hm : a.1 ∈ ((model hO w₀).posEval ((canonEnvO hO w₀ w i).ref x (e.ref hr))).1 :=
        hpq₀ ▸ a.2
      exact interp_canonO t ((Model.Env.diaPush_agree hag hr a hm).trans
        (diaPush_agree_canonO hO w₀ w i (e.ref hr) ⟨a.1, hm⟩))
  termination_by _ _ _ t => t.size
  decreasing_by
    all_goals simp only [Term.size]
    all_goals omega

end OCanon

end V12M
