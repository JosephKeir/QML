import QML.QML_v12_CanonModel

/-!
# QML v12 — the canonical model: the truth lemma for terms

The **canonical environment** at stage `i` of a world gives every visible address the frame object
of its η-expansion (`canonEnv`); so does its reading of every reachable address (`canonEnv_ref`).
Entering a modality from it agrees with the canonical environment of the successor
(`boxPush_agree_canon`, `diaPush_agree_canon`).

⭐`interp_canon`: in any environment agreeing with the canonical one, a term's value is its
denotation.
-/

namespace V12

theorem Model.Env.Agree.trans {σ : Signature} {M : Model.{u} σ} {Γ₁ Γ₂ Γ₃ : Ctx}
    {h₁ : Γ₁.Le Γ₂} {h₂ : Γ₂.Le Γ₃} {w : M.frame.W} {e₁ : M.Env Γ₁ w} {e₂ : M.Env Γ₂ w}
    {e₃ : M.Env Γ₃ w} (a : Model.Env.Agree h₁ e₁ e₂) (b : Model.Env.Agree h₂ e₂ e₃) :
    Model.Env.Agree (h₁.trans h₂) e₁ e₃ :=
  fun v T hv => (a v T hv).trans (b v T (h₁ v T hv))

theorem Spine.ofFn_cons {σ : Signature} {Δ : Ctx} {n : ℕ} (t : Term σ Δ .Var .var)
    (ts : Fin n → Term σ Δ .Var .var) :
    Spine.ofFn (Fin.cons t ts : Fin (n + 1) → Term σ Δ .Var .var) = .cons t (Spine.ofFn ts) := by
  change Spine.cons ((Fin.cons t ts : Fin (n + 1) → Term σ Δ .Var .var) 0)
    (Spine.ofFn fun k => (Fin.cons t ts : Fin (n + 1) → Term σ Δ .Var .var) k.succ) = _
  simp only [Fin.cons_zero, Fin.cons_succ]

namespace Canon

variable {σ : Signature} {N₀ : ℕ} (w₀ : World σ N₀)

/-- The denotations of the η-expansions of an address in two nested contexts agree. -/
theorem rden_eta_le {Γ₁ Γ₂ : Ctx} (h : Γ₁.Le Γ₂) {w : World σ N₀} {i j : ℕ × ℕ}
    (e₁ : Γ₁.Le (w.L.ctx i)) (e₂ : Γ₂.Le (w.L.ctx j)) (v : VarSymb) (T : VarType)
    (p₁ : Γ₁.ref v = some T) (p₂ : Γ₂.ref v = some T) :
    rden w i e₁ (Term.eta (σ := σ) v T p₁) = rden w j e₂ (Term.eta v T p₂) := by
  rw [show Term.eta (σ := σ) v T p₂ = Term.mono h (Term.eta v T p₁) from
    (Term.mono_eta h v T p₁).symm, rden_mono]
  exact rden_congr _ _ _ _ _ _

theorem World.noProdLast (w : World σ N₀) (i : ℕ × ℕ) : (w.L.ctx i).NoProdLast :=
  Ctx.Presented.noProdLast _

/-- ⭐The canonical environment: every visible address denotes its η-expansion. -/
noncomputable def canonEnv (w : World σ N₀) (i : ℕ × ℕ) : (model w₀).Env (w.L.ctx i) w :=
  fun v T hv => toDom w₀ T w
    (rden w i (Ctx.Le.refl _) (Term.eta v T ((Ctx.ref_nonprod _ (w.noProdLast i v T hv)).trans hv)))
    (definable_rden _ _)

/-- Every reachable address reads as its η-expansion. -/
theorem canonEnv_ref (w : World σ N₀) (i : ℕ × ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : (w.L.ctx i).ref v = some T),
      (canonEnv w₀ w i).ref v h =
        toDom w₀ T w (rden w i (Ctx.Le.refl _) (Term.eta v T h)) (definable_rden _ _)
  | .root _, _, _ => rfl
  | .step v s, T, h => by
      by_cases hs : s.isProd = true
      · rw [Model.Env.ref, dif_pos hs]
        split
        · rename_i U hU
          rw [canonEnv_ref w i v hU]
          have hT : U.step s = some T := by
            rw [Ctx.ref_step_prod _ _ hs, hU] at h
            exact h
          cases U <;> cases s <;>
            simp only [VarType.step, Step.isProd, reduceCtorEq, Option.some.injEq,
              Bool.false_eq_true] at hT hs
          · subst hT
            rfl
          · subst hT
            rfl
        · rename_i hU
          rw [Ctx.ref_step_prod _ _ hs, hU] at h
          cases h
      · rw [Model.Env.ref, dif_neg hs]
        rfl

theorem canonEnv_extent (w : World σ N₀) (i : ℕ × ℕ) {x : VarSymb} {X : VarType}
    (hr : (w.L.ctx i).ref x = some (.VTypeDia X)) :
    ((model w₀).posEval ((canonEnv w₀ w i).ref x hr)).1 = extent w x := by
  rw [canonEnv_ref]
  rfl

/-- Pushing the canonical environment into `□` agrees with the successor's. -/
theorem boxPush_agree_canon (w : World σ N₀) (i : ℕ × ℕ) (w' : Succ w) :
    Model.Env.Agree (w'.2.boxIn_le i) ((canonEnv w₀ w i).boxPush w')
      (canonEnv w₀ w'.1 (childStage i)) := by
  intro v T hv
  match v with
  | .step u .box =>
      change (model w₀).necEval ((canonEnv w₀ w i).ref u (Ctx.boxIn_step_box hv)) w' = _
      rw [canonEnv_ref]
      exact toDom_congr w₀ (rden_eta_le (w'.2.boxIn_le i) _ _ _ _ _ _) _ _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

/-- Pushing the canonical environment into `◇_x` agrees with the successor's. -/
theorem diaPush_agree_canon (w : World σ N₀) (i : ℕ × ℕ) {x : VarSymb} {X : VarType}
    (hr : (w.L.ctx i).ref x = some (.VTypeDia X))
    (w' : ((model w₀).posEval ((canonEnv w₀ w i).ref x hr)).1) :
    Model.Env.Agree (extent_le (canonEnv_extent w₀ w i hr ▸ w'.2) i)
      ((canonEnv w₀ w i).diaPush x hr w') (canonEnv w₀ w'.1.1 (childStage i)) := by
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
      have hpq := canonEnv_ref w₀ w i u hr
      have hm : w'.1 ∈ ((model w₀).posEval (toDom w₀ (.VTypeDia X) w
          (rden w i (Ctx.Le.refl _) (Term.eta u (.VTypeDia X) hr)) (definable_rden _ _))).1 :=
        hpq ▸ w'.2
      change ((model w₀).posEval ((canonEnv w₀ w i).ref u hr)).2 w' = _
      rw [Model.posEval_snd_congr hpq w' hm]
      exact toDom_congr w₀ (rden_eta_le (extent_le (canonEnv_extent w₀ w i hr ▸ w'.2) i)
        _ _ _ _ _ _) _ _
  | .step u .box => exact boxPush_agree_canon w₀ w i w'.1 (.step u .box) T hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

/-! ## The truth lemma for terms -/

mutual
  theorem interpFunc_canon : ∀ {Γ : Ctx} {n : ℕ} (g : Func σ Γ n) {w : World σ N₀}
      {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w},
      Model.Env.Agree e env (canonEnv w₀ w i) →
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
          (interp_canon t hag).trans (rden_var_mono e t)
        rw [interpFunc_canon g hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
          (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
        rfl
    termination_by structural _ _ g => g

  /-- ⭐In an environment agreeing with the canonical one, a term's value is its denotation. -/
  theorem interp_canon : ∀ {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
      {w : World σ N₀} {i : ℕ × ℕ} {e : Γ.Le (w.L.ctx i)} {env : (model w₀).Env Γ w},
      Model.Env.Agree e env (canonEnv w₀ w i) →
      Model.interp env t = toDom w₀ A w (rden w i e t) (definable_rden e t)
    | _, _, _, .var v hv, w, i, e, env, hag => by
        change env.ref v hv = _
        rw [Model.Env.ref_agree hag v hv, canonEnv_ref]
        rfl
    | _, _, _, .func f, _, _, _, env, hag => by
        change Model.interpFunc env f Fin.elim0 = _
        exact interpFunc_canon f hag Fin.elim0 Fin.elim0 (fun k => k.elim0)
    | _, _, _, .unit, _, _, _, _, _ => rfl
    | _, _, _, .pair s t, _, _, _, _, hag => Prod.ext (interp_canon s hag) (interp_canon t hag)
    | _, _, _, .boxtm t, w, i, _, env, hag => by
        apply (model w₀).nec_inj
        funext w'
        rw [Model.box_beta]
        exact interp_canon t ((Model.Env.boxPush_agree hag w').trans
          (boxPush_agree_canon w₀ w i w'))
    | _, _, _, .diatm x hx t, w, i, e, env, hag => by
        obtain ⟨X, hr⟩ := hx
        apply (model w₀).pos_inj
        rw [Model.dia_beta env ⟨X, hr⟩ hr t]
        have hpq₀ : env.ref x hr = (canonEnv w₀ w i).ref x (e.ref hr) :=
          Model.Env.ref_agree hag x hr
        have hpq := hpq₀.trans (canonEnv_ref w₀ w i x (e.ref hr))
        refine Model.posSec_ext hpq _ _ fun w' => ?_
        have hm : w'.1 ∈ ((model w₀).posEval ((canonEnv w₀ w i).ref x (e.ref hr))).1 :=
          hpq₀ ▸ w'.2
        exact interp_canon t ((Model.Env.diaPush_agree hag hr w' hm).trans
          (diaPush_agree_canon w₀ w i (e.ref hr) ⟨w'.1, hm⟩))
    termination_by structural _ _ _ t => t
end

end Canon

end V12
