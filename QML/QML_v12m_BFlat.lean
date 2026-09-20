import QML.QML_v12m_BRename

/-!
# QML v12m — flattening a context into a world language

`completenessB` speaks of a world language `ctxOf l`, whose variables are roots.  A presented
context may instead show **view items** (`u.box`, `x.dia`).  This file carries completeness across
such a translation.

* ⭐`Flat σ Γ Δ`: a translation of `Γ`'s formulas into `Δ` that provability follows backwards
  (`prov`) and truth follows along an environment map (`sat`).  Translations compose (`Flat.comp`),
  so a presentation can be flattened one constructor at a time.
* ⭐`Flat.ofPair`: a substitution and an inverse substitution that cancel give one — provability by
  `Proof.subst`, truth by `Model.sat_subst`.
* ⭐`completenessB_flat`: completeness for any context flattened into a world language.
* The arrow into a new child already is such a pair (`subst_pull_arrow`), so a `□` view over a
  world language is flattened by it (`flatBox`), and a `◇_x` view by the witness arrow
  (`flatDia`) — giving `completenessB_boxIn` and `completenessB_diaIn`.

Composing these for an arbitrary presentation needs two more pairs: one for a root declared after
a view, and the push of a pair under a view.  Neither is here yet.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Translations that carry completeness -/

/-- ⭐A translation of `Γ` into `Δ`: provability comes back along it, and truth travels with an
    environment map. -/
structure Flat (σ : Signature) (Γ Δ : Ctx) where
  /-- The translation of formulas. -/
  tr : WFF σ Γ 0 → WFF σ Δ 0
  /-- A proof of the translated sequent gives one of the original. -/
  prov : ∀ {Δs : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}, Provable (Δs.map tr) (tr φ) → Provable Δs φ
  /-- An environment of `Δ` reads as one of `Γ`. -/
  env : {M : Model.{0, 0} σ} → {w : M.frame.W} → M.Env Δ w → M.Env Γ w
  /-- The translation is truth-preserving. -/
  sat : ∀ {M : Model.{0, 0} σ} {w : M.frame.W} (e : M.Env Δ w) (φ : WFF σ Γ 0),
    M.sat e (tr φ) ↔ M.sat (env e) φ

/-- Translations compose. -/
def Flat.comp {Γ Δ E : Ctx} (F : Flat σ Γ Δ) (G : Flat σ Δ E) : Flat σ Γ E where
  tr := G.tr ∘ F.tr
  prov {Δs φ} h := F.prov (G.prov (by rw [← List.map_map] at h; exact h))
  env e := F.env (G.env e)
  sat e φ := (G.sat e (F.tr φ)).trans (F.sat (G.env e) φ)

/-- ⭐A substitution with an inverse that cancels it is a translation. -/
def Flat.ofPair {Γ Δ : Ctx} [Γ.Presented] [Δ.NoSlots] (hnp : Γ.NoProjLast)
    {ι ι' : VarSymb → VarSymb} (θ : Subst σ Δ) (θ' : Subst σ Γ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hθ' : Subst.Ok Δ θ') (hc' : Subst.Coh ι' Δ θ')
    (cancel : ∀ φ : WFF σ Γ 0,
      WFF.subst ι' θ' hθ' hc' Ctx.NoSlots.slots Ctx.NoSlots.slots
        (WFF.subst ι θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ) = φ) :
    Flat σ Γ Δ where
  tr := WFF.subst ι θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots
  prov {Δs φ} h := by
    obtain ⟨p⟩ := h
    have hq := Proof.subst p θ' hθ' hc' Ctx.NoSlots.slots
    rw [List.map_map] at hq
    simp only [Function.comp_def, cancel] at hq
    rw [show (fun x : WFF σ Γ 0 => x) = id from rfl, List.map_id] at hq
    exact ⟨hq⟩
  env e := Model.substEnv θ hθ hnp e
  sat e φ := Model.sat_subst θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots hnp e φ

variable [ModalSys.NoTFour]

/-! ## Pairs of substitutions, and pushing them under a view -/

/-- A substitution similar to the identity stays so under `□`. -/
theorem sim_box_of {Γ : Ctx} {θ : Subst σ Γ} (h : Subst.Sim Γ θ (Subst.idS σ Γ)) :
    Subst.Sim Γ.boxIn θ.box (Subst.idS σ Γ.boxIn) := by
  have hk := ModalSys.NoTFour.keepOnly
  refine Subst.sim_of ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨_, hu⟩ := Ctx.boxIn_box hv
      have hs := (h u _ hu).unbox
      rw [Subst.at_idS] at hs
      change SubE.Sim T ((θ.at u).unbox) (.ren (.step u .box))
      rw [← VarSymb.inner_box hk]
      exact hs
  | .step u .keep =>
      obtain ⟨hF, _⟩ := Ctx.boxIn_keep hv
      exact absurd (ModalSys.NoTFour.noFour.symm.trans hF) (by simp)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- ⭐A substitution with an inverse that cancels it up to `Sim`: the data a `Flat` is built from,
    kept so that it can be pushed under a view. -/
structure Pair (σ : Signature) (Γ Δ : Ctx) where
  /-- The index map of the translation. -/
  ι : VarSymb → VarSymb
  /-- The index map of the translation back. -/
  ι' : VarSymb → VarSymb
  /-- The index map of the composite. -/
  ι₃ : VarSymb → VarSymb
  /-- The translation into `Δ`. -/
  θ : Subst σ Δ
  /-- The translation back. -/
  θ' : Subst σ Γ
  /-- A substitution of `Γ` standing for the composite. -/
  θ₃ : Subst σ Γ
  hθ : Subst.Ok Γ θ
  hc : Subst.Coh ι Γ θ
  hθ' : Subst.Ok Δ θ'
  hc' : Subst.Coh ι' Δ θ'
  hθ₃ : Subst.Ok Γ θ₃
  hc₃ : Subst.Coh ι₃ Γ θ₃
  /-- Going and coming back is the composite. -/
  sim : Subst.Sim Γ θ₃ (θ.comp θ' hθ' hc')
  /-- And the composite is the identity. -/
  simId : Subst.Sim Γ θ₃ (Subst.idS σ Γ)

variable {Γ Δ : Ctx}

omit [ModalSys.NoTFour] in
/-- The two substitutions of a pair cancel. -/
theorem Pair.cancel [Γ.NoSlots] [Δ.NoSlots] (P : Pair σ Γ Δ) (φ : WFF σ Γ 0) :
    WFF.subst P.ι' P.θ' P.hθ' P.hc' Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.subst P.ι P.θ P.hθ P.hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ) = φ := by
  refine (WFF.subst_comp _ _ P.θ₃ _ _ _ _ P.hθ₃ P.hc₃ _ _ _ P.sim φ).trans ?_
  refine (WFF.subst_congr _ _ _ Subst.ok_idS _ Subst.coh_idS _ _ P.simId φ).trans ?_
  exact WFF.subst_id _ _ _ φ

/-- A pair is a translation. -/
def Pair.toFlat [Γ.Presented] [Δ.NoSlots] (P : Pair σ Γ Δ) (hnp : Γ.NoProjLast) :
    Flat σ Γ Δ :=
  Flat.ofPair hnp P.θ P.θ' P.hθ P.hc P.hθ' P.hc' P.cancel

/-- ⭐A pair pushed under `□`. -/
def Pair.box (P : Pair σ Γ Δ) : Pair σ Γ.boxIn Δ.boxIn where
  ι := P.ι
  ι' := P.ι'
  ι₃ := P.ι₃
  θ := P.θ.box
  θ' := P.θ'.box
  θ₃ := P.θ₃.box
  hθ := Subst.ok_box P.hθ
  hc := Subst.coh_box P.hθ P.hc
  hθ' := Subst.ok_box P.hθ'
  hc' := Subst.coh_box P.hθ' P.hc'
  hθ₃ := Subst.ok_box P.hθ₃
  hc₃ := Subst.coh_box P.hθ₃ P.hc₃
  sim := Subst.sim_box_comp P.hθ P.hθ' P.hc' P.sim
  simId := sim_box_of P.simId

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐**Completeness for weak B in any context flattened into a world language.** -/
theorem completenessB_flat (hB : ModalSys.B = true) {Γ : Ctx} {l : List VarType}
    (F : Flat σ Γ (ctxOf l)) (hnp : Γ.NoProjLast) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (hval : ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env Γ w), Γ.NoProjLast →
      (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  refine F.prov (completenessB hB ?_)
  intro M w e _ hΔ
  rw [F.sat]
  exact hval M _ hnp fun ψ hψ => (F.sat e ψ).mp (hΔ _ (List.mem_map_of_mem hψ))

/-! ## Views over a world language -/

/-- ⭐A `□` view over a world language is flattened by the arrow into a new child. -/
def flatBox (l : List VarType) : Flat σ (ctxOf l).boxIn (ctxOf (l.map VarType.bc)) :=
  Flat.ofPair (Ctx.noProjLast_boxIn _) _ (pullS σ l) (ok_arrowS (childImg l))
    (coh_arrowS (childImg l)) (ok_pullS l) (coh_pullS l) (subst_pull_arrow l)

/-- ⭐A `◇_x` view over a world language is flattened by the witness arrow. -/
noncomputable def flatDia (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Flat σ ((ctxOf l).diaIn x) (ctxOf (X :: l.map VarType.bc)) :=
  Flat.ofPair (Ctx.noProjLast_diaIn _ x) _ (pullXS σ l x) (ok_arrowXS (childXImg l X) hx
    (childX_cx l X)) (coh_arrowXS (childXImg l X) hx (childX_cx l X)) (ok_pullXS l hx)
    (coh_pullXS l hx) (subst_pullX_arrowX l hx)

/-- ⭐Completeness in the `□` view of a world language. -/
theorem completenessB_boxIn (hB : ModalSys.B = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l).boxIn 0)} {φ : WFF σ (ctxOf l).boxIn 0}
    (hval : ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env (ctxOf l).boxIn w),
      (ctxOf l).boxIn.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ :=
  completenessB_flat hB (flatBox l) (Ctx.noProjLast_boxIn _) hval

/-- ⭐Completeness in the `◇_x` view of a world language. -/
theorem completenessB_diaIn (hB : ModalSys.B = true) {l : List VarType} {x : VarSymb}
    {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {Δ : List (WFF σ ((ctxOf l).diaIn x) 0)} {φ : WFF σ ((ctxOf l).diaIn x) 0}
    (hval : ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env ((ctxOf l).diaIn x) w),
      ((ctxOf l).diaIn x).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ :=
  completenessB_flat hB (flatDia l hx) (Ctx.noProjLast_diaIn _ x) hval

end BArrow

end V12M
