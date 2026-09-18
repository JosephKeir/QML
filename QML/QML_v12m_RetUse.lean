import QML.QML_v12m_Pack
import QML.QML_v12m_DiaAbs
import QML.QML_v12m_ProofSubst

/-!
# QML v12m — using a strong T hypothesis at a later stage

A `T_dia` hypothesis (`WFF.retHyp`) is added to the theory once, at the stage where the witness is
declared: for every value of the parameter `y : B`, what holds of `t` here holds of the witness
content in `◇_c`.  The canonical model must use it at every later stage, where the parameter's
value is a tuple of constants that did not exist yet.

* ⭐`WFF.instantiate_mono_retBody`: weakening the hypothesis to a later context and instantiating
  its `∀` at a term there gives the implication with that term substituted for the parameter — the
  antecedent read here, the consequent read inside `◇_c`.

The two readings keep the hole formula over `Δ.boxIn` (the later context *without* the witness):
the antecedent stays in the weakened form `WFF.weaken` that `WFF.retHyp` gives it, so both sides
mention the same substituted hole formula.
-/

namespace V12M

variable [ModalSys]

/-- The hole formula with the parameter instantiated: the substitution taken one view in, under
    the hole. -/
abbrev WFF.holeInst {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    (A : VarType) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF σ (Δ.boxIn.insert (.bnd 0) A) 1 :=
  WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
    (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
    (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
    (hΓ.boxIn.insert A) (hΔ.boxIn.insert A) ψ

/-- The body of a `T_dia` hypothesis, under its `∀`. -/
def WFF.retBody {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) (c y : ℕ) (hc : Γ.RootFresh (.free c))
    (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c) (B : VarType)
    (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1) :
    WFF σ ((Γ.insert (.free c) (.VTypeDia A)).insert (.bnd 0) B) 1 :=
  have hne : Root.free y ≠ Root.free c := fun h => hyc (Root.free.inj h)
  have hcy : (Γ.insert (.free y) B).RootFresh (.free c) := hc.insert_ne hne B
  WFF.bindFree y (hy.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots B
    (WFF.mono (Ctx.insert_swap_le hne B (.VTypeDia A))
      (WFF.imp
        ((WFF.hereRead hT (Term.mono (Ctx.le_insert hy.root B) t) ψ).weaken hcy.root
          (.VTypeDia A))
        (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root _ (.free c) (.VTypeDia A)⟩
          (WFF.viewRead c hcy A ψ))))

theorem WFF.retHyp_eq {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) (c y : ℕ) (hc : Γ.RootFresh (.free c))
    (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c) (B : VarType)
    (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1) :
    WFF.retHyp hT t c y hc hy hyc B ψ = .all B (WFF.retBody hT t c y hc hy hyc B ψ) := rfl

/-- Substituting a term for the parameter, as a substitution of the later context. -/
abbrev Subst.paramS {σ : Signature} {Δ : Ctx} (y : ℕ) {B : VarType} {b : Ann B}
    (s : Term σ Δ B b) : Subst σ Δ := Subst.single (.free y) (.tm s)

/-- Substituting for the parameter in the context that has just declared the witness is the
    witness-preserving rename of the substitution below it. -/
theorem Subst.single_eq_rename {σ : Signature} {Δ : Ctx} {y c : ℕ} (hyc : y ≠ c) {A B : VarType}
    {b : Ann B} (s : Term σ Δ B b) (h : Δ (.root (.free c)) = none) :
    Subst.single (σ := σ) (Δ := Δ.insert (.free c) (.VTypeDia A)) (.free y)
        (.tm (Term.mono (Ctx.le_insert h (.VTypeDia A)) s)) =
      Subst.rename (Subst.paramS y s) c c (.VTypeDia A) h := by
  funext v
  by_cases hvc : v = .root (.free c)
  · subst hvc
    rw [Subst.rename_root]
    exact if_neg (fun he => hyc (Root.free.inj (VarSymb.root.inj he)).symm)
  · rw [Subst.rename_ne _ c (.VTypeDia A) h hvc]
    by_cases hvy : v = .root (.free y)
    · subst hvy
      rw [show Subst.single (σ := σ) (Δ := Δ.insert (.free c) (.VTypeDia A)) (.free y)
          (.tm (Term.mono (Ctx.le_insert h (.VTypeDia A)) s)) (.root (.free y)) =
          .tm (Term.mono (Ctx.le_insert h (.VTypeDia A)) s) from if_pos rfl,
        show Subst.paramS (σ := σ) (Δ := Δ) y s (.root (.free y)) = .tm s from if_pos rfl]
      rfl
    · rw [show Subst.single (σ := σ) (Δ := Δ.insert (.free c) (.VTypeDia A)) (.free y)
          (.tm (Term.mono (Ctx.le_insert h (.VTypeDia A)) s)) v = .ren v from if_neg hvy,
        show Subst.paramS (σ := σ) (Δ := Δ) y s v = .ren v from if_neg hvy]
      rfl

/-- ⭐Weakening a `T_dia` hypothesis to a later context and instantiating its `∀` at a term there:
    the parameter is substituted by that term, in the reading here and in the reading inside
    `◇_c` alike. -/
theorem WFF.instantiate_mono_retBody {σ : Signature} {Γ Δ : Ctx}
    [Γ.NoSlots] [Δ.NoSlots] (hT : ModalSys.T = true) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (c y : ℕ) (hc : Γ.RootFresh (.free c)) (hy : Γ.RootFresh (.free y)) (hyc : y ≠ c)
    (B : VarType) (ψ : WFF σ ((Γ.insert (.free y) B).boxIn.insert (.bnd 0) A) 1)
    (hle : Γ.Le Δ) (hcΔ : Δ.RootFresh (.free c)) {b : Ann B} (s : Term σ Δ B b) :
    WFF.instantiate Ctx.NoSlots.slots (Term.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)) s)
        (WFF.mono ((hle.insert (.free c) (.VTypeDia A)).insert (.bnd 0) B)
          (WFF.retBody hT t c y hc hy hyc B ψ)) =
      .imp
        ((WFF.hereRead hT
            (Term.subst (Subst.singleIdx (.free y) (.tm s)) (Subst.paramS y s)
              (Subst.ok_single (T := B) (e := SubE.tm s) hle rfl)
              (Subst.coh_single (T := B) (e := SubE.tm s) hy hle rfl)
              (Term.mono (Ctx.le_insert hy.root B) t))
            (WFF.holeInst (Subst.paramS y s) (Subst.ok_single (T := B) (e := SubE.tm s) hle rfl)
              (Subst.coh_single (T := B) (e := SubE.tm s) hy hle rfl) Ctx.NoSlots.slots
              Ctx.NoSlots.slots A ψ)).weaken
          hcΔ.root (.VTypeDia A))
        (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root Δ (.free c) (.VTypeDia A)⟩
          (WFF.viewRead c hcΔ A
            (WFF.holeInst (Subst.paramS y s) (Subst.ok_single (T := B) (e := SubE.tm s) hle rfl)
              (Subst.coh_single (T := B) (e := SubE.tm s) hy hle rfl) Ctx.NoSlots.slots
              Ctx.NoSlots.slots A ψ))) := by
  have hne : Root.free y ≠ Root.free c := fun h => hyc (Root.free.inj h)
  have hcy : (Γ.insert (.free y) B).RootFresh (.free c) := hc.insert_ne hne B
  -- Binding the parameter and instantiating it is substituting the term for it.
  rw [show WFF.retBody hT t c y hc hy hyc B ψ =
      WFF.bindFree y (hy.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots B
        (WFF.mono (Ctx.insert_swap_le hne B (.VTypeDia A))
          (WFF.imp
            ((WFF.hereRead hT (Term.mono (Ctx.le_insert hy.root B) t) ψ).weaken hcy.root
              (.VTypeDia A))
            (.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root _ (.free c) (.VTypeDia A)⟩
              (WFF.viewRead c hcy A ψ)))) from rfl,
    WFF.instantiate_mono_bindFree (hle.insert (.free c) (.VTypeDia A)) y
      (hy.insert_ne hne.symm (.VTypeDia A)) Ctx.NoSlots.slots Ctx.NoSlots.slots
      (Term.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)) s),
    WFF.subst_mono (hΓ := Ctx.NoSlots.slots) (Ctx.insert_swap_le hne B (.VTypeDia A))]
  -- The same substitution, seen as the rename that keeps the witness.
  have hok : Subst.Ok (Γ.insert (.free y) B) (Subst.paramS (σ := σ) y s) :=
    Subst.ok_single (T := B) (e := SubE.tm s) hle rfl
  have hcoh : Subst.Coh (Subst.singleIdx (.free y) (.tm s)) (Γ.insert (.free y) B)
      (Subst.paramS (σ := σ) y s) := Subst.coh_single (T := B) (e := SubE.tm s) hy hle rfl
  refine (WFF.subst_congr _ (Subst.rename (Subst.paramS y s) c c (.VTypeDia A) hcΔ.root) _
    (Subst.ok_rename hok (.VTypeDia A) hcΔ.root) _
    (Subst.coh_rename hok hcoh hcy (.VTypeDia A) hcΔ.root)
    Ctx.NoSlots.slots Ctx.NoSlots.slots
    (Subst.sim_of (fun v _ _ _ => by rw [Subst.single_eq_rename hyc s hcΔ.root]; exact .refl _))
    _).trans ?_
  refine congrArg₂ WFF.imp ?_ ?_
  · -- What holds of `t` here: the weakening comes out, and the reading here substitutes.
    refine (WFF.subst_mono_eq (Ctx.le_insert hcy.root (.VTypeDia A))
      (Ctx.le_insert hcΔ.root (.VTypeDia A)) (Subst.paramS y s) hok hcoh _ _ _
      Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots
      (Subst.sim_rename_mono hcy (.VTypeDia A) hcΔ.root) _).trans ?_
    exact congrArg (WFF.mono (Ctx.le_insert hcΔ.root (.VTypeDia A)))
      (WFF.subst_hereRead hT (Subst.paramS y s) hok hcoh Ctx.NoSlots.slots Ctx.NoSlots.slots _ ψ)
  · -- What the witness content satisfies in its view: the reading inside `◇_c` substitutes.
    exact WFF.subst_diaViewRead (Subst.paramS y s) hok hcoh Ctx.NoSlots.slots Ctx.NoSlots.slots
      hcy hcΔ A ψ

end V12M
