import QML.QML_v12m_Compactness
import QML.QML_v12m_GFlat
import QML.QML_v12m_GCluCompleteness

/-!
# QML v12m — completeness for every system without B

With B off (`ModalSys.NoB`; T, D, 4 and 4's strong forms free, each strong form in either or both
forms; 5 with 4, both of 4's lifts and T off — K45 and KD45), every presented context whose
presentation is well-formed has the metatheorems: a valid sequent is provable
(⭐`completenessNoB`, and soundness with it, `provable_iff_validNoB`), a consistent set is
satisfiable (`model_existenceNoB`), and strong completeness and compactness
(`strong_completenessNoB`, `compactnessNoB`).  The canonical model is the cluster model with 5
(`GArrow.cmodel`), the growing tree with 4 and without 5 (`GArrow.gmodel`), and the staged tree
without 4 (`Canon`, where 4's strong forms say nothing, `ModalSys.StagedSys`; without 4 there is
no 5, `ModalSys.NoB.fiveCluster`).
-/

namespace V12M

variable [ModalSys]

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoB]

/-- Without 4 the staged canonical model applies: 5 is off, and 4's strong forms say nothing. -/
theorem stagedSys_of_noFour (hF : ¬ ModalSys.Four = true) : ModalSys.StagedSys :=
  { (inferInstance : ModalSys.NoB) with
    noFive := Bool.eq_false_iff.mpr fun hV => hF (ModalSys.NoB.fiveCluster hV).1
    noLift := fun h => absurd h hF }

/-- With 4 and without 5 the growing tree applies. -/
theorem growSys_of_noFive (hV : ¬ ModalSys.Five = true) : ModalSys.GrowSys :=
  { (inferInstance : ModalSys.NoB) with noFive := Bool.eq_false_iff.mpr hV }

/-- With 5 the cluster model applies. -/
theorem cluFlags_of_five (hV : ModalSys.Five = true) : GArrow.CluFlags :=
  have h := ModalSys.NoB.fiveCluster hV
  ⟨hV, h.2.1, h.2.2, fun hS => (ModalSys.NoB.absurdStrong hS).elim,
    fun hS => (ModalSys.NoB.absurdStrong hS).elim, fun hS => (ModalSys.NoB.absurdStrong hS).elim⟩

/-- ⭐**Completeness without B**: in a well-formed presented context, a sequent valid in every
    model is provable. -/
theorem completenessNoB (e : CtxExpr) (he : e.Wf)
    {Δ : List (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env e.denote w),
      e.denote.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  by_cases hF : ModalSys.Four = true
  · by_cases hV : ModalSys.Five = true
    · exact GArrow.completenessC_presented hF (cluFlags_of_five hV) e he hval
    · haveI := growSys_of_noFive hV
      exact GArrow.completenessG_presented hF e he hval
  · haveI := stagedSys_of_noFour hF
    letI : e.denote.Presented := ⟨e, he.1, rfl⟩
    exact completeness hval

/-- ⭐**Soundness and completeness without B**, in a well-formed presented context. -/
theorem provable_iff_validNoB (e : CtxExpr) (he : e.Wf)
    {Δ : List (WFF σ e.denote 0)} {φ : WFF σ e.denote 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env e.denote w),
      e.denote.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ := by
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  exact ⟨fun ⟨p⟩ M hM _ env => Model.soundness p M hM env (Ctx.Presented.tame _),
    completenessNoB e he⟩

/-- ⭐**Model existence without B.** -/
theorem model_existenceNoB (e : CtxExpr) (he : e.Wf) {S : Set (WFF σ e.denote 0)}
    (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S := by
  by_cases hF : ModalSys.Four = true
  · by_cases hV : ModalSys.Five = true
    · exact GArrow.model_existenceC hF (cluFlags_of_five hV) e he hS
    · haveI := growSys_of_noFive hV
      exact GArrow.model_existenceG hF e he hS
  · haveI := stagedSys_of_noFour hF
    letI : e.denote.Presented := ⟨e, he.1, rfl⟩
    exact model_existence hS

/-- ⭐**Strong completeness without B.** -/
theorem strong_completenessNoB (e : CtxExpr) (he : e.Wf)
    {S : Set (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env e.denote w),
      (∀ ψ ∈ S, M.sat env ψ) → M.sat env φ) :
    ∃ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) ∧ Provable Δ φ := by
  by_cases hF : ModalSys.Four = true
  · by_cases hV : ModalSys.Five = true
    · exact GArrow.strong_completenessC hF (cluFlags_of_five hV) e he hval
    · haveI := growSys_of_noFive hV
      exact GArrow.strong_completenessG hF e he hval
  · haveI := stagedSys_of_noFour hF
    letI : e.denote.Presented := ⟨e, he.1, rfl⟩
    exact strong_completeness hval

/-- ⭐**Compactness without B**, in models of any universe. -/
theorem compactnessNoB (e : CtxExpr) (he : e.Wf) {S : Set (WFF σ e.denote 0)}
    (hfin : ∀ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) →
      ∃ (M : Model.{u, v} σ) (_ : M.IndInvariant) (w : M.frame.W) (env : M.Env e.denote w),
        ∀ ψ ∈ Δ, M.sat env ψ) :
    WFF.SetSatisfiable S := by
  by_cases hF : ModalSys.Four = true
  · by_cases hV : ModalSys.Five = true
    · exact GArrow.compactnessC hF (cluFlags_of_five hV) e he hfin
    · haveI := growSys_of_noFive hV
      exact GArrow.compactnessG hF e he hfin
  · haveI := stagedSys_of_noFour hF
    letI : e.denote.Presented := ⟨e, he.1, rfl⟩
    exact compactness hfin

end V12M
