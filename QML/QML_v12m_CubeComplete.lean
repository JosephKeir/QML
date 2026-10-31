import QML.QML_v12m_NoBComplete
import QML.QML_v12m_BCompactness

/-!
# QML v12m — completeness across the cube

Every system with a canonical model, in one theorem.  `ModalSys.CubeSys` says which: 5 with 4 and
both of 4's lifts, B with 5 only under T, B with 4 only with 5, and strong B only with 4 off.  In a
well-formed presented context such a system has the metatheorems: a valid sequent is provable
(⭐`completenessCube`, and soundness with it, ⭐`provable_iff_validCube`), a consistent set is
satisfiable (`model_existenceCube`), and strong completeness and compactness
(`strong_completenessCube`, `compactnessCube`).

The canonical model is the cluster model with 5 (`GArrow.cmodel`, `GArrow.CluFlags`), the
arrow-based network with B and without 5 (`BArrow`, 4 off), and otherwise whatever `NoBComplete`
picks.

`ModalSys.S5`, every flag but strong B's, is one of them (`ModalSys.S5_cube`).
-/

namespace V12M

variable [ModalSys]

/-- ⭐**The systems with a canonical model.**  Not a statement of what is coherent, but of what is
    built: strong B with 5, B with 5 without T (KB5, KDB5), and 5 without both lifts are still to
    come.  `strongT` is `ModalSys.WCoh`, which the network asks for. -/
class ModalSys.CubeSys [ModalSys] : Prop where
  /-- 5 comes with 4 and both of 4's lifts. -/
  five_lifts : ModalSys.Five = true →
    ModalSys.Four = true ∧ ModalSys.FourStrong = true ∧ ModalSys.FourStrongW = true
  /-- B with 5 comes with T: the cluster has weak B through the root's own arrow. -/
  five_B : ModalSys.Five = true → ModalSys.B = true → ModalSys.T = true
  /-- B with 4 comes with 5. -/
  four_B : ModalSys.B = true → ModalSys.Four = true → ModalSys.Five = true
  /-- Strong B comes with weak B, and with 4 off. -/
  strongB : ModalSys.BStrong = true → ModalSys.B = true ∧ ModalSys.Four = false
  strongT : ModalSys.BStrongW = true → ModalSys.T = true → ModalSys.TStrong = true

/-- S5, with every strong form but strong B's. -/
def ModalSys.S5 : ModalSys :=
  { T := true, Four := true, TStrong := true, D := true, DStrong := true, B := true,
    BStrong := false, BStrongW := false, FourStrong := true, FourStrongW := true,
    Five := true, FiveStrong := true }

omit [ModalSys] in
/-- ⭐S5 is in the cube. -/
theorem ModalSys.S5_cube : @ModalSys.CubeSys ModalSys.S5 :=
  letI := ModalSys.S5
  { five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ _ => rfl
    four_B := fun _ _ => rfl
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun _ _ => rfl }

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.CubeSys]

/-- With 5 the cluster model applies. -/
theorem cluFlags_of_cube (hV : ModalSys.Five = true) : GArrow.CluFlags :=
  have h := ModalSys.CubeSys.five_lifts hV
  ⟨hV, h.2.1, h.2.2, ModalSys.CubeSys.five_B hV, Bool.eq_false_iff.mpr fun hS => by
    have := (ModalSys.CubeSys.strongB hS).2
    rw [h.1] at this
    cases this⟩

/-- With B and without 5 the network applies. -/
theorem noFour_of_cube (hV : ¬ ModalSys.Five = true) (hB : ModalSys.B = true) : ModalSys.NoFour :=
  { strongT := ModalSys.CubeSys.strongT
    noFour := Bool.eq_false_iff.mpr fun hF => hV (ModalSys.CubeSys.four_B hB hF)
    noFive := Bool.eq_false_iff.mpr hV }

/-- Without B and without 5, `NoBComplete` applies. -/
theorem noB_of_cube (hV : ¬ ModalSys.Five = true) (hB : ¬ ModalSys.B = true) : ModalSys.NoB :=
  { noB := Bool.eq_false_iff.mpr hB
    noBStrong := Bool.eq_false_iff.mpr fun hS => hB (ModalSys.CubeSys.strongB hS).1
    fiveCluster := fun h => absurd h hV }

/-- ⭐⭐**Completeness across the cube**: in a well-formed presented context, a sequent valid in
    every model is provable. -/
theorem completenessCube (e : CtxExpr) (he : e.Wf)
    {Δ : List (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env e.denote w),
      e.denote.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  by_cases hV : ModalSys.Five = true
  · exact GArrow.completenessC_presented (ModalSys.CubeSys.five_lifts hV).1 (cluFlags_of_cube hV)
      e he hval
  by_cases hB : ModalSys.B = true
  · haveI := noFour_of_cube hV hB
    exact BArrow.completenessB_presented hB e he hval
  · haveI := noB_of_cube hV hB
    exact completenessNoB e he hval

/-- ⭐⭐**Soundness and completeness across the cube**, in a well-formed presented context. -/
theorem provable_iff_validCube (e : CtxExpr) (he : e.Wf)
    {Δ : List (WFF σ e.denote 0)} {φ : WFF σ e.denote 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env e.denote w),
      e.denote.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ := by
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  exact ⟨fun ⟨p⟩ M hM _ env => Model.soundness p M hM env (Ctx.Presented.tame _),
    completenessCube e he⟩

/-- ⭐**Model existence across the cube.** -/
theorem model_existenceCube (e : CtxExpr) (he : e.Wf) {S : Set (WFF σ e.denote 0)}
    (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S := by
  by_cases hV : ModalSys.Five = true
  · exact GArrow.model_existenceC (ModalSys.CubeSys.five_lifts hV).1 (cluFlags_of_cube hV) e he hS
  by_cases hB : ModalSys.B = true
  · haveI := noFour_of_cube hV hB
    exact BArrow.model_existenceB hB e he hS
  · haveI := noB_of_cube hV hB
    exact model_existenceNoB e he hS

/-- ⭐**Strong completeness across the cube.** -/
theorem strong_completenessCube (e : CtxExpr) (he : e.Wf)
    {S : Set (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env e.denote w),
      (∀ ψ ∈ S, M.sat env ψ) → M.sat env φ) :
    ∃ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) ∧ Provable Δ φ := by
  by_cases hV : ModalSys.Five = true
  · exact GArrow.strong_completenessC (ModalSys.CubeSys.five_lifts hV).1 (cluFlags_of_cube hV)
      e he hval
  by_cases hB : ModalSys.B = true
  · haveI := noFour_of_cube hV hB
    exact BArrow.strong_completenessB hB e he hval
  · haveI := noB_of_cube hV hB
    exact strong_completenessNoB e he hval

/-- ⭐**Compactness across the cube**, in models of any universe. -/
theorem compactnessCube (e : CtxExpr) (he : e.Wf) {S : Set (WFF σ e.denote 0)}
    (hfin : ∀ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) →
      ∃ (M : Model.{u, v} σ) (_ : M.IndInvariant) (w : M.frame.W) (env : M.Env e.denote w),
        ∀ ψ ∈ Δ, M.sat env ψ) :
    WFF.SetSatisfiable S := by
  by_cases hV : ModalSys.Five = true
  · exact GArrow.compactnessC (ModalSys.CubeSys.five_lifts hV).1 (cluFlags_of_cube hV) e he hfin
  by_cases hB : ModalSys.B = true
  · haveI := noFour_of_cube hV hB
    exact BArrow.compactnessB hB e he hfin
  · haveI := noB_of_cube hV hB
    exact compactnessNoB e he hfin

end V12M
