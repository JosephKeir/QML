import QML.QML_v12m_NoBComplete
import QML.QML_v12m_BCompactness

/-!
# QML v12m — completeness across the cube

Every system with a canonical model, in one theorem.  `ModalSys.CubeSys` says which: 5 with 4 and
both of 4's lifts in force, by flag or under T, B with 4 only with 5, strong B with weak B, and
with 5 only under T.  In a
well-formed presented context such a system has the metatheorems: a valid sequent is provable
(⭐`completenessCube`, and soundness with it, ⭐`provable_iff_validCube`), a consistent set is
satisfiable (`model_existenceCube`), and strong completeness and compactness
(`strong_completenessCube`, `compactnessCube`).

The canonical model is the cluster model with 5 (`GArrow.cmodel`, `GArrow.CluFlags`), the
arrow-based network with B and without 5 (`BArrow`, 4 off), and otherwise whatever `NoBComplete`
picks.

`ModalSys.S5`, every flag but strong B's, is one of them (`ModalSys.S5_cube`), and so is
`ModalSys.S5Strong`, every flag (`ModalSys.S5Strong_cube`).  Under T + 5 the lifts are derivable
(`Proof.keep_lift_T`, `Proof.keep_lift_posT`), so S5 needs neither flag: `ModalSys.S5NoLift`, weak
everything, and `ModalSys.S5StrongNoLift`, every flag but the lifts.  So are KB5 and KDB5
(`ModalSys.KB5_cube`, `ModalSys.KDB5_cube`), T off: the root has its self-arrow, or none is needed.
-/

namespace V12M

variable [ModalSys]

/-- ⭐**Strong B collapses the arrows**: with 4, an arrow out of `w` and strong B, out and home
    is an arrow `w → w` meeting T's frame laws (`refl_trans`, `trans_refl`, `side_refl`), arrows
    being unique.  So strong B's frames with 5 are S5's, but for dead ends
    (`Frame.exists_unit_of_serial`): why `CubeSys.five_B` costs KDB5 nothing. -/
theorem Frame.exists_unit {σ : Signature} (F : Frame σ) (hF : ModalSys.Four = true)
    (hB : ModalSys.B = true) (hS : ModalSys.BStrong = true) {w v : F.W} (a : F.R w v) :
    ∃ e : F.R w w, (∀ {t : F.W} (b : F.R w t), F.trans hF e b = b) ∧
      (∀ {t : F.W} (c : F.R t w), F.trans hF c e = c) ∧
      ∀ (hV : ModalSys.Five = true) {t : F.W} (b : F.R w t), F.side hV e b = b := by
  obtain ⟨r⟩ := F.symm hB a
  have hu : ∀ {x y : F.W}, Subsingleton (F.R x y) := F.homeUnique hS
  exact ⟨F.trans hF a r, fun _ => hu.elim _ _, fun _ => hu.elim _ _, fun _ {_} _ => hu.elim _ _⟩

/-- Under D, `Frame.exists_unit` at every world: KDB5 with strong B has S5's frames. -/
theorem Frame.exists_unit_of_serial {σ : Signature} (F : Frame σ) (hD : ModalSys.D = true)
    (hF : ModalSys.Four = true) (hB : ModalSys.B = true) (hS : ModalSys.BStrong = true) (w : F.W) :
    ∃ e : F.R w w, (∀ {t : F.W} (b : F.R w t), F.trans hF e b = b) ∧
      (∀ {t : F.W} (c : F.R t w), F.trans hF c e = c) ∧
      ∀ (hV : ModalSys.Five = true) {t : F.W} (b : F.R w t), F.side hV e b = b := by
  obtain ⟨v, ⟨a⟩⟩ := F.serial hD w
  exact F.exists_unit hF hB hS a

/-- With 4 and 5, `side` composes: `(side x y) ; (side y z) = side x z`. -/
theorem Frame.side_cocycle {σ : Signature} (F : Frame σ) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) {w u v t : F.W} (x : F.R w u) (y : F.R w v) (z : F.R w t) :
    F.trans hF (F.side hV x y) (F.side hV y z) = F.side hV x z := by
  have h := F.trans_side hF hV (F.side hV x y) (F.side hV x z)
  rwa [F.side_side hV x y z] at h

/-- ⭐**`side a a` is a left unit**, in every frame with 4 and 5, relational or not, and `a` followed
    by it is `a`.  So at every world an arrow reaches, `□φ̂(k) → φ(k)` holds: `Proof.loop_tup`'s
    statement is valid with no lift (docs, "The countermodel check"). -/
theorem Frame.side_self_unit {σ : Signature} (F : Frame σ) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) {w v t : F.W} (a : F.R w v) (c : F.R v t) :
    F.trans hF (F.side hV a a) c = c := by
  have he := F.side_cocycle hF hV a a a
  have hc := F.trans_side hF hV (F.side hV a a) c
  rw [← hc, ← F.trans_assoc hF, he]

/-- ⭐**The systems with a canonical model.**  Not a statement of what is coherent, but of what
    is built: 5 with T off and without both lifts is still to come.  Strong B with 5 without T is
    left out: KDB5
    there is S5 (`Frame.exists_unit_of_serial`), and KB5 there is a possible gap, to review (docs,
    "Strong B on KB5 and KDB5").  `strongT` is `ModalSys.WCoh`, which the network and the cluster
    ask for. -/
class ModalSys.CubeSys [ModalSys] : Prop where
  /-- 5 comes with 4 and both of 4's lifts in force: by flag, or under T, which with 5 proves
      them. -/
  five_lifts : ModalSys.Five = true →
    ModalSys.Four = true ∧ ModalSys.fourL = true ∧ ModalSys.fourLW = true
  /-- Strong B with 5 comes with T, which under D its frames meet anyway
      (`Frame.exists_unit_of_serial`).  Weak B needs no T: the root has its self-arrow. -/
  five_B : ModalSys.Five = true → ModalSys.BStrong = true → ModalSys.T = true
  /-- B with 4 comes with 5. -/
  four_B : ModalSys.B = true → ModalSys.Four = true → ModalSys.Five = true
  /-- Strong B comes with weak B, so with 4 it comes with 5 (`four_B`). -/
  strongB : ModalSys.BStrong = true → ModalSys.B = true
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

/-- S5 with every strong form. -/
def ModalSys.S5Strong : ModalSys :=
  { T := true, Four := true, TStrong := true, D := true, DStrong := true, B := true,
    BStrong := true, BStrongW := true, FourStrong := true, FourStrongW := true,
    Five := true, FiveStrong := true }

omit [ModalSys] in
/-- ⭐S5 with every strong form is in the cube. -/
theorem ModalSys.S5Strong_cube : @ModalSys.CubeSys ModalSys.S5Strong :=
  letI := ModalSys.S5Strong
  { five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ _ => rfl
    four_B := fun _ _ => rfl
    strongB := fun _ => rfl
    strongT := fun _ _ => rfl }

/-- S5 with every strong form off, 4's lifts included. -/
def ModalSys.S5NoLift : ModalSys :=
  { T := true, Four := true, TStrong := false, D := false, DStrong := false, B := true,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := true, FiveStrong := false }

omit [ModalSys] in
/-- ⭐S5 with no strong form is in the cube: T and 5 prove 4's lifts. -/
theorem ModalSys.S5NoLift_cube : @ModalSys.CubeSys ModalSys.S5NoLift :=
  letI := ModalSys.S5NoLift
  { five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ _ => rfl
    four_B := fun _ _ => rfl
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- S5 with every flag on but 4's lifts. -/
def ModalSys.S5StrongNoLift : ModalSys :=
  { T := true, Four := true, TStrong := true, D := true, DStrong := true, B := true,
    BStrong := true, BStrongW := true, FourStrong := false, FourStrongW := false,
    Five := true, FiveStrong := true }

omit [ModalSys] in
/-- ⭐S5 with every strong form but the lifts is in the cube. -/
theorem ModalSys.S5StrongNoLift_cube : @ModalSys.CubeSys ModalSys.S5StrongNoLift :=
  letI := ModalSys.S5StrongNoLift
  { five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ _ => rfl
    four_B := fun _ _ => rfl
    strongB := fun _ => rfl
    strongT := fun _ _ => rfl }

/-- KB5: weak B and 5, T and D off, with both of 4's lifts. -/
def ModalSys.KB5 : ModalSys :=
  { T := false, Four := true, TStrong := false, D := false, DStrong := false, B := true,
    BStrong := false, BStrongW := false, FourStrong := true, FourStrongW := true,
    Five := true, FiveStrong := true }

omit [ModalSys] in
/-- ⭐KB5 is in the cube. -/
theorem ModalSys.KB5_cube : @ModalSys.CubeSys ModalSys.KB5 :=
  letI := ModalSys.KB5
  { five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun _ _ => rfl
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- KDB5: KB5 with D in both strengths. -/
def ModalSys.KDB5 : ModalSys :=
  { T := false, Four := true, TStrong := false, D := true, DStrong := true, B := true,
    BStrong := false, BStrongW := false, FourStrong := true, FourStrongW := true,
    Five := true, FiveStrong := true }

omit [ModalSys] in
/-- ⭐KDB5 is in the cube. -/
theorem ModalSys.KDB5_cube : @ModalSys.CubeSys ModalSys.KDB5 :=
  letI := ModalSys.KDB5
  { five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun _ _ => rfl
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.CubeSys]

/-- With 5 the cluster model applies. -/
theorem cluFlags_of_cube (hV : ModalSys.Five = true) : GArrow.CluFlags :=
  have h := ModalSys.CubeSys.five_lifts hV
  ⟨hV, h.2.1, h.2.2, ModalSys.CubeSys.five_B hV, ModalSys.CubeSys.strongB,
    fun hS hW => ModalSys.CubeSys.strongT hW (ModalSys.CubeSys.five_B hV hS)⟩

/-- With B and without 5 the network applies. -/
theorem noFour_of_cube (hV : ¬ ModalSys.Five = true) (hB : ModalSys.B = true) : ModalSys.NoFour :=
  { strongT := ModalSys.CubeSys.strongT
    noFour := Bool.eq_false_iff.mpr fun hF => hV (ModalSys.CubeSys.four_B hB hF)
    noFive := Bool.eq_false_iff.mpr hV }

/-- Without B and without 5, `NoBComplete` applies. -/
theorem noB_of_cube (hV : ¬ ModalSys.Five = true) (hB : ¬ ModalSys.B = true) : ModalSys.NoB :=
  { noB := Bool.eq_false_iff.mpr hB
    noBStrong := Bool.eq_false_iff.mpr fun hS => hB (ModalSys.CubeSys.strongB hS)
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
  · exact GArrow.model_existenceC (ModalSys.CubeSys.five_lifts hV).1 (cluFlags_of_cube hV)
      e he hS
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
  · exact GArrow.compactnessC (ModalSys.CubeSys.five_lifts hV).1 (cluFlags_of_cube hV)
      e he hfin
  by_cases hB : ModalSys.B = true
  · haveI := noFour_of_cube hV hB
    exact BArrow.compactnessB hB e he hfin
  · haveI := noB_of_cube hV hB
    exact compactnessNoB e he hfin

end V12M
