import QML.QML_v12m_NoBComplete
import QML.QML_v12m_BCompactness

/-!
# QML v12m — completeness across the cube

Every system with a canonical model, in one theorem.  `ModalSys.CubeSys` says which: 5 with 4 and
both of 4's lifts in force, by flag, under T or with weak B, B with 4 only with 5, strong B with
weak B, and with 5 only under T.  In a
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
Weak B and 5 prove the lifts too (`Proof.keep_lift_B`, `Proof.keep_lift_posB`), so neither needs a
flag: `ModalSys.KB5NoLift`, `ModalSys.KDB5NoLift`.  K45 and KD45 without both lifts by flag have
the hub: the world asked about on top of the cluster (`GArrow.hubCone`), with neither lift
(`ModalSys.K45NoLift`, `ModalSys.KD45NoLift`), one (`ModalSys.K45BoxLift`, `ModalSys.K45DiaLift`),
or the `□`-lift with strong 5 (`ModalSys.K45Strong5`, `ModalSys.KD45Strong5`).
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

/-- With an arrow in, `side` from the unit is the identity. -/
theorem Frame.side_unit_self {σ : Signature} (F : Frame σ) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) {u w v : F.W} (r : F.R u w) (a : F.R w v) :
    F.side hV (F.side hV r r) a = a := by
  have h := F.trans_side hF hV (F.side hV r r) a
  rwa [F.side_self_unit hF hV] at h

/-- ⭐**An arrow out of a reached world has a left inverse**, up to the unit at its target. -/
theorem Frame.exists_left_inverse {σ : Signature} (F : Frame σ) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) {u w v : F.W} (r : F.R u w) (a : F.R w v) :
    ∃ x : F.R v w, F.trans hF x a = F.side hV a a := by
  refine ⟨F.side hV a (F.side hV r r), ?_⟩
  have h := F.side_cocycle hF hV a (F.side hV r r) a
  rwa [F.side_unit_self hF hV r a] at h

/-- ⭐**Keep is onto along every arrow out of a reached world**, in every model with 4 and 5,
    whatever the lift flags say.  So the lifts only say anything at a world with no arrow in. -/
theorem Model.boxLift_of_reached {σ : Signature} (M : Model σ) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) {A : VarType} {u w : M.frame.W} (r : M.frame.R u w)
    (a : M.frame.Acc w) (n : M.frame.Nec A a.1) :
    ∃ m : M.frame.Nec A w, M.necEval (M.ops.necDup hF m) a = n := by
  obtain ⟨x, hx⟩ := M.frame.exists_left_inverse hF hV r a.2.down
  refine ⟨M.necEval (M.ops.necDup hF n) ⟨w, ⟨x⟩⟩, M.nec_inj ?_⟩
  funext s
  rw [M.necDup_eval hF _ a s, M.necDup_eval hF n ⟨w, ⟨x⟩⟩ _]
  have e : M.frame.trans hF x (M.frame.trans hF a.2.down s.2.down) = s.2.down := by
    rw [← M.frame.trans_assoc hF, hx, M.frame.side_self_unit hF hV]
  rw [e]

/-- `Model.boxLift_of_reached` for possible objects, with shapes off. -/
theorem Model.diaLift_of_reached {σ : Signature} (M : Model σ) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hN : ModalSys.shaped = false) {A : VarType} {u w : M.frame.W}
    (r : M.frame.R u w) (a : M.frame.Acc w) (q : M.frame.Pos A a.1) :
    ∃ m : M.frame.Pos A w, M.necEval (M.ops.posKeep hF m) a = q := by
  obtain ⟨x, hx⟩ := M.frame.exists_left_inverse hF hV r a.2.down
  refine ⟨M.necEval (M.ops.posKeep hF q) ⟨w, ⟨x⟩⟩, M.posFull_inj ?_⟩
  have e : ∀ {t : M.frame.W} (s : M.frame.R a.1 t),
      M.frame.trans hF x (M.frame.trans hF a.2.down s) = s := fun s => by
    rw [← M.frame.trans_assoc hF, hx, M.frame.side_self_unit hF hV]
  refine Prod.ext ?_ (funext fun h => by simp [hN] at h)
  have key : ∀ (g : ∀ b : M.frame.Acc a.1, PLift (M.frame.R a.1 b.1)), (∀ b, g b = b.2) →
      ((⟨{b | (⟨b.1, g b⟩ : M.frame.Acc a.1) ∈ (M.posFull q).1.1},
        fun b => (M.posFull q).1.2 ⟨⟨b.1.1, g b.1⟩, b.2⟩⟩ : M.frame.PosSec A a.1) =
        (M.posFull q).1) := by
    intro g hg
    obtain rfl : g = fun b => b.2 := funext hg
    rfl
  have h₁ := congrArg Prod.fst (M.posKeep_full hF (M.necEval (M.ops.posKeep hF q) ⟨w, ⟨x⟩⟩) a)
  have h₂ := congrArg Prod.fst (M.posKeep_full hF q ⟨w, ⟨x⟩⟩)
  dsimp only at h₁ h₂
  rw [h₁, h₂]
  exact key (fun b => ⟨M.frame.trans hF x (M.frame.trans hF a.2.down b.2.down)⟩)
    (fun b => congrArg PLift.up (e b.2.down))

/-- ⭐**The systems with a canonical model.**  Not a statement of what is coherent, but of what
    is built.  Strong 5 needs strong 4 where the hub is (`hub_fiveS`).  Strong
    B with 5 without T is left out: KDB5
    there is S5 (`Frame.exists_unit_of_serial`), and KB5 there is a possible gap, to review (docs,
    "Strong B on KB5 and KDB5").  `strongT` is `ModalSys.WCoh`, which the network and the cluster
    ask for.  `Opt` is off (for now: every canonical model is built without the box view of
    possible objects; M1 brings it to K and D). -/
class ModalSys.CubeSys [ModalSys] : Prop extends ModalSys.NoOpt where
  /-- 5 comes with 4 and both of 4's lifts in force: by flag, or under T or weak B, either of which
      with 5 proves them. -/
  five_lifts : ModalSys.Five = true →
    ModalSys.Four = true ∧ ModalSys.fourL = true ∧ ModalSys.fourLW = true
  /-- Strong B with 5 comes with T, which under D its frames meet anyway
      (`Frame.exists_unit_of_serial`).  Weak B needs no T: the root has its self-arrow. -/
  five_B : ModalSys.Five = true → ModalSys.BStrong = true → ModalSys.T = true
  /-- B with 4 comes with 5. -/
  four_B : ModalSys.B = true → ModalSys.Four = true → ModalSys.Five = true
  /-- With the hub (K45 and KD45 without both lifts), strong 5 comes with strong 4: without it,
      strong 5 is incomplete as ruled (docs, "K45 and KD45 without both lifts: the hub", 6). -/
  hub_fiveS : ModalSys.hubFlags = true → ModalSys.FiveStrong = true → ModalSys.FourStrong = true
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
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ _ => rfl
    four_B := fun _ _ => rfl
    hub_fiveS := fun h => Bool.noConfusion ((rfl : ModalSys.hubFlags = false).symm.trans h)
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
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ _ => rfl
    four_B := fun _ _ => rfl
    hub_fiveS := fun h => Bool.noConfusion ((rfl : ModalSys.hubFlags = false).symm.trans h)
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
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ _ => rfl
    four_B := fun _ _ => rfl
    hub_fiveS := fun h => Bool.noConfusion ((rfl : ModalSys.hubFlags = false).symm.trans h)
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
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ _ => rfl
    four_B := fun _ _ => rfl
    hub_fiveS := fun h => Bool.noConfusion ((rfl : ModalSys.hubFlags = false).symm.trans h)
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
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun _ _ => rfl
    hub_fiveS := fun h => Bool.noConfusion ((rfl : ModalSys.hubFlags = false).symm.trans h)
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
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun _ _ => rfl
    hub_fiveS := fun h => Bool.noConfusion ((rfl : ModalSys.hubFlags = false).symm.trans h)
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- KB5 with no strong form: 4's lifts off. -/
def ModalSys.KB5NoLift : ModalSys :=
  { T := false, Four := true, TStrong := false, D := false, DStrong := false, B := true,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := true, FiveStrong := false }

omit [ModalSys] in
/-- ⭐KB5 with no strong form is in the cube: 5 and weak B prove 4's lifts. -/
theorem ModalSys.KB5NoLift_cube : @ModalSys.CubeSys ModalSys.KB5NoLift :=
  letI := ModalSys.KB5NoLift
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun _ _ => rfl
    hub_fiveS := fun h => Bool.noConfusion ((rfl : ModalSys.hubFlags = false).symm.trans h)
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- KDB5 with D in both strengths, 4's lifts off. -/
def ModalSys.KDB5NoLift : ModalSys :=
  { T := false, Four := true, TStrong := false, D := true, DStrong := true, B := true,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := true, FiveStrong := false }

omit [ModalSys] in
/-- ⭐KDB5 without 4's lifts is in the cube. -/
theorem ModalSys.KDB5NoLift_cube : @ModalSys.CubeSys ModalSys.KDB5NoLift :=
  letI := ModalSys.KDB5NoLift
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun _ _ => rfl
    hub_fiveS := fun h => Bool.noConfusion ((rfl : ModalSys.hubFlags = false).symm.trans h)
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- K45 with no strong form. -/
def ModalSys.K45NoLift : ModalSys :=
  { T := false, Four := true, TStrong := false, D := false, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := true, FiveStrong := false }

omit [ModalSys] in
/-- ⭐K45 with no strong form is in the cube: the hub. -/
theorem ModalSys.K45NoLift_cube : @ModalSys.CubeSys ModalSys.K45NoLift :=
  letI := ModalSys.K45NoLift
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun h => (Bool.false_ne_true h).elim
    hub_fiveS := fun _ h => (Bool.false_ne_true h).elim
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- KD45 with D in both strengths, 4's lifts off. -/
def ModalSys.KD45NoLift : ModalSys :=
  { T := false, Four := true, TStrong := false, D := true, DStrong := true, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := true, FiveStrong := false }

omit [ModalSys] in
/-- ⭐KD45 without 4's lifts is in the cube: the hub, with strong D at the world asked about. -/
theorem ModalSys.KD45NoLift_cube : @ModalSys.CubeSys ModalSys.KD45NoLift :=
  letI := ModalSys.KD45NoLift
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun h => (Bool.false_ne_true h).elim
    hub_fiveS := fun _ h => (Bool.false_ne_true h).elim
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- K45 with 4's `□`-lift and not its `◇`-lift. -/
def ModalSys.K45BoxLift : ModalSys :=
  { T := false, Four := true, TStrong := false, D := false, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := true, FourStrongW := false,
    Five := true, FiveStrong := false }

omit [ModalSys] in
/-- ⭐K45 with the `□`-lift alone is in the cube: the hub, the world asked about lifting by flag. -/
theorem ModalSys.K45BoxLift_cube : @ModalSys.CubeSys ModalSys.K45BoxLift :=
  letI := ModalSys.K45BoxLift
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun h => (Bool.false_ne_true h).elim
    hub_fiveS := fun _ h => (Bool.false_ne_true h).elim
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- K45 with 4's `◇`-lift and not its `□`-lift. -/
def ModalSys.K45DiaLift : ModalSys :=
  { T := false, Four := true, TStrong := false, D := false, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := true,
    Five := true, FiveStrong := false }

omit [ModalSys] in
/-- ⭐K45 with the `◇`-lift alone is in the cube. -/
theorem ModalSys.K45DiaLift_cube : @ModalSys.CubeSys ModalSys.K45DiaLift :=
  letI := ModalSys.K45DiaLift
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun h => (Bool.false_ne_true h).elim
    hub_fiveS := fun _ h => (Bool.false_ne_true h).elim
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- K45 with strong 5 and the `□`-lift it needs, without the `◇`-lift. -/
def ModalSys.K45Strong5 : ModalSys :=
  { T := false, Four := true, TStrong := false, D := false, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := true, FourStrongW := false,
    Five := true, FiveStrong := true }

omit [ModalSys] in
/-- ⭐K45 with strong 5 and the `□`-lift is in the cube: the gather at the world asked about. -/
theorem ModalSys.K45Strong5_cube : @ModalSys.CubeSys ModalSys.K45Strong5 :=
  letI := ModalSys.K45Strong5
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun h => (Bool.false_ne_true h).elim
    hub_fiveS := fun _ _ => rfl
    strongB := fun h => (Bool.false_ne_true h).elim
    strongT := fun h => (Bool.false_ne_true h).elim }

/-- KD45 with D in both strengths, strong 5 and the `□`-lift, without the `◇`-lift. -/
def ModalSys.KD45Strong5 : ModalSys :=
  { T := false, Four := true, TStrong := false, D := true, DStrong := true, B := false,
    BStrong := false, BStrongW := false, FourStrong := true, FourStrongW := false,
    Five := true, FiveStrong := true }

omit [ModalSys] in
/-- ⭐KD45 with every strong form but the `◇`-lift is in the cube. -/
theorem ModalSys.KD45Strong5_cube : @ModalSys.CubeSys ModalSys.KD45Strong5 :=
  letI := ModalSys.KD45Strong5
  { noOpt := rfl
    five_lifts := fun _ => ⟨rfl, rfl, rfl⟩
    five_B := fun _ h => (Bool.false_ne_true h).elim
    four_B := fun h => (Bool.false_ne_true h).elim
    hub_fiveS := fun _ _ => rfl
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
  { noOpt := ModalSys.NoOpt.noOpt
    strongT := ModalSys.CubeSys.strongT
    noFour := Bool.eq_false_iff.mpr fun hF => hV (ModalSys.CubeSys.four_B hB hF)
    noFive := Bool.eq_false_iff.mpr hV }

/-- Without B and without 5, `NoBComplete` applies. -/
theorem noB_of_cube (hV : ¬ ModalSys.Five = true) (hB : ¬ ModalSys.B = true) : ModalSys.NoB :=
  { noOpt := ModalSys.NoOpt.noOpt
    noB := Bool.eq_false_iff.mpr hB
    noBStrong := Bool.eq_false_iff.mpr fun hS => hB (ModalSys.CubeSys.strongB hS)
    fiveCluster := fun h => absurd h hV
    hubFiveS := ModalSys.CubeSys.hub_fiveS }

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
      ModalSys.CubeSys.hub_fiveS e he hval
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
  exact ⟨fun ⟨p⟩ M hM _ env hnp =>
    Model.soundness p M hM env (Ctx.Presented.tame _) hnp (by env_opened),
    completenessCube e he⟩

/-- ⭐**Model existence across the cube.** -/
theorem model_existenceCube (e : CtxExpr) (he : e.Wf) {S : Set (WFF σ e.denote 0)}
    (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S := by
  by_cases hV : ModalSys.Five = true
  · exact GArrow.model_existenceC (ModalSys.CubeSys.five_lifts hV).1 (cluFlags_of_cube hV)
      ModalSys.CubeSys.hub_fiveS e he hS
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
      ModalSys.CubeSys.hub_fiveS e he hval
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
      ModalSys.CubeSys.hub_fiveS e he hfin
  by_cases hB : ModalSys.B = true
  · haveI := noFour_of_cube hV hB
    exact BArrow.compactnessB hB e he hfin
  · haveI := noB_of_cube hV hB
    exact compactnessNoB e he hfin

end V12M
