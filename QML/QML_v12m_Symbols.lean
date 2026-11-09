import Mathlib.Tactic

/-!
# QML v12m — foundations: modal systems, types, addresses, contexts, annotations

The generalised counterpart of `QML_v12_Symbols`, parameterised by a modal system (`ModalSys`,
a type class, so the parameter is invisible in the notation).  With every flag off it is K.

* **Variable symbols are ADDRESSES**: a root and a path of steps.  Steps are either
  *projections* (`fst`, `snd`, and under T `here`), which stay at the current level and are always
  reached from the parent (`Ctx.ref`), or *level steps* (`box`, `dia`, and under 4 `keep`), which
  descend into a modality and must be visible.
* **Weak T** reads a necessary object at the current world: `u.here : A` for `u : □A`.  It is a
  projection, so it needs no context entry.  It is a different step from `box`: for `u : □□C`,
  inside a `□` the address `u.here.box` is `u(w)(v)` while `u.box.here` is `u(v)(v)`.
* **Collapsing** a level turns a `box` into `here` (`VarSymb.collapse k`: the level step with
  exactly `k` level steps after it).  It moves syntax from a `□` view to the current level.
* **Weak 4** keeps a necessary object inside a `□`, restricted to the worlds accessible from there:
  `u.keep : □A` for `u : □A`.  At each level an address records whether an object was evaluated
  (`box`) or kept (`keep`), so every object has one address.
* **Shifting** inserts a `keep` below a level (`VarSymb.shift k`).  It moves syntax from a `□` view
  one view further in.
* **T and 4 together** make `u.box` the kept copy read where it was kept (`u.keep.here`).  A view
  then shows only `u.keep` (`ModalSys.keepOnly`), so its entries stay independent and every object
  still has one address; `VarSymb.inner` builds the contents address for either case.
-/

namespace V12M

/-! ## Modal systems -/

/-- The modal principles in force.  K has every flag off. -/
class ModalSys where
  /-- Weak T: necessary objects can be read at the current world (`u.here`). -/
  T : Bool
  /-- Weak 4: necessary objects stay visible, restricted, inside `□` (`u.keep`). -/
  Four : Bool
  /-- Strong T: every object has a possible object realised at the current world with it as its
      content there.  Needs weak T, which the rules using it require. -/
  TStrong : Bool
  /-- Weak D: every world has an accessible world. -/
  D : Bool
  /-- Strong D: some possible object has a nonempty extent, `⊢ ∃x:◇𝟙. ◇_x ⊤`. -/
  DStrong : Bool
  /-- Weak B: what is possibly necessary is true, for closed formulas, `◇□ψ ⊢ ψ`. -/
  B : Bool
  /-- Strong B: round trips are named — `Back` (an object comes back as a given value from every
      successor) and the returning possibility `◇[d ↦ t]` — and every object is the constant round
      trip of some carrier (`docs/v12-modal-extensions.md` §11).  Needs weak B, which the rules
      using it require. -/
  BStrong : Bool
  /-- Strong B with **witnessed ways home** (rows 3–4, `docs/v12-modal-extensions.md` §11.23):
      along any arrow, some possible object at its source has the arrow in its extent, with any
      given content at its target.  Read at a returning possibility's way home it is B's unit
      `A → □◇A` per arrow (`Proof.ret_realise`); read at its arrow out it names the route,
      which is derivable (`Proof.ret_route_node`).  Needs strong B, which the rules using it
      require. -/
  BStrongW : Bool
  /-- ⭐Strong 4, the **`□`-lift** (`docs/v12-modal-extensions.md` §3 4, "4's strong forms"):
      along any arrow, every necessary object at its target is the restriction (`keep`) of one at
      its source.  Rows `(□,□)` and `(◇,□)` of 4's grid.  Needs weak 4, which the rule requires. -/
  FourStrong : Bool
  /-- ⭐Strong 4, the **`◇`-lift**: along any arrow, every possible object at its target is the
      restriction of one at its source.  The join `◇◇A → ◇A` follows with `four_dia`.  Rows
      `(□,◇)` and `(◇,◇)`.  Needs weak 4, which the rule requires. -/
  FourStrongW : Bool
  /-- ⭐Weak 5 (`docs/v12-modal-extensions.md` §3 5, "5: scope and plan"): for arrows `a : w → v`
      and `b : w → s` an arrow `side a b : v → s`, and possible objects stay visible inside `□`,
      their extents moved across (`x.side`). -/
  Five : Bool
  /-- ⭐Strong 5, the **gather**: along any arrow `a : w → v`, every necessary object at `v`, read
      along the side arrows `side a b`, is one at `w`.  Needs weak 5, which the rule requires. -/
  FiveStrong : Bool
  /-- **The box view of possible objects** (branch `wip/in-atom`, docs §12.13–12.16): inside a
      view, each possible object of the context one level out is a **witness** whose value along
      the arrow just taken (present or not) is in view, read by `◇⁰`.  A language switch, not an
      axiom: off, the language is the one every existing construction is built for; it is on while
      the constructions are extended, and goes when they all are. -/
  Opt : Bool := false
  /-- **The stage of the build** (branch `wip/in-atom`): the box view of possible objects is built
      for K and D first (M1); T, 4, B (weak and strong) and 5 each read it in their own milestone
      (docs §12.10), and this field loses a disjunct with each.  Meanwhile their syntax may assume
      `Opt` off; in particular shapes (`ModalSys.shaped`, T or strong B) are off with `Opt` on. -/
  optStage : Opt = true → (T || Four || B || BStrong || Five) = false := by decide

/-- The system K. -/
def ModalSys.K : ModalSys :=
  ⟨false, false, false, false, false, false, false, false, false, false, false, false, false,
    by decide⟩

/-- With T on, `Opt` is off (for now: `ModalSys.optStage`). -/
theorem ModalSys.noOpt_of_T [ModalSys] (h : ModalSys.T = true) :
    ModalSys.Opt = false := by
  cases hO : ModalSys.Opt
  · rfl
  · have := ModalSys.optStage hO; simp [h] at this

/-- With 4 on, `Opt` is off (for now: `ModalSys.optStage`). -/
theorem ModalSys.noOpt_of_Four [ModalSys] (h : ModalSys.Four = true) :
    ModalSys.Opt = false := by
  cases hO : ModalSys.Opt
  · rfl
  · have := ModalSys.optStage hO; simp [h] at this

/-- With B on, `Opt` is off (for now: `ModalSys.optStage`). -/
theorem ModalSys.noOpt_of_B [ModalSys] (h : ModalSys.B = true) :
    ModalSys.Opt = false := by
  cases hO : ModalSys.Opt
  · rfl
  · have := ModalSys.optStage hO; simp [h] at this

/-- With strong B on, `Opt` is off (for now: `ModalSys.optStage`). -/
theorem ModalSys.noOpt_of_BStrong [ModalSys] (h : ModalSys.BStrong = true) :
    ModalSys.Opt = false := by
  cases hO : ModalSys.Opt
  · rfl
  · have := ModalSys.optStage hO; simp [h] at this

/-- With 5 on, `Opt` is off (for now: `ModalSys.optStage`). -/
theorem ModalSys.noOpt_of_Five [ModalSys] (h : ModalSys.Five = true) :
    ModalSys.Opt = false := by
  cases hO : ModalSys.Opt
  · rfl
  · have := ModalSys.optStage hO; simp [h] at this

/-- 4's lifts are derivable: with T and 5 (`Proof.keep_lift_T`), or with 5, T and strong B off, from
    the closed sentences `Proof.five_refl` necessitates (`Proof.keep_lift_F`): weak B gives them
    wherever something is accessible, and without B the tree's root is a hub that holds them
    (docs, "K45 and KD45 without both lifts: the hub"). -/
def ModalSys.liftsProved [ModalSys] : Bool :=
  ModalSys.Five && (ModalSys.T || !ModalSys.BStrong)

/-- The tree's nodes must hold those closed sentences: the lifts are derived from them, T off, and
    not both lifts are given by flag. -/
def ModalSys.axNeed [ModalSys] : Bool :=
  ModalSys.liftsProved && !ModalSys.T && !(ModalSys.FourStrong && ModalSys.FourStrongW)

/-- ⭐**The tree's root is a hub**, not the world asked about: B off, so nothing gives the closed
    sentences at the root itself. -/
def ModalSys.hubFlags [ModalSys] : Bool := ModalSys.axNeed && !ModalSys.B

/-- 4's `□`-lift in force: `FourStrong`, or derivable. -/
def ModalSys.fourL [ModalSys] : Bool := ModalSys.FourStrong || ModalSys.liftsProved

/-- 4's `◇`-lift in force: `FourStrongW`, or derivable. -/
def ModalSys.fourLW [ModalSys] : Bool := ModalSys.FourStrongW || ModalSys.liftsProved

/-- The language without the box view of possible objects: `Opt` off, so no view has witnesses.
    What every construction built before it assumes (branch `wip/in-atom`, docs §12.16). -/
class ModalSys.NoOpt [ModalSys] : Prop where
  noOpt : ModalSys.Opt = false

/-- The systems without B.  B's accessible worlds lead back to their origin, against the order
    of construction; its canonical model is the arrow-based network (`BArrow`).  Strong B needs
    weak B, so it is off too.  Their canonical model is the staged tree (`Canon`) without 4's strong
    forms and the growing tree (`GArrow`) with 4. -/
class ModalSys.NoB [ModalSys] : Prop extends ModalSys.NoOpt where
  noB : ModalSys.B = false
  noBStrong : ModalSys.BStrong = false
  /-- 5 is covered with 4 and both of 4's lifts — K45, KD45 and S5 (the cluster model,
      `GArrow.cmodel`, `docs/v12-modal-extensions.md` §3 5); its other systems are not yet. -/
  fiveCluster : ModalSys.Five = true → ModalSys.Four = true ∧
    ModalSys.fourL = true ∧ ModalSys.fourLW = true
  /-- With the hub (K45 and KD45 without both lifts), strong 5 comes with strong 4: without it,
      strong 5 is incomplete as ruled (docs, "K45 and KD45 without both lifts: the hub", 6). -/
  hubFiveS : ModalSys.hubFlags = true → ModalSys.FiveStrong = true → ModalSys.FourStrong = true

/-- 5 off: what the staged tree and the growing tree are built for (with 5, the cluster model). -/
class ModalSys.NoFive [ModalSys] : Prop where
  noFive : ModalSys.Five = false

/-- ⭐**The systems the staged canonical model is built for**: B and 5 off, and 4's strong forms
    off when 4 is on (with 4 the growing tree covers every strong form, `GArrow`). -/
class ModalSys.StagedSys [ModalSys] : Prop extends ModalSys.NoB, ModalSys.NoFive where
  noLift : ModalSys.Four = true → ModalSys.FourStrong = false ∧ ModalSys.FourStrongW = false

/-- ⭐**The systems the growing tree is built for**: B and 5 off (4 on, its strong forms free). -/
class ModalSys.GrowSys [ModalSys] : Prop extends ModalSys.NoB, ModalSys.NoFive

theorem ModalSys.NoB.absurd [ModalSys] [ModalSys.NoB] (hB : ModalSys.B = true) : False := by
  rw [ModalSys.NoB.noB] at hB
  cases hB

theorem ModalSys.NoFive.absurdFive [ModalSys] [ModalSys.NoFive] (hV : ModalSys.Five = true) :
    False := by
  rw [ModalSys.NoFive.noFive] at hV
  cases hV

theorem ModalSys.NoB.absurdStrong [ModalSys] [ModalSys.NoB] (hB : ModalSys.BStrong = true) :
    False := by
  rw [ModalSys.NoB.noBStrong] at hB
  cases hB

/-- A link (5 without 4) is never formed under `NoB`: there 5 comes with 4. -/
theorem ModalSys.NoB.absurdLink [ModalSys] [ModalSys.NoB] (hV : ModalSys.Five = true)
    (hF : ModalSys.Four = false) : False := by
  have h := (ModalSys.NoB.fiveCluster hV).1
  rw [hF] at h
  cases h

/-- ⭐**The strong forms cohere** (`docs/v12-modal-extensions.md` §11.23): strong B with witnessed
    ways home contains strong T at the own arrow (`Model.posRet_of_posBack`), and only strong T's
    rule introduces `Here` atoms, so a system with it and T has strong T too; completeness under
    `BStrongW` asks for this.  (It contains strong D as well, `Model.posSerial_of_posBack`, but
    there no flag is needed: strong D's law is asked of a model only under `DStrong`, and its
    formula is derivable by naming a route, itself derivable, `Proof.ret_route_node`.) -/
class ModalSys.WCoh [ModalSys] : Prop extends ModalSys.NoOpt where
  strongT : ModalSys.BStrongW = true → ModalSys.T = true → ModalSys.TStrong = true

/-- Under T and 4 a view shows only kept objects: the contents of `u` are `u.keep.here`. -/
def ModalSys.keepOnly [ModalSys] : Bool := ModalSys.T && ModalSys.Four

theorem ModalSys.keepOnly_flags [ModalSys] (hk : ModalSys.keepOnly = true) :
    ModalSys.T = true ∧ ModalSys.Four = true := by
  simpa [ModalSys.keepOnly] using hk

/-- Possible objects carry a **shape** (their semantic annotation, docs §10.27) under T or strong B:
    T's `extract` and strong B's round trips both read a possibility back at its origin, so both
    need to know where the possibilities inside an object come from (§11.15, phase L3). -/
def ModalSys.shaped [ModalSys] : Bool := ModalSys.T || ModalSys.BStrong

theorem ModalSys.shaped_of_T [ModalSys] (hT : ModalSys.T = true) : ModalSys.shaped = true := by
  simp [ModalSys.shaped, hT]

theorem ModalSys.shaped_of_BStrong [ModalSys] (hB : ModalSys.BStrong = true) :
    ModalSys.shaped = true := by
  simp [ModalSys.shaped, hB]

/-- With shapes on, `Opt` is off (for now). -/
theorem ModalSys.noOpt_of_shaped [ModalSys] (hS : ModalSys.shaped = true) :
    ModalSys.Opt = false := by
  cases hT : ModalSys.T
  · have hB : ModalSys.BStrong = true := by simpa [ModalSys.shaped, hT] using hS
    exact ModalSys.noOpt_of_BStrong hB
  · exact ModalSys.noOpt_of_T hT

theorem ModalSys.NoB.T_of_shaped [ModalSys] [ModalSys.NoB] (h : ModalSys.shaped = true) :
    ModalSys.T = true := by
  simpa [ModalSys.shaped, ModalSys.NoB.noBStrong] using h

/-! ## Types and steps -/

inductive VarType where
  | Var
  | VTypeOne
  | VTypeProd (A B : VarType)
  | VTypeBox (A : VarType)
  | VTypeDia (A : VarType)
deriving DecidableEq

inductive Step where
  | fst
  | snd
  | box
  | dia
  /-- Under T: a necessary object read at the current world. -/
  | here
  /-- Under 4: a necessary object kept, restricted, one level further in. -/
  | keep
deriving DecidableEq

/-- Projection steps stay at the current level; the others are level steps. -/
def Step.isProj : Step → Bool
  | .fst => true
  | .snd => true
  | .here => true
  | _ => false

/-- The number of level steps of a path. -/
def Step.levels : List Step → ℕ
  | [] => 0
  | s :: p => (if s.isProj then 0 else 1) + Step.levels p

/-! ## Addresses -/

inductive Root where
  | free (n : ℕ)
  | bnd (n : ℕ)
deriving DecidableEq

/-- A variable symbol: a root and steps, the innermost step LAST. -/
inductive VarSymb where
  | root (r : Root)
  | step (v : VarSymb) (s : Step)
deriving DecidableEq

namespace VarSymb

def rt : VarSymb → Root
  | root r => r
  | step v _ => v.rt

/-- The steps, root-first. -/
def path : VarSymb → List Step
  | root _ => []
  | step v s => v.path ++ [s]

def ext : VarSymb → List Step → VarSymb
  | v, [] => v
  | v, s :: p => ext (.step v s) p

def reroot (r' : Root) : VarSymb → VarSymb
  | root _ => root r'
  | step v s => step (v.reroot r') s

/-- The last step is a projection. -/
def lastProj : VarSymb → Bool
  | root _ => false
  | step _ s => s.isProj

/-- Collapse the level step with exactly `k` level steps after it: a `box` becomes `here`, and a
    `keep` disappears (a kept object read at the world it was kept from is the object).  (On a
    `dia` this is junk, chosen so that collapses at different levels commute.) -/
def collapse : ℕ → VarSymb → VarSymb
  | _, root r => root r
  | k, step v s =>
      if s.isProj then step (collapse k v) s
      else match k with
        | 0 => if s = .keep then v else step v .here
        | k + 1 => step (collapse k v) s

/-- Insert a level below the level step with exactly `k` level steps after it: that step is then
    reached through a `keep`. -/
def shift : ℕ → VarSymb → VarSymb
  | _, root r => root r
  | k, step v s =>
      if s.isProj then step (shift k v) s
      else match k with
        | 0 => step (step v .keep) s
        | k + 1 => step (shift k v) s

theorem ext_rt : ∀ (v : VarSymb) (p : List Step), (v.ext p).rt = v.rt
  | _, [] => rfl
  | v, s :: p => ext_rt (.step v s) p

theorem ext_path : ∀ (v : VarSymb) (p : List Step), (v.ext p).path = v.path ++ p
  | v, [] => by simp [ext]
  | v, s :: p => by
      change (ext (.step v s) p).path = _
      rw [ext_path]
      simp [path]

theorem reroot_ext (r' : Root) :
    ∀ (v : VarSymb) (p : List Step), (v.ext p).reroot r' = (v.reroot r').ext p
  | _, [] => rfl
  | v, s :: p => reroot_ext r' (.step v s) p

theorem collapse_rt : ∀ (k : ℕ) (v : VarSymb), (v.collapse k).rt = v.rt
  | _, root _ => rfl
  | k, step v s => by
      by_cases hs : s.isProj = true
      · simp only [collapse, if_pos hs, rt]
        exact collapse_rt k v
      · cases k with
        | zero =>
            simp only [collapse, if_neg hs]
            split_ifs <;> rfl
        | succ k =>
            simp only [collapse, if_neg hs, rt]
            exact collapse_rt k v

theorem shift_rt : ∀ (k : ℕ) (v : VarSymb), (v.shift k).rt = v.rt
  | _, root _ => rfl
  | k, step v s => by
      by_cases hs : s.isProj = true
      · simp only [shift, if_pos hs, rt]
        exact shift_rt k v
      · cases k with
        | zero =>
            simp only [shift, if_neg hs]
            rfl
        | succ k =>
            simp only [shift, if_neg hs, rt]
            exact shift_rt k v

/-- Shift the addresses under the slot `bnd d` to the slot `bnd d'`. -/
def shiftSlot (ι : VarSymb → VarSymb) (d d' : ℕ) : VarSymb → VarSymb :=
  fun i => if i.rt = .bnd d then i.reroot (.bnd d') else ι i

end VarSymb

/-! ## Contexts: declarations and freshness -/

/-- An environment's respect for its opened witnesses where there is nothing to check
    (`Frame.Env.opened`); the rules are added where the contexts are (`QML_v12m_Env`,
    `ctxOf_wit`). -/
syntax "opened_triv" : tactic

/-- ⭐**A context**: the visible addresses with their types (`ty`), and — inside a view, with the
    box view of possible objects on (`ModalSys.Opt`, branch `wip/in-atom`, docs §12.16) — the
    **witnesses** (`wit`): `wit y = some X` says that the possible object `y : ◇X` of the context
    one level out can be asked about along the arrow just taken (`WFF.optx`).  Only `Ctx.boxIn`
    makes witnesses; every other operation copies them.  A context written as a function has none
    (the coercion below), so it is the old notion of context. -/
structure Ctx where
  /-- The visible addresses and their types. -/
  ty : VarSymb → Option VarType
  /-- The witnesses in view, with the types of their contents. -/
  wit : VarSymb → Option VarType := fun _ => none
  /-- A witness's content address is free or holds its content: what `Ctx.optIn` declares there
      agrees with what is there already (in `y`'s own `◇_y` view, `y.dia`). -/
  wit_dia : ∀ y X, wit y = some X → ty (.step y .dia) = none ∨ ty (.step y .dia) = some X := by
    intro _ _ h; cases h

instance : CoeFun Ctx (fun _ => VarSymb → Option VarType) := ⟨Ctx.ty⟩

/-- A context written as a function: no witnesses. -/
instance : Coe (VarSymb → Option VarType) Ctx := ⟨fun f => { ty := f }⟩

namespace Ctx

/-- Declare a root.  The witnesses stay. -/
def insert (Γ : Ctx) (r : Root) (T : VarType) : Ctx where
  ty := fun v => if v = .root r then some T else Γ v
  wit := Γ.wit
  wit_dia y X h := by
    simp only [if_neg (show VarSymb.step y .dia ≠ .root r from fun he => by cases he)]
    exact Γ.wit_dia y X h

theorem insert_apply (Γ : Ctx) (r : Root) (T : VarType) (v : VarSymb) :
    Γ.insert r T v = if v = .root r then some T else Γ v := rfl

theorem insert_ne {Γ : Ctx} {r : Root} {T : VarType} {v : VarSymb} (h : v ≠ .root r) :
    Γ.insert r T v = Γ v := if_neg h

/-- ⭐`Γ'` shows everything `Γ` shows: its addresses at their types, and its witnesses. -/
structure Le (Γ Γ' : Ctx) : Prop where
  ty : ∀ v T, Γ v = some T → Γ' v = some T
  wit : ∀ y X, Γ.wit y = some X → Γ'.wit y = some X

instance {Γ Γ' : Ctx} : CoeFun (Γ.Le Γ') (fun _ => ∀ v T, Γ v = some T → Γ' v = some T) :=
  ⟨Le.ty⟩

theorem Le.refl (Γ : Ctx) : Γ.Le Γ := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Le.trans {Γ Γ' Γ'' : Ctx} (h₁ : Γ.Le Γ') (h₂ : Γ'.Le Γ'') : Γ.Le Γ'' :=
  ⟨fun v T h => h₂ v T (h₁ v T h), fun y X h => h₂.wit y X (h₁.wit y X h)⟩

theorem Le.insert {Γ Γ' : Ctx} (h : Γ.Le Γ') (r : Root) (T : VarType) :
    (Γ.insert r T).Le (Γ'.insert r T) := by
  refine ⟨fun v U hv => ?_, fun y X hy => h.wit y X hy⟩
  simp only [Ctx.insert] at hv ⊢
  split_ifs at hv ⊢
  · exact hv
  · exact h v U hv

/-- Weakening by a fresh root. -/
theorem le_insert {Γ : Ctx} {r : Root} (hr : Γ (.root r) = none) (T : VarType) :
    Γ.Le (Γ.insert r T) := by
  refine ⟨fun v U hv => ?_, fun y X hy => hy⟩
  simp only [Ctx.insert]
  split_ifs with h
  · subst h
    rw [hr] at hv
    cases hv
  · exact hv

/-- No slot at or above `d` is visible, as an address or as a witness. -/
structure SlotsFrom (Γ : Ctx) (d : ℕ) : Prop where
  ty : ∀ v n, v.rt = .bnd n → d ≤ n → Γ v = none
  wit : ∀ y n, y.rt = .bnd n → d ≤ n → Γ.wit y = none

instance {Γ : Ctx} {d : ℕ} :
    CoeFun (Γ.SlotsFrom d) (fun _ => ∀ v n, v.rt = .bnd n → d ≤ n → Γ v = none) :=
  ⟨SlotsFrom.ty⟩

theorem SlotsFrom.root {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) : Γ (.root (.bnd d)) = none :=
  h _ d rfl le_rfl

theorem SlotsFrom.insert {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (T : VarType) :
    (Γ.insert (.bnd d) T).SlotsFrom (d + 1) := by
  refine ⟨fun v n hv hn => ?_, fun y n hy hn => h.wit y n hy (by omega)⟩
  simp only [Ctx.insert]
  split_ifs with hvr
  · subst hvr
    cases hv
    omega
  · exact h v n hv (by omega)

theorem SlotsFrom.insertFree {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (u : ℕ) (T : VarType) :
    (Γ.insert (.free u) T).SlotsFrom d := by
  refine ⟨fun v n hv hn => ?_, h.wit⟩
  simp only [Ctx.insert]
  split_ifs with hvr
  · subst hvr
    cases hv
  · exact h v n hv hn

/-- Every address with root `r` is hidden. -/
structure RootFresh (Γ : Ctx) (r : Root) : Prop where
  ty : ∀ v, v.rt = r → Γ v = none
  /-- No witness is named at `r` either: a root declared in a view must not share its name with a
      possible object of the context one level out, whose content address would be its too. -/
  wit : ∀ y, y.rt = r → Γ.wit y = none

instance {Γ : Ctx} {r : Root} : CoeFun (Γ.RootFresh r) (fun _ => ∀ v, v.rt = r → Γ v = none) :=
  ⟨RootFresh.ty⟩

theorem RootFresh.root {Γ : Ctx} {r : Root} (h : Γ.RootFresh r) : Γ (.root r) = none := h _ rfl

theorem RootFresh.insert_ne {Γ : Ctx} {r r' : Root} (h : Γ.RootFresh r) (hne : r' ≠ r)
    (T : VarType) : (Γ.insert r' T).RootFresh r := by
  refine ⟨fun v hv => ?_, h.wit⟩
  simp only [Ctx.insert]
  split_ifs with hvr
  · subst hvr
    exact absurd hv hne
  · exact h v hv

theorem SlotsFrom.rootFresh {Γ : Ctx} {d n : ℕ} (h : Γ.SlotsFrom d) (hn : d ≤ n) :
    Γ.RootFresh (.bnd n) :=
  ⟨fun v hv => h v n hv hn, fun y hy => h.wit y n hy hn⟩

/-- The empty context. -/
def empty : Ctx := { ty := fun _ => none }

theorem RootFresh.empty (r : Root) : Ctx.empty.RootFresh r := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- The empty context is below every context: closed formulas weaken anywhere. -/
theorem empty_le (Γ : Ctx) : Ctx.empty.Le Γ := ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- No quantifier slot is visible: the contexts proofs live in.  Found by instance search. -/
class NoSlots (Γ : Ctx) : Prop where
  slots : Γ.SlotsFrom 0

instance : Ctx.empty.NoSlots := ⟨⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩⟩

instance {Γ : Ctx} [h : Γ.NoSlots] {u : ℕ} {T : VarType} : (Γ.insert (.free u) T).NoSlots :=
  ⟨h.slots.insertFree u T⟩

theorem insert_swap_le {Γ : Ctx} {r r' : Root} (hne : r ≠ r') (T T' : VarType) :
    ((Γ.insert r T).insert r' T').Le ((Γ.insert r' T').insert r T) := by
  refine ⟨fun v U hv => ?_, fun _ _ hy => hy⟩
  simp only [Ctx.insert] at hv ⊢
  by_cases h₁ : v = .root r' <;> by_cases h₂ : v = .root r <;> simp_all

end Ctx

/-! ## Witness annotations -/

/-- ⭐A type with no `◇` in it.  `Ann` branches only at `.dia`, so at such a type the annotation is
    unique (`Ann.eq_of_diaFree`): a term of it carries no witness information, and equality needs no
    annotation index.  This is the content type `Here` is restricted to (§2d): a `Here` whose value
    is a possible object would combine two possibilities that nothing has joined. -/
def VarType.diaFree : VarType → Bool
  | .Var => true
  | .VTypeOne => true
  | .VTypeProd A B => A.diaFree && B.diaFree
  | .VTypeBox A => A.diaFree
  | .VTypeDia _ => false


/-- `◇`-freeness of a product, from its components. -/
theorem VarType.diaFree_prod {A B : VarType} (hA : A.diaFree = true) (hB : B.diaFree = true) :
    (VarType.VTypeProd A B).diaFree = true := by
  simp only [VarType.diaFree, Bool.and_eq_true]
  exact ⟨hA, hB⟩

/-- `◇`-freeness under `□`. -/
theorem VarType.diaFree_box {A : VarType} (hA : A.diaFree = true) :
    (VarType.VTypeBox A).diaFree = true := hA

inductive Ann : VarType → Type where
  | var : Ann .Var
  | one : Ann .VTypeOne
  | prod {A B : VarType} (a : Ann A) (b : Ann B) : Ann (.VTypeProd A B)
  | box {A : VarType} (a : Ann A) : Ann (.VTypeBox A)
  | dia {A : VarType} (i : VarSymb) (a : Ann A) : Ann (.VTypeDia A)
deriving DecidableEq


/-- ⭐At a `◇`-free type the annotation is unique, since `Ann` branches only at `.dia`. -/
theorem Ann.eq_of_diaFree : {T : VarType} → T.diaFree = true → ∀ a a' : Ann T, a = a'
  | .Var, _, .var, .var => rfl
  | .VTypeOne, _, .one, .one => rfl
  | .VTypeProd _ _, h, .prod a b, .prod a' b' => by
      simp only [VarType.diaFree, Bool.and_eq_true] at h
      rw [Ann.eq_of_diaFree h.1 a a', Ann.eq_of_diaFree h.2 b b']
  | .VTypeBox _, h, .box a, .box a' => by
      simp only [VarType.diaFree] at h
      rw [Ann.eq_of_diaFree h a a']
def Ann.mapIdx (f : VarSymb → VarSymb) : {T : VarType} → Ann T → Ann T
  | _, .var => .var
  | _, .one => .one
  | _, .prod a b => .prod (a.mapIdx f) (b.mapIdx f)
  | _, .box a => .box (a.mapIdx f)
  | _, .dia i a => .dia (f i) (a.mapIdx f)

/-- Collapse the indices of an annotation found `k` levels below the collapsed one. -/
def Ann.collapse : ℕ → {T : VarType} → Ann T → Ann T
  | _, _, .var => .var
  | _, _, .one => .one
  | k, _, .prod a b => .prod (a.collapse k) (b.collapse k)
  | k, _, .box a => .box (a.collapse (k + 1))
  | k, _, .dia i a => .dia (i.collapse k) (a.collapse (k + 1))

/-- Shift the indices of an annotation found `k` levels below the shifted one. -/
def Ann.shift : ℕ → {T : VarType} → Ann T → Ann T
  | _, _, .var => .var
  | _, _, .one => .one
  | k, _, .prod a b => .prod (a.shift k) (b.shift k)
  | k, _, .box a => .box (a.shift (k + 1))
  | k, _, .dia i a => .dia (i.shift k) (a.shift (k + 1))

/-- The index at the `◇`-node a path reaches (junk otherwise).  Reading a necessary object at the
    current world (`here`) collapses the level it would have descended into; keeping it (`keep`)
    shifts its body one view further in. -/
def Ann.idxAt : {T : VarType} → Ann T → List Step → VarSymb
  | _, .dia i _, [] => i
  | _, .prod a _, .fst :: p => a.idxAt p
  | _, .prod _ b, .snd :: p => b.idxAt p
  | _, .box a, .box :: p => a.idxAt p
  | _, .box a, .here :: p => (a.idxAt p).collapse (Step.levels p)
  | _, .box a, .keep :: p => (Ann.box (a.shift 0)).idxAt p
  | _, .dia i a, .keep :: p => (Ann.dia (.step i .keep) (a.shift 0)).idxAt p
  | _, .dia _ a, .dia :: p => a.idxAt p
  | _, _, _ => .root (.free 0)

/-! ## The system-dependent part: reaching addresses and modal views -/

variable [ModalSys]

/-- No possible object is kept: 4 is off. -/
abbrev ModalSys.NoDiaKeep : Prop := ModalSys.Four = false

/-- The types whose objects 4 keeps one view further in: necessary objects (`u.keep`, the
    restriction of `u`) and possible objects (`x.keep`, `x`'s extent pulled back along the
    arrow).  Under T + 4 a possible object's shape is kept too, which the labelling convention as a
    model law makes lawful (`Model.posShape_wf`, docs §3 4, "T + 4"). -/
def VarType.keepable : VarType → Bool
  | .VTypeBox _ => true
  | .VTypeDia _ => true
  | _ => false

omit [ModalSys] in
theorem VarType.keepable_dia {A : VarType} : (VarType.VTypeDia A).keepable = true := rfl

/-- The types strong 4 lifts by rule: `□`-types under `FourStrong`, `◇`-types under
    `FourStrongW`. -/
def VarType.liftableR : VarType → Bool
  | .VTypeBox _ => ModalSys.FourStrong
  | .VTypeDia _ => ModalSys.FourStrongW
  | _ => false

/-- The types with 4's lift in force: `VarType.liftableR`, and both kinds where the lift is
    derivable (`ModalSys.liftsProved`). -/
def VarType.liftable : VarType → Bool
  | .VTypeBox _ => ModalSys.fourL
  | .VTypeDia _ => ModalSys.fourLW
  | _ => false

theorem VarType.liftable_of_R {T : VarType} (h : T.liftableR = true) : T.liftable = true := by
  cases T <;> simp_all [VarType.liftableR, VarType.liftable, ModalSys.fourL, ModalSys.fourLW]

theorem VarType.liftableR_or {T : VarType} (h : T.liftable = true) :
    T.liftableR = true ∨ ModalSys.liftsProved = true := by
  cases T <;> simp_all [VarType.liftableR, VarType.liftable, ModalSys.fourL, ModalSys.fourLW]

theorem ModalSys.liftsProved_cases (h : ModalSys.liftsProved = true) :
    ModalSys.Five = true ∧ (ModalSys.T = true ∨
      (ModalSys.T = false ∧ ModalSys.shaped = false)) := by
  cases hT : ModalSys.T <;> cases hS : ModalSys.BStrong <;>
    cases hV : ModalSys.Five <;> simp_all [ModalSys.liftsProved, ModalSys.shaped]

theorem ModalSys.axNeed_flags (h : ModalSys.axNeed = true) :
    ModalSys.Five = true ∧ ModalSys.T = false ∧ ModalSys.shaped = false := by
  cases hT : ModalSys.T <;> cases hS : ModalSys.BStrong <;> cases hV : ModalSys.Five <;>
    simp_all [ModalSys.axNeed, ModalSys.liftsProved, ModalSys.shaped]

/-- The third way to a lift, `Proof.keep_lift_F`, is taken only when the nodes must hold the closed
    sentences. -/
theorem VarType.axNeed_of {T : VarType} (hl : T.liftable = true) (hR : T.liftableR = false)
    (hT : ModalSys.T = false) : ModalSys.axNeed = true := by
  have h := (VarType.liftableR_or hl).resolve_left (by simp [hR])
  cases T <;> simp_all [VarType.liftableR, VarType.liftable, ModalSys.axNeed]

theorem VarType.keepable_of_liftable {T : VarType} (h : T.liftable = true) :
    T.keepable = true := by
  cases T <;> first | rfl | (simp [VarType.liftable] at h)

theorem VarType.keepable_of_liftableR {T : VarType} (h : T.liftableR = true) :
    T.keepable = true :=
  VarType.keepable_of_liftable (VarType.liftable_of_R h)

theorem ModalSys.StagedSys.not_liftable [ModalSys.StagedSys] (hF : ModalSys.Four = true)
    {T : VarType} (h : T.liftableR = true) : False := by
  obtain ⟨h₁, h₂⟩ := ModalSys.StagedSys.noLift hF
  cases T <;> simp [VarType.liftableR, h₁, h₂] at h

def VarType.step : VarType → Step → Option VarType
  | .VTypeProd A _, .fst => some A
  | .VTypeProd _ B, .snd => some B
  | .VTypeBox A, .box => some A
  | .VTypeBox A, .here => if ModalSys.T then some A else none
  | .VTypeDia A, .dia => some A
  | _, _ => none

theorem VarType.step_here {A T : VarType} (h : (VarType.VTypeBox A).step .here = some T) :
    ModalSys.T = true ∧ A = T := by
  simp only [VarType.step] at h
  split_ifs at h with hT
  exact ⟨hT, Option.some.inj h⟩

/-- The contents of `u : □A` one view in: `u.box`, or under T and 4 `u.keep.here`. -/
def VarSymb.inner (u : VarSymb) : VarSymb :=
  if ModalSys.keepOnly then .step (.step u .keep) .here else .step u .box

theorem VarSymb.inner_keepOnly {u : VarSymb} (hk : ModalSys.keepOnly = true) :
    u.inner = .step (.step u .keep) .here :=
  if_pos hk

theorem VarSymb.inner_box {u : VarSymb} (hk : ModalSys.keepOnly = false) :
    u.inner = .step u .box :=
  if_neg (by simp [hk])

namespace Ctx

/-- The type reachable at an address: projections from the parent, level steps must be visible. -/
def ref (Γ : Ctx) : VarSymb → Option VarType
  | .root r => Γ (.root r)
  | .step v s => if s.isProj then (Γ.ref v).bind (·.step s) else Γ (.step v s)

/-- Inside `□`: `v.box : A` exactly when `v : □A` is reachable, and under 4 also `v.keep : □A`
    and, for `v : ◇A`, `v.keep : ◇A`.  Under T and 4 only `v.keep`: `v.box` would be
    `v.keep.here`.  With `Opt` on, every reachable possible object `y : ◇X` is a **witness** of the
    view (docs §12.16): along the arrow just taken it may be present, with a content of type `X`. -/
def boxIn (Γ : Ctx) : Ctx where
  ty v :=
    match v with
    | .step u .box =>
        if ModalSys.keepOnly then none
        else
          match Γ.ref u with
          | some (.VTypeBox A) => some A
          | _ => none
    | .step u .keep =>
        if ModalSys.Four then
          match Γ.ref u with
          | some (.VTypeBox A) => some (.VTypeBox A)
          | some (.VTypeDia A) => some (.VTypeDia A)
          | _ => none
        else none
    | _ => none
  wit y :=
    if ModalSys.Opt then
      match Γ.ref y with
      | some (.VTypeDia X) => some X
      | _ => none
    else none
  wit_dia _ _ _ := .inl rfl

/-- Inside `◇_x`: the `□` view, and `x.dia : X` where `x : ◇X`.  The witnesses are the `□`
    view's; `x`'s own content there is `x.dia`. -/
def diaIn (Γ : Ctx) (x : VarSymb) : Ctx where
  ty v :=
    match v with
    | .step u .dia =>
        if u = x then
          match Γ.ref x with
          | some (.VTypeDia X) => some X
          | _ => none
        else none
    | v => Γ.boxIn v
  wit := Γ.boxIn.wit
  wit_dia y X h := by
    by_cases hyx : y = x
    · subst hyx
      right
      change (if ModalSys.Opt = true then (match Γ.ref y with
        | some (.VTypeDia X) => some X
        | _ => none) else none) = some X at h
      change (if y = y then (match Γ.ref y with
        | some (.VTypeDia X) => some X
        | _ => none) else none) = some X
      rw [if_pos rfl]
      split_ifs at h
      exact h
    · left
      change (if y = x then _ else none) = none
      rw [if_neg hyx]

theorem boxIn_keep {Γ : Ctx} {u : VarSymb} {T : VarType}
    (h : Γ.boxIn (.step u .keep) = some T) :
    ModalSys.Four = true ∧ Γ.ref u = some T ∧ T.keepable = true := by
  change (if ModalSys.Four = true then
    (match Γ.ref u with
      | some (.VTypeBox A) => some (.VTypeBox A)
      | some (.VTypeDia A) => some (.VTypeDia A)
      | _ => none) else none) = some T at h
  by_cases hF : ModalSys.Four = true
  swap
  · rw [if_neg hF] at h; cases h
  rw [if_pos hF] at h
  refine ⟨hF, ?_⟩
  cases hu : Γ.ref u with
  | none => rw [hu] at h; cases h
  | some U =>
      rw [hu] at h
      cases U with
      | VTypeBox A => cases h; exact ⟨rfl, rfl⟩
      | VTypeDia A => cases h; exact ⟨rfl, rfl⟩
      | _ => cases h


theorem boxIn_keep_of' {Γ : Ctx} {u : VarSymb} {T : VarType} (hF : ModalSys.Four = true)
    (hu : Γ.ref u = some T) (hk : T.keepable = true) : Γ.boxIn (.step u .keep) = some T := by
  change (if ModalSys.Four = true then
    (match Γ.ref u with
      | some (.VTypeBox B) => some (.VTypeBox B)
      | some (.VTypeDia B) => some (.VTypeDia B)
      | _ => none) else none) = some T
  rw [if_pos hF, hu]
  cases T with
  | VTypeBox A => rfl
  | VTypeDia A => rfl
  | _ => cases hk

theorem boxIn_keep_of {Γ : Ctx} {u : VarSymb} {A : VarType} (hF : ModalSys.Four = true)
    (hu : Γ.ref u = some (.VTypeBox A)) : Γ.boxIn (.step u .keep) = some (.VTypeBox A) :=
  boxIn_keep_of' hF hu rfl

theorem boxIn_keep_none {Γ : Ctx} {u : VarSymb} (hu : Γ.ref u = none) :
    Γ.boxIn (.step u .keep) = none := by
  change (if ModalSys.Four = true then
    (match Γ.ref u with
      | some (.VTypeBox B) => some (.VTypeBox B)
      | some (.VTypeDia B) => some (.VTypeDia B)
      | _ => none) else none) =
      (none : Option VarType)
  rw [hu]
  split_ifs <;> rfl

theorem boxIn_box {Γ : Ctx} {u : VarSymb} {T : VarType}
    (h : Γ.boxIn (.step u .box) = some T) :
    ModalSys.keepOnly = false ∧ Γ.ref u = some (.VTypeBox T) := by
  change (if ModalSys.keepOnly = true then none
    else (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none)) = some T at h
  split_ifs at h with hk
  refine ⟨Bool.eq_false_iff.mpr hk, ?_⟩
  cases hu : Γ.ref u with
  | none => rw [hu] at h; cases h
  | some U =>
      rw [hu] at h
      cases U <;> first | (cases h; done) | (cases h; rfl)

theorem boxIn_box_of {Γ : Ctx} {u : VarSymb} {A : VarType} (hk : ModalSys.keepOnly = false)
    (hu : Γ.ref u = some (.VTypeBox A)) : Γ.boxIn (.step u .box) = some A := by
  change (if ModalSys.keepOnly = true then none
    else (match Γ.ref u with | some (.VTypeBox B) => some B | _ => none)) = some A
  rw [if_neg (by simp [hk]), hu]

theorem boxIn_box_none {Γ : Ctx} {u : VarSymb} (hu : Γ.ref u = none) :
    Γ.boxIn (.step u .box) = none := by
  change (if ModalSys.keepOnly = true then none
    else (match Γ.ref u with | some (.VTypeBox B) => some B | _ => none)) =
      (none : Option VarType)
  rw [hu]
  split_ifs <;> rfl

theorem ref_nonproj (Γ : Ctx) : ∀ {v : VarSymb}, v.lastProj = false → Γ.ref v = Γ v
  | .root _, _ => rfl
  | .step v s, h => by
      change (if s.isProj then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = _
      have hs : s.isProj = false := h
      rw [if_neg (Bool.eq_false_iff.mp hs)]

theorem ref_step_proj (Γ : Ctx) (v : VarSymb) {s : Step} (hs : s.isProj = true) :
    Γ.ref (.step v s) = (Γ.ref v).bind (·.step s) := by
  change (if s.isProj then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = _
  rw [if_pos hs]

theorem ref_step_nonproj (Γ : Ctx) (v : VarSymb) {s : Step} (hs : ¬ s.isProj = true) :
    Γ.ref (.step v s) = Γ (.step v s) := by
  change (if s.isProj then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = _
  rw [if_neg hs]

/-- The content of a reachable possible address is reachable in its view. -/
theorem ref_diaIn_of {Γ : Ctx} {w : VarSymb} {A : VarType} (h : Γ.ref w = some (.VTypeDia A)) :
    (Γ.diaIn w).ref (.step w .dia) = some A := by
  rw [ref_nonproj _ (rfl : (VarSymb.step w .dia).lastProj = false)]
  change (if w = w then (match Γ.ref w with | some (.VTypeDia X) => some X | _ => none)
    else none) = some A
  rw [if_pos rfl, h]

theorem ref_none_of_rootFresh {Γ : Ctx} {r : Root} (h : ∀ v, v.rt = r → Γ v = none) :
    ∀ v, v.rt = r → Γ.ref v = none := by
  intro v
  induction v with
  | root r' => intro hv; exact h _ hv
  | step v s ih =>
      intro hv
      simp only [ref]
      split_ifs
      · simp only [ih hv, Option.bind_none]
      · exact h _ hv

theorem Le.ref {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ {v : VarSymb} {T : VarType}, Γ.ref v = some T → Γ'.ref v = some T := by
  intro v
  induction v with
  | root r => intro T hv; exact h _ _ hv
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref] at hv ⊢
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [hU] at hv; rw [ih hU]; exact hv
      · exact h _ _ hv

/-- The witnesses of a `□` view: the reachable possible objects, with `Opt` on. -/
theorem boxIn_wit {Γ : Ctx} {y : VarSymb} {X : VarType} :
    Γ.boxIn.wit y = some X ↔ ModalSys.Opt = true ∧ Γ.ref y = some (.VTypeDia X) := by
  change (if ModalSys.Opt = true then (match Γ.ref y with
    | some (.VTypeDia X) => some X
    | _ => none) else none) = some X ↔ _
  constructor
  · intro h
    split_ifs at h with hO
    refine ⟨hO, ?_⟩
    cases hu : Γ.ref y with
    | none => rw [hu] at h; cases h
    | some U =>
        rw [hu] at h
        cases U <;> first | (cases h; done) | (cases h; rfl)
  · rintro ⟨hO, hu⟩
    rw [if_pos hO, hu]

theorem Le.boxIn {Γ Γ' : Ctx} (h : Γ.Le Γ') : Γ.boxIn.Le Γ'.boxIn := by
  refine ⟨fun v T hv => ?_, fun y X hy => ?_⟩
  swap
  · obtain ⟨hO, hu⟩ := boxIn_wit.mp hy
    exact boxIn_wit.mpr ⟨hO, h.ref hu⟩
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := boxIn_box hv
      exact boxIn_box_of hk (h.ref hu)
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := boxIn_keep hv
      exact boxIn_keep_of' hF (h.ref hu) hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem Le.diaIn {Γ Γ' : Ctx} (h : Γ.Le Γ') (x : VarSymb) : (Γ.diaIn x).Le (Γ'.diaIn x) := by
  refine ⟨fun v T hv => ?_, h.boxIn.wit⟩
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      change (if u = x then (match Γ'.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T
      split_ifs at hv ⊢ with hux
      · cases hx : Γ.ref x with
        | none => rw [hx] at hv; cases hv
        | some U => rw [hx] at hv; rw [h.ref hx]; exact hv
  | .step u .box => exact h.boxIn (.step u .box) T hv
  | .step u .keep => exact h.boxIn (.step u .keep) T hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem le_boxIn_diaIn (Γ : Ctx) (x : VarSymb) : Γ.boxIn.Le (Γ.diaIn x) := by
  refine ⟨fun v T hv => ?_, fun _ _ hy => hy⟩
  match v with
  | .step u .box => exact hv
  | .step u .keep => exact hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem SlotsFrom.boxIn {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) : Γ.boxIn.SlotsFrom d := by
  refine ⟨fun v n hv hn => ?_, fun y n hy hn => ?_⟩
  swap
  · rcases hw : Γ.boxIn.wit y with _ | X
    · rfl
    · have hfresh : ∀ w, w.rt = .bnd n → Γ w = none := fun w hw => h w n hw hn
      have h₁ := (boxIn_wit.mp hw).2
      rw [ref_none_of_rootFresh hfresh y hy] at h₁
      cases h₁
  have hfresh : ∀ w, w.rt = .bnd n → Γ w = none := fun w hw => h w n hw hn
  match v with
  | .step u .box => exact boxIn_box_none (ref_none_of_rootFresh hfresh u hv)
  | .step u .keep => exact boxIn_keep_none (ref_none_of_rootFresh hfresh u hv)
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .dia => rfl
  | .step _ .here => rfl

theorem SlotsFrom.diaIn {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (x : VarSymb) :
    (Γ.diaIn x).SlotsFrom d := by
  refine ⟨fun v n hv hn => ?_, (h.boxIn).wit⟩
  have hfresh : ∀ w, w.rt = .bnd n → Γ w = none := fun w hw => h w n hw hn
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = none
      split_ifs with hux
      · rw [← hux]
        simp only [ref_none_of_rootFresh hfresh u hv]
      · rfl
  | .step u .box => exact h.boxIn (.step u .box) n hv hn
  | .step u .keep => exact h.boxIn (.step u .keep) n hv hn
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .here => rfl

theorem RootFresh.boxIn {Γ : Ctx} {r : Root} (h : Γ.RootFresh r) : Γ.boxIn.RootFresh r := by
  refine ⟨fun v hv => ?_, fun y hy => ?_⟩
  swap
  · rcases hw : Γ.boxIn.wit y with _ | X
    · rfl
    · have h₁ := (boxIn_wit.mp hw).2
      rw [ref_none_of_rootFresh h y hy] at h₁
      cases h₁
  match v with
  | .step u .box => exact boxIn_box_none (ref_none_of_rootFresh h u hv)
  | .step u .keep => exact boxIn_keep_none (ref_none_of_rootFresh h u hv)
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .dia => rfl
  | .step _ .here => rfl

theorem RootFresh.diaIn {Γ : Ctx} {r : Root} (h : Γ.RootFresh r) (x : VarSymb) :
    (Γ.diaIn x).RootFresh r := by
  refine ⟨fun v hv => ?_, (h.boxIn).wit⟩
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = none
      split_ifs with hux
      · rw [← hux]
        simp only [ref_none_of_rootFresh h u hv]
      · rfl
  | .step u .box => exact h.boxIn (.step u .box) hv
  | .step u .keep => exact h.boxIn (.step u .keep) hv
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .here => rfl

instance {Γ : Ctx} [h : Γ.NoSlots] : Γ.boxIn.NoSlots := ⟨h.slots.boxIn⟩

instance {Γ : Ctx} [h : Γ.NoSlots] {x : VarSymb} : (Γ.diaIn x).NoSlots := ⟨h.slots.diaIn x⟩

/-! ### The view of a witness (branch `wip/in-atom`, docs §12.16) -/

/-- ⭐**The view of the witness `y`** (`WFF.optx`): the same level, with `y`'s content along the
    arrow declared at `y.dia`.  Nothing is hidden and nothing changes type: a witness's content
    address is free or holds its content already (`Ctx.wit_dia`), so `Γ` sits inside the view
    (`Ctx.le_optIn`).  In a `□` view it declares what `Γ.diaIn y` does. -/
def optIn (Γ : Ctx) (y : VarSymb) : Ctx where
  ty v :=
    if v = .step y .dia then
      match Γ.wit y with
      | some X => some X
      | none => Γ v
    else Γ v
  wit := Γ.wit
  wit_dia y' X h := by
    by_cases hy : y' = y
    · subst hy
      right
      simp [h]
    · have hne : VarSymb.step y' .dia ≠ .step y .dia := fun he => hy (VarSymb.step.inj he).1
      simp only [if_neg hne]
      exact Γ.wit_dia y' X h

omit [ModalSys] in
theorem optIn_apply (Γ : Ctx) (y v : VarSymb) :
    Γ.optIn y v = if v = .step y .dia then (match Γ.wit y with
      | some X => some X
      | none => Γ v) else Γ v := rfl

omit [ModalSys] in
theorem optIn_content_none {Γ : Ctx} {y : VarSymb} (hw : Γ.wit y = none) :
    Γ.optIn y (.step y .dia) = Γ (.step y .dia) := by
  rw [optIn_apply, if_pos rfl, hw]

omit [ModalSys] in
/-- The content of the witness `y`, in its view. -/
theorem optIn_content {Γ : Ctx} {y : VarSymb} {X : VarType} (h : Γ.wit y = some X) :
    Γ.optIn y (.step y .dia) = some X := by
  simp [optIn, h]

omit [ModalSys] in
theorem optIn_ne {Γ : Ctx} {y v : VarSymb} (hv : v ≠ .step y .dia) : Γ.optIn y v = Γ v := by
  simp [optIn, hv]

omit [ModalSys] in
/-- ⭐A context sits inside the view of any of its witnesses. -/
theorem le_optIn (Γ : Ctx) (y : VarSymb) : Γ.Le (Γ.optIn y) := by
  refine ⟨fun v T hv => ?_, fun _ _ hy => hy⟩
  by_cases hc : v = .step y .dia
  · subst hc
    cases hw : Γ.wit y with
    | none => simp [optIn, hw, hv]
    | some X =>
        rcases Γ.wit_dia y X hw with h | h
        · rw [h] at hv; cases hv
        · rw [h] at hv; cases hv; exact optIn_content hw
  · rw [optIn_ne hc]; exact hv

omit [ModalSys] in
theorem Le.optIn {Γ Γ' : Ctx} (h : Γ.Le Γ') (y : VarSymb) : (Γ.optIn y).Le (Γ'.optIn y) := by
  refine ⟨fun v T hv => ?_, h.wit⟩
  by_cases hc : v = .step y .dia
  · subst hc
    rcases hw : Γ.wit y with _ | X
    · rw [optIn_content_none hw] at hv
      exact (le_optIn Γ' y) _ _ (h _ _ hv)
    · rw [optIn_content hw] at hv
      cases hv
      exact optIn_content (h.wit y _ hw)
  · rw [optIn_ne hc] at hv ⊢
    exact h _ _ hv

omit [ModalSys] in
theorem SlotsFrom.optIn {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (y : VarSymb) :
    (Γ.optIn y).SlotsFrom d := by
  refine ⟨fun v n hv hn => ?_, h.wit⟩
  by_cases hc : v = .step y .dia
  · subst hc
    have h₀ : Γ (.step y .dia) = none := h _ n hv hn
    have hw : Γ.wit y = none := h.wit y n hv hn
    rw [optIn_content_none hw]
    exact h₀
  · rw [optIn_ne hc]
    exact h v n hv hn

instance {Γ : Ctx} [h : Γ.NoSlots] {y : VarSymb} : (Γ.optIn y).NoSlots := ⟨h.slots.optIn y⟩

/-- ⭐The `◇_z` view sits inside the view of the witness `z` in the `□` view (with `Opt` on): a
    `diatm z b`'s body is a body there too, so substitution carries it over unchanged. -/
theorem le_diaIn_boxIn_optIn {Γ : Ctx} {z : VarSymb} {X : VarType} (hO : ModalSys.Opt = true)
    (hz : Γ.ref z = some (.VTypeDia X)) : (Γ.diaIn z).Le (Γ.boxIn.optIn z) := by
  refine ⟨fun v T hv => ?_, fun _ _ hy => hy⟩
  by_cases hc : v = .step z .dia
  · subst hc
    have h₁ : (Γ.diaIn z) (.step z .dia) = some X := ref_diaIn_of hz |>.symm.trans
      (ref_nonproj _ rfl) |>.symm
    rw [h₁] at hv
    cases hv
    exact optIn_content (boxIn_wit.mpr ⟨hO, hz⟩)
  · rw [optIn_ne hc]
    match v, hc with
    | .step u .dia, hc =>
        change (if u = z then _ else none) = some T at hv
        rw [if_neg (fun he => hc (by rw [he]))] at hv
        cases hv
    | .step u .box, _ => exact hv
    | .step u .keep, _ => exact hv
    | .root _, _ => exact hv
    | .step _ .fst, _ => exact hv
    | .step _ .snd, _ => exact hv
    | .step _ .here, _ => exact hv

omit [ModalSys] in
theorem RootFresh.optIn {Γ : Ctx} {r : Root} (h : Γ.RootFresh r) (y : VarSymb) :
    (Γ.optIn y).RootFresh r := by
  refine ⟨fun v hv => ?_, h.wit⟩
  by_cases hc : v = .step y .dia
  · subst hc
    rw [optIn_content_none (h.wit y hv)]
    exact h _ hv
  · rw [optIn_ne hc]
    exact h v hv

theorem ref_insert_root (Γ : Ctx) (r : Root) (T : VarType) :
    (Γ.insert r T).ref (.root r) = some T := by
  simp [Ctx.ref, Ctx.insert]

theorem ref_insert_fst (Γ : Ctx) (r : Root) (A B : VarType) :
    (Γ.insert r (.VTypeProd A B)).ref (.step (.root r) .fst) = some A := by
  simp [Ctx.ref, Ctx.insert, Step.isProj, VarType.step]

theorem ref_insert_snd (Γ : Ctx) (r : Root) (A B : VarType) :
    (Γ.insert r (.VTypeProd A B)).ref (.step (.root r) .snd) = some B := by
  simp [Ctx.ref, Ctx.insert, Step.isProj, VarType.step]

end Ctx

end V12M
