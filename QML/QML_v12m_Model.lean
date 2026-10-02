import QML.QML_v12m_Terms

/-!
# QML v12m — models

A **pointed Kripke frame** with a base domain `D w` at each world and, for the modal types,
**carriers**: `Nec A w` (necessary objects) and `Pos A w` (possible objects).  A carrier is not a
set of semantic objects but a domain of its own, with an **injective evaluation map** into them:

* a necessary object evaluates to an object of the domain at every accessible world
  (`necEval`);
* a possible object evaluates to an **extent** — a set of accessible worlds — together with exactly
  one object of the domain at each world of the extent (`posEval`).

**Closure.**  The domains are closed under the **function algebra** `GFunc`: the definable maps
between types, built from function symbols and projections/pairing, together with their modal
lifts (`boxMap`, `boxPair`, `boxUnit`, `diaMap`, `strength`).  The model supplies the lifts on
carriers (`Ops`) and their evaluation laws.

**Weak T.**  Accessibility is reflexive (`Frame.refl`), and a necessary object can be read at the
current world (`GFunc.extract`, evaluated by `Ops.necExtract`, which is `necEval` at the world
itself).

**Weak 4.**  Accessibility is transitive (`Frame.trans`), and a necessary object can be kept at an
accessible world as the necessary object of its values further on (`GFunc.dup`, evaluated by
`Ops.necDup`): with T, `□` is a comonad.
-/

namespace V12M

universe u v

variable [ModalSys]

/-- A pointed frame with base domains, modal carriers, and the interpretation of the signature. -/
structure Frame (σ : Signature) where
  W : Type u
  actual : W
  /-- The **arrows** from one world to another. A `Prop`-valued `R` is an ordinary accessibility
      relation (at most one arrow per pair); a `Type`-valued one lets two arrows between the same
      worlds carry different values, which the canonical construction for B and 5 uses before it
      is unravelled (`docs/v12-arrow-canonical.md`). -/
  R : W → W → Sort v
  /-- Under T, an identity arrow at each world. -/
  refl : ModalSys.T = true → ∀ w, R w w
  /-- Under 4, arrows compose. -/
  trans : ModalSys.Four = true → ∀ {w v s : W}, R w v → R v s → R w s
  /-- Under D, every world has an arrow out. -/
  serial : ModalSys.D = true → ∀ w, ∃ v, Nonempty (R w v)
  /-- Under B, every arrow has some arrow back.  Only existence: which arrow comes back, and
      whether a round trip agrees with anything, is left open (`docs/v12-arrow-canonical.md` §6). -/
  symm : ModalSys.B = true → ∀ {w v : W}, R w v → Nonempty (R v w)
  /-- Under T and 4, the identity arrows are units for composition: reading a kept object at the
      world it was kept at is reading the object (`u.keep.here`), and keeping and then reading at
      once is reading. Automatic for a relational frame. -/
  refl_trans : ∀ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {w v : W} (a : R w v),
    trans hF (refl hT w) a = a
  trans_refl : ∀ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {w v : W} (a : R w v),
    trans hF a (refl hT v) = a
  /-- Under 4, composition is associative: keeping twice is keeping once, whichever pair of steps
      is merged first. Automatic for a relational frame. -/
  trans_assoc : ∀ (hF : ModalSys.Four = true) {w v s t : W} (a : R w v) (b : R v s)
    (c : R s t), trans hF (trans hF a b) c = trans hF a (trans hF b c)
  D : W → Type u
  Nec : VarType → W → Type u
  Pos : VarType → W → Type u
  funcInterp : (f : σ.FuncSyms) → (w : W) → (Fin (σ.funcArity f) → D w) → D w
  relInterp : (r : σ.RelSyms) → (w : W) → (Fin (σ.relArity r) → D w) → Prop

namespace Frame

variable {σ : Signature} (F : Frame.{u, v} σ)

/-- The arrows out of a world, each with its target. For a relational frame this is the set of
    accessible worlds. -/
abbrev Acc (w : F.W) : Type (max u v) := Σ w' : F.W, PLift (F.R w w')

/-- The identity arrow at a world, under T: the arrow `T`'s rules read along. -/
abbrev reflAcc (hT : ModalSys.T = true) (w : F.W) : F.Acc w := ⟨w, ⟨F.refl hT w⟩⟩

/-- The domain of a type at a world. -/
def Dom : VarType → F.W → Type u
  | .Var, w => F.D w
  | .VTypeOne, _ => PUnit
  | .VTypeProd A B, w => Dom A w × Dom B w
  | .VTypeBox A, w => F.Nec A w
  | .VTypeDia A, w => F.Pos A w

/-- What a necessary object delivers: an object at every accessible world. -/
abbrev NecSec (A : VarType) (w : F.W) : Type (max u v) := (w' : F.Acc w) → F.Dom A w'.1

/-- What a possible object delivers: an extent, and exactly one object at each of its worlds. -/
abbrev PosSec (A : VarType) (w : F.W) : Type (max u v) :=
  Σ E : Set (F.Acc w), (w' : E) → F.Dom A w'.1.1

end Frame

/-! ## The function algebra -/

/-- Definable maps between types. -/
inductive GFunc (σ : Signature) : VarType → VarType → Type where
  | id (A : VarType) : GFunc σ A A
  | comp {A B C : VarType} : GFunc σ B C → GFunc σ A B → GFunc σ A C
  | fst {A B : VarType} : GFunc σ (.VTypeProd A B) A
  | snd {A B : VarType} : GFunc σ (.VTypeProd A B) B
  | pair {A B C : VarType} : GFunc σ A B → GFunc σ A C → GFunc σ A (.VTypeProd B C)
  | unit (A : VarType) : GFunc σ A .VTypeOne
  | func {A : VarType} (f : σ.FuncSyms) :
      (Fin (σ.funcArity f) → GFunc σ A .Var) → GFunc σ A .Var
  /-- Apply a map inside a box. -/
  | boxMap {A B : VarType} : GFunc σ A B → GFunc σ (.VTypeBox A) (.VTypeBox B)
  /-- Two necessary objects make a necessary pair. -/
  | boxPair (A B : VarType) :
      GFunc σ (.VTypeProd (.VTypeBox A) (.VTypeBox B)) (.VTypeBox (.VTypeProd A B))
  /-- The necessary unit. -/
  | boxUnit : GFunc σ .VTypeOne (.VTypeBox .VTypeOne)
  /-- Apply a map inside a diamond. -/
  | diaMap {A B : VarType} : GFunc σ A B → GFunc σ (.VTypeDia A) (.VTypeDia B)
  /-- A necessary object rides along inside a possible one. -/
  | strength (A B : VarType) :
      GFunc σ (.VTypeProd (.VTypeBox A) (.VTypeDia B)) (.VTypeDia (.VTypeProd A B))
  /-- Under T: a necessary object read at the current world. -/
  | extract {A : VarType} (hT : ModalSys.T = true) : GFunc σ (.VTypeBox A) A
  /-- Under 4: a necessary object kept at each accessible world. -/
  | dup {A : VarType} (hF : ModalSys.Four = true) :
      GFunc σ (.VTypeBox A) (.VTypeBox (.VTypeBox A))

/-- Under 4, keep an object of a necessary type. -/
def GFunc.keep {σ : Signature} (hF : ModalSys.Four = true) :
    {T : VarType} → (∃ A, T = .VTypeBox A) → GFunc σ T (.VTypeBox T)
  | .VTypeBox _, _ => .dup hF
  | .Var, h => False.elim (h.elim fun _ e => by cases e)
  | .VTypeOne, h => False.elim (h.elim fun _ e => by cases e)
  | .VTypeProd _ _, h => False.elim (h.elim fun _ e => by cases e)
  | .VTypeDia _, h => False.elim (h.elim fun _ e => by cases e)

/-- The lifts of the function algebra to the carriers. -/
structure Frame.Ops {σ : Signature} (F : Frame.{u, v} σ) where
  necMap : {A B : VarType} → {w : F.W} → GFunc σ A B → F.Nec A w → F.Nec B w
  necPair : {A B : VarType} → {w : F.W} → F.Nec A w → F.Nec B w → F.Nec (.VTypeProd A B) w
  necUnit : {w : F.W} → F.Nec .VTypeOne w
  posMap : {A B : VarType} → {w : F.W} → GFunc σ A B → F.Pos A w → F.Pos B w
  posStrength : {A B : VarType} → {w : F.W} → F.Nec A w → F.Pos B w →
    F.Pos (.VTypeProd A B) w
  necExtract : {A : VarType} → {w : F.W} → ModalSys.T = true → F.Nec A w → F.Dom A w
  necDup : {A : VarType} → {w : F.W} → ModalSys.Four = true → F.Nec A w →
    F.Nec (.VTypeBox A) w

/-- Evaluating a definable map at a world. -/
def GFunc.eval {σ : Signature} {F : Frame.{u, v} σ} (ops : F.Ops) :
    {A B : VarType} → GFunc σ A B → (w : F.W) → F.Dom A w → F.Dom B w
  | _, _, .id _, _, a => a
  | _, _, .comp g f, w, a => GFunc.eval ops g w (GFunc.eval ops f w a)
  | _, _, .fst, _, a => a.1
  | _, _, .snd, _, a => a.2
  | _, _, .pair f g, w, a => (GFunc.eval ops f w a, GFunc.eval ops g w a)
  | _, _, .unit _, _, _ => PUnit.unit
  | _, _, .func f args, w, a => F.funcInterp f w (fun i => GFunc.eval ops (args i) w a)
  | _, _, .boxMap f, _, n => ops.necMap f n
  | _, _, .boxPair _ _, _, p => ops.necPair p.1 p.2
  | _, _, .boxUnit, _, _ => ops.necUnit
  | _, _, .diaMap f, _, p => ops.posMap f p
  | _, _, .strength _ _, _, p => ops.posStrength p.1 p.2
  | _, _, .extract hT, _, n => ops.necExtract hT n
  | _, _, .dup hF, _, n => ops.necDup hF n

/-! ## Semantic annotations

Under T a possible object carries, besides its section, a **shape**: the semantic counterpart of a
term's annotation (docs §10.27–10.28).  Two possible objects are identified only when they have the
same section *and* the same shape, so the semantics identifies exactly what `eqRec` can compare,
and never two objects over different witnesses.

A shape is a tree over the type, like `Ann`, whose labels are **leaves** anchored at the object's
world.  A leaf is either a root possibility with a syntactic path into its content, which survives
an empty extent, or a family with one leaf per arrow, for positions reached through a necessary
object.  Levels are counted from the anchor (`Frame.Leaf.collapse`, `Frame.Leaf.shift`). -/

universe x

/-- An annotation tree over a type, with labels of any type at its `◇` nodes.  `Ann` has the same
    shape with addresses as labels. -/
inductive Shp (L : Type x) : VarType → Type x
  | var : Shp L .Var
  | one : Shp L .VTypeOne
  | prod {A B : VarType} (a : Shp L A) (b : Shp L B) : Shp L (.VTypeProd A B)
  | box {A : VarType} (a : Shp L A) : Shp L (.VTypeBox A)
  | dia {A : VarType} (ℓ : L) (a : Shp L A) : Shp L (.VTypeDia A)

namespace Shp

variable {L : Type x}

def fst {A B : VarType} : Shp L (.VTypeProd A B) → Shp L A
  | .prod a _ => a

def snd {A B : VarType} : Shp L (.VTypeProd A B) → Shp L B
  | .prod _ b => b

def inner {A : VarType} : Shp L (.VTypeBox A) → Shp L A
  | .box a => a

/-- The label of a `◇` node: the possibility itself. -/
def label {A : VarType} : Shp L (.VTypeDia A) → L
  | .dia ℓ _ => ℓ

/-- The shape of a possible object's content. -/
def body {A : VarType} : Shp L (.VTypeDia A) → Shp L A
  | .dia _ a => a

def map {L' : Type x} (g : L → L') : {A : VarType} → Shp L A → Shp L' A
  | _, .var => .var
  | _, .one => .one
  | _, .prod a b => .prod (a.map g) (b.map g)
  | _, .box a => .box (a.map g)
  | _, .dia ℓ a => .dia (g ℓ) (a.map g)

end Shp

/-- The path starts with a level step. -/
def Step.headLvl : List Step → Bool
  | [] => false
  | t :: _ => !t.isProj

/-- Collapse the level step `i` levels from the front of a path: a `box` becomes `here`, a `keep`
    disappears — `VarSymb.collapse`, counted from the other end.  (On a `dia` this is junk.)

    ⭐One case differs from `VarSymb.collapse`: a level step right after a `keep` is collapsed by
    deleting the `keep` — "kept, then read where it was kept, is read" (docs §10.30–10.31).
    It makes `collapseAt (j + 1) ∘ shiftAt j` the identity on every path, the second counit law of
    the `□` comonad, and it agrees with `VarSymb.collapse` on every T+4-normal path (no `box`
    after a `keep`), which is all the syntax produces. -/
def Step.collapseAt : ℕ → List Step → List Step
  | _, [] => []
  | i, s :: p =>
      if s.isProj then s :: Step.collapseAt i p
      else
        match i with
        | 0 => if s = .keep then p else .here :: p
        | i + 1 =>
            if i = 0 ∧ s = .keep ∧ Step.headLvl p = true then p else s :: Step.collapseAt i p

/-- Insert a `keep` before the level step `i` levels from the front of a path — `VarSymb.shift`,
    counted from the other end. -/
def Step.shiftAt : ℕ → List Step → List Step
  | _, [] => []
  | i, s :: p =>
      if s.isProj then s :: Step.shiftAt i p
      else
        match i with
        | 0 => .keep :: s :: p
        | i + 1 => s :: Step.shiftAt i p

/-- ⭐A leaf of a semantic annotation, anchored at a world (docs §10.28): a **root** possibility with
    a syntactic path into its content, or a **family** with one leaf at the target of each arrow. -/
inductive Frame.Leaf {σ : Signature} (F : Frame.{u, v} σ) (Root : F.W → Type u) :
    F.W → Type (max u v)
  | root {w : F.W} (r : Root w) (p : List Step) : Frame.Leaf F Root w
  | fam {w : F.W} (f : (s : F.Acc w) → Frame.Leaf F Root s.1) : Frame.Leaf F Root w

namespace Frame.Leaf

variable {σ : Signature} {F : Frame.{u, v} σ} {Root : F.W → Type u}

/-- Under T, collapse the level `i` steps from the anchor: a family is read at the identity arrow
    there, and a root path loses that level step (`Step.collapseAt`). -/
def collapse (hT : ModalSys.T = true) : ℕ → {w : F.W} → Frame.Leaf F Root w → Frame.Leaf F Root w
  | i, _, .root r p => .root r (Step.collapseAt i p)
  | 0, w, .fam f => f (F.reflAcc hT w)
  | i + 1, _, .fam f => .fam fun s => collapse hT i (f s)

/-- Under 4, insert a level `i` steps from the anchor: a family is reindexed by composite arrows,
    and a root path gains a `keep` (`Step.shiftAt`). -/
def shift (hF : ModalSys.Four = true) : ℕ → {w : F.W} → Frame.Leaf F Root w → Frame.Leaf F Root w
  | i, _, .root r p => .root r (Step.shiftAt i p)
  | 0, _, .fam f => .fam fun s => .fam fun t => f ⟨t.1, ⟨F.trans hF s.2.down t.2.down⟩⟩
  | i + 1, _, .fam f => .fam fun s => shift hF i (f s)

end Frame.Leaf

/-- ⭐How a definable map moves the shape of its argument: positions are rearranged as the map
    rearranges components, labels are kept, and `extract`/`dup` collapse/shift the level they act
    at.  `j` is the number of levels above the current position. -/
def GFunc.shp {σ : Signature} {F : Frame.{u, v} σ} {Root : F.W → Type u} {w : F.W} :
    {A B : VarType} → GFunc σ A B → ℕ →
      Shp (Frame.Leaf F Root w) A → Shp (Frame.Leaf F Root w) B
  | _, _, .id _, _, a => a
  | _, _, .comp g f, j, a => GFunc.shp g j (GFunc.shp f j a)
  | _, _, .fst, _, a => a.fst
  | _, _, .snd, _, a => a.snd
  | _, _, .pair f g, j, a => .prod (GFunc.shp f j a) (GFunc.shp g j a)
  | _, _, .unit _, _, _ => .one
  | _, _, .func _ _, _, _ => .var
  | _, _, .boxMap f, j, a => .box (GFunc.shp f (j + 1) a.inner)
  | _, _, .boxPair _ _, _, a => .box (.prod a.fst.inner a.snd.inner)
  | _, _, .boxUnit, _, _ => .box .one
  | _, _, .diaMap f, j, a => .dia a.label (GFunc.shp f (j + 1) a.body)
  | _, _, .strength _ _, _, a => .dia a.snd.label (.prod a.fst.inner a.snd.body)
  | _, _, .extract hT, j, a => a.inner.map (Frame.Leaf.collapse hT j)
  | _, _, .dup hF, j, a => .box (.box (a.inner.map (Frame.Leaf.shift hF j)))

/-- A family of shapes, one at the target of each arrow, as one shape whose leaves are families. -/
def Frame.transposeShp {σ : Signature} {F : Frame.{u, v} σ} {Root : F.W → Type u} {w : F.W} :
    {A : VarType} → ((s : F.Acc w) → Shp (Frame.Leaf F Root s.1) A) →
      Shp (Frame.Leaf F Root w) A
  | .Var, _ => .var
  | .VTypeOne, _ => .one
  | .VTypeProd _ _, g =>
      .prod (Frame.transposeShp fun s => (g s).fst) (Frame.transposeShp fun s => (g s).snd)
  | .VTypeBox _, g => .box (Frame.transposeShp fun s => (g s).inner)
  | .VTypeDia _, g => .dia (.fam fun s => (g s).label) (Frame.transposeShp fun s => (g s).body)

/-- The shape of any object, from the shapes of possible objects: componentwise at a product, and
    at a necessary object the family of its values' shapes. -/
def Frame.domShape {σ : Signature} {F : Frame.{u, v} σ} {Root : F.W → Type u}
    (necEval : ∀ {A : VarType} {w : F.W}, F.Nec A w → F.NecSec A w)
    (shape : ∀ {A : VarType} {w : F.W}, F.Pos A w → Shp (Frame.Leaf F Root w) (.VTypeDia A)) :
    {A : VarType} → {w : F.W} → F.Dom A w → Shp (Frame.Leaf F Root w) A
  | .Var, _, _ => .var
  | .VTypeOne, _, _ => .one
  | .VTypeProd _ _, _, a =>
      .prod (Frame.domShape necEval shape a.1) (Frame.domShape necEval shape a.2)
  | .VTypeBox _, _, n =>
      .box (Frame.transposeShp fun s => Frame.domShape necEval shape (necEval n s))
  | .VTypeDia _, _, p => shape p

/-! ## Models -/

/-- ⭐A model: a pointed frame whose carriers evaluate injectively and are closed under the
    function algebra. -/
structure Model (σ : Signature) where
  frame : Frame.{u, v} σ
  necEval : {A : VarType} → {w : frame.W} → frame.Nec A w → frame.NecSec A w
  nec_inj : ∀ {A : VarType} {w : frame.W}, Function.Injective (@necEval A w)
  /-- Under T, the root possibilities: what a possible object's shape is ultimately built on. -/
  RootPoss : frame.W → Type u
  /-- ⭐**Evaluation of a possible object** (docs §10.27, §10.35): its **section** — an extent, and
      one object at each world of it — and, under T, its **shape**, the semantic annotation that
      records where each possibility inside it comes from.  `Model.posEval` and `Model.shape` are
      the two components. -/
  posFull : {A : VarType} → {w : frame.W} → frame.Pos A w →
    frame.PosSec A w × (ModalSys.T = true → Shp (frame.Leaf RootPoss w) (.VTypeDia A))
  /-- ⭐A possible object **is** its extent, its contents and (under T) its shape: two objects
      agreeing on all three are equal.  So objects over different witnesses, or over one witness
      with differently annotated contents, are never identified (docs §10.24–10.27); without T
      this is plain injectivity of the section. -/
  posFull_inj : ∀ {A : VarType} {w : frame.W}, Function.Injective (@posFull A w)
  ops : frame.Ops
  necMap_eval : ∀ {A B : VarType} {w : frame.W} (f : GFunc σ A B) (n : frame.Nec A w)
    (w' : frame.Acc w), necEval (ops.necMap f n) w' = GFunc.eval ops f w'.1 (necEval n w')
  necPair_eval : ∀ {A B : VarType} {w : frame.W} (a : frame.Nec A w) (b : frame.Nec B w)
    (w' : frame.Acc w),
    necEval (ops.necPair a b) w' = ((necEval a w', necEval b w') : frame.Dom (.VTypeProd A B) w'.1)
  /-- Mapping keeps the extent, maps the contents, keeps the possibility and moves the content's
      shape as the map moves components. -/
  posMap_full : ∀ {A B : VarType} {w : frame.W} (f : GFunc σ A B) (p : frame.Pos A w),
    posFull (ops.posMap f p) =
      (⟨(posFull p).1.1, fun w' => GFunc.eval ops f w'.1.1 ((posFull p).1.2 w')⟩,
        fun hT => .dia ((posFull p).2 hT).label (f.shp 1 ((posFull p).2 hT).body))
  /-- A necessary object riding along keeps the extent, pairs its values into the contents, and
      contributes the family of its values' shapes. -/
  posStrength_full : ∀ {A B : VarType} {w : frame.W} (n : frame.Nec A w) (p : frame.Pos B w),
    posFull (ops.posStrength n p) =
      (⟨(posFull p).1.1, fun w' =>
          ((necEval n w'.1, (posFull p).1.2 w') : frame.Dom (.VTypeProd A B) w'.1.1)⟩,
        fun hT => .dia ((posFull p).2 hT).label
          (.prod (Frame.transposeShp fun s =>
              Frame.domShape necEval (fun q => (posFull q).2 hT) (necEval n s))
            ((posFull p).2 hT).body))
  necExtract_eval : ∀ {A : VarType} {w : frame.W} (hT : ModalSys.T = true) (n : frame.Nec A w),
    ops.necExtract hT n = necEval n ⟨w, ⟨frame.refl hT w⟩⟩
  necDup_eval : ∀ {A : VarType} {w : frame.W} (hF : ModalSys.Four = true) (n : frame.Nec A w)
    (v : frame.Acc w) (s : frame.Acc v.1),
    necEval (necEval (ops.necDup hF n) v) s = necEval n ⟨s.1, ⟨frame.trans hF v.2.down s.2.down⟩⟩
  /-- ⭐Strong T: every object has *some* possible object whose extent contains the current world,
      with the object as its content there.  This says on its own that `R` is reflexive wherever a
      domain is inhabited.

      Stated existentially rather than as an operation on `Frame.Ops`: strong T adds no term former,
      so nothing interprets a map from objects to possible objects, and none is intended — in
      particular there is no uniqueness and no naturality.  Demanding an operation would force the
      canonical model to choose one (and, if naturality were ever wanted, to make the choices
      cohere, which is what sank the `y.ret` design). -/
  posRet_exists : ∀ {A : VarType} {w : frame.W} (_hT : ModalSys.T = true)
    (_hS : ModalSys.TStrong = true) (_hA : A.diaFree = true)
    (a : frame.Dom A w), ∃ (p : frame.Pos A w) (hm : frame.reflAcc _hT w ∈ (posFull p).1.1),
      (posFull p).1.2 ⟨frame.reflAcc _hT w, hm⟩ = a
  /-- ⭐Strong D: some possible object has a nonempty extent.  Stated at `𝟙`, where the content
      carries nothing: `strength` then gives, for every necessary object, a possible object with
      the same extent whose content is that object's value — the `Nec → Pos` map, at every type. -/
  posSerial : ModalSys.DStrong = true → ∀ w : frame.W,
    ∃ p : frame.Pos .VTypeOne w, Nonempty (posFull p).1.1
  /-- ⭐**Indistinguishability**, which `Here` reads at its content (docs §10.23, §10.33): co-named
      objects are indistinguishable, not identical.  Only reflexivity is asked here; that related
      objects satisfy the same formulas mentions satisfaction, which is defined from the model, so
      it is the separate condition `Model.IndInvariant` — a model proper is one satisfying it. -/
  Ind : {A : VarType} → {w : frame.W} → frame.Dom A w → frame.Dom A w → Prop
  Ind_refl : ∀ {A : VarType} {w : frame.W} (o : frame.Dom A w), Ind o o

namespace Model

variable {σ : Signature} (M : Model.{u, v} σ)

/-- The section of a possible object: its extent, and its content at each world of it. -/
abbrev posEval {A : VarType} {w : M.frame.W} (p : M.frame.Pos A w) : M.frame.PosSec A w :=
  (M.posFull p).1

/-- ⭐Under T, the **shape** of a possible object — its semantic annotation (docs §10.27). -/
abbrev shape (hT : ModalSys.T = true) {A : VarType} {w : M.frame.W} (p : M.frame.Pos A w) :
    Shp (M.frame.Leaf M.RootPoss w) (.VTypeDia A) :=
  (M.posFull p).2 hT

variable {M}

/-- Possible objects agreeing on their section and, under T, their shape are equal. -/
theorem pos_inj {A : VarType} {w : M.frame.W} {p q : M.frame.Pos A w}
    (h : M.posEval p = M.posEval q) (hs : ∀ hT : ModalSys.T = true, M.shape hT p = M.shape hT q) :
    p = q :=
  M.posFull_inj (Prod.ext h (funext hs))

theorem posMap_eval {A B : VarType} {w : M.frame.W} (f : GFunc σ A B) (p : M.frame.Pos A w) :
    M.posEval (M.ops.posMap f p) =
      ⟨(M.posEval p).1, fun w' => GFunc.eval M.ops f w'.1.1 ((M.posEval p).2 w')⟩ :=
  congrArg Prod.fst (M.posMap_full f p)

theorem posStrength_eval {A B : VarType} {w : M.frame.W} (n : M.frame.Nec A w)
    (p : M.frame.Pos B w) :
    M.posEval (M.ops.posStrength n p) =
      ⟨(M.posEval p).1, fun w' =>
        ((M.necEval n w'.1, (M.posEval p).2 w') : M.frame.Dom (.VTypeProd A B) w'.1.1)⟩ :=
  congrArg Prod.fst (M.posStrength_full n p)

theorem shape_posMap (hT : ModalSys.T = true) {A B : VarType} {w : M.frame.W}
    (f : GFunc σ A B) (p : M.frame.Pos A w) :
    M.shape hT (M.ops.posMap f p) = .dia (M.shape hT p).label (f.shp 1 (M.shape hT p).body) :=
  congrFun (congrArg Prod.snd (M.posMap_full f p)) hT

theorem shape_posStrength (hT : ModalSys.T = true) {A B : VarType} {w : M.frame.W}
    (n : M.frame.Nec A w) (p : M.frame.Pos B w) :
    M.shape hT (M.ops.posStrength n p) =
      .dia (M.shape hT p).label
        (.prod (Frame.transposeShp fun s => Frame.domShape M.necEval (M.shape hT) (M.necEval n s))
          (M.shape hT p).body) :=
  congrFun (congrArg Prod.snd (M.posStrength_full n p)) hT

end Model

end V12M
