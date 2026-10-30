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
`Ops.necDup`): with T, `□` is a comonad.  A possible object is kept too, restricted: along an
arrow, its extent pulled back and its contents unchanged (`GFunc.dkeep`, evaluated by
`Ops.posKeep`, law `Model.posKeep_full`).  When shaped, the restriction's labels need a root at
the arrow's target: arrows act on roots (`Model.rootKeep`, `Arrows.RootKeep`).
-/

namespace V12M

universe u v

variable [ModalSys]

/-- ⭐The **arrows** of a frame: its worlds, the arrows between them and, under T and 4, identities
    and composition with their laws.  Split off from `Frame` because this is all a shape's leaves
    see (`Arrows.Leaf`), so shapes can be typed before a frame's carriers are built — the canonical
    model stores shapes inside its possible objects (docs §10.36).  The signature is not used: it
    is carried so that the definable maps acting on shapes (`GFunc.shp`) can read it off. -/
structure Arrows (σ : Signature) where
  W : Type u
  /-- The **arrows** from one world to another. A `Prop`-valued `R` is an ordinary accessibility
      relation (at most one arrow per pair); a `Type`-valued one lets two arrows between the same
      worlds carry different values, which the canonical construction for B and 5 uses before it
      is unravelled (`docs/v12-arrow-canonical.md`). -/
  R : W → W → Sort v
  /-- Under T, an identity arrow at each world. -/
  refl : ModalSys.T = true → ∀ w, R w w
  /-- Under 4, arrows compose. -/
  trans : ModalSys.Four = true → ∀ {w v s : W}, R w v → R v s → R w s
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

namespace Arrows

variable {σ : Signature} (F : Arrows.{u, v} σ)

/-- The arrows out of a world, each with its target. For a relational frame this is the set of
    accessible worlds. -/
abbrev Acc (w : F.W) : Type (max u v) := Σ w' : F.W, PLift (F.R w w')

/-- The identity arrow at a world, under T: the arrow `T`'s rules read along. -/
abbrev reflAcc (hT : ModalSys.T = true) (w : F.W) : F.Acc w := ⟨w, ⟨F.refl hT w⟩⟩

end Arrows

/-- A pointed frame with base domains, modal carriers, and the interpretation of the signature. -/
structure Frame (σ : Signature) extends Arrows.{u, v} σ where
  actual : W
  /-- Under D, every world has an arrow out. -/
  serial : ModalSys.D = true → ∀ w, ∃ v, Nonempty (R w v)
  /-- Under B, every arrow has some arrow back.  Only existence: which arrow comes back, and
      whether a round trip agrees with anything, is left open (`docs/v12-arrow-canonical.md` §6). -/
  symm : ModalSys.B = true → ∀ {w v : W}, R w v → Nonempty (R v w)
  /-- Under strong B, **the way home is unique**: at most one arrow between two worlds, so the value
      a round trip brings back is determined (`docs/v12-modal-extensions.md` §11.3).  Relational
      frames satisfy it outright. -/
  homeUnique : ModalSys.BStrong = true → ∀ {w v : W}, Subsingleton (R w v)
  /-- Under 5, **an arrow across**: for `a : w → v` and `b : w → s`, an arrow `side a b : v → s`
      (`docs/v12-modal-extensions.md` §3 5).  An operation, not mere existence, because `x.side`'s
      evaluation law names it (`Model.posSide_ext`), as `necDup_eval` names the composite. -/
  side : ModalSys.Five = true → ∀ {w v s : W}, R w v → R w s → R v s
  /-- Under 5, `side a` is injective, so a possible object's contents along it are well defined.
      Automatic for a relational frame, as are the laws below. -/
  side_inj : ∀ (hV : ModalSys.Five = true) {w v s s' : W} (a : R w v) (b : R w s) (b' : R w s'),
    (⟨s, ⟨side hV a b⟩⟩ : Σ t, PLift (R v t)) = ⟨s', ⟨side hV a b'⟩⟩ →
      (⟨s, ⟨b⟩⟩ : Σ t, PLift (R w t)) = ⟨s', ⟨b'⟩⟩
  /-- Under 5, across twice from one source is across once: `x.side.side` reads as `x.side`. -/
  side_side : ∀ (hV : ModalSys.Five = true) {w v s t : W} (a : R w v) (b : R w s) (e : R w t),
    side hV (side hV a b) (side hV a e) = side hV b e
  /-- Under 4 and 5, out and across is straight there: `u.keep` read along a side arrow is `u`. -/
  trans_side : ∀ (hF : ModalSys.Four = true) (hV : ModalSys.Five = true) {w v s : W} (a : R w v)
    (b : R w s), trans hF a (side hV a b) = b
  /-- Under 4 and 5, across from further in is across from the composite: `shift` sends `x.side`
      to `x.side.side`. -/
  side_trans : ∀ (hF : ModalSys.Four = true) (hV : ModalSys.Five = true) {w v t s : W}
    (a : R w v) (c : R v t) (e : R w s), side hV c (side hV a e) = side hV (trans hF a c) e
  /-- Under T and 5, across from the identity is the arrow itself: the collapse sends `x.side` to
      `x`. -/
  side_refl : ∀ (hT : ModalSys.T = true) (hV : ModalSys.Five = true) {w s : W} (b : R w s),
    side hV (refl hT w) b = b
  D : W → Type u
  Nec : VarType → W → Type u
  Pos : VarType → W → Type u
  funcInterp : (f : σ.FuncSyms) → (w : W) → (Fin (σ.funcArity f) → D w) → D w
  relInterp : (r : σ.RelSyms) → (w : W) → (Fin (σ.relArity r) → D w) → Prop

namespace Frame

variable {σ : Signature} (F : Frame.{u, v} σ)

/-- The domain of a type at a world. -/
def Dom : VarType → F.W → Type u
  | .Var, w => F.D w
  | .VTypeOne, _ => PUnit
  | .VTypeProd A B, w => Dom A w × Dom B w
  | .VTypeBox A, w => F.Nec A w
  | .VTypeDia A, w => F.Pos A w

/-- What a necessary object delivers: an object at every accessible world. -/
abbrev NecSec (A : VarType) (w : F.W) : Type (max u v) := (w' : F.Acc w) → F.Dom A w'.1

/-- Under 5, the arrow across from `a`'s target to `b`'s. -/
abbrev sideAcc (hV : ModalSys.Five = true) {w : F.W} (a b : F.Acc w) : F.Acc a.1 :=
  ⟨b.1, ⟨F.side hV a.2.down b.2.down⟩⟩

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
  /-- Under 4: a possible object kept, restricted, at each accessible world (staged: without T,
      docs §3 4, Finding 4). -/
  | dkeep {A : VarType} (hF : ModalSys.Four = true) :
      GFunc σ (.VTypeDia A) (.VTypeBox (.VTypeDia A))

/-- Under 4, keep an object of a keepable type: `dup` for a necessary object, `dkeep` for a
    possible one. -/
def GFunc.keep {σ : Signature} (hF : ModalSys.Four = true) :
    {T : VarType} → T.keepable = true → GFunc σ T (.VTypeBox T)
  | .VTypeBox _, _ => .dup hF
  | .VTypeDia _, _ => .dkeep hF
  | .Var, h => False.elim (Bool.false_ne_true h)
  | .VTypeOne, h => False.elim (Bool.false_ne_true h)
  | .VTypeProd _ _, h => False.elim (Bool.false_ne_true h)

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
  posKeep : {A : VarType} → {w : F.W} → ModalSys.Four = true →
    F.Pos A w → F.Nec (.VTypeDia A) w
  /-- Under 5, a possible object moved across (`x.side`): at each arrow `a`, its extent carried
      along `side a`, with the same contents. -/
  posSide : {A : VarType} → {w : F.W} → ModalSys.Five = true →
    F.Pos A w → F.Nec (.VTypeDia A) w

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
  | _, _, .dkeep hF, _, p => ops.posKeep hF p

/-! ## Semantic annotations

Under T or strong B (`ModalSys.shaped`) a possible object carries, besides its section, a
**shape**: the semantic counterpart of a term's annotation (docs §10.27–10.28).  Two possible
objects are identified only when they have the same section *and* the same shape, so the semantics
identifies exactly what `eqRec` can compare, and never two objects over different witnesses.

A shape is a tree over the type, like `Ann`, whose labels are **leaves** anchored at the object's
world.  A leaf is either a root possibility with a syntactic path into its content, which survives
an empty extent, or a family with one leaf per arrow, for positions reached through a necessary
object.  Levels are counted from the anchor (`Arrows.Leaf.collapse`, `Arrows.Leaf.shift`). -/

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

/-- ⭐**Well-formed shapes**, for a well-formedness of leaves by position: each leaf is
    well-formed at the level kinds from the anchor down to its node — `true` a `□`, `false` a
    `◇`, outermost first. -/
def WF (P : List Bool → L → Prop) : List Bool → {A : VarType} → Shp L A → Prop
  | _, _, .var => True
  | _, _, .one => True
  | lw, _, .prod a b => WF P lw a ∧ WF P lw b
  | lw, _, .box a => WF P (lw ++ [true]) a
  | lw, _, .dia ℓ a => P lw ℓ ∧ WF P (lw ++ [false]) a

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

/-- Insert a `keep` after the level step `i` levels from the front of a path, at the end if
    there is none after it: the kept possibility at that level, and below it everything reached
    through it (`Step.shiftAt`, which inserts only before a level step). -/
def Step.keepAt : ℕ → List Step → List Step
  | 0, [] => [.keep]
  | _ + 1, [] => []
  | i, s :: p =>
      if s.isProj then s :: Step.keepAt i p
      else
        match i with
        | 0 => .keep :: s :: p
        | i + 1 => s :: Step.keepAt i p

/-- At the `□` levels of a position, a path's level steps are not `dia`: a root's path does not
    cross a `□` level of its position by entering a possibility's content (docs §3 4, "The
    canonical root action's laws").  The other way round is allowed — the strength law moves a
    necessary component under a `◇` (`Arrows.Leaf.wf_relax`). -/
def Step.BoxOK : List Bool → List Step → Prop
  | _, [] => True
  | lw, s :: p =>
      if s.isProj then Step.BoxOK lw p
      else (lw.head? = some true → s ≠ .dia) ∧ Step.BoxOK lw.tail p

/-- One step of a root's path, on types: a projection by `VarType.step`, `dia` into a possibility's
    content, `keep` on a keepable type, `box` into a necessary object's contents when views show
    them (`ModalSys.keepOnly` off). -/
def Step.typeStep (T : VarType) : Step → Option VarType
  | .keep => if T.keepable then some T else none
  | .box => if ModalSys.keepOnly then none else T.step .box
  | s => T.step s

/-- A path walked on types. -/
def Step.walkTy : VarType → List Step → Option VarType
  | T, [] => some T
  | T, s :: p => (Step.typeStep T s).bind fun U => Step.walkTy U p

/-- A path is typed in `T` when each step applies and it ends at a possibility. -/
def Step.Typed (T : VarType) (p : List Step) : Prop := ∃ X, Step.walkTy T p = some (.VTypeDia X)

/-- ⭐**A root's path is typable** (docs §3 4, "Finding: untyped root paths are too weak for the
    laws"): typed in some type.  So it spells a position of some possibility's content, and no
    step contradicts another (a `keep` of a product, a projection out of a possibility).  Which
    type is the root's own is the root action's business. -/
def Step.Typable (p : List Step) : Prop := ∃ T, Step.Typed T p

/-- ⭐A leaf of a semantic annotation, anchored at a world (docs §10.28): a **root** possibility with
    a syntactic path into its content, or a **family** with one leaf at the target of each arrow. -/
inductive Arrows.Leaf {σ : Signature} (F : Arrows.{u, v} σ) (Root : F.W → Type u) :
    F.W → Type (max u v)
  | root {w : F.W} (r : Root w) (p : List Step) : Arrows.Leaf F Root w
  | fam {w : F.W} (f : (s : F.Acc w) → Arrows.Leaf F Root s.1) : Arrows.Leaf F Root w

namespace Arrows.Leaf

variable {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}

/-- ⭐**The labelling convention, without addresses** (docs §10.39; §3 4, "T + 4").  A leaf at a
    position whose level kinds from the anchor are `lw` is well-formed when a root's path has as
    many level steps as the position, and the position does not start with a `□` — a `□` at the
    anchor's level is crossed semantically, by a family — and a family's members are well-formed
    one level down, at their own anchors.  Of a root's path only the *number* of levels is asked,
    and that it does not enter a possibility at a `□` level (`Step.BoxOK`): the strength law moves
    a necessary component under a `◇`, changing a level's kind from `□` to `◇`; and the path
    is typable (`Step.Typable`). -/
def WF : List Bool → {w : F.W} → F.Leaf Root w → Prop
  | lw, _, .root _ p =>
      Step.levels p = lw.length ∧ lw.head? ≠ some true ∧ Step.BoxOK lw p ∧ Step.Typable p
  | [], _, .fam f => ∀ s, WF [] (f s)
  | _ :: q, _, .fam f => ∀ s, WF q (f s)

/-- Under T, collapse the level `i` steps from the anchor: a family is read at the identity arrow
    there, and a root path loses that level step (`Step.collapseAt`). -/
def collapse (hT : ModalSys.T = true) : ℕ → {w : F.W} → F.Leaf Root w → F.Leaf Root w
  | i, _, .root r p => .root r (Step.collapseAt i p)
  | 0, w, .fam f => f (F.reflAcc hT w)
  | i + 1, _, .fam f => .fam fun s => collapse hT i (f s)

/-- Under 4, insert a level `i` steps from the anchor: a family is reindexed by composite arrows,
    and a root path gains a `keep` (`Step.shiftAt`). -/
def shift (hF : ModalSys.Four = true) : ℕ → {w : F.W} → F.Leaf Root w → F.Leaf Root w
  | i, _, .root r p => .root r (Step.shiftAt i p)
  | 0, _, .fam f => .fam fun s => .fam fun t => f ⟨t.1, ⟨F.trans hF s.2.down t.2.down⟩⟩
  | i + 1, _, .fam f => .fam fun s => shift hF i (f s)

end Arrows.Leaf

/-- ⭐Under 4, **arrows act on root possibilities** (docs §3 4, "The leaf-valued root action"):
    `keep hF r a p` is the possibility at position `p` of `r`'s content, restricted along `a` — a
    leaf at the arrow's target, a root path where the restriction's content holds a possibility
    and a family where it holds necessary data of the target (what `strength` puts there).  A
    possible object kept along an arrow takes its labels from it (`Arrows.Leaf.keepAlong`).  Most
    actions send a root to a root (`Arrows.RootKeep.ofRoot`); the laws are `Arrows.RootKeepLaws`. -/
class Arrows.RootKeep {σ : Signature} (F : Arrows.{u, v} σ) (Root : F.W → Type u) where
  keep : ModalSys.Four = true → ∀ {w : F.W}, Root w → (a : F.Acc w) → List Step →
    Arrows.Leaf F Root a.1

/-- A root action sending a root possibility to a root possibility, its paths unchanged. -/
abbrev Arrows.RootKeep.ofRoot {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}
    (k : ModalSys.Four = true → ∀ {w : F.W}, Root w → (a : F.Acc w) → Root a.1) :
    Arrows.RootKeep F Root :=
  ⟨fun hF {_} r a p => .root (k hF r a) p⟩

namespace Arrows.Leaf

variable {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u} [Arrows.RootKeep F Root]

/-- A leaf restricted along an arrow, anchored at its target: a root by the root action, a family
    reindexed by composite arrows. -/
def keepAlong (hF : ModalSys.Four = true) {w : F.W} (a : F.Acc w) :
    F.Leaf Root w → F.Leaf Root a.1
  | .root r p => Arrows.RootKeep.keep hF r a p
  | .fam f => .fam fun t => f ⟨t.1, ⟨F.trans hF a.2.down t.2.down⟩⟩

/-- Under 4, keep the possibility at the level `i` steps from the anchor: at the anchor's own
    level semantically, a family of its restrictions (`keepAlong`); below a `◇` syntactically, a
    `keep` in the root path (`Step.keepAt`); through a family, at each of its entries. -/
def dk (hF : ModalSys.Four = true) : ℕ → {w : F.W} → F.Leaf Root w → F.Leaf Root w
  | 0, _, l => .fam fun s => keepAlong hF s l
  | i + 1, _, .root r p => .root r (Step.keepAt (i + 1) p)
  | i + 1, _, .fam f => .fam fun s => dk hF i (f s)

/-- Under 4, keep the leaves **inside** a kept possibility at level `i`: semantically at the
    anchor's level, as `dk`; below it the `keep` goes before the level step there, as a shift puts
    it (`Step.shiftAt`) — the content of `z.keep` is read in `z.keep`'s own view.  On a path that
    spells its position this is `dk`; it differs only on paths too short for their position,
    where `dk` would append (docs §3 4, "T + 4", the correction to (c)). -/
def dkB (hF : ModalSys.Four = true) : ℕ → {w : F.W} → F.Leaf Root w → F.Leaf Root w
  | 0, _, l => .fam fun s => keepAlong hF s l
  | i + 1, _, .root r p => .root r (Step.shiftAt (i + 1) p)
  | i + 1, _, .fam f => .fam fun s => dkB hF i (f s)

end Arrows.Leaf

/-- ⭐The **laws** of a root action (docs §3 4, "The canonical root action's laws"): restricting
    along two arrows is restricting along their composite; under T, along the identity is the root
    itself; restricting keeps a leaf well-formed; and it is **natural in the path edits** below
    the anchor's level, at well-formed positions — keeping at the end (`dk`), keeping before a
    level step (`dkB`; before a `□` step this is `shift`, `Arrows.Leaf.dkB_eq_shift`), and
    collapsing a `□` level.  A mixin, so that the operations (`Arrows.Leaf.keepAlong`,
    `GFunc.shp`) need only the action. -/
class Arrows.RootKeepLaws {σ : Signature} (F : Arrows.{u, v} σ) (Root : F.W → Type u)
    [Arrows.RootKeep F Root] : Prop where
  keep_trans : ∀ (hF : ModalSys.Four = true) {w : F.W} (r : Root w) (a : F.Acc w)
    (b : F.Acc a.1) (p : List Step),
    Arrows.Leaf.keepAlong hF b (Arrows.RootKeep.keep hF r a p) =
      Arrows.RootKeep.keep hF r ⟨b.1, ⟨F.trans hF a.2.down b.2.down⟩⟩ p
  keep_refl : ∀ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {w : F.W} (r : Root w)
    (p : List Step), Arrows.RootKeep.keep hF r (F.reflAcc hT w) p = .root r p
  keep_wf : ∀ (hF : ModalSys.Four = true) {w : F.W} (r : Root w) (a : F.Acc w)
    (lw : List Bool) (p : List Step), Arrows.Leaf.WF lw (Arrows.Leaf.root (F := F) r p) →
      Arrows.Leaf.WF lw (Arrows.RootKeep.keep hF r a p)
  keep_keepAt : ∀ (hF : ModalSys.Four = true) {w : F.W} (r : Root w) (a : F.Acc w)
    (c : Bool) (lw : List Bool) (p : List Step),
    Arrows.Leaf.WF (c :: lw) (Arrows.Leaf.root (F := F) r p) →
      Arrows.RootKeep.keep hF r a (Step.keepAt (lw.length + 1) p) =
        Arrows.Leaf.dk hF (lw.length + 1) (Arrows.RootKeep.keep hF r a p)
  keep_shiftAt : ∀ (hF : ModalSys.Four = true) {w : F.W} (r : Root w) (a : F.Acc w)
    (c : Bool) (lw q : List Bool) (p : List Step),
    Arrows.Leaf.WF (c :: lw ++ false :: q) (Arrows.Leaf.root (F := F) r p) →
      Arrows.RootKeep.keep hF r a (Step.shiftAt (lw.length + 1) p) =
        Arrows.Leaf.dkB hF (lw.length + 1) (Arrows.RootKeep.keep hF r a p)
  keep_collapseAt : ∀ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {w : F.W}
    (r : Root w) (a : F.Acc w) (c : Bool) (lw q : List Bool) (p : List Step),
    Arrows.Leaf.WF (c :: lw ++ true :: q) (Arrows.Leaf.root (F := F) r p) →
      Arrows.RootKeep.keep hF r a (Step.collapseAt (lw.length + 1) p) =
        Arrows.Leaf.collapse hT (lw.length + 1) (Arrows.RootKeep.keep hF r a p)

/-- A root action sending roots to roots is lawful when its action on roots is: every path edit
    then acts on the path alone. -/
theorem Arrows.RootKeepLaws.ofRoot {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}
    (k : ModalSys.Four = true → ∀ {w : F.W}, Root w → (a : F.Acc w) → Root a.1)
    (htrans : ∀ (hF : ModalSys.Four = true) {w : F.W} (r : Root w) (a : F.Acc w)
      (b : F.Acc a.1), k hF (k hF r a) b = k hF r ⟨b.1, ⟨F.trans hF a.2.down b.2.down⟩⟩)
    (hrefl : ∀ (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {w : F.W} (r : Root w),
      k hF r (F.reflAcc hT w) = r) :
    @Arrows.RootKeepLaws _ σ F Root (Arrows.RootKeep.ofRoot k) := by
  letI := Arrows.RootKeep.ofRoot k
  refine ⟨fun hF {_} r a b p => ?_, fun hT hF {_} r p => ?_, fun _ {_} r a lw p h => ?_,
    fun _ {_} _ _ _ _ _ _ => rfl, fun _ {_} _ _ _ _ _ _ _ => rfl,
    fun _ _ {_} _ _ _ _ _ _ _ => rfl⟩
  · change Arrows.Leaf.root (k hF (k hF r a) b) p = Arrows.Leaf.root _ p
    rw [htrans]
  · change Arrows.Leaf.root (k hF r (F.reflAcc hT _)) p = Arrows.Leaf.root r p
    rw [hrefl]
  · cases lw <;> exact h

/-- ⭐How a definable map moves the shape of its argument: positions are rearranged as the map
    rearranges components, labels are kept, and `extract`/`dup` collapse/shift the level they act
    at.  `j` is the number of levels above the current position. -/
def GFunc.shp {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}
    [Arrows.RootKeep F Root] {w : F.W} :
    {A B : VarType} → GFunc σ A B → ℕ →
      Shp (F.Leaf Root w) A → Shp (F.Leaf Root w) B
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
  | _, _, .extract hT, j, a => a.inner.map (Arrows.Leaf.collapse hT j)
  | _, _, .dup hF, j, a => .box (.box (a.inner.map (Arrows.Leaf.shift hF j)))
  | _, _, .dkeep hF, j, a =>
      .box (.dia (Arrows.Leaf.dk hF j a.label) (a.body.map (Arrows.Leaf.dkB hF j)))

/-- `GFunc.shp` with the root action given explicitly, for statements made before an instance is
    available (a model's own laws). -/
abbrev GFunc.shpK {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}
    (rk : ModalSys.Four = true → ∀ {w : F.W}, Root w → (a : F.Acc w) → List Step →
      Arrows.Leaf F Root a.1) {w : F.W}
    {A B : VarType} (f : GFunc σ A B) (j : ℕ) (a : Shp (F.Leaf Root w) A) :
    Shp (F.Leaf Root w) B :=
  @GFunc.shp _ σ F Root ⟨rk⟩ w A B f j a

/-- A family of shapes, one at the target of each arrow, as one shape whose leaves are families. -/
def Arrows.transposeShp {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u} {w : F.W} :
    {A : VarType} → ((s : F.Acc w) → Shp (F.Leaf Root s.1) A) →
      Shp (F.Leaf Root w) A
  | .Var, _ => .var
  | .VTypeOne, _ => .one
  | .VTypeProd _ _, g =>
      .prod (Arrows.transposeShp fun s => (g s).fst) (Arrows.transposeShp fun s => (g s).snd)
  | .VTypeBox _, g => .box (Arrows.transposeShp fun s => (g s).inner)
  | .VTypeDia _, g => .dia (.fam fun s => (g s).label) (Arrows.transposeShp fun s => (g s).body)

/-- The shape of any object, from the shapes of possible objects: componentwise at a product, and
    at a necessary object the family of its values' shapes. -/
def Frame.domShape {σ : Signature} {F : Frame.{u, v} σ} {Root : F.W → Type u}
    (necEval : ∀ {A : VarType} {w : F.W}, F.Nec A w → F.NecSec A w)
    (shape : ∀ {A : VarType} {w : F.W}, F.Pos A w → Shp (F.Leaf Root w) (.VTypeDia A)) :
    {A : VarType} → {w : F.W} → F.Dom A w → Shp (F.Leaf Root w) A
  | .Var, _, _ => .var
  | .VTypeOne, _, _ => .one
  | .VTypeProd _ _, _, a =>
      .prod (Frame.domShape necEval shape a.1) (Frame.domShape necEval shape a.2)
  | .VTypeBox _, _, n =>
      .box (Arrows.transposeShp fun s => Frame.domShape necEval shape (necEval n s))
  | .VTypeDia _, _, p => shape p

/-! ## Models -/

/-- ⭐A model: a pointed frame whose carriers evaluate injectively and are closed under the
    function algebra. -/
structure Model (σ : Signature) where
  frame : Frame.{u, v} σ
  necEval : {A : VarType} → {w : frame.W} → frame.Nec A w → frame.NecSec A w
  nec_inj : ∀ {A : VarType} {w : frame.W}, Function.Injective (@necEval A w)
  /-- Under T or strong B, the root possibilities: what a possible object's shape is ultimately
      built on. -/
  RootPoss : frame.W → Type u
  /-- Under 4, the restriction of a root possibility along an arrow, read at a path of its
      content (`Arrows.RootKeep`). -/
  rootKeep : ModalSys.Four = true → ∀ {w : frame.W}, RootPoss w → (a : frame.Acc w) →
    List Step → frame.Leaf RootPoss a.1
  /-- The root action's laws (`Arrows.RootKeepLaws`): composition, the identity, well-formedness
      and naturality in the path edits. -/
  rootKeepLaws : @Arrows.RootKeepLaws _ σ frame.toArrows RootPoss ⟨rootKeep⟩
  /-- ⭐**Evaluation of a possible object** (docs §10.27, §10.35): its **section** — an extent, and
      one object at each world of it — and, under T or strong B (`ModalSys.shaped`), its
      **shape**, the semantic annotation that records where each possibility inside it comes from.
      `Model.posEval` and `Model.shape` are the two components. -/
  posFull : {A : VarType} → {w : frame.W} → frame.Pos A w →
    frame.PosSec A w × (ModalSys.shaped = true → Shp (frame.Leaf RootPoss w) (.VTypeDia A))
  /-- ⭐A possible object **is** its extent, its contents and (when shaped) its shape: two objects
      agreeing on all three are equal.  So objects over different witnesses, or over one witness
      with differently annotated contents, are never identified (docs §10.24–10.27); unshaped
      this is plain injectivity of the section. -/
  posFull_inj : ∀ {A : VarType} {w : frame.W}, Function.Injective (@posFull A w)
  /-- ⭐**Possible objects' shapes are well-formed** (docs §3 4, "T + 4"): the labelling
      convention of §10.39, read without addresses (`Arrows.Leaf.WF`).  The operations keep it;
      it is what lets keeping a possibility commute with reading a `□` at the current world. -/
  posShape_wf : ∀ (hS : ModalSys.shaped = true) {A : VarType} {w : frame.W}
    (p : frame.Pos A w),
    Shp.WF (fun lw ℓ => Arrows.Leaf.WF (F := frame.toArrows) (Root := RootPoss) lw ℓ) []
      ((posFull p).2 hS)
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
        fun hS => .dia ((posFull p).2 hS).label (GFunc.shpK rootKeep f 1 ((posFull p).2 hS).body))
  /-- A necessary object riding along keeps the extent, pairs its values into the contents, and
      contributes the family of its values' shapes. -/
  posStrength_full : ∀ {A B : VarType} {w : frame.W} (n : frame.Nec A w) (p : frame.Pos B w),
    posFull (ops.posStrength n p) =
      (⟨(posFull p).1.1, fun w' =>
          ((necEval n w'.1, (posFull p).1.2 w') : frame.Dom (.VTypeProd A B) w'.1.1)⟩,
        fun hS => .dia ((posFull p).2 hS).label
          (.prod (Arrows.transposeShp fun s =>
              Frame.domShape necEval (fun q => (posFull q).2 hS) (necEval n s))
            ((posFull p).2 hS).body))
  necExtract_eval : ∀ {A : VarType} {w : frame.W} (hT : ModalSys.T = true) (n : frame.Nec A w),
    ops.necExtract hT n = necEval n ⟨w, ⟨frame.refl hT w⟩⟩
  necDup_eval : ∀ {A : VarType} {w : frame.W} (hF : ModalSys.Four = true) (n : frame.Nec A w)
    (v : frame.Acc w) (s : frame.Acc v.1),
    necEval (necEval (ops.necDup hF n) v) s = necEval n ⟨s.1, ⟨frame.trans hF v.2.down s.2.down⟩⟩
  /-- ⭐**Strong 4: keep is surjective along each arrow**, at the liftable types
      (`VarType.liftable`): every object of such a type at an arrow's target is the restriction of
      one at its source — the `□`-lift and the `◇`-lift, per arrow (docs §3 4, "4's strong
      forms"). -/
  keepLift : ∀ (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true) {w : frame.W}
    (a : frame.Acc w) (o : frame.Dom T a.1), ∃ m : frame.Dom T w,
      necEval (GFunc.eval ops (GFunc.keep (σ := σ) hF (VarType.keepable_of_liftable hl)) w m) a = o
  /-- ⭐Under 4, **a possible object kept along an arrow** (docs §3 4, "4's four cases"): its
      extent pulled back along the arrow, the same contents, and its labels restricted along the
      arrow (`Arrows.Leaf.keepAlong`). -/
  posKeep_full : ∀ {A : VarType} {w : frame.W} (hF : ModalSys.Four = true)
 (x : frame.Pos A w) (a : frame.Acc w),
    posFull (necEval (ops.posKeep hF x) a) =
      (⟨{b : frame.Acc a.1 |
            (⟨b.1, ⟨frame.trans hF a.2.down b.2.down⟩⟩ : frame.Acc w) ∈ (posFull x).1.1},
          fun b => (posFull x).1.2 ⟨⟨b.1.1, ⟨frame.trans hF a.2.down b.1.2.down⟩⟩, b.2⟩⟩,
        fun hS => ((posFull x).2 hS).map (@Arrows.Leaf.keepAlong _ σ frame.toArrows RootPoss
          ⟨rootKeep⟩ hF w a))
  /-- ⭐Under 5, **a possible object moved across** (docs §3 5, paper check P1): along `a`, its
      extent is the image of `x`'s under `side a`. -/
  posSide_ext : ∀ {A : VarType} {w : frame.W} (hV : ModalSys.Five = true) (x : frame.Pos A w)
    (a : frame.Acc w),
    (posFull (necEval (ops.posSide hV x) a)).1.1 = frame.sideAcc hV a '' (posFull x).1.1
  /-- Under 5, a possible object moved across has at `side a b` the content `x` has at `b`.  Only
      the section is stated: no syntax reads `posSide` in a shaped system yet (with 4 it is
      `posKeep`, docs §3 5, "with 4, `x.side` is `x.keep`"), so the shape waits for S5. -/
  posSide_content : ∀ {A : VarType} {w : frame.W} (hV : ModalSys.Five = true) (x : frame.Pos A w)
    (a b : frame.Acc w) (hb : b ∈ (posFull x).1.1)
    (hc : frame.sideAcc hV a b ∈ (posFull (necEval (ops.posSide hV x) a)).1.1),
    (posFull (necEval (ops.posSide hV x) a)).1.2 ⟨frame.sideAcc hV a b, hc⟩ =
      (posFull x).1.2 ⟨b, hb⟩
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
  /-- ⭐Strong 5, **the gather**, per arrow: a necessary object at `a`'s target, read along the
      arrows across, is (up to `Ind`) one at the source. -/
  necSide_exists : ∀ (hV : ModalSys.Five = true) (_hS : ModalSys.FiveStrong = true) {A : VarType}
    {w : frame.W} (a : frame.Acc w) (n : frame.Nec A a.1),
    ∃ m : frame.Nec A w, ∀ b : frame.Acc w, Ind (necEval m b) (necEval n (frame.sideAcc hV a b))
  /-- ⭐Strong T: every object has *some* possible object whose extent contains the current world,
      with a content there indistinguishable from the object (`Ind`, which is what `Here` reads,
      §10.33).  This says on its own that `R` is reflexive wherever a domain is inhabited.  Any
      content type: the condition asks for no more than `T_dia`'s soundness uses, and with `Ind`
      in place of equality the canonical model meets it at `◇`-typed contents too (§10.41).

      Stated existentially rather than as an operation on `Frame.Ops`: strong T adds no term former,
      so nothing interprets a map from objects to possible objects, and none is intended — in
      particular there is no uniqueness and no naturality.  Demanding an operation would force the
      canonical model to choose one (and, if naturality were ever wanted, to make the choices
      cohere, which is what sank the `y.ret` design). -/
  posRet_exists : ∀ {A : VarType} {w : frame.W} (_hT : ModalSys.T = true)
    (_hS : ModalSys.TStrong = true) (a : frame.Dom A w),
    ∃ (p : frame.Pos A w) (hm : frame.reflAcc _hT w ∈ (posFull p).1.1),
      Ind ((posFull p).1.2 ⟨frame.reflAcc _hT w, hm⟩) a
  /-- ⭐Strong B: **comes back as** (docs §11.20), what `Back` reads.  A carrier is given by its
      round-trip data: an out leg `S` (a set of arrows out), and for each of its arrows `a` the
      carrier's value at the end of every further arrow `b`.  Like `Ind`, a primitive of the model:
      at a `◇`-typed content no formula can single out the value a round trip brings back, so
      "comes back as" is a requirement on models rather than a definition (§11.20, decision of
      2026-10-10).  It implies the round trip (`Ret_fwd`), and at `◇`-free contents, where `Ind`
      is equality, it is the round trip (`Ret_conv`).  Its congruences, which mention hole terms,
      are in `Model.IndInvariant`. -/
  Ret : {A : VarType} → {w : frame.W} → (S : Set (frame.Acc w)) →
    ((a : S) → (b : frame.Acc a.1.1) → frame.Dom A b.1) → frame.Dom A w → Prop
  /-- What comes back as `o` makes the round trip: the leg is nonempty, and from each of its arrows
      some way home returns a value indistinguishable from `o`. -/
  Ret_fwd : ∀ {A : VarType} {w : frame.W} (_hS : ModalSys.BStrong = true)
    {S : Set (frame.Acc w)} {val : (a : S) → (b : frame.Acc a.1.1) → frame.Dom A b.1}
    {o : frame.Dom A w}, Ret S val o →
      Nonempty S ∧ ∀ a : S, ∃ r : frame.R a.1.1 w, Ind (val a ⟨w, ⟨r⟩⟩) o
  /-- At a `◇`-free content the round trip comes back: `Back` is the definite description there
      (`back_ret`). -/
  Ret_conv : ∀ {A : VarType} {w : frame.W} (_hS : ModalSys.BStrong = true)
    (_hA : A.diaFree = true) {S : Set (frame.Acc w)}
    {val : (a : S) → (b : frame.Acc a.1.1) → frame.Dom A b.1} {o : frame.Dom A w},
    (Nonempty S ∧ ∀ a : S, ∃ r : frame.R a.1.1 w, Ind (val a ⟨w, ⟨r⟩⟩) o) → Ret S val o
  /-- ⭐Strong B: wherever there is a way out, every object is what some necessarily necessary
      carrier comes back as, over every arrow out (`Back`, row 1; `Model.Backs`, docs §11.3).
      Existential, as `posRet_exists`: no term former interprets it.  At every content type
      (§11.15).  Row 2's carriers come from row 1's by strength over a nonempty extent, so it has
      no field. -/
  backRet_exists : ∀ {A : VarType} {w : frame.W} (_hS : ModalSys.BStrong = true),
    Nonempty (frame.Acc w) → ∀ o : frame.Dom A w,
      ∃ c : frame.Nec (.VTypeBox A) w,
        Ret (Set.univ : Set (frame.Acc w)) (fun a b => necEval (necEval c a.1) b) o
  /-- ⭐Strong B with **witnessed ways home** (rows 3–4, docs §11.23): along any arrow `b`, some
      possible object at its source has `b` in its extent, with content there indistinguishable
      from any given object at its target.  At a returning possibility's way home it is B's unit
      `A → □◇A` read per arrow (`Proof.ret_realise`); at its arrow out it names the route by a
      possible object here (derived, `Proof.ret_route_node`); at T's identity arrow it is
      `posRet_exists`.
      Existential, as `posRet_exists`: per arrow, with no uniform carrier and no naturality —
      a carrier realising an object at every successor at once is what forced several possible
      objects onto one way home. -/
  posBack_exists : ∀ {A : VarType} {w v : frame.W} (_hS : ModalSys.BStrong = true)
    (_hW : ModalSys.BStrongW = true) (b : frame.R v w) (o : frame.Dom A w),
    ∃ (p : frame.Pos A v) (hm : (⟨w, ⟨b⟩⟩ : frame.Acc v) ∈ (posFull p).1.1),
      Ind ((posFull p).1.2 ⟨⟨w, ⟨b⟩⟩, hm⟩) o

namespace Model

variable {σ : Signature} (M : Model.{u, v} σ)

/-- The model's worlds and arrows, which its shapes are built over. -/
abbrev arrows : Arrows.{u, v} σ := M.frame.toArrows

/-- A model's root action, for the shape operations (`GFunc.shp`). -/
instance instRootKeep : Arrows.RootKeep M.frame.toArrows M.RootPoss := ⟨M.rootKeep⟩

/-- A model's root action is lawful. -/
instance instRootKeepLaws : Arrows.RootKeepLaws M.frame.toArrows M.RootPoss :=
  M.rootKeepLaws

/-- The section of a possible object: its extent, and its content at each world of it. -/
abbrev posEval {A : VarType} {w : M.frame.W} (p : M.frame.Pos A w) : M.frame.PosSec A w :=
  (M.posFull p).1

/-- ⭐Under T or strong B (`ModalSys.shaped`), the **shape** of a possible object — its semantic
    annotation (docs §10.27). -/
abbrev shape (hS : ModalSys.shaped = true) {A : VarType} {w : M.frame.W} (p : M.frame.Pos A w) :
    Shp (M.frame.Leaf M.RootPoss w) (.VTypeDia A) :=
  (M.posFull p).2 hS

variable {M}

/-- ⭐**Strong T is row 3 at the own arrow** (docs §11.23): under T the identity is its own way
    back, and `posBack_exists` there is `posRet_exists`.  So a model of strong B with witnessed
    ways home and T meets strong T's law. -/
theorem posRet_of_posBack (hT : ModalSys.T = true) (hS : ModalSys.BStrong = true)
    (hW : ModalSys.BStrongW = true) {A : VarType} {w : M.frame.W} (a : M.frame.Dom A w) :
    ∃ (p : M.frame.Pos A w) (hm : M.frame.reflAcc hT w ∈ (M.posFull p).1.1),
      M.Ind ((M.posFull p).1.2 ⟨M.frame.reflAcc hT w, hm⟩) a :=
  M.posBack_exists hS hW (M.frame.refl hT w) a

/-- ⭐**Strong D is row 3 seen from the far end** (docs §11.23): an arrow out lies in the extent
    of some possible object here (`posBack_exists` at that arrow, content `()`), so under D some
    possible object has a nonempty extent, strong D's law. -/
theorem posSerial_of_posBack (hD : ModalSys.D = true) (hS : ModalSys.BStrong = true)
    (hW : ModalSys.BStrongW = true) (w : M.frame.W) :
    ∃ p : M.frame.Pos .VTypeOne w, Nonempty (M.posFull p).1.1 := by
  obtain ⟨v, ⟨b⟩⟩ := M.frame.serial hD w
  obtain ⟨p, hm, -⟩ := M.posBack_exists (A := .VTypeOne) hS hW b PUnit.unit
  exact ⟨p, ⟨⟨_, hm⟩⟩⟩

/-- Possible objects agreeing on their section and, when shaped, their shape are equal. -/
theorem pos_inj {A : VarType} {w : M.frame.W} {p q : M.frame.Pos A w}
    (h : M.posEval p = M.posEval q)
    (hs : ∀ hS : ModalSys.shaped = true, M.shape hS p = M.shape hS q) :
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

theorem shape_posMap (hS : ModalSys.shaped = true) {A B : VarType} {w : M.frame.W}
    (f : GFunc σ A B) (p : M.frame.Pos A w) :
    M.shape hS (M.ops.posMap f p) = .dia (M.shape hS p).label (f.shp 1 (M.shape hS p).body) :=
  congrFun (congrArg Prod.snd (M.posMap_full f p)) hS

theorem shape_posStrength (hS : ModalSys.shaped = true) {A B : VarType} {w : M.frame.W}
    (n : M.frame.Nec A w) (p : M.frame.Pos B w) :
    M.shape hS (M.ops.posStrength n p) =
      .dia (M.shape hS p).label
        (.prod (Arrows.transposeShp fun s => Frame.domShape M.necEval (M.shape hS) (M.necEval n s))
          (M.shape hS p).body) :=
  congrFun (congrArg Prod.snd (M.posStrength_full n p)) hS

end Model

end V12M
