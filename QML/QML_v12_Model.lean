import QML.QML_v12_Terms

/-!
# QML v12 — models

A **pointed Kripke frame** with a base domain `D w` at each world and, for the modal types,
**carriers**: `Nec A w` (necessary objects) and `Pos A w` (possible objects).  A carrier is not a
set of semantic objects but a domain of its own, with an **injective evaluation map** into them:

* a necessary object evaluates to an object of the domain at every accessible world
  (`necEval`);
* a possible object evaluates to an **extent** — a set of accessible worlds — together with exactly
  one object of the domain at each world of the extent (`posEval`).

Contents are elements of the domains at the accessible worlds, so everything a modal object
delivers is something the quantifiers there range over.  Products are pairs of objects, the unit
type has one object.

**Closure.**  The domains are closed under the **function algebra** `GFunc`: the definable maps
between types, built from function symbols and projections/pairing, together with their modal
lifts (`boxMap`, `boxPair`, `boxUnit`, `diaMap`, `strength`).  The model supplies the lifts on
carriers (`Ops`) and their evaluation laws.  A full model has every section as a necessary object
and every extent/content pair as a possible object; the canonical model only the denotable ones.
-/

namespace V12

universe u

/-- A pointed frame with base domains, modal carriers, and the interpretation of the signature. -/
structure Frame (σ : Signature) where
  W : Type u
  actual : W
  R : W → W → Prop
  D : W → Type u
  Nec : VarType → W → Type u
  Pos : VarType → W → Type u
  funcInterp : (f : σ.FuncSyms) → (w : W) → (Fin (σ.funcArity f) → D w) → D w
  relInterp : (r : σ.RelSyms) → (w : W) → (Fin (σ.relArity r) → D w) → Prop

namespace Frame

variable {σ : Signature} (F : Frame.{u} σ)

abbrev Acc (w : F.W) : Type u := {w' : F.W // F.R w w'}

/-- The domain of a type at a world. -/
def Dom : VarType → F.W → Type u
  | .Var, w => F.D w
  | .VTypeOne, _ => PUnit
  | .VTypeProd A B, w => Dom A w × Dom B w
  | .VTypeBox A, w => F.Nec A w
  | .VTypeDia A, w => F.Pos A w

/-- What a necessary object delivers: an object at every accessible world. -/
abbrev NecSec (A : VarType) (w : F.W) : Type u := (w' : F.Acc w) → F.Dom A w'.1

/-- What a possible object delivers: an extent, and exactly one object at each of its worlds. -/
abbrev PosSec (A : VarType) (w : F.W) : Type u :=
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

/-- The lifts of the function algebra to the carriers. -/
structure Frame.Ops {σ : Signature} (F : Frame.{u} σ) where
  necMap : {A B : VarType} → {w : F.W} → GFunc σ A B → F.Nec A w → F.Nec B w
  necPair : {A B : VarType} → {w : F.W} → F.Nec A w → F.Nec B w → F.Nec (.VTypeProd A B) w
  necUnit : {w : F.W} → F.Nec .VTypeOne w
  posMap : {A B : VarType} → {w : F.W} → GFunc σ A B → F.Pos A w → F.Pos B w
  posStrength : {A B : VarType} → {w : F.W} → F.Nec A w → F.Pos B w →
    F.Pos (.VTypeProd A B) w

/-- Evaluating a definable map at a world. -/
def GFunc.eval {σ : Signature} {F : Frame.{u} σ} (ops : F.Ops) :
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

/-! ## Models -/

/-- ⭐A model: a pointed frame whose carriers evaluate injectively and are closed under the
    function algebra. -/
structure Model (σ : Signature) where
  frame : Frame.{u} σ
  necEval : {A : VarType} → {w : frame.W} → frame.Nec A w → frame.NecSec A w
  nec_inj : ∀ {A : VarType} {w : frame.W}, Function.Injective (@necEval A w)
  posEval : {A : VarType} → {w : frame.W} → frame.Pos A w → frame.PosSec A w
  pos_inj : ∀ {A : VarType} {w : frame.W}, Function.Injective (@posEval A w)
  ops : frame.Ops
  necMap_eval : ∀ {A B : VarType} {w : frame.W} (f : GFunc σ A B) (n : frame.Nec A w)
    (w' : frame.Acc w), necEval (ops.necMap f n) w' = GFunc.eval ops f w'.1 (necEval n w')
  necPair_eval : ∀ {A B : VarType} {w : frame.W} (a : frame.Nec A w) (b : frame.Nec B w)
    (w' : frame.Acc w),
    necEval (ops.necPair a b) w' = ((necEval a w', necEval b w') : frame.Dom (.VTypeProd A B) w'.1)
  posMap_eval : ∀ {A B : VarType} {w : frame.W} (f : GFunc σ A B) (p : frame.Pos A w),
    posEval (ops.posMap f p) =
      ⟨(posEval p).1, fun w' => GFunc.eval ops f w'.1.1 ((posEval p).2 w')⟩
  posStrength_eval : ∀ {A B : VarType} {w : frame.W} (n : frame.Nec A w) (p : frame.Pos B w),
    posEval (ops.posStrength n p) =
      ⟨(posEval p).1, fun w' =>
        ((necEval n w'.1, (posEval p).2 w') : frame.Dom (.VTypeProd A B) w'.1.1)⟩

end V12
