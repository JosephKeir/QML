import QML.QML_v12m_SemLemmas
import QML.QML_v12m_SemHere
import QML.QML_v12m_SemLink

/-!
# QML v12m — the cone: a world on top of a model

The generic construction of "K45 and KD45 without both lifts: the hub" (docs, step 4).  Given a
relational model `N` with T, B and strong B off, a world `ρ` of it and `ConeData` — a base domain
with the signature on it, and which of `ρ`'s modal objects are the new world's, closed under the
function algebra — the **cone** (`ConeData.cone`) has the worlds `Option N.W`: `none` is the new
world, the **apex**, and `some t` is `t`.  The apex sees what `ρ` sees, nothing sees the apex, and
otherwise the arrows are `N`'s.  At `some t` the cone's objects are `N`'s (`ConeData.toC`), and
at the apex its modal objects are the chosen ones of `ρ`.  `Ind` is equality: with T and strong B
off no formula reads it.

So nothing at `some t` looks at the apex, and a formula means there what it means in `N`
(`ConeData.sat_cone`).
-/

namespace V12M

variable [ModalSys]

/-- With T and strong B off nothing is shaped. -/
theorem shaped_false_of (hT : ModalSys.T = false) (hS : ModalSys.BStrong = false) :
    ModalSys.shaped = false := by
  rw [ModalSys.shaped, hT, hS]
  rfl

/-- A flag that is off is not on. -/
def flagElim {b : Bool} {C : Sort _} (h₁ : b = false) (h₂ : b = true) : C :=
  absurd (h₁.symm.trans h₂) Bool.false_ne_true

namespace Model

variable {σ : Signature}

/-- ⭐**What the cone puts at its apex**: a world `ρ` of `N` whose arrows the apex takes, a base
    domain with the signature on it, and which of `ρ`'s necessary and possible objects are the
    apex's (`DefN`, `DefP`), closed under the function algebra's operations.  Under strong D some
    possible object of the apex has a world; under strong 4, the apex's objects lift, and under
    strong 5, they gather (docs, "the hub", 5). -/
structure ConeData (N : Model.{0, 0} σ) where
  ρ : N.frame.W
  D : Type
  funcInterp : (f : σ.FuncSyms) → (Fin (σ.funcArity f) → D) → D
  relInterp : (r : σ.RelSyms) → (Fin (σ.relArity r) → D) → Prop
  DefN : (A : VarType) → N.frame.Nec A ρ → Prop
  DefP : (A : VarType) → N.frame.Pos A ρ → Prop
  necMap : ∀ {A B : VarType} (f : GFunc σ A B) {n : N.frame.Nec A ρ}, DefN A n →
    DefN B (N.ops.necMap f n)
  necPair : ∀ {A B : VarType} {a : N.frame.Nec A ρ} {b : N.frame.Nec B ρ}, DefN A a →
    DefN B b → DefN (.VTypeProd A B) (N.ops.necPair a b)
  necUnit : DefN .VTypeOne N.ops.necUnit
  posMap : ∀ {A B : VarType} (f : GFunc σ A B) {p : N.frame.Pos A ρ}, DefP A p →
    DefP B (N.ops.posMap f p)
  posStrength : ∀ {A B : VarType} {n : N.frame.Nec A ρ} {p : N.frame.Pos B ρ}, DefN A n →
    DefP B p → DefP (.VTypeProd A B) (N.ops.posStrength n p)
  necDup : ∀ (hF : ModalSys.Four = true) {A : VarType} {n : N.frame.Nec A ρ}, DefN A n →
    DefN (.VTypeBox A) (N.ops.necDup hF n)
  posKeep : ∀ (hF : ModalSys.Four = true) {A : VarType} {p : N.frame.Pos A ρ}, DefP A p →
    DefN (.VTypeDia A) (N.ops.posKeep hF p)
  posSide : ∀ (hV : ModalSys.Five = true) {A : VarType} {p : N.frame.Pos A ρ}, DefP A p →
    DefN (.VTypeDia A) (N.ops.posSide hV p)
  posSerial : ModalSys.DStrong = true →
    ∃ p : N.frame.Pos .VTypeOne ρ, DefP .VTypeOne p ∧ Nonempty (N.posEval p).1
  keepLiftN : ∀ (hF : ModalSys.Four = true) {A : VarType}
    (_hl : (VarType.VTypeBox A).liftableR = true) (a : N.frame.Acc ρ) (o : N.frame.Nec A a.1),
    ∃ m : N.frame.Nec A ρ, DefN A m ∧ N.necEval (N.ops.necDup hF m) a = o
  keepLiftP : ∀ (hF : ModalSys.Four = true) {A : VarType}
    (_hl : (VarType.VTypeDia A).liftableR = true) (a : N.frame.Acc ρ) (o : N.frame.Pos A a.1),
    ∃ m : N.frame.Pos A ρ, DefP A m ∧ N.necEval (N.ops.posKeep hF m) a = o
  necSide : ∀ (hV : ModalSys.Five = true) (_hS : ModalSys.FiveStrong = true) {A : VarType}
    (a : N.frame.Acc ρ) (n : N.frame.Nec A a.1),
    ∃ m : N.frame.Nec A ρ, DefN A m ∧
      ∀ b : N.frame.Acc ρ, N.necEval m b = N.necEval n (N.frame.sideAcc hV a b)

namespace ConeData

variable {N : Model.{0, 0} σ} (c : N.ConeData)

/-! ## The frame -/

/-- The world of `N` under a world of the cone: `ρ` under the apex. -/
def base : Option N.frame.W → N.frame.W
  | none => c.ρ
  | some s => s

/-- The cone's arrows: from `w` to `some t` when `N` has one from `w`'s base, none into the
    apex. -/
def R (w : Option N.frame.W) : Option N.frame.W → Prop
  | some t => N.frame.R (c.base w) t
  | none => False

theorem trans (hF : ModalSys.Four = true) :
    ∀ {w v s : Option N.frame.W}, c.R w v → c.R v s → c.R w s
  | _, some _, some _, a, b => N.frame.trans hF a b
  | _, none, _, a, _ => False.elim a
  | _, some _, none, _, b => False.elim b

theorem side (hV : ModalSys.Five = true) :
    ∀ {w v s : Option N.frame.W}, c.R w v → c.R w s → c.R v s
  | _, some _, some _, a, b => N.frame.side hV a b
  | _, none, _, a, _ => False.elim a
  | _, some _, none, _, b => False.elim b

/-- The base domain of a world of the cone. -/
def Dw : Option N.frame.W → Type
  | none => c.D
  | some s => N.frame.D s

def fI (f : σ.FuncSyms) : (w : Option N.frame.W) → (Fin (σ.funcArity f) → c.Dw w) → c.Dw w
  | none => c.funcInterp f
  | some s => N.frame.funcInterp f s

def rI (r : σ.RelSyms) : (w : Option N.frame.W) → (Fin (σ.relArity r) → c.Dw w) → Prop
  | none => c.relInterp r
  | some s => N.relInterp r s

/-- Which of the base world's necessary objects are the world's: all of them below the apex. -/
def DN : (w : Option N.frame.W) → (A : VarType) → N.frame.Nec A (c.base w) → Prop
  | none => c.DefN
  | some _ => fun _ _ => True

def DP : (w : Option N.frame.W) → (A : VarType) → N.frame.Pos A (c.base w) → Prop
  | none => c.DefP
  | some _ => fun _ _ => True

variable (hT : ModalSys.T = false) (hB : ModalSys.B = false)

/-- The cone's worlds and arrows. -/
def arrows : Arrows.{0, 0} σ where
  W := Option N.frame.W
  R := c.R
  refl h := flagElim hT h
  trans hF := fun a b => c.trans hF a b
  refl_trans h := flagElim hT h
  trans_refl h := flagElim hT h
  trans_assoc := fun _ {_ _ _ _} _ _ _ => rfl

/-- ⭐**The cone's frame.** -/
def frame : Frame.{0, 0} σ where
  toArrows := c.arrows hT
  actual := none
  serial hD w := by
    obtain ⟨t, ⟨r⟩⟩ := N.frame.serial hD (c.base w)
    exact ⟨some t, ⟨r⟩⟩
  symm h := flagElim hB h
  homeUnique _ := ⟨fun _ _ => rfl⟩
  side hV := fun a b => c.side hV a b
  side_inj _ {_ _ s s'} _ _ _ h := by
    obtain rfl : s = s' := congrArg Sigma.fst h
    rfl
  side_side := fun _ {_ _ _ _} _ _ _ => rfl
  trans_side := fun _ _ {_ _ _} _ _ => rfl
  side_trans := fun _ _ {_ _ _ _} _ _ _ => rfl
  side_refl h := flagElim hT h
  side_loop := fun _ _ {_ _ _} _ _ => rfl
  D := c.Dw
  Nec A w := {n : N.frame.Nec A (c.base w) // c.DN w A n}
  Pos A w := {p : N.frame.Pos A (c.base w) // c.DP w A p}
  funcInterp f w := c.fI f w

/-- An arrow of the cone as one of `N`. -/
def down {w : Option N.frame.W} : (c.frame hT hB).Acc w → N.frame.Acc (c.base w)
  | ⟨some t, ⟨r⟩⟩ => ⟨t, ⟨r⟩⟩
  | ⟨none, ⟨r⟩⟩ => False.elim r

/-- An arrow of `N` as one of the cone. -/
def up {w : Option N.frame.W} (b : N.frame.Acc (c.base w)) : (c.frame hT hB).Acc w :=
  ⟨some b.1, ⟨b.2.down⟩⟩

theorem down_up {w : Option N.frame.W} (b : N.frame.Acc (c.base w)) :
    c.down hT hB (c.up hT hB b) = b := rfl

theorem up_down {w : Option N.frame.W} : ∀ a : (c.frame hT hB).Acc w,
    c.up hT hB (c.down hT hB a) = a
  | ⟨some _, ⟨_⟩⟩ => rfl
  | ⟨none, ⟨r⟩⟩ => False.elim r

/-! ## Objects below the apex -/

/-- ⭐An object of `N` as one of the cone, below the apex. -/
def toC : (A : VarType) → (t : N.frame.W) → N.frame.Dom A t → (c.frame hT hB).Dom A (some t)
  | .Var, _, o => o
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A B, t, o =>
      (toC A t (o : N.frame.Dom A t × N.frame.Dom B t).1, toC B t o.2)
  | .VTypeBox A, t, o =>
      (Subtype.mk o trivial : {n : N.frame.Nec A (c.base (some t)) // c.DN (some t) A n})
  | .VTypeDia A, t, o =>
      (Subtype.mk o trivial : {p : N.frame.Pos A (c.base (some t)) // c.DP (some t) A p})

/-- An object of the cone below the apex as one of `N`. -/
def ofC : (A : VarType) → (t : N.frame.W) → (c.frame hT hB).Dom A (some t) → N.frame.Dom A t
  | .Var, _, o => o
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A B, t, o =>
      (ofC A t (o : (c.frame hT hB).Dom A (some t) × (c.frame hT hB).Dom B (some t)).1,
        ofC B t o.2)
  | .VTypeBox A, _, o =>
      (o : {n : N.frame.Nec A (c.base (some _)) // c.DN (some _) A n}).1
  | .VTypeDia A, _, o =>
      (o : {p : N.frame.Pos A (c.base (some _)) // c.DP (some _) A p}).1

theorem ofC_toC : ∀ (A : VarType) (t : N.frame.W) (o : N.frame.Dom A t),
    c.ofC hT hB A t (c.toC hT hB A t o) = o
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A B, t, o => by
      change ((c.ofC hT hB A t (c.toC hT hB A t o.1), c.ofC hT hB B t (c.toC hT hB B t o.2)) :
        N.frame.Dom A t × N.frame.Dom B t) = o
      rw [ofC_toC A t, ofC_toC B t]
      rfl
  | .VTypeBox _, _, _ => rfl
  | .VTypeDia _, _, _ => rfl

theorem toC_ofC : ∀ (A : VarType) (t : N.frame.W) (o : (c.frame hT hB).Dom A (some t)),
    c.toC hT hB A t (c.ofC hT hB A t o) = o
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A B, t, o => by
      change ((c.toC hT hB A t (c.ofC hT hB A t o.1), c.toC hT hB B t (c.ofC hT hB B t o.2)) :
        (c.frame hT hB).Dom A (some t) × (c.frame hT hB).Dom B (some t)) = o
      rw [toC_ofC A t, toC_ofC B t]
      rfl
  | .VTypeBox _, _, _ => rfl
  | .VTypeDia _, _, _ => rfl

theorem toC_injective {A : VarType} {t : N.frame.W} {o o' : N.frame.Dom A t}
    (h : c.toC hT hB A t o = c.toC hT hB A t o') : o = o' := by
  rw [← c.ofC_toC hT hB A t o, h, c.ofC_toC]

/-! ## Carriers -/

/-- A necessary object of the cone, read along an arrow: `N`'s reading. -/
def necEval {A : VarType} {w : Option N.frame.W} (n : (c.frame hT hB).Nec A w) :
    (c.frame hT hB).NecSec A w
  | ⟨some t, ⟨r⟩⟩ => c.toC hT hB A t (N.necEval n.1 ⟨t, ⟨r⟩⟩)
  | ⟨none, ⟨r⟩⟩ => False.elim r

theorem necEval_injective {A : VarType} {w : Option N.frame.W} :
    Function.Injective (@necEval _ _ _ c hT hB A w) := by
  intro n n' h
  refine Subtype.ext (N.nec_inj (funext fun b => ?_))
  obtain ⟨t, ⟨r⟩⟩ := b
  exact c.toC_injective hT hB (congrFun h ⟨some t, ⟨r⟩⟩)

/-- A possible object of the cone: `N`'s extent, read through the arrows, and `N`'s contents. -/
def posSec {A : VarType} {w : Option N.frame.W} (p : (c.frame hT hB).Pos A w) :
    (c.frame hT hB).PosSec A w :=
  ⟨{a | c.down hT hB a ∈ (N.posEval p.1).1}, fun
    | ⟨⟨some t, ⟨r⟩⟩, h⟩ => c.toC hT hB A t ((N.posEval p.1).2 ⟨⟨t, ⟨r⟩⟩, h⟩)
    | ⟨⟨none, ⟨r⟩⟩, _⟩ => False.elim r⟩

end ConeData

namespace ConeData

variable {N : Model.{0, 0} σ} (c : N.ConeData) (hT : ModalSys.T = false)
  (hB : ModalSys.B = false) (hS : ModalSys.BStrong = false)

include hS in
theorem posSec_injective {A : VarType} {w : Option N.frame.W} :
    Function.Injective (@posSec _ _ _ c hT hB A w) := by
  intro p q h
  obtain ⟨hE, hf⟩ := posSec_of_eq h
  refine Subtype.ext (N.posFull_inj (Prod.ext (posSec_ext' ?_ ?_)
    (funext fun h => flagElim (shaped_false_of hT hS) h)))
  · ext b
    obtain ⟨t, ⟨r⟩⟩ := b
    exact Set.ext_iff.mp hE ⟨some t, ⟨r⟩⟩
  · intro b h h'
    obtain ⟨t, ⟨r⟩⟩ := b
    exact c.toC_injective hT hB (hf ⟨some t, ⟨r⟩⟩ h h')

/-! ## The operations -/

theorem dn_map {A B : VarType} (f : GFunc σ A B) : ∀ {w : Option N.frame.W}
    {n : N.frame.Nec A (c.base w)}, c.DN w A n → c.DN w B (N.ops.necMap f n)
  | none, _, h => c.necMap f h
  | some _, _, _ => trivial

theorem dn_pair {A B : VarType} : ∀ {w : Option N.frame.W} {a : N.frame.Nec A (c.base w)}
    {b : N.frame.Nec B (c.base w)}, c.DN w A a → c.DN w B b →
      c.DN w (.VTypeProd A B) (N.ops.necPair a b)
  | none, _, _, h, h' => c.necPair h h'
  | some _, _, _, _, _ => trivial

theorem dn_unit : ∀ w : Option N.frame.W, c.DN w .VTypeOne N.ops.necUnit
  | none => c.necUnit
  | some _ => trivial

theorem dp_map {A B : VarType} (f : GFunc σ A B) : ∀ {w : Option N.frame.W}
    {p : N.frame.Pos A (c.base w)}, c.DP w A p → c.DP w B (N.ops.posMap f p)
  | none, _, h => c.posMap f h
  | some _, _, _ => trivial

theorem dp_strength {A B : VarType} : ∀ {w : Option N.frame.W} {n : N.frame.Nec A (c.base w)}
    {p : N.frame.Pos B (c.base w)}, c.DN w A n → c.DP w B p →
      c.DP w (.VTypeProd A B) (N.ops.posStrength n p)
  | none, _, _, h, h' => c.posStrength h h'
  | some _, _, _, _, _ => trivial

theorem dn_dup (hF : ModalSys.Four = true) {A : VarType} : ∀ {w : Option N.frame.W}
    {n : N.frame.Nec A (c.base w)}, c.DN w A n → c.DN w (.VTypeBox A) (N.ops.necDup hF n)
  | none, _, h => c.necDup hF h
  | some _, _, _ => trivial

theorem dn_keep (hF : ModalSys.Four = true) {A : VarType} : ∀ {w : Option N.frame.W}
    {p : N.frame.Pos A (c.base w)}, c.DP w A p → c.DN w (.VTypeDia A) (N.ops.posKeep hF p)
  | none, _, h => c.posKeep hF h
  | some _, _, _ => trivial

theorem dn_side (hV : ModalSys.Five = true) {A : VarType} : ∀ {w : Option N.frame.W}
    {p : N.frame.Pos A (c.base w)}, c.DP w A p → c.DN w (.VTypeDia A) (N.ops.posSide hV p)
  | none, _, h => c.posSide hV h
  | some _, _, _ => trivial

/-- The operations: `N`'s, on the chosen objects. -/
def ops : (c.frame hT hB).Ops where
  necMap f n := ⟨N.ops.necMap f n.1, c.dn_map f n.2⟩
  necPair a b := ⟨N.ops.necPair a.1 b.1, c.dn_pair a.2 b.2⟩
  necUnit {w} := ⟨N.ops.necUnit, c.dn_unit w⟩
  posMap f p := ⟨N.ops.posMap f p.1, c.dp_map f p.2⟩
  posStrength n p := ⟨N.ops.posStrength n.1 p.1, c.dp_strength n.2 p.2⟩
  necExtract h _ := flagElim hT h
  necDup hF n := ⟨N.ops.necDup hF n.1, c.dn_dup hF n.2⟩
  posKeep hF p := ⟨N.ops.posKeep hF p.1, c.dn_keep hF p.2⟩
  posSide hV p := ⟨N.ops.posSide hV p.1, c.dn_side hV p.2⟩

/-- ⭐Below the apex the operations are `N`'s. -/
theorem eval_toC {t : N.frame.W} : ∀ {A B : VarType} (f : GFunc σ A B) (o : N.frame.Dom A t),
    GFunc.eval (c.ops hT hB) f (some t) (c.toC hT hB A t o) =
      c.toC hT hB B t (GFunc.eval N.ops f t o)
  | _, _, .id _, _ => rfl
  | _, _, .comp g f, o => by
      change GFunc.eval (c.ops hT hB) g (some t) (GFunc.eval (c.ops hT hB) f (some t) _) = _
      rw [eval_toC f, eval_toC g]
      rfl
  | _, _, .fst, _ => rfl
  | _, _, .snd, _ => rfl
  | _, _, .pair f g, o => by
      change (GFunc.eval (c.ops hT hB) f (some t) _, GFunc.eval (c.ops hT hB) g (some t) _) = _
      rw [eval_toC f, eval_toC g]
      rfl
  | _, _, .unit _, _ => rfl
  | _, _, .func f args, o => by
      change N.frame.funcInterp f t (fun i => GFunc.eval (c.ops hT hB) (args i) (some t) _) = _
      simp only [eval_toC (args _)]
      rfl
  | _, _, .boxMap _, _ => rfl
  | _, _, .boxPair _ _, _ => rfl
  | _, _, .boxUnit, _ => rfl
  | _, _, .diaMap _, _ => rfl
  | _, _, .strength _ _, _ => rfl
  | _, _, .extract h, _ => flagElim hT h
  | _, _, .dup _, _ => rfl
  | _, _, .dkeep _, _ => rfl

variable (hInd : ∀ {A : VarType} {w : N.frame.W} (o o' : N.frame.Dom A w), N.Ind o o' → o = o')

/-- ⭐⭐**The cone** over `N`, with apex `none`. -/
def cone : Model.{0, 0} σ where
  frame := c.frame hT hB
  relInterp r w := c.rI r w
  necEval := c.necEval hT hB
  nec_inj h := c.necEval_injective hT hB h
  RootPoss _ := PEmpty
  rootKeep _ _ r := r.elim
  rootKeepLaws := @Arrows.RootKeepLaws.mk _ σ (c.frame hT hB).toArrows (fun _ => PEmpty)
    ⟨fun _ _ r => r.elim⟩ (fun _ _ r => r.elim) (fun _ _ _ r => r.elim) (fun _ _ r => r.elim)
    (fun _ _ r => r.elim) (fun _ _ r => r.elim) (fun _ _ _ r => r.elim)
  posFull p := (c.posSec hT hB p, fun h => flagElim (shaped_false_of hT hS) h)
  posFull_inj h := c.posSec_injective hT hB hS (congrArg Prod.fst h)
  posShape_wf h := flagElim (shaped_false_of hT hS) h
  ops := c.ops hT hB
  necMap_eval f n a := by
    obtain ⟨_ | t, ⟨r⟩⟩ := a
    · exact False.elim r
    · change c.toC hT hB _ t (N.necEval (N.ops.necMap f n.1) ⟨t, ⟨r⟩⟩) =
        GFunc.eval (c.ops hT hB) f (some t) (c.toC hT hB _ t (N.necEval n.1 ⟨t, ⟨r⟩⟩))
      rw [N.necMap_eval, c.eval_toC]
  necPair_eval a b a' := by
    obtain ⟨_ | t, ⟨r⟩⟩ := a'
    · exact False.elim r
    · change c.toC hT hB _ t (N.necEval (N.ops.necPair a.1 b.1) ⟨t, ⟨r⟩⟩) = _
      rw [N.necPair_eval]
      rfl
  posMap_full f p := by
    refine Prod.ext (posSec_ext' ?_ ?_) (funext fun h => flagElim (shaped_false_of hT hS) h)
    · change {a | c.down hT hB a ∈ (N.posEval (N.ops.posMap f p.1)).1} =
        {a | c.down hT hB a ∈ (N.posEval p.1).1}
      rw [N.posMap_eval]
    · intro a h h'
      obtain ⟨_ | t, ⟨r⟩⟩ := a
      · exact False.elim r
      · obtain ⟨-, hf⟩ := posSec_of_eq (N.posMap_eval f p.1)
        change c.toC hT hB _ t ((N.posEval (N.ops.posMap f p.1)).2 ⟨⟨t, ⟨r⟩⟩, h⟩) =
          GFunc.eval (c.ops hT hB) f (some t) (c.toC hT hB _ t ((N.posEval p.1).2 ⟨⟨t, ⟨r⟩⟩, h'⟩))
        rw [c.eval_toC, hf ⟨t, ⟨r⟩⟩ h h']
  posStrength_full n p := by
    refine Prod.ext (posSec_ext' ?_ ?_) (funext fun h => flagElim (shaped_false_of hT hS) h)
    · change {a | c.down hT hB a ∈ (N.posEval (N.ops.posStrength n.1 p.1)).1} =
        {a | c.down hT hB a ∈ (N.posEval p.1).1}
      rw [N.posStrength_eval]
    · intro a h h'
      obtain ⟨_ | t, ⟨r⟩⟩ := a
      · exact False.elim r
      · obtain ⟨-, hf⟩ := posSec_of_eq (N.posStrength_eval n.1 p.1)
        change c.toC hT hB _ t ((N.posEval (N.ops.posStrength n.1 p.1)).2 ⟨⟨t, ⟨r⟩⟩, h⟩) =
          (c.toC hT hB _ t (N.necEval n.1 ⟨t, ⟨r⟩⟩),
            c.toC hT hB _ t ((N.posEval p.1).2 ⟨⟨t, ⟨r⟩⟩, h'⟩))
        rw [hf ⟨t, ⟨r⟩⟩ h h']
        rfl
  necExtract_eval h := flagElim hT h
  necDup_eval hF n v s := by
    obtain ⟨_ | v', ⟨r⟩⟩ := v
    · exact False.elim r
    obtain ⟨_ | s', ⟨r'⟩⟩ := s
    · exact False.elim r'
    exact congrArg (c.toC hT hB _ s') (N.necDup_eval hF n.1 ⟨v', ⟨r⟩⟩ ⟨s', ⟨r'⟩⟩)
  keepLift hF T hl w a o := by
    obtain ⟨_ | t, ⟨r⟩⟩ := a
    · exact False.elim r
    cases w with
    | some s =>
        obtain ⟨m, hm⟩ := N.keepLift hF hl ⟨t, ⟨r⟩⟩ (c.ofC hT hB T t o)
        refine ⟨c.toC hT hB T s m, ?_⟩
        rw [c.eval_toC]
        exact (congrArg (c.toC hT hB T t) hm).trans (c.toC_ofC hT hB T t o)
    | none =>
        cases T with
        | VTypeBox A =>
            obtain ⟨m, hm, he⟩ := c.keepLiftN hF hl ⟨t, ⟨r⟩⟩ o.1
            exact ⟨⟨m, hm⟩, Subtype.ext he⟩
        | VTypeDia A =>
            obtain ⟨m, hm, he⟩ := c.keepLiftP hF hl ⟨t, ⟨r⟩⟩ o.1
            exact ⟨⟨m, hm⟩, Subtype.ext he⟩
        | Var => exact absurd (VarType.keepable_of_liftableR hl) (by simp [VarType.keepable])
        | VTypeOne => exact absurd (VarType.keepable_of_liftableR hl) (by simp [VarType.keepable])
        | VTypeProd _ _ =>
            exact absurd (VarType.keepable_of_liftableR hl) (by simp [VarType.keepable])
  posKeep_full hF x a := by
    obtain ⟨_ | t, ⟨r⟩⟩ := a
    · exact False.elim r
    obtain ⟨hE, hf⟩ := posSec_of_eq (congrArg Prod.fst (N.posKeep_full hF x.1 ⟨t, ⟨r⟩⟩))
    refine Prod.ext (posSec_ext' ?_ ?_) (funext fun h => flagElim (shaped_false_of hT hS) h)
    · ext b
      obtain ⟨_ | s, ⟨r'⟩⟩ := b
      · exact False.elim r'
      exact Set.ext_iff.mp hE ⟨s, ⟨r'⟩⟩
    · intro b h h'
      obtain ⟨_ | s, ⟨r'⟩⟩ := b
      · exact False.elim r'
      exact congrArg (c.toC hT hB _ s) (hf ⟨s, ⟨r'⟩⟩ h h')
  posSide_ext hV x a := by
    obtain ⟨_ | t, ⟨r⟩⟩ := a
    · exact False.elim r
    have hN := N.posSide_ext hV x.1 ⟨t, ⟨r⟩⟩
    ext b
    obtain ⟨_ | s, ⟨r'⟩⟩ := b
    · exact False.elim r'
    change (⟨s, ⟨r'⟩⟩ : N.frame.Acc t) ∈
      (N.posEval (N.necEval (N.ops.posSide hV x.1) ⟨t, ⟨r⟩⟩)).1 ↔ _
    rw [hN]
    constructor
    · rintro ⟨⟨s', ⟨r''⟩⟩, hb, e⟩
      obtain rfl : s' = s := congrArg Sigma.fst e
      exact ⟨⟨some s', ⟨r''⟩⟩, hb, rfl⟩
    · rintro ⟨⟨_ | s', ⟨r''⟩⟩, hb, e⟩
      · exact False.elim r''
      obtain rfl : s' = s := Option.some.inj (congrArg Sigma.fst e)
      exact ⟨⟨s', ⟨r''⟩⟩, hb, rfl⟩
  posSide_content hV x a b hb hc := by
    obtain ⟨_ | t, ⟨r⟩⟩ := a
    · exact False.elim r
    obtain ⟨_ | s, ⟨r'⟩⟩ := b
    · exact False.elim r'
    exact congrArg (c.toC hT hB _ s) (hInd _ _ (N.posSide_content hV x.1 ⟨t, ⟨r⟩⟩ ⟨s, ⟨r'⟩⟩ hb hc))
  posSerial hD w := by
    cases w with
    | none =>
        obtain ⟨p, hp, ⟨⟨⟨t, ⟨r⟩⟩, hb⟩⟩⟩ := c.posSerial hD
        exact ⟨⟨p, hp⟩, ⟨⟨⟨some t, ⟨r⟩⟩, hb⟩⟩⟩
    | some s =>
        obtain ⟨p, ⟨⟨⟨t, ⟨r⟩⟩, hb⟩⟩⟩ := N.posSerial hD s
        exact ⟨⟨p, trivial⟩, ⟨⟨⟨some t, ⟨r⟩⟩, hb⟩⟩⟩
  Ind o o' := o = o'
  Ind_refl _ := rfl
  necSide_exists hV h5 A w a n := by
    obtain ⟨_ | t, ⟨r⟩⟩ := a
    · exact False.elim r
    cases w with
    | none =>
        obtain ⟨m, hm, he⟩ := c.necSide hV h5 ⟨t, ⟨r⟩⟩ n.1
        refine ⟨⟨m, hm⟩, fun b => ?_⟩
        obtain ⟨_ | s, ⟨r'⟩⟩ := b
        · exact False.elim r'
        exact congrArg (c.toC hT hB A s) (he ⟨s, ⟨r'⟩⟩)
    | some w =>
        obtain ⟨m, he⟩ := N.necSide_exists hV h5 ⟨t, ⟨r⟩⟩ n.1
        refine ⟨⟨m, trivial⟩, fun b => ?_⟩
        obtain ⟨_ | s, ⟨r'⟩⟩ := b
        · exact False.elim r'
        exact congrArg (c.toC hT hB A s) (hInd _ _ (he ⟨s, ⟨r'⟩⟩))
  posRet_exists h := flagElim hT h
  Ret _ _ _ _ := False
  Ret_fwd _ _ _ _ _ h := False.elim h
  Ret_conv h := flagElim hS h
  backRet_exists h := flagElim hS h
  posBack_exists h := flagElim hS h

/-! ## Below the apex, a formula means what it means in `N` -/

/-- A cone environment below the apex and an environment of `N` with the same objects. -/
def EnvRel {Γ : Ctx} {t : N.frame.W} (e : (c.cone hT hB hS hInd).Env Γ (some t))
    (e' : N.Env Γ t) : Prop :=
  ∀ v T (h : Γ v = some T), e v T h = c.toC hT hB T t (e' v T h)

variable {c hT hB hS hInd}

theorem stepObj_toC {t : N.frame.W} {U T : VarType} {s : Step} (hs : s.isStruct = true)
    (h : U.step s = some T) (a : N.frame.Dom U t) :
    (c.cone hT hB hS hInd).stepObj hs h (c.toC hT hB U t a) =
      c.toC hT hB T t (N.stepObj hs h a) := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h) <;> try rfl
  exact flagElim hT (VarType.step_here h).1

theorem EnvRel.ref {Γ : Ctx} {t : N.frame.W} {e : (c.cone hT hB hS hInd).Env Γ (some t)}
    {e' : N.Env Γ t} (hag : c.EnvRel hT hB hS hInd e e') :
    ∀ (v : VarSymb) {T : VarType} (hv : Γ.ref v = some T),
      e.ref v hv = c.toC hT hB T t (e'.ref v hv)
  | .root r, _, hv => hag (.root r) _ hv
  | .step v s, T, hv => by
      by_cases hs : s.isStruct = true
      · rw [Env.ref, Env.ref, dif_pos hs, dif_pos hs]
        split
        · rename_i U hU
          rw [EnvRel.ref hag v hU, stepObj_toC]
        · rename_i hU
          exfalso
          rw [Ctx.ref_step_proj Γ v hs, hU] at hv
          cases hv
      · rw [Env.ref, Env.ref, dif_neg hs, dif_neg hs]
        exact hag _ _ _

theorem EnvRel.boxPush {Γ : Ctx} {t : N.frame.W} {e : (c.cone hT hB hS hInd).Env Γ (some t)}
    {e' : N.Env Γ t} (hag : c.EnvRel hT hB hS hInd e e') (a : N.frame.Acc t) :
    c.EnvRel hT hB hS hInd (e.boxPush (c.up hT hB (w := some t) a)) (e'.boxPush a) := by
  intro v T hv
  match v with
  | .step u .box =>
      simp only [Env.boxPush, Env.boxPushVal]
      rw [hag.ref u (Ctx.boxIn_step_box hv)]
      rfl
  | .step u .keep =>
      have hk := Ctx.boxIn_keep hv
      simp only [Env.boxPush, Env.boxPushVal]
      rw [hag.ref u hk.2.1]
      erw [c.eval_toC]
      rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

theorem EnvRel.extend {Γ : Ctx} {t : N.frame.W} {e : (c.cone hT hB hS hInd).Env Γ (some t)}
    {e' : N.Env Γ t} (hag : c.EnvRel hT hB hS hInd e e') (r : Root) {T : VarType}
    (o : N.frame.Dom T t) :
    c.EnvRel hT hB hS hInd (e.extend r (c.toC hT hB T t o)) (e'.extend r o) := by
  intro v U hv
  change (if hvr : v = .root r then _ else _) =
    c.toC hT hB U t (if hvr : v = .root r then _ else _)
  split_ifs with hvr
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rfl
  · exact hag _ _ _

theorem EnvRel.mem_ref {Γ : Ctx} {t : N.frame.W} {e : (c.cone hT hB hS hInd).Env Γ (some t)}
    {e' : N.Env Γ t} (hag : c.EnvRel hT hB hS hInd e e') {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (s : N.frame.W) (r : N.frame.R t s) :
    (⟨some s, ⟨r⟩⟩ : (c.frame hT hB).Acc (some t)) ∈
        ((c.cone hT hB hS hInd).posEval (e.ref x hr)).1 ↔
      (⟨s, ⟨r⟩⟩ : N.frame.Acc t) ∈ (N.posEval (e'.ref x hr)).1 := by
  rw [hag.ref x hr]
  rfl

theorem EnvRel.diaPush {Γ : Ctx} {t : N.frame.W} {e : (c.cone hT hB hS hInd).Env Γ (some t)}
    {e' : N.Env Γ t} (hag : c.EnvRel hT hB hS hInd e e') {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (s : N.frame.W) (r : N.frame.R t s)
    (h : (⟨some s, ⟨r⟩⟩ : (c.frame hT hB).Acc (some t)) ∈
      ((c.cone hT hB hS hInd).posEval (e.ref x hr)).1)
    (hm : (⟨s, ⟨r⟩⟩ : N.frame.Acc t) ∈ (N.posEval (e'.ref x hr)).1) :
    c.EnvRel hT hB hS hInd (e.diaPush x hr ⟨_, h⟩) (e'.diaPush x hr ⟨_, hm⟩) := by
  intro v T hv
  match v with
  | .step u .dia =>
      simp only [Env.diaPush, Env.diaPushVal]
      have hXT := Ctx.diaIn_step_dia hr hv
      subst hXT
      have href := hag.ref x hr
      generalize e.ref x hr = q at h href ⊢
      subst href
      rfl
  | .step u .box => exact hag.boxPush ⟨s, ⟨r⟩⟩ (.step u .box) T hv
  | .step u .keep => exact hag.boxPush ⟨s, ⟨r⟩⟩ (.step u .keep) T hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

mutual
  theorem interpFunc_cone {Γ : Ctx} {t : N.frame.W}
      {e : (c.cone hT hB hS hInd).Env Γ (some t)} {e' : N.Env Γ t}
      (hag : c.EnvRel hT hB hS hInd e e') :
      ∀ {n : ℕ} (g : Func σ Γ n) (args : Fin n → N.frame.D t),
        interpFunc e g args = interpFunc e' g args
    | _, .F _, _ => rfl
    | _, .eval g tm, args => by
        change interpFunc e g (Fin.cons (interp e tm) args) =
          interpFunc e' g (Fin.cons (interp e' tm) args)
        rw [interp_cone hag tm]
        exact interpFunc_cone hag g _

  /-- ⭐Below the apex, values are `N`'s. -/
  theorem interp_cone {Γ : Ctx} {t : N.frame.W}
      {e : (c.cone hT hB hS hInd).Env Γ (some t)} {e' : N.Env Γ t}
      (hag : c.EnvRel hT hB hS hInd e e') :
      ∀ {T : VarType} {a : Ann T} (tm : Term σ Γ T a),
        interp e tm = c.toC hT hB T t (interp e' tm)
    | _, _, .var v hv => hag.ref v hv
    | _, _, .func f => interpFunc_cone hag f Fin.elim0
    | _, _, .unit => rfl
    | _, _, .pair s u => by
        change (interp e s, interp e u) = _
        rw [interp_cone hag s, interp_cone hag u]
        rfl
    | _, _, .boxtm tm => by
        apply (c.cone hT hB hS hInd).nec_inj
        funext a
        obtain ⟨_ | s, ⟨r⟩⟩ := a
        · exact False.elim r
        rw [box_beta]
        refine (interp_cone (hag.boxPush ⟨s, ⟨r⟩⟩) tm).trans ?_
        change c.toC hT hB _ s (interp (e'.boxPush ⟨s, ⟨r⟩⟩) tm) =
          c.toC hT hB _ s (N.necEval (interp e' (Term.boxtm tm)) ⟨s, ⟨r⟩⟩)
        rw [box_beta]
    | _, _, .diatm x hx tm => by
        obtain ⟨X, hr⟩ := hx
        refine (c.cone hT hB hS hInd).pos_inj ?_ fun h => flagElim (shaped_false_of hT hS) h
        rw [dia_beta e _ hr]
        obtain ⟨hE, hf⟩ := posSec_of_eq (dia_beta e' ⟨X, hr⟩ hr tm)
        refine posSec_ext' ?_ ?_
        · ext a
          obtain ⟨_ | s, ⟨r⟩⟩ := a
          · exact False.elim r
          change (⟨some s, ⟨r⟩⟩ : (c.frame hT hB).Acc (some t)) ∈
              ((c.cone hT hB hS hInd).posEval (e.ref x hr)).1 ↔
            (⟨s, ⟨r⟩⟩ : N.frame.Acc t) ∈ (N.posEval (interp e' (Term.diatm x ⟨X, hr⟩ tm))).1
          rw [hag.mem_ref hr s r, hE]
        · intro a h h'
          obtain ⟨_ | s, ⟨r⟩⟩ := a
          · exact False.elim r
          have hm : (⟨s, ⟨r⟩⟩ : N.frame.Acc t) ∈ (N.posEval (e'.ref x hr)).1 := hE ▸ h'
          refine (interp_cone (hag.diaPush hr s r h hm) tm).trans ?_
          change c.toC hT hB _ s (interp (e'.diaPush x hr ⟨_, hm⟩) tm) =
            c.toC hT hB _ s ((N.posEval (interp e' (Term.diatm x ⟨X, hr⟩ tm))).2 ⟨⟨s, ⟨r⟩⟩, h'⟩)
          rw [hf ⟨s, ⟨r⟩⟩ h' hm]
end

theorem relSat_cone {Γ : Ctx} {t : N.frame.W} {e : (c.cone hT hB hS hInd).Env Γ (some t)}
    {e' : N.Env Γ t} (hag : c.EnvRel hT hB hS hInd e e') :
    ∀ {n : ℕ} (ρ : Rel σ Γ n) (args : Fin n → N.frame.D t),
      relSat e ρ args ↔ relSat e' ρ args
  | _, .R _, _ => Iff.rfl
  | _, .eval ρ tm, args => by
      change relSat e ρ (Fin.cons (interp e tm) args) ↔ relSat e' ρ (Fin.cons (interp e' tm) args)
      rw [interp_cone hag tm]
      exact relSat_cone hag ρ _

/-- ⭐⭐**Below the apex, a formula means what it means in `N`**: nothing there looks at the
    apex. -/
theorem sat_cone [ModalSys.NoOpt] (hFV : ModalSys.Five = true → ModalSys.Four = true) :
    ∀ {Γ : Ctx} {d : ℕ} {t : N.frame.W}
    {e : (c.cone hT hB hS hInd).Env Γ (some t)} {e' : N.Env Γ t},
    c.EnvRel hT hB hS hInd e e' → (φ : WFF σ Γ d) →
      ((c.cone hT hB hS hInd).sat e φ ↔ N.sat e' φ)
  | _, _, _, _, _, hag, .atom ρ => relSat_cone hag ρ Fin.elim0
  | _, _, _, _, _, hag, .eq s u => by
      change interp _ s = interp _ u ↔ _
      rw [interp_cone hag s, interp_cone hag u]
      exact ⟨c.toC_injective hT hB, congrArg _⟩
  | _, _, _, _, _, _, .top => Iff.rfl
  | _, _, _, _, _, _, .bot => Iff.rfl
  | _, _, _, _, _, hag, .and φ ψ => and_congr (sat_cone hFV hag φ) (sat_cone hFV hag ψ)
  | _, _, _, _, _, hag, .or φ ψ => or_congr (sat_cone hFV hag φ) (sat_cone hFV hag ψ)
  | _, _, _, _, _, hag, .imp φ ψ => imp_congr (sat_cone hFV hag φ) (sat_cone hFV hag ψ)
  | _, d, t, _, _, hag, .all T φ => by
      constructor
      · intro H o
        exact (sat_cone hFV (hag.extend (.bnd d) o) φ).mp (H _)
      · intro H o
        rw [← c.toC_ofC hT hB T t o]
        exact (sat_cone hFV (hag.extend (.bnd d) _) φ).mpr (H _)
  | _, d, t, _, _, hag, .ex T φ => by
      constructor
      · rintro ⟨o, ho⟩
        rw [← c.toC_ofC hT hB T t o] at ho
        exact ⟨_, (sat_cone hFV (hag.extend (.bnd d) _) φ).mp ho⟩
      · rintro ⟨o, ho⟩
        exact ⟨_, (sat_cone hFV (hag.extend (.bnd d) o) φ).mpr ho⟩
  | _, _, _, _, _, hag, .box φ => by
      constructor
      · intro H a
        exact (sat_cone hFV (hag.boxPush a) φ).mp (H _)
      · intro H a
        obtain ⟨_ | s, ⟨r⟩⟩ := a
        · exact False.elim r
        exact (sat_cone hFV (hag.boxPush ⟨s, ⟨r⟩⟩) φ).mpr (H _)
  | _, _, _, _, _, hag, .dia x _ φ => by
      constructor
      · rintro ⟨X, hr, ⟨⟨_ | s, ⟨r⟩⟩, h⟩, H⟩
        · exact False.elim r
        have hm := (hag.mem_ref hr s r).mp h
        exact ⟨X, hr, ⟨_, hm⟩, (sat_cone hFV (hag.diaPush hr s r h hm) φ).mp H⟩
      · rintro ⟨X, hr, ⟨⟨s, ⟨r⟩⟩, hm⟩, H⟩
        have h := (hag.mem_ref hr s r).mpr hm
        exact ⟨X, hr, ⟨_, h⟩, (sat_cone hFV (hag.diaPush hr s r h hm) φ).mpr H⟩
  | _, _, _, _, _, _, .here h _ _ => flagElim hT h
  | _, _, _, _, _, _, .back h _ _ _ => flagElim hS h
  | _, _, _, _, _, _, .retS h _ _ _ => flagElim hS h
  | _, _, _, _, _, _, .retxS h _ _ _ _ _ => flagElim hS h
  | _, _, _, _, _, _, .link hV hF _ _ => flagElim hF (hFV hV)
  | _, _, _, _, _, _, .linkx hV hF _ _ _ _ => flagElim hF (hFV hV)
  | _, _, _, _, _, _, .optx hO _ _ _ => absurd hO (by rw [ModalSys.NoOpt.noOpt]; decide)

variable (c hT hB hS hInd) in
/-- ⭐The cone is a model proper: its `Ind` is equality. -/
theorem cone_indInvariant : (c.cone hT hB hS hInd).IndInvariant :=
  Model.indInvariant_of_eq (fun _ _ h => h) (fun h => flagElim hS h)

end ConeData

end Model

end V12M
