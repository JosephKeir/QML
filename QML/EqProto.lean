/-
PROTOTYPE — "equality by extensionality" reform (isolated, no QML imports).

Goal: check that equality can be DEFINED by recursion (box_ext / dia_ext as equations,
bottoming out at an atomic predicate on individuals), and how the neutral pair-elim case behaves.

Simplifications (ORTHOGONAL to the question — the real system handles them elsewhere):
  * de Bruijn contexts (no names/freshness/α);
  * the modal context transformation is modelled as `boxCtx = id`, `diaCtx = (.base :: ·)`
    (adds the ◇-witness), so two modal terms at the same type share an inner context and are
    comparable — exactly the shape of `box_ext`/`dia_ext`, whose premises take `tt₁ tt₂` over a
    COMMON inner context;
  * only `.base`-typed variables (faithful: the real grammar has NO box/dia/prod-typed `var`).
-/

namespace EqProto

/-- Object-level types: individuals, necessary (□), possible (◇), products, unit. -/
inductive Ty where
  | base : Ty
  | box  : Ty → Ty
  | dia  : Ty → Ty
  | prod : Ty → Ty → Ty
  | unit : Ty
deriving DecidableEq

abbrev Ctx := List Ty

/-- de Bruijn variable pointing at a `.base` entry (no higher-typed variables). -/
inductive BVar : Ctx → Type where
  | here  : {Γ : Ctx} → BVar (.base :: Γ)
  | there : {T : Ty} → {Γ : Ctx} → BVar Γ → BVar (T :: Γ)

/-- Intrinsically-typed terms.  Modal terms carry a body over the transformed context
    (`box`: same context; `dia`: context + the witness variable). -/
inductive Tm : Ctx → Ty → Type where
  | var   : {Γ : Ctx} → BVar Γ → Tm Γ .base
  | boxtm : {Γ : Ctx} → {A : Ty} → Tm Γ A → Tm Γ (.box A)
  | diatm : {Γ : Ctx} → {A : Ty} → Tm (.base :: Γ) A → Tm Γ (.dia A)
  | pair  : {Γ : Ctx} → {A B : Ty} → Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  | unitt : {Γ : Ctx} → Tm Γ .unit

/-- Formulas.  `prim` = the atomic equality predicate on individuals; `box` = necessity;
    `boxx` = witnessed □_x (= ¬◇_x¬), carrying its witness variable. -/
inductive Wff : Ctx → Type where
  | prim : {Γ : Ctx} → Tm Γ .base → Tm Γ .base → Wff Γ
  | top  : {Γ : Ctx} → Wff Γ
  | conj : {Γ : Ctx} → Wff Γ → Wff Γ → Wff Γ
  | imp  : {Γ : Ctx} → Wff Γ → Wff Γ → Wff Γ
  | box  : {Γ : Ctx} → Wff Γ → Wff Γ
  | boxx : {Γ : Ctx} → Wff (.base :: Γ) → Wff Γ

/-- Type size — the termination measure for `eqf`. -/
def Ty.size : Ty → Nat
  | .base => 1
  | .unit => 1
  | .box A => A.size + 1
  | .dia A => A.size + 1
  | .prod A B => A.size + B.size + 1

/-- **Equality defined by recursion on the type** (the reform).  The extensionality principles
    become DEFINING EQUATIONS:
      * `□`-equality  = `box` of the inner equality        (this is `box_ext`, now definitional);
      * `◇`-equality  = `boxx` of the inner equality        (this is `dia_ext`, now definitional);
      * product-eq   = conjunction of component equalities;
      * unit-eq      = ⊤;
      * base-eq      = the primitive atomic equality `prim`.
    Every equality formula therefore bottoms out at `prim` on individuals. -/
def eqf : {Γ : Ctx} → (S : Ty) → Tm Γ S → Tm Γ S → Wff Γ
  | _, .base,     t,          s          => .prim t s
  | _, .box A,    .boxtm tt₁, .boxtm tt₂ => .box  (eqf A tt₁ tt₂)
  | _, .dia A,    .diatm tt₁, .diatm tt₂ => .boxx (eqf A tt₁ tt₂)
  | _, .prod A B, .pair a b,  .pair c d  => .conj (eqf A a c) (eqf B b d)
  | _, .unit,     _,          _          => .top

/-- Sanity: `eqf` of a `□`-term unfolds to `box` of the inner `eqf` — `box_ext` as an equation. -/
example {Γ : Ctx} {A : Ty} (t s : Tm Γ A) :
    eqf (.box A) (.boxtm t) (.boxtm s) = .box (eqf A t s) := rfl

/-- Sanity: `eqf` of a `◇`-term unfolds to `boxx` (witnessed □_x) of the inner `eqf` — `dia_ext`. -/
example {Γ : Ctx} {A : Ty} (t s : Tm (.base :: Γ) A) :
    eqf (.dia A) (.diatm t) (.diatm s) = .boxx (eqf A t s) := rfl

/-- Sanity: nested — equality of `□(b₁ × b₂)` bottoms out at a conjunction of `box`ed `prim`s. -/
example {Γ : Ctx} (t s : Tm Γ (.prod .base .base)) :
    eqf (.box (.prod .base .base)) (.boxtm t) (.boxtm s)
      = .box (eqf (.prod .base .base) t s) := rfl

/-! ## A minimal proof system, and the Leibniz-style derivations

The point: with equality *defined* by the extensionality equations, reflexivity / symmetry /
Leibniz are DERIVED by induction on the type, and the modal cases go through by exactly the
argument you gave — the individual-level proof lifted under `□` (resp. witnessed `□_x`) via
necessitation + the K distribution rule.  The rules below are all standard and available in the
real QML proof system (necessitation, K, mp, atomic reflexivity/symmetry, ∧-intro/congruence). -/

inductive Pf : {Γ : Ctx} → Wff Γ → Prop where
  | primRefl : {Γ : Ctx} → (t : Tm Γ .base) → Pf (.prim t t)
  | primSymm : {Γ : Ctx} → {a b : Tm Γ .base} → Pf (.imp (.prim a b) (.prim b a))
  | topI     : {Γ : Ctx} → Pf (Wff.top (Γ := Γ))
  | idimp    : {Γ : Ctx} → {p : Wff Γ} → Pf (.imp p p)
  | conjI    : {Γ : Ctx} → {p q : Wff Γ} → Pf p → Pf q → Pf (.conj p q)
  | conjCong : {Γ : Ctx} → {p p' q q' : Wff Γ} →
               Pf (.imp p p') → Pf (.imp q q') → Pf (.imp (.conj p q) (.conj p' q'))
  | nec      : {Γ : Ctx} → {p : Wff Γ} → Pf p → Pf (.box p)
  | necx     : {Γ : Ctx} → {p : Wff (.base :: Γ)} → Pf p → Pf (.boxx p)
  -- K distribution: `□(p → q) ⊢ □p → □q`, and its witnessed-`□_x` analogue.
  | Kdist    : {Γ : Ctx} → {p q : Wff Γ} → Pf (.box (.imp p q)) → Pf (.imp (.box p) (.box q))
  | Kdistx   : {Γ : Ctx} → {p q : Wff (.base :: Γ)} →
               Pf (.boxx (.imp p q)) → Pf (.imp (.boxx p) (.boxx q))

/-- **Reflexivity of the defined equality**, by induction on the type.  The `□`/`◇` cases are
    `necessitation` of the inner reflexivity — the term is forced to be `boxtm`/`diatm` because
    there are no higher-typed variables. -/
def eqf_refl : {Γ : Ctx} → {S : Ty} → (t : Tm Γ S) → Pf (eqf S t t)
  | _, .base,     t           => by simp only [eqf]; exact .primRefl t
  | _, .box _,    .boxtm tt    => by simp only [eqf]; exact .nec  (eqf_refl tt)
  | _, .dia _,    .diatm tt    => by simp only [eqf]; exact .necx (eqf_refl tt)
  | _, .prod _ _, .pair a b    => by simp only [eqf]; exact .conjI (eqf_refl a) (eqf_refl b)
  | _, .unit,     _            => by simp only [eqf]; exact .topI

/-- **Symmetry of the defined equality, as an object implication** `a ≐ b → b ≐ a`, by induction on
    the type.  The `□` case is your exact argument: from the individual-level implication
    `(a' ≐ b') → (b' ≐ a')` (the IH), `necessitate` it and push it through with `K` — giving
    `□(a' ≐ b') → □(b' ≐ a')`, i.e. `(□a' ≐ □b') → (□b' ≐ □a')`.  The `◇` case is *the same proof*
    with the witnessed `□_x` (`necx` + `Kdistx`). -/
def eqf_symm : {Γ : Ctx} → {S : Ty} → (a b : Tm Γ S) → Pf (.imp (eqf S a b) (eqf S b a))
  | _, .base,     _,           _           => by simp only [eqf]; exact .primSymm
  | _, .box _,    .boxtm a',   .boxtm b'   => by simp only [eqf]; exact .Kdist  (.nec  (eqf_symm a' b'))
  | _, .dia _,    .diatm a',   .diatm b'   => by simp only [eqf]; exact .Kdistx (.necx (eqf_symm a' b'))
  | _, .prod _ _, .pair a1 a2, .pair b1 b2 => by simp only [eqf]; exact .conjCong (eqf_symm a1 b1) (eqf_symm a2 b2)
  | _, .unit,     _,           _           => by simp only [eqf]; exact .idimp

end EqProto

#print axioms EqProto.eqf_refl
#print axioms EqProto.eqf_symm
