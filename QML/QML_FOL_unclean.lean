import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Image


/-!
# Classical First-Order Logic: Natural Deduction

This file defines the syntax and proof theory of classical first-order logic
via a natural deduction system.
-/

-- Variable symbols (with decidable equality for substitution)
-- We index variables by natural numbers, so that we have a countable set of variables V1, V2, ...
inductive VarSymb : Type where
  | V : ℕ → VarSymb
  deriving DecidableEq

-- function symbols and relation/predicate symbols
-- terms of type FuncSymb V n are n-ary functions, possibly partially evaluated on terms
-- built from the symbols in V. Terms are either variables or 0-ary functions
mutual
  inductive Func (V : Finset VarSymb) : ℕ → Type where
    | F (m : ℕ) : Func V n
    | eval : Func V (Nat.succ n) → Term V → Func V n
    deriving DecidableEq

  inductive Term (V : Finset VarSymb) : Type where
    | var  : {v : VarSymb // v ∈ V} → Term V
    | func : Func V 0 → Term V
    deriving DecidableEq
end

-- relation symbols: a term of type RelSymb V n is an n-ary relation symbol,
-- possibly partially evaluated.
inductive RelSymb (V : Finset VarSymb) : ℕ → Type where
  | R (m : ℕ) : RelSymb V n
  | eval : RelSymb V (Nat.succ n) → Term V → RelSymb V n
  deriving DecidableEq

-- there is a coersion from variable symbols to terms, so variable symbols can be treated as terms
instance : Coe {v : VarSymb // v ∈ V} (Term V) where coe := Term.var

/-! ## Substitution (mutual recursion over Term and Vec Term) -/

/- Substitute b for a -/
mutual
  def Term.subst {V : Finset VarSymb} (a : Term V) (b : Term V) : Term V → Term V
    | .var y    => if b = .var y then a else .var y
    | .func f   => if b = .func f then a else .func ((Func.subst a b) f)

  def Func.subst {V : Finset VarSymb} (a : Term V) (b : Term V) : Func V n → Func V n
    | .F m      => .F m
    | .eval f t => .eval (Func.subst a b f) (Term.subst a b t)
end

def Rel.subst {V : Finset VarSymb} (a : Term V) (b : Term V) : RelSymb V n → RelSymb V n
  | .R m => .R m
  | .eval R t => .eval (Rel.subst a b R) (Term.subst a b t)

/-! ## Well-Formed Formulas -/

inductive WFF : Finset VarSymb → Type where
  | atom : RelSymb V 0 → WFF V
  | top  : WFF V
  | bot  : WFF V
  | and  : WFF V → WFF V → WFF V
  | or   : WFF V → WFF V → WFF V
  | imp  : WFF V → WFF V → WFF V
  | all  : Π x : VarSymb, WFF (V ∪ {x}) → WFF V
  | ex   : Π x : VarSymb, WFF (V ∪ {x}) → WFF V
deriving DecidableEq

namespace WFF

def Scoped : WFF V → Prop
  | .atom _ | .top | .bot        => True
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.Scoped ∧ ψ.Scoped
  | .all x φ => x ∉ V ∧ φ.Scoped   -- φ : WFF (V ∪ {x})
  | .ex  x φ => x ∉ V ∧ φ.Scoped


def boundVars : WFF V → Finset VarSymb
  | .atom _ | .top | .bot      => ∅
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.boundVars ∪ ψ.boundVars
  | .all x φ => {x} ∪ φ.boundVars
  | .ex  x φ => {x} ∪ φ.boundVars


def neg {V : Finset VarSymb} (φ : WFF V) : WFF V := imp φ bot

/- Context extension replaces the variable context V with a bigger one -/
mutual
  def ctx_ext_term (v : VarSymb) (t : Term V) : Term (V ∪ {v}) :=
    match t with
      | .var w => by
        refine .var ⟨w, ?_⟩
        refine Finset.mem_union.mpr ?_
        left
        exact w.property
      | .func f => by
        refine .func ?_
        exact ctx_ext_func v f

  def ctx_ext_func (v : VarSymb) (f : Func V n) : Func (V ∪ {v}) n :=
    match f with
      | .F m => .F m
      | .eval g t => .eval (ctx_ext_func v g) (ctx_ext_term v t)
end

def subst {V : Finset VarSymb} (a : Term V) (b : Term V) : (WFF V) → (WFF V)
  | .atom P    => .atom (Rel.subst a b P)
  | .top       => .top
  | .bot       => .bot
  | .and ψ χ   => .and (subst a b ψ) (subst a b χ)
  | .or ψ χ    => .or (subst a b ψ) (subst a b χ)
  | .imp ψ χ   => .imp (subst a b ψ) (subst a b χ)
  | .all x ψ   => .all x (subst (ctx_ext_term x a) (ctx_ext_term x b) ψ)
  | .ex x ψ    => .ex x (subst (ctx_ext_term x a) (ctx_ext_term x b) ψ)


/- replace all occurences of the term (.var v) with the term s, and change the context so that
  v no longer appears -/
mutual
  def ctx_rest_term (s : Term V) (v : VarSymb) (t : Term (V ∪ {v})) : Term V :=
    match t with
      | .var ⟨w, wh⟩ => by
        apply Finset.mem_union.mp at wh
        if whV : w ∈ V then
          exact .var ⟨w, whV⟩
        else
          exact s
      | .func F => .func (ctx_rest_func s v F)

  def ctx_rest_func (s : Term V) (v : VarSymb) (f : Func (V ∪ {v}) n) : Func V n :=
    match f with
    | .F m => .F m
    | .eval g t => .eval (ctx_rest_func s v g) (ctx_rest_term s v t)
end


/-! ## Notation -/

infixr:35  " →ₘ " => WFF.imp
infixl:65  " ∧ₘ " => WFF.and
infixl:60  " ∨ₘ " => WFF.or
prefix:75  "¬ₘ"   => WFF.neg
notation   "⊤ₘ"   => WFF.top
notation   "⊥ₘ"   => WFF.bot
notation   "∀ₘ"   => WFF.all
notation   "∃ₘ"   => WFF.ex


def ctx_ext_RelSymb (v : VarSymb) (R : RelSymb V n) : RelSymb (V ∪ {v}) n :=
  match R with
  | .R m => .R m
  | .eval R t => .eval (ctx_ext_RelSymb v R) (ctx_ext_term v t)


def ctx_rest_RelSymb (s : Term V) (v : VarSymb) (R : RelSymb (V ∪ {v}) n) : RelSymb V n :=
  match R with
  | .R m => .R m
  | .eval R t => .eval (ctx_rest_RelSymb s v R) (ctx_rest_term s v t)


def ctx_ext_WFF (v : VarSymb) (ψ : WFF V) : WFF (V ∪ {v}) :=
  match ψ with
  | .atom R => .atom (ctx_ext_RelSymb v R)
  | .top => .top
  | .bot => .bot
  | .and ψ φ => .and (ctx_ext_WFF v ψ) (ctx_ext_WFF v φ)
  | .or ψ φ => .or (ctx_ext_WFF v ψ) (ctx_ext_WFF v φ)
  | .imp ψ φ => .imp (ctx_ext_WFF v ψ) (ctx_ext_WFF v φ)
  | .all x φ => .all x (Finset.union_right_comm V {x} {v} ▸ ctx_ext_WFF v φ)
  | .ex  x φ => .ex  x (Finset.union_right_comm V {x} {v} ▸ ctx_ext_WFF v φ)

/- Need this to show that ctx_rest_WFF terminates, otherwise the cast prevents termination
by checking size-/
def wffDepth : WFF V → ℕ
  | .atom _ => 0
  | .top    => 0
  | .bot    => 0
  | .and φ ψ => wffDepth φ + wffDepth ψ + 1
  | .or  φ ψ => wffDepth φ + wffDepth ψ + 1
  | .imp φ ψ => wffDepth φ + wffDepth ψ + 1
  | .all _ φ => wffDepth φ + 1
  | .ex  _ φ => wffDepth φ + 1

lemma wffDepth_cast {V W : Finset VarSymb} (h : V = W) (φ : WFF V) :
    wffDepth (h ▸ φ) = wffDepth φ := by subst h; rfl

lemma Scoped_cast {V W : Finset VarSymb} (h : V = W) (φ : WFF V) :
    WFF.Scoped (h ▸ φ) = WFF.Scoped φ := by subst h; rfl

/- lemma ctx_ext_WFF_Scoped {V : Finset VarSymb} (v : VarSymb) (φ : WFF V)
    (hφ : φ.Scoped) (hv : v ∉ φ.boundVars) : (ctx_ext_WFF v φ).Scoped := by
  induction φ with
  | atom _ | top | bot => trivial
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
      simp only [boundVars, Finset.mem_union, not_or] at hv
      exact ⟨ihφ hφ.1 hv.1, ihψ hφ.2 hv.2⟩
  | all x φ ih =>
    simp only [boundVars, Finset.mem_union, Finset.mem_singleton, not_or] at hv
    rename_i V'
    change WFF.Scoped (WFF.all x (Finset.union_right_comm V' {x} {v} ▸ ctx_ext_WFF v φ))
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨hφ.1, Ne.symm hv.1⟩
    · rw [Scoped_cast]
      exact ih hφ.2 hv.2
  | ex x φ ih =>
    simp only [boundVars, Finset.mem_union, Finset.mem_singleton, not_or] at hv
    rename_i V'
    change WFF.Scoped (WFF.ex x (Finset.union_right_comm V' {x} {v} ▸ ctx_ext_WFF v φ))
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨hφ.1, Ne.symm hv.1⟩
    · rw [Scoped_cast]
      exact ih hφ.2 hv.2 -/

def ctx_rest_WFF (s : Term V) (v : VarSymb) (ψ : WFF (V ∪ {v})) (hψ : ψ.Scoped) : WFF V :=
  match ψ with
  | .atom R => .atom (ctx_rest_RelSymb s v R)
  | .top => .top
  | .bot => .bot
  | .and ψ φ => .and (ctx_rest_WFF s v ψ hψ.1) (ctx_rest_WFF s v φ hψ.2)
  | .or ψ φ => .or (ctx_rest_WFF s v ψ hψ.1) (ctx_rest_WFF s v φ hψ.2)
  | .imp ψ φ => .imp (ctx_rest_WFF s v ψ hψ.1) (ctx_rest_WFF s v φ hψ.2)
  | .all x φ => by
      let φ' : WFF (V ∪ {x} ∪ {v}) := Finset.union_right_comm V {v} {x} ▸ φ
      refine .all x (ctx_rest_WFF (ctx_ext_term x s) v φ' ?_)
      rw [Scoped_cast]
      exact hψ.2
  | .ex x φ     => by
      let φ' : WFF (V ∪ {x} ∪ {v}) := Finset.union_right_comm V {v} {x} ▸ φ
      refine .ex x (ctx_rest_WFF (ctx_ext_term x s) v φ' ?_)
      rw [Scoped_cast]
      exact hψ.2
termination_by wffDepth ψ
decreasing_by
  all_goals simp_wf
  all_goals simp [wffDepth, wffDepth_cast]
  all_goals omega


def ctx_ext_Finset_WFF (v : VarSymb) (Γ : Finset (WFF V)) : Finset (WFF (V ∪ {v})) :=
  Finset.image (ctx_ext_WFF v) Γ


def ctx_rest_Finset_WFF (s : Term V) (v : VarSymb)
    (Γ : Finset (WFF (V ∪ {v}))) (hΓ : ∀ φ ∈ Γ, φ.Scoped)
    : Finset (WFF V) :=
  Γ.attach.image (fun ⟨ψ, hψ⟩ => ctx_rest_WFF s v ψ (hΓ ψ hψ))




/-! ## Natural Deduction Proof System -/



-- Proof V Γ φ means: in variable context V, from hypotheses Γ, we can derive φ.
inductive Proof : (V : Finset VarSymb) → Finset (WFF V) → (WFF V) → Type where
  -- Axiom: if φ ∈ Γ then V ; Γ ⊢ φ
  | ax         : φ ∈ (Γ : Finset (WFF V)) → φ.Scoped → Proof V Γ φ
  -- Weakening of hypotheses
  | weak       : (ψ.Scoped) → Proof V Γ φ → Proof V (Γ ∪ {ψ}) φ
  -- Weakening of variable context
  | weak_ctx   : (v : VarSymb)
                → v ∉ φ.boundVars
                → (∀ ψ ∈ (Γ : Finset (WFF V)), v ∉ ψ.boundVars)
                → Proof V Γ φ → Proof (V ∪ {v}) (ctx_ext_Finset_WFF v Γ) (ctx_ext_WFF v φ)
  -- Strengthens the context in the case where everything is lifted to a larger context
  | ctx_rest : (y : VarSymb) → (y ∉ V) → (hψ : (ctx_ext_WFF y ψ).Scoped)
           → Proof (V ∪ {y}) (ctx_ext_Finset_WFF y Γ) (ctx_ext_WFF y ψ)
           → Proof V Γ ψ
  -- Conjunction introduction and elimination
  | and_intro  : Proof V Γ φ → Proof V Γ ψ → Proof V Γ (φ ∧ₘ ψ)
  | and_elim_l : Proof V Γ (φ ∧ₘ ψ) → Proof V Γ φ
  | and_elim_r : Proof V Γ (φ ∧ₘ ψ) → Proof V Γ ψ
  -- Disjunction introduction and elimination
  | or_intro_l : ψ.Scoped → Proof V Γ φ → Proof V Γ (φ ∨ₘ ψ)
  | or_intro_r : φ.Scoped → Proof V Γ ψ → Proof V Γ (φ ∨ₘ ψ)
  | or_elim    : Proof V Γ (φ ∨ₘ ψ) →
                 Proof V (Γ ∪ {φ}) χ → Proof V (Γ ∪ {ψ}) χ →
                 Proof V Γ χ
  -- Implication introduction (discharge hypothesis) and elimination (modus ponens)
  | imp_intro  : φ.Scoped → Proof V (Γ ∪ {φ}) ψ → Proof V Γ (φ →ₘ ψ)
  | imp_elim   : Proof V Γ (φ →ₘ ψ) → Proof V Γ φ → Proof V Γ ψ
  -- Top introduction and bottom elimination (ex falso)
  | top_intro  : Proof V Γ ⊤ₘ
  | bot_elim   : φ.Scoped → Proof V Γ ⊥ₘ → Proof V Γ φ
  -- Law of excluded middle
  | lem        : φ.Scoped → Proof V Γ (φ ∨ₘ (¬ₘ φ))
  -- Universal quantifier introduction:
  -- If we can prove φ with x available, and x does not appear free in any
  -- hypothesis, then we can universally quantify over x.
  | all_intro  : (x : VarSymb) → {φ : WFF (V ∪ {x})} → (x ∉ V) → Proof (V ∪ {x}) (ctx_ext_Finset_WFF x Γ) φ → Proof V Γ (WFF.all x φ)
  -- Universal quantifier elimination:
  -- From ∀x.φ, derive φ[x/s] for any term s well-formed in V.
  /- | all_elim : Π y : VarSymb,
              Π hy : y ∉ φ.boundVars,
              (∀ ψ ∈ (Γ : Finset (WFF V)), y ∉ ψ.boundVars)
              → (hφ : φ.Scoped)
              → Π t : Term (V ∪ {y}),
              Proof V Γ (WFF.all x φ)
              → Proof (V ∪ {y}) (ctx_ext_Finset_WFF y Γ)
                (ctx_rest_WFF t x (Finset.union_right_comm V {x} {y} ▸ ctx_ext_WFF y φ)
                  (Scoped_cast (Finset.union_right_comm V {x} {y})
                  (ctx_ext_WFF y φ) ▸ ctx_ext_WFF_Scoped y φ hφ hy)) -/
  | all_elim   : (x : VarSymb) → {φ : WFF (V ∪ {x})} → Π t : Term (V ∪ {x}), Proof V Γ (WFF.all x φ)
                → Proof (V ∪ {x}) (ctx_ext_Finset_WFF x Γ)
                  (φ.subst t (.var ⟨x, Finset.mem_union_right V (Finset.mem_singleton_self x)⟩))
  -- Existential quantifier introduction:
  -- From φ[x/s] with s well-formed in V, derive ∃x.φ.
  | ex_intro : (x : VarSymb) → {φ : WFF (V ∪ {x})} → (x ∉ V) → (s : Term V) → (hφ : φ.Scoped) → Proof V Γ (ctx_rest_WFF s x φ hφ)
                → Proof V Γ (WFF.ex x φ)
  -- Existential quantifier elimination:
  -- From ∃x.φ and V ∪ {x}, Γ ∪ {φ} ⊢ ψ (x not free in ψ or Γ), derive ψ.
  | ex_elim : (x : VarSymb) → {φ : WFF (V ∪ {x})} → (x ∉ V) → Proof V Γ (WFF.ex x φ) →
                 Proof (V ∪ {x}) ((ctx_ext_Finset_WFF x Γ) ∪ {φ}) (ctx_ext_WFF x ψ) →
                 Proof V Γ ψ

-- Turnstile notation
notation:30 V " ; " Γ " ⊢ₘ " φ => Proof V Γ φ
