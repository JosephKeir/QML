import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Image

/-!
# Classical First-Order Logic: Natural Deduction

This file defines the syntax and proof theory of classical first-order logic
via a natural deduction system with explicit variable contexts.
-/

/-! ## Signature -/

-- A signature specifies the function and relation symbols and their arities.
structure Signature where
  FuncSyms : Type
  RelSyms  : Type
  funcArity : FuncSyms → ℕ
  relArity  : RelSyms  → ℕ
  [decEqF  : DecidableEq FuncSyms]
  [decEqR  : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

/-! ## Variable Symbols -/

-- Variables are indexed by natural numbers, giving a countable supply V₁, V₂, ...
inductive VarSymb : Type where
  | V : ℕ → VarSymb
  deriving DecidableEq

/-! ## Terms and Function Symbols -/

-- `Func σ V n` is an n-ary function symbol, possibly partially applied to terms over V.
-- `Term σ V` is either a variable in V or a fully-applied (0-ary) function symbol.
-- Arity is enforced at construction: `F ⟨f, h⟩` requires a proof `h : σ.funcArity f = n`.
mutual
  inductive Func (σ : Signature) (V : Finset VarSymb) : ℕ → Type where
    | F    : {f : σ.FuncSyms // σ.funcArity f = n} → Func σ V n
    | eval : Func σ V (Nat.succ n) → Term σ V → Func σ V n
    deriving DecidableEq

  inductive Term (σ : Signature) (V : Finset VarSymb) : Type where
    | var  : {v : VarSymb // v ∈ V} → Term σ V
    | func : Func σ V 0 → Term σ V
    deriving DecidableEq
end

/-! ## Relation Symbols -/

-- `RelSymb σ V n` is an n-ary relation symbol, possibly partially applied to terms over V.
-- Arity is enforced at construction: `R ⟨r, h⟩` requires a proof `h : σ.relArity r = n`.
inductive RelSymb (σ : Signature) (V : Finset VarSymb) : ℕ → Type where
  | R    : {r : σ.RelSyms // σ.relArity r = n} → RelSymb σ V n
  | eval : RelSymb σ V (Nat.succ n) → Term σ V → RelSymb σ V n
  deriving DecidableEq

-- Variables can be coerced to terms.
instance : Coe {v : VarSymb // v ∈ V} (Term σ V) where coe := Term.var

/-! ## Substitution -/

-- `Term.subst a b t` replaces occurrences of `b` with `a` in `t`.
mutual
  def Term.subst {σ : Signature} {V : Finset VarSymb} (a b : Term σ V) : Term σ V → Term σ V
    | .var y  => if b = .var y  then a else .var y
    | .func f => if b = .func f then a else .func (Func.subst a b f)

  def Func.subst {σ : Signature} {V : Finset VarSymb} (a b : Term σ V) : Func σ V n → Func σ V n
    | .F s      => .F s
    | .eval f t => .eval (Func.subst a b f) (Term.subst a b t)
end

def Rel.subst {σ : Signature} {V : Finset VarSymb} (a b : Term σ V) : RelSymb σ V n → RelSymb σ V n
  | .R r      => .R r
  | .eval R t => .eval (Rel.subst a b R) (Term.subst a b t)

/-! ## Well-Formed Formulas -/

-- `WFF σ V` is the type of formulas over signature σ whose free variables lie in V.
-- Quantifiers extend the context: `all x φ` binds x, with `φ : WFF σ (V ∪ {x})`.
inductive WFF (σ : Signature) : Finset VarSymb → Type where
  | atom : RelSymb σ V 0 → WFF σ V
  | top  : WFF σ V
  | bot  : WFF σ V
  | and  : WFF σ V → WFF σ V → WFF σ V
  | or   : WFF σ V → WFF σ V → WFF σ V
  | imp  : WFF σ V → WFF σ V → WFF σ V
  | all  : (x : VarSymb) → WFF σ (V ∪ {x}) → WFF σ V
  | ex   : (x : VarSymb) → WFF σ (V ∪ {x}) → WFF σ V
  | eq   : Term σ V → Term σ V → WFF σ V
  deriving DecidableEq

namespace WFF

variable {σ : Signature}

def neg (φ : WFF σ V) : WFF σ V := imp φ bot

/-! ## Notation -/

infixr:35  " →ₘ "  => WFF.imp
infixl:65  " ∧ₘ "  => WFF.and
infixl:60  " ∨ₘ "  => WFF.or
prefix:75  "¬ₘ "   => WFF.neg
notation   "⊤ₘ"    => WFF.top
notation   "⊥ₘ"    => WFF.bot
notation   "∀ₘ"    => WFF.all
notation   "∃ₘ"    => WFF.ex
infix:50   " =ₘ "  => WFF.eq

/-! ## Well-Scopedness -/

-- A formula is Scoped if every bound variable x in a quantifier ∀x/∃x is
-- genuinely fresh: x ∉ V at the point of binding.
def Scoped : WFF σ V → Prop
  | .atom _ | .top | .bot | .eq _ _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ  => φ.Scoped ∧ ψ.Scoped
  | .all x φ                        => x ∉ V ∧ φ.Scoped
  | .ex  x φ                        => x ∉ V ∧ φ.Scoped

-- The set of variables bound by quantifiers in a formula.
def boundVars : WFF σ V → Finset VarSymb
  | .atom _ | .top | .bot | .eq _ _ => ∅
  | .and φ ψ | .or φ ψ | .imp φ ψ  => φ.boundVars ∪ ψ.boundVars
  | .all x φ                        => {x} ∪ φ.boundVars
  | .ex  x φ                        => {x} ∪ φ.boundVars

/-! ## Context Extension -/

-- Lift a term/function symbol into a larger variable context.
mutual
  def ctx_ext_term (v : VarSymb) (t : Term σ V) : Term σ (V ∪ {v}) :=
    match t with
    | .var w  => .var ⟨w, Finset.mem_union_left {v} w.property⟩
    | .func f => .func (ctx_ext_func v f)

  def ctx_ext_func (v : VarSymb) (f : Func σ V n) : Func σ (V ∪ {v}) n :=
    match f with
    | .F m      => .F m
    | .eval g t => .eval (ctx_ext_func v g) (ctx_ext_term v t)
end

def ctx_ext_RelSymb (v : VarSymb) (R : RelSymb σ V n) : RelSymb σ (V ∪ {v}) n :=
  match R with
  | .R r      => .R r
  | .eval R t => .eval (ctx_ext_RelSymb v R) (ctx_ext_term v t)

-- Lift a formula into a larger variable context.
-- For quantifiers ∀x/∃x, the bound variable commutes past the new variable v.
def ctx_ext_WFF (v : VarSymb) (ψ : WFF σ V) : WFF σ (V ∪ {v}) :=
  match ψ with
  | .atom R  => .atom (ctx_ext_RelSymb v R)
  | .top     => .top
  | .bot     => .bot
  | .and φ ψ => .and (ctx_ext_WFF v φ) (ctx_ext_WFF v ψ)
  | .or  φ ψ => .or  (ctx_ext_WFF v φ) (ctx_ext_WFF v ψ)
  | .imp φ ψ => .imp (ctx_ext_WFF v φ) (ctx_ext_WFF v ψ)
  | .all x φ => .all x (Finset.union_right_comm V {x} {v} ▸ ctx_ext_WFF v φ)
  | .ex  x φ => .ex  x (Finset.union_right_comm V {x} {v} ▸ ctx_ext_WFF v φ)
  | .eq  s t => .eq  (ctx_ext_term v s) (ctx_ext_term v t)

def ctx_ext_Finset_WFF (v : VarSymb) (Γ : Finset (WFF σ V)) : Finset (WFF σ (V ∪ {v})) :=
  Finset.image (ctx_ext_WFF v) Γ

/-! ## Formula Substitution -/

-- `φ.subst a b` replaces occurrences of term `b` with term `a` in `φ`.
def subst (a b : Term σ V) : WFF σ V → WFF σ V
  | .atom P  => .atom (Rel.subst a b P)
  | .top     => .top
  | .bot     => .bot
  | .and φ ψ => .and (subst a b φ) (subst a b ψ)
  | .or  φ ψ => .or  (subst a b φ) (subst a b ψ)
  | .imp φ ψ => .imp (subst a b φ) (subst a b ψ)
  | .all x φ => .all x (subst (ctx_ext_term x a) (ctx_ext_term x b) φ)
  | .ex  x φ => .ex  x (subst (ctx_ext_term x a) (ctx_ext_term x b) φ)
  | .eq  s t => .eq  (Term.subst a b s) (Term.subst a b t)

/-! ## Context Restriction -/

-- wffDepth is a size measure transparent to type-level casts.
def wffDepth : WFF σ V → ℕ
  | .atom _ | .eq _ _ => 0
  | .top              => 0
  | .bot              => 0
  | .and φ ψ => wffDepth φ + wffDepth ψ + 1
  | .or  φ ψ => wffDepth φ + wffDepth ψ + 1
  | .imp φ ψ => wffDepth φ + wffDepth ψ + 1
  | .all _ φ => wffDepth φ + 1
  | .ex  _ φ => wffDepth φ + 1

lemma wffDepth_cast {V W : Finset VarSymb} (h : V = W) (φ : WFF σ V) :
    wffDepth (h ▸ φ) = wffDepth φ := by subst h; rfl

lemma Scoped_cast {V W : Finset VarSymb} (h : V = W) (φ : WFF σ V) :
    WFF.Scoped (h ▸ φ) = WFF.Scoped φ := by subst h; rfl

-- Restrict terms and relation symbols from V ∪ {v} back to V.
mutual
  def ctx_rest_term (s : Term σ V) (v : VarSymb) (t : Term σ (V ∪ {v})) : Term σ V :=
    match t with
    | .var ⟨w, _⟩ =>
        if hV : w ∈ V then .var ⟨w, hV⟩
        else s
    | .func f => .func (ctx_rest_func s v f)

  def ctx_rest_func (s : Term σ V) (v : VarSymb) (f : Func σ (V ∪ {v}) n) : Func σ V n :=
    match f with
    | .F m      => .F m
    | .eval g t => .eval (ctx_rest_func s v g) (ctx_rest_term s v t)
end

def ctx_rest_RelSymb (s : Term σ V) (v : VarSymb) (R : RelSymb σ (V ∪ {v}) n) : RelSymb σ V n :=
  match R with
  | .R r      => .R r
  | .eval R t => .eval (ctx_rest_RelSymb s v R) (ctx_rest_term s v t)

-- Restrict a formula from context V ∪ {v} back to V, replacing occurrences
-- of the variable v with the term s. Requires a Scoped proof to ensure
-- v is not a bound variable in ψ (preventing capture).
def ctx_rest_WFF (s : Term σ V) (v : VarSymb) (ψ : WFF σ (V ∪ {v})) (hψ : ψ.Scoped) : WFF σ V :=
  match ψ with
  | .atom R  => .atom (ctx_rest_RelSymb s v R)
  | .top     => .top
  | .bot     => .bot
  | .eq  t u => .eq  (ctx_rest_term s v t) (ctx_rest_term s v u)
  | .and φ ψ => .and (ctx_rest_WFF s v φ hψ.1) (ctx_rest_WFF s v ψ hψ.2)
  | .or  φ ψ => .or  (ctx_rest_WFF s v φ hψ.1) (ctx_rest_WFF s v ψ hψ.2)
  | .imp φ ψ => .imp (ctx_rest_WFF s v φ hψ.1) (ctx_rest_WFF s v ψ hψ.2)
  | .all x φ => by
      let φ' : WFF σ (V ∪ {x} ∪ {v}) := Finset.union_right_comm V {v} {x} ▸ φ
      refine .all x (ctx_rest_WFF (ctx_ext_term x s) v φ' ?_)
      rw [Scoped_cast]; exact hψ.2
  | .ex  x φ => by
      let φ' : WFF σ (V ∪ {x} ∪ {v}) := Finset.union_right_comm V {v} {x} ▸ φ
      refine .ex x (ctx_rest_WFF (ctx_ext_term x s) v φ' ?_)
      rw [Scoped_cast]; exact hψ.2
termination_by wffDepth ψ
decreasing_by
  all_goals simp_wf
  all_goals simp [wffDepth, wffDepth_cast]
  all_goals omega

def ctx_rest_Finset_WFF (s : Term σ V) (v : VarSymb)
    (Γ : Finset (WFF σ (V ∪ {v}))) (hΓ : ∀ φ ∈ Γ, φ.Scoped) : Finset (WFF σ V) :=
  Γ.attach.image (fun ⟨ψ, hψ⟩ => ctx_rest_WFF s v ψ (hΓ ψ hψ))

/-! ## Natural Deduction Proof System -/

-- `Proof σ V Γ φ` means: from hypotheses Γ (formulas over σ with free variables in V),
-- we can derive φ, all within variable context V.
inductive Proof (σ : Signature) : (V : Finset VarSymb) → Finset (WFF σ V) → WFF σ V → Type where
  -- Structural rules
  | ax       : φ ∈ (Γ : Finset (WFF σ V)) → φ.Scoped
               → Proof σ V Γ φ
  | weak     : ψ.Scoped → Proof σ V Γ φ
               → Proof σ V (Γ ∪ {ψ}) φ
  | weak_ctx : (v : VarSymb) → v ∉ φ.boundVars → (∀ ψ ∈ (Γ : Finset (WFF σ V)), v ∉ ψ.boundVars)
               → Proof σ V Γ φ
               → Proof σ (V ∪ {v}) (ctx_ext_Finset_WFF v Γ) (ctx_ext_WFF v φ)
  -- Conjunction
  | and_intro  : Proof σ V Γ φ → Proof σ V Γ ψ
                 → Proof σ V Γ (φ ∧ₘ ψ)
  | and_elim_l : Proof σ V Γ (φ ∧ₘ ψ) → Proof σ V Γ φ
  | and_elim_r : Proof σ V Γ (φ ∧ₘ ψ) → Proof σ V Γ ψ
  -- Disjunction
  | or_intro_l : ψ.Scoped → Proof σ V Γ φ → Proof σ V Γ (φ ∨ₘ ψ)
  | or_intro_r : φ.Scoped → Proof σ V Γ ψ → Proof σ V Γ (φ ∨ₘ ψ)
  | or_elim    : Proof σ V Γ (φ ∨ₘ ψ)
                 → Proof σ V (Γ ∪ {φ}) χ → Proof σ V (Γ ∪ {ψ}) χ
                 → Proof σ V Γ χ
  -- Implication
  | imp_intro  : φ.Scoped → Proof σ V (Γ ∪ {φ}) ψ → Proof σ V Γ (φ →ₘ ψ)
  | imp_elim   : Proof σ V Γ (φ →ₘ ψ) → Proof σ V Γ φ → Proof σ V Γ ψ
  -- Truth and falsity
  | top_intro  : Proof σ V Γ ⊤ₘ
  | bot_elim   : φ.Scoped → Proof σ V Γ ⊥ₘ → Proof σ V Γ φ
  -- Classical logic
  | lem        : φ.Scoped → Proof σ V Γ (φ ∨ₘ (¬ₘ φ))
  -- Universal quantifier
  -- Introduction: prove φ in the extended context V ∪ {x}, with x fresh.
  | all_intro  : (x : VarSymb) → {φ : WFF σ (V ∪ {x})} → x ∉ V
                 → Proof σ (V ∪ {x}) (ctx_ext_Finset_WFF x Γ) φ
                 → Proof σ V Γ (∀ₘ x φ)
  -- Elimination: from ∀x.φ and a term t : Term σ V, get φ[t/x] back in context V.
  | all_elim   : {φ : WFF σ (V ∪ {x})} → (hφ : φ.Scoped) → (t : Term σ V)
                 → Proof σ V Γ (∀ₘ x φ)
                 → Proof σ V Γ (ctx_rest_WFF t x φ hφ)
  -- Existential quantifier
  -- Introduction: provide a witness s : Term σ V and a proof of φ[s/x].
  | ex_intro   : (x : VarSymb) → {φ : WFF σ (V ∪ {x})} → x ∉ V → (t : Term σ V)
                 → (hφ : φ.Scoped)
                 → Proof σ V Γ (ctx_rest_WFF t x φ hφ)
                 → Proof σ V Γ (∃ₘ x φ)
  -- Elimination: from ∃x.φ, derive ψ given that ψ holds with x as a fresh variable.
  | ex_elim    : (x : VarSymb) → {φ : WFF σ (V ∪ {x})} → x ∉ V
                 → Proof σ V Γ (∃ₘ x φ)
                 → Proof σ (V ∪ {x}) (ctx_ext_Finset_WFF x Γ ∪ {φ}) (ctx_ext_WFF x ψ)
                 → Proof σ V Γ ψ
  -- Equality
  -- Introduction: given a term t, get t = t
  | eq_intro   : (t : Term σ V) → Proof σ V Γ (t =ₘ t)
  -- Elimination: given t = s, sub t for s
  | eq_elim   : Proof σ V Γ (t =ₘ s) → Proof σ V Γ ψ → Proof σ V Γ (ψ.subst t s)

-- Turnstile notation: σ , V ; Γ ⊢ₘ φ
notation:30 σ " , " V " ; " Γ " ⊢ₘ " φ => Proof σ V Γ φ

end WFF
