import Mathlib

/-!
# Quantified Modal Logic: Natural Deduction

This file defines the syntax and proof theory of QML
via a natural deduction system with explicit variable contexts.
Contexts are lists (not finsets), so contraction and permutation
will be explicit structural rules rather than being built in.
-/

/-! ## Modalities -/

inductive Modality : Type where
  | box : Modality
  | dia : Modality
  deriving DecidableEq


/-! ## Signature -/

structure Signature where
  FuncSyms : Type
  RelSyms  : Type
  funcArity : FuncSyms → ℕ
  relArity  : RelSyms  → ℕ
  [decEqF  : DecidableEq FuncSyms]
  [decEqR  : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

/-! ## Variable Types -/

inductive VarType where
  | Var : VarType
  | VTypeBox : VarType → VarType
  | VTypeDia : VarType → VarType
  | VTypeOne : VarType
  | VTypeProd : VarType → VarType → VarType
  deriving DecidableEq

/-! ## Variable Symbols -/

inductive VarSymb : Type where
  | mk : ℕ → VarSymb
  deriving DecidableEq

/-! ## Variable Contexts (List-based) -/

abbrev PseudoVarCtx := List (VarSymb × VarType × List Modality)
abbrev VarCtx       := List (VarSymb × VarType)

def VarCtx_to_PVarCtx : VarCtx → PseudoVarCtx :=
  List.map fun ⟨v, S⟩ => ⟨v, S, []⟩

-- Apply one box to every variable's type in the context
def box_PseudoVarCtx : PseudoVarCtx → PseudoVarCtx :=
  List.map fun ⟨v, S, α⟩ => ⟨v, S.VTypeBox, α⟩

-- Diamond intro context: x gets ◇, everything else gets □
def dia_PseudoVarCtx (x : VarSymb × VarType × List Modality) (V : PseudoVarCtx) : PseudoVarCtx :=
  ⟨x.1, x.2.1.VTypeDia, x.2.2⟩ :: box_PseudoVarCtx V

-- Swap the elements at positions n and n+1 in a list.
-- Applying it twice is the identity, so it is its own inverse (and injective).
-- Commutes with List.map: map f (swapAdj n l) = swapAdj n (map f l).
def swapAdj {α : Type} : Nat → List α → List α
  | _,          []            => []
  | _,          [x]           => [x]
  | Nat.zero,   x :: y :: rest => y :: x :: rest
  | Nat.succ n, x :: y :: rest => x :: swapAdj n (y :: rest)


/-! ## PseudoTerms -/

inductive PseudoTerm (σ : Signature) : PseudoVarCtx → VarType → List Modality → Type where
  | var      : {v : VarSymb // ⟨v, .Var, α⟩ ∈ V} → PseudoTerm σ V .Var α
  | func     : (f : σ.FuncSyms) → (Fin (σ.funcArity f) → PseudoTerm σ V .Var α) →
               PseudoTerm σ V .Var α
  -- Modal intro rules: box/dia act as functors, mapping (V, S) to (□V, □S) / (◇V, ◇S).
  | boxterm  : PseudoTerm σ V S α → PseudoTerm σ (box_PseudoVarCtx V) S.VTypeBox α
  | diaterm  : PseudoTerm σ (x :: V) S α → PseudoTerm σ (dia_PseudoVarCtx x V) S.VTypeDia α
  -- Modal coercions
  | boxup    : PseudoTerm σ V (.VTypeBox S) α → PseudoTerm σ V S (.box :: α)
  | boxdown  : PseudoTerm σ V S (.box :: α)  → PseudoTerm σ V (.VTypeBox S) α
  | diaup    : PseudoTerm σ V (.VTypeDia S) α → PseudoTerm σ V S (.dia :: α)
  | diadown  : PseudoTerm σ V S (.dia :: α)   → PseudoTerm σ V (.VTypeDia S) α
  -- Unit
  | unit     : PseudoTerm σ V .VTypeOne α
  -- Products (natural deduction style)
  | pair      : PseudoTerm σ V S α → PseudoTerm σ V T α → PseudoTerm σ V (.VTypeProd S T) α
  -- Left rule / recursor: split z : S×T into components v₁ : S and v₂ : T.
  -- z must be fresh in V (not already present as a product entry).
  | pair_elim : (v₁ v₂ : VarSymb × VarType) → (z : VarSymb) → (β : List Modality) →
                ⟨z, .VTypeProd v₁.2 v₂.2, β⟩ ∉ V →
                PseudoTerm σ (⟨v₁.1, v₁.2, β⟩ :: ⟨v₂.1, v₂.2, β⟩ :: V) S α →
                PseudoTerm σ (⟨z, .VTypeProd v₁.2 v₂.2, β⟩ :: V) S α
  -- Structural rules (explicit, since contexts are lists not finsets)
  | wk       : (v : VarSymb × VarType × List Modality) →
               PseudoTerm σ V S α → PseudoTerm σ (v :: V) S α
  | exch     : (n : ℕ) → PseudoTerm σ V S α → PseudoTerm σ (swapAdj n V) S α

/-! ## Injectivity lemmas (needed for DecidableEq of boxterm/diaterm/exch) -/

private lemma VTypeBox_inj : Function.Injective VarType.VTypeBox
  | _, _, rfl => rfl

private lemma VTypeDia_inj : Function.Injective VarType.VTypeDia
  | _, _, rfl => rfl

private lemma box_PseudoVarCtx_inj : Function.Injective box_PseudoVarCtx := by
  intro V W h
  induction V generalizing W with
  | nil => cases W <;> simp_all [box_PseudoVarCtx]
  | cons a V ih =>
    cases W with
    | nil => simp [box_PseudoVarCtx] at h
    | cons b W =>
      simp only [box_PseudoVarCtx, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hv, hST, hα⟩, hVW⟩ := h
      exact congr_arg₂ List.cons
        (Prod.ext hv (Prod.ext (VTypeBox_inj hST) hα))
        (ih hVW)

/-! ## Genuine DecidableEq for PseudoTerm -/

private def PseudoTerm.decEq' {σ : Signature} :
    {V : PseudoVarCtx} → {S : VarType} → {α : List Modality} →
    (a b : PseudoTerm σ V S α) → Decidable (a = b)
  | _, _, _, .var v, .var w =>
      if h : v = w then isTrue (congrArg PseudoTerm.var h)
      else isFalse fun heq => h (by cases heq; rfl)
  | _, _, _, .func f k, .func g l =>
      if hf : f = g then by
        subst hf
        haveI : DecidablePred (fun i => k i = l i) := fun i => PseudoTerm.decEq' (k i) (l i)
        exact if hkl : ∀ i, k i = l i
              then isTrue (congrArg (PseudoTerm.func f) (funext hkl))
              else isFalse fun heq => hkl (fun i => by cases heq; rfl)
      else isFalse fun heq => hf (by cases heq; rfl)
  | _, _, _, .unit, .unit => isTrue rfl
  | _, _, _, .pair s₁ t₁, .pair s₂ t₂ =>
      match PseudoTerm.decEq' s₁ s₂, PseudoTerm.decEq' t₁ t₂ with
      | isTrue hs,  isTrue ht  => isTrue (by rw [hs, ht])
      | isFalse h,  _          => isFalse fun heq => h (by cases heq; rfl)
      | _,          isFalse h  => isFalse fun heq => h (by cases heq; rfl)
  | _, _, _, .boxup t₁, .boxup t₂ =>
      match PseudoTerm.decEq' t₁ t₂ with
      | isTrue h  => isTrue (congrArg PseudoTerm.boxup h)
      | isFalse h => isFalse fun heq => h (by cases heq; rfl)
  | _, _, _, .boxdown t₁, .boxdown t₂ =>
      match PseudoTerm.decEq' t₁ t₂ with
      | isTrue h  => isTrue (congrArg PseudoTerm.boxdown h)
      | isFalse h => isFalse fun heq => h (by cases heq; rfl)
  | _, _, _, .diaup t₁, .diaup t₂ =>
      match PseudoTerm.decEq' t₁ t₂ with
      | isTrue h  => isTrue (congrArg PseudoTerm.diaup h)
      | isFalse h => isFalse fun heq => h (by cases heq; rfl)
  | _, _, _, .diadown t₁, .diadown t₂ =>
      match PseudoTerm.decEq' t₁ t₂ with
      | isTrue h  => isTrue (congrArg PseudoTerm.diadown h)
      | isFalse h => isFalse fun heq => h (by cases heq; rfl)
  | _, _, _, .wk v t₁, .wk _ t₂ =>
      match PseudoTerm.decEq' t₁ t₂ with
      | isTrue h  => isTrue (congrArg (PseudoTerm.wk v) h)
      | isFalse h => isFalse fun heq => h (by cases heq; rfl)
  -- wk fixes V = v :: V₀; if b is boxterm/diaterm/exch the catch-all would need to
  -- solve v :: V₀ = box_PseudoVarCtx/swapAdj/dia_PseudoVarCtx which are not constructors.
  | _, _, _, .wk _ _, _ => sorry
  -- Single-sided: a has a non-constructor index transform; b is anything.
  -- Two-sided simultaneous match fails because box_PseudoVarCtx/swapAdj are not constructors.
  | _, _, _, .boxterm _,             _ => sorry
  | _, _, _, .diaterm _,             _ => sorry
  | _, _, _, .pair_elim _ _ _ _ _ _, _ => sorry
  | _, _, _, .exch _ _,              _ => sorry
  -- Mirror: b has the hard constructor; a's index is unconstrained so unification succeeds.
  | _, _, _, _, .boxterm _             => sorry
  | _, _, _, _, .diaterm _             => sorry
  | _, _, _, _, .pair_elim _ _ _ _ _ _ => sorry
  | _, _, _, _, .exch _ _              => sorry
  -- Remaining: cross-constructor pairs with only constructor-based indices → noConfusion works.
  | _, _, _, _, _                      => isFalse (by rintro ⟨⟩)

instance {σ : Signature} {V : PseudoVarCtx} {S : VarType} {α : List Modality} :
    DecidableEq (PseudoTerm σ V S α) := PseudoTerm.decEq'

abbrev Term (σ : Signature) (V : VarCtx) (S : VarType) : Type :=
  PseudoTerm σ (VarCtx_to_PVarCtx V) S []


/-
  ============================================================================
  OLD CODE (from QML_Full.lean – needs porting to the new List-based design)
  Key differences from the new v2 design:
    · VarSymb constructor was `.V n`, now `.mk n`
    · PseudoVarCtx was `VarType → List Modality → Finset VarSymb` (function),
      now `List (VarSymb × VarType × List Modality)`
    · PseudoVarCtxExt, PseudoVarCtx_merge etc. need replacing with list ops
    · Func mutual inductive removed; use `Fin (σ.funcArity f) → PseudoTerm`
    · Context restriction / extension need rewriting for list-based ctx
  ============================================================================

/-! ## Term Notation -/

postfix:100 "□⁺" => PseudoTerm.boxup
postfix:100 "□⁻" => PseudoTerm.boxdown
postfix:100 "◇⁺" => PseudoTerm.diaup
postfix:100 "◇⁻" => PseudoTerm.diadown

/-! ## Term Conversion -/

-- `PseudoTerm.Conv s t` is the least congruence on terms containing the β/η rules
-- for products, the unit type, and the modal coercions.
inductive PseudoTerm.Conv {σ : Signature} {V : PseudoVarCtx} :
    PseudoTerm σ V S α → PseudoTerm σ V S α → Prop where
  -- β-rules for products
  | fst_β    : Conv (.fst (.pair s t)) s
  | snd_β    : Conv (.snd (.pair s t)) t
  -- η-rules
  | prod_η   : Conv p (.pair (.fst p) (.snd p))
  | unit_η   : Conv t .unit
  -- Modal roundtrips
  | box_β₁   : Conv (.boxdown (.boxup t)) t
  | box_β₂   : Conv (.boxup (.boxdown t)) t
  | dia_β₁   : Conv (.diadown (.diaup t)) t
  | dia_β₂   : Conv (.diaup (.diadown t)) t
  -- Congruence under product constructors
  | pair_l      : Conv s s' → Conv (.pair s t) (.pair s' t)
  | pair_r      : Conv t t' → Conv (.pair s t) (.pair s  t')
  | fst_cong    : Conv p p' → Conv (.fst p) (.fst p')
  | snd_cong    : Conv p p' → Conv (.snd p) (.snd p')
  -- Congruence under modal constructors
  | boxup_cong   : Conv t t' → Conv (.boxup t)   (.boxup t')
  | boxdown_cong : Conv t t' → Conv (.boxdown t) (.boxdown t')
  | diaup_cong   : Conv t t' → Conv (.diaup t)   (.diaup t')
  | diadown_cong : Conv t t' → Conv (.diadown t) (.diadown t')
  -- Equivalence closure
  | refl  : Conv t t
  | symm  : Conv s t → Conv t s
  | trans : Conv s t → Conv t u → Conv s u

/-! ## Relation Symbols -/

-- `RelSymb σ V n` is an n-ary relation symbol, possibly partially applied to terms over V.
-- Arity is enforced at construction: `R ⟨r, h⟩` requires a proof `h : σ.relArity r = n`.
inductive RelSymb (σ : Signature) (V : PseudoVarCtx) (α : List Modality) : ℕ → Type where
  | R    : {r : σ.RelSyms // σ.relArity r = n} → RelSymb σ V α n
  | eval : RelSymb σ V α (Nat.succ n) → PseudoTerm σ V .Var α → RelSymb σ V α n
  deriving DecidableEq

-- Two relation symbols are convertible if corresponding term arguments are convertible.
inductive RelSymb.Conv : RelSymb σ V α n → RelSymb σ V α n → Prop where
  | eval  : RelSymb.Conv p q → PseudoTerm.Conv t s → RelSymb.Conv (.eval p t) (.eval q s)
  | refl  : RelSymb.Conv p p
  | symm  : RelSymb.Conv p q → RelSymb.Conv q p
  | trans : RelSymb.Conv p q → RelSymb.Conv q r → RelSymb.Conv p r

-- Variables of sort S can be coerced to terms of sort S.
instance : Coe {v : VarSymb // ⟨v, .Var, α⟩ ∈ V} (PseudoTerm σ V .Var α) where coe := PseudoTerm.var

/-! ## Substitution -/

-- Needs rewriting: old version used Finset-based membership proofs.
-- New version should use List membership (∈ V) proofs.

/-! ## Well-Formed Formulas -/

-- `WFF σ V` is the type of formulas over signature σ whose free variables lie in V.
-- Quantifiers extend the context: `all x φ` binds x.
-- NOTE: PseudoVarCtxExt needs replacement with list cons/wk.
inductive PseudoWFF (σ : Signature) : PseudoVarCtx → (List Modality) → Type where
  | atom : RelSymb σ V α 0 → PseudoWFF σ V α
  | top  : PseudoWFF σ V α
  | bot  : PseudoWFF σ V α
  | and  : PseudoWFF σ V α → PseudoWFF σ V α → PseudoWFF σ V α
  | or   : PseudoWFF σ V α → PseudoWFF σ V α → PseudoWFF σ V α
  | imp  : PseudoWFF σ V α → PseudoWFF σ V α → PseudoWFF σ V α
  | all  : (x : VarSymb × VarType) → PseudoWFF σ (⟨x.1, x.2, α⟩ :: V) α
                    → PseudoWFF σ V α
  | ex   : (x : VarSymb × VarType) → PseudoWFF σ (⟨x.1, x.2, α⟩ :: V) α
                    → PseudoWFF σ V α
  | eq   : PseudoTerm σ V S α → PseudoTerm σ V S α → PseudoWFF σ V α
  | box : PseudoWFF σ V (.box :: α) → PseudoWFF σ V α
  | dia : PseudoWFF σ V (.dia :: α) → PseudoWFF σ V α
  deriving DecidableEq

abbrev WFF (σ : Signature) (V : VarCtx) : Type
  := PseudoWFF σ (VarCtx_to_PVarCtx V) []

namespace PseudoWFF

variable {σ : Signature}

def neg (φ : PseudoWFF σ V α) : PseudoWFF σ V α := imp φ bot

/-! ## Notation -/

infixr:35  " →ₘ "  => PseudoWFF.imp
infixl:65  " ∧ₘ "  => PseudoWFF.and
infixl:60  " ∨ₘ "  => PseudoWFF.or
prefix:75  "¬ₘ "   => PseudoWFF.neg
notation   "⊤ₘ"    => PseudoWFF.top
notation   "⊥ₘ"    => PseudoWFF.bot
notation   "∀ₘ"    => PseudoWFF.all
notation   "∃ₘ"    => PseudoWFF.ex
prefix:80  "□ₘ "   => PseudoWFF.box
prefix:80  "◇ₘ "   => PseudoWFF.dia

/-! ## Formula Conversion -/

-- `Conv φ ψ` is the least congruence on formulas that lifts `PseudoTerm.Conv`.
inductive Conv {σ : Signature} :
    {V : PseudoVarCtx} → PseudoWFF σ V α → PseudoWFF σ V α → Prop where
  | atom  : RelSymb.Conv p q → Conv (.atom p) (.atom q)
  | and_l : Conv φ φ' → Conv (.and φ ψ) (.and φ' ψ)
  | and_r : Conv ψ ψ' → Conv (.and φ ψ) (.and φ  ψ')
  | or_l  : Conv φ φ' → Conv (.or  φ ψ) (.or  φ' ψ)
  | or_r  : Conv ψ ψ' → Conv (.or  φ ψ) (.or  φ  ψ')
  | imp_l : Conv φ φ' → Conv (.imp φ ψ) (.imp φ' ψ)
  | imp_r : Conv ψ ψ' → Conv (.imp φ ψ) (.imp φ  ψ')
  | eq_l  : PseudoTerm.Conv s s' → Conv (.eq s t) (.eq s' t)
  | eq_r  : PseudoTerm.Conv t t' → Conv (.eq s t) (.eq s  t')
  | all   : Conv (V := ⟨x.1, x.2, α⟩ :: V) φ ψ → Conv (.all x φ) (.all x ψ)
  | ex    : Conv (V := ⟨x.1, x.2, α⟩ :: V) φ ψ → Conv (.ex  x φ) (.ex  x ψ)
  | box   : Conv φ ψ → Conv (.box φ) (.box ψ)
  | dia   : Conv φ ψ → Conv (.dia φ) (.dia ψ)
  | refl  : Conv φ φ
  | symm  : Conv φ ψ → Conv ψ φ
  | trans : Conv φ ψ → Conv ψ χ → Conv φ χ

/-! ## Well-Scopedness -/

-- A formula is Scoped if every bound variable x in a quantifier ∀x/∃x is
-- fresh: ⟨x.1, x.2, α⟩ ∉ V at the point of binding.
def Scoped : PseudoWFF σ V α → Prop
  | .atom _ | .top | .bot         => True
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.Scoped ∧ ψ.Scoped
  | .all x φ                      => ⟨x.1, x.2, α⟩ ∉ V ∧ φ.Scoped
  | .ex  x φ                      => ⟨x.1, x.2, α⟩ ∉ V ∧ φ.Scoped
  | .eq _ _                       => True
  | .box φ | .dia φ               => φ.Scoped

-- The set of variables bound by quantifiers in a formula.
-- NOTE: needs rewriting for List-based ctx (return a List or Prop)
-- def boundVars : PseudoWFF σ V α → PseudoVarCtx := ...

/-! ## Context Extension / Restriction -/

-- These need complete rewriting for List-based contexts.
-- Old Finset-based versions below for reference only.

-- def ctx_ext_term (v : VarSymb × List Modality × VarType) (t : PseudoTerm σ V S α)
--     : PseudoTerm σ (⟨v.1, v.2.2, v.2.1⟩ :: V) S α := ...

-- def ctx_rest_PseudoWFF ... (needs Scoped, wffDepth termination measure)

/-! ## Formula Substitution -/

-- `φ.subst a b` replaces occurrences of term `b` with term `a` in `φ`.
-- NOTE: needs rewriting; old version used PseudoVarCtxExt.
-- def subst (a b : PseudoTerm σ V S α) : PseudoWFF σ V β → PseudoWFF σ V β := ...

/-! ## Context Restriction -/

-- wffDepth is a size measure transparent to type-level casts.
def wffDepth : PseudoWFF σ V α → ℕ
  | .atom _  => 0
  | .top     => 0
  | .bot     => 0
  | .and φ ψ => wffDepth φ + wffDepth ψ + 1
  | .or  φ ψ => wffDepth φ + wffDepth ψ + 1
  | .imp φ ψ => wffDepth φ + wffDepth ψ + 1
  | .all _ φ => wffDepth φ + 1
  | .ex  _ φ => wffDepth φ + 1
  | .eq  _ _ => 0
  | .box φ   => wffDepth φ + 1
  | .dia φ   => wffDepth φ + 1

lemma wffDepth_cast {V W : PseudoVarCtx} (h : V = W) (φ : PseudoWFF σ V α) :
    wffDepth (h ▸ φ) = wffDepth φ := by subst h; rfl

lemma Scoped_cast {V W : PseudoVarCtx} (h : V = W) (φ : PseudoWFF σ V α) :
    PseudoWFF.Scoped (h ▸ φ) = PseudoWFF.Scoped φ := by subst h; rfl

/-! ## Box context transform -/

-- Old definition used function-based PseudoVarCtx; new uses List.map.
-- The new box_PseudoVarCtx is already defined above (in the v2 section).

-- Box lift for formulas – needs rewriting to use new box_PseudoVarCtx.
-- def box_PseudoWFF (φ : PseudoWFF σ V α) : PseudoWFF σ (box_PseudoVarCtx V) (α ++ [.box]) := ...

/-! ## Proof System -/

-- `Proof σ V Γ φ`: a natural deduction proof of φ from hypotheses Γ.
-- NOTE: the context V is now List-based; structural rules wk/exch are in PseudoTerm,
-- but for formulas we still need explicit context management.
-- The K_box rule should use box_PseudoVarCtx (List.map version).

-- inductive Proof (σ : Signature) :
--     (V : PseudoVarCtx) → List (PseudoWFF σ V []) → PseudoWFF σ V [] → Type where
--   | ax        : φ ∈ Γ → φ.Scoped → Proof σ V Γ φ
--   | weak      : ψ.Scoped → Proof σ V Γ φ → Proof σ V (ψ :: Γ) φ
--   | exch      : Proof σ V (φ :: ψ :: Γ) χ → Proof σ V (ψ :: φ :: Γ) χ
--   | weak_ctx  : (v : VarSymb × VarType) → ⟨v.1, v.2, []⟩ ∉ V
--                 → Proof σ V Γ φ
--                 → Proof σ (⟨v.1, v.2, []⟩ :: V) (Γ.map (ctx_ext_WFF v)) (ctx_ext_WFF v φ)
--   | conv      : Conv φ ψ → Proof σ V Γ φ → Proof σ V Γ ψ
--   | and_intro : Proof σ V Γ φ → Proof σ V Γ ψ → Proof σ V Γ (φ ∧ₘ ψ)
--   | and_elim_l: Proof σ V Γ (φ ∧ₘ ψ) → Proof σ V Γ φ
--   | and_elim_r: Proof σ V Γ (φ ∧ₘ ψ) → Proof σ V Γ ψ
--   | or_intro_l: ψ.Scoped → Proof σ V Γ φ → Proof σ V Γ (φ ∨ₘ ψ)
--   | or_intro_r: φ.Scoped → Proof σ V Γ ψ → Proof σ V Γ (φ ∨ₘ ψ)
--   | or_elim   : Proof σ V Γ (φ ∨ₘ ψ) → Proof σ V (φ :: Γ) χ → Proof σ V (ψ :: Γ) χ
--                 → Proof σ V Γ χ
--   | imp_intro : φ.Scoped → Proof σ V (φ :: Γ) ψ → Proof σ V Γ (φ →ₘ ψ)
--   | imp_elim  : Proof σ V Γ (φ →ₘ ψ) → Proof σ V Γ φ → Proof σ V Γ ψ
--   | top_intro : Proof σ V Γ ⊤ₘ
--   | bot_elim  : φ.Scoped → Proof σ V Γ ⊥ₘ → Proof σ V Γ φ
--   | lem       : φ.Scoped → Proof σ V Γ (φ ∨ₘ (¬ₘ φ))
--   | eq_intro  : (t : PseudoTerm σ V S []) → Proof σ V Γ (.eq t t)
--   | eq_elim   : Proof σ V Γ (.eq t s) → Proof σ V Γ φ → Proof σ V Γ (subst s t φ)
--   | all_intro : (x : VarSymb × VarType) → ⟨x.1, x.2, []⟩ ∉ V
--                 → {φ : PseudoWFF σ (⟨x.1, x.2, []⟩ :: V) []}
--                 → Proof σ (⟨x.1, x.2, []⟩ :: V) (Γ.map (ctx_ext_WFF x)) φ
--                 → Proof σ V Γ (.all x φ)
--   | all_elim  : (x : VarSymb × VarType)
--                 → {φ : PseudoWFF σ (⟨x.1, x.2, []⟩ :: V) []}
--                 → (t : PseudoTerm σ V x.2 [])
--                 → Proof σ V Γ (.all x φ)
--                 → Proof σ (⟨x.1, x.2, []⟩ :: V) (Γ.map (ctx_ext_WFF x))
--                     (subst (ctx_ext_term x t) (.var ⟨x.1, List.mem_cons_self _ _⟩) φ)
--   | ex_intro  : (x : VarSymb × VarType) → ⟨x.1, x.2, []⟩ ∉ V
--                 → {φ : PseudoWFF σ (⟨x.1, x.2, []⟩ :: V) []}
--                 → (t : PseudoTerm σ V x.2 [])
--                 → Proof σ (⟨x.1, x.2, []⟩ :: V) (Γ.map (ctx_ext_WFF x))
--                     (subst (ctx_ext_term x t) (.var ⟨x.1, List.mem_cons_self _ _⟩) φ)
--                 → Proof σ V Γ (.ex x φ)
--   | ex_elim   : (x : VarSymb × VarType) → ⟨x.1, x.2, []⟩ ∉ V
--                 → {φ : PseudoWFF σ (⟨x.1, x.2, []⟩ :: V) []}
--                 → Proof σ V Γ (.ex x φ)
--                 → Proof σ (⟨x.1, x.2, []⟩ :: V) (Γ.map (ctx_ext_WFF x) ++ [φ]) (ctx_ext_WFF x ψ)
--                 → Proof σ V Γ ψ
--   | K_box     : Proof σ V Γ φ
--                 → Proof σ (box_PseudoVarCtx V)
--                     (Γ.map (.box ∘ box_PseudoWFF)) (.box (box_PseudoWFF φ))

-- Turnstile notation: σ , V ; Γ ⊢ₘ φ
-- notation:30 σ " , " V " ; " Γ " ⊢ₘ " φ => Proof σ V Γ φ

end PseudoWFF
-/
