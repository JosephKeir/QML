import Mathlib

/-!
# Quantified Modal Logic: Natural Deduction (v3)

Redesign from v2. Key changes:

  · The `List Modality` index α is dropped from terms and formulas entirely.
    It was only ever manipulated by boxup/boxdown/diaup/diadown, which are removed.
    The joint-possibility problem with diamond: if x and y are both `VTypeDia Var`,
    the old diaup/diadown let you combine them inside one diamond — but they may be
    possible in different worlds and are not jointly possible. diaterm prevents this
    by design (only one witness per application).

  · `PseudoVarCtx` collapses to a single `VarCtx = List (VarSymb × VarType)`.
    The old Term/PseudoTerm and WFF/PseudoWFF distinctions disappear.

  · Modal terms are formed exclusively via `boxterm` and `diaterm`:
        boxterm : Term σ V S           → Term σ (box_VarCtx V) (VTypeBox S)
        diaterm : Term σ (x :: V) S    → Term σ (dia_VarCtx x V) (VTypeDia S)
    `diaterm` enforces joint possibility: the body uses x with its plain type plus
    V normally; only after wrapping does x become VTypeDia and V become all-boxed.
    Two diamond witnesses require two nested diatems (◇◇, not one ◇ with two objects).

  · WFFs use context-transforming constructors mirroring boxterm/diaterm:
        box : WFF σ (box_VarCtx V)                    → WFF σ V
        dia : (x : VarSymb × VarType)
              → WFF σ (⟨x.1, x.2⟩ :: box_VarCtx V)  → WFF σ V
    `dia` always carries an explicit witness variable x. Use `x.2 = VTypeOne` for
    the purely propositional case: VTypeOne has a unique element (up to the unit
    η-rule), so ◇(∃x:1.φ) is equivalent to ◇φ. This also gives all finite products
    (VTypeOne = nullary, VTypeProd = binary) with no special-casing.

  · `RelSymb.eval` carries the VarType of its term argument explicitly, so
    predicates can be applied to modal objects (VTypeBox, VTypeDia, …) inside
    box/dia formulas without any coercion. Function symbols still operate on
    base `.Var` objects; modal lifting of function terms is done via `boxterm`/
    `diaterm` before applying predicates.
-/

/-! ## Modalities (kept for documentation; not used in core v3 definitions) -/

inductive Modality : Type where
  | box : Modality
  | dia : Modality
  deriving DecidableEq

/-! ## Signature -/

structure Signature where
  FuncSyms  : Type
  RelSyms   : Type
  funcArity : FuncSyms → ℕ
  relArity  : RelSyms  → ℕ
  [decEqF   : DecidableEq FuncSyms]
  [decEqR   : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

/-! ## Variable Types -/

inductive VarType where
  | Var     : VarType
  | VTypeBox  : VarType → VarType
  | VTypeDia  : VarType → VarType
  | VTypeOne  : VarType                      -- nullary product / trivial dia witness
  | VTypeProd : VarType → VarType → VarType  -- binary product
  deriving DecidableEq

/-! ## Variable Symbols -/

inductive VarSymb : Type where
  | mk : ℕ → VarSymb
  deriving DecidableEq

/-! ## Variable Contexts -/

abbrev VarCtx := List (VarSymb × VarType)

-- Wrap every variable's type in VTypeBox
def box_VarCtx : VarCtx → VarCtx :=
  List.map fun ⟨v, S⟩ => ⟨v, S.VTypeBox⟩

-- One designated witness gets VTypeDia; everything else gets VTypeBox
def dia_VarCtx (x : VarSymb × VarType) (V : VarCtx) : VarCtx :=
  ⟨x.1, x.2.VTypeDia⟩ :: box_VarCtx V

-- Swap elements at positions n and n+1 (used by the exch structural rule)
def swapAdj {α : Type} : Nat → List α → List α
  | _,          []             => []
  | _,          [a]            => [a]
  | Nat.zero,   a :: b :: rest => b :: a :: rest
  | Nat.succ n, a :: b :: rest => a :: swapAdj n (b :: rest)

/-! ## Terms -/

-- `Term σ V S`: a term of VarType S with free variables drawn from VarCtx V.
-- The `var` rule is general (any VarType S), since variables can be declared
-- with any type including VTypeBox and VTypeDia.
-- Function symbols operate only on base `.Var` objects; modal objects are
-- introduced by `boxterm`/`diaterm` and used via the polymorphic RelSymb.eval.
inductive Term (σ : Signature) : VarCtx → VarType → Type where
  | var       : {v : VarSymb // ⟨v, S⟩ ∈ V} → Term σ V S
  | func      : (f : σ.FuncSyms) → (Fin (σ.funcArity f) → Term σ V .Var) →
                Term σ V .Var
  | boxterm   : Term σ V S → Term σ (box_VarCtx V) S.VTypeBox
  | diaterm   : Term σ (x :: V) S → Term σ (dia_VarCtx x V) S.VTypeDia
  | unit      : Term σ V .VTypeOne
  | pair      : Term σ V S → Term σ V T → Term σ V (.VTypeProd S T)
  | pair_elim : (v₁ v₂ : VarSymb × VarType) → (z : VarSymb) →
                ⟨z, .VTypeProd v₁.2 v₂.2⟩ ∉ V →
                Term σ (⟨v₁.1, v₁.2⟩ :: ⟨v₂.1, v₂.2⟩ :: V) S →
                Term σ (⟨z, .VTypeProd v₁.2 v₂.2⟩ :: V) S
  | wk        : (v : VarSymb × VarType) → Term σ V S → Term σ (v :: V) S
  | exch      : (n : ℕ) → Term σ V S → Term σ (swapAdj n V) S

/-! ## Injectivity lemmas -/

private lemma VTypeBox_inj : Function.Injective VarType.VTypeBox
  | _, _, rfl => rfl

private lemma VTypeDia_inj : Function.Injective VarType.VTypeDia
  | _, _, rfl => rfl

private lemma box_VarCtx_inj : Function.Injective box_VarCtx := by
  intro V W h
  induction V generalizing W with
  | nil => cases W <;> simp_all [box_VarCtx]
  | cons a V ih =>
    cases W with
    | nil => simp [box_VarCtx] at h
    | cons b W =>
      simp only [box_VarCtx, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hv, hST⟩, hVW⟩ := h
      exact congr_arg₂ List.cons (Prod.ext hv (VTypeBox_inj hST)) (ih hVW)

private lemma dia_VarCtx_inj {x y : VarSymb × VarType} {V W : VarCtx}
    (h : dia_VarCtx x V = dia_VarCtx y W) : x = y ∧ V = W := by
  simp only [dia_VarCtx, List.cons.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨hv, hS⟩, hVW⟩ := h
  exact ⟨Prod.ext hv (VTypeDia_inj hS), box_VarCtx_inj hVW⟩

-- Lets us unfold swapAdj (n+1) (a :: l) without needing to know the shape of l.
private lemma swapAdj_succ_apply {α : Type} (n : ℕ) (a : α) (l : List α) :
    swapAdj (n + 1) (a :: l) = a :: swapAdj n l := by
  cases l with
  | nil      => simp [swapAdj]
  | cons _ _ => rfl

private lemma swapAdj_invol {α : Type} (n : ℕ) (l : List α) :
    swapAdj n (swapAdj n l) = l := by
  induction l generalizing n with
  | nil      => simp [swapAdj]
  | cons a t ih =>
    cases t with
    | nil      => simp [swapAdj]
    | cons b rest =>
      cases n with
      | zero   => rfl
      | succ n =>
        rw [show swapAdj (n + 1) (a :: b :: rest) = a :: swapAdj n (b :: rest) from rfl,
            swapAdj_succ_apply, ih]

private lemma swapAdj_inj {α : Type} (n : ℕ) :
    Function.Injective (swapAdj (α := α) n) := fun _ _ h => by
  have := congrArg (swapAdj n) h
  rwa [swapAdj_invol, swapAdj_invol] at this

/-! ## DecidableEq for Term -/

-- Constructor tag: maps each constructor to a distinct Fin 9 value.
-- Since Fin 9 has no dependency on V or S, this is accepted by Lean for GADTs.
-- Used to dispatch all cross-constructor cases without noConfusion elaboration issues.
private def Term.ctorTag {σ : Signature} {V : VarCtx} {S : VarType} : Term σ V S → Fin 9
  | .var _               => 0
  | .func _ _            => 1
  | .boxterm _           => 2
  | .diaterm _           => 3
  | .unit                => 4
  | .pair _ _            => 5
  | .pair_elim _ _ _ _ _ => 6
  | .wk _ _              => 7
  | .exch _ _            => 8

-- Extracts the index from exch; used to distinguish exch n from exch m when n ≠ m.
private def Term.exchIdx {σ : Signature} {V : VarCtx} {S : VarType} : Term σ V S → ℕ
  | .exch n _ => n
  | _         => 0

private def Term.decEq' {σ : Signature} :
    {V : VarCtx} → {S : VarType} → (a b : Term σ V S) → Decidable (a = b)
  -- ── same-constructor cases ──────────────────────────────────────────────
  | _, _, .var v, .var w =>
      if h : v = w then isTrue (congrArg Term.var h)
      else isFalse fun heq => h (by cases heq; rfl)
  | _, _, .func f k, .func g l =>
      if hf : f = g then by
        subst hf
        haveI : DecidablePred (fun i => k i = l i) := fun i => Term.decEq' (k i) (l i)
        exact if hkl : ∀ i, k i = l i
              then isTrue (congrArg (Term.func f) (funext hkl))
              else isFalse fun heq => hkl (fun i => by cases heq; rfl)
      else isFalse fun heq => hf (by cases heq; rfl)
  | _, _, .unit, .unit => isTrue rfl
  | _, _, .pair s₁ t₁, .pair s₂ t₂ =>
      match Term.decEq' s₁ s₂, Term.decEq' t₁ t₂ with
      | isTrue hs,  isTrue ht  => isTrue (by rw [hs, ht])
      | isFalse h,  _          => isFalse fun heq => h (by cases heq; rfl)
      | _,          isFalse h  => isFalse fun heq => h (by cases heq; rfl)
  | _, _, .wk v t₁, .wk _ t₂ =>
      match Term.decEq' t₁ t₂ with
      | isTrue h  => isTrue (congrArg (Term.wk v) h)
      | isFalse h => isFalse fun heq => h (by cases heq; rfl)
  | _, _, .boxterm t₁, .boxterm t₂ =>
      match Term.decEq' t₁ t₂ with
      | isTrue h  => isTrue (congrArg Term.boxterm h)
      | isFalse h => isFalse fun heq => h (by cases heq; rfl)
  | _, _, .diaterm t₁, .diaterm t₂ =>
      match Term.decEq' t₁ t₂ with
      | isTrue h  => isTrue (congrArg Term.diaterm h)
      | isFalse h => isFalse fun heq => h (by cases heq; rfl)
  | _, _, .pair_elim _ _ _ _ _, .pair_elim _ _ _ _ _ => sorry
  -- ── cross-constructor cases: closed by ctorTag ──────────────────────────
  -- Each pattern has a known LHS constructor matched against a known RHS
  -- constructor, so `by decide` evaluates the Fin 9 inequality and closes the goal.
  -- wk: only match plain-context constructors on the right; the rest fall to catch-all
  -- (box/dia/pair_elim on the right fail to elaborate because Lean can't unify
  --  v :: V with box_VarCtx/dia_VarCtx/swapAdj expressions at pattern-match time)
  | _, _, .wk _ _,              .var _              => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  | _, _, .wk _ _,              .func _ _           => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  | _, _, .wk _ _,              .unit               => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  | _, _, .wk _ _,              .pair _ _           => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  -- boxterm (S = VTypeBox _, V = box_VarCtx _): box_VarCtx is an opaque def so only `var`
  -- (whose V is a free index) can be unified on the right; all others fall to catch-all.
  | _, _, .boxterm _,           .var _              => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  -- Remaining boxterm cross-cases (wk/exch/pair_elim can't be stated explicitly due to
  -- V-index unification; boxterm-same-constructor is already handled above).
  | _, _, .boxterm _,           _                  => sorry
  -- diaterm (S = VTypeDia _, V = dia_VarCtx x _ = ⟨x.1,VTypeDia x.2⟩::box_VarCtx _):
  -- var works (free index); wk (v::V') unifies with the cons head; exch (swapAdj) and
  -- pair_elim (VTypeProd head) cannot unify → fall to catch-all.
  | _, _, .diaterm _,           .var _              => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  | _, _, .diaterm _,           .wk _ _             => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  -- pair_elim (V = ⟨z,VTypeProd …⟩::V_rest, S arbitrary): var/func/unit/pair work (free or
  -- matching S, V cons-unifies); wk (v::V') unifies with the cons; boxterm (box_VarCtx) and
  -- exch (swapAdj) are opaque defs that can't unify with a concrete cons → fall to catch-all.
  | _, _, .pair_elim _ _ _ _ _, .var _              => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  | _, _, .pair_elim _ _ _ _ _, .func _ _           => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  | _, _, .pair_elim _ _ _ _ _, .unit               => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  | _, _, .pair_elim _ _ _ _ _, .pair _ _           => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  | _, _, .pair_elim _ _ _ _ _, .wk _ _             => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])
  -- exch: two-sided GADT matching fails (both sides introduce independent existential
  -- context variables); handle with one-sided patterns + sorry for now.
  -- TODO: exch vs exch same-constructor case needs swapAdj_inj to unify inner contexts.
  | _, _, .exch _ _,            _                   => sorry
  | _, _, _,                    .exch _ _           => sorry
  -- Remaining cross-constructor pairs: rintro ⟨⟩ fails for GADT equalities where
  -- box_VarCtx/dia_VarCtx appear as V-indices; use ctorTag to avoid dependent elimination.
  | _, _, _, _                                      => isFalse fun heq => absurd (congrArg Term.ctorTag heq) (by simp [Term.ctorTag])

instance {σ : Signature} {V : VarCtx} {S : VarType} : DecidableEq (Term σ V S) :=
  Term.decEq'

/-! ## Relation Symbols -/

-- `RelSymb σ V n`: an n-ary relation symbol, partially applied to terms over V.
-- The VarType S of each term argument is carried explicitly so that DecidableEq
-- can compare entries without heterogeneous equality.
inductive RelSymb (σ : Signature) (V : VarCtx) : ℕ → Type where
  | R    : {r : σ.RelSyms // σ.relArity r = n} → RelSymb σ V n
  | eval : RelSymb σ V (Nat.succ n) → (S : VarType) → Term σ V S → RelSymb σ V n
  deriving DecidableEq

/-! ## Well-Formed Formulas -/

-- `WFF σ V`: a formula whose free variables lie in V.
--
-- `box φ` : □φ.  φ lives in box_VarCtx V (all variables necessarily present).
-- `dia x φ`: ◇(∃x.φ).  φ lives in ⟨x.1, x.2⟩ :: box_VarCtx V — one fresh
--   witness x at its plain type, plus all V-variables boxed.
--   Use x.2 = VTypeOne for the propositional case (trivial witness).
inductive WFF (σ : Signature) : VarCtx → Type where
  | atom : RelSymb σ V 0 → WFF σ V
  | top  : WFF σ V
  | bot  : WFF σ V
  | and  : WFF σ V → WFF σ V → WFF σ V
  | or   : WFF σ V → WFF σ V → WFF σ V
  | imp  : WFF σ V → WFF σ V → WFF σ V
  | all  : (x : VarSymb × VarType) → WFF σ (⟨x.1, x.2⟩ :: V) → WFF σ V
  | ex   : (x : VarSymb × VarType) → WFF σ (⟨x.1, x.2⟩ :: V) → WFF σ V
  | eq   : Term σ V S → Term σ V S → WFF σ V
  | box  : WFF σ (box_VarCtx V) → WFF σ V
  | dia  : (x : VarSymb × VarType) → WFF σ (⟨x.1, x.2⟩ :: box_VarCtx V) → WFF σ V
  deriving DecidableEq

namespace WFF

variable {σ : Signature}

def neg (φ : WFF σ V) : WFF σ V := imp φ bot

/-! ## Notation -/

infixr:35 " →ₘ "  => WFF.imp
infixl:65 " ∧ₘ "  => WFF.and
infixl:60 " ∨ₘ "  => WFF.or
prefix:75 "¬ₘ "   => WFF.neg
notation  "⊤ₘ"    => WFF.top
notation  "⊥ₘ"    => WFF.bot
notation  "∀ₘ"    => WFF.all
notation  "∃ₘ"    => WFF.ex
prefix:80 "□ₘ "   => WFF.box
-- ◇ₘ takes an explicit witness: ◇ₘ x φ
notation  "◇ₘ"    => WFF.dia

/-! ## Well-Scopedness -/

-- A formula is Scoped if every quantifier and dia witness binds a variable that
-- is not already present in the relevant context at the point of binding.
def Scoped : WFF σ V → Prop
  | .atom _ | .top | .bot | .eq _ _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ   => φ.Scoped ∧ ψ.Scoped
  | .all x φ                        => ⟨x.1, x.2⟩ ∉ V ∧ φ.Scoped
  | .ex  x φ                        => ⟨x.1, x.2⟩ ∉ V ∧ φ.Scoped
  | .box φ                          => φ.Scoped
  -- x must be fresh in box_VarCtx V (the context it is prepended to)
  | .dia x φ                        => ⟨x.1, x.2⟩ ∉ box_VarCtx V ∧ φ.Scoped

/-! ## Formula Depth (termination measure) -/

def depth : WFF σ V → ℕ
  | .atom _ | .top | .bot | .eq _ _ => 0
  | .and φ ψ | .or φ ψ | .imp φ ψ   => φ.depth + ψ.depth + 1
  | .all _ φ | .ex _ φ              => φ.depth + 1
  | .box φ   | .dia _ φ             => φ.depth + 1

lemma depth_cast {V W : VarCtx} (h : V = W) (φ : WFF σ V) :
    depth (h ▸ φ) = depth φ := by subst h; rfl

lemma Scoped_cast {V W : VarCtx} (h : V = W) (φ : WFF σ V) :
    Scoped (h ▸ φ) = Scoped φ := by subst h; rfl

end WFF

/-!
## Still to port from v2 (commented-out old code for reference)

  · Term.Conv  (β/η conversion for products and unit)
  · RelSymb.Conv
  · WFF.Conv   (lifting Term.Conv to formulas)
  · Substitution (subst a b φ — replace term b by a in φ)
  · Context extension / restriction helpers
  · Proof system (natural deduction):
      - Classical propositional rules (ax, weak, exch, conv, and/or/imp/top/bot/lem)
      - Equality rules (eq_intro, eq_elim)
      - Quantifier rules (all_intro, all_elim, ex_intro, ex_elim)
      - Modal rules:
          K_box : Proof σ V Γ φ
                  → Proof σ (box_VarCtx V) (Γ.map (□ₘ ∘ box_lift)) (□ₘ (box_lift φ))
          K_dia : analogous rule for ◇ₘ, one witness at a time
-/
