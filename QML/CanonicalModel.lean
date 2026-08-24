import QML.QML_Full_v9
import QML.RModelB
import QML.SubstitutionLemmas9
import Mathlib.Order.Zorn

/-!
# The canonical (term / Henkin) model as an `RModel`

**Goal.** Instantiate `RModelB`'s `RModel` as the canonical model, to validate the redesign for
completeness (the one open design question: does `RModelB` actually instantiate as the *non-full,
denotable* term model?).  We stub the abstract proof-theory and focus on the *structure*.

**What we actually need (the pointed, environmented target).**  Completeness is used
contrapositively, so it suffices to build **ONE** model `M` together with **ONE** environment `η_w`
at each world such that, for a given consistent set of (possibly **open**) WFFs `Γ` in an initial
context, `M, η_{w₀} ⊨ Γ` at the actual world `w₀` — NOT a universal model of all theories.  The
environment is **tautological / forced**: each variable is sent to its own `≈`-class (the object that
"points at" the corresponding variable downstream), so `η` is not a free choice.  The Truth Lemma
then only has to hold for *this* `η`, over *this* `Γ` — not for all environments.

## The construction (per the intended plan)

Seed = a consistent set of open WFFs `Γ` in an initial context `V`.  **`Γ`, `V`, AND the resulting
MCS are all infinite** — even a finite seed maximalises to an infinite MCS (Lindenbaum) — so the
`Set`/`ICtx` (infinitary) layer is load-bearing throughout; we bridge to the finitary `Term`/`WFF`
machinery (which is `Finset`-indexed) via *finite subcontexts* (every formula/term uses only finitely
many variables, so it lives in some finite sub-`VarCtx`).

1. **Extra constants.**  We store extra constants in a tree indexed by **modal words** — words over
   the alphabet `{ box } ∪ { dia_x : x a variable }`.  A word is a path down the modal-accessibility
   tree (each `box`/`dia_x` step goes to an accessible world).  At each word we add one fresh
   constant per existential sentence true there.  **Capture-avoidance wrinkle:** `VarSymb ≅ ℕ` is
   only countable, and the extra constants must (a) avoid the seed's symbols and (b) still leave
   *infinitely many* symbols unused.  So we reserve a co-infinite supply `Reserved ⊆ VarSymb`.

2. **Actual world.**  Maximalise `Γ` to a (witnessed) MCS `Γ'`, expanding `V` to `V'` by adding the
   bottom-level (`word = []`) extra constants.  Domain `D` = terms buildable in `V'` quotiented by
   *provable equality*; predicate/relation extensions are standard (each added constant goes into the
   extension recorded by its defining sentence).

3. **Accessible worlds.**  A world accessible from `w` carries a context *induced* from `w`'s:
   - every `□V`-variable, now at type `V` (necessary — must be present in every accessible world);
   - every extra `□`-variable (from boxed existentials), now at `V`;
   - *some* `◇V`-variables, now at `V` — we **range over all subsets** of these (one world per subset);
   - *some* extra `◇`-variables, now at `V`.
   **Accessibility** `R w w'`: `w'` contains all of `w`'s necessary (unboxed) variables and every
   boxed WFF; and if `w'` contains a possible variable `x` then it contains all `box_x`-WFFs.
   The `Nec`/`Pos` objects at `w` **point at** these unboxed/undiamonded variables (crucially: no
   variable at `w` points at the *newly added* constants of `w'`).  Iterate at every world.

## Status
Foundations (infinitary context bridge, reserved symbols, modal-word tree) started below; the
proof-theory (`Consistent`/`MCS`) and the `RModel` fields are stubbed / `sorry` for now.

## ⭐ COMPLETENESS ROADMAP (critical path; 🔴 = crux/high-risk, 🟡 = moderate)
1. **Interpreter metatheory** (`InterpMeta.lean`, in progress): `interpWFF_substVar` 🟡 (Truth-Lemma
   ∀/∃ cases) on top of `ctx_ext` + `rename`. Congruence family DONE (axiom-clean).
2. **Proof theory**: replace the `axiom Proves/Consistent/IsMCS/lindenbaum` stubs with real defs +
   Lindenbaum 🔴. Needs: monotonicity/cut, ⊥-consistency, MCS negation-completeness (exactly one of
   φ/¬φ) and closure under provable consequence. Plus **rich/saturated MCSs** with ∃- and
   ◇-**witnesses** (the `reservedSym` fresh constants exist for this) 🔴.
3. **Canonical domains** `DObj = Quotient (PreTerm) provSetoidV` 🟡: make `provSetoidV` a real setoid
   (provable-equality ≈) respecting `funcInterp`/application congruence.
4. **Canonical `RModel` instance** 🔴🔴 (THE CRUX): define `relInterp`/`funcInterp`/`necEval`/
   `posEval` and discharge EVERY `_eval` law. `necEval`/`posEval` must be **injective**
   and **denotable-only** so Barcan FAILS — this is the whole reason for the RModelB redesign.
5. **Accessibility + existence** 🔴: `Accessible` = boxed-theory transfer; prove the ◇/∃-existence
   lemma (◇_x φ ∈ w ⇒ ∃ accessible w' and a witness d with the instance ∈ w'). Classic gap.
6. **Truth Lemma** 🔴: `interpWFF φ w env ↔ φ ∈ w.theory`, induction on φ (uses (1) for ∀/∃, (5) for
   □/◇). Stateable now that the interpreter is total + box-β clean.
7. **Completeness**: `Consistent Γ ⇒ satisfiable` (Lindenbaum + rich extension + Truth Lemma) ⇒ ⊨→⊢.
-/

namespace QML.Canonical

open scoped Classical

/-! ## Reserved variable symbols (capture-avoidance)

`VarSymb = .mk ℕ`.  We need a **co-infinite** reserved supply for the extra constants: infinitely
many symbols to draw constants from, while leaving infinitely many for later Henkin witnesses and
keeping the seed's symbols free.  `ℕ ≅ ℕ × ℕ` gives infinitely many disjoint infinite columns. -/

/-- Reserve column `c` of the `ℕ ≅ ℕ × ℕ` splitting: `reservedSym c i` is the `i`-th symbol of the
    `c`-th reserved column.  Distinct columns are disjoint and each column is infinite, so any finite
    (or countable, co-infinitely-used) seed can avoid a chosen column and still leave others free. -/
noncomputable def reservedSym (c i : ℕ) : VarSymb :=
  .mk ((Nat.pairEquiv (c, i)).succ)   -- shift by `succ` to keep `.mk 0` available as a sentinel

/-- Injectivity of the reserved supply: `(column, index)` is recovered, so distinct columns give
    disjoint infinite supplies. -/
theorem reservedSym_injective : Function.Injective (fun p : ℕ × ℕ => reservedSym p.1 p.2) := by
  intro ⟨c₁, i₁⟩ ⟨c₂, i₂⟩ h
  simp only [reservedSym, VarSymb.mk.injEq, Nat.succ.injEq] at h
  exact Nat.pairEquiv.injective (by exact_mod_cast h)

/-! ## Infinitary context bridge

The finitary machinery (`Term`, `WFF`, `VarCtx`) is `Finset`-indexed.  The canonical contexts are
infinite, so we use `Set`s with the same uniqueness invariant, and bridge via finite subcontexts. -/

/-- An **infinite context**: a set of typed variables with `VarCtx`'s uniqueness invariant (no symbol
    carries two types). -/
structure ICtx where
  carrier : Set (VarSymb × VarType)
  uniq : ∀ v ∈ carrier, ∀ w ∈ carrier, v.1 = w.1 → v.2 = w.2

/-- A finite `VarCtx` sitting inside an infinite context. -/
def VarCtx.subOf (V : VarCtx) (I : ICtx) : Prop := ∀ p ∈ V.1, p ∈ I.carrier

/-- Any finite `VarCtx` whose carrier lies in `I` inherits nothing extra — it is automatically a
    consistent finite window on `I`.  (The directed union of all such windows is `I`.) -/
theorem VarCtx.subOf_uniq {V : VarCtx} {I : ICtx} (h : VarCtx.subOf V I) :
    ∀ v ∈ V.1, ∀ w ∈ V.1, v.1 = w.1 → v.2 = w.2 := fun v hv w hw => I.uniq v (h v hv) w (h w hw)

/-! ## General weakening `WFF σ V → WFF σ W` for `V ⊆ W`

Built by folding the single-variable `WFF.ctx_ext` over the extra variables `W \ V` (well-founded on
`(W \ V).card`).  Needed to align the varying-context hypotheses of a Sentence-level derivation into a
common window.  Freshness of each added variable follows from `W`'s uniqueness invariant. -/

/-- Two `VarCtx`es with the same carrier are equal (the uniqueness proof is irrelevant). -/
theorem VarCtx_ext' {V W : VarCtx} (h : V.1 = W.1) : V = W := by
  obtain ⟨v, pv⟩ := V; obtain ⟨w, pw⟩ := W; cases h; rfl

/-- A variable in `W \ V` has a symbol fresh for `V` (else `W`'s uniqueness would force it into `V`). -/
theorem fresh_of_mem_sdiff {V W : VarCtx} (hVW : V.1 ⊆ W.1) {e : VarSymb × VarType}
    (he : e ∈ W.1 \ V.1) : e.1 ∉ VarCtx_to_VarSymbs V := by
  intro hin
  obtain ⟨u, hu, hu1⟩ := Finset.mem_image.mp hin
  have heq : u = e := Prod.ext hu1 (W.2 u (hVW hu) e (Finset.mem_sdiff.mp he).1 hu1)
  exact (Finset.mem_sdiff.mp he).2 (heq ▸ hu)

/-- **General weakening**: a `WFF` over `V` reinterpreted over any `W ⊇ V`, by folding `WFF.ctx_ext`
    over the extra variables `W \ V`. -/
noncomputable def weakenTo {σ : Signature} (V W : VarCtx) (hVW : V.1 ⊆ W.1) (φ : WFF σ V) : WFF σ W :=
  if h : (W.1 \ V.1).Nonempty then
    have he : h.choose ∈ W.1 \ V.1 := h.choose_spec
    have hfresh : h.choose.1 ∉ VarCtx_to_VarSymbs V := fresh_of_mem_sdiff hVW he
    have hV'W : (VarCtx_insert h.choose V hfresh).1 ⊆ W.1 := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpV
      · exact (Finset.mem_sdiff.mp he).1
      · exact hVW hpV
    weakenTo (VarCtx_insert h.choose V hfresh) W hV'W (WFF.ctx_ext h.choose hfresh φ)
  else
    have hWV : W.1 ⊆ V.1 := fun p hpW => by
      by_contra hpV; exact h ⟨p, Finset.mem_sdiff.mpr ⟨hpW, hpV⟩⟩
    (VarCtx_ext' (Finset.Subset.antisymm hVW hWV)) ▸ φ
termination_by (W.1 \ V.1).card
decreasing_by
  have he : h.choose ∈ W.1 \ V.1 := h.choose_spec
  have hins : (VarCtx_insert h.choose V hfresh).1 = insert h.choose V.1 := rfl
  have hset : W.1 \ insert h.choose V.1 = (W.1 \ V.1).erase h.choose := by
    ext p; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
  rw [hins, hset]
  exact Finset.card_erase_lt_of_mem he

/-- General weakening for **terms** (mirror of `weakenTo`): `Term σ V S → Term σ W S` for `V ⊆ W`,
    by folding `Term.ctx_ext`.  Needed to bring two `PreTerm`s into a common window for the
    provable-equality setoid. -/
noncomputable def Term.weakenTo {σ : Signature} {S : VarType} (V W : VarCtx) (hVW : V.1 ⊆ W.1)
    (t : Term σ V S) : Term σ W S :=
  if h : (W.1 \ V.1).Nonempty then
    have he : h.choose ∈ W.1 \ V.1 := h.choose_spec
    have hfresh : h.choose.1 ∉ VarCtx_to_VarSymbs V := fresh_of_mem_sdiff hVW he
    have hV'W : (VarCtx_insert h.choose V hfresh).1 ⊆ W.1 := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpV
      · exact (Finset.mem_sdiff.mp he).1
      · exact hVW hpV
    Term.weakenTo (VarCtx_insert h.choose V hfresh) W hV'W (Term.ctx_ext h.choose hfresh t)
  else
    have hWV : W.1 ⊆ V.1 := fun p hpW => by
      by_contra hpV; exact h ⟨p, Finset.mem_sdiff.mpr ⟨hpW, hpV⟩⟩
    (VarCtx_ext' (Finset.Subset.antisymm hVW hWV)) ▸ t
termination_by (W.1 \ V.1).card
decreasing_by
  have he : h.choose ∈ W.1 \ V.1 := h.choose_spec
  have hins : (VarCtx_insert h.choose V hfresh).1 = insert h.choose V.1 := rfl
  have hset : W.1 \ insert h.choose V.1 = (W.1 \ V.1).erase h.choose := by
    ext p; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
  rw [hins, hset]
  exact Finset.card_erase_lt_of_mem he

/-! ## The modal-word tree (indexing the extra constants / the worlds)

A world of the canonical model is reached from the root by a sequence of modal steps: a `box` step
(to a necessary successor) or a `dia x` step (to the successor witnessing possibility variable `x`).
Words over this alphabet index both the worlds and the extra constants added along the way. -/

/-- One modal step: down a `□` edge, or down the `◇`-edge witnessed by variable `x`. -/
inductive ModalStep
  | box
  | dia (x : VarSymb)
  deriving DecidableEq

/-- A **modal word**: a path from the root world.  `[]` is the actual world. -/
abbrev ModalWord := List ModalStep

/-! ## Proof theory — STUBBED (abstract for now)

We take `Sentence` (closed WFFs over the seed) and the consistency/MCS predicates as abstract; the
canonical construction only needs their interface (Lindenbaum, witnesses, deductive closure). -/

/-- An (open) **WFF over the infinite context** = a real `WFF σ V` over *some* finite context `V`.
    A world's theory constrains these `V`s to sit inside the world's context (`V.subOf w.ctx`). -/
def Sentence (σ : Signature) : Type := Σ V : VarCtx, WFF σ V

/-- **Finitary provability** (Prop-level `Γ ⊢ φ` in a fixed finite context `V`): the derivation type
    `Proof` truncated to a proposition.  This is the concrete core; the Sentence-level `Proves` below
    is built from it by aligning a finite subset of the (varying-context) hypotheses into a common
    window. -/
def Provable {σ : Signature} {V : VarCtx} (Γ : Finset (WFF σ V)) (φ : WFF σ V) : Prop :=
  Nonempty (Proof σ V Γ φ)

namespace Provable
variable {σ : Signature} {V : VarCtx} {Γ Δ : Finset (WFF σ V)} {φ ψ χ : WFF σ V}

theorem ax (h : φ ∈ Γ) : Provable Γ φ := ⟨.ax h⟩
theorem weak1 (h : Provable Γ φ) (ψ : WFF σ V) : Provable (Γ ∪ {ψ}) φ := h.elim fun p => ⟨.weak p⟩
theorem mp (h₁ : Provable Γ (φ.imp ψ)) (h₂ : Provable Γ φ) : Provable Γ ψ :=
  h₁.elim fun p => h₂.elim fun q => ⟨.imp_elim p q⟩
theorem imp_intro (h : Provable (Γ ∪ {φ}) ψ) : Provable Γ (φ.imp ψ) := h.elim fun p => ⟨.imp_intro p⟩
theorem bot_elim (h : Provable Γ .bot) : Provable Γ φ := h.elim fun p => ⟨.bot_elim p⟩
theorem top_intro : Provable Γ .top := ⟨.top_intro⟩
theorem lem (φ : WFF σ V) : Provable Γ (φ.or (neg φ)) := ⟨.lem φ⟩
theorem and_intro (h₁ : Provable Γ φ) (h₂ : Provable Γ ψ) : Provable Γ (φ.and ψ) :=
  h₁.elim fun p => h₂.elim fun q => ⟨.and_intro p q⟩
theorem and_elim_l (h : Provable Γ (φ.and ψ)) : Provable Γ φ := h.elim fun p => ⟨.and_elim_l p⟩
theorem and_elim_r (h : Provable Γ (φ.and ψ)) : Provable Γ ψ := h.elim fun p => ⟨.and_elim_r p⟩
theorem or_intro_l (h : Provable Γ φ) : Provable Γ (φ.or ψ) := h.elim fun p => ⟨.or_intro_l p⟩
theorem or_intro_r (h : Provable Γ ψ) : Provable Γ (φ.or ψ) := h.elim fun p => ⟨.or_intro_r p⟩
theorem or_elim (h : Provable Γ (φ.or ψ)) (h₁ : Provable (Γ ∪ {φ}) χ) (h₂ : Provable (Γ ∪ {ψ}) χ) :
    Provable Γ χ := h.elim fun p => h₁.elim fun q₁ => h₂.elim fun q₂ => ⟨.or_elim p q₁ q₂⟩

/-- Weakening by a whole finite set of extra hypotheses (iterated `weak1`). -/
theorem weak_union (h : Provable Γ φ) : (S : Finset (WFF σ V)) → Provable (Γ ∪ S) φ := by
  intro S
  induction S using Finset.induction with
  | empty => simpa using h
  | @insert a S _ ih =>
      rw [Finset.union_insert]
      have := weak1 ih a
      rwa [Finset.union_singleton] at this

/-- **Monotone** in the hypotheses. -/
theorem mono (hsub : Γ ⊆ Δ) (h : Provable Γ φ) : Provable Δ φ := by
  have := weak_union h Δ
  rwa [Finset.union_eq_right.mpr hsub] at this

/-- **Explosion**: `φ` and `¬φ` prove `⊥` (`neg φ = φ ⟹ ⊥`). -/
theorem neg_elim (hn : Provable Γ (neg φ)) (hp : Provable Γ φ) : Provable Γ .bot := mp hn hp

/-- **Negation introduction**: if `Γ, φ ⊢ ⊥` then `Γ ⊢ ¬φ`. -/
theorem neg_intro (h : Provable (Γ ∪ {φ}) .bot) : Provable Γ (neg φ) := imp_intro h

/-- **Deduction** (forward): `Γ ⊢ φ ⟹ ψ` gives `Γ, φ ⊢ ψ`. -/
theorem deduction_mp (h : Provable Γ (φ.imp ψ)) : Provable (Γ ∪ {φ}) ψ :=
  mp (weak1 h φ) (ax (Finset.mem_union_right _ (Finset.mem_singleton_self _)))

/-- **Cut**: derive a lemma `φ`, then use it. -/
theorem cut (h₁ : Provable Γ φ) (h₂ : Provable (Γ ∪ {φ}) ψ) : Provable Γ ψ := mp (imp_intro h₂) h₁

/-- `φ` is a member of `Γ ∪ {φ}` — the common `ax` witness. -/
private theorem mem_self : φ ∈ Γ ∪ {φ} := Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- **Double-negation elimination** (classical, via `lem` + `or_elim`). -/
theorem dne (h : Provable Γ (neg (neg φ))) : Provable Γ φ :=
  or_elim (lem φ) (ax mem_self) (bot_elim (neg_elim (weak1 h (neg φ)) (ax mem_self)))

/-- **Proof by contradiction**: if `Γ, ¬φ ⊢ ⊥` then `Γ ⊢ φ`. -/
theorem byContra (h : Provable (Γ ∪ {neg φ}) .bot) : Provable Γ φ := dne (neg_intro h)

end Provable

/-- **Finitary consistency**: a finite theory that does not prove `⊥`. -/
def FinConsistent {σ : Signature} {V : VarCtx} (Γ : Finset (WFF σ V)) : Prop := ¬ Provable Γ .bot

namespace FinConsistent
variable {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {φ : WFF σ V}

/-- A consistent theory cannot prove both `φ` and `¬φ`. -/
theorem not_both (hcon : FinConsistent Γ) (hp : Provable Γ φ) : ¬ Provable Γ (neg φ) :=
  fun hn => hcon (Provable.neg_elim hn hp)

/-- If `Γ` is consistent and `Γ ⊬ ¬φ`, then `Γ ∪ {φ}` is consistent (the Lindenbaum extension step). -/
theorem insert_of_not_provable_neg (hcon : FinConsistent Γ) (hnp : ¬ Provable Γ (neg φ)) :
    FinConsistent (Γ ∪ {φ}) := fun hbot => hnp (Provable.neg_intro hbot)

/-- Consistency is inherited by subsets. -/
theorem subset {Δ : Finset (WFF σ V)} (hsub : Δ ⊆ Γ) (hcon : FinConsistent Γ) : FinConsistent Δ :=
  fun hbot => hcon (Provable.mono hsub hbot)

/-- **The Lindenbaum branching step**: from a consistent `Γ`, adding `φ` or `¬φ` stays consistent for
    at least one choice (classically, exactly the one not refuted). -/
theorem either (hcon : FinConsistent Γ) (φ : WFF σ V) :
    FinConsistent (Γ ∪ {φ}) ∨ FinConsistent (Γ ∪ {neg φ}) := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  simp only [FinConsistent, not_not] at h1 h2
  exact hcon (Provable.neg_elim (Provable.neg_intro h2) (Provable.neg_intro h1))

end FinConsistent

/-- The empty variable context. -/
def emptyCtx : VarCtx := ⟨∅, by intro v hv; simp at hv⟩

/-- **Sentence-level provability** (concrete): `φ` is derivable in some common finite window `W` from
    finitely many hypotheses, each a weakening into `W` of a sentence in `Γ`.  Reduces the
    varying-context set `Γ` to a finitary `Provable` in `W`. -/
def Proves {σ : Signature} (Γ : Set (Sentence σ)) (φ : Sentence σ) : Prop :=
  ∃ (W : VarCtx) (hφ : φ.1.1 ⊆ W.1) (Δ : Finset (WFF σ W)),
    (∀ ψ ∈ Δ, ∃ s ∈ Γ, ∃ hs : s.1.1 ⊆ W.1, weakenTo s.1 W hs s.2 = ψ) ∧
    Provable Δ (weakenTo φ.1 W hφ φ.2)

/-- **Consistent**: does not prove (a designated) falsum. -/
def Consistent {σ : Signature} (Γ : Set (Sentence σ)) : Prop :=
  ¬ Proves Γ ⟨emptyCtx, .bot⟩

/-- **Maximal consistent set**: consistent and cannot be consistently extended. -/
def IsMCS {σ : Signature} (Γ : Set (Sentence σ)) : Prop :=
  Consistent Γ ∧ ∀ φ : Sentence σ, Consistent (insert φ Γ) → φ ∈ Γ

/-- `Proves` is **monotone** in the hypotheses. -/
theorem Proves.mono {σ : Signature} {Γ Γ' : Set (Sentence σ)} (hsub : Γ ⊆ Γ') {φ : Sentence σ}
    (h : Proves Γ φ) : Proves Γ' φ := by
  obtain ⟨W, hφ, Δ, hΔ, hpr⟩ := h
  refine ⟨W, hφ, Δ, fun ψ hψ => ?_, hpr⟩
  obtain ⟨s, hsΓ, hs, hweq⟩ := hΔ ψ hψ
  exact ⟨s, hsub hsΓ, hs, hweq⟩

/-- **Consistency is inherited by subsets** (a subset of a consistent set is consistent). -/
theorem Consistent.subset {σ : Signature} {Γ Γ' : Set (Sentence σ)} (hsub : Γ ⊆ Γ')
    (h : Consistent Γ') : Consistent Γ := fun hpr => h (Proves.mono hsub hpr)

/-- Every hypothesis in `Γ` is provable from `Γ` (the `Sentence`-level `ax`). -/
theorem Proves.of_mem {σ : Signature} {Γ : Set (Sentence σ)} {φ : Sentence σ} (h : φ ∈ Γ) :
    Proves Γ φ :=
  ⟨φ.1, subset_rfl, {weakenTo φ.1 φ.1 subset_rfl φ.2},
    fun ψ hψ => ⟨φ, h, subset_rfl, (Finset.mem_singleton.mp hψ).symm⟩,
    Provable.ax (Finset.mem_singleton_self _)⟩

/-- **Finitary character**: a `Proves` uses only finitely many hypotheses — it is witnessed by a
    *finite* subset `Γ₀ ⊆ Γ`.  This is the crux of the Lindenbaum chain-union argument. -/
theorem Proves.finite_support {σ : Signature} {Γ : Set (Sentence σ)} {φ : Sentence σ}
    (h : Proves Γ φ) :
    ∃ Γ₀ : Finset (Sentence σ), (↑Γ₀ : Set (Sentence σ)) ⊆ Γ ∧ Proves (↑Γ₀ : Set (Sentence σ)) φ := by
  obtain ⟨W, hφ, Δ, hΔ, hpr⟩ := h
  choose f hf hs hfeq using hΔ
  refine ⟨Δ.attach.image (fun p => f p.1 p.2), ?_, W, hφ, Δ, ?_, hpr⟩
  · intro s hs'
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and] at hs'
    obtain ⟨p, rfl⟩ := hs'
    exact hf p.1 p.2
  · intro ψ hψ
    refine ⟨f ψ hψ, ?_, hs ψ hψ, hfeq ψ hψ⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and]
    exact ⟨⟨ψ, hψ⟩, rfl⟩

/-- A finite subset of a nonempty chain's union sits inside a single chain element (directedness). -/
theorem exists_of_finset_subset_sUnion {σ : Signature} {c : Set (Set (Sentence σ))}
    (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    (Γ₀ : Finset (Sentence σ)) → (↑Γ₀ : Set (Sentence σ)) ⊆ ⋃₀ c →
    ∃ Δ ∈ c, (↑Γ₀ : Set (Sentence σ)) ⊆ Δ := by
  intro Γ₀
  induction Γ₀ using Finset.induction with
  | empty => intro _; obtain ⟨Δ, hΔ⟩ := hne; exact ⟨Δ, hΔ, by simp⟩
  | @insert s Γ₀' _ ih =>
      intro hsub
      obtain ⟨Δs, hΔs, hsΔs⟩ := hsub (by simp : s ∈ (↑(insert s Γ₀') : Set _))
      obtain ⟨Δ', hΔ', hΓ₀'⟩ := ih fun x hx => hsub (by
        simp only [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inr hx)
      rcases hchain.total hΔs hΔ' with hle | hle
      · refine ⟨Δ', hΔ', fun x hx => ?_⟩
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
        rcases hx with rfl | hx
        · exact hle hsΔs
        · exact hΓ₀' hx
      · refine ⟨Δs, hΔs, fun x hx => ?_⟩
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
        rcases hx with rfl | hx
        · exact hsΔs
        · exact hle (hΓ₀' hx)

/-- **Chain-union preserves consistency** (via finitary character + directedness). -/
theorem Consistent.sUnion {σ : Signature} {c : Set (Set (Sentence σ))}
    (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) (hcon : ∀ Δ ∈ c, Consistent Δ) :
    Consistent (⋃₀ c) := by
  intro hpr
  obtain ⟨Γ₀, hΓ₀sub, hΓ₀pr⟩ := hpr.finite_support
  obtain ⟨Δ, hΔc, hΓ₀Δ⟩ := exists_of_finset_subset_sUnion hchain hne Γ₀ hΓ₀sub
  exact hcon Δ hΔc (hΓ₀pr.mono hΓ₀Δ)

/-- **Lindenbaum**: every consistent set extends to a maximal consistent set (Zorn). -/
theorem lindenbaum {σ : Signature} (Γ : Set (Sentence σ)) (hΓ : Consistent Γ) :
    ∃ Δ, Γ ⊆ Δ ∧ IsMCS Δ := by
  obtain ⟨Δ, hΓΔ, hmax⟩ := zorn_subset_nonempty {Δ | Γ ⊆ Δ ∧ Consistent Δ}
    (fun c hcS hchain hcne => ⟨⋃₀ c, ⟨fun _ hs => by
        obtain ⟨Δ₀, hΔ₀⟩ := hcne
        exact ⟨Δ₀, hΔ₀, (hcS hΔ₀).1 hs⟩,
      Consistent.sUnion hchain hcne fun Δ hΔ => (hcS hΔ).2⟩,
      fun s hs => Set.subset_sUnion_of_mem hs⟩)
    Γ ⟨subset_rfl, hΓ⟩
  refine ⟨Δ, hΓΔ, hmax.1.2, fun φ hφcon => ?_⟩
  by_contra hφΔ
  have hins : insert φ Δ ⊆ Δ :=
    hmax.2 ⟨hΓΔ.trans (Set.subset_insert _ _), hφcon⟩ (Set.subset_insert _ _)
  exact hφΔ (hins (Set.mem_insert _ _))

/-! ## Domains — "populate the domain at each world"

`D w` = individual (`Var`-typed) terms over `w`'s (infinite) context `I`, mod **provable equality**.
We bridge to the finitary `Term` via finite windows of `I`.  The `≈` setoid is STUBBED — concretely
it is "provably equal after weakening to a common finite window, in `w`'s theory". -/

/-- A type-`V` term over a *finite window* of the world's infinite context `I`. -/
structure PreTerm (σ : Signature) (I : ICtx) (V : VarType) where
  ctx : VarCtx
  sub : VarCtx.subOf ctx I
  tm : Term σ ctx V

/-- Finitary reflexivity of equality (`⊢ t = t`), from the `eq_intro` rule. -/
theorem Provable.eq_refl {σ : Signature} {V : VarCtx} {S : VarType} {Γ : Finset (WFF σ V)}
    (t : Term σ V S) : Provable Γ (WFF.eq t t) := ⟨.eq_intro t⟩

/-- Public re-derivation of the (private) `Term.substVar_eq_ctx_rest`: for a pair-free extended
    context, `substVar` coincides with `ctx_rest`.  Copied verbatim from `SubstitutionLemmas9`
    (both `Term.substVar` and `Term.ctx_rest_MU` are public). -/
theorem Term.substVar_eq_ctx_rest' {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S')
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) :
    Term.substVar hx s t = Term.ctx_rest hx hpf s t := by
  simp only [Term.substVar]
  conv_lhs => unfold Term.ctx_rest_MU
  split
  · rfl
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

/-- **Finitary symmetry of provable equality** (Leibniz derivation via `eq_elim`).  Requires a fresh
    `.Var`-typed witness `x` and a pair-free extended context (`hpf`).  Instantiate `φ := (x = a↑)`:
    `substVar a φ = (a = a)` (provable) and `substVar b φ = (b = a)` (the goal). -/
theorem Provable.eq_symm {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)}
    (a b : Term σ V .Var)
    (x : VarSymb) (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, .Var⟩ V hx).firstPairVar = none)
    (h : Provable Γ (WFF.eq a b)) : Provable Γ (WFF.eq b a) := by
  obtain ⟨p⟩ := h
  set xv : VarSymb × VarType := ⟨x, .Var⟩ with hxv
  have hxmem : (⟨x, VarType.Var⟩ : VarSymb × VarType) ∈ (VarCtx_insert xv V hx).1 :=
    Finset.mem_insert_self _ _
  set φ : WFF σ (VarCtx_insert xv V hx) :=
    WFF.eq (Term.var ⟨x, hxmem⟩) (Term.ctx_ext xv hx a) with hφ
  -- substitution reduction: substVar c φ = (c = a) for any individual term `c`.
  have key : ∀ (c : Term σ V .Var), WFF.substVar hx c φ = WFF.eq c a := by
    intro c
    rw [hφ, WFF.substVar_eq hx c hpf]
    congr 1
    · rw [Term.substVar_var hx c hpf x hxmem, dif_pos rfl]
    · rw [Term.substVar_eq_ctx_rest' hx c (Term.ctx_ext xv hx a) hpf]
      exact Term.ctx_rest_ctx_ext hx hpf c a
  have pa : Proof σ V Γ (WFF.substVar hx a φ) := (key a).symm ▸ Proof.eq_intro a
  have pb : Proof σ V Γ (WFF.substVar hx b φ) := Proof.eq_elim xv hx a b p pa
  exact ⟨(key b) ▸ pb⟩

/-- **Finitary transitivity of provable equality** (Leibniz derivation via `eq_elim`).  Instantiate
    `φ := (a↑ = x)`: from `a = b` we get `substVar b φ = (a = b)`, and `eq_elim` with `b = c`
    yields `substVar c φ = (a = c)`. -/
theorem Provable.eq_trans {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)}
    (a b c : Term σ V .Var)
    (x : VarSymb) (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, .Var⟩ V hx).firstPairVar = none)
    (hab : Provable Γ (WFF.eq a b)) (hbc : Provable Γ (WFF.eq b c)) :
    Provable Γ (WFF.eq a c) := by
  obtain ⟨pab⟩ := hab
  obtain ⟨pbc⟩ := hbc
  set xv : VarSymb × VarType := ⟨x, .Var⟩ with hxv
  have hxmem : (⟨x, VarType.Var⟩ : VarSymb × VarType) ∈ (VarCtx_insert xv V hx).1 :=
    Finset.mem_insert_self _ _
  set φ : WFF σ (VarCtx_insert xv V hx) :=
    WFF.eq (Term.ctx_ext xv hx a) (Term.var ⟨x, hxmem⟩) with hφ
  have key : ∀ (d : Term σ V .Var), WFF.substVar hx d φ = WFF.eq a d := by
    intro d
    rw [hφ, WFF.substVar_eq hx d hpf]
    congr 1
    · rw [Term.substVar_eq_ctx_rest' hx d (Term.ctx_ext xv hx a) hpf]
      exact Term.ctx_rest_ctx_ext hx hpf d a
    · rw [Term.substVar_var hx d hpf x hxmem, dif_pos rfl]
  have pb : Proof σ V Γ (WFF.substVar hx b φ) := (key b).symm ▸ pab
  have pc : Proof σ V Γ (WFF.substVar hx c φ) := Proof.eq_elim xv hx b c pbc pb
  exact ⟨(key c) ▸ pc⟩

/-- **Provable-equality relation** on `PreTerm`s (theory-relative, concrete): the two terms, weakened
    to a common window, are provably equal in `Γ`.  This is the real `≈` that `provSetoidV` should be
    built from (with the theory `Γ` added to the signature — see the plan).  Remaining for the full
    `Setoid`: `refl` (via `eq_refl` + `weakenTo`-over-`eq`), `symm`/`trans` (via `eq_elim` — needs
    `SubstitutionLemmas9`'s `substVar` reductions + a window merge). -/
def provTermEq {σ : Signature} {I : ICtx} (Γ : Set (Sentence σ)) {V : VarType}
    (s t : PreTerm σ I V) : Prop :=
  ∃ (W : VarCtx) (hs : s.ctx.1 ⊆ W.1) (ht : t.ctx.1 ⊆ W.1),
    Proves Γ ⟨W, WFF.eq (Term.weakenTo s.ctx W hs s.tm) (Term.weakenTo t.ctx W ht t.tm)⟩

/-- Weakening to the same context is the identity (the `▸` cast collapses by `Eq` proof-irrelevance). -/
theorem weakenTo_self {σ : Signature} {V : VarCtx} (h : V.1 ⊆ V.1) (X : WFF σ V) :
    weakenTo V V h X = X := by
  rw [weakenTo, dif_neg (by simp : ¬ (V.1 \ V.1).Nonempty)]

theorem Term.weakenTo_self {σ : Signature} {V : VarCtx} {S : VarType} (h : V.1 ⊆ V.1)
    (t : Term σ V S) : Term.weakenTo V V h t = t := by
  rw [Term.weakenTo, dif_neg (by simp : ¬ (V.1 \ V.1).Nonempty)]

/-- Transport of an `eq`-formula along a `VarCtx` identity distributes over the two terms. -/
theorem VarCtx_transport_eq {σ : Signature} {S : VarType} {V W : VarCtx} (p : V = W)
    (a b : Term σ V S) :
    (p ▸ (WFF.eq a b) : WFF σ W) = WFF.eq (p ▸ a) (p ▸ b) := by
  cases p; rfl

/-- `weakenTo` distributes over `WFF.eq`: weakening an equality formula equals the equality of the
    two weakened terms.  Needed to expose the `eq` structure inside `Proves` for the setoid's
    `symm`/`trans`.  Proven by strong induction on `(W.1 \ V.1).card`, mirroring `weakenTo`'s own
    recursion. -/
theorem weakenTo_eq {σ : Signature} {S : VarType} (W : VarCtx) :
    ∀ (n : ℕ) (V : VarCtx) (hVW : V.1 ⊆ W.1) (a b : Term σ V S),
      (W.1 \ V.1).card = n →
      weakenTo V W hVW (WFF.eq a b)
        = WFF.eq (Term.weakenTo V W hVW a) (Term.weakenTo V W hVW b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V hVW a b hn
    rw [weakenTo, Term.weakenTo, Term.weakenTo]
    by_cases h : (W.1 \ V.1).Nonempty
    · simp only [dif_pos h]
      simp only [WFF.ctx_ext]
      have he : h.choose ∈ W.1 \ V.1 := h.choose_spec
      have hfresh : h.choose.1 ∉ VarCtx_to_VarSymbs V := fresh_of_mem_sdiff hVW he
      have hV'W : (VarCtx_insert h.choose V hfresh).1 ⊆ W.1 := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hpV
        · exact (Finset.mem_sdiff.mp he).1
        · exact hVW hpV
      have hset : W.1 \ (VarCtx_insert h.choose V hfresh).1 = (W.1 \ V.1).erase h.choose := by
        show W.1 \ insert h.choose V.1 = _
        ext p; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      have hlt : (W.1 \ (VarCtx_insert h.choose V hfresh).1).card < n := by
        rw [hset, ← hn]; exact Finset.card_erase_lt_of_mem he
      exact ih _ hlt (VarCtx_insert h.choose V hfresh) hV'W
        (Term.ctx_ext h.choose hfresh a) (Term.ctx_ext h.choose hfresh b) rfl
    · simp only [dif_neg h]
      exact VarCtx_transport_eq _ a b

/-- **Reflexivity of provable equality** (first setoid law): witnessed at the term's own window with
    an empty hypothesis set, via `eq_intro`. -/
theorem provTermEq.refl {σ : Signature} {I : ICtx} (Γ : Set (Sentence σ)) {V : VarType}
    (s : PreTerm σ I V) : provTermEq Γ s s :=
  ⟨s.ctx, subset_rfl, subset_rfl, s.ctx, subset_rfl, ∅, fun ψ hψ => by simp at hψ, by
    rw [weakenTo_self]; exact Provable.eq_refl _⟩

/-- Provable-equality setoid on type-`V` terms (STUB — the concrete relation is `provTermEq` above;
    a real `Setoid` needs the support lemmas noted there + the theory in the signature). -/
axiom provSetoidV (σ : Signature) (I : ICtx) (V : VarType) : Setoid (PreTerm σ I V)

/-- **Denotable objects of type `V`** at a world with context `I`: type-`V` terms mod provable
    equality.  The whole `interp` tower is instances of this: `D w = DObj Var`, `Pos U w = DObj (◇U)`,
    `NecVar k w = DObj (□^{k+1} Var)`, `NecDia k U w = DObj (□^{k+1} ◇U)`. -/
def DObj (σ : Signature) (I : ICtx) (V : VarType) : Type := Quotient (provSetoidV σ I V)

/-- `□^k` applied to a type — for the box-tower levels. -/
def boxPow : ℕ → VarType → VarType
  | 0,     V => V
  | k + 1, V => .VTypeBox (boxPow k V)

/- **Why `nec_inj` will hold** (world-extensionality — the property the non-full redesign lives on).
   Suppose two necessary objects `x`, `y` point at the same section `S` (equal value at every
   accessible world).  By the Truth-Lemma IH their values are *provably equal* at every world; then
   `nec_ext` (the syntactic extensionality principle for `□`) proves `x = y` as necessary objects; and
   being provably equal they lie in the same `≈`-class, hence are the *same* domain object.  So
   distinct denotable necessary objects have distinct sections — exactly `nec_inj`. (`pos_inj`
   dually.) -/

/-! ## The canonical frame — SKELETON

Worlds = witnessed MCSs bundled with their (infinite) induced context; `D w = Dom σ w.ctx`;
`relInterp`/`funcInterp` read atomic membership off `theory`; `R` = the accessibility above.  All the
*data* fields are buildable here; only the *law* fields + Truth Lemma need the real proof theory. -/

/-- A **world**: a witnessed MCS together with its (infinite) induced context. -/
structure World (σ : Signature) where
  ctx : ICtx
  theory : Set (Sentence σ)
  isMCS : IsMCS theory
  -- TODO: the modal word reaching this world + the added constants (for the tree/pointing structure).

/-- Necessary variables induced by a context: each `□`-typed variable, *unboxed*.  Present (unboxed)
    in **every** accessible world. -/
def necVars (I : ICtx) : Set (VarSymb × VarType) :=
  {p | (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ∈ I.carrier}

/-- Possible variables: each `◇`-typed variable, *undiamonded*.  Present in **some** accessible
    worlds (the ones whose individuals include it). -/
def posVars (I : ICtx) : Set (VarSymb × VarType) :=
  {p | (⟨p.1, p.2.VTypeDia⟩ : VarSymb × VarType) ∈ I.carrier}

/-- Theory-side of accessibility (STUB — needs `WFF` structure): `w'.theory` contains the content of
    every `□`-WFF of `w`, plus the `box_x`-WFFs of `w` for each possible variable `w'` carries. -/
axiom boxedTheoryTransfers {σ : Signature} : World σ → World σ → Prop

/-- **Accessibility.**  Context-side is concrete: `w'`'s individual variables include *all* of `w`'s
    necessary variables and are drawn *only* from `necVars ∪ posVars`.  Theory-side stubbed.  Per the
    plan the accessible worlds are **every** consistent MCS whose individual-variable set lies between
    `necVars w` and `necVars w ∪ posVars w` (and which respects the boxed theory) — so `W` is all such
    MCSs and `R = Accessible` picks out the accessible ones. -/
def Accessible {σ : Signature} (w w' : World σ) : Prop :=
  necVars w.ctx ⊆ w'.ctx.carrier ∧
  (∀ p ∈ w'.ctx.carrier, p.2 = VarType.Var → p ∈ necVars w.ctx ∪ posVars w.ctx) ∧
  boxedTheoryTransfers w w'

/-- The canonical **frame** for a chosen actual world `w₀`.  Carrier (`W`/`R`/`actual`) and the whole
    `interp` tower (`D`/`NecVar`/`Pos`/`NecDia` = denotable objects of the right type) are concrete;
    only `relInterp`/`funcInterp` need the `WFF`/`≈` structure and are stubbed. -/
noncomputable def canonicalFrame (σ : Signature) (w₀ : World σ) : RFrame σ where
  W := World σ
  actual := w₀
  R := Accessible
  D := fun w => DObj σ w.ctx .Var
  relInterp := fun _ _ _ => sorry   -- `r(args) ∈ w.theory` (needs the atomic-`WFF` interface)
  funcInterp := fun _ _ _ => sorry  -- `≈`-class of `f(args)` (needs the `≈` congruence)
  NecVar := fun k w => DObj σ w.ctx (boxPow (k + 1) .Var)
  Pos := fun U w => DObj σ w.ctx (.VTypeDia U)
  NecDia := fun k U w => DObj σ w.ctx (boxPow (k + 1) (.VTypeDia U))

/-! ## `RModel` ops — `necEval` / `posEval` (sections / realizations)

Per the design these **factor through the tautological environment**.  A necessary object is denoted
by a `□`-term; `necEval` peels its box at an accessible `w'` by re-reading the *unboxed* term there.
Cleanest case — a `□`-variable `⟨v, □V⟩`: accessibility transfers it unboxed
(`⟨v, V⟩ ∈ necVars w.ctx ⊆ w'.ctx`), so `necEval` returns the environment value `[var ⟨v, V⟩]` at
`w'`.  A `boxterm □s` returns `[s]` recontextualised (this *is* the box-β).  `posEval` dually: a
`◇`-object's realization set = the `⟨w', value⟩` pairs it points at.  (Like `necEvalLvl`, both
distribute over products structurally; only the `Var`/`◇` leaves touch the pointing.) -/

/-- `necEval` on the canonical tower (OUTLINE): peel a box off a denotable `□V`-object at `w`, giving
    a denotable `V`-object at an accessible `w'`.  Variable leaf = environment lookup at the unboxed
    variable; `boxterm` leaf = the body recontextualised.  Term-surgery + quotient-lift STUBBED. -/
noncomputable def canonNecEval (σ : Signature) (V : VarType) (w w' : World σ)
    (_h : Accessible w w') : DObj σ w.ctx V.VTypeBox → DObj σ w'.ctx V := sorry

/-- `posEval` on the canonical tower (OUTLINE): the realization set of a denotable `◇V`-object at `w`
    — the `⟨accessible w', denotable V-value⟩` pairs it points at.  STUBBED. -/
noncomputable def canonPosEval (σ : Signature) (V : VarType) (w : World σ) :
    DObj σ w.ctx V.VTypeDia →
      Set (Σ' w' : {w' : World σ // Accessible w w'}, DObj σ w'.1.ctx V) := sorry

/- **TARGET (pointed, environmented).**  Given a consistent `Γ`, produce a model `M`, an actual
   world `w₀`, and the tautological environment, with `Γ` true at `w₀`.  Schematically:

     `def canonical (σ) (Γ : Set Sentence) (hΓ : Consistent Γ) :`
     `    Σ (M : RModel σ) (w₀ : M.frame.W), (env-at-each-world) × (∀ φ ∈ Γ, ⟦φ⟧_{M, η w₀} = ⊤)`

   Fields to build: `frame` (W = `World`, `R` = `Accessible`, `D` = terms/≈, `NecVar`/`Pos`/`NecDia`
   = the *denotable* objects — NON-FULL), `necEval`/`posEval` (sections/realizations) with the key
   `nec_inj`/`pos_inj` (world-extensionality), the closure ops `funcNecStk`/`posLift`/`posStrength`
   (+ `_box`), and the tautological `η` (each var ↦ its own `≈`-class / downstream-pointer).  Needs
   `interpWFF` on `RModelB` (not yet built) for the `⟦φ⟧` and the Truth Lemma. -/

end QML.Canonical
