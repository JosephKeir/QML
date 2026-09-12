import QML.QML_v12_Subst
import QML.QML_v12_Presented

/-!
# QML v12 — the proof system

Classical natural deduction.  The hypotheses form a LIST, with explicit weakening, contraction and
exchange; `Proof.lookup` / `Proof.ofSubset` and the tactics `by_hyp` / `hyps_from` handle them in
practice, so the structural rules never need to be applied by hand.

* **Proofs live at binder depth 0**: no rule changes the depth, so it is fixed once and for all.
  The slot side conditions are the type class `Ctx.NoSlots`, found by instance search.
* **Binder-introducing rules take a free variable** `u` (fresh at its root: the `fresh` tactic),
  and the rule binds it to the slot (`WFF.bindFree`).  **Binder-eliminating rules** substitute for
  the slot (`WFF.instantiate`), with a term of ANY annotation: quantifiers range over plain types.
* **Equality** is primitive only at base type; compound equality is `eqRec`.
* **Pair elimination** renames the user's components `u₁ u₂` to `z.fst`, `z.snd`.
* **Modal K** rules state their premises in the `□` / `◇_x` views of the conclusion's context.
-/

namespace V12

inductive Proof (σ : Signature) : (Γ : Ctx) → List (WFF σ Γ 0) → WFF σ Γ 0 → Type where
  -- Structural
  | ax {Γ : Ctx} (φ : WFF σ Γ 0) : Proof σ Γ [φ] φ
  | weak {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (ψ : WFF σ Γ 0) :
      Proof σ Γ Δ φ → Proof σ Γ (ψ :: Δ) φ
  | contr {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ (ψ :: ψ :: Δ) φ → Proof σ Γ (ψ :: Δ) φ
  | exch {Γ : Ctx} (Δ₁ Δ₂ : List (WFF σ Γ 0)) {φ ψ χ : WFF σ Γ 0} :
      Proof σ Γ (Δ₁ ++ ψ :: χ :: Δ₂) φ → Proof σ Γ (Δ₁ ++ χ :: ψ :: Δ₂) φ
  | weak_ctx {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) :
      Proof σ Γ Δ φ →
      Proof σ (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T)) (φ.weaken hu.root T)
  -- Conjunction
  | and_intro {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ Δ φ → Proof σ Γ Δ ψ → Proof σ Γ Δ (φ.and ψ)
  | and_elim_l {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ Δ (φ.and ψ) → Proof σ Γ Δ φ
  | and_elim_r {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ Δ (φ.and ψ) → Proof σ Γ Δ ψ
  -- Disjunction
  | or_intro_l {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (ψ : WFF σ Γ 0) :
      Proof σ Γ Δ φ → Proof σ Γ Δ (φ.or ψ)
  | or_intro_r {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (φ : WFF σ Γ 0) {ψ : WFF σ Γ 0} :
      Proof σ Γ Δ ψ → Proof σ Γ Δ (φ.or ψ)
  | or_elim {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ χ : WFF σ Γ 0} :
      Proof σ Γ Δ (φ.or ψ) → Proof σ Γ (φ :: Δ) χ → Proof σ Γ (ψ :: Δ) χ → Proof σ Γ Δ χ
  -- Implication
  | imp_intro {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ (φ :: Δ) ψ → Proof σ Γ Δ (φ.imp ψ)
  | imp_elim {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      Proof σ Γ Δ (φ.imp ψ) → Proof σ Γ Δ φ → Proof σ Γ Δ ψ
  -- Truth and falsity
  | top_intro {Γ : Ctx} {Δ : List (WFF σ Γ 0)} : Proof σ Γ Δ .top
  | bot_elim {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (φ : WFF σ Γ 0) :
      Proof σ Γ Δ .bot → Proof σ Γ Δ φ
  -- Classical logic
  | lem {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (φ : WFF σ Γ 0) : Proof σ Γ Δ (φ.or φ.neg)
  -- ⭐Universal quantifier: the eigenvariable `u` is free in the subproof and bound to the slot.
  | all_intro {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} :
      Proof σ (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T)) φ →
      Proof σ Γ Δ (.all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ))
  -- Elimination substitutes a term of any annotation for the slot.
  | all_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (T : VarType)
      {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) :
      Proof σ Γ Δ (.all T φ) → Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)
  -- Existential quantifier
  | ex_intro {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (T : VarType)
      {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) :
      Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ) → Proof σ Γ Δ (.ex T φ)
  | ex_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} {ψ : WFF σ Γ 0} :
      Proof σ Γ Δ (.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ)) →
      Proof σ (Γ.insert (.free u) T) (φ :: Δ.map (WFF.weaken hu.root T)) (ψ.weaken hu.root T) →
      Proof σ Γ Δ ψ
  -- ⭐Equality, primitive only at base type (compound equality is `eqRec`).
  | eq_intro {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (t : Term σ Γ .Var .var) : Proof σ Γ Δ (.eq t t)
  -- The formula `φ` has its hole at the slot `bnd 0`, as for `all_elim`.
  | eq_elim {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} {φ : WFF σ (Γ.insert (.bnd 0) .Var) 1}
      (t s : Term σ Γ .Var .var) :
      Proof σ Γ Δ (.eq t s) → Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ) →
      Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots s φ)
  -- ⭐Pairing: the user's components `u₁ u₂` become `z.fst`, `z.snd`.
  | pair_elim {Γ : Ctx} [Γ.NoSlots] (A B : VarType) (u₁ u₂ z : ℕ) (hu : u₁ ≠ u₂) (hz₁ : z ≠ u₁)
      (hu₁ : Γ.RootFresh (.free u₁)) (hu₂ : Γ.RootFresh (.free u₂))
      (hzf : Γ.RootFresh (.free z))
      {Δ : List (WFF σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) 0)}
      {φ : WFF σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) 0} :
      Proof σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) Δ φ →
      Proof σ (Γ.insert (.free z) (.VTypeProd A B))
        (Δ.map (WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Ctx.NoSlots.slots A B))
        (WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf Ctx.NoSlots.slots A B φ)
  -- Modal K
  | K_box {Γ : Ctx} {Δ : List (WFF σ Γ.boxIn 0)} {φ : WFF σ Γ.boxIn 0} :
      Proof σ Γ.boxIn Δ φ → Proof σ Γ (Δ.map fun ψ => WFF.box (Γ := Γ) ψ) (.box φ)
  /-- From `ψ, Δ₂, Δ₁ ⊢ φ` inside `◇_x` conclude `◇_x ψ, □_x Δ₂, □ Δ₁ ⊢ ◇_x φ`: `Δ₁` is
      witness-free (plain `□`), `Δ₂` may mention the witness content `x.dia`. -/
  | K_dia {Γ : Ctx} (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
      {Δ₁ : List (WFF σ Γ.boxIn 0)} {Δ₂ : List (WFF σ (Γ.diaIn x) 0)}
      {φ ψ : WFF σ (Γ.diaIn x) 0} :
      Proof σ (Γ.diaIn x) (ψ :: (Δ₂ ++ Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))) φ →
      Proof σ Γ (.dia x hx ψ :: (Δ₂.map (WFF.boxx x hx) ++ Δ₁.map fun χ => WFF.box (Γ := Γ) χ))
        (.dia x hx φ)
  | dia_bot {Γ : Ctx} {Δ : List (WFF σ Γ 0)} (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
      Proof σ Γ Δ (.dia x hx .bot) → Proof σ Γ Δ .bot

/-! ## Handling hypotheses -/

namespace Proof

variable {σ : Signature} {Γ : Ctx}

/-- Weaken by a whole list at the front. -/
def weakenAll : (pre : List (WFF σ Γ 0)) → {Δ : List (WFF σ Γ 0)} → {φ : WFF σ Γ 0} →
    Proof σ Γ Δ φ → Proof σ Γ (pre ++ Δ) φ
  | [], _, _, p => p
  | ψ :: pre, _, _, p => Proof.weak ψ (weakenAll pre p)

/-- Bring the hypothesis after `pre` to the front, by exchanges. -/
def rise {φ : WFF σ Γ 0} : (outer pre : List (WFF σ Γ 0)) → (x : WFF σ Γ 0) →
    (rest : List (WFF σ Γ 0)) →
    Proof σ Γ (outer ++ (pre ++ x :: rest)) φ → Proof σ Γ (outer ++ x :: (pre ++ rest)) φ
  | _, [], _, _, p => p
  | outer, y :: pre, x, rest, p => by
      have p₁ : Proof σ Γ ((outer ++ [y]) ++ (pre ++ x :: rest)) φ := by
        rw [List.append_assoc]
        exact p
      have p₂ := rise (outer ++ [y]) pre x rest p₁
      rw [List.append_assoc] at p₂
      exact Proof.exch outer (pre ++ rest) p₂

/-- ⭐A hypothesis proves itself. -/
def lookup : {Δ : List (WFF σ Γ 0)} → {x : WFF σ Γ 0} → x ∈ Δ → Proof σ Γ Δ x
  | [], _, h => absurd h List.not_mem_nil
  | y :: Δ, x, h =>
      if hxy : x = y then by
        subst hxy
        have p : Proof σ Γ (Δ ++ [x]) x := weakenAll Δ (Proof.ax x)
        have p' := rise [] Δ x [] p
        simpa using p'
      else Proof.weak y (lookup ((List.mem_cons.mp h).resolve_left hxy))

/-- ⭐Move a proof to any hypothesis list containing its hypotheses. -/
def ofSubset : {Δ Δ' : List (WFF σ Γ 0)} → {φ : WFF σ Γ 0} → (∀ ψ ∈ Δ, ψ ∈ Δ') →
    Proof σ Γ Δ φ → Proof σ Γ Δ' φ
  | [], Δ', _, _, p => by
      have p' := weakenAll Δ' p
      rw [List.append_nil] at p'
      exact p'
  | x :: Δ, _, _, h, p =>
      Proof.imp_elim (ofSubset (fun ψ hψ => h ψ (List.mem_cons_of_mem x hψ)) (Proof.imp_intro p))
        (lookup (h x List.mem_cons_self))

end Proof

/-- Close `Proof σ Γ Δ φ` when `φ` is among the hypotheses. -/
macro "by_hyp" : tactic => `(tactic| exact Proof.lookup (by first | decide | simp))

/-- Close `Proof σ Γ Δ' φ` from `p : Proof σ Γ Δ φ` when every hypothesis of `Δ` is in `Δ'`. -/
macro "hyps_from " p:term : tactic =>
  `(tactic| exact Proof.ofSubset (by first | decide | simp) $p)

/-- Discharge `Γ.RootFresh (.free u)` for presented contexts (`u` beyond the bound), contexts built
    from `Ctx.empty` by adding variables and taking views, or from a freshness hypothesis. -/
macro "fresh" : tactic =>
  `(tactic| repeat (first
    | exact Ctx.RootFresh.empty _
    | assumption
    | exact Ctx.Presented.fresh _ (by decide)
    | refine Ctx.RootFresh.insert_ne ?_ (by decide) _
    | refine Ctx.RootFresh.boxIn ?_
    | refine Ctx.RootFresh.diaIn ?_ _))

/-! ## Examples -/

namespace ProofCheck

variable {σ : Signature} {Γ : Ctx}

example (φ ψ : WFF σ Γ 0) : Proof σ Γ [ψ, φ] φ := by by_hyp

example (φ ψ χ : WFF σ Γ 0) (p : Proof σ Γ [φ, ψ] χ) : Proof σ Γ [ψ, χ, φ, φ] χ := by
  hyps_from p

/-- `φ ∧ ψ ⊢ ψ ∧ φ`. -/
example (φ ψ : WFF σ Γ 0) : Proof σ Γ [φ.and ψ] (ψ.and φ) :=
  .and_intro (.and_elim_r (.ax _)) (.and_elim_l (.ax _))

/-- `⊢ □(φ → φ)`. -/
example (φ : WFF σ Γ.boxIn 0) : Proof σ Γ [] (.box (φ.imp φ)) :=
  .K_box (Δ := []) (.imp_intro (.ax φ))

/-- `□φ, □ψ ⊢ □(φ ∧ ψ)`. -/
example (φ ψ : WFF σ Γ.boxIn 0) : Proof σ Γ [.box φ, .box ψ] (.box (φ.and ψ)) :=
  .K_box (Δ := [φ, ψ]) (.and_intro (by by_hyp) (by by_hyp))

example : (Ctx.empty.insert (.free 3) .Var).boxIn.RootFresh (.free 7) := by fresh

end ProofCheck

end V12
