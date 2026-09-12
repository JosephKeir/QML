import QML.QML_v12_Subst

/-!
# QML v12 — the proof system

Classical natural deduction, following v11 rule for rule.  The hypotheses form a LIST, with
explicit weakening, contraction and exchange; `Proof.lookup` / `Proof.ofSubset` and the tactics
`by_hyp` / `hyps_from` handle them in practice, so the structural rules never need to be applied by
hand.

* **Contexts** are v12 contexts; formulas carry their binder depth `d`.
* **Binder-introducing rules take a free variable** `u` (fresh at its root), and the rule binds it
  to the slot `bnd d` (`WFF.bindFree`).  **Binder-eliminating rules** substitute for the slot
  (`WFF.instantiate`), with a term of ANY annotation: quantifiers range over plain types.
* **Equality** is primitive only at base type; compound equality is `eqRec`.
* **Pair elimination** renames the user's components `u₁ u₂` to `z.fst`, `z.snd`.
* **Modal K** rules state their premises in the `□` / `◇_x` views of the conclusion's context.
-/

namespace V12

inductive Proof (σ : Signature) : (Γ : Ctx) → (d : ℕ) → List (WFF σ Γ d) → WFF σ Γ d → Type where
  -- Structural
  | ax {Γ : Ctx} {d : ℕ} (φ : WFF σ Γ d) : Proof σ Γ d [φ] φ
  | weak {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ : WFF σ Γ d} (ψ : WFF σ Γ d) :
      Proof σ Γ d Δ φ → Proof σ Γ d (ψ :: Δ) φ
  | contr {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ ψ : WFF σ Γ d} :
      Proof σ Γ d (ψ :: ψ :: Δ) φ → Proof σ Γ d (ψ :: Δ) φ
  | exch {Γ : Ctx} {d : ℕ} (Δ₁ Δ₂ : List (WFF σ Γ d)) {φ ψ χ : WFF σ Γ d} :
      Proof σ Γ d (Δ₁ ++ ψ :: χ :: Δ₂) φ → Proof σ Γ d (Δ₁ ++ χ :: ψ :: Δ₂) φ
  | weak_ctx {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ : WFF σ Γ d} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) :
      Proof σ Γ d Δ φ →
      Proof σ (Γ.insert (.free u) T) d (Δ.map (WFF.weaken hu.root T)) (φ.weaken hu.root T)
  -- Conjunction
  | and_intro {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ ψ : WFF σ Γ d} :
      Proof σ Γ d Δ φ → Proof σ Γ d Δ ψ → Proof σ Γ d Δ (φ.and ψ)
  | and_elim_l {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ ψ : WFF σ Γ d} :
      Proof σ Γ d Δ (φ.and ψ) → Proof σ Γ d Δ φ
  | and_elim_r {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ ψ : WFF σ Γ d} :
      Proof σ Γ d Δ (φ.and ψ) → Proof σ Γ d Δ ψ
  -- Disjunction
  | or_intro_l {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ : WFF σ Γ d} (ψ : WFF σ Γ d) :
      Proof σ Γ d Δ φ → Proof σ Γ d Δ (φ.or ψ)
  | or_intro_r {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (φ : WFF σ Γ d) {ψ : WFF σ Γ d} :
      Proof σ Γ d Δ ψ → Proof σ Γ d Δ (φ.or ψ)
  | or_elim {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ ψ χ : WFF σ Γ d} :
      Proof σ Γ d Δ (φ.or ψ) → Proof σ Γ d (φ :: Δ) χ → Proof σ Γ d (ψ :: Δ) χ →
      Proof σ Γ d Δ χ
  -- Implication
  | imp_intro {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ ψ : WFF σ Γ d} :
      Proof σ Γ d (φ :: Δ) ψ → Proof σ Γ d Δ (φ.imp ψ)
  | imp_elim {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} {φ ψ : WFF σ Γ d} :
      Proof σ Γ d Δ (φ.imp ψ) → Proof σ Γ d Δ φ → Proof σ Γ d Δ ψ
  -- Truth and falsity
  | top_intro {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} : Proof σ Γ d Δ .top
  | bot_elim {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (φ : WFF σ Γ d) :
      Proof σ Γ d Δ .bot → Proof σ Γ d Δ φ
  -- Classical logic
  | lem {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (φ : WFF σ Γ d) : Proof σ Γ d Δ (φ.or φ.neg)
  -- ⭐Universal quantifier: the eigenvariable `u` is free in the subproof and bound to the slot.
  | all_intro {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom d) {φ : WFF σ (Γ.insert (.free u) T) d} :
      Proof σ (Γ.insert (.free u) T) d (Δ.map (WFF.weaken hu.root T)) φ →
      Proof σ Γ d Δ (.all T (WFF.bindFree u hu hs T φ))
  -- Elimination substitutes a term of any annotation for the slot.
  | all_elim {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (T : VarType) (hs : Γ.SlotsFrom d)
      {φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)} {a : Ann T} (t : Term σ Γ T a) :
      Proof σ Γ d Δ (.all T φ) → Proof σ Γ d Δ (WFF.instantiate hs t φ)
  -- Existential quantifier
  | ex_intro {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (T : VarType) (hs : Γ.SlotsFrom d)
      {φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)} {a : Ann T} (t : Term σ Γ T a) :
      Proof σ Γ d Δ (WFF.instantiate hs t φ) → Proof σ Γ d Δ (.ex T φ)
  | ex_elim {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom d) {φ : WFF σ (Γ.insert (.free u) T) d}
      {ψ : WFF σ Γ d} :
      Proof σ Γ d Δ (.ex T (WFF.bindFree u hu hs T φ)) →
      Proof σ (Γ.insert (.free u) T) d (φ :: Δ.map (WFF.weaken hu.root T))
        (ψ.weaken hu.root T) →
      Proof σ Γ d Δ ψ
  -- ⭐Equality, primitive only at base type (compound equality is `eqRec`).
  | eq_intro {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (t : Term σ Γ .Var .var) :
      Proof σ Γ d Δ (.eq t t)
  | eq_elim {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (u : ℕ) (hu : Γ.RootFresh (.free u))
      (hs : Γ.SlotsFrom d) {φ : WFF σ (Γ.insert (.free u) .Var) d} (t s : Term σ Γ .Var .var) :
      Proof σ Γ d Δ (.eq t s) → Proof σ Γ d Δ (WFF.substFree u hu hs t φ) →
      Proof σ Γ d Δ (WFF.substFree u hu hs s φ)
  -- ⭐Pairing: the user's components `u₁ u₂` become `z.fst`, `z.snd`.
  | pair_elim {Γ : Ctx} {d : ℕ} (A B : VarType) (u₁ u₂ z : ℕ) (hu : u₁ ≠ u₂) (hz₁ : z ≠ u₁)
      (hu₁ : Γ.RootFresh (.free u₁)) (hu₂ : Γ.RootFresh (.free u₂))
      (hzf : Γ.RootFresh (.free z)) (hs : Γ.SlotsFrom d)
      {Δ : List (WFF σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) d)}
      {φ : WFF σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) d} :
      Proof σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) d Δ φ →
      Proof σ (Γ.insert (.free z) (.VTypeProd A B)) d
        (Δ.map (WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf hs A B))
        (WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf hs A B φ)
  -- Modal K
  | K_box {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ.boxIn d)} {φ : WFF σ Γ.boxIn d} :
      Proof σ Γ.boxIn d Δ φ → Proof σ Γ d (Δ.map fun ψ => WFF.box (Γ := Γ) ψ) (.box φ)
  /-- From `ψ, Δ₂, Δ₁ ⊢ φ` inside `◇_x` conclude `◇_x ψ, □_x Δ₂, □ Δ₁ ⊢ ◇_x φ`: `Δ₁` is
      witness-free (plain `□`), `Δ₂` may mention the witness content `x.dia`. -/
  | K_dia {Γ : Ctx} {d : ℕ} (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
      {Δ₁ : List (WFF σ Γ.boxIn d)} {Δ₂ : List (WFF σ (Γ.diaIn x) d)}
      {φ ψ : WFF σ (Γ.diaIn x) d} :
      Proof σ (Γ.diaIn x) d (ψ :: (Δ₂ ++ Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))) φ →
      Proof σ Γ d (.dia x hx ψ :: (Δ₂.map (WFF.boxx x hx) ++ Δ₁.map fun χ => WFF.box (Γ := Γ) χ))
        (.dia x hx φ)
  | dia_bot {Γ : Ctx} {d : ℕ} {Δ : List (WFF σ Γ d)} (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
      Proof σ Γ d Δ (.dia x hx .bot) → Proof σ Γ d Δ .bot

/-! ## Handling hypotheses -/

namespace Proof

variable {σ : Signature} {Γ : Ctx} {d : ℕ}

/-- Weaken by a whole list at the front. -/
def weakenAll : (pre : List (WFF σ Γ d)) → {Δ : List (WFF σ Γ d)} → {φ : WFF σ Γ d} →
    Proof σ Γ d Δ φ → Proof σ Γ d (pre ++ Δ) φ
  | [], _, _, p => p
  | ψ :: pre, _, _, p => Proof.weak ψ (weakenAll pre p)

/-- Bring the hypothesis after `pre` to the front, by exchanges. -/
def rise {φ : WFF σ Γ d} : (outer pre : List (WFF σ Γ d)) → (x : WFF σ Γ d) →
    (rest : List (WFF σ Γ d)) →
    Proof σ Γ d (outer ++ (pre ++ x :: rest)) φ → Proof σ Γ d (outer ++ x :: (pre ++ rest)) φ
  | _, [], _, _, p => p
  | outer, y :: pre, x, rest, p => by
      have p₁ : Proof σ Γ d ((outer ++ [y]) ++ (pre ++ x :: rest)) φ := by
        rw [List.append_assoc]
        exact p
      have p₂ := rise (outer ++ [y]) pre x rest p₁
      rw [List.append_assoc] at p₂
      exact Proof.exch outer (pre ++ rest) p₂

/-- ⭐A hypothesis proves itself. -/
def lookup : {Δ : List (WFF σ Γ d)} → {x : WFF σ Γ d} → x ∈ Δ → Proof σ Γ d Δ x
  | [], _, h => absurd h List.not_mem_nil
  | y :: Δ, x, h =>
      if hxy : x = y then by
        subst hxy
        have p : Proof σ Γ d (Δ ++ [x]) x := weakenAll Δ (Proof.ax x)
        have p' := rise [] Δ x [] p
        simpa using p'
      else Proof.weak y (lookup ((List.mem_cons.mp h).resolve_left hxy))

/-- ⭐Move a proof to any hypothesis list containing its hypotheses. -/
def ofSubset : {Δ Δ' : List (WFF σ Γ d)} → {φ : WFF σ Γ d} → (∀ ψ ∈ Δ, ψ ∈ Δ') →
    Proof σ Γ d Δ φ → Proof σ Γ d Δ' φ
  | [], Δ', _, _, p => by
      have p' := weakenAll Δ' p
      rw [List.append_nil] at p'
      exact p'
  | x :: Δ, _, _, h, p =>
      Proof.imp_elim (ofSubset (fun ψ hψ => h ψ (List.mem_cons_of_mem x hψ)) (Proof.imp_intro p))
        (lookup (h x List.mem_cons_self))

end Proof

/-- Close `Proof σ Γ d Δ φ` when `φ` is among the hypotheses. -/
macro "by_hyp" : tactic => `(tactic| exact Proof.lookup (by first | decide | simp))

/-- Close `Proof σ Γ d Δ' φ` from `p : Proof σ Γ d Δ φ` when every hypothesis of `Δ` is in `Δ'`. -/
macro "hyps_from " p:term : tactic =>
  `(tactic| exact Proof.ofSubset (by first | decide | simp) $p)

/-! ## Examples -/

namespace ProofCheck

variable {σ : Signature} {Γ : Ctx} {d : ℕ}

example (φ ψ : WFF σ Γ d) : Proof σ Γ d [ψ, φ] φ := by by_hyp

example (φ ψ χ : WFF σ Γ d) (p : Proof σ Γ d [φ, ψ] χ) : Proof σ Γ d [ψ, χ, φ, φ] χ := by
  hyps_from p

/-- `φ ∧ ψ ⊢ ψ ∧ φ`. -/
example (φ ψ : WFF σ Γ d) : Proof σ Γ d [φ.and ψ] (ψ.and φ) :=
  .and_intro (.and_elim_r (.ax _)) (.and_elim_l (.ax _))

/-- `⊢ □(φ → φ)`. -/
example (φ : WFF σ Γ.boxIn d) : Proof σ Γ d [] (.box (φ.imp φ)) :=
  .K_box (Δ := []) (.imp_intro (.ax φ))

/-- `□φ, □ψ ⊢ □(φ ∧ ψ)`. -/
example (φ ψ : WFF σ Γ.boxIn d) : Proof σ Γ d [.box φ, .box ψ] (.box (φ.and ψ)) :=
  .K_box (Δ := [φ, ψ]) (.and_intro (by by_hyp) (by by_hyp))

end ProofCheck

end V12
