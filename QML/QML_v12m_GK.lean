import QML.QML_v12m_ProofSubst

/-!
# QML v12m — the sequent calculus GK

A cut-free sequent calculus for K (`docs/v12-metatheory-todo.md`, item 4): classical, two-sided,
multi-succedent, in **Kleene's G3 style** — every rule keeps its principal formula in the premise,
and the contexts are lists read through membership.  Weakening, exchange and contraction are then
free (`GK.weaken`), and the cut-elimination proof needs no inversion or contraction lemmas.

* *Connectives and quantifiers:* G3c.  `allR`/`exL` bind a fresh eigenvariable of any type as
  `all_intro`/`ex_elim` do (`WFF.bindFree`); `allL`/`exR` instantiate at a term of any type.
* *Equality:* Negri and von Plato's `ref` and `repl`, `repl` on **atoms** only, at base type.  ND's
  `eq_elim` over an arbitrary formula is a corollary (the slot is invisible in every view, so the
  modal cases are trivial).
* *Modal rules:* `□R` (from `Δ ⇒ φ` in the `□` view, `□Δ ⇒ □φ`) and `◇_xL` (from `ψ, Δ ⇒ Θ` in the
  `◇_x` view, `◇_x ψ, □Δ ⇒ ◇_x Θ`).  `◇` and `□_x` are notation (`¬□¬`, `¬◇_x¬`), so the
  symmetric rules of the paper — from `Δ ⇒ φ, Θ`, `□Δ ⇒ □φ, ◇Θ`; from `x : E; Δ, φ ⇒ Θ`,
  `x : ◇E; □Δ, ◇_x φ ⇒ ◇_x Θ` — follow by `¬L`/`¬R`.
* *Not primitive:* `pair_elim` (a substitution, `θ.pairSplit`) and `weak_ctx` (`mono`).

The derivability predicate is indexed by a **height bound**: `GK σ n Γ Δ Θ` says `Δ ⇒ Θ` over `Γ`
has a derivation of height at most `n` (an axiom at any height, a rule one above its premises).
Nothing here assumes K: the formers K lacks have no rules, so they behave as opaque formulas.
-/

namespace V12M

variable [ModalSys]

/-! ## Atoms and weight -/

/-- An atomic formula: a relation or a base-type equation, the formulas of the axioms and of
    `repl`. -/
def WFF.IsAtom {σ : Signature} {Γ : Ctx} {d : ℕ} : WFF σ Γ d → Prop
  | .atom _ => True
  | .eq _ _ => True
  | _ => False

/-- The **weight** of a formula: its connectives, quantifiers and modal operators.  Terms do not
    count, so instantiating a slot keeps it (`WFF.weight_instantiate`). -/
def WFF.weight {σ : Signature} : {Γ : Ctx} → {d : ℕ} → WFF σ Γ d → ℕ
  | _, _, .atom _ => 0
  | _, _, .eq _ _ => 0
  | _, _, .top => 0
  | _, _, .bot => 0
  | _, _, .and φ ψ => φ.weight + ψ.weight + 1
  | _, _, .or φ ψ => φ.weight + ψ.weight + 1
  | _, _, .imp φ ψ => φ.weight + ψ.weight + 1
  | _, _, .all _ φ => φ.weight + 1
  | _, _, .ex _ φ => φ.weight + 1
  | _, _, .box φ => φ.weight + 1
  | _, _, .dia _ _ φ => φ.weight + 1
  | _, _, .here _ _ _ => 0
  | _, _, .back _ _ _ _ => 0
  | _, _, .retS _ _ _ Φ => Φ.weight + 2
  | _, _, .retxS _ _ _ _ _ Φ => Φ.weight + 2
  | _, _, .link _ _ _ Φ => Φ.weight + 2
  | _, _, .linkx _ _ _ _ _ Φ => Φ.weight + 2

/-! ## The calculus -/

/-- ⭐**GK**: `GK σ n Γ Δ Θ` — the sequent `Δ ⇒ Θ` over `Γ` has a cut-free derivation of height at
    most `n`. -/
inductive GK (σ : Signature) : ℕ → (Γ : Ctx) → List (WFF σ Γ 0) → List (WFF σ Γ 0) → Prop where
  -- Axioms, at any height
  | ax {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (P : WFF σ Γ 0) (hP : P.IsAtom) :
      P ∈ Δ → P ∈ Θ → GK σ n Γ Δ Θ
  | botL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} : .bot ∈ Δ → GK σ n Γ Δ Θ
  | topR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} : .top ∈ Θ → GK σ n Γ Δ Θ
  -- Connectives
  | andL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      φ.and ψ ∈ Δ → GK σ n Γ (φ :: ψ :: Δ) Θ → GK σ (n + 1) Γ Δ Θ
  | andR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      φ.and ψ ∈ Θ → GK σ n Γ Δ (φ :: Θ) → GK σ n Γ Δ (ψ :: Θ) → GK σ (n + 1) Γ Δ Θ
  | orL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      φ.or ψ ∈ Δ → GK σ n Γ (φ :: Δ) Θ → GK σ n Γ (ψ :: Δ) Θ → GK σ (n + 1) Γ Δ Θ
  | orR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      φ.or ψ ∈ Θ → GK σ n Γ Δ (φ :: ψ :: Θ) → GK σ (n + 1) Γ Δ Θ
  | impL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      φ.imp ψ ∈ Δ → GK σ n Γ Δ (φ :: Θ) → GK σ n Γ (ψ :: Δ) Θ → GK σ (n + 1) Γ Δ Θ
  | impR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} :
      φ.imp ψ ∈ Θ → GK σ n Γ (φ :: Δ) (ψ :: Θ) → GK σ (n + 1) Γ Δ Θ
  -- Quantifiers
  | allL {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (T : VarType)
      {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) :
      .all T φ ∈ Δ → GK σ n Γ (WFF.instantiate Ctx.NoSlots.slots t φ :: Δ) Θ →
      GK σ (n + 1) Γ Δ Θ
  | allR {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} :
      .all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ) ∈ Θ →
      GK σ n (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T))
        (φ :: Θ.map (WFF.weaken hu.root T)) →
      GK σ (n + 1) Γ Δ Θ
  | exL {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} :
      .ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ) ∈ Δ →
      GK σ n (Γ.insert (.free u) T) (φ :: Δ.map (WFF.weaken hu.root T))
        (Θ.map (WFF.weaken hu.root T)) →
      GK σ (n + 1) Γ Δ Θ
  | exR {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (T : VarType)
      {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) :
      .ex T φ ∈ Θ → GK σ n Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ :: Θ) →
      GK σ (n + 1) Γ Δ Θ
  -- Equality, on atoms
  | ref {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (t : Term σ Γ .Var .var) :
      GK σ n Γ (.eq t t :: Δ) Θ → GK σ (n + 1) Γ Δ Θ
  | repl {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)}
      {P : WFF σ (Γ.insert (.bnd 0) .Var) 1} (hP : P.IsAtom) (t s : Term σ Γ .Var .var) :
      .eq t s ∈ Δ → WFF.instantiate Ctx.NoSlots.slots t P ∈ Δ →
      GK σ n Γ (WFF.instantiate Ctx.NoSlots.slots s P :: Δ) Θ → GK σ (n + 1) Γ Δ Θ
  -- Modal K
  /-- `□R`: from `Δ₁ ⇒ φ` in the `□` view, `□Δ₁ ⇒ □φ`, in any context. -/
  | boxR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {Δ₁ : List (WFF σ Γ.boxIn 0)}
      {φ : WFF σ Γ.boxIn 0} :
      WFF.box (Γ := Γ) φ ∈ Θ → (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) →
      GK σ n Γ.boxIn Δ₁ [φ] → GK σ (n + 1) Γ Δ Θ
  /-- `◇_xL`: from `ψ, Δ₁ ⇒ Θ₁` in the `◇_x` view, `◇_x ψ, □Δ₁ ⇒ ◇_x Θ₁`, in any context. -/
  | diaL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {ψ : WFF σ (Γ.diaIn x) 0}
      {Δ₁ : List (WFF σ Γ.boxIn 0)} {Θ₁ : List (WFF σ (Γ.diaIn x) 0)} :
      .dia x hx ψ ∈ Δ → (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) → (∀ χ ∈ Θ₁, .dia x hx χ ∈ Θ) →
      GK σ n (Γ.diaIn x) (ψ :: Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) Θ₁ →
      GK σ (n + 1) Γ Δ Θ

namespace GK

variable {σ : Signature}

/-! ## Height and weakening -/

/-- A height bound can be raised. -/
theorem mono_height {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (p : GK σ n Γ Δ Θ) :
    ∀ {m : ℕ}, n ≤ m → GK σ m Γ Δ Θ := by
  induction p with
  | ax P hP h₁ h₂ => exact fun _ => .ax P hP h₁ h₂
  | botL h => exact fun _ => .botL h
  | topR h => exact fun _ => .topR h
  | andL h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .andL h (ih (by omega))
  | andR h _ _ ih₁ ih₂ =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .andR h (ih₁ (by omega)) (ih₂ (by omega))
  | orL h _ _ ih₁ ih₂ =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .orL h (ih₁ (by omega)) (ih₂ (by omega))
  | orR h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .orR h (ih (by omega))
  | impL h _ _ ih₁ ih₂ =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .impL h (ih₁ (by omega)) (ih₂ (by omega))
  | impR h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .impR h (ih (by omega))
  | allL T t h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .allL T t h (ih (by omega))
  | allR u T hu h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .allR u T hu h (ih (by omega))
  | exL u T hu h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .exL u T hu h (ih (by omega))
  | exR T t h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .exR T t h (ih (by omega))
  | ref t _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .ref t (ih (by omega))
  | repl hP t s h₁ h₂ _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .repl hP t s h₁ h₂ (ih (by omega))
  | boxR h₁ h₂ _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .boxR h₁ h₂ (ih (by omega))
  | diaL x hx h₁ h₂ h₃ _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .diaL x hx h₁ h₂ h₃ (ih (by omega))

/-- ⭐**Weakening, exchange and contraction**, height-preserving: the contexts are read through
    membership, so any larger lists do. -/
theorem weaken {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (p : GK σ n Γ Δ Θ) :
    ∀ {Δ' Θ' : List (WFF σ Γ 0)}, Δ ⊆ Δ' → Θ ⊆ Θ' → GK σ n Γ Δ' Θ' := by
  induction p with
  | ax P hP h₁ h₂ => exact fun hΔ hΘ => .ax P hP (hΔ h₁) (hΘ h₂)
  | botL h => exact fun hΔ _ => .botL (hΔ h)
  | topR h => exact fun _ hΘ => .topR (hΘ h)
  | andL h _ ih =>
      exact fun hΔ hΘ => .andL (hΔ h) (ih (List.cons_subset_cons _ (List.cons_subset_cons _ hΔ)) hΘ)
  | andR h _ _ ih₁ ih₂ =>
      exact fun hΔ hΘ => .andR (hΘ h) (ih₁ hΔ (List.cons_subset_cons _ hΘ))
        (ih₂ hΔ (List.cons_subset_cons _ hΘ))
  | orL h _ _ ih₁ ih₂ =>
      exact fun hΔ hΘ => .orL (hΔ h) (ih₁ (List.cons_subset_cons _ hΔ) hΘ)
        (ih₂ (List.cons_subset_cons _ hΔ) hΘ)
  | orR h _ ih =>
      exact fun hΔ hΘ => .orR (hΘ h) (ih hΔ (List.cons_subset_cons _ (List.cons_subset_cons _ hΘ)))
  | impL h _ _ ih₁ ih₂ =>
      exact fun hΔ hΘ => .impL (hΔ h) (ih₁ hΔ (List.cons_subset_cons _ hΘ))
        (ih₂ (List.cons_subset_cons _ hΔ) hΘ)
  | impR h _ ih =>
      exact fun hΔ hΘ => .impR (hΘ h) (ih (List.cons_subset_cons _ hΔ) (List.cons_subset_cons _ hΘ))
  | allL T t h _ ih => exact fun hΔ hΘ => .allL T t (hΔ h) (ih (List.cons_subset_cons _ hΔ) hΘ)
  | allR u T hu h _ ih =>
      exact fun hΔ hΘ => .allR u T hu (hΘ h)
        (ih (List.map_subset _ hΔ) (List.cons_subset_cons _ (List.map_subset _ hΘ)))
  | exL u T hu h _ ih =>
      exact fun hΔ hΘ => .exL u T hu (hΔ h)
        (ih (List.cons_subset_cons _ (List.map_subset _ hΔ)) (List.map_subset _ hΘ))
  | exR T t h _ ih => exact fun hΔ hΘ => .exR T t (hΘ h) (ih hΔ (List.cons_subset_cons _ hΘ))
  | ref t _ ih => exact fun hΔ hΘ => .ref t (ih (List.cons_subset_cons _ hΔ) hΘ)
  | repl hP t s h₁ h₂ _ ih =>
      exact fun hΔ hΘ => .repl hP t s (hΔ h₁) (hΔ h₂) (ih (List.cons_subset_cons _ hΔ) hΘ)
  | boxR h₁ h₂ p _ => exact fun hΔ hΘ => .boxR (hΘ h₁) (fun χ hχ => hΔ (h₂ χ hχ)) p
  | diaL x hx h₁ h₂ h₃ p _ =>
      exact fun hΔ hΘ => .diaL x hx (hΔ h₁) (fun χ hχ => hΔ (h₂ χ hχ)) (fun χ hχ => hΘ (h₃ χ hχ)) p

end GK

end V12M
