import QML.QML_v12m_ProofSubst

/-!
# QML v12m — the sequent calculus GK

A cut-free sequent calculus for K, KD, K4 and KD4 (`docs/v12-metatheory-todo.md`, item 4):
classical, two-sided,
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
* *4 (weak):* each modal rule's premise also has the **4-copies** (`cp4`, `kp4`, empty without 4):
  a boxed hypothesis `□χ` is available one view further in as `□(shift χ)`, and a conclusion
  `◇_y θ` as `◇_{y.keep}(shift θ)` (`y.keep`'s extent lies inside `y`'s).  This is `four_box` and
  `four_dia` as sequent rules, K4's `□Γ, Γ ⇒ φ / □Γ ⇒ □φ` with witnesses.
* *D (weak):* `serial`, `□R` without a principal formula: from `Δ₁ ⇒` in the `□` view, `□Δ₁ ⇒`.
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
  | _, _, .dia _ _ φ => φ.weight + 2
  | _, _, .here _ _ _ _ => 0
  | _, _, .back _ _ _ _ => 0
  | _, _, .retS _ _ _ Φ => Φ.weight + 2
  | _, _, .retxS _ _ _ _ _ Φ => Φ.weight + 2
  | _, _, .link _ _ _ Φ => Φ.weight + 2
  | _, _, .linkx _ _ _ _ _ Φ => Φ.weight + 2
  | _, _, .optx _ _ _ _ φ => φ.weight + 1

/-! ## The 4-copies -/

/-- ⭐Under 4, a boxed hypothesis `□χ` one view further in: `□(shift χ)`.  Empty without 4. -/
def cp4 {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (Δ₁ : List (WFF σ Γ.boxIn 0)) :
    List (WFF σ Γ.boxIn 0) :=
  if hF : ModalSys.Four = true then
    Δ₁.map fun χ => WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots χ)
  else []

/-- A conclusion `◇_y θ` one view further in: `◇_{y.keep}(shift θ)`. -/
def WFF.keepDia {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) :
    WFF σ Γ 0 → List (WFF σ Γ.boxIn 0)
  | .dia y hy θ => [WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots θ)]
  | _ => []

/-- ⭐**The fold** (`Opt`, docs §12.33): a conclusion `◇_y θ` seen from inside the view, where `y`
    is a witness: `◇⁰_y θ`.  The bridge `◇_y = ◇ ◇⁰_y` as a copy. -/
def WFF.optDia {σ : Signature} {Γ : Ctx} (hO : ModalSys.Opt = true) :
    WFF σ Γ 0 → List (WFF σ Γ.boxIn 0)
  | .dia y hy θ => [WFF.optx hO .arrow y (hy.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩)
      (WFF.mono (hy.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) θ)]
  | _ => []

/-- ⭐The conclusions `◇_y θ` of a list, one view further in: under 4 their kept copies, with
    `Opt` their folds `◇⁰_y θ` (the two flags exclude each other), otherwise nothing. -/
def kp4 {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (L : List (WFF σ Γ 0)) : List (WFF σ Γ.boxIn 0) :=
  if hF : ModalSys.Four = true then L.flatMap (WFF.keepDia hF)
  else if hO : ModalSys.Opt = true then L.flatMap (WFF.optDia hO) else []

theorem cp4_of_not {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = false)
    (Δ₁ : List (WFF σ Γ.boxIn 0)) : cp4 Δ₁ = [] := by
  unfold cp4; rw [dif_neg (by simp [hF])]

theorem kp4_of_not {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = false)
    (hO : ModalSys.Opt = false) (L : List (WFF σ Γ 0)) : kp4 L = [] := by
  unfold kp4; rw [dif_neg (by simp [hF]), dif_neg (by simp [hO])]

theorem kp4_of_opt {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hO : ModalSys.Opt = true)
    (L : List (WFF σ Γ 0)) : kp4 L = L.flatMap (WFF.optDia hO) := by
  unfold kp4
  rw [dif_neg (fun hF => by rw [ModalSys.noOpt_of_Four hF] at hO; cases hO), dif_pos hO]

theorem kp4_nil {σ : Signature} {Γ : Ctx} [Γ.NoSlots] : kp4 ([] : List (WFF σ Γ 0)) = [] := by
  unfold kp4; split
  · rfl
  · split <;> rfl

theorem cp4_sub {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {Δ₁ Δ₂ : List (WFF σ Γ.boxIn 0)}
    (h : Δ₁ ⊆ Δ₂) : cp4 Δ₁ ⊆ cp4 Δ₂ := by
  unfold cp4; split
  · exact List.map_subset _ h
  · exact fun _ h => h

theorem kp4_sub {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {L₁ L₂ : List (WFF σ Γ 0)}
    (h : L₁ ⊆ L₂) : kp4 L₁ ⊆ kp4 L₂ := by
  unfold kp4; split
  · intro a ha
    obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
    exact List.mem_flatMap.mpr ⟨b, h hb, ha⟩
  · split
    · intro a ha
      obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
      exact List.mem_flatMap.mpr ⟨b, h hb, ha⟩
    · exact fun _ h => h

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
  -- Modal: K, with 4's copies
  /-- `□R`: from `Δ₁, □(shift Δ₁) ⇒ φ, ◇_{y.keep}(shift L)` in the `□` view (the copies only
      under 4), `□Δ₁ ⇒ □φ, L`, in any context. -/
  | boxR {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} {Δ₁ : List (WFF σ Γ.boxIn 0)}
      {φ : WFF σ Γ.boxIn 0} {L : List (WFF σ Γ 0)} :
      WFF.box (Γ := Γ) φ ∈ Θ → (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) → L ⊆ Θ →
      GK σ n Γ.boxIn (Δ₁ ++ cp4 Δ₁) (φ :: kp4 L) → GK σ (n + 1) Γ Δ Θ
  /-- `◇_xL`: from `ψ, Δ₁, □(shift Δ₁) ⇒ Θ₁, ◇_{y.keep}(shift L)` in the `◇_x` view (the copies
      only under 4), `◇_x ψ, □Δ₁ ⇒ ◇_x Θ₁, L`, in any context. -/
  | diaL {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (x : VarSymb)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {ψ : WFF σ (Γ.diaIn x) 0}
      {Δ₁ : List (WFF σ Γ.boxIn 0)} {Θ₁ : List (WFF σ (Γ.diaIn x) 0)} {L : List (WFF σ Γ 0)} :
      .dia x hx ψ ∈ Δ → (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) → (∀ χ ∈ Θ₁, .dia x hx χ ∈ Θ) →
      L ⊆ Θ →
      GK σ n (Γ.diaIn x) (ψ :: (Δ₁ ++ cp4 Δ₁).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
        (Θ₁ ++ (kp4 L).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) →
      GK σ (n + 1) Γ Δ Θ
  /-- `serial` (D): from `Δ₁, □(shift Δ₁) ⇒ ◇_{y.keep}(shift L)` in the `□` view, `□Δ₁ ⇒ L`. -/
  | serial {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hD : ModalSys.D = true)
      {Δ₁ : List (WFF σ Γ.boxIn 0)} {L : List (WFF σ Γ 0)} :
      (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) → L ⊆ Θ →
      GK σ n Γ.boxIn (Δ₁ ++ cp4 Δ₁) (kp4 L) → GK σ (n + 1) Γ Δ Θ
  -- The witness views (`Opt`, docs §12.33)
  /-- `optL`: from `ψ, Δ ⇒ Θ` in the view of the witness `y` (of either kind), `◇⁰_y ψ, Δ ⇒ Θ`.
      The whole sequent goes into the view: no world is crossed. -/
  | optL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (hO : ModalSys.Opt = true) (κ : WitKind)
      (y : VarSymb) (hy : ∃ X, Γ.witK κ y = some X) {ψ : WFF σ (Γ.optInK κ y) 0} :
      .optx hO κ y hy ψ ∈ Δ →
      GK σ n (Γ.optInK κ y) (ψ :: Δ.map (WFF.mono (Ctx.le_optInK Γ κ y)))
        (Θ.map (WFF.mono (Ctx.le_optInK Γ κ y))) →
      GK σ (n + 1) Γ Δ Θ
  /-- `reopenR`: where `y` is already opened, `◇⁰_y χ` on the right is `χ` (`Proof.opt_reopen`).
      After `optL` every `◇⁰_y` formula of the sequent has this form. -/
  | reopenR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (hO : ModalSys.Opt = true) (κ : WitKind)
      (y : VarSymb) (hy : ∃ X, Γ.witK κ y = some X ∧ Γ (.step y κ.step) = some X)
      {χ : WFF σ Γ 0} :
      .optx hO κ y (hy.imp fun _ h => h.1) (WFF.mono (Ctx.le_optInK Γ κ y) χ) ∈ Θ →
      GK σ n Γ Δ (χ :: Θ) → GK σ (n + 1) Γ Δ Θ

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
  | boxR h₁ h₂ h₃ _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .boxR h₁ h₂ h₃ (ih (by omega))
  | diaL x hx h₁ h₂ h₃ h₄ _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .diaL x hx h₁ h₂ h₃ h₄ (ih (by omega))
  | serial hD h₂ h₃ _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .serial hD h₂ h₃ (ih (by omega))
  | optL hO κ y hy h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .optL hO κ y hy h (ih (by omega))
  | reopenR hO κ y hy h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .reopenR hO κ y hy h (ih (by omega))

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
  | boxR h₁ h₂ h₃ p _ =>
      exact fun hΔ hΘ => .boxR (hΘ h₁) (fun χ hχ => hΔ (h₂ χ hχ)) (h₃.trans hΘ) p
  | diaL x hx h₁ h₂ h₃ h₄ p _ =>
      exact fun hΔ hΘ => .diaL x hx (hΔ h₁) (fun χ hχ => hΔ (h₂ χ hχ)) (fun χ hχ => hΘ (h₃ χ hχ))
        (h₄.trans hΘ) p
  | serial hD h₂ h₃ p _ =>
      exact fun hΔ hΘ => .serial hD (fun χ hχ => hΔ (h₂ χ hχ)) (h₃.trans hΘ) p
  | optL hO κ y hy h _ ih =>
      exact fun hΔ hΘ => .optL hO κ y hy (hΔ h)
        (ih (List.cons_subset_cons _ (List.map_subset _ hΔ)) (List.map_subset _ hΘ))
  | reopenR hO κ y hy h _ ih =>
      exact fun hΔ hΘ => .reopenR hO κ y hy (hΘ h) (ih hΔ (List.cons_subset_cons _ hΘ))

end GK

end V12M
