import QML.QML_v12m_GKNTree

/-!
# QML v12m — the nested calculus `GKN` for K and KD

A **tree sequent** over the end sequent's context `Γ₀` and a tree `D` is a pair of lists of
formulas **at nodes**, `⟨τ, φ⟩` with `φ` over `D.ctxAt Γ₀ τ` (docs §12.49, representation (C)).

* The local rules are `GK`'s at any node.  An eigenvariable is **born** at its node
  (`Tree.addBirth`), tree-fresh, and the whole sequent is weakened node-wise (`Seq.mono`).
* ⭐The modal rules act along edges, as in the prototype `KBNestedProto`:
  * `boxR`: `□φ` on the right at `τ` makes a **vacant** `□`-child with `φ`;
  * `diaL`: `◇_x ψ` on the left at `τ` makes a vacant `◇_x`-child with `ψ`;
  * `boxL`: `□χ` on the left at `τ` puts `χ` at any child of `τ`;
  * `diaR`: `◇_x θ` on the right at `τ` puts `θ` at any `◇_x`-child of `τ`;
  * `serial` (D): a vacant `□`-child with nothing in it.
  A rule moving a formula into a child takes the inclusion of the parent's view in the child's
  context as an argument (a proposition, so any proof will do); `Tree` lemmas supply it.
* Height-bounded, G3-style (principal formulas stay), as `GK`.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace GKN

variable {σ : Signature}

/-- A formula at a node of the tree. -/
abbrev LF (σ : Signature) (Γ₀ : Ctx) (D : Tree) : Type := Σ τ : Lab, WFF σ (D.ctxAt Γ₀ τ) 0

/-- A tree sequent's side. -/
abbrev Seq (σ : Signature) (Γ₀ : Ctx) (D : Tree) : Type := List (LF σ Γ₀ D)

/-- ⭐**Node-wise weakening** of a side along node-wise context inclusions. -/
def Seq.mono {Γ₀ : Ctx} {D D' : Tree} (h : ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ τ))
    (L : Seq σ Γ₀ D) : Seq σ Γ₀ D' :=
  L.map fun p => ⟨p.1, WFF.mono (h p.1) p.2⟩

/-- A node is **vacant**: no edge, birth or formula at it or below it. -/
structure Vacant {Γ₀ : Ctx} (D : Tree) (c : Lab) (Δ Θ : Seq σ Γ₀ D) : Prop where
  edge : ∀ τ, c <:+ τ → D.edge τ = none
  births : ∀ b ∈ D.births, ¬ c <:+ b.1
  left : ∀ p ∈ Δ, ¬ c <:+ p.1
  right : ∀ p ∈ Θ, ¬ c <:+ p.1

end GKN

open GKN

/-- ⭐**GKN**: `GKN σ Γ₀ n D Δ Θ` — the tree sequent `Δ ⇒ Θ` on the tree `D` over `Γ₀` has a
    cut-free derivation of height at most `n`. -/
inductive GKN (σ : Signature) (Γ₀ : Ctx) : ℕ → (D : Tree) → Seq σ Γ₀ D → Seq σ Γ₀ D → Prop
    where
  -- Axioms, at any height and any node
  | ax {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      (P : WFF σ (D.ctxAt Γ₀ τ) 0) (hP : P.IsAtom) :
      ⟨τ, P⟩ ∈ Δ → ⟨τ, P⟩ ∈ Θ → GKN σ Γ₀ n D Δ Θ
  | botL {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab) :
      ⟨τ, .bot⟩ ∈ Δ → GKN σ Γ₀ n D Δ Θ
  | topR {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab) :
      ⟨τ, .top⟩ ∈ Θ → GKN σ Γ₀ n D Δ Θ
  -- Connectives, at a node
  | andL {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} :
      ⟨τ, φ.and ψ⟩ ∈ Δ → GKN σ Γ₀ n D (⟨τ, φ⟩ :: ⟨τ, ψ⟩ :: Δ) Θ → GKN σ Γ₀ (n + 1) D Δ Θ
  | andR {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} :
      ⟨τ, φ.and ψ⟩ ∈ Θ → GKN σ Γ₀ n D Δ (⟨τ, φ⟩ :: Θ) → GKN σ Γ₀ n D Δ (⟨τ, ψ⟩ :: Θ) →
      GKN σ Γ₀ (n + 1) D Δ Θ
  | orL {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} :
      ⟨τ, φ.or ψ⟩ ∈ Δ → GKN σ Γ₀ n D (⟨τ, φ⟩ :: Δ) Θ → GKN σ Γ₀ n D (⟨τ, ψ⟩ :: Δ) Θ →
      GKN σ Γ₀ (n + 1) D Δ Θ
  | orR {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} :
      ⟨τ, φ.or ψ⟩ ∈ Θ → GKN σ Γ₀ n D Δ (⟨τ, φ⟩ :: ⟨τ, ψ⟩ :: Θ) → GKN σ Γ₀ (n + 1) D Δ Θ
  | impL {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} :
      ⟨τ, φ.imp ψ⟩ ∈ Δ → GKN σ Γ₀ n D Δ (⟨τ, φ⟩ :: Θ) → GKN σ Γ₀ n D (⟨τ, ψ⟩ :: Δ) Θ →
      GKN σ Γ₀ (n + 1) D Δ Θ
  | impR {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} :
      ⟨τ, φ.imp ψ⟩ ∈ Θ → GKN σ Γ₀ n D (⟨τ, φ⟩ :: Δ) (⟨τ, ψ⟩ :: Θ) → GKN σ Γ₀ (n + 1) D Δ Θ
  -- Quantifiers, at a node; an eigenvariable is born there
  | allL {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0) (T : VarType)
      {φ : WFF σ ((D.ctxAt Γ₀ τ).insert (.bnd 0) T) 1} {a : Ann T}
      (t : Term σ (D.ctxAt Γ₀ τ) T a) :
      ⟨τ, .all T φ⟩ ∈ Δ → GKN σ Γ₀ n D (⟨τ, WFF.instantiate hs t φ⟩ :: Δ) Θ →
      GKN σ Γ₀ (n + 1) D Δ Θ
  | allR {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0) (u : ℕ) (T : VarType) (hu : D.Fresh Γ₀ (.free u))
      {φ : WFF σ ((D.ctxAt Γ₀ τ).insert (.free u) T) 0}
      (hle : ((D.ctxAt Γ₀ τ).insert (.free u) T).Le ((D.addBirth τ (.free u) T).ctxAt Γ₀ τ)) :
      ⟨τ, .all T (WFF.bindFree u (hu.at τ) hs T φ)⟩ ∈ Θ →
      GKN σ Γ₀ n (D.addBirth τ (.free u) T) (Seq.mono (Tree.ctxAt_addBirth hu τ T) Δ)
        (⟨τ, WFF.mono hle φ⟩ :: Seq.mono (Tree.ctxAt_addBirth hu τ T) Θ) →
      GKN σ Γ₀ (n + 1) D Δ Θ
  | exL {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0) (u : ℕ) (T : VarType) (hu : D.Fresh Γ₀ (.free u))
      {φ : WFF σ ((D.ctxAt Γ₀ τ).insert (.free u) T) 0}
      (hle : ((D.ctxAt Γ₀ τ).insert (.free u) T).Le ((D.addBirth τ (.free u) T).ctxAt Γ₀ τ)) :
      ⟨τ, .ex T (WFF.bindFree u (hu.at τ) hs T φ)⟩ ∈ Δ →
      GKN σ Γ₀ n (D.addBirth τ (.free u) T)
        (⟨τ, WFF.mono hle φ⟩ :: Seq.mono (Tree.ctxAt_addBirth hu τ T) Δ)
        (Seq.mono (Tree.ctxAt_addBirth hu τ T) Θ) →
      GKN σ Γ₀ (n + 1) D Δ Θ
  | exR {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0) (T : VarType)
      {φ : WFF σ ((D.ctxAt Γ₀ τ).insert (.bnd 0) T) 1} {a : Ann T}
      (t : Term σ (D.ctxAt Γ₀ τ) T a) :
      ⟨τ, .ex T φ⟩ ∈ Θ → GKN σ Γ₀ n D Δ (⟨τ, WFF.instantiate hs t φ⟩ :: Θ) →
      GKN σ Γ₀ (n + 1) D Δ Θ
  -- Equality, on atoms, at a node
  | ref {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      (t : Term σ (D.ctxAt Γ₀ τ) .Var .var) :
      GKN σ Γ₀ n D (⟨τ, .eq t t⟩ :: Δ) Θ → GKN σ Γ₀ (n + 1) D Δ Θ
  | repl {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab)
      (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0)
      {P : WFF σ ((D.ctxAt Γ₀ τ).insert (.bnd 0) .Var) 1} (hP : P.IsAtom)
      (t s : Term σ (D.ctxAt Γ₀ τ) .Var .var) :
      ⟨τ, .eq t s⟩ ∈ Δ → ⟨τ, WFF.instantiate hs t P⟩ ∈ Δ →
      GKN σ Γ₀ n D (⟨τ, WFF.instantiate hs s P⟩ :: Δ) Θ → GKN σ Γ₀ (n + 1) D Δ Θ
  -- Modal: along edges
  /-- `boxR`: `□φ` on the right at `τ` makes a vacant `□`-child `k :: τ` with `φ` on the right. -/
  | boxR {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab) (k : ℕ)
      {φ : WFF σ (D.ctxAt Γ₀ τ).boxIn 0} (hv : Vacant D (k :: τ) Δ Θ)
      (hle : (D.ctxAt Γ₀ τ).boxIn.Le ((D.addEdge (k :: τ) .box).ctxAt Γ₀ (k :: τ))) :
      ⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ ∈ Θ →
      GKN σ Γ₀ n (D.addEdge (k :: τ) .box)
        (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) .box) Δ)
        (⟨k :: τ, WFF.mono hle φ⟩ ::
          Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) .box) Θ) →
      GKN σ Γ₀ (n + 1) D Δ Θ
  /-- `diaL`: `◇_x ψ` on the left at `τ` makes a vacant `◇_x`-child `k :: τ` with `ψ`. -/
  | diaL {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab) (k : ℕ) (x : VarSymb)
      (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X))
      {ψ : WFF σ ((D.ctxAt Γ₀ τ).diaIn x) 0} (hv : Vacant D (k :: τ) Δ Θ)
      (hle : ((D.ctxAt Γ₀ τ).diaIn x).Le ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ (k :: τ))) :
      ⟨τ, .dia x hx ψ⟩ ∈ Δ →
      GKN σ Γ₀ n (D.addEdge (k :: τ) (.dia x))
        (⟨k :: τ, WFF.mono hle ψ⟩ ::
          Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) (.dia x)) Δ)
        (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) (.dia x)) Θ) →
      GKN σ Γ₀ (n + 1) D Δ Θ
  /-- `boxL`: `□χ` on the left at `τ` puts `χ` on the left at a child of `τ`. -/
  | boxL {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab) (k : ℕ) (e : EdgeKind)
      {χ : WFF σ (D.ctxAt Γ₀ τ).boxIn 0} (he : D.edge (k :: τ) = some e)
      (hle : (D.ctxAt Γ₀ τ).boxIn.Le (D.ctxAt Γ₀ (k :: τ))) :
      ⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) χ⟩ ∈ Δ →
      GKN σ Γ₀ n D (⟨k :: τ, WFF.mono hle χ⟩ :: Δ) Θ → GKN σ Γ₀ (n + 1) D Δ Θ
  /-- `diaR`: `◇_x θ` on the right at `τ` puts `θ` on the right at a `◇_x`-child of `τ`. -/
  | diaR {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (τ : Lab) (k : ℕ) (x : VarSymb)
      (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X))
      {θ : WFF σ ((D.ctxAt Γ₀ τ).diaIn x) 0} (he : D.edge (k :: τ) = some (.dia x))
      (hle : ((D.ctxAt Γ₀ τ).diaIn x).Le (D.ctxAt Γ₀ (k :: τ))) :
      ⟨τ, .dia x hx θ⟩ ∈ Θ →
      GKN σ Γ₀ n D Δ (⟨k :: τ, WFF.mono hle θ⟩ :: Θ) → GKN σ Γ₀ (n + 1) D Δ Θ
  /-- `serial` (D): a vacant `□`-child with nothing in it. -/
  | serial {n : ℕ} {D : Tree} {Δ Θ : Seq σ Γ₀ D} (hD : ModalSys.D = true)
      (τ : Lab) (k : ℕ) (hv : Vacant D (k :: τ) Δ Θ) :
      GKN σ Γ₀ n (D.addEdge (k :: τ) .box)
        (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) .box) Δ)
        (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) .box) Θ) →
      GKN σ Γ₀ (n + 1) D Δ Θ

namespace GKN

theorem Vacant.birthsAt {Γ₀ : Ctx} {D : Tree} {c : Lab} {Δ Θ : Seq σ Γ₀ D}
    (hv : Vacant D c Δ Θ) : D.birthsAt c = [] := by
  unfold Tree.birthsAt
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro b hb
  simp only [decide_eq_true_eq]
  intro he
  exact hv.births b hb (by rw [he])

end GKN

/-- A height bound can be raised. -/
theorem GKN.mono_height {n : ℕ} {Γ₀ : Ctx} {D : Tree} {Δ Θ : Seq σ Γ₀ D}
    (p : GKN σ Γ₀ n D Δ Θ) : ∀ {m : ℕ}, n ≤ m → GKN σ Γ₀ m D Δ Θ := by
  induction p with
  | ax τ P hP h₁ h₂ => exact fun _ => .ax τ P hP h₁ h₂
  | botL τ h => exact fun _ => .botL τ h
  | topR τ h => exact fun _ => .topR τ h
  | andL τ h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .andL τ h (ih (by omega))
  | andR τ h _ _ ih₁ ih₂ =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .andR τ h (ih₁ (by omega)) (ih₂ (by omega))
  | orL τ h _ _ ih₁ ih₂ =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .orL τ h (ih₁ (by omega)) (ih₂ (by omega))
  | orR τ h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .orR τ h (ih (by omega))
  | impL τ h _ _ ih₁ ih₂ =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .impL τ h (ih₁ (by omega)) (ih₂ (by omega))
  | impR τ h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .impR τ h (ih (by omega))
  | allL τ hs T t h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .allL τ hs T t h (ih (by omega))
  | allR τ hs u T hu hle h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .allR τ hs u T hu hle h (ih (by omega))
  | exL τ hs u T hu hle h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .exL τ hs u T hu hle h (ih (by omega))
  | exR τ hs T t h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .exR τ hs T t h (ih (by omega))
  | ref τ t _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .ref τ t (ih (by omega))
  | repl τ hs hP t s h₁ h₂ _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .repl τ hs hP t s h₁ h₂ (ih (by omega))
  | boxR τ k hv hle h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .boxR τ k hv hle h (ih (by omega))
  | diaL τ k x hx hv hle h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .diaL τ k x hx hv hle h (ih (by omega))
  | boxL τ k e he hle h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .boxL τ k e he hle h (ih (by omega))
  | diaR τ k x hx he hle h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .diaR τ k x hx he hle h (ih (by omega))
  | serial hD τ k hv _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .serial hD τ k hv (ih (by omega))

end V12M
