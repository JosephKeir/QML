import QML.QML_v12m_WFF

/-!
# QML v12m — countably many formulas

Over a signature with countably many function and relation symbols, there are countably many
terms and formulas over any context.  Contexts are not countable (they are functions), and they
are indices of every constructor, so the `Countable` deriving handler does not apply: formulas are
encoded by hand into a tree of natural numbers, forgetting the contexts, and the encoding is
injective at each fixed context.
-/

namespace V12M

deriving instance Countable for VarType
deriving instance Countable for Root
deriving instance Countable for Step
deriving instance Countable for VarSymb

/-- Codes: binary trees with natural-number tags. -/
inductive Code where
  | leaf (n : ℕ)
  | node (tag : ℕ) (a b : Code)
deriving Countable

/-- A fixed injection of a countable type into `ℕ`. -/
noncomputable def natCode {α : Type} [Countable α] : α → ℕ :=
  Classical.choose (Countable.exists_injective_nat α)

theorem natCode_injective {α : Type} [Countable α] : Function.Injective (natCode (α := α)) :=
  Classical.choose_spec (Countable.exists_injective_nat α)

/-- Annotations, encoded: an annotation is determined by its type and its witness indices. -/
noncomputable def Ann.code : {T : VarType} → Ann T → Code
  | _, .var => .leaf 0
  | _, .one => .leaf 1
  | _, .prod a b => .node 0 a.code b.code
  | _, .box a => .node 1 a.code (.leaf 0)
  | _, .dia i a => .node 2 (.leaf (natCode i)) a.code

theorem Ann.code_injective : ∀ {T : VarType}, Function.Injective (Ann.code (T := T))
  | .Var, .var, .var, _ => rfl
  | .VTypeOne, .one, .one, _ => rfl
  | .VTypeProd _ _, .prod a b, .prod a' b', h => by
      simp only [Ann.code, Code.node.injEq, true_and] at h
      rw [Ann.code_injective h.1, Ann.code_injective h.2]
  | .VTypeBox _, .box a, .box a', h => by
      simp only [Ann.code, Code.node.injEq, true_and, and_true] at h
      rw [Ann.code_injective h]
  | .VTypeDia _, .dia i a, .dia i' a', h => by
      simp only [Ann.code, Code.node.injEq, Code.leaf.injEq, true_and] at h
      rw [natCode_injective h.1, Ann.code_injective h.2]

instance (T : VarType) : Countable (Ann T) := Ann.code_injective.countable

variable [ModalSys]

section Terms

variable {σ : Signature} [Countable σ.FuncSyms]

mutual
  noncomputable def Func.code : {Γ : Ctx} → {n : ℕ} → Func σ Γ n → Code
    | _, _, .F f => .node 0 (.leaf (natCode f.1)) (.leaf 0)
    | _, _, .eval g t => .node 1 (Func.code g) (Term.code t)

  noncomputable def Term.code : {Γ : Ctx} → {T : VarType} → {a : Ann T} → Term σ Γ T a → Code
    | _, _, _, .var v _ => .node 2 (.leaf (natCode v)) (.leaf 0)
    | _, _, _, .func f => .node 3 (Func.code f) (.leaf 0)
    | _, _, _, .unit => .node 4 (.leaf 0) (.leaf 0)
    | _, _, _, .pair s t => .node 5 (Term.code s) (Term.code t)
    | _, _, _, .boxtm t => .node 6 (Term.code t) (.leaf 0)
    | _, _, _, .diatm x _ t => .node 7 (.leaf (natCode x)) (Term.code t)
end

mutual
  theorem Func.code_inj : {Γ : Ctx} → {n : ℕ} → (f g : Func σ Γ n) → f.code = g.code → f = g
    | _, _, .F f, .F g, h => by
        simp only [Func.code, Code.node.injEq, Code.leaf.injEq, and_true, true_and] at h
        have := natCode_injective h
        congr 1
        exact Subtype.ext this
    | _, _, .F _, .eval _ _, h => by simp [Func.code] at h
    | _, _, .eval _ _, .F _, h => by simp [Func.code] at h
    | _, _, .eval g t, .eval g' t', h => by
        simp only [Func.code, Code.node.injEq, true_and] at h
        rw [Func.code_inj g g' h.1, Term.code_inj t t' h.2]

  theorem Term.code_inj : {Γ : Ctx} → {T : VarType} → {a : Ann T} → (t s : Term σ Γ T a) →
      t.code = s.code → t = s
    | _, _, _, .var v _, .var v' _, h => by
        simp only [Term.code, Code.node.injEq, Code.leaf.injEq, and_true, true_and] at h
        cases natCode_injective h
        rfl
    | _, _, _, .var _ _, .func _, h => by simp [Term.code] at h
    | _, _, _, .func _, .var _ _, h => by simp [Term.code] at h
    | _, _, _, .func f, .func f', h => by
        simp only [Term.code, Code.node.injEq, and_true, true_and] at h
        rw [Func.code_inj f f' h]
    | _, _, _, .unit, .unit, _ => rfl
    | _, _, _, .pair s t, .pair s' t', h => by
        simp only [Term.code, Code.node.injEq, true_and] at h
        rw [Term.code_inj s s' h.1, Term.code_inj t t' h.2]
    | _, _, _, .boxtm t, .boxtm t', h => by
        simp only [Term.code, Code.node.injEq, and_true, true_and] at h
        rw [Term.code_inj t t' h]
    | _, _, _, .diatm _ _ t, .diatm _ _ t', h => by
        simp only [Term.code, Code.node.injEq, true_and] at h
        rw [Term.code_inj t t' h]
end

instance (Γ : Ctx) (T : VarType) (a : Ann T) : Countable (Term σ Γ T a) :=
  Function.Injective.countable (f := Term.code) (fun t s h => Term.code_inj t s h)

end Terms

section Formulas

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]

noncomputable def Rel.code : {Γ : Ctx} → {n : ℕ} → Rel σ Γ n → Code
  | _, _, .R r => .node 8 (.leaf (natCode r.1)) (.leaf 0)
  | _, _, .eval ρ t => .node 9 (Rel.code ρ) (Term.code t)

noncomputable def WFF.code : {Γ : Ctx} → {d : ℕ} → WFF σ Γ d → Code
  | _, _, .atom ρ => .node 10 (Rel.code ρ) (.leaf 0)
  | _, _, .eq t s => .node 11 (Term.code t) (Term.code s)
  | _, _, .top => .node 12 (.leaf 0) (.leaf 0)
  | _, _, .bot => .node 13 (.leaf 0) (.leaf 0)
  | _, _, .and φ ψ => .node 14 (WFF.code φ) (WFF.code ψ)
  | _, _, .or φ ψ => .node 15 (WFF.code φ) (WFF.code ψ)
  | _, _, .imp φ ψ => .node 16 (WFF.code φ) (WFF.code ψ)
  | _, _, .all T φ => .node 17 (.leaf (natCode T)) (WFF.code φ)
  | _, _, .ex T φ => .node 18 (.leaf (natCode T)) (WFF.code φ)
  | _, _, .box φ => .node 19 (WFF.code φ) (.leaf 0)
  | _, _, .dia x _ φ => .node 20 (.leaf (natCode x)) (WFF.code φ)
  | _, _, .here _ (b := b) s t => .node 21 (Ann.code b) (.node 0 (Term.code s) (Term.code t))
  | _, _, .diaEq (A := A) (b := b) s (b' := b') s' =>
      .node 22 (.node 0 (.leaf (natCode A)) (.node 0 (Ann.code b) (Ann.code b')))
        (.node 0 (Term.code s) (Term.code s'))

theorem Rel.code_inj : {Γ : Ctx} → {n : ℕ} → (ρ ρ' : Rel σ Γ n) → ρ.code = ρ'.code → ρ = ρ'
  | _, _, .R r, .R r', h => by
      simp only [Rel.code, Code.node.injEq, Code.leaf.injEq, and_true, true_and] at h
      congr 1
      exact Subtype.ext (natCode_injective h)
  | _, _, .R _, .eval _ _, h => by simp [Rel.code] at h
  | _, _, .eval _ _, .R _, h => by simp [Rel.code] at h
  | _, _, .eval ρ t, .eval ρ' t', h => by
      simp only [Rel.code, Code.node.injEq, true_and] at h
      rw [Rel.code_inj ρ ρ' h.1, Term.code_inj t t' h.2]

theorem WFF.code_inj {Γ : Ctx} {d : ℕ} (φ ψ : WFF σ Γ d) (h : φ.code = ψ.code) : φ = ψ := by
  revert ψ
  induction φ with
  | atom ρ =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Nat.reduceEqDiff, false_and, true_and,
        and_true] at h
      rw [Rel.code_inj _ _ h]
  | eq t s =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Nat.reduceEqDiff, false_and,
        true_and] at h
      rw [Term.code_inj _ _ h.1, Term.code_inj _ _ h.2]
  | top =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Code.leaf.injEq, Nat.reduceEqDiff,
        false_and, and_true] at h
      rfl
  | bot =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Code.leaf.injEq, Nat.reduceEqDiff,
        false_and, and_true] at h
      rfl
  | and φ₁ φ₂ ih₁ ih₂ =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Nat.reduceEqDiff, false_and,
        true_and] at h
      rw [ih₁ _ h.1, ih₂ _ h.2]
  | or φ₁ φ₂ ih₁ ih₂ =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Nat.reduceEqDiff, false_and,
        true_and] at h
      rw [ih₁ _ h.1, ih₂ _ h.2]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Nat.reduceEqDiff, false_and,
        true_and] at h
      rw [ih₁ _ h.1, ih₂ _ h.2]
  | all T φ ih =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Code.leaf.injEq, Nat.reduceEqDiff,
        false_and, true_and] at h
      obtain ⟨h₁, h₂⟩ := h
      cases natCode_injective h₁
      rw [ih _ h₂]
  | ex T φ ih =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Code.leaf.injEq, Nat.reduceEqDiff,
        false_and, true_and] at h
      obtain ⟨h₁, h₂⟩ := h
      cases natCode_injective h₁
      rw [ih _ h₂]
  | box φ ih =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Nat.reduceEqDiff, false_and, true_and,
        and_true] at h
      rw [ih _ h]
  | dia x hx φ ih =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Code.leaf.injEq, Nat.reduceEqDiff,
        false_and, true_and] at h
      obtain ⟨h₁, h₂⟩ := h
      cases natCode_injective h₁
      rw [ih _ h₂]
  | here hT s t =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Nat.reduceEqDiff,
        false_and, true_and] at h
      obtain ⟨hb, hs, ht⟩ := h
      cases Ann.code_injective hb
      rw [Term.code_inj s _ hs, Term.code_inj t _ ht]
  | diaEq s s' =>
      intro ψ h
      cases ψ <;> simp only [WFF.code, Code.node.injEq, Code.leaf.injEq, Nat.reduceEqDiff,
        false_and, true_and] at h
      obtain ⟨⟨hA, hb, hb'⟩, hs, hs'⟩ := h
      cases natCode_injective hA
      cases Ann.code_injective hb
      cases Ann.code_injective hb'
      rw [Term.code_inj s _ hs, Term.code_inj s' _ hs']

instance (Γ : Ctx) (d : ℕ) : Countable (WFF σ Γ d) :=
  Function.Injective.countable (f := WFF.code) (fun φ ψ h => WFF.code_inj φ ψ h)

end Formulas

end V12M
