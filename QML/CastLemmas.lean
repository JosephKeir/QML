import QML.QML_Full_v8

/-!
# Context-transport (cast) lemmas

`VarCtx` equalities aren't definitional (`insert` doesn't commute on the nose), so
reindexing a term/formula across equal contexts uses `h ▸ _`, which doesn't compute.
These lemmas let `simp` **push a transport through every constructor** down to the
leaves, and **cancel** inverse/trivial transports — so most `h ▸ …` bookkeeping is
discharged automatically instead of by hand.

All are `by subst h; rfl` (or proof irrelevance).  Tagged `@[simp]`; since the modal
proofs use `simp only`/`rw`, this only empowers plain `simp`, it doesn't disturb them.
-/

/-! ### Generic transport cancellation. -/

/-- Two inverse transports cancel. -/
@[simp] theorem eqRec_cancel {α : Sort*} {A B : α} {motive : α → Sort*}
    (h1 : A = B) (h2 : B = A) (x : motive B) : (h1 ▸ h2 ▸ x : motive B) = x := by
  subst h1; rfl

/-- A transport along a reflexive equality is the identity. -/
@[simp] theorem eqRec_refl {α : Sort*} {A : α} {motive : α → Sort*}
    (h : A = A) (x : motive A) : (h ▸ x : motive A) = x := by
  rw [proof_irrel h rfl]

/-! Per-type cancellation.  The generic `eqRec_cancel` above rarely fires under `rw`/`simp`
    because its `motive` is a metavariable; these concrete-motive versions do. -/

@[simp] theorem Term.cast_cancel {σ : Signature} {A B : VarCtx} {S : VarType}
    (h1 : A = B) (h2 : B = A) (t : Term σ B S) : (h1 ▸ h2 ▸ t) = t := by subst h1; rfl

@[simp] theorem Func.cast_cancel {σ : Signature} {A B : VarCtx} {N : ℕ}
    (h1 : A = B) (h2 : B = A) (f : Func σ B N) : (h1 ▸ h2 ▸ f) = f := by subst h1; rfl

@[simp] theorem Rel.cast_cancel {σ : Signature} {A B : VarCtx} {n : ℕ}
    (h1 : A = B) (h2 : B = A) (R : Rel σ B n) : (h1 ▸ h2 ▸ R) = R := by subst h1; rfl

@[simp] theorem WFF.cast_cancel {σ : Signature} {A B : VarCtx}
    (h1 : A = B) (h2 : B = A) (φ : WFF σ B) : (h1 ▸ h2 ▸ φ) = φ := by subst h1; rfl

/-! ### Subtype leaves (the `.var` index). -/

@[simp] theorem cast_subtype_val {A B : VarCtx} (h : A = B)
    (e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ A.1}) :
    ((h ▸ e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ B.1}) : VarSymb)
      = (e : VarSymb) := by subst h; rfl

/-! ### `Term` constructors. -/

@[simp] theorem Term.cast_var {σ : Signature} {A B : VarCtx} (h : A = B)
    (e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ A.1}) :
    (h ▸ (Term.var e : Term σ A .Var)) = Term.var (h ▸ e) := by subst h; rfl

@[simp] theorem Term.cast_func {σ : Signature} {A B : VarCtx} (h : A = B) (f : Func σ A 0) :
    (h ▸ (Term.func f : Term σ A .Var)) = Term.func (h ▸ f) := by subst h; rfl

@[simp] theorem Term.cast_unit {σ : Signature} {A B : VarCtx} (h : A = B) :
    (h ▸ (Term.unit : Term σ A .VTypeOne)) = Term.unit := by subst h; rfl

@[simp] theorem Term.cast_pair {σ : Signature} {A B : VarCtx} {S T : VarType} (h : A = B)
    (a : Term σ A S) (b : Term σ A T) :
    (h ▸ (Term.pair a b : Term σ A (S.VTypeProd T))) = Term.pair (h ▸ a) (h ▸ b) := by
  subst h; rfl

@[simp] theorem Term.cast_boxterm {σ : Signature} {W W' V_inner : VarCtx} {S_inner : VarType}
    (h : W = W') (tt : Term σ V_inner S_inner) (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    (h ▸ (Term.boxterm tt hsub hne : Term σ W S_inner.VTypeBox))
      = Term.boxterm tt (h ▸ hsub) (h ▸ hne) := by subst h; rfl

@[simp] theorem Term.cast_diaterm {σ : Signature} {W W' V_inner : VarCtx} {S_inner : VarType}
    (h : W = W') (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) S_inner)
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    (h ▸ (Term.diaterm xv hxv tt hsub hne : Term σ W S_inner.VTypeDia))
      = Term.diaterm xv hxv tt (h ▸ hsub) (h ▸ hne) := by subst h; rfl

/-! ### `Func` constructors. -/

@[simp] theorem Func.cast_F {σ : Signature} {A B : VarCtx} {N : ℕ} (h : A = B)
    (hr : {f // σ.funcArity f = N}) :
    (h ▸ (Func.F hr : Func σ A N)) = Func.F hr := by subst h; rfl

@[simp] theorem Func.cast_eval {σ : Signature} {A B : VarCtx} {N : ℕ} (h : A = B)
    (g : Func σ A (N + 1)) (t : Term σ A .Var) :
    (h ▸ (Func.eval g t : Func σ A N)) = Func.eval (h ▸ g) (h ▸ t) := by subst h; rfl

/-! ### `Rel` constructors. -/

@[simp] theorem Rel.cast_R {σ : Signature} {A B : VarCtx} {n : ℕ} (h : A = B)
    (hr : {r // σ.relArity r = n}) :
    (h ▸ (Rel.R hr : Rel σ A n)) = Rel.R hr := by subst h; rfl

@[simp] theorem Rel.cast_eval {σ : Signature} {A B : VarCtx} {n : ℕ} (h : A = B)
    (R' : Rel σ A (n + 1)) (t : Term σ A .Var) :
    (h ▸ (Rel.eval R' t : Rel σ A n)) = Rel.eval (h ▸ R') (h ▸ t) := by subst h; rfl

/-! ### `WFF` constructors (the pointwise, same-context ones). -/

@[simp] theorem WFF.cast_atom {σ : Signature} {A B : VarCtx} (h : A = B) (R : Rel σ A 0) :
    (h ▸ (WFF.atom R : WFF σ A)) = WFF.atom (h ▸ R) := by subst h; rfl

@[simp] theorem WFF.cast_top {σ : Signature} {A B : VarCtx} (h : A = B) :
    (h ▸ (WFF.top : WFF σ A)) = WFF.top := by subst h; rfl

@[simp] theorem WFF.cast_bot {σ : Signature} {A B : VarCtx} (h : A = B) :
    (h ▸ (WFF.bot : WFF σ A)) = WFF.bot := by subst h; rfl

@[simp] theorem WFF.cast_and {σ : Signature} {A B : VarCtx} (h : A = B) (φ ψ : WFF σ A) :
    (h ▸ (φ.and ψ : WFF σ A)) = (h ▸ φ).and (h ▸ ψ) := by subst h; rfl

@[simp] theorem WFF.cast_or {σ : Signature} {A B : VarCtx} (h : A = B) (φ ψ : WFF σ A) :
    (h ▸ (φ.or ψ : WFF σ A)) = (h ▸ φ).or (h ▸ ψ) := by subst h; rfl

@[simp] theorem WFF.cast_imp {σ : Signature} {A B : VarCtx} (h : A = B) (φ ψ : WFF σ A) :
    (h ▸ (φ.imp ψ : WFF σ A)) = (h ▸ φ).imp (h ▸ ψ) := by subst h; rfl

@[simp] theorem WFF.cast_eq {σ : Signature} {A B : VarCtx} {S : VarType} (h : A = B)
    (s t : Term σ A S) :
    (h ▸ (WFF.eq s t : WFF σ A)) = WFF.eq (h ▸ s) (h ▸ t) := by subst h; rfl
