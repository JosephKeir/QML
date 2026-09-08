import QML.QML_v11_Terms

/-!
# QML v11 — Relation symbols

`Rel σ V n` is an `n`-ary relation symbol partially applied to `Var`-typed terms over `V`.

Structurally this is the same as v10: `Rel` has **no binders** — `eval` only takes `Term σ V .Var`,
which is why `Rel.pairElim` never gets stuck in the way `WFF.pairElim` does.  So nothing here
changes under the v11 naming discipline except what falls away:

* **no `Rel.boundVars`.**  v10 carries it purely to state `new ∉ Rel.boundVars R` when renaming.
  Capture is impossible in v11, so the condition — and the function — are gone.
* **no bespoke `Rel.rename`.**  Renaming is `Rel.mapCtx` along `CtxBij.renameOne`, as for terms.
-/

/-! ## The inductive -/

inductive Rel (σ : Signature) (V : VarCtx) : ℕ → Type where
  | R    : {r : σ.RelSyms // σ.relArity r = n} → Rel σ V n
  | eval : Rel σ V (Nat.succ n) → Term σ V .Var → Rel σ V n
  deriving DecidableEq

/-! ## Rebuilding along a context bijection -/

/-- Rebuild a `Rel` along a context bijection.  No binder arms, so this is a plain recursion —
    the interesting work all happens inside `Term.mapCtx`. -/
def Rel.mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') :
    {n : ℕ} → Rel σ V n → Rel σ V' n
  | _, .R rs      => .R rs
  | _, .eval R' t => .eval (Rel.mapCtx m R') (Term.mapCtx m t)

/-- Rename one free variable in a `Rel`, by rebuilding along the swap bijection. -/
def Rel.rename' {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    {n : ℕ} (R : Rel σ (VarCtx_insert ⟨old, T⟩ V hold) n) :
    Rel σ (VarCtx_insert ⟨new, T⟩ V hnew) n :=
  Rel.mapCtx (CtxBij.renameOne old new T hold hnew) R

/-! ## Measures

Mirroring `Func`'s: `numNodes` for the `ctx_rest` termination measure, `diaCount` for the modal-β
one.  Both delegate to the `Term` versions through `eval`. -/

def Rel.numNodes {σ : Signature} {V : VarCtx} : {n : ℕ} → Rel σ V n → ℕ
  | _, .R _       => 1
  | _, .eval R' t => 1 + Rel.numNodes R' + Term.numNodes t

def Rel.diaCount {σ : Signature} {V : VarCtx} : {n : ℕ} → Rel σ V n → ℕ
  | _, .R _       => 0
  | _, .eval R' t => Rel.diaCount R' + Term.diaCount t
