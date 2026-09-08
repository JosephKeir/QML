import QML.QML_v11_TermSubst

/-!
# QML v11 — Relation symbols

`Rel σ V n` is an `n`-ary relation symbol partially applied to `Var`-typed terms over `V`.

Structurally this is the same as v10: `Rel` has **no binders** — `eval` only takes `Term σ V .Var`,
which is why `Rel.pairElim` never gets stuck in the way `WFF.pairElim` does.  Every operation here
is therefore a plain traversal that delegates to the corresponding `Term` one; all the interesting
work happens a level down.  What falls away relative to v10:

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

Mirroring `Func`'s: `numNodes` for the `WFF.pairElim` termination measure, `diaCount` for the
modal-β one.  Both delegate to the `Term` versions through `eval`. -/

def Rel.numNodes {σ : Signature} {V : VarCtx} : {n : ℕ} → Rel σ V n → ℕ
  | _, .R _       => 1
  | _, .eval R' t => 1 + Rel.numNodes R' + Term.numNodes t

def Rel.diaCount {σ : Signature} {V : VarCtx} : {n : ℕ} → Rel σ V n → ℕ
  | _, .R _       => 0
  | _, .eval R' t => Rel.diaCount R' + Term.diaCount t

theorem Rel.numNodes_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') :
    ∀ {n : ℕ} (R : Rel σ V n), Rel.numNodes (Rel.mapCtx m R) = Rel.numNodes R
  | _, .R _       => rfl
  | _, .eval R' t => by
      simp only [Rel.mapCtx, Rel.numNodes, Rel.numNodes_mapCtx m R', Term.numNodes_mapCtx m t]

theorem Rel.diaCount_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') :
    ∀ {n : ℕ} (R : Rel σ V n), Rel.diaCount (Rel.mapCtx m R) = Rel.diaCount R
  | _, .R _       => rfl
  | _, .eval R' t => by
      simp only [Rel.mapCtx, Rel.diaCount, Rel.diaCount_mapCtx m R', Term.diaCount_mapCtx m t]

theorem Rel.diaCount_rename' {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    {n : ℕ} (R : Rel σ (VarCtx_insert ⟨old, T⟩ V hold) n) :
    Rel.diaCount (Rel.rename' old new T hold hnew R) = Rel.diaCount R :=
  Rel.diaCount_mapCtx _ R

/-! ## Pair-elim distribution -/

/-- Move a `Rel` from the SPLIT context to the JOINED one.  Unlike `WFF.pairElim`, this never gets
    stuck: `eval` only takes `Var`-typed terms, so every arm descends. -/
def Rel.pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
    (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) :
    {n : ℕ} → Rel σ W₁ n → Rel σ W₂ n
  | _, .R rs      => .R rs
  | _, .eval R' t => .eval (Rel.pairElim T₁ T₂ z hz w₁eq w₂eq R')
                           (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t)

theorem Rel.diaCount_pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
    (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) :
    ∀ {n : ℕ} (R : Rel σ W₁ n),
      Rel.diaCount (Rel.pairElim T₁ T₂ z hz w₁eq w₂eq R) = Rel.diaCount R
  | _, .R _       => rfl
  | _, .eval R' t => by
      simp only [Rel.pairElim, Rel.diaCount,
        Rel.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq R',
        Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq t]

/-! ## Weakening -/

def Rel.ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) :
    {n : ℕ} → Rel σ V n → Rel σ (VarCtx_insert ⟨u.toVar, T⟩ V hu) n
  | _, .R rs      => .R rs
  | _, .eval R' t => .eval (Rel.ctx_extU u T hu R') (Term.ctx_extU u T hu t)

theorem Rel.diaCount_ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) :
    ∀ {n : ℕ} (R : Rel σ V n), Rel.diaCount (Rel.ctx_extU u T hu R) = Rel.diaCount R
  | _, .R _       => rfl
  | _, .eval R' t => by
      simp only [Rel.ctx_extU, Rel.diaCount, Rel.diaCount_ctx_extU u T hu R',
        Term.diaCount_ctx_extU u T hu t]

/-- Weakening by an ARBITRARY symbol: as for terms, `ctx_extU` under a fresh user name followed by
    `rename'`. -/
def Rel.ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) {n : ℕ} (R : Rel σ V n) :
    Rel σ (VarCtx_insert xv V hv) n :=
  Rel.rename' (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar xv.1 xv.2
    (UserSymb.fresh_not_mem _) hv
    (Rel.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) xv.2 (UserSymb.fresh_not_mem _) R)

theorem Rel.diaCount_ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) {n : ℕ} (R : Rel σ V n) :
    Rel.diaCount (Rel.ctx_ext xv hv R) = Rel.diaCount R := by
  rw [Rel.ctx_ext, Rel.diaCount_rename', Rel.diaCount_ctx_extU]

/-! ## Unpairing and substitution -/

def Rel.unpair {σ : Signature} {V : VarCtx} (T₁ T₂ : VarType) (z : VarSymb)
    (hzu : z.isUsr = true) (hz : z ∉ VarCtx_to_VarSymbs V) :
    {n : ℕ} → Rel σ (VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz) n →
      Rel σ (VarCtx.insertBnd2 T₁ T₂ V) n
  | _, .R rs      => .R rs
  | _, .eval R' t => .eval (Rel.unpair T₁ T₂ z hzu hz R') (Term.unpair T₁ T₂ z hzu hz t)

/-- The structural substitution pass.  `Rel` has no binders, so there is no dispatcher to write:
    the pair-freeness hypothesis is only passed through to `Term.substCore`. -/
def Rel.substCore {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) :
    {n : ℕ} → Rel σ (VarCtx_insert ⟨x, S⟩ V hx) n → Rel σ V n
  | _, .R rs      => .R rs
  | _, .eval R' t => .eval (Rel.substCore hx h_pf s R') (Term.substCore hx h_pf s t)
