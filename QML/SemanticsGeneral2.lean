import QML.QML_Full_v8

/-!
# General-model semantics v2 — possible objects as **sets of realizations** (existential `◇`)

Refactor of `SemanticsGeneral.lean`.  The single change: a **possible object** is no longer a
single witness (`posEval : Pos F w → Σ' w', F w'`, a `Σ`) but a **set of realizations**
(`posMem : Pos F w → (Σ' w', F w') → Prop`).  Consequences:

* the formula-level `◇_x φ` is a genuine **existential** (`∃` over realizations), so
  `box_x := ¬◇_x¬φ = ∀ realizations ≠ ◇_x` — a real K-diamond: no same-witness recombination,
  and `box_x = ◇_x` is *correctly unprovable*;
* a `diaterm` (which only ever appears inside a `◇_x` or an equality — relations/functions take
  only `.Var` args) interprets as the **functorial image** of the object's realizations through
  the inner term;
* equality of possible objects is equality of realization sets (`pos_eta` ⇒ `posMem` injective);
* the empty realization set is harmless — the possible object realized nowhere, `◇_x` of it is
  `False`, and no term is ever evaluated against it (extraction happens past the `∃`).

`posEval`/`pos_beta` (`Σ`-version) are dropped; `Nec` and the whole `□` side are unchanged.
-/

universe u

/-- A general model, v2: possible objects are designated *sets of realizations*. -/
structure GModel (σ : Signature) where
  W : Type u
  R : W → W → Prop
  D : W → Type u
  relInterp : (r : σ.RelSyms) → (w : W) → (Fin (σ.relArity r) → D w) → Prop
  funcInterp : (f : σ.FuncSyms) → (w : W) → (Fin (σ.funcArity f) → D w) → D w
  /-- Designated domain of necessary objects. -/
  Nec : (W → Type u) → (W → Type u)
  /-- Designated domain of possible objects. -/
  Pos : (W → Type u) → (W → Type u)
  /-- A necessary object *is* a section over accessible worlds. -/
  necEval : {F : W → Type u} → {w : W} → Nec F w → (w' : {w' : W // R w w'}) → F w'.1
  /-- Builder: realise a section as a necessary object. -/
  necIntro : {F : W → Type u} → {w : W} → ((w' : {w' : W // R w w'}) → F w'.1) → Nec F w
  nec_beta : {F : W → Type u} → {w : W} → (s : (w' : {w' : W // R w w'}) → F w'.1) →
      necEval (necIntro s) = s
  /-- A possible object *is* its **set of realizations** `(accessible world, value there)`. -/
  posMem : {F : W → Type u} → {w : W} → Pos F w →
      (Σ' w' : {w' : W // R w w'}, F w'.1) → Prop
  /-- Builder: realise a set of witnesses as a possible object.  (Total here ⇒ full model; the
      faithful model restricts this to a designated class of witness sets.) -/
  posIntro : {F : W → Type u} → {w : W} →
      ((Σ' w' : {w' : W // R w w'}, F w'.1) → Prop) → Pos F w
  pos_beta : {F : W → Type u} → {w : W} →
      (P : (Σ' w' : {w' : W // R w w'}, F w'.1) → Prop) → posMem (posIntro P) = P
  /-- Extensionality: a possible object is determined by its realization set. -/
  pos_eta : {F : W → Type u} → {w : W} → (p : Pos F w) → posIntro (posMem p) = p

namespace GModel

variable {σ : Signature}

/-- The domain of each type at each world. -/
def interp (M : GModel σ) : VarType → M.W → Type u
  | .Var,           w => M.D w
  | .VTypeOne,      _ => PUnit
  | .VTypeProd A B, w => M.interp A w × M.interp B w
  | .VTypeBox T,    w => M.Nec (M.interp T) w
  | .VTypeDia T,    w => M.Pos (M.interp T) w

@[simp] theorem interp_box (M : GModel σ) (T : VarType) (w : M.W) :
    M.interp (.VTypeBox T) w = M.Nec (M.interp T) w := rfl
@[simp] theorem interp_dia (M : GModel σ) (T : VarType) (w : M.W) :
    M.interp (.VTypeDia T) w = M.Pos (M.interp T) w := rfl

/-! ### Necessary-object lifts (unchanged from v1) -/

/-- Lift any pointwise operation `F ⟹ G` to necessary objects (`necEval`, then `necIntro`). -/
def liftNec (M : GModel σ) {F G : M.W → Type u} {w : M.W}
    (op : (w' : {w' : M.W // M.R w w'}) → F w'.1 → G w'.1) (n : M.Nec F w) : M.Nec G w :=
  M.necIntro (fun w' => op w' (M.necEval n w'))

@[simp] theorem necEval_liftNec (M : GModel σ) {F G : M.W → Type u} {w : M.W}
    (op : (w' : {w' : M.W // M.R w w'}) → F w'.1 → G w'.1) (n : M.Nec F w)
    (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.liftNec op n) w' = op w' (M.necEval n w') := by
  rw [liftNec, M.nec_beta]

def funcInterpNec (M : GModel σ) (f : σ.FuncSyms) {w : M.W}
    (ns : Fin (σ.funcArity f) → M.Nec M.D w) : M.Nec M.D w :=
  M.necIntro (fun w' => M.funcInterp f w'.1 (fun i => M.necEval (ns i) w'))

@[simp] theorem necEval_funcInterpNec (M : GModel σ) (f : σ.FuncSyms) {w : M.W}
    (ns : Fin (σ.funcArity f) → M.Nec M.D w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.funcInterpNec f ns) w' = M.funcInterp f w'.1 (fun i => M.necEval (ns i) w') := by
  rw [funcInterpNec, M.nec_beta]

/-! ### Possible-object functorial map (replaces `liftPos`) -/

/-- Map a pointwise operation over a possible object's realizations.  A realization `⟨w', u⟩` of
    the result holds iff some realization `⟨w', v⟩` of `p` maps to it under `op`. -/
def posMap (M : GModel σ) {F G : M.W → Type u} {w : M.W}
    (op : (w' : {w' : M.W // M.R w w'}) → F w'.1 → G w'.1) (p : M.Pos F w) : M.Pos G w :=
  M.posIntro (fun ru => ∃ v : F ru.1.1, M.posMem p ⟨ru.1, v⟩ ∧ op ru.1 v = ru.2)

@[simp] theorem posMem_posMap (M : GModel σ) {F G : M.W → Type u} {w : M.W}
    (op : (w' : {w' : M.W // M.R w w'}) → F w'.1 → G w'.1) (p : M.Pos F w)
    (ru : Σ' w' : {w' : M.W // M.R w w'}, G w'.1) :
    M.posMem (M.posMap op p) ru = ∃ v : F ru.1.1, M.posMem p ⟨ru.1, v⟩ ∧ op ru.1 v = ru.2 := by
  rw [posMap, M.pos_beta]

/-- Environments. -/
def Env (M : GModel σ) (V : VarCtx) (w : M.W) : Type u :=
  (p : VarSymb × VarType) → p ∈ V.1 → M.interp p.2 w

/-- Extend an environment for a freshly-bound variable. -/
def Env.extend {M : GModel σ} {V : VarCtx} {w : M.W} (env : Env M V w)
    (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V) (a : M.interp x.2 w) :
    Env M (VarCtx_insert x V hx) w :=
  fun q hq =>
    if h : q = x then h ▸ a
    else env q ((Finset.mem_insert.mp hq).resolve_left h)

/-- Push a `□`-environment to an accessible world by `necEval`-ing each boxed variable. -/
def Env.boxPush {M : GModel σ} {V_inner W : VarCtx} {w : M.W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (env : Env M W w)
    (w' : {w' : M.W // M.R w w'}) : Env M V_inner w'.1 :=
  fun p hp => M.necEval (env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))) w'

/-! ### Interpretation of terms -/

mutual

def interpTerm (M : GModel σ) : {V : VarCtx} → {S : VarType} →
    Term σ V S → (w : M.W) → Env M V w → M.interp S w
  | _, _, .var ⟨v, hv⟩,          w, env => env ⟨v, .Var⟩ hv
  | _, _, .func f,               w, env => M.interpFunc f w env Fin.elim0
  | _, _, .unit,                 _, _   => PUnit.unit
  | _, _, .pair a b,             w, env => (M.interpTerm a w env, M.interpTerm b w env)
  | _, _, .boxterm tt hsub _,    _, env =>
      -- `□`-object = `necIntro` of the section `w' ↦ ⟦tt⟧ w'`.
      M.necIntro (fun w' => M.interpTerm tt w'.1 (Env.boxPush hsub env w'))
  | _, _, .diaterm x hx tt hsub _, _, env =>
      -- `◇`-object = the functorial image of the ◇-variable's realizations through `tt`.
      M.posIntro (fun ru => ∃ v : M.interp x.2 ru.1.1,
        M.posMem (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))) ⟨ru.1, v⟩ ∧
        M.interpTerm tt ru.1.1
          ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env ru.1).extend x hx v)
          = ru.2)
  | _, _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _ => sorry

def interpFunc (M : GModel σ) : {V : VarCtx} → {n : ℕ} →
    Func σ V n → (w : M.W) → Env M V w → (Fin n → M.D w) → M.D w
  | _, _, .F hr,      w, _,   args => M.funcInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval g t,  w, env, args => M.interpFunc g w env (Fin.cons (M.interpTerm t w env) args)

def interpRel (M : GModel σ) : {V : VarCtx} → {n : ℕ} →
    Rel σ V n → (w : M.W) → Env M V w → (Fin n → M.D w) → Prop
  | _, _, .R hr,      w, _,   args => M.relInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval R' t, w, env, args => M.interpRel R' w env (Fin.cons (M.interpTerm t w env) args)

end

/-! ### Satisfaction of formulas -/

def interpWFF (M : GModel σ) : {V : VarCtx} → WFF σ V → (w : M.W) → Env M V w → Prop
  | _, .atom R,     w, env => M.interpRel R w env Fin.elim0
  | _, .top,        _, _   => True
  | _, .bot,        _, _   => False
  | _, .and φ ψ,    w, env => M.interpWFF φ w env ∧ M.interpWFF ψ w env
  | _, .or φ ψ,     w, env => M.interpWFF φ w env ∨ M.interpWFF ψ w env
  | _, .imp φ ψ,    w, env => M.interpWFF φ w env → M.interpWFF ψ w env
  | _, .eq s t,     w, env => M.interpTerm s w env = M.interpTerm t w env
  | _, @WFF.all _ _ x hx φ, w, env => ∀ a : M.interp x.2 w, M.interpWFF φ w (env.extend x hx a)
  | _, @WFF.ex _ _ x hx φ,  w, env => ∃ a : M.interp x.2 w, M.interpWFF φ w (env.extend x hx a)
  | _, .box φ hsub _, w, env =>
      ∀ w' : {w' : M.W // M.R w w'}, M.interpWFF φ w'.1 (Env.boxPush hsub env w')
  | _, .dia x hx φ hsub _, w, env =>
      -- `◇_x φ` = *some* realization of the ◇-variable makes `φ` hold at its world.
      ∃ dv : Σ' w' : {w' : M.W // M.R w w'}, M.interp x.2 w'.1,
        M.posMem (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))) dv ∧
        M.interpWFF φ dv.1.1
          ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2)
  | _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _ => sorry

end GModel
