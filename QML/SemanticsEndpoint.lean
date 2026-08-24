import QML.QML_Full_v8

/-!
# Endpoint semantics — the concrete **full/standard model**

The **full (standard) model** — a *subclass* of the general models of `SemanticsGeneral.lean`,
the one where every section and every `Σ`-element is present (`necEval`/`posEval` surjective, so
BF / dual-BF hold).  Instead of abstract `Nec`/`Pos` we take the modal domains to be the
concrete `Π`/`Σ` themselves:

* `⟦□T⟧ w = (w' accessible) → ⟦T⟧ w'`  — a `∀`/section;
* `⟦◇T⟧ w = Σ (w' accessible), ⟦T⟧ w'`  — an `∃`/witness.

Everything bottoms out in `D` (the `Var` domain).  Because the domains are *concrete* `Π`/`Σ`,
there are **no builders**: `boxterm` is a `fun`, `diaterm` is a `⟨witness, …⟩`, and **nesting
composes automatically** — `◇`-under-`□` at any depth is just a function returning a pair.  The
representation is *extensional* and *path-sensitive*: a nested `⟦□□T⟧ = w'→w''→⟦T⟧` is a function
of the whole path `(w',w'')`, not of the endpoint (no `◇◇`-endpoint quotient, no path collapse).
The general model (`SemanticsGeneral.lean`) is obtained by replacing these concrete domains with
arbitrary designated ones subject to the denotable-map condition.
-/

universe u

/-- A Kripke frame with a first-order interpretation.  No modal-domain data is needed — the
    modal domains are the concrete `Π`/`Σ` structures over the frame. -/
structure EModel (σ : Signature) where
  /-- Worlds. -/
  W : Type u
  /-- Accessibility. -/
  R : W → W → Prop
  /-- `Var`-domain at each world. -/
  D : W → Type u
  /-- Per-world relation interpretation (Kripke valuation). -/
  relInterp : (r : σ.RelSyms) → (w : W) → (Fin (σ.relArity r) → D w) → Prop
  /-- Per-world function interpretation. -/
  funcInterp : (f : σ.FuncSyms) → (w : W) → (Fin (σ.funcArity f) → D w) → D w

namespace EModel

variable {σ : Signature}

/-- The domain of each type at each world.  `□` is a section (`∀`), `◇` a witness (`∃`), both
    concrete — the endpoint representation. -/
def interp (M : EModel σ) : VarType → M.W → Type u
  | .Var,           w => M.D w
  | .VTypeOne,      _ => PUnit
  | .VTypeProd A B, w => M.interp A w × M.interp B w
  | .VTypeBox T,    w => (w' : {w' : M.W // M.R w w'}) → M.interp T w'.1
  | .VTypeDia T,    w => Σ' w' : {w' : M.W // M.R w w'}, M.interp T w'.1

@[simp] theorem interp_box (M : EModel σ) (T : VarType) (w : M.W) :
    M.interp (.VTypeBox T) w = ((w' : {w' : M.W // M.R w w'}) → M.interp T w'.1) := rfl
@[simp] theorem interp_dia (M : EModel σ) (T : VarType) (w : M.W) :
    M.interp (.VTypeDia T) w = (Σ' w' : {w' : M.W // M.R w w'}, M.interp T w'.1) := rfl

/-- Environments. -/
def Env (M : EModel σ) (V : VarCtx) (w : M.W) : Type u :=
  (p : VarSymb × VarType) → p ∈ V.1 → M.interp p.2 w

/-- Extend an environment for a freshly-bound variable (`∀`/`∃`/`◇`-witness). -/
def Env.extend {M : EModel σ} {V : VarCtx} {w : M.W} (env : Env M V w)
    (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V) (a : M.interp x.2 w) :
    Env M (VarCtx_insert x V hx) w :=
  fun q hq =>
    if h : q = x then h ▸ a
    else env q ((Finset.mem_insert.mp hq).resolve_left h)

/-- Push a `□`-environment to an accessible world — now just **function application** (the
    boxed variable *is* the section), no `necEval` needed. -/
def Env.boxPush {M : EModel σ} {V_inner W : VarCtx} {w : M.W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (env : Env M W w)
    (w' : {w' : M.W // M.R w w'}) : Env M V_inner w'.1 :=
  fun p hp => env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)) w'

/-! ### Interpretation of terms — direct, no builders -/

mutual

/-- Interpret a term.  `boxterm` is a `fun`, `diaterm` is a witness pair; nesting composes. -/
def interpTerm (M : EModel σ) : {V : VarCtx} → {S : VarType} →
    Term σ V S → (w : M.W) → Env M V w → M.interp S w
  | _, _, .var ⟨v, hv⟩,          w, env => env ⟨v, .Var⟩ hv
  | _, _, .func f,               w, env => M.interpFunc f w env Fin.elim0
  | _, _, .unit,                 _, _   => PUnit.unit
  | _, _, .pair a b,             w, env => (M.interpTerm a w env, M.interpTerm b w env)
  | _, _, .boxterm tt hsub _,    _, env =>
      -- `□`-object = the section `w' ↦ ⟦tt⟧ w'` (env pushed by application).
      fun w' => M.interpTerm tt w'.1 (Env.boxPush hsub env w')
  | _, _, .diaterm x hx tt hsub _, _, env =>
      -- `◇`-object = the witness from the ◇-variable, value = ⟦tt⟧ there.
      let dv := env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))
      ⟨dv.1, M.interpTerm tt dv.1.1
        ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2)⟩
  | _, _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _ => sorry

/-- Interpret a function symbol applied to arguments. -/
def interpFunc (M : EModel σ) : {V : VarCtx} → {n : ℕ} →
    Func σ V n → (w : M.W) → Env M V w → (Fin n → M.D w) → M.D w
  | _, _, .F hr,      w, _,   args => M.funcInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval g t,  w, env, args => M.interpFunc g w env (Fin.cons (M.interpTerm t w env) args)

/-- Interpret a relation symbol applied to arguments. -/
def interpRel (M : EModel σ) : {V : VarCtx} → {n : ℕ} →
    Rel σ V n → (w : M.W) → Env M V w → (Fin n → M.D w) → Prop
  | _, _, .R hr,      w, _,   args => M.relInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval R' t, w, env, args => M.interpRel R' w env (Fin.cons (M.interpTerm t w env) args)

end

/-! ### Satisfaction of formulas -/

def interpWFF (M : EModel σ) : {V : VarCtx} → WFF σ V → (w : M.W) → Env M V w → Prop
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
      -- `◇`-witness variable supplies the world (Skolemized), `φ` holds there.
      let dv := env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))
      M.interpWFF φ dv.1.1
        ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2)
  | _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _ => sorry

end EModel
