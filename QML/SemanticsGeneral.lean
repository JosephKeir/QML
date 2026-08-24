import QML.QML_Full_v8

/-!
# General-model semantics — abstract modal domains with `eval`/`intro` into `Π`/`Σ`

The **general model** (Henkin's "general models", as opposed to *standard/full* models with the
maximal `Π`/`Σ` domains — see `SemanticsEndpoint.lean` for the full one).  The modal domains
`Nec`/`Pos` are **abstract** (designated, chosen by the model), connected to the concrete
section/witness types by **functions**:

* `necEval : Nec F w → ((w' accessible) → F w')`  — into the `Π`/section type;
* `posEval : Pos F w → Σ (w' accessible), F w'`   — into the `Σ`/witness type;

plus builders the other way (`necIntro`/`posIntro`), with round-trips (`_beta`).  A model is
free to make `Nec`/`Pos` *small* (`necEval`/`posEval` non-surjective) — that is where private
individuals live and BF/dual-BF fail; it is *not* a predicate carved out of `Π`/`Σ`.

`boxterm`/`diaterm` interpret by `necIntro`/`posIntro` applied to the section / witness built by
recursion — because those compose concretely, **modal terms at arbitrary nesting depth just
work** (contrast the abandoned `funcInterpNec` tower, which avoided `necIntro` and is exactly
what failed to compose).

## The model class (settled)

The domains `Nec`/`Pos` are **arbitrary**, subject to a single *denotable-map* condition: a
function from the **denotable terms** of each type into that domain (`NecD`/`PosD` of
`Denotable.lean`, products, and `Var` = `funcInterp` totality).  This is the inclusive-logic
condition — it can *rule out the empty domain* wherever a denotable term exists, but otherwise
permits empty domains.  `interpTerm`'s `boxterm`/`diaterm` only ever feed *denotable*
sections/witnesses to the builders, so the interpretation is well-defined against it.

**Two independent knobs — extensional but not full (the Henkin/general picture):**
* **fullness** = `necEval`/`posEval` *surjective* (every section/witness realized) ⇒ BF valid.
  General models DROP it — they may be non-surjective (denotable sections only in the limit).
  (As written below `necIntro`/`posIntro` are *total*, so this file is currently a *full* model;
  the faithful general model weakens them to the denotable-map — the one remaining knob.)
* **extensionality** = `necEval`/`posEval` *injective* (an object is its behaviour) ⇒ funext /
  Σ-ext.  KEEP it (independent of, and compatible with, non-surjectivity — that combination *is*
  a general/Henkin model), as a model condition plus the two world-extensionality rules
  `□(t₁ ≐ t₂ : V) ⊢ t₁ = t₂ : □V`, `◇(t₁ ≐ t₂ : V) ⊢ t₁ = t₂ : ◇V` (peel *one* modality, inner
  equality at the *full* type `V`, discharged recursively = nested funext / Σ-ext).

Only `necEval_coh` (path-independence) is genuinely dropped — it is the *opposite* of
extensionality (it collapses path-dependence, whereas funext individuates by the full path).
Equality is `interpWFF.eq` = plain domain-equality on `interp T`.  (TODO: add `necEval`/`posEval`
injectivity as fields.)
-/

universe u

/-- A general model: a Kripke frame, a first-order interpretation, and abstract modal domains
    with structure maps into the `Π`/`Σ` section/witness types. -/
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
  /-- A necessary object *is* (maps to) a section over accessible worlds. -/
  necEval : {F : W → Type u} → {w : W} → Nec F w → (w' : {w' : W // R w w'}) → F w'.1
  /-- A possible object *is* (maps to) a witness. -/
  posEval : {F : W → Type u} → {w : W} → Pos F w → Σ' w' : {w' : W // R w w'}, F w'.1
  /-- Builder: realise a section as a necessary object.  (Total here ⇒ full model; the
      faithful model restricts this to a designated class of sections.) -/
  necIntro : {F : W → Type u} → {w : W} → ((w' : {w' : W // R w w'}) → F w'.1) → Nec F w
  /-- Builder: realise a witness as a possible object.  (Dual caveat.) -/
  posIntro : {F : W → Type u} → {w : W} → (Σ' w' : {w' : W // R w w'}, F w'.1) → Pos F w
  nec_beta : {F : W → Type u} → {w : W} → (s : (w' : {w' : W // R w w'}) → F w'.1) →
      necEval (necIntro s) = s
  pos_beta : {F : W → Type u} → {w : W} → (p : Σ' w' : {w' : W // R w w'}, F w'.1) →
      posEval (posIntro p) = p

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

/-! ### Builders are derived, not primitive

A pointwise operation at the base (`Var`) level lifts to `Π`/`Σ` by post-composition, and
then **up into the abstract domains** via `necEval`/`posEval` and `necIntro`/`posIntro`.  So
`funcInterpNec`/`funcInterpPos` etc. are *derived* — there is no need for them as fields. -/

/-- Lift any pointwise operation `F ⟹ G` to necessary objects (`necEval`, then `necIntro`). -/
def liftNec (M : GModel σ) {F G : M.W → Type u} {w : M.W}
    (op : (w' : {w' : M.W // M.R w w'}) → F w'.1 → G w'.1) (n : M.Nec F w) : M.Nec G w :=
  M.necIntro (fun w' => op w' (M.necEval n w'))

@[simp] theorem necEval_liftNec (M : GModel σ) {F G : M.W → Type u} {w : M.W}
    (op : (w' : {w' : M.W // M.R w w'}) → F w'.1 → G w'.1) (n : M.Nec F w)
    (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.liftNec op n) w' = op w' (M.necEval n w') := by
  rw [liftNec, M.nec_beta]

/-- Dually, lift a pointwise operation to possible objects (`posEval`, then `posIntro`). -/
def liftPos (M : GModel σ) {F G : M.W → Type u} {w : M.W}
    (op : (w' : {w' : M.W // M.R w w'}) → F w'.1 → G w'.1) (p : M.Pos F w) : M.Pos G w :=
  M.posIntro ⟨(M.posEval p).1, op (M.posEval p).1 (M.posEval p).2⟩

@[simp] theorem posEval_liftPos (M : GModel σ) {F G : M.W → Type u} {w : M.W}
    (op : (w' : {w' : M.W // M.R w w'}) → F w'.1 → G w'.1) (p : M.Pos F w) :
    M.posEval (M.liftPos op p) = ⟨(M.posEval p).1, op (M.posEval p).1 (M.posEval p).2⟩ := by
  rw [liftPos, M.pos_beta]

/-- The old primitive `funcInterpNec` is just `liftNec` at a function symbol — derived, and
    its `_beta` (`necEval` a σ-homomorphism) is now a one-line consequence. -/
def funcInterpNec (M : GModel σ) (f : σ.FuncSyms) {w : M.W}
    (ns : Fin (σ.funcArity f) → M.Nec M.D w) : M.Nec M.D w :=
  M.necIntro (fun w' => M.funcInterp f w'.1 (fun i => M.necEval (ns i) w'))

@[simp] theorem necEval_funcInterpNec (M : GModel σ) (f : σ.FuncSyms) {w : M.W}
    (ns : Fin (σ.funcArity f) → M.Nec M.D w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.funcInterpNec f ns) w' = M.funcInterp f w'.1 (fun i => M.necEval (ns i) w') := by
  rw [funcInterpNec, M.nec_beta]

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

/-! ### Interpretation of terms — `necIntro`/`posIntro` on composed sections/witnesses -/

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
      -- `◇`-object = `posIntro` of the witness from the ◇-variable, value = ⟦tt⟧ there.
      let dv := M.posEval (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _)))
      M.posIntro ⟨dv.1, M.interpTerm tt dv.1.1
        ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2)⟩
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
      let dv := M.posEval (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _)))
      M.interpWFF φ dv.1.1
        ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2)
  | _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _ => sorry

end GModel
