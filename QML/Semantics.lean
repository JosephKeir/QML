import QML.QML_Full_v8

/-!
# Semantic models for the QML type theory

A model is a Kripke frame together with **designated domains** for every type at every
world, plus a first-order signature interpretation.  The design follows the semantics
we worked out:

* **Bare worlds + accessibility.** `W` is a plain type of worlds and `R : W → W → Prop`
  the accessibility relation (base logic is K — no frame conditions imposed).

* **Plain individuals.** `D w` is the domain of `Var`-individuals at `w`.  Domains at
  different worlds are *unrelated*: there is no primitive trans-world identity; the only
  cross-world links are the modal objects below.

* **Designated modal domains.** `Nec F` and `Pos F` give, for any world-indexed family
  `F` (the interpretation of the inner type), the types of *necessary* and *possible*
  `F`-objects.  These are arbitrary designated types (Henkin/general models: not forced
  to be the full section/sum space), equipped with structure maps:
  - `necEval` sends a necessary object to a **section** over accessible worlds
    (a function `∀ w' accessible, F w'`);
  - `posEval` sends a possible object to a **witness** at some accessible world
    (a dependent pair `Σ w' accessible, F w'`).
  Non-surjectivity of these maps is allowed and intended — that is exactly the space
  of "private" individuals with no (necessary/possible) cross-world life.

* **The tower and restriction are automatic.** Because `Nec`/`Pos` are *uniform in the
  family* `F`, iterating gives `⟦□□T⟧ w = Nec (Nec ⟦T⟧) w`, and `necEval` on the nested
  family sends a `□□`-object to a section of `□`-objects — i.e. a higher modal object
  **restricts to a lower one at each accessible world**, with no extra data.

* **Path-independence coherence** (`necEval_coh`).  The endpoint value a
  necessary-necessary object assigns to a world reachable via two different intermediates
  agrees.  This is a genuine law (not free): it is what makes the "endpoint function"
  view of higher `□` well-defined.  There is *no* dual law for `Pos`: `◇` records its
  witness, so the nested sum is already correct.

* **Valuations = world-dependent relations.**  `relInterp` interprets each relation
  symbol as a *per-world* predicate on `Var`-individuals — this is the Kripke valuation
  (each world carries its own atomic truth-assignment).  `funcInterp` is likewise
  per-world.  Both act on `Var`-individuals, matching the syntax (`Rel.eval`/`Func.eval`
  consume `.Var` terms).
-/

universe u v

/-- A semantic model of the QML type theory over signature `σ`. -/
structure Model (σ : Signature) where
  /-- Worlds. -/
  W : Type u
  /-- Accessibility relation. -/
  R : W → W → Prop
  /-- Domain of `Var`-individuals at each world. -/
  D : W → Type v
  /-- Designated domain of necessary objects, uniform in the inner family. -/
  Nec : (W → Type v) → (W → Type v)
  /-- Designated domain of possible objects, uniform in the inner family. -/
  Pos : (W → Type v) → (W → Type v)
  /-- A necessary object yields a section over accessible worlds. -/
  necEval : {F : W → Type v} → {w : W} → Nec F w → (w' : {w' : W // R w w'}) → F w'.1
  /-- A possible object yields a witness (value at some accessible world). -/
  posEval : {F : W → Type v} → {w : W} → Pos F w → Σ' w' : {w' : W // R w w'}, F w'.1
  /-- Path-independence: a `□□`-object's endpoint value is independent of the
      intermediate world it is routed through. -/
  necEval_coh : {F : W → Type v} → {w : W} → (n : Nec (Nec F) w) →
      (w₁ w₂ : {w' : W // R w w'}) → (wₑ : W) →
      (h₁ : R w₁.1 wₑ) → (h₂ : R w₂.1 wₑ) →
      necEval (necEval n w₁) ⟨wₑ, h₁⟩ = necEval (necEval n w₂) ⟨wₑ, h₂⟩
  /-- Per-world interpretation of relation symbols (the Kripke valuation). -/
  relInterp : (r : σ.RelSyms) → (w : W) → (Fin (σ.relArity r) → D w) → Prop
  /-- Per-world interpretation of function symbols. -/
  funcInterp : (f : σ.FuncSyms) → (w : W) → (Fin (σ.funcArity f) → D w) → D w
  /-- **The builder.**  There is *no* generic `necIntro : section → Nec`; instead the
      necessary objects are generated exactly as FOL generates domain elements — from the
      shared-context variables (already necessary objects, supplied by the environment),
      constants, and the **pointwise lift of the function symbols**.  `funcInterpNec` is
      that lift: given necessary `Var`-objects it returns the necessary object obtained by
      applying `f` at each accessible world.  Because it builds necessary objects only
      *from* necessary objects, it reaches exactly the term-definable ones and does **not**
      force coverage: undenotable necessary objects and private individuals both survive
      (just like undenotable elements in a FOL Henkin model).  For the `□□`-tower the same
      lift is iterated: `Nec` lifts a σ-structure to a σ-structure, so `funcInterpNec` is
      **polymorphic in the family** and takes the *one-level-down* interpretation `base`.
      Level 1 uses `base := funcInterp f`; level 2 uses the level-1 lift as `base`; etc.
      One construction, iterated up the whole tower — no "n-step function" primitive. -/
  funcInterpNec : (f : σ.FuncSyms) → {F : W → Type v} →
      (base : (w : W) → (Fin (σ.funcArity f) → F w) → F w) →
      {w : W} → (Fin (σ.funcArity f) → Nec F w) → Nec F w
  /-- Compatibility of the lift with the level below: the built necessary object, evaluated
      at an accessible world, is `base` applied there to the evaluated arguments — i.e.
      `necEval (· ) w'` is a **σ-homomorphism** from `Nec F` to `F` at `w'`.  This is the
      `boxterm` round-trip **localized to function application** — the good (soundness)
      constraint, not the bad (coverage) one. -/
  funcInterpNec_beta : (f : σ.FuncSyms) → {F : W → Type v} →
      (base : (w : W) → (Fin (σ.funcArity f) → F w) → F w) →
      {w : W} → (ns : Fin (σ.funcArity f) → Nec F w) → (w' : {w' : W // R w w'}) →
      necEval (funcInterpNec f base ns) w' = base w'.1 (fun i => necEval (ns i) w')
  /-- **The `◇`-builder**, dual to `funcInterpNec` and, like it, *restricted to the
      signature* (this is the fix for the earlier over-general `posMap`, whose arbitrary
      value-map forced a possible object for **every** value at every witnessed world).
      Given a seed possible object (a `◇`-variable, supplying the witness world) and, at that
      world, the argument values of `f`, it returns the possible object obtained by applying
      `f` **on the witness's second component**.  Only function-applications of the witness
      value become possible objects — the definable ones — so `Pos` stays unconstrained and
      `posEval` need not be onto, exactly as `Nec`/`necEval` for the box side. -/
  funcInterpPos : (f : σ.FuncSyms) → {H : W → Type v} → {w : W} → Pos H w →
      ((w' : {w' : W // R w w'}) → H w'.1 → (Fin (σ.funcArity f) → D w'.1)) → Pos D w
  /-- Compatibility with `posEval`: keep the witness world, apply `f` there to the arguments. -/
  funcInterpPos_beta : (f : σ.FuncSyms) → {H : W → Type v} → {w : W} → (p : Pos H w) →
      (args : (w' : {w' : W // R w w'}) → H w'.1 → (Fin (σ.funcArity f) → D w'.1)) →
      posEval (funcInterpPos f p args) =
        ⟨(posEval p).1, funcInterp f (posEval p).1.1 (args (posEval p).1 (posEval p).2)⟩
  /-- The necessary context under a `◇`, evaluated at the witness world: given a seed
      possible object (any type — only its witness world is used) and a necessary object, the
      possible object at that witness world whose value is the necessary object's value there.
      Safe (only `necEval`-values). -/
  posFromNec : {H F : W → Type v} → {w : W} → Pos H w → Nec F w → Pos F w
  posFromNec_beta : {H F : W → Type v} → {w : W} → (seed : Pos H w) → (n : Nec F w) →
      posEval (posFromNec seed n) = ⟨(posEval seed).1, necEval n (posEval seed).1⟩
  /-- **`Nec` lifts the `◇`-builder `funcInterpPos`** (needed for `◇`-under-`□`): applies
      `funcInterpPos` at each accessible world.  Safe (a per-world lift of a safe builder). -/
  funcInterpPosNec : (f : σ.FuncSyms) → {H : W → Type v} → {w : W} → Nec (Pos H) w →
      ((w' : {w' : W // R w w'}) →
        (w'' : {w'' : W // R w'.1 w''}) → H w''.1 → (Fin (σ.funcArity f) → D w''.1)) →
      Nec (Pos D) w
  funcInterpPosNec_beta : (f : σ.FuncSyms) → {H : W → Type v} → {w : W} → (dv : Nec (Pos H) w) →
      (args : (w' : {w' : W // R w w'}) →
        (w'' : {w'' : W // R w'.1 w''}) → H w''.1 → (Fin (σ.funcArity f) → D w''.1)) →
      (w' : {w' : W // R w w'}) →
      necEval (funcInterpPosNec f dv args) w' = funcInterpPos f (necEval dv w') (args w')
  /-- **`Nec` lifts the `◇`-builder `posFromNec`** (needed for `◇`-under-`□`). -/
  posFromNecNec : {H F : W → Type v} → {w : W} → Nec (Pos H) w → Nec (Nec F) w → Nec (Pos F) w
  posFromNecNec_beta : {H F : W → Type v} → {w : W} → (dv : Nec (Pos H) w) → (dn : Nec (Nec F) w) →
      (w' : {w' : W // R w w'}) →
      necEval (posFromNecNec dv dn) w' = posFromNec (necEval dv w') (necEval dn w')

namespace Model

variable {σ : Signature}

/-- Accessible worlds from `w`. -/
abbrev Access (M : Model σ) (w : M.W) : Type u := {w' : M.W // M.R w w'}

/-- The domain of each type at each world.  `Var` is the plain domain; products are
    products; `□`/`◇` pull the designated `Nec`/`Pos` domains.  So
    `⟦□T⟧ w = Nec ⟦T⟧ w`, `⟦◇T⟧ w = Pos ⟦T⟧ w`, and the tower is `⟦□□T⟧ = Nec (Nec ⟦T⟧)`. -/
def interp (M : Model σ) : VarType → M.W → Type v
  | .Var,           w => M.D w
  | .VTypeOne,      _ => PUnit.{v + 1}
  | .VTypeProd A B, w => M.interp A w × M.interp B w
  | .VTypeBox T,    w => M.Nec (M.interp T) w
  | .VTypeDia T,    w => M.Pos (M.interp T) w

@[simp] theorem interp_Var (M : Model σ) (w : M.W) : M.interp .Var w = M.D w := rfl
@[simp] theorem interp_one (M : Model σ) (w : M.W) : M.interp .VTypeOne w = PUnit := rfl
@[simp] theorem interp_prod (M : Model σ) (A B : VarType) (w : M.W) :
    M.interp (.VTypeProd A B) w = (M.interp A w × M.interp B w) := rfl
@[simp] theorem interp_box (M : Model σ) (T : VarType) (w : M.W) :
    M.interp (.VTypeBox T) w = M.Nec (M.interp T) w := rfl
@[simp] theorem interp_dia (M : Model σ) (T : VarType) (w : M.W) :
    M.interp (.VTypeDia T) w = M.Pos (M.interp T) w := rfl

/-! ### Environments -/

/-- An environment at world `w` gives a value in `⟦T⟧ w` for each declared variable
    `⟨v, T⟩` of the context. -/
def Env (M : Model σ) (V : VarCtx) (w : M.W) : Type v :=
  (p : VarSymb × VarType) → p ∈ V.1 → M.interp p.2 w

/-- Extend an environment with a value for a freshly-bound variable (interprets `∀`/`∃`). -/
def Env.extend {M : Model σ} {V : VarCtx} {w : M.W} (env : Env M V w)
    (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V) (a : M.interp x.2 w) :
    Env M (VarCtx_insert x V hx) w :=
  fun q hq =>
    if h : q = x then h ▸ a
    else env q ((Finset.mem_insert.mp hq).resolve_left h)

/-- Push an environment through a `□` context to an accessible world `w'`, by evaluating
    each (necessary) variable there via `necEval`.  This is the semantic content of the
    `K` box rule: a necessary variable's value at `w` yields a value at every `w'`. -/
def Env.boxPush {M : Model σ} {V_inner W : VarCtx} {w : M.W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (env : Env M W w)
    (w' : {w' : M.W // M.R w w'}) : Env M V_inner w'.1 :=
  fun p hp => M.necEval (env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))) w'

/-- A *necessary* environment: a necessary `⟦T⟧`-object for each variable `⟨v,T⟩` of the
    context.  This is what the interpretation of `boxterm` recurses over. -/
def NecEnv (M : Model σ) (V : VarCtx) (w : M.W) : Type v :=
  (p : VarSymb × VarType) → p ∈ V.1 → M.Nec (M.interp p.2) w

/-- The variables under a `□` are *already* necessary objects in the ambient environment
    (their boxed forms `⟨v, □T⟩`); reading them off gives the necessary environment the
    `boxterm` recursion builds from — no destructuring by `necEval`. -/
def Env.boxNec {M : Model σ} {V_inner W : VarCtx} {w : M.W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (env : Env M W w) : NecEnv M V_inner w :=
  fun p hp => env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

/-! ### Interpreting a term under an arbitrary necessity context

Rather than an `ℕ`-indexed tower of pure `Nec`s, `interpTermNec` is parametrised by the
*ambient modality* `N` — the composite of all the type-formers `boxterm` has descended
through so far — together with `liftN`, the **σ-structure lift** for `N` (its coherence,
supplied as data).  Descending through a `boxterm` composes on one more `Nec`: the modality
becomes `N ∘ Nec` and the lift becomes `liftN ∘ liftNec`, both *definitionally*, so there
are no associativity casts.  This is agnostic to what sits below — `◇`, products, or `Nec`
again — so `Nec (Pos …)` and other mixed towers are handled uniformly. -/

/-- A per-world σ-structure on a family `F`: an interpretation of every function symbol. -/
def Str (M : Model σ) (F : M.W → Type v) :=
  (f : σ.FuncSyms) → (w : M.W) → (Fin (σ.funcArity f) → F w) → F w

/-- The base σ-structure on the individual domain. -/
def funcInterpBase (M : Model σ) : Str M M.D := fun f w => M.funcInterp f w

/-- `Nec` lifts a σ-structure to one on `Nec F`, function-symbol-wise via `funcInterpNec`. -/
def Str.liftNec {M : Model σ} {F : M.W → Type v} (s : Str M F) : Str M (M.Nec F) :=
  fun f _ args => M.funcInterpNec f (s f) args

mutual

/-- Interpret a term into `N ⟦S⟧`, where `N` is the ambient necessity modality and `liftN`
    its σ-structure lift.  Variables are read from the necessary environment; functions use
    `liftN` of the base structure; a nested `boxterm` recurses under `N ∘ Nec`. -/
def interpTermNec (M : Model σ) :
    (N : (M.W → Type v) → (M.W → Type v)) →
    (liftN : {F : M.W → Type v} → Str M F → Str M (N F)) →
    {V : VarCtx} → {S : VarType} → Term σ V S → (w : M.W) →
    ((p : VarSymb × VarType) → p ∈ V.1 → N (M.interp p.2) w) → N (M.interp S) w
  | _, _,     _, _, .var ⟨v, hv⟩, w, necEnv => necEnv ⟨v, .Var⟩ hv
  | N, liftN, _, _, .func f,      w, necEnv => M.interpFuncNec N liftN f w necEnv Fin.elim0
  | N, liftN, _, _, @Term.boxterm _ _ _ _ tt hsub _, w, necEnv =>
      -- descend one level: modality `N ∘ Nec`, lift `liftN ∘ liftNec`, reading the
      -- doubly-boxed variables off the environment.  All definitional — no casts.
      M.interpTermNec (fun F => N (M.Nec F)) (fun s => liftN s.liftNec) tt w
        (fun p hp => necEnv ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
  | _, _, _, _, .pair _ _,       _, _ => sorry   -- needs □-preservation of products
  | _, _, _, _, .unit,           _, _ => sorry   -- needs the necessary unit
  | _, _, _, _, .diaterm _ _ _ _ _, _, _ => sorry
      -- ◇-under-`N` (here `N` is always a pure `Nec`-tower, since only `boxterm` descends
      -- into `interpTermNec`).  The `Nec`-lifts of the ◇-builders now exist as fields
      -- (`funcInterpPosNec`, `posFromNecNec`) and give the *base* (`N = Nec`) case.  The
      -- blocker is the descent `N ↦ N∘Nec`: it needs "`Nec` lifts the ◇-op *already at* `N`",
      -- which the single-layer primitives don't provide (it would recurse up the tower).  The
      -- clean fix is to fold the ◇-builders into the transported structure (`Str` → a full
      -- modal structure), so `liftN` carries them and `liftN ∘ liftNec` handles the descent
      -- uniformly — i.e. make `Nec`/`Pos` a *model of the whole type theory*.  Deferred to
      -- that refactor.
  | _, _, _, _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _ => sorry

/-- Interpret a function symbol under modality `N`, applied to `N D`-objects. -/
def interpFuncNec (M : Model σ) :
    (N : (M.W → Type v) → (M.W → Type v)) →
    (liftN : {F : M.W → Type v} → Str M F → Str M (N F)) →
    {V : VarCtx} → {n : ℕ} → Func σ V n → (w : M.W) →
    ((p : VarSymb × VarType) → p ∈ V.1 → N (M.interp p.2) w) →
    (Fin n → N M.D w) → N M.D w
  | _, liftN, _, _, .F hr,     w, _,      args => liftN M.funcInterpBase hr.1 w (hr.2.symm ▸ args)
  | N, liftN, _, _, .eval g t, w, necEnv, args =>
      M.interpFuncNec N liftN g w necEnv (Fin.cons (M.interpTermNec N liftN t w necEnv) args)

end

/-! ### Interpretation of terms, functions, relations -/

mutual

/-- Interpret a term as an element of its type's domain. -/
def interpTerm (M : Model σ) : {V : VarCtx} → {S : VarType} →
    Term σ V S → (w : M.W) → Env M V w → M.interp S w
  | _, _, .var ⟨v, hv⟩,          w, env => env ⟨v, .Var⟩ hv
  | _, _, .func f,               w, env => M.interpFunc f w env Fin.elim0
  | _, _, .unit,                 _, _   => PUnit.unit
  | _, _, .pair a b,             w, env => (M.interpTerm a w env, M.interpTerm b w env)
  | _, _, .boxterm tt hsub _,    w, env =>
      -- FOL-style builder: interpret `tt` directly into `Nec ⟦S⟧` under ambient modality
      -- `Nec` (lift `liftNec`), reading its variables off the environment.
      M.interpTermNec M.Nec (fun s => s.liftNec) tt w (Env.boxNec hsub env)
  | _, _, .diaterm x hx tt hsub _, w, env =>
      -- interpret `tt` into `Pos ⟦S⟧`.  `seed` is the ◇-witness variable's possible object
      -- (supplies the witness world); `posEnv` reads variables (witness ↦ seed, boxed ↦
      -- `posFromNec`); `ordAt` builds the ordinary environment at the witness world (boxed
      -- variables pushed there, witness set to its value) for evaluating function arguments.
      let seed := env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))
      M.interpTermPos tt w seed
        (fun p hp =>
          if h : p = x then h ▸ seed
          else M.posFromNec seed (env ⟨p.1, p.2.VTypeBox⟩
            (hsub (Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨p, (Finset.mem_insert.mp hp).resolve_left h, rfl⟩)))))
        (fun w' a =>
          (Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env w').extend x hx a)
  | _, _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _ => sorry

/-- Interpret a function symbol applied to some arguments. -/
def interpFunc (M : Model σ) : {V : VarCtx} → {n : ℕ} →
    Func σ V n → (w : M.W) → Env M V w → (Fin n → M.D w) → M.D w
  | _, _, .F hr,      w, _,   args => M.funcInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval g t,  w, env, args => M.interpFunc g w env (Fin.cons (M.interpTerm t w env) args)

/-- Interpret a relation symbol applied to some arguments as a proposition. -/
def interpRel (M : Model σ) : {V : VarCtx} → {n : ℕ} →
    Rel σ V n → (w : M.W) → Env M V w → (Fin n → M.D w) → Prop
  | _, _, .R hr,      w, _,   args => M.relInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval R' t, w, env, args => M.interpRel R' w env (Fin.cons (M.interpTerm t w env) args)

/-- Interpret a term into `Pos ⟦S⟧`, dual to `interpTermNec`.  `seed` supplies the witness
    world; `posEnv` reads variables as possible objects (witness ↦ seed, boxed ↦ `posFromNec`);
    `ordAt` builds the ordinary environment at the witness world (given the witness value) for
    evaluating the arguments of function symbols. -/
def interpTermPos (M : Model σ) : {Hs : M.W → Type v} → {V : VarCtx} → {S : VarType} →
    Term σ V S → (w : M.W) → M.Pos Hs w →
    ((p : VarSymb × VarType) → p ∈ V.1 → M.Pos (M.interp p.2) w) →
    ((w' : {w' : M.W // M.R w w'}) → Hs w'.1 → Env M V w'.1) → M.Pos (M.interp S) w
  | _, _, _, .var ⟨v, hv⟩, _, _,    posEnv, _     => posEnv ⟨v, .Var⟩ hv
  | _, _, _, .func f,      w, seed, _,      ordAt => M.interpFuncPos f w seed ordAt (fun _ _ => Fin.elim0)
  | _, _, _, .unit,        _, _,    _,      _     => sorry
  | _, _, _, .pair _ _,    _, _,    _,      _     => sorry
  | _, _, _, .boxterm _ _ _, _, _,  _,      _     => sorry
  | _, _, _, .diaterm _ _ _ _ _, _, _,   _,      _     => sorry
  | _, _, _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _, _, _ => sorry

/-- Lift a function symbol to a possible object (`funcInterpPos` on the base symbol), building
    up its arguments from the argument terms evaluated at the witness world via `ordAt`. -/
def interpFuncPos (M : Model σ) : {Hs : M.W → Type v} → {V : VarCtx} → {n : ℕ} →
    Func σ V n → (w : M.W) → M.Pos Hs w →
    ((w' : {w' : M.W // M.R w w'}) → Hs w'.1 → Env M V w'.1) →
    ((w' : {w' : M.W // M.R w w'}) → Hs w'.1 → (Fin n → M.D w'.1)) → M.Pos M.D w
  | _, _, _, .F hr,     _, seed, _,     accArgs =>
      M.funcInterpPos hr.1 seed (fun w' a => hr.2.symm ▸ accArgs w' a)
  | _, _, _, .eval g t, w, seed, ordAt, accArgs =>
      M.interpFuncPos g w seed ordAt
        (fun w' a => Fin.cons (M.interpTerm t w'.1 (ordAt w' a)) (accArgs w' a))

end

/-! ### Satisfaction of formulas -/

/-- `M.interpWFF φ w env` — `φ` is satisfied at world `w` under environment `env`. -/
def interpWFF (M : Model σ) : {V : VarCtx} → WFF σ V → (w : M.W) → Env M V w → Prop
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
      -- `□φ` holds at `w` iff `φ` holds at every accessible world, env pushed there.
      ∀ w' : {w' : M.W // M.R w w'}, M.interpWFF φ w'.1 (Env.boxPush hsub env w')
  | _, .dia x hx φ hsub _, w, env =>
      -- `◇` is Skolemized: the `◇`-witness variable supplies a possible object, whose
      -- `posEval` gives the witness world `w'` and value `a`.  `φ` is then interpreted at
      -- `w'` with the boxed variables pushed there and the witness variable set to `a`.
      let wit := M.posEval (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _)))
      M.interpWFF φ wit.1.1
        ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env wit.1).extend x hx wit.2)
  | _, .pair_elim _ _ _ _ _ _ _ _ _ _, _, _ => sorry

end Model
