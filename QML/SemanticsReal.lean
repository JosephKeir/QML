import QML.QML_Full_v8

/-!
# The "real" (completeness-oriented) semantics — `RModel`

This is the Henkin/general model we settled on for the completeness direction.  It is the same
shape as `SemanticsGeneral2.GModel`, with two deliberate changes (see the design discussion,
memory `project-qml-semantics` 🧭 block):

* **Extensionality is KEPT (as injectivity), fullness is DROPPED.**  The eval maps out of the
  modal domains are **injective** (a modal object *is* its behaviour — world-extensionality /
  funext, which is exactly what makes the `box_ext` rule sound) but **need not be surjective**
  (non-full: only *denotable* sections/realization-sets are realized, which is what makes the
  Barcan family *fail* and keeps the model general).  Contrast `GModel`, which has a *total*
  `necIntro` (⇒ `necEval` surjective ⇒ full) and NO `necEval`-injectivity.

* **Product types just *are* products.**  `interp (A ×ᵥ B) w = interp A w × interp B w`, so the
  maps in/out are the ordinary `⟨·,·⟩` / `.1` / `.2` — nothing designated.  (Same as `GModel`.)

The **map *in* from the definable terms** is `interpTerm`, and it is genuine *data only at the
actual world*: a map `Term V S → interp S actual` (per context `V`).  At every *accessible* world
its values are **not** freshly constructed — they are **read off the eval maps**: for a box term,
`interpTerm t` at an accessible `w` is *defined to be* `necEval (interpTerm (box t) @) w` (dually
`posEval` for `◇`).  So a single box object at `@` populates every accessible world with the
stripped body, and the only content the model carries is (i) the domains + injective eval maps and
(ii) `interpTerm` at `@`; everything at other worlds is an image under the eval map.  (There is
therefore *no* `necIntro`/`posIntro` to supply — the earlier "denotable `necIntro`" framing is
superseded — and `dia`-witnesses need no population either: `x : ◇…` is always a bound variable,
so its `Pos` object is just `env x`, read from the context.)

Two things are deliberately **loose** in a *general* model (tight only in the canonical one):
* **Junk is allowed.**  `interp S w` may contain objects *not* `@`-denotable (outside the eval-image
  of any `@`-object).  The canonical model has none: `interp S w := Term S` (at `w`'s context) mod
  provable equality — exactly the denotable objects.
* **`interpTerm` need not be injective.**  Two terms that are *not* provably equal may denote the
  *same* object in a general model.  Only the canonical model is faithful (injective `interpTerm`),
  which is what refutes non-theorems.  **This is a different injectivity from `nec_inj`/`pos_inj`:**
  the *eval* maps are injective in *every* model (world-extensionality / the `box_ext` rule);
  `interpTerm` being injective is a canonical-model-only property.  A general model thus has
  injective *eval* but possibly non-injective *denotation* — consistent, since `⟦t⟧` and `⟦t'⟧`
  may be one box object, which still has a unique section.
-/

universe u

/-- A **real** (Henkin/general, completeness-oriented) model: a pointed Kripke frame with
    per-type designated domains and *injective* (but not necessarily surjective) eval maps out of
    the modal domains. -/
structure RModel (σ : Signature) where
  /-- Worlds. -/
  W : Type u
  /-- The distinguished **actual world** (where closed formulas are ultimately evaluated). -/
  actual : W
  /-- Accessibility. -/
  R : W → W → Prop
  /-- Base domain (`Var`-typed objects) at each world. -/
  D : W → Type u
  relInterp : (r : σ.RelSyms) → (w : W) → (Fin (σ.relArity r) → D w) → Prop
  funcInterp : (f : σ.FuncSyms) → (w : W) → (Fin (σ.funcArity f) → D w) → D w
  /-- Designated (primitive) domain of necessary objects of fibre `F`. -/
  Nec : (W → Type u) → (W → Type u)
  /-- Designated (primitive) domain of possible objects of fibre `F`. -/
  Pos : (W → Type u) → (W → Type u)
  /-- **Box eval**: a necessary object projects to a *dependent product* — its value at each
      accessible world.  (For `interp (□T)` this is `∀ w' accessible, interp T w'.1`.) -/
  necEval : {F : W → Type u} → {w : W} → Nec F w → ((w' : {w' : W // R w w'}) → F w'.1)
  /-- **INJECTIVE** (world-extensionality / funext): a necessary object *is* its section.  This
      is what makes `box_ext` sound.  NOT surjective (non-full ⇒ Barcan fails). -/
  nec_inj : {F : W → Type u} → {w : W} → Function.Injective (@necEval F w)
  /-- **Dia eval**: a possible object projects to its **set of realizations** — a set of pairs
      `(accessible world, value there)`, i.e. `Set (Σ' w' accessible, F w'.1)`. -/
  posEval : {F : W → Type u} → {w : W} →
      Pos F w → Set (Σ' w' : {w' : W // R w w'}, F w'.1)
  /-- **INJECTIVE**: a possible object *is* its realization set (the `◇`-side world-ext). -/
  pos_inj : {F : W → Type u} → {w : W} → Function.Injective (@posEval F w)
  /-- **Functorial lift ("map").**  A world-indexed fibre operation lifts to necessary objects.
      Being fibre-polymorphic, one `map` lifts operations to `Nec` of *any* fibre — the base
      domain, other `Nec`/`Pos` domains, and every iterated modality — so functions act on all box
      stacks with a single primitive. -/
  map : {F G : W → Type u} → {w : W} →
      ((w' : {w' : W // R w w'}) → F w'.1 → G w'.1) → Nec F w → Nec G w
  /-- Naturality of `map` (`eval ∘ lift = lift ∘ eval`). -/
  map_eval : {F G : W → Type u} → {w : W} →
      (op : (w' : {w' : W // R w w'}) → F w'.1 → G w'.1) → (n : Nec F w) →
      (w' : {w' : W // R w w'}) → necEval (map op n) w' = op w' (necEval n w')
  /-- **Monoidal product ("zip").**  Pair two necessary objects into a necessary object of pairs;
      with `map`/`unitNec` this assembles multi-argument function applications. -/
  zip : {F G : W → Type u} → {w : W} → Nec F w → Nec G w → Nec (fun w'' => F w'' × G w'') w
  /-- Naturality of `zip`. -/
  zip_eval : {F G : W → Type u} → {w : W} → (x : Nec F w) → (y : Nec G w) →
      (w' : {w' : W // R w w'}) → necEval (zip x y) w' = (necEval x w', necEval y w')
  /-- **Monoidal unit.**  The necessary object over the unit type — interprets `boxterm unit`, and
      is the base a nullary constant is `map`ped onto (there being no argument to `map` from).
      (Its section is `⋆`, forced by `PUnit` being a subsingleton; the field only asserts it exists;
      likewise `nec_inj` makes the monoidal coherence laws automatic.) -/
  unitNec : {w : W} → Nec (fun _ => PUnit) w
  /-- **Possible-object functorial map.**  The `Pos` analog of `map`: a fibre operation acts on each
      realization of a possible object.  (The `◇`-side lift, used for functions under `◇`.) -/
  mapPos : {F G : W → Type u} → {w : W} →
      ((w' : {w' : W // R w w'}) → F w'.1 → G w'.1) → Pos F w → Pos G w
  /-- Naturality of `mapPos`: `⟨w', b⟩` realizes `mapPos g x` iff some `⟨w', a⟩` realizes `x` with
      `g w' a = b` (the realization set of the image is the image of the realization set). -/
  mapPos_eval : {F G : W → Type u} → {w : W} →
      (g : (w' : {w' : W // R w w'}) → F w'.1 → G w'.1) → (x : Pos F w) →
      (ru : Σ' w' : {w' : W // R w w'}, G w'.1) →
      (ru ∈ posEval (mapPos g x) ↔
        ∃ a : F ru.1.1, (⟨ru.1, a⟩ : Σ' w' : {w' : W // R w w'}, F w'.1) ∈ posEval x
          ∧ g ru.1 a = ru.2)

namespace RModel

variable {σ : Signature}

/-- The domain of each syntactic type at each world.  `Var`/`VTypeOne` are the base domain and
    the unit; **products *are* products** (ordinary `×`, with `⟨·,·⟩`/`.1`/`.2` as the maps
    in/out); the modal types are the designated `Nec`/`Pos` domains. -/
def interp (M : RModel σ) : VarType → M.W → Type u
  | .Var,           w => M.D w
  | .VTypeOne,      _ => PUnit
  | .VTypeProd A B, w => M.interp A w × M.interp B w
  | .VTypeBox T,    w => M.Nec (M.interp T) w
  | .VTypeDia T,    w => M.Pos (M.interp T) w

@[simp] theorem interp_Var (M : RModel σ) (w : M.W) : M.interp .Var w = M.D w := rfl
@[simp] theorem interp_prod (M : RModel σ) (A B : VarType) (w : M.W) :
    M.interp (.VTypeProd A B) w = (M.interp A w × M.interp B w) := rfl
@[simp] theorem interp_box (M : RModel σ) (T : VarType) (w : M.W) :
    M.interp (.VTypeBox T) w = M.Nec (M.interp T) w := rfl
@[simp] theorem interp_dia (M : RModel σ) (T : VarType) (w : M.W) :
    M.interp (.VTypeDia T) w = M.Pos (M.interp T) w := rfl

/-! ### The product maps, spelled out (they are just `Prod` — recorded for readability). -/

/-- Pair two objects into a product object. -/
def pair (M : RModel σ) {A B : VarType} {w : M.W}
    (a : M.interp A w) (b : M.interp B w) : M.interp (.VTypeProd A B) w := (a, b)

/-- First projection out of a product object. -/
def fst (M : RModel σ) {A B : VarType} {w : M.W}
    (p : M.interp (.VTypeProd A B) w) : M.interp A w := p.1

/-- Second projection out of a product object. -/
def snd (M : RModel σ) {A B : VarType} {w : M.W}
    (p : M.interp (.VTypeProd A B) w) : M.interp B w := p.2

/-! ### Interpretation of terms

Unlike `SemanticsGeneral2`, `interpTerm` here is **not** carried as data with coherence laws — it is
an ordinary `def` (the FOL pattern), computed from the model's operations.  Function symbols act on
every domain, not just the base one: `funcInterp` at each world *and* `funcNec` on necessary
objects, related by the naturality law `funcNec_eval`.  So `boxterm (f …)` denotes by *applying the
lift* `funcNec f`, with no general `necIntro` — and the naturality law is exactly what makes the
`box`-value's section agree with the body interpreted downstream. -/

/-- Environments: an assignment of a domain value *at world `w`* to each variable of context `V`.
    (Identical to `GModel.Env`.) -/
def Env (M : RModel σ) (V : VarCtx) (w : M.W) : Type u :=
  (p : VarSymb × VarType) → p ∈ V.1 → M.interp p.2 w

/-- Extend an environment for a freshly-bound variable.  (Identical to `GModel.Env.extend`.) -/
def Env.extend {M : RModel σ} {V : VarCtx} {w : M.W} (env : M.Env V w)
    (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V) (a : M.interp x.2 w) :
    M.Env (VarCtx_insert x V hx) w :=
  fun q hq =>
    if h : q = x then h ▸ a
    else env q ((Finset.mem_insert.mp hq).resolve_left h)

/-- Push a `□`-environment to an accessible world by `necEval`-ing each boxed variable.
    (Identical to `GModel.Env.boxPush`.) -/
def Env.boxPush {M : RModel σ} {V_inner W : VarCtx} {w : M.W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (env : M.Env W w)
    (w' : {w' : M.W // M.R w w'}) : M.Env V_inner w'.1 :=
  fun p hp => M.necEval (env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))) w'

/-- **Split an environment at a product-typed variable.**  Given `env` over a context containing
    `z : A ×ᵥ B`, produce an environment over the "components" context `V + {v₁ : A, v₂ : B}` that
    binds `v₁`/`v₂` to `z`'s projections.  This *is* the semantic content of `pair_elim` (the
    product recursor): `interp (A ×ᵥ B) = interp A × interp B`, so `z` splits transparently. -/
def Env.unpairEnv {M : RModel σ} {V W₂ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    (hv₁v₂ : v₁.1 ≠ v₂.1) {hz : z ∉ VarCtx_to_VarSymbs V}
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (env : M.Env W₂ w) :
    M.Env (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂) w :=
  fun p hp =>
    if h1 : p = v₁ then
      (by rw [h1]; exact (env ⟨z, .VTypeProd v₁.2 v₂.2⟩ (W₂eq ▸ Finset.mem_insert_self _ _)).1)
    else if h2 : p = v₂ then
      (by rw [h2]; exact (env ⟨z, .VTypeProd v₁.2 v₂.2⟩ (W₂eq ▸ Finset.mem_insert_self _ _)).2)
    else env p (by
      have hpV : p ∈ V.1 := by
        rcases Finset.mem_insert.mp hp with h | h
        · exact absurd h h1
        · rcases Finset.mem_insert.mp h with h' | h'
          · exact absurd h' h2
          · exact h'
      exact W₂eq ▸ Finset.mem_insert_of_mem hpV)

/-- Applying a context-transported environment reindexes the membership proof. -/
theorem Env_transport_apply {M : RModel σ} {W1 W2 : VarCtx} {w : M.W} (h : W1 = W2)
    (F : M.Env W1 w) (p : VarSymb × VarType) (hp : p ∈ W2.1) :
    (h ▸ F) p hp = F p (h ▸ hp) := by subst h; rfl

/-- `Env.unpairEnv` at `v₁` reads the first projection of the boxed product `z`. -/
theorem Env.unpairEnv_apply_v₁ {M : RModel σ} {V W₂ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    (hv₁v₂ : v₁.1 ≠ v₂.1) {hz : z ∉ VarCtx_to_VarSymbs V}
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂) (env : M.Env W₂ w)
    (hp : v₁ ∈ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂).1)
    (hzs : (⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ W₂.1) :
    Env.unpairEnv hv₁v₂ W₂eq env v₁ hp = (env ⟨z, .VTypeProd v₁.2 v₂.2⟩ hzs).1 := by
  simp only [Env.unpairEnv]
  rw [dif_pos trivial, eq_mpr_eq_cast]; exact eq_of_heq (cast_heq _ _)

/-- `Env.unpairEnv` at `v₂` reads the second projection of the boxed product `z`. -/
theorem Env.unpairEnv_apply_v₂ {M : RModel σ} {V W₂ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    (hv₁v₂ : v₁.1 ≠ v₂.1) {hz : z ∉ VarCtx_to_VarSymbs V}
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂) (env : M.Env W₂ w)
    (hp : v₂ ∈ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂).1)
    (hzs : (⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ W₂.1) :
    Env.unpairEnv hv₁v₂ W₂eq env v₂ hp = (env ⟨z, .VTypeProd v₁.2 v₂.2⟩ hzs).2 := by
  have hne : ¬ (v₂ = v₁) := fun h => hv₁v₂ (congrArg Prod.fst h).symm
  simp only [Env.unpairEnv, dif_neg hne]
  rw [dif_pos trivial, eq_mpr_eq_cast]; exact eq_of_heq (cast_heq _ _)

/-- `Env.unpairEnv` at any other variable just reads `env`. -/
theorem Env.unpairEnv_apply_other {M : RModel σ} {V W₂ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    (hv₁v₂ : v₁.1 ≠ v₂.1) {hz : z ∉ VarCtx_to_VarSymbs V}
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂) (env : M.Env W₂ w)
    {q : VarSymb × VarType} (hp : q ∈ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂).1)
    (h1 : q ≠ v₁) (h2 : q ≠ v₂) (hqW : q ∈ W₂.1) :
    Env.unpairEnv hv₁v₂ W₂eq env q hp = env q hqW := by
  simp only [Env.unpairEnv, dif_neg h1, dif_neg h2]

/-! ### The function lift, now *derived* from the applicative structure

`funcNec` is no longer a primitive field — it is built from `map`/`zip`/`unitNec`.  Only the nullary
(constant) case genuinely needs `unitNec`; everything else is `map` on a `zip`-folded argument
vector.  Its naturality is likewise a *theorem*, `funcNec_eval`, not an axiom. -/

/-- Fold a vector of necessary objects into a necessary object of vectors via `zip` (nullary base:
    `map` off `unitNec`). -/
def zipVec (M : RModel σ) {w : M.W} : {n : ℕ} → (Fin n → M.Nec M.D w) →
    M.Nec (fun w'' => Fin n → M.D w'') w
  | 0,     _    => M.map (fun w'' _ => (Fin.elim0 : Fin 0 → M.D w''.1)) M.unitNec
  | _ + 1, args =>
      M.map (fun _ p => Fin.cons p.1 p.2) (M.zip (args 0) (M.zipVec (fun i => args i.succ)))

/-- **The function lift, derived:** apply `funcInterp` fibrewise to the zipped arguments. -/
def funcNec (M : RModel σ) (f : σ.FuncSyms) {w : M.W}
    (args : Fin (σ.funcArity f) → M.Nec M.D w) : M.Nec M.D w :=
  M.map (fun w'' g => M.funcInterp f w''.1 g) (M.zipVec args)

/-- `zipVec`'s section is the vector of the arguments' sections. -/
theorem zipVec_eval (M : RModel σ) {w : M.W} :
    ∀ {n : ℕ} (args : Fin n → M.Nec M.D w) (w' : {w' : M.W // M.R w w'}),
    M.necEval (M.zipVec args) w' = fun i => M.necEval (args i) w'
  | 0,     _,    _  => by funext i; exact i.elim0
  | _ + 1, args, w' => by
      simp only [zipVec, M.map_eval, M.zip_eval]
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j; simp only [Fin.cons_succ]; rw [M.zipVec_eval]

/-- **Naturality of the (derived) function lift** — now a *theorem*: `map_eval` + `zipVec_eval`. -/
theorem funcNec_eval (M : RModel σ) (f : σ.FuncSyms) {w : M.W}
    (args : Fin (σ.funcArity f) → M.Nec M.D w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.funcNec f args) w' = M.funcInterp f w'.1 (fun i => M.necEval (args i) w') := by
  simp only [funcNec, M.map_eval, M.zipVec_eval]

/-! ### Modality-stack machinery for the box-lift

The box-lift `interpTermNec` must descend through an ambient stack of `□`s (a body under `□⋯□`).
Because `◇`/pairs are *consumed* (terminal `mapPos`/`zip`), never descended through, that stack is
just a `□`-count `Stk`.  `plug c S = □^c S` is the type produced at stack `c`; the box-lift is
`interpTermNecStk (.box .hole)`.  These helpers (`stkUnit`/`stkZip`/`funcNecStk`/`zipVecG`) lift the
base operations through the stack; `promoteDia`/`diaBuild` handle the `◇`-under-`□` arm.  (Validated
first in `SoundnessReal.lean`, then folded here into the `interpTerm` mutual block.) -/

/-- The ambient stack of a box-lift is **boxes-only**, so it is just a `□`-count.  `plug c S = □^c S`
    (outermost box last). -/
inductive Stk where
  | hole
  | box (c : Stk)

/-- Wrap `S` in the stack's boxes (outermost box last). -/
def Stk.plug : Stk → VarType → VarType
  | .hole,  S => S
  | .box c, S => (c.plug S).VTypeBox

/-- Number of boxes in the stack — the third component of the box-lift's termination measure. -/
def Stk.size : Stk → ℕ
  | .hole  => 0
  | .box c => c.size + 1

def Stk.snocBox : Stk → Stk
  | .hole  => .box .hole
  | .box c => .box c.snocBox

theorem Stk.snocBox_plug : ∀ (c : Stk) (S : VarType), c.snocBox.plug S = c.plug S.VTypeBox
  | .hole,  _ => rfl
  | .box c, S => by simp only [Stk.snocBox, Stk.plug, Stk.snocBox_plug c]

/-- The `c`-promotion of the diaterm's `dia`-context `dia x V_dia`: each variable's type wrapped in
    `c`'s boxes.  `diaBuild` threads the environment over this as it walks the stack. -/
def promoteDia (V_dia : VarCtx) (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V_dia) :
    Stk → VarCtx
  | .hole  => VarCtx_dia x V_dia hx
  | .box c => VarCtx_box (promoteDia V_dia x hx c)

theorem promoteDia_char (V_dia : VarCtx) (x : VarSymb × VarType)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V_dia) :
    ∀ (c : Stk) (q : VarSymb × VarType),
      q ∈ (promoteDia V_dia x hx c).1
        ↔ ∃ p ∈ (VarCtx_dia x V_dia hx).1, q = ⟨p.1, c.plug p.2⟩
  | .hole, q => by
      constructor
      · intro hq; exact ⟨q, hq, rfl⟩
      · rintro ⟨p, hp, rfl⟩; exact hp
  | .box c, q => by
      simp only [promoteDia, VarCtx_box, Finset.mem_image, Stk.plug]
      constructor
      · rintro ⟨r, hr, rfl⟩
        obtain ⟨p, hp, rfl⟩ := (promoteDia_char V_dia x hx c r).mp hr
        exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p.1, c.plug p.2⟩, (promoteDia_char V_dia x hx c _).mpr ⟨p, hp, rfl⟩, rfl⟩

/-- Stack every variable of a context through `c`'s boxes: `{⟨p.1, c.plug p.2⟩ : p ∈ V}`.
    A valid `VarCtx` (stacking preserves first components, so uniqueness is inherited).  This is the
    body-context of the `pair_elim` box-lift: the body's variables read at their stacked slots. -/
def Stk.stackCtx (c : Stk) (V : VarCtx) : VarCtx := by
  refine ⟨V.1.image (fun p => (⟨p.1, c.plug p.2⟩ : VarSymb × VarType)), ?_⟩
  intro v v_im w w_im one_eq
  rcases Finset.mem_image.mp v_im with ⟨⟨av, aS⟩, hav, hveq⟩
  rcases Finset.mem_image.mp w_im with ⟨⟨bv, bS⟩, hbw, hweq⟩
  have hav1 : av = v.1 := congrArg Prod.fst hveq
  have hbw1 : bv = w.1 := congrArg Prod.fst hweq
  have hab : aS = bS := V.2 _ hav _ hbw (hav1.trans (one_eq.trans hbw1.symm))
  subst hveq; subst hweq
  exact congrArg (fun S => c.plug S) hab

theorem Stk.mem_stackCtx (c : Stk) (V : VarCtx) (q : VarSymb × VarType) :
    q ∈ (c.stackCtx V).1 ↔ ∃ p ∈ V.1, q = ⟨p.1, c.plug p.2⟩ := by
  simp only [Stk.stackCtx, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

/-- General (fibre-polymorphic) `zipVec`: fold a vector of necessary objects over any fibre `G`.
    (The model's `zipVec` is this specialised to `G = D`.) -/
def zipVecG (M : RModel σ) {G : M.W → Type u} {w : M.W} : {n : ℕ} → (Fin n → M.Nec G w) →
    M.Nec (fun w'' => Fin n → G w'') w
  | 0,     _    => M.map (fun _ _ => (Fin.elim0 : Fin 0 → G _)) M.unitNec
  | _ + 1, args =>
      M.map (fun _ p => Fin.cons p.1 p.2) (M.zip (args 0) (M.zipVecG (fun i => args i.succ)))

/-- `zipVecG`'s section is the vector of the arguments' sections (analogue of `zipVec_eval`). -/
theorem zipVecG_eval (M : RModel σ) {G : M.W → Type u} {w : M.W} :
    ∀ {n : ℕ} (args : Fin n → M.Nec G w) (w' : {w' : M.W // M.R w w'}),
    M.necEval (M.zipVecG args) w' = fun i => M.necEval (args i) w'
  | 0,     _,    _  => by funext i; exact i.elim0
  | _ + 1, args, w' => by
      simp only [zipVecG, M.map_eval, M.zip_eval]
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j; simp only [Fin.cons_succ]; rw [M.zipVecG_eval]

/-- Stacked monoidal unit: the `c`-boxed unit object.  (`unit` arm of the box-lift.) -/
def stkUnit (M : RModel σ) : (c : Stk) → {w : M.W} → M.interp (c.plug .VTypeOne) w
  | .hole,  _ => PUnit.unit
  | .box c, _ => M.map (fun _ _ => M.stkUnit c) M.unitNec

/-- Stacked monoidal product: pair two `c`-boxed objects into a `c`-boxed product.  (`pair` arm.) -/
def stkZip (M : RModel σ) {A B : VarType} : (c : Stk) → {w : M.W} →
    M.interp (c.plug A) w → M.interp (c.plug B) w → M.interp (c.plug (.VTypeProd A B)) w
  | .hole,  _, a, b => (a, b)
  | .box c, _, a, b => M.map (fun _ p => M.stkZip c p.1 p.2) (M.zip a b)

/-- First projection through the box-stack (`map`-lift of `.1`; inverse of `stkZip` on `.1`).
    Used by the `pair_elim` box-lift to split a `c`-boxed product variable. -/
def stkFst (M : RModel σ) {A B : VarType} : (c : Stk) → {w : M.W} →
    M.interp (c.plug (.VTypeProd A B)) w → M.interp (c.plug A) w
  | .hole,  _, p => p.1
  | .box c, _, X => M.map (fun _ y => M.stkFst c y) X

/-- Second projection through the box-stack. -/
def stkSnd (M : RModel σ) {A B : VarType} : (c : Stk) → {w : M.W} →
    M.interp (c.plug (.VTypeProd A B)) w → M.interp (c.plug B) w
  | .hole,  _, p => p.2
  | .box c, _, X => M.map (fun _ y => M.stkSnd c y) X

/-- Stacked function lift: apply `funcInterp f` through the `c`-box-stack to `c`-boxed arguments.
    (`funcNecStk (.box .hole) = funcNec`.)  (Base of the `func` arm.) -/
def funcNecStk (M : RModel σ) (f : σ.FuncSyms) :
    (c : Stk) → {w : M.W} → (Fin (σ.funcArity f) → M.interp (c.plug .Var) w) →
    M.interp (c.plug .Var) w
  | .hole,  w, args => M.funcInterp f w args
  | .box c, _, args => M.map (fun _ argvec => M.funcNecStk f c argvec) (M.zipVecG args)

/-- The body-environment of the `pair_elim` box-lift: over the body's *stacked* context
    `c.stackCtx W₁`, bind the two component variables `v₁,v₂` to the `stkFst`/`stkSnd` split of the
    `c`-boxed product variable `z`, and read every other variable off `env` at its stacked slot.
    (The stacked mirror of `Env.unpairEnv`; no freshness of `v₁,v₂` in `W` is needed — the body is
    reinterpreted over its *own* stacked context.) -/
def stkUnpairEnv (M : RModel σ) (c : Stk) {Vb V_inner W W₁ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs Vb) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs Vb)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs Vb)
    (W₁eq : VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂ = W₁)
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ Vb hz = V_inner)
    (hstk : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W.1)
    (env : M.Env W w) :
    M.Env (c.stackCtx W₁) w :=
  let zbox : M.interp (c.plug (VarType.VTypeProd v₁.2 v₂.2)) w :=
    env ⟨z, c.plug (VarType.VTypeProd v₁.2 v₂.2)⟩
      (hstk ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ (by rw [← W₂eq]; exact Finset.mem_insert_self _ _))
  fun q hq =>
    if h1 : q.1 = v₁.1 then
      (by
        have hq2 : q.2 = c.plug v₁.2 := by
          obtain ⟨p, hpW₁, rfl⟩ := (c.mem_stackCtx W₁ q).mp hq
          have hv₁W₁ : v₁ ∈ W₁.1 := by rw [← W₁eq]; exact Finset.mem_insert_self _ _
          rw [W₁.2 p hpW₁ v₁ hv₁W₁ h1]
        rw [hq2]; exact M.stkFst c zbox)
    else if h2 : q.1 = v₂.1 then
      (by
        have hq2 : q.2 = c.plug v₂.2 := by
          obtain ⟨p, hpW₁, rfl⟩ := (c.mem_stackCtx W₁ q).mp hq
          have hv₂W₁ : v₂ ∈ W₁.1 := by
            rw [← W₁eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          rw [W₁.2 p hpW₁ v₂ hv₂W₁ h2]
        rw [hq2]; exact M.stkSnd c zbox)
    else env q (by
      obtain ⟨p, hpW₁, rfl⟩ := (c.mem_stackCtx W₁ q).mp hq
      have hpit : p ∈ (VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂).1 := by
        rw [W₁eq]; exact hpW₁
      have hpVb : p ∈ Vb.1 := by
        rcases Finset.mem_insert.mp hpit with h | h
        · exact absurd (congrArg Prod.fst h) h1
        · rcases Finset.mem_insert.mp h with h' | h'
          · exact absurd (congrArg Prod.fst h') h2
          · exact h'
      have : (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W.1 :=
        hstk p (by rw [← W₂eq]; exact Finset.mem_insert_of_mem hpVb)
      exact this)

/-- `stkUnpairEnv` at the first component's slot reads the `stkFst` split of the boxed product. -/
theorem stkUnpairEnv_apply_v₁ (M : RModel σ) (c : Stk) {Vb V_inner W W₁ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs Vb) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs Vb)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs Vb)
    (W₁eq : VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂ = W₁)
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ Vb hz = V_inner)
    (hstk : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W.1)
    (env : M.Env W w) (hq : (⟨v₁.1, c.plug v₁.2⟩ : VarSymb × VarType) ∈ (c.stackCtx W₁).1)
    (hzs : (⟨z, c.plug (.VTypeProd v₁.2 v₂.2)⟩ : VarSymb × VarType) ∈ W.1) :
    M.stkUnpairEnv c hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq hstk env ⟨v₁.1, c.plug v₁.2⟩ hq
      = M.stkFst c (env ⟨z, c.plug (.VTypeProd v₁.2 v₂.2)⟩ hzs) := by
  simp only [stkUnpairEnv]
  rw [dif_pos trivial, eq_mpr_eq_cast]
  exact eq_of_heq (cast_heq _ _)

/-- `stkUnpairEnv` at the second component's slot reads the `stkSnd` split of the boxed product. -/
theorem stkUnpairEnv_apply_v₂ (M : RModel σ) (c : Stk) {Vb V_inner W W₁ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs Vb) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs Vb)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs Vb)
    (W₁eq : VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂ = W₁)
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ Vb hz = V_inner)
    (hstk : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W.1)
    (env : M.Env W w) (hq : (⟨v₂.1, c.plug v₂.2⟩ : VarSymb × VarType) ∈ (c.stackCtx W₁).1)
    (hzs : (⟨z, c.plug (.VTypeProd v₁.2 v₂.2)⟩ : VarSymb × VarType) ∈ W.1) :
    M.stkUnpairEnv c hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq hstk env ⟨v₂.1, c.plug v₂.2⟩ hq
      = M.stkSnd c (env ⟨z, c.plug (.VTypeProd v₁.2 v₂.2)⟩ hzs) := by
  have hne : ¬ ((⟨v₂.1, c.plug v₂.2⟩ : VarSymb × VarType).1 = v₁.1) := fun h => hv₁v₂ h.symm
  simp only [stkUnpairEnv, dif_neg hne]
  rw [dif_pos trivial, eq_mpr_eq_cast]
  exact eq_of_heq (cast_heq _ _)

/-- `stkUnpairEnv` at any other (already-present) slot just reads `env`. -/
theorem stkUnpairEnv_apply_other (M : RModel σ) (c : Stk) {Vb V_inner W W₁ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs Vb) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs Vb)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs Vb)
    (W₁eq : VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂ = W₁)
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ Vb hz = V_inner)
    (hstk : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W.1)
    (env : M.Env W w) {q : VarSymb × VarType} (hq : q ∈ (c.stackCtx W₁).1)
    (h1 : q.1 ≠ v₁.1) (h2 : q.1 ≠ v₂.1) (hqW : q ∈ W.1) :
    M.stkUnpairEnv c hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq hstk env q hq = env q hqW := by
  simp only [stkUnpairEnv, dif_neg h1, dif_neg h2]

/-- Two `stkUnpairEnv`s built from environments that agree on the variables they read (`z`'s slot and
    every base slot) are equal.  (The like-to-like congruence used in the box-lift `pair_elim`
    arms — the dependent casts match on both sides, so proof-irrelevance closes them.) -/
theorem stkUnpairEnv_congr (M : RModel σ) (c : Stk) {Vb V_inner W1 W2 W₁ : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs Vb) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs Vb)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs Vb)
    (W₁eq : VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂ = W₁)
    (W₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ Vb hz = V_inner)
    (hstk1 : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W1.1)
    (hstk2 : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W2.1)
    (env1 : M.Env W1 w) (env2 : M.Env W2 w)
    (hag : ∀ (p : VarSymb × VarType) (hp : p ∈ V_inner.1),
       env1 ⟨p.1, c.plug p.2⟩ (hstk1 p hp) = env2 ⟨p.1, c.plug p.2⟩ (hstk2 p hp))
    (q : VarSymb × VarType) (hq : q ∈ (c.stackCtx W₁).1) :
    M.stkUnpairEnv c hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq hstk1 env1 q hq
      = M.stkUnpairEnv c hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq hstk2 env2 q hq := by
  have hzin : (⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ V_inner.1 := by
    rw [← W₂eq]; exact Finset.mem_insert_self _ _
  simp only [stkUnpairEnv]
  split_ifs with h1 h2
  · congr 1
    exact congrArg (M.stkFst c) (hag ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ hzin)
  · congr 1
    exact congrArg (M.stkSnd c) (hag ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ hzin)
  · obtain ⟨p, hpW₁, rfl⟩ := (c.mem_stackCtx W₁ q).mp hq
    have hpit : p ∈ (VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂).1 := by rw [W₁eq]; exact hpW₁
    have hpVb : p ∈ Vb.1 := by
      rcases Finset.mem_insert.mp hpit with h | h
      · exact absurd (congrArg Prod.fst h) h1
      · rcases Finset.mem_insert.mp h with h' | h'
        · exact absurd (congrArg Prod.fst h') h2
        · exact h'
    exact hag p (by rw [← W₂eq]; exact Finset.mem_insert_of_mem hpVb)

mutual

/-- Interpretation of a term at a world.  The `boxterm` case now delegates to the modality-stack
    box-lift `interpTermNecStk (.box .hole)` (formerly the standalone `interpTermNec`), so the whole
    interpreter is `sorry`-free bar the pair sector. -/
def interpTerm (M : RModel σ) : {V : VarCtx} → {S : VarType} →
    (t : Term σ V S) → (w : M.W) → M.Env V w → M.interp S w
  | _, _, .var ⟨v, hv⟩,           w, env => env ⟨v, .Var⟩ hv
  | _, _, .func f,                w, env => M.interpFunc f w env Fin.elim0
  | _, _, .unit,                  _, _   => PUnit.unit
  | _, _, .pair a b,              w, env => (M.interpTerm a w env, M.interpTerm b w env)
  | _, _, .boxterm tt hsub _,     w, env =>
      M.interpTermNecStk (.box .hole)
        (fun p hp => hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)) tt w env
  | _, _, .diaterm x hx tt hsub _, w, env =>
      M.mapPos
        (fun w' v => M.interpTerm tt w'.1
          ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env w').extend x hx v))
        (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _)))
  | _, _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq body, w, env =>
      -- The product recursor: bind `v₁,v₂` to `z`'s projections, interpret the body.
      M.interpTerm body w (W₁eq ▸ Env.unpairEnv hv₁v₂ W₂eq env)
termination_by _ _ t _ _ => (Term.numNodes t, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; simp only [Term.numNodes, Func.numNodes]; omega)
    | (apply Prod.Lex.right; simp only [Stk.size]; omega)

/-- Interpret a function-symbol tree at a world (ordinary FOL recursion). -/
def interpFunc (M : RModel σ) : {V : VarCtx} → {n : ℕ} →
    (ff : Func σ V n) → (w : M.W) → M.Env V w → (Fin n → M.D w) → M.D w
  | _, _, .F hr,     w, _,   args => M.funcInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval g t, w, env, args => M.interpFunc g w env (Fin.cons (M.interpTerm t w env) args)
termination_by _ _ ff _ _ _ => (Func.numNodes ff, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; simp only [Term.numNodes, Func.numNodes]; omega)
    | (apply Prod.Lex.right; simp only [Stk.size]; omega)

/-- Modality-stack-generalised box-lift: lift `t : Term V_inner S` to the necessary/possible object
    of the *stacked* type `c.plug S`, reading each variable off `env` at its stacked slot. -/
def interpTermNecStk (M : RModel σ) : {V_inner : VarCtx} → {S : VarType} → {W : VarCtx} →
    (c : Stk) →
    (hstk : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W.1) →
    (t : Term σ V_inner S) → (w : M.W) → M.Env W w → M.interp (c.plug S) w
  | _, _, _, c, hstk, .var ⟨v, hv⟩, _, env =>
      env ⟨v, c.plug .Var⟩ (hstk ⟨v, .Var⟩ hv)
  | _, _, _, c, hstk, .func f, w, env =>
      M.interpFuncNecStk c hstk f w env Fin.elim0
  | _, _, _, c, _, .unit, _, _ => M.stkUnit c
  | _, _, _, c, hstk, .pair a b, w, env =>
      M.stkZip c (M.interpTermNecStk c hstk a w env) (M.interpTermNecStk c hstk b w env)
  | _, _, _, c, hstk, @Term.boxterm _ V_inner' _ _ tt' hsub_i _, w, env =>
      -- `□`-body: recurse on `tt'` with the stack grown by a `box` at the inner end (`snocBox`);
      -- target unchanged up to the `snocBox_plug` cast.
      Stk.snocBox_plug c _ ▸
        M.interpTermNecStk c.snocBox
          (fun p hp => by
            rw [Stk.snocBox_plug]
            exact hstk ⟨p.1, p.2.VTypeBox⟩ (hsub_i (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
          tt' w env
  | _, _, _, c, hstk, @Term.diaterm _ V_dia _ _ x hx tt hsub_d _, _, env =>
      -- `◇`-body: terminate the box-lift; `diaBuild` walks the stack, threading `env` restricted to
      -- the promoted dia-context `promoteDia c` (⊆ `W` via `hstk` + `hsub_d`).
      M.diaBuild x hx tt c (fun p hp => env p (by
        obtain ⟨r, hr, rfl⟩ := (promoteDia_char V_dia x hx c p).mp hp
        exact hstk r (hsub_d hr)))
  | _, _, _, c, hstk, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq body, w, env =>
      -- Box-lift of the product recursor: reinterpret `body` over its own *stacked* context, with
      -- `v₁,v₂` bound to the `stkFst`/`stkSnd` split of the `c`-boxed product `z` (`stkUnpairEnv`).
      M.interpTermNecStk c
        (fun p hp => (c.mem_stackCtx _ _).mpr ⟨p, hp, rfl⟩) body w
        (M.stkUnpairEnv c hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq hstk env)
termination_by _ _ _ _ _ t _ _ => (Term.numNodes t, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; simp only [Term.numNodes, Func.numNodes]; omega)
    | (apply Prod.Lex.right; simp only [Stk.size]; omega)

/-- Stacked function-tree lift: thread `.eval` arguments through `interpTermNecStk` at the same
    stack, applying `funcNecStk` at the base. -/
def interpFuncNecStk (M : RModel σ) : {V_inner : VarCtx} → {n : ℕ} → {W : VarCtx} →
    (c : Stk) → (hstk : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W.1) →
    (ff : Func σ V_inner n) → (w : M.W) → M.Env W w → (Fin n → M.interp (c.plug .Var) w) →
    M.interp (c.plug .Var) w
  | _, _, _, c, _, .F hr, _, _, args => M.funcNecStk hr.1 c (hr.2.symm ▸ args)
  | _, _, _, c, hstk, .eval g t, w, env, args =>
      M.interpFuncNecStk c hstk g w env (Fin.cons (M.interpTermNecStk c hstk t w env) args)
termination_by _ _ _ _ _ ff _ _ _ => (Func.numNodes ff, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; simp only [Term.numNodes, Func.numNodes]; omega)
    | (apply Prod.Lex.right; simp only [Stk.size]; omega)

/-- The `diaterm` box-lift: walk the `□`-stack (`map` + `boxPush` per box), then the diaterm's own
    `mapPos` over the promoted witness at the bottom, with the body evaluated (`interpTerm`) at each
    realization. -/
def diaBuild (M : RModel σ) {V_dia : VarCtx} {S_body : VarType} (x : VarSymb × VarType)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V_dia) (tt : Term σ (VarCtx_insert x V_dia hx) S_body) :
    (c : Stk) → {w : M.W} → M.Env (promoteDia V_dia x hx c) w →
    M.interp (c.plug (S_body.VTypeDia)) w
  | .hole, _, env =>
      M.mapPos (fun w'' v => M.interpTerm tt w''.1
                 ((Env.boxPush (fun _ hp => Finset.mem_insert_of_mem hp) env w'').extend x hx v))
               (env ⟨x.1, x.2.VTypeDia⟩ (Finset.mem_insert_self _ _))
  | .box c, _, env =>
      M.map (fun w' _ => M.diaBuild x hx tt c (Env.boxPush (Finset.Subset.refl _) env w'))
            (env ⟨x.1, (Stk.box c).plug (x.2.VTypeDia)⟩
              ((promoteDia_char V_dia x hx (Stk.box c) _).mpr
                 ⟨⟨x.1, x.2.VTypeDia⟩, Finset.mem_insert_self _ _, rfl⟩))
termination_by c _ _ => (Term.numNodes tt, c.size + 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; simp only [Term.numNodes, Func.numNodes]; omega)
    | (apply Prod.Lex.right; simp only [Stk.size]; omega)

end

/-- The top-level box-lift (a body over `V_inner` under a single `□`, in a context `W ⊇ □V_inner`):
    the `.box .hole` specialisation of `interpTermNecStk`.  Defeq to the old primitive `interpTermNec`
    since `(.box .hole).plug S = S.VTypeBox`. -/
def interpTermNec (M : RModel σ) {V_inner : VarCtx} {S : VarType} {W : VarCtx}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (tt : Term σ V_inner S) (w : M.W) (env : M.Env W w) :
    M.Nec (M.interp S) w :=
  M.interpTermNecStk (.box .hole)
    (fun p hp => hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)) tt w env

/-- `interpTerm` of a `boxterm` *is* the box-lift `interpTermNec` (both unfold to the same
    `interpTermNecStk (.box .hole)` call).  Lets `necEval_interpTermNec` (box β) fire on a boxterm. -/
theorem interpTerm_boxterm (M : RModel σ) {V_inner W : VarCtx} {S : VarType}
    (tt : Term σ V_inner S) (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hnbe : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (w : M.W) (env : M.Env W w) :
    M.interpTerm (Term.boxterm tt hsub hnbe) w env = M.interpTermNec hsub tt w env := by
  simp only [interpTerm, interpTermNec]

/-- The `.box .hole` specialisation of `interpFuncNecStk` (the old primitive `interpFuncNec`). -/
def interpFuncNec (M : RModel σ) {V_inner : VarCtx} {n : ℕ} {W : VarCtx}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (ff : Func σ V_inner n) (w : M.W) (env : M.Env W w)
    (args : Fin n → M.Nec M.D w) : M.Nec M.D w :=
  M.interpFuncNecStk (.box .hole)
    (fun p hp => hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)) ff w env args

/-! ### Naturality in action: `box β` with no axiom

For the cases implemented above, the box object's section already agrees with the body interpreted
at each accessible world — and it falls straight out of the lift's naturality, with **no `box β`
field imposed**.  (The general statement over all bodies `tt` is a mutual `Term`/`Func` induction —
the remaining `interpTermNec` cases — and is the next step.) -/

/-- `box β` for a **variable** body — definitional: `interpTermNec` returns the box object the
    environment holds, and `boxPush` is exactly `necEval` of it. -/
theorem necEval_interpTermNec_var (M : RModel σ) {V_inner W : VarCtx}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (v : VarSymb)
    (hv : (⟨v, .Var⟩ : VarSymb × VarType) ∈ V_inner.1)
    (w : M.W) (env : M.Env W w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.interpTermNec hsub (.var ⟨v, hv⟩) w env) w'
      = M.interpTerm (.var ⟨v, hv⟩) w'.1 (Env.boxPush hsub env w') := by
  simp only [interpTermNec, interpTermNecStk, interpTerm, Env.boxPush, Stk.plug]

/-- `box β` for a **function application** — this *is* `funcNec_eval`: the section of the lifted
    application `funcNec f` is `funcInterp f` on the arguments' sections (`interpFuncNec (.F …)`
    reduces to `funcNec` definitionally).  So `□f(x)` gets its `box β` from the **naturality of the
    function lift**, not from any imposed coherence axiom. -/
theorem necEval_interpFuncNec_F (M : RModel σ) {V_inner W : VarCtx} {n : ℕ}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (hr : {f : σ.FuncSyms // σ.funcArity f = n})
    (w : M.W) (env : M.Env W w) (args : Fin n → M.Nec M.D w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.interpFuncNec hsub (.F hr) w env args) w'
      = M.funcInterp hr.1 w'.1 (fun i => M.necEval ((hr.2.symm ▸ args) i) w') := by
  simp only [interpFuncNec, interpFuncNecStk, funcNecStk, M.map_eval, M.zipVecG_eval]

/-! ### General `box β` (mutual `Term`/`Func` induction)

`◇`-β is a single `mapPos_eval` (the `◇` interpretation *is* one `mapPos`).  `□`-β must instead be
proven by induction, composing one `map`/`zip` naturality per constructor — the price of `□` being
assembled applicatively.  The statement generalises over the box-stack: peeling one box off
`interpTermNecStk (.box c)` gives `interpTermNecStk c` with the environment pushed one world on. -/

/-- The `c`-promotion of a context: wrap each variable's type in `c`'s boxes. -/
def promote : Stk → VarCtx → VarCtx
  | .hole,  V => V
  | .box c, V => VarCtx_box (promote c V)

theorem promote_char : ∀ (c : Stk) (V : VarCtx) (q : VarSymb × VarType),
    q ∈ (promote c V).1 ↔ ∃ p ∈ V.1, q = ⟨p.1, c.plug p.2⟩
  | .hole, V, q => by
      constructor
      · intro hq; exact ⟨q, hq, rfl⟩
      · rintro ⟨p, hp, rfl⟩; exact hp
  | .box c, V, q => by
      simp only [promote, VarCtx_box, Finset.mem_image, Stk.plug]
      constructor
      · rintro ⟨r, hr, rfl⟩
        obtain ⟨p, hp, rfl⟩ := (promote_char c V r).mp hr
        exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p.1, c.plug p.2⟩, (promote_char c V _).mpr ⟨p, hp, rfl⟩, rfl⟩

/-- Peel one box off a stacked unit. -/
theorem stkUnit_box_eval (M : RModel σ) (c : Stk) {w : M.W} (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.stkUnit (.box c)) w' = M.stkUnit c := by
  simp only [stkUnit, M.map_eval]

/-- Peel one box off a stacked product (`zip` naturality). -/
theorem stkZip_box_eval (M : RModel σ) {A B : VarType} (c : Stk) {w : M.W}
    (a : M.interp ((Stk.box c).plug A) w) (b : M.interp ((Stk.box c).plug B) w)
    (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.stkZip (.box c) a b) w' = M.stkZip c (M.necEval a w') (M.necEval b w') := by
  simp only [stkZip, M.map_eval, M.zip_eval]

/-- Peel one box off a stacked first projection (`map` naturality). -/
theorem stkFst_box_eval (M : RModel σ) {A B : VarType} (c : Stk) {w : M.W}
    (X : M.interp ((Stk.box c).plug (.VTypeProd A B)) w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.stkFst (.box c) X) w' = M.stkFst c (M.necEval X w') := by
  simp only [stkFst, M.map_eval]

/-- Peel one box off a stacked second projection (`map` naturality). -/
theorem stkSnd_box_eval (M : RModel σ) {A B : VarType} (c : Stk) {w : M.W}
    (X : M.interp ((Stk.box c).plug (.VTypeProd A B)) w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.stkSnd (.box c) X) w' = M.stkSnd c (M.necEval X w') := by
  simp only [stkSnd, M.map_eval]

/-- Peel one box off a stacked function lift (`zipVec` naturality). -/
theorem funcNecStk_box_eval (M : RModel σ) (f : σ.FuncSyms) (c : Stk) {w : M.W}
    (args : Fin (σ.funcArity f) → M.interp ((Stk.box c).plug .Var) w)
    (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.funcNecStk f (.box c) args) w'
      = M.funcNecStk f c (fun i => M.necEval (args i) w') := by
  simp only [funcNecStk, M.map_eval, M.zipVecG_eval]

/-- Peel one box off `diaBuild` (`map` naturality; the box-layer of the stack walk). -/
theorem diaBuild_box_eval (M : RModel σ) {V_dia : VarCtx} {S_body : VarType}
    (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V_dia)
    (tt : Term σ (VarCtx_insert x V_dia hx) S_body) (c : Stk) {w : M.W}
    (env : M.Env (promoteDia V_dia x hx (.box c)) w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.diaBuild x hx tt (.box c) env) w'
      = M.diaBuild x hx tt c (Env.boxPush (Finset.Subset.refl _) env w') := by
  simp only [diaBuild, M.map_eval]

/-- `necEval` commutes with a `□`-cast: reading the section of a cast necessary object is the cast of
    the section.  (Used to pull the `boxterm` arm's `snocBox_plug ▸` out through `necEval`.) -/
theorem necEval_box_cast (M : RModel σ) {P Q : VarType} (he : P = Q) {w : M.W}
    (X : M.interp P.VTypeBox w) (w' : {w' : M.W // M.R w w'}) :
    M.necEval (congrArg VarType.VTypeBox he ▸ X) w' = he ▸ (M.necEval X w') := by
  subst he; rfl

/-- Two environments agreeing at `k'` also agree at any `k = k'` (kills the `snocBox_plug`-cast on the
    variable key in the `boxterm` congruence case, where `rw`/`▸` fail on the dependent motive). -/
theorem env_congr_key (M : RModel σ) {W1 W2 : VarCtx} {w : M.W}
    (env1 : M.Env W1 w) (env2 : M.Env W2 w) {k k' : VarSymb × VarType} (hk : k = k')
    (h1 : k ∈ W1.1) (h2 : k ∈ W2.1) (h1' : k' ∈ W1.1) (h2' : k' ∈ W2.1)
    (H : env1 k' h1' = env2 k' h2') : env1 k h1 = env2 k h2 := by
  subst hk; exact H

mutual
/-- **Environment-congruence for the box-lift**: `interpTermNecStk` depends only on the environment's
    values at the variables it reads (`⟨p.1, c.plug p.2⟩`), so two environments — over possibly
    distinct ambient contexts — agreeing there give the same result. -/
theorem interpTermNecStk_congr (M : RModel σ) {V_inner : VarCtx} {S : VarType} {W1 W2 : VarCtx}
    (c : Stk) (hstk1 : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W1.1)
    (hstk2 : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W2.1)
    (tt : Term σ V_inner S) (w : M.W) (env1 : M.Env W1 w) (env2 : M.Env W2 w)
    (hag : ∀ (p : VarSymb × VarType) (hp : p ∈ V_inner.1),
       env1 ⟨p.1, c.plug p.2⟩ (hstk1 p hp) = env2 ⟨p.1, c.plug p.2⟩ (hstk2 p hp)) :
    M.interpTermNecStk c hstk1 tt w env1 = M.interpTermNecStk c hstk2 tt w env2 := by
  match tt with
  | .var ⟨v, hv⟩ => simp only [interpTermNecStk]; exact hag ⟨v, .Var⟩ hv
  | .func f =>
      simp only [interpTermNecStk]
      exact interpFuncNecStk_congr M c hstk1 hstk2 f w env1 env2 hag
        Fin.elim0 Fin.elim0 (fun i => i.elim0)
  | .unit => simp only [interpTermNecStk]
  | .pair a b =>
      simp only [interpTermNecStk]
      rw [interpTermNecStk_congr M c hstk1 hstk2 a w env1 env2 hag,
          interpTermNecStk_congr M c hstk1 hstk2 b w env1 env2 hag]
  | @Term.boxterm _ V' _ _ tt' hsub_i _ =>
      -- Both sides share the same `snocBox_plug ▸` cast (c fixed), so `congr 1` strips it; the
      -- residual is the IH at `c.snocBox`, with `hag` transported along `snocBox_plug`.
      simp only [interpTermNecStk]
      congr 1
      refine interpTermNecStk_congr M c.snocBox _ _ tt' w env1 env2 (fun p hp => ?_)
      have hq : (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ∈ V_inner.1 :=
        hsub_i (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      have hkey : (⟨p.1, c.snocBox.plug p.2⟩ : VarSymb × VarType) = ⟨p.1, c.plug p.2.VTypeBox⟩ := by
        rw [Stk.snocBox_plug]
      exact env_congr_key M env1 env2 hkey _ _ _ _ (hag ⟨p.1, p.2.VTypeBox⟩ hq)
  | @Term.diaterm _ V_dia _ _ x hx tt hsub_d _ =>
      simp only [interpTermNecStk]
      congr 1
      funext p hp
      obtain ⟨r, hr, rfl⟩ := (promoteDia_char V_dia x hx c p).mp hp
      exact hag r (hsub_d hr)
  | @Term.pair_elim _ Vb _ _ _ v₁ v₂ z hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq body =>
      -- Both sides recurse on `body` over `c.stackCtx W₁`; reduce via the IH to `stkUnpairEnv_congr`
      -- (the two `stkUnpairEnv`s agree because `env1,env2` agree at `z`'s slot and every base slot).
      simp only [interpTermNecStk]
      refine interpTermNecStk_congr M c _ _ body w _ _ (fun p hp => ?_)
      exact stkUnpairEnv_congr M c hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq hstk1 hstk2 env1 env2 hag _ _

theorem interpFuncNecStk_congr (M : RModel σ) {V_inner : VarCtx} {n : ℕ} {W1 W2 : VarCtx}
    (c : Stk) (hstk1 : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W1.1)
    (hstk2 : ∀ p ∈ V_inner.1, (⟨p.1, c.plug p.2⟩ : VarSymb × VarType) ∈ W2.1)
    (ff : Func σ V_inner n) (w : M.W) (env1 : M.Env W1 w) (env2 : M.Env W2 w)
    (hag : ∀ (p : VarSymb × VarType) (hp : p ∈ V_inner.1),
       env1 ⟨p.1, c.plug p.2⟩ (hstk1 p hp) = env2 ⟨p.1, c.plug p.2⟩ (hstk2 p hp))
    (args1 args2 : Fin n → M.interp (c.plug .Var) w) (hargs : ∀ i, args1 i = args2 i) :
    M.interpFuncNecStk c hstk1 ff w env1 args1 = M.interpFuncNecStk c hstk2 ff w env2 args2 := by
  match ff with
  | .F hr => simp only [interpFuncNecStk]; rw [show args1 = args2 from funext hargs]
  | .eval g t =>
      simp only [interpFuncNecStk]
      exact interpFuncNecStk_congr M c hstk1 hstk2 g w env1 env2 hag
        (Fin.cons (M.interpTermNecStk c hstk1 t w env1) args1)
        (Fin.cons (M.interpTermNecStk c hstk2 t w env2) args2)
        (fun i => Fin.cases (interpTermNecStk_congr M c hstk1 hstk2 t w env1 env2 hag) hargs i)
end

mutual
/-- **General box β** (stack form): peeling one box off the box-lift `interpTermNecStk (.box c)` and
    reading its section at `w'` is the box-lift at stack `c` with the environment pushed to `w'`. -/
theorem box_beta_stk (M : RModel σ) : {V_inner : VarCtx} → {S : VarType} → {W : VarCtx} →
    (c : Stk) → (hstk : ∀ p ∈ V_inner.1, (⟨p.1, (Stk.box c).plug p.2⟩ : VarSymb × VarType) ∈ W.1) →
    (tt : Term σ V_inner S) → (w : M.W) → (env : M.Env W w) → (w' : {w' : M.W // M.R w w'}) →
    M.necEval (M.interpTermNecStk (.box c) hstk tt w env) w'
      = M.interpTermNecStk c (fun p hp => (promote_char c V_inner _).mpr ⟨p, hp, rfl⟩) tt w'.1
          (Env.boxPush (fun q hq => by
            obtain ⟨p, hp, rfl⟩ := (promote_char (.box c) V_inner q).mp hq; exact hstk p hp) env w')
  | _, _, _, c, hstk, .var ⟨v, hv⟩, w, env, w' => by
      simp only [interpTermNecStk, Env.boxPush, Stk.plug]
  | _, _, _, c, hstk, .unit, w, env, w' => by
      simp only [interpTermNecStk, stkUnit_box_eval]
  | _, _, _, c, hstk, .pair a b, w, env, w' => by
      simp only [interpTermNecStk]
      rw [stkZip_box_eval, box_beta_stk M c hstk a w env w', box_beta_stk M c hstk b w env w']
  | _, _, _, c, hstk, .func f, w, env, w' => by
      simp only [interpTermNecStk]
      rw [box_beta_func_stk M c hstk f w env Fin.elim0 w']
      congr 1
      funext i
      exact i.elim0
  | _, _, _, c, hstk, @Term.boxterm _ _ _ _ tt' hsub_i _, w, env, w' => by
      -- Pull the boxterm arm's `snocBox_plug ▸` out through `necEval` (`necEval_box_cast`), apply the
      -- IH at `c.snocBox`, then reconcile the two pushed environments with `interpTermNecStk_congr`
      -- (both `boxPush`es read the same boxed entry of `env`).
      simp only [interpTermNecStk, Stk.snocBox]
      rw [necEval_box_cast]
      swap
      exact Stk.snocBox_plug c _
      rw [box_beta_stk M c.snocBox _ tt' w env w']
      congr 1
      exact interpTermNecStk_congr M c.snocBox _ _ tt' w'.1 _ _ (fun _ _ => rfl)
  | _, _, _, c, hstk, @Term.diaterm _ V_dia _ _ x hx tt hsub_d _, w, env, w' => by
      -- `diaBuild_box_eval` pulls the box off; the two pushed environments are then defeq (both
      -- `necEval` the same boxed entry of `env`), so `congr 1` closes it.
      simp only [interpTermNecStk]
      rw [diaBuild_box_eval]
      congr 1
  | _, _, _, c, hstk, @Term.pair_elim _ Vb _ _ _ v₁ v₂ z hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq body, w, env, w' => by
      -- Peel the box on the (recursed) LHS via the IH, then reconcile `boxPush∘stkUnpairEnv(.box c)`
      -- with `stkUnpairEnv(c)∘boxPush` slot-by-slot (`stkFst/stkSnd_box_eval` + `boxPush` reads).
      simp only [interpTermNecStk]
      rw [box_beta_stk M c _ body w _ w']
      refine interpTermNecStk_congr M c _ _ body w'.1 _ _ (fun p hp => ?_)
      have hpit : p ∈ (VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂).1 := W₁eq ▸ hp
      rcases Finset.mem_insert.mp hpit with rfl | hp'
      · simp [stkUnpairEnv, Env.boxPush, stkFst, Stk.plug, M.map_eval]
      · rcases Finset.mem_insert.mp hp' with rfl | hpVb
        · have hne1 : ¬ (p.1 = v₁.1) := fun h => hv₁v₂ h.symm
          simp [stkUnpairEnv, Env.boxPush, stkSnd, Stk.plug, M.map_eval, dif_neg hne1]
        · have h1 : p.1 ≠ v₁.1 := fun h => hv₁ (h ▸ Finset.mem_image.mpr ⟨p, hpVb, rfl⟩)
          have h2 : p.1 ≠ v₂.1 := fun h => hv₂ (h ▸ Finset.mem_image.mpr ⟨p, hpVb, rfl⟩)
          simp [stkUnpairEnv, Env.boxPush, Stk.plug, dif_neg h1, dif_neg h2]

theorem box_beta_func_stk (M : RModel σ) : {V_inner : VarCtx} → {n : ℕ} → {W : VarCtx} →
    (c : Stk) → (hstk : ∀ p ∈ V_inner.1, (⟨p.1, (Stk.box c).plug p.2⟩ : VarSymb × VarType) ∈ W.1) →
    (ff : Func σ V_inner n) → (w : M.W) → (env : M.Env W w) →
    (args : Fin n → M.interp ((Stk.box c).plug .Var) w) → (w' : {w' : M.W // M.R w w'}) →
    M.necEval (M.interpFuncNecStk (.box c) hstk ff w env args) w'
      = M.interpFuncNecStk c (fun p hp => (promote_char c V_inner _).mpr ⟨p, hp, rfl⟩) ff w'.1
          (Env.boxPush (fun q hq => by
            obtain ⟨p, hp, rfl⟩ := (promote_char (.box c) V_inner q).mp hq; exact hstk p hp) env w')
          (fun i => M.necEval (args i) w')
  | _, _, _, c, hstk, .F hr, w, env, args, w' => by
      obtain ⟨f, hf⟩ := hr
      subst hf
      simp only [interpFuncNecStk, funcNecStk_box_eval]
  | _, _, _, c, hstk, .eval g t, w, env, args, w' => by
      simp only [interpFuncNecStk]
      rw [box_beta_func_stk M c hstk g w env
            (Fin.cons (M.interpTermNecStk (.box c) hstk t w env) args) w']
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i
      · simpa only [Fin.cons_zero] using box_beta_stk M c hstk t w env w'
      · intro j; simp only [Fin.cons_succ]
end

mutual
/-- The box-lift at the **empty** stack is ordinary interpretation — the bridge from
    `interpTermNecStk` back to `interpTerm` (used for the top-level `box β` corollary). -/
theorem interpTermNecStk_hole (M : RModel σ) {V_inner : VarCtx} {S : VarType}
    (tt : Term σ V_inner S) (w : M.W) (env : M.Env V_inner w) :
    M.interpTermNecStk .hole (fun p hp => hp) tt w env = M.interpTerm tt w env := by
  match tt with
  | .var ⟨v, hv⟩ => simp only [interpTermNecStk, interpTerm, Stk.plug]
  | .func f =>
      simp only [interpTermNecStk, interpTerm]
      exact interpFuncNecStk_hole M f w env Fin.elim0
  | .unit => simp only [interpTermNecStk, interpTerm, stkUnit]
  | .pair a b =>
      simp only [interpTermNecStk, interpTerm, stkZip]
      rw [interpTermNecStk_hole M a w env, interpTermNecStk_hole M b w env]
  | @Term.boxterm _ _ _ _ tt' hsub_i _ =>
      simp only [interpTerm, interpTermNecStk, Stk.snocBox]
  | @Term.diaterm _ V_dia _ _ x hx tt hsub_d _ =>
      simp only [interpTermNecStk, interpTerm, diaBuild]
      congr 1
  | @Term.pair_elim _ Vb _ _ _ v₁ v₂ z hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq body =>
      -- Bridge the box-lift-at-`.hole` of `pair_elim` to `interpTerm` of `pair_elim`: reconcile the
      -- recursion's `stkUnpairEnv .hole` with `Env.unpairEnv` (agree by the apply-lemmas), then the IH.
      have hzs : (⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ V_inner.1 := by
        rw [← W₂eq]; exact Finset.mem_insert_self _ _
      simp only [interpTermNecStk, interpTerm]
      refine (interpTermNecStk_congr M .hole _ (fun p hp => hp) body w _
        (W₁eq ▸ Env.unpairEnv hv₁v₂ W₂eq env) (fun p hp => ?_)).trans
        (interpTermNecStk_hole M body w _)
      -- reindex the `W₁eq ▸` transport, then agree slot-by-slot: `stkUnpairEnv .hole` and
      -- `Env.unpairEnv` both dispatch to `stkFst/stkSnd .hole = .1/.2` of the same boxed `z` (or `env`).
      rw [Env_transport_apply]
      have hpit : p ∈ (VarCtx_insert_twice v₁ v₂ Vb hv₁ hv₂ hv₁v₂).1 := W₁eq ▸ hp
      rcases Finset.mem_insert.mp hpit with rfl | hp'
      · simp [stkUnpairEnv, Env.unpairEnv, stkFst, Stk.plug]
      · rcases Finset.mem_insert.mp hp' with rfl | hpVb
        · have hne1 : ¬ (p.1 = v₁.1) := fun h => hv₁v₂ h.symm
          have hne2 : ¬ (p = v₁) := fun h => hv₁v₂ (congrArg Prod.fst h).symm
          simp [stkUnpairEnv, Env.unpairEnv, stkSnd, Stk.plug, dif_neg hne1, dif_neg hne2]
        · have h1 : p.1 ≠ v₁.1 := fun h => hv₁ (h ▸ Finset.mem_image.mpr ⟨p, hpVb, rfl⟩)
          have h2 : p.1 ≠ v₂.1 := fun h => hv₂ (h ▸ Finset.mem_image.mpr ⟨p, hpVb, rfl⟩)
          have h1' : (⟨p.1, Stk.hole.plug p.2⟩ : VarSymb × VarType) ≠ v₁ :=
            fun h => h1 (congrArg Prod.fst h)
          have h2' : (⟨p.1, Stk.hole.plug p.2⟩ : VarSymb × VarType) ≠ v₂ :=
            fun h => h2 (congrArg Prod.fst h)
          simp only [stkUnpairEnv, Env.unpairEnv, dif_neg h1, dif_neg h2, dif_neg h1', dif_neg h2']

theorem interpFuncNecStk_hole (M : RModel σ) {V_inner : VarCtx} {n : ℕ}
    (ff : Func σ V_inner n) (w : M.W) (env : M.Env V_inner w) (args : Fin n → M.D w) :
    M.interpFuncNecStk .hole (fun p hp => hp) ff w env args = M.interpFunc ff w env args := by
  match ff with
  | .F hr => simp only [interpFuncNecStk, interpFunc, funcNecStk]
  | .eval g t =>
      simp only [interpFuncNecStk, interpFunc]
      rw [interpTermNecStk_hole M t w env]
      exact interpFuncNecStk_hole M g w env _
end

/-- **General `box β`** (the usable, top-level form): the section of the box-lift `interpTermNec tt`
    at an accessible world `w'` is the body `tt` interpreted at `w'` under the pushed environment.
    Now a *theorem* (`box_beta_stk .hole` + `interpTermNecStk_hole`), with no `box β` model field. -/
theorem necEval_interpTermNec (M : RModel σ) {V_inner W : VarCtx} {S : VarType}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1) (tt : Term σ V_inner S) (w : M.W) (env : M.Env W w)
    (w' : {w' : M.W // M.R w w'}) :
    M.necEval (M.interpTermNec hsub tt w env) w'
      = M.interpTerm tt w'.1 (Env.boxPush hsub env w') := by
  simp only [interpTermNec]
  rw [box_beta_stk M .hole _ tt w env w']
  exact interpTermNecStk_hole M tt w'.1 _

/-!
### NEXT STEPS (not yet built)

DONE: `interpTerm` — `var`, `func`, `unit`, `pair`, and top-level `diaterm` (via `mapPos`);
`interpTermNec` — `var`, `func`, `unit` (via `unitNec`), `pair` (via `zip`).

Remaining `sorry`s split into two groups:
1. **Nested-modality arms** — `interpTermNec.boxterm` (□ under □) and `interpTermNec.diaterm` (◇
   under □).  These are *not* one-line applications: lifting a body whose variables are themselves
   `Nec`/`Pos`-valued needs `interpTermNec` **generalised to lift over an arbitrary fibre** (the
   modality stack), because `map` needs an existing object to act on and there's no single one to
   fold the whole body over.  This is exactly the **box-recursion** the `GModel` soundness proof
   (`interpWFF_substVar`, `substVar_boxterm_*`) already tackles — so it's most efficient to finish
   it once on `GModel` and bring it over with the port, not solve it twice.
2. **Pair arms** — `interpTerm.pair_elim`, `interpTermNec.pair_elim` (deferred to post-port).

Then **general `box β`**: `necEval (interpTermNec hsub tt w env) w' = interpTerm tt w'.1 (boxPush)`
for all `tt`, by mutual `Term`/`Func` induction.  The `var`/`func` base cases are the two lemmas
below; `unit`/`pair` are clean inductive steps (`unitNec` trivial, `pair` = `zip_eval` + IH); only
the nested arms of (1) block the *full* theorem.  It is now a *theorem*, not a model field — the
payoff of the refactor.  (Until the stubbed arms are filled, anything referencing the mutual
`interpTerm` inherits a transitive `sorry` flag; the base-case proofs themselves are complete.)
4. **`interpWFF`** ported from `SemanticsGeneral2`; truth of closed formulas is read at `actual`.
5. **Soundness** holds for *every* model (injective eval ⇒ `box_ext` sound; junk objects and a
   non-injective `interpTerm` do no harm).  **Completeness** uses the canonical model: `interp S w
   := Term S` (at `w`'s context) mod provable equality, `interpTerm` = the quotient (faithful, no
   junk), `nec_inj` forced by `box_ext`.
-/

end RModel
