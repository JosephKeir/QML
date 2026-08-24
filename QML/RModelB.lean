import QML.QML_Full_v9

/-!
# `RFrame` / `RModel` — the redesigned (VarType-indexed, distributing) completeness model

Design (memory `project-qml-rmodel-port`).  The model interface is deliberately small and two-sided:

* a frame + `funcInterp` (the only *interpretation* datum, shared);
* **`Nec`** — necessary objects (some sub-collection of sections), closed under the **function
  symbols** (`funcNecStk`); pairs are *free* because `□` distributes (`interp (□(A×B)) = interp (□A)
  × interp (□B)`, via `interpN`);
* **`Pos`** — possible objects (some sub-collection of realization sets), closed under the
  **generalised, product-aware function algebra** `GFunc` (`posLift`); pairs are *not* free (`◇`
  does not distribute), which is exactly why the extra `prod` (`×`) generator is needed;
* **the strength** (`posStrength`) — a necessary object may ride along inside any given possible
  object (correlation-free because `Nec` is total): the semantic content of `□Γ, ◇y ⊢ ◇t`.

"Full or proper" is *not* decided by the structure: a full model realizes every section/realization
set, the canonical model only the denotable ones — both are closed under the algebra + strength.

Two-layer split (`RFrame` data + `RFrame.interp` computing `def` + `RModel` ops) because the op/eval
fields mention `interp`, which only exists once the frame's domains are given.
-/

universe u

/-- **Frame layer** (pure data).  Free modal domains = the **box-towers over the atoms**:
    `NecVar k = interp (□^{k+1} Var)`, `NecDia k U = interp (□^{k+1} ◇U)`, `Pos U = interp (◇U)`.
    Products/unit are *not* stored — they distribute (see `interpN`). -/
structure RFrame (σ : Signature) where
  W : Type u
  actual : W
  R : W → W → Prop
  D : W → Type u
  relInterp : (r : σ.RelSyms) → (w : W) → (Fin (σ.relArity r) → D w) → Prop
  funcInterp : (f : σ.FuncSyms) → (w : W) → (Fin (σ.funcArity f) → D w) → D w
  /-- `interp (□^{k+1} Var)` — necessary individuals `k+1` boxes deep. -/
  NecVar : ℕ → W → Type u
  /-- `interp (◇U)` — possible objects.  Free at every `U` (`◇` does not distribute over `×`). -/
  Pos : VarType → W → Type u
  /-- `interp (□^{k+1} ◇U)` — necessary possible objects `k+1` boxes deep. -/
  NecDia : ℕ → VarType → W → Type u

namespace RFrame

variable {σ : Signature}

/-- `interpN k V = interp (□^k V)`.  `□` distributes over `×`/`1` at every depth; the box case pushes
    one more box inward (`□^k (□U) = □^{k+1} U`); the leaves are the frame's tower domains. -/
def interpN (M : RFrame σ) : VarType → ℕ → M.W → Type u
  | .VTypeProd A B, k,     w => M.interpN A k w × M.interpN B k w
  | .VTypeOne,      _,     _ => PUnit
  | .Var,           0,     w => M.D w
  | .Var,           k + 1, w => M.NecVar k w
  | .VTypeDia U,    0,     w => M.Pos U w
  | .VTypeDia U,    k + 1, w => M.NecDia k U w
  | .VTypeBox U,    k,     w => M.interpN U (k + 1) w

/-- The domain of each type at each world: `interp V = interpN V 0`. -/
def interp (M : RFrame σ) (V : VarType) (w : M.W) : Type u := M.interpN V 0 w

@[simp] theorem interp_Var (M : RFrame σ) (w : M.W) : M.interp .Var w = M.D w := rfl
@[simp] theorem interp_one (M : RFrame σ) (w : M.W) : M.interp .VTypeOne w = PUnit := rfl
@[simp] theorem interp_prod (M : RFrame σ) (A B : VarType) (w : M.W) :
    M.interp (.VTypeProd A B) w = (M.interp A w × M.interp B w) := rfl
@[simp] theorem interp_dia (M : RFrame σ) (U : VarType) (w : M.W) :
    M.interp (.VTypeDia U) w = M.Pos U w := rfl
/-- **Box distributes over products — definitionally.** -/
@[simp] theorem interp_box_prod (M : RFrame σ) (A B : VarType) (w : M.W) :
    M.interp (.VTypeBox (.VTypeProd A B)) w
      = (M.interp (.VTypeBox A) w × M.interp (.VTypeBox B) w) := rfl
@[simp] theorem interp_box_one (M : RFrame σ) (w : M.W) :
    M.interp (.VTypeBox .VTypeOne) w = PUnit := rfl

end RFrame

/-- A **box-stack** = number of `□`s to wrap a type in (boxes only; `◇` is terminal, products
    distribute).  Purely syntactic. -/
inductive Stk
  | hole
  | box (c : Stk)

/-- Wrap `S` in the stack's boxes. -/
def Stk.plug : Stk → VarType → VarType
  | .hole,  S => S
  | .box c, S => (c.plug S).VTypeBox

/-! ### Box-stack depth machinery (relocated here so `GFunc.eval`'s `boxLift` case can reach it). -/

def Stk.size : Stk → ℕ
  | .hole  => 0
  | .box c => c.size + 1

def Stk.boxes : ℕ → Stk
  | 0     => .hole
  | k + 1 => .box (Stk.boxes k)

@[simp] theorem Stk.boxes_size : (k : ℕ) → (Stk.boxes k).size = k
  | 0     => rfl
  | k + 1 => by simp [Stk.boxes, Stk.size, Stk.boxes_size k]

/-- `interp` through a box-stack is `interpN` at the shifted level. -/
theorem RFrame.interpN_plug {σ : Signature} (M : RFrame σ) (X : VarType) :
    (c : Stk) → (j : ℕ) → (w : M.W) → M.interpN (c.plug X) j w = M.interpN X (c.size + j) w
  | .hole,  j, w => by simp only [Stk.plug, Stk.size, Nat.zero_add]
  | .box c, j, w => by
      show M.interpN (c.plug X) (j + 1) w = M.interpN X (c.size + 1 + j) w
      rw [M.interpN_plug X c (j + 1) w]; congr 1; omega

/-- The `k`-box stack plugs `X` to `interpN X k` — the bridge to `funcNecStk (Stk.boxes k)`. -/
theorem RFrame.interp_boxes {σ : Signature} (M : RFrame σ) (X : VarType) (k : ℕ) (w : M.W) :
    M.interp ((Stk.boxes k).plug X) w = M.interpN X k w := by
  rw [RFrame.interp, M.interpN_plug X (Stk.boxes k) 0 w, Stk.boxes_size, Nat.add_zero]

/-- Pushing one box *into* the plugged type = wrapping the plug — the stack/box commutation used to
    bridge `(boxes (k+1)).plug U` with `(boxes k).plug (□U)` in the box-β box case. -/
theorem Stk.plug_box : (c : Stk) → (X : VarType) → c.plug X.VTypeBox = (c.plug X).VTypeBox
  | .hole,  _ => rfl
  | .box c, X => by rw [Stk.plug, Stk.plug_box c X, Stk.plug]

/-! ### The generalised function algebra `GFunc`

`◇` closes under the *product-aware* definable maps, not just function symbols.  `GFunc σ A B` is the
free Cartesian algebra on the function symbols: `sym` (a symbol, from its `Varⁿ` argument-product to
`Var`), `comp`, `idm`, and the product structure `prod` (`×`), `diag` (`Δ`), `fst`/`snd`, `unit`
(`!`).  Its **pointwise** interpretation `GFunc.eval` is the only place `funcInterp` is touched —
exactly the FOL fact that a model interprets *symbols*, and generic maps are derived by recursion. -/

/-- `Varⁿ` as a right-nested product, so a function symbol is a morphism `VarPow n ⤳ Var`. -/
def VarPow : ℕ → VarType
  | 0     => .VTypeOne
  | n + 1 => .VTypeProd .Var (VarPow n)

inductive GFunc (σ : Signature) : VarType → VarType → Type where
  | sym  (f : σ.FuncSyms)                          : GFunc σ (VarPow (σ.funcArity f)) .Var
  | idm  {A : VarType}                             : GFunc σ A A
  | comp {A B C : VarType} : GFunc σ B C → GFunc σ A B → GFunc σ A C
  | prod {A B C D : VarType} : GFunc σ A C → GFunc σ B D → GFunc σ (A.VTypeProd B) (C.VTypeProd D)
  | diag {A : VarType}                             : GFunc σ A (A.VTypeProd A)
  | fst  {A B : VarType}                           : GFunc σ (A.VTypeProd B) A
  | snd  {A B : VarType}                           : GFunc σ (A.VTypeProd B) B
  | unit {A : VarType}                             : GFunc σ A .VTypeOne
  /-- **Box-lift**: apply a map *under a box*.  Evaluated via `funcNecStk` (box-lift of symbols); the
      structural cases are free by `interpN` distributing `□`.  This is what lets a `◇`-body contain a
      `boxterm` that operates on a box-typed witness (`◇_x □(f(x))`) — no new model obligation. -/
  | boxLift {A B : VarType} : GFunc σ A B → GFunc σ A.VTypeBox B.VTypeBox
  /-- `□` distributes over `×`/`1` at the *interp* level but not syntactically; these witness the
      isomorphism as maps (both evaluate to the identity, since `interp (□(A×B)) = interp (□A × □B)`
      definitionally).  Needed to assemble `□`-typed projections into a `□(product)` context. -/
  | boxProd {A B : VarType} : GFunc σ (A.VTypeBox.VTypeProd B.VTypeBox) (A.VTypeProd B).VTypeBox
  | boxUnit                 : GFunc σ .VTypeOne VarType.VTypeOne.VTypeBox
  /-- **◇-lift**: apply a map *under a diamond* (evaluated via `posLift` / `posLiftStk`).  The
      `◇`-analog of `boxLift`; lets a body contain a `diaterm` (nested `◇`). -/
  | diaLift {A B : VarType} : GFunc σ A B → GFunc σ A.VTypeDia B.VTypeDia
  /-- **◇-strength**: thread a necessary object into a possible one (evaluated via `posStrength` /
      `posStrengthStk`).  Builds the `◇(Γ × witness)` collection a nested `diaterm` needs. -/
  | diaStrength {A B : VarType} :
      GFunc σ (A.VTypeBox.VTypeProd B.VTypeDia) (A.VTypeProd B).VTypeDia

namespace RFrame
variable {σ : Signature}

/-- The type of a model's **symbol box-lift** (`= funcNecStk`), threaded into `GFunc.eval` so its
    `boxLift` case can compute.  Kept as data the caller passes (it lives on `RModel`, not `RFrame`). -/
abbrev NecStk (M : RFrame σ) : Type u :=
  (f : σ.FuncSyms) → (c : Stk) → {w : M.W} →
    (Fin (σ.funcArity f) → M.interp (c.plug .Var) w) → M.interp (c.plug .Var) w

/-- The model closure operations `GFunc.eval` needs to interpret the modal `GFunc` constructors —
    bundled so they thread as one parameter.  All five are existing `RModel` fields (`funcNecStk`,
    `posLift`, `posStrength`, `posLiftStk`, `posStrengthStk`); no new obligation. -/
structure GEvalOps (M : RFrame σ) where
  nec : M.NecStk
  pos : {A B : VarType} → {w : M.W} → GFunc σ A B → M.Pos A w → M.Pos B w
  str : {A B : VarType} → {w : M.W} →
    M.interp (.VTypeBox A) w → M.Pos B w → M.Pos (.VTypeProd A B) w
  posStk : {A B : VarType} → GFunc σ A B → (c : Stk) → {w : M.W} →
    M.interp (c.plug (.VTypeDia A)) w → M.interp (c.plug (.VTypeDia B)) w
  strStk : {A B : VarType} → (c : Stk) → {w : M.W} →
    M.interp (c.plug (.VTypeBox A)) w → M.interp (c.plug (.VTypeDia B)) w →
    M.interp (c.plug (.VTypeDia (.VTypeProd A B))) w

/-- Read a `VarPow n` object as the `Fin n`-vector of individuals it packs. -/
def toVec (M : RFrame σ) : (n : ℕ) → {w : M.W} → M.interp (VarPow n) w → (Fin n → M.D w)
  | 0,     _, _ => Fin.elim0
  | _ + 1, _, p => Fin.cons p.1 (M.toVec _ p.2)

/-- `interpN`-level `toVec`: read a `VarPow n` object *at box-depth `m`* as its `Fin n`-vector of
    depth-`m` individuals (all `interpN` products distribute definitionally). -/
def toVecN (M : RFrame σ) (m : ℕ) :
    (n : ℕ) → {w : M.W} → M.interpN (VarPow n) m w → (Fin n → M.interpN .Var m w)
  | 0,     _, _ => Fin.elim0
  | _ + 1, _, p => Fin.cons p.1 (M.toVecN m _ p.2)

/-- **Box-lifted evaluation** of a `GFunc` at box-depth `m`, given the model's symbol box-lift `nec`
    (`= funcNecStk`).  All cases but `sym` are definitional (`interpN` distributes `□` over `×`/`1`,
    and `□` under `boxLift` is `interpN`'s box case); `sym` reaches `nec (Stk.boxes m)` via
    `interp_boxes`.  `GFunc.eval`'s `boxLift` case is `gEvalN 1`. -/
def gEvalN (M : RFrame σ) (ops : M.GEvalOps)
    (w : M.W) : (m : ℕ) → {A B : VarType} → GFunc σ A B → M.interpN A m w → M.interpN B m w
  | m, _, _, .sym f,    a =>
      (M.interp_boxes .Var m w) ▸
        ops.nec f (Stk.boxes m) (fun i => (M.interp_boxes .Var m w).symm ▸ M.toVecN m _ a i)
  | _, _, _, .idm,      a => a
  | m, _, _, .comp g h, a => M.gEvalN ops w m g (M.gEvalN ops w m h a)
  | m, _, _, .prod g h, p => (M.gEvalN ops w m g p.1, M.gEvalN ops w m h p.2)
  | _, _, _, .diag,     a => (a, a)
  | _, _, _, .fst,      p => p.1
  | _, _, _, .snd,      p => p.2
  | _, _, _, .unit,     _ => PUnit.unit
  | m, _, _, .boxLift φ, a => M.gEvalN ops w (m + 1) φ a
  | _, _, _, .boxProd,  a => a
  | _, _, _, .boxUnit,  a => a
  | m, _, _, .diaLift φ, a =>
      (M.interp_boxes _ m w) ▸ ops.posStk φ (Stk.boxes m) ((M.interp_boxes _ m w).symm ▸ a)
  | m, _, _, .diaStrength, p =>
      (M.interp_boxes _ m w) ▸ ops.strStk (Stk.boxes m)
        ((M.interp_boxes _ m w).symm ▸ p.1) ((M.interp_boxes _ m w).symm ▸ p.2)

/-- The interpretation of a definable map.  The base cases are the pointwise `funcInterp`; the modal
    constructors reach the model's closure operations (`ops`) — box-lift via `gEvalN`, ◇ via `pos`. -/
def GFunc.eval (M : RFrame σ) (ops : M.GEvalOps)
    (w : M.W) : {A B : VarType} → GFunc σ A B → M.interp A w → M.interp B w
  | _, _, .sym f,    a => M.funcInterp f w (M.toVec _ a)
  | _, _, .idm,      a => a
  | _, _, .comp g h, a => GFunc.eval M ops w g (GFunc.eval M ops w h a)
  | _, _, .prod g h, p => (GFunc.eval M ops w g p.1, GFunc.eval M ops w h p.2)
  | _, _, .diag,     a => (a, a)
  | _, _, .fst,      p => p.1
  | _, _, .snd,      p => p.2
  | _, _, .unit,     _ => PUnit.unit
  | _, _, .boxLift φ, a => M.gEvalN ops w 1 φ a
  | _, _, .boxProd,  a => a
  | _, _, .boxUnit,  a => a
  | _, _, .diaLift φ, a => ops.pos φ a
  | _, _, .diaStrength, p => ops.str p.1 p.2

/-- `interp`/`interpN` distributes a product through *any* box-stack, at every level — the type-level
    fact behind `necEvalStk_prod`.  Proven by induction on the stack using only the definitional
    product/box reductions of `interpN`. -/
theorem interpN_plug_prod (M : RFrame σ) (A B : VarType) :
    (c : Stk) → (j : ℕ) → (w : M.W) →
    M.interpN (c.plug (.VTypeProd A B)) j w
      = (M.interpN (c.plug A) j w × M.interpN (c.plug B) j w)
  | .hole,  _, _ => rfl
  | .box c, j, w => M.interpN_plug_prod A B c (j + 1) w

/-- `interp`-level product distribution through a box-stack (the `j = 0` case), stated in `interp`
    terms so it casts cleanly against `necEval` results. -/
theorem interp_plug_prod (M : RFrame σ) {A B : VarType} (c : Stk) (w : M.W) :
    M.interp (c.plug (.VTypeProd A B)) w = (M.interp (c.plug A) w × M.interp (c.plug B) w) :=
  M.interpN_plug_prod A B c 0 w

end RFrame

/-- **Model layer**: the frame + injective eval maps + the closure operations. -/
structure RModel (σ : Signature) where
  frame : RFrame σ
  -- ### □ side (settled): `Nec` closed under function symbols; pairs free by distribution.
  /-- **Box eval**: peel one box off a necessary object to its section. -/
  necEval : {V : VarType} → {w : frame.W} →
      frame.interp (.VTypeBox V) w →
      ((w' : {w' : frame.W // frame.R w w'}) → frame.interp V w'.1)
  /-- **INJECTIVE** (world-extensionality): a necessary object *is* its section.  Not surjective. -/
  nec_inj : {V : VarType} → {w : frame.W} → Function.Injective (@necEval V w)
  /-- Coherence for the baked-in distribution: a necessary pair evaluates componentwise. -/
  necEval_prod : {A B : VarType} → {w : frame.W} →
      (a : frame.interp (.VTypeBox A) w) → (b : frame.interp (.VTypeBox B) w) →
      necEval (V := .VTypeProd A B) ((a, b) : frame.interp (.VTypeBox (.VTypeProd A B)) w)
        = fun w' => (necEval a w', necEval b w')
  /-- **Distribution at every box-depth**: `necEval` commutes with a product sitting under *any*
      box-stack `c`, not just directly under one box (`necEval_prod` = the `c = .hole` case).  Needed
      because the diaterm's necessary context is a *product* (the bundled context) that is peeled at
      box-depth `k+1`, where the type under the outer box is `□^k(A×B)` — a box head, so `necEval_prod`
      cannot fire.  Semantically valid in every intended model (`necEval` = section-restriction, which
      is componentwise on denotable products at any depth). -/
  necEvalStk_prod : {A B : VarType} → (c : Stk) → {w : frame.W} →
      (n : frame.interp ((Stk.box c).plug (.VTypeProd A B)) w) →
      necEval (V := c.plug (.VTypeProd A B)) n
        = fun w' => cast (frame.interp_plug_prod c w'.1).symm
            (necEval (V := c.plug A) (cast (frame.interp_plug_prod (Stk.box c) w) n).1 w',
             necEval (V := c.plug B) (cast (frame.interp_plug_prod (Stk.box c) w) n).2 w')
  /-- Lift a function symbol through the `c`-box-stack.  `_hole` = `funcInterp`; `_box` = naturality. -/
  funcNecStk : (f : σ.FuncSyms) → (c : Stk) → {w : frame.W} →
      (Fin (σ.funcArity f) → frame.interp (c.plug .Var) w) → frame.interp (c.plug .Var) w
  funcNecStk_hole : (f : σ.FuncSyms) → {w : frame.W} →
      (args : Fin (σ.funcArity f) → frame.interp (Stk.hole.plug .Var) w) →
      funcNecStk f .hole args = frame.funcInterp f w args
  funcNecStk_box : (f : σ.FuncSyms) → (c : Stk) → {w : frame.W} →
      (args : Fin (σ.funcArity f) → frame.interp ((Stk.box c).plug .Var) w) →
      (w' : {w' : frame.W // frame.R w w'}) →
      necEval (funcNecStk f (.box c) args) w' = funcNecStk f c (fun i => necEval (args i) w')
  -- ### ◇ side: `Pos` closed under the generalised algebra + the strength.
  /-- **Dia eval**: a possible object projects to its realization set. -/
  posEval : {V : VarType} → {w : frame.W} →
      frame.Pos V w → Set (Σ' w' : {w' : frame.W // frame.R w w'}, frame.interp V w'.1)
  /-- **INJECTIVE**: a possible object *is* its realization set. -/
  pos_inj : {V : VarType} → {w : frame.W} → Function.Injective (@posEval V w)
  /-- **The ◇ closure**: every definable map `φ : GFunc A B` sends a possible object to a possible
      object.  Asserts the image *exists* in `Pos`; its value is pinned by `GFunc.eval`
      (= `funcInterp`, no new data) via `pos_inj`.  Contains the denotable objects, constrains no
      further — full model: all present; canonical model: only denotable, both closed. -/
  posLift : {A B : VarType} → {w : frame.W} → GFunc σ A B → frame.Pos A w → frame.Pos B w
  /-- **Strength**: a necessary object rides along inside a given possible object — pair its (total)
      value with each realization.  Correlation-free because `Nec` is total.  Carries the diaterm
      body's outer box-typed variables; the semantic content of `□Γ, ◇y ⊢ ◇t`. -/
  posStrength : {A B : VarType} → {w : frame.W} →
      frame.interp (.VTypeBox A) w → frame.Pos B w → frame.Pos (.VTypeProd A B) w
  /-- **`◇`-closure through boxes** — the ◇-mirror of `funcNecStk`.  A `◇`-collection can be produced
      *as* a necessary object (`NecDia = interp (□^{k+1} ◇_)`) rather than only at the base, which is
      what lets `◇` nested under `□`/`◇` be built and then threaded by `posStrength`.  `_hole` is the
      base `posLift`; `_box` is the `necEval` naturality linking level `k+1` to level `k`. -/
  posLiftStk : {A B : VarType} → (φ : GFunc σ A B) → (c : Stk) → {w : frame.W} →
      frame.interp (c.plug (.VTypeDia A)) w → frame.interp (c.plug (.VTypeDia B)) w
  /-- **Strength through boxes** — the box-lift of `posStrength` (ditto: needed to build the
      `NecDia` object that carries a nested `◇`-collection's necessary context). -/
  posStrengthStk : {A B : VarType} → (c : Stk) → {w : frame.W} →
      frame.interp (c.plug (.VTypeBox A)) w → frame.interp (c.plug (.VTypeDia B)) w →
      frame.interp (c.plug (.VTypeDia (.VTypeProd A B))) w
  -- ### ◇-side laws (data above so `posLift_eval`'s `GFunc.eval` can reference every op).
  posLift_eval : {A B : VarType} → {w : frame.W} → (φ : GFunc σ A B) → (x : frame.Pos A w) →
      (ru : Σ' w' : {w' : frame.W // frame.R w w'}, frame.interp B w'.1) →
      (ru ∈ posEval (posLift φ x) ↔
        ∃ a : frame.interp A ru.1.1,
          (⟨ru.1, a⟩ : Σ' w' : {w' : frame.W // frame.R w w'}, frame.interp A w'.1) ∈ posEval x
            ∧ RFrame.GFunc.eval frame
                ⟨funcNecStk, posLift, posStrength, posLiftStk, posStrengthStk⟩ ru.1.1 φ a = ru.2)
  posStrength_eval : {A B : VarType} → {w : frame.W} →
      (n : frame.interp (.VTypeBox A) w) → (x : frame.Pos B w) →
      (ru : Σ' w' : {w' : frame.W // frame.R w w'}, frame.interp (.VTypeProd A B) w'.1) →
      (ru ∈ posEval (posStrength n x) ↔
        (⟨ru.1, ru.2.2⟩ : Σ' w' : {w' : frame.W // frame.R w w'}, frame.interp B w'.1) ∈ posEval x
          ∧ ru.2.1 = necEval n ru.1)
  posLiftStk_hole : {A B : VarType} → (φ : GFunc σ A B) → {w : frame.W} →
      (x : frame.interp (Stk.hole.plug (.VTypeDia A)) w) → posLiftStk φ .hole x = posLift φ x
  posLiftStk_box : {A B : VarType} → (φ : GFunc σ A B) → (c : Stk) → {w : frame.W} →
      (X : frame.interp ((Stk.box c).plug (.VTypeDia A)) w) →
      (w' : {w' : frame.W // frame.R w w'}) →
      necEval (posLiftStk φ (.box c) X) w' = posLiftStk φ c (necEval X w')
  posStrengthStk_hole : {A B : VarType} → {w : frame.W} →
      (n : frame.interp (Stk.hole.plug (.VTypeBox A)) w) →
      (x : frame.interp (Stk.hole.plug (.VTypeDia B)) w) →
      posStrengthStk .hole n x = posStrength n x
  posStrengthStk_box : {A B : VarType} → (c : Stk) → {w : frame.W} →
      (n : frame.interp ((Stk.box c).plug (.VTypeBox A)) w) →
      (x : frame.interp ((Stk.box c).plug (.VTypeDia B)) w) →
      (w' : {w' : frame.W // frame.R w w'}) →
      necEval (posStrengthStk (.box c) n x) w'
        = posStrengthStk c (necEval n w') (necEval x w')

/-- The model's closure operations bundled for `GFunc.eval` (`= ⟨funcNecStk, posLift, posStrength,
    posLiftStk, posStrengthStk⟩`). -/
def RModel.gOps {σ : Signature} (M : RModel σ) : M.frame.GEvalOps :=
  ⟨M.funcNecStk, M.posLift, M.posStrength, M.posLiftStk, M.posStrengthStk⟩
