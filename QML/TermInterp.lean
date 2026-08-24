import QML.RModelB

/-!
# `TermInterp` — the term interpreter on `RModelB`

The stack-generalized term interpreter and its metatheory:

* `termToNecLvl` / `funcToNecLvl` — interpret a term at box-depth `k` into `interpN S k`, with the
  modal machinery `funcNecStkLvl` / `posLiftStkLvl` / `posStrengthStkLvl` / `bundleNecLvl`;
* `termToGFunc` / `funcToGFunc` — the point-free translation of a body to a definable map, using
  `boxCtx` and the modal `GFunc` constructors `boxLift` / `boxProd` / `boxUnit` / `diaLift` /
  `diaStrength` (all evaluated through the model's existing closures — no new obligation);
* **box-β** (`termToNecLvl_necEvalLvl`): peeling one box off a level-`(k+1)` interpretation equals
  interpreting at level `k` with the environment peeled, via `necEvalLvl_eq_necEval`.

`interpTerm := termToNecLvl 0` (see `InterpWFF`).  `termToNecLvl`, `termToGFunc`, and box-β are all
`sorryAx`-free.  (Was `DiaProto`: it began as a diaterm-interpreter prototype and grew into this.)
-/


/-! ## Body → `GFunc` translation (point-free compile of the functional core)

A diaterm body is interpreted by translating it to a `GFunc` from a *context product* to the body
type, with each `Var`-variable becoming a projection (`proj`).  This is the functional core; the
modal/binding constructors (`boxterm`/`diaterm`/`pair_elim`) are handled by threading, not by this
translation, and are left as placeholders here. -/

/-- Pair two definable maps out of a common domain: `⟨a,b⟩ = (a × b) ∘ Δ`. -/
def GFunc.gpair {σ : Signature} {C A B : VarType} (a : GFunc σ C A) (b : GFunc σ C B) :
    GFunc σ C (A.VTypeProd B) :=
  .comp (.prod a b) .diag

namespace RModel

/-- How each variable of context `V` projects out of the context product `ctxType`
    (arbitrary-typed, so `pair_elim`'s product variable can be projected then split). -/
abbrev Proj (σ : Signature) (ctxType : VarType) (V : VarCtx) : Type :=
  (p : VarSymb × VarType) → p ∈ V.1 → GFunc σ ctxType p.2

/-- Extend a lookup over `W₂` (context with the product variable `z`) to a lookup over `W₁` (context
    with the components `v₁`,`v₂`) — for `pair_elim`.  Splits `z`'s value via generic `mkFst`/`mkSnd`.
    Transparent: the case analysis lives in the (proof-irrelevant) *membership*, not a value cast, so
    it reduces under `dif_pos`/`dif_neg` — which the tactic-mode `subst`-based version did not. -/
def peLookup {X : VarType → Type u}
    (mkFst : {A B : VarType} → X (A.VTypeProd B) → X A)
    (mkSnd : {A B : VarType} → X (A.VTypeProd B) → X B)
    {V W₁ W₂ : VarCtx} (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V) (hv₁v₂ : v₁.1 ≠ v₂.1)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, v₁.2.VTypeProd v₂.2⟩ V hz = W₂)
    (base : (p : VarSymb × VarType) → p ∈ W₂.1 → X p.2) :
    (p : VarSymb × VarType) → p ∈ W₁.1 → X p.2 :=
  fun p hp =>
    if hpv1 : p = v₁ then
      mkFst (base ⟨z, p.2.VTypeProd v₂.2⟩ (by
        rw [congrArg Prod.snd hpv1, ← w₂eq]; exact Finset.mem_insert_self _ _))
    else if hpv2 : p = v₂ then
      mkSnd (base ⟨z, v₁.2.VTypeProd p.2⟩ (by
        rw [congrArg Prod.snd hpv2, ← w₂eq]; exact Finset.mem_insert_self _ _))
    else
      base p (by
        rw [← w₂eq]
        refine Finset.mem_insert_of_mem ?_
        have hp1 : p ∈ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂).1 := by rw [w₁eq]; exact hp
        rcases Finset.mem_insert.mp hp1 with h | h
        · exact absurd h hpv1
        · rcases Finset.mem_insert.mp h with h' | h'
          · exact absurd h' hpv2
          · exact h')

/-- `peLookup` is natural: a family map `φ` commuting with the split ops commutes with the whole
    lookup extension.  This is what makes `pair_elim` faithfulness go through cleanly. -/
theorem peLookup_natural {X : VarType → Type u} {Y : VarType → Type v}
    (mkFstX : {A B : VarType} → X (A.VTypeProd B) → X A)
    (mkSndX : {A B : VarType} → X (A.VTypeProd B) → X B)
    (mkFstY : {A B : VarType} → Y (A.VTypeProd B) → Y A)
    (mkSndY : {A B : VarType} → Y (A.VTypeProd B) → Y B)
    (φ : {T : VarType} → X T → Y T)
    (hFst : ∀ {A B : VarType} (x : X (A.VTypeProd B)), φ (mkFstX x) = mkFstY (φ x))
    (hSnd : ∀ {A B : VarType} (x : X (A.VTypeProd B)), φ (mkSndX x) = mkSndY (φ x))
    {V W₁ W₂ : VarCtx} (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V) (hv₁v₂ : v₁.1 ≠ v₂.1)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, v₁.2.VTypeProd v₂.2⟩ V hz = W₂)
    (base : (p : VarSymb × VarType) → p ∈ W₂.1 → X p.2)
    (p : VarSymb × VarType) (hp : p ∈ W₁.1) :
    φ (peLookup mkFstX mkSndX v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq base p hp)
      = peLookup mkFstY mkSndY v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq
          (fun q hq => φ (base q hq)) p hp := by
  simp only [peLookup]
  by_cases hpv1 : p = v₁
  · simp only [dif_pos hpv1]; exact hFst _
  · by_cases hpv2 : p = v₂
    · simp only [dif_neg hpv1, dif_pos hpv2]; exact hSnd _
    · simp only [dif_neg hpv1, dif_neg hpv2]

/-- Assemble **boxed projections** into a `□`-typed product context.  Given a `GFunc ctxType (□q.2)`
    per list entry `q`, build the product type `Γ`, a `GFunc ctxType (□Γ)` (folding with `boxProd`/
    `boxUnit`, since `□` distributes over `×`/`1` only up to `boxProd`/`boxUnit` at the syntax level),
    and the projections `GFunc Γ q.2`.  This is what feeds `boxLift` in `termToGFunc`'s `boxterm` arm. -/
def boxCtx {σ : Signature} {ctxType : VarType} :
    (l : List (VarSymb × VarType)) →
    ((q : VarSymb × VarType) → q ∈ l → GFunc σ ctxType q.2.VTypeBox) →
    Σ' Γ : VarType, GFunc σ ctxType Γ.VTypeBox × ((q : VarSymb × VarType) → q ∈ l → GFunc σ Γ q.2)
  | [],        _  => ⟨.VTypeOne, .comp GFunc.boxUnit GFunc.unit, fun q hq => absurd hq (by simp)⟩
  | q :: rest, bp =>
      let r := boxCtx rest (fun p hp => bp p (List.mem_cons.mpr (Or.inr hp)))
      ⟨q.2.VTypeProd r.1,
       .comp GFunc.boxProd (GFunc.gpair (bp q (List.mem_cons.mpr (Or.inl rfl))) r.2.1),
       fun p hp =>
         if hpq : p = q then
           (congrArg Prod.snd hpq).symm ▸ (GFunc.fst : GFunc σ (q.2.VTypeProd r.1) q.2)
         else .comp (r.2.2 p ((List.mem_cons.mp hp).resolve_left hpq)) .snd⟩

mutual

/-- Translate a term over context `V` into a definable map `ctxType ⤳ S`, given how each variable of
    `V` projects (`proj`).  A `boxterm` recurses under a `boxLift` (its interior is compiled over a
    fresh `□`-context assembled by `boxCtx`); `diaterm` (nested `◇`) is deferred. -/
noncomputable def termToGFunc {σ : Signature} {ctxType : VarType} : {V : VarCtx} →
    Proj σ ctxType V → {S : VarType} → Term σ V S → GFunc σ ctxType S
  | _, proj, _, .var ⟨v, hv⟩ => proj ⟨v, .Var⟩ hv
  | _, proj, _, .func ff     => funcToGFunc proj ff .unit
  | _, _,    _, .unit        => .unit
  | _, proj, _, .pair s t    => GFunc.gpair (termToGFunc proj s) (termToGFunc proj t)
  | _, proj, _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body =>
      termToGFunc
        (peLookup (fun g => .comp .fst g) (fun g => .comp .snd g)
          v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq proj)
        body
  | _, proj, _, @Term.boxterm _ Vin _ _ s hsub _ =>
      -- box sub-term: compile the interior `s` over the `□`-context `boxCtx` of `Vin`'s boxed vars
      -- (projected from `ctxType` via `proj`), lift it under a box, and prepend that `□`-context map.
      let bc := boxCtx Vin.1.toList (fun q hq =>
        proj ⟨q.1, q.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨q, Finset.mem_toList.mp hq, rfl⟩)))
      .comp (GFunc.boxLift (termToGFunc (fun q hq => bc.2.2 q (Finset.mem_toList.mpr hq)) s)) bc.2.1
  | _, proj, _, @Term.diaterm _ Vdia _ _ x hx tt hsub _ =>
      -- nested `◇`: bundle `Vdia`'s necessary vars (`boxCtx`), strength them onto the projected
      -- `◇`-witness (`diaStrength`), then lift the body translation under the diamond (`diaLift`).
      let bc := boxCtx Vdia.1.toList (fun q hq =>
        proj ⟨q.1, q.2.VTypeBox⟩
          (hsub (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, Finset.mem_toList.mp hq, rfl⟩))))
      .comp
        (GFunc.diaLift (termToGFunc
          (fun p hp =>
            if hpx : p = x then
              (congrArg Prod.snd hpx).symm ▸ (GFunc.snd : GFunc σ (bc.1.VTypeProd x.2) x.2)
            else .comp (bc.2.2 p (Finset.mem_toList.mpr
              ((Finset.mem_insert.mp hp).resolve_left hpx))) .fst)
          tt))
        (.comp GFunc.diaStrength
          (GFunc.gpair bc.2.1 (proj ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _)))))

/-- Translate a (curried) function application, accumulating supplied arguments as a `VarPow n`. -/
noncomputable def funcToGFunc {σ : Signature} {ctxType : VarType} : {V : VarCtx} →
    Proj σ ctxType V → {n : ℕ} → Func σ V n → GFunc σ ctxType (VarPow n) → GFunc σ ctxType .Var
  | _, _,    _, .F ⟨f, hf⟩, args => .comp (.sym f) (hf.symm ▸ args)
  | _, proj, _, .eval g t,  args =>
      funcToGFunc proj g (GFunc.gpair (termToGFunc proj t) args)

end

end RModel

/-! ## Stack generalization — infrastructure

Nested modalities need the box-lift at arbitrary depth.  Cleaner than a `Stk`-indexed lift (which
needs `stkZip`/`stkUnit` casts): index by the **level `k`** and produce `interpN S k` directly, so
`pair`/`unit`/`boxterm` are definitional (`interpN (A×B) k = interpN A k × interpN B k`, etc.).  Only
`func` needs a cast, to reach the `Stk`-indexed `funcNecStk` (via the canonical `k`-box stack).
(`Stk.size`/`Stk.boxes`/`interpN_plug`/`interp_boxes`/`Stk.plug_box` now live in `RModelB`.) -/

namespace RModel
variable {σ : Signature}

/-- Level-indexed `funcNecStk`: apply a symbol at box-depth `k` via the canonical `k`-box stack,
    casting args/result across `interp ((boxes k).plug Var) = interpN Var k`. -/
noncomputable def funcNecStkLvl (M : RModel σ) (k : ℕ) {w : M.frame.W} (f : σ.FuncSyms)
    (args : Fin (σ.funcArity f) → M.frame.interpN VarType.Var k w) :
    M.frame.interpN VarType.Var k w :=
  (M.frame.interp_boxes .Var k w) ▸
    M.funcNecStk f (Stk.boxes k) (fun i => (M.frame.interp_boxes .Var k w).symm ▸ args i)

/-- Level-wrapped `posLiftStk` (box-lift the ◇-closure at depth `k`). -/
noncomputable def posLiftStkLvl (M : RModel σ) (k : ℕ) {w : M.frame.W} {A B : VarType}
    (φ : GFunc σ A B) (x : M.frame.interpN A.VTypeDia k w) : M.frame.interpN B.VTypeDia k w :=
  (M.frame.interp_boxes B.VTypeDia k w) ▸
    M.posLiftStk φ (Stk.boxes k) ((M.frame.interp_boxes A.VTypeDia k w).symm ▸ x)

/-- Level-wrapped `posStrengthStk` (box-lift the strength at depth `k`). -/
noncomputable def posStrengthStkLvl (M : RModel σ) (k : ℕ) {w : M.frame.W} {A B : VarType}
    (n : M.frame.interpN A.VTypeBox k w) (x : M.frame.interpN B.VTypeDia k w) :
    M.frame.interpN (A.VTypeProd B).VTypeDia k w :=
  (M.frame.interp_boxes (A.VTypeProd B).VTypeDia k w) ▸
    M.posStrengthStk (Stk.boxes k)
      ((M.frame.interp_boxes A.VTypeBox k w).symm ▸ n)
      ((M.frame.interp_boxes B.VTypeDia k w).symm ▸ x)

/-- Level-`k` context bundler (bundle a `□`-context at box-depth `k`; projections level-free). -/
def bundleNecLvl (M : RModel σ) (k : ℕ) {w : M.frame.W} :
    (l : List (VarSymb × VarType)) →
    ((p : VarSymb × VarType) → p ∈ l → M.frame.interpN p.2 (k + 1) w) →
    Σ' Γ : VarType, M.frame.interpN Γ (k + 1) w ×
      ((p : VarSymb × VarType) → p ∈ l → GFunc σ Γ p.2)
  | [],        _     => ⟨.VTypeOne, PUnit.unit, fun p hp => absurd hp (by simp)⟩
  | q :: rest, necOf =>
      let r := M.bundleNecLvl k rest (fun p hp => necOf p (List.mem_cons.mpr (Or.inr hp)))
      ⟨q.2.VTypeProd r.1, (necOf q (List.mem_cons.mpr (Or.inl rfl)), r.2.1),
       fun p hp =>
         if hpq : p = q then
           (congrArg Prod.snd hpq).symm ▸ (GFunc.fst : GFunc σ (q.2.VTypeProd r.1) q.2)
         else .comp (r.2.2 p ((List.mem_cons.mp hp).resolve_left hpq)) .snd⟩

/- **Stack-generalized box-lift** (`termToNecLvl`, level-indexed).  Interprets a body over a
   `□`-context into `interpN S k` (`= interp (□^k S)`).  Nested `boxterm` grows `k → k+1` *cast-free*
   (`interpN (S.VTypeBox) k = interpN S (k+1)` definitionally).  `diaterm` uses the level-wrapped ◇
   ops on the box-lifted witness/context. -/
mutual
noncomputable def termToNecLvl (M : RModel σ) (k : ℕ) {w : M.frame.W} : {V : VarCtx} →
    ((p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 k w) →
    {S : VarType} → Term σ V S → M.frame.interpN S k w
  | _, env, _, .var ⟨v, hv⟩ => env ⟨v, .Var⟩ hv
  | _, env, _, .func ff     => M.funcToNecLvl k env ff Fin.elim0
  | _, env, _, .unit        => PUnit.unit
  | _, env, _, .pair a b    => (M.termToNecLvl k env a, M.termToNecLvl k env b)
  | _, env, _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body =>
      M.termToNecLvl k
        (peLookup (X := fun T => M.frame.interpN T k w)
          (fun {A B} x => (x : M.frame.interpN A k w × M.frame.interpN B k w).1)
          (fun {A B} x => (x : M.frame.interpN A k w × M.frame.interpN B k w).2)
          v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq env)
        body
  | _, env, _, .boxterm s hsub _ =>
      M.termToNecLvl (k + 1)
        (fun p hp => env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))) s
  | _, env, _, @Term.diaterm _ V_dia _ _ x hx tt hsub _ =>
      -- ◇ under `k` boxes: bundle the (box-lifted) necessary context, strength it onto the box-lifted
      -- witness, then lift the (level-independent) body translation — all at depth `k`.
      let b := M.bundleNecLvl k V_dia.1.toList (fun p hp =>
        env ⟨p.1, p.2.VTypeBox⟩
          (hsub (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_toList.mp hp, rfl⟩))))
      M.posLiftStkLvl k
        (termToGFunc
          (fun p hp =>
            if hpx : p = x then
              (congrArg Prod.snd hpx).symm ▸ (GFunc.snd : GFunc σ (b.1.VTypeProd x.2) x.2)
            else .comp (b.2.2 p (Finset.mem_toList.mpr
              ((Finset.mem_insert.mp hp).resolve_left hpx))) .fst)
          tt)
        (M.posStrengthStkLvl k b.2.1
          (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))))
noncomputable def funcToNecLvl (M : RModel σ) (k : ℕ) {w : M.frame.W} : {V : VarCtx} →
    ((p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 k w) →
    {n : ℕ} → Func σ V n → (Fin n → M.frame.interpN VarType.Var k w) →
    M.frame.interpN VarType.Var k w
  | _, env, _, .F ⟨f, hf⟩, args => M.funcNecStkLvl k f (hf.symm ▸ args)
  | _, env, _, .eval g t,  args => M.funcToNecLvl k env g (Fin.cons (M.termToNecLvl k env t) args)
end

end RModel


/-! ## Box-β for the stack-generalized lift (`termToNecLvl`)

`necEvalLvl k` peels one box off a level-`(k+1)` object (→ level `k` at an accessible world).  Box-β:
peeling `termToNecLvl (k+1)` = `termToNecLvl k` with the environment peeled.  Functional fragment. -/

namespace RModel
variable {σ : Signature}

/-- Peel one box off a level-`(k+1)` object — **structural on the type, distributing at products**, so
    `necEvalLvl_prod` is DEFINITIONAL: the box-lift's deep products distribute with no model law added.
    Only the atomic leaves (`Var`, `◇`) touch the field `necEval` (via the `interp_boxes` bridge). -/
noncomputable def necEvalLvl (M : RModel σ) : (V : VarType) → (k : ℕ) → (w : M.frame.W) →
    M.frame.interpN V (k + 1) w → (w' : {w' : M.frame.W // M.frame.R w w'}) → M.frame.interpN V k w'.1
  | .VTypeProd A B, k, w, n, w' => (M.necEvalLvl A k w n.1 w', M.necEvalLvl B k w n.2 w')
  | .VTypeBox U,    k, w, n, w' => M.necEvalLvl U (k + 1) w n w'
  | .VTypeOne,      _, _, _, _  => PUnit.unit
  | .Var,           k, w, n, w' =>
      (M.frame.interp_boxes .Var k w'.1) ▸ M.necEval ((M.frame.interp_boxes .Var (k + 1) w).symm ▸ n) w'
  | .VTypeDia U,    k, w, n, w' =>
      (M.frame.interp_boxes (.VTypeDia U) k w'.1) ▸
        M.necEval ((M.frame.interp_boxes (.VTypeDia U) (k + 1) w).symm ▸ n) w'

/-- **`necEvalLvl` distributes over pairs — DEFINITIONALLY** (structural recursion at products).  This
    unblocks the box-β `pair`/`pair_elim` cases, with NO coherence law added to `RModelB`. -/
theorem necEvalLvl_prod (M : RModel σ) (k : ℕ) {A B : VarType} {w : M.frame.W}
    (a : M.frame.interpN A (k + 1) w) (b : M.frame.interpN B (k + 1) w)
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
    M.necEvalLvl (A.VTypeProd B) k w (show M.frame.interpN (A.VTypeProd B) (k + 1) w from (a, b)) w'
      = (M.necEvalLvl A k w a w', M.necEvalLvl B k w b w') := rfl

/-- Projection commutes (up to `HEq`) with a `cast` between product types, given the *component* type
    equalities (so no type-constructor injectivity needed — proof irrelevance identifies the product
    cast with the one built from `hα`,`hβ`).  Needed to realign the distributed necessary context in
    the box-β product case. -/
theorem cast_fst_heq {X₁ X₂ Y₁ Y₂ : Type u} (hα : X₁ = Y₁) (hβ : X₂ = Y₂) (p : X₁ × X₂) :
    (cast (congrArg₂ Prod hα hβ) p).1 ≍ p.1 := by subst hα; subst hβ; simp

theorem cast_snd_heq {X₁ X₂ Y₁ Y₂ : Type u} (hα : X₁ = Y₁) (hβ : X₂ = Y₂) (p : X₁ × X₂) :
    (cast (congrArg₂ Prod hα hβ) p).2 ≍ p.2 := by subst hα; subst hβ; simp

/-- **Structural peel = field peel, at every type.**  `necEvalLvl` (which distributes over products
    structurally, at all box-depths) agrees with the abstract field `necEval` (a single outer-box
    peel).  Leaves are definitional; the product case is exactly `necEvalStk_prod` (the all-depths
    distribution law); the box case threads the depth.  This is the bridge that lets `posStrengthStk`
    (whose box law yields the *field* peel) meet the interpreter (which uses `necEvalLvl`), unblocking
    the diaterm box-β. -/
theorem necEvalLvl_eq_necEval (M : RModel σ) (V : VarType) :
    ∀ (k : ℕ) (w : M.frame.W) (n : M.frame.interpN V (k + 1) w)
      (w' : {w' : M.frame.W // M.frame.R w w'}),
    M.necEvalLvl V k w n w'
      = (M.frame.interp_boxes V k w'.1) ▸
          M.necEval ((M.frame.interp_boxes V (k + 1) w).symm ▸ n) w' := by
  induction V with
  | Var => intro k w n w'; rfl
  | VTypeOne => intro k w n w'; exact Subsingleton.elim (α := PUnit) _ _
  | VTypeDia U _ => intro k w n w'; rfl
  | VTypeProd A B ihA ihB =>
      intro k w n w'
      -- LHS distributes structurally (`necEvalLvl_prod`, def); RHS distributes via `necEvalStk_prod`.
      show (M.necEvalLvl A k w n.1 w', M.necEvalLvl B k w n.2 w') = _
      rw [ihA k w n.1 w', ihB k w n.2 w']
      simp only [M.necEvalStk_prod (Stk.boxes k), eqRec_eq_cast]
      apply eq_of_heq
      refine HEq.trans ?_ (HEq.symm ((cast_heq _ _).trans (cast_heq _ _)))
      congr 1
      · exact (M.frame.interp_boxes A k w'.1).symm
      · exact (M.frame.interp_boxes B k w'.1).symm
      · refine (cast_heq _ _).trans ?_
        congr 1
        apply eq_of_heq
        refine HEq.trans (cast_heq _ _) (HEq.symm ?_)
        simp only [cast_cast]
        exact cast_fst_heq (M.frame.interp_boxes A (k + 1) w).symm
          (M.frame.interp_boxes B (k + 1) w).symm n
      · refine (cast_heq _ _).trans ?_
        congr 1
        apply eq_of_heq
        refine HEq.trans (cast_heq _ _) (HEq.symm ?_)
        simp only [cast_cast]
        exact cast_snd_heq (M.frame.interp_boxes A (k + 1) w).symm
          (M.frame.interp_boxes B (k + 1) w).symm n
  | VTypeBox U ihU =>
      intro k w n w'
      -- `necEvalLvl (□U) k = necEvalLvl U (k+1)`; field side threads `□^k(□U) = □^{k+1}U`.
      show M.necEvalLvl U (k + 1) w n w' = _
      rw [ihU (k + 1) w n w']
      -- both sides are `cast (necEval (cast n))`; the `necEval` instances agree via `plug_box`.
      simp only [eqRec_eq_cast]
      apply eq_of_heq
      refine (cast_heq _ _).trans (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1 <;> simp only [Stk.boxes, Stk.plug, Stk.plug_box]
      exact (cast_heq _ _).trans (cast_heq _ _).symm

end RModel

namespace RModel
variable {σ : Signature}

/-- `necEvalLvl` commutes with `funcNecStkLvl` (via `funcNecStk_box` + cancelling the `interp_boxes`
    casts) — the crux of the box-β `func` case. -/
theorem funcNecStkLvl_necEvalLvl (M : RModel σ) (k : ℕ) (w : M.frame.W) (f : σ.FuncSyms)
    (args : Fin (σ.funcArity f) → M.frame.interpN VarType.Var (k + 1) w)
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
    M.necEvalLvl VarType.Var k w (M.funcNecStkLvl (k + 1) f args) w'
      = M.funcNecStkLvl k f (fun i => M.necEvalLvl VarType.Var k w (args i) w') := by
  simp only [funcNecStkLvl, necEvalLvl, Stk.boxes, eqRec_eq_cast, cast_cast, cast_eq,
    M.funcNecStk_box]

/-- `necEvalLvl` commutes with `posLiftStkLvl` (the ◇-lift), via `posLiftStk_box` — the ◇-analog of
    `funcNecStkLvl_necEvalLvl`, for the diaterm box-β. -/
theorem posLiftStkLvl_necEvalLvl (M : RModel σ) (k : ℕ) (w : M.frame.W) {A B : VarType}
    (φ : GFunc σ A B) (x : M.frame.interpN A.VTypeDia (k + 1) w)
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
    M.necEvalLvl B.VTypeDia k w (M.posLiftStkLvl (k + 1) φ x) w'
      = M.posLiftStkLvl k φ (M.necEvalLvl A.VTypeDia k w x w') := by
  simp only [posLiftStkLvl, necEvalLvl, Stk.boxes, eqRec_eq_cast, cast_cast, cast_eq,
    M.posLiftStk_box]

/-- `necEvalLvl` commutes with `posStrengthStkLvl` (the ◇-strength): the ◇-typed result/witness are
    leaves (field peel = `necEvalLvl`), and the □-typed necessary arg is reconciled by
    `necEvalLvl_eq_necEval`.  The strength half of the diaterm box-β. -/
theorem posStrengthStkLvl_necEvalLvl (M : RModel σ) (k : ℕ) (w : M.frame.W) {A B : VarType}
    (n : M.frame.interpN A.VTypeBox (k + 1) w) (x : M.frame.interpN B.VTypeDia (k + 1) w)
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
    M.necEvalLvl (A.VTypeProd B).VTypeDia k w (M.posStrengthStkLvl (k + 1) n x) w'
      = M.posStrengthStkLvl k (M.necEvalLvl A.VTypeBox k w n w')
          (M.necEvalLvl B.VTypeDia k w x w') := by
  rw [M.necEvalLvl_eq_necEval A.VTypeBox k w n w']
  simp only [posStrengthStkLvl, necEvalLvl, Stk.boxes, eqRec_eq_cast, cast_cast, cast_eq,
    M.posStrengthStk_box]

/-- **Bundle peel.**  Peeling a level-`(k+1)` bundle (each value by `necEvalLvl`) gives the level-`k`
    bundle of the peeled values: the context *type* and *projections* are level-independent, and the
    packed value distributes by `necEvalLvl_prod` (definitional).  The `□b.1`-vs-`b.1` shift is
    absorbed since `necEvalLvl (□U) k = necEvalLvl U (k+1)`. -/
theorem bundleNecLvl_peel (M : RModel σ) (k : ℕ) (w : M.frame.W)
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
    (l : List (VarSymb × VarType)) →
    (necOf : (p : VarSymb × VarType) → p ∈ l → M.frame.interpN p.2 (k + 1 + 1) w) →
    M.bundleNecLvl k l (fun p hp => M.necEvalLvl p.2.VTypeBox k w (necOf p hp) w')
      = ⟨(M.bundleNecLvl (k + 1) l necOf).1,
         M.necEvalLvl (M.bundleNecLvl (k + 1) l necOf).1.VTypeBox k w
           (M.bundleNecLvl (k + 1) l necOf).2.1 w',
         (M.bundleNecLvl (k + 1) l necOf).2.2⟩
  | [], _ => rfl
  | q :: rest, necOf => by
      have ih := M.bundleNecLvl_peel k w w' rest
        (fun p hp => necOf p (List.mem_cons.mpr (Or.inr hp)))
      simp only [bundleNecLvl]; rw [ih]; rfl

/- **Box-β for the stack-generalized lift** (`termToNecLvl_necEvalLvl`): peeling one box off
   `termToNecLvl (k+1)` gives `termToNecLvl k` with the environment peeled.  Functional core +
   `boxterm` proven; `diaterm` deferred. -/
mutual
theorem termToNecLvl_necEvalLvl (M : RModel σ) : (k : ℕ) → (w : M.frame.W) → {V : VarCtx} →
    (env : (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 (k + 1) w) →
    (w' : {w' : M.frame.W // M.frame.R w w'}) → {S : VarType} → (tt : Term σ V S) →
    M.necEvalLvl S k w (M.termToNecLvl (k + 1) env tt) w'
      = M.termToNecLvl k (fun p hp => M.necEvalLvl p.2 k w (env p hp) w') tt
  | _, _, _, _, _, _, .var ⟨v, hv⟩ => rfl
  | _, _, _, _, _, _, .unit        => rfl
  | k, w, _, env, w', _, .pair a b => by
      simp only [RModel.termToNecLvl, RModel.necEvalLvl,
        M.termToNecLvl_necEvalLvl k w env w' a, M.termToNecLvl_necEvalLvl k w env w' b]
  | k, w, _, env, w', _, .func ff => by
      simp only [RModel.termToNecLvl]
      exact M.funcToNecLvl_necEvalLvl k w env w' ff Fin.elim0 Fin.elim0 (fun i => i.elim0)
  | k, w, _, env, w', _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body => by
      simp only [RModel.termToNecLvl]
      rw [M.termToNecLvl_necEvalLvl k w _ w' body]
      congr 1
      funext p hp
      exact RModel.peLookup_natural
        (X := fun T => M.frame.interpN T (k + 1) w) (Y := fun T => M.frame.interpN T k w'.1)
        (fun {A B} x => (x : M.frame.interpN A (k + 1) w × M.frame.interpN B (k + 1) w).1)
        (fun {A B} x => (x : M.frame.interpN A (k + 1) w × M.frame.interpN B (k + 1) w).2)
        (fun {A B} x => (x : M.frame.interpN A k w'.1 × M.frame.interpN B k w'.1).1)
        (fun {A B} x => (x : M.frame.interpN A k w'.1 × M.frame.interpN B k w'.1).2)
        (fun {_} n => M.necEvalLvl _ k w n w')
        (fun _ => rfl) (fun _ => rfl)
        v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq env p hp
  | k, w, _, env, w', _, .boxterm s hsub _ =>
      M.termToNecLvl_necEvalLvl (k + 1) w
        (fun p hp => env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))) w' s
  | k, w, _, env, w', _, .diaterm x hx tt hsub hnbe => by
      -- ◇-lift and ◇-strength commute with the peel (`posLiftStkLvl_necEvalLvl`,
      -- `posStrengthStkLvl_necEvalLvl`); the bundled necessary context peels by `bundleNecLvl_peel`.
      simp only [RModel.termToNecLvl]
      rw [M.posLiftStkLvl_necEvalLvl, M.posStrengthStkLvl_necEvalLvl,
        M.bundleNecLvl_peel k w w' _ (fun p hp => env (p.1, p.2.VTypeBox)
          (hsub (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_toList.mp hp, rfl⟩))))]

theorem funcToNecLvl_necEvalLvl (M : RModel σ) (k : ℕ) (w : M.frame.W) {V : VarCtx}
    (env : (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 (k + 1) w)
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
    {n : ℕ} → (ff : Func σ V n) → (vecArgs : Fin n → M.frame.interpN VarType.Var (k + 1) w) →
    (peeledArgs : Fin n → M.frame.interpN VarType.Var k w'.1) →
    (∀ i, M.necEvalLvl VarType.Var k w (vecArgs i) w' = peeledArgs i) →
    M.necEvalLvl VarType.Var k w (M.funcToNecLvl (k + 1) env ff vecArgs) w'
      = M.funcToNecLvl k (fun p hp => M.necEvalLvl p.2 k w (env p hp) w') ff peeledArgs
  | _, .F ⟨f, hf⟩, vecArgs, peeledArgs, hrel => by
      subst hf
      simp only [RModel.funcToNecLvl]
      rw [M.funcNecStkLvl_necEvalLvl]
      congr 1; funext i; exact hrel i
  | _, .eval g t, vecArgs, peeledArgs, hrel => by
      simp only [RModel.funcToNecLvl]
      refine M.funcToNecLvl_necEvalLvl k w env w' g (Fin.cons (M.termToNecLvl (k + 1) env t) vecArgs)
        (Fin.cons (M.termToNecLvl k (fun p hp => M.necEvalLvl p.2 k w (env p hp) w') t) peeledArgs) ?_
      intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]; exact M.termToNecLvl_necEvalLvl k w env w' t
      · intro j; simp only [Fin.cons_succ]; exact hrel j
end

end RModel
