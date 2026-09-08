import QML.QML_v11_Symbols

/-!
# QML v11 — Terms

The v11 `Term`, differing from v10 in exactly one constructor: `pair_elim`.

## Which variables are genuinely BOUND

Only `pair_elim`'s two components.  Everything modal keeps user-supplied names, because those
variables stay FREE:

* `boxterm` promotes every variable of the inner context with `□`; all of them remain free and
  referenceable in the result.
* `diaterm x` takes an object in a context `Γ` containing `x`, and produces one in a context where
  every variable of `Γ` *except* `x` is promoted with `□`, `x` itself is promoted with `◇`, and
  the context may be weakened provided no boxed variable is added.  So `x` is a *promoted free*
  variable, not a binder — it is still there afterwards, at type `x.2.VTypeDia`.
* `pair_elim v₁ v₂ z`'s `z` is likewise free: it is the pair variable being destructured, live in
  the output context `W₂`.  Only `v₁, v₂` are consumed.

So `v₁, v₂` are the only genuine binders here, and in v11 they are no longer named: they take the
canonical slots `VarCtx.insertBnd2`, which are functions of the context alone.  The constructor
therefore loses its two symbol arguments, both freshness hypotheses, and the distinctness
hypothesis — all of which are now theorems rather than data.

Consequences: α-variants of a `pair_elim` cannot be *expressed*, so `Proof.pair_elim_alpha` has
nothing left to say and becomes retirable; and since `v₁, v₂` can never be user symbols, a user
variable can never be captured, so `new ∉ Term.boundVars t` side conditions are vacuous for user
renamings.
-/

/-! ## Signature (unchanged from v10) -/

structure Signature where
  FuncSyms : Type
  RelSyms : Type
  funcArity : FuncSyms → ℕ
  relArity  : RelSyms  → ℕ
  [decEqF   : DecidableEq FuncSyms]
  [decEqR   : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

/-! ## Terms -/

mutual
  inductive Func (σ : Signature) : VarCtx → ℕ → Type where
    | F    : {f : σ.FuncSyms // σ.funcArity f = n} → Func σ V n
    | eval : Func σ V (Nat.succ n) → Term σ V .Var → Func σ V n
    deriving DecidableEq

  /-- `Term σ V S`: a term of `VarType` `S` with free variables drawn from `VarCtx` `V`. -/
  inductive Term (σ : Signature) : VarCtx → VarType → Type where
    -- `.var` only produces basic (Var-typed) terms; modal / pair / unit terms must be built via
    -- the dedicated constructors, which removes the syntactic ambiguity where `.var x : T.VTypeBox`
    -- and `.boxterm (.var x) …` would be two forms for the same semantic value.
    | var       : {v : VarSymb // ⟨v, .Var⟩ ∈ V.1} → Term σ V .Var
    | func      : Func σ V 0 → Term σ V .Var
    | boxterm   : Term σ V S → (hsub : (VarCtx_box V).1 ⊆ W.1) →
                  (h_no_box_extras :
                    ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1) →
                  Term σ W S.VTypeBox
    -- `x` is a PROMOTED FREE variable, not a binder: it survives into `W` at type `x.2.VTypeDia`.
    | diaterm   : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V) →
                  Term σ (VarCtx_insert x V hx) S →
                  (hsub : (VarCtx_dia x V hx).1 ⊆ W.1) →
                  (h_no_box_extras :
                    ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1) →
                  Term σ W S.VTypeDia
    | unit      : Term σ V .VTypeOne
    | pair      : Term σ V S → Term σ V T → Term σ V (.VTypeProd S T)
    -- ⭐v11: the two components are BOUND, so they are canonical slots rather than names.  Only
    -- the destructured pair variable `z` is user-supplied, because it stays free in `W₂`.
    | pair_elim : (T₁ T₂ : VarType) → (z : VarSymb) →
                  (hz : z ∉ VarCtx_to_VarSymbs V) →
                  (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁) →
                  (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) →
                  Term σ W₁ S →
                  Term σ W₂ S
  deriving DecidableEq
end

/-! ## Rebuilding along a context bijection

`mapCtx` is the single traversal that renaming, shifting and lifting all reduce to.  At a binder it
uses `CtxBij.extendBnd`, which sends the OLD slot to the NEW one — so slots are RECOMPUTED from the
target context rather than transported, which is what makes the result canonical. -/

mutual
  def Func.mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {N : ℕ}
      (fn : Func σ V N) : Func σ V' N := by
    match fn with
    | .F fs => exact .F fs
    | .eval g t => exact .eval (Func.mapCtx m g) (Term.mapCtx m t)
  termination_by sizeOf fn

  def Term.mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {S : VarType}
      (t : Term σ V S) : Term σ V' S := by
    match t with
    | .var ⟨v, veq⟩ => exact .var ⟨m.toCtxMap.f v, m.toCtxMap.maps ⟨v, .Var⟩ veq⟩
    | .func fn => exact .func (Func.mapCtx m fn)
    | .unit => exact .unit
    | .pair t1 t2 => exact .pair (Term.mapCtx m t1) (Term.mapCtx m t2)
    | .boxterm inner hsub h =>
        rename_i V_inner _
        have hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
          VarCtx.symbs_of_box_sub hsub
        refine .boxterm (Term.mapCtx (m.toImage V_inner hU) inner) ?_ ?_
        · -- the image's box-wrap lands in `V'`
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
          rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
          exact m.toCtxMap.maps ⟨r.1, r.2.VTypeBox⟩
            (hsub (Finset.mem_image.mpr ⟨r, hr, rfl⟩))
        · -- ⭐`onto` is exactly what this needs: every box-typed entry of `V'` comes from one of
          -- `V`, which `h` places in the source inner context, hence in its image.
          intro p hp hbox
          obtain ⟨q, hq, rfl⟩ := m.onto p hp
          have hqbox : VarType.isBox q.2 = true := hbox
          have hqin := h q hq hqbox
          rcases Finset.mem_image.mp hqin with ⟨r, hr, hreq⟩
          refine Finset.mem_image.mpr
            ⟨⟨m.toCtxMap.f r.1, r.2⟩, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
          simp only
          obtain ⟨h1, h2⟩ := Prod.mk.inj hreq
          rw [h1, h2]
    | .diaterm x hx inner hsub h =>
        rename_i V_inner _
        -- `x` is a PROMOTED FREE variable: it sits in `V` as `⟨x.1, ◇x.2⟩`.
        have hxdia : (⟨x.1, x.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
          apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        have hxV : x.1 ∈ VarCtx_to_VarSymbs V :=
          Finset.mem_image.mpr ⟨⟨x.1, x.2.VTypeDia⟩, hxdia, rfl⟩
        have hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V := by
          intro v hv
          rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
          refine Finset.mem_image.mpr ⟨⟨p.1, p.2.VTypeBox⟩, hsub ?_, rfl⟩
          rw [VarCtx_dia_fst]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
        have hx' : m.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m.imageCtx V_inner hU) := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨p, hp, hpeq⟩
          rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
          apply hx
          have : m.toCtxMap.f q.1 = m.toCtxMap.f x.1 := hpeq
          have hq1 : q.1 = x.1 :=
            m.toCtxMap.inj q.1 (hU _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)) x.1 hxV this
          exact hq1 ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩
        refine .diaterm ⟨m.toCtxMap.f x.1, x.2⟩ hx'
          (Term.mapCtx (m.extendPoint V_inner hU x hxV hx hx') inner) ?_ ?_
        · intro p hp
          rw [VarCtx_dia_fst] at hp
          rcases Finset.mem_insert.mp hp with rfl | hbox
          · exact m.toCtxMap.maps ⟨x.1, x.2.VTypeDia⟩ hxdia
          · rcases Finset.mem_image.mp hbox with ⟨q, hq, rfl⟩
            rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
            refine m.toCtxMap.maps ⟨r.1, r.2.VTypeBox⟩ (hsub ?_)
            rw [VarCtx_dia_fst]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
        · intro p hp hbox
          obtain ⟨q, hq, rfl⟩ := m.onto p hp
          have hqin := h q hq hbox
          rw [VarCtx_dia_fst] at hqin ⊢
          rcases Finset.mem_insert.mp hqin with rfl | hqbox
          · exact Finset.mem_insert_self _ _
          · rcases Finset.mem_image.mp hqbox with ⟨r, hr, hreq⟩
            refine Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨⟨m.toCtxMap.f r.1, r.2⟩, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩)
            simp only
            obtain ⟨h1, h2⟩ := Prod.mk.inj hreq
            rw [h1, h2]
    | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
        rename_i pe_V pe_W₁
        subst w₂eq
        have hzV' : (⟨m.toCtxMap.f z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∈ V'.1 :=
          m.toCtxMap.maps _ (Finset.mem_insert_self _ _)
        -- Restrict to the node's base contexts, then extend past BOTH slots.  The slots are
        -- RECOMPUTED from the target base, which is why no level hypothesis appears here — the
        -- difficulty that sank the fixed-offset design simply does not arise.
        -- NOTE: transport `w₁eq` on the MAP, not on `body`; substituting `body` would break the
        -- `sizeOf` relationship the termination proof needs.
        exact .pair_elim T₁ T₂ (m.toCtxMap.f z) (VarCtx_erase_fresh hzV') rfl
          (VarCtx_insert_erase hzV' (VarCtx_erase_fresh hzV'))
          (Term.mapCtx (w₁eq ▸ ((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂) body)
  termination_by sizeOf t
end

/-! ## Renaming, as `mapCtx` along a bijection

⭐Renaming a free variable is `mapCtx` along the swap bijection — ONE LINE.

v10 (and v11 up to commit `399c0fb`) instead carried a ~570-line bespoke traversal with a case
analysis at every constructor, plus `isUsr` hypotheses on BOTH symbols.  Those hypotheses were
there because renaming had to leave the binder slots FIXED, which only works for user variables.
`mapCtx` RECOMPUTES slots from the target context, so no slot-preservation constraint arises, the
`isUsr` hypotheses disappear, and the result is strictly MORE general: it renames bound symbols
too.  The bespoke traversal has been deleted — see that commit if it is ever wanted back. -/

/-- Rename one free variable, by rebuilding along the swap bijection. -/
def Term.rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    {S : VarType} (t : Term σ (VarCtx_insert ⟨old, T⟩ V hold) S) :
    Term σ (VarCtx_insert ⟨new, T⟩ V hnew) S :=
  Term.mapCtx (CtxBij.renameOne old new T hold hnew) t

/-- The same for `Func`. -/
def Func.rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    {N : ℕ} (fn : Func σ (VarCtx_insert ⟨old, T⟩ V hold) N) :
    Func σ (VarCtx_insert ⟨new, T⟩ V hnew) N :=
  Func.mapCtx (CtxBij.renameOne old new T hold hnew) fn

/-! ## Measures

`numNodes` and `diaCount` are the termination measures the substitution machinery uses.  Both drop
the `pair_elim` binder arguments, which are no longer data.

⭐Note what is ABSENT: v10 also carries `Term.boundVars` / `Func.boundVars`, used solely to state
capture-avoidance side conditions.  Those conditions are vacuous in v11 (a user variable cannot be
captured, and a bound one is never renamed by hand), so the whole `boundVars` family is gone. -/

mutual
  def Func.numNodes {σ : Signature} {V : VarCtx} {N : ℕ} : Func σ V N → ℕ
    | .F _      => 1
    | .eval g t => 1 + Func.numNodes g + Term.numNodes t

  def Term.numNodes {σ : Signature} {V : VarCtx} {S : VarType} : Term σ V S → ℕ
    | .var _                   => 1
    | .func f                  => 1 + Func.numNodes f
    | .boxterm inner_t _ _     => 1 + Term.numNodes inner_t
    | .diaterm _ _ inner_t _ _ => 1 + Term.numNodes inner_t
    | .unit                    => 1
    | .pair t1 t2              => 1 + Term.numNodes t1 + Term.numNodes t2
    | .pair_elim _ _ _ _ _ _ b => 1 + Term.numNodes b
end

mutual
  def Func.diaCount {σ : Signature} {V : VarCtx} {N : ℕ} : Func σ V N → ℕ
    | .F _      => 0
    | .eval g t => Func.diaCount g + Term.diaCount t

  def Term.diaCount {σ : Signature} {V : VarCtx} {S : VarType} : Term σ V S → ℕ
    | .var _                   => 0
    | .func f                  => Func.diaCount f
    | .boxterm inner_t _ _     => Term.diaCount inner_t
    | .diaterm _ _ inner_t _ _ => 1 + Term.diaCount inner_t
    | .unit                    => 0
    | .pair t1 t2              => Term.diaCount t1 + Term.diaCount t2
    | .pair_elim _ _ _ _ _ _ b => Term.diaCount b
end

-- `mapCtx` is a pure rebuild: it never creates or destroys a `◇`-node.
mutual
  theorem Func.diaCount_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {N : ℕ}
      (fn : Func σ V N) : Func.diaCount (Func.mapCtx m fn) = Func.diaCount fn := by
    match fn with
    | .F _ => rw [Func.mapCtx]; rfl
    | .eval g t =>
        rw [Func.mapCtx]
        simp only [Func.diaCount]
        rw [Func.diaCount_mapCtx m g, Term.diaCount_mapCtx m t]
  termination_by sizeOf fn

  theorem Term.diaCount_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {S : VarType}
      (t : Term σ V S) : Term.diaCount (Term.mapCtx m t) = Term.diaCount t := by
    match t with
    | .var _ => rw [Term.mapCtx]; rfl
    | .unit => rw [Term.mapCtx]; rfl
    | .func fn =>
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Func.diaCount_mapCtx m fn]
    | .pair t1 t2 =>
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Term.diaCount_mapCtx m t1, Term.diaCount_mapCtx m t2]
    | .boxterm inner hsub h =>
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Term.diaCount_mapCtx _ inner]
    | .diaterm xv hxv inner hsub h =>
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Term.diaCount_mapCtx _ inner]
    | .pair_elim T1 T2 z hz w1eq w2eq body =>
        rename_i pe_V pe_W1
        subst w2eq
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Term.diaCount_mapCtx _ body]
  termination_by sizeOf t
end


-- `mapCtx` is a pure rebuild: the node count is unchanged.
mutual
  theorem Func.numNodes_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {N : ℕ}
      (fn : Func σ V N) : Func.numNodes (Func.mapCtx m fn) = Func.numNodes fn := by
    match fn with
    | .F _ => rw [Func.mapCtx]; rfl
    | .eval g t =>
        rw [Func.mapCtx]
        simp only [Func.numNodes]
        rw [Func.numNodes_mapCtx m g, Term.numNodes_mapCtx m t]
  termination_by sizeOf fn

  theorem Term.numNodes_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {S : VarType}
      (t : Term σ V S) : Term.numNodes (Term.mapCtx m t) = Term.numNodes t := by
    match t with
    | .var _ => rw [Term.mapCtx]; rfl
    | .unit => rw [Term.mapCtx]; rfl
    | .func fn =>
        rw [Term.mapCtx]
        simp only [Term.numNodes]
        rw [Func.numNodes_mapCtx m fn]
    | .pair t1 t2 =>
        rw [Term.mapCtx]
        simp only [Term.numNodes]
        rw [Term.numNodes_mapCtx m t1, Term.numNodes_mapCtx m t2]
    | .boxterm inner hsub h =>
        rw [Term.mapCtx]
        simp only [Term.numNodes]
        rw [Term.numNodes_mapCtx _ inner]
    | .diaterm xv hxv inner hsub h =>
        rw [Term.mapCtx]
        simp only [Term.numNodes]
        rw [Term.numNodes_mapCtx _ inner]
    | .pair_elim T1 T2 z hz w1eq w2eq body =>
        rename_i pe_V pe_W1
        subst w2eq
        rw [Term.mapCtx]
        simp only [Term.numNodes]
        rw [Term.numNodes_mapCtx _ body]
  termination_by sizeOf t
end

/-! ## Pair-elim distribution

`pairElim` moves a term from the SPLIT context `V + two slots` to the JOINED one `V + ⟨z, T₁×T₂⟩`.
It is needed by `ctx_ext`: weakening by a pair-typed variable proceeds by weakening by the two
components and re-pairing.

`Rel.pairElim`/`Term.pairElim` never get genuinely stuck the way `WFF.pairElim` does — `eval` only
takes `Var`-typed terms — but the modal and nested-`pair_elim` arms still wrap rather than descend.
In v11 the two components are the canonical slots of `V`, so they are not arguments. -/

mutual
  def Func.pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
      (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
      (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
      (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) {N : ℕ} :
      Func σ W₁ N → Func σ W₂ N
    | .F h => .F h
    | .eval g t =>
        .eval (Func.pairElim T₁ T₂ z hz w₁eq w₂eq g)
              (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t)

  def Term.pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
      (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
      (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
      (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) {S : VarType} :
      Term σ W₁ S → Term σ W₂ S
    | .unit => .unit
    | .var ⟨w, hw⟩ =>
        have hb₁ : (⟨V.nextBnd, T₁⟩ : VarSymb × VarType) ∈ W₁.1 := by
          rw [← w₁eq]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        have hb₂ : (⟨(VarCtx.insertBnd T₁ V).nextBnd, T₂⟩ : VarSymb × VarType) ∈ W₁.1 := by
          rw [← w₁eq]
          exact Finset.mem_insert_self _ _
        if h₁ : w = V.nextBnd then
          have hT₁ : T₁ = .Var := W₁.2 _ hb₁ ⟨w, .Var⟩ hw h₁.symm
          Term.pair_elim T₁ T₂ z hz w₁eq w₂eq
            (.var ⟨V.nextBnd, by rw [← hT₁]; exact hb₁⟩)
        else if h₂ : w = (VarCtx.insertBnd T₁ V).nextBnd then
          have hT₂ : T₂ = .Var := W₁.2 _ hb₂ ⟨w, .Var⟩ hw h₂.symm
          Term.pair_elim T₁ T₂ z hz w₁eq w₂eq
            (.var ⟨(VarCtx.insertBnd T₁ V).nextBnd, by rw [← hT₂]; exact hb₂⟩)
        else
          have hw_V : (⟨w, .Var⟩ : VarSymb × VarType) ∈ V.1 := by
            have hw_W : (⟨w, .Var⟩ : VarSymb × VarType) ∈ W₁.1 := hw
            rw [← w₁eq] at hw_W
            rcases Finset.mem_insert.mp hw_W with h_eq | h_rest
            · exact absurd (congrArg Prod.fst h_eq) h₂
            · rcases Finset.mem_insert.mp h_rest with h_eq | h_in
              · exact absurd (congrArg Prod.fst h_eq) h₁
              · exact h_in
          .var ⟨w, by rw [← w₂eq]; exact Finset.mem_insert_of_mem hw_V⟩
    | .func f => .func (Func.pairElim T₁ T₂ z hz w₁eq w₂eq f)
    | .pair t₁ t₂ =>
        .pair (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t₁)
              (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t₂)
    | .boxterm tt hsub hne =>
        Term.pair_elim T₁ T₂ z hz w₁eq w₂eq (.boxterm tt hsub hne)
    | .diaterm xv hxv tt hsub hne =>
        Term.pair_elim T₁ T₂ z hz w₁eq w₂eq (.diaterm xv hxv tt hsub hne)
    | .pair_elim T₁' T₂' z' hz' w₁eq' w₂eq' body =>
        Term.pair_elim T₁ T₂ z hz w₁eq w₂eq
          (.pair_elim T₁' T₂' z' hz' w₁eq' w₂eq' body)
end

-- `pairElim` only ever wraps or descends; it never creates or destroys a `◇`-node.
mutual
  theorem Func.diaCount_pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
      (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
      (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
      (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) {N : ℕ} (fn : Func σ W₁ N) :
      Func.diaCount (Func.pairElim T₁ T₂ z hz w₁eq w₂eq fn) = Func.diaCount fn := by
    match fn with
    | .F _ => rfl
    | .eval g t =>
        rw [Func.pairElim]
        simp only [Func.diaCount]
        rw [Func.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq g,
            Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq t]
  termination_by sizeOf fn

  theorem Term.diaCount_pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
      (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
      (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
      (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) {S : VarType} (t : Term σ W₁ S) :
      Term.diaCount (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t) = Term.diaCount t := by
    match t with
    | .unit => rfl
    | .var ⟨w, hw⟩ =>
        rw [Term.pairElim]
        split_ifs <;> rfl
    | .func f =>
        rw [Term.pairElim]
        simp only [Term.diaCount]
        rw [Func.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq f]
    | .pair t₁ t₂ =>
        rw [Term.pairElim]
        simp only [Term.diaCount]
        rw [Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq t₁,
            Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq t₂]
    | .boxterm _ _ _ => rfl
    | .diaterm _ _ _ _ _ => rfl
    | .pair_elim _ _ _ _ _ _ _ => rfl
  termination_by sizeOf t
end

/-! ## Weakening by a user variable

Weakening is NOT a `CtxBij` (it is not onto), so it needs its own traversal.  This is the
user-variable case — the only one the proof rules ever need, since the variable being added is
always an eigenvariable.  It takes a `UserSymb` directly, so there is no predicate to carry.

⭐The binder arms are trivial here: `VarCtx.nextBnd_insert_isUsr` says a user insert does not move
the canonical slot, so a `pair_elim`'s components are the SAME before and after — no renaming, no
recomputation.  (Weakening by a BOUND slot does move them; that case belongs with the substitution
machinery, which is where it is needed.) -/

mutual
  def Func.ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
      (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {N : ℕ} (fn : Func σ V N) :
      Func σ (VarCtx_insert ⟨u.toVar, T⟩ V hu) N := by
    match fn with
    | .F fs => exact .F fs
    | .eval g t => exact .eval (Func.ctx_extU u T hu g) (Term.ctx_extU u T hu t)
  termination_by (sizeOf T, sizeOf fn)

  def Term.ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
      (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S) :
      Term σ (VarCtx_insert ⟨u.toVar, T⟩ V hu) S := by
    match t with
    | .var ⟨w, hw⟩ => exact .var ⟨w, Finset.mem_insert_of_mem hw⟩
    | .func fn => exact .func (Func.ctx_extU u T hu fn)
    | .unit => exact .unit
    | .pair t1 t2 => exact .pair (Term.ctx_extU u T hu t1) (Term.ctx_extU u T hu t2)
    | .boxterm tt hsub hne =>
        rename_i V_inner S_inner
        have hu_inner : u.toVar ∉ VarCtx_to_VarSymbs V_inner := by
          intro h_in
          apply hu
          obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in
          exact Finset.mem_image.mpr ⟨⟨q.1, q.2.VTypeBox⟩,
            hsub (Finset.mem_image.mpr ⟨q, hq_in, rfl⟩), hq_eq⟩
        match h_T : T with
        | .VTypeBox U' =>
            -- Box-typed: the inner context gains `⟨u, U'⟩`; recurse into `tt` at the SMALLER type.
            subst h_T
            refine .boxterm (Term.ctx_extU u U' hu_inner tt) ?_ ?_
            · rw [VarCtx_box_fst_insert]
              intro p hp
              rcases Finset.mem_insert.mp hp with rfl | hp_box
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hsub hp_box)
            · intro p hp h_box
              rw [VarCtx_box_fst_insert]
              rcases Finset.mem_insert.mp hp with rfl | hp_V
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hne p hp_V h_box)
        | .VTypeProd a b =>
            -- ⭐Pair-typed: weaken by the two COMPONENTS under fresh USER names, rename each to
            -- its canonical slot, then re-pair.  v10 needs `Term.boundVars` in its avoid set here;
            -- capture is impossible in v11, so the CONTEXT alone suffices.
            subst h_T
            have hw1 : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar ∉ VarCtx_to_VarSymbs V :=
              UserSymb.fresh_not_mem _
            have hw2 : (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))).toVar
                ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd a V) := UserSymb.fresh_not_mem _
            exact Term.pairElim a b u.toVar hu rfl rfl
              (Term.rename _ (VarCtx.insertBnd a V).nextBnd b hw2 (VarCtx.nextBnd_not_mem _)
                (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))) b hw2
                  (Term.rename _ V.nextBnd a hw1 (VarCtx.nextBnd_not_mem V)
                    (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) a hw1
                      (.boxterm tt hsub hne)))))
        | .Var | .VTypeOne | .VTypeDia _ =>
            -- Not box-typed and not a pair: the inner context is untouched, and the added entry
            -- cannot be box-typed, so `h_no_box_extras` transfers unchanged.
            all_goals
              subst h_T
              refine .boxterm tt (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
              intro p hp h_box
              rcases Finset.mem_insert.mp hp with rfl | hp_V
              · simp [VarType.isBox] at h_box
              · exact hne p hp_V h_box
    | .diaterm x hx inner hsub hne =>
        rename_i V_inner S_inner
        have hu_inner : u.toVar ∉ VarCtx_to_VarSymbs V_inner := by
          intro h_in
          apply hu
          obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in
          refine Finset.mem_image.mpr ⟨⟨q.1, q.2.VTypeBox⟩, hsub ?_, hq_eq⟩
          rw [VarCtx_dia_fst]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, hq_in, rfl⟩)
        -- The witness `x` is FREE in `V` (as `⟨x.1, ◇x.2⟩`), so it differs from the new variable.
        have hu_ne_x : u.toVar ≠ x.1 := by
          intro h_eq
          apply hu
          refine Finset.mem_image.mpr ⟨⟨x.1, x.2.VTypeDia⟩, hsub ?_, h_eq.symm⟩
          rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        have hu_outer : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert x V_inner hx) :=
          not_mem_VarSymbs_insert hu_ne_x hu_inner
        match h_T : T with
        | .VTypeBox U' =>
            -- Recurse into the inner term, then swap the inserts so the ◇-witness stays outermost.
            subst h_T
            have hx_ext : x.1 ∉ VarCtx_to_VarSymbs
                (VarCtx_insert ⟨u.toVar, U'⟩ V_inner hu_inner) :=
              not_mem_VarSymbs_insert (Ne.symm hu_ne_x) hx
            have h_swap : VarCtx_insert ⟨u.toVar, U'⟩ (VarCtx_insert x V_inner hx) hu_outer
                = VarCtx_insert x (VarCtx_insert ⟨u.toVar, U'⟩ V_inner hu_inner) hx_ext :=
              VarCtx_insert_comm hu_outer hx_ext
            refine .diaterm x hx_ext
              (h_swap ▸ Term.ctx_extU u U' hu_outer inner) ?_ ?_
            · rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
              intro p hp
              rcases Finset.mem_insert.mp hp with rfl | hp1
              · refine Finset.mem_insert_of_mem (hsub ?_)
                rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
              · rcases Finset.mem_insert.mp hp1 with rfl | hp_box
                · exact Finset.mem_insert_self _ _
                · refine Finset.mem_insert_of_mem (hsub ?_)
                  rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_box
            · intro p hp h_box
              rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
              rcases Finset.mem_insert.mp hp with rfl | hp_V
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              · have := hne p hp_V h_box
                rw [VarCtx_dia_fst] at this
                rcases Finset.mem_insert.mp this with rfl | hp_box
                · exact Finset.mem_insert_self _ _
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp_box)
        | .VTypeProd a b =>
            -- Same peel as `boxterm`: weaken by the two components under fresh USER names,
            -- rename each to its canonical slot, then re-pair.
            subst h_T
            have hw1 : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar ∉ VarCtx_to_VarSymbs V :=
              UserSymb.fresh_not_mem _
            have hw2 : (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))).toVar
                ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd a V) := UserSymb.fresh_not_mem _
            exact Term.pairElim a b u.toVar hu rfl rfl
              (Term.rename _ (VarCtx.insertBnd a V).nextBnd b hw2 (VarCtx.nextBnd_not_mem _)
                (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))) b hw2
                  (Term.rename _ V.nextBnd a hw1 (VarCtx.nextBnd_not_mem V)
                    (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) a hw1
                      (.diaterm x hx inner hsub hne)))))
        | .Var | .VTypeOne | .VTypeDia _ =>
            all_goals
              subst h_T
              refine .diaterm x hx inner (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
              intro p hp h_box
              rcases Finset.mem_insert.mp hp with rfl | hp_V
              · simp [VarType.isBox] at h_box
              · exact hne p hp_V h_box
    | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
        rename_i pe_V pe_W₁
        subst w₂eq
        have hu_pe : u.toVar ∉ VarCtx_to_VarSymbs pe_V := by
          intro hm
          exact hu (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem hm)
        have hz_ne : z ≠ u.toVar := by
          intro h
          refine hu ?_
          rw [VarCtx_to_VarSymbs_insert, ← h]
          exact Finset.mem_insert_self _ _
        have hz' : z ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe) :=
          not_mem_VarSymbs_insert hz_ne hz
        have hu_bnd2 : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd2 T₁ T₂ pe_V) :=
          VarCtx.notMem_insertBnd_of_isUsr rfl T₂
            (VarCtx.notMem_insertBnd_of_isUsr rfl T₁ hu_pe)
        have hu_W₁ : u.toVar ∉ VarCtx_to_VarSymbs pe_W₁ := w₁eq ▸ hu_bnd2
        -- ⭐The slots do not move: a user insert leaves `nextBnd` alone, so the rebuilt node's
        -- components are literally the same ones.  Target the BODY's context so `body` is passed
        -- untouched (transporting it would break the `sizeOf` relation termination needs).
        have w₁eq' : VarCtx.insertBnd2 T₁ T₂ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe)
            = VarCtx_insert ⟨u.toVar, T⟩ pe_W₁ hu_W₁ := by
          rw [VarCtx.insertBnd2_comm_insert ⟨u.toVar, T⟩ pe_V hu_pe rfl T₁ T₂ hu_bnd2]
          apply VarCtx_ext
          change insert (⟨u.toVar, T⟩ : VarSymb × VarType) (VarCtx.insertBnd2 T₁ T₂ pe_V).1
               = insert (⟨u.toVar, T⟩ : VarSymb × VarType) pe_W₁.1
          rw [w₁eq]
        exact .pair_elim T₁ T₂ z hz' w₁eq'
          (VarCtx_insert_comm hz' (not_mem_VarSymbs_insert (Ne.symm hz_ne) hu_pe))
          (Term.ctx_extU u T hu_W₁ body)
  termination_by (sizeOf T, sizeOf t)
end

/-! ## Cast invariance of the measures (ported from v10) -/

-- Term.numNodes is invariant under VarCtx-equality casts.
lemma Term.numNodes_ctx_cast {σ : Signature} {V V' : VarCtx} {S : VarType}
    (h : V = V') (t : Term σ V S) :
    Term.numNodes (h ▸ t) = Term.numNodes t := by
  cases h; rfl

-- Term.sizeOf is invariant under VarCtx-equality casts.
lemma Term.sizeOf_ctx_cast {σ : Signature} {V V' : VarCtx} {S : VarType}
    (h : V = V') (t : Term σ V S) :
    sizeOf (h ▸ t) = sizeOf t := by
  cases h; rfl

-- Term.diaCount is invariant under VarCtx-equality casts.
lemma Term.diaCount_ctx_cast {σ : Signature} {V V' : VarCtx} {S : VarType}
    (h : V = V') (t : Term σ V S) :
    Term.diaCount (h ▸ t) = Term.diaCount t := by
  cases h; rfl

-- Func.diaCount is invariant under VarCtx-equality casts.
lemma Func.diaCount_ctx_cast {σ : Signature} {V V' : VarCtx} {N : ℕ}
    (h : V = V') (f : Func σ V N) :
    Func.diaCount (h ▸ f) = Func.diaCount f := by
  cases h; rfl
