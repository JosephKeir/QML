import QML.QML_v11_Rel

/-!
# QML v11 — Well-formed formulas

Three constructors bind, and all three become nameless: `all`, `ex` and `pair_elim`.  Each takes
the canonical slot(s) of its base context (`VarCtx.insertBnd` / `insertBnd2`) instead of a symbol,
so it sheds its symbol argument AND its freshness hypothesis — both are now theorems.

The modal constructors are unchanged.  `box` promotes every variable of the inner context with `□`;
`dia x` promotes all but `x` with `□` and `x` itself with `◇`, optionally weakening provided no
boxed variable is added.  In both cases the variables stay FREE, so they keep user-supplied names —
`dia`'s `x` is a promoted free variable, not a binder.

⭐Consequence: α-variants of a quantified formula are not EXPRESSIBLE.  Two formulas built at the
same context necessarily choose the same binder, which is exactly what `Proof.congAll` needs and
what makes `hcomm` (`eqRec` commutes with weakening) an equality rather than an implication.
-/

inductive WFF (σ : Signature) : VarCtx → Type where
  | atom : Rel σ V 0 → WFF σ V
  | top  : WFF σ V
  | bot  : WFF σ V
  | and  : WFF σ V → WFF σ V → WFF σ V
  | or   : WFF σ V → WFF σ V → WFF σ V
  | imp  : WFF σ V → WFF σ V → WFF σ V
  -- ⭐Nameless: the binder is `VarCtx.nextBnd V`, so only its TYPE is data.
  | all  : (T : VarType) → WFF σ (VarCtx.insertBnd T V) → WFF σ V
  | ex   : (T : VarType) → WFF σ (VarCtx.insertBnd T V) → WFF σ V
  -- ⭐PRIMITIVE ONLY AT `.Var`.  Equality at every compound type is DEFINED from this one by
  -- `eqRec`, recursing through the extensionality principles, so `box_ext`/`dia_ext` are not
  -- rules but definitional unfoldings — see the eq-by-extensionality reform.
  | eq   : Term σ V .Var → Term σ V .Var → WFF σ V
  -- Modal: inner-context variables are PROMOTED FREE, so they keep their names.
  | box : WFF σ V → (hsub : (VarCtx_box V).1 ⊆ W.1) →
          (h_no_box_extras :
            ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1) →
          WFF σ W
  | dia : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V) →
          WFF σ (VarCtx_insert x V hx) →
          (hsub : (VarCtx_dia x V hx).1 ⊆ W.1) →
          (h_no_box_extras :
            ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1) →
          WFF σ W
  -- ⭐Nameless components; `z` stays user-supplied because it remains FREE in `W₂`.
  | pair_elim : (T₁ T₂ : VarType) → (z : VarSymb) →
                (hz : z ∉ VarCtx_to_VarSymbs V) →
                (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁) →
                (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) →
                WFF σ W₁ →
                WFF σ W₂
  deriving DecidableEq

abbrev neg {σ : Signature} {V : VarCtx} (φ : WFF σ V) : WFF σ V := φ.imp .bot

/-! ## Modal helpers (unchanged from v10) -/

def WFF.box_Finset {σ : Signature} {V W : VarCtx} (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1) :
    Finset (WFF σ V) → Finset (WFF σ W) :=
  fun Γ => Finset.image (fun ψ => WFF.box ψ hsub h_no_box_extras) Γ

def WFF.dia_Finset {σ : Signature} {V W : VarCtx} (x : VarSymb × VarType)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1) :
    Finset (WFF σ (VarCtx_insert x V hx)) → Finset (WFF σ W) :=
  fun Γ => Finset.image (fun ψ => WFF.dia x hx ψ hsub h_no_box_extras) Γ

/-- The **witnessed box** `□_x φ := ¬◇_x¬φ` — "at every realization of the possible object `x`,
    `φ`."  Dual of `WFF.dia`; the `x`-dependent side-hypothesis family of `K_dia`. -/
def WFF.box_x {σ : Signature} {V W : VarCtx} (x : VarSymb × VarType)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (φ : WFF σ (VarCtx_insert x V hx)) : WFF σ W :=
  neg (WFF.dia x hx (neg φ) hsub h_no_box_extras)

def WFF.box_x_Finset {σ : Signature} {V W : VarCtx} (x : VarSymb × VarType)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1) :
    Finset (WFF σ (VarCtx_insert x V hx)) → Finset (WFF σ W) :=
  fun Γ => Finset.image (fun ψ => WFF.box_x x hx hsub h_no_box_extras ψ) Γ

/-! ## Rebuilding along a context bijection

The same traversal as `Term.mapCtx`.  Note how cheap the QUANTIFIER arms are: `extendBnd` supplies
the map past the binder and the constructor recomputes the slot, so there is nothing to say. -/

def WFF.mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (φ : WFF σ V) :
    WFF σ V' := by
  match φ with
  | .atom R  => exact .atom (Rel.mapCtx m R)
  | .top     => exact .top
  | .bot     => exact .bot
  | .and φ ψ => exact .and (WFF.mapCtx m φ) (WFF.mapCtx m ψ)
  | .or φ ψ  => exact .or (WFF.mapCtx m φ) (WFF.mapCtx m ψ)
  | .imp φ ψ => exact .imp (WFF.mapCtx m φ) (WFF.mapCtx m ψ)
  | .eq s t  => exact .eq (Term.mapCtx m s) (Term.mapCtx m t)
  -- ⭐The whole quantifier case: extend past the binder, recurse.  No name, no freshness, no
  -- collision branch — the payoff of nameless binders.
  | .all T ψ => exact .all T (WFF.mapCtx (m.extendBnd T) ψ)
  | .ex T ψ  => exact .ex T (WFF.mapCtx (m.extendBnd T) ψ)
  | .box inner hsub h =>
      rename_i V_inner
      have hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_box_sub hsub
      refine .box (WFF.mapCtx (m.toImage V_inner hU) inner) ?_ ?_
      · intro p hp
        rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
        exact m.toCtxMap.maps ⟨r.1, r.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨r, hr, rfl⟩))
      · intro p hp hbox
        obtain ⟨q, hq, rfl⟩ := m.onto p hp
        have hqin := h q hq hbox
        rcases Finset.mem_image.mp hqin with ⟨r, hr, hreq⟩
        refine Finset.mem_image.mpr
          ⟨⟨m.toCtxMap.f r.1, r.2⟩, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
        simp only
        obtain ⟨h1, h2⟩ := Prod.mk.inj hreq
        rw [h1, h2]
  | .dia x hx inner hsub h =>
      rename_i V_inner
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
        have hfq : m.toCtxMap.f q.1 = m.toCtxMap.f x.1 := hpeq
        have hq1 : q.1 = x.1 :=
          m.toCtxMap.inj q.1 (hU _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)) x.1 hxV hfq
        exact hq1 ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩
      refine .dia ⟨m.toCtxMap.f x.1, x.2⟩ hx'
        (WFF.mapCtx (m.extendPoint V_inner hU x hxV hx hx') inner) ?_ ?_
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
      rename_i pe_V _
      subst w₂eq
      have hzV' : (⟨m.toCtxMap.f z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∈ V'.1 :=
        m.toCtxMap.maps _ (Finset.mem_insert_self _ _)
      -- transport `w₁eq` on the MAP, never on `body` (that breaks the `sizeOf` relation)
      exact .pair_elim T₁ T₂ (m.toCtxMap.f z) (VarCtx_erase_fresh hzV') rfl
        (VarCtx_insert_erase hzV' (VarCtx_erase_fresh hzV'))
        (WFF.mapCtx (w₁eq ▸ ((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂) body)
  termination_by sizeOf φ

/-- Rename one free variable in a formula, by rebuilding along the swap bijection. -/
def WFF.rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨old, T⟩ V hold)) :
    WFF σ (VarCtx_insert ⟨new, T⟩ V hnew) :=
  WFF.mapCtx (CtxBij.renameOne old new T hold hnew) φ

/-! ## Measures -/

def WFF.numNodes {σ : Signature} : {V : VarCtx} → WFF σ V → ℕ
  | _, .atom R                    => 1 + Rel.numNodes R
  | _, .top                       => 1
  | _, .bot                       => 1
  | _, .and φ ψ                   => 1 + WFF.numNodes φ + WFF.numNodes ψ
  | _, .or φ ψ                    => 1 + WFF.numNodes φ + WFF.numNodes ψ
  | _, .imp φ ψ                   => 1 + WFF.numNodes φ + WFF.numNodes ψ
  | _, .all _ φ                   => 1 + WFF.numNodes φ
  | _, .ex _ φ                    => 1 + WFF.numNodes φ
  | _, .eq s t                    => 1 + Term.numNodes s + Term.numNodes t
  | _, .box φ _ _                 => 1 + WFF.numNodes φ
  | _, .dia _ _ φ _ _             => 1 + WFF.numNodes φ
  | _, .pair_elim _ _ _ _ _ _ φ   => 1 + WFF.numNodes φ

def WFF.diaCount {σ : Signature} : {V : VarCtx} → WFF σ V → ℕ
  | _, .atom R                    => Rel.diaCount R
  | _, .top                       => 0
  | _, .bot                       => 0
  | _, .and φ ψ                   => WFF.diaCount φ + WFF.diaCount ψ
  | _, .or φ ψ                    => WFF.diaCount φ + WFF.diaCount ψ
  | _, .imp φ ψ                   => WFF.diaCount φ + WFF.diaCount ψ
  | _, .all _ φ                   => WFF.diaCount φ
  | _, .ex _ φ                    => WFF.diaCount φ
  | _, .eq s t                    => Term.diaCount s + Term.diaCount t
  | _, .box φ _ _                 => WFF.diaCount φ
  | _, .dia _ _ φ _ _             => 1 + WFF.diaCount φ
  | _, .pair_elim _ _ _ _ _ _ φ   => WFF.diaCount φ


/-- Sum of the pair-depths of a formula's QUANTIFIER binders.

    ⭐The invariant it exists for: descending into `.all T ψ` moves `T.pairDepth` OUT of the
    formula and INTO the context, so `V.pairDepth + binderPairDepth φ` is unchanged.  That is what
    lets `substCore` recurse under a quantifier at all — the context's `pairDepth` alone grows.

    `.dia` contributes nothing: its variable is a promoted FREE variable of the outer context, not
    a new binder, so its pair structure is already counted there (as `◇x.2`, whose `pairDepth` is
    `x.2.pairDepth`).  Likewise `.pair_elim`, whose split context is strictly SHALLOWER than its
    joined one. -/
def WFF.binderPairDepth {σ : Signature} : {V : VarCtx} → WFF σ V → ℕ
  | _, .atom _                  => 0
  | _, .top                     => 0
  | _, .bot                     => 0
  | _, .and φ ψ                 => WFF.binderPairDepth φ + WFF.binderPairDepth ψ
  | _, .or φ ψ                  => WFF.binderPairDepth φ + WFF.binderPairDepth ψ
  | _, .imp φ ψ                 => WFF.binderPairDepth φ + WFF.binderPairDepth ψ
  | _, .all T φ                 => T.pairDepth + WFF.binderPairDepth φ
  | _, .ex T φ                  => T.pairDepth + WFF.binderPairDepth φ
  | _, .eq _ _                  => 0
  | _, .box φ _ _               => WFF.binderPairDepth φ
  | _, .dia _ _ φ _ _           => WFF.binderPairDepth φ
  | _, .pair_elim _ _ _ _ _ _ φ => WFF.binderPairDepth φ

lemma WFF.binderPairDepth_ctx_cast {σ : Signature} {V V' : VarCtx} (h : V = V') (φ : WFF σ V) :
    WFF.binderPairDepth (h ▸ φ) = WFF.binderPairDepth φ := by cases h; rfl

theorem WFF.binderPairDepth_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V')
    (φ : WFF σ V) :
    WFF.binderPairDepth (WFF.mapCtx m φ) = WFF.binderPairDepth φ := by
  match φ with
  | .atom R => rw [WFF.mapCtx]; rfl
  | .top => rw [WFF.mapCtx]; rfl
  | .bot => rw [WFF.mapCtx]; rfl
  | .and φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_mapCtx m φ, WFF.binderPairDepth_mapCtx m ψ]
  | .or φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_mapCtx m φ, WFF.binderPairDepth_mapCtx m ψ]
  | .imp φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_mapCtx m φ, WFF.binderPairDepth_mapCtx m ψ]
  | .eq s t => rw [WFF.mapCtx]; rfl
  | .all T ψ =>
      rw [WFF.mapCtx]; simp only [WFF.binderPairDepth]; rw [WFF.binderPairDepth_mapCtx _ ψ]
  | .ex T ψ =>
      rw [WFF.mapCtx]; simp only [WFF.binderPairDepth]; rw [WFF.binderPairDepth_mapCtx _ ψ]
  | .box inner hsub h =>
      rw [WFF.mapCtx]; simp only [WFF.binderPairDepth]; rw [WFF.binderPairDepth_mapCtx _ inner]
  | .dia x hx inner hsub h =>
      rw [WFF.mapCtx]; simp only [WFF.binderPairDepth]; rw [WFF.binderPairDepth_mapCtx _ inner]
  | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
      rename_i pe_V _
      subst w₂eq
      rw [WFF.mapCtx]; simp only [WFF.binderPairDepth]; rw [WFF.binderPairDepth_mapCtx _ body]
  termination_by sizeOf φ

theorem WFF.binderPairDepth_rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨old, T⟩ V hold)) :
    WFF.binderPairDepth (WFF.rename old new T hold hnew φ) = WFF.binderPairDepth φ :=
  WFF.binderPairDepth_mapCtx _ φ

/-! ## Cast and `mapCtx` invariance of the measures -/

lemma WFF.numNodes_ctx_cast {σ : Signature} {V V' : VarCtx} (h : V = V') (φ : WFF σ V) :
    WFF.numNodes (h ▸ φ) = WFF.numNodes φ := by cases h; rfl

lemma WFF.diaCount_ctx_cast {σ : Signature} {V V' : VarCtx} (h : V = V') (φ : WFF σ V) :
    WFF.diaCount (h ▸ φ) = WFF.diaCount φ := by cases h; rfl

lemma WFF.sizeOf_ctx_cast {σ : Signature} {V V' : VarCtx} (h : V = V') (φ : WFF σ V) :
    sizeOf (h ▸ φ) = sizeOf φ := by cases h; rfl

theorem WFF.numNodes_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (φ : WFF σ V) :
    WFF.numNodes (WFF.mapCtx m φ) = WFF.numNodes φ := by
  match φ with
  | .atom R =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]; rw [Rel.numNodes_mapCtx m R]
  | .top => rw [WFF.mapCtx]; rfl
  | .bot => rw [WFF.mapCtx]; rfl
  | .and φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]
      rw [WFF.numNodes_mapCtx m φ, WFF.numNodes_mapCtx m ψ]
  | .or φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]
      rw [WFF.numNodes_mapCtx m φ, WFF.numNodes_mapCtx m ψ]
  | .imp φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]
      rw [WFF.numNodes_mapCtx m φ, WFF.numNodes_mapCtx m ψ]
  | .eq s t =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]
      rw [Term.numNodes_mapCtx m s, Term.numNodes_mapCtx m t]
  | .all T ψ =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]; rw [WFF.numNodes_mapCtx _ ψ]
  | .ex T ψ =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]; rw [WFF.numNodes_mapCtx _ ψ]
  | .box inner hsub h =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]; rw [WFF.numNodes_mapCtx _ inner]
  | .dia x hx inner hsub h =>
      rw [WFF.mapCtx]; simp only [WFF.numNodes]; rw [WFF.numNodes_mapCtx _ inner]
  | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
      rename_i pe_V _
      subst w₂eq
      rw [WFF.mapCtx]; simp only [WFF.numNodes]; rw [WFF.numNodes_mapCtx _ body]
  termination_by sizeOf φ

theorem WFF.diaCount_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (φ : WFF σ V) :
    WFF.diaCount (WFF.mapCtx m φ) = WFF.diaCount φ := by
  match φ with
  | .atom R =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]; rw [Rel.diaCount_mapCtx m R]
  | .top => rw [WFF.mapCtx]; rfl
  | .bot => rw [WFF.mapCtx]; rfl
  | .and φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]
      rw [WFF.diaCount_mapCtx m φ, WFF.diaCount_mapCtx m ψ]
  | .or φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]
      rw [WFF.diaCount_mapCtx m φ, WFF.diaCount_mapCtx m ψ]
  | .imp φ ψ =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]
      rw [WFF.diaCount_mapCtx m φ, WFF.diaCount_mapCtx m ψ]
  | .eq s t =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]
      rw [Term.diaCount_mapCtx m s, Term.diaCount_mapCtx m t]
  | .all T ψ =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]; rw [WFF.diaCount_mapCtx _ ψ]
  | .ex T ψ =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]; rw [WFF.diaCount_mapCtx _ ψ]
  | .box inner hsub h =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]; rw [WFF.diaCount_mapCtx _ inner]
  | .dia x hx inner hsub h =>
      rw [WFF.mapCtx]; simp only [WFF.diaCount]; rw [WFF.diaCount_mapCtx _ inner]
  | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
      rename_i pe_V _
      subst w₂eq
      rw [WFF.mapCtx]; simp only [WFF.diaCount]; rw [WFF.diaCount_mapCtx _ body]
  termination_by sizeOf φ

theorem WFF.diaCount_rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨old, T⟩ V hold)) :
    WFF.diaCount (WFF.rename old new T hold hnew φ) = WFF.diaCount φ :=
  WFF.diaCount_mapCtx _ φ

/-! ## Pair-elim distribution

`WFF.pairElim` moves a formula from the SPLIT context `V + two slots` to the JOINED one
`V + ⟨z, T₁×T₂⟩`.  It is the **positive eliminator** for products commuting inward — the
*commuting conversions* — so it descends through every connective for which one exists and wraps
where none does.

* **`box` / `dia`**: genuinely stuck, and structurally so.  `isBox` of a product is the DISJUNCTION
  of its components, so if either is box-typed then `⟨z, T₁ ×ᵥ T₂⟩` is a box-detected entry that is
  not of the form `□T`, and `h_no_box_extras` becomes unsatisfiable — no `box` can exist in `W₂`
  at all.  The pushed-in form does not typecheck.
* **`all` / `ex`**: ⭐NOT stuck.  This is where v11 pays off.  v10 had to α-rename the binder
  (unconditionally, to keep the arm branch-free) and prove four measure lemmas about that rename.
  Here the binder is nameless, so all that remains is a slot BOOKKEEPING step: the body sits in
  `insertBnd T (insertBnd2 T₁ T₂ V)` — slots `(T₁, T₂, T)` — and the rebuilt node needs
  `insertBnd2 T₁ T₂ (insertBnd T V)` — slots `(T, T₁, T₂)`.  Same three types, cyclically shifted,
  so `CtxBij.rot3` and `mapCtx` do it.

⭐`z` must be USER-named (`hzu`).  That is exactly the design's rule boundary: `z` stays FREE in
`W₂`, so it is user-supplied, and being user-supplied is what makes `insertBnd` commute past it. -/

def WFF.pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
    (T₁ T₂ : VarType) (z : VarSymb) (hzu : z.isUsr = true)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂)
    (φ : WFF σ W₁) : WFF σ W₂ := by
  match φ with
  | .atom R  => exact .atom (Rel.pairElim T₁ T₂ z hz w₁eq w₂eq R)
  | .top     => exact .top
  | .bot     => exact .bot
  | .and φ ψ =>
      exact .and (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ)
                 (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ)
  | .or φ ψ  =>
      exact .or (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ)
                (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ)
  | .imp φ ψ =>
      exact .imp (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ)
                 (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ)
  | .eq s t  =>
      exact .eq (Term.pairElim T₁ T₂ z hz w₁eq w₂eq s)
                (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t)
  | .box inner hsub h =>
      exact .pair_elim T₁ T₂ z hz w₁eq w₂eq (.box inner hsub h)
  | .dia x hx inner hsub h =>
      exact .pair_elim T₁ T₂ z hz w₁eq w₂eq (.dia x hx inner hsub h)
  | .pair_elim T₁' T₂' z' hz' w₁eq' w₂eq' body =>
      exact .pair_elim T₁ T₂ z hz w₁eq w₂eq (.pair_elim T₁' T₂' z' hz' w₁eq' w₂eq' body)
  | .all T ψ =>
      exact .all T (WFF.pairElim T₁ T₂ z hzu (VarCtx.notMem_insertBnd_of_isUsr hzu T hz) rfl
        (VarCtx.quant_pairElim_w₂eq hzu hz w₂eq T)
        (WFF.mapCtx (CtxBij.quantRot T₁ T₂ T V)
          ((congrArg (VarCtx.insertBnd T) w₁eq).symm ▸ ψ)))
  | .ex T ψ =>
      exact .ex T (WFF.pairElim T₁ T₂ z hzu (VarCtx.notMem_insertBnd_of_isUsr hzu T hz) rfl
        (VarCtx.quant_pairElim_w₂eq hzu hz w₂eq T)
        (WFF.mapCtx (CtxBij.quantRot T₁ T₂ T V)
          ((congrArg (VarCtx.insertBnd T) w₁eq).symm ▸ ψ)))
  termination_by WFF.numNodes φ
  decreasing_by
    all_goals first
      | (simp only [WFF.numNodes]; omega)
      | (rw [WFF.numNodes_mapCtx, WFF.numNodes_ctx_cast]
         simp only [WFF.numNodes]
         omega)

/-! ## Weakening by a user variable

The formula-level mirror of `Term.ctx_extU`, and the same five-way split on the added type at the
modal arms.  Two arms are new relative to `Term`, and both are cheap:

* **`all` / `ex`** — ⭐the payoff of nameless binders.  A user insert does not move `nextBnd`
  (`insertBnd_comm_insert`), so the binder slot is *literally the same* before and after; the arm
  is a recursion plus one context permutation.  v10 needed a freshness test and a collision branch
  that α-renamed the binder here.
* **`pair_elim`** — same fact, in its two-slot form.

The pair-typed arm of `box`/`dia` peels: weaken by the two COMPONENTS under fresh user names,
rename each onto its canonical slot, and re-pair with `WFF.pairElim`. -/

def WFF.ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) :
    WFF σ (VarCtx_insert ⟨u.toVar, T⟩ V hu) := by
  match φ with
  | .atom R  => exact .atom (Rel.ctx_extU u T hu R)
  | .top     => exact .top
  | .bot     => exact .bot
  | .and φ ψ => exact .and (WFF.ctx_extU u T hu φ) (WFF.ctx_extU u T hu ψ)
  | .or φ ψ  => exact .or (WFF.ctx_extU u T hu φ) (WFF.ctx_extU u T hu ψ)
  | .imp φ ψ => exact .imp (WFF.ctx_extU u T hu φ) (WFF.ctx_extU u T hu ψ)
  | .eq s t  => exact .eq (Term.ctx_extU u T hu s) (Term.ctx_extU u T hu t)
  | .all T' ψ =>
      have hu_bnd : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T' V) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T' hu
      exact .all T' (VarCtx.insertBnd_comm_insert ⟨u.toVar, T⟩ V hu rfl T' hu_bnd ▸
        WFF.ctx_extU u T hu_bnd ψ)
  | .ex T' ψ =>
      have hu_bnd : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T' V) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T' hu
      exact .ex T' (VarCtx.insertBnd_comm_insert ⟨u.toVar, T⟩ V hu rfl T' hu_bnd ▸
        WFF.ctx_extU u T hu_bnd ψ)
  | .box inner hsub hne =>
      rename_i V_inner
      have hu_inner : u.toVar ∉ VarCtx_to_VarSymbs V_inner := by
        intro h_in
        apply hu
        obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in
        exact Finset.mem_image.mpr ⟨⟨q.1, q.2.VTypeBox⟩,
          hsub (Finset.mem_image.mpr ⟨q, hq_in, rfl⟩), hq_eq⟩
      match h_T : T with
      | .VTypeBox U' =>
          subst h_T
          refine .box (WFF.ctx_extU u U' hu_inner inner) ?_ ?_
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
          subst h_T
          have hw1 : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar ∉ VarCtx_to_VarSymbs V :=
            UserSymb.fresh_not_mem _
          have hw2 : (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))).toVar
              ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd a V) := UserSymb.fresh_not_mem _
          exact WFF.pairElim a b u.toVar rfl hu rfl rfl
            (WFF.rename _ (VarCtx.insertBnd a V).nextBnd b hw2 (VarCtx.nextBnd_not_mem _)
              (WFF.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))) b hw2
                (WFF.rename _ V.nextBnd a hw1 (VarCtx.nextBnd_not_mem V)
                  (WFF.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) a hw1
                    (.box inner hsub hne)))))
      | .Var | .VTypeOne | .VTypeDia _ =>
          all_goals
            subst h_T
            refine .box inner (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
            intro p hp h_box
            rcases Finset.mem_insert.mp hp with rfl | hp_V
            · simp [VarType.isBox] at h_box
            · exact hne p hp_V h_box
  | .dia x hx inner hsub hne =>
      rename_i V_inner
      have hu_inner : u.toVar ∉ VarCtx_to_VarSymbs V_inner := by
        intro h_in
        apply hu
        obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in
        refine Finset.mem_image.mpr ⟨⟨q.1, q.2.VTypeBox⟩, hsub ?_, hq_eq⟩
        rw [VarCtx_dia_fst]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, hq_in, rfl⟩)
      have hu_ne_x : u.toVar ≠ x.1 := by
        intro h_eq
        apply hu
        refine Finset.mem_image.mpr ⟨⟨x.1, x.2.VTypeDia⟩, hsub ?_, h_eq.symm⟩
        rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
      have hu_outer : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert x V_inner hx) :=
        not_mem_VarSymbs_insert hu_ne_x hu_inner
      match h_T : T with
      | .VTypeBox U' =>
          subst h_T
          have hx_ext : x.1 ∉ VarCtx_to_VarSymbs
              (VarCtx_insert ⟨u.toVar, U'⟩ V_inner hu_inner) :=
            not_mem_VarSymbs_insert (Ne.symm hu_ne_x) hx
          have h_swap : VarCtx_insert ⟨u.toVar, U'⟩ (VarCtx_insert x V_inner hx) hu_outer
              = VarCtx_insert x (VarCtx_insert ⟨u.toVar, U'⟩ V_inner hu_inner) hx_ext :=
            VarCtx_insert_comm hu_outer hx_ext
          refine .dia x hx_ext (h_swap ▸ WFF.ctx_extU u U' hu_outer inner) ?_ ?_
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
          subst h_T
          have hw1 : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar ∉ VarCtx_to_VarSymbs V :=
            UserSymb.fresh_not_mem _
          have hw2 : (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))).toVar
              ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd a V) := UserSymb.fresh_not_mem _
          exact WFF.pairElim a b u.toVar rfl hu rfl rfl
            (WFF.rename _ (VarCtx.insertBnd a V).nextBnd b hw2 (VarCtx.nextBnd_not_mem _)
              (WFF.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))) b hw2
                (WFF.rename _ V.nextBnd a hw1 (VarCtx.nextBnd_not_mem V)
                  (WFF.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) a hw1
                    (.dia x hx inner hsub hne)))))
      | .Var | .VTypeOne | .VTypeDia _ =>
          all_goals
            subst h_T
            refine .dia x hx inner (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
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
      -- ⭐The slots do not move: a user insert leaves `nextBnd` alone.  Target the BODY's context
      -- so `body` is passed untouched (transporting it would break the `sizeOf` relation).
      have w₁eq' : VarCtx.insertBnd2 T₁ T₂ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe)
          = VarCtx_insert ⟨u.toVar, T⟩ pe_W₁ hu_W₁ := by
        rw [VarCtx.insertBnd2_comm_insert ⟨u.toVar, T⟩ pe_V hu_pe rfl T₁ T₂ hu_bnd2]
        apply VarCtx_ext
        change insert (⟨u.toVar, T⟩ : VarSymb × VarType) (VarCtx.insertBnd2 T₁ T₂ pe_V).1
             = insert (⟨u.toVar, T⟩ : VarSymb × VarType) pe_W₁.1
        rw [w₁eq]
      exact .pair_elim T₁ T₂ z hz' w₁eq'
        (VarCtx_insert_comm hz' (not_mem_VarSymbs_insert (Ne.symm hz_ne) hu_pe))
        (WFF.ctx_extU u T hu_W₁ body)
  termination_by (sizeOf T, sizeOf φ)

/-! ## `diaCount` invariance

The measure component that `substCore`'s modal-β arm turns on.  Same shape as the `Term` versions;
the quantifier arms carry a `mapCtx` and a cast, both of which `diaCount` sees through. -/

theorem WFF.diaCount_pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
    (T₁ T₂ : VarType) (z : VarSymb) (hzu : z.isUsr = true)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂)
    (φ : WFF σ W₁) :
    WFF.diaCount (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ) = WFF.diaCount φ := by
  match φ with
  | .atom R =>
      rw [WFF.pairElim]; simp only [WFF.diaCount]
      rw [Rel.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq R]
  | .top => rw [WFF.pairElim]; rfl
  | .bot => rw [WFF.pairElim]; rfl
  | .and φ ψ =>
      rw [WFF.pairElim]; simp only [WFF.diaCount]
      rw [WFF.diaCount_pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ,
          WFF.diaCount_pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ]
  | .or φ ψ =>
      rw [WFF.pairElim]; simp only [WFF.diaCount]
      rw [WFF.diaCount_pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ,
          WFF.diaCount_pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ]
  | .imp φ ψ =>
      rw [WFF.pairElim]; simp only [WFF.diaCount]
      rw [WFF.diaCount_pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ,
          WFF.diaCount_pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ]
  | .eq s t =>
      rw [WFF.pairElim]; simp only [WFF.diaCount]
      rw [Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq s,
          Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq t]
  | .box inner hsub hne => rw [WFF.pairElim]; rfl
  | .dia x hx inner hsub hne => rw [WFF.pairElim]; rfl
  | .pair_elim _ _ _ _ _ _ _ => rw [WFF.pairElim]; rfl
  | .all T ψ =>
      rw [WFF.pairElim]; simp only [WFF.diaCount]
      rw [WFF.diaCount_pairElim T₁ T₂ z hzu _ rfl _ _, WFF.diaCount_mapCtx,
          WFF.diaCount_ctx_cast]
  | .ex T ψ =>
      rw [WFF.pairElim]; simp only [WFF.diaCount]
      rw [WFF.diaCount_pairElim T₁ T₂ z hzu _ rfl _ _, WFF.diaCount_mapCtx,
          WFF.diaCount_ctx_cast]
  termination_by WFF.numNodes φ
  decreasing_by
    all_goals first
      | (simp only [WFF.numNodes]; omega)
      | (rw [WFF.numNodes_mapCtx, WFF.numNodes_ctx_cast]
         simp only [WFF.numNodes]
         omega)

theorem WFF.diaCount_ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) :
    WFF.diaCount (WFF.ctx_extU u T hu φ) = WFF.diaCount φ := by
  match φ with
  | .atom R =>
      rw [WFF.ctx_extU]; simp only [WFF.diaCount]; rw [Rel.diaCount_ctx_extU u T hu R]
  | .top => rw [WFF.ctx_extU]; rfl
  | .bot => rw [WFF.ctx_extU]; rfl
  | .and φ ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.diaCount]
      rw [WFF.diaCount_ctx_extU u T hu φ, WFF.diaCount_ctx_extU u T hu ψ]
  | .or φ ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.diaCount]
      rw [WFF.diaCount_ctx_extU u T hu φ, WFF.diaCount_ctx_extU u T hu ψ]
  | .imp φ ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.diaCount]
      rw [WFF.diaCount_ctx_extU u T hu φ, WFF.diaCount_ctx_extU u T hu ψ]
  | .eq s t =>
      rw [WFF.ctx_extU]; simp only [WFF.diaCount]
      rw [Term.diaCount_ctx_extU u T hu s, Term.diaCount_ctx_extU u T hu t]
  | .all T' ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.diaCount]
      rw [WFF.diaCount_ctx_cast, WFF.diaCount_ctx_extU u T _ ψ]
  | .ex T' ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.diaCount]
      rw [WFF.diaCount_ctx_cast, WFF.diaCount_ctx_extU u T _ ψ]
  | .box inner hsub hne =>
      match h_T : T with
      | .VTypeBox U' =>
          subst h_T
          rw [WFF.ctx_extU]; simp only [WFF.diaCount]
          rw [WFF.diaCount_ctx_extU u U' _ inner]
      | .VTypeProd a b =>
          subst h_T
          rw [WFF.ctx_extU, WFF.diaCount_pairElim, WFF.diaCount_rename,
              WFF.diaCount_ctx_extU _ b, WFF.diaCount_rename, WFF.diaCount_ctx_extU _ a]
      | .Var => subst h_T; rw [WFF.ctx_extU]; rfl
      | .VTypeOne => subst h_T; rw [WFF.ctx_extU]; rfl
      | .VTypeDia _ => subst h_T; rw [WFF.ctx_extU]; rfl
  | .dia x hx inner hsub hne =>
      match h_T : T with
      | .VTypeBox U' =>
          subst h_T
          rw [WFF.ctx_extU]; simp only [WFF.diaCount]
          rw [WFF.diaCount_ctx_cast, WFF.diaCount_ctx_extU u U' _ inner]
      | .VTypeProd a b =>
          subst h_T
          rw [WFF.ctx_extU, WFF.diaCount_pairElim, WFF.diaCount_rename,
              WFF.diaCount_ctx_extU _ b, WFF.diaCount_rename, WFF.diaCount_ctx_extU _ a]
      | .Var => subst h_T; rw [WFF.ctx_extU]; rfl
      | .VTypeOne => subst h_T; rw [WFF.ctx_extU]; rfl
      | .VTypeDia _ => subst h_T; rw [WFF.ctx_extU]; rfl
  | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
      rename_i pe_V pe_W₁
      subst w₂eq
      rw [WFF.ctx_extU]; simp only [WFF.diaCount]
      rw [WFF.diaCount_ctx_extU u T _ body]
  termination_by (sizeOf T, sizeOf φ)

theorem WFF.binderPairDepth_pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
    (T₁ T₂ : VarType) (z : VarSymb) (hzu : z.isUsr = true)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂)
    (φ : WFF σ W₁) :
    WFF.binderPairDepth (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ) = WFF.binderPairDepth φ := by
  match φ with
  | .atom R => rw [WFF.pairElim]; rfl
  | .top => rw [WFF.pairElim]; rfl
  | .bot => rw [WFF.pairElim]; rfl
  | .and φ ψ =>
      rw [WFF.pairElim]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ,
          WFF.binderPairDepth_pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ]
  | .or φ ψ =>
      rw [WFF.pairElim]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ,
          WFF.binderPairDepth_pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ]
  | .imp φ ψ =>
      rw [WFF.pairElim]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_pairElim T₁ T₂ z hzu hz w₁eq w₂eq φ,
          WFF.binderPairDepth_pairElim T₁ T₂ z hzu hz w₁eq w₂eq ψ]
  | .eq s t => rw [WFF.pairElim]; rfl
  | .box inner hsub hne => rw [WFF.pairElim]; rfl
  | .dia x hx inner hsub hne => rw [WFF.pairElim]; rfl
  | .pair_elim _ _ _ _ _ _ _ => rw [WFF.pairElim]; rfl
  | .all T ψ =>
      rw [WFF.pairElim]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_pairElim T₁ T₂ z hzu _ rfl _ _, WFF.binderPairDepth_mapCtx,
          WFF.binderPairDepth_ctx_cast]
  | .ex T ψ =>
      rw [WFF.pairElim]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_pairElim T₁ T₂ z hzu _ rfl _ _, WFF.binderPairDepth_mapCtx,
          WFF.binderPairDepth_ctx_cast]
  termination_by WFF.numNodes φ
  decreasing_by
    all_goals first
      | (simp only [WFF.numNodes]; omega)
      | (rw [WFF.numNodes_mapCtx, WFF.numNodes_ctx_cast]
         simp only [WFF.numNodes]
         omega)

theorem WFF.binderPairDepth_ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) :
    WFF.binderPairDepth (WFF.ctx_extU u T hu φ) = WFF.binderPairDepth φ := by
  match φ with
  | .atom R => rw [WFF.ctx_extU]; rfl
  | .top => rw [WFF.ctx_extU]; rfl
  | .bot => rw [WFF.ctx_extU]; rfl
  | .and φ ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_ctx_extU u T hu φ, WFF.binderPairDepth_ctx_extU u T hu ψ]
  | .or φ ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_ctx_extU u T hu φ, WFF.binderPairDepth_ctx_extU u T hu ψ]
  | .imp φ ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_ctx_extU u T hu φ, WFF.binderPairDepth_ctx_extU u T hu ψ]
  | .eq s t => rw [WFF.ctx_extU]; rfl
  | .all T' ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_extU u T _ ψ]
  | .ex T' ψ =>
      rw [WFF.ctx_extU]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_extU u T _ ψ]
  | .box inner hsub hne =>
      match h_T : T with
      | .VTypeBox U' =>
          subst h_T
          rw [WFF.ctx_extU]; simp only [WFF.binderPairDepth]
          rw [WFF.binderPairDepth_ctx_extU u U' _ inner]
      | .VTypeProd a b =>
          subst h_T
          rw [WFF.ctx_extU, WFF.binderPairDepth_pairElim, WFF.binderPairDepth_rename,
              WFF.binderPairDepth_ctx_extU _ b, WFF.binderPairDepth_rename,
              WFF.binderPairDepth_ctx_extU _ a]
      | .Var => subst h_T; rw [WFF.ctx_extU]; rfl
      | .VTypeOne => subst h_T; rw [WFF.ctx_extU]; rfl
      | .VTypeDia _ => subst h_T; rw [WFF.ctx_extU]; rfl
  | .dia x hx inner hsub hne =>
      match h_T : T with
      | .VTypeBox U' =>
          subst h_T
          rw [WFF.ctx_extU]; simp only [WFF.binderPairDepth]
          rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_extU u U' _ inner]
      | .VTypeProd a b =>
          subst h_T
          rw [WFF.ctx_extU, WFF.binderPairDepth_pairElim, WFF.binderPairDepth_rename,
              WFF.binderPairDepth_ctx_extU _ b, WFF.binderPairDepth_rename,
              WFF.binderPairDepth_ctx_extU _ a]
      | .Var => subst h_T; rw [WFF.ctx_extU]; rfl
      | .VTypeOne => subst h_T; rw [WFF.ctx_extU]; rfl
      | .VTypeDia _ => subst h_T; rw [WFF.ctx_extU]; rfl
  | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
      rename_i pe_V pe_W₁
      subst w₂eq
      rw [WFF.ctx_extU]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_ctx_extU u T _ body]
  termination_by (sizeOf T, sizeOf φ)
