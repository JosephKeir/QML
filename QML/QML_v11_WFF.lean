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
  | eq   : Term σ V S → Term σ V S → WFF σ V
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
def WFF.rename' {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
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

theorem WFF.diaCount_rename' {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨old, T⟩ V hold)) :
    WFF.diaCount (WFF.rename' old new T hold hnew φ) = WFF.diaCount φ :=
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
