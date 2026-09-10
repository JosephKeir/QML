import QML.QML_v11_WFF

/-!
# QML v11 — the `mapCtx` algebra

`mapCtx` is the single traversal that renaming, shifting and lifting all reduce to, but the project
has never had its ALGEBRA: that composing two maps whose underlying functions cancel gives back the
original term.  That round-trip is what the quantifier cases of Leibniz need.

⭐**Why they need it.**  `Proof.all_intro`'s premise lives at a USER-named eigenvariable and its
conclusion is `all T (rename u ↦ slot φ)`.  To conclude `all T ψ` for a GIVEN slot-indexed `ψ` —
which is what Leibniz hands you — you must exhibit `ψ` as such a rename, i.e. show that
`rename u↦slot` is surjective.  Taking `φ := rename slot↦u ψ` reduces that to the ROUND TRIP.
This is the `∀`-analogue of what `WFF.bindPair` does for `pair_elim`: go under the binder on a
user name, work there, then rebind — and rebinding must undo the unbinding.

⚠️**The side condition to watch.**  The user name chosen when going under the binder must differ
from every variable already in play — in particular from a weakening variable introduced later.
It is `hid` below that carries this: the composite must be the identity on ALL of `V`'s symbols,
which fails exactly when the two names collide.

⚠️**Why it is cast-heavy.**  `mapCtx`'s `boxterm`/`diaterm` arms rebuild the inner context as
`m.imageCtx V_inner`, and `m₂.imageCtx (m₁.imageCtx U) = U` holds only PROPOSITIONALLY (it is
`Finset.image_image` plus `image_id`).  So the statement transports along a context equality and
every constructor needs a congruence lemma to push that transport inwards.
-/

/-! ## `imageCtx` is functorial -/

/-- Two maps whose underlying functions cancel on `U` leave `U`'s image untouched. -/
theorem CtxBij.imageCtx_roundtrip {V V' V'' : VarCtx} (m₁ : CtxBij V V') (m₂ : CtxBij V' V'')
    (U : VarCtx) (h₁ : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V)
    (h₂ : ∀ v ∈ VarCtx_to_VarSymbs (m₁.imageCtx U h₁), v ∈ VarCtx_to_VarSymbs V')
    (hid : ∀ v ∈ VarCtx_to_VarSymbs U, m₂.toCtxMap.f (m₁.toCtxMap.f v) = v) :
    m₂.imageCtx (m₁.imageCtx U h₁) h₂ = U := by
  refine VarCtx_ext _ _ ?_
  rw [CtxBij.imageCtx_fst, CtxBij.imageCtx_fst, Finset.image_image]
  have heq : Set.EqOn
      ((fun p => (⟨m₂.toCtxMap.f p.1, p.2⟩ : VarSymb × VarType))
        ∘ (fun p => (⟨m₁.toCtxMap.f p.1, p.2⟩ : VarSymb × VarType))) id ↑U.1 := by
    intro p hp
    have hfix : m₂.toCtxMap.f (m₁.toCtxMap.f p.1) = p.1 :=
      hid p.1 (Finset.mem_image.mpr ⟨p, Finset.mem_coe.mp hp, rfl⟩)
    simp only [Function.comp_apply, id_eq, hfix]
  rw [Finset.image_congr heq, Finset.image_id]

/-! ## Constructor congruences

All are `subst`-then-`rfl`: they only push a context transport inwards. -/

theorem Term.cast_var {σ : Signature} {A B : VarCtx} (h : A = B)
    (e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ A.1}) :
    (h ▸ (Term.var e : Term σ A .Var)) = Term.var (h ▸ e) := by subst h; rfl

theorem cast_subtype_val {A B : VarCtx} (h : A = B)
    (e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ A.1}) :
    ((h ▸ e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ B.1}) : VarSymb)
      = (e : VarSymb) := by subst h; rfl

theorem Term.cast_func {σ : Signature} {A B : VarCtx} (h : A = B)
    (f : Func σ A 0) : (h ▸ (Term.func f : Term σ A .Var)) = Term.func (h ▸ f) := by
  subst h; rfl

theorem Term.cast_unit {σ : Signature} {A B : VarCtx} (h : A = B) :
    (h ▸ (Term.unit : Term σ A .VTypeOne)) = Term.unit := by subst h; rfl

theorem Term.cast_pair {σ : Signature} {A B : VarCtx} {S T : VarType} (h : A = B)
    (a : Term σ A S) (b : Term σ A T) :
    (h ▸ (Term.pair a b : Term σ A (S.VTypeProd T))) = Term.pair (h ▸ a) (h ▸ b) := by
  subst h; rfl

/-- Transporting the AMBIENT context of a `boxterm`. -/
theorem Term.cast_boxterm {σ : Signature} {W W' V_inner : VarCtx} {S_inner : VarType}
    (h : W = W') (tt : Term σ V_inner S_inner) (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    (h ▸ (Term.boxterm tt hsub hne : Term σ W S_inner.VTypeBox))
      = Term.boxterm tt (h ▸ hsub) (h ▸ hne) := by subst h; rfl

/-- Transporting the INNER context of a `boxterm` — the direction `mapCtx`'s round trip needs,
    since `imageCtx` only returns the inner context propositionally. -/
theorem Term.boxterm_congr {σ : Signature} {W V_inner V_inner' : VarCtx} {S_inner : VarType}
    (hI : V_inner = V_inner') (tt : Term σ V_inner S_inner)
    (hsub : (VarCtx_box V_inner').1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner').1) :
    (Term.boxterm (hI ▸ tt) hsub hne : Term σ W S_inner.VTypeBox)
      = Term.boxterm tt (hI ▸ hsub) (hI ▸ hne) := by subst hI; rfl

theorem Term.cast_diaterm {σ : Signature} {W W' V_inner : VarCtx} {S_inner : VarType}
    (h : W = W') (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) S_inner)
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    (h ▸ (Term.diaterm xv hxv tt hsub hne : Term σ W S_inner.VTypeDia))
      = Term.diaterm xv hxv tt (h ▸ hsub) (h ▸ hne) := by subst h; rfl

theorem Func.cast_F {σ : Signature} {A B : VarCtx} {N : ℕ} (h : A = B)
    (hr : {f // σ.funcArity f = N}) :
    (h ▸ (Func.F hr : Func σ A N)) = Func.F hr := by subst h; rfl

theorem Func.cast_eval {σ : Signature} {A B : VarCtx} {N : ℕ} (h : A = B)
    (g : Func σ A (N + 1)) (t : Term σ A .Var) :
    (h ▸ (Func.eval g t : Func σ A N)) = Func.eval (h ▸ g) (h ▸ t) := by subst h; rfl

/-! ## `mapCtx` computation rules

⚠️Needed rather than `unfold`-in-place: `conv => unfold Term.mapCtx` twice over a NESTED
`mapCtx m₂ (mapCtx m₁ t)` unfolds the OUTER call at the leaves, where its scrutinee is not yet a
constructor, and strands a stuck `match`.  Rewriting with these fires only where a constructor is
actually present. -/

theorem Term.mapCtx_var {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {v : VarSymb}
    (hv : (⟨v, VarType.Var⟩ : VarSymb × VarType) ∈ V.1)
    (hv' : (⟨m.toCtxMap.f v, VarType.Var⟩ : VarSymb × VarType) ∈ V'.1) :
    Term.mapCtx m (Term.var ⟨v, hv⟩ : Term σ V .Var) = Term.var ⟨m.toCtxMap.f v, hv'⟩ := by
  conv_lhs => unfold Term.mapCtx

theorem Term.mapCtx_func {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (fn : Func σ V 0) :
    Term.mapCtx m (Term.func fn) = Term.func (Func.mapCtx m fn) := by
  conv_lhs => unfold Term.mapCtx

theorem Term.mapCtx_unit {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') :
    Term.mapCtx m (Term.unit : Term σ V .VTypeOne) = Term.unit := by
  conv_lhs => unfold Term.mapCtx

theorem Term.mapCtx_pair {σ : Signature} {V V' : VarCtx} {A B : VarType} (m : CtxBij V V')
    (a : Term σ V A) (b : Term σ V B) :
    Term.mapCtx m (Term.pair a b) = Term.pair (Term.mapCtx m a) (Term.mapCtx m b) := by
  conv_lhs => unfold Term.mapCtx

theorem Func.mapCtx_F {σ : Signature} {V V' : VarCtx} {N : ℕ} (m : CtxBij V V')
    (hr : {f // σ.funcArity f = N}) :
    Func.mapCtx m (Func.F hr : Func σ V N) = Func.F hr := by
  conv_lhs => unfold Func.mapCtx

theorem Func.mapCtx_eval {σ : Signature} {V V' : VarCtx} {N : ℕ} (m : CtxBij V V')
    (g : Func σ V (N + 1)) (t : Term σ V .Var) :
    Func.mapCtx m (Func.eval g t) = Func.eval (Func.mapCtx m g) (Term.mapCtx m t) := by
  conv_lhs => unfold Func.mapCtx

/-- The `boxterm` computation rule.  The inner context becomes `m.imageCtx V_inner hU`; the
    subset/no-extras arguments are `Prop`s, so the caller supplies any proofs. -/
theorem Term.mapCtx_boxterm {σ : Signature} {V V' V_inner : VarCtx} {S : VarType}
    (m : CtxBij V V') (tt : Term σ V_inner S)
    (hsub : (VarCtx_box V_inner).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V)
    (hsub' : (VarCtx_box (m.imageCtx V_inner hU)).1 ⊆ V'.1)
    (hne' : ∀ p ∈ V'.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box (m.imageCtx V_inner hU)).1) :
    Term.mapCtx m (Term.boxterm tt hsub hne)
      = Term.boxterm (Term.mapCtx (m.toImage V_inner hU) tt) hsub' hne' := by
  conv_lhs => unfold Term.mapCtx

/-- Rebuild a `boxterm` across a context equality on the INNER context, given that the inner terms
    correspond.  This is the shape the round trip needs: `subst` the context equality, then the
    term equality, and the side conditions are `Prop`s. -/
theorem Term.boxterm_congr' {σ : Signature} {W V_inner V_inner' : VarCtx} {S : VarType}
    (hI : V_inner' = V_inner) (X : Term σ V_inner' S) (tt : Term σ V_inner S)
    (hX : hI ▸ X = tt)
    (P : (VarCtx_box V_inner').1 ⊆ W.1)
    (Q : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner').1)
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    (Term.boxterm X P Q : Term σ W S.VTypeBox) = Term.boxterm tt hsub hne := by
  subst hI
  subst hX
  rfl

/-- The image of a box-subset is a box-subset of the image — the side condition `mapCtx`'s
    `boxterm` arm builds, extracted so the round trip can name it. -/
theorem CtxBij.box_sub_image {V V' V_inner : VarCtx} (m : CtxBij V V')
    (hsub : (VarCtx_box V_inner).1 ⊆ V.1)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V) :
    (VarCtx_box (m.imageCtx V_inner hU)).1 ⊆ V'.1 := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
  exact m.toCtxMap.maps ⟨r.1, r.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨r, hr, rfl⟩))

/-- The no-box-extras side condition for the image — the other proof `mapCtx`'s `boxterm` arm
    builds.  ⭐`onto` is what this needs: every box-typed entry of `V'` comes from one of `V`,
    which `hne` places in the source inner context, hence in its image. -/
theorem CtxBij.box_extras_image {V V' V_inner : VarCtx} (m : CtxBij V V')
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V) :
    ∀ p ∈ V'.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box (m.imageCtx V_inner hU)).1 := by
  intro p hp hbox
  obtain ⟨q, hq, rfl⟩ := m.onto p hp
  have hqbox : VarType.isBox q.2 = true := hbox
  rcases Finset.mem_image.mp (hne q hq hqbox) with ⟨r, hr, hreq⟩
  refine Finset.mem_image.mpr
    ⟨⟨m.toCtxMap.f r.1, r.2⟩, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
  simp only
  obtain ⟨h1, h2⟩ := Prod.mk.inj hreq
  rw [h1, h2]

/-! ### The `diaterm` side conditions

The `◇`-witness is a PROMOTED FREE variable, so it moves with the map (`⟨m.f x.1, x.2⟩`) while the
interior is imaged.  These four are the proofs `mapCtx`'s `diaterm` arm builds inline. -/

theorem VarCtx.dia_witness_mem {V V_inner : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V_inner} (hsub : (VarCtx_dia x V_inner hx).1 ⊆ V.1) :
    (⟨x.1, x.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
  apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _

theorem VarCtx.symbs_of_dia_sub {V V_inner : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V_inner} (hsub : (VarCtx_dia x V_inner hx).1 ⊆ V.1) :
    ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  refine Finset.mem_image.mpr ⟨⟨p.1, p.2.VTypeBox⟩, hsub ?_, rfl⟩
  rw [VarCtx_dia_fst]
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem CtxBij.notMem_imageCtx {V V' U : VarCtx} (m : CtxBij V V')
    (hU : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V)
    {y : VarSymb} (hyV : y ∈ VarCtx_to_VarSymbs V) (hy : y ∉ VarCtx_to_VarSymbs U) :
    m.toCtxMap.f y ∉ VarCtx_to_VarSymbs (m.imageCtx U hU) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨p, hp, hpeq⟩
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  apply hy
  have hfq : m.toCtxMap.f q.1 = m.toCtxMap.f y := hpeq
  have hq1 : q.1 = y :=
    m.toCtxMap.inj q.1 (hU _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)) y hyV hfq
  exact hq1 ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩

theorem CtxBij.dia_sub_image {V V' V_inner : VarCtx} (m : CtxBij V V') {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V_inner}
    (hsub : (VarCtx_dia x V_inner hx).1 ⊆ V.1)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V)
    (hx' : m.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m.imageCtx V_inner hU)) :
    (VarCtx_dia (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType) (m.imageCtx V_inner hU) hx').1
      ⊆ V'.1 := by
  intro p hp
  rw [VarCtx_dia_fst] at hp
  rcases Finset.mem_insert.mp hp with rfl | hbox
  · exact m.toCtxMap.maps ⟨x.1, x.2.VTypeDia⟩ (VarCtx.dia_witness_mem hsub)
  · rcases Finset.mem_image.mp hbox with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
    refine m.toCtxMap.maps ⟨r.1, r.2.VTypeBox⟩ (hsub ?_)
    rw [VarCtx_dia_fst]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

theorem CtxBij.dia_extras_image {V V' V_inner : VarCtx} (m : CtxBij V V') {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V_inner}
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V_inner hx).1)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V)
    (hx' : m.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m.imageCtx V_inner hU)) :
    ∀ p ∈ V'.1, VarType.isBox p.2 = true
      → p ∈ (VarCtx_dia (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType)
              (m.imageCtx V_inner hU) hx').1 := by
  intro p hp hbox
  obtain ⟨q, hq, rfl⟩ := m.onto p hp
  have hqin := hne q hq hbox
  rw [VarCtx_dia_fst] at hqin ⊢
  rcases Finset.mem_insert.mp hqin with rfl | hqbox
  · exact Finset.mem_insert_self _ _
  · rcases Finset.mem_image.mp hqbox with ⟨r, hr, hreq⟩
    refine Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨⟨m.toCtxMap.f r.1, r.2⟩, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩)
    simp only
    obtain ⟨h1, h2⟩ := Prod.mk.inj hreq
    rw [h1, h2]

theorem Term.mapCtx_diaterm {σ : Signature} {V V' V_inner : VarCtx} {S : VarType}
    (m : CtxBij V V') {x : VarSymb × VarType} (hx : x.1 ∉ VarCtx_to_VarSymbs V_inner)
    (inner : Term σ (VarCtx_insert x V_inner hx) S)
    (hsub : (VarCtx_dia x V_inner hx).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V_inner hx).1)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V)
    (hxV : x.1 ∈ VarCtx_to_VarSymbs V)
    (hx' : m.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m.imageCtx V_inner hU))
    (hsub' : (VarCtx_dia (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType)
                (m.imageCtx V_inner hU) hx').1 ⊆ V'.1)
    (hne' : ∀ p ∈ V'.1, VarType.isBox p.2 = true
              → p ∈ (VarCtx_dia (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType)
                      (m.imageCtx V_inner hU) hx').1) :
    Term.mapCtx m (Term.diaterm x hx inner hsub hne)
      = Term.diaterm ⟨m.toCtxMap.f x.1, x.2⟩ hx'
          (Term.mapCtx (m.extendPoint V_inner hU x hxV hx hx') inner) hsub' hne' := by
  conv_lhs => unfold Term.mapCtx

/-- The `diaterm` analogue of `Term.boxterm_congr'`: rebuild across an equality of the WITNESS and
    of the inner context together. -/
theorem Term.diaterm_congr' {σ : Signature} {W V_inner V_inner' : VarCtx} {S : VarType}
    {x x' : VarSymb × VarType}
    {hx' : x'.1 ∉ VarCtx_to_VarSymbs V_inner'} {hx : x.1 ∉ VarCtx_to_VarSymbs V_inner}
    (hxx : x' = x) (hI : V_inner' = V_inner)
    (X : Term σ (VarCtx_insert x' V_inner' hx') S) (tt : Term σ (VarCtx_insert x V_inner hx) S)
    (hCtx : VarCtx_insert x' V_inner' hx' = VarCtx_insert x V_inner hx)
    (hX : hCtx ▸ X = tt)
    (P : (VarCtx_dia x' V_inner' hx').1 ⊆ W.1)
    (Q : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x' V_inner' hx').1)
    (hsub : (VarCtx_dia x V_inner hx).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V_inner hx).1) :
    (Term.diaterm x' hx' X P Q : Term σ W S.VTypeDia) = Term.diaterm x hx tt hsub hne := by
  subst hxx
  subst hI
  subst hX
  rfl

/-! ### The `pair_elim` side conditions

⚠️This arm is the awkward one.  `boxterm`/`diaterm` recurse along `toImage`/`extendPoint`, whose
underlying function is `m.f` UNCHANGED, so the round-trip hypothesis transfers verbatim.
`pair_elim` recurses along `((restrictInsert hz m).extendBnd T₁).extendBnd T₂`, and
`CtxMap.extendBnd`'s function is `VarSymb.update m.f V.nextBnd V'.nextBnd` — so the composite is a
chain of four `update`s.  `CtxBij.extendBnd_id` handles one layer at a time. -/

@[simp] theorem CtxBij.extendBnd_f {V V' : VarCtx} (m : CtxBij V V') (T : VarType) :
    (m.extendBnd T).toCtxMap.f
      = VarSymb.update m.toCtxMap.f V.nextBnd V'.nextBnd := rfl

@[simp] theorem CtxBij.restrictInsert_f {pe_V V' : VarCtx} {z : VarSymb} {T : VarType}
    (hz : z ∉ VarCtx_to_VarSymbs pe_V) (m : CtxBij (VarCtx_insert ⟨z, T⟩ pe_V hz) V') :
    (CtxBij.restrictInsert hz m).toCtxMap.f = m.toCtxMap.f := rfl

theorem CtxBij.cast_f {A B V' : VarCtx} (h : A = B) (m : CtxBij A V') :
    (h ▸ m : CtxBij B V').toCtxMap.f = m.toCtxMap.f := by subst h; rfl

/-- ⭐One `extendBnd` layer of the round trip.  The slot goes `A.nextBnd ↦ B.nextBnd ↦ C.nextBnd`,
    and `hC : C = A` closes the loop; every other symbol dodges both `update`s because a context's
    `nextBnd` is never one of its own symbols. -/
theorem CtxBij.extendBnd_id {A B C : VarCtx} (m₁ : CtxBij A B) (m₂ : CtxBij B C) (hC : C = A)
    (hid : ∀ v ∈ VarCtx_to_VarSymbs A, m₂.toCtxMap.f (m₁.toCtxMap.f v) = v) (T : VarType) :
    ∀ v ∈ VarCtx_to_VarSymbs (VarCtx.insertBnd T A),
      (m₂.extendBnd T).toCtxMap.f ((m₁.extendBnd T).toCtxMap.f v) = v := by
  intro v hv
  rw [VarCtx.symbs_insertBnd] at hv
  rcases Finset.mem_insert.mp hv with rfl | hv'
  · rw [CtxBij.extendBnd_f, CtxBij.extendBnd_f, VarSymb.update_self, VarSymb.update_self, hC]
  · have h1 : v ≠ A.nextBnd := fun h => VarCtx.nextBnd_not_mem A (h ▸ hv')
    have hmB : m₁.toCtxMap.f v ∈ VarCtx_to_VarSymbs B := by
      rcases Finset.mem_image.mp hv' with ⟨p, hp, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨m₁.toCtxMap.f p.1, p.2⟩, m₁.toCtxMap.maps p hp, rfl⟩
    have h2 : m₁.toCtxMap.f v ≠ B.nextBnd := fun h => VarCtx.nextBnd_not_mem B (h ▸ hmB)
    rw [CtxBij.extendBnd_f, CtxBij.extendBnd_f, VarSymb.update_of_ne _ h1,
        VarSymb.update_of_ne _ h2]
    exact hid v hv'

theorem Term.cast_pair_elim {σ : Signature} {pe_V W₁ W₂ W₂' : VarCtx} {T₁ T₂ S : VarType}
    {z : VarSymb} (h : W₂ = W₂') (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ pe_V = W₁)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂) (body : Term σ W₁ S) :
    (h ▸ (Term.pair_elim T₁ T₂ z hz w₁eq w₂eq body : Term σ W₂ S))
      = Term.pair_elim T₁ T₂ z hz w₁eq (w₂eq.trans h) body := by subst h; rfl

/-- Rebuild a `pair_elim` across an equality of the destructured variable, of the base context and
    of the body's context. -/
theorem Term.pair_elim_congr' {σ : Signature} {pe_V pe_V' W₁ W₁' W₂ : VarCtx}
    {T₁ T₂ S : VarType} {z z' : VarSymb}
    {hz' : z' ∉ VarCtx_to_VarSymbs pe_V'} {hz : z ∉ VarCtx_to_VarSymbs pe_V}
    (hzz : z' = z) (hB : pe_V' = pe_V) (hW : W₁' = W₁)
    (w₁eq' : VarCtx.insertBnd2 T₁ T₂ pe_V' = W₁')
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ pe_V = W₁)
    (w₂eq' : VarCtx_insert ⟨z', T₁.VTypeProd T₂⟩ pe_V' hz' = W₂)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂)
    (X : Term σ W₁' S) (body : Term σ W₁ S) (hX : hW ▸ X = body) :
    (Term.pair_elim T₁ T₂ z' hz' w₁eq' w₂eq' X : Term σ W₂ S)
      = Term.pair_elim T₁ T₂ z hz w₁eq w₂eq body := by
  subst hzz
  subst hB
  subst hW
  subst hX
  rfl

/-- Move a bijection across an equality of its SOURCE by rebuilding it, not by transporting it.
    ⚠️This matters: `h ▸ m` makes `(h ▸ m).f` opaque until `h` is substituted, and in the
    `pair_elim` arm `h`'s left side mentions the very context being substituted (through
    `VarCtx_erase V' …`), so `subst` is unavailable.  Rebuilding keeps `f` DEFINITIONALLY `m.f`. -/
def CtxBij.ofEq {A B V' : VarCtx} (h : A = B) (m : CtxBij B V') : CtxBij A V' where
  f := m.toCtxMap.f
  inj := by subst h; exact m.toCtxMap.inj
  maps := by subst h; exact m.toCtxMap.maps
  onto := by subst h; exact m.onto

@[simp] theorem CtxBij.ofEq_f {A B V' : VarCtx} (h : A = B) (m : CtxBij B V') :
    (CtxBij.ofEq h m).toCtxMap.f = m.toCtxMap.f := rfl

theorem CtxBij.cast_ofEq {A B V' : VarCtx} (h : A = B) (m : CtxBij B V') :
    h ▸ (CtxBij.ofEq h m) = m := by subst h; rfl

/-- Present a `pair_elim` whose output-context equation is `w₂eq` as a TRANSPORT of the `rfl`
    form, so the `rfl`-form computation rule applies. -/
theorem Term.pair_elim_as_cast {σ : Signature} {pe_V W₂ : VarCtx} {T₁ T₂ S : VarType}
    {z : VarSymb} (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (X : Term σ (VarCtx.insertBnd2 T₁ T₂ pe_V) S)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂) :
    (Term.pair_elim T₁ T₂ z hz rfl w₂eq X : Term σ W₂ S)
      = w₂eq ▸ (Term.pair_elim T₁ T₂ z hz rfl rfl X) := by subst w₂eq; rfl

/-- Moving a context transport past `mapCtx`: transport the MAP instead of the term.  (Same
    principle as `mapCtx`'s own `pair_elim` arm, which transports `w₁eq` onto the map so the body
    is passed untouched.) -/
theorem Term.mapCtx_cast {σ : Signature} {A B V' : VarCtx} {S : VarType} (h : A = B)
    (m : CtxBij B V') (m' : CtxBij A V') (hm : h ▸ m' = m) (t : Term σ A S) :
    Term.mapCtx m (h ▸ t) = Term.mapCtx m' t := by
  subst h; subst hm; rfl

/-- The `pair_elim` computation rule, in the `rfl` form the definition itself produces.  The
    general `w₁eq`/`w₂eq` case is reached by `subst`ing them at the call site (they equate a
    context to a VARIABLE, so `subst` applies). -/
theorem Term.mapCtx_pair_elim {σ : Signature} {pe_V V' : VarCtx} {T₁ T₂ S : VarType}
    {z : VarSymb} (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (body : Term σ (VarCtx.insertBnd2 T₁ T₂ pe_V) S)
    (m : CtxBij (VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz) V')
    (hz' : m.toCtxMap.f z ∉ VarCtx_to_VarSymbs
             (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩))
    (w₂eq' : VarCtx_insert ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩
               (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) hz' = V') :
    Term.mapCtx m (Term.pair_elim T₁ T₂ z hz rfl rfl body)
      = Term.pair_elim T₁ T₂ (m.toCtxMap.f z) hz' rfl w₂eq'
          (Term.mapCtx (((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂) body) := by
  conv_lhs => unfold Term.mapCtx

/-! ## The round trip -/

mutual
theorem Term.mapCtx_roundtrip {σ : Signature} :
    ∀ (V V' V'' : VarCtx) (m₁ : CtxBij V V') (m₂ : CtxBij V' V'') (hVV : V'' = V)
      (_hid : ∀ v ∈ VarCtx_to_VarSymbs V, m₂.toCtxMap.f (m₁.toCtxMap.f v) = v)
      (S : VarType) (t : Term σ V S),
      hVV ▸ (Term.mapCtx m₂ (Term.mapCtx m₁ t)) = t
  | V, _, _, m₁, m₂, hVV, hid, _, .var ⟨v, hv⟩ => by
      have hvs : v ∈ VarCtx_to_VarSymbs V := Finset.mem_image.mpr ⟨_, hv, rfl⟩
      rw [Term.mapCtx_var (hv' := m₁.toCtxMap.maps _ hv),
          Term.mapCtx_var (hv' := m₂.toCtxMap.maps _ (m₁.toCtxMap.maps _ hv)),
          Term.cast_var]
      congr 1
      apply Subtype.ext
      rw [cast_subtype_val]
      exact hid v hvs
  | V, V', V'', m₁, m₂, hVV, hid, _, .func fn => by
      rw [Term.mapCtx_func, Term.mapCtx_func, Term.cast_func,
          Func.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid _ fn]
  | _, _, _, m₁, m₂, hVV, _, _, .unit => by
      rw [Term.mapCtx_unit, Term.mapCtx_unit, Term.cast_unit]
  | V, V', V'', m₁, m₂, hVV, hid, _, .pair a b => by
      rw [Term.mapCtx_pair, Term.mapCtx_pair, Term.cast_pair,
          Term.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid _ a,
          Term.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid _ b]
  | V, V', V'', m₁, m₂, hVV, hid, _, .boxterm tt hsub hne => by
      rename_i V_inner _
      have hU₁ : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_box_sub hsub
      have hsub₁ : (VarCtx_box (m₁.imageCtx V_inner hU₁)).1 ⊆ V'.1 :=
        CtxBij.box_sub_image m₁ hsub hU₁
      have hne₁ : ∀ p ∈ V'.1, VarType.isBox p.2 = true
          → p ∈ (VarCtx_box (m₁.imageCtx V_inner hU₁)).1 :=
        CtxBij.box_extras_image m₁ hne hU₁
      have hU₂ : ∀ v ∈ VarCtx_to_VarSymbs (m₁.imageCtx V_inner hU₁),
          v ∈ VarCtx_to_VarSymbs V' := VarCtx.symbs_of_box_sub hsub₁
      have hid' : ∀ v ∈ VarCtx_to_VarSymbs V_inner,
          m₂.toCtxMap.f (m₁.toCtxMap.f v) = v := fun v hv => hid v (hU₁ v hv)
      have hI : m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂ = V_inner :=
        CtxBij.imageCtx_roundtrip m₁ m₂ V_inner hU₁ hU₂ hid'
      have hIH := Term.mapCtx_roundtrip V_inner (m₁.imageCtx V_inner hU₁)
        (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂)
        (m₁.toImage V_inner hU₁) (m₂.toImage (m₁.imageCtx V_inner hU₁) hU₂) hI hid' _ tt
      rw [Term.mapCtx_boxterm m₁ tt hsub hne hU₁ hsub₁ hne₁,
          Term.mapCtx_boxterm m₂ _ hsub₁ hne₁ hU₂
            (CtxBij.box_sub_image m₂ hsub₁ hU₂) (CtxBij.box_extras_image m₂ hne₁ hU₂),
          Term.cast_boxterm]
      exact Term.boxterm_congr' hI _ tt hIH _ _ _ _
  | V, V', V'', m₁, m₂, hVV, hid, _, .diaterm x hx tt hsub hne => by
      rename_i V_inner _
      have hxV : x.1 ∈ VarCtx_to_VarSymbs V :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub, rfl⟩
      have hU₁ : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_dia_sub hsub
      have hx'₁ : m₁.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m₁.imageCtx V_inner hU₁) :=
        CtxBij.notMem_imageCtx m₁ hU₁ hxV hx
      have hsub₁ := CtxBij.dia_sub_image m₁ hsub hU₁ hx'₁
      have hne₁ := CtxBij.dia_extras_image m₁ hne hU₁ hx'₁
      have hxV' : m₁.toCtxMap.f x.1 ∈ VarCtx_to_VarSymbs V' :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub₁, rfl⟩
      have hU₂ : ∀ v ∈ VarCtx_to_VarSymbs (m₁.imageCtx V_inner hU₁),
          v ∈ VarCtx_to_VarSymbs V' := VarCtx.symbs_of_dia_sub hsub₁
      have hx'₂ := CtxBij.notMem_imageCtx m₂ hU₂ hxV' hx'₁
      have hsub₂ := CtxBij.dia_sub_image m₂ hsub₁ hU₂ hx'₂
      have hne₂ := CtxBij.dia_extras_image m₂ hne₁ hU₂ hx'₂
      have hxeq : m₂.toCtxMap.f (m₁.toCtxMap.f x.1) = x.1 := hid x.1 hxV
      have hI : m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂ = V_inner :=
        CtxBij.imageCtx_roundtrip m₁ m₂ V_inner hU₁ hU₂ (fun v hv => hid v (hU₁ v hv))
      have hxx : (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType) = x := by
        rw [hxeq]
      have hCtx : VarCtx_insert
            (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType)
            (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂) hx'₂
          = VarCtx_insert x V_inner hx := by
        refine VarCtx_ext _ _ ?_
        change insert (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType)
              (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂).1
            = insert x V_inner.1
        rw [hxx, hI]
      have hid'' : ∀ v ∈ VarCtx_to_VarSymbs (VarCtx_insert x V_inner hx),
          m₂.toCtxMap.f (m₁.toCtxMap.f v) = v := by
        intro v hv
        rw [VarCtx_to_VarSymbs_insert] at hv
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact hxeq
        · exact hid v (hU₁ v hv')
      have hIH := Term.mapCtx_roundtrip _ _ _
        (m₁.extendPoint V_inner hU₁ x hxV hx hx'₁)
        (m₂.extendPoint (m₁.imageCtx V_inner hU₁) hU₂
          (⟨m₁.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType) hxV' hx'₁ hx'₂)
        hCtx hid'' _ tt
      rw [Term.mapCtx_diaterm m₁ hx tt hsub hne hU₁ hxV hx'₁ hsub₁ hne₁,
          Term.mapCtx_diaterm m₂ hx'₁ _ hsub₁ hne₁ hU₂ hxV' hx'₂ hsub₂ hne₂,
          Term.cast_diaterm]
      exact Term.diaterm_congr' hxx hI _ tt hCtx hIH _ _ _ _
  -- ⭐The hard arm.  Unlike `boxterm`/`diaterm`, whose maps are `toImage`/`extendPoint` (both
  -- carrying `m.f` UNCHANGED, so `hid` transfers verbatim), the body map here is
  -- `((restrictInsert hz m).extendBnd T₁).extendBnd T₂`, and `CtxMap.extendBnd`'s function is
  -- `VarSymb.update m.f V.nextBnd V'.nextBnd`.  The composite is a chain of four `update`s;
  -- `CtxBij.extendBnd_id` peels one layer at a time against the base equation `hB`, which is
  -- `Finset.erase_insert` once `hzz` has brought the destructured variable back to `z`.
  -- The second map cannot be reached by transport (`VarCtx_erase V' …` blocks `subst` on `V'`),
  -- so it is REBUILT at the insert form with `CtxBij.ofEq`.
  | V, V', V'', m₁, m₂, hVV, hid, _, .pair_elim T₁ T₂ z hz w₁eq w₂eq body => by
      rename_i pe_V pe_W₁
      -- ⚠️Take the induction hypothesis BEFORE any `subst`, generalized over the maps: `subst`
      -- re-binds `body`, and the termination checker then cannot relate the recursive call's
      -- argument to the pattern's `body`.  Substituting a HYPOTHESIS afterwards is harmless.
      have IH : ∀ (A B : VarCtx) (M₁ : CtxBij pe_W₁ A) (M₂ : CtxBij A B) (h : B = pe_W₁)
          (hid' : ∀ v ∈ VarCtx_to_VarSymbs pe_W₁, M₂.toCtxMap.f (M₁.toCtxMap.f v) = v),
          h ▸ (Term.mapCtx M₂ (Term.mapCtx M₁ body)) = body :=
        fun A B M₁ M₂ h hid' => Term.mapCtx_roundtrip pe_W₁ A B M₁ M₂ h hid' _ body
      -- Both equations equate a context to a VARIABLE, so they can be substituted outright.
      subst w₂eq
      subst w₁eq
      -- Step 1: `m₁` destructures at `m₁.f z`, over the erased base `E₁`.
      have hzV₁ : (⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩ : VarSymb × VarType) ∈ V'.1 :=
        m₁.toCtxMap.maps _ (Finset.mem_insert_self _ _)
      have hz₁ : m₁.toCtxMap.f z
          ∉ VarCtx_to_VarSymbs (VarCtx_erase V' ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩) :=
        VarCtx_erase_fresh hzV₁
      have w₂eq₁ : VarCtx_insert ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩
          (VarCtx_erase V' ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩) hz₁ = V' :=
        VarCtx_insert_erase hzV₁ hz₁
      -- Step 2 runs along `m₂` REBUILT at the insert form of `V'` (see `CtxBij.ofEq`).
      have hzV₂ : (⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩
          : VarSymb × VarType) ∈ V''.1 :=
        (CtxBij.ofEq w₂eq₁ m₂).toCtxMap.maps _ (Finset.mem_insert_self _ _)
      have hz₂ : (CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z)
          ∉ VarCtx_to_VarSymbs (VarCtx_erase V''
              ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩) :=
        VarCtx_erase_fresh hzV₂
      have w₂eq₂ : VarCtx_insert
          ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩
          (VarCtx_erase V''
            ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩) hz₂ = V'' :=
        VarCtx_insert_erase hzV₂ hz₂
      rw [Term.mapCtx_pair_elim hz body m₁ hz₁ w₂eq₁,
          Term.pair_elim_as_cast hz₁ _ w₂eq₁,
          Term.mapCtx_cast w₂eq₁ m₂ (CtxBij.ofEq w₂eq₁ m₂) (CtxBij.cast_ofEq w₂eq₁ m₂),
          Term.mapCtx_pair_elim hz₁ _ (CtxBij.ofEq w₂eq₁ m₂) hz₂ w₂eq₂,
          Term.cast_pair_elim]
      -- The destructured variable comes back to `z` …
      have hzz : (CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z) = z :=
        hid z (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_self _ _)
      -- … so the doubly-erased base is `pe_V` again (`Finset.erase_insert`).
      have hB : VarCtx_erase V''
          ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩ = pe_V := by
        rw [hzz, hVV]
        refine VarCtx_ext _ _ ?_
        change (insert (⟨z, T₁.VTypeProd T₂⟩ : VarSymb × VarType) pe_V.1).erase
            ⟨z, T₁.VTypeProd T₂⟩ = pe_V.1
        exact Finset.erase_insert (fun hmem => hz (Finset.mem_image.mpr ⟨_, hmem, rfl⟩))
      have hW : VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase V''
          ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩)
          = VarCtx.insertBnd2 T₁ T₂ pe_V := by rw [hB]
      -- The body maps cancel: `restrictInsert` keeps `f`, and each `extendBnd` layer is closed
      -- by `CtxBij.extendBnd_id` against the base equation.
      have hid₀ : ∀ v ∈ VarCtx_to_VarSymbs pe_V,
          (CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).toCtxMap.f
            ((CtxBij.restrictInsert hz m₁).toCtxMap.f v) = v := fun v hv =>
        hid v (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem hv)
      have hid₁ := CtxBij.extendBnd_id (CtxBij.restrictInsert hz m₁)
        (CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)) hB hid₀ T₁
      have hidB := CtxBij.extendBnd_id ((CtxBij.restrictInsert hz m₁).extendBnd T₁)
        ((CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).extendBnd T₁) (by rw [hB]) hid₁ T₂
      have hIH := IH _ _
        (((CtxBij.restrictInsert hz m₁).extendBnd T₁).extendBnd T₂)
        (((CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).extendBnd T₁).extendBnd T₂)
        hW hidB
      exact Term.pair_elim_congr' hzz hB hW _ _ _ _ _ body hIH
  termination_by _ _ _ _ _ _ _ _ t => sizeOf t

theorem Func.mapCtx_roundtrip {σ : Signature} :
    ∀ (V V' V'' : VarCtx) (m₁ : CtxBij V V') (m₂ : CtxBij V' V'') (hVV : V'' = V)
      (_hid : ∀ v ∈ VarCtx_to_VarSymbs V, m₂.toCtxMap.f (m₁.toCtxMap.f v) = v)
      (N : ℕ) (fn : Func σ V N),
      hVV ▸ (Func.mapCtx m₂ (Func.mapCtx m₁ fn)) = fn
  | _, _, _, m₁, m₂, hVV, _, _, .F hr => by
      rw [Func.mapCtx_F, Func.mapCtx_F, Func.cast_F]
  | V, V', V'', m₁, m₂, hVV, hid, _, .eval g t => by
      rw [Func.mapCtx_eval, Func.mapCtx_eval, Func.cast_eval,
          Func.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid _ g,
          Term.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid _ t]
  termination_by _ _ _ _ _ _ _ _ fn => sizeOf fn
end
