import QML.QML_v11_MapCtxWFF

/-!
# QML v11 — `mapCtx` composition

Part of LEMMA A for `congAll`.  `Proof.all_elim` OPENS a binder: it renames the slot to a fresh user
name `y` and then substitutes.  In `congAll` the formula being opened is the weakening by `u` of
`rename u↦slot φ`, so unfolding gives the chain

    rename slot↦y  ∘  ctx_extU u  ∘  rename u↦slot

and LEMMA A collapses it to `ctx_extU u (rename u↦y φ)` up to reordering the context.  It splits:

* **A1** — `ctx_extU` commutes with `mapCtx`.  A separate induction: weakening is NOT a `mapCtx`
  (it is an embedding, not a bijection).
* **A2** (this file) — `mapCtx` COMPOSITION: `mapCtx m₂ ∘ mapCtx m₁ = mapCtx m₃` whenever the
  underlying functions compose, `m₂.f ∘ m₁.f = m₃.f` on the source's symbols.  That is what merges
  `rename slot↦y ∘ rename u↦slot` into `rename u↦y`.

A2 is the round trip of `QML_v11_MapCtx` with the identity on the right replaced by a third map, and
the proof is the same arm for arm: every cast, congruence and computation rule is reused, and only
`imageCtx_comp` / `extendBnd_comp` are new.
-/

/-! ## The two new helpers -/

/-- Images compose: `imageCtx_roundtrip` with `m₃` in place of the identity. -/
theorem CtxBij.imageCtx_comp {V V' V'' V''' : VarCtx} (m₁ : CtxBij V V') (m₂ : CtxBij V' V'')
    (m₃ : CtxBij V V''') (U : VarCtx)
    (h₁ : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V)
    (h₂ : ∀ v ∈ VarCtx_to_VarSymbs (m₁.imageCtx U h₁), v ∈ VarCtx_to_VarSymbs V')
    (hc : ∀ v ∈ VarCtx_to_VarSymbs U, m₂.toCtxMap.f (m₁.toCtxMap.f v) = m₃.toCtxMap.f v) :
    m₂.imageCtx (m₁.imageCtx U h₁) h₂ = m₃.imageCtx U h₁ := by
  refine VarCtx_ext _ _ ?_
  rw [CtxBij.imageCtx_fst, CtxBij.imageCtx_fst, CtxBij.imageCtx_fst, Finset.image_image]
  refine Finset.image_congr ?_
  intro p hp
  have hfix : m₂.toCtxMap.f (m₁.toCtxMap.f p.1) = m₃.toCtxMap.f p.1 :=
    hc p.1 (Finset.mem_image.mpr ⟨p, Finset.mem_coe.mp hp, rfl⟩)
  simp only [Function.comp_apply, hfix]

/-- One `extendBnd` layer of a composition: `extendBnd_id` with `m₃` in place of the identity.  The
    slot goes `A.nextBnd ↦ B.nextBnd ↦ C.nextBnd` on the left and `A.nextBnd ↦ D.nextBnd` on the
    right, and `hCD` makes those agree. -/
theorem CtxBij.extendBnd_comp {A B C D : VarCtx} (m₁ : CtxBij A B) (m₂ : CtxBij B C)
    (m₃ : CtxBij A D) (hCD : C = D)
    (hc : ∀ v ∈ VarCtx_to_VarSymbs A, m₂.toCtxMap.f (m₁.toCtxMap.f v) = m₃.toCtxMap.f v)
    (T : VarType) :
    ∀ v ∈ VarCtx_to_VarSymbs (VarCtx.insertBnd T A),
      (m₂.extendBnd T).toCtxMap.f ((m₁.extendBnd T).toCtxMap.f v)
        = (m₃.extendBnd T).toCtxMap.f v := by
  intro v hv
  rw [VarCtx.symbs_insertBnd] at hv
  rcases Finset.mem_insert.mp hv with rfl | hv'
  · rw [CtxBij.extendBnd_f, CtxBij.extendBnd_f, CtxBij.extendBnd_f, VarSymb.update_self,
      VarSymb.update_self, VarSymb.update_self, hCD]
  · have h1 : v ≠ A.nextBnd := fun h => VarCtx.nextBnd_not_mem A (h ▸ hv')
    have hmB : m₁.toCtxMap.f v ∈ VarCtx_to_VarSymbs B := by
      rcases Finset.mem_image.mp hv' with ⟨p, hp, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨m₁.toCtxMap.f p.1, p.2⟩, m₁.toCtxMap.maps p hp, rfl⟩
    have h2 : m₁.toCtxMap.f v ≠ B.nextBnd := fun h => VarCtx.nextBnd_not_mem B (h ▸ hmB)
    rw [CtxBij.extendBnd_f, CtxBij.extendBnd_f, CtxBij.extendBnd_f, VarSymb.update_of_ne _ h1,
        VarSymb.update_of_ne _ h2, VarSymb.update_of_ne _ h1]
    exact hc v hv'

/-! ## `Term` / `Func` composition -/

mutual
theorem Term.mapCtx_comp {σ : Signature} :
    ∀ (V V' V'' V''' : VarCtx) (m₁ : CtxBij V V') (m₂ : CtxBij V' V'') (m₃ : CtxBij V V''')
      (hVV : V'' = V''')
      (_hc : ∀ v ∈ VarCtx_to_VarSymbs V, m₂.toCtxMap.f (m₁.toCtxMap.f v) = m₃.toCtxMap.f v)
      (S : VarType) (t : Term σ V S),
      hVV ▸ (Term.mapCtx m₂ (Term.mapCtx m₁ t)) = Term.mapCtx m₃ t
  | V, _, _, _, m₁, m₂, m₃, hVV, hc, _, .var ⟨v, hv⟩ => by
      have hvs : v ∈ VarCtx_to_VarSymbs V := Finset.mem_image.mpr ⟨_, hv, rfl⟩
      rw [Term.mapCtx_var m₁ hv (m₁.toCtxMap.maps _ hv),
          Term.mapCtx_var m₂ _ (m₂.toCtxMap.maps _ (m₁.toCtxMap.maps _ hv)),
          Term.mapCtx_var m₃ hv (m₃.toCtxMap.maps _ hv),
          Term.cast_var]
      congr 1
      apply Subtype.ext
      rw [cast_subtype_val]
      exact hc v hvs
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, _, .func fn => by
      rw [Term.mapCtx_func, Term.mapCtx_func, Term.mapCtx_func, Term.cast_func,
          Func.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc _ fn]
  | _, _, _, _, m₁, m₂, m₃, hVV, _, _, .unit => by
      rw [Term.mapCtx_unit, Term.mapCtx_unit, Term.mapCtx_unit, Term.cast_unit]
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, _, .pair a b => by
      rw [Term.mapCtx_pair, Term.mapCtx_pair, Term.mapCtx_pair, Term.cast_pair,
          Term.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc _ a,
          Term.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc _ b]
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, _, .boxterm tt hsub hne => by
      rename_i V_inner _
      have hU₁ : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_box_sub hsub
      have hsub₁ := CtxBij.box_sub_image m₁ hsub hU₁
      have hne₁ := CtxBij.box_extras_image m₁ hne hU₁
      have hU₂ : ∀ v ∈ VarCtx_to_VarSymbs (m₁.imageCtx V_inner hU₁),
          v ∈ VarCtx_to_VarSymbs V' := VarCtx.symbs_of_box_sub hsub₁
      have hc' : ∀ v ∈ VarCtx_to_VarSymbs V_inner,
          m₂.toCtxMap.f (m₁.toCtxMap.f v) = m₃.toCtxMap.f v := fun v hv => hc v (hU₁ v hv)
      have hI : m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂ = m₃.imageCtx V_inner hU₁ :=
        CtxBij.imageCtx_comp m₁ m₂ m₃ V_inner hU₁ hU₂ hc'
      have hIH := Term.mapCtx_comp V_inner (m₁.imageCtx V_inner hU₁)
        (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂) (m₃.imageCtx V_inner hU₁)
        (m₁.toImage V_inner hU₁) (m₂.toImage (m₁.imageCtx V_inner hU₁) hU₂)
        (m₃.toImage V_inner hU₁) hI hc' _ tt
      rw [Term.mapCtx_boxterm m₁ tt hsub hne hU₁ hsub₁ hne₁,
          Term.mapCtx_boxterm m₂ _ hsub₁ hne₁ hU₂
            (CtxBij.box_sub_image m₂ hsub₁ hU₂) (CtxBij.box_extras_image m₂ hne₁ hU₂),
          Term.mapCtx_boxterm m₃ tt hsub hne hU₁
            (CtxBij.box_sub_image m₃ hsub hU₁) (CtxBij.box_extras_image m₃ hne hU₁),
          Term.cast_boxterm]
      exact Term.boxterm_congr' hI _ _ hIH _ _ _ _
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, _, .diaterm x hx tt hsub hne => by
      rename_i V_inner _
      have hxV : x.1 ∈ VarCtx_to_VarSymbs V :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub, rfl⟩
      have hU₁ : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_dia_sub hsub
      have hx'₁ := CtxBij.notMem_imageCtx m₁ hU₁ hxV hx
      have hsub₁ := CtxBij.dia_sub_image m₁ hsub hU₁ hx'₁
      have hne₁ := CtxBij.dia_extras_image m₁ hne hU₁ hx'₁
      have hxV' : m₁.toCtxMap.f x.1 ∈ VarCtx_to_VarSymbs V' :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub₁, rfl⟩
      have hU₂ : ∀ v ∈ VarCtx_to_VarSymbs (m₁.imageCtx V_inner hU₁),
          v ∈ VarCtx_to_VarSymbs V' := VarCtx.symbs_of_dia_sub hsub₁
      have hx'₂ := CtxBij.notMem_imageCtx m₂ hU₂ hxV' hx'₁
      have hsub₂ := CtxBij.dia_sub_image m₂ hsub₁ hU₂ hx'₂
      have hne₂ := CtxBij.dia_extras_image m₂ hne₁ hU₂ hx'₂
      have hx'₃ := CtxBij.notMem_imageCtx m₃ hU₁ hxV hx
      have hsub₃ := CtxBij.dia_sub_image m₃ hsub hU₁ hx'₃
      have hne₃ := CtxBij.dia_extras_image m₃ hne hU₁ hx'₃
      have hxeq : m₂.toCtxMap.f (m₁.toCtxMap.f x.1) = m₃.toCtxMap.f x.1 := hc x.1 hxV
      have hI : m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂ = m₃.imageCtx V_inner hU₁ :=
        CtxBij.imageCtx_comp m₁ m₂ m₃ V_inner hU₁ hU₂ (fun v hv => hc v (hU₁ v hv))
      have hxx : (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType)
          = ⟨m₃.toCtxMap.f x.1, x.2⟩ := by
        rw [hxeq]
      have hCtx : VarCtx_insert
            (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType)
            (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂) hx'₂
          = VarCtx_insert ⟨m₃.toCtxMap.f x.1, x.2⟩ (m₃.imageCtx V_inner hU₁) hx'₃ := by
        refine VarCtx_ext _ _ ?_
        change insert (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType)
              (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂).1
            = insert (⟨m₃.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType)
                (m₃.imageCtx V_inner hU₁).1
        rw [hxx, hI]
      have hc'' : ∀ v ∈ VarCtx_to_VarSymbs (VarCtx_insert x V_inner hx),
          m₂.toCtxMap.f (m₁.toCtxMap.f v) = m₃.toCtxMap.f v := by
        intro v hv
        rw [VarCtx_to_VarSymbs_insert] at hv
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact hxeq
        · exact hc v (hU₁ v hv')
      have hIH := Term.mapCtx_comp _ _ _ _
        (m₁.extendPoint V_inner hU₁ x hxV hx hx'₁)
        (m₂.extendPoint (m₁.imageCtx V_inner hU₁) hU₂
          (⟨m₁.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType) hxV' hx'₁ hx'₂)
        (m₃.extendPoint V_inner hU₁ x hxV hx hx'₃)
        hCtx hc'' _ tt
      rw [Term.mapCtx_diaterm m₁ hx tt hsub hne hU₁ hxV hx'₁ hsub₁ hne₁,
          Term.mapCtx_diaterm m₂ hx'₁ _ hsub₁ hne₁ hU₂ hxV' hx'₂ hsub₂ hne₂,
          Term.mapCtx_diaterm m₃ hx tt hsub hne hU₁ hxV hx'₃ hsub₃ hne₃,
          Term.cast_diaterm]
      exact Term.diaterm_congr' hxx hI _ _ hCtx hIH _ _ _ _
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, _, .pair_elim T₁ T₂ z hz w₁eq w₂eq body => by
      rename_i pe_V pe_W₁
      -- IH before any `subst`, generalized over the maps (see `Term.mapCtx_roundtrip`).
      have IH : ∀ (A B C : VarCtx) (M₁ : CtxBij pe_W₁ A) (M₂ : CtxBij A B)
          (M₃ : CtxBij pe_W₁ C) (h : B = C)
          (hc' : ∀ v ∈ VarCtx_to_VarSymbs pe_W₁,
            M₂.toCtxMap.f (M₁.toCtxMap.f v) = M₃.toCtxMap.f v),
          h ▸ (Term.mapCtx M₂ (Term.mapCtx M₁ body)) = Term.mapCtx M₃ body :=
        fun A B C M₁ M₂ M₃ h hc' => Term.mapCtx_comp pe_W₁ A B C M₁ M₂ M₃ h hc' _ body
      subst w₂eq
      subst w₁eq
      have hzV₁ : (⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩ : VarSymb × VarType) ∈ V'.1 :=
        m₁.toCtxMap.maps _ (Finset.mem_insert_self _ _)
      have hz₁ : m₁.toCtxMap.f z
          ∉ VarCtx_to_VarSymbs (VarCtx_erase V' ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩) :=
        VarCtx_erase_fresh hzV₁
      have w₂eq₁ : VarCtx_insert ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩
          (VarCtx_erase V' ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩) hz₁ = V' :=
        VarCtx_insert_erase hzV₁ hz₁
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
      have hzV₃ : (⟨m₃.toCtxMap.f z, T₁.VTypeProd T₂⟩ : VarSymb × VarType) ∈ V'''.1 :=
        m₃.toCtxMap.maps _ (Finset.mem_insert_self _ _)
      have hz₃ : m₃.toCtxMap.f z
          ∉ VarCtx_to_VarSymbs (VarCtx_erase V''' ⟨m₃.toCtxMap.f z, T₁.VTypeProd T₂⟩) :=
        VarCtx_erase_fresh hzV₃
      have w₂eq₃ : VarCtx_insert ⟨m₃.toCtxMap.f z, T₁.VTypeProd T₂⟩
          (VarCtx_erase V''' ⟨m₃.toCtxMap.f z, T₁.VTypeProd T₂⟩) hz₃ = V''' :=
        VarCtx_insert_erase hzV₃ hz₃
      rw [Term.mapCtx_pair_elim hz body m₁ hz₁ w₂eq₁,
          Term.pair_elim_as_cast hz₁ _ w₂eq₁,
          Term.mapCtx_cast w₂eq₁ m₂ (CtxBij.ofEq w₂eq₁ m₂) (CtxBij.cast_ofEq w₂eq₁ m₂),
          Term.mapCtx_pair_elim hz₁ _ (CtxBij.ofEq w₂eq₁ m₂) hz₂ w₂eq₂,
          Term.cast_pair_elim,
          Term.mapCtx_pair_elim hz body m₃ hz₃ w₂eq₃]
      have hzz : (CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z) = m₃.toCtxMap.f z :=
        hc z (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_self _ _)
      have hB : VarCtx_erase V''
          ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩
          = VarCtx_erase V''' ⟨m₃.toCtxMap.f z, T₁.VTypeProd T₂⟩ := by
        rw [hzz, hVV]
      have hW : VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase V''
          ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩)
          = VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase V''' ⟨m₃.toCtxMap.f z, T₁.VTypeProd T₂⟩) := by
        rw [hB]
      have hc₀ : ∀ v ∈ VarCtx_to_VarSymbs pe_V,
          (CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).toCtxMap.f
            ((CtxBij.restrictInsert hz m₁).toCtxMap.f v)
          = (CtxBij.restrictInsert hz m₃).toCtxMap.f v := fun v hv =>
        hc v (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem hv)
      have hc₁ := CtxBij.extendBnd_comp (CtxBij.restrictInsert hz m₁)
        (CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)) (CtxBij.restrictInsert hz m₃)
        hB hc₀ T₁
      have hcB := CtxBij.extendBnd_comp ((CtxBij.restrictInsert hz m₁).extendBnd T₁)
        ((CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).extendBnd T₁)
        ((CtxBij.restrictInsert hz m₃).extendBnd T₁) (by rw [hB]) hc₁ T₂
      have hIH := IH _ _ _
        (((CtxBij.restrictInsert hz m₁).extendBnd T₁).extendBnd T₂)
        (((CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).extendBnd T₁).extendBnd T₂)
        (((CtxBij.restrictInsert hz m₃).extendBnd T₁).extendBnd T₂)
        hW hcB
      exact Term.pair_elim_congr' hzz hB hW _ _ _ _ _ _ hIH
  termination_by _ _ _ _ _ _ _ _ _ _ t => sizeOf t

theorem Func.mapCtx_comp {σ : Signature} :
    ∀ (V V' V'' V''' : VarCtx) (m₁ : CtxBij V V') (m₂ : CtxBij V' V'') (m₃ : CtxBij V V''')
      (hVV : V'' = V''')
      (_hc : ∀ v ∈ VarCtx_to_VarSymbs V, m₂.toCtxMap.f (m₁.toCtxMap.f v) = m₃.toCtxMap.f v)
      (N : ℕ) (fn : Func σ V N),
      hVV ▸ (Func.mapCtx m₂ (Func.mapCtx m₁ fn)) = Func.mapCtx m₃ fn
  | _, _, _, _, m₁, m₂, m₃, hVV, _, _, .F hr => by
      rw [Func.mapCtx_F, Func.mapCtx_F, Func.mapCtx_F, Func.cast_F]
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, _, .eval g t => by
      rw [Func.mapCtx_eval, Func.mapCtx_eval, Func.mapCtx_eval, Func.cast_eval,
          Func.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc _ g,
          Term.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc _ t]
  termination_by _ _ _ _ _ _ _ _ _ _ fn => sizeOf fn
end
