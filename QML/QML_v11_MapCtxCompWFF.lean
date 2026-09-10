import QML.QML_v11_MapCtxComp

/-!
# QML v11 — `mapCtx` composition for `Rel` and `WFF`, and rename composition

LEMMA A2, second half.  The `WFF` proof is the `WFF` round trip with the identity on the right
replaced by a third map `m₃`, exactly as `Term.mapCtx_comp` generalizes `Term.mapCtx_roundtrip`.

The payoff is `WFF.rename_comp : rename b↦c (rename a↦b φ) = rename a↦c φ`, which is what merges
`rename slot↦y ∘ rename u↦slot` into `rename u↦y` in LEMMA A.
-/

/-! ## `Rel` -/

theorem Rel.mapCtx_comp {σ : Signature} {V V' V'' V''' : VarCtx} (m₁ : CtxBij V V')
    (m₂ : CtxBij V' V'') (m₃ : CtxBij V V''') (hVV : V'' = V''')
    (hc : ∀ v ∈ VarCtx_to_VarSymbs V, m₂.toCtxMap.f (m₁.toCtxMap.f v) = m₃.toCtxMap.f v) :
    ∀ {n : ℕ} (R : Rel σ V n), hVV ▸ (Rel.mapCtx m₂ (Rel.mapCtx m₁ R)) = Rel.mapCtx m₃ R
  | _, .R hr => by rw [Rel.mapCtx_R, Rel.mapCtx_R, Rel.mapCtx_R, Rel.cast_R]
  | _, .eval R' t => by
      rw [Rel.mapCtx_eval, Rel.mapCtx_eval, Rel.mapCtx_eval, Rel.cast_eval,
          Rel.mapCtx_comp m₁ m₂ m₃ hVV hc R',
          Term.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc _ t]

/-! ## `WFF` -/

theorem WFF.mapCtx_comp {σ : Signature} :
    ∀ (V V' V'' V''' : VarCtx) (m₁ : CtxBij V V') (m₂ : CtxBij V' V'') (m₃ : CtxBij V V''')
      (hVV : V'' = V''')
      (_hc : ∀ v ∈ VarCtx_to_VarSymbs V, m₂.toCtxMap.f (m₁.toCtxMap.f v) = m₃.toCtxMap.f v)
      (φ : WFF σ V),
      hVV ▸ (WFF.mapCtx m₂ (WFF.mapCtx m₁ φ)) = WFF.mapCtx m₃ φ
  | _, _, _, _, m₁, m₂, m₃, hVV, hc, .atom R => by
      rw [WFF.mapCtx_atom, WFF.mapCtx_atom, WFF.mapCtx_atom, WFF.cast_atom,
          Rel.mapCtx_comp m₁ m₂ m₃ hVV hc R]
  | _, _, _, _, m₁, m₂, m₃, hVV, _, .top => by
      rw [WFF.mapCtx_top, WFF.mapCtx_top, WFF.mapCtx_top, WFF.cast_top]
  | _, _, _, _, m₁, m₂, m₃, hVV, _, .bot => by
      rw [WFF.mapCtx_bot, WFF.mapCtx_bot, WFF.mapCtx_bot, WFF.cast_bot]
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, .and φ ψ => by
      rw [WFF.mapCtx_and, WFF.mapCtx_and, WFF.mapCtx_and, WFF.cast_and,
          WFF.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc φ,
          WFF.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc ψ]
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, .or φ ψ => by
      rw [WFF.mapCtx_or, WFF.mapCtx_or, WFF.mapCtx_or, WFF.cast_or,
          WFF.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc φ,
          WFF.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc ψ]
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, .imp φ ψ => by
      rw [WFF.mapCtx_imp, WFF.mapCtx_imp, WFF.mapCtx_imp, WFF.cast_imp,
          WFF.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc φ,
          WFF.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc ψ]
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, .eq s t => by
      rw [WFF.mapCtx_eq, WFF.mapCtx_eq, WFF.mapCtx_eq, WFF.cast_eq,
          Term.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc _ s,
          Term.mapCtx_comp V V' V'' V''' m₁ m₂ m₃ hVV hc _ t]
  | _, _, _, _, m₁, m₂, m₃, hVV, hc, .all T ψ => by
      have IH := WFF.mapCtx_comp _ _ _ _ (m₁.extendBnd T) (m₂.extendBnd T) (m₃.extendBnd T)
        (congrArg (VarCtx.insertBnd T) hVV) (CtxBij.extendBnd_comp m₁ m₂ m₃ hVV hc T) ψ
      rw [WFF.mapCtx_all, WFF.mapCtx_all, WFF.mapCtx_all, WFF.cast_all]
      exact congrArg (WFF.all T) IH
  | _, _, _, _, m₁, m₂, m₃, hVV, hc, .ex T ψ => by
      have IH := WFF.mapCtx_comp _ _ _ _ (m₁.extendBnd T) (m₂.extendBnd T) (m₃.extendBnd T)
        (congrArg (VarCtx.insertBnd T) hVV) (CtxBij.extendBnd_comp m₁ m₂ m₃ hVV hc T) ψ
      rw [WFF.mapCtx_ex, WFF.mapCtx_ex, WFF.mapCtx_ex, WFF.cast_ex]
      exact congrArg (WFF.ex T) IH
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, .box inner hsub hne => by
      rename_i V_inner
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
      have hIH := WFF.mapCtx_comp V_inner (m₁.imageCtx V_inner hU₁)
        (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂) (m₃.imageCtx V_inner hU₁)
        (m₁.toImage V_inner hU₁) (m₂.toImage (m₁.imageCtx V_inner hU₁) hU₂)
        (m₃.toImage V_inner hU₁) hI hc' inner
      rw [WFF.mapCtx_box m₁ inner hsub hne hU₁ hsub₁ hne₁,
          WFF.mapCtx_box m₂ _ hsub₁ hne₁ hU₂
            (CtxBij.box_sub_image m₂ hsub₁ hU₂) (CtxBij.box_extras_image m₂ hne₁ hU₂),
          WFF.mapCtx_box m₃ inner hsub hne hU₁
            (CtxBij.box_sub_image m₃ hsub hU₁) (CtxBij.box_extras_image m₃ hne hU₁),
          WFF.cast_box]
      exact WFF.box_congr' hI _ _ hIH _ _ _ _
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, .dia x hx χ hsub hne => by
      rename_i V_inner
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
      have hIH := WFF.mapCtx_comp _ _ _ _
        (m₁.extendPoint V_inner hU₁ x hxV hx hx'₁)
        (m₂.extendPoint (m₁.imageCtx V_inner hU₁) hU₂
          (⟨m₁.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType) hxV' hx'₁ hx'₂)
        (m₃.extendPoint V_inner hU₁ x hxV hx hx'₃)
        hCtx hc'' χ
      rw [WFF.mapCtx_dia m₁ hx χ hsub hne hU₁ hxV hx'₁ hsub₁ hne₁,
          WFF.mapCtx_dia m₂ hx'₁ _ hsub₁ hne₁ hU₂ hxV' hx'₂ hsub₂ hne₂,
          WFF.mapCtx_dia m₃ hx χ hsub hne hU₁ hxV hx'₃ hsub₃ hne₃,
          WFF.cast_dia]
      exact WFF.dia_congr' hxx hI _ _ hCtx hIH _ _ _ _
  | V, V', V'', V''', m₁, m₂, m₃, hVV, hc, .pair_elim T₁ T₂ z hz w₁eq w₂eq body => by
      rename_i pe_V pe_W₁
      have IH : ∀ (A B C : VarCtx) (M₁ : CtxBij pe_W₁ A) (M₂ : CtxBij A B)
          (M₃ : CtxBij pe_W₁ C) (h : B = C)
          (hc' : ∀ v ∈ VarCtx_to_VarSymbs pe_W₁,
            M₂.toCtxMap.f (M₁.toCtxMap.f v) = M₃.toCtxMap.f v),
          h ▸ (WFF.mapCtx M₂ (WFF.mapCtx M₁ body)) = WFF.mapCtx M₃ body :=
        fun A B C M₁ M₂ M₃ h hc' => WFF.mapCtx_comp pe_W₁ A B C M₁ M₂ M₃ h hc' body
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
      rw [WFF.mapCtx_pair_elim hz body m₁ hz₁ w₂eq₁,
          WFF.pair_elim_as_cast hz₁ _ w₂eq₁,
          WFF.mapCtx_cast w₂eq₁ m₂ (CtxBij.ofEq w₂eq₁ m₂) (CtxBij.cast_ofEq w₂eq₁ m₂),
          WFF.mapCtx_pair_elim hz₁ _ (CtxBij.ofEq w₂eq₁ m₂) hz₂ w₂eq₂,
          WFF.cast_pair_elim,
          WFF.mapCtx_pair_elim hz body m₃ hz₃ w₂eq₃]
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
      exact WFF.pair_elim_congr' hzz hB hW _ _ _ _ _ _ hIH
  termination_by _ _ _ _ _ _ _ _ _ φ => sizeOf φ

/-! ## ⭐Rename composition

`rename b↦c ∘ rename a↦b = rename a↦c`.  All three land in contexts of the form `V + ⟨·, T⟩`, so
the context equation is `rfl`; the side condition is that the `VarSymb.update`s compose, which needs
`a`, `b`, `c` all fresh for the base `V`. -/

theorem CtxBij.renameOne_comp_f {V : VarCtx} (a b c : VarSymb) (T : VarType)
    (ha : a ∉ VarCtx_to_VarSymbs V) (hb : b ∉ VarCtx_to_VarSymbs V)
    (hc : c ∉ VarCtx_to_VarSymbs V) :
    ∀ v ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨a, T⟩ V ha),
      (CtxBij.renameOne b c T hb hc).toCtxMap.f ((CtxBij.renameOne a b T ha hb).toCtxMap.f v)
        = (CtxBij.renameOne a c T ha hc).toCtxMap.f v := by
  intro v hv
  rw [VarCtx_to_VarSymbs_insert] at hv
  change VarSymb.update id b c (VarSymb.update id a b v) = VarSymb.update id a c v
  rcases Finset.mem_insert.mp hv with rfl | hv'
  · simp [VarSymb.update]
  · have h1 : v ≠ a := fun h => ha (h ▸ hv')
    have h2 : v ≠ b := fun h => hb (h ▸ hv')
    simp [VarSymb.update, h1, h2]

theorem Term.rename_comp {σ : Signature} {V : VarCtx} (a b c : VarSymb) (T : VarType)
    (ha : a ∉ VarCtx_to_VarSymbs V) (hb : b ∉ VarCtx_to_VarSymbs V)
    (hc : c ∉ VarCtx_to_VarSymbs V) {S : VarType}
    (t : Term σ (VarCtx_insert ⟨a, T⟩ V ha) S) :
    Term.rename b c T hb hc (Term.rename a b T ha hb t) = Term.rename a c T ha hc t :=
  Term.mapCtx_comp _ _ _ _ (CtxBij.renameOne a b T ha hb) (CtxBij.renameOne b c T hb hc)
    (CtxBij.renameOne a c T ha hc) rfl (CtxBij.renameOne_comp_f a b c T ha hb hc) S t

theorem Rel.rename_comp {σ : Signature} {V : VarCtx} (a b c : VarSymb) (T : VarType)
    (ha : a ∉ VarCtx_to_VarSymbs V) (hb : b ∉ VarCtx_to_VarSymbs V)
    (hc : c ∉ VarCtx_to_VarSymbs V) {n : ℕ}
    (R : Rel σ (VarCtx_insert ⟨a, T⟩ V ha) n) :
    Rel.rename b c T hb hc (Rel.rename a b T ha hb R) = Rel.rename a c T ha hc R :=
  Rel.mapCtx_comp (CtxBij.renameOne a b T ha hb) (CtxBij.renameOne b c T hb hc)
    (CtxBij.renameOne a c T ha hc) rfl (CtxBij.renameOne_comp_f a b c T ha hb hc) R

theorem WFF.rename_comp {σ : Signature} {V : VarCtx} (a b c : VarSymb) (T : VarType)
    (ha : a ∉ VarCtx_to_VarSymbs V) (hb : b ∉ VarCtx_to_VarSymbs V)
    (hc : c ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨a, T⟩ V ha)) :
    WFF.rename b c T hb hc (WFF.rename a b T ha hb φ) = WFF.rename a c T ha hc φ :=
  WFF.mapCtx_comp _ _ _ _ (CtxBij.renameOne a b T ha hb) (CtxBij.renameOne b c T hb hc)
    (CtxBij.renameOne a c T ha hc) rfl (CtxBij.renameOne_comp_f a b c T ha hb hc) φ
