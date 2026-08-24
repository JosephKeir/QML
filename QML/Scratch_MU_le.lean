import QML.QML_Full_v7

-- Full mutual block prototype for the bpd-preservation chain (primed names).
-- Measures mirror the corresponding defs (phases: MU 2, ctx_rest 1, arms 0).
-- h_V_inner_eq in dia Case 3 is sorried HERE ONLY (private VarCtx_ext);
-- the v7 port uses the real derivation already proven there.
mutual

theorem scratch_MU_le' {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.ctx_rest_MU hx s φ)
      ≤ WFF.binderPairDepth φ := by
  unfold WFF.ctx_rest_MU
  split
  · rename_i h_pv'
    exact scratch_ctx_rest_le' hx h_pv' s φ
  · rename_i z V1 V2 hzmem h_pv'
    split
    · exact Nat.zero_le _
    · rename_i h_z_ne_x
      simp only [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_pairElim]
      refine le_trans (scratch_MU_le' _ _ _) ?_
      simp only [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_unpair]
      exact le_refl _
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ,
                WFF.diaCount φ, WFF.numNodes φ, 2)
decreasing_by
  · -- none → ctx_rest_le: all comps equal, phase 2 → 1.
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt
    right; refine ⟨rfl, ?_⟩
    right; refine ⟨rfl, ?_⟩
    right; exact ⟨rfl, by decide⟩
  · -- Case B self-call: comp 1 strict (pairDepth shrinks, bpd preserved).
    rename_i z V1 V2 hzmem _ _ _ h_z_ne_x
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    simp only [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_unpair]
    rw [VarCtx.pairDepth_insert, VarCtx.pairDepth_insert]
    have hzmem_V : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1 := by
      rcases Finset.mem_insert.mp hzmem with h_eq | h_in_V
      · exact absurd (Prod.mk.inj h_eq).1 h_z_ne_x
      · exact h_in_V
    exact Nat.add_lt_add_right
      (Nat.add_lt_add_left (VarCtx.pairDepth_unpair_lt hzmem_V _ _ _) _) _

theorem scratch_quant_arm_le' {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (is_ex : Bool)
    (x_a : VarSymb × VarType)
    (hx_a : x_a.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨x, S⟩ V hx))
    (ψ : WFF σ (VarCtx_insert x_a (VarCtx_insert ⟨x, S⟩ V hx) hx_a)) :
    WFF.binderPairDepth (WFF.ctx_rest_quant_arm hx h_pf s is_ex x_a hx_a ψ)
      ≤ x_a.2.pairDepth + WFF.binderPairDepth ψ := by
  unfold WFF.ctx_rest_quant_arm
  cases is_ex
  · simp only [Bool.cond_false, WFF.binderPairDepth]
    refine Nat.add_le_add_left ?_ _
    refine le_trans (scratch_MU_le' _ _ _) ?_
    rw [WFF.binderPairDepth_ctx_cast]
  · simp only [Bool.cond_true, WFF.binderPairDepth]
    refine Nat.add_le_add_left ?_ _
    refine le_trans (scratch_MU_le' _ _ _) ?_
    rw [WFF.binderPairDepth_ctx_cast]
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + x_a.2.pairDepth
                  + WFF.binderPairDepth ψ,
                WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  all_goals (
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt
    right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth_ctx_cast, VarCtx.pairDepth_insert]; omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount_ctx_cast]
      · left; simp only [WFF.numNodes_ctx_cast]; omega)

theorem scratch_box_arm_le' {σ : Signature}
    {V : VarCtx} {V_inner : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (ψ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (h_no_extras : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
                   VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    WFF.binderPairDepth (WFF.ctx_rest_box_arm hx h_pf s ψ hsub h_no_extras)
      ≤ WFF.binderPairDepth ψ := by
  unfold WFF.ctx_rest_box_arm
  split
  · rename_i h_x_in
    cases S with
    | Var =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeOne =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeDia T =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeProd T1 T2 =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeBox T =>
        dsimp only
        split
        · rename_i hxT_in
          split
          · rename_i V_s s_inner s_hsub s_h_no_extras
            have hVs : V_s = VarCtx_erase V_inner ⟨x, T⟩ :=
              ctx_rest_box_V_s_eq hxT_in hsub h_no_extras s_hsub s_h_no_extras
            subst hVs
            refine le_trans (scratch_MU_le' _ _ _) ?_
            rw [WFF.binderPairDepth_ctx_cast]
          · rename_i sv1 sv2 sz _ _ _ _ _ sw2eq _
            exfalso
            have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                ∈ V.1 := by
              rw [← sw2eq]; exact Finset.mem_insert_self _ _
            exact VarCtx.firstPairVar_none_no_pair h_pf
              (Finset.mem_insert_of_mem h_sz_in_V)
        · rename_i hxT_in
          exfalso
          obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
          simp only at hx'_eq; subst hx'_eq
          have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
          rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
          · have hbox : T'.VTypeBox = T.VTypeBox := (Prod.mk.inj h_eq).2
            have hT_eq : T' = T := VarType.VTypeBox.inj hbox
            subst hT_eq
            exact hxT_in hx'T'
          · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
  · exact Nat.le_refl _
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth ψ,
                WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  rename_i hS_eq hxT_in _ _ _ _ _
  have hx_minus : x ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨x, T⟩) :=
    VarCtx_erase_fresh hxT_in
  have h_le := VarCtx.pairDepth_le_of_box_subset hsub
  have h_V_inner_pd : V_inner.pairDepth =
      T.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := by
    conv_lhs => rw [show V_inner = VarCtx_insert ⟨x, T⟩
      (VarCtx_erase V_inner ⟨x, T⟩) hx_minus from
      (VarCtx_insert_erase hxT_in hx_minus).symm]
    exact VarCtx.pairDepth_insert _ _ _
  have hS_pd : S.pairDepth = T.pairDepth := by rw [hS_eq]; rfl
  have e_t : ((x, T) : VarSymb × VarType).2.pairDepth = T.pairDepth := rfl
  have e_s : ((x, S) : VarSymb × VarType).2.pairDepth = S.pairDepth := rfl
  have h_key : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth ≤ V.pairDepth := by
    rw [VarCtx.pairDepth_insert, h_V_inner_pd] at h_le
    have hpd : ((x, T.VTypeBox) : VarSymb × VarType).2.pairDepth
        = T.pairDepth := rfl
    omega
  by_cases h_c1 : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth < V.pairDepth
  · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
    omega
  · have h_c1_eq : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth = V.pairDepth := by
      omega
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
      omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount_ctx_cast]
      · left; simp only [WFF.numNodes_ctx_cast]; omega

theorem scratch_dia_arm_le' {σ : Signature}
    {V : VarCtx} {V_inner : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (h_no_extras : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
                   VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    WFF.binderPairDepth (WFF.ctx_rest_dia_arm hx h_pf s xv hxv ψ hsub h_no_extras)
      ≤ WFF.binderPairDepth ψ := by
  unfold WFF.ctx_rest_dia_arm
  split
  · -- Case 3
    rename_i h_xv_eq_x
    have hxv_in_Vext : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈
        (VarCtx_insert ⟨x, S⟩ V hx).1 := by
      apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
    have h_S_eq : S = xv.2.VTypeDia := by
      rcases Finset.mem_insert.mp hxv_in_Vext with h_eq | h_in_V
      · exact ((Prod.mk.inj h_eq).2).symm
      · exfalso
        exact hx (Finset.mem_image.mpr ⟨_, h_in_V, h_xv_eq_x⟩)
    subst h_S_eq
    dsimp only
    split
    · rename_i V_inner_s xv_s hxv_s tt_s hsub_s h_no_extras_s
      have h_V_inner_eq : V_inner = V_inner_s := by
        sorry -- scratch-only (private VarCtx_ext); v7 uses the real one
      -- subst kills the RHS var: eliminate the SPLIT-LOCAL V_inner_s (not
      -- the theorem binder V_inner), so the original ψ survives unrewritten
      -- and the decreasing goal's caller/callee tuples share it.
      subst h_V_inner_eq
      with_unfolding_all
        exact le_trans (scratch_MU_le' _ _ _)
          (le_of_eq (WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s
            (fun h => (by
              apply hx
              apply Finset.mem_image.mpr
              refine ⟨⟨xv_s.1, xv_s.2.VTypeDia⟩, ?_, h ▸ h_xv_eq_x⟩
              apply hsub_s
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _))
            h_xv_eq_x ψ).2.property.1)
    · rename_i sv1 sv2 sz _ _ _ _ _ sw2eq _
      exfalso
      have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
          ∈ V.1 := by
        rw [← sw2eq]; exact Finset.mem_insert_self _ _
      exact VarCtx.firstPairVar_none_no_pair h_pf
        (Finset.mem_insert_of_mem h_sz_in_V)
  · -- Cases 1/2
    rename_i h_xv_ne_x
    split
    · rename_i h_x_in
      cases S with
      | Var =>
          exfalso
          obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
          simp only at hx'_eq; subst hx'_eq
          have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
          have hx'box_in_dia : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hx'box_in
          rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
          · exact VarType.noConfusion (Prod.mk.inj h_eq).2
          · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
      | VTypeOne =>
          exfalso
          obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
          simp only at hx'_eq; subst hx'_eq
          have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
          have hx'box_in_dia : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hx'box_in
          rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
          · exact VarType.noConfusion (Prod.mk.inj h_eq).2
          · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
      | VTypeDia T =>
          exfalso
          obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
          simp only at hx'_eq; subst hx'_eq
          have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
          have hx'box_in_dia : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hx'box_in
          rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
          · exact VarType.noConfusion (Prod.mk.inj h_eq).2
          · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
      | VTypeProd T1 T2 =>
          exfalso
          obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
          simp only at hx'_eq; subst hx'_eq
          have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
          have hx'box_in_dia : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hx'box_in
          rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
          · exact VarType.noConfusion (Prod.mk.inj h_eq).2
          · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
      | VTypeBox T =>
          dsimp only
          split
          · rename_i hxT_in
            split
            · rename_i V_s s_inner s_hsub s_h_no_extras
              have hVs : V_s = VarCtx_erase V_inner ⟨x, T⟩ :=
                ctx_rest_dia_V_s_eq hxT_in hsub h_no_extras s_hsub
                  s_h_no_extras
              subst hVs
              simp only [WFF.binderPairDepth]
              refine le_trans (scratch_MU_le' _ _ _) ?_
              rw [WFF.binderPairDepth_ctx_cast]
            · rename_i sv1 sv2 sz _ _ _ _ _ sw2eq _
              exfalso
              have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                  ∈ V.1 := by
                rw [← sw2eq]; exact Finset.mem_insert_self _ _
              exact VarCtx.firstPairVar_none_no_pair h_pf
                (Finset.mem_insert_of_mem h_sz_in_V)
          · rename_i hxT_in
            exfalso
            obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
            simp only at hx'_eq; subst hx'_eq
            have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                              ∈ (VarCtx_box V_inner).1 :=
              Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
            have hx'box_in_dia :
                (⟨x', T'.VTypeBox⟩ : VarSymb × VarType) ∈
                  (VarCtx_dia xv V_inner hxv).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hx'box_in
            rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
            · have hT_eq : T' = T :=
                VarType.VTypeBox.inj (Prod.mk.inj h_eq).2
              subst hT_eq
              exact hxT_in hx'T'
            · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    · exact Nat.le_refl _
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth ψ,
                1 + WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  · -- Case 2 MU call (goal order: Case 2 first, despite Case 3 preceding it
    -- in the source): box_arm-style arithmetic with the dia subset.
    -- NO subst in bullets: substituting a theorem binder reverts/repacks
    -- the context.  Bridge S via Nat-level equations instead.
    rename_i hS_eq hxT_in _ _ _ _ _
    have hx_minus : x ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨x, T⟩) :=
      VarCtx_erase_fresh hxT_in
    have h_le := VarCtx.pairDepth_le_of_dia_subset hsub
    have h_V_inner_pd : V_inner.pairDepth =
        T.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := by
      conv_lhs => rw [show V_inner = VarCtx_insert ⟨x, T⟩
        (VarCtx_erase V_inner ⟨x, T⟩) hx_minus from
        (VarCtx_insert_erase hxT_in hx_minus).symm]
      exact VarCtx.pairDepth_insert _ _ _
    have hS_pd : S.pairDepth = T.pairDepth := by rw [hS_eq]; rfl
    have h_key : xv.2.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth
                  ≤ V.pairDepth := by
      rw [VarCtx.pairDepth_insert, VarCtx.pairDepth_insert, h_V_inner_pd]
        at h_le
      have hpd : ((x, T.VTypeBox) : VarSymb × VarType).2.pairDepth
          = T.pairDepth := rfl
      omega
    have e_t : ((x, T) : VarSymb × VarType).2.pairDepth = T.pairDepth := rfl
    have e_s : ((x, S) : VarSymb × VarType).2.pairDepth = S.pairDepth := rfl
    by_cases h_c1 : xv.2.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth
        < V.pairDepth
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
      omega
    · have h_c1_eq : xv.2.pairDepth
          + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth = V.pairDepth := by
        omega
      apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
      refine ⟨?_, ?_⟩
      · simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
        omega
      · left; simp only [WFF.diaCount_ctx_cast]; omega
  · -- Case 3 MU call: comp 1 ≤ via dia-subset on the substituent; comp 2
    -- strict via the +1 gap.  bpd/dC of the reorder projection rewritten
    -- via its subtype property under full transparency (the projection in
    -- the goal carries the def's own ne-proof, ours differs only there).
    rename_i h_xv_eq_x _ _ xv_s _ _ _ _ _
    have eS : S.pairDepth = xv.2.pairDepth := by rw [h_S_eq]; rfl
    have e1 : ((x, xv.2) : VarSymb × VarType).2.pairDepth
        = xv.2.pairDepth := rfl
    have e_s : ((x, S) : VarSymb × VarType).2.pairDepth = S.pairDepth := rfl
    have h_bpd := (WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s
      (fun h => (by
        apply hx
        apply Finset.mem_image.mpr
        refine ⟨⟨xv_s.1, xv_s.2.VTypeDia⟩, ?_, h ▸ h_xv_eq_x⟩
        apply hsub_s
        rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _))
      h_xv_eq_x ψ).2.property.1
    have h_dC := (WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s
      (fun h => (by
        apply hx
        apply Finset.mem_image.mpr
        refine ⟨⟨xv_s.1, xv_s.2.VTypeDia⟩, ?_, h ▸ h_xv_eq_x⟩
        apply hsub_s
        rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _))
      h_xv_eq_x ψ).2.property.2
    have h_le := VarCtx.pairDepth_le_of_dia_subset hsub_s
    rw [VarCtx.pairDepth_insert] at h_le
    with_unfolding_all rw [h_bpd, h_dC]
    by_cases h_c1 : xv_s.2.pairDepth + V_inner.pairDepth < V.pairDepth
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [VarCtx.pairDepth_insert]
      omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
      refine ⟨?_, ?_⟩
      · simp only [VarCtx.pairDepth_insert]
        omega
      · left; omega

theorem scratch_ctx_rest_le' {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.ctx_rest hx h_pf s φ)
      ≤ WFF.binderPairDepth φ := by
  unfold WFF.ctx_rest
  split
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rename_i φ' ψ
    simp only [WFF.binderPairDepth]
    exact Nat.add_le_add (scratch_ctx_rest_le' hx h_pf s φ')
                         (scratch_ctx_rest_le' hx h_pf s ψ)
  · rename_i φ' ψ
    simp only [WFF.binderPairDepth]
    exact Nat.add_le_add (scratch_ctx_rest_le' hx h_pf s φ')
                         (scratch_ctx_rest_le' hx h_pf s ψ)
  · rename_i φ' ψ
    simp only [WFF.binderPairDepth]
    exact Nat.add_le_add (scratch_ctx_rest_le' hx h_pf s φ')
                         (scratch_ctx_rest_le' hx h_pf s ψ)
  · exact Nat.zero_le _
  · rename_i x_a hx_a ψ
    simp only [WFF.binderPairDepth]
    exact scratch_quant_arm_le' hx h_pf s false x_a hx_a ψ
  · rename_i x_a hx_a ψ
    simp only [WFF.binderPairDepth]
    exact scratch_quant_arm_le' hx h_pf s true x_a hx_a ψ
  · rename_i V_inner ψ hsub h_no_extras
    simp only [WFF.binderPairDepth]
    exact scratch_box_arm_le' hx h_pf s ψ hsub h_no_extras
  · rename_i V_inner xv hxv ψ hsub h_no_extras
    simp only [WFF.binderPairDepth]
    exact scratch_dia_arm_le' hx h_pf s xv hxv ψ hsub h_no_extras
  · rename_i v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body
    exfalso
    have h_z_in : (⟨z, v1.2.VTypeProd v2.2⟩ : VarSymb × VarType) ∈
        (VarCtx_insert ⟨x, S⟩ V hx).1 := by
      rw [← w2eq]; exact Finset.mem_insert_self _ _
    exact VarCtx.firstPairVar_none_no_pair h_pf h_z_in
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ,
                WFF.diaCount φ, WFF.numNodes φ, 1)
decreasing_by
  · -- and, on φ' (other = ψ)
    rename_i φ' ψ h_eq
    subst h_eq
    by_cases hb : WFF.binderPairDepth ψ = 0
    · by_cases hd : WFF.diaCount ψ = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- and, on ψ (other = φ')
    rename_i φ' ψ h_eq
    subst h_eq
    by_cases hb : WFF.binderPairDepth φ' = 0
    · by_cases hd : WFF.diaCount φ' = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- or, on φ'
    rename_i φ' ψ h_eq
    subst h_eq
    by_cases hb : WFF.binderPairDepth ψ = 0
    · by_cases hd : WFF.diaCount ψ = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- or, on ψ
    rename_i φ' ψ h_eq
    subst h_eq
    by_cases hb : WFF.binderPairDepth φ' = 0
    · by_cases hd : WFF.diaCount φ' = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- imp, on φ'
    rename_i φ' ψ h_eq
    subst h_eq
    by_cases hb : WFF.binderPairDepth ψ = 0
    · by_cases hd : WFF.diaCount ψ = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- imp, on ψ
    rename_i φ' ψ h_eq
    subst h_eq
    by_cases hb : WFF.binderPairDepth φ' = 0
    · by_cases hd : WFF.diaCount φ' = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- all → quant_arm
    rename_i x_a hx_a ψ h_eq
    subst h_eq
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- ex → quant_arm
    rename_i x_a hx_a ψ h_eq
    subst h_eq
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- box → box_arm
    rename_i V_inner ψ hsub h_no_extras h_eq
    subst h_eq
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- dia → dia_arm
    rename_i V_inner xv hxv ψ hsub h_no_extras h_eq
    subst h_eq
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide

end
