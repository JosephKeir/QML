import QML.QML_Full_v7

-- Σ'-refactor prototype: substitution block members return
-- {result // bpd result ≤ bound} so Case A .pair can recurse with the
-- first call's .property feeding the second call's termination.

-- Local copy of v7's private VarCtx_ext (invisible across imports).
private lemma VarCtx_ext (V W : VarCtx) (h : V.1 = W.1) : V = W := by
  obtain ⟨v, pv⟩ := V
  obtain ⟨w, pw⟩ := W
  subst h
  exact congrArg (PSigma.mk v) (proof_irrel pv pw)

mutual

def WFF_ctx_rest2 {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    {ψ' : WFF σ V // WFF.binderPairDepth ψ' ≤ WFF.binderPairDepth φ} := by
  match φ with
  | .atom R => exact ⟨.atom (Rel.ctx_rest hx h_pf s R), Nat.zero_le _⟩
  | .top => exact ⟨.top, Nat.zero_le _⟩
  | .bot => exact ⟨.bot, Nat.zero_le _⟩
  | .and φ' ψ =>
      let r1 := WFF_ctx_rest2 hx h_pf s φ'
      let r2 := WFF_ctx_rest2 hx h_pf s ψ
      exact ⟨.and r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .or φ' ψ =>
      let r1 := WFF_ctx_rest2 hx h_pf s φ'
      let r2 := WFF_ctx_rest2 hx h_pf s ψ
      exact ⟨.or r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .imp φ' ψ =>
      let r1 := WFF_ctx_rest2 hx h_pf s φ'
      let r2 := WFF_ctx_rest2 hx h_pf s ψ
      exact ⟨.imp r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .eq s' t =>
      exact ⟨.eq (Term.ctx_rest hx h_pf s s') (Term.ctx_rest hx h_pf s t),
             Nat.zero_le _⟩
  | @WFF.all _ _ x_a hx_a ψ =>
      let r := WFF_ctx_rest_quant_arm2 hx h_pf s false x_a hx_a ψ
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | @WFF.ex _ _ x_a hx_a ψ =>
      let r := WFF_ctx_rest_quant_arm2 hx h_pf s true x_a hx_a ψ
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | .box ψ hsub h_no_extras =>
      let r := WFF_ctx_rest_box_arm2 hx h_pf s ψ hsub h_no_extras
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | .dia xv hxv ψ hsub h_no_extras =>
      let r := WFF_ctx_rest_dia_arm2 hx h_pf s xv hxv ψ hsub h_no_extras
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq _ =>
      -- Unreachable: V_ext contains ⟨z, V1×V2⟩ via w2eq, but h_pf says
      -- V_ext.firstPairVar = none.  Contradiction.
      exfalso
      have h_z_in : (⟨z, v1.2.VTypeProd v2.2⟩ : VarSymb × VarType) ∈
          (VarCtx_insert ⟨x, S⟩ V hx).1 := by
        rw [← w2eq]; exact Finset.mem_insert_self _ _
      exact VarCtx.firstPairVar_none_no_pair h_pf h_z_in
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ,
                WFF.diaCount φ, WFF.numNodes φ, 1)
decreasing_by
  -- 10 recursive call sites — per-site bullets with `by_cases` on the
  -- "other" subformula's bpd (0 vs > 0) and dC (0 vs > 0) for and/or/imp;
  -- binder dispatches go directly to phase-strict.
  -- New 4-tuple structure: `(V_ext.pd + bpd, dC, numNodes, phase)`.
  -- Structural recursion cases: if bpd(other) > 0, new comp 1 strict; else if
  -- dC(other) > 0, comp 1 eq + comp 2 strict; else all comps eq, comp 3 strict.
  · -- 1. and on φ' (other = ψ)
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
  · -- 2. and on ψ (other = φ')
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
  · -- 3. or on φ' (other = ψ)
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
  · -- 4. or on ψ (other = φ')
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
  · -- 5. imp on φ' (other = ψ)
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
  · -- 6. imp on ψ (other = φ')
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
  · -- 7. all → quant_arm (comps 1, 2, 3 equal, phase strict)
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- 8. ex → quant_arm
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- 9. box → box_arm
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- 10. dia → dia_arm
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide

def WFF_ctx_rest_MU2 {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    {ψ' : WFF σ V // WFF.binderPairDepth ψ' ≤ WFF.binderPairDepth φ} := by
  match h_pv : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar with
  | none =>
      exact WFF_ctx_rest2 hx h_pv s φ
  | some ⟨(z, V1, V2), hzmem⟩ =>
      by_cases h_z_eq_x : z = x
      · -- Case A: z = x, so S = V1×V2.  Under the Σ' design the second
        -- recursive MU call's termination reads the FIRST call's bpd bound
        -- (h_r1_bpd, from result1.property + unpair/cast preservation) —
        -- this was the circularity that blocked the plain-return design.
        have h_S_eq : S = V1.VTypeProd V2 := by
          rcases Finset.mem_insert.mp hzmem with h_eq | h_in_V
          · exact ((Prod.mk.inj h_eq).2).symm
          · exfalso
            exact hx (Finset.mem_image.mpr ⟨_, h_in_V, h_z_eq_x⟩)
        have hVE_eq : VarCtx_insert ⟨x, S⟩ V hx =
                      VarCtx_insert ⟨x, V1.VTypeProd V2⟩ V hx := by
          apply VarCtx_ext
          change insert (⟨x, S⟩ : VarSymb × VarType) V.1
               = insert (⟨x, V1.VTypeProd V2⟩ : VarSymb × VarType) V.1
          rw [h_S_eq]
        let s_pair : Term σ V (V1.VTypeProd V2) := h_S_eq ▸ s
        let φ_pair : WFF σ (VarCtx_insert ⟨x, V1.VTypeProd V2⟩ V hx) :=
          hVE_eq ▸ φ
        match s_pair with
        | .pair s1 s2 =>
            let avoid : Finset VarSymb :=
              VarCtx_to_VarSymbs V ∪ {x} ∪ WFF.boundVars φ_pair
                ∪ Term.boundVars s1 ∪ Term.boundVars s2
            let v1 : VarSymb := VarSymb.fresh avoid
            have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem avoid
            let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
            have hv2_avoid_v1 : v2 ∉ insert v1 avoid :=
              VarSymb.fresh_not_mem (insert v1 avoid)
            have hv2_avoid : v2 ∉ avoid :=
              fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
            have hv1v2_ne : v1 ≠ v2 :=
              fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
            have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun y h =>
              Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
            have h_avoid_φ : WFF.boundVars φ_pair ⊆ avoid := fun y h =>
              Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_right _ h))
            have hv1_V : v1 ∉ VarCtx_to_VarSymbs V :=
              fun h => hv1_avoid (h_avoid_V h)
            have hv2_V : v2 ∉ VarCtx_to_VarSymbs V :=
              fun h => hv2_avoid (h_avoid_V h)
            have hv1_nb_φ : v1 ∉ WFF.boundVars φ_pair :=
              fun h => hv1_avoid (h_avoid_φ h)
            have hv2_nb_φ : v2 ∉ WFF.boundVars φ_pair :=
              fun h => hv2_avoid (h_avoid_φ h)
            -- Unpair φ_pair at x.
            let V_v1v2 : VarCtx :=
              VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1_V hv2_V hv1v2_ne
            let φ' : WFF σ V_v1v2 :=
              WFF.unpair x V1 V2 v1 v2 V _ V_v1v2
                hx hv1_V hv2_V hv1v2_ne rfl rfl φ_pair hv1_nb_φ hv2_nb_φ
            have hv2_V_only : v2 ∉ VarCtx_to_VarSymbs V := hv2_V
            have hv1_V_plus_v2 : v1 ∉ VarCtx_to_VarSymbs
                (VarCtx_insert ⟨v2, V2⟩ V hv2_V_only) :=
              not_mem_VarSymbs_insert hv1v2_ne hv1_V
            have h_V_v1v2_eq :
                V_v1v2 = VarCtx_insert ⟨v1, V1⟩
                  (VarCtx_insert ⟨v2, V2⟩ V hv2_V_only) hv1_V_plus_v2 := by
              apply VarCtx_ext; rfl
            let φ'_cast : WFF σ (VarCtx_insert ⟨v1, V1⟩
                (VarCtx_insert ⟨v2, V2⟩ V hv2_V_only) hv1_V_plus_v2) :=
              h_V_v1v2_eq ▸ φ'
            -- Weaken s1 : V → V + v2; substitute v1 ↦ s1_weakened.
            let s1_weakened : Term σ (VarCtx_insert ⟨v2, V2⟩ V hv2_V_only) V1 :=
              Term.ctx_ext ⟨v2, V2⟩ hv2_V_only s1
            have h_in_bpd : WFF.binderPairDepth φ'_cast
                = WFF.binderPairDepth φ := by
              simp only [φ'_cast, φ', φ_pair, WFF.binderPairDepth_ctx_cast,
                         WFF.binderPairDepth_unpair]
            let result1 := WFF_ctx_rest_MU2 hv1_V_plus_v2 s1_weakened φ'_cast
            have h_r1_bpd : WFF.binderPairDepth result1.val
                ≤ WFF.binderPairDepth φ :=
              le_trans result1.property (le_of_eq h_in_bpd)
            -- Substitute v2 ↦ s2.
            let result2 := WFF_ctx_rest_MU2 hv2_V_only s2 result1.val
            exact ⟨result2.val, le_trans result2.property h_r1_bpd⟩
        | @Term.pair_elim _ pe_V _ _ _ sv1 sv2 sz hsv1 hsv2 hsv1sv2 hsz
            sw1eq sw2eq sbody =>
            -- s is itself .pair_elim with binder sz: lock-step unpair φ and
            -- s at sz using fresh v1, v2; recurse; re-wrap WFF.pairElim.
            have hsz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                ∈ V.1 := by
              rw [← sw2eq]; exact Finset.mem_insert_self _ _
            let avoid : Finset VarSymb :=
              VarCtx_to_VarSymbs V ∪ {x} ∪ Term.boundVars s_pair
                ∪ WFF.boundVars φ_pair
            let v1 : VarSymb := VarSymb.fresh avoid
            have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem _
            let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
            have hv2_avoid_v1 : v2 ∉ insert v1 avoid := VarSymb.fresh_not_mem _
            have hv2_avoid : v2 ∉ avoid :=
              fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
            have hv1v2_ne : v1 ≠ v2 :=
              fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
            have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun y h =>
              Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ h))
            have h_avoid_x : x ∈ avoid :=
              Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)))
            have h_avoid_s : Term.boundVars s_pair ⊆ avoid := fun y h =>
              Finset.mem_union_left _ (Finset.mem_union_right _ h)
            have h_avoid_φ : WFF.boundVars φ_pair ⊆ avoid :=
              fun y h => Finset.mem_union_right _ h
            have hv1_V : v1 ∉ VarCtx_to_VarSymbs V :=
              fun h => hv1_avoid (h_avoid_V h)
            have hv2_V : v2 ∉ VarCtx_to_VarSymbs V :=
              fun h => hv2_avoid (h_avoid_V h)
            have hv1_x_ne : v1 ≠ x := fun h => hv1_avoid (h ▸ h_avoid_x)
            have hv2_x_ne : v2 ≠ x := fun h => hv2_avoid (h ▸ h_avoid_x)
            have hv1_nb_s : v1 ∉ Term.boundVars s_pair :=
              fun h => hv1_avoid (h_avoid_s h)
            have hv2_nb_s : v2 ∉ Term.boundVars s_pair :=
              fun h => hv2_avoid (h_avoid_s h)
            have hv1_nb_φ : v1 ∉ WFF.boundVars φ_pair :=
              fun h => hv1_avoid (h_avoid_φ h)
            have hv2_nb_φ : v2 ∉ WFF.boundVars φ_pair :=
              fun h => hv2_avoid (h_avoid_φ h)
            have h_peV_subset_V : VarCtx_to_VarSymbs pe_V ⊆
                VarCtx_to_VarSymbs V := fun y h => by
              obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h
              refine Finset.mem_image.mpr ⟨q, ?_, hq_eq⟩
              rw [← sw2eq]; exact Finset.mem_insert_of_mem hq_in
            have hv1_peV : v1 ∉ VarCtx_to_VarSymbs pe_V :=
              fun h => hv1_V (h_peV_subset_V h)
            have hv2_peV : v2 ∉ VarCtx_to_VarSymbs pe_V :=
              fun h => hv2_V (h_peV_subset_V h)
            -- Unpair s_pair at sz → s' in (pe_V + v1 + v2), type V1×V2.
            let peV_v1v2 : VarCtx :=
              VarCtx_insert_twice ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩ pe_V
                hv1_peV hv2_peV hv1v2_ne
            let s' : Term σ peV_v1v2 (V1.VTypeProd V2) :=
              Term.unpair sz sv1.2 sv2.2 v1 v2 pe_V _ peV_v1v2 _
                hsz hv1_peV hv2_peV hv1v2_ne sw2eq.symm rfl s_pair
                hv1_nb_s hv2_nb_s
            -- Unpair φ_pair at sz: first re-express its context as
            -- ((pe_V + ⟨x, V1×V2⟩) + sz).
            have hx_peV : x ∉ VarCtx_to_VarSymbs pe_V :=
              fun h => hx (h_peV_subset_V h)
            let peV_x : VarCtx := VarCtx_insert ⟨x, V1.VTypeProd V2⟩ pe_V hx_peV
            have hsz_ne_x : sz ≠ x := fun h =>
              hx (Finset.mem_image.mpr
                ⟨⟨sz, sv1.2.VTypeProd sv2.2⟩, hsz_in_V, h⟩)
            have hsz_peV_x : sz ∉ VarCtx_to_VarSymbs peV_x :=
              not_mem_VarSymbs_insert hsz_ne_x hsz
            have h_cast_φA :
                VarCtx_insert ⟨x, V1.VTypeProd V2⟩ V hx =
                VarCtx_insert ⟨sz, sv1.2.VTypeProd sv2.2⟩ peV_x hsz_peV_x := by
              apply VarCtx_ext
              change insert (⟨x, V1.VTypeProd V2⟩ : VarSymb × VarType) V.1 =
                   insert (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                     (insert ⟨x, V1.VTypeProd V2⟩ pe_V.1)
              rw [show V.1 = insert (⟨sz, sv1.2.VTypeProd sv2.2⟩ :
                              VarSymb × VarType) pe_V.1
                    from (congrArg PSigma.fst sw2eq).symm]
              exact Finset.insert_comm _ _ _
            let φ_castA : WFF σ (VarCtx_insert ⟨sz, sv1.2.VTypeProd sv2.2⟩
                peV_x hsz_peV_x) :=
              h_cast_φA ▸ φ_pair
            have hv1_peV_x : v1 ∉ VarCtx_to_VarSymbs peV_x :=
              not_mem_VarSymbs_insert hv1_x_ne hv1_peV
            have hv2_peV_x : v2 ∉ VarCtx_to_VarSymbs peV_x :=
              not_mem_VarSymbs_insert hv2_x_ne hv2_peV
            let peV_x_v1v2 : VarCtx :=
              VarCtx_insert_twice ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩ peV_x
                hv1_peV_x hv2_peV_x hv1v2_ne
            have hv1_nb_φ_castA : v1 ∉ WFF.boundVars φ_castA := by
              change v1 ∉ WFF.boundVars (h_cast_φA ▸ φ_pair)
              rw [WFF.boundVars_ctx_cast]; exact hv1_nb_φ
            have hv2_nb_φ_castA : v2 ∉ WFF.boundVars φ_castA := by
              change v2 ∉ WFF.boundVars (h_cast_φA ▸ φ_pair)
              rw [WFF.boundVars_ctx_cast]; exact hv2_nb_φ
            let φ'A : WFF σ peV_x_v1v2 :=
              WFF.unpair sz sv1.2 sv2.2 v1 v2 peV_x _ peV_x_v1v2
                hsz_peV_x hv1_peV_x hv2_peV_x hv1v2_ne rfl rfl φ_castA
                hv1_nb_φ_castA hv2_nb_φ_castA
            -- Re-arrange φ'A to (peV_v1v2 + ⟨x, V1×V2⟩) form.
            have hx_peV_v1v2 : x ∉ VarCtx_to_VarSymbs peV_v1v2 :=
              not_mem_VarSymbs_insert_twice
                (fun h => hv1_x_ne h.symm)
                (fun h => hv2_x_ne h.symm)
                hx_peV
            have h_cast_φ'A :
                peV_x_v1v2 = VarCtx_insert ⟨x, V1.VTypeProd V2⟩
                  peV_v1v2 hx_peV_v1v2 := by
              apply VarCtx_ext
              change insert (⟨v1, sv1.2⟩ : VarSymb × VarType)
                     (insert ⟨v2, sv2.2⟩ (insert ⟨x, V1.VTypeProd V2⟩ pe_V.1)) =
                   insert (⟨x, V1.VTypeProd V2⟩ : VarSymb × VarType)
                     (insert ⟨v1, sv1.2⟩ (insert ⟨v2, sv2.2⟩ pe_V.1))
              rw [Finset.insert_comm (⟨v2, sv2.2⟩ : VarSymb × VarType)
                  ⟨x, V1.VTypeProd V2⟩,
                  Finset.insert_comm (⟨v1, sv1.2⟩ : VarSymb × VarType)
                  ⟨x, V1.VTypeProd V2⟩]
            let φ'A_cast : WFF σ
                (VarCtx_insert ⟨x, V1.VTypeProd V2⟩ peV_v1v2 hx_peV_v1v2) :=
              h_cast_φ'A ▸ φ'A
            -- bpd of the recursion input equals bpd φ (hoisted for the
            -- decreasing bullet).
            have h_in_bpdA : WFF.binderPairDepth φ'A_cast
                = WFF.binderPairDepth φ := by
              simp only [φ'A_cast, φ'A, φ_castA, φ_pair,
                         WFF.binderPairDepth_ctx_cast,
                         WFF.binderPairDepth_unpair]
            -- comp-1 pd strictness (hoisted).
            have h_measure_lt : (V1.VTypeProd V2).pairDepth
                  + peV_v1v2.pairDepth
                < S.pairDepth + V.pairDepth := by
              have h_peV_erase : pe_V = VarCtx_erase V
                  ⟨sz, sv1.2.VTypeProd sv2.2⟩ := by
                apply VarCtx_ext
                change pe_V.1 = V.1.erase ⟨sz, sv1.2.VTypeProd sv2.2⟩
                rw [show V.1 = insert (⟨sz, sv1.2.VTypeProd sv2.2⟩ :
                                VarSymb × VarType) pe_V.1
                      from (congrArg PSigma.fst sw2eq).symm]
                exact (Finset.erase_insert
                  (fun h => hsz (Finset.mem_image.mpr ⟨_, h, rfl⟩))).symm
              have hv1_Vmsz : v1 ∉ VarCtx_to_VarSymbs
                  (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩) := by
                rw [← h_peV_erase]; exact hv1_peV
              have hv2_Vmsz : v2 ∉ VarCtx_to_VarSymbs
                  (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩) := by
                rw [← h_peV_erase]; exact hv2_peV
              have h_lt : (VarCtx_insert_twice ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩
                  (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩)
                  hv1_Vmsz hv2_Vmsz hv1v2_ne).pairDepth < V.pairDepth :=
                VarCtx.pairDepth_unpair_lt hsz_in_V hv1_Vmsz hv2_Vmsz hv1v2_ne
              have h_peV_v1v2_eq : peV_v1v2 =
                  VarCtx_insert_twice ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩
                    (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩)
                    hv1_Vmsz hv2_Vmsz hv1v2_ne := by
                apply VarCtx_ext
                change insert (⟨v1, sv1.2⟩ : VarSymb × VarType)
                    (insert ⟨v2, sv2.2⟩ pe_V.1)
                  = insert ⟨v1, sv1.2⟩ (insert ⟨v2, sv2.2⟩
                      (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩).1)
                rw [h_peV_erase]
              have hS_pd : S.pairDepth = 1 + V1.pairDepth + V2.pairDepth := by
                rw [h_S_eq]; rfl
              have hprod : (V1.VTypeProd V2).pairDepth
                  = 1 + V1.pairDepth + V2.pairDepth := rfl
              rw [h_peV_v1v2_eq]
              omega
            let result := WFF_ctx_rest_MU2 hx_peV_v1v2 s' φ'A_cast
            exact ⟨WFF.pairElim ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩ sz
                hv1_peV hv2_peV hv1v2_ne hsz rfl sw2eq result.val, by
              rw [WFF.binderPairDepth_pairElim_gen]
              exact le_trans result.property (le_of_eq h_in_bpdA)⟩
      · -- Case B: z ≠ x, so z ∈ V.  Pick fresh v1, v2; lock-step unpair
        -- Term.unpair s and WFF.unpair φ at z; recurse on smaller context.
        have hzmem_V : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1 := by
          rcases Finset.mem_insert.mp hzmem with h_eq | h_in_V
          · exact absurd (Prod.mk.inj h_eq).1 h_z_eq_x
          · exact h_in_V
        let V_minus_z := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩
        have hz_fresh : z ∉ VarCtx_to_VarSymbs V_minus_z :=
          VarCtx_erase_fresh hzmem_V
        have V_eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z hz_fresh = V :=
          VarCtx_insert_erase hzmem_V hz_fresh
        let avoid : Finset VarSymb :=
          VarCtx_to_VarSymbs V ∪ {x} ∪ Term.boundVars s ∪ WFF.boundVars φ
        let v1 : VarSymb := VarSymb.fresh avoid
        have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem avoid
        let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
        have hv2_avoid_v1 : v2 ∉ insert v1 avoid :=
          VarSymb.fresh_not_mem (insert v1 avoid)
        have hv2_avoid : v2 ∉ avoid :=
          fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
        have hv1v2_ne : v1 ≠ v2 :=
          fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
        have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun y h =>
          Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have h_avoid_φ : WFF.boundVars φ ⊆ avoid :=
          fun y h => Finset.mem_union_right _ h
        have h_avoid_s : Term.boundVars s ⊆ avoid := fun y h =>
          Finset.mem_union_left _ (Finset.mem_union_right _ h)
        have h_avoid_x : x ∈ avoid := Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_singleton.mpr rfl)))
        have hv1_V : v1 ∉ VarCtx_to_VarSymbs V := fun h => hv1_avoid (h_avoid_V h)
        have hv2_V : v2 ∉ VarCtx_to_VarSymbs V := fun h => hv2_avoid (h_avoid_V h)
        have hv1_Vmz : v1 ∉ VarCtx_to_VarSymbs V_minus_z := fun h =>
          hv1_V (VarCtx_to_VarSymbs_erase_subset h)
        have hv2_Vmz : v2 ∉ VarCtx_to_VarSymbs V_minus_z := fun h =>
          hv2_V (VarCtx_to_VarSymbs_erase_subset h)
        have hv1_x_ne : v1 ≠ x := fun h => hv1_avoid (h ▸ h_avoid_x)
        have hv2_x_ne : v2 ≠ x := fun h => hv2_avoid (h ▸ h_avoid_x)
        have hv1_nb_φ : v1 ∉ WFF.boundVars φ := fun h => hv1_avoid (h_avoid_φ h)
        have hv2_nb_φ : v2 ∉ WFF.boundVars φ := fun h => hv2_avoid (h_avoid_φ h)
        have hv1_nb_s : v1 ∉ Term.boundVars s := fun h => hv1_avoid (h_avoid_s h)
        have hv2_nb_s : v2 ∉ Term.boundVars s := fun h => hv2_avoid (h_avoid_s h)
        have hx_Vmz : x ∉ VarCtx_to_VarSymbs V_minus_z :=
          fun h => hx (VarCtx_to_VarSymbs_erase_subset h)
        let V_minus_z_x : VarCtx := VarCtx_insert ⟨x, S⟩ V_minus_z hx_Vmz
        have hz_Vmz_x : z ∉ VarCtx_to_VarSymbs V_minus_z_x :=
          not_mem_VarSymbs_insert h_z_eq_x hz_fresh
        have h_cast_φ :
            VarCtx_insert ⟨x, S⟩ V hx =
            VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z_x hz_Vmz_x := by
          apply VarCtx_ext
          change insert (⟨x, S⟩ : VarSymb × VarType) V.1 =
               insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
                 (insert ⟨x, S⟩ V_minus_z.1)
          rw [show V.1 = insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) V_minus_z.1
                from (Finset.insert_erase hzmem_V).symm]
          exact Finset.insert_comm _ _ _
        let φ_cast :
            WFF σ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z_x hz_Vmz_x) :=
          h_cast_φ ▸ φ
        have hv1_Vmz_x : v1 ∉ VarCtx_to_VarSymbs V_minus_z_x :=
          not_mem_VarSymbs_insert hv1_x_ne hv1_Vmz
        have hv2_Vmz_x : v2 ∉ VarCtx_to_VarSymbs V_minus_z_x :=
          not_mem_VarSymbs_insert hv2_x_ne hv2_Vmz
        let V_minus_z_x_v1v2 : VarCtx :=
          VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_minus_z_x hv1_Vmz_x hv2_Vmz_x hv1v2_ne
        have hv1_nb_φ_cast : v1 ∉ WFF.boundVars φ_cast := by
          change v1 ∉ WFF.boundVars (h_cast_φ ▸ φ)
          rw [WFF.boundVars_ctx_cast]; exact hv1_nb_φ
        have hv2_nb_φ_cast : v2 ∉ WFF.boundVars φ_cast := by
          change v2 ∉ WFF.boundVars (h_cast_φ ▸ φ)
          rw [WFF.boundVars_ctx_cast]; exact hv2_nb_φ
        let φ' : WFF σ V_minus_z_x_v1v2 :=
          WFF.unpair z V1 V2 v1 v2 V_minus_z_x _ V_minus_z_x_v1v2
            hz_Vmz_x hv1_Vmz_x hv2_Vmz_x hv1v2_ne rfl rfl φ_cast
            hv1_nb_φ_cast hv2_nb_φ_cast
        let V_minus_z_v1v2 : VarCtx :=
          VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne
        let s' : Term σ V_minus_z_v1v2 S :=
          Term.unpair z V1 V2 v1 v2 V_minus_z V V_minus_z_v1v2 S
            hz_fresh hv1_Vmz hv2_Vmz hv1v2_ne V_eq.symm rfl s hv1_nb_s hv2_nb_s
        have hx_Vmz_v1v2 : x ∉ VarCtx_to_VarSymbs V_minus_z_v1v2 :=
          not_mem_VarSymbs_insert_twice
            (fun h => hv1_x_ne h.symm)
            (fun h => hv2_x_ne h.symm)
            hx_Vmz
        have h_cast_φ' :
            V_minus_z_x_v1v2 =
            VarCtx_insert ⟨x, S⟩ V_minus_z_v1v2 hx_Vmz_v1v2 := by
          apply VarCtx_ext
          change insert (⟨v1, V1⟩ : VarSymb × VarType)
                 (insert ⟨v2, V2⟩ (insert ⟨x, S⟩ V_minus_z.1)) =
               insert ⟨x, S⟩
                 (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ V_minus_z.1))
          rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) ⟨x, S⟩,
              Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) ⟨x, S⟩]
        let φ'_cast : WFF σ (VarCtx_insert ⟨x, S⟩ V_minus_z_v1v2 hx_Vmz_v1v2) :=
          h_cast_φ' ▸ φ'
        let result := WFF_ctx_rest_MU2 hx_Vmz_v1v2 s' φ'_cast
        exact ⟨V_eq ▸ WFF.pairElim ⟨v1, V1⟩ ⟨v2, V2⟩ z
                 hv1_Vmz hv2_Vmz hv1v2_ne hz_fresh rfl rfl result.val, by
          simp only [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_pairElim]
          refine le_trans result.property ?_
          simp only [φ'_cast, φ', φ_cast, WFF.binderPairDepth_ctx_cast,
                     WFF.binderPairDepth_unpair]
          exact le_refl _⟩
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ,
                WFF.diaCount φ, WFF.numNodes φ, 2)
decreasing_by
  · -- None branch: delegate to ctx_rest.  4-tuple: comp 1, 2, 3 equal; phase strict.
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt
    right; refine ⟨rfl, ?_⟩
    right; refine ⟨rfl, ?_⟩
    right; exact ⟨rfl, by decide⟩
  · -- Case A, first MU call: comp 1 strict — V_ext.pd drops by 1 + V1.pd
    -- (S = V1×V2 opened to v1:V1, v2:V2) while bpd is preserved by
    -- unpair/casts.
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    simp only [VarCtx.pairDepth_insert]
    have hS_pd : S.pairDepth = 1 + V1.pairDepth + V2.pairDepth := by
      rw [h_S_eq]; rfl
    change V1.pairDepth + (V2.pairDepth + V.pairDepth)
             + WFF.binderPairDepth φ'_cast
         < S.pairDepth + V.pairDepth + WFF.binderPairDepth φ
    omega
  · -- Case A, second MU call: comp 1 strict — V_ext.pd drops by 1 + V1.pd
    -- and bpd(result1.val) ≤ bpd φ via h_r1_bpd (the Σ' payoff).
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    simp only [VarCtx.pairDepth_insert]
    have hS_pd : S.pairDepth = 1 + V1.pairDepth + V2.pairDepth := by
      rw [h_S_eq]; rfl
    change V2.pairDepth + V.pairDepth + WFF.binderPairDepth result1.val
         < S.pairDepth + V.pairDepth + WFF.binderPairDepth φ
    omega
  · -- Case A .pair_elim MU call: comp 1 strict via h_measure_lt (hoisted
    -- pd arithmetic) + h_in_bpdA (bpd preserved through unpair/casts).
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    simp only [VarCtx.pairDepth_insert]
    change (V1.VTypeProd V2).pairDepth + peV_v1v2.pairDepth
             + WFF.binderPairDepth φ'A_cast
         < S.pairDepth + V.pairDepth + WFF.binderPairDepth φ
    omega
  · -- Case B MU call: comp 1 (V_ext.pd + bpd) strict via unpair_lt + bpd
    -- preserved.  4-tuple structure: use `left` at the outer.
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    have h_pd_lt : V_minus_z_v1v2.pairDepth < V.pairDepth :=
      VarCtx.pairDepth_unpair_lt hzmem_V hv1_Vmz hv2_Vmz hv1v2_ne
    have h_bpd_eq :
        WFF.binderPairDepth φ'_cast = WFF.binderPairDepth φ := by
      show WFF.binderPairDepth (h_cast_φ' ▸ φ') = _
      rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_unpair,
          WFF.binderPairDepth_ctx_cast]
    rw [VarCtx.pairDepth_insert, VarCtx.pairDepth_insert]
    show (⟨x, S⟩ : VarSymb × VarType).2.pairDepth + V_minus_z_v1v2.pairDepth
           + WFF.binderPairDepth φ'_cast
         < (⟨x, S⟩ : VarSymb × VarType).2.pairDepth + V.pairDepth
           + WFF.binderPairDepth φ
    rw [h_bpd_eq]
    omega

-- Helper for `WFF.ctx_rest`'s `.all`/`.ex` arms.
def WFF_ctx_rest_quant_arm2 {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (_h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (is_ex : Bool)
    (x_a : VarSymb × VarType)
    (hx_a : x_a.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨x, S⟩ V hx))
    (ψ : WFF σ (VarCtx_insert x_a (VarCtx_insert ⟨x, S⟩ V hx) hx_a))
    : {res : WFF σ V // WFF.binderPairDepth res
         ≤ x_a.2.pairDepth + WFF.binderPairDepth ψ} := by
  have hxa_V : x_a.1 ∉ VarCtx_to_VarSymbs V := by
    intro h; apply hx_a
    rw [VarCtx_to_VarSymbs_insert]
    exact Finset.mem_insert_of_mem h
  have hxa_ne_x : x_a.1 ≠ x := by
    intro heq; apply hx_a
    rw [VarCtx_to_VarSymbs_insert]
    exact Finset.mem_insert.mpr (Or.inl heq)
  have hx_xaV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert x_a V hxa_V) :=
    not_mem_VarSymbs_insert (fun h => hxa_ne_x h.symm) hx
  have h_ψ_ctx :
      VarCtx_insert x_a (VarCtx_insert ⟨x, S⟩ V hx) hx_a =
      VarCtx_insert ⟨x, S⟩ (VarCtx_insert x_a V hxa_V) hx_xaV :=
    VarCtx_ext _ _ (Finset.insert_comm _ _ _)
  let result := WFF_ctx_rest_MU2 hx_xaV (Term.ctx_ext x_a hxa_V s) (h_ψ_ctx ▸ ψ)
  refine ⟨bif is_ex then .ex x_a (hx := hxa_V) result.val
                    else .all x_a (hx := hxa_V) result.val, ?_⟩
  cases is_ex
  · simp only [Bool.cond_false, WFF.binderPairDepth]
    refine Nat.add_le_add_left ?_ _
    refine le_trans result.property ?_
    rw [WFF.binderPairDepth_ctx_cast]
  · simp only [Bool.cond_true, WFF.binderPairDepth]
    refine Nat.add_le_add_left ?_ _
    refine le_trans result.property ?_
    rw [WFF.binderPairDepth_ctx_cast]
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + x_a.2.pairDepth
                  + WFF.binderPairDepth ψ,
                WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  -- quant_arm → MU: comp 1 (V_ext.pd + bpd) equal, comp 2 (dC) equal, comp 3
  -- (numNodes) strict.  4-tuple structure.
  all_goals (
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt
    right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth_ctx_cast, VarCtx.pairDepth_insert]; omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount_ctx_cast]
      · left; simp only [WFF.numNodes_ctx_cast]; omega)

-- Helper for `WFF.ctx_rest`'s `.box` arm.  Mirrors `Term.ctx_rest`'s
-- `.boxterm` arm: case-analyse on whether x ∈ V_inner.  If yes, force
-- S = T.VTypeBox, match s as `.boxterm`, recurse via WFF_ctx_rest_MU2
-- on ψ at the smaller V_inner_minus_x context.  If no, trivial passthrough.
def WFF_ctx_rest_box_arm2 {σ : Signature} {V : VarCtx} {V_inner : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (ψ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (h_no_extras : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
                   VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    : {res : WFF σ V // WFF.binderPairDepth res ≤ WFF.binderPairDepth ψ} := by
  by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
  · -- x ∈ V_inner: forces S = T.VTypeBox.  Match s as `.boxterm`; recurse.
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
    | VTypeDia _ =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeProd _ _ =>
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
        by_cases hxT_in : (⟨x, T⟩ : VarSymb × VarType) ∈ V_inner.1
        · let V_inner_minus_x : VarCtx := VarCtx_erase V_inner ⟨x, T⟩
          have hx_minus : x ∉ VarCtx_to_VarSymbs V_inner_minus_x :=
            VarCtx_erase_fresh hxT_in
          have h_V_inner_eq :
              V_inner = VarCtx_insert ⟨x, T⟩ V_inner_minus_x hx_minus :=
            (VarCtx_insert_erase hxT_in hx_minus).symm
          match s with
          | @Term.boxterm _ V_s _ _ s_inner s_hsub s_h_no_extras =>
              have h_V_eq : V_s = V_inner_minus_x :=
                ctx_rest_box_V_s_eq hxT_in hsub h_no_extras
                  s_hsub s_h_no_extras
              subst h_V_eq
              let ψ_cast : WFF σ
                  (VarCtx_insert ⟨x, T⟩ V_inner_minus_x hx_minus) :=
                h_V_inner_eq ▸ ψ
              let ψ_new := WFF_ctx_rest_MU2 hx_minus s_inner ψ_cast
              exact ⟨.box ψ_new.val s_hsub s_h_no_extras, by
                refine le_trans ψ_new.property ?_
                simp only [ψ_cast, WFF.binderPairDepth_ctx_cast]
                exact le_refl _⟩
          | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
              exfalso
              have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                  ∈ V.1 := by
                rw [← sw2eq]; exact Finset.mem_insert_self _ _
              have h_sz_in_Vext :
                  (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈
                  (VarCtx_insert ⟨x, T.VTypeBox⟩ V hx).1 :=
                Finset.mem_insert_of_mem h_sz_in_V
              exact VarCtx.firstPairVar_none_no_pair h_pf h_sz_in_Vext
        · exfalso
          obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
          simp only at hx'_eq; subst hx'_eq
          have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
          rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
          · have : T'.VTypeBox = T.VTypeBox := (Prod.mk.inj h_eq).2
            have hT_eq : T' = T := VarType.VTypeBox.inj this
            subst hT_eq
            exact hxT_in hx'T'
          · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
  · -- x ∉ V_inner: trivial passthrough.
    have hsub' : (VarCtx_box V_inner).1 ⊆ V.1 := by
      intro p hp
      rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
      · subst h_eq
        exfalso
        rcases Finset.mem_image.mp hp with ⟨w, hw, hweq⟩
        exact h_x_in
          (Finset.mem_image.mpr ⟨w, hw, (Prod.mk.inj hweq).1⟩)
      · exact h_V
    have h_no_extras' :
        ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1 :=
      fun p hp h_box => h_no_extras p (Finset.mem_insert_of_mem hp) h_box
    exact ⟨.box ψ hsub' h_no_extras', Nat.le_refl _⟩
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth ψ,
                WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  -- box_arm Case 2 → MU: comp 1 ≥ (by hsub), comp 3 (numNodes) STRICT when equal.
  -- 4-tuple: (V_ext.pd + bpd, dC, numNodes, phase).
  all_goals (
    have hS_eq : S = T.VTypeBox := ‹S = T.VTypeBox›
    subst hS_eq
    have h_le := VarCtx.pairDepth_le_of_box_subset hsub
    have h_V_inner_pd : V_inner.pairDepth =
        T.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := by
      conv_lhs => rw [h_V_inner_eq]
      exact VarCtx.pairDepth_insert _ _ _
    have h_v_min_unfold :
        V_inner_minus_x.pairDepth = (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := rfl
    have h_ext_pd : (VarCtx_insert ⟨x, T.VTypeBox⟩ V hx).pairDepth
                    = T.pairDepth + V.pairDepth := by
      rw [VarCtx.pairDepth_insert]
      rfl
    have h_key : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth ≤ V.pairDepth := by
      rw [h_ext_pd] at h_le
      omega
    by_cases h_lt : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth < V.pairDepth
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
      show T.pairDepth + _ + _ < T.pairDepth + _ + _
      omega
    · have h_eq : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth = V.pairDepth := by omega
      apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
      refine ⟨?_, ?_⟩
      · simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
        show T.pairDepth + _ + _ = T.pairDepth + _ + _
        omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.diaCount_ctx_cast]
        · left; simp only [WFF.numNodes_ctx_cast]; omega)

-- Helper for `WFF.ctx_rest`'s `.dia` arm.  Mirrors `Term.ctx_rest`'s
-- `.diaterm` arm.  Three cases:
--   1. xv.1 = x: modal beta (TODO: currently stub).
--   2. xv.1 ≠ x AND x ∈ V_inner: recurse into ψ via MU after lifting s.
--   3. xv.1 ≠ x AND x ∉ V_inner: trivial passthrough.
def WFF_ctx_rest_dia_arm2 {σ : Signature} {V : VarCtx} {V_inner : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (h_no_extras : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
                   VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    : {res : WFF σ V // WFF.binderPairDepth res ≤ WFF.binderPairDepth ψ} := by
  by_cases h_xv_eq_x : xv.1 = x
  · -- Case 3: xv.1 = x. Modal-beta reduction. Step 0-1: uniqueness + destructure s.
    have hxv_in_Vext : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈
        (VarCtx_insert ⟨x, S⟩ V hx).1 := by
      apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
    have h_S_eq : S = xv.2.VTypeDia := by
      rcases Finset.mem_insert.mp hxv_in_Vext with h_eq | h_in_V
      · exact ((Prod.mk.inj h_eq).2).symm
      · exfalso
        exact hx (Finset.mem_image.mpr ⟨_, h_in_V, h_xv_eq_x⟩)
    let s_dia : Term σ V xv.2.VTypeDia := h_S_eq ▸ s
    match s_dia with
    | @Term.diaterm _ V_inner_s _ _ xv_s hxv_s tt_s hsub_s h_no_extras_s =>
        -- Step 2: V_inner_s = V_inner via VarCtx_box_inj + no-extras.
        have h_V_inner_eq : V_inner_s = V_inner := by
          apply VarCtx_box_inj
          apply VarCtx_ext
          apply Finset.ext
          intro p
          constructor
          · intro hp_s
            have hp_V : p ∈ V.1 := by
              apply hsub_s
              rw [VarCtx_dia_fst]
              exact Finset.mem_insert_of_mem hp_s
            have hp_box : VarType.isBox p.2 = true := by
              rcases Finset.mem_image.mp hp_s with ⟨q, _, hq_eq⟩
              rw [← hq_eq]; simp [VarType.isBox]
            have hp_Vext : p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1 :=
              Finset.mem_insert_of_mem hp_V
            have hp_dia := h_no_extras p hp_Vext hp_box
            rw [VarCtx_dia_fst] at hp_dia
            rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
            · subst h_eq; simp [VarType.isBox] at hp_box
            · exact h_in_box
          · intro hp
            have hp_Vext : p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1 := by
              apply hsub
              rw [VarCtx_dia_fst]
              exact Finset.mem_insert_of_mem hp
            have hp_box : VarType.isBox p.2 = true := by
              rcases Finset.mem_image.mp hp with ⟨q, _, hq_eq⟩
              rw [← hq_eq]; simp [VarType.isBox]
            have hp_V : p ∈ V.1 := by
              rcases Finset.mem_insert.mp hp_Vext with h_eq | h_V
              · subst h_eq
                rw [h_S_eq] at hp_box
                simp [VarType.isBox] at hp_box
              · exact h_V
            have hp_dia := h_no_extras_s p hp_V hp_box
            rw [VarCtx_dia_fst] at hp_dia
            rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
            · subst h_eq; simp [VarType.isBox] at hp_box
            · exact h_in_box
        cases h_V_inner_eq
        -- Step 3: derive xv_s.1 ≠ x, i.e., xv.1 ≠ xv_s.1.
        have hxv_s_ne_x : xv_s.1 ≠ x := by
          intro h
          apply hx
          apply Finset.mem_image.mpr
          refine ⟨⟨xv_s.1, xv_s.2.VTypeDia⟩, ?_, h⟩
          apply hsub_s
          rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        have h_xv_ne_xv_s : xv.1 ≠ xv_s.1 :=
          fun h => hxv_s_ne_x (h ▸ h_xv_eq_x)
        -- Step 4: use reorder helper to produce ψ_for_sub in the target context.
        obtain ⟨h_x_inner, ψ_for_sub, h_bpd_eq, h_dC_eq⟩ :=
          WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s h_xv_ne_xv_s h_xv_eq_x ψ
        -- Step 5: recursive MU substitution at x with witness tt_s.
        let result_sub := WFF_ctx_rest_MU2 h_x_inner tt_s ψ_for_sub
        -- Step 6: wrap in .dia xv_s producing WFF σ V via hsub_s / h_no_extras_s.
        exact ⟨.dia xv_s hxv_s result_sub.val hsub_s h_no_extras_s, by
          refine le_trans result_sub.property ?_
          exact le_of_eq h_bpd_eq⟩
    | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
        exfalso
        have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
            ∈ V.1 := by
          rw [← sw2eq]; exact Finset.mem_insert_self _ _
        exact VarCtx.firstPairVar_none_no_pair h_pf
          (Finset.mem_insert_of_mem h_sz_in_V)
  · by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
    · -- Case 2: xv.1 ≠ x AND x ∈ V_inner.  Mirrors box arm with hxv lift.
      cases S with
      | Var | VTypeOne | VTypeDia _ | VTypeProd _ _ =>
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
          all_goals first
            | exact VarType.noConfusion (Prod.mk.inj h_eq).2
            | exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
      | VTypeBox T =>
          by_cases hxT_in : (⟨x, T⟩ : VarSymb × VarType) ∈ V_inner.1
          · let V_inner_minus_x : VarCtx := VarCtx_erase V_inner ⟨x, T⟩
            have hx_minus : x ∉ VarCtx_to_VarSymbs V_inner_minus_x :=
              VarCtx_erase_fresh hxT_in
            have hxv_minus : xv.1 ∉ VarCtx_to_VarSymbs V_inner_minus_x :=
              fun h => hxv (VarCtx_to_VarSymbs_erase_subset h)
            match s with
            | @Term.boxterm _ V_s _ _ s_inner s_hsub s_h_no_extras =>
                have h_V_eq : V_s = V_inner_minus_x :=
                  ctx_rest_dia_V_s_eq hxT_in hsub h_no_extras s_hsub
                    s_h_no_extras
                subst h_V_eq
                let s_lifted :
                    Term σ (VarCtx_insert xv V_inner_minus_x hxv_minus) T :=
                  Term.ctx_ext xv hxv_minus s_inner
                have hx_in_outer :
                    x ∉ VarCtx_to_VarSymbs
                          (VarCtx_insert xv V_inner_minus_x hxv_minus) :=
                  not_mem_VarSymbs_insert
                    (fun h => h_xv_eq_x h.symm) hx_minus
                have h_combined :
                    VarCtx_insert xv V_inner hxv =
                    VarCtx_insert ⟨x, T⟩
                      (VarCtx_insert xv V_inner_minus_x hxv_minus)
                      hx_in_outer := by
                  apply VarCtx_ext
                  change insert xv V_inner.1 =
                       insert ⟨x, T⟩ (insert xv V_inner_minus_x.1)
                  rw [Finset.insert_comm]
                  congr 1
                  show V_inner.1 = insert ⟨x, T⟩ V_inner_minus_x.1
                  exact (Finset.insert_erase hxT_in).symm
                let ψ_cast : WFF σ
                    (VarCtx_insert ⟨x, T⟩
                      (VarCtx_insert xv V_inner_minus_x hxv_minus)
                      hx_in_outer) :=
                  h_combined ▸ ψ
                let ψ_new := WFF_ctx_rest_MU2 hx_in_outer s_lifted ψ_cast
                exact ⟨.dia xv hxv_minus ψ_new.val
                  (ctx_rest_dia_hsub_erase hxv_minus
                    (fun h => h_xv_eq_x h) hsub)
                  (ctx_rest_dia_h_no_extras_erase hxv_minus h_no_extras), by
                  refine le_trans ψ_new.property ?_
                  simp only [ψ_cast, WFF.binderPairDepth_ctx_cast]
                  exact le_refl _⟩
            | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
                exfalso
                have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                    ∈ V.1 := by
                  rw [← sw2eq]; exact Finset.mem_insert_self _ _
                have h_sz_in_Vext :
                    (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈
                    (VarCtx_insert ⟨x, T.VTypeBox⟩ V hx).1 :=
                  Finset.mem_insert_of_mem h_sz_in_V
                exact VarCtx.firstPairVar_none_no_pair h_pf h_sz_in_Vext
          · exfalso
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
    · -- Case 1: xv.1 ≠ x AND x ∉ V_inner.  Trivial passthrough.
      have hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1 := by
        rw [VarCtx_dia_fst]
        intro p hp
        rcases Finset.mem_insert.mp hp with h_eq | hp_box
        · subst h_eq
          have hp_in_dia : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈
                            (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
          rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq' | h_in_V
          · exact absurd (Prod.mk.inj h_eq').1 h_xv_eq_x
          · exact h_in_V
        · have hp_in_dia : p ∈ (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_box
          rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq | h_in_V
          · subst h_eq
            exfalso
            apply h_x_in
            rcases Finset.mem_image.mp hp_box with ⟨q, hq_in, hq_eq⟩
            cases q with
            | mk qv qT =>
              refine Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, ?_⟩
              exact (Prod.mk.inj hq_eq).1
          · exact h_in_V
      have h_no_extras' :
          ∀ p ∈ V.1, VarType.isBox p.2 = true →
            p ∈ (VarCtx_dia xv V_inner hxv).1 :=
        fun p hp h_box => h_no_extras p (Finset.mem_insert_of_mem hp) h_box
      exact ⟨.dia xv hxv ψ hsub' h_no_extras', Nat.le_refl _⟩
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth ψ,
                1 + WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  -- dia_arm two recursive MU goals.  Since bpd's `.dia` clause no longer
  -- adds the binder's pairDepth, the measure drops its xv.2.pairDepth term
  -- (comp 1 = V_ext.pd + bpd ψ); comp 2 keeps the 1 + dC ψ gap.
  --  * Case 2 (S = T.VTypeBox): comp 1 ≤ via dia-subset; comp 2 STRICT via +1.
  --  * Case 3 (modal beta): comp 1 ≤ via dia-subset; comp 2 STRICT via +1.
  all_goals first
    | (-- Case 2
       have hS_eq : S = T.VTypeBox := by assumption
       subst hS_eq
       have h_le := VarCtx.pairDepth_le_of_dia_subset hsub
       have h_V_inner_pd : V_inner.pairDepth =
           T.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := by
         conv_lhs => rw [show V_inner = VarCtx_insert ⟨x, T⟩
           (VarCtx_erase V_inner ⟨x, T⟩) hx_minus from
           (VarCtx_insert_erase hxT_in hx_minus).symm]
         exact VarCtx.pairDepth_insert _ _ _
       have h_v_min_unfold :
           V_inner_minus_x.pairDepth = (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := rfl
       have h_ext_pd : (VarCtx_insert ⟨x, T.VTypeBox⟩ V hx).pairDepth
                       = T.pairDepth + V.pairDepth := by
         rw [VarCtx.pairDepth_insert]
         rfl
       have h_le' : (VarCtx_insert xv V_inner hxv).pairDepth
                     ≤ T.pairDepth + V.pairDepth := by
         rw [h_ext_pd] at h_le; exact h_le
       have h_insert_xv_pd :
           (VarCtx_insert xv V_inner hxv).pairDepth
             = xv.2.pairDepth + V_inner.pairDepth :=
         VarCtx.pairDepth_insert _ _ _
       have h_key : xv.2.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth
                     ≤ V.pairDepth := by
         rw [h_insert_xv_pd, h_V_inner_pd] at h_le'
         omega
       -- comp 1: new = T.pd + (xv.2.pd + V_inner_minus_x.pd) + bpd ψ_cast;
       -- outer = T.pd + V.pd + bpd ψ.  Diff ≥ 0 via h_key.
       -- Split into new < outer (comp 1 strict) vs new = outer (comp 2 strict).
       by_cases h_c1_lt :
           xv.2.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth
             < V.pairDepth
       · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
         simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
         show T.pairDepth + _ + _ < T.pairDepth + _ + _
         omega
       · have h_c1_eq :
             xv.2.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth
               = V.pairDepth := by omega
         apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
         refine ⟨?_, ?_⟩
         · simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
           show T.pairDepth + _ + _ = T.pairDepth + _ + _
           omega
         · left; simp only [WFF.diaCount_ctx_cast]; omega)
    | (-- Case 3 (modal beta): MU call on ψ_for_sub / tt_s from reorder helper.
       have hS_eq : S = xv.2.VTypeDia := by assumption
       subst hS_eq
       have h_le := VarCtx.pairDepth_le_of_dia_subset hsub_s
       have h_le' : xv_s.2.pairDepth + V_inner.pairDepth ≤ V.pairDepth := by
         rw [VarCtx.pairDepth_insert] at h_le; exact h_le
       have h_VTypeDia_pd : xv.2.VTypeDia.pairDepth = xv.2.pairDepth := rfl
       -- comp 1: new = xv.2.pd + xv_s.2.pd + V_inner.pd + bpd (via h_bpd_eq)
       -- outer = xv.2.VTypeDia.pd + V.pd + bpd = xv.2.pd + V.pd + bpd.
       -- Diff = V.pd - xv_s.2.pd - V_inner.pd ≥ 0 via h_le'.
       -- comp 2: new = dC ψ_for_sub = dC ψ (via h_dC_eq); outer = 1 + dC ψ.  Strict.
       by_cases h_c1_lt :
           xv_s.2.pairDepth + V_inner.pairDepth < V.pairDepth
       · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
         simp only [VarCtx.pairDepth_insert, h_VTypeDia_pd, h_bpd_eq]
         omega
       · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
         refine ⟨?_, ?_⟩
         · simp only [VarCtx.pairDepth_insert, h_VTypeDia_pd, h_bpd_eq]
           omega
         · left; simp only [h_dC_eq]; omega)

end
