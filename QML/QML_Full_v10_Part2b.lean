import QML.QML_Full_v10_Part2a

/-!
# QML v10 — Part 2b

Continuation of `QML_Full_v10_Part2a`.  Part 2 was split in two because the combined file
was over this machine's build limit: it compiled only intermittently, crashing with a bare
access violation (exit 3221225477 / SIGSEGV) that was independent of content — the same
wall that prompted the original v9 → Part1/Part2 split.  `QML_Full_v10_Part1` (4628 lines)
rebuilds reliably, so the parts are sized against that.

The seam is the top-level `Unpair` section boundary: it crosses no `mutual` block, and the
`ctx_ext` family (whose `mutual` ends just above) is complete in Part 2a.

Part 2a: `Rel`, the `WFF` inductive, bound-variable/measure functions, `WFF.rename` and its
invariance lemmas, `WFF.pairElim`, and the `WFF.ctx_ext` family.

Part 2b (this file): `WFF.unpair`, `WFF.ctx_rest` / `ctx_rest_MU`, the public substitution API,
the modal context-bridging lemmas, and the `Proof` inductive.
-/

/-! ### Unpair -/

-- Translate a WFF from a "joined" context `W₁ = V + ⟨z, V1×V2⟩` to a "split"
-- Case A helper for `WFF.unpair`'s `.pair_elim` arm.  Mirrors
-- `Term.unpair_pe_caseA`: extracts the `subst z'` / `subst pe_V` / `obtain
-- ⟨rfl, rfl⟩` chain into a standalone function so that `WFF.unpair` itself
-- remains eq-lemma-compatible.
def WFF.unpair_pe_caseA {σ : Signature}
    (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
    (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (pe_V pe_W₁ : VarCtx)
    (v₁ v₂ : VarSymb × VarType) (z' : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs pe_V)
    (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs pe_V)
    (hv₁v₂_inner : v₁.1 ≠ v₂.1)
    (hz' : z' ∉ VarCtx_to_VarSymbs pe_V)
    (w₁_eq : VarCtx_insert_twice v₁ v₂ pe_V hv₁ hv₂ hv₁v₂_inner = pe_W₁)
    (w₂_eq : VarCtx_insert ⟨z', v₁.2.VTypeProd v₂.2⟩ pe_V hz' = W₁)
    (inner_wff : WFF σ pe_W₁)
    (h_v1_nb_inner : v1 ∉ WFF.boundVars inner_wff)
    (h_v2_nb_inner : v2 ∉ WFF.boundVars inner_wff)
    (_h1 : v1 ∉ (insert v₁.1 (insert v₂.1 (insert z' (WFF.boundVars inner_wff)))))
    (_h2 : v2 ∉ (insert v₁.1 (insert v₂.1 (insert z' (WFF.boundVars inner_wff)))))
    (h_case : (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩)
    : { t : WFF σ W₂ // WFF.diaCount t = WFF.diaCount inner_wff ∧
                         WFF.binderPairDepth t = WFF.binderPairDepth inner_wff } := by
  have h_z'_eq : z' = z := congrArg Prod.fst h_case
  have h_type_eq : (VarType.VTypeProd v₁.2 v₂.2) = V1.VTypeProd V2 :=
    congrArg Prod.snd h_case
  subst z'
  obtain ⟨rfl, rfl⟩ := VarType.VTypeProd.inj h_type_eq
  have h_pe_V_eq_V : pe_V = V := by
    apply VarCtx_ext
    have h_W_eq : insert (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) pe_V.1
               = insert ⟨z, v₁.2.VTypeProd v₂.2⟩ V.1 :=
      congrArg PSigma.fst (w₂_eq.trans W₁def)
    have h_not_in_pe : (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∉ pe_V.1 :=
      fun h => hz' (Finset.mem_image.mpr ⟨_, h, rfl⟩)
    have h_not_in_V : (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∉ V.1 :=
      fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
    change pe_V.1 = V.1
    rw [← Finset.erase_insert h_not_in_pe, h_W_eq, Finset.erase_insert h_not_in_V]
  subst pe_V
  have h_v1_ne_v₂_1 : v1 ≠ v₂.1 := fun heq =>
    _h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
  have h_v2_ne_v₁_1 : v2 ≠ v₁.1 := fun heq =>
    _h2 (Finset.mem_insert.mpr (Or.inl heq))
  have h_v1_fresh_in_iv₂ :
      v1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂) :=
    not_mem_VarSymbs_insert h_v1_ne_v₂_1 hv1
  have h_v₁1_fresh_in_iv₂ :
      v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂) :=
    not_mem_VarSymbs_insert hv₁v₂_inner hv₁
  have w₁_decomp : pe_W₁ =
      VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) h_v₁1_fresh_in_iv₂ :=
    w₁_eq.symm.trans (VarCtx_ext _ _ rfl)
  let renamed_1 := WFF.rename v₁.1 v1 v₁.2 (VarCtx_insert v₂ V hv₂) pe_W₁
                     h_v₁1_fresh_in_iv₂ h_v1_fresh_in_iv₂ w₁_decomp
                     inner_wff h_v1_nb_inner
  have h_v2_fresh_in_iv1 :
      v2 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) :=
    not_mem_VarSymbs_insert hv1v2.symm hv2
  have h_v₂1_fresh_in_iv1 :
      v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) :=
    not_mem_VarSymbs_insert h_v1_ne_v₂_1.symm hv₂
  have ctx_swap_1 :
      VarCtx_insert ⟨v1, v₁.2⟩ (VarCtx_insert v₂ V hv₂) h_v1_fresh_in_iv₂ =
      VarCtx_insert v₂ (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) h_v₂1_fresh_in_iv1 :=
    VarCtx_insert_comm h_v1_fresh_in_iv₂ h_v₂1_fresh_in_iv1
  have h_v2_nb_renamed_1 : v2 ∉ WFF.boundVars renamed_1 := fun hmem => by
    have h_sub := WFF.boundVars_rename_subset v₁.1 v1 v₁.2
      (VarCtx_insert v₂ V hv₂) pe_W₁
      h_v₁1_fresh_in_iv₂ h_v1_fresh_in_iv₂ w₁_decomp
      inner_wff h_v1_nb_inner
    rcases Finset.mem_insert.mp (h_sub hmem) with heq | hin
    · exact hv1v2.symm heq
    · exact h_v2_nb_inner hin
  let renamed_2 := WFF.rename v₂.1 v2 v₂.2 (VarCtx_insert ⟨v1, v₁.2⟩ V hv1)
                     (VarCtx_insert ⟨v1, v₁.2⟩ (VarCtx_insert v₂ V hv₂) h_v1_fresh_in_iv₂)
                     h_v₂1_fresh_in_iv1 h_v2_fresh_in_iv1 ctx_swap_1
                     renamed_1 h_v2_nb_renamed_1
  have ctx_final :
      VarCtx_insert ⟨v2, v₂.2⟩ (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) h_v2_fresh_in_iv1 =
      VarCtx_insert_twice ⟨v1, v₁.2⟩ ⟨v2, v₂.2⟩ V hv1 hv2 hv1v2 :=
    VarCtx_ext _ _ (by
      change insert ⟨v2, v₂.2⟩ (insert (⟨v1, v₁.2⟩ : VarSymb × VarType) V.1) =
             insert ⟨v1, v₁.2⟩ (insert ⟨v2, v₂.2⟩ V.1)
      exact Finset.insert_comm _ _ _)
  refine ⟨W₂def ▸ ctx_final ▸ renamed_2, ?_, ?_⟩
  · rw [WFF.diaCount_ctx_cast, WFF.diaCount_ctx_cast,
        WFF.diaCount_rename, WFF.diaCount_rename]
  · rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_cast,
        WFF.binderPairDepth_rename, WFF.binderPairDepth_rename]

-- context `W₂ = V + {v1, v2}` (with v1 : V1, v2 : V2).  Mirrors `Term.unpair`:
-- structural recursion through WFF constructors, delegating to `Rel.unpair`
-- for atomic relations and `Term.unpair` for equality terms.  `z` cannot
-- appear inside `.box`/`.dia` modal bodies (z's type is `.VTypeProd`, but
-- `VarCtx_box`/`VarCtx_dia` images only contain `.VTypeBox`/`.VTypeDia`
-- entries), so those arms are pass-through.  The `.pair_elim` arm has two
-- sub-cases (Case A: `z' = z`, drop the constructor and rename inner v₁,
-- v₂ to v1, v2; Case B: recurse on inner) — same pattern as `Term.unpair`.
def WFF.unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
    (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (input : WFF σ W₁)
    (h_v1_nb : v1 ∉ WFF.boundVars input)
    (h_v2_nb : v2 ∉ WFF.boundVars input)
    : WFF σ W₂ := by
  match input, h_v1_nb, h_v2_nb with
  | .atom R, h1, h2 =>
      exact .atom
        (Rel.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def R h1 h2)
  | .top, _, _ => exact .top
  | .bot, _, _ => exact .bot
  | .and φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      exact .and
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ)
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ)
  | .or φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      exact .or
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ)
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ)
  | .imp φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      exact .imp
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ)
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ)
  | .eq s t, h1, h2 =>
      have h1_s : v1 ∉ Term.boundVars s :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_t : v1 ∉ Term.boundVars t :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_s : v2 ∉ Term.boundVars s :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_t : v2 ∉ Term.boundVars t :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      exact .eq
        (Term.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def s h1_s h2_s)
        (Term.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def t h1_t h2_t)
  | @WFF.all _ _ x hx ψ, h1, h2 =>
      -- Recurse on ψ at the extended context (insert x V, insert x W₁, insert x W₂).
      have h_v1_ne_x : v1 ≠ x.1 := fun heq =>
        h1 (Finset.mem_insert.mpr (Or.inl heq))
      have h_v2_ne_x : v2 ≠ x.1 := fun heq =>
        h2 (Finset.mem_insert.mpr (Or.inl heq))
      have h_v1_nb_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_insert_of_mem hmem)
      have h_v2_nb_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_insert_of_mem hmem)
      -- x.1 ∉ symbols V (from hx via W₁def: W₁ = insert ⟨z, _⟩ V; hx says x.1 ∉ W₁).
      have hx_W₁ : x.1 ∉ VarCtx_to_VarSymbs W₁ := hx
      have h_x_ne_z : x.1 ≠ z := by
        intro heq
        apply hx_W₁
        rw [W₁def]
        have h_z_in : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
                        ∈ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz).1 :=
          Finset.mem_insert_self _ _
        exact Finset.mem_image.mpr ⟨_, h_z_in, heq.symm⟩
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := by
        intro hmem
        apply hx_W₁
        rw [W₁def]
        rcases Finset.mem_image.mp hmem with ⟨q, hq_in, hq_eq⟩
        exact Finset.mem_image.mpr ⟨q, Finset.mem_insert_of_mem hq_in, hq_eq⟩
      have hz_inner : z ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => h_x_ne_z h.symm) hz
      have hv1_inner : v1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert h_v1_ne_x hv1
      have hv2_inner : v2 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert h_v2_ne_x hv2
      let W₁_inner : VarCtx := VarCtx_insert ⟨z, V1.VTypeProd V2⟩
        (VarCtx_insert x V hx_V) hz_inner
      let W₂_inner : VarCtx := VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
        (VarCtx_insert x V hx_V) hv1_inner hv2_inner hv1v2
      -- ψ lives at insert x W₁ = insert x (insert ⟨z, _⟩ V), which equals W₁_inner.
      have h_ψ_ctx : VarCtx_insert x W₁ hx = W₁_inner := by
        apply VarCtx_ext
        change insert x W₁.1 = insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) (insert x V.1)
        rw [W₁def]
        change insert x (insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) V.1) = _
        exact Finset.insert_comm _ _ _
      let ψ_cast : WFF σ W₁_inner := h_ψ_ctx ▸ ψ
      have h_v1_nb_ψ_cast : v1 ∉ WFF.boundVars ψ_cast := by
        show v1 ∉ WFF.boundVars (h_ψ_ctx ▸ ψ)
        rw [WFF.boundVars_ctx_cast]; exact h_v1_nb_ψ
      have h_v2_nb_ψ_cast : v2 ∉ WFF.boundVars ψ_cast := by
        show v2 ∉ WFF.boundVars (h_ψ_ctx ▸ ψ)
        rw [WFF.boundVars_ctx_cast]; exact h_v2_nb_ψ
      let ψ_unpaired : WFF σ W₂_inner :=
        WFF.unpair z V1 V2 v1 v2 (VarCtx_insert x V hx_V) W₁_inner W₂_inner
          hz_inner hv1_inner hv2_inner hv1v2 rfl rfl ψ_cast
          h_v1_nb_ψ_cast h_v2_nb_ψ_cast
      -- Now swap inserts so x appears outermost: W₂_inner = insert x W₂.
      have hx_W₂ : x.1 ∉ VarCtx_to_VarSymbs W₂ := by
        rw [W₂def]
        exact not_mem_VarSymbs_insert_twice
          (fun h => h_v1_ne_x h.symm) (fun h => h_v2_ne_x h.symm) hx_V
      have h_swap_ctx : W₂_inner = VarCtx_insert x W₂ hx_W₂ := by
        apply VarCtx_ext
        change insert (⟨v1, V1⟩ : VarSymb × VarType)
                 (insert ⟨v2, V2⟩ (insert x V.1)) =
               insert x W₂.1
        rw [W₂def]
        change _ = insert x (insert (⟨v1, V1⟩ : VarSymb × VarType) (insert ⟨v2, V2⟩ V.1))
        rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) x,
            Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) x]
      exact .all x (hx := hx_W₂) (h_swap_ctx ▸ ψ_unpaired)
  | @WFF.ex _ _ x hx ψ, h1, h2 =>
      -- Symmetric to .all.
      have h_v1_ne_x : v1 ≠ x.1 := fun heq =>
        h1 (Finset.mem_insert.mpr (Or.inl heq))
      have h_v2_ne_x : v2 ≠ x.1 := fun heq =>
        h2 (Finset.mem_insert.mpr (Or.inl heq))
      have h_v1_nb_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_insert_of_mem hmem)
      have h_v2_nb_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_insert_of_mem hmem)
      have hx_W₁ : x.1 ∉ VarCtx_to_VarSymbs W₁ := hx
      have h_x_ne_z : x.1 ≠ z := by
        intro heq
        apply hx_W₁
        rw [W₁def]
        have h_z_in : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
                        ∈ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz).1 :=
          Finset.mem_insert_self _ _
        exact Finset.mem_image.mpr ⟨_, h_z_in, heq.symm⟩
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := by
        intro hmem
        apply hx_W₁
        rw [W₁def]
        rcases Finset.mem_image.mp hmem with ⟨q, hq_in, hq_eq⟩
        exact Finset.mem_image.mpr ⟨q, Finset.mem_insert_of_mem hq_in, hq_eq⟩
      have hz_inner : z ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => h_x_ne_z h.symm) hz
      have hv1_inner : v1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert h_v1_ne_x hv1
      have hv2_inner : v2 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert h_v2_ne_x hv2
      let W₁_inner : VarCtx := VarCtx_insert ⟨z, V1.VTypeProd V2⟩
        (VarCtx_insert x V hx_V) hz_inner
      let W₂_inner : VarCtx := VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
        (VarCtx_insert x V hx_V) hv1_inner hv2_inner hv1v2
      have h_ψ_ctx : VarCtx_insert x W₁ hx = W₁_inner := by
        apply VarCtx_ext
        change insert x W₁.1 = insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) (insert x V.1)
        rw [W₁def]
        change insert x (insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) V.1) = _
        exact Finset.insert_comm _ _ _
      let ψ_cast : WFF σ W₁_inner := h_ψ_ctx ▸ ψ
      have h_v1_nb_ψ_cast : v1 ∉ WFF.boundVars ψ_cast := by
        show v1 ∉ WFF.boundVars (h_ψ_ctx ▸ ψ)
        rw [WFF.boundVars_ctx_cast]; exact h_v1_nb_ψ
      have h_v2_nb_ψ_cast : v2 ∉ WFF.boundVars ψ_cast := by
        show v2 ∉ WFF.boundVars (h_ψ_ctx ▸ ψ)
        rw [WFF.boundVars_ctx_cast]; exact h_v2_nb_ψ
      let ψ_unpaired : WFF σ W₂_inner :=
        WFF.unpair z V1 V2 v1 v2 (VarCtx_insert x V hx_V) W₁_inner W₂_inner
          hz_inner hv1_inner hv2_inner hv1v2 rfl rfl ψ_cast
          h_v1_nb_ψ_cast h_v2_nb_ψ_cast
      have hx_W₂ : x.1 ∉ VarCtx_to_VarSymbs W₂ := by
        rw [W₂def]
        exact not_mem_VarSymbs_insert_twice
          (fun h => h_v1_ne_x h.symm) (fun h => h_v2_ne_x h.symm) hx_V
      have h_swap_ctx : W₂_inner = VarCtx_insert x W₂ hx_W₂ := by
        apply VarCtx_ext
        change insert (⟨v1, V1⟩ : VarSymb × VarType)
                 (insert ⟨v2, V2⟩ (insert x V.1)) =
               insert x W₂.1
        rw [W₂def]
        change _ = insert x (insert (⟨v1, V1⟩ : VarSymb × VarType) (insert ⟨v2, V2⟩ V.1))
        rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) x,
            Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) x]
      exact .ex x (hx := hx_W₂) (h_swap_ctx ▸ ψ_unpaired)
  | .box ψ hsub h_no_box_extras, _, _ =>
      -- `z` is `.VTypeProd`-typed in W₁; `VarCtx_box V_inner` only has
      -- `.VTypeBox`-outer entries.  If V1 or V2 is box-typed, then under
      -- recursive `isBox`, `(V1.VTypeProd V2).isBox = true`, so
      -- `h_no_box_extras` on the original W₁ forces `⟨z, V1×V2⟩` into
      -- `VarCtx_box V_inner` — impossible by constructor mismatch.
      rename_i V_inner
      refine .box ψ ?_ (by
        intro p hp h_box
        rw [W₂def] at hp
        rcases Finset.mem_insert.mp hp with h_eq | hp'
        · subst h_eq
          exfalso
          have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [W₁def]; exact Finset.mem_insert_self _ _
          have hz_box : (V1.VTypeProd V2).isBox = true := by
            simp [VarType.isBox, h_box]
          have hz_in_box := h_no_box_extras _ hz_in_W1 hz_box
          rcases Finset.mem_image.mp hz_in_box with ⟨⟨_, _⟩, _, hveq⟩
          simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
        · rcases Finset.mem_insert.mp hp' with h_eq2 | hp_V
          · subst h_eq2
            exfalso
            have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_self _ _
            have hz_box : (V1.VTypeProd V2).isBox = true := by
              simp [VarType.isBox, h_box]
            have hz_in_box := h_no_box_extras _ hz_in_W1 hz_box
            rcases Finset.mem_image.mp hz_in_box with ⟨⟨_, _⟩, _, hveq⟩
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
          · have hp_W1 : p ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_of_mem hp_V
            exact h_no_box_extras p hp_W1 h_box)
      intro y hy
      rw [W₂def]
      have hy_W : y ∈ W₁.1 := hsub hy
      rw [W₁def] at hy_W
      rcases Finset.mem_insert.mp hy_W with hyz | hyV
      · subst hyz
        rcases Finset.mem_image.mp hy with ⟨_, _, hweq⟩
        simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hweq
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hyV)
  | .dia x hx ψ hsub h_no_box_extras, _, _ =>
      -- Same argument as .box: under recursive `isBox`, V1×V2 box-detected if
      -- V1 or V2 is box; h_no_box_extras then forces ⟨z, V1×V2⟩ into
      -- VarCtx_dia, but neither the x-binder (VTypeDia-outer) nor the
      -- VarCtx_box rest (VTypeBox-outer) entries match VTypeProd.
      rename_i V_inner
      refine .dia x hx ψ ?_ (by
        intro p hp h_box
        rw [W₂def] at hp
        rcases Finset.mem_insert.mp hp with h_eq | hp'
        · subst h_eq
          exfalso
          have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [W₁def]; exact Finset.mem_insert_self _ _
          have hz_box : (V1.VTypeProd V2).isBox = true := by
            simp [VarType.isBox, h_box]
          have hz_in_dia := h_no_box_extras _ hz_in_W1 hz_box
          rcases Finset.mem_insert.mp hz_in_dia with hxeq | hbox
          · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
          · rcases Finset.mem_image.mp hbox with ⟨⟨_, _⟩, _, hveq⟩
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
        · rcases Finset.mem_insert.mp hp' with h_eq2 | hp_V
          · subst h_eq2
            exfalso
            have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_self _ _
            have hz_box : (V1.VTypeProd V2).isBox = true := by
              simp [VarType.isBox, h_box]
            have hz_in_dia := h_no_box_extras _ hz_in_W1 hz_box
            rcases Finset.mem_insert.mp hz_in_dia with hxeq | hbox
            · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
            · rcases Finset.mem_image.mp hbox with ⟨⟨_, _⟩, _, hveq⟩
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
          · have hp_W1 : p ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_of_mem hp_V
            exact h_no_box_extras p hp_W1 h_box)
      intro y hy
      rw [W₂def]
      have hy_W : y ∈ W₁.1 := hsub hy
      rw [W₁def] at hy_W
      rcases Finset.mem_insert.mp hy_W with hyz | hyV
      · subst hyz
        rcases Finset.mem_insert.mp hy with hxeq | hbox
        · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
        · rcases Finset.mem_image.mp hbox with ⟨_, _, hweq⟩
          simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hweq
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hyV)
  | .pair_elim v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff, h1, h2 =>
      rename_i pe_V pe_W₁
      -- Extract freshness conditions from h1/h2.
      have h_v1_nb_inner : v1 ∉ WFF.boundVars inner_wff := fun hmem =>
        h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      have h_v2_nb_inner : v2 ∉ WFF.boundVars inner_wff := fun hmem =>
        h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      by_cases h_case :
          (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩
      · -- Case A: delegate to `WFF.unpair_pe_caseA` helper (subtype return).
        exact (WFF.unpair_pe_caseA z V1 V2 v1 v2 V W₁ W₂
          hz hv1 hv2 hv1v2 W₁def W₂def pe_V pe_W₁ v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner
          hz' w₁_eq w₂_eq inner_wff h_v1_nb_inner h_v2_nb_inner h1 h2 h_case).val
      · -- Case B: ⟨z, V1.VTypeProd V2⟩ must lie in pe_V.  Recurse on inner_wff.
        have h_z_in_pe_V :
            (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ pe_V.1 := by
          have h_z_in_W₁ : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [W₁def]; exact Finset.mem_insert_self _ _
          rw [← w₂_eq] at h_z_in_W₁
          rcases Finset.mem_insert.mp h_z_in_W₁ with h_eq | h_pe_V
          · exact absurd h_eq.symm h_case
          · exact h_pe_V
        let pe_V' := VarCtx_erase pe_V ⟨z, V1.VTypeProd V2⟩
        have hz_pe_V' : z ∉ VarCtx_to_VarSymbs pe_V' :=
          VarCtx_erase_fresh h_z_in_pe_V
        have hv₁_pe_V' : v₁.1 ∉ VarCtx_to_VarSymbs pe_V' :=
          fun hmem => hv₁ (VarCtx_to_VarSymbs_erase_subset hmem)
        have hv₂_pe_V' : v₂.1 ∉ VarCtx_to_VarSymbs pe_V' :=
          fun hmem => hv₂ (VarCtx_to_VarSymbs_erase_subset hmem)
        have h_z_ne_v₁_1 : z ≠ v₁.1 := fun heq =>
          hv₁ (heq ▸ Finset.mem_image.mpr ⟨_, h_z_in_pe_V, rfl⟩)
        have h_z_ne_v₂_1 : z ≠ v₂.1 := fun heq =>
          hv₂ (heq ▸ Finset.mem_image.mpr ⟨_, h_z_in_pe_V, rfl⟩)
        let V_inner_pe :=
          VarCtx_insert_twice v₁ v₂ pe_V' hv₁_pe_V' hv₂_pe_V' hv₁v₂_inner
        have hz_V_inner : z ∉ VarCtx_to_VarSymbs V_inner_pe :=
          not_mem_VarSymbs_insert_twice h_z_ne_v₁_1 h_z_ne_v₂_1 hz_pe_V'
        have h_v1_ne_v₁_1 : v1 ≠ v₁.1 := fun heq =>
          h1 (Finset.mem_insert.mpr (Or.inl heq))
        have h_v1_ne_v₂_1 : v1 ≠ v₂.1 := fun heq =>
          h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
        have h_v2_ne_v₁_1 : v2 ≠ v₁.1 := fun heq =>
          h2 (Finset.mem_insert.mpr (Or.inl heq))
        have h_v2_ne_v₂_1 : v2 ≠ v₂.1 := fun heq =>
          h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
        have h_v1_pe_V' : v1 ∉ VarCtx_to_VarSymbs pe_V' := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨⟨v, S'⟩, hvin', hveq⟩
          have hvin_W₁ : (⟨v, S'⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [← w₂_eq]
            exact Finset.mem_insert_of_mem (Finset.erase_subset _ _ hvin')
          rw [W₁def] at hvin_W₁
          rcases Finset.mem_insert.mp hvin_W₁ with h_eq | h_inV
          · exact (Finset.mem_erase.mp hvin').1 h_eq
          · exact hv1 (Finset.mem_image.mpr ⟨⟨v, S'⟩, h_inV, hveq⟩)
        have h_v2_pe_V' : v2 ∉ VarCtx_to_VarSymbs pe_V' := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨⟨v, S'⟩, hvin', hveq⟩
          have hvin_W₁ : (⟨v, S'⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [← w₂_eq]
            exact Finset.mem_insert_of_mem (Finset.erase_subset _ _ hvin')
          rw [W₁def] at hvin_W₁
          rcases Finset.mem_insert.mp hvin_W₁ with h_eq | h_inV
          · exact (Finset.mem_erase.mp hvin').1 h_eq
          · exact hv2 (Finset.mem_image.mpr ⟨⟨v, S'⟩, h_inV, hveq⟩)
        have hv1_V_inner : v1 ∉ VarCtx_to_VarSymbs V_inner_pe :=
          not_mem_VarSymbs_insert_twice h_v1_ne_v₁_1 h_v1_ne_v₂_1 h_v1_pe_V'
        have hv2_V_inner : v2 ∉ VarCtx_to_VarSymbs V_inner_pe :=
          not_mem_VarSymbs_insert_twice h_v2_ne_v₁_1 h_v2_ne_v₂_1 h_v2_pe_V'
        have W₁_inner_def : pe_W₁ =
            VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_inner_pe hz_V_inner := by
          apply VarCtx_ext
          rw [← w₁_eq]
          change insert v₁ (insert v₂ pe_V.1) =
                 insert ⟨z, V1.VTypeProd V2⟩ (insert v₁ (insert v₂ pe_V'.1))
          rw [← Finset.insert_erase h_z_in_pe_V,
              Finset.insert_comm v₂ ⟨z, V1.VTypeProd V2⟩,
              Finset.insert_comm v₁ ⟨z, V1.VTypeProd V2⟩]
          rfl
        let W₂_inner_pe :=
          VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_inner_pe hv1_V_inner hv2_V_inner hv1v2
        have h_v1_nb_inner_cast : v1 ∉ WFF.boundVars (W₁_inner_def ▸ inner_wff) := by
          rw [WFF.boundVars_ctx_cast]; exact h_v1_nb_inner
        have h_v2_nb_inner_cast : v2 ∉ WFF.boundVars (W₁_inner_def ▸ inner_wff) := by
          rw [WFF.boundVars_ctx_cast]; exact h_v2_nb_inner
        let recursed := WFF.unpair z V1 V2 v1 v2 V_inner_pe
                          (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_inner_pe hz_V_inner)
                          W₂_inner_pe
                          hz_V_inner hv1_V_inner hv2_V_inner hv1v2
                          rfl rfl (W₁_inner_def ▸ inner_wff)
                          h_v1_nb_inner_cast h_v2_nb_inner_cast
        let pe_V_new :=
          VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ pe_V' h_v1_pe_V' h_v2_pe_V' hv1v2
        have hv₁_new : v₁.1 ∉ VarCtx_to_VarSymbs pe_V_new :=
          not_mem_VarSymbs_insert_twice h_v1_ne_v₁_1.symm h_v2_ne_v₁_1.symm hv₁_pe_V'
        have hv₂_new : v₂.1 ∉ VarCtx_to_VarSymbs pe_V_new :=
          not_mem_VarSymbs_insert_twice h_v1_ne_v₂_1.symm h_v2_ne_v₂_1.symm hv₂_pe_V'
        have hz'_new : z' ∉ VarCtx_to_VarSymbs pe_V_new := by
          have h_z'_in_V : (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ V.1 := by
            have h_z'_in_W₁ : (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [← w₂_eq]; exact Finset.mem_insert_self _ _
            rw [W₁def] at h_z'_in_W₁
            rcases Finset.mem_insert.mp h_z'_in_W₁ with h_eq | h_inV
            · exact absurd h_eq h_case
            · exact h_inV
          have h_z'_ne_v1 : z' ≠ v1 := fun heq =>
            hv1 (heq ▸ Finset.mem_image.mpr ⟨_, h_z'_in_V, rfl⟩)
          have h_z'_ne_v2 : z' ≠ v2 := fun heq =>
            hv2 (heq ▸ Finset.mem_image.mpr ⟨_, h_z'_in_V, rfl⟩)
          have h_z'_pe_V' : z' ∉ VarCtx_to_VarSymbs pe_V' :=
            fun hmem => hz' (VarCtx_to_VarSymbs_erase_subset hmem)
          exact not_mem_VarSymbs_insert_twice h_z'_ne_v1 h_z'_ne_v2 h_z'_pe_V'
        have ctx_eq : W₂_inner_pe =
            VarCtx_insert_twice v₁ v₂ pe_V_new hv₁_new hv₂_new hv₁v₂_inner :=
          VarCtx_ext _ _ (by
            change insert (⟨v1, V1⟩ : VarSymb × VarType)
                     (insert ⟨v2, V2⟩ (insert v₁ (insert v₂ pe_V'.1))) =
                   insert v₁ (insert v₂ (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ pe_V'.1)))
            rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) v₁,
                Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) v₁,
                Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) v₂,
                Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) v₂])
        have w₂_eq_new :
            VarCtx_insert ⟨z', .VTypeProd v₁.2 v₂.2⟩ pe_V_new hz'_new = W₂ := by
          rw [W₂def]
          apply VarCtx_ext
          change insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                   (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ pe_V'.1)) =
                 insert (⟨v1, V1⟩ : VarSymb × VarType) (insert ⟨v2, V2⟩ V.1)
          have h_W_set : insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V.1
                       = insert ⟨z, V1.VTypeProd V2⟩ V.1 :=
            congrArg PSigma.fst (w₂_eq.trans W₁def)
          have h_V_eq : V.1 = insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V'.1 := by
            have step :
                (insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V.1).erase
                  ⟨z, V1.VTypeProd V2⟩ = V.1 := by
              rw [h_W_set, Finset.erase_insert
                (fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩))]
            rw [Finset.erase_insert_of_ne h_case] at step
            exact step.symm
          rw [h_V_eq,
              Finset.insert_comm
                (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                (⟨v1, V1⟩ : VarSymb × VarType),
              Finset.insert_comm
                (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                (⟨v2, V2⟩ : VarSymb × VarType)]
        exact w₂_eq_new ▸ .pair_elim v₁ v₂ z' hv₁_new hv₂_new hv₁v₂_inner hz'_new
                                     rfl rfl (ctx_eq ▸ recursed)
termination_by WFF.numNodes input
decreasing_by
  all_goals (first
    | (simp only [WFF.numNodes_ctx_cast, WFF.numNodes]; omega)
    | (simp only [WFF.numNodes]; omega))

-- Probe: does `WFF.unpair` now generate equational theorems?
private theorem WFF.unpair_eq_lemma_probe {σ : Signature}
    (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
    (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (h1 : v1 ∉ WFF.boundVars (.top : WFF σ W₁))
    (h2 : v2 ∉ WFF.boundVars (.top : WFF σ W₁)) :
    WFF.unpair z V1 V2 v1 v2 V W₁ W₂
      hz hv1 hv2 hv1v2 W₁def W₂def
      (.top : WFF σ W₁) h1 h2
      = .top := by
  unfold WFF.unpair
  rfl

-- `WFF.unpair` preserves `diaCount`.  Structural cases recurse via IH;
-- `.box`/`.dia` bodies pass through (z has pair type, can't appear in
-- box/dia inner context); `.pair_elim` Case A uses the helper subtype's
-- diaCount preservation, Case B recurses via `apply`.
theorem WFF.diaCount_unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType)
    (v1 v2 : VarSymb) (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (input : WFF σ W₁)
    (h_v1_nb : v1 ∉ WFF.boundVars input)
    (h_v2_nb : v2 ∉ WFF.boundVars input) :
    WFF.diaCount (WFF.unpair z V1 V2 v1 v2 V W₁ W₂
                    hz hv1 hv2 hv1v2 W₁def W₂def input h_v1_nb h_v2_nb)
      = WFF.diaCount input := by
  match input, h_v1_nb, h_v2_nb with
  | .atom R, h1, h2 =>
      have ih := Rel.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂ _
        hz hv1 hv2 hv1v2 W₁def W₂def R h1 h2
      unfold WFF.unpair
      simp only [WFF.diaCount]
      exact ih
  | .top, _, _ =>
      unfold WFF.unpair; rfl
  | .bot, _, _ =>
      unfold WFF.unpair; rfl
  | .and φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.diaCount]
      omega
  | .or φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.diaCount]
      omega
  | .imp φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.diaCount]
      omega
  | .eq s t, h1, h2 =>
      have h1_s : v1 ∉ Term.boundVars s :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_t : v1 ∉ Term.boundVars t :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_s : v2 ∉ Term.boundVars s :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_t : v2 ∉ Term.boundVars t :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_s := Term.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂ _
        hz hv1 hv2 hv1v2 W₁def W₂def s h1_s h2_s
      have ih_t := Term.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂ _
        hz hv1 hv2 hv1v2 W₁def W₂def t h1_t h2_t
      unfold WFF.unpair
      simp only [WFF.diaCount]
      omega
  | @WFF.all _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
      rw [WFF.diaCount_unpair, WFF.diaCount_ctx_cast]
  | @WFF.ex _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
      rw [WFF.diaCount_unpair, WFF.diaCount_ctx_cast]
  | .box _ _ _, _, _ =>
      unfold WFF.unpair
      rfl
  | .dia _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      rfl
  | .pair_elim v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff, h1, h2 =>
      rename_i pe_V pe_W₁
      have h_v1_nb_inner : v1 ∉ WFF.boundVars inner_wff := fun hmem =>
        h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      have h_v2_nb_inner : v2 ∉ WFF.boundVars inner_wff := fun hmem =>
        h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      unfold WFF.unpair
      by_cases h_case :
          (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩
      · rw [dif_pos h_case]
        exact (WFF.unpair_pe_caseA z V1 V2 v1 v2 V W₁ W₂
          hz hv1 hv2 hv1v2 W₁def W₂def pe_V pe_W₁ v₁ v₂ z' hv₁ hv₂
          hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff h_v1_nb_inner h_v2_nb_inner
          h1 h2 h_case).property.1
      · rw [dif_neg h_case]
        simp only [WFF.diaCount_ctx_cast, WFF.diaCount]
        rw [WFF.diaCount_unpair, WFF.diaCount_ctx_cast]
termination_by WFF.numNodes input
decreasing_by
  all_goals (first
    | (simp only [WFF.numNodes_ctx_cast, WFF.numNodes]; omega)
    | (simp only [WFF.numNodes]; omega))

-- `WFF.unpair` preserves `binderPairDepth`.  Same structure as
-- `WFF.diaCount_unpair`: unpair only shuffles free variables, doesn't add or
-- remove modal/quantifier binders.
theorem WFF.binderPairDepth_unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType)
    (v1 v2 : VarSymb) (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (input : WFF σ W₁)
    (h_v1_nb : v1 ∉ WFF.boundVars input)
    (h_v2_nb : v2 ∉ WFF.boundVars input) :
    WFF.binderPairDepth (WFF.unpair z V1 V2 v1 v2 V W₁ W₂
                           hz hv1 hv2 hv1v2 W₁def W₂def input h_v1_nb h_v2_nb)
      = WFF.binderPairDepth input := by
  match input, h_v1_nb, h_v2_nb with
  | .atom _, _, _ =>
      unfold WFF.unpair; rfl
  | .top, _, _ =>
      unfold WFF.unpair; rfl
  | .bot, _, _ =>
      unfold WFF.unpair; rfl
  | .and φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.binderPairDepth]
      omega
  | .or φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.binderPairDepth]
      omega
  | .imp φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.binderPairDepth]
      omega
  | .eq _ _, _, _ =>
      unfold WFF.unpair; rfl
  | @WFF.all _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
      rw [WFF.binderPairDepth_unpair, WFF.binderPairDepth_ctx_cast]
  | @WFF.ex _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
      rw [WFF.binderPairDepth_unpair, WFF.binderPairDepth_ctx_cast]
  | .box _ _ _, _, _ =>
      unfold WFF.unpair
      rfl
  | .dia _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      rfl
  | .pair_elim v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff, h1, h2 =>
      rename_i pe_V pe_W₁
      have h_v1_nb_inner : v1 ∉ WFF.boundVars inner_wff := fun hmem =>
        h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      have h_v2_nb_inner : v2 ∉ WFF.boundVars inner_wff := fun hmem =>
        h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      unfold WFF.unpair
      by_cases h_case :
          (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩
      · rw [dif_pos h_case]
        exact (WFF.unpair_pe_caseA z V1 V2 v1 v2 V W₁ W₂
          hz hv1 hv2 hv1v2 W₁def W₂def pe_V pe_W₁ v₁ v₂ z' hv₁ hv₂
          hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff h_v1_nb_inner h_v2_nb_inner
          h1 h2 h_case).property.2
      · rw [dif_neg h_case]
        simp only [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth]
        rw [WFF.binderPairDepth_unpair, WFF.binderPairDepth_ctx_cast]
termination_by WFF.numNodes input
decreasing_by
  all_goals (first
    | (simp only [WFF.numNodes_ctx_cast, WFF.numNodes]; omega)
    | (simp only [WFF.numNodes]; omega))

/-! ### Context Restriction -/

-- Substitute the variable `⟨x, S⟩` with the term `s` inside `φ`.  Mirrors
-- `Term.ctx_rest` + `Term.ctx_rest_MU`: `WFF.ctx_rest` is the structural
-- pass requiring `V_ext.firstPairVar = none` (no pair binders in the
-- extended context); `WFF.ctx_rest_MU` is the user-facing wrapper that
-- preprocesses pair binders via `WFF.unpair` / `Term.unpair` before
-- delegating.
--
-- TODO: full implementations.  Currently both are skeleton stubs (returning
-- a placeholder `.top` for the non-trivial arms) so the mutual structure
-- compiles.  The .pair_elim arm of `WFF.ctx_rest` is properly exfalso via
-- `h_pf`; the other binder arms (.all/.ex/.box/.dia) are stubs to fill in.

-- Case-3 (modal beta) reorder helper for `WFF.ctx_rest_dia_arm`.  Extracted
-- outside the ctx_rest mutual block to keep dia_arm's Case 3 body compact and
-- avoid elaborator memory pressure (which caused BSODs on inline attempts).
--
-- Given ψ living in (insert xv V_inner) with xv.1 = x and a separate binder
-- xv_s : VarSymb × VarType with xv_s.1 ∉ V_inner (and xv.1 ≠ xv_s.1), this
-- helper produces the reordered/reformed WFF living in
--   (insert ⟨x, xv.2⟩ (insert xv_s V_inner))
-- ready for the MU substitution step at x.  Preserves `binderPairDepth` and
-- `diaCount` (both are stable under ctx_ext and under VarCtx-equality casts).
def WFF.dia_arm_case3_reorder {σ : Signature} {V_inner : VarCtx}
    (xv xv_s : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (hxv_s : xv_s.1 ∉ VarCtx_to_VarSymbs V_inner)
    (h_xv_ne_xv_s : xv.1 ≠ xv_s.1)
    {x : VarSymb} (h_xv_eq_x : xv.1 = x)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    : Σ' (h_x_inner : x ∉ VarCtx_to_VarSymbs
                          (VarCtx_insert xv_s V_inner hxv_s)),
        { ψ' : WFF σ (VarCtx_insert (⟨x, xv.2⟩ : VarSymb × VarType)
                        (VarCtx_insert xv_s V_inner hxv_s) h_x_inner) //
            WFF.binderPairDepth ψ' = WFF.binderPairDepth ψ ∧
            WFF.diaCount ψ' = WFF.diaCount ψ } := by
  -- Step 1: lift ψ past xv_s.
  have hxv_s_outer : xv_s.1 ∉ VarCtx_to_VarSymbs
      (VarCtx_insert xv V_inner hxv) := by
    apply not_mem_VarSymbs_insert
    · exact fun h => h_xv_ne_xv_s h.symm
    · exact hxv_s
  let ψ_lifted : WFF σ (VarCtx_insert xv_s
      (VarCtx_insert xv V_inner hxv) hxv_s_outer) :=
    WFF.ctx_ext xv_s hxv_s_outer ψ
  -- Step 2: reorder to swap xv_s and xv.
  have hxv_xv_s_outer : xv.1 ∉ VarCtx_to_VarSymbs
      (VarCtx_insert xv_s V_inner hxv_s) :=
    not_mem_VarSymbs_insert h_xv_ne_xv_s hxv
  have h_reorder :
      VarCtx_insert xv_s (VarCtx_insert xv V_inner hxv) hxv_s_outer =
      VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer := by
    apply VarCtx_ext
    change insert xv_s (insert xv V_inner.1) =
           insert xv (insert xv_s V_inner.1)
    exact Finset.insert_comm _ _ _
  let ψ_reordered : WFF σ (VarCtx_insert xv
      (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer) :=
    h_reorder ▸ ψ_lifted
  -- Step 3: reform binder as ⟨x, xv.2⟩ via h_xv_eq_x.
  have hxv_form : xv = (⟨x, xv.2⟩ : VarSymb × VarType) :=
    Prod.ext h_xv_eq_x rfl
  have h_x_inner : x ∉ VarCtx_to_VarSymbs
      (VarCtx_insert xv_s V_inner hxv_s) :=
    h_xv_eq_x ▸ hxv_xv_s_outer
  have h_reform :
      VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer =
      VarCtx_insert (⟨x, xv.2⟩ : VarSymb × VarType)
        (VarCtx_insert xv_s V_inner hxv_s) h_x_inner := by
    apply VarCtx_ext
    change insert xv _ = insert (⟨x, xv.2⟩ : VarSymb × VarType) _
    rw [hxv_form]
  let ψ_for_sub : WFF σ (VarCtx_insert (⟨x, xv.2⟩ : VarSymb × VarType)
      (VarCtx_insert xv_s V_inner hxv_s) h_x_inner) :=
    h_reform ▸ ψ_reordered
  refine ⟨h_x_inner, ⟨ψ_for_sub, ?_, ?_⟩⟩
  · -- binderPairDepth preserved.
    show WFF.binderPairDepth (h_reform ▸ h_reorder ▸
              WFF.ctx_ext xv_s hxv_s_outer ψ) = _
    rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_cast,
        WFF.binderPairDepth_ctx_ext]
  · -- diaCount preserved.
    show WFF.diaCount (h_reform ▸ h_reorder ▸
              WFF.ctx_ext xv_s hxv_s_outer ψ) = _
    rw [WFF.diaCount_ctx_cast, WFF.diaCount_ctx_cast,
        WFF.diaCount_ctx_ext]

mutual

def WFF.ctx_rest {σ : Signature} {V : VarCtx}
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
      let r1 := WFF.ctx_rest hx h_pf s φ'
      let r2 := WFF.ctx_rest hx h_pf s ψ
      exact ⟨.and r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .or φ' ψ =>
      let r1 := WFF.ctx_rest hx h_pf s φ'
      let r2 := WFF.ctx_rest hx h_pf s ψ
      exact ⟨.or r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .imp φ' ψ =>
      let r1 := WFF.ctx_rest hx h_pf s φ'
      let r2 := WFF.ctx_rest hx h_pf s ψ
      exact ⟨.imp r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .eq s' t =>
      exact ⟨.eq (Term.ctx_rest hx h_pf s s') (Term.ctx_rest hx h_pf s t),
             Nat.zero_le _⟩
  | @WFF.all _ _ x_a hx_a ψ =>
      let r := WFF.ctx_rest_quant_arm hx h_pf s false x_a hx_a ψ
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | @WFF.ex _ _ x_a hx_a ψ =>
      let r := WFF.ctx_rest_quant_arm hx h_pf s true x_a hx_a ψ
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | .box ψ hsub h_no_extras =>
      let r := WFF.ctx_rest_box_arm hx h_pf s ψ hsub h_no_extras
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | .dia xv hxv ψ hsub h_no_extras =>
      let r := WFF.ctx_rest_dia_arm hx h_pf s xv hxv ψ hsub h_no_extras
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

def WFF.ctx_rest_MU {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    {ψ' : WFF σ V // WFF.binderPairDepth ψ' ≤ WFF.binderPairDepth φ} := by
  match h_pv : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar with
  | none =>
      exact WFF.ctx_rest hx h_pv s φ
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
            let result1 := WFF.ctx_rest_MU hv1_V_plus_v2 s1_weakened φ'_cast
            have h_r1_bpd : WFF.binderPairDepth result1.val
                ≤ WFF.binderPairDepth φ :=
              le_trans result1.property (le_of_eq h_in_bpd)
            -- Substitute v2 ↦ s2.
            let result2 := WFF.ctx_rest_MU hv2_V_only s2 result1.val
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
            let result := WFF.ctx_rest_MU hx_peV_v1v2 s' φ'A_cast
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
        let result := WFF.ctx_rest_MU hx_Vmz_v1v2 s' φ'_cast
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
def WFF.ctx_rest_quant_arm {σ : Signature} {V : VarCtx}
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
  let result := WFF.ctx_rest_MU hx_xaV (Term.ctx_ext x_a hxa_V s) (h_ψ_ctx ▸ ψ)
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
-- S = T.VTypeBox, match s as `.boxterm`, recurse via WFF.ctx_rest_MU
-- on ψ at the smaller V_inner_minus_x context.  If no, trivial passthrough.
def WFF.ctx_rest_box_arm {σ : Signature} {V : VarCtx} {V_inner : VarCtx}
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
              let ψ_new := WFF.ctx_rest_MU hx_minus s_inner ψ_cast
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
def WFF.ctx_rest_dia_arm {σ : Signature} {V : VarCtx} {V_inner : VarCtx}
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
        let result_sub := WFF.ctx_rest_MU h_x_inner tt_s ψ_for_sub
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
                let ψ_new := WFF.ctx_rest_MU hx_in_outer s_lifted ψ_cast
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

-- Preservation of `binderPairDepth` under the substitution machinery is now
-- carried by the Σ'-subtype returns of the functions themselves (each
-- returns `{res // bpd res ≤ bound}`; Case A .pair/.pair_elim are fully
-- implemented, using the first recursive call's `.property` for the second
-- call's termination).  The previous standalone mutual theorem block is
-- superseded by `.property` projections, kept as named lemmas:
theorem WFF.binderPairDepth_ctx_rest_MU_le {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.ctx_rest_MU hx s φ).val
      ≤ WFF.binderPairDepth φ :=
  (WFF.ctx_rest_MU hx s φ).property

theorem WFF.binderPairDepth_ctx_rest_le {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.ctx_rest hx h_pf s φ).val
      ≤ WFF.binderPairDepth φ :=
  (WFF.ctx_rest hx h_pf s φ).property

/-! ### Variable instantiation (public API) -/

-- Substitute the free variable `x : S` by the term `s : Term σ V S`
-- throughout `φ`, discharging `x` from the context: `φ` lives in `V + x`,
-- the result lives in `V`.  This is THE substitution operation the proof
-- system's quantifier/modal rules use (∀-elim, ∃-intro, modal beta).
--
-- Thin wrapper over the Σ'-subtype machinery: `WFF.ctx_rest_MU` handles
-- pair-typed variables (Case A), pair vars elsewhere in the context
-- (Case B), and the pair-free structural pass, and carries the
-- `binderPairDepth` bound intrinsically.
def WFF.substVar {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) : WFF σ V :=
  (WFF.ctx_rest_MU hx s φ).val

theorem WFF.binderPairDepth_substVar_le {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.substVar hx s φ) ≤ WFF.binderPairDepth φ :=
  (WFF.ctx_rest_MU hx s φ).property

/-! ## Proof System (Natural Deduction) -/

/-! ### Modal context bridging lemmas

    Convert a `dia`-context side condition into the corresponding `box`-context
    one, so that `□Γ` and `◇ₓψ` can inhabit the same outer context `W` in the
    modal rules (`K_dia`, `Mlem`). -/

lemma in_box_of_in_dia {x : VarSymb × VarType} {V W : VarCtx} {hx : x.1 ∉ VarCtx_to_VarSymbs V}
    (in_dia : ∀ p ∈ W.1, p.2.isBox = true → p ∈ (VarCtx_dia x V hx).fst) :
    ∀ p ∈ W.1, p.2.isBox = true → p ∈ (VarCtx_box V).fst := by
  rintro p pmemW pbox
  have pmem := in_dia p pmemW pbox
  unfold VarCtx_dia at pmem
  simp only [Finset.mem_insert] at pmem
  rcases pmem with diacase | boxcase
  · exfalso
    have : p.2.isBox = false := by
      rw [diacase]
      exact Bool.eq_false_of_le_false fun a ↦ a
    rw [pbox] at this
    exact (Bool.true_eq_false_eq_False this)
  · exact boxcase


lemma box_subs_of_dia_subs {x : VarSymb × VarType} {V W : VarCtx} {hx : x.1 ∉ VarCtx_to_VarSymbs V}
    (dia_in_W : (VarCtx_dia x V hx).fst ⊆ W.fst) :
    (VarCtx_box V).fst ⊆ W.fst := by
  intros y ybox
  have : y ∈  (VarCtx_dia x V hx).fst := by
    unfold VarCtx_dia
    simp only [Finset.mem_insert]
    exact Or.inr ybox
  exact dia_in_W this

/-! ### Deduction rules

    `Proof σ V Γ φ` is the type of derivations of `φ` from hypotheses `Γ` in
    context `V`.  Classical natural deduction (structural, propositional,
    quantifier, and equality rules) plus Fitch-style modal K.  Freshness /
    eigenvariable side conditions are discharged by the context typing rather
    than carried as premises. -/

/-- A `pair_elim` body α-renamed `v₁ → n₁` and `v₂ → n₂` (to fresh names of the same type):
    outer rename of `v₁` (`rfl` `Wdef`), then inner rename of `v₂` (`VarCtx_insert_comm` `Wdef`).
    Result lands over the *commuted* context `insert ⟨n₂,·⟩ (insert ⟨n₁,·⟩ V)` — no final cast; the
    commute is absorbed into `pair_elim`'s free `w₁'eq`.  Factored out of `Proof.pair_elim_alpha`. -/
def Term.pairElimAlphaBody {σ : Signature} (v₁ v₂ : VarSymb × VarType) (n₁ n₂ : VarSymb)
    {V : VarCtx} (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V) (hn₁ : n₁ ∉ VarCtx_to_VarSymbs V)
    (hn₁n₂ : n₁ ≠ n₂)
    (hv₁_nest : v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂))
    (hn₁_nest : n₁ ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂))
    (hv₂_nest : v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁))
    (hn₂_nest : n₂ ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁))
    {S : VarType} (body : Term σ (VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest) S)
    (nnb₁ : n₁ ∉ Term.boundVars body) (nnb₂ : n₂ ∉ Term.boundVars body) :
    Term σ (VarCtx_insert ⟨n₂, v₂.2⟩ (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁) hn₂_nest) S :=
  Term.rename v₂.1 n₂ v₂.2 (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁)
    (VarCtx_insert ⟨n₁, v₁.2⟩ (VarCtx_insert v₂ V hv₂) hn₁_nest) S
    hv₂_nest hn₂_nest (VarCtx_insert_comm hn₁_nest hv₂_nest)
    (Term.rename v₁.1 n₁ v₁.2 (VarCtx_insert v₂ V hv₂)
      (VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest) S hv₁_nest hn₁_nest rfl body nnb₁)
    (fun h =>
      (Finset.mem_insert.mp (Term.boundVars_rename_subset v₁.1 n₁ v₁.2 (VarCtx_insert v₂ V hv₂)
          (VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest) S hv₁_nest hn₁_nest rfl body nnb₁ h)).elim
        (fun heq => hn₁n₂ heq.symm) nnb₂)

inductive Proof (σ : Signature) : (V : VarCtx) → Finset (WFF σ V) → WFF σ V → Type where
  -- Structural rules
  | ax       : φ ∈ (Γ : Finset (WFF σ V))
               → Proof σ V Γ φ
  | weak     : Proof σ V Γ φ
               → Proof σ V (Γ ∪ {ψ}) φ
  | weak_ctx : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
               → Proof σ V Γ φ
               → Proof σ (VarCtx_insert x V hx) (WFF.ctx_ext_Finset x hx Γ) (WFF.ctx_ext x hx φ)
  -- Conjunction
  | and_intro  : Proof σ V Γ φ → Proof σ V Γ ψ
                 → Proof σ V Γ (φ.and ψ)
  | and_elim_l : Proof σ V Γ (φ.and ψ) → Proof σ V Γ φ
  | and_elim_r : {φ : WFF σ V}
                 → Proof σ V Γ (φ.and ψ) → Proof σ V Γ ψ
  -- Disjunction
  | or_intro_l : Proof σ V Γ φ → Proof σ V Γ (φ.or ψ)
  | or_intro_r : {φ : WFF σ V}
                 → Proof σ V Γ ψ → Proof σ V Γ (φ.or ψ)
  | or_elim    : Proof σ V Γ (φ.or ψ)
                 → Proof σ V (Γ ∪ {φ}) χ → Proof σ V (Γ ∪ {ψ}) χ
                 → Proof σ V Γ χ
  -- Implication
  | imp_intro  : Proof σ V (Γ ∪ {φ}) ψ → Proof σ V Γ (φ.imp ψ)
  | imp_elim   : Proof σ V Γ (φ.imp ψ) → Proof σ V Γ φ → Proof σ V Γ ψ
  -- Truth and falsity
  | top_intro  : Proof σ V Γ .top
  | bot_elim   : Proof σ V Γ .bot → Proof σ V Γ φ
  -- Classical logic
  | lem        : (φ : WFF σ V) →  Proof σ V Γ (φ.or (neg φ))
  -- Universal quantifier
  -- Introduction: prove φ in the extended context V ∪ {x}, with x fresh.
  | all_intro  : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert x V hx)}
                 → Proof σ (VarCtx_insert x V hx) (WFF.ctx_ext_Finset x hx Γ) φ
                 → Proof σ V Γ (.all x φ)
  -- Elimination: from ∀x.φ and a term t : Term σ V, get φ[t/x] back in context V.
  | all_elim   : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert x V hx)}
                 → (t : Term σ V x.2)
                 → Proof σ V Γ (.all x φ)
                 → Proof σ V Γ (WFF.substVar hx t φ)
  -- Existential quantifier
  -- Introduction: provide a witness t : Term σ V and a proof of φ[s/x].
  | ex_intro   : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert x V hx)}
                 → (t : Term σ V x.2)
                 → Proof σ V Γ (WFF.substVar hx t φ)
                 → Proof σ V Γ (.ex x φ)
  -- Elimination: from ∃x.φ, derive ψ given that ψ holds with x as a fresh variable.
  | ex_elim    : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert x V hx)}
                 → Proof σ V Γ (.ex x φ)
                 → Proof σ (VarCtx_insert x V hx) ((WFF.ctx_ext_Finset x hx Γ) ∪ {φ}) (WFF.ctx_ext x hx ψ)
                 → Proof σ V Γ ψ
  -- Equality
  -- Introduction: given a term t, get t = t
  | eq_intro   : (t : Term σ V S) → Proof σ V Γ (WFF.eq t t)
  -- Elimination: given t = s, sub t for s
  | eq_elim : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
            → {φ : WFF σ (VarCtx_insert x V hx)} → (t s : Term σ V x.2)
            → Proof σ V Γ (WFF.eq t s)
            → Proof σ V Γ (WFF.substVar hx t φ)
            → Proof σ V Γ (WFF.substVar hx s φ)
  -- Pairing
  | pair_elim : (v₁ v₂ : VarSymb × VarType) → (z : VarSymb)
                 → (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) → (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
                 → (hv₁v₂ : v₁.1 ≠ v₂.1) → (hz : z ∉ VarCtx_to_VarSymbs V)
                 → (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
                 → (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
                 → Proof σ W₁ Γ φ
                 → Proof σ W₂ (WFF.pairElim_Finset v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq Γ)
                   (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ)
  -- Modal K rules
  -- K box rule
  | K_box : (hsub : (VarCtx_box V).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
                 → Proof σ V Γ φ
                 → Proof σ W (WFF.box_Finset hsub h_no_box_extras Γ)
                  (WFF.box φ hsub h_no_box_extras)
  -- General modal-`K` rule for `◇_x` (the multi-conclusion K rule, single-conclusion form): from
  -- `Γ, Δ, ψ ⊢ φ` conclude `□Γ, □_x Δ, ◇_x ψ ⊢ ◇_x φ`.  `Γ` is `x`-free (plain `□`); `Δ` may mention
  -- the witness `x` (witnessed box `□_x = ¬◇_x¬`).  Subsumes the old plain-`□`-only `K_dia`
  -- (`Δ = ∅`) and the witnessed-only `K_dia_x` (`Γ = ∅`); the `□`↔`◇_x` bridge (e.g. `□φ ⊢ □_x φ`)
  -- and the box_x-hypothesis transfer needed for canonical-model completeness both live here.
  | K_dia : (x : VarSymb × VarType)
                 → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
                 → {φ ψ : WFF σ (VarCtx_insert x V hx)}
                 → {Γ : Finset (WFF σ V)}
                 → {Δ : Finset (WFF σ (VarCtx_insert x V hx))}
                 → Proof σ (VarCtx_insert x V hx)
                    ((WFF.ctx_ext_Finset x hx Γ) ∪ Δ ∪ {ψ}) φ
                 → Proof σ W ((WFF.box_Finset (box_subs_of_dia_subs hsub)
                  (in_box_of_in_dia h_no_box_extras) Γ)
                    ∪ (WFF.box_x_Finset x hx hsub h_no_box_extras Δ)
                    ∪ {WFF.dia x hx ψ hsub h_no_box_extras})
                  (WFF.dia x hx φ hsub h_no_box_extras)
  -- (A witness-only `K_dia_pure` — `□Γ ⊢ ◇_x φ` with no `◇`-formula hypothesis — was tried and
  -- removed: under the existential `◇` semantics `◇_x ⊤` asserts the possible object `x` is
  -- *nonempty*, which fails for the empty (impossible) possible object.  A possible object may be
  -- empty, so `⊤ ⊢ ◇_x⊤` is correctly not a theorem.)
  -- contradictions are not possible: this can be dropped in some intuitionistic versions
  | dia_bot : (x : VarSymb × VarType)
                 → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {W : VarCtx}
                 → (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
                 → {Γ : Finset (WFF σ W)}
                 → Proof σ W Γ (WFF.dia x hx WFF.bot hsub h_no_box_extras)
                 → Proof σ W Γ WFF.bot
  -- (The "modal LEM" `Mlem` has been removed: with the object-witness `◇_x` it is a disguised
  -- coverage/Barcan axiom, unsound over general models.  The de-dicto version `□φ ∨ ◇' ¬φ`
  -- (using `WFF.dia'`) is just `lem` and is derivable.)
  -- World-extensionality (funext / Σ-ext): necessarily / possibly equal box / dia
  -- terms are equal.  Both conclusions are `necIntro` / `posIntro` of the equal
  -- section / witness the premise provides, so these are sound in *every* model
  -- (no `necEval` / `posEval` injectivity condition is required).
  | box_ext : {V W : VarCtx} → {S : VarType} → {Γ : Finset (WFF σ W)}
                 → (hsub : (VarCtx_box V).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
                 → (tt₁ tt₂ : Term σ V S)
                 → Proof σ W Γ (WFF.box (WFF.eq tt₁ tt₂) hsub h_no_box_extras)
                 → Proof σ W Γ (WFF.eq (Term.boxterm tt₁ hsub h_no_box_extras)
                  (Term.boxterm tt₂ hsub h_no_box_extras))
  | dia_ext : {V W : VarCtx} → {S : VarType} → {Γ : Finset (WFF σ W)}
                 → (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
                 → (tt₁ tt₂ : Term σ (VarCtx_insert x V hx) S)
                 -- premise is `box_x (tt₁ ≐ tt₂)` = `¬◇_x¬(tt₁ ≐ tt₂)` = the terms agree at
                 -- *every* realization of `x` (existential `◇_x` gives only one — too weak).
                 → Proof σ W Γ (neg (WFF.dia x hx (neg (WFF.eq tt₁ tt₂)) hsub h_no_box_extras))
                 → Proof σ W Γ (WFF.eq (Term.diaterm x hx tt₁ hsub h_no_box_extras)
                  (Term.diaterm x hx tt₂ hsub h_no_box_extras))
  -- α-conversion for `pair_elim` — the ONLY term former with a genuine binder (`v₁`,`v₂` are
  -- consumed; `dia_x`'s `x` and `boxterm`'s variables are *promoted free* variables).  Renaming the
  -- bound variables to fresh `n₁,n₂` yields a provably-equal term.  NOT derivable: pair-β only fires
  -- on a *literal* pair, and there are no projections to η-expand a neutral `z` (projections are the
  -- *negative* product, commuting inward; `pair_elim` is *positive* and stays stuck outside).  So α
  -- among stuck `pair_elim`s is a primitive rule; soundness = α-invariance of `interpTerm`
  -- (= `interpTerm_rename`, twice, casts via `interpTerm_cast`).  The renamed body is `pairElimAlphaBody`
  -- (both indices; freshness side-conditions are the usual on-paper ones).
  | pair_elim_alpha :
      (v₁ v₂ : VarSymb × VarType) → (n₁ n₂ z : VarSymb)
      → (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) → (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
      → (hv₁v₂ : v₁.1 ≠ v₂.1) → (hz : z ∉ VarCtx_to_VarSymbs V)
      → (hn₁ : n₁ ∉ VarCtx_to_VarSymbs V) → (hn₂ : n₂ ∉ VarCtx_to_VarSymbs V)
      → (hn₁v₂ : n₁ ≠ v₂.1) → (hn₁n₂ : n₁ ≠ n₂)
      → (hv₁_nest : v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂))
      → (hn₁_nest : n₁ ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂))
      → (hv₂_nest : v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁))
      → (hn₂_nest : n₂ ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁))
      → (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂
                  = VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest)
      → (w₁'eq : VarCtx_insert_twice ⟨n₁, v₁.2⟩ ⟨n₂, v₂.2⟩ V hn₁ hn₂ hn₁n₂
                  = VarCtx_insert ⟨n₂, v₂.2⟩ (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁) hn₂_nest)
      → (w₂eq : VarCtx_insert ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
      → (body : Term σ (VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest) S)
      → (nnb₁ : n₁ ∉ Term.boundVars body) → (nnb₂ : n₂ ∉ Term.boundVars body)
      → Proof σ W₂ Γ (WFF.eq
          (Term.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body)
          (Term.pair_elim ⟨n₁, v₁.2⟩ ⟨n₂, v₂.2⟩ z hn₁ hn₂ hn₁n₂ hz w₁'eq w₂eq
            (Term.pairElimAlphaBody v₁ v₂ n₁ n₂ hv₂ hn₁ hn₁n₂ hv₁_nest hn₁_nest hv₂_nest
              hn₂_nest body nnb₁ nnb₂)))


