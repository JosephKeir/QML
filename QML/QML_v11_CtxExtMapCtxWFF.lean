import QML.QML_v11_CtxExtMapCtx

/-!
# QML v11 — `ctx_extU` commutes with `mapCtx` for `Rel` and `WFF` (LEMMA A1, second half)

The `WFF` proof is the `Term` one arm for arm, plus the quantifier arms.  ⭐Those are the new part
and they are short: after unfolding, both sides are `all T' (…)`, and the two bodies are `mapCtx` of
the same weakened body along `(m.extendBnd T').extendUser u` and `(m.extendUser u).extendBnd T'`.
Their functions differ only in the ORDER of the `u`-update and the slot-update — commuted by
`VarSymb.update_comm`, since a user name is never a slot.

⚠️The one wrinkle: `ctx_extU`'s quantifier arm transports along `insertBnd_comm_insert`, whose
direction is `insertBnd T' (V + u) = (insertBnd T' V) + u`, i.e. the cast goes AGAINST the
equation.  `h ▸ x` elaborates differently in that direction, so `mapCtx_cast'`, `cast_ofEq'` and
`mapCtx_congr'` restate the existing transport lemmas with the equation reversed.
-/

/-! ## Helpers -/

theorem VarSymb.update_comm (f : VarSymb → VarSymb) (a b c d : VarSymb) (h : a ≠ c) :
    VarSymb.update (VarSymb.update f a b) c d = VarSymb.update (VarSymb.update f c d) a b := by
  funext v
  simp only [VarSymb.update]
  split_ifs <;> simp_all

theorem CtxBij.cast_ofEq' {A B V' : VarCtx} (h : B = A) (m : CtxBij B V') :
    h ▸ (CtxBij.ofEq h.symm m) = m := by subst h; rfl

theorem WFF.mapCtx_cast' {σ : Signature} {A B V' : VarCtx} (h : B = A)
    (m : CtxBij B V') (m' : CtxBij A V') (hm : h ▸ m' = m) (φ : WFF σ A) :
    WFF.mapCtx m (h ▸ φ) = WFF.mapCtx m' φ := by
  subst h; subst hm; rfl

theorem WFF.mapCtx_congr' {σ : Signature} {V V₁ V₂ : VarCtx} (m : CtxBij V V₁)
    (m' : CtxBij V V₂) (h : V₂ = V₁)
    (hf : ∀ v ∈ VarCtx_to_VarSymbs V, m.toCtxMap.f v = m'.toCtxMap.f v)
    (φ : WFF σ V) : h ▸ WFF.mapCtx m φ = WFF.mapCtx m' φ := by
  subst h; exact WFF.mapCtx_congr m m' rfl hf φ

theorem WFF.pair_elim_w₁_cast {σ : Signature} {pe_V W₁ W₂ : VarCtx} {T₁ T₂ : VarType}
    {z : VarSymb} (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ pe_V = W₁)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂) (X : WFF σ W₁) :
    (WFF.pair_elim T₁ T₂ z hz w₁eq w₂eq X : WFF σ W₂)
      = WFF.pair_elim T₁ T₂ z hz rfl w₂eq (w₁eq.symm ▸ X) := by
  subst w₁eq; rfl

/-! ## `ctx_extU` computation rules not already available -/

theorem Rel.ctx_extU_eval {σ : Signature} {V : VarCtx} {n : ℕ} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (R' : Rel σ V (n + 1)) (t : Term σ V .Var) :
    Rel.ctx_extU u T hu (Rel.eval R' t)
      = Rel.eval (Rel.ctx_extU u T hu R') (Term.ctx_extU u T hu t) := rfl

theorem WFF.ctx_extU_atom {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (R : Rel σ V 0) :
    WFF.ctx_extU u T hu (WFF.atom R) = WFF.atom (Rel.ctx_extU u T hu R) := by
  conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_or {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (φ ψ : WFF σ V) :
    WFF.ctx_extU u T hu (WFF.or φ ψ)
      = WFF.or (WFF.ctx_extU u T hu φ) (WFF.ctx_extU u T hu ψ) := by
  conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_all {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (T' : VarType) (ψ : WFF σ (VarCtx.insertBnd T' V))
    (hu_bnd : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T' V))
    (hc : VarCtx.insertBnd T' (VarCtx_insert ⟨u.toVar, T⟩ V hu)
            = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T' V) hu_bnd) :
    WFF.ctx_extU u T hu (WFF.all T' ψ) = WFF.all T' (hc ▸ WFF.ctx_extU u T hu_bnd ψ) := by
  conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_ex {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (T' : VarType) (ψ : WFF σ (VarCtx.insertBnd T' V))
    (hu_bnd : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T' V))
    (hc : VarCtx.insertBnd T' (VarCtx_insert ⟨u.toVar, T⟩ V hu)
            = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T' V) hu_bnd) :
    WFF.ctx_extU u T hu (WFF.ex T' ψ) = WFF.ex T' (hc ▸ WFF.ctx_extU u T hu_bnd ψ) := by
  conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_pair_elim {σ : Signature} {pe_V W₁ W₂ : VarCtx} {T₁ T₂ : VarType}
    {z : VarSymb} (u : UserSymb) (T : VarType) (hu : u.toVar ∉ VarCtx_to_VarSymbs W₂)
    (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ pe_V = W₁)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂) (body : WFF σ W₁)
    (hu_pe : u.toVar ∉ VarCtx_to_VarSymbs pe_V)
    (hz' : z ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe))
    (hu_W₁ : u.toVar ∉ VarCtx_to_VarSymbs W₁)
    (w₁eq' : VarCtx.insertBnd2 T₁ T₂ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe)
               = VarCtx_insert ⟨u.toVar, T⟩ W₁ hu_W₁)
    (w₂eq' : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe) hz'
               = VarCtx_insert ⟨u.toVar, T⟩ W₂ hu) :
    WFF.ctx_extU u T hu (WFF.pair_elim T₁ T₂ z hz w₁eq w₂eq body)
      = WFF.pair_elim T₁ T₂ z hz' w₁eq' w₂eq' (WFF.ctx_extU u T hu_W₁ body) := by
  subst w₂eq
  conv_lhs => unfold WFF.ctx_extU

/-! ## `Rel` -/

theorem Rel.ctx_extU_mapCtx {σ : Signature} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false) {V V' : VarCtx} (m : CtxBij V V')
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (hu' : u.toVar ∉ VarCtx_to_VarSymbs V') :
    ∀ {n : ℕ} (R : Rel σ V n),
      Rel.ctx_extU u T hu' (Rel.mapCtx m R)
        = Rel.mapCtx (m.extendUser u.toVar T hu hu') (Rel.ctx_extU u T hu R)
  | _, .R _ => rfl
  | _, .eval R' t => by
      rw [Rel.mapCtx_eval, Rel.ctx_extU_eval, Rel.ctx_extU_eval, Rel.mapCtx_eval,
          Rel.ctx_extU_mapCtx u T hTb hTp m hu hu' R',
          Term.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' _ t]

/-! ## `WFF` -/

theorem WFF.ctx_extU_mapCtx {σ : Signature} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false) :
    ∀ (V V' : VarCtx) (m : CtxBij V V') (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
      (hu' : u.toVar ∉ VarCtx_to_VarSymbs V') (φ : WFF σ V),
      WFF.ctx_extU u T hu' (WFF.mapCtx m φ)
        = WFF.mapCtx (m.extendUser u.toVar T hu hu') (WFF.ctx_extU u T hu φ)
  | _, _, m, hu, hu', .atom R => by
      rw [WFF.mapCtx_atom, WFF.ctx_extU_atom, WFF.ctx_extU_atom, WFF.mapCtx_atom,
          Rel.ctx_extU_mapCtx u T hTb hTp m hu hu' R]
  | _, _, m, hu, hu', .top => by
      rw [WFF.mapCtx_top, WFF.ctx_extU_top, WFF.ctx_extU_top, WFF.mapCtx_top]
  | _, _, m, hu, hu', .bot => by
      rw [WFF.mapCtx_bot, WFF.ctx_extU_bot, WFF.ctx_extU_bot, WFF.mapCtx_bot]
  | V, V', m, hu, hu', .and φ ψ => by
      rw [WFF.mapCtx_and, WFF.ctx_extU_and, WFF.ctx_extU_and, WFF.mapCtx_and,
          WFF.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' φ,
          WFF.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' ψ]
  | V, V', m, hu, hu', .or φ ψ => by
      rw [WFF.mapCtx_or, WFF.ctx_extU_or, WFF.ctx_extU_or, WFF.mapCtx_or,
          WFF.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' φ,
          WFF.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' ψ]
  | V, V', m, hu, hu', .imp φ ψ => by
      rw [WFF.mapCtx_imp, WFF.ctx_extU_imp, WFF.ctx_extU_imp, WFF.mapCtx_imp,
          WFF.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' φ,
          WFF.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' ψ]
  | V, V', m, hu, hu', .eq s t => by
      rw [WFF.mapCtx_eq, WFF.ctx_extU_eq, WFF.ctx_extU_eq, WFF.mapCtx_eq,
          Term.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' _ s,
          Term.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' _ t]
  -- ⭐The quantifier arms: the `u`-update and the slot-update in the other order.
  | V, V', m, hu, hu', .all T' ψ => by
      have hu_bnd : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T' V) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T' hu
      have hu_bnd' : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T' V') :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T' hu'
      have hc : VarCtx.insertBnd T' (VarCtx_insert ⟨u.toVar, T⟩ V hu)
          = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T' V) hu_bnd :=
        VarCtx.insertBnd_comm_insert ⟨u.toVar, T⟩ V hu rfl T' hu_bnd
      have hc' : VarCtx.insertBnd T' (VarCtx_insert ⟨u.toVar, T⟩ V' hu')
          = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T' V') hu_bnd' :=
        VarCtx.insertBnd_comm_insert ⟨u.toVar, T⟩ V' hu' rfl T' hu_bnd'
      have IH := WFF.ctx_extU_mapCtx u T hTb hTp _ _ (m.extendBnd T') hu_bnd hu_bnd' ψ
      have hf : ∀ v ∈ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T' V) hu_bnd),
          ((m.extendBnd T').extendUser u.toVar T hu_bnd hu_bnd').toCtxMap.f v
            = (CtxBij.ofEq hc.symm
                ((m.extendUser u.toVar T hu hu').extendBnd T')).toCtxMap.f v := by
        intro v _
        simp only [CtxBij.extendUser_f, CtxBij.ofEq_f, CtxBij.extendBnd_f]
        rw [VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ V hu rfl,
            VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ V' hu' rfl,
            VarSymb.update_comm _ _ _ _ _ (Ne.symm (VarCtx.ne_nextBnd_of_isUsr rfl V))]
      rw [WFF.mapCtx_all, WFF.ctx_extU_all u T hu' T' _ hu_bnd' hc', IH,
          WFF.ctx_extU_all u T hu T' ψ hu_bnd hc, WFF.mapCtx_all,
          WFF.mapCtx_cast' hc ((m.extendUser u.toVar T hu hu').extendBnd T')
            (CtxBij.ofEq hc.symm ((m.extendUser u.toVar T hu hu').extendBnd T'))
            (CtxBij.cast_ofEq' hc _)]
      exact congrArg (WFF.all T') (WFF.mapCtx_congr' _ _ hc' hf _)
  | V, V', m, hu, hu', .ex T' ψ => by
      have hu_bnd : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T' V) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T' hu
      have hu_bnd' : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T' V') :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T' hu'
      have hc : VarCtx.insertBnd T' (VarCtx_insert ⟨u.toVar, T⟩ V hu)
          = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T' V) hu_bnd :=
        VarCtx.insertBnd_comm_insert ⟨u.toVar, T⟩ V hu rfl T' hu_bnd
      have hc' : VarCtx.insertBnd T' (VarCtx_insert ⟨u.toVar, T⟩ V' hu')
          = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T' V') hu_bnd' :=
        VarCtx.insertBnd_comm_insert ⟨u.toVar, T⟩ V' hu' rfl T' hu_bnd'
      have IH := WFF.ctx_extU_mapCtx u T hTb hTp _ _ (m.extendBnd T') hu_bnd hu_bnd' ψ
      have hf : ∀ v ∈ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T' V) hu_bnd),
          ((m.extendBnd T').extendUser u.toVar T hu_bnd hu_bnd').toCtxMap.f v
            = (CtxBij.ofEq hc.symm
                ((m.extendUser u.toVar T hu hu').extendBnd T')).toCtxMap.f v := by
        intro v _
        simp only [CtxBij.extendUser_f, CtxBij.ofEq_f, CtxBij.extendBnd_f]
        rw [VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ V hu rfl,
            VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ V' hu' rfl,
            VarSymb.update_comm _ _ _ _ _ (Ne.symm (VarCtx.ne_nextBnd_of_isUsr rfl V))]
      rw [WFF.mapCtx_ex, WFF.ctx_extU_ex u T hu' T' _ hu_bnd' hc', IH,
          WFF.ctx_extU_ex u T hu T' ψ hu_bnd hc, WFF.mapCtx_ex,
          WFF.mapCtx_cast' hc ((m.extendUser u.toVar T hu hu').extendBnd T')
            (CtxBij.ofEq hc.symm ((m.extendUser u.toVar T hu hu').extendBnd T'))
            (CtxBij.cast_ofEq' hc _)]
      exact congrArg (WFF.ex T') (WFF.mapCtx_congr' _ _ hc' hf _)
  | V, V', m, hu, hu', .box inner hsub hne => by
      rename_i V_inner
      have hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_box_sub hsub
      have hsubE : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1 :=
        box_sub_insert_pass hsub
      have hneE : ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
          VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1 :=
        box_extras_insert_pass hTb hne
      have hUE : ∀ v ∈ VarCtx_to_VarSymbs V_inner,
          v ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ V hu) :=
        VarCtx.symbs_of_box_sub hsubE
      have hf : ∀ v ∈ VarCtx_to_VarSymbs V_inner,
          m.toCtxMap.f v = (m.extendUser u.toVar T hu hu').toCtxMap.f v := by
        intro v hv
        have hvne : v ≠ u.toVar := fun h => hu (h ▸ hU v hv)
        exact (VarSymb.update_of_ne _ hvne).symm
      have hI : m.imageCtx V_inner hU = (m.extendUser u.toVar T hu hu').imageCtx V_inner hUE :=
        CtxBij.imageCtx_congr m _ V_inner hU hUE hf
      have hX := WFF.mapCtx_congr (m.toImage V_inner hU)
        ((m.extendUser u.toVar T hu hu').toImage V_inner hUE) hI hf inner
      rw [WFF.mapCtx_box m inner hsub hne hU (CtxBij.box_sub_image m hsub hU)
            (CtxBij.box_extras_image m hne hU),
          WFF.ctx_extU_box_pass u T hTb hTp hu' _ _ _
            (box_sub_insert_pass (CtxBij.box_sub_image m hsub hU))
            (box_extras_insert_pass hTb (CtxBij.box_extras_image m hne hU)),
          WFF.ctx_extU_box_pass u T hTb hTp hu inner hsub hne hsubE hneE,
          WFF.mapCtx_box _ inner hsubE hneE hUE
            (CtxBij.box_sub_image _ hsubE hUE) (CtxBij.box_extras_image _ hneE hUE)]
      exact WFF.box_congr' hI _ _ hX _ _ _ _
  | V, V', m, hu, hu', .dia x hx χ hsub hne => by
      rename_i V_inner
      have hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_dia_sub hsub
      have hxV : x.1 ∈ VarCtx_to_VarSymbs V :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub, rfl⟩
      have hx'm := CtxBij.notMem_imageCtx m hU hxV hx
      have hsubm := CtxBij.dia_sub_image m hsub hU hx'm
      have hnem := CtxBij.dia_extras_image m hne hU hx'm
      have hsubE : (VarCtx_dia x V_inner hx).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1 :=
        dia_sub_insert_pass hsub
      have hneE : ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
          VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V_inner hx).1 :=
        dia_extras_insert_pass hTb hne
      have hUE : ∀ v ∈ VarCtx_to_VarSymbs V_inner,
          v ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ V hu) :=
        VarCtx.symbs_of_dia_sub hsubE
      have hxVE : x.1 ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ V hu) :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsubE, rfl⟩
      have hx'E := CtxBij.notMem_imageCtx (m.extendUser u.toVar T hu hu') hUE hxVE hx
      have hsubE' := CtxBij.dia_sub_image (m.extendUser u.toVar T hu hu') hsubE hUE hx'E
      have hneE' := CtxBij.dia_extras_image (m.extendUser u.toVar T hu hu') hneE hUE hx'E
      have hfV : ∀ v ∈ VarCtx_to_VarSymbs V,
          m.toCtxMap.f v = (m.extendUser u.toVar T hu hu').toCtxMap.f v := by
        intro v hv
        have hvne : v ≠ u.toVar := fun h => hu (h ▸ hv)
        exact (VarSymb.update_of_ne _ hvne).symm
      have hxx : (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType)
          = ⟨(m.extendUser u.toVar T hu hu').toCtxMap.f x.1, x.2⟩ := by
        rw [← hfV x.1 hxV]
      have hI : m.imageCtx V_inner hU = (m.extendUser u.toVar T hu hu').imageCtx V_inner hUE :=
        CtxBij.imageCtx_congr m _ V_inner hU hUE (fun v hv => hfV v (hU v hv))
      have hCtx : VarCtx_insert (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType)
            (m.imageCtx V_inner hU) hx'm
          = VarCtx_insert ⟨(m.extendUser u.toVar T hu hu').toCtxMap.f x.1, x.2⟩
              ((m.extendUser u.toVar T hu hu').imageCtx V_inner hUE) hx'E := by
        refine VarCtx_ext _ _ ?_
        change insert (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType) (m.imageCtx V_inner hU).1
            = insert (⟨(m.extendUser u.toVar T hu hu').toCtxMap.f x.1, x.2⟩
                : VarSymb × VarType) ((m.extendUser u.toVar T hu hu').imageCtx V_inner hUE).1
        rw [hxx, hI]
      have hf' : ∀ v ∈ VarCtx_to_VarSymbs (VarCtx_insert x V_inner hx),
          (m.extendPoint V_inner hU x hxV hx hx'm).toCtxMap.f v
            = ((m.extendUser u.toVar T hu hu').extendPoint V_inner hUE x hxVE hx hx'E).toCtxMap.f v
          := by
        intro v hv
        rw [VarCtx_to_VarSymbs_insert] at hv
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact hfV _ hxV
        · exact hfV v (hU v hv')
      have hX := WFF.mapCtx_congr (m.extendPoint V_inner hU x hxV hx hx'm)
        ((m.extendUser u.toVar T hu hu').extendPoint V_inner hUE x hxVE hx hx'E) hCtx hf' χ
      rw [WFF.mapCtx_dia m hx χ hsub hne hU hxV hx'm hsubm hnem,
          WFF.ctx_extU_dia_pass u T hTb hTp hu' hx'm _ hsubm hnem
            (dia_sub_insert_pass hsubm) (dia_extras_insert_pass hTb hnem),
          WFF.ctx_extU_dia_pass u T hTb hTp hu hx χ hsub hne hsubE hneE,
          WFF.mapCtx_dia (m.extendUser u.toVar T hu hu') hx χ hsubE hneE hUE hxVE hx'E
            hsubE' hneE']
      exact WFF.dia_congr' hxx hI _ _ hCtx hX _ _ _ _
  | V, V', m, hu, hu', .pair_elim T₁ T₂ z hz w₁eq w₂eq body => by
      rename_i pe_V pe_W₁
      have IH : ∀ (A : VarCtx) (M : CtxBij pe_W₁ A) (hA : u.toVar ∉ VarCtx_to_VarSymbs pe_W₁)
          (hA' : u.toVar ∉ VarCtx_to_VarSymbs A),
          WFF.ctx_extU u T hA' (WFF.mapCtx M body)
            = WFF.mapCtx (M.extendUser u.toVar T hA hA') (WFF.ctx_extU u T hA body) :=
        fun A M hA hA' => WFF.ctx_extU_mapCtx u T hTb hTp pe_W₁ A M hA hA' body
      subst w₂eq
      subst w₁eq
      have hzne : z ≠ u.toVar := fun h =>
        hu (by rw [VarCtx_to_VarSymbs_insert, ← h]; exact Finset.mem_insert_self _ _)
      have hu_pe : u.toVar ∉ VarCtx_to_VarSymbs pe_V := fun hm =>
        hu (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem hm)
      have hu_bnd2 : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd2 T₁ T₂ pe_V) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T₂ (VarCtx.notMem_insertBnd_of_isUsr rfl T₁ hu_pe)
      have hzV₁ : (⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩ : VarSymb × VarType) ∈ V'.1 :=
        m.toCtxMap.maps _ (Finset.mem_insert_self _ _)
      have hz₁ : m.toCtxMap.f z
          ∉ VarCtx_to_VarSymbs (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) :=
        VarCtx_erase_fresh hzV₁
      have w₂eq₁ : VarCtx_insert ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩
          (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) hz₁ = V' :=
        VarCtx_insert_erase hzV₁ hz₁
      have hu_E₁ : u.toVar
          ∉ VarCtx_to_VarSymbs (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) :=
        fun h => hu' (VarCtx_to_VarSymbs_erase_subset h)
      have hmz_ne : m.toCtxMap.f z ≠ u.toVar := fun h =>
        hu' (h ▸ Finset.mem_image.mpr ⟨_, hzV₁, rfl⟩)
      have hz₁' : m.toCtxMap.f z ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩
          (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) hu_E₁) :=
        not_mem_VarSymbs_insert hmz_ne hz₁
      have hu_bnd2E₁ : u.toVar ∉ VarCtx_to_VarSymbs
          (VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩)) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T₂ (VarCtx.notMem_insertBnd_of_isUsr rfl T₁ hu_E₁)
      have w₁eqL : VarCtx.insertBnd2 T₁ T₂ (VarCtx_insert ⟨u.toVar, T⟩
            (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) hu_E₁)
          = VarCtx_insert ⟨u.toVar, T⟩
            (VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩))
            hu_bnd2E₁ :=
        VarCtx.insertBnd2_comm_insert ⟨u.toVar, T⟩ _ hu_E₁ rfl T₁ T₂ hu_bnd2E₁
      have w₂eqL : VarCtx_insert ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩ (VarCtx_insert ⟨u.toVar, T⟩
            (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) hu_E₁) hz₁'
          = VarCtx_insert ⟨u.toVar, T⟩ V' hu' := by
        refine VarCtx_ext _ _ ?_
        change insert (⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩ : VarSymb × VarType)
            (insert (⟨u.toVar, T⟩ : VarSymb × VarType)
              (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩).1)
          = insert (⟨u.toVar, T⟩ : VarSymb × VarType) V'.1
        rw [Finset.insert_comm]
        congr 1
        exact congrArg (fun W : VarCtx => W.1) w₂eq₁
      have hz' : z ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe) :=
        not_mem_VarSymbs_insert hzne hz
      have w₁eqR : VarCtx.insertBnd2 T₁ T₂ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe)
          = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd2 T₁ T₂ pe_V) hu_bnd2 :=
        VarCtx.insertBnd2_comm_insert ⟨u.toVar, T⟩ pe_V hu_pe rfl T₁ T₂ hu_bnd2
      have w₂eqR : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe) hz'
          = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz) hu :=
        VarCtx_insert_comm hz' (not_mem_VarSymbs_insert (Ne.symm hzne) hu_pe)
      have hzVE : (⟨(CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z,
          T₁.VTypeProd T₂⟩ : VarSymb × VarType) ∈ (VarCtx_insert ⟨u.toVar, T⟩ V' hu').1 :=
        (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.maps _
          (Finset.mem_insert_self _ _)
      have hzE : (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z
          ∉ VarCtx_to_VarSymbs (VarCtx_erase (VarCtx_insert ⟨u.toVar, T⟩ V' hu')
              ⟨(CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z,
                T₁.VTypeProd T₂⟩) :=
        VarCtx_erase_fresh hzVE
      have w₂eqE : VarCtx_insert
          ⟨(CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z, T₁.VTypeProd T₂⟩
          (VarCtx_erase (VarCtx_insert ⟨u.toVar, T⟩ V' hu')
            ⟨(CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z,
              T₁.VTypeProd T₂⟩) hzE
          = VarCtx_insert ⟨u.toVar, T⟩ V' hu' :=
        VarCtx_insert_erase hzVE hzE
      rw [WFF.mapCtx_pair_elim hz body m hz₁ w₂eq₁,
          WFF.ctx_extU_pair_elim u T hu' hz₁ rfl w₂eq₁ _ hu_E₁ hz₁' hu_bnd2E₁ w₁eqL w₂eqL,
          IH _ (((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂) hu_bnd2 hu_bnd2E₁,
          WFF.ctx_extU_pair_elim u T hu hz rfl rfl body hu_pe hz' hu_bnd2 w₁eqR w₂eqR,
          WFF.pair_elim_w₁_cast hz' w₁eqR w₂eqR,
          WFF.pair_elim_as_cast hz' _ w₂eqR,
          WFF.mapCtx_cast w₂eqR (m.extendUser u.toVar T hu hu')
            (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))
            (CtxBij.cast_ofEq w₂eqR (m.extendUser u.toVar T hu hu')),
          WFF.mapCtx_pair_elim hz' _ (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')) hzE
            w₂eqE,
          WFF.mapCtx_cast w₁eqR.symm
            (((CtxBij.restrictInsert hz'
              (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))).extendBnd T₁).extendBnd T₂)
            (CtxBij.ofEq w₁eqR.symm (((CtxBij.restrictInsert hz'
              (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))).extendBnd T₁).extendBnd T₂))
            (CtxBij.cast_ofEq w₁eqR.symm _)]
      have hzz : m.toCtxMap.f z
          = (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z :=
        (VarSymb.update_of_ne _ hzne).symm
      have hB : VarCtx_insert ⟨u.toVar, T⟩
            (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) hu_E₁
          = VarCtx_erase (VarCtx_insert ⟨u.toVar, T⟩ V' hu')
              ⟨(CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z,
                T₁.VTypeProd T₂⟩ := by
        rw [← hzz]
        refine VarCtx_ext _ _ ?_
        change insert (⟨u.toVar, T⟩ : VarSymb × VarType)
            (V'.1.erase ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩)
          = (insert (⟨u.toVar, T⟩ : VarSymb × VarType) V'.1).erase
              ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩
        rw [Finset.erase_insert_of_ne (fun h => hmz_ne (congrArg Prod.fst h).symm)]
      have hW : VarCtx_insert ⟨u.toVar, T⟩
            (VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩))
            hu_bnd2E₁
          = VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase (VarCtx_insert ⟨u.toVar, T⟩ V' hu')
              ⟨(CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z,
                T₁.VTypeProd T₂⟩) := by
        rw [← w₁eqL, hB]
      have hc₁ : (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe).nextBnd = pe_V.nextBnd :=
        VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ pe_V hu_pe rfl
      have hd₁ : (VarCtx_erase (VarCtx_insert ⟨u.toVar, T⟩ V' hu')
            ⟨(CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z,
              T₁.VTypeProd T₂⟩).nextBnd
          = (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩).nextBnd := by
        rw [← hB]
        exact VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ _ hu_E₁ rfl
      have h1p : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T₁ pe_V) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T₁ hu_pe
      have hc₂ : (VarCtx.insertBnd T₁ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe)).nextBnd
          = (VarCtx.insertBnd T₁ pe_V).nextBnd := by
        rw [VarCtx.insertBnd_comm_insert ⟨u.toVar, T⟩ pe_V hu_pe rfl T₁ h1p]
        exact VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ _ h1p rfl
      have h1E : u.toVar ∉ VarCtx_to_VarSymbs
          (VarCtx.insertBnd T₁ (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩)) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T₁ hu_E₁
      have hd₂ : (VarCtx.insertBnd T₁ (VarCtx_erase (VarCtx_insert ⟨u.toVar, T⟩ V' hu')
            ⟨(CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')).toCtxMap.f z,
              T₁.VTypeProd T₂⟩)).nextBnd
          = (VarCtx.insertBnd T₁ (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩)).nextBnd := by
        rw [← hB, VarCtx.insertBnd_comm_insert ⟨u.toVar, T⟩ _ hu_E₁ rfl T₁ h1E]
        exact VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ _ h1E rfl
      have hua₁ : u.toVar ≠ pe_V.nextBnd := VarCtx.ne_nextBnd_of_isUsr rfl pe_V
      have hua₂ : u.toVar ≠ (VarCtx.insertBnd T₁ pe_V).nextBnd :=
        VarCtx.ne_nextBnd_of_isUsr rfl _
      have hfB : ∀ v ∈ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd2 T₁ T₂ pe_V) hu_bnd2),
          ((((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂).extendUser
              u.toVar T hu_bnd2 hu_bnd2E₁).toCtxMap.f v
            = (CtxBij.ofEq w₁eqR.symm (((CtxBij.restrictInsert hz'
                (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))).extendBnd T₁).extendBnd
                  T₂)).toCtxMap.f v := by
        intro v _
        simp only [CtxBij.extendUser_f, CtxBij.ofEq_f, CtxBij.extendBnd_f,
          CtxBij.restrictInsert_f]
        simp only [CtxBij.extendUser_f, CtxBij.ofEq_f] at hd₁ hd₂
        rw [hc₁, hd₁, hc₂, hd₂, VarSymb.update_comm _ _ _ _ _ (Ne.symm hua₂),
          VarSymb.update_comm _ _ _ _ _ (Ne.symm hua₁)]
      have hX := WFF.mapCtx_congr
        ((((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂).extendUser
          u.toVar T hu_bnd2 hu_bnd2E₁)
        (CtxBij.ofEq w₁eqR.symm (((CtxBij.restrictInsert hz'
          (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))).extendBnd T₁).extendBnd T₂))
        hW hfB (WFF.ctx_extU u T hu_bnd2 body)
      exact WFF.pair_elim_congr' hzz hB hW _ _ _ _ _ _ hX
  termination_by _ _ _ _ _ φ => sizeOf φ
