import QML.QML_v11_EqComm
import QML.QML_v11_MapCtxId

/-!
# QML v11 — `ctx_extU` commutes with `mapCtx` (LEMMA A1)

For a PASS-THROUGH weakening type `T` (neither box- nor product-typed):

    ctx_extU u (mapCtx m t)  =  mapCtx (m.extendUser u) (ctx_extU u t)

where `m.extendUser u` is `m` extended by fixing `u` (its function is `update m.f u u`).

⭐**The modal arms need no induction hypothesis**, for the same reason as in `eqRec_ctx_extU_pass`:
a pass-through weakening leaves a box's or dia's interior untouched, so both sides image the SAME
interior — along `m.f` on one side and `update m.f u u` on the other.  Those agree on the interior
(it cannot mention `u`) but land in image contexts that are only propositionally equal, which is
exactly what `imageCtx_congr` and `mapCtx_congr` absorb.
-/

/-! ## Extending a bijection by a fixed user variable -/

def CtxBij.extendUser {V V' : VarCtx} (m : CtxBij V V') (u : VarSymb) (T : VarType)
    (hu : u ∉ VarCtx_to_VarSymbs V) (hu' : u ∉ VarCtx_to_VarSymbs V') :
    CtxBij (VarCtx_insert ⟨u, T⟩ V hu) (VarCtx_insert ⟨u, T⟩ V' hu') where
  f := VarSymb.update m.toCtxMap.f u u
  inj := by
    have hmV' : ∀ c ∈ VarCtx_to_VarSymbs V, m.toCtxMap.f c ∈ VarCtx_to_VarSymbs V' := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨m.toCtxMap.f p.1, p.2⟩, m.toCtxMap.maps p hp, rfl⟩
    intro a ha b hb hab
    rw [VarCtx_to_VarSymbs_insert] at ha hb
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · rfl
      · have hbne : b ≠ a := fun h => hu (h ▸ hb')
        rw [VarSymb.update_self, VarSymb.update_of_ne _ hbne] at hab
        exact absurd (hab ▸ hmV' b hb' : a ∈ VarCtx_to_VarSymbs V') hu'
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · have hane : a ≠ b := fun h => hu (h ▸ ha')
        rw [VarSymb.update_self, VarSymb.update_of_ne _ hane] at hab
        exact absurd (hab ▸ hmV' a ha' : b ∈ VarCtx_to_VarSymbs V') hu'
      · have hane : a ≠ u := fun h => hu (h ▸ ha')
        have hbne : b ≠ u := fun h => hu (h ▸ hb')
        rw [VarSymb.update_of_ne _ hane, VarSymb.update_of_ne _ hbne] at hab
        exact m.toCtxMap.inj a ha' b hb' hab
  maps := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · simp only [VarSymb.update_self]
      exact Finset.mem_insert_self _ _
    · have hpne : p.1 ≠ u := fun h => hu (h ▸ Finset.mem_image.mpr ⟨p, hp', rfl⟩)
      rw [VarSymb.update_of_ne _ hpne]
      exact Finset.mem_insert_of_mem (m.toCtxMap.maps p hp')
  onto := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact ⟨⟨u, T⟩, Finset.mem_insert_self _ _, by simp [VarSymb.update_self]⟩
    · obtain ⟨q, hq, hqeq⟩ := m.onto p hp'
      have hqne : q.1 ≠ u := fun h => hu (h ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      refine ⟨q, Finset.mem_insert_of_mem hq, ?_⟩
      rw [VarSymb.update_of_ne _ hqne]
      exact hqeq

@[simp] theorem CtxBij.extendUser_f {V V' : VarCtx} (m : CtxBij V V') (u : VarSymb)
    (T : VarType) (hu : u ∉ VarCtx_to_VarSymbs V) (hu' : u ∉ VarCtx_to_VarSymbs V') :
    (m.extendUser u T hu hu').toCtxMap.f = VarSymb.update m.toCtxMap.f u u := rfl

/-- Images depend only on the function on the imaged context (not on the source). -/
theorem CtxBij.imageCtx_congr {V W V₁ V₂ : VarCtx} (m : CtxBij V V₁) (m' : CtxBij W V₂)
    (U : VarCtx) (h : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V)
    (h' : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs W)
    (hf : ∀ v ∈ VarCtx_to_VarSymbs U, m.toCtxMap.f v = m'.toCtxMap.f v) :
    m.imageCtx U h = m'.imageCtx U h' := by
  refine VarCtx_ext _ _ ?_
  rw [CtxBij.imageCtx_fst, CtxBij.imageCtx_fst]
  refine Finset.image_congr ?_
  intro p hp
  have hfp := hf p.1 (Finset.mem_image.mpr ⟨p, Finset.mem_coe.mp hp, rfl⟩)
  simp only [hfp]

/-! ## `ctx_extU` computation rules not already in `QML_v11_EqComm` -/

theorem Term.ctx_extU_var {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {v : VarSymb}
    (hv : (⟨v, VarType.Var⟩ : VarSymb × VarType) ∈ V.1) :
    Term.ctx_extU u T hu (Term.var ⟨v, hv⟩ : Term σ V .Var)
      = Term.var ⟨v, Finset.mem_insert_of_mem hv⟩ := by
  conv_lhs => unfold Term.ctx_extU

theorem Term.ctx_extU_func {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (fn : Func σ V 0) :
    Term.ctx_extU u T hu (Term.func fn) = Term.func (Func.ctx_extU u T hu fn) := by
  conv_lhs => unfold Term.ctx_extU

theorem Term.ctx_extU_unit {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) :
    Term.ctx_extU u T hu (Term.unit : Term σ V .VTypeOne) = Term.unit := by
  conv_lhs => unfold Term.ctx_extU

theorem Func.ctx_extU_F {σ : Signature} {V : VarCtx} {N : ℕ} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (hr : {f // σ.funcArity f = N}) :
    Func.ctx_extU u T hu (Func.F hr : Func σ V N) = Func.F hr := by
  conv_lhs => unfold Func.ctx_extU

theorem Func.ctx_extU_eval {σ : Signature} {V : VarCtx} {N : ℕ} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (g : Func σ V (N + 1)) (t : Term σ V .Var) :
    Func.ctx_extU u T hu (Func.eval g t)
      = Func.eval (Func.ctx_extU u T hu g) (Term.ctx_extU u T hu t) := by
  conv_lhs => unfold Func.ctx_extU

/-- The `ctx_extU` rule for `pair_elim`, for ANY output equation `w₂eq` — `ctx_extU` substitutes it
    itself, so a general form is available (unlike `mapCtx`, whose rule has to be the `rfl` form).
    The destructured variable keeps its name; the new user entry goes under it. -/
theorem Term.ctx_extU_pair_elim {σ : Signature} {pe_V W₁ W₂ : VarCtx} {T₁ T₂ S : VarType}
    {z : VarSymb} (u : UserSymb) (T : VarType) (hu : u.toVar ∉ VarCtx_to_VarSymbs W₂)
    (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ pe_V = W₁)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂) (body : Term σ W₁ S)
    (hu_pe : u.toVar ∉ VarCtx_to_VarSymbs pe_V)
    (hz' : z ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe))
    (hu_W₁ : u.toVar ∉ VarCtx_to_VarSymbs W₁)
    (w₁eq' : VarCtx.insertBnd2 T₁ T₂ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe)
               = VarCtx_insert ⟨u.toVar, T⟩ W₁ hu_W₁)
    (w₂eq' : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe) hz'
               = VarCtx_insert ⟨u.toVar, T⟩ W₂ hu) :
    Term.ctx_extU u T hu (Term.pair_elim T₁ T₂ z hz w₁eq w₂eq body)
      = Term.pair_elim T₁ T₂ z hz' w₁eq' w₂eq' (Term.ctx_extU u T hu_W₁ body) := by
  subst w₂eq
  conv_lhs => unfold Term.ctx_extU

/-- Move a non-`rfl` body equation onto the body, so the `rfl`-form `mapCtx` rule can fire. -/
theorem Term.pair_elim_w₁_cast {σ : Signature} {pe_V W₁ W₂ : VarCtx} {T₁ T₂ S : VarType}
    {z : VarSymb} (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ pe_V = W₁)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂) (X : Term σ W₁ S) :
    (Term.pair_elim T₁ T₂ z hz w₁eq w₂eq X : Term σ W₂ S)
      = Term.pair_elim T₁ T₂ z hz rfl w₂eq (w₁eq.symm ▸ X) := by
  subst w₁eq; rfl

/-! ## LEMMA A1 for `Term` / `Func` -/

mutual
theorem Term.ctx_extU_mapCtx {σ : Signature} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false) :
    ∀ (V V' : VarCtx) (m : CtxBij V V') (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
      (hu' : u.toVar ∉ VarCtx_to_VarSymbs V') (S : VarType) (t : Term σ V S),
      Term.ctx_extU u T hu' (Term.mapCtx m t)
        = Term.mapCtx (m.extendUser u.toVar T hu hu') (Term.ctx_extU u T hu t)
  | V, _, m, hu, hu', _, .var ⟨v, hv⟩ => by
      have hvne : v ≠ u.toVar := fun h => hu (h ▸ Finset.mem_image.mpr ⟨_, hv, rfl⟩)
      rw [Term.mapCtx_var m hv (m.toCtxMap.maps _ hv), Term.ctx_extU_var, Term.ctx_extU_var,
          Term.mapCtx_var _ _ ((m.extendUser u.toVar T hu hu').toCtxMap.maps _
            (Finset.mem_insert_of_mem hv))]
      congr 1
      apply Subtype.ext
      exact (VarSymb.update_of_ne _ hvne).symm
  | V, V', m, hu, hu', _, .func fn => by
      rw [Term.mapCtx_func, Term.ctx_extU_func, Term.ctx_extU_func, Term.mapCtx_func,
          Func.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' _ fn]
  | _, _, m, hu, hu', _, .unit => by
      rw [Term.mapCtx_unit, Term.ctx_extU_unit, Term.ctx_extU_unit, Term.mapCtx_unit]
  | V, V', m, hu, hu', _, .pair a b => by
      rw [Term.mapCtx_pair, Term.ctx_extU_pair, Term.ctx_extU_pair, Term.mapCtx_pair,
          Term.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' _ a,
          Term.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' _ b]
  | V, V', m, hu, hu', _, .boxterm tt hsub hne => by
      rename_i V_inner _
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
      have hX := Term.mapCtx_congr (m.toImage V_inner hU)
        ((m.extendUser u.toVar T hu hu').toImage V_inner hUE) hI hf tt
      rw [Term.mapCtx_boxterm m tt hsub hne hU (CtxBij.box_sub_image m hsub hU)
            (CtxBij.box_extras_image m hne hU),
          Term.ctx_extU_boxterm_pass u T hTb hTp hu' _ _ _
            (box_sub_insert_pass (CtxBij.box_sub_image m hsub hU))
            (box_extras_insert_pass hTb (CtxBij.box_extras_image m hne hU)),
          Term.ctx_extU_boxterm_pass u T hTb hTp hu tt hsub hne hsubE hneE,
          Term.mapCtx_boxterm _ tt hsubE hneE hUE
            (CtxBij.box_sub_image _ hsubE hUE) (CtxBij.box_extras_image _ hneE hUE)]
      exact Term.boxterm_congr' hI _ _ hX _ _ _ _
  | V, V', m, hu, hu', _, .diaterm x hx tt hsub hne => by
      rename_i V_inner _
      -- the `m` side
      have hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_dia_sub hsub
      have hxV : x.1 ∈ VarCtx_to_VarSymbs V :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub, rfl⟩
      have hx'm := CtxBij.notMem_imageCtx m hU hxV hx
      have hsubm := CtxBij.dia_sub_image m hsub hU hx'm
      have hnem := CtxBij.dia_extras_image m hne hU hx'm
      -- the `extendUser` side
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
      -- the two functions agree on everything the interior can mention
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
      have hX := Term.mapCtx_congr (m.extendPoint V_inner hU x hxV hx hx'm)
        ((m.extendUser u.toVar T hu hu').extendPoint V_inner hUE x hxVE hx hx'E) hCtx hf' tt
      rw [Term.mapCtx_diaterm m hx tt hsub hne hU hxV hx'm hsubm hnem,
          Term.ctx_extU_diaterm_pass u T hTb hTp hu' hx'm _ hsubm hnem
            (dia_sub_insert_pass hsubm) (dia_extras_insert_pass hTb hnem),
          Term.ctx_extU_diaterm_pass u T hTb hTp hu hx tt hsub hne hsubE hneE,
          Term.mapCtx_diaterm (m.extendUser u.toVar T hu hu') hx tt hsubE hneE hUE hxVE hx'E
            hsubE' hneE']
      exact Term.diaterm_congr' hxx hI _ _ hCtx hX _ _ _ _
  | V, V', m, hu, hu', _, .pair_elim T₁ T₂ z hz w₁eq w₂eq body => by
      rename_i pe_V pe_W₁
      -- IH before any `subst` (see `Term.mapCtx_roundtrip`).
      have IH : ∀ (A : VarCtx) (M : CtxBij pe_W₁ A) (hA : u.toVar ∉ VarCtx_to_VarSymbs pe_W₁)
          (hA' : u.toVar ∉ VarCtx_to_VarSymbs A),
          Term.ctx_extU u T hA' (Term.mapCtx M body)
            = Term.mapCtx (M.extendUser u.toVar T hA hA') (Term.ctx_extU u T hA body) :=
        fun A M hA hA' => Term.ctx_extU_mapCtx u T hTb hTp pe_W₁ A M hA hA' _ body
      subst w₂eq
      subst w₁eq
      have upd_comm : ∀ (f : VarSymb → VarSymb) (a b c d : VarSymb), a ≠ c →
          VarSymb.update (VarSymb.update f a b) c d
            = VarSymb.update (VarSymb.update f c d) a b := by
        intro f a b c d h
        funext v
        simp only [VarSymb.update]
        split_ifs <;> simp_all
      have hzne : z ≠ u.toVar := fun h =>
        hu (by rw [VarCtx_to_VarSymbs_insert, ← h]; exact Finset.mem_insert_self _ _)
      have hu_pe : u.toVar ∉ VarCtx_to_VarSymbs pe_V := fun hm =>
        hu (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem hm)
      have hu_bnd2 : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd2 T₁ T₂ pe_V) :=
        VarCtx.notMem_insertBnd_of_isUsr rfl T₂ (VarCtx.notMem_insertBnd_of_isUsr rfl T₁ hu_pe)
      ---------------- the left side: `mapCtx m` first, then weaken ----------------
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
      ---------------- the right side: weaken first, then `mapCtx` along `extendUser` --------
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
      rw [Term.mapCtx_pair_elim hz body m hz₁ w₂eq₁,
          Term.ctx_extU_pair_elim u T hu' hz₁ rfl w₂eq₁ _ hu_E₁ hz₁' hu_bnd2E₁ w₁eqL w₂eqL,
          IH _ (((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂) hu_bnd2 hu_bnd2E₁,
          Term.ctx_extU_pair_elim u T hu hz rfl rfl body hu_pe hz' hu_bnd2 w₁eqR w₂eqR,
          Term.pair_elim_w₁_cast hz' w₁eqR w₂eqR,
          Term.pair_elim_as_cast hz' _ w₂eqR,
          Term.mapCtx_cast w₂eqR (m.extendUser u.toVar T hu hu')
            (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))
            (CtxBij.cast_ofEq w₂eqR (m.extendUser u.toVar T hu hu')),
          Term.mapCtx_pair_elim hz' _ (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu')) hzE
            w₂eqE,
          Term.mapCtx_cast w₁eqR.symm
            (((CtxBij.restrictInsert hz'
              (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))).extendBnd T₁).extendBnd T₂)
            (CtxBij.ofEq w₁eqR.symm (((CtxBij.restrictInsert hz'
              (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))).extendBnd T₁).extendBnd T₂))
            (CtxBij.cast_ofEq w₁eqR.symm _)]
      ---------------- matching the two `pair_elim`s ----------------
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
      -- the four `nextBnd`s line up across `insert u`
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
      -- ⭐the body maps: `u`'s fixing update commutes past both slot updates
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
        -- ⚠️`simp` also normalized `(ofEq …).f z` inside the erased contexts; bring `hd₁`/`hd₂`
        -- to the same form or their left sides no longer match.
        simp only [CtxBij.extendUser_f, CtxBij.ofEq_f] at hd₁ hd₂
        rw [hc₁, hd₁, hc₂, hd₂, upd_comm _ _ _ _ _ (Ne.symm hua₂),
          upd_comm _ _ _ _ _ (Ne.symm hua₁)]
      have hX := Term.mapCtx_congr
        ((((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂).extendUser
          u.toVar T hu_bnd2 hu_bnd2E₁)
        (CtxBij.ofEq w₁eqR.symm (((CtxBij.restrictInsert hz'
          (CtxBij.ofEq w₂eqR (m.extendUser u.toVar T hu hu'))).extendBnd T₁).extendBnd T₂))
        hW hfB (Term.ctx_extU u T hu_bnd2 body)
      exact Term.pair_elim_congr' hzz hB hW _ _ _ _ _ _ hX
  termination_by _ _ _ _ _ _ t => sizeOf t

theorem Func.ctx_extU_mapCtx {σ : Signature} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false) :
    ∀ (V V' : VarCtx) (m : CtxBij V V') (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
      (hu' : u.toVar ∉ VarCtx_to_VarSymbs V') (N : ℕ) (fn : Func σ V N),
      Func.ctx_extU u T hu' (Func.mapCtx m fn)
        = Func.mapCtx (m.extendUser u.toVar T hu hu') (Func.ctx_extU u T hu fn)
  | _, _, m, hu, hu', _, .F hr => by
      rw [Func.mapCtx_F, Func.ctx_extU_F, Func.ctx_extU_F, Func.mapCtx_F]
  | V, V', m, hu, hu', _, .eval g t => by
      rw [Func.mapCtx_eval, Func.ctx_extU_eval, Func.ctx_extU_eval, Func.mapCtx_eval,
          Func.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' _ g,
          Term.ctx_extU_mapCtx u T hTb hTp V V' m hu hu' _ t]
  termination_by _ _ _ _ _ _ fn => sizeOf fn
end
