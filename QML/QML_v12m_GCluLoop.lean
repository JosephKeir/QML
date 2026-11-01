import QML.QML_v12m_GCluTr

/-!
# QML v12m — the root's loop on the cluster: translating kept terms

The self-arrow's half of `tr_edge`, `tr_edgeX`, `cden_tr` and `cden_trX`.  An edge renames a kept
term by its names; the self-edge fixes kept items, so it gives the term back (`tr_loop`,
`tr_loopX`).  So `□` of a shifted term, read along the self-arrow, is the term itself, which is
what `dup` and `dkeep` ask of the cluster's function algebra (`cden_tr_loop`, `cden_trX_loop`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

theorem le_lstg (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) :
    i ≤ lstg hF M₀ i := by
  have := (lstg_spec (hF := hF) hM₀ hl i).1
  omega

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- With the self-edge, kept items are the object's: T is off. -/
theorem keepOnly_of_loop (hl : GNetSt.LoopOn M₀) : ModalSys.keepOnly = false := by
  have hT : ModalSys.T = false := hl.2.1.2.2.2.2
  simp [ModalSys.keepOnly, hT]

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A kept item's entry, under entries fixing kept items. -/
theorem eS_keep_at {cl : List VarType} {Δ : Ctx} {f : VarSymb → LEnt σ} (hkf : KeepFix cl f)
    {u : VarSymb} {W : VarType} (h : (ctxOf cl).boxIn (.step u .keep) = some W) :
    (eS σ Δ f).at (.step u .keep) = .ren u := by
  rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hkf u W h]
  rfl

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Entries fixing kept items undo the shift on a `◇_x` view, at the kept witness. -/
theorem dia_shift_ren (hF : ModalSys.Four = true) (hb : ModalSys.keepOnly = false)
    {cl : List VarType} {Δ : Ctx} {f : VarSymb → LEnt σ} (hkf : KeepFix cl f) {x : VarSymb}
    {X : VarType} (hx : (ctxOf cl).ref x = some (.VTypeDia X)) {v : VarSymb} {U : VarType}
    (hl : v.lastProj = false) (hv : (ctxOf cl).diaIn x v = some U) :
    SubE.Sim U (((eS σ Δ f).dia (.step x .keep) x).at (v.shift 0)) (.ren v) := by
  by_cases hvz : v = .step x .dia
  · subst hvz
    rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
    change SubE.Sim U (if VarSymb.step x .keep = .step x .keep then _ else _) _
    rw [if_pos rfl, eS_keep_at hkf (Ctx.boxIn_keep_of' hF hx rfl)]
    exact .refl _
  · have hv' := diaIn_boxIn_of_ne' hv hvz
    obtain ⟨u, s, rfl, -, W, hW⟩ := kView_item (k := none) hv'
    cases s with
    | box =>
        obtain ⟨-, hu⟩ := Ctx.boxIn_box hv'
        rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
        change SubE.Sim U (SubE.mono _ (SubE.unbox (Subst.at _ _))) _
        rw [eS_keep_at hkf (Ctx.boxIn_keep_of' hF hu rfl)]
        change SubE.Sim U (.ren (VarSymb.inner u)) _
        rw [show VarSymb.inner u = .step u .box by simp [VarSymb.inner, hb]]
        exact .refl _
    | keep =>
        rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
        change SubE.Sim U (SubE.mono _ (SubE.keepE (Subst.at _ _))) _
        rw [eS_keep_at hkf hv']
        exact .refl _
    | dia => cases hv'
    | fst => cases hl
    | snd => cases hl
    | here => cases hl

/-- The self-edge's translation commutes with the function algebra. -/
theorem loopTm_applyG (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) {A C : VarType}
    (g : GFunc σ A C) {a : Ann A}
    (b : Term σ ((ctxOf (glat (groot hF M₀) i)).kView none) A a) :
    loopTm hM₀ hl i (Canon.applyG g b).2 = Canon.applyG g (loopTm hM₀ hl i b).2 :=
  (Canon.applyG_subst g _ _ _ b).symm

/-- ⭐**Along the self-edge a kept `□`-view term is the term itself.** -/
theorem tr_loop (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) {A : VarType} {a : Ann A}
    (b : Term σ (ctxOf (glat (groot hF M₀) i)).boxIn A a) :
    (⟨_, Term.subst (eIdx (fmapL hF M₀ []))
        (eS σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i))) (fmapL hF M₀ [])).box
        (Subst.ok_box (ok_eS_kView (gloopOk hM₀ hl i)))
        (Subst.coh_box (ok_eS_kView (gloopOk hM₀ hl i)) (coh_eS_kView (gloopOk hM₀ hl i)))
        (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)⟩ :
        Σ c, Term σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i))).boxIn A c) =
      ⟨_, Term.mono (gle hM₀ (groot hF M₀) (le_lstg hM₀ hl i)).boxIn b⟩ := by
  have hE := gloopOk (hF := hF) hM₀ hl i
  have hle := (gle hM₀ (groot hF M₀) (le_lstg (hF := hF) hM₀ hl i)).boxIn
  have hO := Subst.ok_box (ok_eS_kView hE)
  have hC := Subst.coh_box (ok_eS_kView hE) (coh_eS_kView hE)
  refine (Term.subst_shift (Ctx.shifts_boxIn_boxIn hF _) _ hO hC (Subst.atShift _)
    (Subst.ok_atShift (Ctx.shifts_boxIn_boxIn hF _) hO)
    (Subst.coh_atShift (Ctx.shifts_boxIn_boxIn hF _) hO hC (levels_boxIn _))
    (Subst.preShift_atShift _ _) b).trans ?_
  refine (Term.subst_congr _ (Subst.idS σ _) _ (Subst.ok_idS_le hle) _ (Subst.coh_idS_le hle)
    (Subst.sim_of fun v U hl' hv => ?_) b).trans (Term.subst_idS_mono hle _ _ b)
  exact box_shift_ren hF (keepOnly_of_loop hl)
    (fun _ _ h => eS_keep_at (gloopFix hM₀ hl i) h) hl' hv

/-- ⭐**The self-arrow reads `□` of a shifted term as the term** (`cden_tr`). -/
theorem cden_tr_loop (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀)
    {t : GW hF M₀} (ha : t.1 = (groot hF M₀).1) (i : ℕ) {A : VarType} {a : Ann A}
    (b : Term σ (ctxOf (glat (groot hF M₀) i)).boxIn A a) :
    cden hM₀ hX t (lstg hF M₀ i) (glat_le_of_eq ha _)
        (loopTm hM₀ hl i (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))).2 =
      cden hM₀ hX (groot hF M₀) i (Ctx.Le.refl _) (.boxtm b) := by
  obtain rfl : t = groot hF M₀ := gw_eq ha
  refine (cden_sigma hX (q := ⟨_, Term.mono (gle hM₀ (groot hF M₀) (le_lstg hM₀ hl i))
    (.boxtm b)⟩) _ (sig_boxtm (tr_loop hM₀ hl i b))).trans ?_
  rw [cden_mono]
  exact cden_congr hX _ _ _ _ _ _

/-- ⭐**Along the self-edge a kept possible term is the term itself.** -/
theorem tr_loopX (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀) (i : ℕ) {x : VarSymb}
    {X : VarType} (hx : (ctxOf (glat (groot hF M₀) i)).ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (c : Term σ ((ctxOf (glat (groot hF M₀) i)).diaIn x) A a) :
    (⟨_, Term.subst (eIdx (fmapL hF M₀ []))
        (eS σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i))) (fmapL hF M₀ []))
        (ok_eS_kView (gloopOk hM₀ hl i)) (coh_eS_kView (gloopOk hM₀ hl i))
        (.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
          (Term.shift (Ctx.shifts_diaIn_keep hF _ x) c))⟩ :
        Σ e, Term σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i))) (.VTypeDia A) e) =
      ⟨_, Term.mono (gle hM₀ (groot hF M₀) (le_lstg hM₀ hl i)) (.diatm x ⟨X, hx⟩ c)⟩ := by
  have hG := gle hM₀ (groot hF M₀) (le_lstg (hF := hF) hM₀ hl i)
  have hE := gloopOk (hF := hF) hM₀ hl i
  have hO := ok_eS_kView hE
  have hC := coh_eS_kView hE
  have hidx : eIdx (fmapL hF M₀ []) (.step x .keep) = x := by
    rw [show (VarSymb.step x .keep) = (VarSymb.step x .keep).ext [] from rfl,
      eIdx_item _ (reach_ppath hx).1 rfl [],
      gloopFix hM₀ hl i x (.VTypeDia X) (Ctx.boxIn_keep_of' hF hx rfl)]
    rfl
  have hk := Ctx.exists_keep_dia hF ⟨X, hx⟩
  have hOd : Subst.Ok ((ctxOf (glat (groot hF M₀) i)).boxIn.diaIn (.step x .keep))
      ((eS σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i))) (fmapL hF M₀ [])).dia (.step x .keep) x) :=
    Subst.ok_dia hO hk ((hC _ _ hk.choose_spec []).trans hidx)
  have hCd : Subst.Coh (eIdx (fmapL hF M₀ []))
      ((ctxOf (glat (groot hF M₀) i)).boxIn.diaIn (.step x .keep))
      ((eS σ (ctxOf (glat (groot hF M₀) (lstg hF M₀ i))) (fmapL hF M₀ [])).dia
        (.step x .keep) x) := by
    have h₀ := Subst.coh_dia hO hC hk
    rw [hidx] at h₀
    exact h₀
  have hC' := Ctx.shifts_diaIn_keep hF (ctxOf (glat (groot hF M₀) i)) x
  refine (sig_subst_diatm _ hO hC hk _ x hidx ⟨X, hG.ref hx⟩ hOd hCd).trans (sig_diatm ?_)
  refine (Term.subst_shift hC' _ hOd hCd (Subst.atShift _) (Subst.ok_atShift hC' hOd)
    (Subst.coh_atShift hC' hOd hCd (levels_diaIn _ _)) (Subst.preShift_atShift _ _) c).trans ?_
  refine (Term.subst_congr _ (Subst.idS σ _) _ (Subst.ok_idS_le (hG.diaIn x)) _
    (Subst.coh_idS_le (hG.diaIn x)) (Subst.sim_of fun v U hl' hv => ?_) c).trans
    (Term.subst_idS_mono (hG.diaIn x) _ _ c)
  exact dia_shift_ren hF (keepOnly_of_loop hl) (gloopFix hM₀ hl i) hx hl' hv

/-- ⭐**The self-arrow reads `◇` of a kept term as the term** (`cden_trX`). -/
theorem cden_trX_loop (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (hl : GNetSt.LoopOn M₀)
    {t : GW hF M₀} (ha : t.1 = (groot hF M₀).1) (i : ℕ) {x : VarSymb} {X : VarType}
    (hx : (ctxOf (glat (groot hF M₀) i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (c : Term σ ((ctxOf (glat (groot hF M₀) i)).diaIn x) A a) :
    cden hM₀ hX t (lstg hF M₀ i) (glat_le_of_eq ha _)
        (loopTm hM₀ hl i (.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
          (Term.shift (Ctx.shifts_diaIn_keep hF _ x) c))).2 =
      cden hM₀ hX (groot hF M₀) i (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ c) := by
  obtain rfl : t = groot hF M₀ := gw_eq ha
  refine (cden_sigma hX _ (tr_loopX hM₀ hl i hx c)).trans ?_
  rw [cden_mono]
  exact cden_congr hX _ _ _ _ _ _

end GArrow

end V12M
