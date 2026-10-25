import QML.QML_v12m_GCanonModel
import QML.QML_v12m_GViewSubst

/-!
# QML v12m — the growing tree's canonical model: strong 4's lift, and the model

* ⭐`gkeep_edge`: along one edge, every definable object of a liftable type at the child is a
  kept object of the parent.  The chain lifted its term `u` to a root `r` (`gllift`); the root's
  η-expansion, kept (`applyG_keep_eta`), translates along the edge to `u`'s entry
  (`Term.subst_eta_tm`).
* ⭐`graw_keepLift`: along any arrow, by induction on its path, keeping composing along paths
  (`grawEval_keep_comp`).
* ⭐`gmodel`: the canonical model.  `necDup_eval` and `posKeep_full` hold by definition; `Ind` is
  equality (nothing reads it with T and strong B off).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Keeping an η-expanded address is the η-expansion of its kept item, inside `□`. -/
theorem applyG_keep_eta {Γ : Ctx} : ∀ {T : VarType} (hk : T.keepable = true) (r : VarSymb)
    (h : Γ.ref r = some T),
    Canon.applyG (GFunc.keep (σ := σ) hF hk) (Term.eta r T h) =
      ⟨_, .boxtm (Term.eta (.step r .keep) T (Ctx.ref_keep_of' hF h hk))⟩
  | .VTypeBox B, _, r, h =>
      sig_boxtm (sig_boxtm ((Term.shift_eta (Ctx.shifts_boxIn_boxIn hF Γ) r.inner B
        (Ctx.ref_inner h)).trans (Term.eta_congr (VarSymb.inner_shift_zero r) B _ _)))
  | .VTypeDia B, _, r, h =>
      sig_boxtm (sig_diatm ((Term.shift_eta (Ctx.shifts_diaIn_keep hF Γ r) (.step r .dia) B
        (Ctx.ref_diaIn_of h)).trans
          (Term.eta_congr (VarSymb.shift_level_zero (s := .dia) rfl) B _ _)))
  | .Var, hk, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeOne, hk, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeProd _ _, hk, _, _ => (Bool.false_ne_true hk).elim

variable {hM₀ : Theory.IsMCS M₀}

/-- Keeping along a composite arrow is keeping twice. -/
theorem grawEval_keep_comp : ∀ {T : VarType} (hk : T.keepable = true) {s u t : GW hF M₀}
    (e : GR s u) (q : GR u t) (m : GRDom hM₀ T s),
    grawEval hM₀ (GFunc.keep hF hk) s m ⟨t, ⟨gtrans e q⟩⟩ =
      grawEval hM₀ (GFunc.keep hF hk) u (grawEval hM₀ (GFunc.keep hF hk) s m ⟨u, ⟨e⟩⟩)
        ⟨t, ⟨q⟩⟩
  | .VTypeBox _, _, _, _, _, _, _, _ => rfl
  | .VTypeDia _, _, _, u, t, e, q, m => GRPos.ext_E rfl (fun _ _ _ => rfl) fun hT => by
      change _ = ((m.3 hT).map _).map _
      rw [Shp.map_map]
      exact congrArg (fun g => Shp.map g (m.3 hT))
        (funext fun ℓ => (Arrows.Leaf.keepAlong_comp hF (F := garrows hF M₀)
          (⟨u, ⟨e⟩⟩ : GAcc hF M₀ _) (⟨t, ⟨q⟩⟩ : GAcc hF M₀ u) ℓ).symm)
  | .Var, hk, _, _, _, _, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeOne, hk, _, _, _, _, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeProd _ _, hk, _, _, _, _, _, _ => (Bool.false_ne_true hk).elim

/-- Under T keeping along the world's own arrow is the object itself. -/
theorem grawEval_keep_refl (hT : ModalSys.T = true) : ∀ {T : VarType} (hk : T.keepable = true)
    {s : GW hF M₀} (hR : GR s s) (m : GRDom hM₀ T s),
    grawEval hM₀ (GFunc.keep hF hk) s m ⟨s, ⟨hR⟩⟩ = m
  | .VTypeBox _, _, _, _, _ => funext fun _ => rfl
  | .VTypeDia _, _, _, hR, m => gkeep_refl hT m hR
  | .Var, hk, _, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeOne, hk, _, _, _ => (Bool.false_ne_true hk).elim
  | .VTypeProd _ _, hk, _, _, _ => (Bool.false_ne_true hk).elim

/-- ⭐**Strong 4 along an edge**: every definable object of a liftable type at a child is a kept
    object of its parent, kept from a pulled-back term (docs §3 4, D-H1, D-H2): a necessary one
    `⟦□b⟧` from `□ b'`, `b'` read through the root lifted to the `□` view tuple
    (`subst_shift_pullBox`); a possible one `⟦◇_z u⟧` from `◇_x u'`, `x` the root lifted to `z`'s
    view tuple (`subst_shift_pullS`). -/
theorem gkeep_edge {T : VarType} (hl : T.liftable = true) {s t : GW hF M₀} (c : ℕ)
    (hc : t.1 = c :: s.1) (o : GRDom hM₀ T t) (ho : GDefinable hM₀ T t o) :
    ∃ m, GDefinable hM₀ T s m ∧
      grawEval hM₀ (GFunc.keep hF (VarType.keepable_of_liftable hl)) s m
        ⟨t, ⟨⟨[c], pathOk_cons, hc⟩⟩⟩ = o := by
  obtain ⟨j, a, u, rfl⟩ := ho
  cases T with
  | VTypeBox A =>
      match a, u with
      | _, .boxtm b =>
          obtain ⟨i, r, hr, hroot, L, hL, hfm, hLsuf⟩ := gllift hM₀ ⟨c, hc⟩ j
            (GArrow.boxTuple (σ := σ) hF (glat t j)).2.2.2 (by simpa [VarType.liftable] using hl)
            (liftAdm_boxTuple hF _)
          have hR : (ctxOf (glat s i)).ref (.root (.free r)) =
              some (.VTypeBox (itemsTy (boxItems (glat t j)))) := by
            rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr, hroot]
            rfl
          refine ⟨grden hM₀ s i (Ctx.Le.refl _) (.boxtm
            (Term.subst (pullBoxIdx (glat t j) (.root (.free r)))
              (pullBoxS (glat t j) (.root (.free r))) (ok_pullBoxS hF hR)
              (coh_pullBoxS hF hR) b)), gdefinable_rden _ _, ?_⟩
          rw [← grden_applyG]
          change grden hM₀ s i (Ctx.Le.refl _) (.boxtm (.boxtm
            (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i))) _))) _ = _
          rw [grden_boxtm_path (Ctx.Le.refl _) _ t _ [c] hc (pathOk_cons), Term.mono_refl]
          have hle : (ctxOf (glat t j)).Le (ctxOf (glat t (glstg s t i))) :=
            (ctxOf_le_of_suffix hL).trans (ctxOf_le_of_suffix hLsuf)
          have hat : (eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).at
              (.step (.root (.free r)) .keep) =
                .tm (Term.mono hle (GArrow.boxTuple (σ := σ) hF (glat t j)).2.2.2) := by
            rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfm, entOf_tm (ctxOf_le_of_suffix hLsuf),
              Term.mono_mono]
          refine (grden_sigma (Ctx.Le.refl _)
            (sig_boxtm (subst_shift_pullBox hF hle hR _ (ok_eS_kView (gentOk_box hM₀ ⟨c, hc⟩ i))
              (coh_eS_kView (gentOk_box hM₀ ⟨c, hc⟩ i)) hat b))).trans ?_
          change grden hM₀ t _ _ (Term.mono hle (.boxtm b)) = _
          rw [grden_mono]
          exact grden_congr _ _ _ _ _ _
  | VTypeDia A =>
      match a, u with
      | _, .diatm z hz u' =>
          obtain ⟨Z, hzZ⟩ := hz
          by_cases hS : ModalSys.FourStrong = true
          · -- D-H3: `z` and the `□` view's items are lifted separately.
            obtain ⟨i₁, x, hx₁, hroot₁, L₁, hL₁, hfm₁, hLsuf₁⟩ := gllift hM₀ ⟨c, hc⟩ j
              (GArrow.etaTerm (σ := σ) (glat t j) z Z hzZ).2.2.2
              (by simpa [VarType.liftable] using hl) (liftAdm_etaTerm hF _ z Z hzZ)
            obtain ⟨i₂, r, hr₂, hroot₂, L₂, hL₂, hfm₂, hLsuf₂⟩ := gllift hM₀ ⟨c, hc⟩ j
              (GArrow.boxTuple (σ := σ) hF (glat t j)).2.2.2
              (by simpa [VarType.liftable, GArrow.boxTuple] using hS)
              (liftAdm_boxTuple hF _)
            have hX : (ctxOf (glat s (max i₁ i₂))).ref (.root (.free x)) = some (.VTypeDia Z) :=
              ((gw hM₀ s).le (le_max_left i₁ i₂)).ref
                (show (ctxOf (glat s i₁)).ref (.root (.free x)) = some (.VTypeDia Z) by
                  rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hx₁, hroot₁]
                  rfl)
            have hR : (ctxOf (glat s (max i₁ i₂))).ref (.root (.free r)) =
                some (.VTypeBox (itemsTy (boxItems (glat t j)))) :=
              ((gw hM₀ s).le (le_max_right i₁ i₂)).ref
                (show (ctxOf (glat s i₂)).ref (.root (.free r)) =
                    some (.VTypeBox (itemsTy (boxItems (glat t j)))) by
                  rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr₂, hroot₂]
                  rfl)
            refine ⟨grden hM₀ s (max i₁ i₂) (Ctx.Le.refl _) (.diatm (.root (.free x)) ⟨_, hX⟩
              (Term.subst (pullDIdx (glat t j) z (.root (.free x)) (.root (.free r)))
                (pullD (glat t j) z (.root (.free x)) (.root (.free r))) (ok_pullD hF hzZ hX hR)
                (coh_pullD hF hzZ hX hR) u')), gdefinable_rden _ _, ?_⟩
            rw [← grden_applyG]
            change grden hM₀ s _ (Ctx.Le.refl _) (.boxtm (.diatm _ _
              (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s (max i₁ i₂))) _) _))) _ = _
            rw [grden_boxtm_path (Ctx.Le.refl _) _ t _ [c] hc (pathOk_cons), Term.mono_refl]
            have hst₁ : (ctxOf (glat t (glstg s t i₁))).Le
                (ctxOf (glat t (glstg s t (max i₁ i₂)))) :=
              (gw hM₀ t).le (glstg_monotone hM₀ ⟨c, hc⟩ (le_max_left i₁ i₂))
            have hst₂ : (ctxOf (glat t (glstg s t i₂))).Le
                (ctxOf (glat t (glstg s t (max i₁ i₂)))) :=
              (gw hM₀ t).le (glstg_monotone hM₀ ⟨c, hc⟩ (le_max_right i₁ i₂))
            have hle : (ctxOf (glat t j)).Le (ctxOf (glat t (glstg s t (max i₁ i₂)))) :=
              (ctxOf_le_of_suffix hL₁).trans ((ctxOf_le_of_suffix hLsuf₁).trans hst₁)
            have hatx : (eS σ (ctxOf (glat t (glstg s t (max i₁ i₂)))) (fmapL hF M₀ t.1)).at
                (.step (.root (.free x)) .keep) =
                  .tm (Term.mono hle (GArrow.etaTerm (σ := σ) (glat t j) z Z hzZ).2.2.2) := by
              rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfm₁,
                entOf_tm ((ctxOf_le_of_suffix hLsuf₁).trans hst₁), Term.mono_mono]
            have hatr : (eS σ (ctxOf (glat t (glstg s t (max i₁ i₂)))) (fmapL hF M₀ t.1)).at
                (.step (.root (.free r)) .keep) =
                  .tm (Term.mono hle (GArrow.boxTuple (σ := σ) hF (glat t j)).2.2.2) := by
              rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfm₂,
                entOf_tm ((ctxOf_le_of_suffix hLsuf₂).trans hst₂), Term.mono_mono]
            refine (grden_sigma (Ctx.Le.refl _)
              (subst_shift_pullD hF hle hzZ hX hR _ _ _ hatx hatr u')).trans ?_
            rw [grden_mono]
            exact grden_congr _ _ _ _ _ _
          have hvt := liftAdm_viewTuple (σ := σ) hF (Bool.eq_false_iff.mpr hS) (glat t j) z Z hzZ
          obtain ⟨i, r, hr, hroot, L, hL, hfm, hLsuf⟩ := gllift hM₀ ⟨c, hc⟩ j
            (GArrow.viewTuple (σ := σ) hF (glat t j) z Z hzZ).2.2.2
            (by simpa [VarType.liftable] using hl) hvt
          have hR : (ctxOf (glat s i)).ref (.root (.free r)) =
              some (.VTypeDia (.VTypeProd Z (itemsTy (boxItems (glat t j))))) := by
            rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr, hroot]
            rfl
          refine ⟨grden hM₀ s i (Ctx.Le.refl _) (.diatm (.root (.free r)) ⟨_, hR⟩
            (Term.subst (pullIdx (glat t j) z (.root (.free r)))
              (pullS (glat t j) z (.root (.free r))) (ok_pullS hF hzZ hR)
              (coh_pullS hF hzZ hR) u')), gdefinable_rden _ _, ?_⟩
          rw [← grden_applyG]
          change grden hM₀ s i (Ctx.Le.refl _) (.boxtm (.diatm _ _
            (Term.shift (Ctx.shifts_diaIn_keep hF (ctxOf (glat s i)) _) _))) _ = _
          rw [grden_boxtm_path (Ctx.Le.refl _) _ t _ [c] hc (pathOk_cons), Term.mono_refl]
          have hle : (ctxOf (glat t j)).Le (ctxOf (glat t (glstg s t i))) :=
            (ctxOf_le_of_suffix hL).trans (ctxOf_le_of_suffix hLsuf)
          have hat : (eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).at
              (.step (.root (.free r)) .keep) =
                .tm (Term.mono hle (GArrow.viewTuple (σ := σ) hF (glat t j) z Z hzZ).2.2.2) := by
            rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfm, entOf_tm (ctxOf_le_of_suffix hLsuf),
              Term.mono_mono]
          refine (grden_sigma (Ctx.Le.refl _) (subst_shift_pullS hF hle hzZ hR _ _ _ hat u')).trans
            ?_
          rw [grden_mono]
          exact grden_congr _ _ _ _ _ _
  | Var => exact absurd hl (by simp [VarType.liftable])
  | VTypeOne => exact absurd hl (by simp [VarType.liftable])
  | VTypeProd _ _ => exact absurd hl (by simp [VarType.liftable])

/-- Strong 4 along a path. -/
theorem gkeepLift_path {T : VarType} (hl : T.liftable = true) : ∀ (P : List ℕ) (s t : GW hF M₀)
    (_ : t.1 = nodeOf s.1 P) (_ : PathOk P) (o : GRDom hM₀ T t) (_ : GDefinable hM₀ T t o)
    (hR : GR s t),
    ∃ m, GDefinable hM₀ T s m ∧
      grawEval hM₀ (GFunc.keep hF (VarType.keepable_of_liftable hl)) s m ⟨t, ⟨hR⟩⟩ = o
  | [], s, t, h, hP, o, ho, hR => by
      obtain rfl : t = s := gw_eq h
      exact ⟨o, ho, grawEval_keep_refl hP.T_of_nil _ hR o⟩
  | [c], _, _, h, _, o, ho, _ => gkeep_edge hl c h o ho
  | c :: c' :: P, s, t, h, _, o, ho, _ => by
      have hb := born_step h
      have q : GR (stepW s c hb) t := ⟨c' :: P, pathOk_cons, h⟩
      obtain ⟨m', hm', e'⟩ :=
        gkeepLift_path hl (c' :: P) (stepW s c hb) t h (pathOk_cons) o ho q
      obtain ⟨m, hm, e⟩ := gkeep_edge hl (s := s) (t := stepW s c hb) c rfl m' hm'
      refine ⟨m, hm, ?_⟩
      subst e' e
      exact grawEval_keep_comp _ ⟨[c], pathOk_cons, rfl⟩ q m

/-- ⭐**Strong 4 on raw objects**: along any arrow, every definable object of a liftable type at its
    target is a kept definable object of its source. -/
theorem graw_keepLift {T : VarType} (hl : T.liftable = true) (s : GW hF M₀) (a : GAcc hF M₀ s)
    (o : GRDom hM₀ T a.1) (ho : GDefinable hM₀ T a.1 o) :
    ∃ m, GDefinable hM₀ T s m ∧
      grawEval hM₀ (GFunc.keep hF (VarType.keepable_of_liftable hl)) s m a = o := by
  obtain ⟨t, ⟨hR⟩⟩ := a
  exact gkeepLift_path hl (pathOf hR) s t (pathOf_eq hR) (pathOf_ok hR) o ho hR

/-! ## The model -/

variable [ModalSys.NoB]

theorem absBS (h : ModalSys.BStrong = true) : False := by
  rw [ModalSys.NoB.noBStrong] at h
  cases h

variable (hF hM₀) in
/-- ⭐**The canonical model on the growing tree** (4 without T or B, every strong form of 4 and
    D). -/
noncomputable def gmodel : Model.{0, 0} σ where
  frame := gframe hF hM₀
  necEval := gnecEval hM₀
  nec_inj := fun h => gnecEval_injective hM₀ h
  RootPoss _ := VarSymb
  rootKeep := Arrows.RootKeep.keep (F := garrows hF M₀) (Root := fun _ => VarSymb)
  rootKeepLaws := instRootKeepLawsG
  posFull p := gposFull hM₀ p
  posFull_inj := fun h => gposFull_injective hM₀ h
  posShape_wf := fun hSh {_} {_} p => gposShape_wf_canon hM₀ (gT_of_shaped hSh) p
  ops := gops hF hM₀
  necMap_eval g _ a := (geval_toDom hM₀ g a.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_full g _ := Prod.ext
    (congrArg (Sigma.mk _) (funext fun a => (geval_toDom hM₀ g a.1.1 _ _).symm)) rfl
  posStrength_full n _ := Prod.ext rfl (funext fun hSh =>
    congrArg (fun z => Shp.dia _ (Shp.prod z _)) (congrArg Arrows.transposeShp (funext fun s =>
      (gdomShape_toDom hM₀ hSh _ s.1 (n.1 s) (gdefinable_box_apply n.2 s)).symm)))
  necExtract_eval _ _ := rfl
  necDup_eval _ _ _ _ := rfl
  keepLift := by
    intro _ T hl w a o
    obtain ⟨m, hm, e⟩ := graw_keepLift hl w a _ (gdefinable_fromDom hM₀ T a.1 o)
    refine ⟨gtoDom hM₀ T w m hm, ?_⟩
    rw [geval_toDom]
    exact (gtoDom_congr e _ _).trans (gtoDom_fromDom hM₀ T a.1 o)
  posKeep_full _ _ _ := Prod.ext rfl (funext fun _ => rfl)
  posSerial hDS s := gposSerial_canon hM₀ hDS s
  Ind o o' := (ModalSys.T = true → gInd hM₀ o o') ∧ (ModalSys.T = false → o = o')
  Ind_refl o := ⟨fun _ => gInd_refl hM₀ o, fun _ => rfl⟩
  posRet_exists hT hS a := by
    obtain ⟨p, hm, hp⟩ := gposRet_exists_canon hM₀ hT hS a
    exact ⟨p, hm, fun _ => hp, fun hT' => absurd (hT.symm.trans hT') (by decide)⟩
  Ret _ _ _ := False
  Ret_fwd hS := (absBS hS).elim
  Ret_conv hS := (absBS hS).elim
  backRet_exists hS := (absBS hS).elim
  posBack_exists hS := (absBS hS).elim

end GArrow

end V12M
