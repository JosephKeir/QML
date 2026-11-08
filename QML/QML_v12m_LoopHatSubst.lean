import QML.QML_v12m_LoopHat
import QML.QML_v12m_LeibnizQuant

/-!
# QML v12m — U with objects under a substitution

`Proof.five_refl` is closed under substitution: a substitution sends the hat of a body to the hat
of its image.  Both legs are `WFF.subst_hatGen`, the shift commuted past the substitution
(`WFF.shift_subst`) and the two composites compared.
-/

namespace V12M

variable [ModalSys]

section

variable {σ : Signature} {T : VarType}

/-- Equal terms are `Sim`. -/
theorem SubE.Sim.of_sig {Δ : Ctx} {T : VarType} {a b : Ann T} {s : Term σ Δ T a}
    {t : Term σ Δ T b} (h : (⟨a, s⟩ : Σ c, Term σ Δ T c) = ⟨b, t⟩) (U : VarType) :
    SubE.Sim U (.tm s) (.tm t) := by
  cases h
  exact .refl _

/-- An entry weakened past a substitution fixing its context is the entry weakened. -/
theorem SubE.comp_mono_fix {ι : VarSymb → VarSymb} {Ω Ω₁ Ω₂ : Ctx} (l : Ω.Le Ω₁) (l' : Ω.Le Ω₂)
    (θ : Subst σ Ω₂) (hθ : Subst.Ok Ω₁ θ) (hc : Subst.Coh ι Ω₁ θ)
    (hid : ∀ v U, Ω.ref v = some U → θ.at v = .ren v) {U : VarType} :
    ∀ (e : SubE σ Ω), e.OkRef U → SubE.Sim U (e.mono l') ((e.mono l).comp θ hθ hc)
  | .hide, h => h.elim
  | .ren w, h => by
      change SubE.Sim U (.ren w) (θ.at w)
      rw [hid w U h]
      exact .refl _
  | .tm s, h => by
      cases h
      change SubE.Sim _ (.tm (Term.mono l' s)) (.tm (Term.subst ι θ hθ hc (Term.mono l s)))
      rw [Term.subst_mono]
      exact SubE.Sim.of_sig (Term.subst_ren l' θ _ _ hid s).symm _

/-- ⭐**The hat under a substitution**, for both legs: `K` is the slot kept, `Θ` the substitution
    on the body, `Θp` on its shift, `Θw` on the hat. -/
theorem WFF.subst_hatGen {V Vp W V' Vp' W' : Ctx} (D : Ctx.Shifts 0 V Vp) (D' : Ctx.Shifts 0 V' Vp')
    (hV : V.SlotsFrom 0) (hVp : Vp.SlotsFrom 0) (hV' : V'.SlotsFrom 0) (hVp' : Vp'.SlotsFrom 0)
    (hW : W.SlotsFrom 1) (hW' : W'.SlotsFrom 1) (hle : Vp.Le W) (hle' : Vp'.Le W')
    {K₀ : Ann T} (K : Term σ W T K₀) {K₀' : Ann T} (K' : Term σ W' T K₀')
    {ι₀ ιp ιw : VarSymb → VarSymb} (Θ : Subst σ (V'.insert (.bnd 0) T))
    (hΘ : Subst.Ok (V.insert (.bnd 0) T) Θ) (hcΘ : Subst.Coh ι₀ (V.insert (.bnd 0) T) Θ)
    (Θp : Subst σ (Vp'.insert (.bnd 0) T)) (hΘp : Subst.Ok (Vp.insert (.bnd 0) T) Θp)
    (hcΘp : Subst.Coh ιp (Vp.insert (.bnd 0) T) Θp)
    (hcr : Subst.ShiftCorr (V.insert (.bnd 0) T)
      (D'.insert (hV'.rootFresh (le_refl 0)) T) Θ Θp)
    (Θw : Subst σ W') (hΘw : Subst.Ok W Θw) (hcw : Subst.Coh ιw W Θw)
    (hKs : (⟨_, Term.subst ιw Θw hΘw hcw K⟩ : Σ b, Term σ W' T b) = ⟨_, K'⟩)
    (hroot : Θp (.root (.bnd 0)) = .ren (.root (.bnd 0)))
    (hfix : ∀ v U, v.lastProj = false → Vp v = some U →
      SubE.Sim U (Θw v) ((Θp v).comp (Subst.single (.bnd 0) (.tm K'))
        (Subst.ok_single hle' rfl) (Subst.coh_single (hVp'.rootFresh (le_refl 0)) hle' rfl)))
    (φ : WFF σ (V.insert (.bnd 0) T) 1) :
    WFF.subst ιw Θw hΘw hcw hW hW'
        (WFF.subst (Subst.singleIdx (.bnd 0) (.tm K)) (Subst.single (.bnd 0) (.tm K))
          (Subst.ok_single hle rfl) (Subst.coh_single (hVp.rootFresh (le_refl 0)) hle rfl)
          (hVp.insert T) hW
          (WFF.shift (D.insert (hV.rootFresh (le_refl 0)) T) (hV.insert T) φ)) =
      WFF.subst (Subst.singleIdx (.bnd 0) (.tm K')) (Subst.single (.bnd 0) (.tm K'))
        (Subst.ok_single hle' rfl) (Subst.coh_single (hVp'.rootFresh (le_refl 0)) hle' rfl)
        (hVp'.insert T) hW'
        (WFF.shift (D'.insert (hV'.rootFresh (le_refl 0)) T) (hV'.insert T)
          (WFF.subst ι₀ Θ hΘ hcΘ (hV.insert T) (hV'.insert T) φ)) := by
  have _hOff : ModalSys.Opt = false := ModalSys.noOpt_of_Four D.hF
  have hO := hΘw.restrict hle
  have hC := hcw.restrict hle
  have hΨ := Subst.ok_set (r := .bnd 0) (T := T) (e := .tm K') hO rfl
  have hcΨ := Subst.coh_set (r := .bnd 0) (T := T) (e := .tm K') hO hC
    (hVp.rootFresh (le_refl 0)) rfl
  rw [WFF.shift_subst (D.insert (hV.rootFresh (le_refl 0)) T)
    (D'.insert (hV'.rootFresh (le_refl 0)) T) Θ hΘ hcΘ Θp hΘp hcΘp
    (hV.insert T) (hVp.insert T) (hV'.insert T) (hVp'.insert T) hcr φ]
  refine (WFF.subst_comp _ _ (Θw.set (.bnd 0) (.tm K')) _ _ _ _ hΨ hcΨ _ _ _ ?_ _).trans
    (WFF.subst_comp _ _ _ _ _ _ _ hΨ hcΨ _ _ _ ?_ _).symm
  · refine Subst.sim_of fun v U hl hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      change SubE.Sim _ (Θw.set (.bnd 0) (.tm K') (.root (.bnd 0)))
        (SubE.comp _ _ _ (Subst.single (.bnd 0) (.tm K) (.root (.bnd 0))))
      rw [Subst.set_root, Subst.single_self]
      exact SubE.Sim.of_sig hKs.symm _
    · change SubE.Sim U (Θw.set (.bnd 0) (.tm K') v)
        (SubE.comp _ _ _ (Subst.single (.bnd 0) (.tm K) v))
      rw [Subst.set_ne _ _ hvr, show Subst.single (σ := σ) (Δ := W) (.bnd 0) (.tm K) v = .ren v
        from if_neg hvr]
      change SubE.Sim U _ (Subst.at _ v)
      rw [Subst.at_nonproj _ hl]
      exact .refl _
  · refine Subst.sim_of fun v U hl hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      change SubE.Sim _ (Θw.set (.bnd 0) (.tm K') (.root (.bnd 0))) (SubE.comp _ _ _ (Θp _))
      rw [Subst.set_root, hroot]
      change SubE.Sim _ _ ((Subst.single (σ := σ) (Δ := W') (.bnd 0) (.tm K')).at (.root (.bnd 0)))
      rw [Subst.at_single_root]
      exact .refl _
    · have hv' : Vp v = some U := by
        have := hv
        simpa [Ctx.insert, hvr] using this
      change SubE.Sim U (Θw.set (.bnd 0) (.tm K') v) (SubE.comp _ _ _ (Θp v))
      rw [Subst.set_ne _ _ hvr]
      exact hfix v U hl hv'

/-- A substitution fixing a slot's addresses fixes the slot kept. -/
theorem Term.subst_keepOf (hF : ModalSys.Four = true) {ι : VarSymb → VarSymb} {Ω Ω₂ V V' : Ctx}
    (θa : Subst σ Ω) (θb : Subst σ Ω₂) (hθ : Subst.Ok V.boxIn θb) (hc : Subst.Coh ι V.boxIn θb)
    (hle : V'.boxIn.Le Ω₂)
    (hfix : ∀ p U, θa.at p = .ren p → V.ref p = some U → U.keepable = true →
      θb.at (.step p .keep) = .ren (.step p .keep)) :
    ∀ (T : VarType) (ht : T.tup = true) (w : VarSymb) (h : V.ref w = some T)
      (h' : V'.ref w = some T), θa.at w = .ren w →
      (⟨_, Term.subst ι θb hθ hc (Term.keepOf hF T ht w h)⟩ : Σ b, Term σ Ω₂ T b) =
        ⟨_, Term.mono hle (Term.keepOf hF T ht w h')⟩
  | .VTypeOne, _, _, _, _, _ => rfl
  | .Var, ht, _, _, _, _ => by cases ht
  | .VTypeBox A, _, w, h, h', hw => by
      refine (Term.subst_eta_renAt θb hθ hc (.VTypeBox A) _ _ _
        (hle.ref (Ctx.ref_keep_of' hF h' rfl)) (hfix w _ hw h rfl)).trans ?_
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
  | .VTypeDia A, _, w, h, h', hw => by
      refine (Term.subst_eta_renAt θb hθ hc (.VTypeDia A) _ _ _
        (hle.ref (Ctx.ref_keep_of' hF h' rfl)) (hfix w _ hw h rfl)).trans ?_
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
  | .VTypeProd A B, ht, w, h, h', hw => by
      have hAB : A.tup = true ∧ B.tup = true := by simpa [VarType.tup] using ht
      refine sig_pair
        (Term.subst_keepOf hF θa θb hθ hc hle hfix A hAB.1 _ _ (Ctx.ref_fst_of h') ?_)
        (Term.subst_keepOf hF θa θb hθ hc hle hfix B hAB.2 _ _ (Ctx.ref_snd_of h') ?_)
      · change (θa.at w).proj .fst = _
        rw [hw]
        rfl
      · change (θa.at w).proj .snd = _
        rw [hw]
        rfl

/-- `□` of a binder's substitution is `□□` of the substitution, weakened. -/
theorem Subst.box_under_eq {Γ Δ : Ctx} (θ : Subst σ Δ) (hΓ : Γ.SlotsFrom 0)
    (h : Δ (.root (.bnd 0)) = none) {v : VarSymb} {U : VarType} (hv : Γ.boxIn v = some U) :
    (θ.under 0 0 T h).box v = (θ.box v).mono (Ctx.le_insert h T).boxIn := by
  match v with
  | .step u .box =>
      change ((θ.under 0 0 T h).at u).unbox = ((θ.at u).unbox).mono _
      rw [Subst.under_eq_mono θ hΓ T h u _ (Ctx.boxIn_step_box hv), SubE.unbox_mono]
  | .step u .keep =>
      change ((θ.under 0 0 T h).at u).keepE = ((θ.at u).keepE).mono _
      rw [Subst.under_eq_mono θ hΓ T h u _ (Ctx.boxIn_keep hv).2.1, SubE.keepE_mono]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- ⭐**The hat along `□`, under a substitution.** -/
theorem WFF.subst_loopHat_under (hF : ModalSys.Four = true) (hT : T.tup = true)
    {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 T hΔ.boxIn.root).box
        (Subst.ok_box (Subst.ok_under (Subst.ok_box hθ) T hΔ.boxIn.root))
        (Subst.coh_box (Subst.ok_under (Subst.ok_box hθ) T hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn T hΔ.boxIn.root))
        (hΓ.boxIn.insert T).boxIn (hΔ.boxIn.insert T).boxIn (WFF.loopHat hF hT φ) =
      WFF.loopHat hF hT (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 T hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) T hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn T hΔ.boxIn.root)
        (hΓ.boxIn.insert T) (hΔ.boxIn.insert T) φ) := by
  have hb := Subst.ok_box hθ
  have hcb := Subst.coh_box hθ hc
  have hr₂ := hΔ.boxIn.boxIn.rootFresh (le_refl 0)
  have hle' := (Ctx.le_insert hΔ.boxIn.root T).boxIn
  have hO := Subst.ok_under (d := 0) hb T hΔ.boxIn.root
  have hC := Subst.coh_under hb hcb hΓ.boxIn T hΔ.boxIn.root
  unfold WFF.loopHat
  refine WFF.subst_hatGen (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.shifts_boxIn_boxIn hF Δ)
    Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots _ _
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root T).boxIn hle' _ _ _ hO hC
    (θ.box.box.under 0 0 T hΔ.boxIn.boxIn.root)
    (Subst.ok_under (Subst.ok_box hb) T hΔ.boxIn.boxIn.root)
    (Subst.coh_under (Subst.ok_box hb) (Subst.coh_box hb hcb) hΓ.boxIn.boxIn T
      hΔ.boxIn.boxIn.root)
    (Subst.shiftCorr_under hb (Subst.shiftCorr_box_box hF hθ) hΓ.boxIn T hΔ.boxIn.root
      hΔ.boxIn.boxIn.root (hΔ.boxIn.rootFresh (le_refl 0))) _ _ _ ?_
    (Subst.under_slot _ _ _ _ _) ?_ φ
  · refine (Term.subst_keepOf hF (θ.box.under 0 0 T hΔ.boxIn.root) _ _ _ (Ctx.Le.refl _)
      (fun p U hp _ _ => ?_) T hT _ _ (Ctx.ref_insert_root _ _ T) (if_pos rfl)).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ _))
    rw [Subst.at_nonproj _ rfl]
    change ((θ.box.under 0 0 T hΔ.boxIn.root).at p).keepE = _
    rw [hp]
    rfl
  · intro v U hl hv
    have hne : v ≠ .root (.bnd 0) := fun e => by
      subst e
      cases hv
    rw [Subst.box_under_eq θ.box hΓ.boxIn hΔ.boxIn.root hv,
      show θ.box.box.under 0 0 T hΔ.boxIn.boxIn.root v = (θ.box.box v).mono _ from if_neg hne]
    exact SubE.comp_mono_fix _ _ _ _ _
      (fun w W hw => Subst.single_at_ne (Ctx.ref_rt_ne hr₂ hw)) _
      (Subst.ok_box hb v U hl hv)

theorem SubE.mono_mono' {Ω₁ Ω₂ Ω₃ : Ctx} (l : Ω₁.Le Ω₂) (l' : Ω₂.Le Ω₃) :
    ∀ e : SubE σ Ω₁, (e.mono l).mono l' = e.mono (l.trans l')
  | .hide => rfl
  | .ren _ => rfl
  | .tm s => congrArg SubE.tm (Term.mono_mono l l' s)

/-- Along `x`, the body's substitution on the `□` view is `□`'s, weakened. -/
theorem Subst.under_dia_box {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] (θ : Subst σ Δ)
    (hΓ : Γ.SlotsFrom 0) (x y : VarSymb) (h : (Δ.diaIn y) (.root (.bnd 0)) = none)
    {u : VarSymb} {U : VarType} (hu : Γ.boxIn.ref u = some U) :
    ((θ.dia x y).under 0 0 T h).at u = (θ.box.at u).mono (Ctx.le_boxIn_body Δ y T) := by
  rw [Subst.under_eq_mono (θ.dia x y) (hΓ.diaIn x) T h u U ((Ctx.le_boxIn_diaIn Γ x).ref hu),
    Subst.dia_eq_box_mono (Δ₁ := Γ) θ x y u U hu, SubE.mono_mono']

/-- ⭐**The hat along `◇_x`, under a substitution.** -/
theorem WFF.subst_loopHatX_under (hF : ModalSys.Four = true) (hT : T.tup = true)
    {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1)
    (hθy : Subst.Ok (((Γ.diaIn x).insert (.bnd 0) T).diaIn (.step x .keep))
      (((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).dia (.step x .keep)
        (.step (ι x) .keep)))
    (hcy : Subst.Coh (VarSymb.shiftSlot ι 0 0)
      (((Γ.diaIn x).insert (.bnd 0) T).diaIn (.step x .keep))
      (((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).dia (.step x .keep)
        (.step (ι x) .keep)))
    (hO : Subst.Ok ((Γ.diaIn x).insert (.bnd 0) T)
      ((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root))
    (hC : Subst.Coh (VarSymb.shiftSlot ι 0 0) ((Γ.diaIn x).insert (.bnd 0) T)
      ((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root)) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        (((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).dia (.step x .keep)
          (.step (ι x) .keep)) hθy hcy
        ((hΓ.diaIn x).insert T |>.diaIn _) ((hΔ.diaIn (ι x)).insert T |>.diaIn _)
        (WFF.loopHatX hF hT x φ) =
      WFF.loopHatX hF hT (ι x) (WFF.subst (VarSymb.shiftSlot ι 0 0)
        ((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root) hO hC
        ((hΓ.diaIn x).insert T) ((hΔ.diaIn (ι x)).insert T) φ) := by
  have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
  have hb := Subst.ok_box hθ
  have hcb := Subst.coh_box hθ hc
  obtain ⟨X, hX⟩ := id hx
  have hk₂ : ι (.step x .keep) = .step (ι x) .keep := Subst.coh_keep_dia hθ hc hX
  have hwk : (θ.box.at (.step x .keep)).idxAlong [] = .step (ι x) .keep :=
    Subst.idx_box_keep_dia hF hθ hc hX
  have hxk := Ctx.exists_keep_dia hF hx
  have hOd := Subst.ok_dia hb hxk hwk
  have hCd : Subst.Coh ι (Γ.boxIn.diaIn (.step x .keep))
      (θ.box.dia (.step x .keep) (.step (ι x) .keep)) := hk₂ ▸ Subst.coh_dia hb hcb hxk
  have hs : (Δ.boxIn.diaIn (.step (ι x) .keep)).SlotsFrom 0 := Ctx.NoSlots.slots
  have hsG : (Γ.boxIn.diaIn (.step x .keep)).SlotsFrom 0 := Ctx.NoSlots.slots
  have hrB := hs.rootFresh (le_refl 0)
  have hle' : (Δ.boxIn.diaIn (.step (ι x) .keep)).Le
      (((Δ.diaIn (ι x)).insert (.bnd 0) T).diaIn (.step (ι x) .keep)) :=
    (Ctx.le_boxIn_body Δ (ι x) T).diaIn _
  unfold WFF.loopHatX
  refine WFF.subst_hatGen (Ctx.shifts_diaIn_keep hF Γ x) (Ctx.shifts_diaIn_keep hF Δ (ι x))
    Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots _ _
    ((Ctx.le_boxIn_body Γ x T).diaIn _) hle' _ _ _ hO hC
    ((θ.box.dia (.step x .keep) (.step (ι x) .keep)).under 0 0 T hs.root)
    (Subst.ok_under hOd T hs.root) (Subst.coh_under hOd hCd hsG T hs.root)
    (Subst.shiftCorr_under (Subst.ok_dia hθ hx hw) (Subst.shiftCorr_dia_keep hF hθ hx hw)
      (hΓ.diaIn x) T (hΔ.diaIn (ι x)).root hs.root ((hΔ.diaIn (ι x)).rootFresh (le_refl 0)))
    _ _ _ ?_ (Subst.under_slot _ _ _ _ _) ?_ φ
  · have hroot : ((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).at (.root (.bnd 0)) =
        .ren (.root (.bnd 0)) := by
      rw [Subst.at_nonproj _ rfl]
      exact Subst.under_slot _ _ _ _ _
    rw [Term.subst_mono]
    refine Term.subst_keepOf hF ((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root) _ _ _
      (Ctx.le_boxIn_diaIn _ _) (fun p U hp hv hkU => ?_) T hT _ _ _ hroot
    rw [Subst.dia_eq_box_mono (Δ₁ := (Γ.diaIn x).insert (.bnd 0) T) _ _ _ (.step p .keep) U
      (Ctx.ref_keep_of' hF hv hkU), Subst.at_nonproj _ rfl]
    change (((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).at p).keepE.mono _ = _
    rw [hp]
    rfl
  · intro v U hl hv
    have hne : v ≠ .root (.bnd 0) := fun e => by
      subst e
      cases hv
    have e₁ : (((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).dia (.step x .keep)
        (.step (ι x) .keep)) v =
        ((θ.box.dia (.step x .keep) (.step (ι x) .keep)) v).mono hle' := by
      match v with
      | .step u .dia =>
          change (if u = .step x .keep then
              (((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).at (.step x .keep)).diaBody
                (.step (ι x) .keep) else .hide) =
            (if u = .step x .keep then
              (θ.box.at (.step x .keep)).diaBody (.step (ι x) .keep) else .hide).mono _
          by_cases hu : u = .step x .keep
          · rw [if_pos hu, if_pos hu, Subst.under_dia_box θ hΓ x (ι x) _
              (Ctx.ref_keep_of' hF hX rfl), SubE.diaBody_mono]
          · rw [if_neg hu, if_neg hu]
            rfl
      | .step u .box =>
          change (((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).at u).unbox.mono _ =
            ((θ.box.at u).unbox.mono _).mono _
          rw [Subst.under_dia_box θ hΓ x (ι x) _ (Ctx.boxIn_step_box (Γ := Γ.boxIn) hv),
            SubE.unbox_mono, SubE.mono_mono', SubE.mono_mono']
      | .step u .keep =>
          change (((θ.dia x (ι x)).under 0 0 T (hΔ.diaIn (ι x)).root).at u).keepE.mono _ =
            ((θ.box.at u).keepE.mono _).mono _
          rw [Subst.under_dia_box θ hΓ x (ι x) _ (Ctx.boxIn_keep (Γ := Γ.boxIn) hv).2.1,
            SubE.keepE_mono, SubE.mono_mono', SubE.mono_mono']
      | .root _ => cases hv
      | .step _ .fst => cases hv
      | .step _ .snd => cases hv
      | .step _ .here => cases hv
    rw [e₁, show (θ.box.dia (.step x .keep) (.step (ι x) .keep)).under 0 0 T hs.root v =
      ((θ.box.dia (.step x .keep) (.step (ι x) .keep)) v).mono _ from if_neg hne]
    exact SubE.comp_mono_fix _ _ _ _ _
      (fun w W hw => Subst.single_at_ne (Ctx.ref_rt_ne hrB hw)) _ (hOd v U hl hv)

end

end V12M
