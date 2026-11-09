import QML.QML_v12m_LiftT
import QML.QML_v12m_GLoopStep

/-!
# QML v12m — weak B, 4 and 5 prove 4's lifts

With 4, 5 and weak B, T and strong B off, `Proof.keep_lift` is derivable at both legs
(`docs/v12-modal-extensions.md`, "KB5 and KDB5 without lifts: the check").  `Proof.five_refl` plays
`T_box`'s part in `QML_v12m_LiftT`, except at the last step, which needs closed T, `Proof.closed_T`.
B is closed, so the context's parameters are abstracted first, all at once: the `□` view is pulled
back to one root `r`, whose value is the `□` view tuple.
-/

namespace V12M

variable [ModalSys]

open BArrow GArrow

section Kept

variable {σ : Signature} {T : VarType}

/-- A body with its slot read kept, and nothing shifted.  `WFF.loopHat` is this at the shifted
    body (`WFF.loopHat_eq`). -/
def WFF.keptBody {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (ht : T.tup = true)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) : WFF σ (Γ.insert (.bnd 0) T).boxIn 1 :=
  have hle : Γ.boxIn.Le (Γ.insert (.bnd 0) T).boxIn :=
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root T).boxIn
  have hfr := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  WFF.subst (Subst.singleIdx (.bnd 0) (.tm (Term.keepOf hF T ht (.root (.bnd 0))
      (Ctx.ref_insert_root Γ (.bnd 0) T))))
    (Subst.single (.bnd 0) (.tm (Term.keepOf hF T ht (.root (.bnd 0))
      (Ctx.ref_insert_root Γ (.bnd 0) T))))
    (Subst.ok_single hle rfl) (Subst.coh_single hfr hle rfl)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
    ((Ctx.NoSlots.slots (Γ := Γ)).insert T).boxIn φ

theorem WFF.loopHat_eq {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (ht : T.tup = true)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    WFF.loopHat hF ht φ = WFF.keptBody (Γ := Γ.boxIn) hF ht
      (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ) :=
  rfl

/-- ⭐`∃y. ◇φ(y.keep)`: what the lift's subproof gets, before opening it. -/
def WFF.liftEx {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (ht : T.tup = true)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) : WFF σ Γ 0 :=
  .ex T (WFF.box (WFF.keptBody hF ht φ.neg)).neg

/-- `liftEx` of the shifted body is `∃y. ◇φ̂(y)`. -/
theorem WFF.liftEx_shift {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (ht : T.tup = true)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    WFF.liftEx (Γ := Γ.boxIn) hF ht
        (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ) =
      WFF.ex T (WFF.liftBody hF ht φ) :=
  rfl

/-- A keepable slot sent to an address, kept, is the address kept. -/
theorem Term.subst_keepOf_read (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (ht : T.tup = true) {Ω V : Ctx} {ι : VarSymb → VarSymb} (θ : Subst σ Ω) (hθ : Subst.Ok V θ)
    (hc : Subst.Coh ι V θ) (w : VarSymb) (h : V.ref w = some T) (y : VarSymb)
    (hy : Ω.ref y = some T) (hw : θ.at w = .tm (Term.eta y T hy)) :
    (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
      (Term.keepOf hF T ht w h)⟩ : Σ b, Term σ Ω.boxIn T b) =
      ⟨_, Term.keepOf hF T ht y hy⟩ := by
  have e : θ.box.at (.step w .keep) =
      .tm (Term.eta (.step y .keep) T (Ctx.ref_keep_of' hF hy hk)) := by
    rw [Subst.box_at_keep, hw, SubE.keepE_eta_of hF hy hk]
  cases T with
  | VTypeBox A => exact Term.subst_eta_tm _ _ _ _ _ _ _ e
  | VTypeDia A => exact Term.subst_eta_tm _ _ _ _ _ _ _ e
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd A B => cases hk

/-- ⭐`□` of a kept body, read at an address, is the body read at the address kept. -/
theorem WFF.keptBody_read {Γ Ω : Ctx} [Γ.NoSlots] [Ω.NoSlots] (hF : ModalSys.Four = true)
    (ht : T.tup = true) (hk : T.keepable = true) (h : Γ.Le Ω)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (w : VarSymb) (hw : Ω.ref w = some T) :
    WFF.instantiate Ctx.NoSlots.slots (Term.eta w T hw)
        (WFF.mono (h.insert (.bnd 0) T) (.box (WFF.keptBody hF ht φ))) =
      .box (WFF.instantiate Ctx.NoSlots.slots (Term.keepOf hF T ht w hw)
        (WFF.mono (h.boxIn.insert (.bnd 0) T) φ)) := by
  have hfr := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  have hfrΩ := (Ctx.NoSlots.slots (Γ := Ω)).rootFresh (le_refl 0)
  have hOk₃ : Subst.Ok (Γ.boxIn.insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keepOf hF T ht w hw))) :=
    Subst.ok_single h.boxIn rfl
  have hCo₃ : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.keepOf hF T ht w hw)))
      (Γ.boxIn.insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keepOf hF T ht w hw))) :=
    Subst.coh_single hfr h.boxIn rfl
  have hO : Subst.Ok (Ω.insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))) :=
    Subst.ok_single (Ctx.Le.refl _) rfl
  have hC : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.eta (σ := σ) w T hw)))
      (Ω.insert (.bnd 0) T) (Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))) :=
    Subst.coh_single hfrΩ (Ctx.Le.refl _) rfl
  refine congrArg WFF.box ((WFF.subst_mono _ _ _ _ _ _ _ _).trans
    ((WFF.subst_comp _ _ (Subst.single (.bnd 0) (.tm (Term.keepOf hF T ht w hw))) _ _ _ _
      hOk₃ hCo₃ _ _ _ ?_ _).trans (WFF.subst_mono _ _ _ _ _ _ _ _).symm))
  refine Subst.sim_of (hwit := fun _ _ _ _ => by wit_refl) ?_
  intro v U hl hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hU : T = U := by simpa [Ctx.insert] using hv
    subst hU
    have e := Term.subst_keepOf_read hF hk ht (Subst.single (.bnd 0) (.tm (Term.eta w T hw)))
      (hO.restrict (h.insert _ _)) (hC.restrict (h.insert _ _)) (.root (.bnd 0))
      (Ctx.ref_insert_root Γ (.bnd 0) T) w hw (Subst.at_single_root _ _)
    rw [Subst.comp_apply, Subst.single_self, Subst.single_self]
    exact SubE.Sim.of_sig e.symm _
  · have hv' : Γ.boxIn v = some U := by
      have := hv
      simpa [Ctx.insert, hvr] using this
    have hid : ∀ y W, Γ.ref y = some W →
        (Subst.single (σ := σ) (Δ := Ω) (.bnd 0) (.tm (Term.eta w T hw))).at y = .ren y :=
      fun _ _ hy => Subst.single_at_ne
        (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hy)
    change SubE.Sim U (if v = .root (.bnd 0) then _ else _)
      (SubE.comp _ _ _ (if v = .root (.bnd 0) then _ else _))
    rw [if_neg hvr, if_neg hvr]
    change SubE.Sim U _ (Subst.at _ v)
    rw [Subst.ren_box hid v U ((Ctx.ref_nonproj _ hl).trans hv')]
    exact .refl _

/-- `liftRead` along `□` is `liftEx`'s body, opened. -/
theorem WFF.liftRead_keptBody {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true)
    (hl : T.liftable = true) (ht : T.tup = true) (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) {c : ℕ}
    (hc : Γ.RootFresh (.free c)) :
    WFF.liftRead hF hl (.nec : OutLeg Γ) hc φ = WFF.openFree c hc Ctx.NoSlots.slots
      (WFF.box (WFF.keptBody hF ht φ.neg)).neg := by
  have hk := VarType.keepable_of_liftable hl
  have e := WFF.keptBody_read hF ht hk (Ctx.le_insert hc.root T) φ.neg (.root (.free c))
    (Ctx.ref_insert_root Γ (.free c) T)
  rw [WFF.openFree_neg, ← WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots Ctx.NoSlots.slots, e]
  cases T with
  | VTypeBox A => rfl
  | VTypeDia A => rfl
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd A B => cases hk

/-- ⭐**A kept body under a substitution** is the kept body of the image. -/
theorem WFF.subst_keptBody (hF : ModalSys.Four = true) (ht : T.tup = true)
    {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 T hΔ.root).box
        (Subst.ok_box (Subst.ok_under hθ T hΔ.root))
        (Subst.coh_box (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root))
        (hΓ.insert T).boxIn (hΔ.insert T).boxIn (WFF.keptBody hF ht φ) =
      WFF.keptBody hF ht (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 T hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) T hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn T hΔ.boxIn.root)
        (hΓ.boxIn.insert T) (hΔ.boxIn.insert T) φ) := by
  have hΘ := Subst.ok_box (Subst.ok_under (d := 0) hθ T hΔ.root)
  have hcΘ := Subst.coh_box (Subst.ok_under (d := 0) hθ T hΔ.root)
    (Subst.coh_under hθ hc hΓ T hΔ.root)
  have hL : Γ.boxIn.Le (Γ.insert (.bnd 0) T).boxIn := (Ctx.le_insert hΓ.root T).boxIn
  have hO := hΘ.restrict hL
  have hC := hcΘ.restrict hL
  have hfr := hΓ.boxIn.rootFresh (le_refl 0)
  have hr := hΔ.boxIn.rootFresh (le_refl 0)
  have hΨ := Subst.ok_set (r := .bnd 0) (T := T)
    (e := .tm (Term.keepOf hF T ht (.root (.bnd 0)) (Ctx.ref_insert_root Δ (.bnd 0) T))) hO rfl
  have hcΨ := Subst.coh_set (r := .bnd 0) (T := T)
    (e := .tm (Term.keepOf hF T ht (.root (.bnd 0)) (Ctx.ref_insert_root Δ (.bnd 0) T)))
    hO hC hfr rfl
  have hKs := (Term.subst_keepOf hF (θ.under 0 0 T hΔ.root) (θ.under 0 0 T hΔ.root).box hΘ hcΘ
    (Ctx.Le.refl _) (fun p U hp _ _ => by
      rw [Subst.at_nonproj _ rfl]
      change ((θ.under 0 0 T hΔ.root).at p).keepE = _
      rw [hp]
      rfl) T ht (.root (.bnd 0)) (Ctx.ref_insert_root Γ (.bnd 0) T)
    (Ctx.ref_insert_root Δ (.bnd 0) T) (by
      rw [Subst.at_nonproj _ rfl]
      exact Subst.under_slot _ _ _ _ _)).trans (congrArg (Sigma.mk _) (Term.mono_refl _ _))
  unfold WFF.keptBody
  refine (WFF.subst_comp _ _ ((θ.under 0 0 T hΔ.root).box.set (.bnd 0)
    (.tm (Term.keepOf hF T ht (.root (.bnd 0)) (Ctx.ref_insert_root Δ (.bnd 0) T)))) _ _ _ _ hΨ hcΨ
    _ _ _ ?_ _).trans (WFF.subst_comp _ _ _ _ _ _ _ hΨ hcΨ _ _ _ ?_ _).symm
  · refine Subst.sim_of (hwit := fun _ _ _ _ => by wit_refl) fun v U hl hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      change SubE.Sim _ (Subst.set _ (.bnd 0) _ (.root (.bnd 0)))
        (SubE.comp _ _ _ (Subst.single (.bnd 0) (.tm _) (.root (.bnd 0))))
      rw [Subst.set_root, Subst.single_root]
      exact SubE.Sim.of_sig hKs.symm _
    · change SubE.Sim U (Subst.set _ (.bnd 0) _ v)
        (SubE.comp _ _ _ (Subst.single (.bnd 0) (.tm _) v))
      rw [Subst.set_ne _ _ hvr, Subst.single_ne _ hvr]
      change SubE.Sim U _ (Subst.at _ v)
      rw [Subst.at_nonproj _ hl]
      exact .refl _
  · refine Subst.sim_of (hwit := fun _ _ _ _ => by wit_refl) fun v U hl hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.comp_apply]
      rw [Subst.set_root, show Subst.under θ.box 0 0 T hΔ.boxIn.root (.root (.bnd 0)) =
        .ren (.root (.bnd 0)) from by slot_rfl]
      change SubE.Sim _ _ ((Subst.single (.bnd 0) _).at (.root (.bnd 0)))
      rw [Subst.at_single_root]
      exact .refl _
    · have hv' : Γ.boxIn v = some U := by
        have := hv
        simpa [Ctx.insert, hvr] using this
      rw [Subst.comp_apply]
      rw [Subst.set_ne _ _ hvr, Subst.box_under_eq θ hΓ hΔ.root hv',
        show Subst.under θ.box 0 0 T hΔ.boxIn.root v = (θ.box v).mono _ from if_neg hvr]
      exact SubE.comp_mono_fix _ _ _ _ _
        (fun w W hw => Subst.single_at_ne (Ctx.ref_rt_ne hr hw)) _ (Subst.ok_box hθ v U hl hv')

/-- ⭐`liftEx` under a substitution is `liftEx` of the image. -/
theorem WFF.subst_liftEx (hF : ModalSys.Four = true) (ht : T.tup = true)
    {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.liftEx hF ht φ) =
      WFF.liftEx hF ht (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 T hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) T hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn T hΔ.boxIn.root)
        (hΓ.boxIn.insert T) (hΔ.boxIn.insert T) φ) :=
  congrArg (fun z => WFF.ex T (WFF.box z).neg) (WFF.subst_keptBody hF ht θ hθ hc hΓ hΔ φ.neg)

end Kept

/-! ## Out and back: the rule in `T_box`'s place -/

section Back

variable {σ : Signature} {T : VarType}

/-- The rule's body along `□`: `∀c. □φ̂(c) → φ(c)`. -/
abbrev WFF.reflBody {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (ht : T.tup = true)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) : WFF σ Γ.boxIn 0 :=
  .all T (.imp (.box (WFF.loopHat hF ht φ)) φ)

/-- `Proof.far_nec`, with the rule's body for `T_box`. -/
def Proof.far_necU (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hk : T.keepable = true) (ht : T.tup = true) {Γ : Ctx} [Γ.NoSlots]
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (c : ℕ) (hc : Γ.boxIn.RootFresh (.free c)) :
    Proof σ (Γ.boxIn.insert (.free c) T)
      [WFF.openFree c hc Ctx.NoSlots.slots φ, WFF.weaken hc.root T (WFF.reflBody hF ht φ.neg)]
      (.box (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF (Γ.boxIn.insert (.free c) T))
        Ctx.NoSlots.slots
        (WFF.instantiate Ctx.NoSlots.slots
          (Term.keepOf hF T ht (.root (.free c)) (Ctx.ref_insert_root Γ.boxIn (.free c) T))
          (WFF.mono ((Ctx.le_insert hc.root T).boxIn.insert (.bnd 0) T)
            (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
              φ.neg))))).neg) := by
  have e := WFF.keptBody_read (Γ := Γ.boxIn) hF ht hk (Ctx.le_insert hc.root T)
    (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ.neg)
    (.root (.free c)) (Ctx.ref_insert_root Γ.boxIn (.free c) T)
  have e₂ := WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ.neg
  refine Proof.byContra (Proof.imp_elim ?_
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
  refine Proof.imp_elim (φ := .box _) (Proof.conv (congrArg₂ WFF.imp e e₂) ?_)
    (Proof.five_box hF hV (Proof.lookup List.mem_cons_self))
  exact Proof.all_elim T (Term.eta (.root (.free c)) T (Ctx.ref_insert_root Γ.boxIn (.free c) T))
    (φ := WFF.mono ((Ctx.le_insert hc.root T).insert (.bnd 0) T)
      (.imp (.box (WFF.loopHat hF ht φ.neg)) φ.neg))
    (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- `Proof.far_ex`, with the rule's body for `T_box`. -/
def Proof.far_exU (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hk : T.keepable = true) (ht : T.tup = true) {Γ : Ctx} [Γ.NoSlots]
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (c : ℕ) (hc : Γ.boxIn.RootFresh (.free c)) :
    Proof σ Γ.boxIn [WFF.ex T φ, WFF.reflBody hF ht φ.neg]
      (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots
        (WFF.ex T (WFF.liftBody hF ht φ)))) := by
  have hle := Ctx.le_insert hc.root T
  have hk' := Term.kept_keepOf (σ := σ) hF hk ht (K := Γ.boxIn.insert (.free c) T)
    (.root (.free c)) (Ctx.ref_insert_root Γ.boxIn (.free c) T)
  have eS : WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
      (WFF.liftBody hF ht φ) = WFF.liftBody (Γ := Γ.boxIn) hF ht
        (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ) :=
    congrArg WFF.neg (congrArg WFF.box (WFF.shift_loopHat hF hk ht φ.neg))
  have hb : Proof σ (Γ.boxIn.insert (.free c) T).boxIn
      [(WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF (Γ.boxIn.insert (.free c) T))
        Ctx.NoSlots.slots
        (WFF.instantiate Ctx.NoSlots.slots
          (Term.keepOf hF T ht (.root (.free c)) (Ctx.ref_insert_root Γ.boxIn (.free c) T))
          (WFF.mono ((Ctx.le_insert hc.root T).boxIn.insert (.bnd 0) T)
            (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
              φ.neg))))).neg]
      (WFF.ex T (WFF.mono (hle.boxIn.insert (.bnd 0) T)
        (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
          (WFF.liftBody hF ht φ)))) := by
    refine Proof.ex_intro T (Term.keepOf hF T ht (.root (.free c))
      (Ctx.ref_insert_root Γ.boxIn (.free c) T)) ?_
    rw [eS, WFF.liftBody_read hF ht hle _ hk']
    exact Proof.lookup List.mem_cons_self
  refine Proof.ex_elim c T hc (φ := WFF.openFree c hc Ctx.NoSlots.slots φ)
    (Proof.conv (congrArg (WFF.ex T)
      (WFF.bindFree_openFree c hc (Ctx.NoSlots.slots (Γ := Γ.boxIn)) φ).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  refine Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx)
    (Proof.imp_intro (Proof.K_box (Δ := [_]) hb))) ?_
  refine Proof.ofSubset (fun y hy => ?_) (Proof.far_necU hF hV hk ht φ c hc)
  rcases List.mem_cons.mp hy with rfl | hy
  · exact List.mem_cons_self
  · rw [List.mem_singleton.mp hy]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

/-- ⭐**`□∃y. ◇φ̂(y)`, from `◇∃c. φ(c)`** (4, 5, the rule; no B). -/
def Proof.lift_boxU (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hN : ModalSys.shaped = false) (hk : T.keepable = true) (ht : T.tup = true) {Γ : Ctx}
    [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (c : ℕ)
    (hc : Γ.boxIn.RootFresh (.free c))
    (p : Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.ex T φ))) :
    Proof σ Γ Δ (.box (WFF.ex T (WFF.liftBody hF ht φ))) := by
  have hr : Proof σ Γ Δ (.box (WFF.reflBody hF ht φ.neg)) := Proof.five_refl hF hV hN .nec ht φ.neg
  refine Proof.five_box hF hV (Proof.imp_intro ?_)
  have a : Proof σ Γ.boxIn [(WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots
      (WFF.ex T (WFF.liftBody hF ht φ)))).neg, WFF.reflBody hF ht φ.neg] (WFF.ex T φ).neg := by
    refine Proof.imp_intro (Proof.imp_elim
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ofSubset (fun y hy => ?_) (Proof.far_exU hF hV hk ht φ c hc)))
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    · rw [List.mem_singleton.mp hy]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have b := Proof.imp_intro (Proof.imp_intro (Proof.K_box a))
  refine Proof.imp_elim (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) p) ?_
  exact Proof.imp_elim (Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx) b)
    (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) hr)) (Proof.lookup List.mem_cons_self)

end Back

/-! ## One generic parameter -/

section Generic

variable {σ : Signature} {T K : VarType}

theorem Ctx.boxIn_empty_le : Ctx.empty.boxIn.Le Ctx.empty := by
  refine ⟨fun v U h => ?_, fun y X h => ?_⟩
  swap
  · have := (Ctx.boxIn_wit.mp h).2
    rw [Ctx.ref_empty] at this
    cases this
  exfalso
  match v, h with
  | .root _, h => cases h
  | .step u s, h =>
      cases s with
      | box =>
          have := (Ctx.boxIn_box h).2
          rw [Ctx.ref_empty] at this
          cases this
      | keep =>
          have := (Ctx.boxIn_keep h).2.1
          rw [Ctx.ref_empty] at this
          cases this
      | dia => cases h
      | fst => cases h
      | snd => cases h
      | here => cases h

/-- ⭐**The rule, closed by closed T** (the only use of B): with `□⊥` refuted, `∀k. □ζ̂(k) → ζ(k)`
    holds here, for `ζ` closed apart from its slot. -/
def Proof.root_refl (hB : ModalSys.B = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hN : ModalSys.shaped = false) (hK : K.tup = true)
    (ζ : WFF σ (Ctx.empty.boxIn.insert (.bnd 0) K) 1) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)}
    (hne : Proof σ (ctxOf l) Δ (WFF.box (Γ := ctxOf l) .bot).neg) :
    Proof σ (ctxOf l) Δ (WFF.mono (Ctx.boxIn_empty_le.trans (Ctx.empty_le _))
      (.all K (.imp (.box (WFF.loopHat hF hK ζ)) ζ))) := by
  have r : Proof σ Ctx.empty [] (WFF.fiveRefl hF hK (.nec : OutLeg Ctx.empty) ζ) :=
    Proof.five_refl hF hV hN .nec hK ζ
  have m := Proof.mono (Ctx.empty_le (ctxOf l)) r
  refine Proof.conv ?_ (Proof.closed_T hB hF
    (WFF.mono Ctx.boxIn_empty_le (.all K (.imp (.box (WFF.loopHat hF hK ζ)) ζ))) hne
    (Proof.conv ?_ (Proof.ofSubset (fun _ hx => by cases hx) m)))
  · exact WFF.mono_mono _ _ _
  · exact congrArg WFF.box (WFF.mono_mono _ _ _).symm

/-- A possibility refutes `□⊥`. -/
def Proof.not_box_bot {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {χ : WFF σ Γ.boxIn 0}
    (p : Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia χ)) :
    Proof σ Γ Δ (WFF.box (Γ := Γ) .bot).neg := by
  have q : Proof σ Γ.boxIn [.bot] χ.neg :=
    Proof.imp_intro (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  refine Proof.imp_intro (Proof.imp_elim
    (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) p) ?_)
  exact Proof.ofSubset (fun z hz => by
    rw [List.mem_singleton.mp hz]
    exact List.mem_cons_self) (Proof.K_box (Δ := [.bot]) q)

/-- The generic parameter. -/
abbrev genR : VarSymb := .root (.free 0)

theorem genR_ref (K : VarType) : (ctxOf [K]).ref genR = some K := ctxOf_ref_new K []

omit [ModalSys] in
/-- With T off, a keepable generic parameter is the context's only address. -/
theorem genR_only [ModalSys] (hT : ModalSys.T = false) (hK : K.keepable = true) :
    ∀ (u : VarSymb) (U : VarType), (ctxOf [K]).ref u = some U → u = genR ∧ U = K
  | .root x, U, h => by
      by_cases hx : x = .free 0
      · subst hx
        rw [genR_ref] at h
        exact ⟨rfl, (Option.some.inj h).symm⟩
      · exfalso
        have h' : (Ctx.empty.insert (.free 0) K) (.root x) = some U := h
        simp [Ctx.insert, hx, Ctx.empty] at h'
  | .step u s, U, h => by
      exfalso
      by_cases hs : s.isProj = true
      · have h' : ((ctxOf [K]).ref u).bind (·.step s) = some U := by
          have := h
          simpa [Ctx.ref, hs] using this
        cases hu : (ctxOf [K]).ref u with
        | none =>
            rw [hu] at h'
            cases h'
        | some W =>
            obtain ⟨-, rfl⟩ := genR_only hT hK u W hu
            rw [hu] at h'
            cases W with
            | Var => cases hK
            | VTypeOne => cases hK
            | VTypeProd A B => cases hK
            | VTypeBox A =>
                cases s <;> first | (simp [VarType.step, hT] at h'; done) | cases hs
            | VTypeDia A =>
                cases s <;> first | (simp [VarType.step, hT] at h'; done) | cases hs
      · have h' : (Ctx.empty.insert (.free 0) K) (.step u s) = some U := by
          have := h
          simpa [Ctx.ref, hs] using this
        simp [Ctx.insert, Ctx.empty] at h'

/-- `r ↦ r.keep`: shifting the generic parameter's view. -/
abbrev genKeep (σ : Signature) (K : VarType) : Subst σ (ctxOf [K]).boxIn :=
  Subst.single (.free 0) (.ren (.step genR .keep))

theorem ok_genKeep (hF : ModalSys.Four = true) (hK : K.keepable = true) :
    Subst.Ok (ctxOf [K]) (genKeep σ K) :=
  Subst.ok_single (Γ := Ctx.empty) (Ctx.empty_le _) (Ctx.ref_keep_of' hF (genR_ref K) hK)

theorem coh_genKeep (hF : ModalSys.Four = true) (hK : K.keepable = true) :
    Subst.Coh (Subst.singleIdx (σ := σ) (Δ := (ctxOf [K]).boxIn) (.free 0)
      (.ren (.step genR .keep))) (ctxOf [K]) (genKeep σ K) :=
  Subst.coh_single (Γ := Ctx.empty) (Ctx.RootFresh.empty _) (Ctx.empty_le _)
    (Ctx.ref_keep_of' hF (genR_ref K) hK)

/-- ⭐**At one keepable parameter, `shift` is the substitution `r ↦ r.keep`.** -/
theorem WFF.shift_gen (hF : ModalSys.Four = true) (hT : ModalSys.T = false)
    (hK : K.keepable = true) (ξ : WFF σ (ctxOf [K]).boxIn 0) :
    WFF.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf [K])) Ctx.NoSlots.slots ξ =
      WFF.subst _ (genKeep σ K).box (Subst.ok_box (ok_genKeep hF hK))
        (Subst.coh_box (ok_genKeep hF hK) (coh_genKeep hF hK)) Ctx.NoSlots.slots
        Ctx.NoSlots.slots ξ := by
  have hb : ModalSys.keepOnly = false := by simp [ModalSys.keepOnly, hT]
  have C := Ctx.shifts_boxIn_boxIn hF (ctxOf [K])
  have e := WFF.subst_shift C Ctx.NoSlots.slots Ctx.NoSlots.slots (Subst.idS σ _) Subst.ok_idS
    Subst.coh_idS (Subst.atShift (Subst.idS σ _)) (Subst.ok_atShift C Subst.ok_idS)
    (Subst.coh_atShift C Subst.ok_idS Subst.coh_idS levels_boxIn_ctxOf) Ctx.NoSlots.slots
    (Subst.preShift_atShift _ _) ξ
  rw [WFF.subst_id] at e
  refine e.trans (WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ξ)
  refine Subst.sim_of (hwit := fun _ _ _ _ => by wit_refl) fun v U hl hv => ?_
  match v, hl, hv with
  | .step u .box, _, hv =>
      obtain ⟨rfl, -⟩ := genR_only hT hK u _ (Ctx.boxIn_box hv).2
      change SubE.Sim U ((Subst.idS σ _).at _) ((genKeep σ K).at genR).unbox
      rw [Subst.at_idS, VarSymb.shift_level_zero rfl, Subst.at_single_root]
      change SubE.Sim U _ (.ren (VarSymb.inner _))
      rw [show VarSymb.inner (.step genR .keep) = .step (.step genR .keep) .box by
        simp [VarSymb.inner, hb]]
      exact .refl _
  | .step u .keep, _, hv =>
      obtain ⟨rfl, -⟩ := genR_only hT hK u _ (Ctx.boxIn_keep hv).2.1
      change SubE.Sim U ((Subst.idS σ _).at _) ((genKeep σ K).at genR).keepE
      rw [Subst.at_idS, VarSymb.shift_level_zero rfl, Subst.at_single_root]
      exact .refl _
  | .root _, _, hv => cases hv
  | .step _ .fst, _, hv => cases hv
  | .step _ .snd, _, hv => cases hv
  | .step _ .dia, _, hv => cases hv
  | .step _ .here, _, hv => cases hv

/-- `liftEx` with the generic parameter bound: closed apart from the slot. -/
abbrev WFF.genBody (hF : ModalSys.Four = true) (ht : T.tup = true)
    (χ : WFF σ ((ctxOf [K]).boxIn.insert (.bnd 0) T) 1) :
    WFF σ (Ctx.empty.boxIn.insert (.bnd 0) K) 1 :=
  WFF.mono ((Ctx.empty_le _).insert (.bnd 0) K)
    (WFF.bindFree 0 (Ctx.RootFresh.empty _) Ctx.NoSlots.slots K
      (WFF.liftEx (Γ := ctxOf [K]) hF ht χ))

/-- ⭐**The closed sentence the lift reads**: `∀k. □ζ̂(k) → ζ(k)`, at `ζ` the lift's conclusion with
    the generic parameter bound.  Its necessity is a theorem (`Proof.genAx_nec`); with weak B it
    holds wherever something is accessible (`Proof.root_refl`). -/
def WFF.genAx (hF : ModalSys.Four = true) (ht : T.tup = true) (hKt : K.tup = true)
    (χ : WFF σ ((ctxOf [K]).boxIn.insert (.bnd 0) T) 1) : WFF σ Ctx.empty 0 :=
  WFF.mono Ctx.boxIn_empty_le (.all K (.imp (.box (WFF.loopHat hF hKt (WFF.genBody hF ht χ)))
    (WFF.genBody hF ht χ)))

/-- ⭐`□genAx` is a theorem: the rule at the empty context. -/
def Proof.genAx_nec (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hN : ModalSys.shaped = false) (ht : T.tup = true) (hKt : K.tup = true)
    (χ : WFF σ ((ctxOf [K]).boxIn.insert (.bnd 0) T) 1) :
    Proof σ Ctx.empty [] (.box ((WFF.genAx hF ht hKt χ).closed Ctx.empty.boxIn)) :=
  Proof.conv (congrArg WFF.box ((WFF.mono_mono _ _ _).trans (WFF.mono_refl _ _)).symm)
    (Proof.five_refl hF hV hN .nec hKt (WFF.genBody hF ht χ))

/-- ⭐**The lift at one generic parameter.**  `□ξ` from `Proof.lift_boxU`, read in `genAx` at the
    parameter: `ζ̂(r)` is `ζ(r.keep)`, which is `ξ`. -/
def Proof.lift_gen (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hN : ModalSys.shaped = false) (hT : ModalSys.T = false)
    (hk : T.keepable = true) (ht : T.tup = true) (hK : K.keepable = true) (hKt : K.tup = true)
    {Δ : List (WFF σ (ctxOf [K]) 0)} (χ : WFF σ ((ctxOf [K]).boxIn.insert (.bnd 0) T) 1)
    (p : Proof σ (ctxOf [K]) Δ ((OutLeg.nec : OutLeg (ctxOf [K])).dia (WFF.ex T χ)))
    (hax : Proof σ (ctxOf [K]) Δ ((WFF.genAx hF ht hKt χ).closed _)) :
    Proof σ (ctxOf [K]) Δ (WFF.liftEx hF ht χ) := by
  have hfr₀ : Ctx.empty.RootFresh (.free 0) := Ctx.RootFresh.empty _
  have hbox := Proof.lift_boxU hF hV hN hk ht χ 1 (ctxOf_fresh (l := [K]) le_rfl).boxIn p
  have hle : Ctx.empty.boxIn.Le (ctxOf [K]) := Ctx.boxIn_empty_le.trans (Ctx.empty_le _)
  have hleb : Ctx.empty.boxIn.Le (ctxOf [K]).boxIn := Ctx.boxIn_empty_le.trans (Ctx.empty_le _)
  have hr := genR_ref K
  have hfr := (Ctx.NoSlots.slots (Γ := Ctx.empty.boxIn)).rootFresh (le_refl 0)
  have hO : Subst.Ok (Ctx.empty.boxIn.insert (.bnd 0) K)
      (Subst.single (σ := σ) (Δ := ctxOf [K]) (.bnd 0) (.tm (Term.eta genR K hr))) :=
    Subst.ok_single hle rfl
  have hC : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.eta genR K hr)))
      (Ctx.empty.boxIn.insert (.bnd 0) K)
      (Subst.single (σ := σ) (Δ := ctxOf [K]) (.bnd 0) (.tm (Term.eta genR K hr))) :=
    Subst.coh_single hfr hle rfl
  have hk' := Term.subst_keepOf_read hF hK hKt _ hO hC (.root (.bnd 0))
    (Ctx.ref_insert_root _ _ K) genR hr (Subst.at_single_root _ _)
  have e₁ := WFF.subst_loopHat (Γ := Ctx.empty) (Γ₁ := ctxOf [K]) hF hKt _ hO hC hleb _ hk'
    (fun v U _ hv => by
      have h := Ctx.boxIn_empty_le v U hv
      cases h) (WFF.genBody hF ht χ)
  have e₃ : WFF.subst _ ((genKeep σ K).box.under 0 0 T
      (Ctx.NoSlots.slots (Γ := (ctxOf [K]).boxIn.boxIn)).root) _ _ _ _ χ =
      WFF.shift (Ctx.shifts_loop hF (ctxOf [K]) T)
        ((Ctx.NoSlots.slots (Γ := (ctxOf [K]).boxIn)).insert T) χ :=
    (eq_of_heq (WFF.ex.inj (WFF.shift_gen hF hT hK (.ex T χ))).2).symm
  have eL : WFF.instantiate Ctx.NoSlots.slots (Term.eta genR K hr)
      (WFF.mono (hle.insert (.bnd 0) K) (.box (WFF.loopHat hF hKt (WFF.genBody hF ht χ)))) =
      .box (WFF.liftEx (Γ := (ctxOf [K]).boxIn) hF ht
        (WFF.shift (Ctx.shifts_loop hF (ctxOf [K]) T)
          ((Ctx.NoSlots.slots (Γ := (ctxOf [K]).boxIn)).insert T) χ)) := by
    refine congrArg WFF.box ((WFF.subst_mono _ _ _ _ _ _ _ _).trans (e₁.trans ?_))
    rw [WFF.mono_mono]
    refine (WFF.instantiate_bindFree (Ctx.empty_le (ctxOf [K]).boxIn) 0 hfr₀
      (Term.keepOf hF K hKt genR hr) (WFF.liftEx (Γ := ctxOf [K]) hF ht χ)).trans ?_
    refine (WFF.subst_congr _ (genKeep σ K) _ (ok_genKeep hF hK) _ (coh_genKeep hF hK) _ _ ?_
      _).trans ?_
    · refine Subst.sim_of (hwit := fun _ _ _ _ => by wit_refl) fun v U hl hv => ?_
      by_cases hvr : v = .root (.free 0)
      · subst hvr
        have hU : K = U := Option.some.inj ((genR_ref K).symm.trans hv)
        subst hU
        change SubE.Sim K (Subst.single _ _ (.root (.free 0))) (Subst.single _ _ (.root (.free 0)))
        rw [Subst.single_root, Subst.single_root]
        cases K with
        | VTypeBox A => exact .eta_ren _ _
        | VTypeDia A => exact .eta_ren _ _
        | Var => cases hK
        | VTypeOne => cases hK
        | VTypeProd A B => cases hK
      · change SubE.Sim U (Subst.single _ _ v) (Subst.single _ _ v)
        rw [Subst.single_ne _ hvr, Subst.single_ne _ hvr]
        exact .refl _
    · exact (WFF.subst_liftEx hF ht (genKeep σ K) (ok_genKeep hF hK) (coh_genKeep hF hK)
        Ctx.NoSlots.slots Ctx.NoSlots.slots χ).trans (congrArg (WFF.liftEx hF ht) e₃)
  have eR : WFF.instantiate Ctx.NoSlots.slots (Term.eta genR K hr)
      (WFF.mono (hle.insert (.bnd 0) K) (WFF.genBody hF ht χ)) = WFF.liftEx hF ht χ := by
    rw [WFF.mono_mono]
    exact (WFF.instantiate_eta_openFree 0 hfr₀ Ctx.NoSlots.slots Ctx.NoSlots.slots _).trans
      (WFF.openFree_bindFree 0 hfr₀ Ctx.NoSlots.slots _)
  have F : Proof σ (ctxOf [K]) Δ (WFF.mono (Ctx.boxIn_empty_le.trans (Ctx.empty_le _))
      (.all K (.imp (.box (WFF.loopHat hF hKt (WFF.genBody hF ht χ))) (WFF.genBody hF ht χ)))) :=
    Proof.conv (WFF.mono_mono _ _ _) hax
  exact Proof.imp_elim (Proof.conv (congrArg₂ WFF.imp eL eR)
    (Proof.all_elim K (Term.eta genR K hr) (φ := WFF.mono (hle.insert (.bnd 0) K)
      (.imp (.box (WFF.loopHat hF hKt (WFF.genBody hF ht χ))) (WFF.genBody hF ht χ))) F))
    (Proof.conv (congrArg WFF.box (WFF.liftEx_shift hF ht χ).symm) hbox)

end Generic

/-! ## The whole `□` view, as one parameter -/

section Whole

variable {σ : Signature} {T : VarType}

/-- The type of the `□` view tuple. -/
abbrev boxK (l : List VarType) : VarType := .VTypeBox (itemsTy (boxItems l))

/-- The generic parameter at the `□` view tuple. -/
abbrev tupS (σ : Signature) (hF : ModalSys.Four = true) (l : List VarType) : Subst σ (ctxOf l) :=
  Subst.single (.free 0) (.tm (Term.boxtm (itemsTm (boxItems l) (boxItems_ref hF l)).2))

theorem ok_tupS (hF : ModalSys.Four = true) (l : List VarType) :
    Subst.Ok (ctxOf [boxK l]) (tupS σ hF l) :=
  Subst.ok_single (Γ := Ctx.empty) (Ctx.empty_le _) rfl

theorem coh_tupS (hF : ModalSys.Four = true) (l : List VarType) :
    Subst.Coh (Subst.singleIdx (.free 0) (.tm (Term.boxtm (itemsTm (σ := σ) (boxItems l)
      (boxItems_ref hF l)).2))) (ctxOf [boxK l]) (tupS σ hF l) :=
  Subst.coh_single (Γ := Ctx.empty) (Ctx.RootFresh.empty _) (Ctx.empty_le _) rfl

/-- ⭐**The `□` view tuple undoes the pull-back.** -/
theorem WFF.subst_pull_tuple (hF : ModalSys.Four = true) (hT : ModalSys.T = false)
    {l : List VarType} (ξ : WFF σ (ctxOf l).boxIn 0) :
    WFF.subst _ (tupS σ hF l).box (Subst.ok_box (ok_tupS hF l))
        (Subst.coh_box (ok_tupS hF l) (coh_tupS hF l)) Ctx.NoSlots.slots Ctx.NoSlots.slots
        (WFF.subst (pullBoxIdx l genR) (pullBoxS l genR) (ok_pullBoxS hF (genR_ref (boxK l)))
          (coh_pullBoxS hF (genR_ref (boxK l))) Ctx.NoSlots.slots Ctx.NoSlots.slots ξ) = ξ := by
  have hb : ModalSys.keepOnly = false := by simp [ModalSys.keepOnly, hT]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ ξ).trans
    (WFF.subst_id _ _ _ ξ)
  refine Subst.sim_of (hwit := fun _ _ _ _ => by wit_refl) fun v U _ hv => ?_
  change SubE.Sim U (.ren v) ((pullBoxS l genR v).comp _ _ _)
  have hm := mem_boxItems hv
  have hany : (boxItems l).any (·.1 == v) = true := List.any_eq_true.mpr ⟨_, hm, by simp⟩
  have hlt := findIdx_lt_boxItems hm
  have hin : (tupS σ hF l).box.at genR.inner =
      .tm (itemsTm (boxItems l) (boxItems_ref hF l)).2 := by
    rw [VarSymb.inner_box hb, Subst.at_nonproj _ rfl]
    change ((tupS σ hF l).at genR).unbox = _
    rw [Subst.at_single_root]
    rfl
  rw [pullBoxS_item hany]
  change SubE.Sim U (.ren _) ((tupS σ hF l).box.at _)
  rw [Subst.at_ext_ppath _ _ _ (itemPath_ppath _), hin, projs_itemsTm _ _ _ hlt]
  refine SubE.sim_ren_eta' _ (getElem_findIdx_boxItems hm) ?_
  have e := boxItems_spec hF l _ (List.getElem_mem hlt)
  rw [getElem_findIdx_boxItems hm, hv] at e
  exact (Option.some.inj e).symm

/-- The body pulled back to the generic parameter. -/
def WFF.pullGen (hF : ModalSys.Four = true) {l : List VarType}
    (φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) :
    WFF σ ((ctxOf [boxK l]).boxIn.insert (.bnd 0) T) 1 :=
  have hO := ok_pullBoxS (σ := σ) hF (genR_ref (boxK l))
  have hC := coh_pullBoxS (σ := σ) hF (genR_ref (boxK l))
  have hs := Ctx.NoSlots.slots (Γ := (ctxOf [boxK l]).boxIn)
  have hs₀ := Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)
  WFF.subst (VarSymb.shiftSlot (pullBoxIdx l genR) 0 0) ((pullBoxS l genR).under 0 0 T hs.root)
    (Subst.ok_under hO T hs.root) (Subst.coh_under hO hC hs₀ T hs.root) (hs₀.insert T)
    (hs.insert T) φ

/-- ⭐**The closed sentence the lift of `φ` reads**: `genAx` at the pulled-back body. -/
def WFF.liftAx (hF : ModalSys.Four = true) (ht : T.tup = true) {l : List VarType}
    (φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) : WFF σ Ctx.empty 0 :=
  WFF.genAx hF ht rfl (WFF.pullGen hF φ)

/-- ⭐`□liftAx` is a theorem. -/
def Proof.liftAx_nec (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hN : ModalSys.shaped = false) (ht : T.tup = true) {l : List VarType}
    (φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) :
    Proof σ Ctx.empty [] (.box ((WFF.liftAx hF ht φ).closed Ctx.empty.boxIn)) :=
  Proof.genAx_nec hF hV hN ht rfl _

/-- ⭐⭐**`∃y. ◇φ(y.keep)`, from `◇∃c. φ(c)` and `liftAx φ`** (4 and 5, T and strong B off): the
    lift at the generic parameter, which `tupS` brings back to the whole context. -/
def Proof.lift_exF (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hN : ModalSys.shaped = false) (hT : ModalSys.T = false)
    (hk : T.keepable = true) (ht : T.tup = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} (φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1)
    (p : Proof σ (ctxOf l) Δ ((OutLeg.nec : OutLeg (ctxOf l)).dia (WFF.ex T φ)))
    (hax : Proof σ (ctxOf l) Δ ((WFF.liftAx hF ht φ).closed _)) :
    Proof σ (ctxOf l) Δ (WFF.liftEx hF ht φ) := by
  have g : Proof σ (ctxOf [boxK l])
      [(OutLeg.nec : OutLeg (ctxOf [boxK l])).dia (WFF.ex T (WFF.pullGen hF φ)),
        (WFF.genAx hF ht rfl (WFF.pullGen hF φ)).closed _]
      (WFF.liftEx hF ht (WFF.pullGen hF φ)) :=
    Proof.lift_gen hF hV hN hT hk ht rfl rfl _ (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
  have s := Proof.subst g (tupS σ hF l) (ok_tupS hF l) (coh_tupS hF l) Ctx.NoSlots.slots
  have e₁ : WFF.subst _ (tupS σ hF l).box (Subst.ok_box (ok_tupS hF l))
      (Subst.coh_box (ok_tupS hF l) (coh_tupS hF l)) Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.ex T (WFF.pullGen hF φ)) = WFF.ex T φ := WFF.subst_pull_tuple hF hT (WFF.ex T φ)
  have e₂ : WFF.subst _ (tupS σ hF l) (ok_tupS hF l) (coh_tupS hF l) Ctx.NoSlots.slots
      Ctx.NoSlots.slots ((WFF.genAx hF ht rfl (WFF.pullGen hF φ)).closed _) =
      (WFF.liftAx hF ht φ).closed _ := WFF.subst_mono_empty _ _ _ _ _ _ _ _
  have ec := (WFF.subst_liftEx hF ht (tupS σ hF l) (ok_tupS hF l) (coh_tupS hF l)
    Ctx.NoSlots.slots Ctx.NoSlots.slots (WFF.pullGen hF φ)).trans
    (congrArg (WFF.liftEx hF ht) (eq_of_heq (WFF.ex.inj e₁).2))
  have s' : Proof σ (ctxOf l) [(OutLeg.nec : OutLeg (ctxOf l)).dia (WFF.ex T φ),
      (WFF.liftAx hF ht φ).closed _] (WFF.liftEx hF ht φ) :=
    Proof.conv ec (Proof.castHyps (congrArg₂ (fun z y => [(WFF.box (WFF.neg z)).neg, y]) e₁ e₂) s)
  exact Proof.imp_elim (Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx)
    (Proof.imp_intro (Proof.imp_intro s'))) hax) p

/-- ⭐⭐**`∃y. ◇φ(y.keep)`, from `◇∃c. φ(c)`** (4, 5, weak B, T and strong B off): `liftAx` by
    closed T. -/
def Proof.lift_exB (hB : ModalSys.B = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hN : ModalSys.shaped = false) (hT : ModalSys.T = false)
    (hk : T.keepable = true) (ht : T.tup = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} (φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1)
    (p : Proof σ (ctxOf l) Δ ((OutLeg.nec : OutLeg (ctxOf l)).dia (WFF.ex T φ))) :
    Proof σ (ctxOf l) Δ (WFF.liftEx hF ht φ) :=
  Proof.lift_exF hF hV hN hT hk ht φ p (Proof.conv (WFF.mono_mono _ _ _).symm
    (Proof.root_refl hB hF hV hN rfl (WFF.genBody hF ht (WFF.pullGen hF φ)) (Proof.not_box_bot p)))

/-- ⭐⭐**`keep_lift` along `□`, given `liftAx`** (4 and 5, T and strong B off), whatever
    `FourStrong` and `FourStrongW` say. -/
def Proof.keep_lift_F (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hN : ModalSys.shaped = false) (hT : ModalSys.T = false)
    (hl : T.liftable = true) (ht : T.tup = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} (φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) (c : ℕ)
    (hc : (ctxOf l).RootFresh (.free c)) {ψ : WFF σ (ctxOf l) 0}
    (p : Proof σ (ctxOf l) Δ ((OutLeg.nec : OutLeg (ctxOf l)).dia (WFF.ex T φ)))
    (hax : Proof σ (ctxOf l) Δ ((WFF.liftAx hF ht φ).closed _))
    (q : Proof σ ((ctxOf l).insert (.free c) T)
      (WFF.liftRead hF hl (.nec : OutLeg (ctxOf l)) hc φ :: Δ.map (WFF.weaken hc.root T))
      (ψ.weaken hc.root T)) :
    Proof σ (ctxOf l) Δ ψ := by
  refine Proof.ex_elim c T hc (φ := WFF.liftRead hF hl (.nec : OutLeg (ctxOf l)) hc φ) ?_ q
  rw [WFF.liftRead_keptBody hF hl ht φ hc, WFF.bindFree_openFree]
  exact Proof.lift_exF hF hV hN hT (VarType.keepable_of_liftable hl) ht φ p hax

/-- ⭐⭐**`keep_lift` along `□` is derivable with 4, 5 and weak B**, whatever `FourStrong` and
    `FourStrongW` say, T and strong B off: the rule's own shape. -/
def Proof.keep_lift_B (hB : ModalSys.B = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hN : ModalSys.shaped = false) (hT : ModalSys.T = false)
    (hl : T.liftable = true) (ht : T.tup = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} (φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) (c : ℕ)
    (hc : (ctxOf l).RootFresh (.free c)) {ψ : WFF σ (ctxOf l) 0}
    (p : Proof σ (ctxOf l) Δ ((OutLeg.nec : OutLeg (ctxOf l)).dia (WFF.ex T φ)))
    (q : Proof σ ((ctxOf l).insert (.free c) T)
      (WFF.liftRead hF hl (.nec : OutLeg (ctxOf l)) hc φ :: Δ.map (WFF.weaken hc.root T))
      (ψ.weaken hc.root T)) :
    Proof σ (ctxOf l) Δ ψ := by
  refine Proof.ex_elim c T hc (φ := WFF.liftRead hF hl (.nec : OutLeg (ctxOf l)) hc φ) ?_ q
  rw [WFF.liftRead_keptBody hF hl ht φ hc, WFF.bindFree_openFree]
  exact Proof.lift_exB hB hF hV hN hT (VarType.keepable_of_liftable hl) ht φ p

end Whole

/-! ## Along `◇_x` -/

section Pos

variable {σ : Signature} {Γ : Ctx} [Γ.Presented] {x : VarSymb} {X T : VarType}

omit [Γ.Presented] in
/-- Weakening a body read at a term weakens the term. -/
theorem WFF.mono_readAt [ModalSys.NoOpt]
    {Λ Ω Ω' : Ctx} [Λ.NoSlots] {P : VarType} {d : ℕ} (hle : Λ.Le Ω)
    (h : Ω.Le Ω') (hs : Ω.SlotsFrom d) (hs' : Ω'.SlotsFrom d) {a : Ann P} (u : Term σ Ω P a)
    (B : WFF σ (Λ.insert (.bnd 0) P) 1) :
    WFF.mono h (WFF.readAt hle hs u B) = WFF.readAt (hle.trans h) hs' (Term.mono h u) B := by
  have hO : Subst.Ok Ω (Subst.idRen (σ := σ) Ω') := Subst.ok_idRen.restrict h
  have hC : Subst.Coh id Ω (Subst.idRen (σ := σ) Ω') := Subst.coh_idRen.restrict h
  have hid : ∀ v U, Ω.ref v = some U → (Subst.idRen (σ := σ) Ω').at v = .ren v :=
    fun v _ _ => Subst.at_idRen v
  refine (WFF.subst_ren h (Subst.idRen Ω') hO hC hs hs' hid _).symm.trans
    ((WFF.subst_readAt hle (hle.trans h) hs hs' u B _ hO hC
      (fun v U hv => hid v U (hle.ref hv))).trans
      (WFF.readAt_congr _ _ (Term.subst_ren h _ _ _ hid u) B))

/-- A body along `◇_x` is its abstraction, read at the content and the slot. -/
theorem WFF.body_readAt [ModalSys.NoOpt] (hx : Γ.ref x = some (.VTypeDia X))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF.readAt (Λ := Γ.boxIn) ((Ctx.le_boxIn_diaIn Γ x).trans
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T))
      ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T)
      (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T)
          (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)))
        (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) T)))
      (WFF.bodyAbsA x hx φ) = φ :=
  (WFF.viewBody_readAt hx).symm.trans (WFF.viewBody_bodyAbsA x hx φ)

/-- ⭐**`loopHatX` is `liftS` read at `x`'s content and the slot kept.** -/
theorem WFF.loopHatX_eq [ModalSys.NoOpt] (hF : ModalSys.Four = true) (ht : T.tup = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF.loopHatX hF ht x φ =
      WFF.readAt (Λ := Γ.boxIn.boxIn)
        ((Ctx.le_boxIn_diaIn Γ.boxIn (.step x .keep)).trans ((Ctx.le_boxIn_body Γ x T).diaIn _))
        (((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T).diaIn _)
        (Term.pair (Term.mono ((Ctx.le_boxIn_body Γ x T).diaIn _) (Term.bdK hF hx))
          (Term.keptSlotX hF ht Γ x))
        (WFF.liftS hF hx φ) := by
  have hs₀ := (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T
  have hs₁ := (Ctx.NoSlots.slots (Γ := Γ.boxIn.diaIn (.step x .keep))).insert T
  have D := Ctx.shifts_loopX hF Γ x T
  have hfr := (Ctx.NoSlots.slots (Γ := Γ.boxIn.diaIn (.step x .keep))).rootFresh (le_refl 0)
  have hle := (Ctx.le_boxIn_body Γ x T).diaIn (.step x .keep)
  have hO : Subst.Ok ((Γ.boxIn.diaIn (.step x .keep)).insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keptSlotX hF ht Γ x))) := Subst.ok_single hle rfl
  have hC : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.keptSlotX (σ := σ) hF ht Γ x)))
      ((Γ.boxIn.diaIn (.step x .keep)).insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keptSlotX hF ht Γ x))) :=
    Subst.coh_single hfr hle rfl
  have hid : ∀ v U, (Γ.boxIn.diaIn (.step x .keep)).ref v = some U →
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keptSlotX hF ht Γ x))).at v = .ren v :=
    fun _ _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hfr hv)
  have e₂ := (congrArg (WFF.shift D hs₀) (WFF.body_readAt hx φ).symm).trans
    (WFF.shift_readAt (Ctx.shifts_boxIn_boxIn hF Γ) D _
      ((Ctx.le_boxIn_diaIn Γ.boxIn (.step x .keep)).trans (Ctx.le_insert hfr.root T)) hs₀ hs₁ _ _)
  unfold WFF.loopHatX
  refine (congrArg (WFF.subst _ _ _ _ hs₁ _) e₂).trans
    ((WFF.subst_readAt _ _ _ _ _ _ _ hO hC fun v W hv =>
      hid v W ((Ctx.le_boxIn_diaIn Γ.boxIn (.step x .keep)).ref hv)).trans
      (WFF.readAt_congr _ _ (sig_pair ?_ ?_) _))
  · change (⟨_, Term.subst _ _ hO hC (Term.shift D (Term.mono _ _))⟩ : Σ c, Term σ _ X c) = _
    rw [Term.shift_mono (Ctx.shifts_diaIn_keep hF Γ x) D _ (Ctx.le_insert hfr.root T),
      Term.subst_mono]
    exact Term.subst_ren _ _ _ _ hid _
  · refine (Term.sig_subst _ hO hC (Term.shift_eta D _ T _)).trans ?_
    exact Term.subst_eta_tm _ hO hC T (.root (.bnd 0)) _ _ (Subst.at_single_root _ _)

/-- ⭐**`liftPos`, in `x`'s view, is `◇_{x.keep}` of the hat.** -/
theorem WFF.mono_liftPos [ModalSys.NoOpt]
    (hF : ModalSys.Four = true) (hk : T.keepable = true) (ht : T.tup = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (hx' : ∃ X', Γ.ref x = some (.VTypeDia X'))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF.mono ((Ctx.le_boxIn_diaIn Γ x).insert (.bnd 0) T) (WFF.liftPos hF hk hx φ) =
      .dia (.step x .keep) (Ctx.exists_keep_body hF hx' T) (WFF.loopHatX hF ht x φ) := by
  unfold WFF.liftPos
  refine congrArg (WFF.dia _ _) ?_
  rw [WFF.loopHatX_eq hF ht hx φ]
  refine (WFF.mono_readAt _ _ _ _ _ _).trans (WFF.readAt_congr _ _ (sig_pair ?_ ?_) _)
  · exact congrArg (Sigma.mk _) (Term.mono_mono _ _ _)
  · cases T with
    | VTypeBox A =>
        exact congrArg (Sigma.mk _) ((Term.mono_mono _ _ _).trans
          ((Term.mono_eta _ _ _ _).trans (Term.mono_eta _ _ _ _).symm))
    | VTypeDia A =>
        exact congrArg (Sigma.mk _) ((Term.mono_mono _ _ _).trans
          ((Term.mono_eta _ _ _ _).trans (Term.mono_eta _ _ _ _).symm))
    | Var => cases hk
    | VTypeOne => cases hk
    | VTypeProd A B => cases hk

/-- The rule's body along `◇_x`, at `¬φ`. -/
abbrev WFF.reflX (hF : ModalSys.Four = true) (ht : T.tup = true)
    (hx' : ∃ X', Γ.ref x = some (.VTypeDia X')) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF σ (Γ.diaIn x) 0 :=
  .all T (.imp (WFF.boxx (.step x .keep) (Ctx.exists_keep_body hF hx' T)
    (WFF.loopHatX hF ht x φ.neg)) φ.neg)

/-- Double negation, removed. -/
def Proof.neg_neg_elim {Ω : Ctx} (χ : WFF σ Ω 0) : Proof σ Ω [χ.neg.neg] χ :=
  Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
    (Proof.lookup List.mem_cons_self))

/-- ⭐**At a world of `x`'s extent, the body at `c` is `liftPos` at `c`**: `Proof.far_pos`, with the
    rule's `◇_x` row for `Proof.here_intro`. -/
def Proof.far_posU [ModalSys.NoOpt]
    (hF : ModalSys.Four = true) (hk : T.keepable = true) (ht : T.tup = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (hx' : ∃ X', Γ.ref x = some (.VTypeDia X'))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ}
    (hc : (Γ.diaIn x).RootFresh (.free c)) :
    Proof σ (posK Γ x T c)
      [WFF.openFree c hc Ctx.NoSlots.slots φ, WFF.weaken hc.root T (WFF.reflX hF ht hx' φ)]
      (WFF.instantiate Ctx.NoSlots.slots
        (Term.eta (.root (.free c)) T (Ctx.ref_insert_root (Γ.diaIn x) (.free c) T))
        (WFF.mono (((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).insert (.bnd 0) T)
          (WFF.liftPos hF hk hx φ))) := by
  have hL := Ctx.le_insert hc.root T
  have hw := Ctx.ref_insert_root (Γ.diaIn x) (.free c) T
  have e₁ : WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) T hw)
      (WFF.mono (hL.insert (.bnd 0) T) (WFF.boxx (.step x .keep)
        (Ctx.exists_keep_body hF hx' T) (WFF.loopHatX hF ht x φ.neg))) =
      (WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) T hw)
        (WFF.mono (((Ctx.le_boxIn_diaIn Γ x).trans hL).insert (.bnd 0) T)
          (WFF.liftPos hF hk hx φ.neg.neg))).neg := by
    have e := congrArg (fun z => (WFF.instantiate Ctx.NoSlots.slots
      (Term.eta (.root (.free c)) T hw) (WFF.mono (hL.insert (.bnd 0) T) z)).neg)
      (WFF.mono_liftPos hF hk ht hx hx' φ.neg.neg)
    refine e.symm.trans (congrArg (fun z => (WFF.instantiate Ctx.NoSlots.slots
      (Term.eta (.root (.free c)) T hw) z).neg) (WFF.mono_mono _ _ _))
  have e₂ := WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ.neg
  have hp : Proof σ (posK Γ x T c)
      [WFF.openFree c hc Ctx.NoSlots.slots φ, WFF.weaken hc.root T (WFF.reflX hF ht hx' φ)]
      (WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) T hw)
        (WFF.mono (((Ctx.le_boxIn_diaIn Γ x).trans hL).insert (.bnd 0) T)
          (WFF.liftPos hF hk hx φ.neg.neg))) := by
    refine Proof.byContra (Proof.imp_elim (Proof.imp_elim (Proof.conv (congrArg₂ WFF.imp e₁ e₂)
      (Proof.all_elim T (Term.eta (.root (.free c)) T hw) (φ := WFF.mono (hL.insert (.bnd 0) T)
        (.imp (WFF.boxx (.step x .keep) (Ctx.exists_keep_body hF hx' T)
          (WFF.loopHatX hF ht x φ.neg)) φ.neg))
        (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
      (Proof.lookup List.mem_cons_self))
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
  rw [WFF.read_liftPos hF hk hx φ ((Ctx.le_boxIn_diaIn Γ x).trans hL)]
  rw [WFF.read_liftPos hF hk hx φ.neg.neg ((Ctx.le_boxIn_diaIn Γ x).trans hL)] at hp
  exact Proof.leg_dia (.pos (.step x .keep) _) (Proof.neg_neg_elim _) hp

/-- ⭐In `x`'s view, the body's `∃` gives `liftPos`'s, a formula of the `□` view. -/
def Proof.pos_viewU [ModalSys.NoOpt]
    (hF : ModalSys.Four = true) (hk : T.keepable = true) (ht : T.tup = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (hx' : ∃ X', Γ.ref x = some (.VTypeDia X'))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ}
    (hc : (Γ.diaIn x).RootFresh (.free c)) :
    Proof σ (Γ.diaIn x) [WFF.ex T φ, WFF.reflX hF ht hx' φ]
      (WFF.mono (Ctx.le_boxIn_diaIn Γ x) (WFF.ex T (WFF.liftPos hF hk hx φ))) := by
  have e : WFF.weaken hc.root T (WFF.mono (Ctx.le_boxIn_diaIn Γ x)
      (WFF.ex T (WFF.liftPos hF hk hx φ))) =
      WFF.ex T (WFF.mono (((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).insert
        (.bnd 0) T) (WFF.liftPos hF hk hx φ)) := by
    unfold WFF.weaken
    rw [WFF.mono_mono]
    rfl
  refine Proof.ex_elim c T hc (φ := WFF.openFree c hc Ctx.NoSlots.slots φ)
    (Proof.conv (congrArg (WFF.ex T)
      (WFF.bindFree_openFree c hc (Ctx.NoSlots.slots (Γ := Γ.diaIn x)) φ).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  rw [e]
  refine Proof.ex_intro T (Term.eta (.root (.free c)) T
    (Ctx.ref_insert_root (Γ.diaIn x) (.free c) T)) ?_
  refine Proof.ofSubset (fun y hy => ?_) (Proof.far_posU hF hk ht hx hx' φ hc)
  rcases List.mem_cons.mp hy with rfl | hy
  · exact List.mem_cons_self
  · rw [List.mem_singleton.mp hy]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- ⭐The plain possibility `liftPos` needs, from `◇_x`: the rule's `◇_x` row in `here_keep`'s
    place. -/
def Proof.pos_necU [ModalSys.NoOpt] (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hN : ModalSys.shaped = false) (hk : T.keepable = true) (ht : T.tup = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (hx' : ∃ X', Γ.ref x = some (.VTypeDia X'))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ} (hc : Γ.RootFresh (.free c))
    {Δ : List (WFF σ Γ 0)} (p : Proof σ Γ Δ (.dia x hx' (WFF.ex T φ))) :
    Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.ex T (WFF.liftPos hF hk hx φ))) := by
  refine Proof.dia_forget hx' _ ?_
  have h₁ : Proof σ Γ [.dia x hx' (WFF.ex T φ), WFF.boxx x hx' (WFF.reflX hF ht hx' φ)]
      (.dia x hx' (WFF.mono (Ctx.le_boxIn_diaIn Γ x) (WFF.ex T (WFF.liftPos hF hk hx φ)))) :=
    Proof.castHyps (by simp) (Proof.K_dia (Δ₁ := []) (Δ₂ := [WFF.reflX hF ht hx' φ])
      (ψ := WFF.ex T φ) x hx'
      (Proof.castHyps (by simp) (Proof.pos_viewU hF hk ht hx hx' φ (hc.diaIn x))))
  have h₂ : Proof σ Γ Δ (WFF.boxx x hx' (WFF.reflX hF ht hx' φ)) :=
    Proof.five_refl hF hV hN (.pos x hx') ht φ.neg
  have h₃ := Proof.imp_intro (Proof.imp_intro h₁)
  exact Proof.imp_elim (Proof.imp_elim (Proof.ofSubset (fun _ hz => by cases hz) h₃) h₂) p

end Pos

section PosLift

variable {σ : Signature} {l : List VarType} {x : VarSymb} {X T : VarType}

/-- ⭐⭐**`keep_lift` along `◇_x` is derivable with 4, 5 and weak B**: `liftPos` carries the body
    through the lift along `□`, and `four_dia` brings it back into `x`'s extent. -/
def Proof.keep_lift_posB [ModalSys.NoOpt] (hB : ModalSys.B = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hN : ModalSys.shaped = false) (hT : ModalSys.T = false)
    (hl : T.liftable = true) (hx : (ctxOf l).ref x = some (.VTypeDia X))
    (hx' : ∃ X', (ctxOf l).ref x = some (.VTypeDia X')) {Δ : List (WFF σ (ctxOf l) 0)}
    (φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) T) 1) (c : ℕ)
    (hc : (ctxOf l).RootFresh (.free c)) {ψ : WFF σ (ctxOf l) 0}
    (p : Proof σ (ctxOf l) Δ (.dia x hx' (WFF.ex T φ)))
    (q : Proof σ ((ctxOf l).insert (.free c) T)
      (WFF.liftRead hF hl (.pos x hx') hc φ :: Δ.map (WFF.weaken hc.root T))
      (ψ.weaken hc.root T)) :
    Proof σ (ctxOf l) Δ ψ := by
  have hk := VarType.keepable_of_liftable hl
  have ht := VarType.tup_of_keepable hk
  have h := Ctx.le_insert hc.root T
  have hw' : ((ctxOf l).insert (.free c) T).boxIn.ref (.step (.root (.free c)) .keep) = some T :=
    Ctx.ref_keep_of' hF (Ctx.ref_insert_root (ctxOf l) (.free c) T) hk
  have hw := (Ctx.le_boxIn_diaIn ((ctxOf l).insert (.free c) T) x).ref hw'
  have hx₁ : ∃ X', ((ctxOf l).insert (.free c) T).ref x = some (.VTypeDia X') :=
    hx'.imp fun _ hY => h.ref hY
  have e := WFF.read_liftPos hF hk hx φ h.boxIn (.step (.root (.free c)) .keep) hw'
  rw [← WFF.shift_read_body hF hk hx φ hc hw hw'] at e
  have d : Proof σ ((ctxOf l).insert (.free c) T)
      [WFF.liftRead hF hl (.nec : OutLeg (ctxOf l)) hc (WFF.liftPos hF hk hx φ)]
      (WFF.liftRead hF hl (.pos x hx') hc φ) :=
    Proof.four_dia_home hF hx₁ _ (Proof.conv (congrArg (fun z => (WFF.box z.neg).neg) e)
      (Proof.lookup List.mem_cons_self))
  refine Proof.keep_lift_B hB hF hV hN hT hl ht (WFF.liftPos hF hk hx φ) c hc
    (Proof.pos_necU hF hV hN hk ht hx hx' φ hc p) ?_
  exact Proof.imp_elim (Proof.ofSubset (fun _ hz => List.mem_cons_of_mem _ hz) (Proof.imp_intro q))
    (Proof.ofSubset (fun z hz => by
      rw [List.mem_singleton.mp hz]
      exact List.mem_cons_self) d)

/-- ⭐⭐**`keep_lift` along `◇_x`, given `liftAx` at `liftPos`** (4 and 5, T and strong B off):
    `liftPos` carries the body through the lift along `□`, and `four_dia` brings it back. -/
def Proof.keep_lift_posF [ModalSys.NoOpt] (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hN : ModalSys.shaped = false) (hT : ModalSys.T = false)
    (hl : T.liftable = true) (hx : (ctxOf l).ref x = some (.VTypeDia X))
    (hx' : ∃ X', (ctxOf l).ref x = some (.VTypeDia X')) {Δ : List (WFF σ (ctxOf l) 0)}
    (φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) T) 1) (c : ℕ)
    (hc : (ctxOf l).RootFresh (.free c)) {ψ : WFF σ (ctxOf l) 0}
    (p : Proof σ (ctxOf l) Δ (.dia x hx' (WFF.ex T φ)))
    (hax : Proof σ (ctxOf l) Δ ((WFF.liftAx hF
      (VarType.tup_of_keepable (VarType.keepable_of_liftable hl))
      (WFF.liftPos hF (VarType.keepable_of_liftable hl) hx φ)).closed _))
    (q : Proof σ ((ctxOf l).insert (.free c) T)
      (WFF.liftRead hF hl (.pos x hx') hc φ :: Δ.map (WFF.weaken hc.root T))
      (ψ.weaken hc.root T)) :
    Proof σ (ctxOf l) Δ ψ := by
  have hk := VarType.keepable_of_liftable hl
  have ht := VarType.tup_of_keepable hk
  have h := Ctx.le_insert hc.root T
  have hw' : ((ctxOf l).insert (.free c) T).boxIn.ref (.step (.root (.free c)) .keep) = some T :=
    Ctx.ref_keep_of' hF (Ctx.ref_insert_root (ctxOf l) (.free c) T) hk
  have hw := (Ctx.le_boxIn_diaIn ((ctxOf l).insert (.free c) T) x).ref hw'
  have hx₁ : ∃ X', ((ctxOf l).insert (.free c) T).ref x = some (.VTypeDia X') :=
    hx'.imp fun _ hY => h.ref hY
  have e := WFF.read_liftPos hF hk hx φ h.boxIn (.step (.root (.free c)) .keep) hw'
  rw [← WFF.shift_read_body hF hk hx φ hc hw hw'] at e
  have d : Proof σ ((ctxOf l).insert (.free c) T)
      [WFF.liftRead hF hl (.nec : OutLeg (ctxOf l)) hc (WFF.liftPos hF hk hx φ)]
      (WFF.liftRead hF hl (.pos x hx') hc φ) :=
    Proof.four_dia_home hF hx₁ _ (Proof.conv (congrArg (fun z => (WFF.box z.neg).neg) e)
      (Proof.lookup List.mem_cons_self))
  refine Proof.keep_lift_F hF hV hN hT hl ht (WFF.liftPos hF hk hx φ) c hc
    (Proof.pos_necU hF hV hN hk ht hx hx' φ hc p) hax ?_
  exact Proof.imp_elim (Proof.ofSubset (fun _ hz => List.mem_cons_of_mem _ hz) (Proof.imp_intro q))
    (Proof.ofSubset (fun z hz => by
      rw [List.mem_singleton.mp hz]
      exact List.mem_cons_self) d)

end PosLift

end V12M
