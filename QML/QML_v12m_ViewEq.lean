import QML.QML_v12m_ViewRen
import QML.QML_v12m_ProofSubst
import QML.QML_v12m_EqDia

/-!
# QML v12m — transferring a `□_x` fact along `x ≐ y`

What the canonical model needs of the `◇`-types' equality (§2d) is that a `□_x` fact becomes the
corresponding `□_y` fact when the theory identifies the two witnesses.  This is Leibniz
(`Proof.diaEq_elim`) with the hole formula `□_□ (φ read in the slot's view)`:

* ⭐`WFF.reViewSlot`: the body of that hole formula — `φ`, written in the `x`-view, read in the view
  of the slot, one depth up.  A single substitution does both, since `WFF.subst` may change the
  depth.
* ⭐`WFF.instantiate_reViewSlot`: filling the slot with `η z` gives `φ` read in the `z`-view.  The
  two substitutions collapse into one by `WFF.subst_comp`, and the composite agrees with the view
  renaming up to η — the content address goes to `.tm (η (z.dia))` one way and to `.ren (z.dia)` the
  other, which is exactly `SubE.Sim.eta_ren`.
-/

namespace V12M

variable [ModalSys]

variable {σ : Signature}

/-- The slot's own view, as a context. -/
abbrev Ctx.slotView (Γ : Ctx) (A : VarType) : Ctx :=
  (Γ.insert (.bnd 0) (.VTypeDia A)).diaIn (.root (.bnd 0))

/-- ⭐`φ`, written in the `x`-view, read in the view of the slot one depth up. -/
def WFF.reViewSlot {Γ : Ctx} [Γ.NoSlots] {A : VarType} {x : VarSymb}
    (hx : Γ.ref x = some (.VTypeDia A))
    (hclI : Ctx.ViewClean (Γ.insert (.bnd 0) (.VTypeDia A)) x) (φ : WFF σ (Γ.diaIn x) 0) :
    WFF σ (Γ.slotView A) 1 :=
  WFF.subst (VarSymb.reView x (.root (.bnd 0)))
    (Subst.viewRen σ (Γ.insert (.bnd 0) (.VTypeDia A)) x (.root (.bnd 0)))
    ((Subst.ok_viewRen ((Ctx.le_insert Ctx.NoSlots.slots.root _).ref hx)
      (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A))).restrict
      ((Ctx.le_insert Ctx.NoSlots.slots.root (.VTypeDia A)).diaIn x))
    ((Subst.coh_viewRen ((Ctx.le_insert Ctx.NoSlots.slots.root _).ref hx)
      (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)) hclI).restrict
      ((Ctx.le_insert Ctx.NoSlots.slots.root (.VTypeDia A)).diaIn x))
    (Ctx.NoSlots.slots.diaIn x) ((Ctx.NoSlots.slots.insert (.VTypeDia A)).diaIn _) φ

/-- Filling the slot with `η z`: the witness becomes `z` and the body is `φ` read in the `z`-view.
    Two substitutions collapse into one (`WFF.subst_comp`); the composite sends the content address
    to `.tm (η (z.dia))` where the view renaming sends it to `.ren (z.dia)`, and those agree up to η
    (`SubE.Sim.ren_eta`). -/
theorem WFF.instantiate_reViewSlot {Γ : Ctx} [Γ.NoSlots] {A : VarType} {x z : VarSymb}
    (hx : Γ.ref x = some (.VTypeDia A)) (hz : Γ.ref z = some (.VTypeDia A))
    (hcl : Ctx.ViewClean Γ x) (hclI : Ctx.ViewClean (Γ.insert (.bnd 0) (.VTypeDia A)) x)
    (φ : WFF σ (Γ.diaIn x) 0) :
    WFF.instantiate (d := 0) Ctx.NoSlots.slots (Term.eta z (.VTypeDia A) hz)
        (WFF.dia (.root (.bnd 0)) ⟨A, Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)⟩
          (WFF.reViewSlot hx hclI φ)) =
      WFF.dia z ⟨A, hz⟩ (WFF.reView hx hz hcl φ) := by
  have hslot : (Γ.insert (.bnd 0) (.VTypeDia A)).ref (.root (.bnd 0)) = some (.VTypeDia A) :=
    Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)
  have hidx : Subst.singleIdx (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (Term.eta z (.VTypeDia A) hz)) (.root (.bnd 0)) = z := rfl
  have hok : Subst.Ok (Γ.insert (.bnd 0) (.VTypeDia A))
      (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.eta z (.VTypeDia A) hz))) :=
    Subst.ok_single (Ctx.Le.refl Γ) rfl
  have hcoh : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.eta z (.VTypeDia A) hz)))
      (Γ.insert (.bnd 0) (.VTypeDia A))
      (Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.eta z (.VTypeDia A) hz))) :=
    Subst.coh_single (Ctx.NoSlots.slots.rootFresh (le_refl 0)) (Ctx.Le.refl Γ) rfl
  refine (WFF.subst_dia (y := z) (hxy := hidx) (hy := ⟨A, hz⟩)
      (hθy := Subst.ok_dia hok ⟨A, hslot⟩ hidx)
      (hcy := Subst.coh_dia hok hcoh ⟨A, hslot⟩)
      (hsy := Ctx.NoSlots.slots.diaIn z) _ _ _ _ _ _ _).trans ?_
  refine congrArg (fun ψ => WFF.dia z (⟨A, hz⟩ : ∃ X, Γ.ref z = some (.VTypeDia X)) ψ) ?_
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ φ
  refine Subst.sim_of ?_
  intro v T hlp hv
  match v with
  | .root _ => cases hv
  | .step _ .fst => exact absurd hlp (by simp [VarSymb.lastProj, Step.isProj])
  | .step _ .snd => exact absurd hlp (by simp [VarSymb.lastProj, Step.isProj])
  | .step _ .here => exact absurd hlp (by simp [VarSymb.lastProj, Step.isProj])
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · rw [hx] at hv
        cases hv
        subst hux
        simp only [Subst.comp, Subst.viewRen_dia]
        change SubE.Sim A (.ren (.step z .dia))
          (((Subst.single (.bnd 0) (SubE.tm (Term.eta z (.VTypeDia A) hz))).dia
            (.root (.bnd 0)) z).at (.step (.root (.bnd 0)) .dia))
        rw [Subst.at_nonproj _ (rfl : (VarSymb.step (.root (.bnd 0)) .dia).lastProj = false)]
        change SubE.Sim A (.ren (.step z .dia))
          ((SubE.tm (Term.eta z (.VTypeDia A) hz)).diaBody z)
        rw [show (SubE.tm (Term.eta (σ := σ) z (.VTypeDia A) hz)).diaBody z =
          SubE.tm (Term.mono (Ctx.Le.refl _)
            (Term.eta (.step z .dia) A (Ctx.ref_diaIn_of hz))) from dif_pos rfl, Term.mono_eta]
        exact SubE.Sim.ren_eta _ _
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ) hv
      have hrt : u.rt ≠ .bnd 0 := Ctx.NoSlots.ref_bnd0 hu
      rw [Subst.viewRen_of_ne_dia (fun _ h => by cases h)]
      change SubE.Sim T (.ren (.step u .box))
        (((Subst.single (.bnd 0) (SubE.tm (Term.eta z (.VTypeDia A) hz))).dia
          (.root (.bnd 0)) z).at (.step u .box))
      rw [Subst.at_nonproj _ (rfl : (VarSymb.step u .box).lastProj = false)]
      change SubE.Sim T (.ren (.step u .box))
        (((Subst.single (.bnd 0) (SubE.tm (Term.eta z (.VTypeDia A) hz))).at u).unbox.mono
          (Ctx.le_boxIn_diaIn Γ z))
      rw [Subst.single_at_ne hrt]
      change SubE.Sim T (.ren (.step u .box)) (SubE.ren u.inner)
      rw [VarSymb.inner_box hk]
      exact SubE.Sim.refl _
  | .step u .keep =>
      rw [Subst.viewRen_of_ne_dia (fun _ h => by cases h)]
      change SubE.Sim T (.ren (.step u .keep))
        (((Subst.single (.bnd 0) (SubE.tm (Term.eta z (.VTypeDia A) hz))).dia
          (.root (.bnd 0)) z).at (.step u .keep))
      rw [Subst.at_nonproj _ (rfl : (VarSymb.step u .keep).lastProj = false)]
      have hrt : u.rt ≠ .bnd 0 := Ctx.NoSlots.ref_bnd0 (Ctx.boxIn_keep (Γ := Γ) hv).2.1
      change SubE.Sim T (.ren (.step u .keep))
        (((Subst.single (.bnd 0) (SubE.tm (Term.eta z (.VTypeDia A) hz))).at u).keepE.mono
          (Ctx.le_boxIn_diaIn Γ z))
      rw [Subst.single_at_ne hrt]
      exact SubE.Sim.refl _

/-- ⭐Renaming a view onto itself leaves a formula alone. -/
theorem WFF.reView_self {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) (hcl : Ctx.ViewClean Γ x) (φ : WFF σ (Γ.diaIn x) 0) :
    WFF.reView hx hx hcl φ = φ :=
  (WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (fun _ _ hv => Subst.at_viewRen_self hv) φ).trans
    (WFF.mono_refl _ φ)

/-- ⭐**The transfer**: what is `□_x`-necessary is `□_y`-necessary of the renamed formula, once the
    theory identifies the two witnesses.  Leibniz for `≐`, with the hole formula `□_□ (φ read in the
    slot's view)`. -/
def Proof.boxx_reView {Γ : Ctx} [Γ.NoSlots] {A : VarType} {x z : VarSymb}
    (hx : Γ.ref x = some (.VTypeDia A)) (hz : Γ.ref z = some (.VTypeDia A))
    (hcl : Ctx.ViewClean Γ x) (hclI : Ctx.ViewClean (Γ.insert (.bnd 0) (.VTypeDia A)) x)
    (φ : WFF σ (Γ.diaIn x) 0) :
    Proof σ Γ [WFF.diaEq (Term.eta x (.VTypeDia A) hx) (Term.eta z (.VTypeDia A) hz),
        WFF.boxx x ⟨A, hx⟩ φ]
      (WFF.boxx z ⟨A, hz⟩ (WFF.reView hx hz hcl φ)) :=
  Proof.conv
    (by
      change (WFF.instantiate (d := 0) Ctx.NoSlots.slots (Term.eta z (.VTypeDia A) hz)
        (WFF.dia (.root (.bnd 0)) ⟨A, Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)⟩
          (WFF.reViewSlot hx hclI φ.neg))).neg = _
      rw [WFF.instantiate_reViewSlot hx hz hcl hclI φ.neg]
      rfl)
    (Proof.diaEq_elim
      (φ := WFF.boxx (.root (.bnd 0)) ⟨A, Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)⟩
        (WFF.reViewSlot hx hclI φ))
      (Term.eta x (.VTypeDia A) hx) (Term.eta z (.VTypeDia A) hz)
      (Proof.lookup List.mem_cons_self)
      (Proof.conv
        (by
          change _ = (WFF.instantiate (d := 0) Ctx.NoSlots.slots (Term.eta x (.VTypeDia A) hx)
            (WFF.dia (.root (.bnd 0)) ⟨A, Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)⟩
              (WFF.reViewSlot hx hclI φ.neg))).neg
          rw [WFF.instantiate_reViewSlot hx hx hcl hclI φ.neg, WFF.reView_self hx hcl φ.neg])
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))

end V12M
