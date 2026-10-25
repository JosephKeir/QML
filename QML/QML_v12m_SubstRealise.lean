import QML.QML_v12m_RealiseKeep
import QML.QML_v12m_ProofSubst
import QML.QML_v12m_RetMono

/-!
# QML v12m — substituting into a realisation

A realisation (`WFF.realiseAtA`) abstracts the witness's content and reads the hole back at the
datum's content.  Where a substitution **renames the witness**, substituting into the realisation is
realising the image:

* `WFF.diaAbsA_viewReadAtA`: reading a hole formula back at the content and abstracting again gives
  it back (the round trip `WFF.viewReadAtA_diaAbsA` the other way);
* ⭐`WFF.subst_diaAbsA`: so abstraction commutes with the substitution — every view formula is its
  abstraction read back, and substituting into a reading reads the substituted hole formula
  (`WFF.subst_viewReadTm`);
* ⭐`WFF.subst_realiseAtA`: hence, with `WFF.subst_hereRead`, substitution commutes with
  realisation.

The growing tree's canonical model needs this along an edge made for a witness: the child's reading
of a formula of the witness's view is the realisation, at the child's content, of the formula
translated with the witness kept.
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-- ⭐Reading a hole formula back at the content, then abstracting, gives it back. -/
theorem WFF.diaAbsA_viewReadAtA {Γ : Ctx} [hp : Γ.Presented] (x : VarSymb) {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A)) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.diaAbsA x hxA (WFF.viewReadAtA x hxA ψ) = ψ := by
  have h₀ : Γ.boxIn (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root
  unfold WFF.diaAbsA WFF.viewReadAtA WFF.renameRoot
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ ψ).trans
    (WFF.subst_id Subst.ok_idS Subst.coh_idS _ ψ)
  refine Subst.sim_of ?_
  intro v U hlp hv
  rw [Subst.comp_apply]
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.single_root, SubE.comp_ren,
      Subst.at_nonproj _ (rfl : (VarSymb.step x .dia).lastProj = false)]
    change SubE.Sim U (SubE.ren (.root (.bnd 0)))
      (if x = x then SubE.ren (.root (.bnd 0)) else .hide)
    rw [if_pos rfl]
    exact .refl _
  · have hv' : Γ.boxIn v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [Subst.single_ne _ hvr, SubE.comp_ren, Subst.at_nonproj _ hlp]
    match v, hv' with
    | .step u .box, _ => exact .refl _
    | .step u .keep, _ => exact .refl _
    | .root _, hv' => cases hv'
    | .step _ .fst, hv' => cases hv'
    | .step _ .snd, hv' => cases hv'
    | .step _ .dia, hv' => cases hv'
    | .step _ .here, hv' => cases hv'

/-- ⭐**Abstraction commutes with a substitution renaming the witness**: a view formula is its
    abstraction read back at the content (`WFF.viewReadAtA_diaAbsA`), the substitution reads the
    substituted hole formula at the image's content (`WFF.subst_viewReadTm`, the content renamed),
    and abstracting that reading gives the hole formula back (`WFF.diaAbsA_viewReadAtA`). -/
theorem WFF.subst_diaAbsA {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.Presented] [Δ.Presented]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {x : VarSymb} {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A)) (hxA' : Δ.ref (ι x) = some (.VTypeDia A))
    (hren : θ.at x = .ren (ι x)) (χ : WFF σ (Γ.diaIn x) 0) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        (θ.box.under 0 0 A (Ctx.NoSlots.slots (Γ := Δ).boxIn.root))
        (Subst.ok_under (Subst.ok_box hθ) A _)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc)
          (Ctx.NoSlots.slots (Γ := Γ)).boxIn A _)
        ((Ctx.NoSlots.slots (Γ := Γ)).boxIn.insert A) ((Ctx.NoSlots.slots (Γ := Δ)).boxIn.insert A)
        (WFF.diaAbsA x hxA χ) =
      WFF.diaAbsA (ι x) hxA' (WFF.subst ι (θ.dia x (ι x))
        (Subst.ok_dia hθ ⟨A, hxA⟩ (by rw [hren]; rfl)) (Subst.coh_dia hθ hc ⟨A, hxA⟩)
        Ctx.NoSlots.slots Ctx.NoSlots.slots χ) := by
  have hdia : (θ.dia x (ι x)).at (.step x .dia) = .ren (.step (ι x) .dia) := by
    rw [Subst.at_nonproj _ (rfl : (VarSymb.step x .dia).lastProj = false)]
    change (if x = x then (θ.at x).diaBody (ι x) else .hide) = _
    rw [if_pos rfl, hren]
    rfl
  have hη := Term.subst_eta_renAt (θ.dia x (ι x)) (Subst.ok_dia hθ ⟨A, hxA⟩ (by rw [hren]; rfl))
    (Subst.coh_dia hθ hc ⟨A, hxA⟩) A (.step x .dia) (.step (ι x) .dia) (Ctx.ref_diaIn_of hxA)
    (Ctx.ref_diaIn_of hxA') hdia
  conv_rhs => rw [← WFF.viewReadAtA_diaAbsA x hxA χ]
  rw [show WFF.viewReadAtA x hxA (WFF.diaAbsA x hxA χ) =
      WFF.viewReadTm (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA)) (WFF.diaAbsA x hxA χ) from
    (WFF.viewReadTm_eta hxA _).symm]
  rw [WFF.subst_viewReadTm θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots (ι x)]
  rw [show WFF.viewReadTm (Term.subst ι (θ.dia x (ι x)) _ _
        (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hxA))) _ =
      WFF.viewReadTm (Term.eta (.step (ι x) .dia) A (Ctx.ref_diaIn_of hxA')) _ from
    WFF.instantiate_congr_sig _ hη _, WFF.viewReadTm_eta hxA']
  exact (WFF.diaAbsA_viewReadAtA (ι x) hxA' _).symm

/-- ⭐**Substituting into a realisation at a witness the substitution renames is realising the
    image** at the substituted content, of the formula substituted in the witness's view. -/
theorem WFF.subst_realiseAtA {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.Presented] [Δ.Presented]
    (hT : ModalSys.T = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    {x : VarSymb} {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A))
    (hxA' : Δ.ref (ι x) = some (.VTypeDia A)) (hren : θ.at x = .ren (ι x)) {a₀ : Ann A}
    (t₀ : Term σ Γ A a₀) (χ : WFF σ (Γ.diaIn x) 0) :
    WFF.subst ι θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots (WFF.realiseAtA hT x hxA t₀ χ) =
      WFF.realiseAtA hT (ι x) hxA' (Term.subst ι θ hθ hc t₀)
        (WFF.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ ⟨A, hxA⟩ (by rw [hren]; rfl))
          (Subst.coh_dia hθ hc ⟨A, hxA⟩) Ctx.NoSlots.slots Ctx.NoSlots.slots χ) := by
  unfold WFF.realiseAtA
  rw [WFF.subst_hereRead hT θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots t₀ (WFF.diaAbsA x hxA χ),
    WFF.subst_diaAbsA θ hθ hc hxA hxA' hren χ]

/-- Weakening commutes with realisation. -/
theorem WFF.mono_realiseAtA {Γ Γ' : Ctx} [Γ.Presented] [Γ'.Presented] (hT : ModalSys.T = true)
    (h : Γ.Le Γ') {x : VarSymb} {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A))
    (hxA' : Γ'.ref x = some (.VTypeDia A)) {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    (χ : WFF σ (Γ.diaIn x) 0) :
    WFF.mono h (WFF.realiseAtA hT x hxA t₀ χ) =
      WFF.realiseAtA hT x hxA' (Term.mono h t₀) (WFF.mono (h.diaIn x) χ) := by
  unfold WFF.realiseAtA
  rw [WFF.mono_hereRead, WFF.mono_diaAbsA h hxA hxA']

end V12M
