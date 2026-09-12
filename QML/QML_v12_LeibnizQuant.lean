import QML.QML_v12_Leibniz

/-!
# QML v12 — Leibniz: the quantifier steps

Under a quantifier, a substitution `θ` becomes `θ.under d 0` (slot to slot).  A proof works with
an eigenvariable `u` instead: `θ.toFree d u` (slot to `u`).  The two agree through the proof
rules:

* `WFF.bindFree_toFree`: binding `u` back to the slot (`∀`-introduction) gives `θ.under`;
* `WFF.instantiate_toFree`: instantiating the weakened `θ.under`-body at the η-expansion of `u`
  (`∀`-elimination) gives `θ.toFree`.
-/

namespace V12

namespace Subst

variable {σ : Signature}

/-- Every address to itself. -/
def idRen (Δ : Ctx) : Subst σ Δ := fun v => .ren v

theorem at_idRen {Δ : Ctx} : ∀ v, (idRen (σ := σ) Δ).at v = .ren v
  | .root _ => rfl
  | .step v s => by
      change (if s.isProd then ((idRen (σ := σ) Δ).at v).proj s else SubE.ren (.step v s)) = _
      rw [at_idRen v]
      split_ifs <;> rfl

theorem ok_idRen {Δ : Ctx} : Ok Δ (idRen (σ := σ) Δ) := fun v T hlp hv => by
  change Δ.ref v = some T
  rw [Ctx.ref_nonprod Δ hlp]
  exact hv

theorem coh_idRen {Δ : Ctx} : Coh id Δ (idRen (σ := σ) Δ) := fun v _ _ p => by
  rw [at_idRen]
  rfl

end Subst

theorem SubE.comp_idRen {σ : Signature} {Δ : Ctx} :
    ∀ (e : SubE σ Δ), e.comp (Subst.idRen Δ) Subst.ok_idRen Subst.coh_idRen = e
  | .ren w => Subst.at_idRen w
  | .hide => rfl
  | .tm s =>
      (SubE.tm_eq_of_sig (Term.subst_ren (Ctx.Le.refl Δ) (Subst.idRen Δ) Subst.ok_idRen
        Subst.coh_idRen (fun v _ _ => Subst.at_idRen v) s)).trans
        (congrArg SubE.tm (Term.mono_refl _ s))

theorem Ctx.ref_rt_ne {Γ : Ctx} {r : Root} (hr : Γ.RootFresh r) {v : VarSymb} {T : VarType}
    (hv : Γ.ref v = some T) : v.rt ≠ r := fun he => by
  rw [Ctx.ref_none_of_rootFresh hr v he] at hv
  cases hv

/-- ⭐Binding the eigenvariable back to the slot undoes `toFree`. -/
theorem WFF.bindFree_toFree {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d : ℕ}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d)
    (hΔ : Δ.SlotsFrom 0) (u : ℕ) (hu : Δ.RootFresh (.free u)) (T : VarType)
    (ψ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) :
    WFF.bindFree u hu hΔ T (WFF.subst (VarSymb.slotToFree ι d u) (θ.toFree d u T hu.root)
        (Subst.ok_toFree hθ T hu.root) (Subst.coh_toFree hθ hc hΓ T hu.root) (hΓ.insert T)
        (hΔ.insertFree u T) ψ) =
      WFF.subst (VarSymb.shiftSlot ι d 0) (θ.under d 0 T hΔ.root) (Subst.ok_under hθ T hΔ.root)
        (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T) ψ := by
  have hle : Δ.Le (Δ.insert (.bnd 0) T) := Ctx.le_insert hΔ.root T
  have hw : (Δ.insert (.bnd 0) T).ref (.root (.bnd 0)) = some T := Ctx.ref_insert_root Δ _ T
  refine WFF.subst_comp _ (Subst.single (.free u) (.ren (.root (.bnd 0)))) _ _ _
    (Subst.ok_single (σ := σ) hle hw) (Subst.coh_single hu hle hw) _ _ _ _ _ ?_ ψ
  refine Subst.sim_of ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    rw [show θ.under d 0 T hΔ.root (.root (.bnd d)) = .ren (.root (.bnd 0)) from if_pos rfl]
    change SubE.Sim U _ ((θ.toFree d u T hu.root (.root (.bnd d))).comp _ _ _)
    rw [show θ.toFree d u T hu.root (.root (.bnd d)) = .ren (.root (.free u)) from if_pos rfl]
    change SubE.Sim U _ (Subst.single (.free u) (.ren (.root (.bnd 0))) (.root (.free u)))
    rw [show Subst.single (σ := σ) (Δ := Δ.insert (.bnd 0) T) (.free u)
      (.ren (.root (.bnd 0))) (.root (.free u)) = .ren (.root (.bnd 0)) from if_pos rfl]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show θ.under d 0 T hΔ.root v = (θ v).mono (Ctx.le_insert hΔ.root T) from if_neg hvr]
    change SubE.Sim U _ ((θ.toFree d u T hu.root v).comp _ _ _)
    rw [show θ.toFree d u T hu.root v = (θ v).mono (Ctx.le_insert hu.root T) from if_neg hvr,
      SubE.comp_mono (Subst.idRen Δ) Subst.ok_idRen Subst.coh_idRen (Ctx.le_insert hu.root T)
        hle _ _ _
        (fun w _ hw' => by
          rw [Subst.single_at_ne (Ctx.ref_rt_ne hu hw'), Subst.at_idRen]
          rfl)
        (hθ v U hlp hv'),
      SubE.comp_idRen]
    exact .refl _

/-- ⭐Instantiating the weakened `θ.under`-body at the η-expanded eigenvariable is `toFree`. -/
theorem WFF.instantiate_toFree {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d : ℕ}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d)
    (hΔ : Δ.SlotsFrom 0) (u : ℕ) (hu : Δ.RootFresh (.free u)) (T : VarType)
    (hs : (Δ.insert (.free u) T).SlotsFrom 0) (ψ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) :
    WFF.instantiate hs (Term.eta (.root (.free u)) T (Ctx.ref_insert_root Δ _ T))
        (WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T)
          (WFF.subst (VarSymb.shiftSlot ι d 0) (θ.under d 0 T hΔ.root)
            (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T)
            (hΔ.insert T) ψ)) =
      WFF.subst (VarSymb.slotToFree ι d u) (θ.toFree d u T hu.root)
        (Subst.ok_toFree hθ T hu.root) (Subst.coh_toFree hθ hc hΓ T hu.root) (hΓ.insert T)
        (hΔ.insertFree u T) ψ := by
  have hle : (Δ.insert (.bnd 0) T).Le ((Δ.insert (.free u) T).insert (.bnd 0) T) :=
    (Ctx.le_insert hu.root T).insert (.bnd 0) T
  refine (WFF.subst_mono hle _ _ _ (hΔ.insert T) (hs.insert T) hs _).trans ?_
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ψ
  refine Subst.sim_of ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [show θ.toFree d u T hu.root (.root (.bnd d)) = .ren (.root (.free u)) from if_pos rfl]
    change SubE.Sim T _ ((θ.under d 0 T hΔ.root (.root (.bnd d))).comp _ _ _)
    rw [show θ.under d 0 T hΔ.root (.root (.bnd d)) = .ren (.root (.bnd 0)) from if_pos rfl]
    change SubE.Sim T _ (Subst.single (.bnd 0)
      (.tm (Term.eta (σ := σ) (.root (.free u)) T (Ctx.ref_insert_root Δ _ T))) (.root (.bnd 0)))
    rw [show Subst.single (.bnd 0)
      (SubE.tm (Term.eta (σ := σ) (.root (.free u)) T (Ctx.ref_insert_root Δ _ T)))
      (.root (.bnd 0)) =
        SubE.tm (Term.eta (σ := σ) (.root (.free u)) T (Ctx.ref_insert_root Δ _ T))
      from if_pos rfl]
    exact .ren_eta _ _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show θ.toFree d u T hu.root v = (θ v).mono (Ctx.le_insert hu.root T) from if_neg hvr]
    change SubE.Sim U _ ((θ.under d 0 T hΔ.root v).comp _ _ _)
    rw [show θ.under d 0 T hΔ.root v = (θ v).mono (Ctx.le_insert hΔ.root T) from if_neg hvr,
      SubE.comp_mono (Subst.idRen Δ) Subst.ok_idRen Subst.coh_idRen (Ctx.le_insert hΔ.root T)
        (Ctx.le_insert hu.root T) _ _ _
        (fun w _ hw' => by
          rw [Subst.single_at_ne (Ctx.ref_rt_ne (hΔ.rootFresh le_rfl) hw'), Subst.at_idRen]
          rfl)
        (hθ v U hlp hv'),
      SubE.comp_idRen]
    exact .refl _

end V12
