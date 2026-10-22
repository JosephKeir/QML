import QML.QML_v12m_ShiftSubst

/-!
# QML v12m — substituting twice

`θ₁ : Γ → Δ₁` followed by `θ₂ : Δ₁ → Δ₂` is `θ₃ : Γ → Δ₂` whenever `θ₃` agrees up to η with the
composite entries `θ₁.comp θ₂` (an address goes to its `θ₂` entry, a term is substituted by `θ₂`).
`θ₃` carries its own annotation map, so the composite never needs one.

Under T, the `here` component of a composite term entry is handled by `Term.collapse_subst`: the
`□` view of a substitution corresponds, across the collapse, to the substitution itself
(`Subst.corr_box_self`).
-/

namespace V12M

variable [ModalSys]

/-! ## The `□` view collapses onto the substitution -/

theorem SubE.proj_here_eq {σ : Signature} {Δ : Ctx} (hT : ModalSys.T = true) :
    ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) →
      e.proj .here = e.unbox.collapse (Ctx.collapses_boxIn_self hT Δ)
  | .ren w, _, _ => by
      change SubE.ren (.step w .here) = SubE.ren (w.inner.collapse 0)
      rw [VarSymb.inner_collapse_zero]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t => exact SubE.proj_boxtm_here t hT

/-- Under T and 4, a kept entry collapsed onto the current level is the entry. -/
theorem SubE.keepE_collapse_self {σ : Signature} {Δ : Ctx} (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) :
    ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) →
      e.keepE.collapse (Ctx.collapses_boxIn_self hT Δ) = e
  | .ren _, _, _ => rfl
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          rw [SubE.keepE_tm _ hF]
          exact SubE.tm_eq_of_sig (sig_boxtm ((Term.collapse_shift_self (m := 0)
            (Ctx.shifts_boxIn_boxIn hF Δ) (Ctx.collapses_boxIn_self hT Δ).boxIn
            (Ctx.Le.refl _) t).trans (congrArg (Sigma.mk _) (Term.mono_refl _ t))))

/-- `SubE.keepE_collapse_self` at any keepable type. -/
theorem SubE.keepE_collapse_self' {σ : Signature} {Δ : Ctx} (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) :
    ∀ {e : SubE σ Δ} {T : VarType}, T.keepable = true → e.OkRef T →
      e.keepE.collapse (Ctx.collapses_boxIn_self hT Δ) = e
  | .ren _, _, _, _ => rfl
  | .hide, _, _, he => False.elim he
  | .tm (T := U) s, T, hk, he => by
      have hU : U = T := he
      subst hU
      cases U with
      | VTypeBox A => exact SubE.keepE_collapse_self hT hF (e := .tm s) rfl
      | VTypeDia A =>
          cases s with
          | diatm y hy t =>
              have hnS := VarType.noShaped_of_keepable_dia hk
              rw [SubE.keepE_dia _ _ _ hF hnS]
              exact SubE.tm_eq_of_sig (sig_diatm ((Term.collapse_shift_self (m := 0)
                (Ctx.shifts_diaIn_keep hF hnS Δ y)
                ((Ctx.collapses_boxIn_self hT Δ).diaIn (.step y .keep))
                (Ctx.Le.refl _) t).trans (congrArg (Sigma.mk _) (Term.mono_refl _ t))))
      | _ => cases hk

theorem Subst.corr_box_self {σ : Signature} {Γ Δ : Ctx} (hT : ModalSys.T = true)
    {θ : Subst σ Δ} (hθ : Subst.Ok Γ θ) :
    Subst.Corr Γ.boxIn (Ctx.collapses_boxIn_self hT Δ) θ.box θ := by
  refine Subst.corr_of (Subst.ok_box hθ) ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      change SubE.Sim T (θ.at (.step u .here)) ((θ.at u).unbox.collapse _)
      rw [show θ.at (.step u .here) = (θ.at u).proj .here from if_pos rfl,
        SubE.proj_here_eq hT (Subst.okRef_at hθ hu)]
      exact .refl _
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      change SubE.Sim T (θ.at u) ((θ.at u).keepE.collapse _)
      rw [SubE.keepE_collapse_self' hT hF hk (Subst.okRef_at hθ hu)]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

namespace SubE

variable {σ : Signature} {ι₂ : VarSymb → VarSymb} {Δ₁ Δ₂ : Ctx}

/-- Push an entry over `Δ₁` through `θ₂`. -/
def comp (θ₂ : Subst σ Δ₂) (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) :
    SubE σ Δ₁ → SubE σ Δ₂
  | .hide => .hide
  | .ren w => θ₂.at w
  | .tm s => .tm (Term.subst ι₂ θ₂ hθ₂ hc₂ s)

theorem toVar_tmSelf {Δ : Ctx} :
    ∀ (s : Term σ Δ .Var .var) (h : (SubE.tm s).OkRef .Var), (SubE.tm s).toVar h = s
  | .var _ _, _ => rfl
  | .func _, _ => rfl

variable (θ₂ : Subst σ Δ₂) (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂)

theorem okRef_comp : ∀ {e : SubE σ Δ₁} {T : VarType}, e.OkRef T → (e.comp θ₂ hθ₂ hc₂).OkRef T
  | .ren _, _, he => Subst.okRef_at hθ₂ he
  | .tm _, _, he => he
  | .hide, _, he => False.elim he

theorem toVar_comp : ∀ (e : SubE σ Δ₁) (he : e.OkRef .Var),
    Term.subst ι₂ θ₂ hθ₂ hc₂ (e.toVar he) = (e.comp θ₂ hθ₂ hc₂).toVar (okRef_comp θ₂ hθ₂ hc₂ he)
  | .ren _, _ => rfl
  | .tm (.var _ _), _ => (toVar_tmSelf _ _).symm
  | .tm (.func _), _ => (toVar_tmSelf _ _).symm
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _), h => nomatch h
  | .tm (.diatm _ _ _), h => nomatch h
  | .hide, h => False.elim h

theorem idxAlong_comp : ∀ {e : SubE σ Δ₁} {X : VarType}, e.OkRef (.VTypeDia X) →
    (e.comp θ₂ hθ₂ hc₂).idxAlong [] = ι₂ (e.idxAlong [])
  | .ren w, _, he => hc₂ w _ he []
  | .tm (.diatm _ _ _), _, _ => rfl
  | .tm (.var _ _), _, he => nomatch he
  | .tm (.func _), _, he => nomatch he
  | .tm .unit, _, he => nomatch he
  | .tm (.pair _ _), _, he => nomatch he
  | .tm (.boxtm _), _, he => nomatch he
  | .hide, _, he => False.elim he

theorem proj_comp : ∀ {e : SubE σ Δ₁} {U T : VarType} {s : Step}, e.OkRef U →
    s.isProj = true → U.step s = some T →
    (e.comp θ₂ hθ₂ hc₂).proj s = (e.proj s).comp θ₂ hθ₂ hc₂
  | .ren w, _, _, s, _, hs, _ => by
      change (θ₂.at w).proj s = θ₂.at (.step w s)
      change _ = (if s.isProj then (θ₂.at w).proj s else θ₂ (.step w s))
      rw [if_pos hs]
  | .hide, _, _, _, he, _, _ => False.elim he
  | .tm (T := U') s₀, U, T, s, he, hs, hst => by
      have hU : U' = U := he
      subst hU
      cases s with
      | fst =>
          cases s₀ <;> (try cases hst)
          rfl
      | snd =>
          cases s₀ <;> (try cases hst)
          rfl
      | box => cases hs
      | dia => cases hs
      | keep => cases hs
      | here =>
          cases s₀ with
          | boxtm t =>
              obtain ⟨hT, hAT⟩ := VarType.step_here hst
              subst hAT
              change (SubE.tm (Term.boxtm (Term.subst ι₂ θ₂.box (Subst.ok_box hθ₂)
                  (Subst.coh_box hθ₂ hc₂) t))).proj .here =
                ((SubE.tm (Term.boxtm t)).proj .here).comp θ₂ hθ₂ hc₂
              rw [proj_boxtm_here _ hT, proj_boxtm_here _ hT]
              exact tm_eq_of_sig (Term.collapse_subst (Ctx.collapses_boxIn_self hT Δ₁)
                (Ctx.collapses_boxIn_self hT Δ₂) θ₂.box (Subst.ok_box hθ₂)
                (Subst.coh_box hθ₂ hc₂) θ₂ hθ₂ hc₂ (Subst.corr_box_self hT hθ₂) t)
          | _ => cases hst

theorem unbox_comp (hk : ModalSys.keepOnly = false) : ∀ {e : SubE σ Δ₁} {A : VarType},
    e.OkRef (.VTypeBox A) →
    (e.comp θ₂ hθ₂ hc₂).unbox = e.unbox.comp θ₂.box (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂)
  | .ren w, _, _ => by
      change (θ₂.at w).unbox = θ₂.box.at w.inner
      rw [VarSymb.inner_box hk]
      rfl
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem keepE_comp (hF : ModalSys.Four = true) : ∀ {e : SubE σ Δ₁} {A : VarType},
    e.OkRef (.VTypeBox A) →
    (e.comp θ₂ hθ₂ hc₂).keepE = e.keepE.comp θ₂.box (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂)
  | .ren _, _, _ => rfl
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          change (SubE.tm (Term.boxtm (Term.subst ι₂ θ₂.box (Subst.ok_box hθ₂)
              (Subst.coh_box hθ₂ hc₂) t))).keepE =
            ((SubE.tm (Term.boxtm t)).keepE).comp θ₂.box (Subst.ok_box hθ₂)
              (Subst.coh_box hθ₂ hc₂)
          rw [keepE_tm _ hF, keepE_tm _ hF]
          exact tm_eq_of_sig (sig_boxtm (Term.shift_subst (Ctx.shifts_boxIn_boxIn hF Δ₁)
            (Ctx.shifts_boxIn_boxIn hF Δ₂) θ₂.box (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂)
            θ₂.box.box (Subst.ok_box (Subst.ok_box hθ₂))
            (Subst.coh_box (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂))
            (Subst.shiftCorr_box_box hF hθ₂) t))

/-- `keepE_comp` at any keepable type: the kept witness `y.keep` goes to `(ι₂ y).keep`
    (coherence at the `keep` step), and the shifted body is substituted by the `◇_{y.keep}` view
    of `θ₂.box` (`Subst.shiftCorr_dia_keep`). -/
theorem keepE_comp' (hF : ModalSys.Four = true) : ∀ {e : SubE σ Δ₁} {T : VarType},
    T.keepable = true → e.OkRef T →
    (e.comp θ₂ hθ₂ hc₂).keepE = e.keepE.comp θ₂.box (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂)
  | .ren _, _, _, _ => rfl
  | .hide, _, _, he => False.elim he
  | .tm (T := U) s, T, hk, he => by
      have hU : U = T := he
      subst hU
      cases U with
      | VTypeBox A => exact keepE_comp θ₂ hθ₂ hc₂ hF (e := .tm s) rfl
      | VTypeDia A =>
          cases s with
          | diatm y hy t =>
              have hnS := VarType.noShaped_of_keepable_dia hk
              obtain ⟨X, hX⟩ := hy
              have hw : (θ₂.at y).idxAlong [] = ι₂ y := hc₂ y _ hX []
              have hwk : (θ₂.box.at (.step y .keep)).idxAlong [] = .step (ι₂ y) .keep := by
                change ((θ₂.at y).keepE).idxAlong [] = _
                rw [SubE.idxAlong_keepE' hF [] (VarType.keepable_dia hnS) (Subst.okRef_at hθ₂ hX),
                  SubE.idxAlong_keep_dia (Subst.okRef_at hθ₂ hX), hw]
              have hk₂ : ι₂ (.step y .keep) = .step (ι₂ y) .keep := by
                have h := hc₂ y _ hX [.keep]
                rw [SubE.idxAlong_keep_dia (Subst.okRef_at hθ₂ hX), hw] at h
                exact h.symm
              obtain ⟨X₂, hy₂⟩ := SubE.ref_witness (Subst.okRef_at hθ₂ hX) hw
              have hyk : ∃ X', Δ₁.boxIn.ref (.step y .keep) = some (.VTypeDia X') :=
                ⟨X, Ctx.ref_keep_of' hF hX (VarType.keepable_dia hnS)⟩
              change (SubE.tm (Term.diatm (ι₂ y) _ (Term.subst ι₂ (θ₂.dia y (ι₂ y))
                  (Subst.ok_dia hθ₂ ⟨X, hX⟩ hw) (Subst.coh_dia hθ₂ hc₂ ⟨X, hX⟩) t))).keepE =
                ((SubE.tm (Term.diatm y ⟨X, hX⟩ t)).keepE).comp θ₂.box (Subst.ok_box hθ₂)
                  (Subst.coh_box hθ₂ hc₂)
              rw [keepE_dia _ _ _ hF hnS, keepE_dia _ _ _ hF hnS]
              refine SubE.tm_eq_of_sig (Eq.symm ((Term.subst_diatm_sig θ₂.box
                (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂) hyk _ hk₂ hwk
                (Subst.ok_dia (Subst.ok_box hθ₂) hyk hwk)
                (hk₂ ▸ Subst.coh_dia (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂) hyk)
                ⟨X₂, Ctx.ref_keep_of' hF hy₂ (VarType.keepable_dia hnS)⟩).trans (sig_diatm ?_)))
              exact (Term.shift_subst (Ctx.shifts_diaIn_keep hF hnS Δ₁ y)
                (Ctx.shifts_diaIn_keep hF hnS Δ₂ (ι₂ y)) (θ₂.dia y (ι₂ y))
                (Subst.ok_dia hθ₂ ⟨X, hX⟩ hw) (Subst.coh_dia hθ₂ hc₂ ⟨X, hX⟩) _ _ _
                (Subst.shiftCorr_dia_keep hF hnS hθ₂ ⟨X, hX⟩ hw) t).symm
      | _ => cases hk

theorem diaBody_comp {x₁ : VarSymb} (hx₁ : ∃ X, Δ₁.ref x₁ = some (.VTypeDia X))
    (hw : (θ₂.at x₁).idxAlong [] = ι₂ x₁) :
    ∀ {e : SubE σ Δ₁} {X : VarType}, e.OkRef (.VTypeDia X) → e.idxAlong [] = x₁ →
    (e.diaBody x₁).comp (θ₂.dia x₁ (ι₂ x₁)) (Subst.ok_dia hθ₂ hx₁ hw)
        (Subst.coh_dia hθ₂ hc₂ hx₁) =
      (e.comp θ₂ hθ₂ hc₂).diaBody (ι₂ x₁)
  | .ren w, _, _, hwx => by
      have hwx' : w = x₁ := hwx
      subst hwx'
      change (θ₂.dia w (ι₂ w)) (.step w .dia) = (θ₂.at w).diaBody (ι₂ w)
      change (if w = w then (θ₂.at w).diaBody (ι₂ w) else SubE.hide) = _
      rw [if_pos rfl]
  | .tm (.diatm y hy u), _, _, hyx => by
      have hyx' : y = x₁ := hyx
      subst hyx'
      rw [diaBody_diatm]
      change _ = SubE.diaBody (ι₂ y)
        (SubE.tm (Term.diatm (ι₂ y) _ (Term.subst ι₂ (θ₂.dia y (ι₂ y)) _ _ u)))
      exact (diaBody_diatm _ _ _).symm
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

/-- Weakening before `θ₂'` is weakening after `θ₂`, when `θ₂'` is `θ₂` weakened. -/
theorem comp_mono {Δ₁' Δ₂' : Ctx} (h : Δ₁.Le Δ₁') (h₂ : Δ₂.Le Δ₂') {ι₂' : VarSymb → VarSymb}
    (θ₂' : Subst σ Δ₂') (hθ₂' : Subst.Ok Δ₁' θ₂') (hc₂' : Subst.Coh ι₂' Δ₁' θ₂')
    (heq : ∀ w T, Δ₁.ref w = some T → θ₂'.at w = (θ₂.at w).mono h₂) :
    ∀ {e : SubE σ Δ₁} {T : VarType}, e.OkRef T →
      (e.mono h).comp θ₂' hθ₂' hc₂' = (e.comp θ₂ hθ₂ hc₂).mono h₂
  | .ren w, T, he => heq w T he
  | .hide, _, _ => rfl
  | .tm s, _, _ => by
      change SubE.tm (Term.subst ι₂' θ₂' hθ₂' hc₂' (Term.mono h s)) =
        SubE.tm (Term.mono h₂ (Term.subst ι₂ θ₂ hθ₂ hc₂ s))
      rw [Term.subst_mono, Term.mono_subst]
      exact tm_eq_of_sig (Term.subst_congr _ _ _ _ _ _
        (fun w T hw => by rw [heq w T hw, Subst.at_mono]; exact .refl _) s)

end SubE

namespace Subst

variable {σ : Signature} {ι₁ ι₂ ι₃ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx}

/-- The composite entries. -/
def comp (θ₁ : Subst σ Δ₁) (θ₂ : Subst σ Δ₂) (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂) :
    Subst σ Δ₂ :=
  fun v => (θ₁ v).comp θ₂ hθ₂ hc₂

theorem at_comp {θ₁ : Subst σ Δ₁} (hθ₁ : Ok Γ θ₁) (θ₂ : Subst σ Δ₂) (hθ₂ : Ok Δ₁ θ₂)
    (hc₂ : Coh ι₂ Δ₁ θ₂) :
    ∀ {v : VarSymb} {T : VarType}, Γ.ref v = some T →
      (θ₁.comp θ₂ hθ₂ hc₂).at v = (θ₁.at v).comp θ₂ hθ₂ hc₂ := by
  intro v
  induction v with
  | root r => intro T _; rfl
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            rw [ih hU]
            exact SubE.proj_comp θ₂ hθ₂ hc₂ (okRef_at hθ₁ hU) hs hv
      · rfl

theorem at_eq_mono_of {Δ Δ' : Ctx} {θ : Subst σ Δ} {θ' : Subst σ Δ'} (h : Δ'.Le Δ)
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T → θ v = (θ' v).mono h) :
    ∀ v T, Γ.ref v = some T → θ.at v = (θ'.at v).mono h := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [ih U hU, SubE.proj_mono]
      · exact hvis _ _ (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs) hv

theorem dia_eq_box_mono (θ₂ : Subst σ Δ₂) (x₁ y : VarSymb) :
    ∀ v T, Δ₁.boxIn.ref v = some T →
      (θ₂.dia x₁ y).at v = (θ₂.box.at v).mono (Ctx.le_boxIn_diaIn Δ₂ y) :=
  at_eq_mono_of _ fun v T _ hv => by
    match v with
    | .step u .box => rfl
    | .step u .keep => rfl
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .dia => cases hv
    | .step _ .here => cases hv

theorem under_eq_mono (θ₂ : Subst σ Δ₂) {d₁ d₂ : ℕ} (hΔ₁ : Δ₁.SlotsFrom d₁) (T : VarType)
    (h : Δ₂ (.root (.bnd d₂)) = none) :
    ∀ v U, Δ₁.ref v = some U →
      (θ₂.under d₁ d₂ T h).at v = (θ₂.at v).mono (Ctx.le_insert h T) :=
  at_eq_mono_of _ fun v U _ hv => by
    have hvr : v ≠ .root (.bnd d₁) := fun he => by
      subst he
      rw [hΔ₁.root] at hv
      cases hv
    exact if_neg hvr

theorem idx_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁) (hc₁ : Coh ι₁ Γ θ₁)
    (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂) (hc₃ : Coh ι₃ Γ θ₃)
    (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
    ι₃ x = ι₂ (ι₁ x) := by
  obtain ⟨X, hX⟩ := hx
  have h₃ : (θ₃.at x).idxAlong [] = ι₃ x := hc₃ x _ hX []
  have h₁ : (θ₁.at x).idxAlong [] = ι₁ x := hc₁ x _ hX []
  rw [← h₃, (hs x _ hX).idx, at_comp hθ₁ θ₂ hθ₂ hc₂ hX,
    SubE.idxAlong_comp θ₂ hθ₂ hc₂ (okRef_at hθ₁ hX), h₁]

theorem sim_box_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁) (hθ₂ : Ok Δ₁ θ₂)
    (hc₂ : Coh ι₂ Δ₁ θ₂) (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
    Sim Γ.boxIn θ₃.box (θ₁.box.comp θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂)) := by
  refine sim_of ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      change SubE.Sim _ (θ₃.at u).unbox
        (((θ₁.at u).unbox).comp θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂))
      rw [← SubE.unbox_comp θ₂ hθ₂ hc₂ hk (okRef_at hθ₁ hu), ← at_comp hθ₁ θ₂ hθ₂ hc₂ hu]
      exact (hs u _ hu).unbox
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      change SubE.Sim T (θ₃.at u).keepE
        (((θ₁.at u).keepE).comp θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂))
      rw [← SubE.keepE_comp' θ₂ hθ₂ hc₂ hF hk (okRef_at hθ₁ hu), ← at_comp hθ₁ θ₂ hθ₂ hc₂ hu]
      exact (hs u _ hu).keepE' hF hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem sim_dia_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁)
    (hc₁ : Coh ι₁ Γ θ₁) (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂)
    (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hx₁ : ∃ X, Δ₁.ref (ι₁ x) = some (.VTypeDia X))
    (hw₂ : (θ₂.at (ι₁ x)).idxAlong [] = ι₂ (ι₁ x))
    (hw₃ : (θ₃.at x).idxAlong [] = ι₂ (ι₁ x)) :
    Sim (Γ.diaIn x) (θ₃.dia x (ι₂ (ι₁ x)))
      ((θ₁.dia x (ι₁ x)).comp (θ₂.dia (ι₁ x) (ι₂ (ι₁ x))) (ok_dia hθ₂ hx₁ hw₂)
        (coh_dia hθ₂ hc₂ hx₁)) := by
  have hw₁ : (θ₁.at x).idxAlong [] = ι₁ x := hx.elim fun _ hX => hc₁ x _ hX []
  refine sim_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change SubE.Sim T (if u = x then (θ₃.at x).diaBody (ι₂ (ι₁ x)) else SubE.hide)
        ((if u = x then (θ₁.at x).diaBody (ι₁ x) else SubE.hide).comp
          (θ₂.dia (ι₁ x) (ι₂ (ι₁ x))) (ok_dia hθ₂ hx₁ hw₂) (coh_dia hθ₂ hc₂ hx₁))
      by_cases hux : u = x
      · obtain ⟨X, hX⟩ := hx
        change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        rw [if_pos hux, hX] at hv
        cases hv
        rw [if_pos hux, if_pos hux,
          SubE.diaBody_comp θ₂ hθ₂ hc₂ hx₁ hw₂ (okRef_at hθ₁ hX) hw₁,
          ← at_comp hθ₁ θ₂ hθ₂ hc₂ hX]
        exact (hs x _ hX).diaBody hw₃
      · rw [if_neg hux, if_neg hux]
        exact .refl _
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ) hv
      change SubE.Sim _ (((θ₃.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ₂ (ι₂ (ι₁ x))))
        ((((θ₁.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ₁ (ι₁ x))).comp
          (θ₂.dia (ι₁ x) (ι₂ (ι₁ x))) (ok_dia hθ₂ hx₁ hw₂) (coh_dia hθ₂ hc₂ hx₁))
      rw [SubE.comp_mono θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂)
          (Ctx.le_boxIn_diaIn Δ₁ (ι₁ x)) (Ctx.le_boxIn_diaIn Δ₂ (ι₂ (ι₁ x))) _ _ _
          (dia_eq_box_mono θ₂ (ι₁ x) (ι₂ (ι₁ x))) (SubE.okRef_unbox (okRef_at hθ₁ hu)),
        ← SubE.unbox_comp θ₂ hθ₂ hc₂ hk (okRef_at hθ₁ hu), ← at_comp hθ₁ θ₂ hθ₂ hc₂ hu]
      exact (hs u _ hu).unbox.mono _
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      change SubE.Sim T
        (((θ₃.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ₂ (ι₂ (ι₁ x))))
        ((((θ₁.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ₁ (ι₁ x))).comp
          (θ₂.dia (ι₁ x) (ι₂ (ι₁ x))) (ok_dia hθ₂ hx₁ hw₂) (coh_dia hθ₂ hc₂ hx₁))
      rw [SubE.comp_mono θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂)
          (Ctx.le_boxIn_diaIn Δ₁ (ι₁ x)) (Ctx.le_boxIn_diaIn Δ₂ (ι₂ (ι₁ x))) _ _ _
          (dia_eq_box_mono θ₂ (ι₁ x) (ι₂ (ι₁ x))) (SubE.okRef_keepE' hF hk (okRef_at hθ₁ hu)),
        ← SubE.keepE_comp' θ₂ hθ₂ hc₂ hF hk (okRef_at hθ₁ hu), ← at_comp hθ₁ θ₂ hθ₂ hc₂ hu]
      exact ((hs u _ hu).keepE' hF hk).mono _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem sim_under_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁) (hθ₂ : Ok Δ₁ θ₂)
    (hc₂ : Coh ι₂ Δ₁ θ₂) (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) {d d₁ d₂ : ℕ}
    (hΔ₁ : Δ₁.SlotsFrom d₁) (T : VarType) (h₁ : Δ₁ (.root (.bnd d₁)) = none)
    (h₂ : Δ₂ (.root (.bnd d₂)) = none) :
    Sim (Γ.insert (.bnd d) T) (θ₃.under d d₂ T h₂)
      ((θ₁.under d d₁ T h₁).comp (θ₂.under d₁ d₂ T h₂) (ok_under hθ₂ T h₂)
        (coh_under hθ₂ hc₂ hΔ₁ T h₂)) := by
  refine sim_of ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · rw [show θ₃.under d d₂ T h₂ v = .ren (.root (.bnd d₂)) from if_pos hvr]
    change SubE.Sim U _ ((θ₁.under d d₁ T h₁ v).comp _ _ _)
    rw [show θ₁.under d d₁ T h₁ v = .ren (.root (.bnd d₁)) from if_pos hvr]
    change SubE.Sim U _ ((θ₂.under d₁ d₂ T h₂) (.root (.bnd d₁)))
    rw [show θ₂.under d₁ d₂ T h₂ (.root (.bnd d₁)) = .ren (.root (.bnd d₂)) from if_pos rfl]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show θ₃.under d d₂ T h₂ v = (θ₃ v).mono (Ctx.le_insert h₂ T) from if_neg hvr]
    change SubE.Sim U _ ((θ₁.under d d₁ T h₁ v).comp _ _ _)
    rw [show θ₁.under d d₁ T h₁ v = (θ₁ v).mono (Ctx.le_insert h₁ T) from if_neg hvr,
      SubE.comp_mono θ₂ hθ₂ hc₂ (Ctx.le_insert h₁ T) (Ctx.le_insert h₂ T) _ _ _
        (under_eq_mono θ₂ hΔ₁ T h₂) (hθ₁ v U hlp hv')]
    have h₃ := hs v U ((Ctx.ref_nonproj Γ hlp).trans hv')
    rw [at_nonproj θ₃ hlp, at_nonproj _ hlp] at h₃
    exact h₃.mono _

end Subst

theorem SubE.Sim.okRef {σ : Signature} {Δ : Ctx} {T : VarType} {e e' : SubE σ Δ}
    (h : SubE.Sim T e e') (he : e.OkRef T) : e'.OkRef T := by
  cases h with
  | refl => exact he
  | eta_ren w h => exact h
  | ren_eta w h => exact rfl

/-! ## Substituting twice -/

mutual
  theorem Func.subst_comp {σ : Signature} {ι₁ ι₂ ι₃ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx}
      (θ₁ : Subst σ Δ₁) (θ₂ θ₃ : Subst σ Δ₂) (hθ₁ : Subst.Ok Γ θ₁) (hc₁ : Subst.Coh ι₁ Γ θ₁)
      (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) (hθ₃ : Subst.Ok Γ θ₃)
      (hc₃ : Subst.Coh ι₃ Γ θ₃) (hs : Subst.Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
      {n : ℕ} → (f : Func σ Γ n) →
      Func.subst ι₂ θ₂ hθ₂ hc₂ (Func.subst ι₁ θ₁ hθ₁ hc₁ f) = Func.subst ι₃ θ₃ hθ₃ hc₃ f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι₂ θ₂ hθ₂ hc₂ (Func.subst ι₁ θ₁ hθ₁ hc₁ g))
          (Term.subst ι₂ θ₂ hθ₂ hc₂ (Term.subst ι₁ θ₁ hθ₁ hc₁ t)) = _
        rw [Func.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs g,
          eq_of_heq (Sigma.mk.inj (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)).2]
        rfl
    termination_by structural _ f => f

  /-- ⭐**Substituting twice, at every type**: the annotation moves with the index maps, so the
      two sides are equal as annotated terms.  Only the `Var` case needs `Sim`; the structured
      cases are the recursion, the witness of a `◇`-term travelling by `Subst.idx_comp`. -/
  theorem Term.subst_comp_sig {σ : Signature} {ι₁ ι₂ ι₃ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx}
      (θ₁ : Subst σ Δ₁) (θ₂ θ₃ : Subst σ Δ₂) (hθ₁ : Subst.Ok Γ θ₁) (hc₁ : Subst.Coh ι₁ Γ θ₁)
      (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) (hθ₃ : Subst.Ok Γ θ₃)
      (hc₃ : Subst.Coh ι₃ Γ θ₃) (hs : Subst.Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.subst ι₂ θ₂ hθ₂ hc₂ (Term.subst ι₁ θ₁ hθ₁ hc₁ t)⟩ : Σ b, Term σ Δ₂ T b) =
        ⟨_, Term.subst ι₃ θ₃ hθ₃ hc₃ t⟩
    | _, _, .var v hv =>
        have p₄ := Subst.okRef_at hθ₃ hv
        have p₃ := (hs v _ hv).okRef p₄
        congrArg (Sigma.mk _) ((SubE.toVar_comp θ₂ hθ₂ hc₂ _ (Subst.okRef_at hθ₁ hv)).trans
          ((SubE.toVar_congr (Subst.at_comp hθ₁ θ₂ hθ₂ hc₂ hv).symm _ p₃).trans
            ((hs v _ hv).toVar p₄ p₃).symm))
    | _, _, .func f => by
        change (⟨_, Term.func (Func.subst ι₂ θ₂ hθ₂ hc₂ (Func.subst ι₁ θ₁ hθ₁ hc₁ f))⟩ :
            Σ b, Term σ Δ₂ .Var b) = ⟨_, Term.func (Func.subst ι₃ θ₃ hθ₃ hc₃ f)⟩
        rw [Func.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs s)
          (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.subst_comp_sig θ₁.box θ₂.box θ₃.box (Subst.ok_box hθ₁)
          (Subst.coh_box hθ₁ hc₁) (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂) (Subst.ok_box hθ₃)
          (Subst.coh_box hθ₃ hc₃) (Subst.sim_box_comp hθ₁ hθ₂ hc₂ hs) t)
    | _, _, .diatm x hx t => by
        have hw₁ : (θ₁.at x).idxAlong [] = ι₁ x := hx.elim fun _ hX => hc₁ x _ hX []
        have hx₁ : ∃ X, Δ₁.ref (ι₁ x) = some (.VTypeDia X) :=
          hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ₁ hX) hw₁
        have hw₂ : (θ₂.at (ι₁ x)).idxAlong [] = ι₂ (ι₁ x) := hx₁.elim fun _ hX => hc₂ _ _ hX []
        have hι : ι₃ x = ι₂ (ι₁ x) := Subst.idx_comp hθ₁ hc₁ hθ₂ hc₂ hc₃ hs hx
        have hw₃ : (θ₃.at x).idxAlong [] = ι₂ (ι₁ x) :=
          (hx.elim fun _ hX => hc₃ x _ hX []).trans hι
        have key : ∀ (y : VarSymb) (_hy : y = ι₂ (ι₁ x)) (P : ∃ Y, Δ₂.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ.diaIn x) (θ₃.dia x y)) (q : Subst.Coh ι₃ (Γ.diaIn x) (θ₃.dia x y)),
            (⟨_, Term.subst ι₂ θ₂ hθ₂ hc₂ (Term.subst ι₁ θ₁ hθ₁ hc₁ (Term.diatm x hx t))⟩ :
              Σ b, Term σ Δ₂ _ b) =
              ⟨_, Term.diatm y P (Term.subst ι₃ (θ₃.dia x y) p q t)⟩ := by
          intro y hy P p q
          subst hy
          exact sig_diatm (Term.subst_comp_sig (θ₁.dia x (ι₁ x)) (θ₂.dia (ι₁ x) (ι₂ (ι₁ x)))
            (θ₃.dia x (ι₂ (ι₁ x))) (Subst.ok_dia hθ₁ hx hw₁) (Subst.coh_dia hθ₁ hc₁ hx)
            (Subst.ok_dia hθ₂ hx₁ hw₂) (Subst.coh_dia hθ₂ hc₂ hx₁) p q
            (Subst.sim_dia_comp hθ₁ hc₁ hθ₂ hc₂ hs hx hx₁ hw₂ hw₃) t)
        exact key (ι₃ x) hι _ _ _
    termination_by structural _ _ t => t
end

theorem Term.subst_comp {σ : Signature} {ι₁ ι₂ ι₃ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx}
    (θ₁ : Subst σ Δ₁) (θ₂ θ₃ : Subst σ Δ₂) (hθ₁ : Subst.Ok Γ θ₁) (hc₁ : Subst.Coh ι₁ Γ θ₁)
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) (hθ₃ : Subst.Ok Γ θ₃)
    (hc₃ : Subst.Coh ι₃ Γ θ₃) (hs : Subst.Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂))
    (t : Term σ Γ .Var .var) :
    Term.subst ι₂ θ₂ hθ₂ hc₂ (Term.subst ι₁ θ₁ hθ₁ hc₁ t) = Term.subst ι₃ θ₃ hθ₃ hc₃ t :=
  eq_of_heq (Sigma.mk.inj (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)).2

theorem Rel.subst_comp {σ : Signature} {ι₁ ι₂ ι₃ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx}
    (θ₁ : Subst σ Δ₁) (θ₂ θ₃ : Subst σ Δ₂) (hθ₁ : Subst.Ok Γ θ₁) (hc₁ : Subst.Coh ι₁ Γ θ₁)
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) (hθ₃ : Subst.Ok Γ θ₃)
    (hc₃ : Subst.Coh ι₃ Γ θ₃) (hs : Subst.Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
    {n : ℕ} → (ρ : Rel σ Γ n) →
    Rel.subst ι₂ θ₂ hθ₂ hc₂ (Rel.subst ι₁ θ₁ hθ₁ hc₁ ρ) = Rel.subst ι₃ θ₃ hθ₃ hc₃ ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.subst ι₂ θ₂ hθ₂ hc₂ (Rel.subst ι₁ θ₁ hθ₁ hc₁ ρ))
        (Term.subst ι₂ θ₂ hθ₂ hc₂ (Term.subst ι₁ θ₁ hθ₁ hc₁ t)) = _
      rw [Rel.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs ρ,
        Term.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t]
      rfl

/-- ⭐**Substituting twice** is substituting once, by any coherent `θ₃` agreeing up to η with the
    composite entries. -/
theorem WFF.subst_comp {σ : Signature} : {ι₁ ι₂ ι₃ : VarSymb → VarSymb} → {Γ Δ₁ Δ₂ : Ctx} →
    {d d₁ d₂ : ℕ} → (θ₁ : Subst σ Δ₁) → (θ₂ θ₃ : Subst σ Δ₂) → (hθ₁ : Subst.Ok Γ θ₁) →
    (hc₁ : Subst.Coh ι₁ Γ θ₁) → (hθ₂ : Subst.Ok Δ₁ θ₂) → (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) →
    (hθ₃ : Subst.Ok Γ θ₃) → (hc₃ : Subst.Coh ι₃ Γ θ₃) → (hΓ : Γ.SlotsFrom d) →
    (hΔ₁ : Δ₁.SlotsFrom d₁) → (hΔ₂ : Δ₂.SlotsFrom d₂) →
    Subst.Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂) → (φ : WFF σ Γ d) →
    WFF.subst ι₂ θ₂ hθ₂ hc₂ hΔ₁ hΔ₂ (WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ hΔ₁ φ) =
      WFF.subst ι₃ θ₃ hθ₃ hc₃ hΓ hΔ₂ φ
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, _, _, _, hs, .atom ρ =>
      congrArg WFF.atom (Rel.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs ρ)
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, _, _, _, hs, .eq t s =>
      congrArg₂ WFF.eq (Term.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)
        (Term.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs s)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂, hs,
      .and φ ψ =>
      congrArg₂ WFF.and
        (WFF.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hΓ hΔ₁ hΔ₂ hs φ)
        (WFF.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hΓ hΔ₁ hΔ₂ hs ψ)
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂, hs,
      .or φ ψ =>
      congrArg₂ WFF.or
        (WFF.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hΓ hΔ₁ hΔ₂ hs φ)
        (WFF.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hΓ hΔ₁ hΔ₂ hs ψ)
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂, hs,
      .imp φ ψ =>
      congrArg₂ WFF.imp
        (WFF.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hΓ hΔ₁ hΔ₂ hs φ)
        (WFF.subst_comp θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hΓ hΔ₁ hΔ₂ hs ψ)
  | _, _, _, _, _, _, d, d₁, d₂, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂, hs,
      .all T φ =>
      congrArg (WFF.all T) (WFF.subst_comp (θ₁.under d d₁ T hΔ₁.root)
        (θ₂.under d₁ d₂ T hΔ₂.root) (θ₃.under d d₂ T hΔ₂.root) (Subst.ok_under hθ₁ T hΔ₁.root)
        (Subst.coh_under hθ₁ hc₁ hΓ T hΔ₁.root) (Subst.ok_under hθ₂ T hΔ₂.root)
        (Subst.coh_under hθ₂ hc₂ hΔ₁ T hΔ₂.root) (Subst.ok_under hθ₃ T hΔ₂.root)
        (Subst.coh_under hθ₃ hc₃ hΓ T hΔ₂.root) (hΓ.insert T) (hΔ₁.insert T) (hΔ₂.insert T)
        (Subst.sim_under_comp hθ₁ hθ₂ hc₂ hs hΔ₁ T hΔ₁.root hΔ₂.root) φ)
  | _, _, _, _, _, _, d, d₁, d₂, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂, hs,
      .ex T φ =>
      congrArg (WFF.ex T) (WFF.subst_comp (θ₁.under d d₁ T hΔ₁.root)
        (θ₂.under d₁ d₂ T hΔ₂.root) (θ₃.under d d₂ T hΔ₂.root) (Subst.ok_under hθ₁ T hΔ₁.root)
        (Subst.coh_under hθ₁ hc₁ hΓ T hΔ₁.root) (Subst.ok_under hθ₂ T hΔ₂.root)
        (Subst.coh_under hθ₂ hc₂ hΔ₁ T hΔ₂.root) (Subst.ok_under hθ₃ T hΔ₂.root)
        (Subst.coh_under hθ₃ hc₃ hΓ T hΔ₂.root) (hΓ.insert T) (hΔ₁.insert T) (hΔ₂.insert T)
        (Subst.sim_under_comp hθ₁ hθ₂ hc₂ hs hΔ₁ T hΔ₁.root hΔ₂.root) φ)
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂, hs,
      .box φ =>
      congrArg WFF.box (WFF.subst_comp θ₁.box θ₂.box θ₃.box (Subst.ok_box hθ₁)
        (Subst.coh_box hθ₁ hc₁) (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂) (Subst.ok_box hθ₃)
        (Subst.coh_box hθ₃ hc₃) hΓ.boxIn hΔ₁.boxIn hΔ₂.boxIn
        (Subst.sim_box_comp hθ₁ hθ₂ hc₂ hs) φ)
  | ι₁, ι₂, ι₃, Γ, Δ₁, Δ₂, _, _, d₂, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂,
      hs, .dia x hx φ => by
      have hw₁ : (θ₁.at x).idxAlong [] = ι₁ x := hx.elim fun _ hX => hc₁ x _ hX []
      have hx₁ : ∃ X, Δ₁.ref (ι₁ x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ₁ hX) hw₁
      have hw₂ : (θ₂.at (ι₁ x)).idxAlong [] = ι₂ (ι₁ x) := hx₁.elim fun _ hX => hc₂ _ _ hX []
      have hι : ι₃ x = ι₂ (ι₁ x) := Subst.idx_comp hθ₁ hc₁ hθ₂ hc₂ hc₃ hs hx
      have hw₃ : (θ₃.at x).idxAlong [] = ι₂ (ι₁ x) :=
        (hx.elim fun _ hX => hc₃ x _ hX []).trans hι
      have key : ∀ (y : VarSymb) (_hy : y = ι₂ (ι₁ x)) (P : ∃ Y, Δ₂.ref y = some (.VTypeDia Y))
          (p : Subst.Ok (Γ.diaIn x) (θ₃.dia x y)) (q : Subst.Coh ι₃ (Γ.diaIn x) (θ₃.dia x y))
          (hΔy : (Δ₂.diaIn y).SlotsFrom d₂),
          WFF.subst ι₂ θ₂ hθ₂ hc₂ hΔ₁ hΔ₂ (WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ hΔ₁ (.dia x hx φ)) =
            .dia y P (WFF.subst ι₃ (θ₃.dia x y) p q (hΓ.diaIn x) hΔy φ) := by
        intro y hy P p q hΔy
        subst hy
        exact congrArg (WFF.dia (ι₂ (ι₁ x)) _) (WFF.subst_comp (θ₁.dia x (ι₁ x))
          (θ₂.dia (ι₁ x) (ι₂ (ι₁ x))) (θ₃.dia x (ι₂ (ι₁ x))) (Subst.ok_dia hθ₁ hx hw₁)
          (Subst.coh_dia hθ₁ hc₁ hx) (Subst.ok_dia hθ₂ hx₁ hw₂) (Subst.coh_dia hθ₂ hc₂ hx₁) p q
          (hΓ.diaIn x) (hΔ₁.diaIn (ι₁ x)) hΔy
          (Subst.sim_dia_comp hθ₁ hc₁ hθ₂ hc₂ hs hx hx₁ hw₂ hw₃) φ)
      exact key (ι₃ x) hι _ _ _ _
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, _, _, _, hs,
      .here hT s t =>
      WFF.here_congr hT (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs s)
        (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, _, _, _, hs,
      .back hB L s t =>
      WFF.back_congr hB L (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs s)
        (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)
  | _, _, _, _, _, _, d, d₁, d₂, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂, hs,
      .retS hB S t Φ =>
      WFF.retS_congr hB S (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)
        (WFF.subst_comp (θ₁.box.under d d₁ _ hΔ₁.boxIn.root) (θ₂.box.under d₁ d₂ _ hΔ₂.boxIn.root)
          (θ₃.box.under d d₂ _ hΔ₂.boxIn.root) (Subst.ok_under (Subst.ok_box hθ₁) _ hΔ₁.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ₁) (Subst.coh_box hθ₁ hc₁) hΓ.boxIn _ hΔ₁.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ₂) _ hΔ₂.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂) hΔ₁.boxIn _ hΔ₂.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ₃) _ hΔ₂.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ₃) (Subst.coh_box hθ₃ hc₃) hΓ.boxIn _ hΔ₂.boxIn.root)
          (hΓ.boxIn.insert _) (hΔ₁.boxIn.insert _) (hΔ₂.boxIn.insert _)
          (Subst.sim_under_comp (Subst.ok_box hθ₁) (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂)
            (Subst.sim_box_comp hθ₁ hθ₂ hc₂ hs) hΔ₁.boxIn _ hΔ₁.boxIn.root hΔ₂.boxIn.root) Φ)
  | ι₁, ι₂, ι₃, Γ, Δ₁, Δ₂, d, d₁, d₂, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂,
      hs, .retxS hB y hy S t Φ => by
      have hw₁ : (θ₁.at y).idxAlong [] = ι₁ y := hy.elim fun _ hY => hc₁ y _ hY []
      have hy₁ : ∃ Y, Δ₁.ref (ι₁ y) = some (.VTypeDia Y) :=
        hy.elim fun _ hY => SubE.ref_witness (Subst.okRef_at hθ₁ hY) hw₁
      have hw₂ : (θ₂.at (ι₁ y)).idxAlong [] = ι₂ (ι₁ y) := hy₁.elim fun _ hY => hc₂ _ _ hY []
      have hι : ι₃ y = ι₂ (ι₁ y) := Subst.idx_comp hθ₁ hc₁ hθ₂ hc₂ hc₃ hs hy
      have hw₃ : (θ₃.at y).idxAlong [] = ι₂ (ι₁ y) :=
        (hy.elim fun _ hY => hc₃ y _ hY []).trans hι
      have hr₁ := (hΔ₁.diaIn (ι₁ y)).root
      have key : ∀ (z : VarSymb) (_hz : z = ι₂ (ι₁ y)) (P : ∃ Y, Δ₂.ref z = some (.VTypeDia Y))
          (hΔz : (Δ₂.diaIn z).SlotsFrom d₂)
          (p : Subst.Ok ((Γ.diaIn y).insert (.bnd d) S.ty)
            ((θ₃.dia y z).under d d₂ _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot ι₃ d d₂) ((Γ.diaIn y).insert (.bnd d) S.ty)
            ((θ₃.dia y z).under d d₂ _ hΔz.root)),
          WFF.subst ι₂ θ₂ hθ₂ hc₂ hΔ₁ hΔ₂ (WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ hΔ₁ (.retxS hB y hy S t Φ)) =
            .retxS hB z P S (Term.subst ι₃ θ₃ hθ₃ hc₃ t)
              (WFF.subst (VarSymb.shiftSlot ι₃ d d₂) ((θ₃.dia y z).under d d₂ _ hΔz.root) p q
                ((hΓ.diaIn y).insert _) (hΔz.insert _) Φ) := by
        intro z hz P hΔz p q
        subst hz
        exact WFF.retxS_congr hB _ _ S
          (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)
          (WFF.subst_comp ((θ₁.dia y (ι₁ y)).under d d₁ _ hr₁)
            ((θ₂.dia (ι₁ y) (ι₂ (ι₁ y))).under d₁ d₂ _ hΔz.root) _
            (Subst.ok_under (Subst.ok_dia hθ₁ hy hw₁) _ hr₁)
            (Subst.coh_under (Subst.ok_dia hθ₁ hy hw₁) (Subst.coh_dia hθ₁ hc₁ hy) (hΓ.diaIn y) _
              hr₁)
            (Subst.ok_under (Subst.ok_dia hθ₂ hy₁ hw₂) _ hΔz.root)
            (Subst.coh_under (Subst.ok_dia hθ₂ hy₁ hw₂) (Subst.coh_dia hθ₂ hc₂ hy₁)
              (hΔ₁.diaIn (ι₁ y)) _ hΔz.root)
            p q ((hΓ.diaIn y).insert _) ((hΔ₁.diaIn (ι₁ y)).insert _) (hΔz.insert _)
            (Subst.sim_under_comp (Subst.ok_dia hθ₁ hy hw₁) (Subst.ok_dia hθ₂ hy₁ hw₂)
              (Subst.coh_dia hθ₂ hc₂ hy₁) (Subst.sim_dia_comp hθ₁ hc₁ hθ₂ hc₂ hs hy hy₁ hw₂ hw₃)
              (hΔ₁.diaIn (ι₁ y)) _ hr₁ hΔz.root) Φ)
      exact key (ι₃ y) hι _ (hΔ₂.diaIn _) _ _

end V12M
