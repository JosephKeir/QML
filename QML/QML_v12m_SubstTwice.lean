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
              rw [SubE.keepE_dia _ _ _ hF]
              exact SubE.tm_eq_of_sig (sig_diatm ((Term.collapse_shift_self (m := 0)
                (Ctx.shifts_diaIn_keep hF Δ y)
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

/-- A witness entry's content one view in, collapsed back at level 0, is the entry's identity
    content (M2). -/
theorem SubE.toWit_optBody_collapse_self {σ : Signature} {Δ : Ctx} (hT : ModalSys.T = true)
    (hO : ModalSys.Opt = true) {z : VarSymb} {Z : VarType} (hz : Δ.boxIn.wit z = some Z) :
    ∀ {e : SubE σ Δ} {X : VarType}, e.OkRef (.VTypeDia X) → e.idxAlong [] = z →
      (e.toWit.optBody z).collapse ((Ctx.collapses_boxIn_self hT Δ).optIn_zero hO hz) =
        e.atBody z
  | .ren w, _, _, hw => by
      have hw' : w = z := hw
      subst hw'
      change SubE.ren ((VarSymb.step w .dia).collapse 0) = SubE.ren (.step w .at)
      rw [VarSymb.collapse_dia_zero_opt hO]
  | .tm (.diatm x hx b), _, _, hw => by
      have hxz : x = z := hw
      subst hxz
      obtain ⟨Y, hY⟩ := id hx
      rw [show (SubE.tm (Term.diatm x hx b) : SubE σ Δ).toWit =
          WitE.tm x (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) b) from dif_pos hO,
        show (WitE.tm x (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) b) :
            WitE σ Δ.boxIn).optBody x =
          SubE.tm (Term.mono (Ctx.Le.refl _) (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) b))
          from dif_pos rfl, Term.mono_refl,
        show (SubE.tm (Term.diatm x hx b) : SubE σ Δ).atBody x =
          SubE.tm (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) b)
          from dif_pos ⟨hT, hO, rfl⟩]
      change SubE.tm (Term.collapse _ (Term.mono _ b)) = _
      rw [Term.collapse_mono (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) _ _ (Ctx.Le.refl _) b,
        Term.mono_refl]
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

/-- ⭐At the T rule the `□` view's witnesses correspond to the possible objects' identity
    contents (M2). -/
theorem Subst.corrW_box_self {σ : Signature} {Γ Δ : Ctx} (hT : ModalSys.T = true)
    {θ : Subst σ Δ} (hθ : Subst.Ok Γ θ) :
    Subst.CorrW Γ.boxIn (Ctx.collapses_boxIn_self hT Δ) θ.box θ := by
  intro y X hy hO z hzi
  obtain ⟨-, hr⟩ := Ctx.boxIn_wit.mp hy
  have he := Subst.okRef_at hθ hr
  have hzi' : (θ.at y).idxAlong [] = z := (SubE.idxAlong_toWit hO [] he).symm.trans hzi
  refine ⟨hzi', ?_⟩
  obtain ⟨Z, hZ⟩ := WitE.wit_of (SubE.okW_toWit hO he) hzi
  refine ⟨Z, hZ, ?_⟩
  change SubE.Sim X ((θ.at y).atBody z) (((θ.at y).toWit.optBody z).collapse _)
  rw [SubE.toWit_optBody_collapse_self hT hO hZ he hzi']
  exact .refl _

/-- A possible object's content one view in, collapsed at level 0 onto its identity view, is its
    identity content (M2). -/
theorem SubE.diaBody_collapse_zero {σ : Signature} {Δ : Ctx} (hT : ModalSys.T = true)
    (hO : ModalSys.Opt = true) {z : VarSymb} {Y : VarType} (hz : Δ.ref z = some (.VTypeDia Y)) :
    ∀ {e : SubE σ Δ} {X : VarType}, e.OkRef (.VTypeDia X) → e.idxAlong [] = z →
      (e.diaBody z).collapse (Ctx.collapses_diaIn_optInT hT hO Δ hz) = e.atBody z
  | .ren w, _, _, hw => by
      have hw' : w = z := hw
      subst hw'
      change SubE.ren ((VarSymb.step w .dia).collapse 0) = SubE.ren (.step w .at)
      rw [VarSymb.collapse_dia_zero_opt hO]
  | .tm (.diatm x hx b), _, _, hw => by
      have hxz : x = z := hw
      subst hxz
      rw [SubE.diaBody_diatm, show (SubE.tm (Term.diatm x hx b) : SubE σ Δ).atBody x =
        SubE.tm (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) b)
        from dif_pos ⟨hT, hO, rfl⟩]
      rfl
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

/-- A necessary object's content in the `◇_z` view, collapsed onto `z`'s identity view, is its
    value here (M2). -/
theorem SubE.unbox_collapse_zero {σ : Signature} {Δ : Ctx} (hT : ModalSys.T = true)
    (hO : ModalSys.Opt = true) {z : VarSymb} {Y : VarType} (hz : Δ.ref z = some (.VTypeDia Y)) :
    ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) →
      (e.unbox.mono (Ctx.le_boxIn_diaIn Δ z)).collapse (Ctx.collapses_diaIn_optInT hT hO Δ hz) =
        (e.proj .here).mono (Ctx.le_optInT Δ z)
  | .ren w, _, _ => by
      have hF : ModalSys.Four = false := by
        cases h : ModalSys.Four
        · rfl
        · exact absurd (ModalSys.noOpt_of_Four h) (by rw [hO]; decide)
      have hk : ModalSys.keepOnly = false := by simp [ModalSys.keepOnly, hF]
      change SubE.ren ((VarSymb.inner w).collapse 0) = SubE.ren (.step w .here)
      rw [VarSymb.inner, if_neg (by rw [hk]; decide),
        VarSymb.collapse_level_zero rfl (by decide) (by decide)]
  | .tm (.boxtm t), _, _ => by
      rw [SubE.proj_boxtm_here _ hT]
      exact congrArg SubE.tm (Term.collapse_mono (Ctx.collapses_boxIn_self hT Δ) _ _ _ t)
  | .tm (.var _ _), _, he => nomatch he
  | .tm (.func _), _, he => nomatch he
  | .tm .unit, _, he => nomatch he
  | .tm (.pair _ _), _, he => nomatch he
  | .tm (.diatm _ _ _), _, he => nomatch he
  | .hide, _, he => False.elim he

/-- ⭐At level 0 the `◇_z` view of a substitution corresponds to its identity view (M2). -/
theorem Subst.corr_dia_optInT {σ : Signature} {ι₂ : VarSymb → VarSymb} {Δ₁ Δ₂ : Ctx}
    (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) {θ₂ : Subst σ Δ₂}
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) {x₁ : VarSymb} {X₁ : VarType}
    (hx₁ : Δ₁.ref x₁ = some (.VTypeDia X₁)) {z₂ : VarSymb} (hw₂ : (θ₂.at x₁).idxAlong [] = z₂)
    {Y : VarType} (hz₂ : Δ₂.ref z₂ = some (.VTypeDia Y)) :
    Subst.Corr (Δ₁.diaIn x₁) (Ctx.collapses_diaIn_optInT hT hO Δ₂ hz₂) (θ₂.dia x₁ z₂)
      (θ₂.optInT x₁ z₂) := by
  have hxT : Δ₁.witT x₁ = some X₁ := Ctx.witT_of hT hO hx₁
  refine Subst.corr_of (Subst.ok_dia hθ₂ ⟨X₁, hx₁⟩ hw₂) ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x₁ then (match Δ₁.ref x₁ with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      rw [hx₁] at hv
      cases hv
      rw [VarSymb.collapse_dia_zero_opt hO, Subst.at_nonproj _ rfl, Subst.optInT_content]
      change SubE.Sim _ _ ((if u = u then (θ₂.at u).diaBody z₂ else SubE.hide).collapse _)
      rw [if_pos rfl, SubE.diaBody_collapse_zero hT hO hz₂ (Subst.okRef_at hθ₂ hx₁) hw₂]
      exact .refl _
  | .step u .box =>
      have hu := Ctx.boxIn_step_box (Γ := Δ₁) hv
      rw [VarSymb.collapse_level_zero rfl (by decide) (by decide)]
      change SubE.Sim T (((θ₂.optInT x₁ z₂).at u).proj .here)
        ((((θ₂.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ₂ z₂)).collapse _)
      rw [Subst.at_optInT_of hc₂ hxT hw₂ u _ hu, SubE.proj_mono,
        SubE.unbox_collapse_zero hT hO hz₂ (Subst.okRef_at hθ₂ hu)]
      exact .refl _
  | .step u .keep =>
      exact absurd hO (by rw [ModalSys.noOpt_of_Four (Ctx.boxIn_keep (Γ := Δ₁) hv).1]; decide)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

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
    s.isStruct = true → U.step s = some T →
    (e.comp θ₂ hθ₂ hc₂).proj s = (e.proj s).comp θ₂ hθ₂ hc₂
  | .ren w, _, _, s, _, hs, _ => by
      change (θ₂.at w).proj s = θ₂.at (.step w s)
      change _ = (if s.isStruct then (θ₂.at w).proj s else θ₂ (.step w s))
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
      | «at» => cases hs
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
              obtain ⟨X, hX⟩ := hy
              have hw : (θ₂.at y).idxAlong [] = ι₂ y := hc₂ y _ hX []
              have hwk : (θ₂.box.at (.step y .keep)).idxAlong [] = .step (ι₂ y) .keep := by
                change ((θ₂.at y).keepE).idxAlong [] = _
                rw [SubE.idxAlong_keepE' hF [] VarType.keepable_dia (Subst.okRef_at hθ₂ hX),
                  SubE.idxAlong_keep_dia (Subst.okRef_at hθ₂ hX), hw]
              have hk₂ : ι₂ (.step y .keep) = .step (ι₂ y) .keep := by
                have h := hc₂ y _ hX [.keep]
                rw [SubE.idxAlong_keep_dia (Subst.okRef_at hθ₂ hX), hw] at h
                exact h.symm
              obtain ⟨X₂, hy₂⟩ := SubE.ref_witness (Subst.okRef_at hθ₂ hX) hw
              have hyk : ∃ X', Δ₁.boxIn.ref (.step y .keep) = some (.VTypeDia X') :=
                ⟨X, Ctx.ref_keep_of' hF hX VarType.keepable_dia⟩
              change (SubE.tm (Term.diatm (ι₂ y) _ (Term.subst ι₂ (θ₂.dia y (ι₂ y))
                  (Subst.ok_dia hθ₂ ⟨X, hX⟩ hw) (Subst.coh_dia hθ₂ hc₂ ⟨X, hX⟩) t))).keepE =
                ((SubE.tm (Term.diatm y ⟨X, hX⟩ t)).keepE).comp θ₂.box (Subst.ok_box hθ₂)
                  (Subst.coh_box hθ₂ hc₂)
              rw [keepE_dia _ _ _ hF, keepE_dia _ _ _ hF]
              refine SubE.tm_eq_of_sig (Eq.symm ((Term.subst_diatm_sig θ₂.box
                (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂) hyk _ hk₂ hwk
                (Subst.ok_dia (Subst.ok_box hθ₂) hyk hwk)
                (hk₂ ▸ Subst.coh_dia (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂) hyk)
                ⟨X₂, Ctx.ref_keep_of' hF hy₂ VarType.keepable_dia⟩).trans (sig_diatm ?_)))
              exact (Term.shift_subst (Ctx.shifts_diaIn_keep hF Δ₁ y)
                (Ctx.shifts_diaIn_keep hF Δ₂ (ι₂ y)) (θ₂.dia y (ι₂ y))
                (Subst.ok_dia hθ₂ ⟨X, hX⟩ hw) (Subst.coh_dia hθ₂ hc₂ ⟨X, hX⟩) _ _ _
                (Subst.shiftCorr_dia_keep hF hθ₂ ⟨X, hX⟩ hw) t).symm
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

/-- ⭐**A substituted possible object's identity content**: the entry's identity content pushed
    through `θ₂`'s identity view is the pushed entry's identity content (M2). -/
theorem atBody_comp (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) (θ₂ : Subst σ Δ₂)
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) {x₁ : VarSymb} {X₁ : VarType}
    (hx₁ : Δ₁.witT x₁ = some X₁) (hw₂ : (θ₂.at x₁).idxAlong [] = ι₂ x₁) :
    ∀ {e : SubE σ Δ₁} {X : VarType}, e.OkRef (.VTypeDia X) → e.idxAlong [] = x₁ →
      (e.atBody x₁).comp (θ₂.optInT x₁ (ι₂ x₁)) (Subst.ok_optInT hθ₂ hx₁ hw₂)
          (Subst.coh_optInT hθ₂ hc₂ hx₁) =
        (e.comp θ₂ hθ₂ hc₂).atBody (ι₂ x₁)
  | .ren w, _, _, hw => by
      have hw' : w = x₁ := hw
      subst hw'
      change (θ₂.optInT w (ι₂ w)).at (.step w .at) = (θ₂.at w).atBody (ι₂ w)
      rw [Subst.at_nonproj _ rfl, Subst.optInT_content]
  | .tm (.diatm x hx b), _, _, hw => by
      have hxz : x = x₁ := hw
      subst hxz
      obtain ⟨X₀, hr⟩ := id hx
      obtain ⟨Y, hY⟩ := SubE.ref_witness (Subst.okRef_at hθ₂ hr) hw₂
      rw [show (SubE.tm (Term.diatm x hx b) : SubE σ Δ₁).atBody x =
        SubE.tm (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) b)
        from dif_pos ⟨hT, hO, rfl⟩]
      change SubE.tm (Term.subst ι₂ _ _ _ _) =
        (SubE.tm (Term.diatm (ι₂ x) _ (Term.subst ι₂ (θ₂.dia x (ι₂ x))
          (Subst.ok_dia hθ₂ hx hw₂) (Subst.coh_dia hθ₂ hc₂ hx) b))).atBody (ι₂ x)
      rw [show (SubE.tm (Term.diatm (ι₂ x) ⟨Y, hY⟩ (Term.subst ι₂ (θ₂.dia x (ι₂ x))
          (Subst.ok_dia hθ₂ hx hw₂) (Subst.coh_dia hθ₂ hc₂ hx) b)) : SubE σ Δ₂).atBody (ι₂ x) =
        SubE.tm (Term.collapse (Ctx.collapses_diaIn_optInT hT hO Δ₂ hY)
          (Term.subst ι₂ (θ₂.dia x (ι₂ x)) (Subst.ok_dia hθ₂ hx hw₂) (Subst.coh_dia hθ₂ hc₂ hx) b))
        from dif_pos ⟨hT, hO, rfl⟩]
      exact tm_eq_of_sig (Term.collapse_subst (Ctx.collapses_diaIn_optInT hT hO Δ₁ hr)
        (Ctx.collapses_diaIn_optInT hT hO Δ₂ hY) (θ₂.dia x (ι₂ x)) (Subst.ok_dia hθ₂ hx hw₂)
        (Subst.coh_dia hθ₂ hc₂ hx) (θ₂.optInT x (ι₂ x)) (Subst.ok_optInT hθ₂ hx₁ hw₂)
        (Subst.coh_optInT hθ₂ hc₂ hx₁)
        (Subst.corr_dia_optInT hT hO hθ₂ hc₂ hr hw₂ hY) b).symm
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

end SubE

/-- `θ.dia` weakened into the witness view is the witness view of `θ.box`: the content's entry is
    the body either way (`SubE.toWit_optBody`). -/
theorem Subst.simT_dia_box_optIn {σ : Signature} {Δ₁ Δ₂ : Ctx} {θ₂ : Subst σ Δ₂}
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hO : ModalSys.Opt = true) {z ιz : VarSymb} {Z : VarType}
    (hZ : Δ₁.ref z = some (.VTypeDia Z)) (L : (Δ₂.diaIn ιz).Le (Δ₂.boxIn.optIn ιz)) :
    Subst.SimT (Δ₁.diaIn z) ((θ₂.dia z ιz).mono L) (θ₂.box.optIn z ιz) := by
  refine Subst.simT_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = z then (match Δ₁.ref z with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with huz
      subst huz
      rw [hZ] at hv
      cases hv
      change SubE.Sim Z (SubE.mono L (if u = u then (θ₂.at u).diaBody ιz else SubE.hide))
        (θ₂.box.optIn u ιz (.step u .dia))
      rw [if_pos rfl, Subst.optIn_content]
      change SubE.Sim Z _ (((θ₂.at u).toWit).optBody ιz)
      rw [SubE.toWit_optBody hO ιz (Subst.okRef_at hθ₂ hZ) L]
      exact .refl _
  | .step u .box =>
      change SubE.Sim T (SubE.mono L (((θ₂.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ₂ ιz)))
        (θ₂.box.optIn z ιz (.step u .box))
      rw [Subst.optIn_ne θ₂.box ιz (fun h => by cases h)]
      change SubE.Sim T _ (((θ₂.at u).unbox).mono _)
      simp only [SubE.mono_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (SubE.mono L (((θ₂.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ₂ ιz)))
        (θ₂.box.optIn z ιz (.step u .keep))
      rw [Subst.optIn_ne θ₂.box ιz (fun h => by cases h)]
      change SubE.Sim T _ (((θ₂.at u).keepE).mono _)
      simp only [SubE.mono_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem WitE.tm_eq_of_sig {σ : Signature} {Δ : Ctx} {z : VarSymb} {A : VarType} {a a' : Ann A}
    {t : Term σ (Δ.optIn z) A a} {t' : Term σ (Δ.optIn z) A a'}
    (h : (⟨a, t⟩ : Σ c, Term σ (Δ.optIn z) A c) = ⟨a', t'⟩) : WitE.tm z t = WitE.tm z t' := by
  cases h
  rfl

namespace WitE

variable {σ : Signature} {ι₂ : VarSymb → VarSymb} {Δ₁ Δ₂ : Ctx}

/-- Push a witness entry over `Δ₁` through `θ₂`: a witness to its entry, a body substituted in the
    witness's view, its new name the index map's (as `SubE.comp`). -/
def comp (θ₂ : Subst σ Δ₂) (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) :
    WitE σ Δ₁ → WitE σ Δ₂
  | .hide => .hide
  | .ren z => θ₂.wit z
  | .tm z b =>
      if h : ModalSys.Opt = true ∧ (Δ₁.wit z).isSome = true then
        .tm (ι₂ z) (Term.subst ι₂ (θ₂.optIn z (ι₂ z))
          (Subst.ok_optIn hθ₂ h.1 (Option.some_get h.2).symm
            (hc₂.wit h.1 z _ (Option.some_get h.2).symm []))
          (Subst.coh_optIn hθ₂ hc₂ h.1 (Option.some_get h.2).symm) b)
      else .hide

variable (θ₂ : Subst σ Δ₂) (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂)

theorem comp_tm (hO : ModalSys.Opt = true) {z : VarSymb} {X : VarType} (hz : Δ₁.wit z = some X)
    {A : VarType} {a : Ann A} (b : Term σ (Δ₁.optIn z) A a) :
    (WitE.tm z b).comp θ₂ hθ₂ hc₂ = .tm (ι₂ z) (Term.subst ι₂ (θ₂.optIn z (ι₂ z))
      (Subst.ok_optIn hθ₂ hO hz (hc₂.wit hO z X hz [])) (Subst.coh_optIn hθ₂ hc₂ hO hz) b) :=
  dif_pos ⟨hO, by rw [hz]; rfl⟩

theorem idxAlong_comp (hO : ModalSys.Opt = true) : ∀ {e : WitE σ Δ₁} {X : VarType}, e.OkW X →
    (e.comp θ₂ hθ₂ hc₂).idxAlong [] = ι₂ (e.idxAlong [])
  | .ren z, X, he => hc₂.wit hO z X he []
  | .tm z b, _, he => by
      obtain ⟨Z, hZ⟩ := he.1
      rw [comp_tm θ₂ hθ₂ hc₂ hO hZ b]
      rfl
  | .hide, _, he => False.elim he

/-- Weakening before `θ₂'` is weakening after `θ₂`, when `θ₂'` is `θ₂` weakened (as
    `SubE.comp_mono`). -/
theorem comp_mono (hO : ModalSys.Opt = true) {Δ₁' Δ₂' : Ctx} (h : Δ₁.Le Δ₁') (h₂ : Δ₂.Le Δ₂')
    {ι₂' : VarSymb → VarSymb} (θ₂' : Subst σ Δ₂') (hθ₂' : Subst.Ok Δ₁' θ₂')
    (hc₂' : Subst.Coh ι₂' Δ₁' θ₂')
    (heq : ∀ w T, Δ₁.ref w = some T → θ₂'.at w = (θ₂.at w).mono h₂)
    (hweq : ∀ z X, Δ₁.wit z = some X → θ₂'.wit z = (θ₂.wit z).mono h₂) :
    ∀ {e : WitE σ Δ₁} {X : VarType}, e.OkW X →
      (e.mono h).comp θ₂' hθ₂' hc₂' = (e.comp θ₂ hθ₂ hc₂).mono h₂
  | .hide, _, _ => rfl
  | .ren z, X, he => hweq z X he
  | .tm z b, _, he => by
      obtain ⟨Z, hZ⟩ := he.1
      have hZ' : Δ₁'.wit z = some Z := h.wit z Z hZ
      have hι : ι₂' z = ι₂ z := by
        have h' := hc₂'.wit hO z Z hZ' []
        rw [hweq z Z hZ, WitE.idxAlong_mono, hc₂.wit hO z Z hZ []] at h'
        exact h'.symm
      change (WitE.tm z (Term.mono (h.optIn z) b)).comp θ₂' hθ₂' hc₂' = _
      rw [comp_tm θ₂' hθ₂' hc₂' hO hZ', comp_tm θ₂ hθ₂ hc₂ hO hZ b]
      have key : ∀ (z' : VarSymb) (_hz : z' = ι₂ z) (p : Subst.Ok (Δ₁'.optIn z) (θ₂'.optIn z z'))
          (q : Subst.Coh ι₂' (Δ₁'.optIn z) (θ₂'.optIn z z')),
          WitE.tm z' (Term.subst ι₂' (θ₂'.optIn z z') p q (Term.mono (h.optIn z) b)) =
            (WitE.tm (ι₂ z) (Term.subst ι₂ (θ₂.optIn z (ι₂ z))
              (Subst.ok_optIn hθ₂ hO hZ (hc₂.wit hO z Z hZ []))
              (Subst.coh_optIn hθ₂ hc₂ hO hZ) b)).mono h₂ := by
        intro z' hz p q
        subst hz
        change _ = WitE.tm (ι₂ z) (Term.mono (h₂.optIn (ι₂ z)) _)
        refine WitE.tm_eq_of_sig ?_
        rw [Term.subst_mono, Term.mono_subst]
        refine Term.subst_congr _ _ _ _ _ _ (Subst.simT_of fun v T hlp hv => ?_) b
        change SubE.Sim T (θ₂'.optIn z (ι₂ z) v) (SubE.mono (h₂.optIn (ι₂ z)) (θ₂.optIn z (ι₂ z) v))
        by_cases hc : v = .step z .dia
        · subst hc
          rw [Subst.optIn_content, Subst.optIn_content, hweq z Z hZ, ← WitE.optBody_mono]
          exact .refl _
        · rw [Ctx.optIn_ne hc] at hv
          rw [Subst.optIn_ne θ₂' _ hc, Subst.optIn_ne θ₂ _ hc, ← Subst.at_nonproj θ₂' hlp,
            heq v T ((Ctx.ref_nonproj Δ₁ hlp).trans hv), Subst.at_nonproj θ₂ hlp]
          simp only [SubE.mono_mono]
          exact .refl _
      exact key (ι₂' z) hι _ _

/-- The content of a re-opened witness, pushed through `θ₂`'s witness view, is the content of the
    pushed witness (as `SubE.diaBody_comp`). -/
theorem optBody_comp (hO : ModalSys.Opt = true) {x₁ : VarSymb} {X₁ : VarType}
    (hx₁ : Δ₁.wit x₁ = some X₁) :
    ∀ {e : WitE σ Δ₁} {X : VarType}, e.OkW X → e.idxAlong [] = x₁ →
      (e.optBody x₁).comp (θ₂.optIn x₁ (ι₂ x₁))
          (Subst.ok_optIn hθ₂ hO hx₁ (hc₂.wit hO x₁ X₁ hx₁ []))
          (Subst.coh_optIn hθ₂ hc₂ hO hx₁) =
        (e.comp θ₂ hθ₂ hc₂).optBody (ι₂ x₁)
  | .ren w, _, _, hwx => by
      have hwx' : w = x₁ := hwx
      subst hwx'
      change (θ₂.optIn w (ι₂ w)) (.step w .dia) = (θ₂.wit w).optBody (ι₂ w)
      exact Subst.optIn_content θ₂ w (ι₂ w)
  | .tm w b, _, _, hwx => by
      have hwx' : w = x₁ := hwx
      subst hwx'
      rw [show (WitE.tm w b : WitE σ Δ₁).optBody w = SubE.tm (Term.mono (Ctx.Le.refl _) b)
          from dif_pos rfl, Term.mono_refl, comp_tm θ₂ hθ₂ hc₂ hO hx₁ b,
        show (WitE.tm (ι₂ w) (Term.subst ι₂ (θ₂.optIn w (ι₂ w))
            (Subst.ok_optIn hθ₂ hO hx₁ (hc₂.wit hO w X₁ hx₁ []))
            (Subst.coh_optIn hθ₂ hc₂ hO hx₁) b) : WitE σ Δ₂).optBody (ι₂ w) =
          SubE.tm (Term.mono (Ctx.Le.refl _) (Term.subst ι₂ (θ₂.optIn w (ι₂ w))
            (Subst.ok_optIn hθ₂ hO hx₁ (hc₂.wit hO w X₁ hx₁ []))
            (Subst.coh_optIn hθ₂ hc₂ hO hx₁) b)) from dif_pos rfl, Term.mono_refl]
      rfl
  | .hide, _, he, _ => False.elim he

end WitE

/-- The witness entry of a pushed entry is the pushed witness entry, one view in. -/
theorem SubE.toWit_comp {σ : Signature} {ι₂ : VarSymb → VarSymb} {Δ₁ Δ₂ : Ctx}
    (θ₂ : Subst σ Δ₂) (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂)
    (hO : ModalSys.Opt = true) : ∀ {e : SubE σ Δ₁} {X : VarType}, e.OkRef (.VTypeDia X) →
      (e.comp θ₂ hθ₂ hc₂).toWit = e.toWit.comp θ₂.box (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂)
  | .ren _, _, _ => rfl
  | .tm (.diatm z hz b), _, _ => by
      obtain ⟨Z, hZ⟩ := hz
      have hw : (θ₂.at z).idxAlong [] = ι₂ z := hc₂ z _ hZ []
      obtain ⟨Y, hY⟩ := SubE.ref_witness (Subst.okRef_at hθ₂ hZ) hw
      have hzb : Δ₁.boxIn.wit z = some Z := Ctx.boxIn_wit.mpr ⟨hO, hZ⟩
      change SubE.toWit (SubE.tm (Term.diatm (ι₂ z) ⟨Y, hY⟩ (Term.subst ι₂ (θ₂.dia z (ι₂ z))
          (Subst.ok_dia hθ₂ ⟨Z, hZ⟩ hw) (Subst.coh_dia hθ₂ hc₂ ⟨Z, hZ⟩) b))) =
        WitE.comp θ₂.box (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂)
          (SubE.toWit (SubE.tm (Term.diatm z ⟨Z, hZ⟩ b)))
      rw [show SubE.toWit (SubE.tm (Term.diatm (ι₂ z) ⟨Y, hY⟩ (Term.subst ι₂ (θ₂.dia z (ι₂ z))
            (Subst.ok_dia hθ₂ ⟨Z, hZ⟩ hw) (Subst.coh_dia hθ₂ hc₂ ⟨Z, hZ⟩) b))) =
          WitE.tm (ι₂ z) (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY)
            (Term.subst ι₂ (θ₂.dia z (ι₂ z))
              (Subst.ok_dia hθ₂ ⟨Z, hZ⟩ hw) (Subst.coh_dia hθ₂ hc₂ ⟨Z, hZ⟩) b)) from dif_pos hO,
        show SubE.toWit (SubE.tm (Term.diatm z ⟨Z, hZ⟩ b)) =
          WitE.tm z (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hZ) b) from dif_pos hO,
        WitE.comp_tm θ₂.box (Subst.ok_box hθ₂) (Subst.coh_box hθ₂ hc₂) hO hzb]
      refine congrArg (WitE.tm (ι₂ z)) ?_
      rw [Term.mono_subst, Term.subst_mono]
      exact Term.subst_congr_eq _ _ _ _ _ _
        (Subst.simT_dia_box_optIn hθ₂ hO hZ (Ctx.le_diaIn_boxIn_optIn hO hY)) b
  | .tm (.var _ _), _, he => nomatch he
  | .tm (.func _), _, he => nomatch he
  | .tm .unit, _, he => nomatch he
  | .tm (.pair _ _), _, he => nomatch he
  | .tm (.boxtm _), _, he => nomatch he
  | .hide, _, he => False.elim he

namespace Subst

variable {σ : Signature} {ι₁ ι₂ ι₃ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx}

/-- The composite entries. -/
def comp (θ₁ : Subst σ Δ₁) (θ₂ : Subst σ Δ₂) (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂) :
    Subst σ Δ₂ where
  ty v := (θ₁ v).comp θ₂ hθ₂ hc₂
  wit y := (θ₁.wit y).comp θ₂ hθ₂ hc₂

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

/-- `θ₂`'s witness view agrees with `θ₂` on `Δ₁`: at an opened witness's content by `Coh.opened`. -/
theorem optIn_eq_mono (θ₂ : Subst σ Δ₂) (hc₂ : Coh ι₂ Δ₁ θ₂) (hO : ModalSys.Opt = true)
    {x₁ : VarSymb} {X₁ : VarType} (hx₁ : Δ₁.wit x₁ = some X₁) :
    ∀ v T, Δ₁.ref v = some T →
      (θ₂.optIn x₁ (ι₂ x₁)).at v = (θ₂.at v).mono (Ctx.le_optIn Δ₂ (ι₂ x₁)) :=
  at_eq_mono_of _ fun v T _ hv => by
    by_cases hc : v = .step x₁ .dia
    · subst hc
      rw [optIn_content]
      have hT : T = X₁ := by
        rcases Δ₁.wit_dia x₁ X₁ hx₁ with h | h
        · rw [h] at hv; cases hv
        · rw [h] at hv; exact (Option.some.inj hv).symm
      subst hT
      exact (hc₂.opened hO x₁ T (ι₂ x₁) hx₁ hv (hc₂.wit hO x₁ T hx₁ [])).symm
    · exact optIn_ne θ₂ _ hc

/-- The witness of a composite lands where the two index maps send it. -/
theorem idx_comp_wit {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁)
    (hc₁ : Coh ι₁ Γ θ₁) (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂) (hc₃ : Coh ι₃ Γ θ₃)
    (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType}
    (hy : Γ.wit y = some X) : ι₃ y = ι₂ (ι₁ y) :=
  calc ι₃ y = (θ₃.wit y).idxAlong [] := (hc₃.wit hO y X hy []).symm
    _ = ((θ₁.wit y).comp θ₂ hθ₂ hc₂).idxAlong [] := (hs.wit hO y X hy).idx
    _ = ι₂ ((θ₁.wit y).idxAlong []) := WitE.idxAlong_comp θ₂ hθ₂ hc₂ hO (hθ₁.wit hO y X hy)
    _ = ι₂ (ι₁ y) := by rw [hc₁.wit hO y X hy []]; rfl

theorem idx_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁) (hc₁ : Coh ι₁ Γ θ₁)
    (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂) (hc₃ : Coh ι₃ Γ θ₃)
    (hs : SimT Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
    ι₃ x = ι₂ (ι₁ x) := by
  obtain ⟨X, hX⟩ := hx
  have h₃ : (θ₃.at x).idxAlong [] = ι₃ x := hc₃ x _ hX []
  have h₁ : (θ₁.at x).idxAlong [] = ι₁ x := hc₁ x _ hX []
  rw [← h₃, (hs x _ hX).idx, at_comp hθ₁ θ₂ hθ₂ hc₂ hX,
    SubE.idxAlong_comp θ₂ hθ₂ hc₂ (okRef_at hθ₁ hX), h₁]

theorem simT_box_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁) (hθ₂ : Ok Δ₁ θ₂)
    (hc₂ : Coh ι₂ Δ₁ θ₂) (hs : SimT Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
    SimT Γ.boxIn θ₃.box (θ₁.box.comp θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂)) := by
  refine simT_of ?_
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

theorem sim_box_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁) (hθ₂ : Ok Δ₁ θ₂)
    (hc₂ : Coh ι₂ Δ₁ θ₂) (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
    Sim Γ.boxIn θ₃.box (θ₁.box.comp θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂)) := by
  refine ⟨simT_box_comp hθ₁ hθ₂ hc₂ hs.ty, fun hO y X hy => ?_⟩
  obtain ⟨_, hu⟩ := Ctx.boxIn_wit.mp hy
  change WitE.Sim X (θ₃.at y).toWit
    (((θ₁.at y).toWit).comp θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂))
  rw [← SubE.toWit_comp θ₂ hθ₂ hc₂ hO (okRef_at hθ₁ hu), ← at_comp hθ₁ θ₂ hθ₂ hc₂ hu]
  exact (hs y _ hu).toWit hO

theorem simT_dia_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁)
    (hc₁ : Coh ι₁ Γ θ₁) (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂)
    (hs : SimT Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hx₁ : ∃ X, Δ₁.ref (ι₁ x) = some (.VTypeDia X))
    (hw₂ : (θ₂.at (ι₁ x)).idxAlong [] = ι₂ (ι₁ x))
    (hw₃ : (θ₃.at x).idxAlong [] = ι₂ (ι₁ x)) :
    SimT (Γ.diaIn x) (θ₃.dia x (ι₂ (ι₁ x)))
      ((θ₁.dia x (ι₁ x)).comp (θ₂.dia (ι₁ x) (ι₂ (ι₁ x))) (ok_dia hθ₂ hx₁ hw₂)
        (coh_dia hθ₂ hc₂ hx₁)) := by
  have hw₁ : (θ₁.at x).idxAlong [] = ι₁ x := hx.elim fun _ hX => hc₁ x _ hX []
  refine simT_of ?_
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
  refine ⟨simT_dia_comp hθ₁ hc₁ hθ₂ hc₂ hs.ty hx hx₁ hw₂ hw₃, fun hO y X hy => ?_⟩
  obtain ⟨_, hu⟩ := Ctx.boxIn_wit.mp hy
  change WitE.Sim X (((θ₃.at y).toWit).mono (Ctx.le_boxIn_diaIn Δ₂ (ι₂ (ι₁ x))))
    ((((θ₁.at y).toWit).mono (Ctx.le_boxIn_diaIn Δ₁ (ι₁ x))).comp
      (θ₂.dia (ι₁ x) (ι₂ (ι₁ x))) (ok_dia hθ₂ hx₁ hw₂) (coh_dia hθ₂ hc₂ hx₁))
  rw [WitE.comp_mono θ₂.box (ok_box hθ₂) (coh_box hθ₂ hc₂) hO (Ctx.le_boxIn_diaIn Δ₁ (ι₁ x))
      (Ctx.le_boxIn_diaIn Δ₂ (ι₂ (ι₁ x))) _ _ _ (dia_eq_box_mono θ₂ (ι₁ x) (ι₂ (ι₁ x)))
      (fun _ _ _ => rfl) (SubE.okW_toWit hO (okRef_at hθ₁ hu)),
    ← SubE.toWit_comp θ₂ hθ₂ hc₂ hO (okRef_at hθ₁ hu), ← at_comp hθ₁ θ₂ hθ₂ hc₂ hu]
  exact ((hs y _ hu).toWit hO).mono _

theorem sim_under_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁) (hθ₂ : Ok Δ₁ θ₂)
    (hc₂ : Coh ι₂ Δ₁ θ₂) (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) {d d₁ d₂ : ℕ}
    (hΔ₁ : Δ₁.SlotsFrom d₁) (T : VarType) (h₁ : Δ₁ (.root (.bnd d₁)) = none)
    (h₂ : Δ₂ (.root (.bnd d₂)) = none) :
    Sim (Γ.insert (.bnd d) T) (θ₃.under d d₂ T h₂)
      ((θ₁.under d d₁ T h₁).comp (θ₂.under d₁ d₂ T h₂) (ok_under hθ₂ T h₂)
        (coh_under hθ₂ hc₂ hΔ₁ T h₂)) := by
  refine sim_of ?_ fun hO y X hy => ?_
  swap
  · change Γ.wit y = some X at hy
    change WitE.Sim X ((θ₃.wit y).mono (Ctx.le_insert h₂ T))
      (((θ₁.wit y).mono (Ctx.le_insert h₁ T)).comp (θ₂.under d₁ d₂ T h₂) (ok_under hθ₂ T h₂)
        (coh_under hθ₂ hc₂ hΔ₁ T h₂))
    rw [WitE.comp_mono θ₂ hθ₂ hc₂ hO (Ctx.le_insert h₁ T) (Ctx.le_insert h₂ T) _ _ _
      (under_eq_mono θ₂ hΔ₁ T h₂) (fun _ _ _ => rfl) (hθ₁.wit hO y X hy)]
    exact (hs.wit hO y X hy).mono _
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · rw [show θ₃.under d d₂ T h₂ v = .ren (.root (.bnd d₂)) from if_pos hvr]
    change SubE.Sim U _ ((θ₁.under d d₁ T h₁ v).comp _ _ _)
    rw [show θ₁.under d d₁ T h₁ v = .ren (.root (.bnd d₁)) from if_pos hvr]
    change SubE.Sim U _ ((θ₂.under d₁ d₂ T h₂) (.root (.bnd d₁)))
    rw [show θ₂.under d₁ d₂ T h₂ (.root (.bnd d₁)) = .ren (.root (.bnd d₂)) from if_pos rfl]
    exact .refl _
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
    rw [show θ₃.under d d₂ T h₂ v = (θ₃ v).mono (Ctx.le_insert h₂ T) from if_neg hvr]
    change SubE.Sim U _ ((θ₁.under d d₁ T h₁ v).comp _ _ _)
    rw [show θ₁.under d d₁ T h₁ v = (θ₁ v).mono (Ctx.le_insert h₁ T) from if_neg hvr,
      SubE.comp_mono θ₂ hθ₂ hc₂ (Ctx.le_insert h₁ T) (Ctx.le_insert h₂ T) _ _ _
        (under_eq_mono θ₂ hΔ₁ T h₂) (hθ₁ v U hlp hv')]
    have h₃ := hs v U ((Ctx.ref_nonproj Γ hlp).trans hv')
    rw [at_nonproj θ₃ hlp, at_nonproj _ hlp] at h₃
    exact h₃.mono _

theorem sim_optIn_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁)
    (hc₁ : Coh ι₁ Γ θ₁) (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂)
    (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType}
    (hy : Γ.wit y = some X) {X₁ : VarType} (hx₁ : Δ₁.wit (ι₁ y) = some X₁)
    (hw₃ : (θ₃.wit y).idxAlong [] = ι₂ (ι₁ y)) :
    Sim (Γ.optIn y) (θ₃.optIn y (ι₂ (ι₁ y)))
      ((θ₁.optIn y (ι₁ y)).comp (θ₂.optIn (ι₁ y) (ι₂ (ι₁ y)))
        (ok_optIn hθ₂ hO hx₁ (hc₂.wit hO _ X₁ hx₁ [])) (coh_optIn hθ₂ hc₂ hO hx₁)) := by
  have hw₁ : (θ₁.wit y).idxAlong [] = ι₁ y := hc₁.wit hO y X hy []
  refine sim_of ?_ fun hO' y' X' hy' => ?_
  swap
  · change WitE.Sim X' ((θ₃.wit y').mono (Ctx.le_optIn Δ₂ (ι₂ (ι₁ y))))
      (((θ₁.wit y').mono (Ctx.le_optIn Δ₁ (ι₁ y))).comp (θ₂.optIn (ι₁ y) (ι₂ (ι₁ y)))
        (ok_optIn hθ₂ hO hx₁ (hc₂.wit hO _ X₁ hx₁ [])) (coh_optIn hθ₂ hc₂ hO hx₁))
    rw [WitE.comp_mono θ₂ hθ₂ hc₂ hO' (Ctx.le_optIn Δ₁ (ι₁ y)) (Ctx.le_optIn Δ₂ (ι₂ (ι₁ y)))
      _ _ _ (optIn_eq_mono θ₂ hc₂ hO hx₁) (fun _ _ _ => rfl) (hθ₁.wit hO' y' X' hy')]
    exact (hs.wit hO' y' X' hy').mono _
  intro v U hlp hv
  by_cases hc : v = .step y .dia
  · subst hc
    rw [Ctx.optIn_content hy] at hv
    cases hv
    change SubE.Sim X (θ₃.optIn y (ι₂ (ι₁ y)) (.step y .dia))
      ((θ₁.optIn y (ι₁ y) (.step y .dia)).comp (θ₂.optIn (ι₁ y) (ι₂ (ι₁ y)))
        (ok_optIn hθ₂ hO hx₁ (hc₂.wit hO _ X₁ hx₁ [])) (coh_optIn hθ₂ hc₂ hO hx₁))
    rw [optIn_content, optIn_content,
      WitE.optBody_comp θ₂ hθ₂ hc₂ hO hx₁ (hθ₁.wit hO y X hy) hw₁]
    exact (hs.wit hO y X hy).optBody hw₃
  · rw [Ctx.optIn_ne hc] at hv
    change SubE.Sim U (θ₃.optIn y (ι₂ (ι₁ y)) v)
      ((θ₁.optIn y (ι₁ y) v).comp (θ₂.optIn (ι₁ y) (ι₂ (ι₁ y)))
        (ok_optIn hθ₂ hO hx₁ (hc₂.wit hO _ X₁ hx₁ [])) (coh_optIn hθ₂ hc₂ hO hx₁))
    rw [optIn_ne θ₃ _ hc, optIn_ne θ₁ _ hc,
      SubE.comp_mono θ₂ hθ₂ hc₂ (Ctx.le_optIn Δ₁ (ι₁ y)) (Ctx.le_optIn Δ₂ (ι₂ (ι₁ y))) _ _ _
        (optIn_eq_mono θ₂ hc₂ hO hx₁) (hθ₁ v U hlp hv)]
    have h₃ := hs v U ((Ctx.ref_nonproj Γ hlp).trans hv)
    rw [at_nonproj θ₃ hlp, at_nonproj _ hlp] at h₃
    exact h₃.mono _

theorem sim_optInT_comp {θ₁ : Subst σ Δ₁} {θ₂ θ₃ : Subst σ Δ₂} (hθ₁ : Ok Γ θ₁)
    (hc₁ : Coh ι₁ Γ θ₁) (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂)
    (hs : Sim Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X)
    {X₁ : VarType} (hx₁ : Δ₁.witT (ι₁ y) = some X₁)
    (hw₂ : (θ₂.at (ι₁ y)).idxAlong [] = ι₂ (ι₁ y))
    (hw₃ : (θ₃.at y).idxAlong [] = ι₂ (ι₁ y)) :
    Sim (Γ.optInT y) (θ₃.optInT y (ι₂ (ι₁ y)))
      ((θ₁.optInT y (ι₁ y)).comp (θ₂.optInT (ι₁ y) (ι₂ (ι₁ y)))
        (ok_optInT hθ₂ hx₁ hw₂) (coh_optInT hθ₂ hc₂ hx₁)) := by
  obtain ⟨hT, hO, hr⟩ := Ctx.witT_spec hy
  have hw₁ : (θ₁.at y).idxAlong [] = ι₁ y := hc₁ y _ hr []
  have heq : ∀ v T, Δ₁.ref v = some T →
      (θ₂.optInT (ι₁ y) (ι₂ (ι₁ y))).at v = (θ₂.at v).mono (Ctx.le_optInT Δ₂ (ι₂ (ι₁ y))) :=
    fun v T hv => at_optInT_of hc₂ hx₁ hw₂ v T hv
  refine sim_of ?_ fun hO' y' X' hy' => ?_
  swap
  · change WitE.Sim X' ((θ₃.wit y').mono (Ctx.le_optInT Δ₂ (ι₂ (ι₁ y))))
      (((θ₁.wit y').mono (Ctx.le_optInT Δ₁ (ι₁ y))).comp (θ₂.optInT (ι₁ y) (ι₂ (ι₁ y)))
        (ok_optInT hθ₂ hx₁ hw₂) (coh_optInT hθ₂ hc₂ hx₁))
    rw [WitE.comp_mono θ₂ hθ₂ hc₂ hO' (Ctx.le_optInT Δ₁ (ι₁ y)) (Ctx.le_optInT Δ₂ (ι₂ (ι₁ y)))
      _ _ _ heq (fun _ _ _ => rfl) (hθ₁.wit hO' y' X' hy')]
    exact (hs.wit hO' y' X' hy').mono _
  intro v U hlp hv
  by_cases hc : v = .step y .at
  · subst hc
    rw [Ctx.optInT_content hy] at hv
    cases hv
    change SubE.Sim _ (θ₃.optInT y (ι₂ (ι₁ y)) (.step y .at))
      ((θ₁.optInT y (ι₁ y) (.step y .at)).comp (θ₂.optInT (ι₁ y) (ι₂ (ι₁ y)))
        (ok_optInT hθ₂ hx₁ hw₂) (coh_optInT hθ₂ hc₂ hx₁))
    rw [optInT_content, optInT_content,
      SubE.atBody_comp hT hO θ₂ hθ₂ hc₂ hx₁ hw₂ (okRef_at hθ₁ hr) hw₁,
      ← at_comp hθ₁ θ₂ hθ₂ hc₂ hr]
    exact (hs y _ hr).atBody hT hO hw₃
  · rw [Ctx.optInT_ne hc] at hv
    change SubE.Sim U (θ₃.optInT y (ι₂ (ι₁ y)) v)
      ((θ₁.optInT y (ι₁ y) v).comp (θ₂.optInT (ι₁ y) (ι₂ (ι₁ y)))
        (ok_optInT hθ₂ hx₁ hw₂) (coh_optInT hθ₂ hc₂ hx₁))
    rw [optInT_ne θ₃ _ hc, optInT_ne θ₁ _ hc,
      SubE.comp_mono θ₂ hθ₂ hc₂ (Ctx.le_optInT Δ₁ (ι₁ y)) (Ctx.le_optInT Δ₂ (ι₂ (ι₁ y))) _ _ _
        heq (hθ₁ v U hlp hv)]
    have h₃ := hs v U ((Ctx.ref_nonproj Γ hlp).trans hv)
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
      (hc₃ : Subst.Coh ι₃ Γ θ₃) (hs : Subst.SimT Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
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
      (hc₃ : Subst.Coh ι₃ Γ θ₃) (hs : Subst.SimT Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
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
          (Subst.coh_box hθ₃ hc₃) (Subst.simT_box_comp hθ₁ hθ₂ hc₂ hs) t)
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
            (Subst.simT_dia_comp hθ₁ hc₁ hθ₂ hc₂ hs hx hx₁ hw₂ hw₃) t)
        exact key (ι₃ x) hι _ _ _
    termination_by structural _ _ t => t
end

theorem Term.subst_comp {σ : Signature} {ι₁ ι₂ ι₃ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx}
    (θ₁ : Subst σ Δ₁) (θ₂ θ₃ : Subst σ Δ₂) (hθ₁ : Subst.Ok Γ θ₁) (hc₁ : Subst.Coh ι₁ Γ θ₁)
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) (hθ₃ : Subst.Ok Γ θ₃)
    (hc₃ : Subst.Coh ι₃ Γ θ₃) (hs : Subst.SimT Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂))
    (t : Term σ Γ .Var .var) :
    Term.subst ι₂ θ₂ hθ₂ hc₂ (Term.subst ι₁ θ₁ hθ₁ hc₁ t) = Term.subst ι₃ θ₃ hθ₃ hc₃ t :=
  eq_of_heq (Sigma.mk.inj (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)).2

theorem Rel.subst_comp {σ : Signature} {ι₁ ι₂ ι₃ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx}
    (θ₁ : Subst σ Δ₁) (θ₂ θ₃ : Subst σ Δ₂) (hθ₁ : Subst.Ok Γ θ₁) (hc₁ : Subst.Coh ι₁ Γ θ₁)
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) (hθ₃ : Subst.Ok Γ θ₃)
    (hc₃ : Subst.Coh ι₃ Γ θ₃) (hs : Subst.SimT Γ θ₃ (θ₁.comp θ₂ hθ₂ hc₂)) :
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
  | ι₁, ι₂, ι₃, Γ, Δ₁, Δ₂, _, _, d₂, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂,
      hs, .optx hO .arrow y hy φ => by
      obtain ⟨X, hX⟩ := hy
      have hw₁ : (θ₁.wit y).idxAlong [] = ι₁ y := hc₁.wit hO y X hX []
      obtain ⟨X₁, hx₁⟩ := WitE.wit_of (hθ₁.wit hO y X hX) hw₁
      have hw₂ : (θ₂.wit (ι₁ y)).idxAlong [] = ι₂ (ι₁ y) := hc₂.wit hO _ X₁ hx₁ []
      have hι : ι₃ y = ι₂ (ι₁ y) := Subst.idx_comp_wit hθ₁ hc₁ hθ₂ hc₂ hc₃ hs hO hX
      have hw₃ : (θ₃.wit y).idxAlong [] = ι₂ (ι₁ y) := (hc₃.wit hO y X hX []).trans hι
      have key : ∀ (z : VarSymb) (_hz : z = ι₂ (ι₁ y)) (P : ∃ Z, Δ₂.wit z = some Z)
          (p : Subst.Ok (Γ.optIn y) (θ₃.optIn y z)) (q : Subst.Coh ι₃ (Γ.optIn y) (θ₃.optIn y z))
          (hΔz : (Δ₂.optIn z).SlotsFrom d₂),
          WFF.subst ι₂ θ₂ hθ₂ hc₂ hΔ₁ hΔ₂
              (WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ hΔ₁ (.optx hO .arrow y ⟨X, hX⟩ φ)) =
            .optx hO .arrow z P (WFF.subst ι₃ (θ₃.optIn y z) p q (hΓ.optIn y) hΔz φ) := by
        intro z hz P p q hΔz
        subst hz
        exact congrArg (WFF.optx hO .arrow (ι₂ (ι₁ y)) _) (WFF.subst_comp (θ₁.optIn y (ι₁ y))
          (θ₂.optIn (ι₁ y) (ι₂ (ι₁ y))) (θ₃.optIn y (ι₂ (ι₁ y))) (Subst.ok_optIn hθ₁ hO hX hw₁)
          (Subst.coh_optIn hθ₁ hc₁ hO hX) (Subst.ok_optIn hθ₂ hO hx₁ hw₂)
          (Subst.coh_optIn hθ₂ hc₂ hO hx₁) p q (hΓ.optIn y) (hΔ₁.optIn (ι₁ y)) hΔz
          (Subst.sim_optIn_comp hθ₁ hc₁ hθ₂ hc₂ hs hO hX hx₁ hw₃) φ)
      exact key (ι₃ y) hι _ _ _ _
  | ι₁, ι₂, ι₃, Γ, Δ₁, Δ₂, _, _, d₂, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂,
      hs, .optx hO .ident y hy φ => by
      obtain ⟨X, hX⟩ := hy
      obtain ⟨hT, -, hr⟩ := Ctx.witT_spec hX
      have hw₁ : (θ₁.at y).idxAlong [] = ι₁ y := hc₁ y _ hr []
      obtain ⟨X₁, hr₁⟩ := SubE.ref_witness (Subst.okRef_at hθ₁ hr) hw₁
      have hx₁ : Δ₁.witT (ι₁ y) = some X₁ := Ctx.witT_of hT hO hr₁
      have hw₂ : (θ₂.at (ι₁ y)).idxAlong [] = ι₂ (ι₁ y) := hc₂ _ _ hr₁ []
      have hι : ι₃ y = ι₂ (ι₁ y) := Subst.idx_comp hθ₁ hc₁ hθ₂ hc₂ hc₃ hs.ty ⟨X, hr⟩
      have hw₃ : (θ₃.at y).idxAlong [] = ι₂ (ι₁ y) := (hc₃ y _ hr []).trans hι
      have key : ∀ (z : VarSymb) (_hz : z = ι₂ (ι₁ y)) (P : ∃ Z, Δ₂.witT z = some Z)
          (p : Subst.Ok (Γ.optInT y) (θ₃.optInT y z))
          (q : Subst.Coh ι₃ (Γ.optInT y) (θ₃.optInT y z)) (hΔz : (Δ₂.optInT z).SlotsFrom d₂),
          WFF.subst ι₂ θ₂ hθ₂ hc₂ hΔ₁ hΔ₂
              (WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ hΔ₁ (.optx hO .ident y ⟨X, hX⟩ φ)) =
            .optx hO .ident z P (WFF.subst ι₃ (θ₃.optInT y z) p q (hΓ.optInT y) hΔz φ) := by
        intro z hz P p q hΔz
        subst hz
        exact congrArg (WFF.optx hO .ident (ι₂ (ι₁ y)) _) (WFF.subst_comp (θ₁.optInT y (ι₁ y))
          (θ₂.optInT (ι₁ y) (ι₂ (ι₁ y))) (θ₃.optInT y (ι₂ (ι₁ y))) (Subst.ok_optInT hθ₁ hX hw₁)
          (Subst.coh_optInT hθ₁ hc₁ hX) (Subst.ok_optInT hθ₂ hx₁ hw₂)
          (Subst.coh_optInT hθ₂ hc₂ hx₁) p q (hΓ.optInT y) (hΔ₁.optInT (ι₁ y)) hΔz
          (Subst.sim_optInT_comp hθ₁ hc₁ hθ₂ hc₂ hs hX hx₁ hw₂ hw₃) φ)
      exact key (ι₃ y) hι _ _ _ _
  | _, _, _, _, _, _, _, _, _, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, _, _, _, hs,
      .here hT s t hO =>
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
  | _, _, _, _, _, _, d, d₁, d₂, θ₁, θ₂, θ₃, hθ₁, hc₁, hθ₂, hc₂, hθ₃, hc₃, hΓ, hΔ₁, hΔ₂, hs,
      .link hV hF t Φ =>
      WFF.link_congr hV hF (Term.subst_comp_sig θ₁ θ₂ θ₃ hθ₁ hc₁ hθ₂ hc₂ hθ₃ hc₃ hs t)
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
      hs, .linkx hV hF y hy (D := D) t Φ => by
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
          (p : Subst.Ok ((Γ.diaIn y).insert (.bnd d) D.ty)
            ((θ₃.dia y z).under d d₂ _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot ι₃ d d₂) ((Γ.diaIn y).insert (.bnd d) D.ty)
            ((θ₃.dia y z).under d d₂ _ hΔz.root)),
          WFF.subst ι₂ θ₂ hθ₂ hc₂ hΔ₁ hΔ₂ (WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ hΔ₁ (.linkx hV hF y hy t Φ)) =
            .linkx hV hF z P (Term.subst ι₃ θ₃ hθ₃ hc₃ t)
              (WFF.subst (VarSymb.shiftSlot ι₃ d d₂) ((θ₃.dia y z).under d d₂ _ hΔz.root) p q
                ((hΓ.diaIn y).insert _) (hΔz.insert _) Φ) := by
        intro z hz P hΔz p q
        subst hz
        exact WFF.linkx_congr hV hF _ _
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
