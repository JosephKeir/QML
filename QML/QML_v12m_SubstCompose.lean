import QML.QML_v12m_SubstComp

/-!
# QML v12m — weakening substituted formulas

* `mono_subst`: weakening a substituted formula is substituting the weakened entries.
-/

namespace V12M

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ Δ' : Ctx}

/-- Weaken every entry. -/
def mono (θ : Subst σ Δ) (h : Δ.Le Δ') : Subst σ Δ' := fun v => (θ v).mono h

theorem at_mono (θ : Subst σ Δ) (h : Δ.Le Δ') : ∀ v, (θ.mono h).at v = (θ.at v).mono h
  | .root _ => rfl
  | .step v s => by
      change (if s.isProj then ((θ.mono h).at v).proj s else (θ.mono h) (.step v s)) =
        SubE.mono h (if s.isProj then (θ.at v).proj s else θ (.step v s))
      rw [at_mono θ h v]
      split_ifs
      · exact SubE.proj_mono h _ s
      · rfl

theorem ok_mono {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) (h : Δ.Le Δ') : Ok Γ (θ.mono h) :=
  fun v T hlp hv => SubE.okRef_mono h (hθ v T hlp hv)

theorem coh_mono {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hc : Coh ι Γ θ)
    (h : Δ.Le Δ') : Coh ι Γ (θ.mono h) := fun v T hv p => by
  rw [at_mono, SubE.idxAlong_mono]
  exact hc v T hv p

theorem sim_box_mono {Γ : Ctx} (θ : Subst σ Δ) (h : Δ.Le Δ') :
    Sim Γ.boxIn (θ.box.mono h.boxIn) ((θ.mono h).box) := by
  refine sim_of ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      change SubE.Sim T (((θ.at u).unbox).mono h.boxIn) ((θ.mono h).at u).unbox
      rw [at_mono, SubE.unbox_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (((θ.at u).keepE).mono h.boxIn) ((θ.mono h).at u).keepE
      rw [at_mono, SubE.keepE_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem sim_dia_mono {Γ : Ctx} (θ : Subst σ Δ) (h : Δ.Le Δ') (x ιx : VarSymb) :
    Sim (Γ.diaIn x) ((θ.dia x ιx).mono (h.diaIn ιx)) ((θ.mono h).dia x ιx) := by
  refine sim_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change SubE.Sim T (SubE.mono (h.diaIn ιx) (if u = x then (θ.at x).diaBody ιx else SubE.hide))
        (if u = x then ((θ.mono h).at x).diaBody ιx else SubE.hide)
      by_cases hux : u = x
      · rw [if_pos hux, if_pos hux, at_mono, SubE.diaBody_mono]
        exact .refl _
      · rw [if_neg hux, if_neg hux]
        exact .refl _
  | .step u .box =>
      change SubE.Sim T (SubE.mono (h.diaIn ιx) (((θ.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ ιx)))
        ((((θ.mono h).at u).unbox).mono (Ctx.le_boxIn_diaIn Δ' ιx))
      rw [at_mono, SubE.unbox_mono, SubE.mono_mono, SubE.mono_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (SubE.mono (h.diaIn ιx) (((θ.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ ιx)))
        ((((θ.mono h).at u).keepE).mono (Ctx.le_boxIn_diaIn Δ' ιx))
      rw [at_mono, SubE.keepE_mono, SubE.mono_mono, SubE.mono_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem sim_under_mono {Γ : Ctx} (θ : Subst σ Δ) (h : Δ.Le Δ') {d d' : ℕ} (T : VarType)
    (h₀ : Δ (.root (.bnd d')) = none) (h₁ : Δ' (.root (.bnd d')) = none) :
    Sim (Γ.insert (.bnd d) T) ((θ.under d d' T h₀).mono (h.insert _ T))
      ((θ.mono h).under d d' T h₁) := by
  refine sim_of ?_
  intro v U _ _
  change SubE.Sim U (SubE.mono _ (θ.under d d' T h₀ v)) _
  by_cases hvr : v = .root (.bnd d)
  · rw [show (θ.mono h).under d d' T h₁ v = .ren (.root (.bnd d')) from if_pos hvr,
      show θ.under d d' T h₀ v = .ren (.root (.bnd d')) from if_pos hvr]
    exact .refl _
  · rw [show (θ.mono h).under d d' T h₁ v = ((θ v).mono h).mono (Ctx.le_insert h₁ T) from
        if_neg hvr,
      show θ.under d d' T h₀ v = (θ v).mono (Ctx.le_insert h₀ T) from if_neg hvr,
      SubE.mono_mono, SubE.mono_mono]
    exact .refl _

end Subst

/-! ## Weakening a substituted formula -/

theorem SubE.toVar_congr {σ : Signature} {Δ : Ctx} {e e' : SubE σ Δ} (he : e = e')
    (h : e.OkRef .Var) (h' : e'.OkRef .Var) : e.toVar h = e'.toVar h' := by
  subst he
  rfl

theorem SubE.toVar_mono {σ : Signature} {Δ Δ' : Ctx} (hle : Δ.Le Δ') :
    ∀ (e : SubE σ Δ) (h : e.OkRef .Var),
      Term.mono hle (e.toVar h) = (e.mono hle).toVar (SubE.okRef_mono hle h)
  | .ren _, _ => rfl
  | .tm (.var _ _), _ => rfl
  | .tm (.func _), _ => rfl
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _), h => nomatch h
  | .tm (.diatm _ _ _), h => nomatch h
  | .hide, h => False.elim h

/-- Congruence with one annotation map: an equation of terms. -/
theorem Term.subst_congr_eq {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx}
    (θ θ' : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
    (hc' : Subst.Coh ι Γ θ') (hs : Subst.Sim Γ θ θ') {T : VarType} {a : Ann T}
    (t : Term σ Γ T a) : Term.subst ι θ hθ hc t = Term.subst ι θ' hθ' hc' t :=
  eq_of_heq (Sigma.mk.inj (Term.subst_congr θ θ' hθ hθ' hc hc' hs t)).2

mutual
  theorem Func.mono_subst {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ Δ' : Ctx}
      (h : Δ.Le Δ') (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
      {n : ℕ} → (f : Func σ Γ n) →
      Func.mono h (Func.subst ι θ hθ hc f) =
        Func.subst ι (θ.mono h) (Subst.ok_mono hθ h) (Subst.coh_mono hc h) f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.mono h (Func.subst ι θ hθ hc g))
          (Term.mono h (Term.subst ι θ hθ hc t)) = _
        rw [Func.mono_subst h θ hθ hc g, Term.mono_subst h θ hθ hc t]
        rfl
    termination_by structural _ f => f

  theorem Term.mono_subst {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ Δ' : Ctx}
      (h : Δ.Le Δ') (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      Term.mono h (Term.subst ι θ hθ hc t) =
        Term.subst ι (θ.mono h) (Subst.ok_mono hθ h) (Subst.coh_mono hc h) t
    | _, _, .var v _ =>
        (SubE.toVar_mono h _ _).trans (SubE.toVar_congr (Subst.at_mono θ h v).symm _ _)
    | _, _, .func f => by
        change Term.func (Func.mono h (Func.subst ι θ hθ hc f)) = _
        rw [Func.mono_subst h θ hθ hc f]
        rfl
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change Term.pair (Term.mono h (Term.subst ι θ hθ hc s))
          (Term.mono h (Term.subst ι θ hθ hc t)) = _
        rw [Term.mono_subst h θ hθ hc s, Term.mono_subst h θ hθ hc t]
        rfl
    | _, _, .boxtm t => by
        change Term.boxtm (Term.mono h.boxIn
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) t)) = _
        rw [Term.mono_subst h.boxIn θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) t]
        exact congrArg Term.boxtm (Term.subst_congr_eq _ _
          (Subst.ok_mono (Subst.ok_box hθ) h.boxIn) (Subst.ok_box (Subst.ok_mono hθ h))
          (Subst.coh_mono (Subst.coh_box hθ hc) h.boxIn)
          (Subst.coh_box (Subst.ok_mono hθ h) (Subst.coh_mono hc h)) (Subst.sim_box_mono θ h) t)
    | _, _, .diatm x hx t => by
        have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
        have hw' : ((θ.mono h).at x).idxAlong [] = ι x :=
          hx.elim fun _ hX => Subst.coh_mono hc h x _ hX []
        change Term.diatm (ι x) _ (Term.mono (h.diaIn (ι x))
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) t)) = _
        rw [Term.mono_subst (h.diaIn (ι x)) (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw)
          (Subst.coh_dia hθ hc hx) t]
        exact congrArg (Term.diatm (ι x) _) (Term.subst_congr_eq _ _
          (Subst.ok_mono (Subst.ok_dia hθ hx hw) (h.diaIn (ι x)))
          (Subst.ok_dia (Subst.ok_mono hθ h) hx hw')
          (Subst.coh_mono (Subst.coh_dia hθ hc hx) (h.diaIn (ι x)))
          (Subst.coh_dia (Subst.ok_mono hθ h) (Subst.coh_mono hc h) hx)
          (Subst.sim_dia_mono θ h x (ι x)) t)
    termination_by structural _ _ t => t
end

theorem Rel.mono_subst {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ Δ' : Ctx}
    (h : Δ.Le Δ') (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
    {n : ℕ} → (ρ : Rel σ Γ n) →
    Rel.mono h (Rel.subst ι θ hθ hc ρ) =
      Rel.subst ι (θ.mono h) (Subst.ok_mono hθ h) (Subst.coh_mono hc h) ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.mono h (Rel.subst ι θ hθ hc ρ))
        (Term.mono h (Term.subst ι θ hθ hc t)) = _
      rw [Rel.mono_subst h θ hθ hc ρ, Term.mono_subst h θ hθ hc t]
      rfl

theorem WFF.mono_subst {σ : Signature} : {ι : VarSymb → VarSymb} → {Γ Δ Δ' : Ctx} →
    {d d' : ℕ} → (h : Δ.Le Δ') → (θ : Subst σ Δ) → (hθ : Subst.Ok Γ θ) →
    (hc : Subst.Coh ι Γ θ) → (hΓ : Γ.SlotsFrom d) → (hΔ : Δ.SlotsFrom d') →
    (hΔ' : Δ'.SlotsFrom d') → (φ : WFF σ Γ d) →
    WFF.mono h (WFF.subst ι θ hθ hc hΓ hΔ φ) =
      WFF.subst ι (θ.mono h) (Subst.ok_mono hθ h) (Subst.coh_mono hc h) hΓ hΔ' φ
  | _, _, _, _, _, _, h, θ, hθ, hc, _, _, _, .atom ρ =>
      congrArg WFF.atom (Rel.mono_subst h θ hθ hc ρ)
  | _, _, _, _, _, _, h, θ, hθ, hc, _, _, _, .eq t s =>
      congrArg₂ WFF.eq (Term.mono_subst h θ hθ hc t) (Term.mono_subst h θ hθ hc s)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΔ, hΔ', .and φ ψ =>
      congrArg₂ WFF.and (WFF.mono_subst h θ hθ hc hΓ hΔ hΔ' φ)
        (WFF.mono_subst h θ hθ hc hΓ hΔ hΔ' ψ)
  | _, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΔ, hΔ', .or φ ψ =>
      congrArg₂ WFF.or (WFF.mono_subst h θ hθ hc hΓ hΔ hΔ' φ)
        (WFF.mono_subst h θ hθ hc hΓ hΔ hΔ' ψ)
  | _, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΔ, hΔ', .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.mono_subst h θ hθ hc hΓ hΔ hΔ' φ)
        (WFF.mono_subst h θ hθ hc hΓ hΔ hΔ' ψ)
  | ι, _, _, _, d, d', h, θ, hθ, hc, hΓ, hΔ, hΔ', .all T φ => by
      change WFF.all T (WFF.mono (h.insert _ T) (WFF.subst (VarSymb.shiftSlot ι d d')
        (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
        (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T) φ)) = _
      rw [WFF.mono_subst (h.insert _ T) (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
        (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T) (hΔ'.insert T) φ]
      exact congrArg (WFF.all T) (WFF.subst_congr _ _ _ _ _ _ _ _
        (Subst.sim_under_mono θ h T hΔ.root hΔ'.root) φ)
  | ι, _, _, _, d, d', h, θ, hθ, hc, hΓ, hΔ, hΔ', .ex T φ => by
      change WFF.ex T (WFF.mono (h.insert _ T) (WFF.subst (VarSymb.shiftSlot ι d d')
        (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
        (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T) φ)) = _
      rw [WFF.mono_subst (h.insert _ T) (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
        (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T) (hΔ'.insert T) φ]
      exact congrArg (WFF.ex T) (WFF.subst_congr _ _ _ _ _ _ _ _
        (Subst.sim_under_mono θ h T hΔ.root hΔ'.root) φ)
  | ι, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΔ, hΔ', .box φ => by
      change WFF.box (WFF.mono h.boxIn (WFF.subst ι θ.box (Subst.ok_box hθ)
        (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn φ)) = _
      rw [WFF.mono_subst h.boxIn θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
        hΔ.boxIn hΔ'.boxIn φ]
      exact congrArg WFF.box (WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_box_mono θ h) φ)
  | ι, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΔ, hΔ', .dia x hx φ => by
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      change WFF.dia (ι x) _ (WFF.mono (h.diaIn (ι x)) (WFF.subst ι (θ.dia x (ι x))
        (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) (hΓ.diaIn x) (hΔ.diaIn (ι x)) φ)) = _
      rw [WFF.mono_subst (h.diaIn (ι x)) (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw)
        (Subst.coh_dia hθ hc hx) (hΓ.diaIn x) (hΔ.diaIn (ι x)) (hΔ'.diaIn (ι x)) φ]
      exact congrArg (WFF.dia (ι x) _) (WFF.subst_congr _ _ _ _ _ _ _ _
        (Subst.sim_dia_mono θ h x (ι x)) φ)
  | ι, _, _, _, _, _, h, θ, hθ, hc, _, _, _, .here hT s t =>
      WFF.here_congr' hT (Term.mono_subst h θ hθ hc s) (Term.mono_subst h θ hθ hc t)
  | ι, _, _, _, _, _, h, θ, hθ, hc, _, _, _, .back hB L s t =>
      WFF.back_congr' hB L (Term.mono_subst h θ hθ hc s) (Term.mono_subst h θ hθ hc t)
  | ι, _, _, _, d, d', h, θ, hθ, hc, hΓ, hΔ, hΔ', .retSH hB S Zs hZs ws t cs Φ => by
      change WFF.retSH hB S Zs hZs _ (Term.mono h (Term.subst ι θ hθ hc t)) _
        (WFF.mono (h.boxIn.insert _ _) (WFF.subst (VarSymb.shiftSlot ι d d')
          (θ.box.under d d' _ hΔ.boxIn.root) (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
          (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) Φ)) = _
      rw [WFF.mono_subst (h.boxIn.insert _ _) (θ.box.under d d' _ hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
        (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) (hΔ'.boxIn.insert _) Φ]
      refine WFF.retSH_congr' hB S Zs hZs ((TmList.map_map _ _ ws).trans
        (TmList.map_congr (fun p => (congrArg (Sigma.mk _)
          (Term.mono_subst h.boxIn θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) p)).trans
          (Term.subst_congr _ _ _ _ _ _ (Subst.sim_box_mono θ h) p)) ws))
        (Term.mono_subst h θ hθ hc t)
        ((TmList.map_map _ _ cs).trans (TmList.map_congr (fun p => congrArg (Sigma.mk _)
          (Term.mono_subst h θ hθ hc p)) cs)) ?_
      have hok := Subst.ok_mono (Subst.ok_box hθ) h.boxIn
      have hcoh := Subst.coh_mono (Subst.coh_box hθ hc) h.boxIn
      refine (WFF.subst_congr _ ((θ.box.mono h.boxIn).under d d' _ hΔ'.boxIn.root) _
        (Subst.ok_under hok _ hΔ'.boxIn.root) _ (Subst.coh_under hok hcoh hΓ.boxIn _ hΔ'.boxIn.root)
        _ _ (Subst.sim_under_mono θ.box h.boxIn _ hΔ.boxIn.root hΔ'.boxIn.root) Φ).trans ?_
      exact WFF.subst_congr _ _ _ _ _ _ _ _
        (Subst.sim_under (Subst.sim_box_mono θ h) _ hΔ'.boxIn.root) Φ
  | ι, _, _, _, d, d', h, θ, hθ, hc, hΓ, hΔ, hΔ', .retxSH hB y hy S Zs hZs ws t cs Φ => by
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      have hok₀ := Subst.ok_dia hθ hy hw
      have hc₀ := Subst.coh_dia hθ hc hy
      have hr := (hΔ.diaIn (ι y)).root
      have hr' := (hΔ'.diaIn (ι y)).root
      change WFF.retxSH hB (ι y) _ S Zs hZs _ (Term.mono h (Term.subst ι θ hθ hc t)) _
        (WFF.mono ((h.diaIn (ι y)).insert _ _) (WFF.subst (VarSymb.shiftSlot ι d d')
          ((θ.dia y (ι y)).under d d' _ hr) (Subst.ok_under hok₀ _ hr)
          (Subst.coh_under hok₀ hc₀ (hΓ.diaIn y) _ hr)
          ((hΓ.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _) Φ)) = _
      rw [WFF.mono_subst ((h.diaIn (ι y)).insert _ _) ((θ.dia y (ι y)).under d d' _ hr)
        (Subst.ok_under hok₀ _ hr) (Subst.coh_under hok₀ hc₀ (hΓ.diaIn y) _ hr)
        ((hΓ.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _) ((hΔ'.diaIn (ι y)).insert _) Φ]
      refine WFF.retxSH_congr' hB _ _ S Zs hZs ((TmList.map_map _ _ ws).trans
        (TmList.map_congr (fun p => (congrArg (Sigma.mk _)
          (Term.mono_subst (h.diaIn (ι y)) (θ.dia y (ι y)) hok₀ hc₀ p)).trans
          (Term.subst_congr _ _ _ _ _ _ (Subst.sim_dia_mono θ h y (ι y)) p)) ws))
        (Term.mono_subst h θ hθ hc t)
        ((TmList.map_map _ _ cs).trans (TmList.map_congr (fun p => congrArg (Sigma.mk _)
          (Term.mono_subst h θ hθ hc p)) cs)) ?_
      have hok := Subst.ok_mono hok₀ (h.diaIn (ι y))
      have hcoh := Subst.coh_mono hc₀ (h.diaIn (ι y))
      refine (WFF.subst_congr _ (((θ.dia y (ι y)).mono (h.diaIn (ι y))).under d d' _ hr') _
        (Subst.ok_under hok _ hr') _ (Subst.coh_under hok hcoh (hΓ.diaIn y) _ hr')
        _ _ (Subst.sim_under_mono (θ.dia y (ι y)) (h.diaIn (ι y)) _ hr hr') Φ).trans ?_
      exact WFF.subst_congr _ _ _ _ _ _ _ _
        (Subst.sim_under (Subst.sim_dia_mono θ h y (ι y)) _ hr') Φ

end V12M
