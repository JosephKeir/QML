import QML.QML_v12m_SubstCongr

/-!
# QML v12m — substituting into weakened formulas

* `mono_mono`, `mono_refl`: weakening twice, weakening along `Γ ≤ Γ`.
* `collapse_mono`: collapsing commutes with weakening.
* `SubE.proj_mono` / `unbox_mono` / `diaBody_mono`: entry operations commute with weakening.
* `subst_mono`: substituting into a weakened formula is substituting into the formula.
-/

namespace V12M

variable [ModalSys]

/-! ## Weakening twice -/

mutual
  theorem Func.mono_mono {σ : Signature} {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : Γ₁.Le Γ₂) (h₂ : Γ₂.Le Γ₃) :
      {n : ℕ} → (f : Func σ Γ₁ n) → Func.mono h₂ (Func.mono h₁ f) = Func.mono (h₁.trans h₂) f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.mono h₂ (Func.mono h₁ g)) (Term.mono h₂ (Term.mono h₁ t)) = _
        rw [Func.mono_mono h₁ h₂ g, Term.mono_mono h₁ h₂ t]
        rfl
    termination_by structural _ f => f

  theorem Term.mono_mono {σ : Signature} {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : Γ₁.Le Γ₂) (h₂ : Γ₂.Le Γ₃) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      Term.mono h₂ (Term.mono h₁ t) = Term.mono (h₁.trans h₂) t
    | _, _, .var _ _ => rfl
    | _, _, .func f => by
        change Term.func (Func.mono h₂ (Func.mono h₁ f)) = _
        rw [Func.mono_mono h₁ h₂ f]
        rfl
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change Term.pair (Term.mono h₂ (Term.mono h₁ s)) (Term.mono h₂ (Term.mono h₁ t)) = _
        rw [Term.mono_mono h₁ h₂ s, Term.mono_mono h₁ h₂ t]
        rfl
    | _, _, .boxtm t => by
        change Term.boxtm (Term.mono h₂.boxIn (Term.mono h₁.boxIn t)) = _
        rw [Term.mono_mono h₁.boxIn h₂.boxIn t]
        rfl
    | _, _, .diatm x _ t => by
        change Term.diatm x _ (Term.mono (h₂.diaIn x) (Term.mono (h₁.diaIn x) t)) = _
        rw [Term.mono_mono (h₁.diaIn x) (h₂.diaIn x) t]
        rfl
    termination_by structural _ _ t => t
end

mutual
  theorem Func.mono_refl {σ : Signature} {Γ : Ctx} (h : Γ.Le Γ) :
      {n : ℕ} → (f : Func σ Γ n) → Func.mono h f = f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.mono h g) (Term.mono h t) = _
        rw [Func.mono_refl h g, Term.mono_refl h t]
    termination_by structural _ f => f

  theorem Term.mono_refl {σ : Signature} {Γ : Ctx} (h : Γ.Le Γ) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) → Term.mono h t = t
    | _, _, .var _ _ => rfl
    | _, _, .func f => by
        change Term.func (Func.mono h f) = _
        rw [Func.mono_refl h f]
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change Term.pair (Term.mono h s) (Term.mono h t) = _
        rw [Term.mono_refl h s, Term.mono_refl h t]
    | _, _, .boxtm t => by
        change Term.boxtm (Term.mono h.boxIn t) = _
        rw [Term.mono_refl h.boxIn t]
    | _, _, .diatm x _ t => by
        change Term.diatm x _ (Term.mono (h.diaIn x) t) = _
        rw [Term.mono_refl (h.diaIn x) t]
    termination_by structural _ _ t => t
end

/-! ## Collapsing commutes with weakening -/

mutual
  theorem Func.collapse_mono {σ : Signature} {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx}
      (h : Ctx.Collapses k Γ₁ Γ₂) (h' : Ctx.Collapses k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁')
      (l₂ : Γ₂.Le Γ₂') :
      {n : ℕ} → (f : Func σ Γ₁ n) →
      Func.collapse h' (Func.mono l₁ f) = Func.mono l₂ (Func.collapse h f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.collapse h' (Func.mono l₁ g)) (Term.collapse h' (Term.mono l₁ t)) = _
        rw [Func.collapse_mono h h' l₁ l₂ g, Term.collapse_mono h h' l₁ l₂ t]
        rfl
    termination_by structural _ f => f

  theorem Term.collapse_mono {σ : Signature} {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx}
      (h : Ctx.Collapses k Γ₁ Γ₂) (h' : Ctx.Collapses k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁')
      (l₂ : Γ₂.Le Γ₂') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      Term.collapse h' (Term.mono l₁ t) = Term.mono l₂ (Term.collapse h t)
    | _, _, .var _ _ => rfl
    | _, _, .func f => by
        change Term.func (Func.collapse h' (Func.mono l₁ f)) = _
        rw [Func.collapse_mono h h' l₁ l₂ f]
        rfl
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change Term.pair (Term.collapse h' (Term.mono l₁ s)) (Term.collapse h' (Term.mono l₁ t)) = _
        rw [Term.collapse_mono h h' l₁ l₂ s, Term.collapse_mono h h' l₁ l₂ t]
        rfl
    | _, _, .boxtm t => by
        change Term.boxtm (Term.collapse h'.boxIn (Term.mono l₁.boxIn t)) = _
        rw [Term.collapse_mono h.boxIn h'.boxIn l₁.boxIn l₂.boxIn t]
        rfl
    | _, _, .diatm x _ t => by
        change Term.diatm _ _ (Term.collapse (h'.diaIn x) (Term.mono (l₁.diaIn x) t)) = _
        rw [Term.collapse_mono (h.diaIn x) (h'.diaIn x) (l₁.diaIn x) (l₂.diaIn _) t]
        rfl
    termination_by structural _ _ t => t
end

/-! ## Shifting commutes with weakening -/

mutual
  theorem Func.shift_mono {σ : Signature} {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx}
      (h : Ctx.Shifts k Γ₁ Γ₂) (h' : Ctx.Shifts k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁')
      (l₂ : Γ₂.Le Γ₂') :
      {n : ℕ} → (f : Func σ Γ₁ n) →
      Func.shift h' (Func.mono l₁ f) = Func.mono l₂ (Func.shift h f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.shift h' (Func.mono l₁ g)) (Term.shift h' (Term.mono l₁ t)) = _
        rw [Func.shift_mono h h' l₁ l₂ g, Term.shift_mono h h' l₁ l₂ t]
        rfl
    termination_by structural _ f => f

  theorem Term.shift_mono {σ : Signature} {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx}
      (h : Ctx.Shifts k Γ₁ Γ₂) (h' : Ctx.Shifts k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁')
      (l₂ : Γ₂.Le Γ₂') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      Term.shift h' (Term.mono l₁ t) = Term.mono l₂ (Term.shift h t)
    | _, _, .var _ _ => rfl
    | _, _, .func f => by
        change Term.func (Func.shift h' (Func.mono l₁ f)) = _
        rw [Func.shift_mono h h' l₁ l₂ f]
        rfl
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change Term.pair (Term.shift h' (Term.mono l₁ s)) (Term.shift h' (Term.mono l₁ t)) = _
        rw [Term.shift_mono h h' l₁ l₂ s, Term.shift_mono h h' l₁ l₂ t]
        rfl
    | _, _, .boxtm t => by
        change Term.boxtm (Term.shift h'.boxIn (Term.mono l₁.boxIn t)) = _
        rw [Term.shift_mono h.boxIn h'.boxIn l₁.boxIn l₂.boxIn t]
        rfl
    | _, _, .diatm x _ t => by
        change Term.diatm _ _ (Term.shift (h'.diaIn x) (Term.mono (l₁.diaIn x) t)) = _
        rw [Term.shift_mono (h.diaIn x) (h'.diaIn x) (l₁.diaIn x) (l₂.diaIn _) t]
        rfl
    termination_by structural _ _ t => t
end

namespace SubE

variable {σ : Signature}

theorem mono_mono {Δ₁ Δ₂ Δ₃ : Ctx} (h₁ : Δ₁.Le Δ₂) (h₂ : Δ₂.Le Δ₃) :
    ∀ (e : SubE σ Δ₁), (e.mono h₁).mono h₂ = e.mono (h₁.trans h₂)
  | .hide => rfl
  | .ren _ => rfl
  | .tm t => congrArg SubE.tm (Term.mono_mono h₁ h₂ t)

theorem proj_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ (e : SubE σ Δ) (s : Step), (e.mono h).proj s = (e.proj s).mono h
  | .hide, _ => rfl
  | .ren _, _ => rfl
  | .tm t, s => by
      cases t with
      | boxtm t =>
          cases s with
          | here =>
              change (SubE.tm (Term.boxtm (Term.mono h.boxIn t))).proj .here =
                ((SubE.tm (Term.boxtm t)).proj .here).mono h
              by_cases hT : ModalSys.T = true
              · rw [proj_boxtm_here _ hT, proj_boxtm_here _ hT]
                exact congrArg SubE.tm (Term.collapse_mono _ _ h.boxIn h t)
              · rw [show (SubE.tm (Term.boxtm (Term.mono h.boxIn t))).proj .here = .hide from
                    dif_neg hT,
                  show (SubE.tm (Term.boxtm t)).proj .here = .hide from dif_neg hT]
                rfl
          | _ => rfl
      | _ => cases s <;> rfl

theorem unbox_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ (e : SubE σ Δ), (e.mono h).unbox = e.unbox.mono h.boxIn
  | .hide => rfl
  | .ren _ => rfl
  | .tm t => by cases t <;> rfl

theorem keepE_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ (e : SubE σ Δ), (e.mono h).keepE = e.keepE.mono h.boxIn
  | .hide => rfl
  | .ren _ => rfl
  | .tm t => by
      cases t with
      | boxtm t =>
          change (SubE.tm (Term.boxtm (Term.mono h.boxIn t))).keepE =
            ((SubE.tm (Term.boxtm t)).keepE).mono h.boxIn
          by_cases hF : ModalSys.Four = true
          · rw [keepE_tm _ hF, keepE_tm _ hF]
            exact congrArg (fun s => SubE.tm (Term.boxtm s))
              (Term.shift_mono _ _ h.boxIn h.boxIn.boxIn t)
          · rw [show (SubE.tm (Term.boxtm (Term.mono h.boxIn t)) : SubE σ Δ').keepE = .hide from
                dif_neg hF,
              show (SubE.tm (Term.boxtm t) : SubE σ Δ).keepE = .hide from dif_neg hF]
            rfl
      | diatm y hy t =>
          change (SubE.tm (Term.diatm y _ (Term.mono (h.diaIn y) t))).keepE =
            ((SubE.tm (Term.diatm y hy t)).keepE).mono h.boxIn
          by_cases hK : ModalSys.Four = true ∧ ModalSys.shaped = false
          · rw [keepE_dia _ _ _ hK.1 hK.2, keepE_dia _ _ _ hK.1 hK.2]
            exact congrArg (fun s => SubE.tm (Term.diatm _ _ s))
              (Term.shift_mono _ _ (h.diaIn y) (h.boxIn.diaIn _) t)
          · rw [keepE_dia_off _ _ _ hK, keepE_dia_off _ _ _ hK]
            rfl
      | _ => rfl

theorem diaBody_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') (ιx : VarSymb) :
    ∀ (e : SubE σ Δ), (e.mono h).diaBody ιx = (e.diaBody ιx).mono (h.diaIn ιx)
  | .hide => rfl
  | .ren _ => rfl
  | .tm (.diatm y hy u) => by
      by_cases hyx : y = ιx
      · subst hyx
        rw [show (SubE.mono h (SubE.tm (Term.diatm y hy u))).diaBody y =
            SubE.tm (Term.mono (Ctx.Le.refl _) (Term.mono (h.diaIn y) u)) from dif_pos rfl,
          show (SubE.tm (Term.diatm y hy u) : SubE σ Δ).diaBody y =
            SubE.tm (Term.mono (Ctx.Le.refl _) u) from dif_pos rfl]
        exact congrArg SubE.tm ((Term.mono_mono _ _ u).trans (Term.mono_mono _ _ u).symm)
      · rw [show (SubE.mono h (SubE.tm (Term.diatm y hy u))).diaBody ιx = SubE.hide from
            dif_neg hyx,
          show (SubE.tm (Term.diatm y hy u) : SubE σ Δ).diaBody ιx = SubE.hide from dif_neg hyx]
        rfl
  | .tm (.var _ _) => rfl
  | .tm (.func _) => rfl
  | .tm .unit => rfl
  | .tm (.pair _ _) => rfl
  | .tm (.boxtm _) => rfl

end SubE

/-! ## Substituting into a weakened formula -/

theorem Subst.Ok.restrict {σ : Signature} {Γ Γ' Δ : Ctx} {θ : Subst σ Δ} (hθ : Subst.Ok Γ' θ)
    (h : Γ.Le Γ') : Subst.Ok Γ θ :=
  fun v T hlp hv => hθ v T hlp (h v T hv)

theorem Subst.Coh.restrict {σ : Signature} {ι : VarSymb → VarSymb} {Γ Γ' Δ : Ctx}
    {θ : Subst σ Δ} (hc : Subst.Coh ι Γ' θ) (h : Γ.Le Γ') : Subst.Coh ι Γ θ :=
  fun v T hv p => hc v T (h.ref hv) p

mutual
  theorem Func.subst_mono {σ : Signature} {ι : VarSymb → VarSymb} {Γ Γ' Δ : Ctx}
      (h : Γ.Le Γ') (θ : Subst σ Δ) (hθ : Subst.Ok Γ' θ) (hc : Subst.Coh ι Γ' θ) :
      {n : ℕ} → (f : Func σ Γ n) →
      Func.subst ι θ hθ hc (Func.mono h f) = Func.subst ι θ (hθ.restrict h) (hc.restrict h) f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι θ hθ hc (Func.mono h g))
          (Term.subst ι θ hθ hc (Term.mono h t)) = _
        rw [Func.subst_mono h θ hθ hc g, Term.subst_mono h θ hθ hc t]
        rfl
    termination_by structural _ f => f

  theorem Term.subst_mono {σ : Signature} {ι : VarSymb → VarSymb} {Γ Γ' Δ : Ctx}
      (h : Γ.Le Γ') (θ : Subst σ Δ) (hθ : Subst.Ok Γ' θ) (hc : Subst.Coh ι Γ' θ) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      Term.subst ι θ hθ hc (Term.mono h t) = Term.subst ι θ (hθ.restrict h) (hc.restrict h) t
    | _, _, .var _ _ => rfl
    | _, _, .func f => by
        change Term.func (Func.subst ι θ hθ hc (Func.mono h f)) = _
        rw [Func.subst_mono h θ hθ hc f]
        rfl
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change Term.pair (Term.subst ι θ hθ hc (Term.mono h s))
          (Term.subst ι θ hθ hc (Term.mono h t)) = _
        rw [Term.subst_mono h θ hθ hc s, Term.subst_mono h θ hθ hc t]
        rfl
    | _, _, .boxtm t =>
        congrArg Term.boxtm
          (Term.subst_mono h.boxIn θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) t)
    | _, _, .diatm x hx t =>
        have hx' : ∃ X, Γ'.ref x = some (.VTypeDia X) := hx.imp fun _ hX => h.ref hX
        congrArg (Term.diatm (ι x) _)
          (Term.subst_mono (h.diaIn x) (θ.dia x (ι x))
            (Subst.ok_dia hθ hx' (hx'.elim fun _ hX => hc x _ hX [])) (Subst.coh_dia hθ hc hx') t)
    termination_by structural _ _ t => t
end

theorem Rel.subst_mono {σ : Signature} {ι : VarSymb → VarSymb} {Γ Γ' Δ : Ctx}
    (h : Γ.Le Γ') (θ : Subst σ Δ) (hθ : Subst.Ok Γ' θ) (hc : Subst.Coh ι Γ' θ) :
    {n : ℕ} → (ρ : Rel σ Γ n) →
    Rel.subst ι θ hθ hc (Rel.mono h ρ) = Rel.subst ι θ (hθ.restrict h) (hc.restrict h) ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.subst ι θ hθ hc (Rel.mono h ρ))
        (Term.subst ι θ hθ hc (Term.mono h t)) = _
      rw [Rel.subst_mono h θ hθ hc ρ, Term.subst_mono h θ hθ hc t]
      rfl

theorem WFF.subst_mono {σ : Signature} : {ι : VarSymb → VarSymb} → {Γ Γ' Δ : Ctx} → {d d' : ℕ} →
    (h : Γ.Le Γ') → (θ : Subst σ Δ) → (hθ : Subst.Ok Γ' θ) → (hc : Subst.Coh ι Γ' θ) →
    (hΓ : Γ.SlotsFrom d) → (hΓ' : Γ'.SlotsFrom d) → (hΔ : Δ.SlotsFrom d') → (φ : WFF σ Γ d) →
    WFF.subst ι θ hθ hc hΓ' hΔ (WFF.mono h φ) =
      WFF.subst ι θ (hθ.restrict h) (hc.restrict h) hΓ hΔ φ
  | _, _, _, _, _, _, h, θ, hθ, hc, _, _, _, .atom ρ =>
      congrArg WFF.atom (Rel.subst_mono h θ hθ hc ρ)
  | _, _, _, _, _, _, h, θ, hθ, hc, _, _, _, .eq t s =>
      congrArg₂ WFF.eq (Term.subst_mono h θ hθ hc t) (Term.subst_mono h θ hθ hc s)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΓ', hΔ, .and φ ψ =>
      congrArg₂ WFF.and (WFF.subst_mono h θ hθ hc hΓ hΓ' hΔ φ)
        (WFF.subst_mono h θ hθ hc hΓ hΓ' hΔ ψ)
  | _, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΓ', hΔ, .or φ ψ =>
      congrArg₂ WFF.or (WFF.subst_mono h θ hθ hc hΓ hΓ' hΔ φ)
        (WFF.subst_mono h θ hθ hc hΓ hΓ' hΔ ψ)
  | _, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΓ', hΔ, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.subst_mono h θ hθ hc hΓ hΓ' hΔ φ)
        (WFF.subst_mono h θ hθ hc hΓ hΓ' hΔ ψ)
  | _, _, _, _, d, d', h, θ, hθ, hc, hΓ, hΓ', hΔ, .all T φ =>
      congrArg (WFF.all T) (WFF.subst_mono (h.insert _ T) (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ' T hΔ.root)
        (hΓ.insert T) (hΓ'.insert T) (hΔ.insert T) φ)
  | _, _, _, _, d, d', h, θ, hθ, hc, hΓ, hΓ', hΔ, .ex T φ =>
      congrArg (WFF.ex T) (WFF.subst_mono (h.insert _ T) (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ' T hΔ.root)
        (hΓ.insert T) (hΓ'.insert T) (hΔ.insert T) φ)
  | _, _, _, _, _, _, h, θ, hθ, hc, hΓ, hΓ', hΔ, .box φ =>
      congrArg WFF.box (WFF.subst_mono h.boxIn θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        hΓ.boxIn hΓ'.boxIn hΔ.boxIn φ)
  | ι, _, Γ', _, _, _, h, θ, hθ, hc, hΓ, hΓ', hΔ, .dia x hx φ =>
      have hx' : ∃ X, Γ'.ref x = some (.VTypeDia X) := hx.imp fun _ hX => h.ref hX
      congrArg (WFF.dia (ι x) _)
        (WFF.subst_mono (h.diaIn x) (θ.dia x (ι x))
          (Subst.ok_dia hθ hx' (hx'.elim fun _ hX => hc x _ hX [])) (Subst.coh_dia hθ hc hx')
          (hΓ.diaIn x) (hΓ'.diaIn x) (hΔ.diaIn (ι x)) φ)
  | _, _, _, _, _, _, h, θ, hθ, hc, _, _, _, .here hT s t =>
      WFF.here_congr' hT (Term.subst_mono h θ hθ hc s) (Term.subst_mono h θ hθ hc t)
  | _, _, _, _, _, _, h, θ, hθ, hc, _, _, _, .back hB L s t =>
      WFF.back_congr' hB L (Term.subst_mono h θ hθ hc s) (Term.subst_mono h θ hθ hc t)
  | _, _, _, _, d, d', h, θ, hθ, hc, hΓ, hΓ', hΔ, .retS hB S t Φ =>
      WFF.retS_congr' hB S (Term.subst_mono h θ hθ hc t)
        (WFF.subst_mono (h.boxIn.insert _ _) (θ.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ'.boxIn _ hΔ.boxIn.root)
          (hΓ.boxIn.insert _) (hΓ'.boxIn.insert _) (hΔ.boxIn.insert _) Φ)
  | ι, _, Γ', _, d, d', h, θ, hθ, hc, hΓ, hΓ', hΔ, .retxS hB y hy S t Φ =>
      have hy' : ∃ Y, Γ'.ref y = some (.VTypeDia Y) := hy.imp fun _ hY => h.ref hY
      have hw : (θ.at y).idxAlong [] = ι y := hy'.elim fun _ hY => hc y _ hY []
      WFF.retxS_congr' hB _ _ S (Term.subst_mono h θ hθ hc t)
        (WFF.subst_mono ((h.diaIn y).insert _ _)
          ((θ.dia y (ι y)).under d d' _ (hΔ.diaIn (ι y)).root)
          (Subst.ok_under (Subst.ok_dia hθ hy' hw) _ (hΔ.diaIn (ι y)).root)
          (Subst.coh_under (Subst.ok_dia hθ hy' hw) (Subst.coh_dia hθ hc hy') (hΓ'.diaIn y) _
            (hΔ.diaIn (ι y)).root)
          ((hΓ.diaIn y).insert _) ((hΓ'.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _) Φ)

end V12M
