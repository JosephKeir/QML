import QML.QML_v12m_SubstTwice

/-!
# QML v12m — the identity substitution

Substituting every address for itself changes nothing.  The proof is the usual one: the identity
substitution is preserved, up to `Subst.Sim`, by the three transformations (`Subst.box`,
`Subst.dia`, `Subst.under`), so `Subst.subst_congr` reduces each recursive call to the identity
again.

The `□` case is where the two differ on invisible addresses: `(idS).box (u.box)` is
`.ren u.inner`, which is `u.keep.here` under `keepOnly`.  There `u.box` is not visible, so `Sim`
does not see it.

This is what the round trip of a `◇` view abstraction needs (`QML_v12m_DiaAbs`).
-/

namespace V12M

theorem Ann.mapIdx_id : ∀ {T : VarType} (a : Ann T), a.mapIdx id = a
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by
      change Ann.prod (a.mapIdx id) (b.mapIdx id) = _
      rw [Ann.mapIdx_id a, Ann.mapIdx_id b]
  | _, .box a => by
      change Ann.box (a.mapIdx id) = _
      rw [Ann.mapIdx_id a]
  | _, .dia i a => by
      change Ann.dia (id i) (a.mapIdx id) = _
      rw [Ann.mapIdx_id a]
      rfl

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- The substitution that leaves every address alone. -/
def idS (σ : Signature) (Δ : Ctx) : Subst σ Δ := fun v => .ren v

theorem at_idS : ∀ v : VarSymb, (idS σ Δ).at v = .ren v
  | .root _ => rfl
  | .step v s => by
      change (if s.isProj then ((idS σ Δ).at v).proj s else SubE.ren (.step v s)) = _
      split_ifs with hs
      · rw [at_idS v]
        rfl
      · rfl

theorem ok_idS : Ok Δ (idS σ Δ) :=
  fun _ _ hlp hv => (Ctx.ref_nonproj Δ hlp).trans hv

theorem coh_idS : Coh id Δ (idS σ Δ) :=
  coh_of ok_idS (fun _ _ _ _ _ => rfl)

theorem sim_box_idS : Sim Δ.boxIn (idS σ Δ).box (idS σ Δ.boxIn) := by
  refine sim_of ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, _⟩ := Ctx.boxIn_box hv
      change SubE.Sim T (((idS σ Δ).at u).unbox) (.ren (.step u .box))
      rw [at_idS]
      change SubE.Sim T (.ren u.inner) _
      rw [VarSymb.inner_box hk]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (((idS σ Δ).at u).keepE) (.ren (.step u .keep))
      rw [at_idS]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem sim_dia_idS (x : VarSymb) :
    Sim (Δ.diaIn x) ((idS σ Δ).dia x x) (idS σ (Δ.diaIn x)) := by
  refine sim_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change SubE.Sim T (if u = x then ((idS σ Δ).at x).diaBody x else .hide)
        (.ren (.step u .dia))
      have hux : u = x := by
        change (if u = x then (match Δ.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        split_ifs at hv with h
        exact h
      subst hux
      rw [if_pos rfl, at_idS]
      exact .refl _
  | .step u .box =>
      obtain ⟨hk, _⟩ := Ctx.boxIn_box (Γ := Δ) hv
      change SubE.Sim T ((((idS σ Δ).at u).unbox).mono (Ctx.le_boxIn_diaIn Δ x))
        (.ren (.step u .box))
      rw [at_idS]
      change SubE.Sim T (SubE.mono _ (SubE.ren u.inner)) _
      rw [VarSymb.inner_box hk]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T ((((idS σ Δ).at u).keepE).mono (Ctx.le_boxIn_diaIn Δ x))
        (.ren (.step u .keep))
      rw [at_idS]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem ok_idS_le {Γ : Ctx} (hle : Γ.Le Δ) : Ok Γ (idS σ Δ) :=
  fun v T hlp hv => (Ctx.ref_nonproj Δ hlp).trans (hle v T hv)

theorem coh_idS_le {Γ : Ctx} (hle : Γ.Le Δ) : Coh id Γ (idS σ Δ) :=
  coh_of (ok_idS_le hle) (fun _ _ _ _ _ => rfl)

theorem Sim.restrict {Γ Δ Δ' : Ctx} {θ θ' : Subst σ Δ'} (h : Sim Δ θ θ')
    (hle : Γ.Le Δ) : Sim Γ θ θ' :=
  fun v T hv => h v T (hle.ref hv)

theorem sim_under_idS (d : ℕ) (T : VarType) (h : Δ (.root (.bnd d)) = none) :
    Sim (Δ.insert (.bnd d) T) ((idS σ Δ).under d d T h) (idS σ (Δ.insert (.bnd d) T)) := by
  refine sim_of ?_
  intro v U _ _
  change SubE.Sim U (if v = .root (.bnd d) then .ren (.root (.bnd d))
    else SubE.mono (Ctx.le_insert h T) (.ren v)) (.ren v)
  split_ifs with hv
  · subst hv
    exact .refl _
  · exact .refl _

end Subst

/-! ## Substituting by the identity -/

mutual
  theorem Func.subst_id {σ : Signature} {Δ : Ctx} (hθ : Subst.Ok Δ (Subst.idS σ Δ))
      (hc : Subst.Coh id Δ (Subst.idS σ Δ)) :
      ∀ {n : ℕ} (f : Func σ Δ n), Func.subst id (Subst.idS σ Δ) hθ hc f = f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst id _ hθ hc g) (Term.subst id _ hθ hc t) = _
        rw [Func.subst_id hθ hc g, Term.subst_id_var hθ hc t]

  theorem Term.subst_id_var {σ : Signature} {Δ : Ctx} (hθ : Subst.Ok Δ (Subst.idS σ Δ))
      (hc : Subst.Coh id Δ (Subst.idS σ Δ)) (t : Term σ Δ .Var .var) :
      Term.subst id (Subst.idS σ Δ) hθ hc t = t := by
    match t with
    | .var v hv =>
        change ((Subst.idS σ Δ).at v).toVar _ = _
        have e : (Subst.idS σ Δ).at v = .ren v := Subst.at_idS v
        simp only [e]
        rfl
    | .func f =>
        change Term.func (Func.subst id _ hθ hc f) = _
        rw [Func.subst_id hθ hc f]
end

theorem Rel.subst_id {σ : Signature} {Δ : Ctx} (hθ : Subst.Ok Δ (Subst.idS σ Δ))
    (hc : Subst.Coh id Δ (Subst.idS σ Δ)) :
    ∀ {n : ℕ} (ρ : Rel σ Δ n), Rel.subst id (Subst.idS σ Δ) hθ hc ρ = ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.subst id _ hθ hc ρ) (Term.subst id _ hθ hc t) = _
      rw [Rel.subst_id hθ hc ρ, Term.subst_id_var hθ hc t]

/-! ## Substituting by the identity into a larger context -/

mutual
  theorem Func.subst_idS_mono {σ : Signature} {Γ Δ : Ctx} (hle : Γ.Le Δ)
      (hθ : Subst.Ok Γ (Subst.idS σ Δ)) (hc : Subst.Coh id Γ (Subst.idS σ Δ)) :
      ∀ {n : ℕ} (f : Func σ Γ n), Func.subst id (Subst.idS σ Δ) hθ hc f = Func.mono hle f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst id _ hθ hc g) (Term.subst id _ hθ hc t) = _
        rw [Func.subst_idS_mono hle hθ hc g, Term.subst_idS_mono_var hle hθ hc t]
        rfl

  theorem Term.subst_idS_mono_var {σ : Signature} {Γ Δ : Ctx} (hle : Γ.Le Δ)
      (hθ : Subst.Ok Γ (Subst.idS σ Δ)) (hc : Subst.Coh id Γ (Subst.idS σ Δ))
      (t : Term σ Γ .Var .var) :
      Term.subst id (Subst.idS σ Δ) hθ hc t = Term.mono hle t := by
    match t with
    | .var v hv =>
        change ((Subst.idS σ Δ).at v).toVar _ = _
        have e : (Subst.idS σ Δ).at v = .ren v := Subst.at_idS v
        simp only [e]
        rfl
    | .func f =>
        change Term.func (Func.subst id _ hθ hc f) = _
        rw [Func.subst_idS_mono hle hθ hc f]
        rfl
end

/-- ⭐Substituting every address for itself into a larger context is weakening. -/
theorem Term.subst_idS_mono {σ : Signature} : {Γ Δ : Ctx} → (hle : Γ.Le Δ) →
    (hθ : Subst.Ok Γ (Subst.idS σ Δ)) → (hc : Subst.Coh id Γ (Subst.idS σ Δ)) →
    {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
    (⟨_, Term.subst id (Subst.idS σ Δ) hθ hc t⟩ : Σ b, Term σ Δ T b) = ⟨a, Term.mono hle t⟩
  | _, _, hle, hθ, hc, _, _, .var v hv =>
      congrArg (Sigma.mk _) (Term.subst_idS_mono_var hle hθ hc (.var v hv))
  | _, _, hle, hθ, hc, _, _, .func f =>
      congrArg (Sigma.mk _) (Term.subst_idS_mono_var hle hθ hc (.func f))
  | _, _, _, _, _, _, _, .unit => rfl
  | _, _, hle, hθ, hc, _, _, .pair s t => by
      have hs := Term.subst_idS_mono hle hθ hc s
      have ht := Term.subst_idS_mono hle hθ hc t
      exact sig_pair hs ht
  | _, Δ, hle, hθ, hc, _, _, .boxtm b => by
      change (⟨_, Term.boxtm (Term.subst id (Subst.idS σ Δ).box _ _ b)⟩ :
        Σ c, Term σ Δ (.VTypeBox _) c) = _
      exact sig_boxtm ((Term.subst_congr (Subst.idS σ Δ).box (Subst.idS σ Δ.boxIn) _
        (Subst.ok_idS_le hle.boxIn) _ (Subst.coh_idS_le hle.boxIn)
        (Subst.sim_box_idS.restrict hle.boxIn) b).trans
        (Term.subst_idS_mono hle.boxIn (Subst.ok_idS_le hle.boxIn)
          (Subst.coh_idS_le hle.boxIn) b))
  | _, Δ, hle, hθ, hc, _, _, .diatm x hx b => by
      change (⟨_, Term.diatm x _ (Term.subst id ((Subst.idS σ Δ).dia x x) _ _ b)⟩ :
        Σ c, Term σ Δ (.VTypeDia _) c) = _
      exact sig_diatm ((Term.subst_congr ((Subst.idS σ Δ).dia x x) (Subst.idS σ (Δ.diaIn x)) _
        (Subst.ok_idS_le (hle.diaIn x)) _ (Subst.coh_idS_le (hle.diaIn x))
        ((Subst.sim_dia_idS x).restrict (hle.diaIn x)) b).trans
        (Term.subst_idS_mono (hle.diaIn x) (Subst.ok_idS_le (hle.diaIn x))
          (Subst.coh_idS_le (hle.diaIn x)) b))
  termination_by structural _ _ _ _ _ _ _ t => t

/-- ⭐Substituting every address for itself changes nothing. -/
theorem WFF.subst_id {σ : Signature} : {Δ : Ctx} → {d : ℕ} → (hθ : Subst.Ok Δ (Subst.idS σ Δ)) →
    (hc : Subst.Coh id Δ (Subst.idS σ Δ)) → (hΔ : Δ.SlotsFrom d) → (φ : WFF σ Δ d) →
    WFF.subst id (Subst.idS σ Δ) hθ hc hΔ hΔ φ = φ
  | _, _, hθ, hc, _, .atom ρ => congrArg WFF.atom (Rel.subst_id hθ hc ρ)
  | _, _, hθ, hc, _, .eq t s =>
      congrArg₂ WFF.eq (Term.subst_id_var hθ hc t) (Term.subst_id_var hθ hc s)
  | _, _, _, _, _, .top => rfl
  | _, _, _, _, _, .bot => rfl
  | _, _, hθ, hc, hΔ, .and φ ψ =>
      congrArg₂ WFF.and (WFF.subst_id hθ hc hΔ φ) (WFF.subst_id hθ hc hΔ ψ)
  | _, _, hθ, hc, hΔ, .or φ ψ =>
      congrArg₂ WFF.or (WFF.subst_id hθ hc hΔ φ) (WFF.subst_id hθ hc hΔ ψ)
  | _, _, hθ, hc, hΔ, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.subst_id hθ hc hΔ φ) (WFF.subst_id hθ hc hΔ ψ)
  | Δ, d, _, _, hΔ, .all T φ => by
      refine congrArg (WFF.all T) ?_
      refine (WFF.subst_congr _ (Subst.idS σ (Δ.insert (.bnd d) T)) _ Subst.ok_idS _
        Subst.coh_idS (hΔ.insert T) (hΔ.insert T)
        (Subst.sim_under_idS d T hΔ.root) φ).trans ?_
      exact WFF.subst_id Subst.ok_idS Subst.coh_idS (hΔ.insert T) φ
  | Δ, d, _, _, hΔ, .ex T φ => by
      refine congrArg (WFF.ex T) ?_
      refine (WFF.subst_congr _ (Subst.idS σ (Δ.insert (.bnd d) T)) _ Subst.ok_idS _
        Subst.coh_idS (hΔ.insert T) (hΔ.insert T)
        (Subst.sim_under_idS d T hΔ.root) φ).trans ?_
      exact WFF.subst_id Subst.ok_idS Subst.coh_idS (hΔ.insert T) φ
  | Δ, _, _, _, hΔ, .box φ => by
      refine congrArg WFF.box ?_
      refine (WFF.subst_congr _ (Subst.idS σ Δ.boxIn) _ Subst.ok_idS _ Subst.coh_idS hΔ.boxIn
        hΔ.boxIn Subst.sim_box_idS φ).trans ?_
      exact WFF.subst_id Subst.ok_idS Subst.coh_idS hΔ.boxIn φ
  | Δ, _, _, _, hΔ, .dia x _ φ => by
      refine congrArg (WFF.dia x _) ?_
      refine (WFF.subst_congr _ (Subst.idS σ (Δ.diaIn x)) _ Subst.ok_idS _ Subst.coh_idS
        (hΔ.diaIn x) (hΔ.diaIn x) (Subst.sim_dia_idS x) _).trans ?_
      exact WFF.subst_id Subst.ok_idS Subst.coh_idS (hΔ.diaIn x) _

end V12M
