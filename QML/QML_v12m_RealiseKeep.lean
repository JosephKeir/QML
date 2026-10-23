import QML.QML_v12m_CanonWorld

/-!
# QML v12m — realising a kept witness (T + 4)

Under T + 4 a member of a possible object's extent reads its content by realisation, through the
kept witness (`Canon.rden_diatm_tFour`).  The truth lemma's `◇_x χ ⇒ some member` step needs the
syntactic identity behind that reading (docs §3 4, "T + 4 on paper" (b)):

  `realise_{x.keep, x.dia}(shift χ) = χ`, up to weakening (`WFF.realiseAtA_shift_keep`).

* The abstraction of `x.keep`'s content commutes with the shift: it is the abstraction of `x`'s,
  shifted (`WFF.shift_subst`, `Subst.shiftCorr_diaAbsA_keep`).
* Collapsing a shift at one level is the identity where the shift-then-collapse fixes every
  address (`WFF.collapse_shift_same`), which under T + 4 every `□` view does
  (`Ctx.shiftCollapseId_keepOnly`).
* Reading the abstraction back at the content is the round trip (`WFF.viewReadAtA_diaAbsA`).
-/

namespace V12M

variable [ModalSys]

/-! ## Collapsing a shift at one level, for formulas -/

theorem Ctx.ShiftCollapseId.insert {m : ℕ} {Γ : Ctx} (h : Γ.ShiftCollapseId m) (r : Root)
    (T : VarType) : (Γ.insert r T).ShiftCollapseId m := by
  refine Ctx.ShiftCollapseId.of_raw ?_
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    rfl
  · have hv' : Γ v = some U := by
      change (if v = .root r then some T else Γ v) = some U at hv
      rwa [if_neg hvr] at hv
    exact h v U ((Ctx.ref_nonproj _ hlp).trans hv')

section CollapseShift

variable {σ : Signature}

theorem Rel.collapse_shift_same {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
    (hs : Ctx.Shifts m Γ₁ Γ₂) (hc : Ctx.Collapses m Γ₂ Γ₃) (hle : Γ₁.Le Γ₃)
    (hid : Γ₁.ShiftCollapseId m) :
    {n : ℕ} → (ρ : Rel σ Γ₁ n) → Rel.collapse hc (Rel.shift hs ρ) = Rel.mono hle ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.collapse hc (Rel.shift hs ρ)) (Term.collapse hc (Term.shift hs t)) = _
      rw [Rel.collapse_shift_same hs hc hle hid ρ,
        eq_of_heq (Sigma.mk.inj (Term.collapse_shift_same hs hc hle hid t)).2]
      rfl

/-- ⭐**Where shifting then collapsing at one level fixes the addresses, it undoes itself** — the
    formula form of `Term.collapse_shift_same`. -/
theorem WFF.collapse_shift_same : ∀ {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx} {d : ℕ}
    (hs : Ctx.Shifts m Γ₁ Γ₂) (hc : Ctx.Collapses m Γ₂ Γ₃) (hle : Γ₁.Le Γ₃)
    (_hid : Γ₁.ShiftCollapseId m) (hs₁ : Γ₁.SlotsFrom d) (hs₂ : Γ₂.SlotsFrom d)
    (φ : WFF σ Γ₁ d),
    WFF.collapse hc hs₂ (WFF.shift hs hs₁ φ) = WFF.mono hle φ
  | _, _, _, _, _, hs, hc, hle, hid, _, _, .atom ρ =>
      congrArg WFF.atom (Rel.collapse_shift_same hs hc hle hid ρ)
  | _, _, _, _, _, hs, hc, hle, hid, _, _, .eq t s =>
      congrArg₂ WFF.eq (eq_of_heq (Sigma.mk.inj (Term.collapse_shift_same hs hc hle hid t)).2)
        (eq_of_heq (Sigma.mk.inj (Term.collapse_shift_same hs hc hle hid s)).2)
  | _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, hs, hc, hle, hid, hs₁, hs₂, .and φ ψ =>
      congrArg₂ WFF.and (WFF.collapse_shift_same hs hc hle hid hs₁ hs₂ φ)
        (WFF.collapse_shift_same hs hc hle hid hs₁ hs₂ ψ)
  | _, _, _, _, _, hs, hc, hle, hid, hs₁, hs₂, .or φ ψ =>
      congrArg₂ WFF.or (WFF.collapse_shift_same hs hc hle hid hs₁ hs₂ φ)
        (WFF.collapse_shift_same hs hc hle hid hs₁ hs₂ ψ)
  | _, _, _, _, _, hs, hc, hle, hid, hs₁, hs₂, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.collapse_shift_same hs hc hle hid hs₁ hs₂ φ)
        (WFF.collapse_shift_same hs hc hle hid hs₁ hs₂ ψ)
  | _, _, _, _, _, hs, hc, hle, hid, hs₁, hs₂, .all T φ =>
      congrArg (WFF.all T) (WFF.collapse_shift_same (hs.insert (hs₁.rootFresh le_rfl) T)
        (hc.insert (hs₂.rootFresh le_rfl) T) (hle.insert _ T) (hid.insert _ T) (hs₁.insert T)
        (hs₂.insert T) φ)
  | _, _, _, _, _, hs, hc, hle, hid, hs₁, hs₂, .ex T φ =>
      congrArg (WFF.ex T) (WFF.collapse_shift_same (hs.insert (hs₁.rootFresh le_rfl) T)
        (hc.insert (hs₂.rootFresh le_rfl) T) (hle.insert _ T) (hid.insert _ T) (hs₁.insert T)
        (hs₂.insert T) φ)
  | _, _, _, _, _, hs, hc, hle, hid, hs₁, hs₂, .box φ =>
      congrArg WFF.box (WFF.collapse_shift_same hs.boxIn hc.boxIn hle.boxIn hid.boxIn hs₁.boxIn
        hs₂.boxIn φ)
  | m, Γ₁, _, Γ₃, _, hs, hc, hle, hid, hs₁, hs₂, .dia x hx φ => by
      have key : ∀ (y : VarSymb) (_hy : y = (x.shift m).collapse m)
          (P : ∃ X, Γ₃.ref y = some (.VTypeDia X)) (hle' : (Γ₁.diaIn x).Le (Γ₃.diaIn y)),
          WFF.collapse hc hs₂ (WFF.shift hs hs₁ (.dia x hx φ)) = .dia y P (WFF.mono hle' φ) := by
        intro y hy P hle'
        subst hy
        exact congrArg (WFF.dia _ P) (WFF.collapse_shift_same (hs.diaIn x) (hc.diaIn _) hle'
          (hid.diaIn x) (hs₁.diaIn x) (hs₂.diaIn _) φ)
      exact hx.elim fun _ hX => key x (hid x _ hX).symm _ _
  | _, _, _, _, _, hs, hc, hle, hid, _, _, .here hT s t =>
      WFF.here_congr hT (Term.collapse_shift_same hs hc hle hid s)
        (Term.collapse_shift_same hs hc hle hid t)
  | _, _, _, _, _, hs, hc, hle, hid, _, _, .back hB L s t =>
      WFF.back_congr hB L (Term.collapse_shift_same hs hc hle hid s)
        (Term.collapse_shift_same hs hc hle hid t)
  | _, _, _, _, _, hs, hc, hle, hid, hs₁, hs₂, .retS hB S t Φ =>
      WFF.retS_congr hB S (Term.collapse_shift_same hs hc hle hid t)
        (WFF.collapse_shift_same (hs.boxIn.insert (hs₁.boxIn.rootFresh le_rfl) _)
          (hc.boxIn.insert (hs₂.boxIn.rootFresh le_rfl) _) (hle.boxIn.insert _ _)
          (hid.boxIn.insert _ _) (hs₁.boxIn.insert _) (hs₂.boxIn.insert _) Φ)
  | m, Γ₁, _, Γ₃, _, hs, hc, hle, hid, hs₁, hs₂, .retxS hB y hy S t Φ => by
      have key : ∀ (z : VarSymb) (_hz : z = (y.shift m).collapse m)
          (P : ∃ Y, Γ₃.ref z = some (.VTypeDia Y))
          (hle' : ((Γ₁.diaIn y).insert (.bnd _) S.ty).Le ((Γ₃.diaIn z).insert (.bnd _) S.ty)),
          WFF.collapse hc hs₂ (WFF.shift hs hs₁ (.retxS hB y hy S t Φ)) =
            .retxS hB z P S (Term.mono hle t) (WFF.mono hle' Φ) := by
        intro z hz P hle'
        subst hz
        exact WFF.retxS_congr hB _ P S (Term.collapse_shift_same hs hc hle hid t)
          (WFF.collapse_shift_same ((hs.diaIn y).insert ((hs₁.diaIn y).rootFresh le_rfl) _)
            ((hc.diaIn _).insert ((hs₂.diaIn _).rootFresh le_rfl) _) hle'
            ((hid.diaIn y).insert _ _) ((hs₁.diaIn y).insert _) ((hs₂.diaIn _).insert _) Φ)
      exact hy.elim fun _ hY => key y (hid y _ hY).symm _ _

end CollapseShift

/-! ## The abstraction at a kept witness -/

section Abs

variable {σ : Signature}

/-- Realising a negation is negating the realisation: the three operations are structural. -/
theorem WFF.realiseAtA_neg {Γ : Ctx} [Γ.Presented] (hT : ModalSys.T = true) (x : VarSymb)
    {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A)) {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    (χ : WFF σ (Γ.diaIn x) 0) :
    WFF.realiseAtA hT x hxA t₀ χ.neg = (WFF.realiseAtA hT x hxA t₀ χ).neg := rfl

/-- Abstraction commutes with weakening (the formula form of `Term.mono_diaAbsA`). -/
theorem WFF.mono_diaAbsA {Γ Γ' : Ctx} [Γ.Presented] [Γ'.Presented] {x : VarSymb}
    {A : VarType} (h : Γ.Le Γ') (hcA : Γ.ref x = some (.VTypeDia A))
    (hcA' : Γ'.ref x = some (.VTypeDia A)) (χ : WFF σ (Γ.diaIn x) 0) :
    WFF.mono (h.boxIn.insert (.bnd 0) A) (WFF.diaAbsA x hcA χ) =
      WFF.diaAbsA x hcA' (WFF.mono (h.diaIn x) χ) := by
  unfold WFF.diaAbsA
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ χ
  refine Subst.sim_of ?_
  intro v U _ _
  match v with
  | .step u .dia =>
      change SubE.Sim U (SubE.mono _ (if u = x then SubE.ren (.root (.bnd 0))
        else .hide)) (if u = x then SubE.ren (.root (.bnd 0)) else .hide)
      by_cases hu : u = x
      · simp only [if_pos hu]
        exact .refl _
      · simp only [if_neg hu]
        exact .refl _
  | .step _ .box => exact .refl _
  | .step _ .keep => exact .refl _
  | .root _ => exact .refl _
  | .step _ .fst => exact .refl _
  | .step _ .snd => exact .refl _
  | .step _ .here => exact .refl _

/-- ⭐**Abstracting the kept witness's content, after the shift, is abstracting the witness's
    content, before it**: `x.dia ↦ x.keep.dia ↦ bnd 0` and `bnd 0 ↦ bnd 0`; the `□` entries go
    one keep further in on both sides. -/
theorem Subst.shiftCorr_diaAbsA_keep (hF : ModalSys.Four = true) {Γ : Ctx} {x : VarSymb}
    {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A))
    (hnb : ∀ p : List Step, Γ.ref ((VarSymb.step x .dia).ext p) = none)
    (h₀ : Γ.boxIn (.root (.bnd 0)) = none) (hrf : Γ.boxIn.RootFresh (.bnd 0)) :
    Subst.ShiftCorr (Γ.diaIn x) ((Ctx.shifts_boxIn_boxIn hF Γ).insert hrf A)
      (Subst.diaAbsA σ (Γ.boxIn.insert (.bnd 0) A) x)
      (Subst.diaAbsA σ (Γ.boxIn.boxIn.insert (.bnd 0) A) (.step x .keep)) := by
  refine Subst.shiftCorr_of (Subst.ok_diaAbsA hxA hnb h₀) ?_
  intro v T hlp hv
  match v with
  | .step u .dia =>
      have hux : u = x := by
        change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        split_ifs at hv with h
        exact h
      subst hux
      rw [VarSymb.shift_level_zero (rfl : Step.isProj .dia = false),
        Subst.at_nonproj _ (rfl : (VarSymb.step (VarSymb.step u .keep) .dia).lastProj = false)]
      change SubE.Sim T (if VarSymb.step u .keep = VarSymb.step u .keep then
          SubE.ren (.root (.bnd 0)) else .hide)
        ((if u = u then SubE.ren (.root (.bnd 0)) else .hide).shift _)
      rw [if_pos rfl, if_pos rfl]
      exact .refl _
  | .step u .box =>
      rw [VarSymb.shift_level_zero (rfl : Step.isProj .box = false),
        Subst.at_nonproj _ (rfl : (VarSymb.step (VarSymb.step u .keep) .box).lastProj = false)]
      exact .refl _
  | .step u .keep =>
      rw [VarSymb.shift_level_zero (rfl : Step.isProj .keep = false),
        Subst.at_nonproj _ (rfl : (VarSymb.step (VarSymb.step u .keep) .keep).lastProj = false)]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hlp
  | .step _ .snd => cases hlp
  | .step _ .here => cases hlp

/-- ⭐**Realising the kept witness at the witness's content gives the formula back** (T + 4): the
    abstraction commutes with the shift (`Subst.shiftCorr_diaAbsA_keep`), the realisation's
    collapse undoes the shift (`WFF.collapse_shift_same`, every `□` view being kept-only), and
    reading the abstraction back at the content is the round trip (`WFF.viewReadAtA_diaAbsA`). -/
theorem WFF.realiseAtA_shift_keep (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    {Γ Δ : Ctx} [hp : Γ.Presented] [Δ.Presented] {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) (hle : (Γ.diaIn x).Le Δ)
    (hk : Δ.ref (.step x .keep) = some (.VTypeDia X)) (hdia : Δ.ref (.step x .dia) = some X)
    (χ : WFF σ (Γ.diaIn x) 0) :
    WFF.realiseAtA hT (.step x .keep) hk (Term.eta (.step x .dia) X hdia)
        (WFF.mono (((Ctx.le_boxIn_diaIn Γ x).trans hle).diaIn (.step x .keep))
          (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots χ)) =
      WFF.mono hle χ := by
  have hkO : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  have hk₀ : Γ.boxIn.ref (.step x .keep) = some (.VTypeDia X) :=
    Ctx.ref_keep_of' hF hx VarType.keepable_dia
  have hle₀ : Γ.boxIn.Le Δ := (Ctx.le_boxIn_diaIn Γ x).trans hle
  have h₀ : Γ.boxIn (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root
  have hrf : Γ.boxIn.RootFresh (.bnd 0) :=
    (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  have hrf₂ : Γ.boxIn.boxIn.RootFresh (.bnd 0) :=
    (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  -- the abstraction at `Δ`, pulled back out of the weakening
  have e₁ := WFF.mono_diaAbsA hle₀ hk₀ hk
    (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots χ)
  -- the abstraction of the shifted formula is the shifted abstraction
  have e₂ : WFF.diaAbsA (.step x .keep) hk₀
        (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots χ) =
      WFF.shift ((Ctx.shifts_boxIn_boxIn hF Γ).insert hrf X)
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert X) (WFF.diaAbsA x hx χ) :=
    (WFF.shift_subst (Ctx.shifts_diaIn_keep hF Γ x) ((Ctx.shifts_boxIn_boxIn hF Γ).insert hrf X)
      _ _ _ _ _ _ _ _ _ _ (Subst.shiftCorr_diaAbsA_keep hF hx (hp.not_below hx rfl) h₀ hrf)
      χ).symm
  -- the realisation's collapse undoes the shift
  have e₃ : WFF.collapse ((Ctx.collapses_boxIn_self hT Γ.boxIn).insert hrf₂ X)
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert X)
        (WFF.shift ((Ctx.shifts_boxIn_boxIn hF Γ).insert hrf X)
          ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert X) (WFF.diaAbsA x hx χ)) =
      WFF.diaAbsA x hx χ := by
    rw [WFF.collapse_shift_same _ _ (Ctx.Le.refl _)
      ((Ctx.shiftCollapseId_keepOnly hkO Γ).insert _ _), WFF.mono_refl]
  unfold WFF.realiseAtA WFF.hereRead
  rw [← e₁, e₂, WFF.collapse_mono ((Ctx.collapses_boxIn_self hT Γ.boxIn).insert hrf₂ X) _
    (hle₀.boxIn.insert _ X) (hle₀.insert _ X) ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert X),
    e₃]
  -- reading the abstraction back at the content
  conv_rhs => rw [← WFF.viewReadAtA_diaAbsA x hx χ]
  unfold WFF.viewReadAtA WFF.renameRoot WFF.instantiate WFF.substRoot
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ _
  refine Subst.sim_of ?_
  intro v U _ hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hU : U = X := by
      change (if VarSymb.root (Root.bnd 0) = .root (.bnd 0) then some X else _) = some U at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    subst hU
    change SubE.Sim U (if VarSymb.root (Root.bnd 0) = .root (.bnd 0) then
        SubE.tm (Term.eta (.step x .dia) U hdia) else _)
      (SubE.mono _ (if VarSymb.root (Root.bnd 0) = .root (.bnd 0) then
        SubE.ren (.step x .dia) else _))
    rw [if_pos rfl, if_pos rfl]
    exact .eta_ren _ hdia
  · change SubE.Sim U (if v = .root (.bnd 0) then _ else SubE.ren v)
      (SubE.mono _ (if v = .root (.bnd 0) then _ else SubE.ren v))
    rw [if_neg hvr, if_neg hvr]
    exact .refl _

end Abs

end V12M
