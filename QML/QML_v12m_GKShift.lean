import QML.QML_v12m_GKSubst
import QML.QML_v12m_GViewSubst
import QML.QML_v12m_LiftT

/-!
# QML v12m — shifting GK derivations (weak 4)

Under 4 a modal rule's premise carries the 4-copies (`cp4`, `kp4`): formulas shifted one view
further in.  The cut reductions at them re-derive a conclusion inside a view, by shifting a whole
derivation (`GK.shiftD`) and applying the rule one level in.  This file has what that needs.

* `Ctx.Leveled Γ L`: every declared address of `Γ` lies `L r` level steps below its root `r`.
  Presented contexts are leveled (`Ctx.Presented.leveled`), which is what makes the shifted
  identity a coherent substitution (`Subst.coh_atShiftL`, `coh_atShift` for any leveling).
* ⭐`GK.shiftD`: a derivation over `Γ₁` shifted to `Γ₂` (`Ctx.Shifts 0 Γ₁ Γ₂`), height kept.
* `WFF.shift_mono`, `WFF.weight_shift`: shifting commutes with weakening and keeps the weight.
* `GK.shift_cp4`, `GK.shift_kp4`: shifting the copies gives the copies of the shifted formulas
  (`WFF.shift_shift_same`: two adjacent `keep`s, in either order).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-! ## Leveled contexts -/

namespace Ctx

/-- Every declared address of `Γ` lies `L r` level steps below its root `r`. -/
def Leveled (Γ : Ctx) (L : Root → ℕ) : Prop :=
  ∀ v T, v.lastProj = false → Γ v = some T → Step.levels v.path = L v.rt

theorem Leveled.ref {Γ : Ctx} {L : Root → ℕ} (h : Γ.Leveled L) :
    ∀ {v : VarSymb} {T : VarType}, Γ.ref v = some T → Step.levels v.path = L v.rt
  | .root _, T, hv => h _ T rfl hv
  | .step v s, T, hv => by
      by_cases hs : s.isProj = true
      · rw [Γ.ref_step_proj v hs] at hv
        cases hT : Γ.ref v with
        | none => rw [hT] at hv; cases hv
        | some T' =>
            change Step.levels (v.path ++ [s]) = L v.rt
            rw [Step.levels_append, h.ref hT]
            simp [Step.levels, hs]
      · rw [Γ.ref_step_nonproj v hs] at hv
        exact h _ T (Bool.eq_false_iff.mpr hs) hv

theorem Leveled.levels_step {Γ : Ctx} {L : Root → ℕ} (h : Γ.Leveled L) {u : VarSymb}
    {s : Step} (hs : s.isProj = false) {T : VarType} (hu : Γ.ref u = some T) :
    Step.levels (VarSymb.step u s).path = L u.rt + 1 := by
  change Step.levels (u.path ++ [s]) = _
  rw [Step.levels_append, h.ref hu]
  simp [Step.levels, hs]

theorem Leveled.boxIn {Γ : Ctx} {L : Root → ℕ} (h : Γ.Leveled L) :
    Γ.boxIn.Leveled (fun r => L r + 1) := by
  intro v T _ hv
  match v, hv with
  | .step u .box, hv => exact h.levels_step rfl (boxIn_box hv).2
  | .step u .keep, hv => exact h.levels_step rfl (boxIn_keep hv).2.1
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

theorem Leveled.diaIn {Γ : Ctx} {L : Root → ℕ} (h : Γ.Leveled L) (x : VarSymb) :
    (Γ.diaIn x).Leveled (fun r => L r + 1) := by
  intro v T hlp hv
  match v, hv with
  | .step u .dia, hv =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      cases hx : Γ.ref u with
      | none => rw [hx] at hv; cases hv
      | some U => exact h.levels_step rfl hx
  | .step u .box, hv => exact h.boxIn _ T hlp hv
  | .step u .keep, hv => exact h.boxIn _ T hlp hv
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

omit [ModalSys] in
theorem Leveled.insert {Γ : Ctx} {L : Root → ℕ} (h : Γ.Leveled L) {r : Root}
    (hr : Γ.RootFresh r) (T : VarType) : (Γ.insert r T).Leveled (Function.update L r 0) := by
  intro v U hlp hv
  simp only [Ctx.insert] at hv
  split_ifs at hv with hvr
  · subst hvr
    simp [VarSymb.path, Step.levels, VarSymb.rt]
  · have hne : v.rt ≠ r := fun he => by rw [hr v he] at hv; cases hv
    rw [Function.update_of_ne hne]
    exact h v U hlp hv

end Ctx

/-- A presentation is leveled: its depth assignment (`CtxExpr.levelDepth`) at the declared
    addresses. -/
theorem CtxExpr.leveled (e : CtxExpr) (he : e.Fresh) : ∃ L, e.denote.Leveled L := by
  obtain ⟨d, hd, -⟩ := e.levelDepth he
  exact ⟨d, fun v T hlp hv => hd v T ((Ctx.ref_nonproj _ hlp).trans hv)⟩

/-- A presented context is leveled. -/
theorem Ctx.Presented.leveled (Γ : Ctx) [h : Γ.Presented] : ∃ L, Γ.Leveled L :=
  h.denote_eq ▸ h.expr.leveled h.fresh

/-! ## The shifted identity -/

namespace Subst

variable {Δ : Ctx}

/-- `coh_atShift` for any leveling: an address `L r` levels below its root is shifted at the
    level step just after the declared part. -/
theorem coh_atShiftL {Γ Γ' : Ctx} (C : Ctx.Shifts 0 Γ Γ') {Ψ : Subst σ Δ} (hΨ : Ok Γ' Ψ)
    {ι : VarSymb → VarSymb} (hc : Coh ι Γ' Ψ) {L : Root → ℕ} (hlv : Γ.Leveled L) :
    Coh (fun y => ι (y.shift (Step.levels y.path - L y.rt))) Γ (atShift Ψ) := by
  haveI : ModalSys.NoOpt := ⟨ModalSys.noOpt_of_Four C.hF⟩
  refine coh_of (ok_atShift C hΨ) fun v T hlp hv p => ?_
  change (Ψ.at (v.shift 0)).idxAlong p = _
  rw [hc _ _ (C v T ((Ctx.ref_nonproj Γ hlp).trans hv)) p, VarSymb.ext_path, VarSymb.ext_rt,
    Step.levels_append, hlv v T hlp hv,
    show L v.rt + Step.levels p - L v.rt = 0 + Step.levels p by omega, VarSymb.shift_ext]

end Subst

/-! ## Shifting commutes with weakening; weight -/

theorem Rel.shift_mono {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂)
    (h' : Ctx.Shifts k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁') (l₂ : Γ₂.Le Γ₂') :
    {n : ℕ} → (ρ : Rel σ Γ₁ n) → Rel.shift h' (Rel.mono l₁ ρ) = Rel.mono l₂ (Rel.shift h ρ)
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.shift h' (Rel.mono l₁ ρ)) (Term.shift h' (Term.mono l₁ t)) = _
      rw [Rel.shift_mono h h' l₁ l₂ ρ, Term.shift_mono h h' l₁ l₂ t]
      rfl

/-- Shifting commutes with weakening. -/
theorem WFF.shift_mono : ∀ {k : ℕ} {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} {d : ℕ} (h : Ctx.Shifts k Γ₁ Γ₂)
    (h' : Ctx.Shifts k Γ₁' Γ₂') (l₁ : Γ₁.Le Γ₁') (l₂ : Γ₂.Le Γ₂') (hs : Γ₁.SlotsFrom d)
    (hs' : Γ₁'.SlotsFrom d) (φ : WFF σ Γ₁ d),
    WFF.shift h' hs' (WFF.mono l₁ φ) = WFF.mono l₂ (WFF.shift h hs φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, _, _, .atom ρ =>
      congrArg WFF.atom (Rel.shift_mono h h' l₁ l₂ ρ)
  | _, _, _, _, _, _, h, h', l₁, l₂, _, _, .eq t s => by
      change WFF.eq (Term.shift h' (Term.mono l₁ t)) (Term.shift h' (Term.mono l₁ s)) = _
      rw [Term.shift_mono h h' l₁ l₂ t, Term.shift_mono h h' l₁ l₂ s]
      rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .and φ ψ =>
      congrArg₂ WFF.and (WFF.shift_mono h h' l₁ l₂ hs hs' φ) (WFF.shift_mono h h' l₁ l₂ hs hs' ψ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .or φ ψ =>
      congrArg₂ WFF.or (WFF.shift_mono h h' l₁ l₂ hs hs' φ) (WFF.shift_mono h h' l₁ l₂ hs hs' ψ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.shift_mono h h' l₁ l₂ hs hs' φ) (WFF.shift_mono h h' l₁ l₂ hs hs' ψ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .all T φ =>
      congrArg (WFF.all T) (WFF.shift_mono (h.insert (hs.rootFresh le_rfl) T)
        (h'.insert (hs'.rootFresh le_rfl) T) (l₁.insert _ T) (l₂.insert _ T) (hs.insert T)
        (hs'.insert T) φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .ex T φ =>
      congrArg (WFF.ex T) (WFF.shift_mono (h.insert (hs.rootFresh le_rfl) T)
        (h'.insert (hs'.rootFresh le_rfl) T) (l₁.insert _ T) (l₂.insert _ T) (hs.insert T)
        (hs'.insert T) φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .box φ =>
      congrArg WFF.box (WFF.shift_mono h.boxIn h'.boxIn l₁.boxIn l₂.boxIn hs.boxIn hs'.boxIn φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .dia x _ φ =>
      congrArg (WFF.dia _ _) (WFF.shift_mono (h.diaIn x) (h'.diaIn x) (l₁.diaIn x)
        (l₂.diaIn _) (hs.diaIn x) (hs'.diaIn x) φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, _, _, .here hT s t => by
      change WFF.here hT (Term.shift h' (Term.mono l₁ s)) (Term.shift h' (Term.mono l₁ t)) = _
      rw [Term.shift_mono h h' l₁ l₂ s, Term.shift_mono h h' l₁ l₂ t]
      rfl
  | _, _, _, _, _, _, h, h', l₁, l₂, _, _, .back hB L s t => by
      change WFF.back hB L (Term.shift h' (Term.mono l₁ s)) (Term.shift h' (Term.mono l₁ t)) = _
      rw [Term.shift_mono h h' l₁ l₂ s, Term.shift_mono h h' l₁ l₂ t]
      rfl
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .retS hB S t Φ =>
      WFF.retS_congr' hB S (Term.shift_mono h h' l₁ l₂ t)
        (WFF.shift_mono (h.boxIn.insert (hs.boxIn.rootFresh le_rfl) _)
          (h'.boxIn.insert (hs'.boxIn.rootFresh le_rfl) _) (l₁.boxIn.insert _ _)
          (l₂.boxIn.insert _ _) (hs.boxIn.insert _) (hs'.boxIn.insert _) Φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .retxS hB y _ S t Φ =>
      WFF.retxS_congr' hB _ _ S (Term.shift_mono h h' l₁ l₂ t)
        (WFF.shift_mono ((h.diaIn y).insert ((hs.diaIn y).rootFresh le_rfl) _)
          ((h'.diaIn y).insert ((hs'.diaIn y).rootFresh le_rfl) _) ((l₁.diaIn y).insert _ _)
          ((l₂.diaIn _).insert _ _) ((hs.diaIn y).insert _) ((hs'.diaIn y).insert _) Φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .link hV hF t Φ =>
      WFF.link_congr' hV hF (Term.shift_mono h h' l₁ l₂ t)
        (WFF.shift_mono (h.boxIn.insert (hs.boxIn.rootFresh le_rfl) _)
          (h'.boxIn.insert (hs'.boxIn.rootFresh le_rfl) _) (l₁.boxIn.insert _ _)
          (l₂.boxIn.insert _ _) (hs.boxIn.insert _) (hs'.boxIn.insert _) Φ)
  | _, _, _, _, _, _, h, h', l₁, l₂, hs, hs', .linkx hV hF y _ t Φ =>
      WFF.linkx_congr' hV hF _ _ (Term.shift_mono h h' l₁ l₂ t)
        (WFF.shift_mono ((h.diaIn y).insert ((hs.diaIn y).rootFresh le_rfl) _)
          ((h'.diaIn y).insert ((hs'.diaIn y).rootFresh le_rfl) _) ((l₁.diaIn y).insert _ _)
          ((l₂.diaIn _).insert _ _) ((hs.diaIn y).insert _) ((hs'.diaIn y).insert _) Φ)
  | _, _, _, _, _, _, h, _, _, _, _, _, .optx hO _ _ _ =>
      False.elim (by have := ModalSys.noOpt_of_Four h.hF; rw [hO] at this; cases this)

/-- Shifting keeps the weight. -/
theorem WFF.weight_shift : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} {d : ℕ} (h : Ctx.Shifts k Γ₁ Γ₂)
    (hs : Γ₁.SlotsFrom d) (φ : WFF σ Γ₁ d), (WFF.shift h hs φ).weight = φ.weight
  | _, _, _, _, _, _, .atom _ => rfl
  | _, _, _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, h, hs, .and φ ψ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift h hs φ, WFF.weight_shift h hs ψ]
  | _, _, _, _, h, hs, .or φ ψ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift h hs φ, WFF.weight_shift h hs ψ]
  | _, _, _, _, h, hs, .imp φ ψ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift h hs φ, WFF.weight_shift h hs ψ]
  | _, _, _, _, _, _, .all _ φ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift _ _ φ]
  | _, _, _, _, _, _, .ex _ φ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift _ _ φ]
  | _, _, _, _, _, _, .box φ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift _ _ φ]
  | _, _, _, _, _, _, .dia _ _ φ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift _ _ φ]
  | _, _, _, _, _, _, .here _ _ _ => rfl
  | _, _, _, _, _, _, .back _ _ _ _ => rfl
  | _, _, _, _, _, _, .retS _ _ _ Φ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift _ _ Φ]
  | _, _, _, _, _, _, .retxS _ _ _ _ _ Φ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift _ _ Φ]
  | _, _, _, _, _, _, .link _ _ _ Φ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift _ _ Φ]
  | _, _, _, _, _, _, .linkx _ _ _ _ _ Φ => by
      simp only [WFF.shift, WFF.weight]
      rw [WFF.weight_shift _ _ Φ]
  | _, _, _, _, h, _, .optx hO _ _ _ =>
      False.elim (by have := ModalSys.noOpt_of_Four h.hF; rw [hO] at this; cases this)

/-! ## Shifting a derivation -/

namespace GK

/-- ⭐**Shifting a derivation** one level in, height kept: the shifted identity is a coherent
    substitution over a leveled context. -/
theorem shiftD {n : ℕ} {Γ₁ Γ₂ : Ctx} [Γ₁.NoSlots] [Γ₂.Presented] (C : Ctx.Shifts 0 Γ₁ Γ₂)
    {L : Root → ℕ} (hlv : Γ₁.Leveled L) {Δ Θ : List (WFF σ Γ₁ 0)} (p : GK σ n Γ₁ Δ Θ) :
    GK σ n Γ₂ (Δ.map (WFF.shift C Ctx.NoSlots.slots))
      (Θ.map (WFF.shift C Ctx.NoSlots.slots)) := by
  haveI : ModalSys.NoOpt := ⟨ModalSys.noOpt_of_Four C.hF⟩
  have hθ := Subst.ok_atShift C (Subst.ok_idRen (σ := σ) (Δ := Γ₂))
  have hc := Subst.coh_atShiftL C (Subst.ok_idRen (σ := σ) (Δ := Γ₂)) Subst.coh_idRen hlv
  have key : ∀ φ : WFF σ Γ₁ 0,
      WFF.subst _ _ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ =
        WFF.shift C Ctx.NoSlots.slots φ := fun φ => by
    rw [← WFF.subst_shift C Ctx.NoSlots.slots Ctx.NoSlots.slots (Subst.idRen Γ₂) Subst.ok_idRen
      Subst.coh_idRen _ hθ hc Ctx.NoSlots.slots (Subst.preShift_atShift _ _) φ,
      WFF.subst_ren (Ctx.Le.refl Γ₂) _ _ _ _ _ (fun v _ _ => Subst.at_idRen v), WFF.mono_refl]
  have q := p.subst (Subst.atShift (Subst.idRen Γ₂)) hθ hc Ctx.NoSlots.slots
  rwa [List.map_congr_left fun φ _ => key φ, List.map_congr_left fun φ _ => key φ] at q

end GK

/-! ## The copies under shifting -/

theorem cp4_append {Γ : Ctx} [Γ.NoSlots] (Δ₁ Δ₂ : List (WFF σ Γ.boxIn 0)) :
    cp4 (Δ₁ ++ Δ₂) = cp4 Δ₁ ++ cp4 Δ₂ := by
  unfold cp4; split
  · exact List.map_append
  · rfl

theorem kp4_append {Γ : Ctx} [Γ.NoSlots] (L₁ L₂ : List (WFF σ Γ 0)) :
    kp4 (L₁ ++ L₂) = kp4 L₁ ++ kp4 L₂ := by
  unfold kp4; split
  · exact List.flatMap_append
  · rfl

section Copies

variable {Γ : Ctx} [Γ.Presented] (hF : ModalSys.Four = true)

/-- Shifting a boxed hypothesis' copy is copying the shifted hypothesis. -/
theorem shift_cp4 (Δ₁ : List (WFF σ Γ.boxIn 0)) :
    (cp4 Δ₁).map (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots) =
      cp4 (Δ₁.map (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots)) := by
  unfold cp4
  rw [dif_pos hF, dif_pos hF, List.map_map, List.map_map]
  refine List.map_congr_left fun χ _ => ?_
  exact congrArg WFF.box (WFF.shift_shift_same (Ctx.shifts_boxIn_boxIn hF Γ)
    (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) (Ctx.shifts_boxIn_boxIn hF Γ).boxIn _ _ χ).symm

theorem shift_keepDia (A : WFF σ Γ 0) :
    (WFF.keepDia hF A).map (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots) =
      (WFF.keepDia hF A).flatMap (WFF.keepDia hF) := by
  cases A
  case dia y hy θ =>
    simp only [WFF.keepDia, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact congrArg (fun φ => [φ]) (congrArg (WFF.dia _ _) (WFF.shift_shift_same
      (Ctx.shifts_diaIn_keep hF Γ y) (Ctx.shifts_diaIn_keep hF Γ.boxIn (.step y .keep))
      ((Ctx.shifts_boxIn_boxIn hF Γ).diaIn (.step y .keep)) _ _ θ).symm)
  all_goals rfl

/-- Shifting a conclusion's copy is copying the copy. -/
theorem shift_kp4 (L : List (WFF σ Γ 0)) :
    (kp4 L).map (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots) = kp4 (kp4 L) := by
  unfold kp4
  rw [dif_pos hF, dif_pos hF, List.map_flatMap, List.flatMap_assoc]
  exact List.flatMap_congr fun A _ => shift_keepDia hF A

/-- Shifting into the kept witness' view commutes with moving the `□` view into the `◇` view. -/
theorem shift_mono_diaIn (y : VarSymb) (χ : WFF σ Γ.boxIn 0) :
    WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots
        (WFF.mono (Ctx.le_boxIn_diaIn Γ y) χ) =
      WFF.mono (Ctx.le_boxIn_diaIn Γ.boxIn (.step y .keep))
        (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots χ) :=
  WFF.shift_mono _ _ _ _ _ _ χ

end Copies

end V12M
