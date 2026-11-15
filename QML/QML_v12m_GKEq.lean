import QML.QML_v12m_GKCut

/-!
# QML v12m — GK at K: identity and replacement

Two derived rules of GK in K, for the equivalence with natural deduction
(`docs/v12-metatheory-todo.md`, item 4):

* ⭐`GK.ident`: `φ ⇒ φ` for every formula (axioms give it only for atoms).
* ⭐`GK.replace`: `t = s, φ(t) ⇒ φ(s)` for every formula `φ` with a base-type slot, ND's `eq_elim`.
  `repl` replaces only in atoms; the rest is an induction on `φ`, stated for **two
  substitutions** `θ₁`, `θ₂` that agree everywhere except at the slot `bnd 0`, sent to `t` and `s`
  (`GK.replaceGen`).  Under a quantifier both become `toFree` (`WFF.bindFree_toFree`,
  `WFF.instantiate_toFree`); in the `□` and `◇_x` views the slot is invisible, so both sides are
  the same formula (`Subst.sim_box_of_agree`, `Subst.sim_dia_of_agree`); at an atom the hole
  formula is the atom substituted by `θ₁.under 0 0` (`instantiate_underHole`).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-- ⭐**The flags GK's systems turn off**: every one but weak D, weak 4 and weak T, with T only
    alongside `Opt` (`ModalSys.TOpt`; with `Opt` 4 is off, `ModalSys.optStage`).  So K, KD, K4 and
    KD4, and K, KD, KT and KDT with `Opt` on (docs §12.33, §12.35). -/
class ModalSys.GKBase [ModalSys] : Prop where
  tOpt : ModalSys.T = true → ModalSys.Opt = true
  noTStrong : ModalSys.TStrong = false
  noDStrong : ModalSys.DStrong = false
  noB : ModalSys.B = false
  noBStrong : ModalSys.BStrong = false
  noBStrongW : ModalSys.BStrongW = false
  noFourStrong : ModalSys.FourStrong = false
  noFourStrongW : ModalSys.FourStrongW = false
  noFive : ModalSys.Five = false
  noFiveStrong : ModalSys.FiveStrong = false

/-- **The systems of GK with `Opt` off**: K, KD, K4 and KD4 in the `◇⁰`-free language. -/
class ModalSys.GKSys [ModalSys] : Prop extends ModalSys.GKBase, ModalSys.NoOpt

instance ModalSys.GKBase.toTOpt [ModalSys] [ModalSys.GKBase] : ModalSys.TOpt :=
  ⟨ModalSys.GKBase.tOpt⟩

/-- With `Opt` off, T is off. -/
instance ModalSys.GKSys.toNoT [ModalSys] [ModalSys.GKSys] : ModalSys.NoT := by
  refine ⟨?_⟩
  cases h : ModalSys.T
  · rfl
  · exact absurd (ModalSys.GKBase.tOpt h) (by rw [ModalSys.NoOpt.noOpt]; decide)

/-- KD: weak D. -/
def ModalSys.KD : ModalSys :=
  { T := false, Four := false, TStrong := false, D := true, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := false, FiveStrong := false }

/-- K4: weak 4. -/
def ModalSys.K4 : ModalSys :=
  { T := false, Four := true, TStrong := false, D := false, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := false, FiveStrong := false }

/-- KD4: weak D and weak 4. -/
def ModalSys.KD4 : ModalSys :=
  { T := false, Four := true, TStrong := false, D := true, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := false, FiveStrong := false }

instance : @ModalSys.GKSys ModalSys.K :=
  @ModalSys.GKSys.mk ModalSys.K
    (@ModalSys.GKBase.mk ModalSys.K (fun h => absurd h (by decide)) rfl rfl rfl rfl rfl
      rfl rfl rfl rfl)
    (@ModalSys.NoOpt.mk ModalSys.K rfl)

instance : @ModalSys.GKSys ModalSys.KD :=
  @ModalSys.GKSys.mk ModalSys.KD
    (@ModalSys.GKBase.mk ModalSys.KD (fun h => absurd h (by decide)) rfl rfl rfl rfl rfl
      rfl rfl rfl rfl)
    (@ModalSys.NoOpt.mk ModalSys.KD rfl)

instance : @ModalSys.GKSys ModalSys.K4 :=
  @ModalSys.GKSys.mk ModalSys.K4
    (@ModalSys.GKBase.mk ModalSys.K4 (fun h => absurd h (by decide)) rfl rfl rfl rfl rfl
      rfl rfl rfl rfl)
    (@ModalSys.NoOpt.mk ModalSys.K4 rfl)

instance : @ModalSys.GKSys ModalSys.KD4 :=
  @ModalSys.GKSys.mk ModalSys.KD4
    (@ModalSys.GKBase.mk ModalSys.KD4 (fun h => absurd h (by decide)) rfl rfl rfl rfl rfl
      rfl rfl rfl rfl)
    (@ModalSys.NoOpt.mk ModalSys.KD4 rfl)

/-- KT with the box view of possible objects: weak T and `Opt` (docs §12.35). -/
def ModalSys.KTOpt : ModalSys :=
  { T := true, Four := false, TStrong := false, D := false, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := false, FiveStrong := false, Opt := true }

instance : @ModalSys.GKBase ModalSys.KTOpt :=
  @ModalSys.GKBase.mk ModalSys.KTOpt (fun _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## Substitutions agreeing off the base-type addresses -/

namespace Subst

variable {Δ : Ctx}

/-- Two substitutions agreeing at every address of a type other than `Var` agree in the `□`
    view. -/
theorem sim_box_of_agree {Γ₀ : Ctx} {θ₁ θ₂ : Subst σ Δ}
    (hA : ∀ u X, Γ₀.ref u = some X → X ≠ .Var → θ₁.at u = θ₂.at u) :
    Sim Γ₀.boxIn θ₁.box θ₂.box :=
  sim_of (hwit := fun _ y _ hy => by
      change WitE.Sim _ (θ₁.at y).toWit (θ₂.at y).toWit
      rw [hA y _ (Ctx.boxIn_wit.mp hy).2 (fun h => by cases h)]
      exact .refl _) fun v T _ hv => by
    match v with
    | .step u .box =>
        obtain ⟨_, hu⟩ := Ctx.boxIn_box hv
        change SubE.Sim T (θ₁.at u).unbox (θ₂.at u).unbox
        rw [hA u _ hu (fun h => by cases h)]
        exact .refl _
    | .step u .keep =>
        obtain ⟨_, hu, hk⟩ := Ctx.boxIn_keep hv
        change SubE.Sim T (θ₁.at u).keepE (θ₂.at u).keepE
        rw [hA u _ hu (by rintro rfl; cases hk)]
        exact .refl _
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .dia => cases hv
    | .step _ .here => cases hv

/-- The same in a `◇_x` view. -/
theorem sim_dia_of_agree {Γ₀ : Ctx} {θ₁ θ₂ : Subst σ Δ}
    (hA : ∀ u X, Γ₀.ref u = some X → X ≠ .Var → θ₁.at u = θ₂.at u) (x ιx : VarSymb) :
    Sim (Γ₀.diaIn x) (θ₁.dia x ιx) (θ₂.dia x ιx) :=
  sim_of (hwit := fun _ y _ hy => by
      change WitE.Sim _ ((θ₁.at y).toWit.mono (Ctx.le_boxIn_diaIn Δ ιx))
        ((θ₂.at y).toWit.mono (Ctx.le_boxIn_diaIn Δ ιx))
      rw [hA y _ (Ctx.boxIn_wit.mp (show Γ₀.boxIn.wit y = _ from hy)).2 (fun h => by cases h)]
      exact .refl _) fun v T _ hv => by
    match v with
    | .step u .dia =>
        change (if u = x then (match Γ₀.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        split_ifs at hv with hux
        · subst hux
          cases hx : Γ₀.ref u with
          | none => rw [hx] at hv; cases hv
          | some U =>
              change SubE.Sim T (if u = u then (θ₁.at u).diaBody ιx else SubE.hide)
                (if u = u then (θ₂.at u).diaBody ιx else SubE.hide)
              rw [if_pos rfl, if_pos rfl, hA u U hx (by rintro rfl; rw [hx] at hv; cases hv)]
              exact .refl _
    | .step u .box =>
        obtain ⟨_, hu⟩ := Ctx.boxIn_box (Γ := Γ₀) hv
        change SubE.Sim T ((θ₁.at u).unbox.mono _) ((θ₂.at u).unbox.mono _)
        rw [hA u _ hu (fun h => by cases h)]
        exact .refl _
    | .step u .keep =>
        obtain ⟨_, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ₀) hv
        change SubE.Sim T ((θ₁.at u).keepE.mono _) ((θ₂.at u).keepE.mono _)
        rw [hA u _ hu (by rintro rfl; cases hk)]
        exact .refl _
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .here => cases hv

/-- `under`'s coherence, for a source context that already declares the slot, provided no other
    address declared there, and no witness, has the slot's root. -/
theorem coh_under_occ
    {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {d d' : ℕ} (T : VarType) (h : Δ (.root (.bnd d')) = none)
    (hrt : ∀ v U, Γ v = some U → v ≠ .root (.bnd d) → v.rt ≠ .bnd d)
    (hwrt : ∀ y X, Γ.wit y = some X → y.rt ≠ .bnd d) :
    Coh (VarSymb.shiftSlot ι d d') (Γ.insert (.bnd d) T) (θ.under d d' T h) := by
  have hT' : ∀ {y : VarSymb} {X : VarType}, (Γ.insert (.bnd d) T).witT y = some X →
      (Γ.insert (.bnd d) T) (.step y .at) = some X →
      Γ.witT y = some X ∧ Γ (.step y .at) = some X ∧ y.rt ≠ .bnd d := by
    intro y X hy hyd
    obtain ⟨hT, hO, -⟩ := Ctx.witT_spec hy
    have hyd' := Ctx.insert_ne_some hyd (fun he => by cases he)
    have hr := hrt (.step y .at) X hyd' (fun he => by cases he)
    exact ⟨Ctx.witT_of_at hT hO hyd', hyd', hr⟩
  refine coh_of (ok_under hθ T h) ?_ ?_ ?_ ?_
    (fun y X z hy hyd hz => by
      obtain ⟨hy', hyd', hrt'⟩ := hT' hy hyd
      exact openedT_of_mono (Ctx.le_insert h T) hc hy' hyd' (at_under_ne θ T h hrt')
        (if_neg (t := SubE.ren (.root (.bnd d')))
          (show VarSymb.step y .at ≠ .root (.bnd d) from fun he => by cases he)) hz)
    (fun y X z hy hyd hz => by
      obtain ⟨hy', hyd', hrt'⟩ := hT' hy hyd
      exact openedToT_of_mono (Ctx.le_insert h T) hc hy' hyd' (at_under_ne θ T h hrt') hz)
  rotate_left
  · intro hO y X hy p
    change Γ.wit y = some X at hy
    change ((θ.wit y).mono (Ctx.le_insert h T)).idxAlong p =
      if (y.ext p).rt = .bnd d then _ else ι (y.ext p)
    rw [WitE.idxAlong_mono, VarSymb.ext_rt, if_neg (hwrt y X hy)]
    exact hc.wit hO y X hy p
  · intro hO y X z hy hyd hz
    change Γ.wit y = some X at hy
    have hne : VarSymb.step y .dia ≠ .root (.bnd d) := fun he => by cases he
    replace hyd := Ctx.insert_ne_some hyd hne
    change ((θ.wit y).mono (Ctx.le_insert h T)).idxAlong [] = z at hz
    rw [WitE.idxAlong_mono] at hz
    rw [show θ.under d d' T h (.step y .dia) = (θ (.step y .dia)).mono (Ctx.le_insert h T)
        from if_neg (t := SubE.ren (.root (.bnd d'))) hne,
      show (θ.under d d' T h).wit y = (θ.wit y).mono (Ctx.le_insert h T) from rfl,
      ← WitE.optBody_mono, ← hc.opened hO y X z hy hyd hz]
    simp only [SubE.mono_mono]
  · intro hO y X z hy hyd hz
    change Γ.wit y = some X at hy
    have hne : VarSymb.step y .dia ≠ .root (.bnd d) := fun he => by cases he
    replace hyd := Ctx.insert_ne_some hyd hne
    change ((θ.wit y).mono (Ctx.le_insert h T)).idxAlong [] = z at hz
    rw [WitE.idxAlong_mono] at hz
    obtain ⟨Z, hZ, hZd⟩ := hc.openedTo hO y X z hy hyd hz
    exact ⟨Z, hZ, (Ctx.le_insert h T).ty _ _ hZd⟩
  intro v U hlp hv p
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    rw [show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from by slot_rfl]
    change (VarSymb.root (.bnd d')).ext p =
      (if ((VarSymb.root (.bnd d)).ext p).rt = .bnd d then
        ((VarSymb.root (.bnd d)).ext p).reroot (.bnd d') else ι _)
    have hc0 : (VarSymb.root (Root.bnd d)).rt = Root.bnd d := rfl
    rw [VarSymb.ext_rt, if_pos hc0]
    exact (VarSymb.reroot_ext (.bnd d') (.root (.bnd d)) p).symm
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
    have hrt' := hrt v U hv' hvr
    rw [show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      SubE.idxAlong_mono, ← at_nonproj θ hlp, hc v U ((Ctx.ref_nonproj Γ hlp).trans hv') p]
    change ι (v.ext p) = if (v.ext p).rt = .bnd d then _ else ι (v.ext p)
    rw [VarSymb.ext_rt, if_neg hrt']

/-- Agreement off one root gives agreement of `at` off that root. -/
theorem at_agree {θ₁ θ₂ : Subst σ Δ} {c : Root} (hag : ∀ v, v ≠ .root c → θ₁ v = θ₂ v) :
    ∀ u : VarSymb, u.rt ≠ c → θ₁.at u = θ₂.at u
  | .root r, h => hag _ fun he => h (by cases he; rfl)
  | .step w s, h => by
      change (if s.isStruct then (θ₁.at w).proj s else θ₁ (.step w s)) =
        (if s.isStruct then (θ₂.at w).proj s else θ₂ (.step w s))
      rw [at_agree hag w h, hag _ (fun he => by cases he)]

end Subst

/-! ## The slot in the source context -/

section Slot

variable {Γ₀ : Ctx}

/-- Addresses whose root is the slot, other than the slot itself, are undeclared. -/
def SlotOnly (Γ₀ : Ctx) : Prop :=
  Γ₀ (.root (.bnd 0)) = some .Var ∧ (∀ v, v.rt = .bnd 0 → v ≠ .root (.bnd 0) → Γ₀ v = none) ∧
    ∀ y, y.rt = .bnd 0 → Γ₀.wit y = none

theorem SlotOnly.rt_ne (h : SlotOnly Γ₀) :
    ∀ (u : VarSymb) (X : VarType), Γ₀.ref u = some X → X ≠ .Var → u.rt ≠ .bnd 0
  | .root r, X, hu, hX, he => by
      change r = .bnd 0 at he
      subst he
      change Γ₀ (.root (.bnd 0)) = some X at hu
      rw [h.1] at hu
      cases hu
      exact hX rfl
  | .step w s, X, hu, hX, he => by
      simp only [Ctx.ref] at hu
      split_ifs at hu with hs
      · cases hw : Γ₀.ref w with
        | none => rw [hw] at hu; cases hu
        | some W =>
            rw [hw] at hu
            by_cases hW : W = .Var
            · subst hW; cases s <;> cases hu
            · exact SlotOnly.rt_ne h w W hw hW he
      · rw [h.2.1 _ he (fun h => by cases h)] at hu
        cases hu

omit [ModalSys] in
theorem SlotOnly.wit_rt (h : SlotOnly Γ₀) : ∀ y X, Γ₀.wit y = some X → y.rt ≠ .bnd 0 :=
  fun y _ hy he => by rw [h.2.2 y he] at hy; cases hy

omit [ModalSys] in
theorem SlotOnly.ne_rt (h : SlotOnly Γ₀) :
    ∀ v U, Γ₀ v = some U → v ≠ .root (.bnd 0) → v.rt ≠ .bnd 0 :=
  fun v U hv hne he => by rw [h.2.1 v he hne] at hv; cases hv

omit [ModalSys] in
theorem SlotOnly.le (h : SlotOnly Γ₀) : Γ₀.Le (Γ₀.insert (.bnd 0) .Var) := by
  refine ⟨fun v T hv => ?_, fun _ _ h => h⟩
  rw [Ctx.insert_apply]
  split_ifs with hvr hb
  · subst hvr; rw [h.1] at hv; exact hv
  · rw [h.2.1 v (VarSymb.atBelow_rt hb) hvr] at hv; cases hv
  · exact hv

omit [ModalSys] in
/-- A witness's view keeps the slot alone: the content's root is the witness's. -/
theorem SlotOnly.optIn (h : SlotOnly Γ₀) {y : VarSymb} {X : VarType} (hy : Γ₀.wit y = some X) :
    SlotOnly (Γ₀.optIn y) := by
  refine ⟨?_, fun v hv hne => ?_, h.2.2⟩
  · rw [Ctx.optIn_ne (fun he => by cases he)]
    exact h.1
  · by_cases hvy : v = .step y .dia
    · subst hvy
      exact absurd hv (h.wit_rt y X hy)
    · rw [Ctx.optIn_ne hvy]
      exact h.2.1 v hv hne

/-- An identity view keeps the slot alone: the content's root is the possible object's. -/
theorem SlotOnly.optInT (h : SlotOnly Γ₀) {y : VarSymb} {X : VarType} (hy : Γ₀.witT y = some X) :
    SlotOnly (Γ₀.optInT y) := by
  have hr := (Ctx.witT_spec hy).2.2
  refine ⟨?_, fun v hv hne => ?_, h.2.2⟩
  · rw [Ctx.optInT_ne (fun he => by cases he)]
    exact h.1
  · by_cases hvy : v = .step y .at
    · subst hvy
      exact absurd hv (h.rt_ne y _ hr (fun h => by cases h))
    · rw [Ctx.optInT_ne hvy]
      exact h.2.1 v hv hne

omit [ModalSys] in
/-- A quantifier's slot keeps the base slot alone. -/
theorem SlotOnly.insert (h : SlotOnly Γ₀) {d : ℕ} (hd : d ≠ 0) (T : VarType) :
    SlotOnly (Γ₀.insert (.bnd d) T) := by
  refine ⟨?_, fun v hv hne => ?_, h.2.2⟩
  · change (if VarSymb.root (.bnd 0) = .root (.bnd d) then some T else _) = _
    rw [if_neg (fun he => hd (by cases he; rfl))]
    exact h.1
  · show (Γ₀.insert (.bnd d) T) v = none
    rw [Ctx.insert_apply, if_neg (fun he => by subst he; cases hv; exact hd rfl)]
    split_ifs
    · rfl
    · exact h.2.1 v hv hne

end Slot

/-! ## The atom's hole formula -/

section Hole

variable {Γ₀ Γ : Ctx} [Γ.NoSlots] {d : ℕ} {ι : VarSymb → VarSymb}

/-- `θ` with the slot made the hole: the slot to itself, everything else as `θ` weakened. -/
abbrev holeS (θ : Subst σ Γ) : Subst σ (Γ.insert (.bnd 0) .Var) :=
  θ.under 0 0 .Var (Ctx.NoSlots.slots (Γ := Γ)).root

theorem holeS_ok {θ : Subst σ Γ} (hθ : Subst.Ok Γ₀ θ) (hS : SlotOnly Γ₀) :
    Subst.Ok Γ₀ (holeS θ) :=
  (Subst.ok_under hθ .Var _).restrict hS.le

theorem holeS_coh {θ : Subst σ Γ} (hθ : Subst.Ok Γ₀ θ) (hc : Subst.Coh ι Γ₀ θ)
    (hS : SlotOnly Γ₀) : Subst.Coh (VarSymb.shiftSlot ι 0 0) Γ₀ (holeS θ) :=
  (Subst.coh_under_occ hθ hc .Var _ hS.ne_rt hS.wit_rt).restrict hS.le

/-- The hole formula of `φ` along `θ₁`. -/
abbrev holeF (θ₁ : Subst σ Γ) (hθ₁ : Subst.Ok Γ₀ θ₁) (hc₁ : Subst.Coh ι Γ₀ θ₁)
    (hΓ₀ : Γ₀.SlotsFrom d) (hS : SlotOnly Γ₀) (φ : WFF σ Γ₀ d) :
    WFF σ (Γ.insert (.bnd 0) .Var) 1 :=
  WFF.subst (VarSymb.shiftSlot ι 0 0) (holeS θ₁) (holeS_ok hθ₁ hS) (holeS_coh hθ₁ hc₁ hS) hΓ₀
    ((Ctx.NoSlots.slots (Γ := Γ)).insert .Var) φ

/-- ⭐Filling the hole with `t` substitutes along any `θ` sending the slot to `t` and agreeing with
    `θ₁` elsewhere. -/
theorem instantiate_hole
    (θ₁ θ : Subst σ Γ) (hθ₁ : Subst.Ok Γ₀ θ₁) (hc₁ : Subst.Coh ι Γ₀ θ₁)
    (hθ : Subst.Ok Γ₀ θ) (hc : Subst.Coh ι Γ₀ θ) (hΓ₀ : Γ₀.SlotsFrom d) (hS : SlotOnly Γ₀)
    {t : Term σ Γ .Var .var} (h₀ : θ (.root (.bnd 0)) = .tm t)
    (hag : ∀ v, v ≠ .root (.bnd 0) → θ₁ v = θ v) (hagw : ∀ y, θ₁.wit y = θ.wit y)
    (φ : WFF σ Γ₀ d) :
    WFF.instantiate Ctx.NoSlots.slots t (holeF θ₁ hθ₁ hc₁ hΓ₀ hS φ) =
      WFF.subst ι θ hθ hc hΓ₀ Ctx.NoSlots.slots φ := by
  have hrΓ : Γ.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ)).rootFresh le_rfl
  unfold WFF.instantiate WFF.substRoot holeF
  refine WFF.subst_comp _ _ _ _ _ _ _ hθ hc _ _ _ ?_ φ
  refine Subst.sim_of ?_ fun hO y X hy => ?_
  swap
  · refine Eq.mpr (congrArg (WitE.Sim X _) (WitE.comp_mono (Subst.idRen Γ) Subst.ok_idRen
      Subst.coh_idRen hO (Ctx.le_insert hrΓ.root .Var) (Ctx.Le.refl Γ)
      (Subst.single (.bnd 0) (.tm t)) (Subst.ok_single (Ctx.Le.refl Γ) rfl)
      (Subst.coh_single hrΓ (Ctx.Le.refl Γ) rfl)
      (fun w _ hw' => by
        rw [Subst.single_at_ne (Ctx.ref_rt_ne hrΓ hw'), Subst.at_idRen]
        rfl)
      (fun _ _ _ => rfl) (hθ₁.wit hO y X hy))) ?_
    rw [WitE.comp_idRen hO (hθ₁.wit hO y X hy), WitE.mono_refl, hagw y]
    exact .refl _
  intro v U hlp hv
  rw [Subst.comp_apply]
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [show holeS θ₁ (.root (.bnd 0)) = .ren (.root (.bnd 0)) from by slot_rfl, SubE.comp_ren,
      Subst.at_single_root, h₀]
    exact .refl _
  · rw [show holeS θ₁ v = (θ₁ v).mono (Ctx.le_insert hrΓ.root .Var) from if_neg hvr,
      SubE.comp_mono (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen (Ctx.le_insert hrΓ.root .Var)
        (Ctx.Le.refl Γ) _ _ _
        (fun w _ hw' => by
          rw [Subst.single_at_ne (Ctx.ref_rt_ne hrΓ hw'), Subst.at_idRen]
          rfl)
        (hθ₁ v U hlp hv),
      SubE.comp_idRen, SubE.mono_refl, hag v hvr]
    exact .refl _

theorem hole_isAtom
    (θ₁ : Subst σ Γ) (hθ₁ : Subst.Ok Γ₀ θ₁) (hc₁ : Subst.Coh ι Γ₀ θ₁)
    (hΓ₀ : Γ₀.SlotsFrom d) (hS : SlotOnly Γ₀) {φ : WFF σ Γ₀ d} (hφ : φ.IsAtom) :
    (holeF θ₁ hθ₁ hc₁ hΓ₀ hS φ).IsAtom :=
  WFF.IsAtom.subst hφ

end Hole

/-! ## Identity -/

namespace GK

section Ident

variable [ModalSys.GKBase]

/-- ⭐**Identity**: `φ ⇒ φ`, for every formula of K. -/
theorem ident_aux : ∀ (w : ℕ) {Γ : Ctx} [Γ.Presented] (φ : WFF σ Γ 0) {Δ Θ : List (WFF σ Γ 0)},
    φ.weight < w → φ ∈ Δ → φ ∈ Θ → ∃ n, GK σ n Γ Δ Θ
  | 0, _, _, _, _, _, hw, _, _ => absurd hw (Nat.not_lt_zero _)
  | w + 1, Γ, _, φ, Δ, Θ, hw, hΔ, hΘ => by
      cases φ with
      | atom ρ => exact ⟨0, .ax (.atom ρ) trivial hΔ hΘ⟩
      | eq t s => exact ⟨0, .ax (.eq t s) trivial hΔ hΘ⟩
      | top => exact ⟨0, .topR hΘ⟩
      | bot => exact ⟨0, .botL hΔ⟩
      | and φ ψ =>
          simp only [WFF.weight] at hw
          obtain ⟨n₁, e₁⟩ := ident_aux w φ (Δ := φ :: ψ :: Δ) (Θ := φ :: Θ) (by omega)
            List.mem_cons_self List.mem_cons_self
          obtain ⟨n₂, e₂⟩ := ident_aux w ψ (Δ := φ :: ψ :: Δ) (Θ := ψ :: Θ) (by omega)
            (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
          exact ⟨_, .andL hΔ (.andR hΘ (both e₁ e₂).1 (both e₁ e₂).2)⟩
      | or φ ψ =>
          simp only [WFF.weight] at hw
          obtain ⟨n₁, e₁⟩ := ident_aux w φ (Δ := φ :: Δ) (Θ := φ :: ψ :: Θ) (by omega)
            List.mem_cons_self List.mem_cons_self
          obtain ⟨n₂, e₂⟩ := ident_aux w ψ (Δ := ψ :: Δ) (Θ := φ :: ψ :: Θ) (by omega)
            List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
          exact ⟨_, .orL hΔ (.orR hΘ (both e₁ e₂).1) (.orR hΘ (both e₁ e₂).2)⟩
      | imp φ ψ =>
          simp only [WFF.weight] at hw
          obtain ⟨n₁, e₁⟩ := ident_aux w φ (Δ := φ :: Δ) (Θ := φ :: ψ :: Θ) (by omega)
            List.mem_cons_self List.mem_cons_self
          obtain ⟨n₂, e₂⟩ := ident_aux w ψ (Δ := ψ :: φ :: Δ) (Θ := ψ :: Θ) (by omega)
            List.mem_cons_self List.mem_cons_self
          exact ⟨_, .impR hΘ (.impL (List.mem_cons_of_mem _ hΔ) (both e₁ e₂).1 (both e₁ e₂).2)⟩
      | all T ψ =>
          simp only [WFF.weight] at hw
          have hu : Γ.RootFresh (.free (Ctx.Presented.bound Γ)) :=
            Ctx.Presented.fresh_bound _ le_rfl
          have hm : WFF.all T (WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T) ψ) ∈
              Δ.map (WFF.weaken hu.root T) := List.mem_map_of_mem hΔ
          obtain ⟨n, e⟩ := ident_aux w (WFF.openFree _ hu Ctx.NoSlots.slots ψ)
            (Δ := WFF.openFree _ hu Ctx.NoSlots.slots ψ :: Δ.map (WFF.weaken hu.root T))
            (Θ := WFF.openFree _ hu Ctx.NoSlots.slots ψ :: Θ.map (WFF.weaken hu.root T))
            (by unfold WFF.openFree; rw [WFF.weight_subst]; omega)
            List.mem_cons_self List.mem_cons_self
          rw [← WFF.instantiate_eta_openFree _ hu Ctx.NoSlots.slots Ctx.NoSlots.slots ψ] at e
          refine ⟨_, .allR _ T hu ?_ (.allL T _ hm e)⟩
          rw [WFF.instantiate_eta_openFree _ hu Ctx.NoSlots.slots Ctx.NoSlots.slots ψ,
            WFF.bindFree_openFree]
          exact hΘ
      | ex T ψ =>
          simp only [WFF.weight] at hw
          have hu : Γ.RootFresh (.free (Ctx.Presented.bound Γ)) :=
            Ctx.Presented.fresh_bound _ le_rfl
          have hm : WFF.ex T (WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T) ψ) ∈
              Θ.map (WFF.weaken hu.root T) := List.mem_map_of_mem hΘ
          obtain ⟨n, e⟩ := ident_aux w (WFF.openFree _ hu Ctx.NoSlots.slots ψ)
            (Δ := WFF.openFree _ hu Ctx.NoSlots.slots ψ :: Δ.map (WFF.weaken hu.root T))
            (Θ := WFF.openFree _ hu Ctx.NoSlots.slots ψ :: Θ.map (WFF.weaken hu.root T))
            (by unfold WFF.openFree; rw [WFF.weight_subst]; omega)
            List.mem_cons_self List.mem_cons_self
          rw [← WFF.instantiate_eta_openFree _ hu Ctx.NoSlots.slots Ctx.NoSlots.slots ψ] at e
          refine ⟨_, .exL _ T hu ?_ (.exR T _ hm e)⟩
          rw [WFF.instantiate_eta_openFree _ hu Ctx.NoSlots.slots Ctx.NoSlots.slots ψ,
            WFF.bindFree_openFree]
          exact hΔ
      | box φ =>
          simp only [WFF.weight] at hw
          obtain ⟨n, e⟩ := ident_aux w φ (Δ := [φ]) (Θ := [φ]) (by omega)
            List.mem_cons_self List.mem_cons_self
          exact ⟨_, .boxR (L := []) hΘ (fun χ hχ => by rw [List.mem_singleton.mp hχ]; exact hΔ)
            (List.nil_subset _) (e.weaken (fun _ h => List.mem_append_left _ h)
              (fun a ha => by rw [kp4_nil]; exact ha))⟩
      | dia x hx φ =>
          simp only [WFF.weight] at hw
          obtain ⟨n, e⟩ := ident_aux w φ (Δ := [φ]) (Θ := [φ]) (by omega)
            List.mem_cons_self List.mem_cons_self
          refine ⟨_, .diaL x hx (Δ₁ := []) (L := []) hΔ (fun _ h => absurd h List.not_mem_nil)
            (fun χ hχ => by rw [List.mem_singleton.mp hχ]; exact hΘ) (List.nil_subset _)
            (e.weaken (fun a ha => ?_) (fun _ h => List.mem_append_left _ h))⟩
          rw [List.mem_singleton.mp ha]; exact List.mem_cons_self
      | here hT _ _ hO' =>
          exact absurd (ModalSys.GKBase.tOpt hT) (by rw [hO']; decide)
      | back hB _ _ _ => exact absurd hB (by rw [ModalSys.GKBase.noBStrong]; decide)
      | retS hB _ _ _ => exact absurd hB (by rw [ModalSys.GKBase.noBStrong]; decide)
      | retxS hB _ _ _ _ _ => exact absurd hB (by rw [ModalSys.GKBase.noBStrong]; decide)
      | link hV _ _ _ => exact absurd hV (by rw [ModalSys.GKBase.noFive]; decide)
      | linkx hV _ _ _ _ _ => exact absurd hV (by rw [ModalSys.GKBase.noFive]; decide)
      | optx hO κ y hy ψ =>
          -- `◇⁰_y ψ ⇒ ◇⁰_y ψ`: open the witness, re-open on the right, identity on the body
          simp only [WFF.weight] at hw
          obtain ⟨n, e⟩ := ident_aux w ψ
            (Δ := ψ :: Δ.map (WFF.mono (Ctx.le_optInK Γ κ y)))
            (Θ := ψ :: Θ.map (WFF.mono (Ctx.le_optInK Γ κ y))) (by omega)
            List.mem_cons_self List.mem_cons_self
          exact ⟨_, .optL hO κ y hy hΔ (.reopenR (χ := ψ) hO κ y (Ctx.opened_optInK hy)
            (List.mem_map_of_mem hΘ) e)⟩

theorem ident {Γ : Ctx} [Γ.Presented] (φ : WFF σ Γ 0) {Δ Θ : List (WFF σ Γ 0)} (hΔ : φ ∈ Δ)
    (hΘ : φ ∈ Θ) : ∃ n, GK σ n Γ Δ Θ :=
  ident_aux _ φ (Nat.lt_succ_self _) hΔ hΘ

end Ident

variable [ModalSys.GKBase]

/-! ## Replacement -/

/-- ⭐**Replacement, for two substitutions** agreeing everywhere but at the slot `bnd 0`, sent to
    `t` and to `s`: `t = s, s = t, φ[θ₁] ⇒ φ[θ₂]`. -/
theorem replaceGen {Γ₀ : Ctx} {d : ℕ} (φ : WFF σ Γ₀ d) :
    ∀ {Γ : Ctx} [Γ.Presented] {ι : VarSymb → VarSymb} (θ₁ θ₂ : Subst σ Γ)
      (hθ₁ : Subst.Ok Γ₀ θ₁) (hθ₂ : Subst.Ok Γ₀ θ₂) (hc₁ : Subst.Coh ι Γ₀ θ₁)
      (hc₂ : Subst.Coh ι Γ₀ θ₂) (hΓ₀ : Γ₀.SlotsFrom d), SlotOnly Γ₀ →
      ∀ {t s : Term σ Γ .Var .var}, θ₁ (.root (.bnd 0)) = .tm t → θ₂ (.root (.bnd 0)) = .tm s →
      (∀ v, v ≠ .root (.bnd 0) → θ₁ v = θ₂ v) → (∀ y, θ₁.wit y = θ₂.wit y) →
      ∀ {Δ Θ : List (WFF σ Γ 0)},
      .eq t s ∈ Δ → .eq s t ∈ Δ → WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots φ ∈ Δ →
      WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots φ ∈ Θ → ∃ n, GK σ n Γ Δ Θ := by
  induction φ with
  | atom ρ =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts _ hφ₁ hφ₂
      have e₁ := instantiate_hole θ₁ θ₁ hθ₁ hc₁ hθ₁ hc₁ hΓ₀ hS h₁ (fun _ _ => rfl)
        (fun _ => rfl) (.atom ρ)
      have e₂ := instantiate_hole θ₁ θ₂ hθ₁ hc₁ hθ₂ hc₂ hΓ₀ hS h₂ hag hagw (.atom ρ)
      have hP := hole_isAtom θ₁ hθ₁ hc₁ hΓ₀ hS (φ := .atom ρ) trivial
      exact ⟨_, .repl hP t s hts (by rw [e₁]; exact hφ₁)
        (.ax (n := 0) _ hP.instantiate List.mem_cons_self (by rw [e₂]; exact hφ₂))⟩
  | eq a b =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts _ hφ₁ hφ₂
      have e₁ := instantiate_hole θ₁ θ₁ hθ₁ hc₁ hθ₁ hc₁ hΓ₀ hS h₁ (fun _ _ => rfl)
        (fun _ => rfl) (.eq a b)
      have e₂ := instantiate_hole θ₁ θ₂ hθ₁ hc₁ hθ₂ hc₂ hΓ₀ hS h₂ hag hagw (.eq a b)
      have hP := hole_isAtom θ₁ hθ₁ hc₁ hΓ₀ hS (φ := .eq a b) trivial
      exact ⟨_, .repl hP t s hts (by rw [e₁]; exact hφ₁)
        (.ax (n := 0) _ hP.instantiate List.mem_cons_self (by rw [e₂]; exact hφ₂))⟩
  | top =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts _ hφ₁ hφ₂
      exact ⟨0, .topR hφ₂⟩
  | bot =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts _ hφ₁ hφ₂
      exact ⟨0, .botL hφ₁⟩
  | and φ ψ ih₁ ih₂ =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts hst hφ₁ hφ₂
      obtain ⟨n₁, e₁⟩ := ih₁ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS h₁ h₂ hag hagw
        (Δ := WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots φ ::
          WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots ψ :: Δ)
        (Θ := WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots φ :: Θ)
        (by simp [hts])
        (by simp [hst]) List.mem_cons_self List.mem_cons_self
      obtain ⟨n₂, e₂⟩ := ih₂ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS h₁ h₂ hag hagw
        (Δ := WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots φ ::
          WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots ψ :: Δ)
        (Θ := WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots ψ :: Θ)
        (by simp [hts])
        (by simp [hst]) (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
      exact ⟨_, .andL hφ₁ (.andR hφ₂ (both e₁ e₂).1 (both e₁ e₂).2)⟩
  | or φ ψ ih₁ ih₂ =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts hst hφ₁ hφ₂
      obtain ⟨n₁, e₁⟩ := ih₁ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS h₁ h₂ hag hagw
        (Δ := WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots φ :: Δ)
        (Θ := WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots φ ::
          WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots ψ :: Θ)
        (by simp [hts])
        (by simp [hst]) List.mem_cons_self List.mem_cons_self
      obtain ⟨n₂, e₂⟩ := ih₂ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS h₁ h₂ hag hagw
        (Δ := WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots ψ :: Δ)
        (Θ := WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots φ ::
          WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots ψ :: Θ)
        (by simp [hts])
        (by simp [hst]) List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨_, .orL hφ₁ (.orR hφ₂ (both e₁ e₂).1) (.orR hφ₂ (both e₁ e₂).2)⟩
  | imp φ ψ ih₁ ih₂ =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts hst hφ₁ hφ₂
      obtain ⟨n₁, e₁⟩ := ih₁ θ₂ θ₁ hθ₂ hθ₁ hc₂ hc₁ hΓ₀ hS h₂ h₁ (fun v hv => (hag v hv).symm)
        (fun y => (hagw y).symm)
        (Δ := WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots φ :: Δ)
        (Θ := WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots φ ::
          WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots ψ :: Θ)
        (by simp [hst]) (by simp [hts]) List.mem_cons_self List.mem_cons_self
      obtain ⟨n₂, e₂⟩ := ih₂ θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS h₁ h₂ hag hagw
        (Δ := WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots ψ ::
          WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots φ :: Δ)
        (Θ := WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots ψ :: Θ)
        (by simp [hts])
        (by simp [hst]) List.mem_cons_self List.mem_cons_self
      exact ⟨_, .impR hφ₂ (.impL (List.mem_cons_of_mem _ hφ₁) (both e₁ e₂).1 (both e₁ e₂).2)⟩
  | @all Γ₀ d T ψ ih =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts hst hφ₁ hφ₂
      have hd : d ≠ 0 := fun h0 => by
        have h' := hΓ₀.root
        rw [h0, hS.1] at h'
        cases h'
      have hΓ : Γ.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu : Γ.RootFresh (.free (Ctx.Presented.bound Γ)) := Ctx.Presented.fresh_bound _ le_rfl
      have hd0 : (VarSymb.root (.bnd 0)) ≠ .root (.bnd d) := fun he => hd (by cases he; rfl)
      obtain ⟨n, e⟩ := ih (θ₁.toFree d _ T hu.root) (θ₂.toFree d _ T hu.root)
        (Subst.ok_toFree hθ₁ T hu.root) (Subst.ok_toFree hθ₂ T hu.root)
        (Subst.coh_toFree hθ₁ hc₁ hΓ₀ T hu.root) (Subst.coh_toFree hθ₂ hc₂ hΓ₀ T hu.root)
        (hΓ₀.insert T) (hS.insert hd T)
        (t := Term.mono (Ctx.le_insert hu.root T) t) (s := Term.mono (Ctx.le_insert hu.root T) s)
        (by rw [show θ₁.toFree d _ T hu.root (.root (.bnd 0)) =
          (θ₁ (.root (.bnd 0))).mono (Ctx.le_insert hu.root T) from if_neg hd0, h₁]; rfl)
        (by rw [show θ₂.toFree d _ T hu.root (.root (.bnd 0)) =
          (θ₂ (.root (.bnd 0))).mono (Ctx.le_insert hu.root T) from if_neg hd0, h₂]; rfl)
        (fun v hv => by
          by_cases hvd : v = .root (.bnd d)
          · rw [show θ₁.toFree d _ T hu.root v = _ from if_pos hvd,
              show θ₂.toFree d _ T hu.root v = _ from if_pos hvd]
          · rw [show θ₁.toFree d _ T hu.root v = (θ₁ v).mono (Ctx.le_insert hu.root T)
              from if_neg hvd, show θ₂.toFree d _ T hu.root v = (θ₂ v).mono
                (Ctx.le_insert hu.root T) from if_neg hvd, hag v hv])
        (fun y => by
          change (θ₁.wit y).mono (Ctx.le_insert hu.root T) =
            (θ₂.wit y).mono (Ctx.le_insert hu.root T)
          rw [hagw y])
        (Δ := WFF.subst (VarSymb.slotToFree ι d _) (θ₁.toFree d _ T hu.root)
          (Subst.ok_toFree hθ₁ T hu.root) (Subst.coh_toFree hθ₁ hc₁ hΓ₀ T hu.root)
          (hΓ₀.insert T) (hΓ.insertFree _ T) ψ :: Δ.map (WFF.weaken hu.root T))
        (Θ := WFF.subst (VarSymb.slotToFree ι d _) (θ₂.toFree d _ T hu.root)
          (Subst.ok_toFree hθ₂ T hu.root) (Subst.coh_toFree hθ₂ hc₂ hΓ₀ T hu.root)
          (hΓ₀.insert T) (hΓ.insertFree _ T) ψ :: Θ.map (WFF.weaken hu.root T))
        (List.mem_cons_of_mem _ (List.mem_map_of_mem hts))
        (List.mem_cons_of_mem _ (List.mem_map_of_mem hst)) List.mem_cons_self List.mem_cons_self
      rw [← WFF.instantiate_toFree θ₁ hθ₁ hc₁ hΓ₀ hΓ _ hu T Ctx.NoSlots.slots ψ] at e
      refine ⟨_, .allR _ T hu ?_ (.allL T _ (List.mem_map_of_mem hφ₁) e)⟩
      rw [WFF.bindFree_toFree θ₂ hθ₂ hc₂ hΓ₀ hΓ _ hu T ψ]
      exact hφ₂
  | @ex Γ₀ d T ψ ih =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts hst hφ₁ hφ₂
      have hd : d ≠ 0 := fun h0 => by
        have h' := hΓ₀.root
        rw [h0, hS.1] at h'
        cases h'
      have hΓ : Γ.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu : Γ.RootFresh (.free (Ctx.Presented.bound Γ)) := Ctx.Presented.fresh_bound _ le_rfl
      have hd0 : (VarSymb.root (.bnd 0)) ≠ .root (.bnd d) := fun he => hd (by cases he; rfl)
      obtain ⟨n, e⟩ := ih (θ₁.toFree d _ T hu.root) (θ₂.toFree d _ T hu.root)
        (Subst.ok_toFree hθ₁ T hu.root) (Subst.ok_toFree hθ₂ T hu.root)
        (Subst.coh_toFree hθ₁ hc₁ hΓ₀ T hu.root) (Subst.coh_toFree hθ₂ hc₂ hΓ₀ T hu.root)
        (hΓ₀.insert T) (hS.insert hd T)
        (t := Term.mono (Ctx.le_insert hu.root T) t) (s := Term.mono (Ctx.le_insert hu.root T) s)
        (by rw [show θ₁.toFree d _ T hu.root (.root (.bnd 0)) =
          (θ₁ (.root (.bnd 0))).mono (Ctx.le_insert hu.root T) from if_neg hd0, h₁]; rfl)
        (by rw [show θ₂.toFree d _ T hu.root (.root (.bnd 0)) =
          (θ₂ (.root (.bnd 0))).mono (Ctx.le_insert hu.root T) from if_neg hd0, h₂]; rfl)
        (fun v hv => by
          by_cases hvd : v = .root (.bnd d)
          · rw [show θ₁.toFree d _ T hu.root v = _ from if_pos hvd,
              show θ₂.toFree d _ T hu.root v = _ from if_pos hvd]
          · rw [show θ₁.toFree d _ T hu.root v = (θ₁ v).mono (Ctx.le_insert hu.root T)
              from if_neg hvd, show θ₂.toFree d _ T hu.root v = (θ₂ v).mono
                (Ctx.le_insert hu.root T) from if_neg hvd, hag v hv])
        (fun y => by
          change (θ₁.wit y).mono (Ctx.le_insert hu.root T) =
            (θ₂.wit y).mono (Ctx.le_insert hu.root T)
          rw [hagw y])
        (Δ := WFF.subst (VarSymb.slotToFree ι d _) (θ₁.toFree d _ T hu.root)
          (Subst.ok_toFree hθ₁ T hu.root) (Subst.coh_toFree hθ₁ hc₁ hΓ₀ T hu.root)
          (hΓ₀.insert T) (hΓ.insertFree _ T) ψ :: Δ.map (WFF.weaken hu.root T))
        (Θ := WFF.subst (VarSymb.slotToFree ι d _) (θ₂.toFree d _ T hu.root)
          (Subst.ok_toFree hθ₂ T hu.root) (Subst.coh_toFree hθ₂ hc₂ hΓ₀ T hu.root)
          (hΓ₀.insert T) (hΓ.insertFree _ T) ψ :: Θ.map (WFF.weaken hu.root T))
        (List.mem_cons_of_mem _ (List.mem_map_of_mem hts))
        (List.mem_cons_of_mem _ (List.mem_map_of_mem hst)) List.mem_cons_self List.mem_cons_self
      rw [← WFF.instantiate_toFree θ₂ hθ₂ hc₂ hΓ₀ hΓ _ hu T Ctx.NoSlots.slots ψ] at e
      refine ⟨_, .exL _ T hu ?_ (.exR T _ (List.mem_map_of_mem hφ₂) e)⟩
      rw [WFF.bindFree_toFree θ₁ hθ₁ hc₁ hΓ₀ hΓ _ hu T ψ]
      exact hφ₁
  | box φ _ =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts hst hφ₁ hφ₂
      have hA : ∀ u X, _ → X ≠ VarType.Var → θ₁.at u = θ₂.at u := fun u X hu hX =>
        Subst.at_agree hag u (hS.rt_ne u X hu hX)
      have e : WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots (WFF.box φ) =
          WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots (WFF.box φ) :=
        congrArg WFF.box (WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_box_of_agree hA) φ)
      exact ident _ (e ▸ hφ₁) hφ₂
  | dia x hx φ _ =>
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts hst hφ₁ hφ₂
      have hA : ∀ u X, _ → X ≠ VarType.Var → θ₁.at u = θ₂.at u := fun u X hu hX =>
        Subst.at_agree hag u (hS.rt_ne u X hu hX)
      have hw : (θ₁.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc₁ x _ hX []
      have hwx : ∃ X, Γ.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ₁ hX) hw
      have e : WFF.subst ι θ₁ hθ₁ hc₁ hΓ₀ Ctx.NoSlots.slots (WFF.dia x hx φ) =
          WFF.subst ι θ₂ hθ₂ hc₂ hΓ₀ Ctx.NoSlots.slots (WFF.dia x hx φ) :=
        congrArg (WFF.dia (ι x) hwx)
          (WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_dia_of_agree hA x (ι x)) φ)
      exact ident _ (e ▸ hφ₁) hφ₂
  | here hT _ _ hO' => exact absurd (ModalSys.GKBase.tOpt hT) (by rw [hO']; decide)
  | back hB _ _ _ => exact absurd hB (by rw [ModalSys.GKBase.noBStrong]; decide)
  | retS hB _ _ _ _ => exact absurd hB (by rw [ModalSys.GKBase.noBStrong]; decide)
  | retxS hB _ _ _ _ _ _ => exact absurd hB (by rw [ModalSys.GKBase.noBStrong]; decide)
  | link hV _ _ _ _ => exact absurd hV (by rw [ModalSys.GKBase.noFive]; decide)
  | linkx hV _ _ _ _ _ _ => exact absurd hV (by rw [ModalSys.GKBase.noFive]; decide)
  | optx hO κ y hy ψ ih =>
      -- the slot stays in view: open the witness on the left, re-open on the right
      intro Γ _ ι θ₁ θ₂ hθ₁ hθ₂ hc₁ hc₂ hΓ₀ hS t s h₁ h₂ hag hagw Δ Θ hts hst hφ₁ hφ₂
      cases κ with
      | ident =>
          obtain ⟨X, hX⟩ := hy
          obtain ⟨hT, hO'', hr⟩ := Ctx.witT_spec hX
          have hw₁ : (θ₁.at y).idxAlong [] = ι y := hc₁ y _ hr []
          have hw₂ : (θ₂.at y).idxAlong [] = ι y := hc₂ y _ hr []
          have hy' : ∃ Y, Γ.witK .ident (ι y) = some Y := by
            obtain ⟨Y, hY⟩ := SubE.ref_witness (Subst.okRef_at hθ₁ hr) hw₁
            exact ⟨Y, Ctx.witT_of hT hO'' hY⟩
          have hat : θ₁.at y = θ₂.at y :=
            Subst.at_agree hag y (hS.rt_ne y _ hr (fun h => by cases h))
          have hle := Ctx.le_optInT Γ (ι y)
          obtain ⟨n, e⟩ := ih (Γ := Γ.optInT (ι y)) (θ₁.optInT y (ι y)) (θ₂.optInT y (ι y))
            (Subst.ok_optInT hθ₁ hX hw₁) (Subst.ok_optInT hθ₂ hX hw₂)
            (Subst.coh_optInT hθ₁ hc₁ hX) (Subst.coh_optInT hθ₂ hc₂ hX) (hΓ₀.optInT y)
            (hS.optInT hX) (t := Term.mono hle t) (s := Term.mono hle s)
            (by rw [Subst.optInT_ne θ₁ _ (fun he => by cases he), h₁]; rfl)
            (by rw [Subst.optInT_ne θ₂ _ (fun he => by cases he), h₂]; rfl)
            (fun v hv => by
              by_cases hvy : v = .step y .at
              · subst hvy
                rw [Subst.optInT_content, Subst.optInT_content, hat]
              · rw [Subst.optInT_ne θ₁ _ hvy, Subst.optInT_ne θ₂ _ hvy, hag v hv])
            (fun y' => by
              change (θ₁.wit y').mono hle = (θ₂.wit y').mono hle
              rw [hagw y'])
            (Δ := WFF.subst ι (θ₁.optInT y (ι y)) (Subst.ok_optInT hθ₁ hX hw₁)
              (Subst.coh_optInT hθ₁ hc₁ hX) (hΓ₀.optInT y) Ctx.NoSlots.slots ψ ::
                Δ.map (WFF.mono hle))
            (Θ := WFF.subst ι (θ₂.optInT y (ι y)) (Subst.ok_optInT hθ₂ hX hw₂)
              (Subst.coh_optInT hθ₂ hc₂ hX) (hΓ₀.optInT y) Ctx.NoSlots.slots ψ ::
                Θ.map (WFF.mono hle))
            (List.mem_cons_of_mem _ (List.mem_map_of_mem hts))
            (List.mem_cons_of_mem _ (List.mem_map_of_mem hst)) List.mem_cons_self
            List.mem_cons_self
          exact ⟨_, .optL hO .ident (ι y) hy' hφ₁ (.reopenR hO .ident (ι y)
            (Ctx.opened_optInK hy') (List.mem_map_of_mem hφ₂) e)⟩
      | arrow =>
          obtain ⟨X, hX⟩ := hy
          have hw₁ : (θ₁.wit y).idxAlong [] = ι y := hc₁.wit hO y X hX []
          have hw₂ : (θ₂.wit y).idxAlong [] = ι y := hc₂.wit hO y X hX []
          have hy' : ∃ Y, Γ.witK .arrow (ι y) = some Y := WitE.wit_of (hθ₁.wit hO y X hX) hw₁
          have hle := Ctx.le_optIn Γ (ι y)
          obtain ⟨n, e⟩ := ih (Γ := Γ.optIn (ι y)) (θ₁.optIn y (ι y)) (θ₂.optIn y (ι y))
            (Subst.ok_optIn hθ₁ hO hX hw₁) (Subst.ok_optIn hθ₂ hO hX hw₂)
            (Subst.coh_optIn hθ₁ hc₁ hO hX) (Subst.coh_optIn hθ₂ hc₂ hO hX) (hΓ₀.optIn y)
            (hS.optIn hX) (t := Term.mono hle t) (s := Term.mono hle s)
            (by rw [Subst.optIn_ne θ₁ _ (fun he => by cases he), h₁]; rfl)
            (by rw [Subst.optIn_ne θ₂ _ (fun he => by cases he), h₂]; rfl)
            (fun v hv => by
              by_cases hvy : v = .step y .dia
              · subst hvy
                rw [Subst.optIn_content, Subst.optIn_content, hagw y]
              · rw [Subst.optIn_ne θ₁ _ hvy, Subst.optIn_ne θ₂ _ hvy, hag v hv])
            (fun y' => by
              change (θ₁.wit y').mono hle = (θ₂.wit y').mono hle
              rw [hagw y'])
            (Δ := WFF.subst ι (θ₁.optIn y (ι y)) (Subst.ok_optIn hθ₁ hO hX hw₁)
              (Subst.coh_optIn hθ₁ hc₁ hO hX) (hΓ₀.optIn y) Ctx.NoSlots.slots ψ ::
                Δ.map (WFF.mono hle))
            (Θ := WFF.subst ι (θ₂.optIn y (ι y)) (Subst.ok_optIn hθ₂ hO hX hw₂)
              (Subst.coh_optIn hθ₂ hc₂ hO hX) (hΓ₀.optIn y) Ctx.NoSlots.slots ψ ::
                Θ.map (WFF.mono hle))
            (List.mem_cons_of_mem _ (List.mem_map_of_mem hts))
            (List.mem_cons_of_mem _ (List.mem_map_of_mem hst)) List.mem_cons_self
            List.mem_cons_self
          exact ⟨_, .optL hO .arrow (ι y) hy' hφ₁ (.reopenR hO .arrow (ι y)
            (Ctx.opened_optInK hy') (List.mem_map_of_mem hφ₂) e)⟩

/-- ⭐**Replacement**: `t = s, s = t, φ(t) ⇒ φ(s)`, for every formula `φ` with a base-type slot —
    ND's `eq_elim`. -/
theorem replace {Γ : Ctx} [Γ.Presented] (φ : WFF σ (Γ.insert (.bnd 0) .Var) 1)
    (t s : Term σ Γ .Var .var) {Δ Θ : List (WFF σ Γ 0)} (h₁ : .eq t s ∈ Δ) (h₂ : .eq s t ∈ Δ)
    (h₃ : WFF.instantiate Ctx.NoSlots.slots t φ ∈ Δ)
    (h₄ : WFF.instantiate Ctx.NoSlots.slots s φ ∈ Θ) : ∃ n, GK σ n Γ Δ Θ := by
  have hr : Γ.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ)).rootFresh le_rfl
  have hS : SlotOnly (Γ.insert (.bnd 0) .Var) :=
    ⟨Ctx.ref_insert_root _ _ _, fun v hv hne => by
      rw [Ctx.insert_ne_of_fresh hne hr.root]
      exact hr.ty v hv, hr.wit⟩
  exact replaceGen φ (Subst.single (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm s))
    (Subst.ok_single (Ctx.Le.refl Γ) rfl) (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single hr (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single (e := .tm s) hr (Ctx.Le.refl Γ) rfl :
      Subst.Coh (Subst.singleIdx (.bnd 0) (.tm t)) _ (Subst.single (.bnd 0) (.tm s)))
    ((Ctx.NoSlots.slots (Γ := Γ)).insert .Var) hS (Subst.single_self _ _) (Subst.single_self _ _)
    (fun v hv => by rw [Subst.single_ne _ hv, Subst.single_ne _ hv]) (fun _ => rfl) h₁ h₂ h₃ h₄

omit [ModalSys.GKBase] in
/-- Symmetry of base equality. -/
theorem eq_symm {Γ : Ctx} [Γ.Presented] (t s : Term σ Γ .Var .var) {Δ Θ : List (WFF σ Γ 0)}
    (h : .eq t s ∈ Δ) (h' : .eq s t ∈ Θ) : ∃ n, GK σ n Γ Δ Θ := by
  have hP : (eqHoleL t).IsAtom := trivial
  refine ⟨_, .ref t (.repl hP t s (List.mem_cons_of_mem _ h) ?_
    (.ax (n := 0) _ hP.instantiate List.mem_cons_self ?_))⟩
  · rw [instantiate_eqHoleL]; exact List.mem_cons_self
  · rw [instantiate_eqHoleL]; exact h'

end GK

end V12M
