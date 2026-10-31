import QML.QML_v12m_RetLiftN
import QML.QML_v12m_GCanonLift

/-!
# QML v12m — strong B on S5: lifting a witnessed returning possibility

`◇[⟨d, x⟩ ↦ ⟨t, c⟩] Ψ(d, x)` (`d : □F`, `x : ◇X`) gives, as an `∃`-elimination, fresh `n : □F` and
`z : ◇X` here with `Back (n.dup) t`, `Here z c` and `◇Ψ(n.keep, z.keep)`.  So the cluster needs no
new world here either, and the way home lies in the extent of `z.keep` because the identity lies in
`z`'s.

This is `Proof.ret_lift` for the one object `⟨d, x⟩ : G := □F × ◇X`, whose kept form is
`⟨d.keep, x.keep⟩`: the companion is `b : □G`, and `⟨n, z⟩` is its value.  The derivation stays at
the witnessed shape, since a body over the leg's view has no closed form to forget the witness
with: the unit is `ret_unitD`, so the nested returning possibility goes along `x`.  The ties are
hole formulas with no `◇_x` in them; `□_x Here(z', x.dia)`, which `ret_counitD` asks for, is built
at the far end from `here_keep`.
-/

namespace V12M

variable [ModalSys] {σ : Signature}

open BArrow

/-! ## One object with a possible part -/

/-- The object of a witnessed shape, as one type. -/
abbrev wTy (F X : VarType) : VarType := .VTypeProd (.VTypeBox F) (.VTypeDia X)

section Term

variable {Γ : Ctx} {F X : VarType} {r₁ r₂ : VarSymb}

/-- Two addresses as one object. -/
def wTerm (h₁ : Γ.ref r₁ = some (.VTypeBox F)) (h₂ : Γ.ref r₂ = some (.VTypeDia X)) :
    Σ b, Term σ Γ (wTy F X) b :=
  ⟨_, Term.pair (Term.eta r₁ _ h₁) (Term.eta r₂ _ h₂)⟩

/-- The object kept, one view in. -/
def wKeep (hF : ModalSys.Four = true) (h₁ : Γ.ref r₁ = some (.VTypeBox F))
    (h₂ : Γ.ref r₂ = some (.VTypeDia X)) : Σ b, Term σ Γ.boxIn (wTy F X) b :=
  wTerm (Ctx.ref_keep_of' hF h₁ rfl) (Ctx.ref_keep_of' hF h₂ VarType.keepable_dia)

/-- The object under a weakening. -/
theorem Term.mono_wTerm {Γ' : Ctx} (L : Γ.Le Γ') (h₁ : Γ.ref r₁ = some (.VTypeBox F))
    (h₂ : Γ.ref r₂ = some (.VTypeDia X)) :
    (⟨_, Term.mono L (wTerm (σ := σ) h₁ h₂).2⟩ : Σ b, Term σ Γ' (wTy F X) b) =
      ⟨_, (wTerm (L.ref h₁) (L.ref h₂)).2⟩ :=
  sig_pair (congrArg (Sigma.mk _) (Term.mono_eta L _ _ h₁))
    (congrArg (Sigma.mk _) (Term.mono_eta L _ _ h₂))

/-- Keeping the object, as a definable map. -/
def keepG (hF : ModalSys.Four = true) (F X : VarType) :
    GFunc σ (wTy F X) (.VTypeBox (wTy F X)) :=
  .comp (.boxPair _ _) (.pair (.comp (.dup hF) .fst) (.comp (.dkeep hF) .snd))

/-- ⭐Keeping the object is keeping its parts. -/
theorem applyG_keepG (hF : ModalSys.Four = true) (h₁ : Γ.ref r₁ = some (.VTypeBox F))
    (h₂ : Γ.ref r₂ = some (.VTypeDia X)) :
    Canon.applyG (keepG (σ := σ) hF F X) (wTerm h₁ h₂).2 =
      ⟨_, Term.boxtm (wKeep hF h₁ h₂).2⟩ := by
  have e₁ := GArrow.applyG_keep_eta (σ := σ) (hF := hF) (T := .VTypeBox F) rfl r₁ h₁
  have e₂ := GArrow.applyG_keep_eta (σ := σ) (hF := hF) (T := .VTypeDia X)
    VarType.keepable_dia r₂ h₂
  exact sig_boxtm (sig_pair (sig_unbox e₁) (sig_unbox e₂))

/-- The kept object, read here, is the object. -/
theorem Term.collapse_wKeep (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (h₁ : Γ.ref r₁ = some (.VTypeBox F)) (h₂ : Γ.ref r₂ = some (.VTypeDia X)) :
    (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) (wKeep (σ := σ) hF h₁ h₂).2⟩ :
      Σ b, Term σ Γ (wTy F X) b) = ⟨_, (wTerm h₁ h₂).2⟩ :=
  sig_pair (Term.collapse_eta _ _ _ _) (Term.collapse_eta _ _ _ _)

end Term

/-! ## `Back` at the object -/

/-- `Back (y.keep.dup) c` on a hole `⟨y, c⟩`. -/
def WFF.backDK (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) (F X : VarType) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (wTy F X) (wTy F X))) 1 :=
  WFF.backG hS (.comp (.dup hF) (.comp (keepG hF F X) .fst)) .snd

theorem WFF.holeAt_backDK (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Γ : Ctx}
    {d : ℕ} (hs : Γ.SlotsFrom d) {F X : VarType} {r₁ r₂ : VarSymb}
    (h₁ : Γ.ref r₁ = some (.VTypeBox F)) (h₂ : Γ.ref r₂ = some (.VTypeDia X)) {c₀ : Ann (wTy F X)}
    (c : Term σ Γ (wTy F X) c₀) :
    WFF.holeAt hs (Term.pair (wTerm h₁ h₂).2 c) (WFF.backDK hS hF F X) =
      WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ)
        (wKeep hF h₁ h₂).2))) c := by
  refine (WFF.holeAt_backG hS hs _ _ _).trans (WFF.back_congr hS .nec ?_ rfl)
  exact Canon.applyG_sig (.dup hF) (applyG_keepG hF h₁ h₂)

section Keep

variable {Γ : Ctx} [Γ.NoSlots] {F X : VarType} {r₁ r₂ : VarSymb}

/-- ⭐A kept object comes back as itself. -/
def Proof.back_wKeep (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (h₁ : Γ.ref r₁ = some (.VTypeBox F))
    (h₂ : Γ.ref r₂ = some (.VTypeDia X)) :
    Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) (wKeep hF h₁ h₂).2))) (wTerm h₁ h₂).2) :=
  Proof.conv (OutLeg.back_congr hS .nec (congrArg (Sigma.mk _) (Term.mono_refl _ _))
      (Term.collapse_wKeep hT hF h₁ h₂))
    (Proof.back_keep hS hT hF .nec (wKeep hF h₁ h₂).2 (Proof.dia_top hT))

/-- ⭐**Interchange at the object.** -/
def Proof.back_wKeep_read (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (h₁ : Γ.ref r₁ = some (.VTypeBox F))
    (h₂ : Γ.ref r₂ = some (.VTypeDia X)) {b : Ann (wTy F X)} (t : Term σ Γ (wTy F X) b)
    (φ : WFF σ (Γ.insert (.bnd 0) (wTy F X)) 1)
    (h : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) (wKeep hF h₁ h₂).2))) t))
    (p : Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots (wTerm h₁ h₂).2 φ) :=
  Proof.conv (WFF.instantiate_congr_sig _ ((congrArg (fun p =>
      (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) p.2⟩ : Σ e, Term σ Γ (wTy F X) e))
      (Term.collapse_shift_boxIn hT hF (wKeep hF h₁ h₂).2)).trans
      (Term.collapse_wKeep hT hF h₁ h₂)) φ)
    (Proof.back_here hS hT _ t φ h p)

end Keep

/-! ## The ties -/

section Ties

variable (F X : VarType)

/-- The type the packed object holds: the object's value, and the object kept. -/
abbrev wPackTy : VarType := .VTypeProd F (wTy F X)

/-- The slot of the packed shape. -/
abbrev wSlotTy : VarType := .VTypeProd (.VTypeBox (wPackTy F X)) (.VTypeDia X)

/-- The ties' hole. -/
abbrev wCtx : Ctx := Ctx.empty.insert (.bnd 0) (wSlotTy F X)

omit [ModalSys] in
theorem wCtx_slots : (wCtx F X).SlotsFrom 1 := Ctx.slotsFrom_empty.insert _

theorem w_p : (wCtx F X).ref (.step (.root (.bnd 0)) .fst) =
    some (.VTypeBox (wPackTy F X)) :=
  Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (wSlotTy F X))

theorem w_x : (wCtx F X).ref (.step (.root (.bnd 0)) .snd) = some (.VTypeDia X) :=
  Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (wSlotTy F X))

/-- The packed object's second part, one view in. -/
theorem w_z : (wCtx F X).boxIn.ref (.step (VarSymb.step (.root (.bnd 0)) .fst).inner .snd) =
    some (wTy F X) :=
  Ctx.ref_snd_of (Ctx.ref_inner (w_p F X))

/-- `Back (y.dup) x₁` on a hole `⟨x₁, ⟨y, _⟩⟩`. -/
def WFF.backFst (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (Ctx.empty.insert (.bnd 0) (wPackTy F X)) 1 :=
  WFF.backG hS (.comp (.dup hF) (.comp .fst .snd)) .fst

/-- `□ Back (y.dup) x₁`: `y`'s value comes back as the object's. -/
def WFF.wTieOne (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (wCtx F X) 1 :=
  WFF.box (WFF.holeAt (wCtx_slots F X).boxIn
    (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner (wPackTy F X)
      (Ctx.ref_inner (w_p F X)))
    (WFF.backFst F X hS hF))

/-- `□ Back (z.keep.dup) ⟨z.fst, x.keep⟩`: the second part one view in is `x` kept. -/
def WFF.wTieHere (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (wCtx F X) 1 :=
  WFF.box (WFF.holeAt (wCtx_slots F X).boxIn
    (Term.pair
      (Term.eta (.step (VarSymb.step (.root (.bnd 0)) .fst).inner .snd) (wTy F X) (w_z F X))
      (Term.pair
        (Term.eta (.step (.step (VarSymb.step (.root (.bnd 0)) .fst).inner .snd) .fst)
          (.VTypeBox F) (Ctx.ref_fst_of (w_z F X)))
        (Term.eta (.step (.step (.root (.bnd 0)) .snd) .keep) (.VTypeDia X)
          (Ctx.ref_keep_of' hF (w_x F X) VarType.keepable_dia))))
    (WFF.backDK hS hF F X))

/-- `□□ Back (y.keep.dup) z.keep`: the second part read two views in is of kept form. -/
def WFF.wTieTwo (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (wCtx F X) 1 :=
  WFF.box (WFF.box (WFF.holeAt (wCtx_slots F X).boxIn.boxIn
    (Term.pair
      (Term.eta (.step (VarSymb.step (.step (.root (.bnd 0)) .fst) .keep).inner .snd) (wTy F X)
        (Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_keep_of' hF (w_p F X) rfl))))
      (wKeep hF (Ctx.ref_fst_of (w_z F X)) (Ctx.ref_snd_of (w_z F X))).2)
    (WFF.backDK hS hF F X)))

/-- `Back (b.dup) ⟨d, x⟩`: the object read off `b` is the object. -/
def WFF.wTieThree (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (wCtx F X) 1 :=
  WFF.backG hS (.comp (.dup hF) (.comp (.boxMap .snd) .fst))
    (.pair (.comp (.boxMap .fst) .fst) .snd)

/-- ⭐**The ties** on the packed slot. -/
def WFF.wTies (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) : WFF σ (wCtx F X) 1 :=
  WFF.and (WFF.wTieOne F X hS hF) (WFF.and (WFF.wTieHere F X hS hF)
    (WFF.and (WFF.wTieTwo F X hS hF) (WFF.wTieThree F X hS hF)))

end Ties

section Read

variable {Γ : Ctx} {F X : VarType} {a₀ : Ann F} {z₁ z₂ x₂ : VarSymb}

/-- The packed slot's value at a term. -/
abbrev wSlot {Γ : Ctx} {F X : VarType} {a₀ : Ann F} {b₀ : Ann (wTy F X)} {x₀ : Ann (.VTypeDia X)}
    (a : Term σ Γ.boxIn F a₀) (Z : Term σ Γ.boxIn (wTy F X) b₀)
    (x : Term σ Γ (.VTypeDia X) x₀) : Term σ Γ (wSlotTy F X) (.prod (.box (.prod a₀ b₀)) x₀) :=
  Term.pair (Term.boxtm (Term.pair a Z)) x

/-- ⭐**The ties, read** at a packed object whose second part is two addresses, and an address. -/
theorem WFF.holeAt_wTies (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {d : ℕ}
    (hs : Γ.SlotsFrom d) (a : Term σ Γ.boxIn F a₀)
    (h₁ : Γ.boxIn.ref z₁ = some (.VTypeBox F)) (h₂ : Γ.boxIn.ref z₂ = some (.VTypeDia X))
    (hx : Γ.ref x₂ = some (.VTypeDia X)) :
    WFF.holeAt hs (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)) (WFF.wTies F X hS hF) =
      WFF.and
        (WFF.box (WFF.holeAt hs.boxIn (Term.pair a (wTerm h₁ h₂).2) (WFF.backFst F X hS hF)))
        (WFF.and
          (WFF.box (WFF.holeAt hs.boxIn
            (Term.pair (wTerm h₁ h₂).2 (wTerm h₁ (Ctx.ref_keep_of' hF hx
              VarType.keepable_dia)).2) (WFF.backDK hS hF F X)))
          (WFF.and
            (WFF.box (WFF.box (WFF.holeAt hs.boxIn.boxIn
              (Term.pair (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) (wTerm h₁ h₂).2)
                (wKeep hF h₁ h₂).2) (WFF.backDK hS hF F X))))
            (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
              (Ctx.shifts_boxIn_boxIn hF Γ) (wTerm h₁ h₂).2)))
              (Term.pair (Term.boxtm a) (Term.eta x₂ _ hx))))) := by
  have hr := Subst.at_single_root (σ := σ) (Δ := Γ) (.bnd 0)
    (.tm (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)))
  have hp : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)))).at (.step (.root (.bnd 0)) .fst) =
      .tm (Term.boxtm (Term.pair a (wTerm h₁ h₂).2)) := by
    rw [Subst.at_proj _ _ rfl, hr]
    rfl
  have hxx : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)))).at (.step (.root (.bnd 0)) .snd) =
      .tm (Term.eta x₂ _ hx) := by
    rw [Subst.at_proj _ _ rfl, hr]
    rfl
  have hin := Subst.box_at_inner_boxtm _ hp
  have hz : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)))).box.at
        (.step (VarSymb.step (.root (.bnd 0)) .fst).inner .snd) = .tm (wTerm h₁ h₂).2 := by
    rw [Subst.at_proj _ _ rfl, hin]
    rfl
  have hz₁ : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)))).box.at
        (.step (.step (VarSymb.step (.root (.bnd 0)) .fst).inner .snd) .fst) =
      .tm (Term.eta z₁ _ h₁) := by
    rw [Subst.at_proj _ _ rfl, hz]
    rfl
  have hz₂ : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)))).box.at
        (.step (.step (VarSymb.step (.root (.bnd 0)) .fst).inner .snd) .snd) =
      .tm (Term.eta z₂ _ h₂) := by
    rw [Subst.at_proj _ _ rfl, hz]
    rfl
  have hkp : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)))).box.at
        (.step (.step (.root (.bnd 0)) .fst) .keep) =
      .tm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ)
        (Term.pair a (wTerm h₁ h₂).2))) := by
    rw [Subst.box_at_keep, hp, SubE.keepE_tm _ hF]
  have e₁ : WFF.holeAt hs (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)) (WFF.wTieOne F X hS hF) =
      WFF.box (WFF.holeAt hs.boxIn (Term.pair a (wTerm h₁ h₂).2) (WFF.backFst F X hS hF)) :=
    congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ _).trans
      (WFF.holeAt_congr _ (Term.subst_eta_tm _ _ _ _ _ _ _ hin) _))
  have e₂ : WFF.holeAt hs (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx))
      (WFF.wTieHere F X hS hF) =
      WFF.box (WFF.holeAt hs.boxIn (Term.pair (wTerm h₁ h₂).2 (wTerm h₁ (Ctx.ref_keep_of' hF hx
        VarType.keepable_dia)).2) (WFF.backDK hS hF F X)) := by
    refine congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ _).trans
      (WFF.holeAt_congr _ (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _ hz)
        (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _ hz₁)
          (Term.subst_eta_tm _ _ _ _ _ _ _ ?_))) _))
    rw [Subst.box_at_keep, hxx]
    exact SubE.keepE_eta_dia hF hx
  have e₃ : WFF.holeAt hs (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx))
      (WFF.wTieTwo F X hS hF) =
      WFF.box (WFF.box (WFF.holeAt hs.boxIn.boxIn
        (Term.pair (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) (wTerm h₁ h₂).2)
          (wKeep hF h₁ h₂).2) (WFF.backDK hS hF F X))) := by
    refine congrArg WFF.box (congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ _).trans
      (WFF.holeAt_congr _ (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _ ?_)
        (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _ ?_)
          (Term.subst_eta_tm _ _ _ _ _ _ _ ?_))) _)))
    · rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ hkp]
      rfl
    · rw [Subst.box_at_keep, hz₁]
      exact SubE.keepE_eta hF h₁
    · rw [Subst.box_at_keep, hz₂]
      exact SubE.keepE_eta_dia hF h₂
  exact congrArg₂ WFF.and e₁ (congrArg₂ WFF.and e₂ (congrArg₂ WFF.and e₃
    (WFF.holeAt_backG hS hs _ _ _)))

end Read

/-! ## The unit's hole -/

section Unit

variable (F X : VarType)

/-- The hole of the unit: the packed value, the content, and the object going home. -/
abbrev wUnitTy : VarType :=
  .VTypeProd (.VTypeProd (wPackTy F X) X) (.VTypeBox (wTy F X))

/-- The hole's own context. -/
abbrev wUnitCtx : Ctx := Ctx.empty.insert (.bnd 0) (wUnitTy F X)

theorem wu_e : (wUnitCtx F X).ref (.step (.root (.bnd 0)) .snd) =
    some (.VTypeBox (wTy F X)) :=
  Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (wUnitTy F X))

theorem wu_y : (wUnitCtx F X).ref (.step (.step (.step (.root (.bnd 0)) .fst) .fst) .snd) =
    some (wTy F X) :=
  Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_fst_of
    (Ctx.ref_insert_root Ctx.empty (.bnd 0) (wUnitTy F X))))

/-- `□ Back (e.inner.keep.dup) y.keep` on a hole `⟨⟨⟨_, y⟩, _⟩, e⟩`: what the unit carries to the
    far end, where `e` is `y` kept. -/
def WFF.wTieUnit (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) :
    WFF σ (wUnitCtx F X) 1 :=
  WFF.box (WFF.holeAt (Ctx.slotsFrom_empty.insert _).boxIn
    (Term.pair
      (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner (wTy F X) (Ctx.ref_inner (wu_e F X)))
      (wKeep hF (Ctx.ref_fst_of (wu_y F X)) (Ctx.ref_snd_of (wu_y F X))).2)
    (WFF.backDK hS hF F X))

variable {F X}

/-- ⭐`WFF.wTieUnit`, read. -/
theorem WFF.holeAt_wTieUnit (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {Ω : Ctx}
    {d : ℕ} (hs : Ω.SlotsFrom d) {a₀ : Ann F} {c₀ : Ann X} {e₀ : Ann (wTy F X)}
    {z₁ z₂ : VarSymb} (a : Term σ Ω F a₀) (h₁ : Ω.ref z₁ = some (.VTypeBox F))
    (h₂ : Ω.ref z₂ = some (.VTypeDia X)) (c : Term σ Ω X c₀)
    (e : Term σ Ω.boxIn (wTy F X) e₀) :
    WFF.holeAt hs (Term.pair (Term.pair (Term.pair a (wTerm h₁ h₂).2) c) (Term.boxtm e))
        (WFF.wTieUnit F X hS hF) =
      WFF.box (WFF.holeAt hs.boxIn (Term.pair e (wKeep hF h₁ h₂).2) (WFF.backDK hS hF F X)) := by
  have hr := Subst.at_single_root (σ := σ) (Δ := Ω) (.bnd 0)
    (.tm (Term.pair (Term.pair (Term.pair a (wTerm h₁ h₂).2) c) (Term.boxtm e)))
  refine congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _
    (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ e (Subst.box_at_inner_boxtm _ ?_))
      (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _ ?_) (Term.subst_eta_tm _ _ _ _ _ _ _ ?_))) _))
  · rw [Subst.at_proj _ _ rfl, hr]
    rfl
  · rw [Subst.box_at_keep, Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl,
      Subst.at_proj _ _ rfl, hr]
    exact SubE.keepE_eta hF h₁
  · rw [Subst.box_at_keep, Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl,
      Subst.at_proj _ _ rfl, hr]
    exact SubE.keepE_eta_dia hF h₂

end Unit

/-! ## Opening the unit -/

/-- ⭐The unit along a possible part, opened at a fresh root of any view containing the `□` view. -/
theorem WFF.openFree_mono_unitBodyD {Γ V : Ctx} [Γ.NoSlots] [V.NoSlots] (h : Γ.boxIn.Le V) (u : ℕ)
    (hu : V.RootFresh (.free u)) (hS : ModalSys.BStrong = true) {C X A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd C X) (.VTypeBox A))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.mono (h.insert (.bnd 0) _) (WFF.unitBodyD hS sb θ)) =
      WFF.retx hS (.step (.root (.free u)) .snd)
        ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root V (.free u) (RShape.wit (.box C) X).ty)⟩
        (Term.mono (h.trans (Ctx.le_insert hu.root _)) sb)
        (WFF.holeAt ((Ctx.NoSlots.slots (Γ := (V.insert (.free u)
            (RShape.wit (.box C) X).ty).diaIn (.step (.root (.free u)) .snd))).insert _)
          (Term.pair
            (Term.pair
              (Term.eta (VarSymb.step (.root (.free u)) .fst).inner C
                ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := (V.insert (.free u)
                  (RShape.wit (.box C) X).ty).diaIn (.step (.root (.free u)) .snd))).root
                  (.VTypeBox A)).ref ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of
                    (Ctx.ref_insert_root V (.free u) (RShape.wit (.box C) X).ty))))))
              (Term.eta (.step (.step (.root (.free u)) .snd) .dia) X
                ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := (V.insert (.free u)
                  (RShape.wit (.box C) X).ty).diaIn (.step (.root (.free u)) .snd))).root
                  (.VTypeBox A)).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of
                    (Ctx.ref_insert_root V (.free u) (RShape.wit (.box C) X).ty))))))
            (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _)))
          θ) := by
  have hu0 := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu0
  have hs : V.SlotsFrom 0 := Ctx.NoSlots.slots
  have hθ₀ := Subst.ok_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := V))
    (RShape.wit (.box C) X).ty hu.root
  have hc₀ := Subst.coh_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := V)) Subst.coh_idRen hs
    (RShape.wit (.box C) X).ty hu.root
  have hl := h.insert (.bnd 0) (RShape.wit (.box C) X).ty
  have hθ := hθ₀.restrict hl
  have hc := hc₀.restrict hl
  have h0 : ((Subst.idRen (σ := σ) V).toFree 0 u (RShape.wit (.box C) X).ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  have hw : (((Subst.idRen (σ := σ) V).toFree 0 u (RShape.wit (.box C) X).ty
      hu.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .step (.root (.free u)) .snd := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hsl := (hs.insertFree u (RShape.wit (.box C) X).ty).diaIn (.step (.root (.free u)) .snd)
  unfold WFF.openFree
  rw [WFF.subst_mono]
  rotate_left
  · exact (Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _
  unfold WFF.unitBodyD
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.step (.root (.free u)) .snd) rfl
    ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ hsl (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · rw [Term.subst_mono]
    refine Term.subst_ren _ _ _ _ (Subst.at_ren_of fun v U hlp hv => ?_) sb
    have hvr : v ≠ .root (.bnd 0) := fun e => by
      subst e
      rw [(Ctx.NoSlots.slots (Γ := Γ.boxIn)).root] at hv
      cases hv
    rw [Subst.toFree_ne _ _ _ _ hvr]
    change ((Subst.idRen V) v).mono _ = _
    rw [← Subst.at_nonproj (Subst.idRen V) hlp, Subst.at_idRen]
    rfl
  · rw [WFF.subst_holeAt]
    have hT := Ctx.ref_insert_root V (.free u) (RShape.wit (.box C) X).ty
    refine WFF.holeAt_congr _ (sig_pair (sig_pair
      (Term.subst_eta_renAt _ _ _ C _ (VarSymb.step (.root (.free u)) .fst).inner _ _ ?_)
      (Term.subst_eta_renAt _ _ _ X _ (.step (.step (.root (.free u)) .snd) .dia) _ _ ?_))
      (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
        (Subst.under_at_slot _ (0 + 1) 0 _ _))) _
    · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.dia_eq_box_mono (Δ₁ := Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty)
          _ _ _ _ _ (Ctx.ref_inner (Ctx.ref_fst_of hu0)),
        Subst.box_at_inner_ren _ (w := .step (.root (.free u)) .fst)
          (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
      rfl
    · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
      dsimp only [Subst.dia]
      rw [if_pos rfl, Subst.at_proj _ _ rfl, h0]
      rfl

/-! ## The tied body -/

section Body

variable {V : Ctx} [V.NoSlots] {F X : VarType}

/-- The object read off the packed slot. -/
def wObj₀ (F X : VarType) : Σ b, Term σ (wCtx F X) (wTy F X) b :=
  ⟨_, Term.pair
    (Term.boxtm (Term.eta (.step (VarSymb.step (.root (.bnd 0)) .fst).inner .fst) F
      (Ctx.ref_fst_of (Ctx.ref_inner (w_p F X)))))
    (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeDia X) (w_x F X))⟩

/-- ⭐**The tied body**: `Ψ` of the object, with the ties. -/
def WFF.tiedW (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (Ψ : WFF σ (V.insert (.bnd 0) (wTy F X)) 1) : WFF σ (V.insert (.bnd 0) (wSlotTy F X)) 1 :=
  WFF.and (WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _) (wObj₀ (σ := σ) F X).2) Ψ)
    (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _)
      (Term.eta (.root (.bnd 0)) (wSlotTy F X) (Ctx.ref_insert_root V (.bnd 0) (wSlotTy F X)))
      (WFF.wTies F X hS hF))

/-- The tied body under a weakening of the view. -/
theorem WFF.mono_tiedW {V' : Ctx} [V'.NoSlots] (h : V.Le V') (hS : ModalSys.BStrong = true)
    (hF : ModalSys.Four = true) (Ψ : WFF σ (V.insert (.bnd 0) (wTy F X)) 1) :
    WFF.mono (h.insert (.bnd 0) _) (WFF.tiedW hS hF Ψ) =
      WFF.tiedW hS hF (WFF.mono (h.insert (.bnd 0) _) Ψ) := by
  refine congrArg₂ WFF.and ?_ ?_
  · rw [WFF.mono_bodyRepl h, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := V')).insert _), Term.mono_eta]

/-- ⭐The tied body at a packed object. -/
theorem WFF.instantiate_tiedW (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (Ψ : WFF σ (V.insert (.bnd 0) (wTy F X)) 1) {a₀ : Ann F} {b₀ : Ann (wTy F X)}
    {x₀ : Ann (.VTypeDia X)} (a : Term σ V.boxIn F a₀) (Z : Term σ V.boxIn (wTy F X) b₀)
    (x : Term σ V (.VTypeDia X) x₀) :
    WFF.instantiate Ctx.NoSlots.slots (wSlot a Z x) (WFF.tiedW hS hF Ψ) =
      WFF.and (WFF.instantiate Ctx.NoSlots.slots (Term.pair (Term.boxtm a) x) Ψ)
        (WFF.holeAt Ctx.NoSlots.slots (wSlot a Z x) (WFF.wTies F X hS hF)) := by
  have hat := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0) (.tm (wSlot a Z x))
  have hp : (Subst.single (σ := σ) (Δ := V) (.bnd 0) (.tm (wSlot a Z x))).at
      (.step (.root (.bnd 0)) .fst) = .tm (Term.boxtm (Term.pair a Z)) := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have hx : (Subst.single (σ := σ) (Δ := V) (.bnd 0) (.tm (wSlot a Z x))).at
      (.step (.root (.bnd 0)) .snd) = .tm x := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have ha : (Subst.single (σ := σ) (Δ := V) (.bnd 0) (.tm (wSlot a Z x))).box.at
      (.step (VarSymb.step (.root (.bnd 0)) .fst).inner .fst) = .tm a := by
    rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ hp]
    rfl
  refine congrArg₂ WFF.and ((WFF.instantiate_bodyRepl _ _ _).trans
    (WFF.instantiate_congr_sig _ ?_ Ψ)) ?_
  · rw [Term.subst_mono]
    exact sig_pair (sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ a ha))
      (Term.subst_eta_tm _ _ _ _ _ _ x hx)
  · change WFF.subst _ _ _ _ _ _ (WFF.holeAt _ _ _) = _
    rw [WFF.subst_holeAt]
    exact WFF.holeAt_congr _ (Term.subst_eta_tm _ _ _ _ _ _ _ hat) _

end Body

/-! ## The ties hold of the object kept -/

section Intro

variable {Γ : Ctx} [Γ.NoSlots] {F X : VarType} {a₁ a₂ : VarSymb}

/-- ⭐**The ties hold of `⟨d, x⟩` and its kept form**: each is `back_keep`. -/
def Proof.wTies_intro (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (h₁ : Γ.ref a₁ = some (.VTypeBox F))
    (h₂ : Γ.ref a₂ = some (.VTypeDia X)) :
    Proof σ Γ Δ (WFF.holeAt Ctx.NoSlots.slots
      (wSlot (Term.eta a₁.inner F (Ctx.ref_inner h₁)) (wKeep hF h₁ h₂).2 (Term.eta a₂ _ h₂))
      (WFF.wTies F X hS hF)) := by
  have k₁ := Ctx.ref_keep_of' hF h₁ rfl
  have k₂ := Ctx.ref_keep_of' hF h₂ VarType.keepable_dia
  have hsh := Ctx.shifts_boxIn_boxIn hF Γ
  refine Proof.conv (WFF.holeAt_wTies hS hF _ _ k₁ k₂ h₂).symm (Proof.and_intro ?_
    (Proof.and_intro ?_ (Proof.and_intro ?_ ?_)))
  · have e : (⟨_, Term.eta (σ := σ) (VarSymb.step a₁ .keep).inner F (Ctx.ref_inner k₁)⟩ :
        Σ c, Term σ Γ.boxIn.boxIn F c) =
        ⟨_, Term.shift hsh (Term.eta (σ := σ) a₁.inner F (Ctx.ref_inner h₁))⟩ :=
      ((Term.shift_eta hsh a₁.inner F (Ctx.ref_inner h₁)).trans
        (Term.eta_congr (VarSymb.inner_shift_zero a₁) F _ _)).symm
    exact Proof.nec (Proof.conv (Eq.symm ((WFF.holeAt_backG hS _ _ _ _).trans
      (WFF.back_congr hS .nec (sig_boxtm (sig_boxtm (congrArg (fun p =>
        (⟨_, Term.shift (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) p.2⟩ :
          Σ c, Term σ Γ.boxIn.boxIn.boxIn F c)) e))) rfl)))
      (Proof.back_shift hS hT hF (Term.eta a₁.inner F (Ctx.ref_inner h₁))))
  · exact Proof.nec (Proof.conv (WFF.holeAt_backDK hS hF _ k₁ k₂ _).symm
      (Proof.back_wKeep hS hT hF k₁ k₂))
  · have k₁' := Ctx.ref_keep_of' hF k₁ rfl
    have k₂' := Ctx.ref_keep_of' hF k₂ VarType.keepable_dia
    refine Proof.nec (Proof.nec (Proof.conv ((WFF.holeAt_backDK hS hF _ k₁' k₂' _).symm.trans
      (WFF.holeAt_congr _ (sig_pair ?_ rfl) _)) (Proof.back_wKeep hS hT hF k₁' k₂')))
    exact (sig_pair
      ((Term.shift_eta hsh _ _ _).trans (Term.eta_congr
        (VarSymb.shift_level_zero (s := .keep) rfl) _ _ _))
      ((Term.shift_eta hsh _ _ _).trans (Term.eta_congr
        (VarSymb.shift_level_zero (s := .keep) rfl) _ _ _))).symm
  · exact Proof.back_wKeep hS hT hF h₁ h₂

end Intro

/-! ## The nested step along a leg -/

section Swap

variable {V : Ctx} [V.NoSlots] {F X : VarType}

/-- `□ Back (e.inner.keep.dup) x`, the body `ret_counitC` asks of the nested returning possibility,
    in any view. -/
def WFF.cBodyW (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) {b : Ann (wTy F X)}
    (x : Term σ V.boxIn (wTy F X) b) : WFF σ (V.insert (.bnd 0) (.VTypeBox (wTy F X))) 1 :=
  WFF.box (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert (.VTypeBox (wTy F X))).boxIn
    (Term.pair
      (Term.eta (VarSymb.root (.bnd 0)).inner (wTy F X)
        (Ctx.ref_inner (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox (wTy F X)))))
      (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root
        (.VTypeBox (wTy F X))).boxIn) x))
    (WFF.backDK hS hF F X))

/-- `WFF.cBodyW`, opened at a fresh root. -/
theorem WFF.openFree_cBodyW (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true) (e : ℕ)
    (he : V.RootFresh (.free e)) {b : Ann (wTy F X)} (x : Term σ V.boxIn (wTy F X) b) :
    WFF.openFree e he Ctx.NoSlots.slots (WFF.cBodyW hS hF x) =
      WFF.box (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair
          (Term.eta (VarSymb.root (.free e)).inner (wTy F X)
            (Ctx.ref_inner (Ctx.ref_insert_root V (.free e) (.VTypeBox (wTy F X)))))
          (Term.mono (Ctx.le_insert he.root (.VTypeBox (wTy F X))).boxIn x))
        (WFF.backDK hS hF F X)) := by
  have hl := Ctx.le_insert he.root (.VTypeBox (wTy F X))
  rw [← WFF.instantiate_eta_openFree e he Ctx.NoSlots.slots Ctx.NoSlots.slots]
  unfold WFF.cBodyW WFF.instantiate WFF.substRoot
  change WFF.box (WFF.subst _ _ _ _ _ _ (WFF.mono _ (WFF.holeAt _ _ _))) = _
  rw [WFF.mono_holeAt _ _
    ((Ctx.NoSlots.slots (Γ := V.insert (.free e) (.VTypeBox (wTy F X)))).insert _).boxIn,
    WFF.subst_holeAt]
  refine congrArg WFF.box (WFF.holeAt_congr _ (sig_pair ?_ ?_) _)
  · rw [Term.mono_eta]
    exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _))
  · rw [Term.mono_mono]
    exact Term.subst_single_box_mono hl
      (hl.trans (Ctx.le_insert (Ctx.NoSlots.slots
        (Γ := V.insert (.free e) (.VTypeBox (wTy F X)))).root _))
      (.tm (Term.eta (.root (.free e)) (.VTypeBox (wTy F X)) (Ctx.ref_insert_root _ _ _)))
      (Subst.ok_single (Ctx.Le.refl _) rfl)
      (Subst.coh_single ((Ctx.NoSlots.slots
        (Γ := V.insert (.free e) (.VTypeBox (wTy F X)))).rootFresh (le_refl 0))
        (Ctx.Le.refl _) rfl)
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) x

/-- Necessity along a leg distributes over a derivation in its view. -/
def Proof.leg_K {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} : (O : OutLeg Γ) →
    {ψ χ : WFF σ O.view 0} → Proof σ O.view [ψ] χ → Proof σ Γ Δ (O.box ψ) → Proof σ Γ Δ (O.box χ)
  | .nec, ψ, _, h, p => Proof.imp_elim (Proof.imp_intro (Proof.ofSubset (fun _ hx => by
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
      subst hx
      exact List.mem_cons_self) (Proof.K_box (Δ := [ψ]) h))) p
  | .pos _ hy, ψ, _, h, p => Proof.imp_elim (Proof.imp_intro (Proof.ofSubset (fun _ hx => by
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
      subst hx
      exact List.mem_cons_self) (Proof.boxxK hy (Δ := [ψ]) h))) p

/-- ⭐**Swapping the value** under a nested returning possibility along a leg. -/
def Proof.ret_swapW (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ)
    (e : ℕ) (he : O.view.RootFresh (.free e)) {m₀ : Ann (wTy F X)}
    (m : Term σ Γ (wTy F X) m₀) {y₁ y₂ : VarSymb}
    (hy₁ : O.view.boxIn.ref y₁ = some (.VTypeBox F))
    (hy₂ : O.view.boxIn.ref y₂ = some (.VTypeDia X)) {k₀ : Ann (wTy F X)}
    (k : Term σ O.view.boxIn (wTy F X) k₀)
    (hN : Proof σ Γ Δ (O.ret hS m (WFF.cBodyW hS hF k)))
    (h₂ : Proof σ Γ Δ (O.box (WFF.box (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (wTerm hy₁ hy₂).2 k) (WFF.backDK hS hF F X))))) :
    Proof σ Γ Δ (O.ret hS m (WFF.cBodyW hS hF (wTerm hy₁ hy₂).2)) := by
  have hl := Ctx.le_insert he.root (.VTypeBox (wTy F X))
  let E := Term.eta (σ := σ) (VarSymb.root (.free e)).inner (wTy F X)
    (Ctx.ref_inner (Ctx.ref_insert_root O.view (.free e) (.VTypeBox (wTy F X))))
  let T := WFF.holeAt Ctx.NoSlots.slots (Term.pair (wTerm hy₁ hy₂).2 k) (WFF.backDK hS hF F X)
  let H := WFF.holeAt Ctx.NoSlots.slots (Term.pair E (Term.mono hl.boxIn k))
    (WFF.backDK hS hF F X)
  have hy₁' := hl.boxIn.ref hy₁
  have hy₂' := hl.boxIn.ref hy₂
  have hm : Term.mono hl.boxIn (wTerm hy₁ hy₂).2 = (wTerm (σ := σ) hy₁' hy₂').2 :=
    congrArg₂ Term.pair (Term.mono_eta _ _ _ _) (Term.mono_eta _ _ _ _)
  have e₁ : WFF.mono hl.boxIn T = WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF _) (wKeep hF hy₁' hy₂').2))) (Term.mono hl.boxIn k) := by
    refine (WFF.mono_holeAt hl.boxIn Ctx.NoSlots.slots Ctx.NoSlots.slots _ _).trans ?_
    refine (WFF.holeAt_congr _ (sig_pair (congrArg (Sigma.mk _) hm) rfl) _).trans ?_
    exact WFF.holeAt_backDK hS hF _ hy₁' hy₂' _
  have q₂ : Proof σ (O.view.insert (.free e) (.VTypeBox (wTy F X))).boxIn
      [H, WFF.mono hl.boxIn T]
      (WFF.holeAt Ctx.NoSlots.slots (Term.pair E (Term.mono hl.boxIn (wTerm hy₁ hy₂).2))
        (WFF.backDK hS hF F X)) := by
    rw [hm]
    exact Proof.conv (WFF.instantiate_holeAt_pair E _ _) (Proof.back_wKeep_read hS hT hF hy₁' hy₂'
      (Term.mono hl.boxIn k) _
      (Proof.conv e₁ (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
      (Proof.conv (WFF.instantiate_holeAt_pair E _ _).symm (Proof.lookup List.mem_cons_self)))
  have h₀ := Proof.all_intro (Δ := [WFF.box T]) e (.VTypeBox (wTy F X)) he
    (φ := WFF.openFree e he Ctx.NoSlots.slots
      (WFF.imp (WFF.cBodyW hS hF k) (WFF.cBodyW hS hF (wTerm hy₁ hy₂).2)))
    (Proof.conv (congrArg₂ WFF.imp (WFF.openFree_cBodyW hS hF e he k)
      (WFF.openFree_cBodyW hS hF e he (wTerm hy₁ hy₂).2)).symm
      (Proof.imp_intro (Proof.K_box (Δ := [H, WFF.mono hl.boxIn T]) q₂)))
  rw [WFF.bindFree_openFree] at h₀
  exact Proof.ret_mono hS O m _ _ hN (Proof.leg_K O h₀ h₂)

end Swap

/-! ## The counit along either leg -/

section Counit

/-- A body over the `□` view, in the leg's view, is that body weakened. -/
theorem OutLeg.lift_eq_mono {Γ : Ctx} {T : VarType} (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    (O : OutLeg Γ) → O.lift φ = WFF.mono (O.le_view.insert (.bnd 0) T) φ
  | .nec => (WFF.mono_refl _ φ).symm
  | .pos _ _ => rfl

/-- The negation of a hole formula at the first half of its hole. -/
def WFF.negFst {C D : VarType} (ψ : WFF σ (Ctx.empty.insert (.bnd 0) C) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C D)) 1 :=
  WFF.neg (WFF.holeAt (Ctx.slotsFrom_empty.insert _)
    (Term.eta (.step (.root (.bnd 0)) .fst) C (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) ψ)

theorem WFF.holeAt_negFst {Ω : Ctx} {d : ℕ} (hs : Ω.SlotsFrom d) {C D : VarType}
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) C) 1) {a : Ann C} {b : Ann D} (p : Term σ Ω C a)
    (q : Term σ Ω D b) :
    WFF.holeAt hs (Term.pair p q) (WFF.negFst (D := D) ψ) = WFF.neg (WFF.holeAt hs p ψ) :=
  congrArg WFF.neg ((WFF.subst_holeAt _ _ _ _ _ _ _).trans
    (WFF.holeAt_congr _ (Term.holeAt_pair_fst p q) ψ))

/-- Possibility of nothing is nothing, along a leg. -/
def Proof.leg_dia_bot {Γ : Ctx} {Δ : List (WFF σ Γ 0)} :
    (O : OutLeg Γ) → Proof σ Γ Δ (O.dia .bot) → Proof σ Γ Δ .bot
  | .nec, p => Proof.imp_elim p (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
      (Proof.K_box (Δ := []) (Proof.imp_intro (Proof.lookup List.mem_cons_self))))
  | .pos y hy, p => Proof.dia_bot y hy p

variable {Γ : Ctx} [Γ.NoSlots] {C X : VarType}

/-- ⭐**The counit of a possible part, along either leg**: `ret_counitD`, for a body that makes the
    hole formula necessary along the part.  Were it false, the unit would carry its negation out
    along the part, against the body. -/
def Proof.counitD_leg (hS : ModalSys.BStrong = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ)
    {c : Ann (.VTypeProd C X)} (y : Term σ Γ (.VTypeProd C X) c)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) 1) (u e : ℕ)
    (hu : O.view.RootFresh (.free u))
    (he : ((O.view.insert (.free u) (RShape.wit (.box C) X).ty).diaIn
      (.step (.root (.free u)) .snd)).RootFresh (.free e))
    (H : Proof σ Γ Δ (O.retS hS (.wit (.box C) X) y Ψ))
    (hb : Proof σ (O.view.insert (.free u) (RShape.wit (.box C) X).ty)
      [WFF.openFree u hu Ctx.NoSlots.slots Ψ]
      (WFF.boxx (.step (.root (.free u)) .snd)
        ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root O.view (.free u) (RShape.wit (.box C) X).ty)⟩
        (WFF.holeAt Ctx.NoSlots.slots
          (Term.pair
            (Term.eta (VarSymb.step (.root (.free u)) .fst).inner C
              ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of
                (Ctx.ref_insert_root O.view (.free u) (RShape.wit (.box C) X).ty)))))
            (Term.eta (.step (.step (.root (.free u)) .snd) .dia) X
              (Ctx.ref_diaIn_of (Ctx.ref_snd_of
                (Ctx.ref_insert_root O.view (.free u) (RShape.wit (.box C) X).ty))))) ψ))) :
    Proof σ Γ Δ (WFF.holeRead y ψ) := by
  refine Proof.byContra ?_
  have q : Proof σ Γ (WFF.neg (WFF.holeRead y ψ) :: Δ)
      (WFF.holeRead (Term.pair y (Term.boxtm (Term.unit))) (WFF.negFst ψ)) :=
    Proof.conv (((WFF.holeAt_negFst _ ψ y _).trans (congrArg WFF.neg
      (WFF.holeRead_eq_holeAt y ψ).symm)).symm.trans (WFF.holeRead_eq_holeAt _ _).symm)
      (Proof.lookup List.mem_cons_self)
  refine Proof.leg_dia_bot O (Proof.leg_dia O ?_ (Proof.ret_diaS hS O _ _
    (Proof.ret_unitD hS O y Ψ Term.unit (WFF.negFst ψ)
      (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) H) q)))
  have hx' : ∃ X', (O.view.insert (.free u) (RShape.wit (.box C) X).ty).ref
      (.step (.root (.free u)) .snd) = some (.VTypeDia X') :=
    ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root O.view (.free u) (RShape.wit (.box C) X).ty)⟩
  refine Proof.ex_elim u _ hu
    (φ := WFF.and (WFF.openFree u hu Ctx.NoSlots.slots Ψ) (WFF.openFree u hu Ctx.NoSlots.slots
      (O.lift (WFF.unitBodyD hS (Term.unit) (WFF.negFst ψ)))))
    (Proof.conv ?_ (Proof.lookup List.mem_cons_self)) ?_
  · exact (congrArg (WFF.ex _) (WFF.bindFree_openFree u hu Ctx.NoSlots.slots
      (WFF.and Ψ (O.lift (WFF.unitBodyD hS Term.unit (WFF.negFst ψ)))))).symm
  let D := (O.view.insert (.free u) (RShape.wit (.box C) X).ty).diaIn
    (.step (.root (.free u)) .snd)
  have hle := Ctx.le_insert (Ctx.NoSlots.slots (Γ := D)).root (.VTypeBox .VTypeOne)
  let P₀ := Term.pair (Term.eta (σ := σ) (VarSymb.step (.root (.free u)) .fst).inner C
      ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of
        (Ctx.ref_insert_root O.view (.free u) (RShape.wit (.box C) X).ty)))))
    (Term.eta (.step (.step (.root (.free u)) .snd) .dia) X
      (Ctx.ref_diaIn_of (Ctx.ref_snd_of
        (Ctx.ref_insert_root O.view (.free u) (RShape.wit (.box C) X).ty))))
  have eU : WFF.openFree u hu Ctx.NoSlots.slots
      (O.lift (WFF.unitBodyD hS Term.unit (WFF.negFst ψ))) =
      WFF.retx hS (.step (.root (.free u)) .snd) hx'
        (Term.mono (O.le_view.trans (Ctx.le_insert hu.root _)) Term.unit)
        (WFF.neg (WFF.holeAt ((Ctx.NoSlots.slots (Γ := D)).insert _) (Term.mono hle P₀) ψ)) := by
    rw [OutLeg.lift_eq_mono _ O, WFF.openFree_mono_unitBodyD O.le_view]
    refine WFF.retxS_congr hS _ _ _ rfl ((WFF.holeAt_negFst _ ψ _ _).trans
      (congrArg WFF.neg (WFF.holeAt_congr _ (sig_pair ?_ ?_) ψ)))
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
  have h₃ : Proof σ D [WFF.ex (.VTypeBox .VTypeOne)
      (WFF.neg (WFF.holeAt ((Ctx.NoSlots.slots (Γ := D)).insert _) (Term.mono hle P₀) ψ))]
      (WFF.neg (WFF.holeAt Ctx.NoSlots.slots P₀ ψ)) := by
    refine Proof.ex_elim e _ he (φ := WFF.openFree e he Ctx.NoSlots.slots
      (WFF.neg (WFF.holeAt ((Ctx.NoSlots.slots (Γ := D)).insert _) (Term.mono hle P₀) ψ)))
      (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree e he Ctx.NoSlots.slots _)).symm
        (Proof.lookup List.mem_cons_self)) ?_
    have eO : WFF.openFree e he Ctx.NoSlots.slots
        (WFF.neg (WFF.holeAt ((Ctx.NoSlots.slots (Γ := D)).insert _) (Term.mono hle P₀) ψ)) =
        WFF.neg (WFF.holeAt Ctx.NoSlots.slots
          (Term.mono (Ctx.le_insert he.root (.VTypeBox .VTypeOne)) P₀) ψ) :=
      congrArg WFF.neg ((WFF.subst_holeAt _ _ _ _ _ _ ψ).trans
        (WFF.holeAt_congr _ (subst_toFree_mono_sig he P₀) ψ))
    exact Proof.conv (congrArg WFF.neg (WFF.mono_holeAt _ _ Ctx.NoSlots.slots P₀ ψ)).symm
      (Proof.conv eO (Proof.lookup List.mem_cons_self))
  refine Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
    (Proof.imp_intro ?_)) (Proof.lookup List.mem_cons_self)
  exact Proof.imp_elim (Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
    (Proof.imp_intro hb)) (Proof.and_elim_l (Proof.lookup List.mem_cons_self)))
    (Proof.leg_dia (.pos _ hx') h₃ (Proof.ret_diaS hS (.pos _ hx') _ _ (Proof.conv eU
      (Proof.and_elim_r (Proof.lookup List.mem_cons_self)))))

end Counit

/-! ## The far end -/

section Far

variable {F X : VarType}

/-- `Back (y.dup) x₁ ∧ Here (z, c)` on a hole `⟨⟨x₁, ⟨y, z⟩⟩, c⟩`: what comes home. -/
def WFF.wCounit (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (F X : VarType) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (wPackTy F X) X)) 1 :=
  WFF.and
    (WFF.holeAt (Ctx.slotsFrom_empty.insert _)
      (Term.eta (.step (.root (.bnd 0)) .fst) (wPackTy F X)
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) (WFF.backFst F X hS hF))
    (WFF.here hT
      (Term.eta (.step (.step (.step (.root (.bnd 0)) .fst) .snd) .snd) (.VTypeDia X)
        (Ctx.ref_snd_of (Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))))
      (Term.eta (.step (.root (.bnd 0)) .snd) X (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))

/-- `WFF.wCounit`, read. -/
theorem WFF.holeAt_wCounit (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Ω : Ctx} {d : ℕ} (hs : Ω.SlotsFrom d) {a₀ : Ann F} {c₀ : Ann X}
    {z₁ z₂ : VarSymb} (a : Term σ Ω F a₀) (h₁ : Ω.ref z₁ = some (.VTypeBox F))
    (h₂ : Ω.ref z₂ = some (.VTypeDia X)) (c : Term σ Ω X c₀) :
    WFF.holeAt hs (Term.pair (Term.pair a (wTerm h₁ h₂).2) c) (WFF.wCounit hS hT hF F X) =
      WFF.and (WFF.holeAt hs (Term.pair a (wTerm h₁ h₂).2) (WFF.backFst F X hS hF))
        (WFF.here hT (Term.eta z₂ _ h₂) c) := by
  have hr := Subst.at_single_root (σ := σ) (Δ := Ω) (.bnd 0)
    (.tm (Term.pair (Term.pair a (wTerm h₁ h₂).2) c))
  refine congrArg₂ WFF.and ((WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _
    (Term.holeAt_pair_fst _ _) _)) (WFF.here_congr hT (Term.subst_eta_tm _ _ _ _ _ _ _ ?_)
      (Term.holeAt_pair_snd _ _))
  rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, hr]
  rfl

/-- Filling a pair into a `Here` about its second half. -/
theorem WFF.instantiate_here_snd {Ω : Ctx} [Ω.NoSlots] (hT : ModalSys.T = true) {B : VarType}
    {c₀ : Ann X} (c : Term σ Ω X c₀) {u₀ : Ann B} {v₀ : Ann (.VTypeDia X)} (u : Term σ Ω B u₀)
    (v : Term σ Ω (.VTypeDia X) v₀) :
    WFF.instantiate Ctx.NoSlots.slots (Term.pair u v) (WFF.here hT
      (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeDia X)
        (Ctx.ref_snd_of (Ctx.ref_insert_root Ω (.bnd 0) (.VTypeProd B (.VTypeDia X)))))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Ω)).root _) c)) =
      WFF.here hT v c := by
  have hr := Subst.at_single_root (σ := σ) (Δ := Ω) (.bnd 0) (.tm (Term.pair u v))
  refine WFF.here_congr hT (Term.subst_eta_tm _ _ _ _ _ _ v ?_)
    ((Term.subst_single_mono (Ctx.Le.refl _) _ _ _ _
      ((Ctx.NoSlots.slots (Γ := Ω)).rootFresh (le_refl 0)) c).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ c)))
  rw [Subst.at_proj _ _ rfl, hr]
  rfl

theorem WFF.cBodyW_congr {V : Ctx} [V.NoSlots] (hS : ModalSys.BStrong = true)
    (hF : ModalSys.Four = true) {b b' : Ann (wTy F X)} {x : Term σ V.boxIn (wTy F X) b}
    {x' : Term σ V.boxIn (wTy F X) b'}
    (h : (⟨b, x⟩ : Σ c, Term σ V.boxIn (wTy F X) c) = ⟨b', x'⟩) :
    WFF.cBodyW hS hF x = WFF.cBodyW hS hF x' := by
  cases h
  rfl

variable {Γ : Ctx} [Γ.NoSlots] {z₁ z₂ x₂ : VarSymb}

/-- ⭐**What comes home is necessary along the part**: the ties, and `here_keep`, whose possible
    object the ties identify with the packed one. -/
def Proof.wCounit_boxx (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} {a₀ : Ann F} (a : Term σ Γ.boxIn F a₀)
    (h₁ : Γ.boxIn.ref z₁ = some (.VTypeBox F)) (h₂ : Γ.boxIn.ref z₂ = some (.VTypeDia X))
    (hx : Γ.ref x₂ = some (.VTypeDia X))
    (hK : Proof σ Γ Δ (WFF.holeAt Ctx.NoSlots.slots
      (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)) (WFF.wTies F X hS hF))) :
    Proof σ Γ Δ (WFF.boxx x₂ ⟨X, hx⟩ (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.pair (Term.mono (Ctx.le_boxIn_diaIn Γ x₂) a)
        (wTerm ((Ctx.le_boxIn_diaIn Γ x₂).ref h₁) ((Ctx.le_boxIn_diaIn Γ x₂).ref h₂)).2)
        (Term.eta (.step x₂ .dia) X (Ctx.ref_diaIn_of hx))) (WFF.wCounit hS hT hF F X))) := by
  have hK' := Proof.conv (WFF.holeAt_wTies hS hF _ a h₁ h₂ hx) hK
  have L := Ctx.le_boxIn_diaIn Γ x₂
  have h₁' := L.ref h₁
  have h₂' := L.ref h₂
  have hkx := Ctx.ref_keep_of' hF hx VarType.keepable_dia
  have hkx' := L.ref hkx
  let c' := Term.eta (σ := σ) (.step x₂ .dia) X (Ctx.ref_diaIn_of hx)
  let A₁ := WFF.holeAt (Ctx.NoSlots.slots (Γ := Γ.boxIn)) (Term.pair a (wTerm (σ := σ) h₁ h₂).2)
    (WFF.backFst F X hS hF)
  let A₄ := WFF.holeAt (Ctx.NoSlots.slots (Γ := Γ.boxIn))
    (Term.pair (wTerm (σ := σ) h₁ h₂).2 (wTerm h₁ hkx).2) (WFF.backDK hS hF F X)
  have hm : ∀ {r₁ r₂ : VarSymb} (u₁ : Γ.boxIn.ref r₁ = some (.VTypeBox F))
      (u₂ : Γ.boxIn.ref r₂ = some (.VTypeDia X)),
      Term.mono L (wTerm (σ := σ) u₁ u₂).2 = (wTerm (L.ref u₁) (L.ref u₂)).2 :=
    fun _ _ => congrArg₂ Term.pair (Term.mono_eta _ _ _ _) (Term.mono_eta _ _ _ _)
  have e₁ : WFF.mono L A₁ = WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.mono L a) (wTerm h₁' h₂').2) (WFF.backFst F X hS hF) :=
    (WFF.mono_holeAt L _ Ctx.NoSlots.slots _ _).trans
      (WFF.holeAt_congr _ (sig_pair rfl (congrArg (Sigma.mk _) (hm h₁ h₂))) _)
  have e₄ : WFF.mono L A₄ = WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF _) (wKeep hF h₁' h₂').2))) (wTerm h₁' hkx').2 :=
    (WFF.mono_holeAt L _ Ctx.NoSlots.slots _ _).trans ((WFF.holeAt_congr _
      (sig_pair (congrArg (Sigma.mk _) (hm h₁ h₂)) (congrArg (Sigma.mk _) (hm h₁ hkx))) _).trans
      (WFF.holeAt_backDK hS hF _ h₁' h₂' _))
  have hH := Proof.here_keep (Δ := Δ) hT hF x₂ ⟨X, hx⟩ c'
  let H₃ : WFF σ (Γ.diaIn x₂) 0 := WFF.here hT (Term.mono L (Term.diatm (.step x₂ .keep)
    (Ctx.exists_keep_dia hF ⟨X, hx⟩)
    (Term.shift (Ctx.shifts_diaIn_keep hF Γ x₂) c'))) c'
  have e₃ : H₃ = WFF.here hT (Term.eta (.step x₂ .keep) (.VTypeDia X) hkx') c' := by
    have s₁ : (⟨_, Term.diatm (.step x₂ .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
        (Term.shift (Ctx.shifts_diaIn_keep hF Γ x₂) c')⟩ :
        Σ b, Term σ Γ.boxIn (.VTypeDia X) b) = ⟨_, Term.eta (.step x₂ .keep) (.VTypeDia X) hkx⟩ :=
      sig_diatm ((Term.shift_eta _ _ X _).trans (Term.eta_congr
        (VarSymb.shift_level_zero (s := .dia) rfl) X _ _))
    refine WFF.here_congr hT ((congrArg (fun p =>
      (⟨_, Term.mono L p.2⟩ : Σ b, Term σ (Γ.diaIn x₂) (.VTypeDia X) b)) s₁).trans ?_) rfl
    exact congrArg (Sigma.mk _) (Term.mono_eta L _ _ hkx)
  have q : Proof σ (Γ.diaIn x₂) [WFF.mono L A₁, WFF.mono L A₄, H₃]
      (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair (Term.pair (Term.mono L a) (wTerm h₁' h₂').2) c')
        (WFF.wCounit hS hT hF F X)) := by
    refine Proof.conv (WFF.holeAt_wCounit hS hT hF _ _ h₁' h₂' c').symm (Proof.and_intro
      (Proof.conv e₁ (Proof.lookup List.mem_cons_self)) ?_)
    have hw := Proof.back_wKeep_read (Δ := [WFF.mono L A₁, WFF.mono L A₄, H₃]) hS hT hF h₁' h₂'
      (wTerm h₁' hkx').2 (WFF.here hT
        (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeDia X)
          (Ctx.ref_snd_of (Ctx.ref_insert_root (Γ.diaIn x₂) (.bnd 0) (wTy F X))))
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x₂)).root _) c'))
      (Proof.conv e₄ (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
      (Proof.conv (e₃.trans (WFF.instantiate_here_snd hT c' _ _).symm)
        (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    exact Proof.conv (WFF.instantiate_here_snd hT c' _ _) hw
  refine Proof.imp_elim (Proof.imp_elim (Proof.imp_elim (Proof.ofSubset
    (fun _ h => absurd h List.not_mem_nil) (Proof.imp_intro (Proof.imp_intro (Proof.imp_intro
      (Proof.boxxK ⟨X, hx⟩ q))))) hH) ?_) ?_
  · exact Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
      (Proof.imp_intro (Proof.box_boxx ⟨X, hx⟩ A₄)))
      (Proof.and_elim_l (Proof.and_elim_r hK'))
  · exact Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
      (Proof.imp_intro (Proof.box_boxx ⟨X, hx⟩ A₁))) (Proof.and_elim_l hK')

/-- ⭐**The far end of the unit**: `Ψ` of the object, the ties, and the nested returning possibility
    along the part, whose value is the kept object from home, give `Ψ` of that value. -/
def Proof.liftW_inner (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (e : ℕ)
    (he : (Γ.diaIn x₂).RootFresh (.free e)) {a₀ : Ann F} (a : Term σ Γ.boxIn F a₀)
    (h₁ : Γ.boxIn.ref z₁ = some (.VTypeBox F)) (h₂ : Γ.boxIn.ref z₂ = some (.VTypeDia X))
    (hx : Γ.ref x₂ = some (.VTypeDia X)) {m₁ m₂ : VarSymb}
    (hm₁ : Γ.ref m₁ = some (.VTypeBox F)) (hm₂ : Γ.ref m₂ = some (.VTypeDia X))
    (φ : WFF σ (Γ.insert (.bnd 0) (wTy F X)) 1)
    (hΦ : Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots
      (Term.pair (Term.boxtm a) (Term.eta x₂ _ hx)) φ))
    (hK : Proof σ Γ Δ (WFF.holeAt Ctx.NoSlots.slots
      (wSlot a (wTerm h₁ h₂).2 (Term.eta x₂ _ hx)) (WFF.wTies F X hS hF)))
    (hN : Proof σ Γ Δ ((OutLeg.pos x₂ ⟨X, hx⟩ : OutLeg Γ).ret hS (wTerm hm₁ hm₂).2
      (WFF.cBodyW (V := Γ.diaIn x₂) hS hF (wKeep hF ((Ctx.le_boxIn_diaIn Γ x₂).ref h₁)
        ((Ctx.le_boxIn_diaIn Γ x₂).ref h₂)).2))) :
    Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots (wTerm hm₁ hm₂).2 φ) := by
  have hK' := Proof.conv (WFF.holeAt_wTies hS hF _ a h₁ h₂ hx) hK
  have hT₂ := Proof.and_elim_l (Proof.and_elim_r (Proof.and_elim_r hK'))
  have hT₃ := Proof.and_elim_r (Proof.and_elim_r (Proof.and_elim_r hK'))
  have L := Ctx.le_boxIn_diaIn Γ x₂
  have hsh := Ctx.shifts_boxIn_boxIn hF Γ
  have hΦ' : Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots
      (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (wTerm h₁ h₂).2) φ) :=
    Proof.conv (WFF.instantiate_congr_sig _ (congrArg (fun p =>
      (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) p.2⟩ : Σ e, Term σ Γ (wTy F X) e))
      (Term.collapse_shift_boxIn hT hF (wTerm h₁ h₂).2)) φ)
      (Proof.back_here hS hT _ _ φ hT₃ hΦ)
  have hy₁ := hsh z₁ _ h₁
  have hy₂ := hsh z₂ _ h₂
  have hy₁' := L.boxIn.ref hy₁
  have hy₂' := L.boxIn.ref hy₂
  have eY : (⟨_, Term.shift hsh (wTerm (σ := σ) h₁ h₂).2⟩ :
      Σ b, Term σ Γ.boxIn.boxIn (wTy F X) b) = ⟨_, (wTerm hy₁ hy₂).2⟩ :=
    sig_pair (Term.shift_eta hsh _ _ _) (Term.shift_eta hsh _ _ _)
  have eY' : (⟨_, Term.mono L.boxIn (Term.shift hsh (wTerm (σ := σ) h₁ h₂).2)⟩ :
      Σ b, Term σ (Γ.diaIn x₂).boxIn (wTy F X) b) = ⟨_, (wTerm hy₁' hy₂').2⟩ :=
    (congrArg (fun p => (⟨_, Term.mono L.boxIn p.2⟩ :
      Σ b, Term σ (Γ.diaIn x₂).boxIn (wTy F X) b)) eY).trans (Term.mono_wTerm L.boxIn hy₁ hy₂)
  have eK : (⟨_, Term.mono L.boxIn (wKeep (σ := σ) hF h₁ h₂).2⟩ :
      Σ b, Term σ (Γ.diaIn x₂).boxIn (wTy F X) b) = ⟨_, (wKeep hF (L.ref h₁) (L.ref h₂)).2⟩ :=
    Term.mono_wTerm L.boxIn (Ctx.ref_keep_of' hF h₁ rfl)
      (Ctx.ref_keep_of' hF h₂ VarType.keepable_dia)
  have eP : (⟨_, Term.mono L.boxIn (Term.pair (Term.shift hsh (wTerm (σ := σ) h₁ h₂).2)
      (wKeep (σ := σ) hF h₁ h₂).2)⟩ :
      Σ b, Term σ (Γ.diaIn x₂).boxIn (.VTypeProd (wTy F X) (wTy F X)) b) =
      ⟨_, Term.pair (wTerm hy₁' hy₂').2 (wKeep hF (L.ref h₁) (L.ref h₂)).2⟩ := sig_pair eY' eK
  have h₂' : Proof σ Γ Δ ((OutLeg.pos x₂ ⟨X, hx⟩ : OutLeg Γ).box (WFF.box (WFF.holeAt
      Ctx.NoSlots.slots (Term.pair (wTerm hy₁' hy₂').2 (wKeep hF (L.ref h₁) (L.ref h₂)).2)
      (WFF.backDK hS hF F X)))) := by
    refine Proof.conv (congrArg (fun χ => WFF.boxx x₂ ⟨X, hx⟩ (WFF.box χ))
      ((WFF.mono_holeAt L.boxIn _ Ctx.NoSlots.slots _ _).trans (WFF.holeAt_congr _ eP _)))
      (Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
        (Proof.imp_intro (Proof.box_boxx ⟨X, hx⟩ _))) hT₂)
  have hsw := Proof.ret_swapW hS hT hF (.pos x₂ ⟨X, hx⟩) e he _ hy₁' hy₂' _ hN h₂'
  have hne : Proof σ Γ Δ ((OutLeg.pos x₂ ⟨X, hx⟩ : OutLeg Γ).dia .top) :=
    Proof.leg_dia _ Proof.top_intro (Proof.ret_diaS hS _ _ _ hN)
  have hc := Proof.ret_counitC hS (.pos x₂ ⟨X, hx⟩) (wTerm hm₁ hm₂).2
    (Term.mono L.boxIn (Term.shift hsh (wTerm (σ := σ) h₁ h₂).2)) _ (WFF.backDK hS hF F X)
    (Proof.conv (OutLeg.retS_congr hS _ (.box (wTy F X)) rfl
      (WFF.cBodyW_congr hS hF eY'.symm)) hsw)
    (Proof.back_keep hS hT hF (.pos x₂ ⟨X, hx⟩) (wTerm h₁ h₂).2 hne)
  exact Proof.back_wKeep_read hS hT hF hm₁ hm₂ _ φ (Proof.conv ((WFF.holeRead_eq_holeAt _ _).trans
    (WFF.holeAt_backDK hS hF _ hm₁ hm₂ _)) hc) hΦ'

end Far

/-! ## The two conclusions -/

section Concl

variable {F X : VarType}

/-- The tied body opened at a fresh root. -/
theorem WFF.openFree_tiedW {V : Ctx} [V.NoSlots] (hS : ModalSys.BStrong = true)
    (hF : ModalSys.Four = true) (Ψ : WFF σ (V.insert (.bnd 0) (wTy F X)) 1) (u : ℕ)
    (hu : V.RootFresh (.free u)) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.tiedW hS hF Ψ) =
      WFF.and (WFF.instantiate Ctx.NoSlots.slots
          (Term.pair
            (Term.boxtm (Term.eta (.step (VarSymb.step (.root (.free u)) .fst).inner .fst) F
              (Ctx.ref_fst_of (Ctx.ref_inner (Ctx.ref_fst_of
                (Ctx.ref_insert_root V (.free u) (wSlotTy F X)))))))
            (Term.eta (.step (.root (.free u)) .snd) (.VTypeDia X)
              (Ctx.ref_snd_of (Ctx.ref_insert_root V (.free u) (wSlotTy F X)))))
          (WFF.mono ((Ctx.le_insert hu.root (wSlotTy F X)).insert (.bnd 0) _) Ψ))
        (WFF.holeAt Ctx.NoSlots.slots
          (wSlot (Term.eta (.step (VarSymb.step (.root (.free u)) .fst).inner .fst) F
              (Ctx.ref_fst_of (Ctx.ref_inner (Ctx.ref_fst_of
                (Ctx.ref_insert_root V (.free u) (wSlotTy F X))))))
            (wTerm (Ctx.ref_fst_of (Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_fst_of
                (Ctx.ref_insert_root V (.free u) (wSlotTy F X))))))
              (Ctx.ref_snd_of (Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_fst_of
                (Ctx.ref_insert_root V (.free u) (wSlotTy F X))))))).2
            (Term.eta (.step (.root (.free u)) .snd) (.VTypeDia X)
              (Ctx.ref_snd_of (Ctx.ref_insert_root V (.free u) (wSlotTy F X)))))
          (WFF.wTies F X hS hF)) := by
  rw [← WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots,
    WFF.mono_tiedW (Ctx.le_insert hu.root (wSlotTy F X)) hS hF Ψ]
  exact WFF.instantiate_tiedW hS hF _ _ _ _

variable {Γ : Ctx} [Γ.NoSlots] {c₁ c₂ : VarSymb}

/-- ⭐**The first conclusion**: the necessary part comes back, and the possible part is realised
    here with the content. -/
def Proof.liftW_back (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {a₁ : Ann F} {a₂ : Ann X}
    (t₁ : Term σ Γ F a₁) (h₁ : Γ.ref c₁ = some (.VTypeBox F))
    (h₂ : Γ.ref c₂ = some (.VTypeDia X)) (t₂ : Term σ Γ X a₂)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (wTy F X)) 1) (u e : ℕ)
    (hu : O.view.RootFresh (.free u))
    (he : ((O.view.insert (.free u) (wSlotTy F X)).diaIn
      (.step (.root (.free u)) .snd)).RootFresh (.free e))
    (H : Proof σ Γ Δ (O.retS hS (.wit (.box (wPackTy F X)) X)
      (Term.pair (Term.pair t₁ (wTerm h₁ h₂).2) t₂) (WFF.tiedW hS hF Ψ))) :
    Proof σ Γ Δ (WFF.and (WFF.holeAt Ctx.NoSlots.slots (Term.pair t₁ (wTerm h₁ h₂).2)
      (WFF.backFst F X hS hF)) (WFF.here hT (Term.eta c₂ _ h₂) t₂)) := by
  refine Proof.conv ((WFF.holeRead_eq_holeAt _ _).trans
    (WFF.holeAt_wCounit hS hT hF _ t₁ h₁ h₂ t₂))
    (Proof.counitD_leg hS O _ _ (WFF.wCounit hS hT hF F X) u e hu he H ?_)
  have h₀ := Ctx.ref_insert_root O.view (.free u) (wSlotTy F X)
  have hz := Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_fst_of h₀))
  have hb := Proof.wCounit_boxx (Δ := [WFF.openFree u hu Ctx.NoSlots.slots (WFF.tiedW hS hF Ψ)])
    hS hT hF (Term.eta (.step (VarSymb.step (.root (.free u)) .fst).inner .fst) F
      (Ctx.ref_fst_of (Ctx.ref_inner (Ctx.ref_fst_of h₀))))
    (Ctx.ref_fst_of hz) (Ctx.ref_snd_of hz) (Ctx.ref_snd_of h₀)
    (Proof.and_elim_r (Proof.conv (WFF.openFree_tiedW hS hF Ψ u hu)
      (Proof.lookup List.mem_cons_self)))
  rw [Term.mono_eta] at hb
  exact hb

/-- ⭐**The second conclusion**: the kept object has `Ψ`, possibly. -/
def Proof.liftW_dia (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {a₁ : Ann F} {a₂ : Ann X}
    (t₁ : Term σ Γ F a₁) (h₁ : Γ.ref c₁ = some (.VTypeBox F))
    (h₂ : Γ.ref c₂ = some (.VTypeDia X)) (t₂ : Term σ Γ X a₂)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (wTy F X)) 1) (u e : ℕ)
    (hu : O.view.RootFresh (.free u))
    (he : ((O.view.insert (.free u) (wSlotTy F X)).diaIn
      (.step (.root (.free u)) .snd)).RootFresh (.free e))
    (H : Proof σ Γ Δ (O.retS hS (.wit (.box (wPackTy F X)) X)
      (Term.pair (Term.pair t₁ (wTerm h₁ h₂).2) t₂) (WFF.tiedW hS hF Ψ))) :
    Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.mono O.le_view (wKeep hF h₁ h₂).2) Ψ)) := by
  have k₁ := Ctx.ref_keep_of' hF h₁ rfl
  have k₂ := Ctx.ref_keep_of' hF h₂ VarType.keepable_dia
  have q : Proof σ Γ Δ (WFF.holeRead (Term.pair (Term.pair (Term.pair t₁ (wTerm h₁ h₂).2) t₂)
      (Term.boxtm (wKeep hF h₁ h₂).2)) (WFF.wTieUnit F X hS hF)) :=
    Proof.conv ((WFF.holeAt_wTieUnit hS hF _ t₁ h₁ h₂ t₂ _).symm.trans
      (WFF.holeRead_eq_holeAt _ _).symm)
      (Proof.nec (Proof.conv (WFF.holeAt_backDK hS hF _ k₁ k₂ _).symm
        (Proof.back_wKeep hS hT hF k₁ k₂)))
  refine Proof.leg_dia O ?_ (Proof.ret_diaS hS O _ _ (Proof.ret_unitD hS O _ _ _ _ H q))
  have hV := Ctx.le_insert hu.root (wSlotTy F X)
  have h₀ := Ctx.ref_insert_root O.view (.free u) (wSlotTy F X)
  have hz := Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_fst_of h₀))
  have hx := Ctx.ref_snd_of h₀
  let U := WFF.unitBodyD (Γ := Γ) hS (wKeep (σ := σ) hF h₁ h₂).2 (WFF.wTieUnit F X hS hF)
  refine Proof.ex_elim u _ hu
    (φ := WFF.and (WFF.openFree u hu Ctx.NoSlots.slots (WFF.tiedW hS hF Ψ))
      (WFF.openFree u hu Ctx.NoSlots.slots (O.lift U)))
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree u hu Ctx.NoSlots.slots
      (WFF.and (WFF.tiedW hS hF Ψ) (O.lift U)))).symm (Proof.lookup List.mem_cons_self)) ?_
  have hm₁ := (O.le_view.trans hV).ref k₁
  have hm₂ := (O.le_view.trans hV).ref k₂
  have hmono : (⟨_, Term.mono (O.le_view.trans hV) (wKeep (σ := σ) hF h₁ h₂).2⟩ :
      Σ b, Term σ (O.view.insert (.free u) (wSlotTy F X)) (wTy F X) b) = ⟨_, (wTerm hm₁ hm₂).2⟩ :=
    Term.mono_wTerm _ k₁ k₂
  have L := Ctx.le_boxIn_diaIn (O.view.insert (.free u) (wSlotTy F X))
    (.step (.root (.free u)) .snd)
  have eU : WFF.openFree u hu Ctx.NoSlots.slots (O.lift U) =
      (OutLeg.pos _ ⟨X, hx⟩).ret hS (wTerm hm₁ hm₂).2
        (WFF.cBodyW hS hF
          (wKeep hF (L.ref (Ctx.ref_fst_of hz)) (L.ref (Ctx.ref_snd_of hz))).2) := by
    rw [OutLeg.lift_eq_mono _ O, WFF.openFree_mono_unitBodyD O.le_view]
    refine WFF.retxS_congr hS _ _ _ hmono ?_
    refine (WFF.holeAt_wTieUnit hS hF _ _ _ _ _ _).trans (congrArg WFF.box
      (WFF.holeAt_congr _ (sig_pair rfl (Term.mono_wTerm _ _ _).symm) _))
  refine Proof.conv ?_ (Proof.liftW_inner hS hT hF e he
    (Term.eta (.step (VarSymb.step (.root (.free u)) .fst).inner .fst) F
      (Ctx.ref_fst_of (Ctx.ref_inner (Ctx.ref_fst_of h₀))))
    (Ctx.ref_fst_of hz) (Ctx.ref_snd_of hz)
    hx hm₁ hm₂ (WFF.mono (hV.insert (.bnd 0) _) Ψ) ?_ ?_ ?_)
  · refine Eq.symm ((WFF.mono_instantiate hV _ Ctx.NoSlots.slots _ Ψ).trans ?_)
    rw [Term.mono_mono]
    exact WFF.instantiate_congr_sig _ hmono _
  · exact Proof.and_elim_l (Proof.conv (WFF.openFree_tiedW hS hF Ψ u hu)
      (Proof.and_elim_l (Proof.lookup List.mem_cons_self)))
  · exact Proof.and_elim_r (Proof.conv (WFF.openFree_tiedW hS hF Ψ u hu)
      (Proof.and_elim_l (Proof.lookup List.mem_cons_self)))
  · exact Proof.conv eU (Proof.and_elim_r (Proof.lookup List.mem_cons_self))

end Concl

/-! ## The companion -/

section Companion

variable {W : Ctx} [W.NoSlots] {F B X : VarType}

/-- `pairUpS` at the witnessed shape, under a weakening of the view. -/
theorem WFF.mono_pairUpW {V V' : Ctx} [V.NoSlots] [V'.NoSlots] (h : V.Le V')
    (Φ : WFF σ (V.insert (.bnd 0) (RShape.wit (.box (.VTypeProd F B)) X).ty) 1) :
    WFF.mono ((h.insert (.bnd 0) _).insert (.bnd 1) _)
        (WFF.pairUpS (.wit (.box F) X) B (packW (σ := σ) F B X).2 Φ) =
      WFF.pairUpS (.wit (.box F) X) B (packW (σ := σ) F B X).2
        (WFF.mono (h.insert (.bnd 0) _) Φ) := by
  unfold WFF.pairUpS
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = (RShape.wit (.box (.VTypeProd F B)) X).ty := by
      simpa [Ctx.insert] using hv.symm
    change SubE.Sim _ (SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))))
      (Subst.set _ _ _ (.root (.bnd 0)))
    rw [Subst.set_root, Subst.set_root]
    change SubE.Sim _ (.tm (Term.mono _ _)) _
    refine SubE.sim_tm_sigma ((Term.mono_holeAt_sig _ _ _).trans (Term.holeAt_congr_sig ?_ _))
    exact sig_pair (sig_pair (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)))
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))
  · change SubE.Sim T (SubE.mono _ (Subst.set _ _ _ v)) (Subst.set _ _ _ v)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐**`∃`-introduction at a companion of the witnessed shape.** -/
def Proof.ex_pairUpW {Δ : List (WFF σ W 0)} {a₀ : Ann F} {c₀ : Ann B} {x₀ : Ann (.VTypeDia X)}
    (a : Term σ W.boxIn F a₀) (c : Term σ W.boxIn B c₀) (e : Term σ W (.VTypeDia X) x₀)
    (Y : WFF σ (W.insert (.bnd 0) (RShape.wit (.box (.VTypeProd F B)) X).ty) 1)
    (p : Proof σ W Δ (WFF.instantiate Ctx.NoSlots.slots
      (Term.pair (Term.boxtm (Term.pair a c)) e) Y)) :
    Proof σ W Δ (WFF.instantiate Ctx.NoSlots.slots (Term.pair (Term.boxtm a) e)
      (WFF.ex (.VTypeBox B) (WFF.pairUpS (.wit (.box F) X) B (packW (σ := σ) F B X).2 Y))) := by
  refine Proof.ex_intro _ (Term.boxtm c) (Proof.conv (Eq.symm ?_) p)
  unfold WFF.instantiate WFF.substRoot WFF.pairUpS
  have hfr : W (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := W)).root
  have hl := Ctx.le_insert hfr (.VTypeBox B)
  have hfresh : W.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := W)).rootFresh (le_refl 0)
  have hne : ∀ {v : VarSymb} {U : VarType}, v.lastProj = false → W v = some U →
      v.rt ≠ .bnd 0 ∧ v.rt ≠ .bnd 1 := fun hlp hv =>
    ⟨Ctx.ref_rt_ne hfresh ((Ctx.ref_nonproj W hlp).trans hv),
      Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := W)).rootFresh (Nat.zero_le 1))
        ((Ctx.ref_nonproj W hlp).trans hv)⟩
  have hw : ∀ {v : VarSymb} {U : VarType}, v.lastProj = false →
      (W.insert (.bnd 0) (RShape.wit (.box (.VTypeProd F B)) X).ty) v = some U →
      v ≠ .root (.bnd 0) → W v = some U := fun _ hv hvr => by simpa [Ctx.insert, hvr] using hv
  let s₁₂ : Term σ (W.insert (.bnd 0) (.VTypeBox B))
      (RShape.wit (.box (.VTypeProd F B)) X).ty _ :=
    Term.pair (Term.boxtm (Term.pair (Term.mono hl.boxIn a)
      (Term.eta (VarSymb.root (.bnd 0)).inner B
        (Ctx.ref_inner (Ctx.ref_insert_root W (.bnd 0) _))))) (Term.mono hl e)
  have ok₁₂ := Subst.ok_single (σ := σ) (Γ := W) (r := .bnd 0)
    (T := (RShape.wit (.box (.VTypeProd F B)) X).ty) (e := .tm s₁₂) hl rfl
  have coh₁₂ := Subst.coh_single (σ := σ) (Γ := W) (r := .bnd 0)
    (T := (RShape.wit (.box (.VTypeProd F B)) X).ty) (e := .tm s₁₂) hfresh hl rfl
  refine Eq.trans (congrArg (WFF.subst _ _ _ _ _ _)
    (WFF.subst_comp _ _ (Subst.single (.bnd 0) (.tm s₁₂)) _ _ _ _ ok₁₂ coh₁₂ _ _ _ ?_ Y)) ?_
  · refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = (RShape.wit (.box (.VTypeProd F B)) X).ty := by
        simpa [Ctx.insert] using hv.symm
      rw [Subst.comp_apply, Subst.set_root, Subst.single_root]
      dsimp only [SubE.comp]
      refine SubE.sim_tm_sigma (Eq.symm ((Term.subst_holeAt_sig _ _ _ _ _).trans
        ((Term.holeAt_congr_sig (sig_pair (sig_pair (Term.subst_eta_tm _ _ _ _ _ _
          (Term.boxtm (Term.mono hl.boxIn a)) ?_)
          (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
            (Subst.under_at_slot _ (0 + 1) 0 _ hfr)))
          (Term.subst_eta_tm _ _ _ _ _ _ (Term.mono hl e) ?_)) _).trans
          (ShapeMap.liftObj_pack_wit _ _ _))))
      · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_proj _ _ rfl,
          Subst.at_single_root]
        rfl
      · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_proj _ _ rfl,
          Subst.at_single_root]
        rfl
    · obtain ⟨h0, h1⟩ := hne hlp (hw hlp hv hvr)
      rw [Subst.comp_apply, Subst.set_ne _ _ hvr,
        (Subst.at_nonproj (Subst.single (σ := σ) (.bnd 0) (.tm s₁₂)) hlp).symm,
        Subst.single_at_ne h0]
      change SubE.Sim U _ (Subst.at _ v)
      rw [Subst.at_under_ne _ _ _ h1, Subst.single_at_ne h0]
      exact .refl _
  · refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Y
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = (RShape.wit (.box (.VTypeProd F B)) X).ty := by
        simpa [Ctx.insert] using hv.symm
      rw [Subst.comp_apply, Subst.single_root, Subst.single_root]
      dsimp only [SubE.comp]
      refine SubE.sim_tm_sigma (sig_pair (sig_boxtm (sig_pair ?_ (Term.subst_eta_tm _ _ _ _ _ _ c
        (Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _))))) ?_).symm
      · exact (Term.subst_single_box_mono (Ctx.Le.refl W) hl (.tm (Term.boxtm c))
          (Subst.ok_single (Ctx.Le.refl _) rfl) (Subst.coh_single hfresh (Ctx.Le.refl _) rfl)
          hfresh a).trans (congrArg (Sigma.mk _) (Term.mono_refl _ a))
      · exact (Term.subst_single_mono (Ctx.Le.refl W) hl (.tm (Term.boxtm c)) _ _ hfresh e).trans
          (congrArg (Sigma.mk _) (Term.mono_refl _ e))
    · obtain ⟨h0, _⟩ := hne hlp (hw hlp hv hvr)
      rw [Subst.comp_apply,
        (Subst.at_nonproj (Subst.single (σ := σ) (.bnd 0) (.tm s₁₂)) hlp).symm,
        (Subst.at_nonproj (Subst.single (σ := σ) (.bnd 0)
          (.tm (Term.pair (Term.boxtm (Term.pair a c)) e))) hlp).symm,
        Subst.single_at_ne h0, Subst.single_at_ne h0]
      change SubE.Sim U _ (Subst.at _ v)
      rw [Subst.single_at_ne h0]
      exact .refl _

end Companion

/-! ## Lifting -/

section Main

variable {Γ : Ctx} [Γ.NoSlots] {F X : VarType}

/-- ⭐**The ties come for free**: the object has its companion, its kept form, tied. -/
def Proof.retW_tied (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ)
    {a : Ann (RShape.wit (.box F) X).flat} (y : Term σ Γ (RShape.wit (.box F) X).flat a)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (wTy F X)) 1) (r : ℕ) (hr : O.view.RootFresh (.free r))
    (H : Proof σ Γ Δ (O.retS hS (.wit (.box F) X) y Ψ)) :
    Proof σ Γ Δ (O.retS hS (.wit (.box F) X) y (WFF.ex (.VTypeBox (wTy F X))
      (WFF.pairUpS (.wit (.box F) X) (wTy F X) (packW (σ := σ) F (wTy F X) X).2
        (WFF.tiedW hS hF Ψ)))) := by
  refine Proof.ret_monoS (S := .wit (.box F) X) hS O y Ψ _ H (Proof.leg_all O _ _ r hr ?_)
  have hV := Ctx.le_insert hr.root (wTy F X)
  have h₀ := Ctx.ref_insert_root O.view (.free r) (wTy F X)
  have h₁ := Ctx.ref_fst_of h₀
  have h₂ := Ctx.ref_snd_of h₀
  rw [← WFF.instantiate_eta_openFree r hr Ctx.NoSlots.slots Ctx.NoSlots.slots
    (WFF.ex (.VTypeBox (wTy F X)) _)]
  refine Proof.conv ?_ (Proof.ex_pairUpW
    (Term.eta (σ := σ) (VarSymb.step (.root (.free r)) .fst).inner F (Ctx.ref_inner h₁))
    (wKeep hF h₁ h₂).2 (Term.eta _ _ h₂)
    (WFF.tiedW hS hF (WFF.mono (hV.insert (.bnd 0) _) Ψ)) ?_)
  · exact congrArg (fun φ => WFF.instantiate _ _ (WFF.ex _ φ))
      (((congrArg (WFF.pairUpS _ _ _) (WFF.mono_tiedW hV hS hF Ψ)).symm.trans
        (WFF.mono_pairUpW hV _).symm))
  · refine Proof.conv (WFF.instantiate_tiedW hS hF _ _ _ _).symm
      (Proof.and_intro ?_ (Proof.wTies_intro hS hT hF h₁ h₂))
    exact Proof.conv (WFF.instantiate_eta_openFree r hr Ctx.NoSlots.slots
      Ctx.NoSlots.slots Ψ).symm (Proof.lookup List.mem_cons_self)

/-- What a lifted witnessed returning possibility says of its fresh `c : G`: `c.fst` comes back as
    `t₁`, `c.snd` is realised here with content `t₂`, and possibly `Ψ` of `c` kept. -/
def WFF.liftedW (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (O : OutLeg Γ) {a₁ : Ann F} {a₂ : Ann X} (t₁ : Term σ Γ F a₁)
    (t₂ : Term σ Γ X a₂) (Ψ : WFF σ (O.view.insert (.bnd 0) (wTy F X)) 1) (c : ℕ)
    (hc : Γ.RootFresh (.free c)) : WFF σ (Γ.insert (.free c) (wTy F X)) 0 :=
  have h₀ := Ctx.ref_insert_root Γ (.free c) (wTy F X)
  WFF.and
    (WFF.and
      (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair (Term.weaken hc.root _ t₁) (wTerm (Ctx.ref_fst_of h₀) (Ctx.ref_snd_of h₀)).2)
        (WFF.backFst F X hS hF))
      (WFF.here hT (Term.eta (.step (.root (.free c)) .snd) _ (Ctx.ref_snd_of h₀))
        (Term.weaken hc.root _ t₂)))
    ((O.mono (Ctx.le_insert hc.root _)).dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.mono (O.mono (Ctx.le_insert hc.root _)).le_view
        (wKeep hF (Ctx.ref_fst_of h₀) (Ctx.ref_snd_of h₀)).2)
      (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root _)).insert (.bnd 0) _) Ψ)))

/-- ⭐⭐**Lifting a witnessed returning possibility** (T + 4, strong B), along either leg, as an
    `∃`-elimination at a fresh `c : □F × ◇X`. -/
def Proof.retW_lift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (O : OutLeg Γ)
    {a₁ : Ann F} {a₂ : Ann X} (t₁ : Term σ Γ F a₁) (t₂ : Term σ Γ X a₂)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (wTy F X)) 1) (c : ℕ) (hc : Γ.RootFresh (.free c))
    (hc₁ : Γ.RootFresh (.free (c + 1))) (hc₂ : Γ.RootFresh (.free (c + 2)))
    (p : Proof σ Γ Δ (O.retS hS (.wit (.box F) X) (Term.pair t₁ t₂) Ψ))
    (q : Proof σ (Γ.insert (.free c) (wTy F X))
      (WFF.liftedW hS hT hF O t₁ t₂ Ψ c hc :: Δ.map (WFF.weaken hc.root _))
      (φ.weaken hc.root _)) :
    Proof σ Γ Δ φ := by
  refine Proof.ret_extS hS O (S := .wit (.box F) X) (Term.pair t₁ t₂)
    (WFF.pairUpS (.wit (.box F) X) (wTy F X) (packW (σ := σ) F (wTy F X) X).2
      (WFF.tiedW hS hF Ψ)) c hc
    (Proof.retW_tied hS hT hF O _ Ψ (c + 1) (OutLeg.rootFresh hc₁ O) p) ?_
  have hle := Ctx.le_insert hc.root (wTy F X)
  have hV' := O.le_view_mono hle
  have hb := WFF.bodySplit_mono_pairUpS (Ctx.Le.refl O.view) (.wit (.box F) X) (wTy F X)
    (packW (σ := σ) F (wTy F X) X).2 (WFF.tiedW hS hF Ψ)
  rw [WFF.mono_refl, WFF.mono_refl] at hb
  rw [hb, WFF.mono_bodyRepl hV', Term.mono_mono, WFF.mono_tiedW hV']
  have h₀ := Ctx.ref_insert_root Γ (.free c) (wTy F X)
  have hne₁ : Root.free c ≠ .free (c + 1) := fun h => by
    have := Root.free.inj h
    omega
  have hne₂ : Root.free c ≠ .free (c + 2) := fun h => by
    have := Root.free.inj h
    omega
  have hne₃ : Root.free (c + 1) ≠ .free (c + 2) := fun h => by
    have := Root.free.inj h
    omega
  have hu := OutLeg.rootFresh (hc₁.insert_ne hne₁ (wTy F X)) (O.mono hle)
  have he : (((O.mono hle).view.insert (.free (c + 1)) (wSlotTy F X)).diaIn
      (.step (.root (.free (c + 1))) .snd)).RootFresh (.free (c + 2)) :=
    ((OutLeg.rootFresh (hc₂.insert_ne hne₂ (wTy F X)) (O.mono hle)).insert_ne hne₃ _).diaIn _
  refine Proof.imp_elim (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx)
    (Proof.imp_intro q)) ?_
  suffices hR : Proof σ _ _ ((O.mono hle).retS hS (.wit (.box (wPackTy F X)) X)
      (Term.pair (Term.pair (Term.weaken hc.root _ t₁)
        (wTerm (Ctx.ref_fst_of h₀) (Ctx.ref_snd_of h₀)).2) (Term.weaken hc.root _ t₂))
      (WFF.tiedW hS hF (WFF.mono (hV'.insert (.bnd 0) _) Ψ))) from Proof.and_intro
    (Proof.liftW_back hS hT hF (O.mono hle) (Term.weaken hc.root _ t₁) (Ctx.ref_fst_of h₀)
      (Ctx.ref_snd_of h₀) (Term.weaken hc.root _ t₂) _ (c + 1) (c + 2) hu he hR)
    (Proof.liftW_dia hS hT hF (O.mono hle) (Term.weaken hc.root _ t₁) (Ctx.ref_fst_of h₀)
      (Ctx.ref_snd_of h₀) (Term.weaken hc.root _ t₂) _ (c + 1) (c + 2) hu he hR)
  refine Proof.conv (OutLeg.retS_congr hS (O.mono hle) (.wit (.box (wPackTy F X)) X) ?_ rfl)
    (Proof.ret_map hS (O.mono hle) (S := .wit (.prod (.box F) (.box (wTy F X))) X)
      (.pack F (wTy F X)) _ (WFF.tiedW hS hF (WFF.mono (hV'.insert (.bnd 0) _) Ψ))
      (Proof.lookup List.mem_cons_self))
  rw [Term.holeRead_eq_holeAt]
  exact (Term.holeAt_congr_sig (RShape.extTm_wit _ _ _) _).trans (ShapeMap.liftVal_pack_wit _ _)

end Main

/-! ## Every witnessed shape -/

section Packed

variable {V : Ctx} [V.NoSlots] {N : NShape} {X : VarType}

/-- The object read back off a packed slot. -/
abbrev unpackW₀ (N : NShape) (X : VarType) :
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) (wTy N.flat X)) (RShape.wit N X).ty b :=
  ⟨_, Term.pair
    (Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox N.flat)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) (NShape.unpack₀ N).2)
    (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeDia X)
      (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))⟩

/-- The object and its packing, off a packed slot. -/
abbrev tieW₀ (N : NShape) (X : VarType) :
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) (wTy N.flat X)) (packHoleTy N) b :=
  ⟨_, Term.pair
    (Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox N.flat)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) (NShape.unpack₀ N).2)
    (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox N.flat)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))⟩

/-- ⭐**The packed body at a witnessed shape.** -/
def WFF.packedBodyW (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (Φ : WFF σ (V.insert (.bnd 0) (RShape.wit N X).ty) 1) :
    WFF σ (V.insert (.bnd 0) (wTy N.flat X)) 1 :=
  WFF.and (WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _) (unpackW₀ N X).2) Φ)
    (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _)
      (Term.mono ((Ctx.empty_le V).insert (.bnd 0) _) (tieW₀ N X).2) (WFF.packTies hS hF N))

theorem WFF.mono_packedBodyW {V' : Ctx} [V'.NoSlots] (h : V.Le V') (hS : ModalSys.BStrong = true)
    (hF : ModalSys.Four = true) (Φ : WFF σ (V.insert (.bnd 0) (RShape.wit N X).ty) 1) :
    WFF.mono (h.insert (.bnd 0) _) (WFF.packedBodyW hS hF Φ) =
      WFF.packedBodyW hS hF (WFF.mono (h.insert (.bnd 0) _) Φ) := by
  refine congrArg₂ WFF.and ?_ ?_
  · rw [WFF.mono_bodyRepl h, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := V')).insert _), Term.mono_mono]

/-- ⭐The packed body at an object's own packing. -/
theorem WFF.instantiate_packedBodyW (hS : ModalSys.BStrong = true) (hF : ModalSys.Four = true)
    (Φ : WFF σ (V.insert (.bnd 0) (RShape.wit N X).ty) 1) (u x : VarSymb)
    (hu : V.ref u = some N.ty) (hx : V.ref x = some (.VTypeDia X)) :
    WFF.instantiate Ctx.NoSlots.slots
        (Term.pair (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2) (Term.eta x _ hx))
        (WFF.packedBodyW hS hF Φ) =
      WFF.and (WFF.instantiate Ctx.NoSlots.slots
          (Term.pair (Term.eta u N.ty hu) (Term.eta x _ hx)) Φ)
        (WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.eta u N.ty hu)
          (Term.boxtm (NShape.contents (Ctx.Le.refl _) N u hu).2)) (WFF.packTies hS hF N)) := by
  let P := Term.boxtm (σ := σ) (NShape.contents (Ctx.Le.refl _) N u hu).2
  let s := Term.pair P (Term.eta (σ := σ) x (.VTypeDia X) hx)
  have hat := Subst.at_single_root (σ := σ) (Δ := V) (.bnd 0) (.tm s)
  have hp : (Subst.single (σ := σ) (Δ := V) (.bnd 0) (.tm s)).at
      (.step (.root (.bnd 0)) .fst) = .tm P := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have hq : (Subst.single (σ := σ) (Δ := V) (.bnd 0) (.tm s)).at
      (.step (.root (.bnd 0)) .snd) = .tm (Term.eta x _ hx) := by
    rw [Subst.at_proj _ _ rfl, hat]
    rfl
  have hhole : (⟨_, Term.holeAt P (NShape.unpack₀ (σ := σ) N).2⟩ : Σ b, Term σ V N.ty b) =
      ⟨_, Term.eta u N.ty hu⟩ :=
    NShape.subst_unpack _ _ _ N _ _ u hu
      (Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _))
  have hU : (⟨_, Term.subst (Subst.singleIdx (.bnd 0) (.tm s)) (Subst.single (.bnd 0) (.tm s))
      (Subst.ok_single (Ctx.empty_le V) rfl)
      (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le V) rfl)
      (Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox N.flat)
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) (NShape.unpack₀ N).2)⟩ :
      Σ b, Term σ V N.ty b) = ⟨_, Term.eta u N.ty hu⟩ :=
    (Term.subst_holeAt_sig _ _ _ _ _).trans ((Term.holeAt_congr_sig
      (Term.subst_eta_tm _ _ _ _ _ _ P hp) _).trans hhole)
  refine congrArg₂ WFF.and ((WFF.instantiate_bodyRepl _ _ _).trans
    (WFF.instantiate_congr_sig _ ?_ Φ)) ?_
  · rw [Term.subst_mono]
    exact sig_pair hU (Term.subst_eta_tm _ _ _ _ _ _ _ hq)
  · change WFF.subst _ _ _ _ _ _ (WFF.holeAt _ _ _) = _
    rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ ?_ _
    rw [Term.subst_mono]
    exact sig_pair hU (Term.subst_eta_tm _ _ _ _ _ _ P hp)

end Packed

section MainN

variable {Γ : Ctx} [Γ.NoSlots] {X : VarType}

/-- ⭐**Packing a witnessed returning possibility.** -/
def Proof.retWN_packed (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) (N : NShape)
    {a₁ : Ann N.flat} {a₂ : Ann X} (t₁ : Term σ Γ N.flat a₁) (t₂ : Term σ Γ X a₂)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N X).ty) 1) (u : ℕ)
    (hu : O.view.RootFresh (.free u))
    (H : Proof σ Γ Δ (O.retS hS (.wit N X) (Term.pair t₁ t₂) Φ)) :
    Proof σ Γ Δ (O.retS hS (.wit (.box N.flat) X) (Term.pair t₁ t₂)
      (WFF.packedBodyW hS hF Φ)) := by
  have h₁ : Proof σ Γ Δ (O.retS hS (.wit N X) (Term.pair t₁ t₂) (WFF.bodyRepl
      (Term.mono ((Ctx.empty_le O.view).insert (.bnd 0) _)
        (ShapeMap.liftObj (.wit N X) (NShape.packMap (σ := σ) N)).2)
      (WFF.packedBodyW hS hF Φ))) := by
    refine Proof.ret_monoS (S := .wit N X) hS O _ Φ _ H (Proof.leg_all O _ _ u hu ?_)
    have hV := Ctx.le_insert hu.root (RShape.wit N X).ty
    have h₀ := Ctx.ref_insert_root O.view (.free u) (RShape.wit N X).ty
    have hf := Ctx.ref_fst_of h₀
    have hs := Ctx.ref_snd_of h₀
    have hP := NShape.holeAt_packObj (σ := σ) N _ hf
    have hat := Subst.at_single_root (σ := σ) (Δ := O.view.insert (.free u) (RShape.wit N X).ty)
      (.bnd 0) (.tm (Term.eta (.root (.free u)) (RShape.wit N X).ty h₀))
    have hO : (⟨_, Term.subst (Subst.singleIdx (.bnd 0)
        (.tm (Term.eta (.root (.free u)) (RShape.wit N X).ty h₀)))
        (Subst.single (.bnd 0) (.tm (Term.eta (.root (.free u)) (RShape.wit N X).ty h₀)))
        (Subst.ok_single (Ctx.empty_le _) rfl)
        (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le _) rfl)
        (ShapeMap.liftObj (.wit N X) (NShape.packMap (σ := σ) N)).2⟩ :
        Σ b, Term σ _ (wTy N.flat X) b) =
        ⟨_, Term.pair (Term.boxtm (NShape.contents (Ctx.Le.refl _) N _ hf).2)
          (Term.eta _ _ hs)⟩ := by
      refine sig_pair ((Term.subst_holeAt_sig _ _ _ _ _).trans ((Term.holeAt_congr_sig
        (Term.subst_eta_tm _ _ _ _ _ _ (Term.eta _ N.ty hf) ?_) _).trans hP))
        (Term.subst_eta_tm _ _ _ _ _ _ _ ?_)
      · rw [Subst.at_proj _ _ rfl, hat]
        rfl
      · rw [Subst.at_proj _ _ rfl, hat]
        rfl
    rw [← WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.bodyRepl _ _), WFF.mono_bodyRepl hV, WFF.instantiate_bodyRepl, Term.mono_mono,
      Term.subst_mono]
    refine Proof.conv (WFF.instantiate_congr_sig _ hO _).symm ?_
    rw [WFF.mono_packedBodyW hV, WFF.instantiate_packedBodyW]
    exact Proof.and_intro (Proof.conv (WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots
      Ctx.NoSlots.slots Φ).symm (Proof.lookup List.mem_cons_self))
      (Proof.packTies_intro hS hT hF N _ hf)
  refine Proof.conv (OutLeg.retS_congr hS O (.wit (.box N.flat) X) ?_ rfl)
    (Proof.ret_map hS O (S := .wit N X) (T := .box N.flat) (NShape.packMap N) _ _ h₁)
  rw [Term.holeRead_eq_holeAt]
  refine sig_pair ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
    (Term.holeAt_pair_fst _ _) _).trans (NShape.holeAt_packVal N t₁))) (Term.holeAt_pair_snd _ _)

/-- ⭐⭐**Lifting at every witnessed shape** (T + 4, strong B), along either leg: `Proof.retW_lift`
    at the packed object.  With `Proof.retN_lift`, every returnable shape. -/
def Proof.retWN_lift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} (O : OutLeg Γ) (N : NShape)
    {a₁ : Ann N.flat} {a₂ : Ann X} (t₁ : Term σ Γ N.flat a₁) (t₂ : Term σ Γ X a₂)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N X).ty) 1) (c : ℕ)
    (hc : Γ.RootFresh (.free c)) (hc₁ : Γ.RootFresh (.free (c + 1)))
    (hc₂ : Γ.RootFresh (.free (c + 2)))
    (p : Proof σ Γ Δ (O.retS hS (.wit N X) (Term.pair t₁ t₂) Φ))
    (q : Proof σ (Γ.insert (.free c) (wTy N.flat X))
      (WFF.liftedW hS hT hF O t₁ t₂ (WFF.packedBodyW hS hF Φ) c hc ::
        Δ.map (WFF.weaken hc.root _)) (φ.weaken hc.root _)) :
    Proof σ Γ Δ φ :=
  Proof.retW_lift hS hT hF O t₁ t₂ _ c hc hc₁ hc₂
    (Proof.retWN_packed hS hT hF O N t₁ t₂ Φ (c + 1) (OutLeg.rootFresh hc₁ O) p) q

end MainN

/-! ## What `Here` says of the kept object -/

namespace Model

universe u v

variable {σ : Signature} {M : Model.{u, v} σ}

/-- ⭐**The way home lies in the kept object's extent**: what is realised here is, kept along an
    arrow out, realised along the way home with the same content, since out and home is the
    identity (`homeUnique`).  So the witness clause of `ComesBack` follows from `Here`. -/
theorem realised_keep (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {X : VarType} {w : M.frame.W} (a : M.frame.Acc w)
    (r : M.frame.R a.1 w) (z : M.frame.Pos X w) {o : M.frame.Dom X w}
    (h : M.Realised hT (z : M.frame.Dom (.VTypeDia X) w) o) :
    ∃ hm : (⟨w, ⟨r⟩⟩ : M.frame.Acc a.1) ∈ (M.posEval (M.necEval (M.ops.posKeep hF z) a)).1,
      M.Ind ((M.posEval (M.necEval (M.ops.posKeep hF z) a)).2 ⟨_, hm⟩) o := by
  obtain ⟨hm, hi⟩ := h
  have key : ∀ (s : M.frame.R w w), ∃ hx : (⟨w, ⟨s⟩⟩ : M.frame.Acc w) ∈ (M.posEval z).1,
      M.Ind ((M.posEval z).2 ⟨⟨w, ⟨s⟩⟩, hx⟩) o := fun s => by
    obtain rfl : s = M.frame.refl hT w := @Subsingleton.elim _ (M.frame.homeUnique hS) _ _
    exact ⟨hm, hi⟩
  obtain ⟨hx, hi'⟩ := key (M.frame.trans hF a.2.down r)
  have hP := congrArg (fun p => p.1) (M.posKeep_full hF z a)
  change M.posEval _ = _ at hP
  rw [hP]
  exact ⟨hx, hi'⟩

end Model

end V12M
