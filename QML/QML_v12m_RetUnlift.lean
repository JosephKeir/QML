import QML.QML_v12m_RetLiftW
import QML.QML_v12m_BCompNamed

/-!
# QML v12m — strong B on S5: unlifting a returning possibility

The converse of `Proof.ret_lift` and `Proof.retW_lift`: what comes back as `t` is the kept image of
something whose value here is `t`.  So at T + 4 + strong B a returning possibility says no more
than its lift: `◇[⟨d, x⟩ ↦ ⟨t, c⟩] Ψ` holds exactly when some `⟨n, z⟩` has `Back (n.dup) t`,
`Here z c` and `◇Ψ(n.keep, z.keep)`.

`Back (n.dup) t` is along every arrow, so it names `t` at the own arrow only.  `back_keep` puts the
carrier on the leg with `n`'s own value, `ret_bridge` builds the atom there, and `back_here`,
contraposed, replaces that value by `t` (`Proof.back_value`).  The possible part is `ret_keep`.
-/

namespace V12M

variable [ModalSys] {σ : Signature}

open BArrow

section Main

variable {Γ : Ctx} [Γ.NoSlots] {A : VarType}

/-- ⭐**Interchange, the other way**: what a kept carrier comes back as has whatever the carrier's
    value has.  `back_here`, contraposed. -/
def Proof.back_value (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} {a₀ : Ann A} (b : Term σ Γ.boxIn A a₀)
    {a : Ann A} (t : Term σ Γ A a) (φ : WFF σ (Γ.insert (.bnd 0) A) 1)
    (h : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) b))) t))
    (p : Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots
      (Term.collapse (Ctx.collapses_boxIn_self hT Γ) b) φ)) :
    Proof σ Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ) := by
  refine Proof.byContra ?_
  have hn : Proof σ Γ (WFF.neg (WFF.instantiate Ctx.NoSlots.slots t φ) :: Δ)
      (WFF.instantiate Ctx.NoSlots.slots (Term.collapse (Ctx.collapses_boxIn_self hT Γ) b)
        φ.neg) :=
    Proof.conv (WFF.instantiate_congr_sig _ (congrArg (fun p =>
        (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) p.2⟩ : Σ e, Term σ Γ A e))
        (Term.collapse_shift_boxIn hT hF b)) φ.neg)
      (Proof.back_here hS hT _ t φ.neg
        (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) h)
        (Proof.lookup List.mem_cons_self))
  exact Proof.imp_elim hn (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) p)

/-- ⭐⭐**Unlifting a returning possibility** (T + 4, strong B), the converse of `Proof.ret_lift`,
    along either leg: if `□b` comes back as `t` and possibly `Φ(□b, kept)`, then `◇[d ↦ t] Φ(d)`. -/
def Proof.ret_unlift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {a₀ : Ann A}
    (b : Term σ Γ.boxIn A a₀) {a₁ : Ann A} (t : Term σ Γ A a₁)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (hb : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) b))) t))
    (hd : Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.mono O.le_view (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) Φ))) :
    Proof σ Γ Δ (O.ret hS t Φ) := by
  have hne : Proof σ Γ Δ (O.dia .top) := Proof.leg_dia O Proof.top_intro hd
  have H := Proof.ret_bridge hS O _ _ Φ (Proof.back_keep hS hT hF O b hne) hd
  refine Proof.conv (OutLeg.instantiate_retSlot hS O (.box A) Φ t) ?_
  exact Proof.back_value hS hT hF b t _ hb
    (Proof.conv (OutLeg.instantiate_retSlot hS O (.box A) Φ _).symm H)

end Main

section Witnessed

variable {Γ : Ctx} [Γ.NoSlots] {F X : VarType}

/-- `ret_keep`'s premise, instantiated: the slot's object paired with the kept possible object. -/
theorem RShape.instantiate_keepL (hF : ModalSys.Four = true) (O : OutLeg Γ) (N : NShape)
    {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {b₀ : Ann X}
    (bd : Term σ (Γ.diaIn x) X b₀) {a : Ann N.ty} (z : Term σ O.view N.ty a)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N X).ty) 1) :
    WFF.instantiate Ctx.NoSlots.slots z (WFF.bodyRepl (RShape.keepL hF O N hx bd).2 Ψ) =
      WFF.instantiate Ctx.NoSlots.slots
        (Term.pair z (Term.mono O.le_view (Term.keptDia hF hx bd).2)) Ψ :=
  (WFF.instantiate_bodyRepl _ _ z).trans (WFF.instantiate_congr_sig _
    (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ z (Subst.at_single_root _ _))
      ((Term.subst_single_mono (Ctx.Le.refl _) _ _ _ _
        ((Ctx.NoSlots.slots (Γ := O.view)).rootFresh (le_refl 0)) _).trans
        (congrArg (Sigma.mk _) (Term.mono_refl _ _)))) Ψ)

/-- ⭐⭐**Unlifting a witnessed returning possibility** (T + 4, strong B), the converse of
    `Proof.retW_lift`, along either leg, at terms. -/
def Proof.retW_unlift (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {a₀ : Ann F}
    (b : Term σ Γ.boxIn F a₀) {a₁ : Ann F} (t₁ : Term σ Γ F a₁) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {b₀ : Ann X} (bd : Term σ (Γ.diaIn x) X b₀)
    {a₂ : Ann X} (t₂ : Term σ Γ X a₂)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.box F) X).ty) 1)
    (hb : Proof σ Γ Δ (WFF.back hS .nec (Term.boxtm (Term.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF Γ) b))) t₁))
    (hh : Proof σ Γ Δ (WFF.here hT (Term.diatm x hx bd) t₂))
    (hd : Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.pair (Term.mono O.le_view (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)))
        (Term.mono O.le_view (Term.keptDia hF hx bd).2)) Ψ))) :
    Proof σ Γ Δ (O.retS hS (.wit (.box F) X) (Term.pair t₁ t₂) Ψ) :=
  Proof.ret_keep hS hT hF O (.box F) x hx bd t₂ t₁ Ψ hh
    (Proof.ret_unlift hS hT hF O b t₁ _ hb
      (Proof.conv (congrArg O.dia (RShape.instantiate_keepL hF O (.box F) hx bd _ Ψ)).symm hd))

variable {c₁ c₂ : VarSymb}

/-- ⭐⭐**The exact converse of `Proof.retW_lift`**: from what `WFF.liftedW` says of `⟨c₁, c₂⟩`, the
    witnessed returning possibility. -/
def Proof.retW_unlift_at (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Δ : List (WFF σ Γ 0)} (O : OutLeg Γ) {a₁ : Ann F} {a₂ : Ann X}
    (t₁ : Term σ Γ F a₁) (h₁ : Γ.ref c₁ = some (.VTypeBox F))
    (h₂ : Γ.ref c₂ = some (.VTypeDia X)) (t₂ : Term σ Γ X a₂)
    (Ψ : WFF σ (O.view.insert (.bnd 0) (wTy F X)) 1)
    (hb : Proof σ Γ Δ (WFF.holeAt Ctx.NoSlots.slots (Term.pair t₁ (wTerm h₁ h₂).2)
      (WFF.backFst F X hS hF)))
    (hh : Proof σ Γ Δ (WFF.here hT (Term.eta c₂ _ h₂) t₂))
    (hd : Proof σ Γ Δ (O.dia (WFF.instantiate Ctx.NoSlots.slots
      (Term.mono O.le_view (wKeep hF h₁ h₂).2) Ψ))) :
    Proof σ Γ Δ (O.retS hS (.wit (.box F) X) (Term.pair t₁ t₂) Ψ) := by
  have e₁ : (⟨_, Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ)
      (Term.eta c₁.inner F (Ctx.ref_inner h₁)))⟩ : Σ e, Term σ Γ.boxIn (.VTypeBox F) e) =
      ⟨_, Term.eta (.step c₁ .keep) (.VTypeBox F) (Ctx.ref_keep_of' hF h₁ rfl)⟩ :=
    sig_boxtm ((Term.shift_eta _ _ F _).trans (Term.eta_congr (VarSymb.inner_shift_zero c₁) F _ _))
  have e₂ : Term.keptDia (σ := σ) hF ⟨X, h₂⟩ (Term.eta (.step c₂ .dia) X (Ctx.ref_diaIn_of h₂)) =
      ⟨_, Term.eta (.step c₂ .keep) (.VTypeDia X) (Ctx.ref_keep_of' hF h₂ VarType.keepable_dia)⟩ :=
    sig_diatm ((Term.shift_eta _ _ X _).trans
      (Term.eta_congr (VarSymb.shift_level_zero (s := .dia) rfl) X _ _))
  refine Proof.retW_unlift hS hT hF O (Term.eta c₁.inner F (Ctx.ref_inner h₁)) t₁ c₂ ⟨X, h₂⟩
    (Term.eta (.step c₂ .dia) X (Ctx.ref_diaIn_of h₂)) t₂ Ψ
    (Proof.conv (WFF.holeAt_backG hS Ctx.NoSlots.slots _ _ _) hb) hh
    (Proof.conv (congrArg O.dia (WFF.instantiate_congr_sig _ ?_ Ψ)) hd)
  exact sig_pair (sig_mono _ e₁.symm) (sig_mono _ e₂.symm)

end Witnessed

end V12M
