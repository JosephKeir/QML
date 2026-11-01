import QML.QML_v12m_GLoop
import QML.QML_v12m_RealiseKeep
import QML.QML_v12m_BodyAbs

/-!
# QML v12m — T + 4 + 5 prove 4's lifts

Under T, 4 and 5 every arrow is invertible (`Frame.exists_inverse`), so keeping along an arrow is
onto in every model, whatever `FourStrong` and `FourStrongW` say.  The rules see it: `keep_lift` is
derivable (docs, "The open lifts: scope").

* `WFF.collapse_shift_self`, `WFF.shift_shift_same`: `Term.collapse_shift_self` and
  `Term.shift_shift_same` for formulas.
* ⭐`Proof.keep_lift_T`: the lift, along `□`.  At the far world `φ(c)` gives `□◇(shift φ̂(c))`, by
  `five_box` and `T_box`, so `□ξ` holds there kept for `ξ := ∃y. ◇φ̂(y)`; then `five_box` and
  `T_box` bring `ξ` home.
* ⭐`Proof.keep_lift_posT`: the lift, along `◇_x`.  `WFF.liftPos` is a body of the `□` view saying
  the body holds here, through `x.keep`, which `here_keep` realises at each world of `x`'s extent
  (`Proof.far_pos`, `Proof.here_intro`).  It goes through the lift along `□`, and `four_dia` brings
  it back into `x`'s extent (`Proof.four_dia_home`).
-/

namespace V12M

variable [ModalSys]

/-- ⭐**Under T, 4 and 5 every arrow is invertible**, in every model. -/
theorem Frame.exists_inverse {σ : Signature} (F : Frame σ) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (hV : ModalSys.Five = true) {w v : F.W} (a : F.R w v) :
    ∃ r : F.R v w, F.trans hF a r = F.refl hT w ∧ F.trans hF r a = F.refl hT v := by
  have h₁ : F.trans hF a (F.side hV a (F.refl hT w)) = F.refl hT w := F.trans_side hF hV a _
  have h₂ := F.trans_side hF hV (F.side hV a (F.refl hT w)) (F.refl hT v)
  refine ⟨_, h₁, ?_⟩
  have h₃ : F.side hV (F.side hV a (F.refl hT w)) (F.refl hT v) = a := by
    have := F.trans_assoc hF a (F.side hV a (F.refl hT w))
      (F.side hV (F.side hV a (F.refl hT w)) (F.refl hT v))
    rw [h₁, h₂, F.refl_trans hT hF, F.trans_refl hT hF] at this
    exact this
  rw [h₃] at h₂
  exact h₂

/-- ⭐**So keep is onto**, in every model with T, 4 and 5, whatever `FourStrong` says: `n`, kept
    along the inverse arrow and kept back, is `n`. -/
theorem Model.boxLift_of_T_five {σ : Signature} (M : Model σ) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) (hV : ModalSys.Five = true) {A : VarType} {w : M.frame.W}
    (a : M.frame.Acc w) (n : M.frame.Nec A a.1) :
    ∃ m : M.frame.Nec A w, M.necEval (M.ops.necDup hF m) a = n := by
  obtain ⟨r, -, hra⟩ := M.frame.exists_inverse hT hF hV a.2.down
  refine ⟨M.necEval (M.ops.necDup hF n) ⟨w, ⟨r⟩⟩, M.nec_inj ?_⟩
  funext s
  rw [M.necDup_eval hF _ a s, M.necDup_eval hF n ⟨w, ⟨r⟩⟩ _]
  have e : M.frame.trans hF r (M.frame.trans hF a.2.down s.2.down) = s.2.down := by
    rw [← M.frame.trans_assoc hF, hra, M.frame.refl_trans hT hF]
  rw [e]

section Forms

variable {σ : Signature}

theorem Rel.collapse_shift_self {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
    (hs : Ctx.Shifts m Γ₁ Γ₂) (hc : Ctx.Collapses (m + 1) Γ₂ Γ₃) (hle : Γ₁.Le Γ₃) :
    {n : ℕ} → (ρ : Rel σ Γ₁ n) → Rel.collapse hc (Rel.shift hs ρ) = Rel.mono hle ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.collapse hc (Rel.shift hs ρ)) (Term.collapse hc (Term.shift hs t)) = _
      rw [Rel.collapse_shift_self hs hc hle ρ,
        eq_of_heq (Sigma.mk.inj (Term.collapse_shift_self hs hc hle t)).2]
      rfl

/-- ⭐**Collapsing just outside a shift undoes it**: `Term.collapse_shift_self` for formulas. -/
theorem WFF.collapse_shift_self : ∀ {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx} {d : ℕ}
    (hs : Ctx.Shifts m Γ₁ Γ₂) (hc : Ctx.Collapses (m + 1) Γ₂ Γ₃) (hle : Γ₁.Le Γ₃)
    (hs₁ : Γ₁.SlotsFrom d) (hs₂ : Γ₂.SlotsFrom d) (φ : WFF σ Γ₁ d),
    WFF.collapse hc hs₂ (WFF.shift hs hs₁ φ) = WFF.mono hle φ
  | _, _, _, _, _, hs, hc, hle, _, _, .atom ρ =>
      congrArg WFF.atom (Rel.collapse_shift_self hs hc hle ρ)
  | _, _, _, _, _, hs, hc, hle, _, _, .eq t s =>
      congrArg₂ WFF.eq (eq_of_heq (Sigma.mk.inj (Term.collapse_shift_self hs hc hle t)).2)
        (eq_of_heq (Sigma.mk.inj (Term.collapse_shift_self hs hc hle s)).2)
  | _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, hs, hc, hle, hs₁, hs₂, .and φ ψ =>
      congrArg₂ WFF.and (WFF.collapse_shift_self hs hc hle hs₁ hs₂ φ)
        (WFF.collapse_shift_self hs hc hle hs₁ hs₂ ψ)
  | _, _, _, _, _, hs, hc, hle, hs₁, hs₂, .or φ ψ =>
      congrArg₂ WFF.or (WFF.collapse_shift_self hs hc hle hs₁ hs₂ φ)
        (WFF.collapse_shift_self hs hc hle hs₁ hs₂ ψ)
  | _, _, _, _, _, hs, hc, hle, hs₁, hs₂, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.collapse_shift_self hs hc hle hs₁ hs₂ φ)
        (WFF.collapse_shift_self hs hc hle hs₁ hs₂ ψ)
  | _, _, _, _, _, hs, hc, hle, hs₁, hs₂, .all T φ =>
      congrArg (WFF.all T) (WFF.collapse_shift_self (hs.insert (hs₁.rootFresh le_rfl) T)
        (hc.insert (hs₂.rootFresh le_rfl) T) (hle.insert _ T) (hs₁.insert T) (hs₂.insert T) φ)
  | _, _, _, _, _, hs, hc, hle, hs₁, hs₂, .ex T φ =>
      congrArg (WFF.ex T) (WFF.collapse_shift_self (hs.insert (hs₁.rootFresh le_rfl) T)
        (hc.insert (hs₂.rootFresh le_rfl) T) (hle.insert _ T) (hs₁.insert T) (hs₂.insert T) φ)
  | _, _, _, _, _, hs, hc, hle, hs₁, hs₂, .box φ =>
      congrArg WFF.box (WFF.collapse_shift_self hs.boxIn hc.boxIn hle.boxIn hs₁.boxIn
        hs₂.boxIn φ)
  | m, Γ₁, _, Γ₃, _, hs, hc, hle, hs₁, hs₂, .dia x hx φ => by
      have key : ∀ (y : VarSymb) (_hy : y = (x.shift m).collapse (m + 1))
          (P : ∃ X, Γ₃.ref y = some (.VTypeDia X)) (hle' : (Γ₁.diaIn x).Le (Γ₃.diaIn y)),
          WFF.collapse hc hs₂ (WFF.shift hs hs₁ (.dia x hx φ)) = .dia y P (WFF.mono hle' φ) := by
        intro y hy P hle'
        subst hy
        exact congrArg (WFF.dia _ P) (WFF.collapse_shift_self (hs.diaIn x) (hc.diaIn _) hle'
          (hs₁.diaIn x) (hs₂.diaIn _) φ)
      exact key x (VarSymb.collapse_shift_self x m).symm _ _
  | _, _, _, _, _, hs, hc, hle, _, _, .here hT s t =>
      WFF.here_congr hT (Term.collapse_shift_self hs hc hle s)
        (Term.collapse_shift_self hs hc hle t)
  | _, _, _, _, _, hs, hc, hle, _, _, .back hB L s t =>
      WFF.back_congr hB L (Term.collapse_shift_self hs hc hle s)
        (Term.collapse_shift_self hs hc hle t)
  | _, _, _, _, _, hs, hc, hle, hs₁, hs₂, .retS hB S t Φ =>
      WFF.retS_congr hB S (Term.collapse_shift_self hs hc hle t)
        (WFF.collapse_shift_self (hs.boxIn.insert (hs₁.boxIn.rootFresh le_rfl) _)
          (hc.boxIn.insert (hs₂.boxIn.rootFresh le_rfl) _) (hle.boxIn.insert _ _)
          (hs₁.boxIn.insert _) (hs₂.boxIn.insert _) Φ)
  | m, Γ₁, _, Γ₃, _, hs, hc, hle, hs₁, hs₂, .retxS hB y hy S t Φ => by
      have key : ∀ (z : VarSymb) (_hz : z = (y.shift m).collapse (m + 1))
          (P : ∃ Y, Γ₃.ref z = some (.VTypeDia Y))
          (hle' : ((Γ₁.diaIn y).insert (.bnd _) S.ty).Le ((Γ₃.diaIn z).insert (.bnd _) S.ty)),
          WFF.collapse hc hs₂ (WFF.shift hs hs₁ (.retxS hB y hy S t Φ)) =
            .retxS hB z P S (Term.mono hle t) (WFF.mono hle' Φ) := by
        intro z hz P hle'
        subst hz
        exact WFF.retxS_congr hB _ P S (Term.collapse_shift_self hs hc hle t)
          (WFF.collapse_shift_self ((hs.diaIn y).insert ((hs₁.diaIn y).rootFresh le_rfl) _)
            ((hc.diaIn _).insert ((hs₂.diaIn _).rootFresh le_rfl) _) hle'
            ((hs₁.diaIn y).insert _) ((hs₂.diaIn _).insert _) Φ)
      exact key y (VarSymb.collapse_shift_self y m).symm _ _

theorem Rel.shift_shift_same {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
    (h₁₂ : Ctx.Shifts m Γ₁ Γ₂) (h₂₃ : Ctx.Shifts m Γ₂ Γ₃) (h₂₃' : Ctx.Shifts (m + 1) Γ₂ Γ₃) :
    {n : ℕ} → (ρ : Rel σ Γ₁ n) →
    Rel.shift h₂₃ (Rel.shift h₁₂ ρ) = Rel.shift h₂₃' (Rel.shift h₁₂ ρ)
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.shift h₂₃ (Rel.shift h₁₂ ρ)) (Term.shift h₂₃ (Term.shift h₁₂ t)) = _
      rw [Rel.shift_shift_same h₁₂ h₂₃ h₂₃' ρ,
        eq_of_heq (Sigma.mk.inj (Term.shift_shift_same h₁₂ h₂₃ h₂₃' t)).2]
      rfl

/-- ⭐**Shifting twice at one level**: `Term.shift_shift_same` for formulas. -/
theorem WFF.shift_shift_same : ∀ {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx} {d : ℕ}
    (h₁₂ : Ctx.Shifts m Γ₁ Γ₂) (h₂₃ : Ctx.Shifts m Γ₂ Γ₃) (h₂₃' : Ctx.Shifts (m + 1) Γ₂ Γ₃)
    (hs₁ : Γ₁.SlotsFrom d) (hs₂ : Γ₂.SlotsFrom d) (φ : WFF σ Γ₁ d),
    WFF.shift h₂₃ hs₂ (WFF.shift h₁₂ hs₁ φ) = WFF.shift h₂₃' hs₂ (WFF.shift h₁₂ hs₁ φ)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', _, _, .atom ρ =>
      congrArg WFF.atom (Rel.shift_shift_same h₁₂ h₂₃ h₂₃' ρ)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', _, _, .eq t s =>
      congrArg₂ WFF.eq (eq_of_heq (Sigma.mk.inj (Term.shift_shift_same h₁₂ h₂₃ h₂₃' t)).2)
        (eq_of_heq (Sigma.mk.inj (Term.shift_shift_same h₁₂ h₂₃ h₂₃' s)).2)
  | _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .and φ ψ =>
      congrArg₂ WFF.and (WFF.shift_shift_same h₁₂ h₂₃ h₂₃' hs₁ hs₂ φ)
        (WFF.shift_shift_same h₁₂ h₂₃ h₂₃' hs₁ hs₂ ψ)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .or φ ψ =>
      congrArg₂ WFF.or (WFF.shift_shift_same h₁₂ h₂₃ h₂₃' hs₁ hs₂ φ)
        (WFF.shift_shift_same h₁₂ h₂₃ h₂₃' hs₁ hs₂ ψ)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.shift_shift_same h₁₂ h₂₃ h₂₃' hs₁ hs₂ φ)
        (WFF.shift_shift_same h₁₂ h₂₃ h₂₃' hs₁ hs₂ ψ)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .all T φ =>
      congrArg (WFF.all T) (WFF.shift_shift_same (h₁₂.insert (hs₁.rootFresh le_rfl) T)
        (h₂₃.insert (hs₂.rootFresh le_rfl) T) (h₂₃'.insert (hs₂.rootFresh le_rfl) T)
        (hs₁.insert T) (hs₂.insert T) φ)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .ex T φ =>
      congrArg (WFF.ex T) (WFF.shift_shift_same (h₁₂.insert (hs₁.rootFresh le_rfl) T)
        (h₂₃.insert (hs₂.rootFresh le_rfl) T) (h₂₃'.insert (hs₂.rootFresh le_rfl) T)
        (hs₁.insert T) (hs₂.insert T) φ)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .box φ =>
      congrArg WFF.box (WFF.shift_shift_same h₁₂.boxIn h₂₃.boxIn h₂₃'.boxIn hs₁.boxIn
        hs₂.boxIn φ)
  | m, _, Γ₂, Γ₃, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .dia x hx φ => by
      have key : ∀ (y : VarSymb) (_hy : y = (x.shift m).shift m)
          (P : ∃ X, Γ₃.ref y = some (.VTypeDia X))
          (h' : Ctx.Shifts (m + 1 + 1) (Γ₂.diaIn (x.shift m)) (Γ₃.diaIn y)),
          WFF.shift h₂₃ hs₂ (WFF.shift h₁₂ hs₁ (.dia x hx φ)) =
            .dia y P (WFF.shift h' (hs₂.diaIn _) (WFF.shift (h₁₂.diaIn x) (hs₁.diaIn x) φ)) := by
        intro y hy P h'
        subst hy
        exact congrArg (WFF.dia _ P) (WFF.shift_shift_same (h₁₂.diaIn x) (h₂₃.diaIn _) h'
          (hs₁.diaIn x) (hs₂.diaIn _) _)
      exact key _ (VarSymb.shift_shift_same x m).symm _ _
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', _, _, .here hT s t =>
      WFF.here_congr hT (Term.shift_shift_same h₁₂ h₂₃ h₂₃' s)
        (Term.shift_shift_same h₁₂ h₂₃ h₂₃' t)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', _, _, .back hB L s t =>
      WFF.back_congr hB L (Term.shift_shift_same h₁₂ h₂₃ h₂₃' s)
        (Term.shift_shift_same h₁₂ h₂₃ h₂₃' t)
  | _, _, _, _, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .retS hB S t Φ =>
      WFF.retS_congr hB S (Term.shift_shift_same h₁₂ h₂₃ h₂₃' t)
        (WFF.shift_shift_same (h₁₂.boxIn.insert (hs₁.boxIn.rootFresh le_rfl) _)
          (h₂₃.boxIn.insert (hs₂.boxIn.rootFresh le_rfl) _)
          (h₂₃'.boxIn.insert (hs₂.boxIn.rootFresh le_rfl) _)
          (hs₁.boxIn.insert _) (hs₂.boxIn.insert _) Φ)
  | m, _, Γ₂, Γ₃, _, h₁₂, h₂₃, h₂₃', hs₁, hs₂, .retxS hB y hy S t Φ => by
      have key : ∀ (z : VarSymb) (_hz : z = (y.shift m).shift m)
          (P : ∃ Y, Γ₃.ref z = some (.VTypeDia Y))
          (h' : Ctx.Shifts (m + 1 + 1) ((Γ₂.diaIn (y.shift m)).insert (.bnd _) S.ty)
            ((Γ₃.diaIn z).insert (.bnd _) S.ty)),
          WFF.shift h₂₃ hs₂ (WFF.shift h₁₂ hs₁ (.retxS hB y hy S t Φ)) =
            .retxS hB z P S (Term.shift h₂₃' (Term.shift h₁₂ t))
              (WFF.shift h' ((hs₂.diaIn _).insert _)
                (WFF.shift ((h₁₂.diaIn y).insert ((hs₁.diaIn y).rootFresh le_rfl) _)
                  ((hs₁.diaIn y).insert _) Φ)) := by
        intro z hz P h'
        subst hz
        exact WFF.retxS_congr hB _ P S (Term.shift_shift_same h₁₂ h₂₃ h₂₃' t)
          (WFF.shift_shift_same ((h₁₂.diaIn y).insert ((hs₁.diaIn y).rootFresh le_rfl) _)
            ((h₂₃.diaIn _).insert ((hs₂.diaIn _).rootFresh le_rfl) _) h'
            ((hs₁.diaIn y).insert _) ((hs₂.diaIn _).insert _) Φ)
      exact key _ (VarSymb.shift_shift_same y m).symm _ _

end Forms

/-! ## The lift along `□` -/

section Lift

variable {σ : Signature} {T : VarType}

/-- The collapse of a kept address is the address. -/
theorem Term.collapse_keepOf (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hk : T.keepable = true) (ht : T.tup = true) {K : Ctx} (c : VarSymb)
    (h : K.ref c = some T) :
    (⟨_, Term.collapse (Ctx.collapses_boxIn_self hT K) (Term.keepOf (σ := σ) hF T ht c h)⟩ :
      Σ b, Term σ K T b) = ⟨_, Term.eta c T h⟩ := by
  cases T with
  | VTypeBox A =>
      exact (Term.collapse_eta _ _ _ _).trans (Term.eta_congr VarSymb.collapse_keep_zero _ _ _)
  | VTypeDia A =>
      exact (Term.collapse_eta _ _ _ _).trans (Term.eta_congr VarSymb.collapse_keep_zero _ _ _)
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd A B => cases hk

/-- The slot at a kept address corresponds, under the collapse, to the slot at the address. -/
theorem corr_keepOf (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hk : T.keepable = true) (ht : T.tup = true) {Ξ : Ctx} [Ξ.NoSlots] {c : ℕ}
    (hc : Ξ.RootFresh (.free c)) :
    Subst.Corr (Ξ.boxIn.insert (.bnd 0) T)
      (Ctx.collapses_boxIn_self hT (Ξ.insert (.free c) T))
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keepOf hF T ht (.root (.free c))
        (Ctx.ref_insert_root Ξ (.free c) T))))
      (Subst.single (.bnd 0) (.tm (Term.eta (.root (.free c)) T
        (Ctx.ref_insert_root Ξ (.free c) T)))) := by
  have hr := (Ctx.NoSlots.slots (Γ := Ξ.boxIn)).rootFresh (le_refl 0)
  refine Subst.corr_of (Subst.ok_single (Ctx.le_insert hc.root T).boxIn rfl) ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hU : T = U := by simpa [Ctx.insert] using hv
    subst hU
    change SubE.Sim T (Subst.at _ (.root (.bnd 0))) (SubE.collapse _ (if _ then _ else _))
    rw [if_pos rfl, Subst.at_single_root]
    exact SubE.Sim.of_sig (Term.collapse_keepOf hT hF hk ht _ _).symm T
  · have hv' : Ξ.boxIn v = some U := by
      have := hv
      simpa [Ctx.insert, hvr] using this
    have hne := Ctx.ref_rt_ne hr ((Ctx.ref_nonproj _ hlp).trans hv')
    change SubE.Sim U (Subst.at _ _) (SubE.collapse _ (if v = _ then _ else _))
    rw [if_neg hvr, Subst.single_at_ne (by rwa [VarSymb.collapse_rt])]
    exact .refl _

/-- ⭐The collapse of a body read at a kept address is the collapsed body read at the address. -/
theorem WFF.collapse_read (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hk : T.keepable = true) (ht : T.tup = true) {Ξ : Ctx} [Ξ.NoSlots] {c : ℕ}
    (hc : Ξ.RootFresh (.free c)) (Ψ : WFF σ (Ξ.boxIn.insert (.bnd 0) T) 1) :
    WFF.collapse (Ctx.collapses_boxIn_self hT (Ξ.insert (.free c) T)) Ctx.NoSlots.slots
      (WFF.instantiate Ctx.NoSlots.slots
        (Term.keepOf hF T ht (.root (.free c)) (Ctx.ref_insert_root Ξ (.free c) T))
        (WFF.mono ((Ctx.le_insert hc.root T).boxIn.insert (.bnd 0) T) Ψ)) =
    WFF.instantiate Ctx.NoSlots.slots
      (Term.eta (.root (.free c)) T (Ctx.ref_insert_root Ξ (.free c) T))
      (WFF.mono ((Ctx.le_insert hc.root T).insert (.bnd 0) T)
        (WFF.collapse ((Ctx.collapses_boxIn_self hT Ξ).insert
          ((Ctx.NoSlots.slots (Γ := Ξ.boxIn)).rootFresh (le_refl 0)) T)
          ((Ctx.NoSlots.slots (Γ := Ξ.boxIn)).insert T) Ψ)) := by
  have hr := (Ctx.NoSlots.slots (Γ := Ξ.boxIn)).rootFresh (le_refl 0)
  have hr' := (Ctx.NoSlots.slots (Γ := Ξ)).rootFresh (le_refl 0)
  have key := WFF.collapse_subst ((Ctx.collapses_boxIn_self hT Ξ).insert hr T)
    (Ctx.collapses_boxIn_self hT (Ξ.insert (.free c) T))
    (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keepOf hF T ht (.root (.free c))
      (Ctx.ref_insert_root Ξ (.free c) T))))
    (Subst.ok_single (Ctx.le_insert hc.root T).boxIn rfl)
    (Subst.coh_single hr (Ctx.le_insert hc.root T).boxIn rfl)
    (Subst.single (.bnd 0) (.tm (Term.eta (.root (.free c)) T
      (Ctx.ref_insert_root Ξ (.free c) T))))
    (Subst.ok_single (Ctx.le_insert hc.root T) rfl)
    (Subst.coh_single hr' (Ctx.le_insert hc.root T) rfl)
    ((Ctx.NoSlots.slots (Γ := Ξ.boxIn)).insert T) ((Ctx.NoSlots.slots (Γ := Ξ)).insert T)
    Ctx.NoSlots.slots Ctx.NoSlots.slots (corr_keepOf hT hF hk ht hc) Ψ
  unfold WFF.instantiate WFF.substRoot
  exact (congrArg _ (WFF.subst_mono _ _ _ _ _ _ _ _)).trans
    (key.trans (WFF.subst_mono _ _ _ _ _ _ _ _).symm)

/-- A root's `keep` tuple shifted one view further in, past its own step. -/
theorem Term.shift_keepOf_root (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (ht : T.tup = true) {Ω Ω' : Ctx} (D : Ctx.Shifts 1 Ω.boxIn Ω'.boxIn) (r : Root)
    (h : Ω.ref (.root r) = some T) (h' : Ω'.ref (.root r) = some T) :
    (⟨_, Term.shift D (Term.keepOf (σ := σ) hF T ht (.root r) h)⟩ : Σ b, Term σ Ω'.boxIn T b) =
      ⟨_, Term.keepOf hF T ht (.root r) h'⟩ := by
  cases T with
  | VTypeBox A => exact Term.shift_eta D _ _ _
  | VTypeDia A => exact Term.shift_eta D _ _ _
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd A B => cases hk

/-- ⭐**The hat, shifted, is the hat of the shift.** -/
theorem WFF.shift_loopHat (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (ht : T.tup = true) {Γ : Ctx} [Γ.NoSlots] (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) :
    WFF.shift (Ctx.shifts_loop hF Γ T).boxIn ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T).boxIn
      (WFF.loopHat hF ht φ) =
    WFF.loopHat (Γ := Γ.boxIn) hF ht
      (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ) := by
  have hr₂ := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  have hr₃ := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn.boxIn)).rootFresh (le_refl 0)
  have C : Ctx.Shifts 1 (Γ.boxIn.boxIn.insert (.bnd 0) T) (Γ.boxIn.boxIn.boxIn.insert (.bnd 0) T) :=
    (Ctx.shifts_boxIn_boxIn hF Γ).boxIn.insert hr₂ T
  have hle : Γ.boxIn.boxIn.Le (Γ.boxIn.insert (.bnd 0) T).boxIn :=
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root T).boxIn
  have hle' : Γ.boxIn.boxIn.boxIn.Le (Γ.boxIn.boxIn.insert (.bnd 0) T).boxIn :=
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).root T).boxIn
  have hcr : Subst.ShiftCorr (Γ.boxIn.boxIn.insert (.bnd 0) T) (Ctx.shifts_loop hF Γ T).boxIn
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keepOf hF T ht (.root (.bnd 0))
        (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))))
      (Subst.single (.bnd 0) (.tm (Term.keepOf hF T ht (.root (.bnd 0))
        (Ctx.ref_insert_root Γ.boxIn.boxIn (.bnd 0) T)))) := by
    refine Subst.shiftCorr_of (Subst.ok_single hle rfl) ?_
    intro v U hlp hv
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      have hU : T = U := by simpa [Ctx.insert] using hv
      subst hU
      change SubE.Sim T (Subst.at _ (.root (.bnd 0))) (SubE.shift _ (if _ then _ else _))
      rw [if_pos rfl, Subst.at_single_root]
      exact SubE.Sim.of_sig (Term.shift_keepOf_root hF hk ht _ _ _ _).symm T
    · have hv' : Γ.boxIn.boxIn v = some U := by
        have := hv
        simpa [Ctx.insert, hvr] using this
      have hne := Ctx.ref_rt_ne hr₂ ((Ctx.ref_nonproj _ hlp).trans hv')
      change SubE.Sim U (Subst.at _ _) (SubE.shift _ (if v = _ then _ else _))
      rw [if_neg hvr, Subst.single_at_ne (by rwa [VarSymb.shift_rt])]
      exact .refl _
  have key := WFF.shift_subst C (Ctx.shifts_loop hF Γ T).boxIn
    (Subst.single (σ := σ) (.bnd 0) (.tm (Term.keepOf hF T ht (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))))
    (Subst.ok_single hle rfl) (Subst.coh_single hr₂ hle rfl)
    (Subst.single (.bnd 0) (.tm (Term.keepOf hF T ht (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn.boxIn (.bnd 0) T))))
    (Subst.ok_single hle' rfl) (Subst.coh_single hr₃ hle' rfl)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert T)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn.boxIn)).insert T)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T).boxIn
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert T).boxIn hcr
    (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ)
  refine key.trans ?_
  exact congrArg (WFF.subst _ _ _ _ _ _) (WFF.shift_shift_same (Ctx.shifts_loop hF Γ T)
    (Ctx.shifts_loop hF Γ.boxIn T) C _ _ φ).symm

/-- `ξ`'s body: a possibility of the hat. -/
def WFF.liftBody {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (ht : T.tup = true)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1 :=
  (WFF.box (WFF.loopHat hF ht φ.neg)).neg

/-- `liftBody` read at a kept object is a possibility of the formula read there, shifted. -/
theorem WFF.liftBody_read {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (hF : ModalSys.Four = true)
    (ht : T.tup = true) (h : Γ.Le Γ') (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) {t₀ : Ann T}
    {t : Term σ Γ'.boxIn T t₀} (hk : Term.Kept t) :
    WFF.instantiate Ctx.NoSlots.slots t
      (WFF.mono (h.boxIn.insert (.bnd 0) T) (WFF.liftBody hF ht φ)) =
      (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ') Ctx.NoSlots.slots
        (WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (h.boxIn.insert (.bnd 0) T) φ.neg)))).neg :=
  congrArg WFF.neg (WFF.loopHat_read hF ht h φ.neg hk)

/-- A kept root is kept. -/
theorem Term.kept_keepOf (hF : ModalSys.Four = true) (hk : T.keepable = true) (ht : T.tup = true)
    {K : Ctx} (c : VarSymb) (h : K.ref c = some T) :
    Term.Kept (Term.keepOf (σ := σ) hF T ht c h) := by
  cases T with
  | VTypeBox A => exact .leaf hk _ _
  | VTypeDia A => exact .leaf hk _ _
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd A B => cases hk

/-- ⭐**What holds out there is, from there, necessarily possible, kept** (T + 4 + 5): `five_box`
    refutes the contrary, and `T_box` reads it, the collapse undoing the hat. -/
def Proof.far_nec (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hk : T.keepable = true) (ht : T.tup = true) {Γ : Ctx} [Γ.NoSlots]
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (c : ℕ) (hc : Γ.boxIn.RootFresh (.free c)) :
    Proof σ (Γ.boxIn.insert (.free c) T) [WFF.openFree c hc Ctx.NoSlots.slots φ]
      (.box (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF (Γ.boxIn.insert (.free c) T))
        Ctx.NoSlots.slots
        (WFF.instantiate Ctx.NoSlots.slots
          (Term.keepOf hF T ht (.root (.free c)) (Ctx.ref_insert_root Γ.boxIn (.free c) T))
          (WFF.mono ((Ctx.le_insert hc.root T).boxIn.insert (.bnd 0) T)
            (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
              φ.neg))))).neg) := by
  have hr := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  have e := WFF.collapse_shift_same (Ctx.shifts_loop hF Γ T)
    ((Ctx.collapses_boxIn_self hT Γ.boxIn).insert hr T) (Ctx.Le.refl _)
    ((Ctx.shiftCollapseId_keepOnly (keepOnly_of hT hF) Γ).insert _ _)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert T) φ.neg
  rw [WFF.mono_refl] at e
  have e₂ := WFF.collapse_read hT hF hk ht hc
    (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ.neg)
  rw [e, WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ.neg] at e₂
  refine Proof.byContra (Proof.imp_elim ?_
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
  rw [WFF.openFree_neg] at e₂
  exact Proof.conv e₂ (Proof.T_box hT (Proof.five_box hF hV (Proof.lookup List.mem_cons_self)))

/-- ⭐`∃y. ◇φ̂(y)` holds kept at every successor of a world with `φ(c)`. -/
def Proof.far_ex (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hk : T.keepable = true) (ht : T.tup = true) {Γ : Ctx} [Γ.NoSlots]
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (c : ℕ) (hc : Γ.boxIn.RootFresh (.free c)) :
    Proof σ Γ.boxIn [WFF.ex T φ]
      (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots
        (WFF.ex T (WFF.liftBody hF ht φ)))) := by
  have hle := Ctx.le_insert hc.root T
  have hk' := Term.kept_keepOf (σ := σ) hF hk ht (K := Γ.boxIn.insert (.free c) T)
    (.root (.free c)) (Ctx.ref_insert_root Γ.boxIn (.free c) T)
  have eS : WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
      (WFF.liftBody hF ht φ) = WFF.liftBody (Γ := Γ.boxIn) hF ht
        (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ) :=
    congrArg WFF.neg (congrArg WFF.box (WFF.shift_loopHat hF hk ht φ.neg))
  have hb : Proof σ (Γ.boxIn.insert (.free c) T).boxIn
      [(WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF (Γ.boxIn.insert (.free c) T))
        Ctx.NoSlots.slots
        (WFF.instantiate Ctx.NoSlots.slots
          (Term.keepOf hF T ht (.root (.free c)) (Ctx.ref_insert_root Γ.boxIn (.free c) T))
          (WFF.mono ((Ctx.le_insert hc.root T).boxIn.insert (.bnd 0) T)
            (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
              φ.neg))))).neg]
      (WFF.ex T (WFF.mono (hle.boxIn.insert (.bnd 0) T)
        (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)
          (WFF.liftBody hF ht φ)))) := by
    refine Proof.ex_intro T (Term.keepOf hF T ht (.root (.free c))
      (Ctx.ref_insert_root Γ.boxIn (.free c) T)) ?_
    rw [eS, WFF.liftBody_read hF ht hle _ hk']
    exact Proof.lookup List.mem_cons_self
  refine Proof.ex_elim c T hc (φ := WFF.openFree c hc Ctx.NoSlots.slots φ)
    (Proof.conv (congrArg (WFF.ex T)
      (WFF.bindFree_openFree c hc (Ctx.NoSlots.slots (Γ := Γ.boxIn)) φ).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  refine Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx)
    (Proof.imp_intro (Proof.K_box (Δ := [_]) hb))) ?_
  exact Proof.ofSubset (fun y hy => by
    rw [List.mem_singleton.mp hy]
    exact List.mem_cons_self) (Proof.far_nec hT hF hV hk ht φ c hc)

/-- ⭐**`∃y. ◇φ(y.keep)`, from `◇∃c. φ(c)`** (T + 4 + 5): `ξ` comes home by `five_box` and
    `T_box`. -/
def Proof.lift_ex_T (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hk : T.keepable = true) (ht : T.tup = true) {Γ : Ctx} [Γ.NoSlots]
    {Δ : List (WFF σ Γ 0)} (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (c : ℕ)
    (hc : Γ.RootFresh (.free c)) (p : Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.ex T φ))) :
    Proof σ Γ Δ (WFF.collapse (Ctx.collapses_boxIn_self hT Γ) Ctx.NoSlots.slots
      (WFF.ex T (WFF.liftBody hF ht φ))) :=
  Proof.T_box hT (Proof.five_box hF hV (Proof.leg_dia .nec
    (Proof.far_ex hT hF hV hk ht φ c hc.boxIn) p))

/-- The lift's body, opened at `c`, is what `keep_lift` hands its subproof. -/
theorem WFF.liftRead_nec (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hl : T.liftable = true) (ht : T.tup = true) {Γ : Ctx} [Γ.NoSlots]
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) {c : ℕ} (hc : Γ.RootFresh (.free c)) :
    WFF.liftRead hF hl (.nec : OutLeg Γ) hc φ = WFF.openFree c hc Ctx.NoSlots.slots
      (WFF.collapse ((Ctx.collapses_boxIn_self hT Γ).insert
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) T)
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) (WFF.liftBody hF ht φ)) := by
  have hk := VarType.keepable_of_liftable hl
  have hle := Ctx.le_insert hc.root T
  have hk' := Term.kept_keepOf (σ := σ) hF hk ht (K := Γ.insert (.free c) T)
    (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) T)
  have e₁ := WFF.collapse_read hT hF hk ht hc (WFF.liftBody hF ht φ)
  rw [WFF.liftBody_read hF ht hle φ hk',
    WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots Ctx.NoSlots.slots] at e₁
  have e₂ := WFF.collapse_shift_self (Ctx.shifts_boxIn_boxIn hF (Γ.insert (.free c) T))
    (Ctx.collapses_boxIn_self hT (Γ.insert (.free c) T)).boxIn (Ctx.Le.refl _)
    Ctx.NoSlots.slots Ctx.NoSlots.slots
    (WFF.instantiate Ctx.NoSlots.slots
      (Term.keepOf hF T ht (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) T))
      (WFF.mono (hle.boxIn.insert (.bnd 0) T) φ.neg))
  rw [WFF.mono_refl] at e₂
  have e₃ := (congrArg (fun z => (WFF.box z).neg) e₂.symm).trans e₁
  cases T with
  | VTypeBox A => exact e₃
  | VTypeDia A => exact e₃
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd A B => cases hk

/-- ⭐⭐**`keep_lift` along `□` is derivable under T, 4 and 5**, whatever `FourStrong` and
    `FourStrongW` say: the rule's own shape. -/
def Proof.keep_lift_T (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hl : T.liftable = true) (ht : T.tup = true) {Γ : Ctx} [Γ.NoSlots]
    {Δ : List (WFF σ Γ 0)} (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (c : ℕ)
    (hc : Γ.RootFresh (.free c)) {ψ : WFF σ Γ 0}
    (p : Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.ex T φ)))
    (q : Proof σ (Γ.insert (.free c) T)
      (WFF.liftRead hF hl (.nec : OutLeg Γ) hc φ :: Δ.map (WFF.weaken hc.root T))
      (ψ.weaken hc.root T)) :
    Proof σ Γ Δ ψ := by
  refine Proof.ex_elim c T hc (φ := WFF.liftRead hF hl (.nec : OutLeg Γ) hc φ) ?_ q
  rw [WFF.liftRead_nec hT hF hl ht φ hc, WFF.bindFree_openFree]
  exact Proof.lift_ex_T hT hF hV (VarType.keepable_of_liftable hl) ht φ c hc p

end Lift

/-! ## A body read at a term -/

section Read

variable {σ : Signature}

/-- A body with its slot read at a term of a larger context. -/
def WFF.readAt {Λ Ω : Ctx} [Λ.NoSlots] {P : VarType} {d : ℕ} (hle : Λ.Le Ω) (hs : Ω.SlotsFrom d)
    {a : Ann P} (u : Term σ Ω P a) (B : WFF σ (Λ.insert (.bnd 0) P) 1) : WFF σ Ω d :=
  WFF.subst (Subst.singleIdx (.bnd 0) (.tm u)) (Subst.single (.bnd 0) (.tm u))
    (Subst.ok_single hle rfl)
    (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Λ)).rootFresh (le_refl 0)) hle rfl)
    ((Ctx.NoSlots.slots (Γ := Λ)).insert P) hs B

theorem WFF.readAt_congr {Λ Ω : Ctx} [Λ.NoSlots] {P : VarType} {d : ℕ} (hle : Λ.Le Ω)
    (hs : Ω.SlotsFrom d) {a b : Ann P} {u : Term σ Ω P a} {t : Term σ Ω P b}
    (h : (⟨a, u⟩ : Σ c, Term σ Ω P c) = ⟨b, t⟩) (B : WFF σ (Λ.insert (.bnd 0) P) 1) :
    WFF.readAt hle hs u B = WFF.readAt hle hs t B := by
  cases h
  rfl

/-- ⭐A substitution fixing the body's old items moves only the term it is read at. -/
theorem WFF.subst_readAt {Λ Ω Ω₂ : Ctx} [Λ.NoSlots] {P : VarType} {d d₂ : ℕ}
    {ι : VarSymb → VarSymb} (hle : Λ.Le Ω) (hle₂ : Λ.Le Ω₂) (hs : Ω.SlotsFrom d)
    (hs₂ : Ω₂.SlotsFrom d₂) {a : Ann P} (u : Term σ Ω P a) (B : WFF σ (Λ.insert (.bnd 0) P) 1)
    (θ : Subst σ Ω₂) (hθ : Subst.Ok Ω θ) (hc : Subst.Coh ι Ω θ)
    (hfix : ∀ v W, Λ.ref v = some W → θ.at v = .ren v) :
    WFF.subst ι θ hθ hc hs hs₂ (WFF.readAt hle hs u B) =
      WFF.readAt hle₂ hs₂ (Term.subst ι θ hθ hc u) B := by
  have hr := (Ctx.NoSlots.slots (Γ := Λ)).rootFresh (le_refl 0)
  refine WFF.subst_comp _ _ (Subst.single (.bnd 0) (.tm (Term.subst ι θ hθ hc u))) _ _ _ _
    (Subst.ok_single hle₂ rfl) (Subst.coh_single hr hle₂ rfl) _ _ _ ?_ B
  refine Subst.sim_of ?_
  intro v U hl hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hU : P = U := by simpa [Ctx.insert] using hv
    subst hU
    change SubE.Sim P (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _)
      (SubE.comp _ _ _ (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _))
    rw [if_pos rfl, if_pos rfl]
    exact .refl _
  · have hv' : Λ v = some U := by
      have := hv
      simpa [Ctx.insert, hvr] using this
    change SubE.Sim U (if v = .root (.bnd 0) then _ else _)
      (SubE.comp _ _ _ (if v = .root (.bnd 0) then _ else _))
    rw [if_neg hvr, if_neg hvr]
    change SubE.Sim U _ (Subst.at _ v)
    rw [hfix v U ((Ctx.ref_nonproj _ hl).trans hv')]
    exact .refl _

/-- ⭐Shifting a body read at a term is the shifted body read at the shifted term. -/
theorem WFF.shift_readAt {Λ Λ' Ω Ω' : Ctx} [Λ.NoSlots] [Λ'.NoSlots] {P : VarType} {d : ℕ}
    (C : Ctx.Shifts 0 Λ Λ') (D : Ctx.Shifts 0 Ω Ω') (hle : Λ.Le Ω) (hle' : Λ'.Le Ω')
    (hs : Ω.SlotsFrom d) (hs' : Ω'.SlotsFrom d) {a : Ann P} (u : Term σ Ω P a)
    (B : WFF σ (Λ.insert (.bnd 0) P) 1) :
    WFF.shift D hs (WFF.readAt hle hs u B) =
      WFF.readAt hle' hs' (Term.shift D u)
        (WFF.shift (C.insert ((Ctx.NoSlots.slots (Γ := Λ)).rootFresh (le_refl 0)) P)
          ((Ctx.NoSlots.slots (Γ := Λ)).insert P) B) := by
  have hr := (Ctx.NoSlots.slots (Γ := Λ)).rootFresh (le_refl 0)
  have hr' := (Ctx.NoSlots.slots (Γ := Λ')).rootFresh (le_refl 0)
  refine WFF.shift_subst (C.insert hr P) D _ _ _
    (Subst.single (.bnd 0) (.tm (Term.shift D u))) (Subst.ok_single hle' rfl)
    (Subst.coh_single hr' hle' rfl) _ _ _ _ ?_ B
  refine Subst.shiftCorr_of (Subst.ok_single hle rfl) ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hU : P = U := by simpa [Ctx.insert] using hv
    subst hU
    change SubE.Sim P (Subst.at _ (.root (.bnd 0))) (SubE.shift _ (if _ then _ else _))
    rw [if_pos rfl, Subst.at_single_root]
    exact .refl _
  · have hv' : Λ v = some U := by
      have := hv
      simpa [Ctx.insert, hvr] using this
    have hne := Ctx.ref_rt_ne hr ((Ctx.ref_nonproj _ hlp).trans hv')
    change SubE.Sim U (Subst.at _ _) (SubE.shift _ (if v = _ then _ else _))
    rw [if_neg hvr, Subst.single_at_ne (by rwa [VarSymb.shift_rt])]
    exact .refl _

/-- ⭐Collapsing a body read at a term is the collapsed body read at the collapsed term. -/
theorem WFF.collapse_readAt {Λ Λ' Ω Ω' : Ctx} [Λ.NoSlots] [Λ'.NoSlots] {P : VarType} {d : ℕ}
    (C : Ctx.Collapses 0 Λ Λ') (D : Ctx.Collapses 0 Ω Ω') (hle : Λ.Le Ω) (hle' : Λ'.Le Ω')
    (hs : Ω.SlotsFrom d) (hs' : Ω'.SlotsFrom d) {a : Ann P} (u : Term σ Ω P a)
    (B : WFF σ (Λ.insert (.bnd 0) P) 1) :
    WFF.collapse D hs (WFF.readAt hle hs u B) =
      WFF.readAt hle' hs' (Term.collapse D u)
        (WFF.collapse (C.insert ((Ctx.NoSlots.slots (Γ := Λ)).rootFresh (le_refl 0)) P)
          ((Ctx.NoSlots.slots (Γ := Λ)).insert P) B) := by
  have hr := (Ctx.NoSlots.slots (Γ := Λ)).rootFresh (le_refl 0)
  have hr' := (Ctx.NoSlots.slots (Γ := Λ')).rootFresh (le_refl 0)
  refine WFF.collapse_subst (C.insert hr P) D _ _ _
    (Subst.single (.bnd 0) (.tm (Term.collapse D u))) (Subst.ok_single hle' rfl)
    (Subst.coh_single hr' hle' rfl) _ _ _ _ ?_ B
  refine Subst.corr_of (Subst.ok_single hle rfl) ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hU : P = U := by simpa [Ctx.insert] using hv
    subst hU
    change SubE.Sim P (Subst.at _ (.root (.bnd 0))) (SubE.collapse _ (if _ then _ else _))
    rw [if_pos rfl, Subst.at_single_root]
    exact .refl _
  · have hv' : Λ v = some U := by
      have := hv
      simpa [Ctx.insert, hvr] using this
    have hne := Ctx.ref_rt_ne hr ((Ctx.ref_nonproj _ hlp).trans hv')
    change SubE.Sim U (Subst.at _ _) (SubE.collapse _ (if v = _ then _ else _))
    rw [if_neg hvr, Subst.single_at_ne (by rwa [VarSymb.collapse_rt])]
    exact .refl _

end Read

/-! ## The lift along `◇_x` -/

section LiftPos

variable {σ : Signature}

/-- A substitution fixing a context fixes its `◇_y` view. -/
theorem dia_at_ren {Λ Δ : Ctx} {θ : Subst σ Δ}
    (hid : ∀ v U, Λ.ref v = some U → θ.at v = .ren v) {y : VarSymb} :
    ∀ v U, (Λ.diaIn y).ref v = some U → (θ.dia y y).at v = .ren v := by
  refine Subst.at_ren_of ?_
  intro v U hlp hv
  by_cases hvd : v = .step y .dia
  · subst hvd
    change (if y = y then (θ.at y).diaBody y else .hide) = _
    rw [if_pos rfl]
    have hy : Λ.ref y ≠ none := by
      intro h
      change (if y = y then (match Λ.ref y with
        | some (.VTypeDia X) => some X
        | _ => none) else none) = some U at hv
      rw [if_pos rfl, h] at hv
      cases hv
    obtain ⟨W, hW⟩ := Option.ne_none_iff_exists'.mp hy
    rw [hid y W hW]
    rfl
  · have hb : Λ.boxIn v = some U := by
      cases v with
      | root r => exact hv
      | step u s =>
          cases s with
          | dia =>
              change (if u = y then _ else none) = some U at hv
              have : u ≠ y := fun e => hvd (by rw [e])
              rw [if_neg this] at hv
              cases hv
          | box => exact hv
          | keep => exact hv
          | fst => exact hv
          | snd => exact hv
          | here => exact hv
    have e := Subst.dia_eq_box_mono (Δ₁ := Λ) θ y y v U ((Ctx.ref_nonproj _ hlp).trans hb)
    rw [Subst.at_nonproj _ hlp] at e
    rw [e, Subst.ren_box hid v U ((Ctx.ref_nonproj _ hlp).trans hb)]
    rfl

variable {Γ : Ctx} [Γ.Presented] {x : VarSymb} {X T : VarType}

/-- The content of `x` kept, in `x.keep`'s view. -/
abbrev Term.bdK (hF : ModalSys.Four = true) (hx : Γ.ref x = some (.VTypeDia X)) :=
  Term.shift (σ := σ) (Ctx.shifts_diaIn_keep hF Γ x)
    (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))

/-- The abstraction of a body along `◇_x`, one view in. -/
def WFF.liftS (hF : ModalSys.Four = true) (hx : Γ.ref x = some (.VTypeDia X))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF σ (Γ.boxIn.boxIn.insert (.bnd 0) (.VTypeProd X T)) 1 :=
  WFF.shift (Ctx.shifts_loop hF Γ (.VTypeProd X T))
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _) (WFF.bodyAbsA x hx φ)

/-- A view body is its abstraction read at the content and the slot. -/
theorem WFF.viewBody_readAt {A : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd X T)) 1}
    (hx : Γ.ref x = some (.VTypeDia X)) :
    WFF.viewBody ⟨X, hx⟩ (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)) A =
      WFF.readAt (Λ := Γ.boxIn) ((Ctx.le_boxIn_diaIn Γ x).trans
          (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T))
        ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T)
        (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T)
            (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)))
          (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) T))) A := by
  unfold WFF.viewBody WFF.bodyRepl WFF.readAt
  dsimp only [OutLeg.lift]
  rw [WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ A
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : VarType.VTypeProd X T = U := by simpa [Ctx.insert] using hv
    rw [Subst.set_root]
    change SubE.Sim _ _ (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _)
    rw [if_pos rfl]
    exact .refl _
  · change SubE.Sim U (if v = _ then _ else SubE.ren v) (if v = _ then _ else SubE.ren v)
    rw [if_neg hvr]
    exact .refl _

/-- ⭐A body along `◇_x` read at a term is its abstraction read at the content and the term. -/
theorem WFF.read_body (hx : Γ.ref x = some (.VTypeDia X))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {Ω : Ctx} [Ω.NoSlots] (h : (Γ.diaIn x).Le Ω)
    {a : Ann T} (t : Term σ Ω T a) :
    WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (h.insert (.bnd 0) T) φ) =
      WFF.readAt ((Ctx.le_boxIn_diaIn Γ x).trans h) Ctx.NoSlots.slots
        (Term.pair (Term.mono h (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))) t)
        (WFF.bodyAbsA x hx φ) := by
  have hb := WFF.viewBody_bodyAbsA x hx φ
  rw [WFF.viewBody_readAt hx] at hb
  have hr := (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).rootFresh (le_refl 0)
  have hrΩ := (Ctx.NoSlots.slots (Γ := Ω)).rootFresh (le_refl 0)
  have hO : Subst.Ok ((Γ.diaIn x).insert (.bnd 0) T) (Subst.single (σ := σ) (.bnd 0) (.tm t)) :=
    Subst.ok_single h rfl
  have hC : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm t)) ((Γ.diaIn x).insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm t)) := Subst.coh_single hr h rfl
  have hs₁ := (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T
  have key := WFF.subst_readAt (Λ := Γ.boxIn) (Ω₂ := Ω) ((Ctx.le_boxIn_diaIn Γ x).trans
      (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T))
    ((Ctx.le_boxIn_diaIn Γ x).trans h) hs₁ Ctx.NoSlots.slots
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T)
        (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)))
      (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) T)))
    (WFF.bodyAbsA x hx φ) (Subst.single (.bnd 0) (.tm t)) hO hC
    (fun v W hv => Subst.single_at_ne (Ctx.ref_rt_ne (Ctx.RootFresh.boxIn
      ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0))) hv))
  unfold WFF.instantiate WFF.substRoot
  rw [WFF.subst_mono]
  refine (congrArg (fun z => WFF.subst _ _ hO hC hs₁ Ctx.NoSlots.slots z) hb.symm).trans
    (key.trans (WFF.readAt_congr _ _ (sig_pair ?_ ?_) _))
  · rw [Term.subst_mono]
    exact Term.subst_ren h _ _ _ (fun v W hv => Subst.single_at_ne (Ctx.ref_rt_ne hr hv)) _
  · exact Term.subst_eta_tm _ hO hC T (.root (.bnd 0)) _ t (Subst.at_single_root _ _)

/-- ⭐The body the `□` lift runs on: `◇_{x.keep}`, at `x.keep`'s content and the slot kept, of the
    body's abstraction one view in.  At a world of `x`'s extent it says the body holds there. -/
def WFF.liftPos (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) T) 1 :=
  have hV : Γ.boxIn.Le (Γ.boxIn.insert (.bnd 0) T) :=
    Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root T
  have hk₀ : Γ.boxIn.ref (.step x .keep) = some (.VTypeDia X) := Ctx.ref_keep_of' hF hx rfl
  .dia (.step x .keep) ⟨X, hV.ref hk₀⟩
    (WFF.readAt (Λ := Γ.boxIn.boxIn) (hV.boxIn.trans (Ctx.le_boxIn_diaIn _ _))
      (((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T).diaIn _)
      (Term.pair (Term.mono (hV.diaIn _) (Term.bdK hF hx))
        (Term.mono (Ctx.le_boxIn_diaIn _ _) (Term.eta (.step (.root (.bnd 0)) .keep) T
          (Ctx.ref_keep_of' hF (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T) hk))))
      (WFF.liftS hF hx φ))

/-- ⭐`liftPos` read at an address: `◇_{x.keep}` at the content and the address kept. -/
theorem WFF.read_liftPos (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {Ω : Ctx}
    [Ω.NoSlots] (h : Γ.boxIn.Le Ω) (w : VarSymb) (hw : Ω.ref w = some T) :
    WFF.instantiate Ctx.NoSlots.slots (Term.eta w T hw)
        (WFF.mono (h.insert (.bnd 0) T) (WFF.liftPos hF hk hx φ)) =
      .dia (.step x .keep) ⟨X, h.ref (Ctx.ref_keep_of' hF hx rfl)⟩
        (WFF.readAt (Λ := Γ.boxIn.boxIn) (h.boxIn.trans (Ctx.le_boxIn_diaIn _ _))
          Ctx.NoSlots.slots
          (Term.pair (Term.mono (h.diaIn _) (Term.bdK hF hx))
            (Term.mono (Ctx.le_boxIn_diaIn _ _)
              (Term.eta (.step w .keep) T (Ctx.ref_keep_of' hF hw hk))))
          (WFF.liftS hF hx φ)) := by
  have hr := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  have hO : Subst.Ok (Γ.boxIn.insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))) := Subst.ok_single h rfl
  have hC : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.eta (σ := σ) w T hw)))
      (Γ.boxIn.insert (.bnd 0) T) (Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))) :=
    Subst.coh_single hr h rfl
  have hid : ∀ v U, Γ.boxIn.ref v = some U →
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))).at v = .ren v :=
    fun _ _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hr hv)
  have hk₀ : Γ.boxIn.ref (.step x .keep) = some (.VTypeDia X) := Ctx.ref_keep_of' hF hx rfl
  have hV : Γ.boxIn.Le (Γ.boxIn.insert (.bnd 0) T) := Ctx.le_insert hr.root T
  have hι : Subst.singleIdx (.bnd 0) (.tm (Term.eta (σ := σ) w T hw)) (.step x .keep) =
      .step x .keep := if_neg (Ctx.ref_rt_ne hr hk₀)
  have hxI : ∃ Y, (Γ.boxIn.insert (.bnd 0) T).ref (.step x .keep) = some (.VTypeDia Y) :=
    ⟨X, hV.ref hk₀⟩
  have hkey : ((Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))).at
      (.step x .keep)).idxAlong [] = .step x .keep := by
    rw [hid _ _ hk₀]
    rfl
  have hθy := Subst.ok_dia hO hxI hkey
  have hcy : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.eta (σ := σ) w T hw)))
      ((Γ.boxIn.insert (.bnd 0) T).diaIn (.step x .keep))
      ((Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))).dia (.step x .keep)
        (.step x .keep)) := by
    have := Subst.coh_dia hO hC hxI
    rwa [hι] at this
  have hfix : ∀ v U, Γ.boxIn.boxIn.ref v = some U →
      ((Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))).dia (.step x .keep)
        (.step x .keep)).at v = .ren v := by
    intro v U hv
    rw [Subst.dia_eq_box_mono (Δ₁ := Γ.boxIn) _ _ _ v U hv, Subst.ren_box hid v U hv]
    rfl
  have hreadK : (Γ.boxIn.insert (.bnd 0) T).boxIn.ref (.step (.root (.bnd 0)) .keep) = some T :=
    Ctx.ref_keep_of' hF (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T) hk
  have hsK : ((Subst.single (σ := σ) (.bnd 0) (.tm (Term.eta w T hw))).dia (.step x .keep)
      (.step x .keep)).at (.step (.root (.bnd 0)) .keep) =
      .tm (Term.mono (Ctx.le_boxIn_diaIn _ _)
        (Term.eta (.step w .keep) T (Ctx.ref_keep_of' hF hw hk))) := by
    rw [Subst.dia_eq_box_mono (Δ₁ := Γ.boxIn.insert (.bnd 0) T) _ _ _ _ T hreadK,
      Subst.box_at_keep, Subst.at_single_root, SubE.keepE_eta_of hF hw hk]
    rfl
  unfold WFF.instantiate WFF.substRoot
  rw [WFF.subst_mono (h.insert (.bnd 0) T) _ _ _ ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T)]
  unfold WFF.liftPos
  refine (WFF.subst_dia _ _ _ ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) Ctx.NoSlots.slots hxI
    (.step x .keep) hι ⟨X, h.ref hk₀⟩ hθy hcy Ctx.NoSlots.slots _).trans ?_
  refine congrArg (WFF.dia _ _) ?_
  refine (WFF.subst_readAt _ (h.boxIn.trans (Ctx.le_boxIn_diaIn _ _)) _ _ _ _ _ hθy hcy
    hfix).trans (WFF.readAt_congr _ _ (sig_pair ?_ ?_) _)
  · rw [Term.subst_mono]
    exact Term.subst_ren (h.diaIn _) _ _ _ (dia_at_ren hid) _
  · rw [Term.subst_mono]
    exact Term.subst_eta_tm _ _ _ T _ _ _ hsK

theorem Term.sig_subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {U : VarType} {a a' : Ann U}
    {s : Term σ Γ U a} {t : Term σ Γ U a'} (e : (⟨a, s⟩ : Σ c, Term σ Γ U c) = ⟨a', t⟩) :
    (⟨_, Term.subst ι θ hθ hc s⟩ : Σ c, Term σ Δ U c) = ⟨_, Term.subst ι θ hθ hc t⟩ := by
  cases e
  rfl

/-- The world a body along `◇_x` is opened in. -/
abbrev posK (Γ : Ctx) (x : VarSymb) (T : VarType) (c : ℕ) : Ctx :=
  (Γ.diaIn x).insert (.free c) T

/-- The hole formula `Proof.here_intro` is applied to: the abstraction one view in, at the hole and
    `c` kept. -/
def WFF.liftψ (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ}
    (hc : (Γ.diaIn x).RootFresh (.free c)) :
    WFF σ ((posK Γ x T c).boxIn.insert (.bnd 0) X) 1 :=
  WFF.readAt (Λ := Γ.boxIn.boxIn)
    (((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).boxIn.trans
      (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (posK Γ x T c).boxIn)).root X))
    ((Ctx.NoSlots.slots (Γ := (posK Γ x T c).boxIn)).insert X)
    (Term.pair (Term.eta (.root (.bnd 0)) X (Ctx.ref_insert_root _ (.bnd 0) X))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (posK Γ x T c).boxIn)).root X)
        (Term.eta (.step (.root (.free c)) .keep) T
          (Ctx.ref_keep_of' hF (Ctx.ref_insert_root (Γ.diaIn x) (.free c) T) hk))))
    (WFF.liftS hF hx φ)

/-- ⭐The hole formula read here, at `x`'s content, is the body at `c`. -/
theorem WFF.hereRead_liftψ (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hk : T.keepable = true) (hx : Γ.ref x = some (.VTypeDia X))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ}
    (hc : (Γ.diaIn x).RootFresh (.free c)) :
    WFF.hereRead hT (Term.mono (Ctx.le_insert hc.root T)
        (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))) (WFF.liftψ hF hk hx φ hc) =
      WFF.openFree c hc Ctx.NoSlots.slots φ := by
  have hrV := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  have e₀ : WFF.collapse ((Ctx.collapses_boxIn_self hT Γ.boxIn).insert hrV (.VTypeProd X T))
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert _) (WFF.liftS hF hx φ) =
      WFF.bodyAbsA x hx φ := by
    have := WFF.collapse_shift_same (Ctx.shifts_loop hF Γ (.VTypeProd X T))
      ((Ctx.collapses_boxIn_self hT Γ.boxIn).insert hrV _) (Ctx.Le.refl _)
      ((Ctx.shiftCollapseId_keepOnly (keepOnly_of hT hF) Γ).insert _ _)
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _)
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert _) (WFF.bodyAbsA x hx φ)
    rwa [WFF.mono_refl] at this
  have hK := Ctx.le_insert hc.root T
  have hVK : Γ.boxIn.Le (posK Γ x T c) := (Ctx.le_boxIn_diaIn Γ x).trans hK
  have hr' := (Ctx.NoSlots.slots (Γ := posK Γ x T c)).rootFresh (le_refl 0)
  have hrB := (Ctx.NoSlots.slots (Γ := (posK Γ x T c).boxIn)).rootFresh (le_refl 0)
  have hins := Ctx.le_insert hr'.root X
  have hinsB := Ctx.le_insert hrB.root X
  have hle : Γ.boxIn.boxIn.Le ((posK Γ x T c).boxIn.insert (.bnd 0) X) := hVK.boxIn.trans hinsB
  have hO : Subst.Ok ((posK Γ x T c).insert (.bnd 0) X) (Subst.single (σ := σ) (.bnd 0) (.tm
      (Term.mono hK (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))))) :=
    Subst.ok_single (Ctx.Le.refl _) rfl
  have hC := Subst.coh_single (σ := σ) (e := .tm
      (Term.mono hK (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)))) hr' (Ctx.Le.refl _) rfl
  have hid : ∀ v U, (posK Γ x T c).ref v = some U → (Subst.single (σ := σ) (.bnd 0) (.tm
      (Term.mono hK (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))))).at v = .ren v :=
    fun _ _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hr' hv)
  have key₁ := WFF.collapse_readAt (Ctx.collapses_boxIn_self hT Γ.boxIn)
    ((Ctx.collapses_boxIn_self hT (posK Γ x T c)).insert hrB X) hle (hVK.trans hins)
    ((Ctx.NoSlots.slots (Γ := (posK Γ x T c).boxIn)).insert X)
    ((Ctx.NoSlots.slots (Γ := posK Γ x T c)).insert X)
    (Term.pair (Term.eta (.root (.bnd 0)) X (Ctx.ref_insert_root _ (.bnd 0) X))
      (Term.mono hinsB (Term.eta (.step (.root (.free c)) .keep) T
        (Ctx.ref_keep_of' hF (Ctx.ref_insert_root (Γ.diaIn x) (.free c) T) hk))))
    (WFF.liftS hF hx φ)
  rw [e₀] at key₁
  rw [← WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots Ctx.NoSlots.slots φ,
    WFF.read_body hx φ hK]
  unfold WFF.hereRead WFF.liftψ WFF.instantiate WFF.substRoot
  refine (congrArg (fun z => WFF.subst _ _ hO hC _ _ z) key₁).trans
    ((WFF.subst_readAt (Λ := Γ.boxIn) (Ω₂ := posK Γ x T c) (hVK.trans hins) hVK _
      Ctx.NoSlots.slots _ (WFF.bodyAbsA x hx φ) _ hO hC
      (fun v U hv => hid v U (hVK.ref hv))).trans ?_)
  refine WFF.readAt_congr _ _ (sig_pair ?_ ?_) _
  · refine (Term.sig_subst _ hO hC (Term.collapse_eta _ (.root (.bnd 0)) X _)).trans ?_
    exact Term.subst_eta_tm _ hO hC X (.root (.bnd 0)) _ _ (Subst.at_single_root _ _)
  · rw [Term.collapse_mono (Ctx.collapses_boxIn_self hT (posK Γ x T c)) _ hinsB hins,
      Term.subst_mono]
    refine (Term.sig_subst _ _ _ ((Term.collapse_eta _ _ _ _).trans
      (Term.eta_congr VarSymb.collapse_keep_zero _ _
        (Ctx.ref_insert_root (Γ.diaIn x) (.free c) T)))).trans ?_
    refine (Term.subst_ren (Ctx.Le.refl _) _ _ _ hid _).trans ?_
    exact congrArg (Sigma.mk _) (Term.mono_refl _ _)

/-- ⭐The hole formula read along `x.keep`, at its content, is `liftPos` at `c`. -/
theorem WFF.viewRead_liftψ (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ}
    (hc : (Γ.diaIn x).RootFresh (.free c)) :
    WFF.viewReadTm (x := .step x .keep)
        (Term.mono (((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).diaIn _)
          (Term.bdK (σ := σ) hF hx)) (WFF.liftψ hF hk hx φ hc) =
      WFF.readAt (Λ := Γ.boxIn.boxIn) (((Ctx.le_boxIn_diaIn Γ x).trans
          (Ctx.le_insert hc.root T)).boxIn.trans (Ctx.le_boxIn_diaIn _ _)) Ctx.NoSlots.slots
        (Term.pair (Term.mono (((Ctx.le_boxIn_diaIn Γ x).trans
            (Ctx.le_insert hc.root T)).diaIn _) (Term.bdK hF hx))
          (Term.mono (Ctx.le_boxIn_diaIn _ _) (Term.eta (.step (.root (.free c)) .keep) T
            (Ctx.ref_keep_of' hF (Ctx.ref_insert_root (Γ.diaIn x) (.free c) T) hk))))
        (WFF.liftS hF hx φ) := by
  have hVK : Γ.boxIn.Le (posK Γ x T c) := (Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)
  have hrB := (Ctx.NoSlots.slots (Γ := (posK Γ x T c).boxIn)).rootFresh (le_refl 0)
  have hinsB := Ctx.le_insert hrB.root X
  have hl := Ctx.le_boxIn_diaIn (posK Γ x T c) (.step x .keep)
  have hO : Subst.Ok ((posK Γ x T c).boxIn.insert (.bnd 0) X)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.mono (hVK.diaIn _) (Term.bdK hF hx)))) :=
    Subst.ok_single hl rfl
  have hC := Subst.coh_single (σ := σ) (e := .tm (Term.mono (hVK.diaIn _) (Term.bdK hF hx)))
    hrB hl rfl
  have hid : ∀ v U, (posK Γ x T c).boxIn.ref v = some U → (Subst.single (σ := σ) (.bnd 0) (.tm
      (Term.mono (hVK.diaIn _) (Term.bdK hF hx)))).at v = .ren v :=
    fun _ _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hrB hv)
  unfold WFF.viewReadTm WFF.instantiate WFF.substRoot WFF.liftψ
  rw [WFF.subst_mono]
  refine (WFF.subst_readAt _ (hVK.boxIn.trans hl) _ _ _ _ _ hO hC
    (fun v U hv => hid v U (hVK.boxIn.ref hv))).trans (WFF.readAt_congr _ _ (sig_pair ?_ ?_) _)
  · exact Term.subst_eta_tm _ hO hC X (.root (.bnd 0)) _ _ (Subst.at_single_root _ _)
  · rw [Term.subst_mono]
    exact Term.subst_ren hl _ _ _ hid _

/-- ⭐**At a world of `x`'s extent, the body at `c` is `liftPos` at `c`**: `x` kept is realised
    there at its content (`here_keep`), so `Proof.here_intro` applies. -/
def Proof.far_pos (hT : ModalSys.T = true) (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ}
    (hc : (Γ.diaIn x).RootFresh (.free c)) :
    Proof σ (posK Γ x T c)
      [WFF.openFree c hc Ctx.NoSlots.slots φ,
        WFF.here hT (Term.diatm (.step x .keep)
            ⟨X, ((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).ref
              (Ctx.ref_keep_of' hF hx rfl)⟩
            (Term.mono (((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).diaIn _)
              (Term.bdK hF hx)))
          (Term.mono (Ctx.le_insert hc.root T)
            (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)))]
      (WFF.instantiate Ctx.NoSlots.slots
        (Term.eta (.root (.free c)) T (Ctx.ref_insert_root (Γ.diaIn x) (.free c) T))
        (WFF.mono (((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).insert (.bnd 0) T)
          (WFF.liftPos hF hk hx φ))) := by
  rw [WFF.read_liftPos hF hk hx φ ((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T))]
  rw [← WFF.viewRead_liftψ hF hk hx φ hc]
  refine Proof.here_intro hT (.step x .keep) _ _ _ _
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
  rw [WFF.hereRead_liftψ hT hF hk hx φ hc]
  exact Proof.lookup List.mem_cons_self

/-- Double negation, under a leg. -/
def Proof.neg_neg_intro {Ω : Ctx} (χ : WFF σ Ω 0) : Proof σ Ω [χ] χ.neg.neg :=
  Proof.imp_intro (Proof.imp_elim (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- `◇_x` of a `□`-view formula is a plain possibility. -/
def Proof.dia_forget {Ω : Ctx} {y : VarSymb} (hy : ∃ Y, Ω.ref y = some (.VTypeDia Y))
    (χ : WFF σ Ω.boxIn 0) {Δ : List (WFF σ Ω 0)}
    (p : Proof σ Ω Δ (.dia y hy (WFF.mono (Ctx.le_boxIn_diaIn Ω y) χ))) :
    Proof σ Ω Δ ((OutLeg.nec : OutLeg Ω).dia χ) := by
  refine Proof.imp_intro (Proof.imp_elim (Proof.ofSubset (fun z hz => ?_)
    (BArrow.Proof.box_boxx hy χ.neg))
    (Proof.leg_dia (.pos y hy) (Proof.neg_neg_intro _)
      (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) p)))
  rw [List.mem_singleton.mp hz]
  exact List.mem_cons_self

/-- `◇◇_{x.keep}(shift L) ⊢ ◇_x L`: `four_dia`'s `◇` form. -/
def Proof.four_dia_home {Ω : Ctx} [Ω.NoSlots] (hF : ModalSys.Four = true) {y : VarSymb}
    (hy : ∃ Y, Ω.ref y = some (.VTypeDia Y)) (L : WFF σ (Ω.diaIn y) 0) {Δ : List (WFF σ Ω 0)}
    (p : Proof σ Ω Δ ((OutLeg.nec : OutLeg Ω).dia (.dia (.step y .keep)
      (Ctx.exists_keep_dia hF hy)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Ω y) Ctx.NoSlots.slots L)))) :
    Proof σ Ω Δ (.dia y hy L) := by
  refine Proof.byContra (Proof.imp_elim (Proof.ofSubset
    (fun _ hx => List.mem_cons_of_mem _ hx) p) ?_)
  have h₁ : Proof σ Ω ((WFF.dia y hy L).neg :: Δ) (WFF.boxx y hy L.neg) :=
    Proof.ofSubset (fun z hz => by
      rw [List.mem_singleton.mp hz]
      exact List.mem_cons_self) (Proof.boxx_neg_of_not_dia y hy L)
  have h₂ := Proof.four_dia hF hy h₁
  have h₃ : Proof σ Ω.boxIn
      [WFF.boxx (.step y .keep) (Ctx.exists_keep_dia hF hy)
        (WFF.shift (Ctx.shifts_diaIn_keep hF Ω y) Ctx.NoSlots.slots L.neg)]
      (WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
        (WFF.shift (Ctx.shifts_diaIn_keep hF Ω y) Ctx.NoSlots.slots L)).neg :=
    Proof.imp_intro (Proof.imp_elim
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.leg_dia (.pos _ (Ctx.exists_keep_dia hF hy)) (Proof.neg_neg_intro _)
        (Proof.lookup List.mem_cons_self)))
  exact Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx)
    (Proof.imp_intro (Proof.K_box (Δ := [_]) h₃))) h₂

/-- The `Here` atom of `x` kept, in `x`'s view: `here_keep` at the content. -/
abbrev WFF.hereK (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hx : Γ.ref x = some (.VTypeDia X)) : WFF σ (Γ.diaIn x) 0 :=
  WFF.here hT (Term.mono (Ctx.le_boxIn_diaIn Γ x)
    (Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩) (Term.bdK hF hx)))
    (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))

/-- ⭐In `x`'s view, the body's `∃` gives `liftPos`'s, a formula of the `□` view. -/
def Proof.pos_view (hT : ModalSys.T = true) (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ}
    (hc : (Γ.diaIn x).RootFresh (.free c)) :
    Proof σ (Γ.diaIn x) [WFF.ex T φ, WFF.hereK hT hF hx]
      (WFF.mono (Ctx.le_boxIn_diaIn Γ x) (WFF.ex T (WFF.liftPos hF hk hx φ))) := by
  have e : WFF.weaken hc.root T (WFF.mono (Ctx.le_boxIn_diaIn Γ x)
      (WFF.ex T (WFF.liftPos hF hk hx φ))) =
      WFF.ex T (WFF.mono (((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).insert
        (.bnd 0) T) (WFF.liftPos hF hk hx φ)) := by
    unfold WFF.weaken
    rw [WFF.mono_mono]
    rfl
  have eH : WFF.here hT (Term.diatm (.step x .keep)
        ⟨X, ((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).ref
          (Ctx.ref_keep_of' hF hx rfl)⟩
        (Term.mono (((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hc.root T)).diaIn _)
          (Term.bdK hF hx)))
      (Term.mono (Ctx.le_insert hc.root T) (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))) =
      WFF.weaken hc.root T (WFF.hereK (σ := σ) hT hF hx) :=
    WFF.here_congr hT (congrArg (Sigma.mk _) (Term.mono_mono (Ctx.le_boxIn_diaIn Γ x)
      (Ctx.le_insert hc.root T) (Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
        (Term.bdK (σ := σ) hF hx))).symm) rfl
  refine Proof.ex_elim c T hc (φ := WFF.openFree c hc Ctx.NoSlots.slots φ)
    (Proof.conv (congrArg (WFF.ex T)
      (WFF.bindFree_openFree c hc (Ctx.NoSlots.slots (Γ := Γ.diaIn x)) φ).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  rw [e]
  refine Proof.ex_intro T (Term.eta (.root (.free c)) T
    (Ctx.ref_insert_root (Γ.diaIn x) (.free c) T)) ?_
  refine Proof.ofSubset (fun y hy => ?_) (Proof.far_pos hT hF hk hx φ hc)
  rcases List.mem_cons.mp hy with rfl | hy
  · exact List.mem_cons_self
  · rw [List.mem_singleton.mp hy, eH]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem
      (List.mem_cons_of_mem _ List.mem_cons_self))

/-- ⭐The plain possibility `liftPos` needs, from `◇_x`. -/
def Proof.pos_nec (hT : ModalSys.T = true) (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (hx' : ∃ X', Γ.ref x = some (.VTypeDia X'))
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ} (hc : Γ.RootFresh (.free c))
    {Δ : List (WFF σ Γ 0)} (p : Proof σ Γ Δ (.dia x hx' (WFF.ex T φ))) :
    Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.ex T (WFF.liftPos hF hk hx φ))) := by
  refine Proof.dia_forget hx' _ ?_
  have h₁ : Proof σ Γ [.dia x hx' (WFF.ex T φ), WFF.boxx x hx' (WFF.hereK (σ := σ) hT hF hx)]
      (.dia x hx' (WFF.mono (Ctx.le_boxIn_diaIn Γ x) (WFF.ex T (WFF.liftPos hF hk hx φ)))) :=
    Proof.castHyps (by simp) (Proof.K_dia (Δ₁ := []) (Δ₂ := [WFF.hereK (σ := σ) hT hF hx])
      (ψ := WFF.ex T φ) x hx'
      (Proof.castHyps (by simp) (Proof.pos_view hT hF hk hx φ (hc.diaIn x))))
  have h₂ : Proof σ Γ Δ (WFF.hereKeep hT hF x hx' (Term.eta (.step x .dia) X
      (Ctx.ref_diaIn_of hx))) := Proof.here_keep hT hF x hx' _
  have h₃ := Proof.imp_intro (Proof.imp_intro h₁)
  exact Proof.imp_elim (Proof.imp_elim (Proof.ofSubset (fun _ hz => by cases hz) h₃) h₂) p

omit [Γ.Presented] [ModalSys] in
theorem VarType.tup_of_keepable [ModalSys] {T : VarType} (hk : T.keepable = true) :
    T.tup = true := by
  cases T <;> first | rfl | cases hk

/-- ⭐The body at a kept object, shifted, is `liftPos`'s reading at it. -/
theorem WFF.shift_read_body (hF : ModalSys.Four = true) (hk : T.keepable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) {c : ℕ}
    (hc : Γ.RootFresh (.free c))
    (hw : ((Γ.insert (.free c) T).diaIn x).ref (.step (.root (.free c)) .keep) = some T)
    (hw' : (Γ.insert (.free c) T).boxIn.ref (.step (.root (.free c)) .keep) = some T) :
    WFF.shift (Ctx.shifts_diaIn_keep hF (Γ.insert (.free c) T) x) Ctx.NoSlots.slots
        (WFF.instantiate Ctx.NoSlots.slots (Term.eta (.step (.root (.free c)) .keep) T hw)
          (WFF.mono (((Ctx.le_insert hc.root T).diaIn x).insert (.bnd 0) T) φ)) =
      WFF.readAt (Λ := Γ.boxIn.boxIn)
        ((Ctx.le_insert hc.root T).boxIn.boxIn.trans (Ctx.le_boxIn_diaIn _ _)) Ctx.NoSlots.slots
        (Term.pair (Term.mono ((Ctx.le_insert hc.root T).boxIn.diaIn _) (Term.bdK hF hx))
          (Term.mono (Ctx.le_boxIn_diaIn _ _)
            (Term.eta (.step (.step (.root (.free c)) .keep) .keep) T
              (Ctx.ref_keep_of' hF hw' hk))))
        (WFF.liftS hF hx φ) := by
  have h := Ctx.le_insert hc.root T
  rw [WFF.read_body hx φ (h.diaIn x)]
  unfold WFF.liftS
  refine (WFF.shift_readAt (Ctx.shifts_boxIn_boxIn hF Γ)
    (Ctx.shifts_diaIn_keep hF (Γ.insert (.free c) T) x) _
    (h.boxIn.boxIn.trans (Ctx.le_boxIn_diaIn _ _)) _ _ _ _).trans
    (WFF.readAt_congr _ _ (sig_pair ?_ ?_) _)
  · exact congrArg (Sigma.mk _) (Term.shift_mono (Ctx.shifts_diaIn_keep hF Γ x) _ (h.diaIn x)
      (h.boxIn.diaIn _) _)
  · exact (Term.shift_eta _ _ T _).trans ((Term.eta_congr (VarSymb.shift_level_zero rfl) T _
      ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_keep_of' hF hw' hk))).trans
        (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm))

/-- ⭐⭐**`keep_lift` along `◇_x` is derivable under T, 4 and 5**: `liftPos` carries the body through
    the lift along `□`, and `four_dia` brings it back into `x`'s extent. -/
def Proof.keep_lift_posT (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) (hl : T.liftable = true)
    (hx : Γ.ref x = some (.VTypeDia X)) (hx' : ∃ X', Γ.ref x = some (.VTypeDia X'))
    {Δ : List (WFF σ Γ 0)} (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) (c : ℕ)
    (hc : Γ.RootFresh (.free c)) {ψ : WFF σ Γ 0}
    (p : Proof σ Γ Δ (.dia x hx' (WFF.ex T φ)))
    (q : Proof σ (Γ.insert (.free c) T)
      (WFF.liftRead hF hl (.pos x hx') hc φ :: Δ.map (WFF.weaken hc.root T))
      (ψ.weaken hc.root T)) :
    Proof σ Γ Δ ψ := by
  have hk := VarType.keepable_of_liftable hl
  have h := Ctx.le_insert hc.root T
  have hw' : (Γ.insert (.free c) T).boxIn.ref (.step (.root (.free c)) .keep) = some T :=
    Ctx.ref_keep_of' hF (Ctx.ref_insert_root Γ (.free c) T) hk
  have hw := (Ctx.le_boxIn_diaIn (Γ.insert (.free c) T) x).ref hw'
  have hx₁ : ∃ X', (Γ.insert (.free c) T).ref x = some (.VTypeDia X') :=
    hx'.imp fun _ hY => h.ref hY
  have e := WFF.read_liftPos hF hk hx φ h.boxIn (.step (.root (.free c)) .keep) hw'
  rw [← WFF.shift_read_body hF hk hx φ hc hw hw'] at e
  have d : Proof σ (Γ.insert (.free c) T)
      [WFF.liftRead hF hl (.nec : OutLeg Γ) hc (WFF.liftPos hF hk hx φ)]
      (WFF.liftRead hF hl (.pos x hx') hc φ) :=
    Proof.four_dia_home hF hx₁ _ (Proof.conv (congrArg (fun z => (WFF.box z.neg).neg) e)
      (Proof.lookup List.mem_cons_self))
  refine Proof.keep_lift_T hT hF hV hl (VarType.tup_of_keepable hk) (WFF.liftPos hF hk hx φ) c hc
    (Proof.pos_nec hT hF hk hx hx' φ hc p) ?_
  exact Proof.imp_elim (Proof.ofSubset (fun _ hz => List.mem_cons_of_mem _ hz) (Proof.imp_intro q))
    (Proof.ofSubset (fun z hz => by
      rw [List.mem_singleton.mp hz]
      exact List.mem_cons_self) d)

end LiftPos

end V12M
