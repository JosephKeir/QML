import QML.QML_v12m_RetLift
import QML.QML_v12m_GViewSubst

/-!
# QML v12m — 5 without T: the root's loop

KB5 and KDB5 (`docs/v12-modal-extensions.md`, "KB5 and KDB5: the root's loop").  With T off the
root joins the cluster by a self-edge, `u.keep ↦ u`, `u.box ↦` a late root.  Two facts make its
transfer consistent, and neither needs a new rule.

* ⭐`Proof.closed_T`, the base: with `□⊥` refuted, `□ψ ⊢ ψ` for closed `ψ`, by weak B and 4.  The
  only use of B.
* ⭐`Proof.loop_tup`, the step: what the new variable's reading says is reflected, by 5 and the
  lifts.  `WFF.loopHat` is a formula one view in with its slot kept, and `◇¬(□φ̂ → φ)` gives, by
  `Proof.keep_lift_tup`, `◇(□(shift Q) ∧ ¬Q)` for `Q` the body read at kept objects, which
  `five_box` refutes (`WFF.loopHat_read`).
-/

namespace V12M

variable [ModalSys]

open BArrow GArrow

section Closed

variable {σ : Signature}

/-- Shifting a closed formula leaves it alone. -/
theorem WFF.shift_closed (hF : ModalSys.Four = true) {l : List VarType}
    (ψ : WFF σ Ctx.empty 0) :
    WFF.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf l)) Ctx.NoSlots.slots
      (ψ.closed (ctxOf l).boxIn) = ψ.closed (ctxOf l).boxIn.boxIn := by
  have C := Ctx.shifts_boxIn_boxIn hF (ctxOf l)
  have e := WFF.subst_shift C Ctx.NoSlots.slots Ctx.NoSlots.slots (Subst.idS σ _) Subst.ok_idS
    Subst.coh_idS (Subst.atShift (Subst.idS σ _)) (Subst.ok_atShift C Subst.ok_idS)
    (Subst.coh_atShift C Subst.ok_idS Subst.coh_idS levels_boxIn_ctxOf) Ctx.NoSlots.slots
    (Subst.preShift_atShift _ _) (ψ.closed (ctxOf l).boxIn)
  rw [WFF.subst_id] at e
  exact e.trans (WFF.subst_mono_empty _ _ _ _ _ _ _ _)

/-- ⭐**Closed T** (B + 4): with `□⊥` refuted, `□ψ ⊢ ψ` for a closed `ψ`: `¬ψ ⊢ □◇¬ψ` and
    `□ψ ⊢ □□ψ` give `□⊥`. -/
def Proof.closed_T {l : List VarType} {Δ : List (WFF σ (ctxOf l) 0)} (hB : ModalSys.B = true)
    (hF : ModalSys.Four = true) (ψ : WFF σ Ctx.empty 0)
    (hne : Proof σ (ctxOf l) Δ (WFF.box (Γ := ctxOf l) .bot).neg)
    (h : Proof σ (ctxOf l) Δ (.box (ψ.closed _))) : Proof σ (ctxOf l) Δ (ψ.closed (ctxOf l)) := by
  refine Proof.byContra (Proof.imp_elim
    (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) hne) ?_)
  have hb : Proof σ (ctxOf l) ((ψ.closed (ctxOf l)).neg :: Δ)
      (.box (WFF.box (Γ := (ctxOf l).boxIn) ((ψ.neg).closed _).neg).neg) :=
    Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx)
      (Proof.imp_intro (Proof.B_box hB ψ.neg))) (Proof.lookup List.mem_cons_self)
  have h₄ : Proof σ (ctxOf l) ((ψ.closed (ctxOf l)).neg :: Δ)
      (.box (.box (ψ.closed (ctxOf l).boxIn.boxIn))) := by
    rw [← WFF.shift_closed hF ψ]
    exact Proof.four_box hF (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) h)
  have hn : Proof σ (ctxOf l).boxIn.boxIn [ψ.closed (ctxOf l).boxIn.boxIn]
      ((ψ.neg).closed (ctxOf l).boxIn.boxIn).neg :=
    Proof.imp_intro (Proof.imp_elim (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hk : Proof σ (ctxOf l).boxIn
      [(WFF.box (Γ := (ctxOf l).boxIn) ((ψ.neg).closed _).neg).neg,
        .box (ψ.closed (ctxOf l).boxIn.boxIn)] .bot :=
    Proof.imp_elim (Proof.lookup List.mem_cons_self)
      (Proof.ofSubset (fun _ hx => by
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
        subst hx
        exact List.mem_cons_of_mem _ List.mem_cons_self) (Proof.K_box hn))
  have hkb : Proof σ (ctxOf l) [.box (WFF.box (Γ := (ctxOf l).boxIn) ((ψ.neg).closed _).neg).neg,
      .box (.box (ψ.closed (ctxOf l).boxIn.boxIn))] (.box .bot) := Proof.K_box hk
  exact Proof.imp_elim (Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx)
    (Proof.imp_intro (Proof.imp_intro hkb))) h₄) hb

end Closed

section Step

variable {σ : Signature} {T : VarType}

/-- A kept η-term is the η-term of the kept address. -/
theorem SubE.keepE_eta_of {Δ : Ctx} (hF : ModalSys.Four = true) {w : VarSymb}
    (hw : Δ.ref w = some T) (hk : T.keepable = true) :
    (SubE.tm (Term.eta (σ := σ) w T hw)).keepE =
      SubE.tm (Term.eta (.step w .keep) T (Ctx.ref_keep_of' hF hw hk)) := by
  cases T with
  | VTypeBox A => exact SubE.keepE_eta hF hw
  | VTypeDia A => exact SubE.keepE_eta_dia hF hw
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd A B => cases hk

/-- `¬(A → B) ⊢ A`. -/
def Proof.of_neg_imp {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {A B : WFF σ Γ 0}
    (h : Proof σ Γ Δ (WFF.imp A B).neg) : Proof σ Γ Δ A :=
  Proof.byContra (Proof.imp_elim (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) h)
    (Proof.imp_intro (Proof.bot_elim B (Proof.imp_elim
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self)))))

/-- `¬□∀B ⊢ ◇∃¬B`. -/
def Proof.dia_ex_neg {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (B : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) (c : ℕ) (hc : Γ.boxIn.RootFresh (.free c))
    (h : Proof σ Γ Δ (WFF.box (.all T B)).neg) :
    Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (.ex T B.neg)) := by
  have r : Proof σ (Γ.boxIn.insert (.free c) T)
      ([(WFF.ex T B.neg).neg].map (WFF.weaken hc.root T))
      (WFF.openFree c hc Ctx.NoSlots.slots B) := by
    refine Proof.byContra (Proof.imp_elim
      (Proof.lookup (x := (WFF.weaken hc.root T (WFF.ex T B.neg).neg))
        (List.mem_cons_of_mem _ List.mem_cons_self)) ?_)
    refine Proof.ex_intro T (Term.eta (.root (.free c)) T (Ctx.ref_insert_root _ _ T)) ?_
    exact Proof.conv (WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots Ctx.NoSlots.slots
      B.neg).symm (Proof.lookup List.mem_cons_self)
  have r' := Proof.all_intro c T hc r
  rw [WFF.bindFree_openFree] at r'
  have hb : Proof σ Γ [WFF.box (WFF.ex T B.neg).neg] (.box (.all T B)) := Proof.K_box r'
  exact Proof.imp_intro (Proof.imp_elim (Proof.ofSubset (fun _ hx => List.mem_cons_of_mem _ hx) h)
    (Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx) (Proof.imp_intro hb))
      (Proof.lookup List.mem_cons_self)))

/-- `◇¬(□(shift Q) → Q)` is refuted: by `five_box`, `□Q`. -/
def Proof.five_refute {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hF : ModalSys.Four = true)
    (hV : ModalSys.Five = true) {P : WFF σ Γ.boxIn.boxIn 0} {Q : WFF σ Γ.boxIn 0}
    (hP : WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots Q = P)
    (h : Proof σ Γ Δ ((OutLeg.nec : OutLeg Γ).dia (WFF.imp (.box P) Q).neg)) :
    Proof σ Γ Δ .bot := by
  subst hP
  have h₁ : Proof σ Γ.boxIn [(WFF.imp (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ)
      Ctx.NoSlots.slots Q)) Q).neg] (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ)
      Ctx.NoSlots.slots Q)) := Proof.of_neg_imp (Proof.lookup List.mem_cons_self)
  have h₂ : Proof σ Γ Δ (.box Q) := Proof.five_box hF hV (Proof.leg_dia .nec h₁ h)
  have hk : Proof σ Γ.boxIn [Q] (WFF.imp (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ)
      Ctx.NoSlots.slots Q)) Q).neg.neg :=
    Proof.imp_intro (Proof.imp_elim (Proof.lookup List.mem_cons_self) (Proof.imp_intro
      (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  have hb : Proof σ Γ [.box Q] (.box (WFF.imp (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ)
      Ctx.NoSlots.slots Q)) Q).neg.neg) := Proof.K_box hk
  exact Proof.imp_elim h (Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx)
    (Proof.imp_intro hb)) h₂)

/-- Equal terms are `Sim`. -/
theorem SubE.Sim.of_sig {Δ : Ctx} {T : VarType} {a b : Ann T} {s : Term σ Δ T a}
    {t : Term σ Δ T b} (h : (⟨a, s⟩ : Σ c, Term σ Δ T c) = ⟨b, t⟩) (U : VarType) :
    SubE.Sim U (.tm s) (.tm t) := by
  cases h
  exact .refl _

/-! ## Tuples of kept objects -/

/-- The types of tuples of keepable objects. -/
def VarType.tup : VarType → Bool
  | .VTypeBox _ => true
  | .VTypeDia _ => true
  | .VTypeOne => true
  | .VTypeProd A B => VarType.tup A && VarType.tup B
  | .Var => false

/-- The keepable components of a variable of type `A`. -/
def VarType.kc : VarType → VarType
  | .Var => .VTypeOne
  | .VTypeOne => .VTypeOne
  | .VTypeProd A B => .VTypeProd (VarType.kc A) (VarType.kc B)
  | .VTypeBox A => .VTypeBox A
  | .VTypeDia A => .VTypeDia A

omit [ModalSys] in
theorem VarType.tup_kc : ∀ A : VarType, (VarType.kc A).tup = true
  | .Var => rfl
  | .VTypeOne => rfl
  | .VTypeBox _ => rfl
  | .VTypeDia _ => rfl
  | .VTypeProd A B => by
      change ((VarType.kc A).tup && (VarType.kc B).tup) = true
      rw [VarType.tup_kc A, VarType.tup_kc B]
      rfl

/-- The annotation of `Term.keepOf`. -/
def keepAnn : VarSymb → (T : VarType) → Ann T
  | _, .Var => .var
  | _, .VTypeOne => .one
  | w, .VTypeProd A B => .prod (keepAnn (.step w .fst) A) (keepAnn (.step w .snd) B)
  | w, .VTypeBox A => Ann.eta (.step w .keep) (.VTypeBox A)
  | w, .VTypeDia A => Ann.eta (.step w .keep) (.VTypeDia A)

/-- ⭐A tuple of objects, kept: the tuple of its components' `keep` steps. -/
def Term.keepOf (hF : ModalSys.Four = true) {Γ : Ctx} : (T : VarType) → T.tup = true →
    (w : VarSymb) → Γ.ref w = some T → Term σ Γ.boxIn T (keepAnn w T)
  | .VTypeOne, _, _, _ => .unit
  | .VTypeProd A B, ht, w, h =>
      have hAB : A.tup = true ∧ B.tup = true := by simpa [VarType.tup] using ht
      .pair (Term.keepOf hF A hAB.1 (.step w .fst) (Ctx.ref_fst_of h))
        (Term.keepOf hF B hAB.2 (.step w .snd) (Ctx.ref_snd_of h))
  | .VTypeBox A, _, w, h => Term.eta (.step w .keep) (.VTypeBox A) (Ctx.ref_keep_of' hF h rfl)
  | .VTypeDia A, _, w, h => Term.eta (.step w .keep) (.VTypeDia A) (Ctx.ref_keep_of' hF h rfl)

/-- A tuple of kept addresses. -/
inductive Term.Kept {σ : Signature} {Ω : Ctx} : {T : VarType} → {a : Ann T} → Term σ Ω T a → Prop
  | unit : Term.Kept .unit
  | pair {A B : VarType} {a : Ann A} {b : Ann B} {s : Term σ Ω A a} {t : Term σ Ω B b} :
      Term.Kept s → Term.Kept t → Term.Kept (.pair s t)
  | leaf {T : VarType} (hk : T.keepable = true) (x : VarSymb)
      (h : Ω.ref (.step x .keep) = some T) : Term.Kept (Term.eta (.step x .keep) T h)

/-- ⭐Under a substitution sending `w` to a tuple of kept addresses, `w` kept is the tuple
    shifted. -/
theorem Term.Kept.read (hF : ModalSys.Four = true) {Ω V : Ctx} {ι : VarSymb → VarSymb}
    (θ : Subst σ Ω) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) (D : Ctx.Shifts 0 Ω Ω.boxIn)
    {T : VarType} {a : Ann T} {t : Term σ Ω T a} (ht : Term.Kept t) :
    ∀ (hT : T.tup = true) (w : VarSymb) (h : V.ref w = some T), θ.at w = .tm t →
      (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        (Term.keepOf hF T hT w h)⟩ : Σ b, Term σ Ω.boxIn T b) = ⟨_, Term.shift D t⟩ := by
  induction ht with
  | unit =>
      intro _ _ _ _
      rfl
  | pair _ _ ihs iht =>
      intro hT w h hw
      refine sig_pair (ihs _ _ _ ?_) (iht _ _ _ ?_)
      · rw [Subst.at_proj _ _ rfl, hw]
        rfl
      · rw [Subst.at_proj _ _ rfl, hw]
        rfl
  | @leaf T hk x hx =>
      intro hT w h hw
      have e : θ.box.at (.step w .keep) =
          .tm (Term.eta (.step (.step x .keep) .keep) T (Ctx.ref_keep_of' hF hx hk)) := by
        rw [Subst.box_at_keep, hw, SubE.keepE_eta_of hF hx hk]
      have e' := (Term.shift_eta (σ := σ) D (.step x .keep) T hx).trans
        (Term.eta_congr (VarSymb.shift_level_zero rfl) T _ (Ctx.ref_keep_of' hF hx hk))
      cases T with
      | VTypeBox A => exact (Term.subst_eta_tm _ _ _ _ _ _ _ e).trans e'.symm
      | VTypeDia A => exact (Term.subst_eta_tm _ _ _ _ _ _ _ e).trans e'.symm
      | Var => cases hk
      | VTypeOne => cases hk
      | VTypeProd A B => cases hk

/-! ## The body of the step -/

theorem Ctx.shifts_loop (hF : ModalSys.Four = true) (Γ : Ctx) [Γ.NoSlots] (T : VarType) :
    Ctx.Shifts 0 (Γ.boxIn.insert (.bnd 0) T) (Γ.boxIn.boxIn.insert (.bnd 0) T) :=
  (Ctx.shifts_boxIn_boxIn hF Γ).insert ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) T

/-- ⭐`φ` one view in with its slot kept: the old items shifted, the slot `c″` read as `c″.keep`. -/
def WFF.loopHat {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (hT : T.tup = true)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) : WFF σ (Γ.boxIn.insert (.bnd 0) T).boxIn 1 :=
  have hle : Γ.boxIn.boxIn.Le (Γ.boxIn.insert (.bnd 0) T).boxIn :=
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root T).boxIn
  have hfr := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  WFF.subst (Subst.singleIdx (.bnd 0) (.tm (Term.keepOf hF T hT (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))))
    (Subst.single (.bnd 0) (.tm (Term.keepOf hF T hT (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))))
    (Subst.ok_single hle rfl) (Subst.coh_single hfr hle rfl)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert T)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T).boxIn
    (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ)

/-- ⭐**The slot read at a tuple of kept addresses**: `□φ̂` is `□(shift φ(t))`. -/
theorem WFF.loopHat_read {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (hF : ModalSys.Four = true)
    (hT : T.tup = true) (h : Γ.Le Γ') (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) {t₀ : Ann T}
    {t : Term σ Γ'.boxIn T t₀} (ht : Term.Kept t) :
    WFF.instantiate Ctx.NoSlots.slots t
      (WFF.mono (h.boxIn.insert (.bnd 0) T) (.box (WFF.loopHat hF hT φ))) =
      .box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ') Ctx.NoSlots.slots
        (WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (h.boxIn.insert (.bnd 0) T) φ))) := by
  have D := Ctx.shifts_boxIn_boxIn hF Γ'
  have hfr := (Ctx.NoSlots.slots (Γ := Γ'.boxIn)).rootFresh (le_refl 0)
  have hfr₂ := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  have hfr₁ := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  have hOk : Subst.Ok (Γ.boxIn.insert (.bnd 0) T) (Subst.single (σ := σ) (.bnd 0) (.tm t)) :=
    Subst.ok_single h.boxIn rfl
  have hCo : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm t)) (Γ.boxIn.insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm t)) := Subst.coh_single hfr₁ h.boxIn rfl
  have hOk₃ : Subst.Ok (Γ.boxIn.boxIn.insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.shift D t))) := Subst.ok_single h.boxIn.boxIn rfl
  have hCo₃ : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.shift D t)))
      (Γ.boxIn.boxIn.insert (.bnd 0) T)
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.shift D t))) :=
    Subst.coh_single hfr₂ h.boxIn.boxIn rfl
  have hid : ∀ w W, Γ.boxIn.ref w = some W →
      (Subst.single (σ := σ) (.bnd 0) (.tm t)).at w = .ren w :=
    fun _ _ hw => Subst.single_at_ne (Ctx.ref_rt_ne hfr₁ hw)
  refine congrArg WFF.box ((WFF.subst_mono _ _ _ _ _ _ _ _).trans
    ((WFF.subst_comp _ _ (Subst.single (.bnd 0) (.tm (Term.shift D t))) _ _ _ _ hOk₃ hCo₃
      _ _ _ ?_ _).trans (Eq.symm ((congrArg (WFF.shift D _) (WFF.subst_mono _ _ _ _ _ _ _ _)).trans
        (WFF.shift_subst (Ctx.shifts_loop hF Γ T) D _ hOk hCo _ hOk₃ hCo₃ _ _ _ _ ?_ φ)))))
  · refine Subst.sim_of ?_
    intro v U hl hv
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      have hU : T = U := by simpa [Ctx.insert] using hv
      subst hU
      have e := Term.Kept.read hF (Subst.single (.bnd 0) (.tm t)) hOk hCo D ht hT (.root (.bnd 0))
        (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T) (Subst.at_single_root _ _)
      change SubE.Sim T (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _)
        (SubE.comp _ _ _ (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _))
      rw [if_pos rfl, if_pos rfl]
      change SubE.Sim T _ (.tm (Term.subst _ _ _ _ _))
      rw [SubE.tm_eq_of_sig e]
      exact .refl _
    · have hv' : Γ.boxIn.boxIn v = some U := by
        have := hv
        simpa [Ctx.insert, hvr] using this
      change SubE.Sim U (if v = .root (.bnd 0) then _ else _)
        (SubE.comp _ _ _ (if v = .root (.bnd 0) then _ else _))
      rw [if_neg hvr, if_neg hvr]
      change SubE.Sim U _ (Subst.at _ v)
      rw [Subst.ren_box hid v U ((Ctx.ref_nonproj _ hl).trans hv')]
      exact .refl _
  · refine Subst.shiftCorr_of hOk ?_
    intro v U hl hv
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      change SubE.Sim U (Subst.single (σ := σ) (Δ := Γ'.boxIn.boxIn) (.bnd 0)
          (.tm (Term.shift D t)) (.root (.bnd 0)))
        (SubE.shift D (Subst.single (σ := σ) (Δ := Γ'.boxIn) (.bnd 0) (.tm t) (.root (.bnd 0))))
      unfold Subst.single
      rw [if_pos rfl, if_pos rfl]
      exact .refl _
    · have hv' : Γ.boxIn v = some U := by
        have := hv
        simpa [Ctx.insert, hvr] using this
      change SubE.Sim U _ (SubE.shift D (if v = .root (.bnd 0) then _ else _))
      rw [if_neg hvr, Subst.single_at_ne (r := .bnd 0) (e := .tm (Term.shift D t))
        (Ctx.ref_rt_ne hfr₂ (Ctx.shifts_boxIn_boxIn hF Γ v U ((Ctx.ref_nonproj _ hl).trans hv')))]
      exact .refl _

/-! ## Splitting a slot of pair type -/

section Pairs

variable {V : Ctx} [V.NoSlots] {X Y : VarType}

/-- Two slots. -/
abbrev twoCtx (V : Ctx) (X Y : VarType) : Ctx := (V.insert (.bnd 0) X).insert (.bnd 1) Y

omit [ModalSys] in
theorem two_le_one : (V.insert (.bnd 0) X).Le (twoCtx V X Y) :=
  Ctx.le_insert ((Ctx.NoSlots.slots (Γ := V)).insert X).root Y

omit [ModalSys] in
theorem two_le : V.Le (twoCtx V X Y) := (body_le X).trans two_le_one

theorem two_ref : (twoCtx V X Y).ref (.root (.bnd 0)) = some X :=
  two_le_one.ref (Ctx.ref_insert_root V (.bnd 0) X)

/-- The pair of the two slots. -/
def twoPair (V : Ctx) [V.NoSlots] (X Y : VarType) : Term σ (twoCtx V X Y) (.VTypeProd X Y)
    (.prod (Ann.eta (.root (.bnd 0)) X) (Ann.eta (.root (.bnd 1)) Y)) :=
  .pair (Term.eta (.root (.bnd 0)) X two_ref)
    (Term.eta (.root (.bnd 1)) Y (Ctx.ref_insert_root _ _ Y))

/-- A body about `p : X × Y` as a body about its two components. -/
def WFF.slotPair (ρ : WFF σ (V.insert (.bnd 0) (.VTypeProd X Y)) 1) : WFF σ (twoCtx V X Y) 2 :=
  WFF.subst (Subst.setIdx id (.bnd 0) (.tm (twoPair V X Y)))
    ((Subst.idS σ _).set (.bnd 0) (.tm (twoPair V X Y)))
    (Subst.ok_set (Subst.ok_idS_le two_le) rfl)
    (Subst.coh_set (Subst.ok_idS_le two_le) (Subst.coh_idS_le two_le)
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := V)).insert _) (((Ctx.NoSlots.slots (Γ := V)).insert X).insert Y) ρ

/-- The pair of a term and the slot. -/
abbrev slotTm {a₀ : Ann X} (a : Term σ V X a₀) (Y : VarType) :
    Term σ (V.insert (.bnd 0) Y) (.VTypeProd X Y) (.prod a₀ (Ann.eta (.root (.bnd 0)) Y)) :=
  .pair (Term.mono (body_le Y) a) (Term.eta (.root (.bnd 0)) Y (Ctx.ref_insert_root V (.bnd 0) Y))

/-- ⭐Filling the first component of a split slot. -/
theorem WFF.instantiate_ex_slotPair {V' : Ctx} [V'.NoSlots] (h : V.Le V')
    (ρ : WFF σ (V.insert (.bnd 0) (.VTypeProd X Y)) 1) {a₀ : Ann X} (a : Term σ V' X a₀) :
    WFF.instantiate Ctx.NoSlots.slots a (WFF.mono (h.insert (.bnd 0) X) (.ex Y (WFF.slotPair ρ))) =
      .ex Y (WFF.bodyRepl (slotTm a Y) (WFF.mono (h.insert (.bnd 0) _) ρ)) := by
  have hle : V.Le (V'.insert (.bnd 0) Y) := h.trans (body_le Y)
  have hfr := (Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)
  have hOk : Subst.Ok (V.insert (.bnd 0) (.VTypeProd X Y))
      ((Subst.idS σ (V'.insert (.bnd 0) Y)).set (.bnd 0) (.tm (slotTm a Y))) :=
    Subst.ok_set (Subst.ok_idS_le hle) rfl
  have hCo : Subst.Coh (Subst.setIdx id (.bnd 0) (.tm (slotTm a Y)))
      (V.insert (.bnd 0) (.VTypeProd X Y))
      ((Subst.idS σ (V'.insert (.bnd 0) Y)).set (.bnd 0) (.tm (slotTm a Y))) :=
    Subst.coh_set (Subst.ok_idS_le hle) (Subst.coh_idS_le hle) hfr rfl
  refine congrArg (WFF.ex Y) ((WFF.subst_mono _ _ _ _ _ _ _ _).trans
    ((WFF.subst_comp _ _ _ _ _ _ _ hOk hCo _ _ _ ?_ ρ).trans (WFF.subst_mono _ _ _ _ _ _ _ _).symm))
  refine Subst.sim_of ?_
  intro v U hl hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim _ ((Subst.idS σ _).set (.bnd 0) (.tm (slotTm a Y)) (.root (.bnd 0)))
      (SubE.comp _ _ _ ((Subst.idS σ _).set (.bnd 0) (.tm (twoPair V X Y)) (.root (.bnd 0))))
    rw [Subst.set_root, Subst.set_root]
    change SubE.Sim _ _ (.tm (Term.pair (Term.subst _ _ _ _ (Term.eta (.root (.bnd 0)) X two_ref))
      (Term.subst _ _ _ _ (Term.eta (.root (.bnd 1)) Y (Ctx.ref_insert_root _ _ Y)))))
    refine SubE.Sim.of_sig (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ (Term.mono (body_le Y) a) ?_)
      (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_insert_root V' (.bnd 0) Y) ?_)).symm _
    · change Subst.under _ _ _ _ _ (VarSymb.root (.bnd 0)) = _
      unfold Subst.under
      rw [if_neg (by simp), show Subst.single (.bnd 0) (.tm a) (.root (.bnd 0)) = .tm a from
        if_pos rfl]
      rfl
    · change Subst.under _ _ _ _ _ (VarSymb.root (.bnd 1)) = _
      unfold Subst.under
      exact if_pos rfl
  · have hv' : V.ref v = some U := by
      have := hv
      rw [Ctx.ref_nonproj _ hl]
      simpa [Ctx.insert, hvr] using this
    have hne : v ≠ .root (.bnd 1) := fun e => Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (Nat.zero_le 1)) hv' (by rw [e]; rfl)
    change SubE.Sim U ((Subst.idS σ _).set (.bnd 0) (.tm (slotTm a Y)) v)
      (SubE.comp _ _ _ ((Subst.idS σ _).set (.bnd 0) (.tm (twoPair V X Y)) v))
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim U _ (Subst.at _ v)
    rw [Subst.at_nonproj _ hl]
    change SubE.Sim U _ (if v = .root (.bnd 1) then _ else
      SubE.mono _ (Subst.single (.bnd 0) (.tm a) v))
    rw [if_neg hne, show Subst.single (.bnd 0) (.tm a) v = .ren v from if_neg hvr]
    exact .refl _

/-- ⭐Filling the second component of a split slot. -/
theorem WFF.instantiate_bodyRepl_pair {V' : Ctx} [V'.NoSlots] (h : V.Le V') {a₀ : Ann X}
    (a : Term σ V X a₀) (ρ : WFF σ (V.insert (.bnd 0) (.VTypeProd X Y)) 1) {b₀ : Ann Y}
    (b : Term σ V' Y b₀) :
    WFF.instantiate Ctx.NoSlots.slots b
      (WFF.mono (h.insert (.bnd 0) Y) (WFF.bodyRepl (slotTm a Y) ρ)) =
      WFF.instantiate Ctx.NoSlots.slots (Term.pair (Term.mono h a) b)
        (WFF.mono (h.insert (.bnd 0) _) ρ) := by
  have hfr := (Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)
  have hfr' := (Ctx.NoSlots.slots (Γ := V')).rootFresh (le_refl 0)
  have hOk : Subst.Ok (V.insert (.bnd 0) (.VTypeProd X Y))
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.pair (Term.mono h a) b))) :=
    Subst.ok_single h rfl
  have hCo : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.pair (Term.mono h a) b)))
      (V.insert (.bnd 0) (.VTypeProd X Y))
      (Subst.single (σ := σ) (.bnd 0) (.tm (Term.pair (Term.mono h a) b))) :=
    Subst.coh_single hfr h rfl
  refine (WFF.subst_mono _ _ _ _ _ _ _ _).trans
    ((WFF.subst_comp _ _ _ _ _ _ _ hOk hCo _ _ _ ?_ ρ).trans (WFF.subst_mono _ _ _ _ _ _ _ _).symm)
  refine Subst.sim_of ?_
  intro v U hl hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim _ (Subst.single (.bnd 0) (.tm (Term.pair (Term.mono h a) b)) (.root (.bnd 0)))
      (SubE.comp _ _ _ ((Subst.idS σ _).set (.bnd 0) (.tm (slotTm a Y)) (.root (.bnd 0))))
    rw [Subst.set_root, show Subst.single (.bnd 0) (.tm (Term.pair (Term.mono h a) b))
      (.root (.bnd 0)) = .tm (Term.pair (Term.mono h a) b) from if_pos rfl]
    change SubE.Sim _ _ (.tm (Term.pair (Term.subst _ _ _ _ (Term.mono (body_le Y) a))
      (Term.subst _ _ _ _ (Term.eta (.root (.bnd 0)) Y (Ctx.ref_insert_root V (.bnd 0) Y)))))
    refine SubE.Sim.of_sig (sig_pair ?_
      (Term.subst_eta_tm _ _ _ _ _ _ b (Subst.at_single_root _ _))).symm _
    rw [Term.subst_mono]
    exact Term.subst_ren h _ _ _ (fun v _ hv => Subst.single_at_ne (Ctx.ref_rt_ne hfr hv)) a
  · have hv' : V.ref v = some U := by
      have := hv
      rw [Ctx.ref_nonproj _ hl]
      simpa [Ctx.insert, hvr] using this
    change SubE.Sim U (Subst.single (.bnd 0) (.tm (Term.pair (Term.mono h a) b)) v)
      (SubE.comp _ _ _ ((Subst.idS σ _).set (.bnd 0) (.tm (slotTm a Y)) v))
    rw [Subst.set_ne _ _ hvr, show Subst.single (.bnd 0)
      (.tm (Term.pair (Term.mono h a) b)) v = .ren v from if_neg hvr]
    change SubE.Sim U _ (Subst.at _ v)
    rw [Subst.single_at_ne (Ctx.ref_rt_ne hfr hv')]
    exact .refl _

/-- `∃p : X × Y. ρ(p) ⊢ ∃a. ∃b. ρ(a, b)`. -/
def Proof.ex_slotPair (ρ : WFF σ (V.insert (.bnd 0) (.VTypeProd X Y)) 1) (u : ℕ)
    (hu : V.RootFresh (.free u)) : Proof σ V [.ex _ ρ] (.ex X (.ex Y (WFF.slotPair ρ))) := by
  have hL : V.Le (V.insert (.free u) (.VTypeProd X Y)) := Ctx.le_insert hu.root _
  have hr := Ctx.ref_insert_root V (.free u) (.VTypeProd X Y)
  have ha : (V.insert (.free u) (.VTypeProd X Y)).ref (.step (.root (.free u)) .fst) = some X :=
    Ctx.ref_fst_of hr
  have hb : (V.insert (.free u) (.VTypeProd X Y)).ref (.step (.root (.free u)) .snd) = some Y :=
    Ctx.ref_snd_of hr
  refine Proof.ex_elim u _ hu (φ := WFF.openFree u hu Ctx.NoSlots.slots ρ) ?_ ?_
  · rw [WFF.bindFree_openFree]
    exact Proof.lookup List.mem_cons_self
  refine Proof.ex_intro X (Term.eta _ X ha) (Proof.conv
    (WFF.instantiate_ex_slotPair hL ρ _).symm ?_)
  refine Proof.ex_intro Y (Term.eta _ Y hb) ?_
  have e := WFF.instantiate_bodyRepl_pair (Ctx.Le.refl _) (Term.eta _ X ha)
    (WFF.mono (hL.insert (.bnd 0) _) ρ) (Term.eta _ Y hb)
  rw [WFF.mono_refl, WFF.mono_refl, Term.mono_refl] at e
  rw [e]
  exact Proof.conv (WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots ρ).symm
    (Proof.lookup List.mem_cons_self)

/-- `∃p : 𝟙. ρ(p) ⊢ ρ(⋆)`. -/
def Proof.ex_one (ρ : WFF σ (V.insert (.bnd 0) .VTypeOne) 1) (u : ℕ)
    (hu : V.RootFresh (.free u)) :
    Proof σ V [.ex _ ρ] (WFF.instantiate Ctx.NoSlots.slots .unit ρ) := by
  refine Proof.ex_elim u _ hu (φ := WFF.openFree u hu Ctx.NoSlots.slots ρ) ?_ ?_
  · rw [WFF.bindFree_openFree]
    exact Proof.lookup List.mem_cons_self
  rw [show WFF.weaken hu.root .VTypeOne (WFF.instantiate Ctx.NoSlots.slots .unit ρ) = _ from
    WFF.mono_instantiate _ _ Ctx.NoSlots.slots _ ρ]
  exact Proof.conv (WFF.instantiate_eta_openFree u hu Ctx.NoSlots.slots Ctx.NoSlots.slots ρ).symm
    (Proof.lookup List.mem_cons_self)

end Pairs

theorem Term.Kept.mono {Ω Ω' : Ctx} (h : Ω.Le Ω') {T : VarType} {a : Ann T} {t : Term σ Ω T a}
    (ht : Term.Kept t) : Term.Kept (Term.mono h t) := by
  induction ht with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | leaf hk x hx =>
      rw [Term.mono_eta]
      exact .leaf hk x _

/-! ## The lift at a tuple -/

/-- What `keep_lift_tup` hands on: the possibility read at a tuple of kept objects, further on. -/
abbrev LiftGoal (σ : Signature) (T : VarType) (l : List VarType)
    (ρ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) : Type :=
  ∀ (l' : List VarType) (h : (ctxOf l).Le (ctxOf l')) (a : Ann T)
    (t : Term σ (ctxOf l').boxIn T a), Term.Kept t →
    Proof σ (ctxOf l') [(OutLeg.nec : OutLeg (ctxOf l')).dia
      (WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (h.boxIn.insert (.bnd 0) T) ρ))] .bot

/-- `keep_lift` at one object, refuting. -/
def Proof.keep_lift_leaf (hF : ModalSys.Four = true) (hl : T.liftableR = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} (ρ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1)
    (p : Proof σ (ctxOf l) Δ ((OutLeg.nec : OutLeg (ctxOf l)).dia (.ex T ρ)))
    (K : LiftGoal σ T l ρ) : Proof σ (ctxOf l) Δ .bot := by
  have hk := VarType.keepable_of_liftableR hl
  have hr := Ctx.ref_keep_of' hF (Ctx.ref_insert_root (ctxOf l) (.free l.length) T) hk
  refine Proof.keep_lift hF hl .nec ρ l.length (ctxOf_fresh le_rfl) (ψ := .bot) p ?_
  have q := K (T :: l) (ctxOf_le_append [T] l) _ (Term.eta _ T hr) (.leaf hk _ hr)
  exact Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx) (Proof.imp_intro q))
    (Proof.lookup List.mem_cons_self)

/-- ⭐**`keep_lift` at a tuple**, refuting: each keepable component in turn. -/
def Proof.keep_lift_tup (hF : ModalSys.Four = true) (hS : ModalSys.FourStrong = true)
    (hW : ModalSys.FourStrongW = true) : (T : VarType) → T.tup = true → {l : List VarType} →
    {Δ : List (WFF σ (ctxOf l) 0)} → (ρ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) →
    Proof σ (ctxOf l) Δ ((OutLeg.nec : OutLeg (ctxOf l)).dia (.ex T ρ)) → LiftGoal σ T l ρ →
    Proof σ (ctxOf l) Δ .bot
  | .VTypeBox A, _, _, _, ρ, p, K => Proof.keep_lift_leaf (T := .VTypeBox A) hF hS ρ p K
  | .VTypeDia A, _, _, _, ρ, p, K => Proof.keep_lift_leaf (T := .VTypeDia A) hF hW ρ p K
  | .VTypeOne, _, l, _, ρ, p, K => by
      have hc := (ctxOf_fresh (l := l) le_rfl).boxIn
      have q := K l (Ctx.Le.refl _) _ .unit .unit
      rw [WFF.mono_refl] at q
      exact Proof.imp_elim (Proof.ofSubset (fun _ hx => by cases hx) (Proof.imp_intro q))
        (Proof.leg_dia .nec (Proof.ex_one ρ l.length hc) p)
  | .VTypeProd X Y, ht, l, _, ρ, p, K => by
      have hXY : X.tup = true ∧ Y.tup = true := by simpa [VarType.tup] using ht
      have hc := (ctxOf_fresh (l := l) le_rfl).boxIn
      refine Proof.keep_lift_tup hF hS hW X hXY.1 (.ex Y (WFF.slotPair ρ))
        (Proof.leg_dia .nec (Proof.ex_slotPair ρ l.length hc) p) fun l₁ h₁ _ t₁ k₁ => ?_
      refine Proof.keep_lift_tup hF hS hW Y hXY.2
        (WFF.bodyRepl (slotTm t₁ Y) (WFF.mono (h₁.boxIn.insert (.bnd 0) _) ρ))
        (Proof.conv (congrArg (fun z => (OutLeg.nec : OutLeg (ctxOf l₁)).dia z)
          (WFF.instantiate_ex_slotPair h₁.boxIn ρ t₁)) (Proof.lookup List.mem_cons_self))
        fun l₂ h₂ _ t₂ k₂ => ?_
      have q := K l₂ (h₁.trans h₂) _ _ (.pair (k₁.mono h₂.boxIn) k₂)
      have e := WFF.instantiate_bodyRepl_pair h₂.boxIn t₁
        (WFF.mono (h₁.boxIn.insert (.bnd 0) _) ρ) t₂
      rw [WFF.mono_mono] at e
      rw [e]
      exact q

/-- ⭐**The loop's step** (5 and the lifts, no B, no D): `⊢ □∀c″. □φ̂(c″) → φ(c″)`.  Otherwise
    `◇¬(…)`, by `keep_lift_tup` at some tuple of kept objects `t`, against `five_box` at `φ(t)`:
    `φ̂(t)` is `φ(t)` shifted (`WFF.loopHat_read`). -/
def Proof.loop_tup (hF : ModalSys.Four = true) (hV : ModalSys.Five = true)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true) (hT : T.tup = true)
    {l : List VarType} {Δ : List (WFF σ (ctxOf l) 0)}
    (φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) :
    Proof σ (ctxOf l) Δ (.box (.all T (.imp (.box (WFF.loopHat hF hT φ)) φ))) := by
  refine Proof.byContra (Proof.keep_lift_tup hF hS hW T hT _ (Proof.dia_ex_neg _ l.length
    (ctxOf_fresh le_rfl).boxIn (Proof.lookup List.mem_cons_self)) fun l' h _ t ht => ?_)
  refine Proof.five_refute hF hV
    (Q := WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (h.boxIn.insert (.bnd 0) T) φ)) rfl
    (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  exact congrArg (fun z => (OutLeg.nec : OutLeg (ctxOf l')).dia z.neg)
    (congrArg₂ WFF.imp (WFF.loopHat_read hF hT h φ ht) rfl)

end Step

end V12M
