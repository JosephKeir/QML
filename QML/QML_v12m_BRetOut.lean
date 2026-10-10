import QML.QML_v12m_BRetTruthW

/-!
# QML v12m — B's canonical model: `ret` membership ⇒ truth (strong B, T off)

A returning possibility `◇[d ↦ t] Φ(d)` in a node's theory is made true by a returning successor
(docs §11.20).  The network makes successors for **obligations** `◇[d ↦ ⟨(), y⟩] Φ'(d)` valued at
a root `y` (`NetSt.mkRet`); a user atom becomes one by an alias `y` of `t` (`NetSt.mkAlias`,
whose alias formula at the atom's slot formula moves the value) and two hole maps
(`ret_map`): `□A → □(1 × (□A).bc)` on the object, `□(1 × (□A).bc) → □A` on the body.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Terms and bodies -/

omit [ModalSys.NoFour] in
/-- A substitution sending a variable to the η-expansion of another, at a type equal to its own:
    the η-expansion at its own type. -/
theorem Term.subst_eta_eta {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {T T' : VarType} (e : T' = T) {v : VarSymb}
    (hv : Γ.ref v = some T) {w : VarSymb} (hw : Δ.ref w = some T')
    (h : θ.at v = .tm (Term.eta w T' hw)) :
    (⟨_, Term.subst ι θ hθ hc (Term.eta v T hv)⟩ : Σ b, Term σ Δ T b) =
      ⟨_, Term.eta w T (hw.trans (congrArg some e))⟩ := by
  subst e
  exact Term.subst_eta_tm _ _ _ _ _ _ _ h

omit [ModalSys.NoFour] in
theorem SubE.tm_sig {Δ : Ctx} {T : VarType} {a a' : Ann T} {s : Term σ Δ T a}
    {s' : Term σ Δ T a'} (h : (⟨a, s⟩ : Σ b, Term σ Δ T b) = ⟨a', s'⟩) :
    (SubE.tm s : SubE σ Δ) = SubE.tm s' := by
  cases h
  rfl

omit [ModalSys.NoFour] in
theorem SubE.proj_snd_sig {Δ : Ctx} {A B : VarType} {c : Ann (.VTypeProd A B)}
    {H : Term σ Δ (.VTypeProd A B) c} {a : Ann A} {b : Ann B} {p : Term σ Δ A a}
    {q : Term σ Δ B b} (h : (⟨c, H⟩ : Σ e, Term σ Δ (.VTypeProd A B) e) = ⟨_, Term.pair p q⟩) :
    (SubE.tm H : SubE σ Δ).proj .snd = SubE.tm q := by
  cases h
  rfl

section Body

variable {V : Ctx} [V.NoSlots]

omit [ModalSys.NoFour] in
/-- ⭐Replacing a body's slot twice is replacing it by the composed hole term. -/
theorem WFF.bodyRepl_bodyRepl {A B C : VarType} {b : Ann B} {c : Ann C}
    (X : Term σ (Ctx.empty.insert (.bnd 0) A) B b) (Y : Term σ (Ctx.empty.insert (.bnd 0) B) C c)
    (Φ : WFF σ (V.insert (.bnd 0) C) 1) :
    WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) A) X)
        (WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) B) Y) Φ) =
      WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) A) (Term.holeAt X Y)) Φ := by
  unfold WFF.bodyRepl
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = C := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ (((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0)))
      ((((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))).comp _ _ _)
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (Eq.symm ?_)
    refine (Term.subst_closed_sig _ _ _ _ (Subst.set_root _ _ _) Y).trans ?_
    exact (Term.mono_holeAt_sig _ X Y).symm
  · change SubE.Sim T (((Subst.idS σ _).set (.bnd 0) _) v)
      ((((Subst.idS σ _).set (.bnd 0) _) v).comp _ _ _)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim T _ ((Subst.set _ _ _).at v)
    have hv' : V v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    rw [Subst.at_set_of_rt_ne _ _ (Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0))
      ((Ctx.ref_nonproj _ hlp).trans hv')), Subst.at_idS]
    exact .refl _

omit [ModalSys.NoFour] in
/-- Replacing a body's slot by its own η-expansion leaves it alone. -/
theorem WFF.bodyRepl_eta {A : VarType} (Φ : WFF σ (V.insert (.bnd 0) A) 1) :
    WFF.bodyRepl (Term.mono ((Ctx.empty_le V).insert (.bnd 0) A)
      (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ _ _))) Φ = Φ := by
  unfold WFF.bodyRepl
  refine (WFF.subst_congr _ (Subst.idS σ _) _ (Subst.ok_idS_le (Ctx.Le.refl _)) _
    (Subst.coh_idS_le (Ctx.Le.refl _)) _ _ ?_ Φ).trans
    ((WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (fun v _ _ => Subst.at_idS v) Φ).trans
      (WFF.mono_refl _ Φ))
  refine Subst.sim_of fun v T _ hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ (((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))) (.ren _)
    rw [Subst.set_root, Term.mono_eta]
    exact .eta_ren _ _
  · change SubE.Sim T (((Subst.idS σ _).set (.bnd 0) _) v) (.ren v)
    rw [Subst.set_ne _ _ hvr]
    exact .refl _

end Body

/-! ## The obligation's hole maps -/

section Obl

variable (hT : ModalSys.T = false) (A : VarType)
include hT

omit [ModalSys.NoFour] in
theorem oblS_ref : (Ctx.empty.insert (.bnd 0) A).ref (.root (.bnd 0)) =
    some (VarType.VTypeBox A).bc :=
  (Ctx.ref_insert_root _ _ _).trans (congrArg some (bc_box_noT hT A).symm)

/-- The object's map into the obligation: `z ↦ ⟨(), z⟩`, `z : A` read at `(□A).bc`. -/
def oblS : Term σ (Ctx.empty.insert (.bnd 0) A) (bcT [.VTypeBox A])
    (.prod .one (Ann.eta (.root (.bnd 0)) (VarType.VTypeBox A).bc)) :=
  Term.pair .unit (Term.eta (.root (.bnd 0)) _ (oblS_ref hT A))

omit [ModalSys.NoFour] in
theorem oblB_ref : ((Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT [.VTypeBox A]))).boxIn).ref
    (.step (VarSymb.root (.bnd 0)).inner .snd) = some A :=
  (Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))).trans
    (congrArg some (bc_box_noT hT A))

/-- The body's map back: `e ↦ □(e.box.snd)`. -/
def oblB : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT [.VTypeBox A]))) (.VTypeBox A)
    (.box (Ann.eta (.step (VarSymb.root (.bnd 0)).inner .snd) A)) :=
  Term.boxtm (Term.eta (.step (VarSymb.root (.bnd 0)).inner .snd) A (oblB_ref hT A))

/-- ⭐The two maps compose to the identity on the object: `□a ↦ □⟨(), a⟩ ↦ □a`. -/
theorem holeAt_hole_oblB :
    (⟨_, Term.holeAt (ShapeMap.hole (σ := σ) (oblS hT A)).obj.2 (oblB hT A)⟩ :
      Σ c, Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) (.VTypeBox A) c) =
      ⟨_, Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ _ _)⟩ := by
  have hin : ((Ctx.empty.insert (.bnd 0) (.VTypeBox A)).boxIn).ref (VarSymb.root (.bnd 0)).inner =
      some A := Ctx.ref_inner (Ctx.ref_insert_root _ _ _)
  have hH : (⟨_, Term.holeAt (Term.eta (VarSymb.root (.bnd 0)).inner A hin) (oblS hT A)⟩ :
      Σ c, Term σ _ (bcT [.VTypeBox A]) c) =
      ⟨_, Term.pair .unit (Term.eta (VarSymb.root (.bnd 0)).inner (VarType.VTypeBox A).bc
        (hin.trans (congrArg some (bc_box_noT hT A).symm)))⟩ := by
    unfold Term.holeAt oblS
    refine sig_pair rfl (Term.subst_eta_eta _ _ _ (bc_box_noT hT A).symm _ hin ?_)
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  unfold Term.holeAt oblB
  refine sig_boxtm ?_
  refine Term.subst_eta_eta _ _ _ (bc_box_noT hT A) _
    (hin.trans (congrArg some (bc_box_noT hT A).symm)) ?_
  rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ (by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl)]
  exact SubE.proj_snd_sig hH

omit [ModalSys.NoFour] in
/-- The object's map at a variable: `⟨(), y⟩`. -/
theorem holeRead_eta_oblS {Γ : Ctx} [Γ.NoSlots] {y : VarSymb} (hy : Γ.ref y = some A) :
    (⟨_, Term.holeRead (Term.eta y A hy) (oblS (σ := σ) hT A)⟩ :
      Σ c, Term σ Γ (bcT [.VTypeBox A]) c) =
      ⟨_, Term.pair .unit (Term.eta y (VarType.VTypeBox A).bc
        (hy.trans (congrArg some (bc_box_noT hT A).symm)))⟩ := by
  rw [Term.holeRead_eq_holeAt]
  unfold Term.holeAt oblS
  refine sig_pair rfl (Term.subst_eta_eta _ _ _ (bc_box_noT hT A).symm _ hy ?_)
  change Subst.single _ _ (.root (.bnd 0)) = _
  exact if_pos rfl

/-- ⭐⭐**A returning possibility at an alias becomes the obligation**: `◇[d ↦ y] Φ(d)`, `y : A` a
    root, gives `◇[e ↦ ⟨(), y⟩] Φ(□(e.box.snd))` — `ret_map` along the hole `z ↦ ⟨(), z⟩`, the two
    maps composing to the identity on the object (`holeAt_hole_oblB`). -/
theorem ret_obl (hS : ModalSys.BStrong = true) {l : List VarType}
    {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M) {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some A)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.ret hS (Term.eta (.root (.free y)) A hy) Φ ∈ M) :
    WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y)
        (retBackImg l A (hy.trans (congrArg some (bc_box_noT hT A).symm)))).2
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (oblB hT A)) Φ) ∈ M := by
  refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h, ⟨?_⟩⟩
  refine Proof.conv ?_ (Proof.ret_map hS .nec (S := .box A) (.hole (oblS hT A))
    (Term.eta (.root (.free y)) A hy)
    (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (oblB hT A)) Φ)
    (Proof.conv ?_ (Proof.lookup List.mem_cons_self)))
  · exact OutLeg.retS_congr hS .nec (.box (bcT [.VTypeBox A])) (holeRead_eta_oblS hT A hy) rfl
  · change WFF.ret hS _ Φ = WFF.ret hS _ (WFF.bodyRepl _ (WFF.bodyRepl _ Φ))
    rw [WFF.bodyRepl_bodyRepl]
    dsimp only [ShapeMap.liftObj]
    rw [WFF.bodyRepl_congr (sig_mono _ (holeAt_hole_oblB hT A)),
      WFF.bodyRepl_eta]

end Obl

/-- ⭐**A returning possibility moves to an alias**: the alias formulas at the atom's slot formula
    (`WFF.retSlot`) give `◇[d ↦ y] Φ` from `◇[d ↦ t] Φ` (`alias_interch`). -/
theorem ret_alias (hS : ModalSys.BStrong = true) {l lj : List VarType} {A : VarType}
    (hsuf : (A :: l) <:+ lj) {M : Set (WFF σ (ctxOf lj) 0)} (hM : Theory.IsMCS M) {a : Ann A}
    (t : Term σ (ctxOf l) A a)
    (hal : ∀ ψ, WFF.mono (ctxOf_le_of_suffix hsuf) (aliasFormula t ψ) ∈ M)
    (Φ : WFF σ ((ctxOf lj).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.ret hS (Term.mono (ctxOf_le_of_suffix hsuf) (Term.mono (aliasLe A l) t)) Φ ∈ M) :
    WFF.ret hS (Term.eta (.root (.free l.length)) A
      ((ctxOf_le_of_suffix hsuf).ref (ctxOf_ref_new A l))) Φ ∈ M := by
  have hi := (alias_interch hsuf hM t hal (WFF.retSlot hS (.box A) Φ)).mpr
  have h₁ := WFF.instantiate_retSlot (Γ := ctxOf lj) hS (.box A) Φ
    (Term.mono (ctxOf_le_of_suffix hsuf) (Term.mono (aliasLe A l) t))
  have h₂ := WFF.instantiate_retSlot (Γ := ctxOf lj) hS (.box A) Φ
    (Term.mono (ctxOf_le_of_suffix hsuf) (Term.eta (.root (.free l.length)) A
      (ctxOf_ref_new A l)))
  have := (congrArg (· ∈ M) h₂).mp (hi ((congrArg (· ∈ M) h₁).mpr h))
  exact (congrArg (· ∈ M) (OutLeg.retS_congr hS .nec (.box A)
    (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)) rfl)).mp this

end BArrow

end V12M
