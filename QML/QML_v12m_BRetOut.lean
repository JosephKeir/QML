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

/-- A term at a type equal to another, as a term of the other (a dependent pair). -/
def Term.castTy {Γ : Ctx} {T T' : VarType} : T' = T → {b : Ann T'} → Term σ Γ T' b →
    Σ c, Term σ Γ T c
  | rfl, _, s => ⟨_, s⟩

omit [ModalSys.NoFour] in
theorem Term.castTy_sig {Γ : Ctx} {T T' : VarType} (e : T' = T) {b b' : Ann T'}
    {s : Term σ Γ T' b} {s' : Term σ Γ T' b'} (h : (⟨b, s⟩ : Σ c, Term σ Γ T' c) = ⟨b', s'⟩) :
    Term.castTy e s = Term.castTy e s' := by
  cases h
  rfl

omit [ModalSys.NoFour] in
theorem Term.castTy_eta {Γ : Ctx} {T T' : VarType} (e : T' = T) {w : VarSymb}
    (hw : Γ.ref w = some T') :
    Term.castTy e (Term.eta (σ := σ) w T' hw) =
      ⟨_, Term.eta w T (hw.trans (congrArg some e))⟩ := by
  subst e
  rfl

omit [ModalSys.NoFour] in
theorem Term.subst_castTy {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {T T' : VarType} (e : T' = T) {b : Ann T'}
    (s : Term σ Γ T' b) :
    (⟨_, Term.subst ι θ hθ hc (Term.castTy e s).2⟩ : Σ c, Term σ Δ T c) =
      Term.castTy e (Term.subst ι θ hθ hc s) := by
  subst e
  rfl

omit [ModalSys.NoFour] in
/-- A substitution sending a variable to a term of a type equal to its own. -/
theorem Term.subst_eta_cast {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {T T' : VarType} (e : T' = T) {v : VarSymb}
    (hv : Γ.ref v = some T) {b : Ann T'} {s : Term σ Δ T' b} (h : θ.at v = .tm s) :
    (⟨_, Term.subst ι θ hθ hc (Term.eta v T hv)⟩ : Σ c, Term σ Δ T c) = Term.castTy e s := by
  subst e
  exact Term.subst_eta_tm _ _ _ _ _ _ _ h

omit [ModalSys.NoFour] in
theorem Term.subst_sig_congr {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {T : VarType} {a a' : Ann T}
    {t : Term σ Γ T a} {t' : Term σ Γ T a'} (h : (⟨a, t⟩ : Σ c, Term σ Γ T c) = ⟨a', t'⟩) :
    (⟨_, Term.subst ι θ hθ hc t⟩ : Σ c, Term σ Δ T c) = ⟨_, Term.subst ι θ hθ hc t'⟩ := by
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
theorem ret_obl (hS : ModalSys.BStrong = true) {l : List VarType} (O : OutLeg (ctxOf l))
    {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.IsMCS M) {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some A)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : O.ret hS (Term.eta (.root (.free y)) A hy) Φ ∈ M) :
    O.ret hS (tupImgT [.VTypeBox A] (fun _ => y)
        (retBackImg l A (hy.trans (congrArg some (bc_box_noT hT A).symm)))).2
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (oblB hT A)) Φ) ∈ M := by
  refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h, ⟨?_⟩⟩
  refine Proof.conv ?_ (Proof.ret_map hS O (S := .box A) (.hole (oblS hT A))
    (Term.eta (.root (.free y)) A hy)
    (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (oblB hT A)) Φ)
    (Proof.conv ?_ (Proof.lookup List.mem_cons_self)))
  · exact OutLeg.retS_congr hS O (.box (bcT [.VTypeBox A])) (holeRead_eta_oblS hT A hy) rfl
  · change O.ret hS _ Φ = O.ret hS _ (WFF.bodyRepl _ (WFF.bodyRepl _ Φ))
    rw [WFF.bodyRepl_bodyRepl]
    dsimp only [ShapeMap.liftObj]
    rw [WFF.bodyRepl_congr (sig_mono _ (holeAt_hole_oblB hT A)),
      WFF.bodyRepl_eta]

/-- The obligation's body read at the committed root `c` of the child: the object `□g` with
    `g = (c's item read at (□A).bc) : A`. -/
def oblRead {lk : List VarType} (hcl : [VarType.VTypeBox A] <:+ lk) :
    Σ b, Term σ (ctxOf lk).boxIn A b :=
  ⟨_, Term.subst _ (Subst.single (.bnd 0) (.tm (Term.boxtm (Term.mono
      (ctxOf_le_of_suffix hcl).boxIn (tupT [.VTypeBox A]).2)))).box
    (Subst.ok_box (Subst.ok_single (Ctx.empty_le _) rfl))
    (Subst.coh_box (Subst.ok_single (Ctx.empty_le _) rfl)
      (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le _) rfl))
    (Term.eta (.step (VarSymb.root (.bnd 0)).inner .snd) A (oblB_ref hT A))⟩

theorem holeAt_oblB {lk : List VarType} (hcl : [VarType.VTypeBox A] <:+ lk) :
    Term.holeAt (Term.boxtm (Term.mono (ctxOf_le_of_suffix hcl).boxIn
      (tupT (σ := σ) [.VTypeBox A]).2)) (oblB hT A) = Term.boxtm (oblRead hT A hcl).2 := rfl

/-- ⭐**The child's object comes home as the alias**: `g` read along the way home, whose image of
    the committed root is `y`, is `y` (`subst_arrow_tupB`). -/
theorem home_oblRead {lk : List VarType} (hcl : [VarType.VTypeBox A] <:+ lk) {Δ : Ctx}
    [Δ.NoSlots] {img : ℕ → ℕ} (himg : ImgOk lk Δ img) {y : ℕ} (hy0 : img 0 = y)
    (hyΔ : Δ.ref (.root (.free y)) = some A) :
    (⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
        (oblRead hT A hcl).2⟩ : Σ b, Term σ Δ A b) =
      ⟨_, Term.eta (.root (.free y)) A hyΔ⟩ := by
  have hu : (ctxOf [VarType.VTypeBox A]).ref (.root (.free 0)) = some (.VTypeBox A) :=
    ctxOf_ref_new _ []
  have k1 : oblRead (σ := σ) hT A hcl = Term.castTy (bc_box_noT hT A)
      (Term.mono (ctxOf_le_of_suffix hcl).boxIn (tup (.root (.free 0)) (.VTypeBox A) hu)) := by
    refine Term.subst_eta_cast _ _ _ (bc_box_noT hT A) _ ?_
    rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ (by
      change Subst.single _ _ (.root (.bnd 0)) = _
      exact if_pos rfl)]
    rfl
  have hh : Δ.ref ((VarSymb.root (.free (img 0))).ext
      (encPath (VarSymb.root (.free 0)).path)) = some (VarType.VTypeBox A).bc := by
    change Δ.ref (.root (.free (img 0))) = _
    rw [hy0]
    exact hyΔ.trans (congrArg some (bc_box_noT hT A).symm)
  rw [k1]
  refine (Term.subst_castTy _ _ _ _ _).trans ?_
  rw [Term.subst_mono]
  refine (Term.castTy_sig _ (subst_arrow_tupB (himg.suffix hcl) ModalSys.T rfl _ (.VTypeBox A)
    hu rfl hh)).trans ((Term.castTy_eta _ _).trans (eta_addr_congr ?_ _ _))
  change VarSymb.root (.free (img 0)) = _
  rw [hy0]

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

/-- A returning possibility along a witness moves to an alias (`WFF.retxSlot`). -/
theorem ret_aliasX (hS : ModalSys.BStrong = true) {l lj : List VarType} {A : VarType}
    (hsuf : (A :: l) <:+ lj) {M : Set (WFF σ (ctxOf lj) 0)} (hM : Theory.IsMCS M) {a : Ann A}
    (t : Term σ (ctxOf l) A a)
    (hal : ∀ ψ, WFF.mono (ctxOf_le_of_suffix hsuf) (aliasFormula t ψ) ∈ M) {x : VarSymb}
    (hx : ∃ X, (ctxOf lj).ref x = some (.VTypeDia X))
    (Φ : WFF σ (((ctxOf lj).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1)
    (h : (OutLeg.pos x hx).ret hS
      (Term.mono (ctxOf_le_of_suffix hsuf) (Term.mono (aliasLe A l) t)) Φ ∈ M) :
    (OutLeg.pos x hx).ret hS (Term.eta (.root (.free l.length)) A
      ((ctxOf_le_of_suffix hsuf).ref (ctxOf_ref_new A l))) Φ ∈ M := by
  have hi := (alias_interch hsuf hM t hal (WFF.retxSlot hS x hx (.box A) Φ)).mpr
  have h₁ := WFF.instantiate_retxSlot (Γ := ctxOf lj) hS x hx (.box A) Φ
    (Term.mono (ctxOf_le_of_suffix hsuf) (Term.mono (aliasLe A l) t))
  have h₂ := WFF.instantiate_retxSlot (Γ := ctxOf lj) hS x hx (.box A) Φ
    (Term.mono (ctxOf_le_of_suffix hsuf) (Term.eta (.root (.free l.length)) A
      (ctxOf_ref_new A l)))
  have := (congrArg (· ∈ M) h₂).mp (hi ((congrArg (· ∈ M) h₁).mpr h))
  exact (congrArg (· ∈ M) (OutLeg.retS_congr hS (.pos x hx) (.box A)
    (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)) rfl)).mp this

theorem readArrowX_cx {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx cx' : ℕ} (e : cx = cx') (hcx : Δ.ref (.root (.free cx)) = some X)
    (hcx' : Δ.ref (.root (.free cx')) = some X) {B : VarType} {c : Ann B} (g : Term σ Δ B c)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) B) 1) :
    readArrowX himg hx hcx g Φ = readArrowX himg hx hcx' g Φ := by
  subst e
  rfl

/-! ## The chain makes aliases and returning children -/

section Chain

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐Every term eventually has an alias. -/
theorem StrongChain.alias_at {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A : VarType}
    {a : Ann A} (t : Term σ (ctxOf ((C.net n).st s).l) A a) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      (C.net (m + 1)).st s =
        aliasStep ((C.net m).st s) (Term.mono (ctxOf_le_of_suffix hsuf) t) := by
  obtain ⟨m, hnm, hstep⟩ := C.aliasOp s ⟨_, A, a, t⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  refine ⟨m, hnm, hsuf, ?_⟩
  rw [hstep hlm]
  simp only [NetSt.mkAlias, dif_pos hsuf]
  exact Function.update_self _ _ _

omit [ModalSys.NoFour] in
/-- The obligation atom, weakened, is the obligation atom of the larger list. -/
theorem mono_ret_obl {l l' : List VarType} (hsuf : l <:+ l') {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Φ : WFF σ (bodyCtx [.VTypeBox A] l) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Φ) =
      WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y)
          (retBackImg l' A ((ctxOf_le_of_suffix hsuf).ref hy))).2
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) := by
  change WFF.retS hS (.box (bcT [.VTypeBox A]))
    (Term.pair Term.unit (Term.mono _ (Term.eta _ _ _))) _ = _
  rw [Term.mono_eta]
  rfl

/-- ⭐**Every obligation eventually has its returning child** (T off): a child born of the atom,
    with the parent's roots one up, its root `0` (the object) coming back to `y`, and the atom's
    body read there (`retChild_body`). -/
theorem StrongChain.ret_child (hT : ModalSys.T = false) {n : ℕ} {s : Node}
    (hs : (C.net n).Live s) {A : VarType} {y : ℕ}
    (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Φ : WFF σ (bodyCtx [.VTypeBox A] ((C.net n).st s).l) 1)
    (h : WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg _ A hy)).2 Φ ∈
      ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChild hS ((ctxOf_le_of_suffix hsuf).ref hy)
          (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = none ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = Nat.succ ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = [.VTypeBox A] ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = (fun _ => y) ∧
      liftBody (rcl_suffix ((C.net m).st s).l A) (rclImg ((C.net m).st s).l A)
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) ∈
          (retChild hS ((ctxOf_le_of_suffix hsuf).ref hy)
            (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retOp s ⟨_, A, y, Φ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have hin : WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg _ A hy')).2
      (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) ∈ ((C.net m).st s).M := by
    rw [← mono_ret_obl hsuf hy Φ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s none 0
      (retChild hS hy' (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ))
      Nat.succ [.VTypeBox A] (fun _ => y) := by
    rw [hstep hlm]
    simp only [NetSt.mkRet, dif_pos hsuf, dif_pos hy', if_pos hin]
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact retChild_body hS hy' hT hM hin

/-- ⭐⭐**A returning child at the limit**: an obligation at a stage of `s` has a forward edge
    `s → t` whose way home sends `t`'s root `0` to `y`, with the atom's body read along the edge
    at the slot `□⟨(), c⟩` of the committed root (`StrongChain.ret_child`, grown to the edge's
    stage). -/
theorem lret (hT : ModalSys.T = false) (s : LW C.toFairChain) (i : ℕ) {A : VarType} {y : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Φ : WFF σ (bodyCtx [.VTypeBox A] (lat s i)) 1)
    (h : WFF.ret hS (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg _ A hy)).2 Φ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hst : LR C.toFairChain s t)
      (hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧
      readArrow (limgOk C.toFairChain hst i)
        (Term.boxtm (Term.mono (ctxOf_le_of_suffix hcl).boxIn (tupT [.VTypeBox A]).2)) Φ ∈
          ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, -, hfcl, hfimg, hbcl, hbimg, hmem⟩ :=
    C.ret_child hT (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy Φ h
  let t : LW C.toFairChain := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have h' : LR C.toFairChain s t := Or.inl ⟨_, hc⟩
  have hbt : m < birth C.toFairChain t.2 := le_birth C.toFairChain t.2 hnot
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i) :=
    (rcl_suffix _ A).trans hg.suf
  refine ⟨t, h', hcl, ?_, ?_⟩
  · have hnb : ¬ ∃ c, s.1 = c :: t.1 := not_fwd_of_back (C := C.toFairChain) (t := s) hc
    rw [limg, if_neg hnb, bimgL_eq C.toFairChain hlive (by rw [hbcl]; exact Nat.zero_lt_one),
      hbimg]
  · have hm := hg.sub _ hmem
    have hag : ∀ r < (lat s i).length, Nat.succ r = limg C.toFairChain s t r := fun r hr => by
      have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
        rw [hc, hfcl]
        exact lt_of_lt_of_le hr hsuf.length_le
      rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C.toFairChain hlive hlen, hfimg]
    have himg₀ : ImgOk (lat s i) (ctxOf (rcl ((C.net m).st s.1).l A)) Nat.succ :=
      (rclImg ((C.net m).st s.1).l A).suffix hsuf
    have e1 := readArrow_mono_congr hsuf (Ctx.Le.refl _) himg₀ (rclImg _ A) (fun r _ => rfl)
      (Term.boxtm (Term.mono (ctxOf_le_of_suffix (rcl_suffix _ A)).boxIn
        (tupT (σ := σ) [.VTypeBox A]).2)) Φ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (readArrow (rclImg _ A) _ _) ∈ _ at hm
    rw [← e1, WFF.mono_mono, readArrow_mono_congr (List.suffix_refl _) _ himg₀
      (limgOk C.toFairChain h' i) hag, WFF.mono_refl] at hm
    refine (congrArg (· ∈ _) (readArrow_sig _ ?_ Φ)).mp hm
    change (⟨_, Term.boxtm (Term.mono _ (Term.mono _ _))⟩ : Σ c, Term σ _ _ c) = _
    rw [Term.mono_mono]

/-- ⭐**Aliases at the limit**: a term at a stage of `s` has, from some later stage on, an alias
    root (`l.length`, after the list `l`) with its alias formulas at every stage
    (`StrongChain.alias_at`, `aliasStep_ok`). -/
theorem lalias (s : LW C.toFairChain) (i : ℕ) {A : VarType} {a : Ann A}
    (t : Term σ (ctxOf (lat s i)) A a) :
    ∃ i₁, i ≤ i₁ ∧ ∃ (l : List VarType) (hl : lat s i <:+ l), ∀ j, i₁ ≤ j →
      ∃ hsuf : (A :: l) <:+ lat s j, ∀ ψ,
        WFF.mono (ctxOf_le_of_suffix hsuf) (aliasFormula (Term.mono (ctxOf_le_of_suffix hl) t) ψ)
          ∈ ((C.net (birth C.toFairChain s.2 + j)).st s.1).M := by
  obtain ⟨m, hnm, hsuf, hst⟩ :=
    C.alias_at (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) t
  refine ⟨m + 1 - birth C.toFairChain s.2, by omega, _, hsuf, fun j hj => ?_⟩
  have hlm : (C.net (m + 1)).Live s.1 := live_birth C.toFairChain s.2 (by omega)
  have hg := (C.ext (show m + 1 ≤ birth C.toFairChain s.2 + j by omega)).grows s.1 hlm
  have hal := (aliasStep_ok ((C.good m).mcs s.1
    (live_birth C.toFairChain s.2 (by omega))) (Term.mono (ctxOf_le_of_suffix hsuf) t)).2.2
  rw [hst] at hg
  exact ⟨hg.suf, fun ψ => hg.sub _ (hal ⟨ψ, rfl⟩)⟩

omit [ModalSys.NoFour] in
/-- The obligation atom along a witness, weakened. -/
theorem mono_retx_obl {l l' : List VarType} (hsuf : l <:+ l') {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
    {X : VarType} (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Φ : WFF σ (bodyCtxX [.VTypeBox A] l x) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retx hS x ⟨X, hX⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg l A hy)).2 Φ) =
      WFF.retx hS x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩ (tupImgT [.VTypeBox A] (fun _ => y)
          (retBackImg l' A ((ctxOf_le_of_suffix hsuf).ref hy))).2
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ) := by
  change WFF.retxS hS x _ (.box (bcT [.VTypeBox A]))
    (Term.pair Term.unit (Term.mono _ (Term.eta _ _ _))) _ = _
  rw [Term.mono_eta]
  rfl

/-- ⭐**Every obligation along a witness eventually has its witness child** (T off). -/
theorem StrongChain.ret_childX (hT : ModalSys.T = false) {n : ℕ} {s : Node}
    (hs : (C.net n).Live s) {A : VarType} {y : ℕ}
    (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    {x : VarSymb} {X : VarType} (hX : (ctxOf ((C.net n).st s).l).ref x = some (.VTypeDia X))
    (Φ : WFF σ (bodyCtxX [.VTypeBox A] ((C.net n).st s).l x) 1)
    (h : WFF.retx hS x ⟨X, hX⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg _ A hy)).2 Φ ∈
      ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildX hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hX)
          (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ) ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = some (x, X) ∧
      (C.net (m + 1)).cx ((C.net m).nch s :: s) = ((C.net m).st s).l.length + 1 ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = Nat.succ ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = [.VTypeBox A] ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = (fun _ => y) ∧
      liftBodyX (rclX_suffix ((C.net m).st s).l A X) (rclXImg ((C.net m).st s).l A X)
        ((ctxOf_le_of_suffix hsuf).ref hX) (rclX_cx ((C.net m).st s).l A X)
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ) ∈
          (retChildX hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hX)
            (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retXOp s ⟨_, A, x, y, Φ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have hX' := (ctxOf_le_of_suffix hsuf).ref hX
  have hin : WFF.retx hS x ⟨X, hX'⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg _ A hy')).2
      (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ) ∈
        ((C.net m).st s).M := by
    rw [← mono_retx_obl hsuf hy hX Φ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s (some (x, X)) (((C.net m).st s).l.length + 1)
      (retChildX hS hy' hX' (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ))
      Nat.succ [.VTypeBox A] (fun _ => y) := by
    rw [hstep hlm]
    simp only [NetSt.mkRetX, dif_pos hsuf, dif_pos hy']
    split
    · rename_i X'' hX''
      obtain rfl : X'' = X := by
        rw [hX'] at hX''
        exact (VarType.VTypeDia.inj (Option.some.inj hX'')).symm
      rw [if_pos hin]
    · rename_i hne
      exact absurd hX' (hne X)
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact (retChildX_spec hS hy' hX' hT hM hin).1 (Or.inl rfl)

/-- ⭐⭐**A witness child at the limit**: an obligation along `x` at a stage of `s` has a witness
    edge `s → t` for `x` whose way home sends `t`'s root `0` to `y`, with the atom's body read along
    it at the committed root (`StrongChain.ret_childX`). -/
theorem lretX (hT : ModalSys.T = false) (s : LW C.toFairChain) (i : ℕ) {A : VarType} {y : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
    {X : VarType} (hX : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (Φ : WFF σ (bodyCtxX [.VTypeBox A] (lat s i) x) 1)
    (h : WFF.retx hS x ⟨X, hX⟩ (tupImgT [.VTypeBox A] (fun _ => y) (retBackImg _ A hy)).2 Φ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hk : lkd C.toFairChain s t = some (x, X))
      (hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧
      readArrowX (limgOk C.toFairChain (lkdR hk) i) hX (lhcx C.toFairChain hk i)
        (Term.boxtm (Term.mono (ctxOf_le_of_suffix hcl).boxIn (tupT [.VTypeBox A]).2)) Φ ∈
          ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, hkind, hcxe, hfcl, hfimg, hbcl, hbimg, hmem⟩ :=
    C.ret_childX hT (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy hX Φ h
  let t : LW C.toFairChain := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have hbt : m < birth C.toFairChain t.2 := le_birth C.toFairChain t.2 hnot
  have hbt' : birth C.toFairChain t.2 ≤ m + 1 := birth_le t.2 hlive
  have hkd : lkd C.toFairChain s t = some (x, X) := by
    rw [lkd, if_pos ⟨_, hc⟩, ← kind_at C.toFairChain t hbt']
    exact hkind
  have hlcx : lcx C.toFairChain s t = ((C.net m).st s.1).l.length + 1 := by
    rw [lcx, if_pos ⟨_, hc⟩]
    exact (cx_at C.toFairChain t hbt').symm.trans hcxe
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i) :=
    (rclX_suffix _ A X).trans hg.suf
  refine ⟨t, hkd, hcl, ?_, ?_⟩
  · have hnb : ¬ ∃ c, s.1 = c :: t.1 := not_fwd_of_back (C := C.toFairChain) (t := s) hc
    rw [limg, if_neg hnb, bimgL_eq C.toFairChain hlive (by rw [hbcl]; exact Nat.zero_lt_one),
      hbimg]
  · have hm := hg.sub _ hmem
    have hag : ∀ r < (lat s i).length, Nat.succ r = limg C.toFairChain s t r := fun r hr => by
      have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
        rw [hc, hfcl]
        exact lt_of_lt_of_le hr hsuf.length_le
      rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C.toFairChain hlive hlen, hfimg]
    have himg₀ : ImgOk (lat s i) (ctxOf (X :: rcl ((C.net m).st s.1).l A)) Nat.succ :=
      (rclXImg ((C.net m).st s.1).l A X).suffix hsuf
    have e1 := readArrowX_mono_congr hsuf (Ctx.Le.refl _) himg₀ (rclXImg _ A X)
      (fun _ _ => rfl) hX ((ctxOf_le_of_suffix hsuf).ref hX) (rclX_cx _ A X) (rclX_cx _ A X)
      (Term.boxtm (Term.mono (ctxOf_le_of_suffix (rclX_suffix _ A X)).boxIn
        (tupT (σ := σ) [.VTypeBox A]).2)) Φ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (readArrowX (rclXImg _ A X) ((ctxOf_le_of_suffix hsuf).ref hX)
      (rclX_cx _ A X) _ _) ∈ _ at hm
    rw [← e1, WFF.mono_mono, readArrowX_mono_congr (List.suffix_refl _) _ himg₀
      (limgOk C.toFairChain (lkdR hkd) i) hag hX hX _ (hlcx ▸ lhcx C.toFairChain hkd i),
      WFF.mono_refl] at hm
    rw [readArrowX_cx _ _ hlcx _ (hlcx ▸ lhcx C.toFairChain hkd i)]
    refine (congrArg (· ∈ _) (readArrowX_sig _ _ _ ?_ Φ)).mp hm
    change (⟨_, Term.boxtm (Term.mono _ (Term.mono _ _))⟩ : Σ c, Term σ _ _ c) = _
    rw [Term.mono_mono]

end Chain

/-! ## Membership ⇒ truth -/

namespace BData

/-- ⭐**Returning successors** (plain leg, `□` shape): a returning possibility in a world's theory
    has an arrow `s → k` and a term `g` of `k`'s `□` view with `Φ(□g)` at `k` (read along the
    arrow), whose reading home is `Ind` to the value.  The limit of a strong chain has it
    (`bdataS_retOut`). -/
def RetOut (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {A : VarType} {a : Ann A} (t : Term σ ((B.w s).ctx i) A a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (.VTypeBox A)) 1),
    WFF.ret hS t Φ ∈ (B.w s).M i →
      ∃ (k : B.W) (h : B.R s k) (j : ℕ) (hj : B.stg s k i ≤ j) (b : Ann A)
        (g : Term σ ((B.w k).ctx j).boxIn A b),
        readArrow ((B.imgOk h i).mono ((B.w k).le hj)) (Term.boxtm g) Φ ∈ (B.w k).M j ∧
        B.Ind (B.toDom A s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm h) j)) (coh_arrowS (B.imgOk (B.symm h) j)) g))
            (definable_rden _ _))
          (B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _))

variable {B : BData σ}

/-- ⭐⭐**`ret`, membership ⇒ truth** (plain leg, `□` shape): the returning successor's object
    `□g` has `Φ` by the induction hypothesis (`sat_readArrow`, `boxPush_canon_at`), and comes back
    as `g` read home (`box_beta`, `boxPush_canon_at`, `interp_subst`), `Ind` to the value. -/
theorem sat_ret_of_mem (hS : ModalSys.BStrong = true) (hRO : B.RetOut hS) {s : B.W} {i : ℕ}
    {A : VarType} {a : Ann A} (t : Term σ ((B.w s).ctx i) A a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.ret hS t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : (WFF.ret hS t Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.ret hS t Φ : WFF σ _ 0) := by
  have hsz : (WFF.ret hS t Φ : WFF σ _ 0).size = Φ.size + A.eqRecSize + 1 := rfl
  obtain ⟨k, hR, j, hj, b, g, hmem, hInd⟩ := hRO t Φ h
  have hsat := (IH k j _ (by
    rw [hsz]; unfold readArrow; rw [WFF.size_subst]; omega)).mpr hmem
  rw [sat_readArrow, ← boxPush_canon_at s i ⟨k, ⟨Or.inl hR⟩⟩ hR hj] at hsat
  refine ⟨⟨k, ⟨Or.inl hR⟩⟩, _, hsat, Or.inl (B.symm hR), ?_⟩
  change B.Ind (B.model.necEval (Model.interp _ (Term.boxtm g)) ⟨s, ⟨Or.inl (B.symm hR)⟩⟩) _
  rw [Model.box_beta, boxPush_canon_at k j ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
    ← Model.interp_subst, interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon t (Model.Env.Agree.refl' _)]
  exact hInd

end BData

/-! ## The limit -/

section LimitOut

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- The stage an edge commits a stage at grows with it. -/
theorem lstg_mono {s t : LW C.toFairChain} (h : LR C.toFairChain s t) {i i' : ℕ}
    (hii : i ≤ i') : lstg C.toFairChain s t i ≤ lstg C.toFairChain s t i' := by
  classical
  have hP := lstg_spec C.toFairChain h i'
  have hP' : StgP C.toFairChain s t i (lstg C.toFairChain s t i') :=
    ⟨by have := hP.1; omega, le_trans (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))).length_le hP.2⟩
  rw [lstg, dif_pos ⟨_, hP'⟩]
  exact Nat.find_min' _ hP'

/-- ⭐**An alias is `Ind` to its term**: its alias formulas at every later stage make the two
    interchangeable there (`alias_interch`), so `DTerm.Rel`. -/
theorem lalias_ind (hT : ModalSys.T = false) (s : LW C.toFairChain) {i i₁ : ℕ}
    {A : VarType} {a : Ann A} (t : Term σ (ctxOf (lat s i)) A a) {l : List VarType}
    (hl : lat s i <:+ l)
    (hal : ∀ j, i₁ ≤ j → ∃ hsuf : (A :: l) <:+ lat s j, ∀ ψ,
      WFF.mono (ctxOf_le_of_suffix hsuf) (aliasFormula (Term.mono (ctxOf_le_of_suffix hl) t) ψ)
        ∈ ((C.net (birth C.toFairChain s.2 + j)).st s.1).M)
    (hy₁ : (ctxOf (lat s i₁)).ref (.root (.free l.length)) = some A) :
    (bdataS C hT).Ind
      ((bdataS C hT).toDom A s ((bdataS C hT).rden s i₁ (Ctx.Le.refl _)
        (Term.eta (.root (.free l.length)) A hy₁)) (BData.definable_rden _ _))
      ((bdataS C hT).toDom A s ((bdataS C hT).rden s i (Ctx.Le.refl _) t)
        (BData.definable_rden _ _)) := by
  refine ⟨⟨i₁, _, Term.eta (.root (.free l.length)) A hy₁⟩, ⟨i, a, t⟩,
    (BData.fromDom_toDom _ _ _ _ _).symm, (BData.fromDom_toDom _ _ _ _ _).symm, fun j h h' φ => ?_⟩
  obtain ⟨hsufj, halj⟩ := hal j h
  have hi := alias_interch hsufj ((C.good _).mcs s.1
    (live_birth C.toFairChain s.2 (Nat.le_add_right _ j))) (Term.mono (ctxOf_le_of_suffix hl) t)
    halj φ
  rw [Term.mono_eta, Term.mono_mono, Term.mono_mono] at hi
  rw [BWorld.mem_T, BWorld.mem_T]
  change WFF.instantiate _ (Term.mono _ (Term.eta _ A hy₁)) φ ∈ _ ↔
    WFF.instantiate _ (Term.mono _ t) φ ∈ _
  rw [Term.mono_eta]
  exact hi

/-- ⭐⭐**The limit has returning successors** (plain leg, `□` shape; T off): alias the value
    (`lalias`), move the atom to the alias (`ret_alias`), make it the obligation (`ret_obl`), take
    its returning child (`lret`), read the body there (`readArrow_bodyRepl`, `holeAt_oblB`), and
    the object comes home as the alias (`home_oblRead`), `Ind` to the value (`lalias_ind`). -/
theorem bdataS_retOut (hT : ModalSys.T = false) : (bdataS C hT).RetOut hS := by
  classical
  intro s i A a t Φ h
  obtain ⟨i₁, hii₁, l, hl, hal⟩ := lalias C s i t
  obtain ⟨hsuf₁, hal₁⟩ := hal i₁ le_rfl
  have hM₁ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ i₁))
  have hy₁ : (ctxOf (lat s i₁)).ref (.root (.free l.length)) = some A :=
    (ctxOf_le_of_suffix hsuf₁).ref (ctxOf_ref_new A l)
  have hret₁ : WFF.ret hS (Term.mono (ctxOf_le_of_suffix hsuf₁) (Term.mono (aliasLe A l)
      (Term.mono (ctxOf_le_of_suffix hl) t)))
      (WFF.mono ((((bdataS C hT).w s).le hii₁).boxIn.insert (.bnd 0) _) Φ) ∈
        ((C.net (birth C.toFairChain s.2 + i₁)).st s.1).M := by
    have := (BWorld.mem_lift (w := (bdataS C hT).w s) hii₁).mp h
    rw [Term.mono_mono, Term.mono_mono]
    exact this
  have hy := ret_alias hS hsuf₁ hM₁ (Term.mono (ctxOf_le_of_suffix hl) t) hal₁ _ hret₁
  have hobl := ret_obl hT A hS .nec hM₁ hy₁ _ hy
  obtain ⟨k, hsk, hcl, hback, hmk⟩ := lret C hT s i₁
    (hy₁.trans (congrArg some (bc_box_noT hT A).symm)) _ hobl
  rw [readArrow_bodyRepl, holeAt_oblB hT A hcl] at hmk
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k i₁ := lstg_mono C hsk hii₁
  refine ⟨k, hsk, lstg C.toFairChain s k i₁, hj, _, (oblRead hT A hcl).2, ?_, ?_⟩
  · have e := readArrow_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C hT).w k).le hj))
      (limgOk C.toFairChain hsk i₁) (fun _ _ => rfl) (Term.boxtm (oblRead hT A hcl).2) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  · have hiK : i₁ ≤ lstg C.toFairChain k s (lstg C.toFairChain s k i₁) := by
      have h₁ := (lstg_spec C.toFairChain hsk i₁).1
      have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k i₁)).1
      omega
    have hyK := (((bdataS C hT).w s).le hiK).ref hy₁
    have hhome := home_oblRead (σ := σ) hT A hcl (limgOk C.toFairChain hsk.symm
      (lstg C.toFairChain s k i₁)) hback hyK
    have e2 := congrArg (fun p : Σ b, Term σ _ A b =>
      (bdataS C hT).rden s _ (Ctx.Le.refl _) p.2) hhome
    have e3 : (bdataS C hT).rden s _ (Ctx.Le.refl _) (Term.eta (.root (.free l.length)) A hyK) =
        (bdataS C hT).rden s i₁ (Ctx.Le.refl _) (Term.eta (.root (.free l.length)) A hy₁) := by
      have := BData.rden_lift (B := bdataS C hT) hiK (Term.eta (.root (.free l.length)) A hy₁)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C hT).Ind o _) ?_).mpr (lalias_ind C hT s t hl hal hy₁)
    exact BData.toDom_congr (e2.trans e3) _ _

end LimitOut

/-! ## Products: packing a necessary shape into one `□` -/

section Products

/-- ⭐The **packing map** of a necessary shape: its items into one necessary object. -/
def packN : (N : NShape) → ShapeMap σ N (.box N.flat)
  | .box A => .id (.box A)
  | .prod R S => .comp (.pair (.comp (.fst R S) (packN R)) (.comp (.snd R S) (packN S)))
      (.pack R.flat S.flat)

omit [ModalSys.NoFour] in
theorem unpack_ref_fst (R S : NShape) :
    ((Ctx.empty.insert (.bnd 0) (.VTypeBox (.VTypeProd R.flat S.flat))).boxIn).ref
      (.step (VarSymb.root (.bnd 0)).inner .fst) = some R.flat :=
  Ctx.ref_fst_of (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))

omit [ModalSys.NoFour] in
theorem unpack_ref_snd (R S : NShape) :
    ((Ctx.empty.insert (.bnd 0) (.VTypeBox (.VTypeProd R.flat S.flat))).boxIn).ref
      (.step (VarSymb.root (.bnd 0)).inner .snd) = some S.flat :=
  Ctx.ref_snd_of (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))

/-- ⭐The **unpacking** of one necessary object into a necessary shape's object: `□⟨a, b⟩ ↦
    ⟨□a, □b⟩`, recursively. -/
def unpackN : (N : NShape) → Σ b, Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox N.flat)) N.ty b
  | .box A => ⟨_, Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ _ _)⟩
  | .prod R S => ⟨_, Term.pair
      (Term.holeAt (Term.boxtm (Term.eta (.step (VarSymb.root (.bnd 0)).inner .fst) R.flat
        (unpack_ref_fst R S))) (unpackN R).2)
      (Term.holeAt (Term.boxtm (Term.eta (.step (VarSymb.root (.bnd 0)).inner .snd) S.flat
        (unpack_ref_snd R S))) (unpackN S).2)⟩

omit [ModalSys.NoFour] in
theorem exists_boxtm {Γ : Ctx} {A : VarType} {c : Ann (.VTypeBox A)}
    (x : Term σ Γ (.VTypeBox A) c) :
    ∃ (b : Ann A) (s : Term σ Γ.boxIn A b), (⟨c, x⟩ : Σ e, Term σ Γ (.VTypeBox A) e) =
      ⟨_, Term.boxtm s⟩ := by
  cases x with
  | boxtm s => exact ⟨_, s, rfl⟩

/-- Reading a necessary pair's first item. -/
theorem holeAt_box_fst {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ Γ.boxIn A a) (t : Term σ Γ.boxIn B b) (h : _) :
    (⟨_, Term.holeAt (Term.boxtm (Term.pair s t))
        (Term.boxtm (Term.eta (.step (VarSymb.root (.bnd 0)).inner .fst) A h))⟩ :
      Σ e, Term σ Γ (.VTypeBox A) e) = ⟨_, Term.boxtm s⟩ := by
  refine sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ s ?_)
  rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ (by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl)]
  rfl

/-- Reading a necessary pair's second item. -/
theorem holeAt_box_snd {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ Γ.boxIn A a) (t : Term σ Γ.boxIn B b) (h : _) :
    (⟨_, Term.holeAt (Term.boxtm (Term.pair s t))
        (Term.boxtm (Term.eta (.step (VarSymb.root (.bnd 0)).inner .snd) B h))⟩ :
      Σ e, Term σ Γ (.VTypeBox B) e) = ⟨_, Term.boxtm t⟩ := by
  refine sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ t ?_)
  rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ (by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl)]
  rfl

/-- ⭐**Packing then unpacking is the identity** on objects of a necessary shape. -/
theorem holeAt_packN_unpackN : (N : NShape) → {Γ : Ctx} → {c : Ann N.ty} →
    (x : Term σ Γ N.ty c) →
    (⟨_, Term.holeAt (Term.holeAt x (packN (σ := σ) N).obj.2) (unpackN N).2⟩ :
      Σ e, Term σ Γ N.ty e) = ⟨c, x⟩
  | .box A, Γ, c, x => by
      exact (Term.holeAt_congr_sig (Term.holeAt_eta_root x) _).trans (Term.holeAt_eta_root x)
  | .prod R S, Γ, _, .pair x₁ x₂ => by
      obtain ⟨_, s₁, h₁⟩ := exists_boxtm (Term.holeAt x₁ (packN (σ := σ) R).obj.2)
      obtain ⟨_, s₂, h₂⟩ := exists_boxtm (Term.holeAt x₂ (packN (σ := σ) S).obj.2)
      have hP : (⟨_, Term.holeAt (Term.pair x₁ x₂) (packN (σ := σ) (.prod R S)).obj.2⟩ :
          Σ e, Term σ Γ (.VTypeBox (.VTypeProd R.flat S.flat)) e) =
          ⟨_, Term.boxtm (Term.pair s₁ s₂)⟩ := by
        change (⟨_, Term.holeAt (Term.pair x₁ x₂) (Term.holeAt (Term.pair
          (Term.holeAt _ (packN (σ := σ) R).obj.2) (Term.holeAt _ (packN (σ := σ) S).obj.2))
          (ShapeMap.pack (σ := σ) R.flat S.flat).obj.2)⟩ : Σ e, Term σ Γ _ e) = _
        refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
        refine (Term.holeAt_congr_sig (sig_pair
          ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
            (Term.holeAt_pair_fst x₁ x₂) _).trans h₁))
          ((Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
            (Term.holeAt_pair_snd x₁ x₂) _).trans h₂))) _).trans ?_
        exact Term.holeAt_pack s₁ s₂
      refine (Term.holeAt_congr_sig hP _).trans ?_
      change (⟨_, Term.pair (Term.holeAt _ (Term.holeAt _ (unpackN (σ := σ) R).2))
        (Term.holeAt _ (Term.holeAt _ (unpackN (σ := σ) S).2))⟩ : Σ e, Term σ Γ _ e) = _
      refine sig_pair ?_ ?_
      · refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          ((holeAt_box_fst s₁ s₂ _).trans h₁.symm) _).trans ?_)
        exact holeAt_packN_unpackN R x₁
      · refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          ((holeAt_box_snd s₁ s₂ _).trans h₂.symm) _).trans ?_)
        exact holeAt_packN_unpackN S x₂

/-- Packing then unpacking, on the slot. -/
theorem holeAt_packN_unpackN_slot (N : NShape) :
    (⟨_, Term.holeAt (packN (σ := σ) N).obj.2 (unpackN N).2⟩ :
      Σ e, Term σ (Ctx.empty.insert (.bnd 0) N.ty) N.ty e) =
      ⟨_, Term.eta (.root (.bnd 0)) N.ty (Ctx.ref_insert_root _ _ _)⟩ := by
  have h := holeAt_packN_unpackN N (σ := σ)
    (Term.eta (.root (.bnd 0)) N.ty (Ctx.ref_insert_root Ctx.empty (.bnd 0) N.ty))
  rw [Term.holeAt_congr_sig (Term.holeAt_eta_slot (V := Ctx.empty) _) _, Term.mono_refl] at h
  exact h

/-- ⭐**A returning possibility at a necessary shape is one at `□`**: `ret_map` along the packing
    map, the body read back through the unpacking. -/
def retS_packN (hS : ModalSys.BStrong = true) {Γ : Ctx} [Γ.NoSlots] (O : OutLeg Γ)
    {Δ : List (WFF σ Γ 0)} {N : NShape} {a : Ann N.flat} (t : Term σ Γ N.flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1)
    (p : Proof σ Γ Δ (O.retS hS (.nec N) t Φ)) :
    Proof σ Γ Δ (O.ret hS (Term.holeRead t (packN N).val.2)
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unpackN N).2) Φ)) := by
  refine Proof.ret_map hS O (S := .nec N) (packN N) t _ (Proof.conv ?_ p)
  change O.retS hS (.nec N) t Φ = O.retS hS (.nec N) t (WFF.bodyRepl _ (WFF.bodyRepl _ Φ))
  rw [WFF.bodyRepl_bodyRepl]
  dsimp only [ShapeMap.liftObj]
  rw [WFF.bodyRepl_congr (sig_mono _ (holeAt_packN_unpackN_slot N))]
  exact congrArg (O.retS hS (.nec N) t) (WFF.bodyRepl_eta Φ).symm

end Products

/-! ## Products, semantically -/

namespace BData

variable {B : BData σ}

/-- A representative of an object is one of the value under a hole term, filled (as
    `BData.rden_holeAt`). -/
theorem rden_holeAt_ret {s : B.W} {A : VarType} {o : B.model.frame.Dom A s}
    (u : Canon.DTerm (B.w s).sys (B.w s).T A)
    (hu : B.rden s u.i (Ctx.Le.refl _) u.t = B.fromDom A s o)
    {C : VarType} {c : Ann C} (hh : Term σ (Ctx.empty.insert (.bnd 0) A) C c) :
    B.rden s u.i (Ctx.Le.refl _) (Term.holeAt u.t hh) = B.fromDom C s (B.model.holeVal hh o) := by
  have e1 := interp_canon (Term.holeAt u.t hh) (env := B.canonEnv s u.i)
    (e := Ctx.Le.refl _) (fun _ _ _ => rfl)
  have e2 : Model.interp (B.canonEnv s u.i) u.t = o := by
    rw [interp_canon u.t (env := B.canonEnv s u.i) (e := Ctx.Le.refl _) (fun _ _ _ => rfl)]
    exact (B.toDom_congr hu _ _).trans (B.toDom_fromDom A s o)
  rw [Model.interp_holeAt, e2] at e1
  rw [e1, B.fromDom_toDom]

/-- Canonical `Ind` is a congruence for hole terms (as `BData.indInvariant`'s `map`). -/
theorem ind_map {s : B.W} {A C : VarType} {c : Ann C}
    (hh : Term σ (Ctx.empty.insert (.bnd 0) A) C c) {o o' : B.frame.Dom A s}
    (h : B.Ind o o') : B.Ind (B.model.holeVal hh o) (B.model.holeVal hh o') := by
  obtain ⟨u, u', hu, hu', hrel⟩ := h
  exact ⟨⟨u.i, _, Term.holeAt u.t hh⟩, ⟨u'.i, _, Term.holeAt u'.t hh⟩, rden_holeAt_ret u hu hh,
    rden_holeAt_ret u' hu' hh, hrel.holeAt hh⟩

/-- A necessary pair's first item, read along an arrow. -/
theorem necEval_boxFst {k : B.W} {X Y : VarType}
    (E : B.model.frame.Dom (.VTypeBox (.VTypeProd X Y)) k) (acc : B.model.frame.Acc k) (h : _) :
    B.model.necEval (B.model.holeVal (Term.boxtm (Term.eta (σ := σ)
        (.step (VarSymb.root (.bnd 0)).inner .fst) X h)) E : B.model.frame.Nec X k) acc =
      (B.model.necEval (E : B.model.frame.Nec (.VTypeProd X Y) k) acc).1 := by
  have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox (.VTypeProd X Y))
  unfold Model.holeVal
  rw [Model.box_beta, Model.interp_eta, Model.Env.ref_fst _ (Ctx.ref_inner hu) h,
    Model.Env.ref_inner _ _ hu]
  have he : ((Model.Env.empty (M := B.model) k).extend (.bnd 0) E).ref (.root (.bnd 0)) hu = E :=
    Model.Env.extend_root _ _ _ _
  rw [he]

/-- A necessary pair's second item, read along an arrow. -/
theorem necEval_boxSnd {k : B.W} {X Y : VarType}
    (E : B.model.frame.Dom (.VTypeBox (.VTypeProd X Y)) k) (acc : B.model.frame.Acc k) (h : _) :
    B.model.necEval (B.model.holeVal (Term.boxtm (Term.eta (σ := σ)
        (.step (VarSymb.root (.bnd 0)).inner .snd) Y h)) E : B.model.frame.Nec Y k) acc =
      (B.model.necEval (E : B.model.frame.Nec (.VTypeProd X Y) k) acc).2 := by
  have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox (.VTypeProd X Y))
  unfold Model.holeVal
  rw [Model.box_beta, Model.interp_eta, Model.Env.ref_snd _ (Ctx.ref_inner hu) h,
    Model.Env.ref_inner _ _ hu]
  have he : ((Model.Env.empty (M := B.model) k).extend (.bnd 0) E).ref (.root (.bnd 0)) hu = E :=
    Model.Env.extend_root _ _ _ _
  rw [he]

/-- ⭐**Unpacking comes back**: if a packed object comes back `Ind` to a packed value, its unpacking
    comes back as the value, componentwise (`ind_map` at the projections). -/
theorem ncb_unpackN {s k : B.W} (r : B.RT k s) : ∀ (N : NShape)
    (E : B.model.frame.Dom (.VTypeBox N.flat) k) (o : B.model.frame.Dom N.flat s),
    B.Ind (B.model.necEval (E : B.model.frame.Nec N.flat k) ⟨s, ⟨r⟩⟩)
      (B.model.holeVal (packN (σ := σ) N).val.2 o) →
      B.model.NComesBack N (B.model.holeVal (unpackN (σ := σ) N).2 E) r o
  | .box A, E, o, h => by
      have h₁ : B.model.holeVal (unpackN (σ := σ) (.box A)).2 E = E :=
        Model.interp_eta_slot _ _ (Ctx.ref_insert_root _ _ _)
      have h₂ : B.model.holeVal (packN (σ := σ) (.box A)).val.2 o = o :=
        Model.interp_eta_slot _ _ (Ctx.ref_insert_root _ _ _)
      rw [h₂] at h
      rw [h₁]
      exact h
  | .prod R S, E, o, h => by
      have hv : B.model.holeVal (packN (σ := σ) (.prod R S)).val.2 o =
          (B.model.holeVal (packN (σ := σ) R).val.2 o.1,
            B.model.holeVal (packN (σ := σ) S).val.2 o.2) := by
        unfold Model.holeVal
        change Model.interp _ (Term.holeAt _ _) = _
        rw [Model.interp_holeAt]
        unfold Model.holeVal
        rw [show (ShapeMap.pack (σ := σ) R.flat S.flat).val.2 = Term.eta (.root (.bnd 0)) _
          (Ctx.ref_insert_root _ _ _) from rfl, Model.interp_eta_slot]
        change (Model.interp _ (Term.holeAt _ _), Model.interp _ (Term.holeAt _ _)) = _
        rw [Model.interp_holeAt, Model.interp_holeAt]
        have e₁ : Model.interp ((Model.Env.empty (M := B.model) s).extend (.bnd 0) o)
            (ShapeMap.fst (σ := σ) R S).val.2 = o.1 := Model.interp_eta_slot_fst _ _ _
        have e₂ : Model.interp ((Model.Env.empty (M := B.model) s).extend (.bnd 0) o)
            (ShapeMap.snd (σ := σ) R S).val.2 = o.2 := Model.interp_eta_slot_snd _ _ _
        rw [e₁, e₂]
        rfl
      rw [hv] at h
      refine ⟨?_, ?_⟩
      · have h₁ := ind_map (Term.eta (.step (.root (.bnd 0)) .fst) R.flat
          (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
            (.VTypeProd R.flat S.flat)))) h
        unfold Model.holeVal at h₁
        rw [Model.interp_eta_slot_fst] at h₁
        erw [Model.interp_eta_slot_fst] at h₁
        change B.model.NComesBack R (Model.interp _ (Term.holeAt _ _)) r o.1
        rw [Model.interp_holeAt]
        refine ncb_unpackN r R _ o.1 ?_
        exact (congrArg (fun x => B.Ind x _) (necEval_boxFst E _ _)).mpr h₁
      · have h₂ := ind_map (Term.eta (.step (.root (.bnd 0)) .snd) S.flat
          (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
            (.VTypeProd R.flat S.flat)))) h
        unfold Model.holeVal at h₂
        rw [Model.interp_eta_slot_snd] at h₂
        erw [Model.interp_eta_slot_snd] at h₂
        change B.model.NComesBack S (Model.interp _ (Term.holeAt _ _)) r o.2
        rw [Model.interp_holeAt]
        refine ncb_unpackN r S _ o.2 ?_
        exact (congrArg (fun x => B.Ind x _) (necEval_boxSnd E _ _)).mpr h₂

/-- ⭐⭐**`ret`, membership ⇒ truth at every necessary shape** (plain leg): pack the shape into one
    `□` (`retS_packN`), take the returning successor (`RetOut`), and unpack its object
    (`readArrow_bodyRepl`, `ncb_unpackN`). -/
theorem sat_retS_nec_of_mem (hS : ModalSys.BStrong = true) (hRO : B.RetOut hS) {s : B.W}
    {i : ℕ} {N : NShape} {a : Ann N.flat} (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.retS hS (.nec N) t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : (WFF.retS hS (.nec N) t Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.retS hS (.nec N) t Φ : WFF σ _ 0) := by
  have hsz : (WFF.retS hS (.nec N) t Φ : WFF σ _ 0).size = Φ.size + N.flat.eqRecSize + 1 := rfl
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packN hS .nec t Φ (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨k, hR, j, hj, b, g, hmem, hInd⟩ := hRO _ _ hp
  rw [readArrow_bodyRepl] at hmem
  have hsat := (IH k j _ (by
    rw [hsz]; unfold readArrow; rw [WFF.size_subst]; omega)).mpr hmem
  rw [sat_readArrow, ← boxPush_canon_at s i ⟨k, ⟨Or.inl hR⟩⟩ hR hj] at hsat
  refine ⟨⟨k, ⟨Or.inl hR⟩⟩, _, hsat, Or.inl (B.symm hR), ?_⟩
  change B.model.NComesBack N (Model.interp _ (Term.holeAt _ _)) _ _
  rw [Model.interp_holeAt]
  refine ncb_unpackN (Or.inl (B.symm hR)) N _ _ ?_
  rw [Model.box_beta, boxPush_canon_at k j ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
    ← Model.interp_subst, interp_canon _ (Model.Env.Agree.refl' _),
    ← Model.interp_holeRead (noProjLast s i), interp_canon _ (Model.Env.Agree.refl' _)]
  exact hInd

/-- ⭐**Returning successors along a witness** (`□` shape): as `RetOut`, along an arrow of `y`'s
    extent.  The limit of a strong chain has it (`bdataS_retOutX`). -/
def RetOutX (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {y : VarSymb} {Y : VarType}
    (hy : ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {A : VarType} {a : Ann A}
    (t : Term σ ((B.w s).ctx i) A a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (.VTypeBox A)) 1),
    (OutLeg.pos y ⟨Y, hy⟩ : OutLeg ((B.w s).ctx i)).ret hS t Φ ∈ (B.w s).M i →
      ∃ (k : B.W) (hk : B.kd s k = some (y, Y)) (j : ℕ) (hj : B.stg s k i ≤ j) (b : Ann A)
        (g : Term σ ((B.w k).ctx j).boxIn A b),
        readArrowX ((B.imgOk (B.kdR hk) i).mono ((B.w k).le hj)) hy
            (((B.w k).le hj).ref (B.hcx hk i)) (Term.boxtm g) Φ ∈ (B.w k).M j ∧
        B.Ind (B.toDom A s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm (B.kdR hk)) j))
              (coh_arrowS (B.imgOk (B.symm (B.kdR hk)) j)) g))
            (definable_rden _ _))
          (B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _))

/-- ⭐⭐**`ret` along a witness, membership ⇒ truth at every necessary shape**: as
    `sat_retS_nec_of_mem`, along an arrow of `y`'s extent (`RetOutX`, `diaPush_canon_at`). -/
theorem sat_retxS_nec_of_mem (hS : ModalSys.BStrong = true) (hRX : B.RetOutX hS) {s : B.W}
    {i : ℕ} {y : VarSymb} (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape}
    {a : Ann N.flat} (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ :
        WFF σ _ 0).size → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0) ∈
      (B.w s).M i) :
    B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0) := by
  have hsz : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ :
      WFF σ _ 0).size = Φ.size + N.flat.eqRecSize + 1 := rfl
  obtain ⟨Y, hY⟩ := hy
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packN hS (.pos y ⟨Y, hY⟩) t Φ (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨k, hk, j, hj, b, g, hmem, hInd⟩ := hRX hY _ _ hp
  have hR := B.kdR hk
  rw [readArrowX_bodyRepl] at hmem
  have hsat := (IH k j _ (by
    rw [hsz]; unfold readArrowX; rw [WFF.size_subst]; omega)).mpr hmem
  have ha : (⟨k, ⟨Or.inl hR⟩⟩ : B.Acc s) ∈
      (B.model.posEval ((B.canonEnv s i).ref y hY)).1 := by
    rw [canonEnv_extent s i hY]
    exact Or.inl ⟨Y, hk⟩
  rw [sat_readArrowX, ← diaPush_canon_at s i hY ⟨⟨k, ⟨Or.inl hR⟩⟩, ha⟩ hk hj] at hsat
  refine ⟨Y, hY, ⟨⟨k, ⟨Or.inl hR⟩⟩, ha⟩, _, hsat, Or.inl (B.symm hR), ?_⟩
  change B.model.NComesBack N (Model.interp _ (Term.holeAt _ _)) _ _
  rw [Model.interp_holeAt]
  refine ncb_unpackN (Or.inl (B.symm hR)) N _ _ ?_
  rw [Model.box_beta, boxPush_canon_at k j ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
    ← Model.interp_subst, interp_canon _ (Model.Env.Agree.refl' _),
    ← Model.interp_holeRead (noProjLast s i), interp_canon _ (Model.Env.Agree.refl' _)]
  exact hInd

end BData

section LimitOutX

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐⭐**The limit has returning successors along a witness** (`□` shape; T off): as
    `bdataS_retOut`, with the witness child (`ret_aliasX`, `ret_obl` along `x`, `lretX`). -/
theorem bdataS_retOutX (hT : ModalSys.T = false) : (bdataS C hT).RetOutX hS := by
  classical
  intro s i y Y hy A a t Φ h
  obtain ⟨i₁, hii₁, l, hl, hal⟩ := lalias C s i t
  obtain ⟨hsuf₁, hal₁⟩ := hal i₁ le_rfl
  have hM₁ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ i₁))
  have hy₁ : (ctxOf (lat s i₁)).ref (.root (.free l.length)) = some A :=
    (ctxOf_le_of_suffix hsuf₁).ref (ctxOf_ref_new A l)
  have hyi₁ := (((bdataS C hT).w s).le hii₁).ref hy
  have hret₁ : (OutLeg.pos y ⟨Y, hyi₁⟩ : OutLeg (ctxOf (lat s i₁))).ret hS
      (Term.mono (ctxOf_le_of_suffix hsuf₁) (Term.mono (aliasLe A l)
        (Term.mono (ctxOf_le_of_suffix hl) t)))
      (WFF.mono (((((bdataS C hT).w s).le hii₁).diaIn y).insert (.bnd 0) _) Φ) ∈
        ((C.net (birth C.toFairChain s.2 + i₁)).st s.1).M := by
    have := (BWorld.mem_lift (w := (bdataS C hT).w s) hii₁).mp h
    rw [Term.mono_mono, Term.mono_mono]
    exact this
  have hy' := ret_aliasX hS hsuf₁ hM₁ (Term.mono (ctxOf_le_of_suffix hl) t) hal₁ ⟨Y, hyi₁⟩ _
    hret₁
  have hobl := ret_obl hT A hS (.pos y ⟨Y, hyi₁⟩) hM₁ hy₁ _ hy'
  obtain ⟨k, hk, hcl, hback, hmk⟩ := lretX C hT s i₁
    (hy₁.trans (congrArg some (bc_box_noT hT A).symm)) hyi₁ _ hobl
  rw [readArrowX_bodyRepl, holeAt_oblB hT A hcl] at hmk
  have hsk := lkdR hk
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k i₁ := lstg_mono C hsk hii₁
  refine ⟨k, hk, lstg C.toFairChain s k i₁, hj, _, (oblRead hT A hcl).2, ?_, ?_⟩
  · have e := readArrowX_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C hT).w k).le hj))
      (limgOk C.toFairChain hsk i₁) (fun _ _ => rfl) hy hyi₁
      ((((bdataS C hT).w k).le hj).ref ((bdataS C hT).hcx hk i)) (lhcx C.toFairChain hk i₁)
      (Term.boxtm (oblRead hT A hcl).2) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  · have hiK : i₁ ≤ lstg C.toFairChain k s (lstg C.toFairChain s k i₁) := by
      have h₁ := (lstg_spec C.toFairChain hsk i₁).1
      have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k i₁)).1
      omega
    have hyK := (((bdataS C hT).w s).le hiK).ref hy₁
    have hhome := home_oblRead (σ := σ) hT A hcl (limgOk C.toFairChain hsk.symm
      (lstg C.toFairChain s k i₁)) hback hyK
    have e2 := congrArg (fun p : Σ b, Term σ _ A b =>
      (bdataS C hT).rden s _ (Ctx.Le.refl _) p.2) hhome
    have e3 : (bdataS C hT).rden s _ (Ctx.Le.refl _) (Term.eta (.root (.free l.length)) A hyK) =
        (bdataS C hT).rden s i₁ (Ctx.Le.refl _) (Term.eta (.root (.free l.length)) A hy₁) := by
      have := BData.rden_lift (B := bdataS C hT) hiK (Term.eta (.root (.free l.length)) A hy₁)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C hT).Ind o _) ?_).mpr (lalias_ind C hT s t hl hal hy₁)
    exact BData.toDom_congr (e2.trans e3) _ _


end LimitOutX

end BArrow

end V12M
