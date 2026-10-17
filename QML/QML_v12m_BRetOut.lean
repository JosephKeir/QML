import QML.QML_v12m_BRetTruthW

/-!
# QML v12m — B's canonical model: `ret` membership ⇒ truth (strong B, T off)

A returning possibility `◇[d ↦ t] Φ(d)` in a node's theory is made true by a returning successor
(docs §11.20, §11.21).  The network makes successors for **obligations** at the born root's own
shape, `◇^{S_A}[u ↦ unarrT y] Ξ(u)` valued at a root `y` (`NetSt.mkRetC`), on the generic
children: every obligation eventually has its child (`StrongChain.ret_childC`), and at the limit
an edge whose way home sends the born root `c` to `y`, with the body read at `c` (`lretC`).
A user atom becomes an obligation by an alias `y` of `t` (`NetSt.mkAlias`, whose alias formula
at the atom's slot formula moves the value, `ret_alias`); with T off the born root has no
companions, so the atom at the alias *is* the obligation (`ret_oblC_noT`; under T the companions
are named first).  The child's object `c = □(c.inner)` comes home as `y`
(`subst_arrow_eta_inner`).  Products are packed into one `□` first (`retS_packN`).  Along a
witness the same goes through the witness child (`mkRetXC`, `lretXC`).

At a witnessed shape `□N × ◇Z` the necessary part is packed (`retS_packNW`), each item of the
value gets its own alias (`y`, `z`), and a unit alias `o` fills the possible part's back image;
the obligation is at `S_A × ◇Z`, valued at `unarrDT y z` (`ret_oblDC_noT`), and the
back-witness child (`mkRetDC`, or `mkRetXDC` along a witness) brings the object's necessary part
home as `y` and its witness's content home as `z` (⭐`bdataS_retOutD`, ⭐`bdataS_retOutXD`,
⭐`BData.sat_retS_wit_of_mem`, ⭐`BData.sat_retxS_wit_of_mem`).
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

end Body

section Pair

variable {V : Ctx} [V.NoSlots] {A Z : VarType}

omit [ModalSys.NoFour] in
/-- The slot formula for a pair's first item: `χ(⟨d, u⟩)`. -/
theorem WFF.instantiate_pairFst {c : Ann Z} (u : Term σ V Z c)
    (χ : WFF σ (V.insert (.bnd 0) (.VTypeProd A Z)) 1) {a : Ann A} (s : Term σ V A a) :
    WFF.instantiate Ctx.NoSlots.slots s (WFF.bodyRepl
      (Term.pair (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ _ _))
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root A) u)) χ) =
      WFF.instantiate Ctx.NoSlots.slots (Term.pair s u) χ := by
  rw [WFF.instantiate_bodyRepl]
  exact WFF.instantiate_congr_sig _ (sig_pair
    (Term.subst_eta_tm _ _ _ _ _ _ s (Subst.at_single_root _ _)) (subst_single_mono_tm s u)) χ

omit [ModalSys.NoFour] in
/-- The slot formula for a pair's second item: `χ(⟨u, d⟩)`. -/
theorem WFF.instantiate_pairSnd {c : Ann A} (u : Term σ V A c)
    (χ : WFF σ (V.insert (.bnd 0) (.VTypeProd A Z)) 1) {a : Ann Z} (s : Term σ V Z a) :
    WFF.instantiate Ctx.NoSlots.slots s (WFF.bodyRepl
      (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root Z) u)
        (Term.eta (.root (.bnd 0)) Z (Ctx.ref_insert_root _ _ _))) χ) =
      WFF.instantiate Ctx.NoSlots.slots (Term.pair u s) χ := by
  rw [WFF.instantiate_bodyRepl]
  exact WFF.instantiate_congr_sig _ (sig_pair (subst_single_mono_tm s u)
    (Term.subst_eta_tm _ _ _ _ _ _ s (Subst.at_single_root _ _))) χ

end Pair

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
/-- With T off a born root has no companions. -/
theorem bornComps_noT (hT : ModalSys.T = false) (A : VarType) : bornComps A = [] := by
  change A.compsAllB ModalSys.T = []
  rw [hT]
  rfl

/-- The obligation's value, weakened, is the obligation's value in the larger list. -/
theorem mono_unarrT {l l' : List VarType} (hsuf : l <:+ l') {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) :
    (⟨_, Term.mono (ctxOf_le_of_suffix hsuf) (unarrT (σ := σ) hy).2⟩ :
      Σ a, Term σ (ctxOf l') (A.compsFlat (bornComps A)) a) =
      unarrT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy) :=
  (subst_arrow_tgt_mono (ctxOf_le_of_suffix hsuf) (retBackImg l A hy) _).symm

/-- ⭐**With T off, a returning possibility at an alias is the obligation** at the born shape:
    the born root has no companions, so `◇[d ↦ y] Φ` is `◇^{S_A}[u ↦ unarrT y] Φ`, the
    obligation's value `y` itself (`subst_arrow_eta_inner`).  Under T the companions are named
    first. -/
theorem ret_oblC_noT (hT : ModalSys.T = false) (hS : ModalSys.BStrong = true)
    {l : List VarType} (O : OutLeg (ctxOf l)) {A : VarType} {y : ℕ}
    (hy₁ : (ctxOf l).ref (.root (.free y)) = some A)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) :
    O.retS hS (.nec (bornShape A))
        (unarrT (σ := σ) (hy₁.trans (congrArg some (bc_box_noT hT A).symm))).2 Φ =
      O.retS hS (.nec (.box A)) (Term.eta (.root (.free y)) A hy₁) Φ := by
  have hy := hy₁.trans (congrArg some (bc_box_noT hT A).symm)
  obtain ⟨hw, e⟩ := subst_arrow_eta_inner (σ := σ) (retBackImg l A hy)
    (x := .root (.free 0)) (Ctx.ref_inner (born_ref A))
  have e' := e.trans (eta_addr_congr (by
    change itemAt (imgRoot (fun _ => y) (.free 0)) (.root (.free 0)) = _
    rw [itemAt_noT hT]
    rfl) hw hy₁)
  unfold unarrT bornShape
  generalize bornComps_ok A = hcs
  revert hcs
  rw [bornComps_noT hT A]
  intro hcs
  exact OutLeg.retS_congr hS O (.nec (.box A)) e' rfl

/-- The born-shape obligation atom, weakened. -/
theorem mono_ret_oblC {l l' : List VarType} (hsuf : l <:+ l') {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ) =
      WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy)).2
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) := by
  change WFF.retS hS (.nec (bornShape A)) (Term.mono _ _) _ = _
  exact OutLeg.retS_congr hS .nec _ (mono_unarrT hsuf hy) rfl

/-- The child's body over the born root is the body read along the arrow at the born root. -/
theorem liftBodyR_eq_readArrow (l : List VarType) (A : VarType)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    liftBodyR l A Ξ = readArrow (rclImg l A)
      (Term.eta (.root (.free 0)) (.VTypeBox A) (rcl_born_ref l A)) Ξ := by
  unfold liftBodyR readArrow
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Ξ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.set_root, Subst.set_root]
    exact .ren_eta _ _
  · change SubE.Sim T (Subst.set _ _ _ v) (Subst.set _ _ _ v)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐**Every obligation eventually has its returning child**: a child born of the obligation,
    with the parent's roots one up, its root `0` (the born root) coming back to `y`, and the
    obligation's body read there at the born root (`retChildC_body`). -/
theorem StrongChain.ret_childC {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A : VarType} {y : ℕ}
    (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Ξ : WFF σ ((ctxOf ((C.net n).st s).l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈ ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildC hS ((ctxOf_le_of_suffix hsuf).ref hy)
          (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = none ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = Nat.succ ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = [.VTypeBox A] ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = (fun _ => y) ∧
      liftBodyR ((C.net m).st s).l A
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∈
          (retChildC hS ((ctxOf_le_of_suffix hsuf).ref hy)
            (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retOp s ⟨_, A, y, Ξ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have hin : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy').2
      (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∈ ((C.net m).st s).M := by
    rw [← mono_ret_oblC hsuf hy Ξ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s none 0
      (retChildC hS hy' (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ))
      Nat.succ [.VTypeBox A] (fun _ => y) := by
    rw [hstep hlm]
    simp only [NetSt.mkRetC, dif_pos hsuf, dif_pos hy', if_pos hin]
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact retChildC_body hS hy' hM hin

/-- ⭐⭐**A returning child at the limit**: an obligation at a stage of `s` has a forward edge
    `s → t` whose way home sends `t`'s root `0` to `y`, with the obligation's body read along the
    edge at the born root `c` (`StrongChain.ret_childC`, grown to the edge's stage). -/
theorem lretC (s : LW C.toFairChain) (i : ℕ) {A : VarType} {y : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (Ξ : WFF σ ((ctxOf (lat s i)).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hst : LR C.toFairChain s t)
      (hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧
      readArrow (limgOk C.toFairChain hst i)
        (Term.eta (.root (.free 0)) (.VTypeBox A) ((ctxOf_le_of_suffix hcl).ref (born_ref A)))
        Ξ ∈ ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, -, hfcl, hfimg, hbcl, hbimg, hmem⟩ :=
    C.ret_childC (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy Ξ h
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
      (Term.eta (σ := σ) (.root (.free 0)) (.VTypeBox A) (rcl_born_ref _ A)) Ξ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (liftBodyR _ A _) ∈ _ at hm
    rw [liftBodyR_eq_readArrow, ← e1, WFF.mono_mono, readArrow_mono_congr (List.suffix_refl _) _
      himg₀ (limgOk C.toFairChain h' i) hag, WFF.mono_refl] at hm
    refine (congrArg (· ∈ _) (readArrow_sig _ ?_ Ξ)).mp hm
    rw [Term.mono_eta]

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

/-- The born-shape obligation atom along a witness, weakened. -/
theorem mono_retx_oblC {l l' : List VarType} (hsuf : l <:+ l') {A : VarType} {y : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
    {X : VarType} (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ) =
      WFF.retxS hS x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩ (.nec (bornShape A))
        (unarrT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy)).2
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) := by
  change WFF.retxS hS x _ (.nec (bornShape A)) (Term.mono _ _) _ = _
  exact OutLeg.retS_congr hS (.pos x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩) _
    (mono_unarrT hsuf hy) rfl

/-- The witness child's body over the born root is the body read along the witness arrow at the
    born root. -/
theorem liftBodyXR_eq_readArrowX (l : List VarType) (A : VarType) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1) :
    liftBodyXR l A hX Ξ = readArrowX (rclXImg l A X) hX (rclX_cx l A X)
      (Term.eta (.root (.free 0)) (.VTypeBox A) (rclX_born_ref l A X)) Ξ := by
  unfold liftBodyXR readArrowX
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Ξ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [Subst.set_root, Subst.set_root]
    exact .ren_eta _ _
  · change SubE.Sim T (Subst.set _ _ _ v) (Subst.set _ _ _ v)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐**Every obligation along a witness eventually has its witness child**. -/
theorem StrongChain.ret_childXC {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A : VarType}
    {y : ℕ} (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    {x : VarSymb} {X : VarType} (hX : (ctxOf ((C.net n).st s).l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf ((C.net n).st s).l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈
      ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildXC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hX)
          (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = some (x, X) ∧
      (C.net (m + 1)).cx ((C.net m).nch s :: s) = ((C.net m).st s).l.length + 1 ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = Nat.succ ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = [.VTypeBox A] ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = (fun _ => y) ∧
      liftBodyXR ((C.net m).st s).l A ((ctxOf_le_of_suffix hsuf).ref hX)
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∈
          (retChildXC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hX)
            (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retXOp s ⟨_, A, x, y, Ξ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have hX' := (ctxOf_le_of_suffix hsuf).ref hX
  have hin : WFF.retxS hS x ⟨X, hX'⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy').2
      (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∈
        ((C.net m).st s).M := by
    rw [← mono_retx_oblC hsuf hy hX Ξ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s (some (x, X)) (((C.net m).st s).l.length + 1)
      (retChildXC hS hy' hX'
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ))
      Nat.succ [.VTypeBox A] (fun _ => y) := by
    rw [hstep hlm]
    simp only [NetSt.mkRetXC, dif_pos hsuf, dif_pos hy']
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
  exact retChildXC_body hS hy' hX' hM hin

/-- ⭐⭐**A witness child at the limit**: an obligation along `x` at a stage of `s` has a witness
    edge `s → t` for `x` whose way home sends `t`'s root `0` to `y`, with the obligation's body
    read along it at the born root (`StrongChain.ret_childXC`). -/
theorem lretXC (s : LW C.toFairChain) (i : ℕ) {A : VarType} {y : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc) {x : VarSymb}
    {X : VarType} (hX : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf (lat s i)).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1)
    (h : WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2 Ξ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hk : lkd C.toFairChain s t = some (x, X))
      (hcl : [VarType.VTypeBox A] <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧
      readArrowX (limgOk C.toFairChain (lkdR hk) i) hX (lhcx C.toFairChain hk i)
        (Term.eta (.root (.free 0)) (.VTypeBox A) ((ctxOf_le_of_suffix hcl).ref (born_ref A)))
        Ξ ∈ ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, hkind, hcxe, hfcl, hfimg, hbcl, hbimg, hmem⟩ :=
    C.ret_childXC (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy hX Ξ h
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
      (Term.eta (σ := σ) (.root (.free 0)) (.VTypeBox A) (rclX_born_ref _ A X)) Ξ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (liftBodyXR _ A _ _) ∈ _ at hm
    rw [liftBodyXR_eq_readArrowX, ← e1, WFF.mono_mono, readArrowX_mono_congr
      (List.suffix_refl _) _ himg₀ (limgOk C.toFairChain (lkdR hkd) i) hag hX hX _
      (hlcx ▸ lhcx C.toFairChain hkd i), WFF.mono_refl] at hm
    rw [readArrowX_cx _ _ hlcx _ (hlcx ▸ lhcx C.toFairChain hkd i)]
    refine (congrArg (· ∈ _) (readArrowX_sig _ _ _ ?_ Ξ)).mp hm
    rw [Term.mono_eta]

/-- ⭐**With T off, a witnessed returning possibility at aliases is the witnessed obligation** at
    the born shape: `◇_O[⟨d, e⟩ ↦ ⟨y, z⟩] Φ` is `◇_O^{S_A × ◇Z}[⟨u, e⟩ ↦ unarrDT y z] Φ`, the
    born root having no companions. -/
theorem ret_oblDC_noT (hT : ModalSys.T = false) (hS : ModalSys.BStrong = true)
    {l : List VarType} (O : OutLeg (ctxOf l)) {A Z : VarType} {y z : ℕ}
    (hy₁ : (ctxOf l).ref (.root (.free y)) = some A)
    (hz : (ctxOf l).ref (.root (.free z)) = some Z)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.box A) Z).ty) 1) :
    O.retS hS (.wit (bornShape A) Z)
        (unarrDT (σ := σ) (hy₁.trans (congrArg some (bc_box_noT hT A).symm)) hz).2 Φ =
      O.retS hS (.wit (.box A) Z)
        (Term.pair (Term.eta (.root (.free y)) A hy₁) (Term.eta (.root (.free z)) Z hz)) Φ := by
  have hy := hy₁.trans (congrArg some (bc_box_noT hT A).symm)
  obtain ⟨hw, e⟩ := subst_arrow_eta_inner (σ := σ) (retBackImg l A hy)
    (x := .root (.free 0)) (Ctx.ref_inner (born_ref A))
  have e' := e.trans (eta_addr_congr (by
    change itemAt (imgRoot (fun _ => y) (.free 0)) (.root (.free 0)) = _
    rw [itemAt_noT hT]
    rfl) hw hy₁)
  unfold unarrDT unarrT bornShape
  generalize bornComps_ok A = hcs
  revert hcs
  rw [bornComps_noT hT A]
  intro hcs
  exact OutLeg.retS_congr hS O (.wit (.box A) Z) (sig_pair e' rfl) rfl

/-- The witnessed born-shape obligation atom, weakened. -/
theorem mono_retD_oblC {l l' : List VarType} (hsuf : l <:+ l') {A X : VarType} {y z : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (hz : (ctxOf l).ref (.root (.free z)) = some X)
    (Ξ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ) =
      WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy)
          ((ctxOf_le_of_suffix hsuf).ref hz)).2
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) := by
  change WFF.retS hS (.wit (bornShape A) X) (Term.pair (Term.mono _ _) (Term.mono _ _)) _ = _
  exact OutLeg.retS_congr hS .nec _ (sig_pair (mono_unarrT hsuf hy) (by rw [Term.mono_eta]))
    rfl

/-- ⭐**Every witnessed obligation eventually has its back-witness child**. -/
theorem StrongChain.ret_childDC {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A X : VarType}
    {y o z : ℕ}
    (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf ((C.net n).st s).l).ref (.root (.free o)) = some .VTypeOne)
    (hz : (ctxOf ((C.net n).st s).l).ref (.root (.free z)) = some X) (hyo : y ≠ o)
    (Ξ : WFF σ ((ctxOf ((C.net n).st s).l).boxIn.insert (.bnd 0)
      (RShape.wit (bornShape A) X).ty) 1)
    (h : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ ∈
      ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildDC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hz)
          (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∧
      (C.net (m + 1)).bkind ((C.net m).nch s :: s) = some (.root (.free 1), X) ∧
      (C.net (m + 1)).bcx ((C.net m).nch s :: s) = z ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = (· + 2) ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = bclD A X ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = backImgD y o ∧
      liftBodyDR ((C.net m).st s).l A X
        (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∈
          (retChildDC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hz)
            (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retDOp s ⟨_, A, X, (y, o, z), Ξ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have ho' := (ctxOf_le_of_suffix hsuf).ref ho
  have hz' := (ctxOf_le_of_suffix hsuf).ref hz
  have hin : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy' hz').2
      (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ) ∈
        ((C.net m).st s).M := by
    rw [← mono_retD_oblC hsuf hy hz Ξ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s none 0
      (retChildDC hS hy' hz' (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Ξ))
      (· + 2) (bclD A X) (backImgD y o) (some (.root (.free 1), X)) z := by
    rw [hstep hlm]
    simp only [NetSt.mkRetDC, dif_pos hsuf, dif_pos hy', if_pos ho', dif_pos hz', if_pos hin,
      if_pos hyo]
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact retChildDC_body hS hy' hz' hM hin

/-- ⭐⭐**A back-witness child at the limit**: a witnessed obligation at a stage of `s` has a
    forward edge `s → t` whose way home is a witness edge for `t`'s root `e`, sending `t`'s root
    `c` to `y`, with content `z`, and the obligation's body read along the edge at `⟨c, e⟩`
    (`StrongChain.ret_childDC`). -/
theorem lretDC (s : LW C.toFairChain) (i : ℕ) {A X : VarType} {y o z : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf (lat s i)).ref (.root (.free o)) = some .VTypeOne)
    (hz : (ctxOf (lat s i)).ref (.root (.free z)) = some X) (hyo : y ≠ o)
    (Ξ : WFF σ ((ctxOf (lat s i)).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1)
    (h : WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2 Ξ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hst : LR C.toFairChain s t)
      (_ : lkd C.toFairChain t s = some (.root (.free 1), X))
      (hcl : bclD A X <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧ lcx C.toFairChain t s = z ∧
      readArrow (limgOk C.toFairChain hst i)
        (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A)
            ((ctxOf_le_of_suffix hcl).ref (bclD_c A X)))
          (Term.eta (.root (.free 1)) (.VTypeDia X) ((ctxOf_le_of_suffix hcl).ref (bclD_e A X))))
        Ξ ∈ ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, hbk, hbcx, hfcl, hfimg, hbcl, hbimg, hmem⟩ :=
    C.ret_childDC (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy ho hz hyo Ξ h
  let t : LW C.toFairChain := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have h' : LR C.toFairChain s t := Or.inl ⟨_, hc⟩
  have hbt : m < birth C.toFairChain t.2 := le_birth C.toFairChain t.2 hnot
  have hbt' : birth C.toFairChain t.2 ≤ m + 1 := birth_le t.2 hlive
  have hnb : ¬ ∃ c, s.1 = c :: t.1 := not_fwd_of_back (C := C.toFairChain) (t := s) hc
  have hkd : lkd C.toFairChain t s = some (.root (.free 1), X) := by
    rw [lkd, if_neg hnb, if_pos ⟨_, hc⟩, ← bkind_at C.toFairChain t hbt']
    exact hbk
  have hlcx : lcx C.toFairChain t s = z := by
    rw [lcx, if_neg hnb]
    exact (bcx_at C.toFairChain t hbt').symm.trans hbcx
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hcl : bclD A X <:+ lat t (lstg C.toFairChain s t i) :=
    (rclD_suffix _ A X).trans hg.suf
  refine ⟨t, h', hkd, hcl, ?_, hlcx, ?_⟩
  · rw [limg, if_neg hnb, bimgL_eq C.toFairChain hlive (by rw [hbcl]; simp), hbimg]
    rfl
  · have hm := hg.sub _ hmem
    have hag : ∀ r < (lat s i).length, r + 2 = limg C.toFairChain s t r := fun r hr => by
      have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
        rw [hc, hfcl]
        exact lt_of_lt_of_le hr hsuf.length_le
      rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C.toFairChain hlive hlen, hfimg]
    have himg₀ : ImgOk (lat s i) (ctxOf (rclD ((C.net m).st s.1).l A X)) (· + 2) :=
      (rclDImg ((C.net m).st s.1).l A X).suffix hsuf
    have e1 := readArrow_mono_congr hsuf (Ctx.Le.refl _) himg₀ (rclDImg _ A X)
      (fun r _ => rfl) (Term.pair (Term.eta (σ := σ) (.root (.free 0)) (.VTypeBox A)
        (rclD_c _ A X)) (Term.eta (.root (.free 1)) (.VTypeDia X) (rclD_e _ A X))) Ξ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (readArrow (rclDImg _ A X) (Term.pair (Term.eta (.root (.free 0))
      (.VTypeBox A) (rclD_c _ A X)) (Term.eta (.root (.free 1)) (.VTypeDia X)
        (rclD_e _ A X))) _) ∈ _ at hm
    rw [← e1, WFF.mono_mono, readArrow_mono_congr (List.suffix_refl _) _ himg₀
      (limgOk C.toFairChain h' i) hag, WFF.mono_refl] at hm
    refine (congrArg (· ∈ _) (readArrow_sig _ ?_ Ξ)).mp hm
    change (⟨_, Term.pair (Term.mono _ (Term.eta _ _ _)) (Term.mono _ (Term.eta _ _ _))⟩ :
      Σ c, Term σ _ _ c) = _
    rw [Term.mono_eta, Term.mono_eta]

/-- The doubly witnessed born-shape obligation atom, weakened. -/
theorem mono_retXD_oblC {l l' : List VarType} (hsuf : l <:+ l') {A Xe : VarType} {y z : ℕ}
    (hy : (ctxOf l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (hz : (ctxOf l).ref (.root (.free z)) = some Xe) {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1) :
    WFF.mono (ctxOf_le_of_suffix hsuf)
        (WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ) =
      WFF.retxS hS x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩ (.wit (bornShape A) Xe)
        (unarrDT (σ := σ) ((ctxOf_le_of_suffix hsuf).ref hy)
          ((ctxOf_le_of_suffix hsuf).ref hz)).2
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) := by
  change WFF.retxS hS x _ (.wit (bornShape A) Xe) (Term.pair (Term.mono _ _) (Term.mono _ _))
    _ = _
  exact OutLeg.retS_congr hS (.pos x ⟨X, (ctxOf_le_of_suffix hsuf).ref hX⟩) _
    (sig_pair (mono_unarrT hsuf hy) (by rw [Term.mono_eta])) rfl

/-- ⭐**Every doubly witnessed obligation eventually has its child**. -/
theorem StrongChain.ret_childXDC {n : ℕ} {s : Node} (hs : (C.net n).Live s) {A Xe : VarType}
    {y o z : ℕ}
    (hy : (ctxOf ((C.net n).st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf ((C.net n).st s).l).ref (.root (.free o)) = some .VTypeOne)
    (hz : (ctxOf ((C.net n).st s).l).ref (.root (.free z)) = some Xe) (hyo : y ≠ o)
    {x : VarSymb} {X : VarType} (hX : (ctxOf ((C.net n).st s).l).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf ((C.net n).st s).l).diaIn x).insert (.bnd 0)
      (RShape.wit (bornShape A) Xe).ty) 1)
    (h : WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ ∈
      ((C.net n).st s).M) :
    ∃ m, n ≤ m ∧ ∃ hsuf : ((C.net n).st s).l <:+ ((C.net m).st s).l,
      ¬ (C.net m).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).Live ((C.net m).nch s :: s) ∧
      (C.net (m + 1)).st ((C.net m).nch s :: s) =
        retChildXDC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hz)
          ((ctxOf_le_of_suffix hsuf).ref hX)
          (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∧
      (C.net (m + 1)).kind ((C.net m).nch s :: s) = some (x, X) ∧
      (C.net (m + 1)).cx ((C.net m).nch s :: s) = ((C.net m).st s).l.length + 2 ∧
      (C.net (m + 1)).bkind ((C.net m).nch s :: s) = some (.root (.free 1), Xe) ∧
      (C.net (m + 1)).bcx ((C.net m).nch s :: s) = z ∧
      (C.net (m + 1)).fcl ((C.net m).nch s :: s) = ((C.net m).st s).l ∧
      (C.net (m + 1)).fimg ((C.net m).nch s :: s) = (· + 2) ∧
      (C.net (m + 1)).bcl ((C.net m).nch s :: s) = bclD A Xe ∧
      (C.net (m + 1)).bimg ((C.net m).nch s :: s) = backImgD y o ∧
      liftBodyXDR ((C.net m).st s).l A Xe ((ctxOf_le_of_suffix hsuf).ref hX)
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∈
          (retChildXDC hS ((ctxOf_le_of_suffix hsuf).ref hy) ((ctxOf_le_of_suffix hsuf).ref hz)
            ((ctxOf_le_of_suffix hsuf).ref hX)
            (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ)).M := by
  obtain ⟨m, hnm, hstep⟩ := C.retXDOp s ⟨_, A, Xe, x, (y, o, z), Ξ⟩ n
  have hlm := C.live_mono hnm hs
  have hsuf := C.lang_suffix hnm hs
  have hg := (C.ext hnm).grows s hs
  have hM := (C.good m).mcs s hlm
  have hy' := (ctxOf_le_of_suffix hsuf).ref hy
  have ho' := (ctxOf_le_of_suffix hsuf).ref ho
  have hz' := (ctxOf_le_of_suffix hsuf).ref hz
  have hX' := (ctxOf_le_of_suffix hsuf).ref hX
  have hin : WFF.retxS hS x ⟨X, hX'⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy' hz').2
      (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ) ∈
        ((C.net m).st s).M := by
    rw [← mono_retXD_oblC hsuf hy hz hX Ξ]
    exact hg.sub _ h
  have hst : C.net (m + 1) = (C.net m).newChild s (some (x, X)) (((C.net m).st s).l.length + 2)
      (retChildXDC hS hy' hz' hX'
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Ξ))
      (· + 2) (bclD A Xe) (backImgD y o) (some (.root (.free 1), Xe)) z := by
    rw [hstep hlm]
    simp only [NetSt.mkRetXDC, dif_pos hsuf, dif_pos hy', if_pos ho', dif_pos hz', if_pos hyo]
    split
    · rename_i X'' hX''
      obtain rfl : X'' = X := by
        rw [hX'] at hX''
        exact (VarType.VTypeDia.inj (Option.some.inj hX'')).symm
      rw [if_pos hin]
    · rename_i hne
      exact absurd hX' (hne X)
  refine ⟨m, hnm, hsuf, NetSt.not_live_new s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    exact (NetSt.live_newChild hlm _ _ _ _).mpr (Or.inr rfl)
  all_goals first
    | (rw [hst]; exact Function.update_self _ _ _)
    | skip
  exact retChildXDC_body hS hy' hz' hX' hM hin

/-- ⭐⭐**A doubly witnessed child at the limit**: a doubly witnessed obligation along `x` at a
    stage of `s` has a witness edge `s → t` for `x` whose way home is a witness edge for `t`'s
    root `e`, sending `t`'s root `c` to `y`, with content `z`, and the obligation's body read
    along the edge at `⟨c, e⟩` (`StrongChain.ret_childXDC`). -/
theorem lretXDC (s : LW C.toFairChain) (i : ℕ) {A Xe : VarType} {y o z : ℕ}
    (hy : (ctxOf (lat s i)).ref (.root (.free y)) = some (VarType.VTypeBox A).bc)
    (ho : (ctxOf (lat s i)).ref (.root (.free o)) = some .VTypeOne)
    (hz : (ctxOf (lat s i)).ref (.root (.free z)) = some Xe) (hyo : y ≠ o) {x : VarSymb}
    {X : VarType} (hX : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (Ξ : WFF σ (((ctxOf (lat s i)).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1)
    (h : WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2 Ξ ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hk : lkd C.toFairChain s t = some (x, X))
      (_ : lkd C.toFairChain t s = some (.root (.free 1), Xe))
      (hcl : bclD A Xe <:+ lat t (lstg C.toFairChain s t i)),
      limg C.toFairChain t s 0 = y ∧ lcx C.toFairChain t s = z ∧
      readArrowX (limgOk C.toFairChain (lkdR hk) i) hX (lhcx C.toFairChain hk i)
        (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A)
            ((ctxOf_le_of_suffix hcl).ref (bclD_c A Xe)))
          (Term.eta (.root (.free 1)) (.VTypeDia Xe)
            ((ctxOf_le_of_suffix hcl).ref (bclD_e A Xe)))) Ξ ∈
          ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, hnot, hlive, hst, hkind, hcxe, hbk, hbcx, hfcl, hfimg, hbcl, hbimg,
    hmem⟩ := C.ret_childXDC (live_birth C.toFairChain s.2 (Nat.le_add_right _ i)) hy ho hz hyo
      hX Ξ h
  let t : LW C.toFairChain := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have hbt : m < birth C.toFairChain t.2 := le_birth C.toFairChain t.2 hnot
  have hbt' : birth C.toFairChain t.2 ≤ m + 1 := birth_le t.2 hlive
  have hnb : ¬ ∃ c, s.1 = c :: t.1 := not_fwd_of_back (C := C.toFairChain) (t := s) hc
  have hkd : lkd C.toFairChain s t = some (x, X) := by
    rw [lkd, if_pos ⟨_, hc⟩, ← kind_at C.toFairChain t hbt']
    exact hkind
  have hlcx : lcx C.toFairChain s t = ((C.net m).st s.1).l.length + 2 := by
    rw [lcx, if_pos ⟨_, hc⟩]
    exact (cx_at C.toFairChain t hbt').symm.trans hcxe
  have hkdb : lkd C.toFairChain t s = some (.root (.free 1), Xe) := by
    rw [lkd, if_neg hnb, if_pos ⟨_, hc⟩, ← bkind_at C.toFairChain t hbt']
    exact hbk
  have hlcxb : lcx C.toFairChain t s = z := by
    rw [lcx, if_neg hnb]
    exact (bcx_at C.toFairChain t hbt').symm.trans hbcx
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hcl : bclD A Xe <:+ lat t (lstg C.toFairChain s t i) :=
    (rclXD_suffix _ A X Xe).trans hg.suf
  refine ⟨t, hkd, hkdb, hcl, ?_, hlcxb, ?_⟩
  · rw [limg, if_neg hnb, bimgL_eq C.toFairChain hlive (by rw [hbcl]; simp), hbimg]
    rfl
  · have hm := hg.sub _ hmem
    have hag : ∀ r < (lat s i).length, r + 2 = limg C.toFairChain s t r := fun r hr => by
      have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
        rw [hc, hfcl]
        exact lt_of_lt_of_le hr hsuf.length_le
      rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C.toFairChain hlive hlen, hfimg]
    have himg₀ : ImgOk (lat s i) (ctxOf (X :: rclD ((C.net m).st s.1).l A Xe)) (· + 2) :=
      (rclXDImg ((C.net m).st s.1).l A X Xe).suffix hsuf
    have e1 := readArrowX_mono_congr hsuf (Ctx.Le.refl _) himg₀ (rclXDImg _ A X Xe)
      (fun _ _ => rfl) hX ((ctxOf_le_of_suffix hsuf).ref hX) (rclXD_cx _ A X Xe)
      (rclXD_cx _ A X Xe) (Term.pair (Term.eta (σ := σ) (.root (.free 0)) (.VTypeBox A)
        (rclXD_c _ A X Xe)) (Term.eta (.root (.free 1)) (.VTypeDia Xe) (rclXD_e _ A X Xe))) Ξ
    rw [Term.mono_refl] at e1
    change WFF.mono _ (readArrowX (rclXDImg _ A X Xe) ((ctxOf_le_of_suffix hsuf).ref hX)
      (rclXD_cx _ A X Xe) (Term.pair (Term.eta (.root (.free 0)) (.VTypeBox A)
        (rclXD_c _ A X Xe)) (Term.eta (.root (.free 1)) (.VTypeDia Xe) (rclXD_e _ A X Xe))) _)
      ∈ _ at hm
    rw [← e1, WFF.mono_mono, readArrowX_mono_congr (List.suffix_refl _) _ himg₀
      (limgOk C.toFairChain (lkdR hkd) i) hag hX hX _ (hlcx ▸ lhcx C.toFairChain hkd i),
      WFF.mono_refl] at hm
    rw [readArrowX_cx _ _ hlcx _ (hlcx ▸ lhcx C.toFairChain hkd i)]
    refine (congrArg (· ∈ _) (readArrowX_sig _ _ _ ?_ Ξ)).mp hm
    change (⟨_, Term.pair (Term.mono _ (Term.eta _ _ _)) (Term.mono _ (Term.eta _ _ _))⟩ :
      Σ c, Term σ _ _ c) = _
    rw [Term.mono_eta, Term.mono_eta]

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
    (`lalias`), move the atom to the alias (`ret_alias`), read it as the obligation at the born
    shape (`ret_oblC_noT`), take its returning child (`lretC`): the body holds there at the born
    root `c = □(c.inner)`, and `c.inner` comes home as the alias (`subst_arrow_eta_inner`), `Ind`
    to the value (`lalias_ind`). -/
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
  have hobl := (congrArg (· ∈ _) (ret_oblC_noT hT hS .nec hy₁ _)).mpr hy
  obtain ⟨k, hsk, hcl, hback, hmk⟩ := lretC C s i₁ _ _ hobl
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k i₁ := lstg_mono C hsk hii₁
  have hcA : (ctxOf (lat k (lstg C.toFairChain s k i₁))).boxIn.ref
      (VarSymb.root (.free 0)).inner = some A :=
    Ctx.ref_inner ((ctxOf_le_of_suffix hcl).ref (born_ref A))
  refine ⟨k, hsk, lstg C.toFairChain s k i₁, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A hcA, ?_, ?_⟩
  · have e := readArrow_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C hT).w k).le hj))
      (limgOk C.toFairChain hsk i₁) (fun _ _ => rfl)
      (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A hcA)) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  · have hiK : i₁ ≤ lstg C.toFairChain k s (lstg C.toFairChain s k i₁) := by
      have h₁ := (lstg_spec C.toFairChain hsk i₁).1
      have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k i₁)).1
      omega
    have hyK := (((bdataS C hT).w s).le hiK).ref hy₁
    obtain ⟨hw, hhome⟩ := subst_arrow_eta_inner (σ := σ) (limgOk C.toFairChain hsk.symm
      (lstg C.toFairChain s k i₁)) hcA
    have hhome' := hhome.trans (eta_addr_congr (by
      change itemAt (imgRoot (limg C.toFairChain k s) (.free 0)) (.root (.free 0)) = _
      rw [itemAt_noT hT]
      change VarSymb.root (.free (limg C.toFairChain k s 0)) = _
      rw [hback]) hw hyK)
    have e2 := congrArg (fun p : Σ b, Term σ _ A b =>
      (bdataS C hT).rden s _ (Ctx.Le.refl _) p.2) hhome'
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
  | .boxC A (p :: ps) h => .packC A (p :: ps) h
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

/-- The address of a packed `□A` object's own contents, ahead of its companions'. -/
def compsFstAddr : List (List Step) → VarSymb → VarSymb
  | [], u => u
  | _ :: ps, u => compsFstAddr ps (.step u .fst)

omit [ModalSys.NoFour] in
theorem ref_compsFstAddr {Δ : Ctx} {A : VarType} : ∀ (cs : List (List Step)) {u : VarSymb},
    Δ.ref u = some (A.compsFlat cs) → Δ.ref (compsFstAddr cs u) = some A
  | [], _, h => h
  | _ :: ps, _, h => ref_compsFstAddr ps (Ctx.ref_fst_of h)

/-- ⭐The **unpacking** of one necessary object into a necessary shape's object: `□⟨a, b⟩ ↦
    ⟨□a, □b⟩`, recursively. -/
def unpackN : (N : NShape) → Σ b, Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox N.flat)) N.ty b
  | .box A => ⟨_, Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ _ _)⟩
  | .boxC A (p :: ps) _ => ⟨_, Term.boxtm (Term.eta
      (compsFstAddr (p :: ps) (VarSymb.root (.bnd 0)).inner) A
      (ref_compsFstAddr (p :: ps) (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))))⟩
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
theorem holeAt_packN_unpackN (hT : ModalSys.T = false) : (N : NShape) → {Γ : Ctx} →
    {c : Ann N.ty} →
    (x : Term σ Γ N.ty c) →
    (⟨_, Term.holeAt (Term.holeAt x (packN (σ := σ) N).obj.2) (unpackN N).2⟩ :
      Σ e, Term σ Γ N.ty e) = ⟨c, x⟩
  | .box A, Γ, c, x => by
      exact (Term.holeAt_congr_sig (Term.holeAt_eta_root x) _).trans (Term.holeAt_eta_root x)
  | .boxC _ (_ :: _) h, _, _, _ =>
      absurd ((h.resolve_left (List.cons_ne_nil _ _)).1.symm.trans hT) (by decide)
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
        exact holeAt_packN_unpackN hT R x₁
      · refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
          ((holeAt_box_snd s₁ s₂ _).trans h₂.symm) _).trans ?_)
        exact holeAt_packN_unpackN hT S x₂

/-- Packing then unpacking, on the slot. -/
theorem holeAt_packN_unpackN_slot (hT : ModalSys.T = false) (N : NShape) :
    (⟨_, Term.holeAt (packN (σ := σ) N).obj.2 (unpackN N).2⟩ :
      Σ e, Term σ (Ctx.empty.insert (.bnd 0) N.ty) N.ty e) =
      ⟨_, Term.eta (.root (.bnd 0)) N.ty (Ctx.ref_insert_root _ _ _)⟩ := by
  have h := holeAt_packN_unpackN hT N (σ := σ)
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
  rw [WFF.bodyRepl_congr (sig_mono _ (holeAt_packN_unpackN_slot (ModalSys.NoFour.noTStrong hS) N))]
  exact congrArg (O.retS hS (.nec N) t) (WFF.bodyRepl_eta Φ).symm

/-- The unpacking at a witnessed shape: the necessary part unpacked, the possible part kept. -/
def unpackW (N : NShape) (Z : VarType) :
    Σ b, Term σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.box N.flat) Z).ty) (RShape.wit N Z).ty b :=
  ⟨_, Term.pair (Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox N.flat)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))) (unpackN N).2)
    (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeDia Z)
      (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))⟩

/-- Packing then unpacking at a witnessed shape, on the slot. -/
theorem holeAt_packN_unpackW (hT : ModalSys.T = false) (N : NShape) (Z : VarType) :
    (⟨_, Term.holeAt (ShapeMap.liftObj (σ := σ) (.wit N Z) (packN N)).2 (unpackW N Z).2⟩ :
      Σ e, Term σ (Ctx.empty.insert (.bnd 0) (RShape.wit N Z).ty) (RShape.wit N Z).ty e) =
      ⟨_, Term.eta (.root (.bnd 0)) (RShape.wit N Z).ty (Ctx.ref_insert_root _ _ _)⟩ := by
  dsimp only [ShapeMap.liftObj, unpackW]
  refine sig_pair ?_ (Term.holeAt_pair_snd _ _)
  refine (Term.holeAt_holeAt_sig _ _ _).trans ((Term.holeAt_congr_sig
    (Term.holeAt_pair_fst _ _) _).trans ?_)
  exact holeAt_packN_unpackN hT N _

/-- ⭐A returning possibility at a witnessed shape is one at `□ × ◇`: `ret_map` along the packing
    map, the body read back through the unpacking. -/
def retS_packNW (hS : ModalSys.BStrong = true) {Γ : Ctx} [Γ.NoSlots] (O : OutLeg Γ)
    {Δ : List (WFF σ Γ 0)} {N : NShape} {Z : VarType} {a : Ann (RShape.wit N Z).flat}
    (t : Term σ Γ (RShape.wit N Z).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (p : Proof σ Γ Δ (O.retS hS (.wit N Z) t Φ)) :
    Proof σ Γ Δ (O.retS hS (.wit (.box N.flat) Z)
      (Term.holeRead t (ShapeMap.liftVal (.wit N Z) (packN N)).2)
      (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unpackW N Z).2) Φ)) := by
  refine Proof.ret_map hS O (S := .wit N Z) (packN N) t _ (Proof.conv ?_ p)
  change O.retS hS (.wit N Z) t Φ = O.retS hS (.wit N Z) t (WFF.bodyRepl _ (WFF.bodyRepl _ Φ))
  rw [WFF.bodyRepl_bodyRepl, WFF.bodyRepl_congr
    (sig_mono _ (holeAt_packN_unpackW (ModalSys.NoFour.noTStrong hS) N Z))]
  exact congrArg (O.retS hS (.wit N Z) t) (WFF.bodyRepl_eta Φ).symm

omit [ModalSys.NoFour] in
/-- Every term of a product type is a pair. -/
theorem Term.exists_pair {Γ : Ctx} {A B : VarType} {c : Ann (.VTypeProd A B)}
    (g : Term σ Γ (.VTypeProd A B) c) :
    ∃ (a : Ann A) (b : Ann B) (t₁ : Term σ Γ A a) (t₂ : Term σ Γ B b),
      (⟨c, g⟩ : Σ e, Term σ Γ (.VTypeProd A B) e) = ⟨_, Term.pair t₁ t₂⟩ := by
  match g with
  | .pair t₁ t₂ => exact ⟨_, _, t₁, t₂, rfl⟩

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
theorem ncb_unpackN (hT : ModalSys.T = false) {s k : B.W} (r : B.RT k s) : ∀ (N : NShape)
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
  | .boxC _ (_ :: _) hc, _, _, _ =>
      absurd ((hc.resolve_left (List.cons_ne_nil _ _)).1.symm.trans hT) (by decide)
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
        refine ncb_unpackN hT r R _ o.1 ?_
        exact (congrArg (fun x => B.Ind x _) (necEval_boxFst E _ _)).mpr h₁
      · have h₂ := ind_map (Term.eta (.step (.root (.bnd 0)) .snd) S.flat
          (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
            (.VTypeProd R.flat S.flat)))) h
        unfold Model.holeVal at h₂
        rw [Model.interp_eta_slot_snd] at h₂
        erw [Model.interp_eta_slot_snd] at h₂
        change B.model.NComesBack S (Model.interp _ (Term.holeAt _ _)) r o.2
        rw [Model.interp_holeAt]
        refine ncb_unpackN hT r S _ o.2 ?_
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
  refine ncb_unpackN (B.noT_of_strong hS) (Or.inl (B.symm hR)) N _ _ ?_
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
  refine ncb_unpackN (B.noT_of_strong hS) (Or.inl (B.symm hR)) N _ _ ?_
  rw [Model.box_beta, boxPush_canon_at k j ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
    ← Model.interp_subst, interp_canon _ (Model.Env.Agree.refl' _),
    ← Model.interp_holeRead (noProjLast s i), interp_canon _ (Model.Env.Agree.refl' _)]
  exact hInd

/-- ⭐**Returning successors at a witnessed shape** (plain leg, `□ × ◇`): a returning possibility
    valued at a pair has an arrow `s → k`, a term `g` of `k`'s `□` view and a witness `e` of `k`
    whose way home is the witness edge back, with `Φ(⟨□g, e⟩)` at `k` (read along the arrow); `g`
    read home is `Ind` to the first value and `e`'s content there to the second.  The limit of a
    strong chain has it (`bdataS_retOutD`). -/
def RetOutD (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {A Z : VarType} {a₁ : Ann A} {a₂ : Ann Z}
    (t₁ : Term σ ((B.w s).ctx i) A a₁) (t₂ : Term σ ((B.w s).ctx i) Z a₂)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit (.box A) Z).ty) 1),
    WFF.retS hS (.wit (.box A) Z) (Term.pair t₁ t₂) Φ ∈ (B.w s).M i →
      ∃ (k : B.W) (h : B.R s k) (j : ℕ) (hj : B.stg s k i ≤ j) (b : Ann A)
        (g : Term σ ((B.w k).ctx j).boxIn A b) (e : VarSymb)
        (he : ((B.w k).ctx j).ref e = some (.VTypeDia Z)) (hk : B.kd k s = some (e, Z)),
        readArrow ((B.imgOk h i).mono ((B.w k).le hj))
          (Term.pair (Term.boxtm g) (Term.eta e (.VTypeDia Z) he)) Φ ∈ (B.w k).M j ∧
        B.Ind (B.toDom A s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm h) j)) (coh_arrowS (B.imgOk (B.symm h) j)) g))
            (definable_rden _ _))
          (B.toDom A s (B.rden s i (Ctx.Le.refl _) t₁) (definable_rden _ _)) ∧
        B.Ind (B.toDom Z s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.eta (.root (.free (B.cx k s))) Z (B.hcx hk j))) (definable_rden _ _))
          (B.toDom Z s (B.rden s i (Ctx.Le.refl _) t₂) (definable_rden _ _))

/-- The unpacking at a witnessed shape, semantically. -/
theorem holeVal_unpackW {k : B.W} (N : NShape) (Z : VarType)
    (E : B.model.frame.Dom (RShape.wit (.box N.flat) Z).ty k) :
    B.model.holeVal (unpackW (σ := σ) N Z).2 E =
      (B.model.holeVal (unpackN (σ := σ) N).2 E.1, E.2) := by
  unfold Model.holeVal
  change (Model.interp _ (Term.holeAt _ _), Model.interp _ (Term.eta _ _ _)) = _
  rw [Model.interp_holeAt, Model.interp_eta_slot_snd]
  unfold Model.holeVal
  erw [Model.interp_eta_slot_fst]

/-- The packing's value at a witnessed shape, semantically. -/
theorem holeVal_liftVal_packN {s : B.W} (N : NShape) (Z : VarType)
    (o : B.model.frame.Dom (RShape.wit N Z).flat s) :
    B.model.holeVal (ShapeMap.liftVal (σ := σ) (.wit N Z) (packN N)).2 o =
      (B.model.holeVal (packN (σ := σ) N).val.2 o.1, o.2) := by
  unfold Model.holeVal
  change (Model.interp _ (Term.holeAt _ _), Model.interp _ (Term.eta _ _ _)) = _
  rw [Model.interp_holeAt, Model.interp_eta_slot_snd]
  unfold Model.holeVal
  rw [Model.interp_eta_slot_fst]

/-- ⭐**A canonical witness variable's possible object comes back** along the witness edge home:
    the way home is in its extent, with content the edge's content variable (`dia_beta`,
    `diaPush_canon_at`). -/
theorem posEval_eta_home {k s : B.W} {j : ℕ} {e : VarSymb} {Z : VarType}
    (he : ((B.w k).ctx j).ref e = some (.VTypeDia Z)) (hk : B.kd k s = some (e, Z))
    {o : B.model.frame.Dom Z s}
    (hI : B.Ind (B.toDom Z s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
      (Term.eta (.root (.free (B.cx k s))) Z (B.hcx hk j))) (definable_rden _ _)) o) :
    ∃ h : (⟨s, ⟨Or.inl (B.kdR hk)⟩⟩ : B.model.frame.Acc k) ∈ (B.model.posEval
        (Model.interp (B.canonEnv k j) (Term.eta e (.VTypeDia Z) he) :
          B.model.frame.Pos Z k)).1,
      B.Ind ((B.model.posEval (Model.interp (B.canonEnv k j) (Term.eta e (.VTypeDia Z) he) :
        B.model.frame.Pos Z k)).2 ⟨_, h⟩) o := by
  have hD : B.model.posEval (Model.interp (B.canonEnv k j) (Term.eta e (.VTypeDia Z) he) :
      B.model.frame.Pos Z k) = ⟨_, fun w' => Model.interp ((B.canonEnv k j).diaPush e he w')
        (Term.eta (σ := σ) (.step e .dia) Z (Ctx.ref_diaIn_of he))⟩ :=
    Model.dia_beta _ ⟨Z, he⟩ he _
  generalize B.model.posEval (Model.interp (B.canonEnv k j) (Term.eta e (.VTypeDia Z) he) :
      B.model.frame.Pos Z k) = Q at hD ⊢
  subst hD
  have hmem : (⟨s, ⟨Or.inl (B.kdR hk)⟩⟩ : B.Acc k) ∈
      (B.model.posEval ((B.canonEnv k j).ref e he)).1 := by
    rw [canonEnv_extent k j he]
    exact Or.inl ⟨Z, hk⟩
  refine ⟨hmem, ?_⟩
  dsimp only
  rw [diaPush_canon_at k j he ⟨_, hmem⟩ hk le_rfl,
    ← Model.interp_subst (ι := arrowXIdx (B.img k s) e (B.cx k s)) _ _
      (coh_arrowXS ((B.imgOk (B.kdR hk) j).mono ((B.w s).le le_rfl)) he
        (((B.w s).le le_rfl).ref (B.hcx hk j)))]
  rw [← interp_canon_eta] at hI
  refine (congrArg (fun x => B.Ind x o) ?_).mpr hI
  refine congrArg (fun p : Σ b, Term σ ((B.w s).ctx (B.stg k s j)) Z b =>
    Model.interp (B.canonEnv s (B.stg k s j)) p.2) (Term.subst_eta_renAt _ _ _ Z _ _ _ _ ?_)
  change (if Step.isProj .dia then _ else _) = _
  rw [if_neg (by decide)]
  change (if e = e then _ else _) = _
  exact if_pos rfl

/-- ⭐⭐**`ret`, membership ⇒ truth at every witnessed shape** (plain leg): pack the necessary
    part into one `□` (`retS_packNW`), take the returning successor (`RetOutD`), unpack its
    object (`ncb_unpackN`), and its witness comes home along the witness edge
    (`posEval_eta_home`). -/
theorem sat_retS_wit_of_mem (hS : ModalSys.BStrong = true) (hRO : B.RetOutD hS) {s : B.W}
    {i : ℕ} {N : NShape} {Z : VarType} {a : Ann (RShape.wit N Z).flat}
    (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) := by
  have hsz : (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0).size =
      Φ.size + (RShape.wit N Z).flat.eqRecSize + 1 := rfl
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packNW hS .nec t Φ (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨_, _, t₁, t₂, ht⟩ := Term.exists_pair
    (Term.holeRead t (ShapeMap.liftVal (σ := σ) (.wit N Z) (packN N)).2)
  have hp' := (congrArg (· ∈ (B.w s).M i)
    (OutLeg.retS_congr hS .nec (.wit (.box N.flat) Z) ht rfl)).mp hp
  obtain ⟨k, hR, j, hj, b, g, e, he, hk, hmem, hInd₁, hInd₂⟩ := hRO t₁ t₂ _ hp'
  rw [readArrow_bodyRepl] at hmem
  have hsat := (IH k j _ (by
    rw [hsz]; unfold readArrow; rw [WFF.size_subst]; omega)).mpr hmem
  rw [sat_readArrow, ← boxPush_canon_at s i ⟨k, ⟨Or.inl hR⟩⟩ hR hj] at hsat
  refine ⟨⟨k, ⟨Or.inl hR⟩⟩, _, hsat, Or.inl (B.symm hR), ?_⟩
  have hv := congrArg (fun p : Σ c, Term σ ((B.w s).ctx i) (RShape.wit (.box N.flat) Z).flat c =>
    Model.interp (B.canonEnv s i) p.2) ht
  simp only [Model.interp_holeRead (noProjLast s i), holeVal_liftVal_packN] at hv
  change B.model.ComesBack (.wit N Z) (Model.interp _ (Term.holeAt _ _)) _ _
  rw [Model.interp_holeAt, holeVal_unpackW]
  refine ⟨ncb_unpackN (B.noT_of_strong hS) (Or.inl (B.symm hR)) N _ _ ?_, ?_⟩
  · rw [show B.model.holeVal (packN (σ := σ) N).val.2 (Model.interp (B.canonEnv s i) t).1 =
      Model.interp (B.canonEnv s i) t₁ from congrArg Prod.fst hv]
    change B.Ind (B.model.necEval (Model.interp _ (Term.boxtm g)) _) _
    rw [Model.box_beta, boxPush_canon_at k j ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
      ← Model.interp_subst, interp_canon _ (Model.Env.Agree.refl' _),
      interp_canon t₁ (Model.Env.Agree.refl' _)]
    exact hInd₁
  · rw [show (Model.interp (B.canonEnv s i) t).2 = Model.interp (B.canonEnv s i) t₂ from
      congrArg Prod.snd hv, interp_canon t₂ (Model.Env.Agree.refl' _)]
    exact posEval_eta_home he hk hInd₂

/-- ⭐**Returning successors along a witness at a witnessed shape** (`□ × ◇`): as `RetOutD`,
    along an arrow of `y`'s extent.  The limit of a strong chain has it (`bdataS_retOutXD`). -/
def RetOutXD (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {y : VarSymb} {Y : VarType}
    (hy : ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {A Z : VarType} {a₁ : Ann A}
    {a₂ : Ann Z} (t₁ : Term σ ((B.w s).ctx i) A a₁) (t₂ : Term σ ((B.w s).ctx i) Z a₂)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (RShape.wit (.box A) Z).ty) 1),
    (OutLeg.pos y ⟨Y, hy⟩ : OutLeg ((B.w s).ctx i)).retS hS (.wit (.box A) Z)
        (Term.pair t₁ t₂) Φ ∈ (B.w s).M i →
      ∃ (k : B.W) (hk : B.kd s k = some (y, Y)) (j : ℕ) (hj : B.stg s k i ≤ j) (b : Ann A)
        (g : Term σ ((B.w k).ctx j).boxIn A b) (e : VarSymb)
        (he : ((B.w k).ctx j).ref e = some (.VTypeDia Z)) (hke : B.kd k s = some (e, Z)),
        readArrowX ((B.imgOk (B.kdR hk) i).mono ((B.w k).le hj)) hy
            (((B.w k).le hj).ref (B.hcx hk i))
            (Term.pair (Term.boxtm g) (Term.eta e (.VTypeDia Z) he)) Φ ∈ (B.w k).M j ∧
        B.Ind (B.toDom A s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm (B.kdR hk)) j))
              (coh_arrowS (B.imgOk (B.symm (B.kdR hk)) j)) g))
            (definable_rden _ _))
          (B.toDom A s (B.rden s i (Ctx.Le.refl _) t₁) (definable_rden _ _)) ∧
        B.Ind (B.toDom Z s (B.rden s (B.stg k s j) (Ctx.Le.refl _)
            (Term.eta (.root (.free (B.cx k s))) Z (B.hcx hke j))) (definable_rden _ _))
          (B.toDom Z s (B.rden s i (Ctx.Le.refl _) t₂) (definable_rden _ _))

/-- ⭐⭐**`ret` along a witness, membership ⇒ truth at every witnessed shape**: as
    `sat_retS_wit_of_mem`, along an arrow of `y`'s extent (`RetOutXD`, `diaPush_canon_at`). -/
theorem sat_retxS_wit_of_mem (hS : ModalSys.BStrong = true) (hRX : B.RetOutXD hS) {s : B.W}
    {i : ℕ} {y : VarSymb} (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape}
    {Z : VarType} {a : Ann (RShape.wit N Z).flat}
    (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ :
        WFF σ _ 0).size → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈
      (B.w s).M i) :
    B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ : WFF σ _ 0) := by
  have hsz : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ :
      WFF σ _ 0).size = Φ.size + (RShape.wit N Z).flat.eqRecSize + 1 := rfl
  obtain ⟨Y, hY⟩ := hy
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packNW hS (.pos y ⟨Y, hY⟩) t Φ (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨_, _, t₁, t₂, ht⟩ := Term.exists_pair
    (Term.holeRead t (ShapeMap.liftVal (σ := σ) (.wit N Z) (packN N)).2)
  have hp' := (congrArg (· ∈ (B.w s).M i)
    (OutLeg.retS_congr hS (.pos y ⟨Y, hY⟩) (.wit (.box N.flat) Z) ht rfl)).mp hp
  obtain ⟨k, hk, j, hj, b, g, e, he, hke, hmem, hInd₁, hInd₂⟩ := hRX hY t₁ t₂ _ hp'
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
  have hv := congrArg (fun p : Σ c, Term σ ((B.w s).ctx i) (RShape.wit (.box N.flat) Z).flat c =>
    Model.interp (B.canonEnv s i) p.2) ht
  simp only [Model.interp_holeRead (noProjLast s i), holeVal_liftVal_packN] at hv
  change B.model.ComesBack (.wit N Z) (Model.interp _ (Term.holeAt _ _)) _ _
  rw [Model.interp_holeAt, holeVal_unpackW]
  refine ⟨ncb_unpackN (B.noT_of_strong hS) (Or.inl (B.symm hR)) N _ _ ?_, ?_⟩
  · rw [show B.model.holeVal (packN (σ := σ) N).val.2 (Model.interp (B.canonEnv s i) t).1 =
      Model.interp (B.canonEnv s i) t₁ from congrArg Prod.fst hv]
    change B.Ind (B.model.necEval (Model.interp _ (Term.boxtm g)) _) _
    rw [Model.box_beta, boxPush_canon_at k j ⟨s, ⟨Or.inl (B.symm hR)⟩⟩ (B.symm hR) le_rfl,
      ← Model.interp_subst, interp_canon _ (Model.Env.Agree.refl' _),
      interp_canon t₁ (Model.Env.Agree.refl' _)]
    exact hInd₁
  · rw [show (Model.interp (B.canonEnv s i) t).2 = Model.interp (B.canonEnv s i) t₂ from
      congrArg Prod.snd hv, interp_canon t₂ (Model.Env.Agree.refl' _)]
    exact posEval_eta_home he hke hInd₂

end BData

section LimitOutX

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐⭐**The limit has returning successors along a witness** (`□` shape; T off): as
    `bdataS_retOut`, with the witness child (`ret_aliasX`, `ret_oblC_noT` along `x`, `lretXC`). -/
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
  have hobl := (congrArg (· ∈ _) (ret_oblC_noT hT hS (.pos y ⟨Y, hyi₁⟩) hy₁ _)).mpr hy'
  obtain ⟨k, hk, hcl, hback, hmk⟩ := lretXC C s i₁ _ hyi₁ _ hobl
  have hsk := lkdR hk
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k i₁ := lstg_mono C hsk hii₁
  have hcA : (ctxOf (lat k (lstg C.toFairChain s k i₁))).boxIn.ref
      (VarSymb.root (.free 0)).inner = some A :=
    Ctx.ref_inner ((ctxOf_le_of_suffix hcl).ref (born_ref A))
  refine ⟨k, hk, lstg C.toFairChain s k i₁, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A hcA, ?_, ?_⟩
  · have e := readArrowX_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C hT).w k).le hj))
      (limgOk C.toFairChain hsk i₁) (fun _ _ => rfl) hy hyi₁
      ((((bdataS C hT).w k).le hj).ref ((bdataS C hT).hcx hk i)) (lhcx C.toFairChain hk i₁)
      (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A hcA)) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  · have hiK : i₁ ≤ lstg C.toFairChain k s (lstg C.toFairChain s k i₁) := by
      have h₁ := (lstg_spec C.toFairChain hsk i₁).1
      have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k i₁)).1
      omega
    have hyK := (((bdataS C hT).w s).le hiK).ref hy₁
    obtain ⟨hw, hhome⟩ := subst_arrow_eta_inner (σ := σ) (limgOk C.toFairChain hsk.symm
      (lstg C.toFairChain s k i₁)) hcA
    have hhome' := hhome.trans (eta_addr_congr (by
      change itemAt (imgRoot (limg C.toFairChain k s) (.free 0)) (.root (.free 0)) = _
      rw [itemAt_noT hT]
      change VarSymb.root (.free (limg C.toFairChain k s 0)) = _
      rw [hback]) hw hyK)
    have e2 := congrArg (fun p : Σ b, Term σ _ A b =>
      (bdataS C hT).rden s _ (Ctx.Le.refl _) p.2) hhome'
    have e3 : (bdataS C hT).rden s _ (Ctx.Le.refl _) (Term.eta (.root (.free l.length)) A hyK) =
        (bdataS C hT).rden s i₁ (Ctx.Le.refl _) (Term.eta (.root (.free l.length)) A hy₁) := by
      have := BData.rden_lift (B := bdataS C hT) hiK (Term.eta (.root (.free l.length)) A hy₁)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C hT).Ind o _) ?_).mpr (lalias_ind C hT s t hl hal hy₁)
    exact BData.toDom_congr (e2.trans e3) _ _

end LimitOutX

section LimitOutD

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐⭐**The limit has returning successors at a witnessed shape** (plain leg; T off): alias the
    two values (`y`, `z`) and a unit root `o` after `y`, move the atom to them item by item
    (`alias_interch` at `WFF.instantiate_pairFst`/`Snd` of the slot formula), read it as the
    witnessed obligation at the born shape (`ret_oblDC_noT`), take its back-witness child
    (`lretDC`): the body holds at `⟨c, e⟩`, `c.inner` comes home as `y`
    (`subst_arrow_eta_inner`), and the witness's content is `z`, each `Ind` to its value
    (`lalias_ind`). -/
theorem bdataS_retOutD (hT : ModalSys.T = false) : (bdataS C hT).RetOutD hS := by
  classical
  intro s i A Z a₁ a₂ t₁ t₂ Φ h
  obtain ⟨i₁, hii₁, l₁, hl₁, hal₁⟩ := lalias C s i t₁
  obtain ⟨i₂, hii₂, l₂, hl₂, hal₂⟩ := lalias C s i t₂
  obtain ⟨i₃, hi₁₃, l₃, hl₃, hal₃⟩ :=
    lalias C s i₁ (Term.unit : Term σ (ctxOf (lat s i₁)) .VTypeOne _)
  set J := max i₂ i₃ with hJ
  have hi₁J : i₁ ≤ J := hi₁₃.trans (le_max_right _ _)
  have hi₂J : i₂ ≤ J := le_max_left _ _
  have hiJ : i ≤ J := hii₁.trans hi₁J
  obtain ⟨hs₁, hf₁⟩ := hal₁ J hi₁J
  obtain ⟨hs₂, hf₂⟩ := hal₂ J hi₂J
  obtain ⟨hs₃, -⟩ := hal₃ J (le_max_right _ _)
  have hMJ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ J))
  have hy : (ctxOf (lat s J)).ref (.root (.free l₁.length)) = some A :=
    (ctxOf_le_of_suffix hs₁).ref (ctxOf_ref_new A l₁)
  have hz : (ctxOf (lat s J)).ref (.root (.free l₂.length)) = some Z :=
    (ctxOf_le_of_suffix hs₂).ref (ctxOf_ref_new Z l₂)
  have ho : (ctxOf (lat s J)).ref (.root (.free l₃.length)) = some .VTypeOne :=
    (ctxOf_le_of_suffix hs₃).ref (ctxOf_ref_new _ l₃)
  have hyo : l₁.length ≠ l₃.length := by
    have h1 := (hal₁ i₁ le_rfl).1.length_le
    have h2 := hl₃.length_le
    simp only [List.length_cons] at h1
    omega
  set eJ := ((bdataS C hT).w s).le hiJ
  set ΦJ : WFF σ ((ctxOf (lat s J)).boxIn.insert (.bnd 0) (RShape.wit (.box A) Z).ty) 1 :=
    WFF.mono (eJ.boxIn.insert (.bnd 0) (RShape.wit (.box A) Z).ty) Φ
  have hJm : WFF.retS hS (.wit (.box A) Z) (Term.pair (Term.mono eJ t₁) (Term.mono eJ t₂)) ΦJ ∈
      ((C.net (birth C.toFairChain s.2 + J)).st s.1).M :=
    (BWorld.mem_lift (w := (bdataS C hT).w s) hiJ).mp h
  -- the first item moves to `y`
  have m1 : WFF.retS hS (.wit (.box A) Z)
      (Term.pair (Term.eta (.root (.free l₁.length)) A hy) (Term.mono eJ t₂)) ΦJ ∈
        ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := (alias_interch hs₁ hMJ (Term.mono (ctxOf_le_of_suffix hl₁) t₁) hf₁
      (WFF.bodyRepl (Term.pair (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ _ _))
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root A)
          (Term.mono eJ t₂))) (WFF.retSlot hS (.wit (.box A) Z) ΦJ))).mpr
    rw [WFF.instantiate_pairFst, WFF.instantiate_pairFst, Term.mono_mono, Term.mono_mono] at hi
    have h₁ := WFF.instantiate_retSlot (Γ := ctxOf (lat s J)) hS (.wit (.box A) Z) ΦJ
      (Term.pair (Term.mono eJ t₁) (Term.mono eJ t₂))
    have h₂ := WFF.instantiate_retSlot (Γ := ctxOf (lat s J)) hS (.wit (.box A) Z) ΦJ
      (Term.pair (Term.mono (ctxOf_le_of_suffix hs₁) (Term.eta (.root (.free l₁.length)) A
        (ctxOf_ref_new A l₁))) (Term.mono eJ t₂))
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS .nec (.wit (.box A) Z)
      (sig_pair (congrArg (Sigma.mk _) (Term.mono_eta (ctxOf_le_of_suffix hs₁)
        (.root (.free l₁.length)) A (ctxOf_ref_new A l₁))) rfl) rfl)).mp ?_
    exact (congrArg (· ∈ _) h₂).mp (hi ((congrArg (· ∈ _) h₁).mpr hJm))
  -- the second item moves to `z`
  have m2 : WFF.retS hS (.wit (.box A) Z)
      (Term.pair (Term.eta (.root (.free l₁.length)) A hy)
        (Term.eta (.root (.free l₂.length)) Z hz)) ΦJ ∈
        ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := (alias_interch hs₂ hMJ (Term.mono (ctxOf_le_of_suffix hl₂) t₂) hf₂
      (WFF.bodyRepl (Term.pair
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root Z)
          (Term.eta (.root (.free l₁.length)) A hy))
        (Term.eta (.root (.bnd 0)) Z (Ctx.ref_insert_root _ _ _)))
        (WFF.retSlot hS (.wit (.box A) Z) ΦJ))).mpr
    rw [WFF.instantiate_pairSnd, WFF.instantiate_pairSnd, Term.mono_mono, Term.mono_mono] at hi
    have h₁ := WFF.instantiate_retSlot (Γ := ctxOf (lat s J)) hS (.wit (.box A) Z) ΦJ
      (Term.pair (Term.eta (.root (.free l₁.length)) A hy) (Term.mono eJ t₂))
    have h₂ := WFF.instantiate_retSlot (Γ := ctxOf (lat s J)) hS (.wit (.box A) Z) ΦJ
      (Term.pair (Term.eta (.root (.free l₁.length)) A hy)
        (Term.mono (ctxOf_le_of_suffix hs₂) (Term.eta (.root (.free l₂.length)) Z
          (ctxOf_ref_new Z l₂))))
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS .nec (.wit (.box A) Z)
      (sig_pair rfl (congrArg (Sigma.mk _) (Term.mono_eta (ctxOf_le_of_suffix hs₂)
        (.root (.free l₂.length)) Z (ctxOf_ref_new Z l₂)))) rfl)).mp ?_
    exact (congrArg (· ∈ _) h₂).mp (hi ((congrArg (· ∈ _) h₁).mpr m1))
  have hobl := (congrArg (· ∈ _) (ret_oblDC_noT hT hS .nec hy hz ΦJ)).mpr m2
  obtain ⟨k, hsk, hkd, hcl, hback, hlcx, hmk⟩ := lretDC C s J _ ho hz hyo _ hobl
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k J := lstg_mono C hsk hiJ
  have hiK : J ≤ lstg C.toFairChain k s (lstg C.toFairChain s k J) := by
    have h₁ := (lstg_spec C.toFairChain hsk J).1
    have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k J)).1
    omega
  have hcA : (ctxOf (lat k (lstg C.toFairChain s k J))).boxIn.ref
      (VarSymb.root (.free 0)).inner = some A :=
    Ctx.ref_inner ((ctxOf_le_of_suffix hcl).ref (bclD_c A Z))
  refine ⟨k, hsk, lstg C.toFairChain s k J, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A hcA, .root (.free 1),
    (ctxOf_le_of_suffix hcl).ref (bclD_e A Z), hkd, ?_, ?_, ?_⟩
  · have e := readArrow_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C hT).w k).le hj))
      (limgOk C.toFairChain hsk J) (fun _ _ => rfl)
      (Term.pair (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A hcA))
        (Term.eta (.root (.free 1)) (.VTypeDia Z) ((ctxOf_le_of_suffix hcl).ref (bclD_e A Z)))) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  · obtain ⟨hsuf₁, -⟩ := hal₁ i₁ le_rfl
    have hy₁ : (ctxOf (lat s i₁)).ref (.root (.free l₁.length)) = some A :=
      (ctxOf_le_of_suffix hsuf₁).ref (ctxOf_ref_new A l₁)
    have hyK := (((bdataS C hT).w s).le (hi₁J.trans hiK)).ref hy₁
    obtain ⟨hw, hhome⟩ := subst_arrow_eta_inner (σ := σ) (limgOk C.toFairChain hsk.symm
      (lstg C.toFairChain s k J)) hcA
    have hhome' := hhome.trans (eta_addr_congr (by
      change itemAt (imgRoot (limg C.toFairChain k s) (.free 0)) (.root (.free 0)) = _
      rw [itemAt_noT hT]
      change VarSymb.root (.free (limg C.toFairChain k s 0)) = _
      rw [hback]) hw hyK)
    have e2 := congrArg (fun p : Σ b, Term σ _ A b =>
      (bdataS C hT).rden s _ (Ctx.Le.refl _) p.2) hhome'
    have e3 : (bdataS C hT).rden s _ (Ctx.Le.refl _)
        (Term.eta (.root (.free l₁.length)) A hyK) =
        (bdataS C hT).rden s i₁ (Ctx.Le.refl _) (Term.eta (.root (.free l₁.length)) A hy₁) := by
      have := BData.rden_lift (B := bdataS C hT) (hi₁J.trans hiK)
        (Term.eta (.root (.free l₁.length)) A hy₁)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C hT).Ind o _) ?_).mpr
      (lalias_ind C hT s t₁ hl₁ hal₁ hy₁)
    exact BData.toDom_congr (e2.trans e3) _ _
  · obtain ⟨hsuf₂, -⟩ := hal₂ i₂ le_rfl
    have hz₂ : (ctxOf (lat s i₂)).ref (.root (.free l₂.length)) = some Z :=
      (ctxOf_le_of_suffix hsuf₂).ref (ctxOf_ref_new Z l₂)
    have hzK := (((bdataS C hT).w s).le (hi₂J.trans hiK)).ref hz₂
    have e2 := congrArg (fun p : Σ b, Term σ _ Z b =>
      (bdataS C hT).rden s _ (Ctx.Le.refl _) p.2)
      (eta_addr_congr (σ := σ) (congrArg (fun c => VarSymb.root (.free c)) hlcx)
        ((bdataS C hT).hcx hkd (lstg C.toFairChain s k J)) hzK)
    have e3 : (bdataS C hT).rden s _ (Ctx.Le.refl _)
        (Term.eta (.root (.free l₂.length)) Z hzK) =
        (bdataS C hT).rden s i₂ (Ctx.Le.refl _) (Term.eta (.root (.free l₂.length)) Z hz₂) := by
      have := BData.rden_lift (B := bdataS C hT) (hi₂J.trans hiK)
        (Term.eta (.root (.free l₂.length)) Z hz₂)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C hT).Ind o _) ?_).mpr
      (lalias_ind C hT s t₂ hl₂ hal₂ hz₂)
    exact BData.toDom_congr (e2.trans e3) _ _

/-- ⭐⭐**The limit has returning successors along a witness at a witnessed shape** (T off): as
    `bdataS_retOutD`, along `x` (`WFF.instantiate_retxSlot`, `ret_oblDC_noT` along `x`,
    `lretXDC`). -/
theorem bdataS_retOutXD (hT : ModalSys.T = false) : (bdataS C hT).RetOutXD hS := by
  classical
  intro s i x X hx A Z a₁ a₂ t₁ t₂ Φ h
  obtain ⟨i₁, hii₁, l₁, hl₁, hal₁⟩ := lalias C s i t₁
  obtain ⟨i₂, hii₂, l₂, hl₂, hal₂⟩ := lalias C s i t₂
  obtain ⟨i₃, hi₁₃, l₃, hl₃, hal₃⟩ :=
    lalias C s i₁ (Term.unit : Term σ (ctxOf (lat s i₁)) .VTypeOne _)
  set J := max i₂ i₃ with hJ
  have hi₁J : i₁ ≤ J := hi₁₃.trans (le_max_right _ _)
  have hi₂J : i₂ ≤ J := le_max_left _ _
  have hiJ : i ≤ J := hii₁.trans hi₁J
  obtain ⟨hs₁, hf₁⟩ := hal₁ J hi₁J
  obtain ⟨hs₂, hf₂⟩ := hal₂ J hi₂J
  obtain ⟨hs₃, -⟩ := hal₃ J (le_max_right _ _)
  have hMJ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ J))
  have hy : (ctxOf (lat s J)).ref (.root (.free l₁.length)) = some A :=
    (ctxOf_le_of_suffix hs₁).ref (ctxOf_ref_new A l₁)
  have hz : (ctxOf (lat s J)).ref (.root (.free l₂.length)) = some Z :=
    (ctxOf_le_of_suffix hs₂).ref (ctxOf_ref_new Z l₂)
  have ho : (ctxOf (lat s J)).ref (.root (.free l₃.length)) = some .VTypeOne :=
    (ctxOf_le_of_suffix hs₃).ref (ctxOf_ref_new _ l₃)
  have hyo : l₁.length ≠ l₃.length := by
    have h1 := (hal₁ i₁ le_rfl).1.length_le
    have h2 := hl₃.length_le
    simp only [List.length_cons] at h1
    omega
  set eJ := ((bdataS C hT).w s).le hiJ
  have hxJ : (ctxOf (lat s J)).ref x = some (.VTypeDia X) := eJ.ref hx
  set ΦJ : WFF σ (((ctxOf (lat s J)).diaIn x).insert (.bnd 0) (RShape.wit (.box A) Z).ty) 1 :=
    WFF.mono ((eJ.diaIn x).insert (.bnd 0) (RShape.wit (.box A) Z).ty) Φ
  have hJm : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (.box A) Z)
      (Term.pair (Term.mono eJ t₁) (Term.mono eJ t₂)) ΦJ ∈
        ((C.net (birth C.toFairChain s.2 + J)).st s.1).M :=
    (BWorld.mem_lift (w := (bdataS C hT).w s) hiJ).mp h
  -- the first item moves to `y`
  have m1 : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (.box A) Z)
      (Term.pair (Term.eta (.root (.free l₁.length)) A hy) (Term.mono eJ t₂)) ΦJ ∈
        ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := (alias_interch hs₁ hMJ (Term.mono (ctxOf_le_of_suffix hl₁) t₁) hf₁
      (WFF.bodyRepl (Term.pair (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ _ _))
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root A)
          (Term.mono eJ t₂))) (WFF.retxSlot hS x ⟨X, hxJ⟩ (.wit (.box A) Z) ΦJ))).mpr
    rw [WFF.instantiate_pairFst, WFF.instantiate_pairFst, Term.mono_mono, Term.mono_mono] at hi
    have h₁ := WFF.instantiate_retxSlot (Γ := ctxOf (lat s J)) hS x ⟨X, hxJ⟩ (.wit (.box A) Z)
      ΦJ
      (Term.pair (Term.mono eJ t₁) (Term.mono eJ t₂))
    have h₂ := WFF.instantiate_retxSlot (Γ := ctxOf (lat s J)) hS x ⟨X, hxJ⟩ (.wit (.box A) Z)
      ΦJ
      (Term.pair (Term.mono (ctxOf_le_of_suffix hs₁) (Term.eta (.root (.free l₁.length)) A
        (ctxOf_ref_new A l₁))) (Term.mono eJ t₂))
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS (.pos x ⟨X, hxJ⟩) (.wit (.box A) Z)
      (sig_pair (congrArg (Sigma.mk _) (Term.mono_eta (ctxOf_le_of_suffix hs₁)
        (.root (.free l₁.length)) A (ctxOf_ref_new A l₁))) rfl) rfl)).mp ?_
    exact (congrArg (· ∈ _) h₂).mp (hi ((congrArg (· ∈ _) h₁).mpr hJm))
  -- the second item moves to `z`
  have m2 : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (.box A) Z)
      (Term.pair (Term.eta (.root (.free l₁.length)) A hy)
        (Term.eta (.root (.free l₂.length)) Z hz)) ΦJ ∈
        ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := (alias_interch hs₂ hMJ (Term.mono (ctxOf_le_of_suffix hl₂) t₂) hf₂
      (WFF.bodyRepl (Term.pair
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root Z)
          (Term.eta (.root (.free l₁.length)) A hy))
        (Term.eta (.root (.bnd 0)) Z (Ctx.ref_insert_root _ _ _)))
        (WFF.retxSlot hS x ⟨X, hxJ⟩ (.wit (.box A) Z) ΦJ))).mpr
    rw [WFF.instantiate_pairSnd, WFF.instantiate_pairSnd, Term.mono_mono, Term.mono_mono] at hi
    have h₁ := WFF.instantiate_retxSlot (Γ := ctxOf (lat s J)) hS x ⟨X, hxJ⟩ (.wit (.box A) Z)
      ΦJ
      (Term.pair (Term.eta (.root (.free l₁.length)) A hy) (Term.mono eJ t₂))
    have h₂ := WFF.instantiate_retxSlot (Γ := ctxOf (lat s J)) hS x ⟨X, hxJ⟩ (.wit (.box A) Z)
      ΦJ
      (Term.pair (Term.eta (.root (.free l₁.length)) A hy)
        (Term.mono (ctxOf_le_of_suffix hs₂) (Term.eta (.root (.free l₂.length)) Z
          (ctxOf_ref_new Z l₂))))
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS (.pos x ⟨X, hxJ⟩) (.wit (.box A) Z)
      (sig_pair rfl (congrArg (Sigma.mk _) (Term.mono_eta (ctxOf_le_of_suffix hs₂)
        (.root (.free l₂.length)) Z (ctxOf_ref_new Z l₂)))) rfl)).mp ?_
    exact (congrArg (· ∈ _) h₂).mp (hi ((congrArg (· ∈ _) h₁).mpr m1))
  have hobl := (congrArg (· ∈ _) (ret_oblDC_noT hT hS (.pos x ⟨X, hxJ⟩) hy hz ΦJ)).mpr m2
  obtain ⟨k, hkx, hkd, hcl, hback, hlcx, hmk⟩ := lretXDC C s J _ ho hz hyo hxJ _ hobl
  have hsk := lkdR hkx
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k J := lstg_mono C hsk hiJ
  have hiK : J ≤ lstg C.toFairChain k s (lstg C.toFairChain s k J) := by
    have h₁ := (lstg_spec C.toFairChain hsk J).1
    have h₂ := (lstg_spec C.toFairChain hsk.symm (lstg C.toFairChain s k J)).1
    omega
  have hcA : (ctxOf (lat k (lstg C.toFairChain s k J))).boxIn.ref
      (VarSymb.root (.free 0)).inner = some A :=
    Ctx.ref_inner ((ctxOf_le_of_suffix hcl).ref (bclD_c A Z))
  refine ⟨k, hkx, lstg C.toFairChain s k J, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A hcA, .root (.free 1),
    (ctxOf_le_of_suffix hcl).ref (bclD_e A Z), hkd, ?_, ?_, ?_⟩
  · have e := readArrowX_mono_congr (C.lang_suffix (by omega)
      (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
      ((limgOk C.toFairChain hsk i).mono (((bdataS C hT).w k).le hj))
      (limgOk C.toFairChain hsk J) (fun _ _ => rfl) hx hxJ
      ((((bdataS C hT).w k).le hj).ref ((bdataS C hT).hcx hkx i)) (lhcx C.toFairChain hkx J)
      (Term.pair (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A hcA))
        (Term.eta (.root (.free 1)) (.VTypeDia Z) ((ctxOf_le_of_suffix hcl).ref (bclD_e A Z)))) Φ
    rw [Term.mono_refl, WFF.mono_refl] at e
    exact (congrArg (· ∈ _) e).mpr hmk
  · obtain ⟨hsuf₁, -⟩ := hal₁ i₁ le_rfl
    have hy₁ : (ctxOf (lat s i₁)).ref (.root (.free l₁.length)) = some A :=
      (ctxOf_le_of_suffix hsuf₁).ref (ctxOf_ref_new A l₁)
    have hyK := (((bdataS C hT).w s).le (hi₁J.trans hiK)).ref hy₁
    obtain ⟨hw, hhome⟩ := subst_arrow_eta_inner (σ := σ) (limgOk C.toFairChain hsk.symm
      (lstg C.toFairChain s k J)) hcA
    have hhome' := hhome.trans (eta_addr_congr (by
      change itemAt (imgRoot (limg C.toFairChain k s) (.free 0)) (.root (.free 0)) = _
      rw [itemAt_noT hT]
      change VarSymb.root (.free (limg C.toFairChain k s 0)) = _
      rw [hback]) hw hyK)
    have e2 := congrArg (fun p : Σ b, Term σ _ A b =>
      (bdataS C hT).rden s _ (Ctx.Le.refl _) p.2) hhome'
    have e3 : (bdataS C hT).rden s _ (Ctx.Le.refl _)
        (Term.eta (.root (.free l₁.length)) A hyK) =
        (bdataS C hT).rden s i₁ (Ctx.Le.refl _) (Term.eta (.root (.free l₁.length)) A hy₁) := by
      have := BData.rden_lift (B := bdataS C hT) (hi₁J.trans hiK)
        (Term.eta (.root (.free l₁.length)) A hy₁)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C hT).Ind o _) ?_).mpr
      (lalias_ind C hT s t₁ hl₁ hal₁ hy₁)
    exact BData.toDom_congr (e2.trans e3) _ _
  · obtain ⟨hsuf₂, -⟩ := hal₂ i₂ le_rfl
    have hz₂ : (ctxOf (lat s i₂)).ref (.root (.free l₂.length)) = some Z :=
      (ctxOf_le_of_suffix hsuf₂).ref (ctxOf_ref_new Z l₂)
    have hzK := (((bdataS C hT).w s).le (hi₂J.trans hiK)).ref hz₂
    have e2 := congrArg (fun p : Σ b, Term σ _ Z b =>
      (bdataS C hT).rden s _ (Ctx.Le.refl _) p.2)
      (eta_addr_congr (σ := σ) (congrArg (fun c => VarSymb.root (.free c)) hlcx)
        ((bdataS C hT).hcx hkd (lstg C.toFairChain s k J)) hzK)
    have e3 : (bdataS C hT).rden s _ (Ctx.Le.refl _)
        (Term.eta (.root (.free l₂.length)) Z hzK) =
        (bdataS C hT).rden s i₂ (Ctx.Le.refl _) (Term.eta (.root (.free l₂.length)) Z hz₂) := by
      have := BData.rden_lift (B := bdataS C hT) (hi₂J.trans hiK)
        (Term.eta (.root (.free l₂.length)) Z hz₂)
      rwa [Term.mono_eta] at this
    refine (congrArg (fun o => (bdataS C hT).Ind o _) ?_).mpr
      (lalias_ind C hT s t₂ hl₂ hal₂ hz₂)
    exact BData.toDom_congr (e2.trans e3) _ _

end LimitOutD

end BArrow

end V12M
