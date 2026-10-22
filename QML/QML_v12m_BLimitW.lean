import QML.QML_v12m_BRetOutDC

/-!
# QML v12m — strong B's rows 3–4 at the limit: existence from doubly witnessed children

Under rows 3–4 (`BStrongW`) the network makes no plain or witness children, only doubly
witnessed returning successors (`mkRetXDC`), after naming routes (`mkRoute`).  The limit's
existence (`LimitEx`: `ex`, `exX`, `unl`, fresh witness arrows) comes from them (docs §11.23,
paper check 3).

* ⭐`lretOutXDC`: a returning possibility along `x` at a witnessed companion shape has a witness
  edge for `x` where its body holds — the chain-level half of `bdataS_retOutXDC` (the half that
  does not mention the canonical model), with the edge's content fresh.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Bodies that do not use their slot -/

omit [ModalSys.NoFour] in
/-- Instantiating a body that does not use its slot gives the formula back. -/
theorem WFF.instantiate_slotUp {Γ : Ctx} [Γ.NoSlots] {T : VarType} {a : Ann T}
    (t : Term σ Γ T a) (ψ : WFF σ Γ 0) :
    WFF.instantiate Ctx.NoSlots.slots t (WFF.slotUp Ctx.NoSlots.slots T ψ) = ψ := by
  unfold WFF.instantiate WFF.substRoot
  rw [WFF.subst_slotUp, WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (fun v U hv =>
    Subst.single_at_ne (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)),
    WFF.mono_refl]

omit [ModalSys.NoFour] in
/-- Replacing the bound item of a body that does not use it changes nothing but its type. -/
theorem WFF.bodyRepl_slotUp {V : Ctx} [V.NoSlots] {A B : VarType} {b : Ann B}
    (X : Term σ (V.insert (.bnd 0) A) B b) (ψ : WFF σ V 0) :
    WFF.bodyRepl X (WFF.slotUp Ctx.NoSlots.slots B ψ) = WFF.slotUp Ctx.NoSlots.slots A ψ := by
  unfold WFF.bodyRepl
  rw [WFF.subst_slotUp]
  unfold WFF.slotUp
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) ψ
  have hvr : v ≠ .root (.bnd 0) := fun h => by
    subst h
    rw [(Ctx.NoSlots.slots (Γ := V)).root] at hv
    cases hv
  rw [Subst.set_ne _ _ hvr]
  exact .refl _

/-- A witness body that does not use its slot, read along a witness arrow: the arrow's reading. -/
theorem readArrowX_slotUp {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) {B : VarType} {c : Ann B}
    (g : Term σ Δ B c) (ψ : WFF σ ((ctxOf l).diaIn x) 0) :
    readArrowX himg hx hcx g (WFF.slotUp Ctx.NoSlots.slots B ψ) =
      WFF.subst (arrowXIdx img x cx) (arrowXS σ Δ img x cx) (ok_arrowXS himg hx hcx)
        (coh_arrowXS himg hx hcx) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
  unfold readArrowX
  rw [WFF.subst_slotUp]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) ψ
  have hvr : v ≠ .root (.bnd 0) := fun h => by
    subst h
    rw [(Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).root] at hv
    cases hv
  rw [Subst.set_ne _ _ hvr]
  exact .refl _

/-- Reading along a witness arrow into a larger context is reading into the smaller one,
    weakened. -/
theorem mono_subst_arrowXS {l : List VarType} {Δ Δ' : Ctx} [Δ.NoSlots] [Δ'.NoSlots]
    (hle : Δ.Le Δ') {img : ℕ → ℕ} (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : Δ.ref (.root (.free cx)) = some X) (ψ : WFF σ ((ctxOf l).diaIn x) 0) :
    WFF.mono hle (WFF.subst (arrowXIdx img x cx) (arrowXS σ Δ img x cx)
        (ok_arrowXS himg hx hcx) (coh_arrowXS himg hx hcx) Ctx.NoSlots.slots Ctx.NoSlots.slots
        ψ) =
      WFF.subst (arrowXIdx img x cx) (arrowXS σ Δ' img x cx)
        (ok_arrowXS (himg.mono hle) hx (hle.ref hcx)) (coh_arrowXS (himg.mono hle) hx (hle.ref hcx))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
  rw [WFF.mono_subst _ _ _ _ _ _ Ctx.NoSlots.slots]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
  rw [arrowXS_mono]
  exact sim_arrowXS (fun _ _ => rfl)

/-- Reading along an arrow into a larger context is reading into the smaller one, weakened. -/
theorem mono_subst_arrowS {l : List VarType} {Δ Δ' : Ctx} [Δ.NoSlots] [Δ'.NoSlots]
    (hle : Δ.Le Δ') {img : ℕ → ℕ} (himg : ImgOk l Δ img) (ψ : WFF σ (ctxOf l).boxIn 0) :
    WFF.mono hle (WFF.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ) =
      WFF.subst (arrowIdx img) (arrowS σ Δ' img) (ok_arrowS (himg.mono hle))
        (coh_arrowS (himg.mono hle)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
  rw [WFF.mono_subst _ _ _ _ _ _ Ctx.NoSlots.slots]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
  rw [arrowS_mono]
  exact sim_arrowS (fun _ _ => rfl)

/-- A `□`-view formula read in a witness's view, along a witness arrow, is the formula read along
    the arrow. -/
theorem subst_arrowXS_mono_boxIn {l l' : List VarType} (hl : l <:+ l') {Δ : Ctx} [Δ.NoSlots]
    {img : ℕ → ℕ} (himg : ImgOk l' Δ img) {κ : VarSymb} {X : VarType}
    (hκ : (ctxOf l').ref κ = some (.VTypeDia X)) {cx : ℕ}
    (hcx : Δ.ref (.root (.free cx)) = some X) (hle : (ctxOf l).boxIn.Le ((ctxOf l').diaIn κ))
    (ψ : WFF σ (ctxOf l).boxIn 0) :
    WFF.subst (arrowXIdx img κ cx) (arrowXS σ Δ img κ cx) (ok_arrowXS himg hκ hcx)
        (coh_arrowXS himg hκ hcx) Ctx.NoSlots.slots Ctx.NoSlots.slots (WFF.mono hle ψ) =
      WFF.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS (himg.suffix hl))
        (coh_arrowS (himg.suffix hl)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots]
  exact WFF.subst_congr _ _ _ _ _ _ _ _ (sim_arrowXS_arrowS (fun _ _ => rfl)) ψ

omit [ModalSys.NoFour] in
/-- A returning possibility along `κ` whose body does not use its slot gives `◇_κ` of it
    (`ret_diaS`, then the `∃` dropped inside, as `RetInvX.transferX`). -/
theorem BWorld.dia_of_retx (w : BWorld σ) (hS : ModalSys.BStrong = true) {i : ℕ}
    {κ : VarSymb} {X : VarType} (hκ : (w.ctx i).ref κ = some (.VTypeDia X)) {S : RShape}
    {a : Ann S.flat} (t : Term σ (w.ctx i) S.flat a) {V : Ctx} [V.NoSlots]
    (hle : V.Le ((w.ctx i).diaIn κ)) (φ : WFF σ V 0)
    (h : WFF.retxS hS κ ⟨X, hκ⟩ S t
      (WFF.mono (hle.insert (.bnd 0) S.ty) (WFF.slotUp Ctx.NoSlots.slots S.ty φ)) ∈ w.M i) :
    WFF.dia κ ⟨X, hκ⟩ (WFF.mono hle φ) ∈ w.M i := by
  have hu := (ctxOf_fresh (l := w.l i) le_rfl).diaIn κ
  have inner : Proof σ ((w.ctx i).diaIn κ)
      [WFF.ex S.ty (WFF.mono (hle.insert (.bnd 0) _) (WFF.slotUp Ctx.NoSlots.slots _ φ))]
      (WFF.mono hle φ) := by
    refine Proof.ex_elim (w.l i).length _ hu
      (φ := WFF.openFree (w.l i).length hu Ctx.NoSlots.slots _)
      (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
        (Proof.lookup List.mem_cons_self)) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    rw [WFF.openFree_mono_slotUp]
  exact w.mem_of_provable (Δ := [_]) (fun y hy => by rw [List.mem_singleton.mp hy]; exact h)
    ⟨Proof.imp_elim (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil)
        (Proof.imp_intro (Proof.K_dia (Δ₁ := []) (Δ₂ := []) κ ⟨X, hκ⟩ inner)))
      (Proof.ret_diaS hS (.pos κ ⟨X, hκ⟩) t _ (Proof.lookup List.mem_cons_self))⟩

omit [ModalSys.NoFour] in
/-- ⭐**A failing necessity returns along `□`** (rows 3–4): `¬□ψ` gives `◇[() ↦ ()] ¬ψ`, by
    `ret_new` at the unit. -/
theorem BWorld.ret_of_not_box (w : BWorld σ) (hS : ModalSys.BStrong = true)
    (hB : ModalSys.B = true) {i : ℕ} (ψ : WFF σ (w.ctx i).boxIn 0) (h : .box ψ ∉ w.M i) :
    WFF.retS hS (.box .VTypeOne) Term.unit (WFF.slotUp Ctx.NoSlots.slots _ ψ.neg) ∈ w.M i := by
  have hb : (OutLeg.nec : OutLeg (w.ctx i)).dia
      (WFF.ex (.VTypeBox .VTypeOne) (WFF.slotUp Ctx.NoSlots.slots _ ψ.neg)) ∈ w.M i := by
    refine (w.mcs i).neg_mem_iff.mpr fun hb => h ?_
    refine w.mem_of_provable (Δ := [_]) (fun y hy => by rw [List.mem_singleton.mp hy]; exact hb)
      ⟨Proof.K_box (Δ := [_]) ?_⟩
    exact Proof.or_elim (Proof.lem ψ) (Proof.lookup List.mem_cons_self)
      (Proof.bot_elim _ (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
        (Proof.ex_intro _ (Term.boxtm Term.unit)
          (Proof.conv (WFF.instantiate_slotUp _ ψ.neg).symm (Proof.lookup List.mem_cons_self)))))
  exact w.mem_of_provable (Δ := [_]) (fun y hy => by rw [List.mem_singleton.mp hy]; exact hb)
    ⟨Proof.ret_new hS hB .nec (A := .VTypeOne) _ (w.l i).length (ctxOf_fresh le_rfl)
      (Proof.lookup List.mem_cons_self) (Proof.lookup List.mem_cons_self)⟩

/-! ## Possibilities return along their witnesses -/

omit [ModalSys.NoFour] in
/-- ⭐**A possibility returns along its witness** (rows 3–4): `◇_x ψ` gives
    `◇_x^{□𝟙 × ◇𝟙}[⟨d, e⟩ ↦ ⟨(), ()⟩] ψ` — `ret_new` at the unit, whose value is `()`, then
    `ret_realise`. -/
theorem BWorld.retx_of_dia (w : BWorld σ) (hS : ModalSys.BStrong = true)
    (hB : ModalSys.B = true) (hW : ModalSys.BStrongW = true) {i : ℕ} {x : VarSymb}
    {X : VarType} (hx : (w.ctx i).ref x = some (.VTypeDia X)) (ψ : WFF σ ((w.ctx i).diaIn x) 0)
    (h : WFF.dia x ⟨X, hx⟩ ψ ∈ w.M i) :
    (OutLeg.pos x ⟨X, hx⟩ : OutLeg (w.ctx i)).retS hS (.wit (.box .VTypeOne) .VTypeOne)
      (Term.pair Term.unit Term.unit)
      (WFF.bodyRepl (RShape.realL ((w.ctx i).diaIn x) (.box .VTypeOne) .VTypeOne).2
        (WFF.slotUp Ctx.NoSlots.slots _ ψ)) ∈ w.M i := by
  have hu : (w.ctx i).RootFresh (.free (w.l i).length) := ctxOf_fresh le_rfl
  refine w.mem_of_provable (Δ := [_]) (fun φ hφ => by rw [List.mem_singleton.mp hφ]; exact h)
    ⟨Proof.ret_realise hS hW (.pos x ⟨X, hx⟩) (.box .VTypeOne) Term.unit Term.unit _ ?_⟩
  refine Proof.ret_new hS hB (.pos x ⟨X, hx⟩) (A := .VTypeOne)
    (WFF.slotUp Ctx.NoSlots.slots _ ψ) _ hu ?_ (Proof.lookup List.mem_cons_self)
  refine Proof.ofSubset (fun φ hφ => ?_) (Proof.K_dia (Δ₁ := []) (Δ₂ := []) x ⟨X, hx⟩
    (Proof.ex_intro _ (Term.boxtm Term.unit)
      (Proof.conv (WFF.instantiate_slotUp _ ψ).symm (Proof.lookup List.mem_cons_self))))
  rcases List.mem_cons.mp hφ with rfl | hφ
  · exact List.mem_cons_self
  · simp at hφ

section LimitW

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐**A returning possibility along `x` at a witnessed companion shape has its child at the
    limit**: a witness edge `s → k` for `x`, at a stage of which the body holds of the born root's
    box and the back witness, and whose content is no image of the stage's variables.  As
    `bdataS_retOutXDC`, without the readings home. -/
theorem lretOutXDC (s : LW C.toFairChain) (i : ℕ) {x : VarSymb} {X : VarType}
    (hx : ((nodeWorld C.toFairChain s.1 s.2).ctx i).ref x = some (.VTypeDia X))
    {A Z : VarType} {cs : List (List Step)} {h : A.CompOk cs} {a : Ann (A.compsFlat cs)}
    {a₂ : Ann Z} (V : Term σ ((nodeWorld C.toFairChain s.1 s.2).ctx i) (A.compsFlat cs) a)
    (t₂ : Term σ ((nodeWorld C.toFairChain s.1 s.2).ctx i) Z a₂)
    (Φ : WFF σ ((((nodeWorld C.toFairChain s.1 s.2).ctx i).diaIn x).insert (.bnd 0)
      (RShape.wit (.boxC A cs h) Z).ty) 1)
    (hm : (OutLeg.pos x ⟨X, hx⟩ : OutLeg ((nodeWorld C.toFairChain s.1 s.2).ctx i)).retS hS
      (.wit (.boxC A cs h) Z) (Term.pair V t₂) Φ ∈ (nodeWorld C.toFairChain s.1 s.2).M i) :
    ∃ (k : LW C.toFairChain) (hk : lkd C.toFairChain s k = some (x, X)) (j : ℕ)
      (hj : lstg C.toFairChain s k i ≤ j) (b : Ann A)
      (g : Term σ ((nodeWorld C.toFairChain k.1 k.2).ctx j).boxIn A b) (e : VarSymb)
      (he : ((nodeWorld C.toFairChain k.1 k.2).ctx j).ref e = some (.VTypeDia Z)),
      readArrowX ((limgOk C.toFairChain (lkdR hk) i).mono
          ((nodeWorld C.toFairChain k.1 k.2).le hj)) hx
          (((nodeWorld C.toFairChain k.1 k.2).le hj).ref (lhcx C.toFairChain hk i))
          (Term.pair (Term.boxtm g) (Term.eta e (.VTypeDia Z) he)) Φ ∈
        (nodeWorld C.toFairChain k.1 k.2).M j ∧
      ∀ r < ((nodeWorld C.toFairChain s.1 s.2).l i).length,
        limg C.toFairChain s k r ≠ lcx C.toFairChain s k := by
  classical
  -- name the missing companions, and reorder to the born order
  obtain ⟨j₁, hij₁, a₁, V₁, hV₁, hm₁⟩ :=
    BWorld.ret_comps_namedW (nodeWorld C.toFairChain s.1 s.2) hS
    (missComps A cs) (missComps_ok h) (.pos x ⟨X, hx⟩) V t₂ Φ hm
  have hx₁ := ((nodeWorld C.toFairChain s.1 s.2).le hij₁).ref hx
  set R := ShapeMap.subC (σ := σ) A (missComps A cs ++ cs) (bornComps A) (missComps_ok h)
    (bornComps_ok A) (missComps_sub A cs)
  set e₁ := (nodeWorld C.toFairChain s.1 s.2).le hij₁
  set Φ₁ := WFF.mono ((e₁.diaIn x).insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) Φ
  have hm₂ : WFF.retxS hS x ⟨X, hx₁⟩ (.wit (bornShape A) Z)
      (Term.pair (Term.holeRead V₁ R.val.2) (Term.mono e₁ t₂)) Φ₁ ∈
        (nodeWorld C.toFairChain s.1 s.2).M j₁ := by
    have hp := BWorld.mem_of_provable (Δ := [_])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hm₁)
      ⟨Proof.ret_map hS (.pos x ⟨X, hx₁⟩)
        (S := .wit (.boxC A (missComps A cs ++ cs) (missComps_ok h)) Z)
        R (Term.pair V₁ (Term.mono e₁ t₂)) Φ₁ (Proof.conv (congrArg _
          ((WFF.bodyRepl_congr (sig_mono _ (liftObj_subC_wit (σ := σ) A _ _ (missComps_ok h)
            (bornComps_ok A) (missComps_sub A cs) Z)) Φ₁).trans (WFF.bodyRepl_eta Φ₁)).symm)
          (Proof.lookup List.mem_cons_self))⟩
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS (.pos x ⟨X, hx₁⟩) _ ?_ rfl)).mp hp
    rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
    exact holeAt_liftVal_wit R V₁ _
  -- aliases: the value's tuple, the possible part's value, and a unit after the first
  set W := Term.holeRead V₁ R.val.2
  set t := Term.holeAt W (arrB (σ := σ) A).2
  obtain ⟨i₂, hj₁i₂, l₁, hl₁, hal₁⟩ := lalias C s j₁ t
  obtain ⟨i₃, hii₃, l₂, hl₂, hal₂⟩ := lalias C s i t₂
  obtain ⟨i₄, hi₂₄, l₃, hl₃, hal₃⟩ :=
    lalias C s i₂ (Term.unit : Term σ (ctxOf (lat s i₂)) .VTypeOne _)
  set J := max i₃ i₄ with hJ
  have hi₂J : i₂ ≤ J := hi₂₄.trans (le_max_right _ _)
  have hi₃J : i₃ ≤ J := le_max_left _ _
  have hj₁J : j₁ ≤ J := hj₁i₂.trans hi₂J
  have hiJ : i ≤ J := hij₁.trans hj₁J
  obtain ⟨hs₁, hf₁⟩ := hal₁ J hi₂J
  obtain ⟨hs₂, hf₂⟩ := hal₂ J hi₃J
  obtain ⟨hs₃, -⟩ := hal₃ J (le_max_right _ _)
  have hMJ := (C.good _).mcs s.1 (live_birth C.toFairChain s.2 (Nat.le_add_right _ J))
  have hyJ : (ctxOf (lat s J)).ref (.root (.free l₁.length)) = some (VarType.VTypeBox A).bc :=
    (ctxOf_le_of_suffix hs₁).ref (ctxOf_ref_new _ l₁)
  have hz : (ctxOf (lat s J)).ref (.root (.free l₂.length)) = some Z :=
    (ctxOf_le_of_suffix hs₂).ref (ctxOf_ref_new Z l₂)
  have ho : (ctxOf (lat s J)).ref (.root (.free l₃.length)) = some .VTypeOne :=
    (ctxOf_le_of_suffix hs₃).ref (ctxOf_ref_new _ l₃)
  have hyo : l₁.length ≠ l₃.length := by
    have h1 := (hal₁ i₂ le_rfl).1.length_le
    have h2 := hl₃.length_le
    simp only [List.length_cons] at h1
    omega
  set eJ := (nodeWorld C.toFairChain s.1 s.2).le hiJ
  have hxJ : (ctxOf (lat s J)).ref x = some (.VTypeDia X) := eJ.ref hx
  set e₁J := (nodeWorld C.toFairChain s.1 s.2).le hj₁J
  set ΦJ : WFF σ (((ctxOf (lat s J)).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Z).ty)
      1 := WFF.mono ((eJ.diaIn x).insert (.bnd 0) (RShape.wit (.boxC A cs h) Z).ty) Φ
  have hJm : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z)
      (Term.pair (Term.mono e₁J W) (Term.mono eJ t₂)) ΦJ ∈
        ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have := (BWorld.mem_lift (w := nodeWorld C.toFairChain s.1 s.2) hj₁J).mp hm₂
    change WFF.retxS hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z)
      (Term.pair (Term.mono e₁J W) (Term.mono e₁J (Term.mono e₁ t₂)))
      (WFF.mono _ (WFF.mono _ Φ)) ∈ _ at this
    rw [WFF.mono_mono, Term.mono_mono] at this
    exact this
  -- the necessary part moves to `unarrT y`
  have m1 : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z)
      (Term.pair (unarrT hyJ).2 (Term.mono eJ t₂)) ΦJ ∈
      ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := alias_interch hs₁ hMJ (Term.mono (ctxOf_le_of_suffix hl₁) t) hf₁
      (WFF.bodyRepl (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) (WFF.retxSlot hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z) ΦJ))
    have ea := OutLeg.instantiate_compSlot hS (.pos x ⟨X, hxJ⟩) (.wit (bornShape A) Z) (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) ΦJ
      (Term.mono (ctxOf_le_of_suffix hs₁) (Term.eta (.root (.free l₁.length)) _
        (ctxOf_ref_new _ l₁)))
    have eb := OutLeg.instantiate_compSlot hS (.pos x ⟨X, hxJ⟩) (.wit (bornShape A) Z) (Term.pair
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (unarrHole (σ := σ) A).2)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root _)
          (Term.mono eJ t₂))) ΦJ
      (Term.mono (ctxOf_le_of_suffix hs₁) (Term.mono (aliasLe _ l₁)
        (Term.mono (ctxOf_le_of_suffix hl₁) t)))
    have e_y : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hs₁)
        (Term.eta (.root (.free l₁.length)) _ (ctxOf_ref_new _ l₁))) (unarrHole (σ := σ) A).2⟩ :
        Σ c, Term σ (ctxOf (lat s J)) _ c) = unarrT hyJ := by
      rw [Term.holeRead_eq_holeAt]
      refine (holeAt_unarrHole A _).trans ?_
      rw [Term.mono_eta]
      exact unarrAt_eta hyJ
    have e_t : (⟨_, Term.holeRead (Term.mono (ctxOf_le_of_suffix hs₁)
        (Term.mono (aliasLe _ l₁) (Term.mono (ctxOf_le_of_suffix hl₁) t)))
          (unarrHole (σ := σ) A).2⟩ :
        Σ c, Term σ (ctxOf (lat s J)) _ c) = ⟨_, Term.mono e₁J W⟩ := by
      rw [Term.holeRead_eq_holeAt]
      refine (holeAt_unarrHole A _).trans ?_
      rw [Term.mono_mono, Term.mono_mono]
      refine (unarrAt_sig A (Term.mono_holeAt_sig _ W _)).trans ?_
      exact unarrAt_arrB A _
    exact (congrArg (· ∈ _) (ea.trans (OutLeg.retS_congr hS (.pos x ⟨X, hxJ⟩) _
      (sig_pair e_y (Term.subst_single_mono_sig _ _)) rfl))).mp
      (hi.mpr ((congrArg (· ∈ _) (eb.trans (OutLeg.retS_congr hS (.pos x ⟨X, hxJ⟩) _
        (sig_pair e_t (Term.subst_single_mono_sig _ _)) rfl))).mpr hJm))
  -- the possible part's value moves to `z`
  have m2 : WFF.retxS hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z) (unarrDT (σ := σ) hyJ hz).2 ΦJ ∈
      ((C.net (birth C.toFairChain s.2 + J)).st s.1).M := by
    have hi := (alias_interch hs₂ hMJ (Term.mono (ctxOf_le_of_suffix hl₂) t₂) hf₂
      (WFF.bodyRepl (Term.pair
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf (lat s J))).root Z)
          (unarrT hyJ).2)
        (Term.eta (.root (.bnd 0)) Z (Ctx.ref_insert_root _ _ _)))
        (WFF.retxSlot hS x ⟨X, hxJ⟩ (.wit (bornShape A) Z) ΦJ))).mpr
    rw [WFF.instantiate_pairSnd, WFF.instantiate_pairSnd, Term.mono_mono, Term.mono_mono] at hi
    have h₁ := WFF.instantiate_retxSlot (Γ := ctxOf (lat s J)) hS x ⟨X, hxJ⟩
      (.wit (bornShape A) Z) ΦJ
      (Term.pair (unarrT hyJ).2 (Term.mono eJ t₂))
    have h₂ := WFF.instantiate_retxSlot (Γ := ctxOf (lat s J)) hS x ⟨X, hxJ⟩
      (.wit (bornShape A) Z) ΦJ
      (Term.pair (unarrT hyJ).2
        (Term.mono (ctxOf_le_of_suffix hs₂) (Term.eta (.root (.free l₂.length)) Z
          (ctxOf_ref_new Z l₂))))
    refine (congrArg (· ∈ _) (OutLeg.retS_congr hS (.pos x ⟨X, hxJ⟩) (.wit (bornShape A) Z)
      (sig_pair rfl (congrArg (Sigma.mk _) (Term.mono_eta (ctxOf_le_of_suffix hs₂)
        (.root (.free l₂.length)) Z (ctxOf_ref_new Z l₂)))) rfl)).mp ?_
    exact (congrArg (· ∈ _) h₂).mp (hi ((congrArg (· ∈ _) h₁).mpr m1))
  -- the back-witness child
  obtain ⟨k, hkx, -, hcl, -, -, hmk, hfr⟩ := lretXDC C s J hyJ ho hz hyo hxJ ΦJ m2
  have hsk := lkdR hkx
  have hj : lstg C.toFairChain s k i ≤ lstg C.toFairChain s k J := lstg_mono C hsk hiJ
  have hcK : (ctxOf (lat k (lstg C.toFairChain s k J))).ref (.root (.free 0)) =
      some (.VTypeBox A) := (ctxOf_le_of_suffix hcl).ref (bclD_c A Z)
  refine ⟨k, hkx, lstg C.toFairChain s k J, hj, _,
    Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK), .root (.free 1),
    (ctxOf_le_of_suffix hcl).ref (bclD_e A Z), ?_,
    fun r hr => hfr r
      (lt_of_lt_of_le hr ((nodeWorld C.toFairChain s.1 s.2).suf hiJ).length_le)⟩
  have e := readArrowX_mono_congr (C.lang_suffix (by omega)
    (live_birth C.toFairChain s.2 (Nat.le_add_right _ i))) (Ctx.Le.refl _)
    ((limgOk C.toFairChain hsk i).mono ((nodeWorld C.toFairChain k.1 k.2).le hj))
    (limgOk C.toFairChain hsk J) (fun _ _ => rfl) hx hxJ
    (((nodeWorld C.toFairChain k.1 k.2).le hj).ref (lhcx C.toFairChain hkx i))
    (lhcx C.toFairChain hkx J)
    (Term.pair (Term.boxtm (Term.eta (VarSymb.root (.free 0)).inner A (Ctx.ref_inner hcK)))
      (Term.eta (.root (.free 1)) (.VTypeDia Z) ((ctxOf_le_of_suffix hcl).ref (bclD_e A Z)))) Φ
  rw [Term.mono_refl, WFF.mono_refl] at e
  exact (congrArg (· ∈ _) e).mpr hmk

/-- ⭐**Rows 3–4: a possibility has a witness child at the limit**, where its body holds, with
    the child's content fresh: the possibility returns along its witness
    (`BWorld.retx_of_dia`), and the returning possibility has its doubly witnessed child
    (`lretOutXDC`). -/
theorem lexXW (hB : ModalSys.B = true) (hW : ModalSys.BStrongW = true) (s : LW C.toFairChain)
    (i : ℕ) (x : VarSymb) (X : VarType) (hx : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (lat s i)).diaIn x) 0)
    (hψ : WFF.dia x ⟨X, hx⟩ ψ ∈ ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (hk : lkd C.toFairChain s t = some (x, X)),
      WFF.subst (arrowXIdx (limg C.toFairChain s t) x (lcx C.toFairChain s t))
        (arrowXS σ _ (limg C.toFairChain s t) x (lcx C.toFairChain s t))
        (ok_arrowXS (limgOk C.toFairChain (lkdR hk) i) hx (lhcx C.toFairChain hk i))
        (coh_arrowXS (limgOk C.toFairChain (lkdR hk) i) hx (lhcx C.toFairChain hk i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
          ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M ∧
      ∀ r < (lat s i).length, limg C.toFairChain s t r ≠ lcx C.toFairChain s t := by
  obtain ⟨k, hk, j, hj, b, g, e, he, hmem, hfr⟩ := lretOutXDC C s i hx
    (A := .VTypeOne) (cs := []) (h := Or.inl rfl) Term.unit Term.unit _
    (BWorld.retx_of_dia (nodeWorld C.toFairChain s.1 s.2) hS hB hW (i := i) hx ψ hψ)
  refine ⟨k, hk, ?_, hfr⟩
  rw [WFF.bodyRepl_slotUp] at hmem
  erw [readArrowX_slotUp] at hmem
  refine ((nodeWorld C.toFairChain k.1 k.2).mem_lift hj).mpr ?_
  erw [mono_subst_arrowXS _ (limgOk C.toFairChain (lkdR hk) i) hx (lhcx C.toFairChain hk i)]
  exact hmem

/-- ⭐**Rows 3–4: a failing necessity has a child at the limit** where its translation fails,
    along a route `κ` past the stage's variables: `¬□ψ` returns along `□` with `¬ψ`
    (`BWorld.ret_of_not_box`), names its route (`lroute`), so `◇_κ ¬ψ` (`BWorld.dia_of_retx`),
    and `lexXW` along `κ`. -/
theorem lexW (hB : ModalSys.B = true) (hW : ModalSys.BStrongW = true) (s : LW C.toFairChain)
    (i : ℕ) (ψ : WFF σ (ctxOf (lat s i)).boxIn 0)
    (hψ : .box ψ ∉ ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    ∃ (t : LW C.toFairChain) (h : LR C.toFairChain s t) (κ i₁ : ℕ),
      lkd C.toFairChain s t = some (.root (.free κ), .VTypeOne) ∧ (lat s i).length ≤ κ ∧
      κ < (lat s i₁).length ∧
      (WFF.subst (arrowIdx (limg C.toFairChain s t)) (arrowS σ _ (limg C.toFairChain s t))
        (ok_arrowS (limgOk C.toFairChain h i)) (coh_arrowS (limgOk C.toFairChain h i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ).neg ∈
          ((C.net (birth C.toFairChain t.2 + lstg C.toFairChain s t i)).st t.1).M := by
  have hr := BWorld.ret_of_not_box (nodeWorld C.toFairChain s.1 s.2) hS hB (i := i) ψ hψ
  obtain ⟨i₁, hii₁, l, hl, hsuf, hmr⟩ :=
    lroute C hW s i (S := .box .VTypeOne) Term.unit (WFF.slotUp Ctx.NoSlots.slots _ ψ.neg) hr
  have hκ : (ctxOf (lat s i₁)).ref (.root (.free l.length)) = some (.VTypeDia .VTypeOne) :=
    (ctxOf_le_of_suffix hsuf).ref (ctxOf_ref_new _ l)
  have hli : lat s i <:+ lat s i₁ := hl.trans ((List.suffix_cons _ _).trans hsuf)
  have hle : (ctxOf (lat s i)).boxIn.Le ((ctxOf (lat s i₁)).diaIn (.root (.free l.length))) :=
    (ctxOf_le_of_suffix hli).boxIn.trans (Ctx.le_boxIn_diaIn _ _)
  have hm : WFF.retxS hS (.root (.free l.length)) ⟨.VTypeOne, hκ⟩ (.box .VTypeOne) Term.unit
      (WFF.mono (hle.insert (.bnd 0) _) (WFF.slotUp Ctx.NoSlots.slots _ ψ.neg)) ∈
        ((C.net (birth C.toFairChain s.2 + i₁)).st s.1).M := by
    unfold routeFormula at hmr
    simp only [WFF.mono, WFF.mono_mono] at hmr
    exact hmr
  have hd := BWorld.dia_of_retx (nodeWorld C.toFairChain s.1 s.2) hS (i := i₁) hκ
    (S := .box .VTypeOne) Term.unit hle ψ.neg hm
  obtain ⟨t, hk, hmem, -⟩ := lexXW C hB hW s i₁ _ _ hκ (WFF.mono hle ψ.neg) hd
  refine ⟨t, lkdR hk, l.length, i₁, hk, hl.length_le, ?_, ?_⟩
  · have := hsuf.length_le
    simp only [List.length_cons] at this
    omega
  · change WFF.subst (arrowIdx (limg C.toFairChain s t)) (arrowS σ _ (limg C.toFairChain s t))
      (ok_arrowS (limgOk C.toFairChain (lkdR hk) i))
      (coh_arrowS (limgOk C.toFairChain (lkdR hk) i)) Ctx.NoSlots.slots Ctx.NoSlots.slots
      ψ.neg ∈ _
    refine ((nodeWorld C.toFairChain t.1 t.2).mem_lift (lstg_mono C (lkdR hk) hii₁)).mpr ?_
    erw [mono_subst_arrowS _ (limgOk C.toFairChain (lkdR hk) i)]
    erw [subst_arrowXS_mono_boxIn hli (limgOk C.toFairChain (lkdR hk) i₁) hκ
      (lhcx C.toFairChain hk i₁)] at hmem
    exact hmem

/-- ⭐**Rows 3–4: every arrow out has an arrow out not labelled `y`**: a route named past `y`
    (`lexW`, once more after `y` is declared if the first route is `y`). -/
theorem lunlW (hB : ModalSys.B = true) (hW : ModalSys.BStrongW = true) {s t : LW C.toFairChain}
    (y : VarSymb) (h : LR C.toFairChain s t) :
    ∃ t', LR C.toFairChain s t' ∧ lbOfKd (lkd C.toFairChain) s t' y = none := by
  have hbot : ∀ i, WFF.box (.bot : WFF σ (ctxOf (lat s i)).boxIn 0) ∉
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M := fun i hb =>
    ((nodeWorld C.toFairChain t.1 t.2).mcs _).bot_not_mem (ltr C.toFairChain h i .bot hb)
  have key : ∀ i, ∃ (t' : LW C.toFairChain) (κ i₁ : ℕ), LR C.toFairChain s t' ∧
      lkd C.toFairChain s t' = some (.root (.free κ), .VTypeOne) ∧ (lat s i).length ≤ κ ∧
      κ < (lat s i₁).length := fun i => by
    obtain ⟨t', h', κ, i₁, hk, hge, hlt, -⟩ := lexW C hB hW s i .bot (hbot i)
    exact ⟨t', κ, i₁, h', hk, hge, hlt⟩
  have none_of : ∀ {t' : LW C.toFairChain} {κ : ℕ},
      lkd C.toFairChain s t' = some (.root (.free κ), .VTypeOne) → y ≠ .root (.free κ) →
      lbOfKd (lkd C.toFairChain) s t' y = none := fun hk hne => by
    unfold lbOfKd
    rw [hk]
    dsimp only
    rw [if_neg (Ne.symm hne)]
  obtain ⟨t₁, κ₁, i₁, h₁, hk₁, -, hlt₁⟩ := key 0
  by_cases hy : y = .root (.free κ₁)
  · obtain ⟨t₂, κ₂, -, h₂, hk₂, hge₂, -⟩ := key i₁
    refine ⟨t₂, h₂, none_of hk₂ fun e => ?_⟩
    rw [hy] at e
    cases e
    omega
  · exact ⟨t₁, h₁, none_of hk₁ hy⟩

/-- ⭐⭐**Rows 3–4: existence in the limit of a strong chain**, from doubly witnessed children:
    `ex` (`lexW`), `exX` and fresh witness arrows (`lexXW`), `unl` (`lunlW`). -/
theorem LimitEx.ofW (hB : ModalSys.B = true) (hW : ModalSys.BStrongW = true) :
    LimitEx C.toFairChain where
  ex s i ψ hψ := let ⟨t, h, _, _, _, _, _, hm⟩ := lexW C hB hW s i ψ hψ; ⟨t, h, hm⟩
  exX s i x X hx ψ hψ := let ⟨t, hk, hm, _⟩ := lexXW C hB hW s i x X hx ψ hψ; ⟨t, hk, hm⟩
  unl y h := lunlW C hB hW y h
  cxFresh s i x X hx hψ :=
    let ⟨t, hk, _, hfr⟩ := lexXW C hB hW s i x X hx .top hψ; ⟨t, hk, hfr⟩

end LimitW

end BArrow

end V12M
