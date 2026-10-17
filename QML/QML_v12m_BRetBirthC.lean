import QML.QML_v12m_BStepWDC

/-!
# V12M strong B under T: the arrow invariants with companions, at birth and as nodes grow

What the network needs of the companion invariants (`RetInvB`, `RetInvWB`, `RetInvXB`,
`RetInvWDB`) besides the steps:
* the forward invariant of a weak B child at birth (`RetInvB.birth`, `RetInvWB.birth`), by the
  companion units' base forms (`ret_unit_baseC`, `ret_unitW_baseC`);
* an arrow with nothing committed (`RetInvB.nil`, `RetInvXB.nil`): no companions to name;
* growth of either end (`grow_src`, `grow_tgt`);
* forgetting the companions (`forget`), so the T-generic consequences carry over.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The companion unit's base form -/

omit [ModalSys.NoFour] in
/-- Instantiating the unused slot of `unitBodyC hS [] _ sb cs h (holeSnd θ)` gives
    `◇^{S}[d ↦ sb with companions] θ(d)`. -/
theorem WFF.instantiate_unitBodyC_holeSnd {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step))
    (h : A.CompOk cs) (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) 1)
    {c : Ann (.VTypeBox .VTypeOne)} (t : Term σ Γ.boxIn (.VTypeBox .VTypeOne) c) :
    WFF.instantiate Ctx.NoSlots.slots t
        (WFF.unitBodyC hS [] (Or.inl rfl) sb cs h (WFF.holeSnd (C := .VTypeOne) θ)) =
      WFF.retS hS (.nec (.boxC A cs h)) (compsVal sb cs h).2
        (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert _)
          (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _)) θ) := by
  unfold WFF.unitBodyC
  rw [WFF.holeAt_pair_holeSnd]
  unfold WFF.instantiate WFF.substRoot
  refine WFF.retS_congr hS _ ?_ ?_
  · exact Term.subst_single_mono_sig t _
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ ?_ θ
    exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ _ _ _ _)

omit [ModalSys.NoFour] in
/-- ⭐**The companion unit's base form**: what holds of `□sb` holds, necessarily, of `sb`'s returns
    with its companions — `ret_unit_base` with `ret_unitC`. -/
def Proof.ret_unit_baseC {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeBox A)) 1)
    (p : Proof σ Γ Δ (WFF.holeRead (Term.boxtm sb) θ)) :
    Proof σ Γ Δ (WFF.box (WFF.retS hS (.nec (.boxC A cs h)) (compsVal sb cs h).2
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert _)
        (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _)) θ))) := by
  refine Proof.byContra ?_
  have q : Proof σ Γ.boxIn
      [WFF.neg (WFF.ex (.VTypeBox .VTypeOne)
        (WFF.neg (WFF.unitBodyC hS [] (Or.inl rfl) sb cs h (WFF.holeSnd (C := .VTypeOne) θ))))]
      (WFF.retS hS (.nec (.boxC A cs h)) (compsVal sb cs h).2
        (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert _)
          (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _)) θ)) := by
    refine Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ex_intro _ (Term.boxtm Term.unit) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))))
    exact congrArg WFF.neg
      (WFF.instantiate_unitBodyC_holeSnd hS sb cs h θ (Term.boxtm Term.unit)).symm
  have hd : Proof σ Γ (_ :: Δ) ((OutLeg.nec : OutLeg Γ).dia (WFF.ex (.VTypeBox .VTypeOne)
      (WFF.neg (WFF.unitBodyC hS [] (Or.inl rfl) sb cs h (WFF.holeSnd (C := .VTypeOne) θ))))) :=
    Proof.imp_intro (Proof.imp_elim
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self)
        (Proof.K_box q)))
  refine Proof.ret_new hS hB .nec _ _ (Ctx.Presented.fresh_bound _ le_rfl) hd ?_
  have hle := Ctx.le_insert (Ctx.Presented.fresh_bound (Γ := Γ) _ le_rfl).root .VTypeOne
  have r₁ : Proof σ (Γ.insert (.free (Ctx.Presented.bound Γ)) .VTypeOne)
      [WFF.ret hS (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
        (WFF.mono (hle.boxIn.insert (.bnd 0) _)
          (WFF.neg (WFF.unitBodyC hS [] (Or.inl rfl) sb cs h (WFF.holeSnd (C := .VTypeOne) θ))))]
      (WFF.ret hS (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
        (WFF.neg (WFF.unitBodyC hS [] (Or.inl rfl) (Term.mono hle.boxIn sb) cs h
          (WFF.holeSnd (C := .VTypeOne) θ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    refine congrArg (WFF.ret hS _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyC hle]
  have r₂ : Proof σ (Γ.insert (.free (Ctx.Presented.bound Γ)) .VTypeOne) (Δ.map (WFF.mono hle))
      (WFF.holeRead (Term.pair
          (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
        (Term.boxtm (Term.mono hle.boxIn sb))) (WFF.holeSnd (C := .VTypeOne) θ)) := by
    refine Proof.conv ?_ (Proof.mono hle p)
    rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt, WFF.mono_holeAt _ _ Ctx.NoSlots.slots,
      WFF.holeAt_pair_holeSnd]
    rfl
  exact Proof.ret_absurd hS _ _ (Ctx.Presented.fresh_bound _ le_rfl)
    (Proof.ret_unitC hS .nec [] (Or.inl rfl) _ _ _ cs h _
      (Proof.ofSubset (fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) r₁)
      (Proof.ofSubset (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) r₂))

/-- ⭐**The forward arrow at birth has the invariant with companions**: with nothing committed
    back, a body true at the parent of the committed roots' necessary object is, by
    `ret_unit_baseC`, necessarily a returning possibility from their tuple with its companions,
    which the arrow's transfer sends to the child (`subst_arrow_compsVal`). -/
theorem RetInvB.birth (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {tv tw : NodeSt σ}
    {cls : List VarType} {imgs imgt : ℕ → ℕ} (hv : Theory.IsMCS tv.M) (hs : cls <:+ tv.l)
    (himgs : ImgOk cls (ctxOf tw.l) imgs)
    (htr : Transfer tv.M cls (ctxOf_le_of_suffix hs) tw.M imgs himgs) :
    RetInvB hS ModalSys.T rfl tv tw cls imgs [] imgt := by
  have himgt : ImgOk [] (ctxOf tv.l) imgt := fun r hr => absurd hr (Nat.not_lt_zero r)
  refine ⟨hs, himgs, List.nil_suffix, himgt, fun Φ hΦ => ?_⟩
  have hle := ctxOf_le_of_suffix hs
  have hread : WFF.holeRead (Term.boxtm (Term.mono hle.boxIn (tupT cls).2))
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert _)
        (Term.pair Term.unit (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
        (pack2 [] (.VTypeBox (bcT cls)) Φ)) = liftBody hs himgt Φ := by
    rw [WFF.holeRead_eq_holeAt, WFF.holeAt_holeAt_pairUnit, ← WFF.holeRead_eq_holeAt]
    exact holeRead_tupImgT_pack2 himgt _ Φ
  have hbox := hv.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hΦ,
    ⟨Proof.ret_unit_baseC hS hB _ ((bcT cls).compsAllB ModalSys.T)
      (VarType.compOk_compsAllB _ rfl _) _
      (Proof.conv hread.symm (Proof.lookup List.mem_cons_self))⟩⟩
  have hbox' : WFF.mono hle (.box (WFF.retS hS (.nec (tupShape ModalSys.T rfl cls))
      (compsVal (tupT cls).2 _ (VarType.compOk_compsAllB _ rfl _)).2
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := (ctxOf cls).boxIn.boxIn)).insert _)
        (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _))
        (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert _)
          (Term.pair Term.unit (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
          (pack2 [] (.VTypeBox (bcT cls)) Φ))))) ∈ tv.M := by
    refine (congrArg (· ∈ tv.M) ?_).mpr hbox
    change WFF.box (WFF.retS hS _ (Term.mono _ _) (WFF.mono _ (WFF.holeAt _ _ _))) = _
    rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := (ctxOf tv.l).boxIn.boxIn)).insert _),
      Term.mono_eta]
    exact congrArg WFF.box (WFF.retS_congr hS _ (mono_compsVal hle (tupT cls).2 _ _).symm rfl)
  refine (congrArg (· ∈ tw.M) ?_).mp (htr _ hbox')
  refine WFF.retS_congr hS _ (subst_arrow_compsVal cls himgs _ _) ?_
  rw [WFF.subst_holeAt]
  refine (WFF.holeAt_congr _ (Term.subst_eta_renAt _ _ _ _ _ _ _
    (Ctx.ref_insert_root _ (.bnd 0) _) (Subst.under_at_slot _ _ _ _ _)) _).trans ?_
  dsimp only [RShape.ty, NShape.ty]
  rw [WFF.holeAt_holeAt_pairUnit]
  exact holeAt_tupT_pack2 (ctxOf_le_of_suffix (List.nil_suffix (l := tw.l))).boxIn Φ

/-! ## The witnessed companion unit's base form -/

omit [ModalSys.NoFour] in
/-- The witnessed companion unit's base body, in `x`'s view: `◇^{S × ◇X}[d ↦ sb with companions,
    e ⇝ u] θ(⟨d, e⟩)`. -/
def WFF.unitBaseWC {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {x : VarSymb}
    {A X : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1) :
    WFF σ (Γ.diaIn x) 0 :=
  WFF.retS hS (.wit (.boxC A cs h) X)
    (Term.pair (Term.mono (Ctx.le_boxIn_diaIn Γ x) (compsVal sb cs h).2) u)
    (WFF.holeAt ((Ctx.NoSlots.slots (Γ := (Γ.diaIn x).boxIn)).insert _)
      (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)) θ)

omit [ModalSys.NoFour] in
theorem WFF.mono_unitBaseWC {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {x : VarSymb} {A X : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X} (u : Term σ (Γ.diaIn x) X b₀)
    (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1) :
    WFF.mono (h.diaIn x) (WFF.unitBaseWC hS sb u cs hcs θ) =
      WFF.unitBaseWC hS (Term.mono h.boxIn sb) (Term.mono (h.diaIn x) u) cs hcs θ := by
  unfold WFF.unitBaseWC
  refine WFF.retS_congr hS _ (sig_pair ?_ rfl) ?_
  · rw [mono_compsVal h sb cs hcs]
    change (⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩ : Σ c, _) =
      ⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩
    rw [Term.mono_mono, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := (Γ'.diaIn x).boxIn)).insert _),
      Term.mono_eta]

omit [ModalSys.NoFour] in
/-- Instantiating the unused slot of the witnessed companion unit's conjunct gives its base body. -/
theorem WFF.instantiate_unitBodyWC_holeSnd {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {x : VarSymb} {A X : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1)
    {c : Ann (.VTypeBox .VTypeOne)} (t : Term σ (Γ.diaIn x) (.VTypeBox .VTypeOne) c) :
    WFF.instantiate Ctx.NoSlots.slots t
        (WFF.unitBodyWC hS [] (Or.inl rfl) sb u cs h (WFF.holeSnd (C := .VTypeOne) θ)) =
      WFF.unitBaseWC hS sb u cs h θ := by
  unfold WFF.unitBodyWC WFF.unitBaseWC
  rw [WFF.holeAt_pair_holeSnd]
  unfold WFF.instantiate WFF.substRoot
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
  · rw [← Term.mono_mono (Ctx.le_boxIn_diaIn Γ x)
      (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _)]
    exact Term.subst_single_mono_sig t _
  · exact Term.subst_single_mono_sig t u
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ ?_ θ
    exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ _ _ _ _)

omit [ModalSys.NoFour] in
/-- ⭐**The witnessed companion unit's base form**: `ret_unitW_base` with `ret_unitWC`. -/
def Proof.ret_unitW_baseC {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {x : VarSymb}
    (hx : ∃ X', Γ.ref x = some (.VTypeDia X')) {A X : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X} (u : Term σ (Γ.diaIn x) X b₀)
    (cs : List (List Step)) (h : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1)
    (p : Proof σ Γ Δ (WFF.holeRead (Term.pair (Term.boxtm sb) (Term.diatm x hx u)) θ)) :
    Proof σ Γ Δ (WFF.boxx x hx (WFF.unitBaseWC hS sb u cs h θ)) := by
  refine Proof.byContra ?_
  have qR : Proof σ (Γ.diaIn x)
      [WFF.neg (WFF.ex (.VTypeBox .VTypeOne)
        (WFF.neg (WFF.unitBodyWC hS [] (Or.inl rfl) sb u cs h (WFF.holeSnd (C := .VTypeOne) θ))))]
      (WFF.unitBaseWC hS sb u cs h θ) := by
    refine Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ex_intro _ (Term.boxtm Term.unit) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))))
    exact congrArg WFF.neg
      (WFF.instantiate_unitBodyWC_holeSnd hS sb u cs h θ (Term.boxtm Term.unit)).symm
  have q : Proof σ (Γ.diaIn x) [WFF.neg (WFF.unitBaseWC hS sb u cs h θ)]
      (WFF.ex (.VTypeBox .VTypeOne)
        (WFF.neg (WFF.unitBodyWC hS [] (Or.inl rfl) sb u cs h
          (WFF.holeSnd (C := .VTypeOne) θ)))) :=
    Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ofSubset (fun y hy => by rw [List.mem_singleton.mp hy]; exact List.mem_cons_self) qR))
  have hdn : Proof σ Γ (WFF.neg (WFF.boxx x hx (WFF.unitBaseWC hS sb u cs h θ)) :: Δ)
      (WFF.dia x hx (WFF.neg (WFF.unitBaseWC hS sb u cs h θ))) :=
    Proof.byContra (Proof.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup List.mem_cons_self))
  have hd : Proof σ Γ (WFF.neg (WFF.boxx x hx (WFF.unitBaseWC hS sb u cs h θ)) :: Δ)
      ((OutLeg.pos x hx : OutLeg Γ).dia (WFF.ex (.VTypeBox .VTypeOne)
        (WFF.neg (WFF.unitBodyWC hS [] (Or.inl rfl) sb u cs h
          (WFF.holeSnd (C := .VTypeOne) θ))))) :=
    Proof.imp_elim (Proof.ofSubset (fun _ h => by simp at h)
      (Proof.imp_intro (Proof.K_dia x hx (Δ₁ := []) (Δ₂ := []) q))) hdn
  refine Proof.ret_new hS hB (.pos x hx) _ _ (Ctx.Presented.fresh_bound _ le_rfl) hd ?_
  have hle := Ctx.le_insert (Ctx.Presented.fresh_bound (Γ := Γ) _ le_rfl).root .VTypeOne
  have hx' : ∃ X', (Γ.insert (.free (Ctx.Presented.bound Γ)) .VTypeOne).ref x =
      some (.VTypeDia X') := hx.imp fun _ hX => hle.ref hX
  have r₁ : Proof σ (Γ.insert (.free (Ctx.Presented.bound Γ)) .VTypeOne)
      [WFF.retx hS x hx'
        (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
        (WFF.mono ((hle.diaIn x).insert (.bnd 0) _)
          (WFF.neg (WFF.unitBodyWC hS [] (Or.inl rfl) sb u cs h
            (WFF.holeSnd (C := .VTypeOne) θ))))]
      (WFF.retx hS x hx'
        (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
        (WFF.neg (WFF.unitBodyWC hS [] (Or.inl rfl) (Term.mono hle.boxIn sb)
          (Term.mono (hle.diaIn x) u) cs h (WFF.holeSnd (C := .VTypeOne) θ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    refine congrArg (WFF.retx hS x hx' _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyWC hle]
  have r₂ : Proof σ (Γ.insert (.free (Ctx.Presented.bound Γ)) .VTypeOne) (Δ.map (WFF.mono hle))
      (WFF.holeRead (Term.pair
          (Term.eta (.root (.free (Ctx.Presented.bound Γ))) _ (Ctx.ref_insert_root _ _ _))
          (Term.pair (Term.boxtm (Term.mono hle.boxIn sb))
            (Term.diatm x hx' (Term.mono (hle.diaIn x) u))))
        (WFF.holeSnd (C := .VTypeOne) θ)) := by
    refine Proof.conv ?_ (Proof.mono hle p)
    rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt, WFF.mono_holeAt _ _ Ctx.NoSlots.slots,
      WFF.holeAt_pair_holeSnd]
    rfl
  exact Proof.retx_absurd hS hx' _ _ (Ctx.Presented.fresh_bound _ le_rfl)
    (Proof.ret_unitWC hS hx' [] (Or.inl rfl) _ _ _ _ cs h _
      (Proof.ofSubset (fun y hy => by rw [List.mem_singleton.mp hy]; exact List.mem_cons_self) r₁)
      (Proof.ofSubset (fun y hy => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)) r₂))

/-- ⭐**The forward arrow of a witness child at birth has the invariant with companions**:
    `RetInvW.birth` with the witnessed companion unit's base form. -/
theorem RetInvWB.birth (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    {tv tw : NodeSt σ} {cls : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType}
    {cx : ℕ} (hv : Theory.IsMCS tv.M) (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs)
    (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tw.l).ref (.root (.free cx)) = some X)
    (htr : TransferX tv.M cls (ctxOf_le_of_suffix hs) hx tw.M imgs himgs cx hcx) :
    RetInvWB hS ModalSys.T rfl tv tw cls imgs [] imgt x X cx := by
  have himgt : ImgOk [] (ctxOf tv.l) imgt := fun r hr => absurd hr (Nat.not_lt_zero r)
  refine ⟨hs, himgs, List.nil_suffix, himgt, hx, hcx, fun Φ hΦ => ?_⟩
  have hle := ctxOf_le_of_suffix hs
  have hx' : ∃ X', (ctxOf tv.l).ref x = some (.VTypeDia X') := ⟨X, hle.ref hx⟩
  have hread : WFF.holeRead (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT cls).2))
      (Term.diatm x hx' (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx)))))
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert _)
        (Term.pair Term.unit (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
        (pack2 [] (RShape.wit (.box (bcT cls)) X).ty Φ)) = liftBodyW hs himgt hx Φ := by
    rw [WFF.holeRead_eq_holeAt, WFF.holeAt_holeAt_pairUnit, ← WFF.holeRead_eq_holeAt]
    exact holeRead_tupImgT_pack2 himgt _ Φ
  have hbox := hv.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hΦ,
    ⟨Proof.ret_unitW_baseC hS hB hx' _ _ ((bcT cls).compsAllB ModalSys.T)
      (VarType.compOk_compsAllB _ rfl _) _
      (Proof.conv hread.symm (Proof.lookup List.mem_cons_self))⟩⟩
  have hbox' : WFF.mono hle (WFF.boxx x ⟨X, hx⟩ (WFF.unitBaseWC (Γ := ctxOf cls) hS (tupT cls).2
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx)) ((bcT cls).compsAllB ModalSys.T)
      (VarType.compOk_compsAllB _ rfl _)
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert _)
        (Term.pair Term.unit (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
        (pack2 [] (RShape.wit (.box (bcT cls)) X).ty Φ)))) ∈ tv.M := by
    refine (congrArg (· ∈ tv.M) ?_).mpr hbox
    change WFF.boxx x _ (WFF.mono (hle.diaIn x) _) = _
    rw [WFF.mono_unitBaseWC hle, Term.mono_eta]
    rfl
  refine (congrArg (· ∈ tw.M) ?_).mp (htr _ hbox')
  unfold WFF.unitBaseWC
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ _ imgs) _ (ok_arrowS himgs) _ (coh_arrowS himgs)
      (Subst.sim_of fun v T _ hv => ?_) _).trans (subst_arrow_compsVal cls himgs _ _)
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    exact .refl _
  · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by rw [Subst.at_nonproj _ rfl]; exact if_pos rfl)
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ (Term.subst_eta_renAt _ _ _ _ _ _ _
      (Ctx.ref_insert_root _ (.bnd 0) _) (Subst.under_at_slot _ _ _ _ _)) _).trans ?_
    dsimp only [RShape.ty, NShape.ty]
    rw [WFF.holeAt_holeAt_pairUnit]
    exact holeAt_tupT_pack2 (ctxOf_le_of_suffix (List.nil_suffix (l := tw.l))).boxIn Φ

/-! ## Nothing committed -/

/-- An arrow with nothing committed has the invariant with companions, for either value of the
    flag: the tuple of no roots has no companions. -/
theorem RetInvB.nil (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {tv tw : NodeSt σ}
    {clt : List VarType} {imgs imgt : ℕ → ℕ} (hv : Theory.IsMCS tv.M) (hw : Theory.IsMCS tw.M)
    (ht : clt <:+ tw.l) (himgt : ImgOk clt (ctxOf tv.l) imgt)
    (htr : Transfer tw.M clt (ctxOf_le_of_suffix ht) tv.M imgt himgt) :
    ∀ (b : Bool) (hb : ModalSys.T = b), RetInvB hS b hb tv tw [] imgs clt imgt
  | false, _ => RetInv.nil hS hB hv hw ht himgt htr
  | true, _ => RetInv.nil hS hB hv hw ht himgt htr

/-- An arrow along `x` with nothing committed has the invariant with companions. -/
theorem RetInvXB.nil (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {tk tp : NodeSt σ}
    {clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M) (ht : clt <:+ tp.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X)
    (htr : TransferX tp.M clt (ctxOf_le_of_suffix ht) hx tk.M imgt himgt cx hcx) :
    ∀ (b : Bool) (hb : ModalSys.T = b), RetInvXB hS b hb tk tp [] imgs clt imgt x X cx
  | false, _ => RetInvX.nil hS hB hk hp ht himgt hx hcx htr
  | true, _ => RetInvX.nil hS hB hk hp ht himgt hx hcx htr

/-! ## Growth -/

/-- Weakening the images' tuple with companions is the tuple with companions in the larger
    target. -/
theorem tupCompsImg_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') (cls : List VarType) (img : ℕ → ℕ)
    (himg : ImgOk cls Δ img) : ∀ (cs : List (List Step)) (hc : (bcT cls).CompOk cs),
    (⟨_, Term.mono h (tupCompsImg (σ := σ) cls img himg cs hc).2⟩ :
      Σ a, Term σ Δ' ((bcT cls).compsFlat cs) a) = tupCompsImg cls img (himg.mono h) cs hc
  | [], _ => tupImgT_mono h cls img himg
  | _ :: ps, hc => sig_pair (tupCompsImg_mono h cls img himg ps hc.tail)
      (subst_arrow_tgt_mono h himg _).symm

theorem RetInvB.grow_tgt {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw tw' : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ}
    (h : RetInvB hS b hb tv tw cls imgs clt imgt) (hg : Grows tw tw') :
    RetInvB hS b hb tv tw' cls imgs clt imgt := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs, himgs.mono hle, ht.trans hg.suf, himgt, fun Φ hΦ => ?_⟩
  have h' := hg.sub _ (hinv Φ hΦ)
  change WFF.retS hS _ (Term.mono hle _) (WFF.mono _ (WFF.mono _ Φ)) ∈ tw'.M at h'
  rw [WFF.mono_mono, WFF.retS_congr hS _ (tupCompsImg_mono hle cls imgs himgs _ _) rfl] at h'
  exact h'

theorem RetInvB.grow_src {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tv' tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ}
    (hv : Theory.IsMCS tv.M) (hv' : Theory.IsMCS tv'.M)
    (h : RetInvB hS b hb tv tw cls imgs clt imgt) (hg : Grows tv tv') :
    RetInvB hS b hb tv' tw cls imgs clt imgt := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs.trans hg.suf, himgs, ht, himgt.mono hle, fun Φ hΦ => hinv Φ ?_⟩
  refine mem_of_mono_mem hle hv hv' hg.sub ?_
  rw [liftBody_mono hs hg.suf himgt Φ]
  exact hΦ

theorem RetInvXB.grow_tgt {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tk tp tp' : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cx : ℕ} (h : RetInvXB hS b hb tk tp cls imgs clt imgt x X cx)
    (hg : Grows tp tp') : RetInvXB hS b hb tk tp' cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs, himgs.mono hle, ht.trans hg.suf, himgt, hx, hcx, fun Φ hΦ => ?_⟩
  have h' := hg.sub _ (hinv Φ hΦ)
  change WFF.retxS hS x _ (.nec _) (Term.mono hle _) (WFF.mono _ (WFF.mono _ Φ)) ∈ tp'.M at h'
  rw [WFF.mono_mono, WFF.retxS_congr hS x _ (.nec _)
    (tupCompsImg_mono hle cls imgs himgs _ _) rfl] at h'
  exact h'

theorem RetInvXB.grow_src {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tk tk' tp : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cx : ℕ} (hk : Theory.IsMCS tk.M) (hk' : Theory.IsMCS tk'.M)
    (h : RetInvXB hS b hb tk tp cls imgs clt imgt x X cx) (hg : Grows tk tk') :
    RetInvXB hS b hb tk' tp cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs.trans hg.suf, himgs, ht, himgt.mono hle, hx, hle.ref hcx, fun Φ hΦ => hinv Φ ?_⟩
  refine mem_of_mono_mem hle hk hk' hg.sub ?_
  rw [liftBodyX_mono hs hg.suf himgt hx hcx Φ]
  exact hΦ

theorem RetInvWB.grow_tgt {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw tw' : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cx : ℕ} (h : RetInvWB hS b hb tv tw cls imgs clt imgt x X cx)
    (hg : Grows tw tw') : RetInvWB hS b hb tv tw' cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs, himgs.mono hle, ht.trans hg.suf, himgt, hx, hle.ref hcx, fun Φ hΦ => ?_⟩
  have h' := hg.sub _ (hinv Φ hΦ)
  change WFF.retS hS _ (Term.mono hle _) (WFF.mono _ (WFF.mono _ Φ)) ∈ tw'.M at h'
  rw [WFF.mono_mono, WFF.retS_congr hS _ (sig_pair (tupCompsImg_mono hle cls imgs himgs _ _)
    (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))) rfl] at h'
  exact h'

theorem RetInvWB.grow_src {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tv' tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cx : ℕ} (hv : Theory.IsMCS tv.M) (hv' : Theory.IsMCS tv'.M)
    (h : RetInvWB hS b hb tv tw cls imgs clt imgt x X cx) (hg : Grows tv tv') :
    RetInvWB hS b hb tv' tw cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs.trans hg.suf, himgs, ht, himgt.mono hle, hx, hcx, fun Φ hΦ => hinv Φ ?_⟩
  refine mem_of_mono_mem hle hv hv' hg.sub ?_
  rw [liftBodyW_mono hs hg.suf himgt hx Φ]
  exact hΦ

theorem RetInvWDB.grow_tgt {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw tw' : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cxw : ℕ} {e : VarSymb} {E : VarType} {cxv : ℕ}
    (h : RetInvWDB hS b hb tv tw cls imgs clt imgt x X cxw e E cxv) (hg : Grows tw tw') :
    RetInvWDB hS b hb tv tw' cls imgs clt imgt x X cxw e E cxv := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs, himgs.mono hle, ht.trans hg.suf, himgt, hx, hle.ref hcxw, he, hcxv,
    fun Φ hΦ => ?_⟩
  have h' := hg.sub _ (hinv Φ hΦ)
  change WFF.retxS hS e _ (.wit _ _) (Term.pair (Term.mono hle _) (Term.mono hle _))
    (WFF.mono _ (WFF.mono _ Φ)) ∈ tw'.M at h'
  rw [WFF.mono_mono, WFF.retxS_congr hS e _ (.wit _ _) (sig_pair
    (tupCompsImg_mono hle cls imgs himgs _ _) (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)))
    rfl] at h'
  exact h'

theorem RetInvWDB.grow_src {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tv' tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cxw : ℕ} {e : VarSymb} {E : VarType} {cxv : ℕ} (hv : Theory.IsMCS tv.M)
    (hv' : Theory.IsMCS tv'.M) (h : RetInvWDB hS b hb tv tw cls imgs clt imgt x X cxw e E cxv)
    (hg : Grows tv tv') : RetInvWDB hS b hb tv' tw cls imgs clt imgt x X cxw e E cxv := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs.trans hg.suf, himgs, ht, himgt.mono hle, hx, hcxw, he, hle.ref hcxv,
    fun Φ hΦ => hinv Φ ?_⟩
  refine mem_of_mono_mem hle hv hv' hg.sub ?_
  rw [liftBodyWD_mono hs hg.suf himgt hx he hcxv Φ]
  exact hΦ

/-! ## Forgetting the companions -/

omit [ModalSys.NoFour] in
/-- Forgetting companions at a witnessed shape leaves a body as it was. -/
theorem WFF.bodyRepl_liftObj_wit_forgetC {V : Ctx} [V.NoSlots] (A : VarType)
    (cs : List (List Step)) (h : A.CompOk cs) (X : VarType)
    (Φ : WFF σ (V.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1) :
    WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
      (ShapeMap.liftObj (σ := σ) (.wit (.boxC A cs h) X) (ShapeMap.forgetC A cs h)).2) Φ = Φ := by
  have e : (⟨_, (ShapeMap.liftObj (σ := σ) (.wit (.boxC A cs h) X)
      (ShapeMap.forgetC A cs h)).2⟩ : Σ c, Term σ (Ctx.empty.insert (.bnd 0)
        (RShape.wit (.boxC A cs h) X).ty) (RShape.wit (.box A) X).ty c) =
      ⟨_, Term.eta (.root (.bnd 0)) (RShape.wit (.boxC A cs h) X).ty
        (Ctx.ref_insert_root _ _ _)⟩ := by
    dsimp only [ShapeMap.liftObj, ShapeMap.obj]
    exact sig_pair (Term.holeAt_eta_root _) rfl
  rw [WFF.bodyRepl_congr_sig (sig_mono _ e)]
  exact WFF.bodyRepl_eta Φ

/-- The value with companions forgotten at a witnessed shape: the images' tuple and the
    witness's content. -/
theorem holeRead_forgetC_wit {Δ : Ctx} [Δ.NoSlots] (cls : List VarType) (img : ℕ → ℕ)
    (himg : ImgOk cls Δ img) (cs : List (List Step)) (h : (bcT cls).CompOk cs) {X : VarType}
    {x : Ann X} (e : Term σ Δ X x) :
    (⟨_, Term.holeRead (Term.pair (tupCompsImg cls img himg cs h).2 e)
        (ShapeMap.liftVal (σ := σ) (.wit (.boxC (bcT cls) cs h) X)
          (ShapeMap.forgetC (bcT cls) cs h)).2⟩ :
      Σ a, Term σ Δ (RShape.wit (.box (bcT cls)) X).flat a) =
      ⟨_, Term.pair (tupImgT cls img himg).2 e⟩ := by
  have e₁ := holeRead_forgetC_tupCompsImg (σ := σ) cls img himg cs h
  rw [Term.holeRead_eq_holeAt] at e₁ ⊢
  exact (liftVal_wit_pair (ShapeMap.forgetC (bcT cls) cs h) _ e).trans (sig_pair e₁ rfl)

/-- Forgetting the companions along `x`. -/
theorem RetInvXB.forget {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tk tp : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cx : ℕ} (hM : Theory.IsMCS tp.M)
    (h : RetInvXB hS b hb tk tp cls imgs clt imgt x X cx) :
    RetInvX hS tk tp cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  refine ⟨hs, himgs, ht, himgt, hx, hcx, fun Φ hΦ => ?_⟩
  have hret := hinv Φ hΦ
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hret, ⟨?_⟩⟩
  refine Proof.conv (WFF.retxS_congr hS x _ _
      (holeRead_forgetC_tupCompsImg cls imgs himgs _ _) rfl)
    (Proof.ret_map hS (.pos x _) (S := .nec (tupShape b hb cls))
      (ShapeMap.forgetC (bcT cls) _ (VarType.compOk_compsAllB b hb _)) _ _ ?_)
  exact Proof.conv (congrArg (WFF.retxS hS x _ _ _) (WFF.bodyRepl_eta _).symm)
    (Proof.lookup List.mem_cons_self)

/-- Forgetting the companions at the witnessed shape. -/
theorem RetInvWB.forget {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cx : ℕ} (hM : Theory.IsMCS tw.M)
    (h : RetInvWB hS b hb tv tw cls imgs clt imgt x X cx) :
    RetInvW hS tv tw cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  refine ⟨hs, himgs, ht, himgt, hx, hcx, fun Φ hΦ => ?_⟩
  have hret := hinv Φ hΦ
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hret, ⟨?_⟩⟩
  refine Proof.conv (WFF.retS_congr hS _ (holeRead_forgetC_wit cls imgs himgs _ _ _) rfl)
    (Proof.ret_map hS .nec (S := .wit (tupShape b hb cls) X)
      (ShapeMap.forgetC (bcT cls) _ (VarType.compOk_compsAllB b hb _)) _ _ ?_)
  exact Proof.conv (congrArg (WFF.retS hS _ _)
      (WFF.bodyRepl_liftObj_wit_forgetC _ _ _ _ _).symm)
    (Proof.lookup List.mem_cons_self)

/-- Forgetting the companions along `e` at the witnessed shape. -/
theorem RetInvWDB.forget {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw : NodeSt σ} {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb}
    {X : VarType} {cxw : ℕ} {e : VarSymb} {E : VarType} {cxv : ℕ} (hM : Theory.IsMCS tw.M)
    (h : RetInvWDB hS b hb tv tw cls imgs clt imgt x X cxw e E cxv) :
    RetInvWD hS tv tw cls imgs clt imgt x X cxw e E cxv := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
  refine ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, fun Φ hΦ => ?_⟩
  have hret := hinv Φ hΦ
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hret, ⟨?_⟩⟩
  refine Proof.conv (WFF.retxS_congr hS e _ _ (holeRead_forgetC_wit cls imgs himgs _ _ _) rfl)
    (Proof.ret_map hS (.pos e _) (S := .wit (tupShape b hb cls) X)
      (ShapeMap.forgetC (bcT cls) _ (VarType.compOk_compsAllB b hb _)) _ _ ?_)
  exact Proof.conv (congrArg (WFF.retxS hS e _ _ _)
      (WFF.bodyRepl_liftObj_wit_forgetC _ _ _ _ _).symm)
    (Proof.lookup List.mem_cons_self)

end BArrow

end V12M
