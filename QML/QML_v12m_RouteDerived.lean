import QML.QML_v12m_RetForget

/-!
# QML v12m — naming the route is derivable (rows 3–4)

Naming the route — a returning possibility along `□` runs along some fresh `κ : ◇𝟙`, once a
primitive rule — follows from the units, `ret_realise` and the possible-part unit (docs §11.23,
"`WCoh` and the derivability of `ret_route`").  Were no possible object here to name the route
of `◇[d ↦ y] Ψ`, `ret_unit` would carry `∀κ. ¬◇_κ[e ↦ y] Ψ` out (`kThetaR`); at the far world
`ret_realise` gives the returning possibility back a possible part `p`, and `ret_unitD` along `p`
brings `Ψ` back, against the carried universal at `κ := p`.

* ⭐`Proof.ret_routeK` (necessary shape with companions) and ⭐`Proof.ret_routeKW` (witnessed
  shape), for a body given by home items and a hole formula (`kPsiS`);
* ⭐`Proof.ret_route_node`: at a node, any body at a boxed shape (`RShape.boxed`), packed by
  `kPsiS_pack2` — what the network's route naming uses (`route_consistent`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-- A non-slot variable of a `□` view is an item (as `boxIn_item'`, which comes later). -/
theorem boxIn_item_route {Γ : Ctx} {v : VarSymb} {T : VarType} (h : Γ.boxIn v = some T) :
    ∃ u, v = .step u .box ∧ Γ.ref u = some (.VTypeBox T) := by
  match v with
  | .step u .box => exact ⟨u, rfl, (Ctx.boxIn_box h).2⟩
  | .step u .keep =>
      obtain ⟨hF, _⟩ := Ctx.boxIn_keep h
      rw [ModalSys.NoFour.noFour] at hF
      cases hF
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

/-- A body over a slot of any type `T`, as a hole formula `θΨ` read at home items `sb` and the
    slot: `kPsi` (slot `□A`) and `kPsiD` (slot `□A × ◇X`) are its instances. -/
def kPsiV {V : Ctx} [V.NoSlots] {C : VarType} (T : VarType) {c : Ann C} (y : Term σ V C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C T)) 1) :
    WFF σ (V.insert (.bnd 0) T) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _)
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root _) y)
      (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root _ (.bnd 0) _)))
    θΨ

/-- `kPsiV` in the `□` view. -/
abbrev kPsiS {Γ : Ctx} [Γ.NoSlots] {C : VarType} (T : VarType) {c : Ann C}
    (sb : Term σ Γ.boxIn C c) (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C T)) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) T) 1 :=
  kPsiV (V := Γ.boxIn) T sb θΨ

section KThetaR

variable (hS : ModalSys.BStrong = true) {C : VarType} (S : RShape)

/-- The hole context with a route bound: the hole `bnd 0 : ⟨value, □items⟩`, the route `bnd 1`. -/
abbrev kRCtx (S : RShape) (C : VarType) : Ctx :=
  (Ctx.empty.insert (.bnd 0) (.VTypeProd S.flat (.VTypeBox C))).insert (.bnd 1)
    (.VTypeDia .VTypeOne)

omit [ModalSys.NoFour] in
theorem kRCtx_slots : (kRCtx S C).SlotsFrom 2 :=
  (Ctx.slotsFrom_empty.insert _).insert _

omit [ModalSys.NoFour] in
theorem kRCtx_route : (kRCtx S C).ref (.root (.bnd 1)) = some (.VTypeDia .VTypeOne) :=
  Ctx.ref_insert_root _ _ _

omit [ModalSys.NoFour] in
theorem kRCtx_hole : (kRCtx S C).ref (.root (.bnd 0)) =
    some (.VTypeProd S.flat (.VTypeBox C)) :=
  (Ctx.le_insert (Ctx.slotsFrom_empty.insert _).root _).ref (Ctx.ref_insert_root _ _ _)

omit [ModalSys.NoFour] in
theorem kRCtx_items : (((kRCtx S C).diaIn (.root (.bnd 1))).insert (.bnd 2) S.ty).ref
    (VarSymb.step (.root (.bnd 0)) .snd).inner = some C :=
  (Ctx.le_insert ((kRCtx_slots S).diaIn _).root _).ref ((Ctx.le_boxIn_diaIn _ _).ref
    (Ctx.ref_inner (Ctx.ref_snd_of (kRCtx_hole S))))

/-- ⭐The negated route as a hole formula over a value `y` and a necessary object `s`:
    `∀κ. ¬◇_κ[e ↦ y] θΨ(s.box, e)`. -/
def kThetaR (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C S.ty)) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd S.flat (.VTypeBox C))) 1 :=
  WFF.all (.VTypeDia .VTypeOne) (WFF.neg (WFF.retxS hS (.root (.bnd 1))
    ⟨.VTypeOne, kRCtx_route S⟩ S
    (Term.eta (.step (.root (.bnd 0)) .fst) S.flat (Ctx.ref_fst_of (kRCtx_hole S)))
    (WFF.holeAt (((kRCtx_slots S).diaIn _).insert S.ty)
      (Term.pair (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner C (kRCtx_items S))
        (Term.eta (.root (.bnd 2)) S.ty (Ctx.ref_insert_root _ (.bnd 2) _)))
      θΨ)))

omit [ModalSys.NoFour] in
/-- ⭐The negated route read, at any depth, at a value and a necessary object `□s`. -/
theorem holeAt_kThetaR {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) {a : Ann S.flat}
    (y : Term σ Δ S.flat a) {c : Ann C} (s : Term σ Δ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C S.ty)) 1) :
    WFF.holeAt hs (Term.pair y (Term.boxtm s)) (kThetaR hS S θΨ) =
      WFF.all (.VTypeDia .VTypeOne) (WFF.neg (WFF.retxS hS (.root (.bnd d))
        ⟨.VTypeOne, Ctx.ref_insert_root Δ (.bnd d) _⟩ S
        (Term.mono (Ctx.le_insert hs.root _) y)
        (WFF.holeAt (((hs.insert _).diaIn _).insert S.ty)
          (Term.pair (Term.mono ((((Ctx.le_insert hs.root _).boxIn.trans
              (Ctx.le_boxIn_diaIn _ _)).trans (Ctx.le_insert ((hs.insert _).diaIn _).root _)))
              s)
            (Term.eta (.root (.bnd (d + 1))) S.ty (Ctx.ref_insert_root _ (.bnd (d + 1)) _)))
          θΨ))) := by
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair y (Term.boxtm s)))).at
      (.root (.bnd 0)) = .tm (Term.pair y (Term.boxtm s)) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  have hθ₀ := Subst.ok_single (σ := σ) (Ctx.empty_le Δ) (r := .bnd 0)
    (e := .tm (Term.pair y (Term.boxtm s)))
    (T := .VTypeProd S.flat (.VTypeBox C)) rfl
  have hc₀ := Subst.coh_single (σ := σ) (Ctx.RootFresh.empty (.bnd 0)) (Ctx.empty_le Δ)
    (e := .tm (Term.pair y (Term.boxtm s))) (T := .VTypeProd S.flat (.VTypeBox C)) rfl
  have hθ := Subst.ok_under hθ₀ (d := 0 + 1) (.VTypeDia .VTypeOne) hs.root
  have hc := Subst.coh_under hθ₀ hc₀ (Ctx.slotsFrom_empty.insert _) (.VTypeDia .VTypeOne) hs.root
  have hw : (((Subst.single (σ := σ) (.bnd 0) (.tm (Term.pair y (Term.boxtm s)))).under (0 + 1) d
      (.VTypeDia .VTypeOne) hs.root).at (.root (.bnd 1))).idxAlong [] = .root (.bnd d) := by
    rw [Subst.under_at_slot]
    rfl
  have hsl := (hs.insert (.VTypeDia .VTypeOne)).diaIn (.root (.bnd d))
  conv_lhs => unfold WFF.holeAt kThetaR
  refine congrArg (WFF.all _) (congrArg (fun φ => WFF.imp φ WFF.bot) ?_)
  rw [WFF.subst_retxS_at _ hθ hc _ _ hS _ _ _ _ _ (.root (.bnd d)) rfl
    ⟨_, Ctx.ref_insert_root Δ (.bnd d) _⟩ hsl (Subst.ok_dia hθ ⟨_, kRCtx_route S⟩ hw)
    (Subst.coh_dia hθ hc ⟨_, kRCtx_route S⟩)]
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · exact Term.subst_eta_tm _ _ _ _ _ _ _
      (by rw [Subst.at_proj _ _ rfl, Subst.at_under_ne _ _ _ (fun h => by cases h), h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
    · refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      have hsnd : ((Subst.single (σ := σ) (.bnd 0) (.tm (Term.pair y (Term.boxtm s)))).under
          (0 + 1) d (.VTypeDia .VTypeOne) hs.root).at (.step (.root (.bnd 0)) .snd) =
          .tm (Term.boxtm (Term.mono (Ctx.le_insert hs.root (.VTypeDia .VTypeOne)).boxIn s)) := by
        rw [Subst.at_proj _ _ rfl, Subst.at_under_ne _ _ _ (fun h => by cases h), h0]
        rfl
      rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.dia_eq_box_mono (Δ₁ := kRCtx S C) _ _ _ _ _
          (Ctx.ref_inner (Ctx.ref_snd_of (kRCtx_hole S))),
        Subst.box_at_inner_boxtm _ hsnd]
      change SubE.tm (Term.mono _ (Term.mono _ (Term.mono _ s))) = _
      rw [Term.mono_mono, Term.mono_mono]
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ 2 (d + 1) _ _)

/-- The negated route over a home value `y` and items `s`, the route bound: `¬◇_κ[e ↦ y] θΨ(s, e)`
    with `κ` the slot (`kThetaR` read at home). -/
def routeBody {Γ : Ctx} [Γ.NoSlots] {a : Ann S.flat} (y : Term σ Γ S.flat a)
    {c : Ann C} (s : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C S.ty)) 1) :
    WFF σ (Γ.insert (.bnd 0) (.VTypeDia .VTypeOne)) 1 :=
  WFF.neg (WFF.retxS hS (.root (.bnd 0))
    ⟨.VTypeOne, Ctx.ref_insert_root Γ (.bnd 0) _⟩ S
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _) y)
    (WFF.holeAt ((((Ctx.NoSlots.slots (Γ := Γ)).insert _).diaIn _).insert S.ty)
      (Term.pair (Term.mono ((((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _).boxIn.trans
          (Ctx.le_boxIn_diaIn _ _)).trans
          (Ctx.le_insert (((Ctx.NoSlots.slots (Γ := Γ)).insert _).diaIn _).root _))) s)
        (Term.eta (.root (.bnd (0 + 1))) S.ty
          (Ctx.ref_insert_root _ (.bnd (0 + 1)) _)))
      θΨ))

omit [ModalSys.NoFour] in
/-- At home the negated route is the universal of `routeBody`. -/
theorem holeRead_kThetaR {Γ : Ctx} [Γ.NoSlots] {a : Ann S.flat}
    (y : Term σ Γ S.flat a) {c : Ann C} (s : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C S.ty)) 1) :
    WFF.holeRead (Term.pair y (Term.boxtm s)) (kThetaR hS S θΨ) =
      WFF.all (.VTypeDia .VTypeOne) (routeBody hS S y s θΨ) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaR]
  rfl

/-- ⭐**The route instantiated** at a possible object `x`: `¬◇_x[e ↦ y] θΨ(s, e)`, the body read
    in `x`'s view. -/
theorem instantiate_routeBody {Γ : Ctx} [Γ.NoSlots] {a : Ann S.flat}
    (y : Term σ Γ S.flat a) {c : Ann C} (s : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C S.ty)) 1) {x : VarSymb}
    (hx : Γ.ref x = some (.VTypeDia .VTypeOne)) :
    WFF.instantiate Ctx.NoSlots.slots (Term.eta x (.VTypeDia .VTypeOne) hx)
        (routeBody hS S y s θΨ) =
      WFF.neg (WFF.retxS hS x ⟨.VTypeOne, hx⟩ S y
        ((OutLeg.pos x ⟨.VTypeOne, hx⟩).lift (kPsiS S.ty s θΨ))) := by
  have hθ := Subst.ok_single (σ := σ) (Ctx.Le.refl Γ) (r := .bnd 0)
    (e := .tm (Term.eta x (.VTypeDia .VTypeOne) hx)) (T := .VTypeDia .VTypeOne) rfl
  have hc := Subst.coh_single (σ := σ) ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0))
    (Ctx.Le.refl Γ) (e := .tm (Term.eta x (.VTypeDia .VTypeOne) hx)) (T := .VTypeDia .VTypeOne) rfl
  have hw : ((Subst.single (σ := σ) (.bnd 0)
      (.tm (Term.eta x (.VTypeDia .VTypeOne) hx))).at (.root (.bnd 0))).idxAlong [] = x := by
    rw [Subst.at_single_root]
    rfl
  have hr0 := Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia .VTypeOne)
  unfold WFF.instantiate WFF.substRoot routeBody
  refine congrArg (fun φ => WFF.imp φ WFF.bot) ?_
  rw [WFF.subst_retxS_at _ hθ hc _ _ hS (.root (.bnd 0)) _ _ _ _ x
    (show Subst.singleIdx (.bnd 0) (.tm (Term.eta x _ hx)) (.root (.bnd 0)) = x from
      (hc _ _ hr0 []).symm.trans hw) ⟨_, hx⟩
    ((Ctx.NoSlots.slots (Γ := Γ)).diaIn x) (Subst.ok_dia hθ ⟨_, hr0⟩ hw)
    (Subst.coh_dia hθ hc ⟨_, hr0⟩)]
  refine WFF.retxS_congr hS _ _ _ (Term.subst_single_mono_sig _ y) ?_
  unfold kPsiS kPsiV
  dsimp only [OutLeg.lift]
  rw [WFF.subst_holeAt, WFF.mono_holeAt _ _ (((Ctx.NoSlots.slots (Γ := Γ)).diaIn x).insert _)]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
  · rw [Term.subst_mono]
    refine (Term.subst_ren _ _ _ _ (Subst.at_ren_of fun v U _ hv => ?_) s).trans
      (congrArg (Sigma.mk _) (Term.mono_mono _ _ s).symm)
    obtain ⟨u, rfl, hu⟩ := boxIn_item_route hv
    have hu0 : u.rt ≠ .bnd 0 :=
      Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hu
    change (if VarSymb.step u .box = .root (.bnd (0 + 1)) then _ else _) = _
    rw [if_neg (fun h => by cases h)]
    change (((Subst.single _ _).at u).unbox.mono _).mono _ = _
    rw [Subst.single_at_ne hu0]
    change SubE.ren u.inner = _
    rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
  · exact (Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) 0 _ _)).trans
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm)

omit [ModalSys.NoFour] in
theorem mono_routeBody {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    {a : Ann S.flat} (y : Term σ Γ S.flat a) {c : Ann C}
    (s : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C S.ty)) 1) :
    WFF.mono (h.insert (.bnd 0) _) (routeBody hS S y s θΨ) =
      routeBody hS S (Term.mono h y) (Term.mono h.boxIn s) θΨ := by
  unfold routeBody
  refine congrArg (fun φ => WFF.imp φ WFF.bot) ?_
  refine WFF.retxS_congr hS _ _ _ (congrArg (Sigma.mk _) (by rw [Term.mono_mono, Term.mono_mono]))
    ?_
  rw [WFF.mono_holeAt _ _ ((((Ctx.NoSlots.slots (Γ := Γ')).insert _).diaIn _).insert _)]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
  · rw [Term.mono_mono, Term.mono_mono]
  · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

end KThetaR

/-! ## The derivation, at a necessary shape -/

section Route

variable (hS : ModalSys.BStrong = true) (hW : ModalSys.BStrongW = true) {A C : VarType}
  (co : List (List Step)) (ho : A.CompOk co)

/-- `θΨ` read at a witnessed value's first part and an object: `θΨ(hole.1.1, hole.2)`. -/
def thetaFst {T : VarType} (X : VarType)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C T)) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd C X) T)) 1 :=
  WFF.holeAt (Ctx.slotsFrom_empty.insert _)
    (Term.pair
      (Term.eta (.step (.step (.root (.bnd 0)) .fst) .fst) C
        (Ctx.ref_fst_of (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
      (Term.eta (.step (.root (.bnd 0)) .snd) T
        (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
    θΨ

omit [ModalSys.NoFour] in
theorem holeAt_thetaFst {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (X : VarType) {c : Ann C}
    (s : Term σ Δ C c) {b : Ann X} (z : Term σ Δ X b) {T : VarType} {e : Ann T}
    (o : Term σ Δ T e) (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C T)) 1) :
    WFF.holeAt hs (Term.pair (Term.pair s z) o) (thetaFst X θΨ) =
      WFF.holeAt hs (Term.pair s o) θΨ := by
  have h0 := Subst.at_single_root (σ := σ) (Δ := Δ) (.bnd 0)
    (.tm (Term.pair (Term.pair s z) o))
  change WFF.subst _ _ _ _ _ _ (WFF.holeAt _ _ θΨ) = _
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
  · exact Term.subst_eta_tm _ _ _ _ _ _ s
      (by rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]; rfl)
  · exact Term.subst_eta_tm _ _ _ _ _ _ o (by rw [Subst.at_proj _ _ rfl, h0]; rfl)

omit [ModalSys.NoFour] in
theorem holeRead_thetaFst {Γ : Ctx} [Γ.NoSlots] (X : VarType) {c : Ann C} (s : Term σ Γ C c)
    {b : Ann X} (z : Term σ Γ X b) {T : VarType} {e : Ann T} (o : Term σ Γ T e)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C T)) 1) :
    WFF.holeRead (Term.pair (Term.pair s z) o) (thetaFst X θΨ) =
      WFF.holeRead (Term.pair s o) θΨ := by
  rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt, holeAt_thetaFst]

omit [ModalSys.NoFour] in
/-- Weakening `kPsi` weakens its home object. -/
theorem mono_kPsi {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ') {c : Ann C}
    (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.mono (h.boxIn.insert (.bnd 0) _) (kPsi sb θΨ) = kPsi (Term.mono h.boxIn sb) θΨ := by
  unfold kPsi
  rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).insert _)]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
  · rw [Term.mono_mono, Term.mono_mono]
  · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

omit [ModalSys.NoFour] in
/-- Opening the unit's conjunct at `u`: a returning possibility whose body is `θ` read at `u`'s
    contents with companions and the inner slot. -/
theorem openFree_unitBodyC {Γ : Ctx} [Γ.NoSlots] {u : ℕ} (hu : Γ.boxIn.RootFresh (.free u))
    {a₀ : Ann C} (sb : Term σ Γ.boxIn C a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (A.compsFlat co) (.VTypeBox C))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.unitBodyC (Γ := Γ) hS co ho sb [] (Or.inl rfl) θ) =
      WFF.retS hS (.box C) (Term.mono (Ctx.le_insert hu.root _) sb)
        (kPsi (Γ := Γ.boxIn.insert (.free u) (.VTypeBox A))
          (compsSlot (Ctx.ref_insert_root _ _ _) (Ctx.Le.refl _) co ho).2 θ) := by
  unfold WFF.openFree WFF.unitBodyC kPsi
  refine WFF.retS_congr hS _ (subst_toFree_mono_sig hu sb) ?_
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair
    ((Term.subst_compsSlot _ _ (Ctx.ref_insert_root Γ.boxIn (.free u) (.VTypeBox A))
      (Ctx.le_insert (Ctx.NoSlots.slots
        (Γ := (Γ.boxIn.insert (.free u) (.VTypeBox A)).boxIn)).root _) _ _ _
      (fun q _ hq _ => ?_) co ho).trans
      (mono_compsSlot (Ctx.ref_insert_root Γ.boxIn (.free u) (.VTypeBox A))
        (Ctx.Le.refl _) _ co ho).symm)
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) θ
  rw [Subst.at_under_ne _ _ _ (by
      rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
    Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q (by
      change Subst.toFree _ _ _ _ _ (.root (.bnd 0)) = _
      exact Subst.toFree_root _ _ _ _ _) hq)]
  rfl

omit [ModalSys.NoFour] in
theorem bodyRepl_realL_kPsi {Γ : Ctx} [Γ.NoSlots] (X : VarType) {c : Ann C}
    (s : Term σ Γ.boxIn C c)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.bodyRepl (RShape.realL Γ.boxIn (.box A) X).2 (kPsi s θ) = kPsiF X s θ := by
  unfold WFF.bodyRepl kPsi kPsiF
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θ
  · rw [Term.subst_mono]
    refine Term.subst_ren _ _ _ _ (Subst.at_ren_of fun v U _ hv => ?_) s
    have hvr : v ≠ .root (.bnd 0) := fun h => by
      subst h
      rw [(Ctx.NoSlots.slots (Γ := Γ.boxIn)).root] at hv
      cases hv
    rw [Subst.set_ne _ _ hvr]
    rfl
  · exact Term.subst_eta_tm _ _ _ _ _ _ _ (by rw [Subst.at_nonproj _ rfl, Subst.set_root]; rfl)

omit [ModalSys.NoFour] in
/-- Opening the possible-part unit's conjunct, carrying `thetaFst`: a returning possibility along
    the possible part whose body is `θΨ` read at the necessary part's contents. -/
theorem openFree_unitBodyDC_thetaFst {Γ : Ctx} [Γ.NoSlots] {u : ℕ}
    (hu : Γ.boxIn.RootFresh (.free u)) {X : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots
        (WFF.unitBodyDC (Γ := Γ) hS [] (Or.inl rfl) sb co ho (thetaFst X θΨ)) =
      WFF.retxS hS (.step (.root (.free u)) .snd) ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
        (.nec (.boxC A co ho)) (Term.mono (Ctx.le_insert hu.root _) (compsVal sb co ho).2)
        ((OutLeg.pos (.step (.root (.free u)) .snd)
            ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩).lift
          (kPsi (Γ := Γ.boxIn.insert (.free u) (RShape.wit (.box C) X).ty)
            (Term.eta (VarSymb.step (.root (.free u)) .fst).inner C
              (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
            θΨ)) := by
  have hu0 := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu0
  have hθ := Subst.ok_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn))
    (RShape.wit (.box C) X).ty hu.root
  have hc := Subst.coh_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn)) Subst.coh_idRen
    (Ctx.NoSlots.slots (Γ := Γ.boxIn)) (RShape.wit (.box C) X).ty hu.root
  have h0 : ((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box C) X).ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  have hw : (((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box C) X).ty
      hu.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .step (.root (.free u)) .snd := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hsl := ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insertFree u
    (RShape.wit (.box C) X).ty).diaIn (.step (.root (.free u)) .snd)
  unfold WFF.openFree WFF.unitBodyDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.step (.root (.free u)) .snd) rfl
    ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ hsl (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (subst_toFree_mono_sig hu _) ?_
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root Γ.boxIn (.free u) (RShape.wit (.box C) X).ty
  refine (WFF.holeAt_congr _ (sig_pair (sig_pair
    (Term.subst_eta_renAt _ _ _ C _ (VarSymb.step (.root (.free u)) .fst).inner _
      ((Ctx.le_insert hsl.root (.VTypeBox A)).ref ((Ctx.le_boxIn_diaIn _ _).ref
        (Ctx.ref_inner (Ctx.ref_fst_of hT)))) ?_)
    (Term.subst_eta_renAt _ _ _ X _ (.step (.step (.root (.free u)) .snd) .dia) _
      ((Ctx.le_insert hsl.root (.VTypeBox A)).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of hT))) ?_))
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.dia_eq_box_mono (Δ₁ := Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) _ _ _ _ _
        (Ctx.ref_inner (Ctx.ref_fst_of hu0)),
      Subst.box_at_inner_ren _ (w := .step (.root (.free u)) .fst)
        (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  · rw [holeAt_thetaFst]
    unfold kPsi
    dsimp only [OutLeg.lift]
    rw [WFF.mono_holeAt _ _ (((Ctx.NoSlots.slots (Γ := (Γ.boxIn.insert (.free u)
      (RShape.wit (.box C) X).ty).diaIn (.step (.root (.free u)) .snd))).insert _))]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
    · exact congrArg (Sigma.mk _) (by rw [Term.mono_mono, Term.mono_eta])
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm

/-- ⭐**The far world refutes the carried negation**, in the `□` view: `Ψ(d)` with, looking back,
    `∀κ. ¬◇_κ[e ↦ d's contents] Ψ(e)` has no instance.  At the far world the backward returning
    possibility is realised with a possible part `p` (`ret_realise`), and the possible-part unit
    along `p` (`ret_unitDC`) brings `Ψ` back as a returning possibility along `p`, against the
    universal at `κ := p`. -/
def Proof.kThetaR_refute {Γ : Ctx} [Γ.Presented] {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    Proof σ Γ.boxIn [WFF.ex (.VTypeBox A)
      (WFF.and (kPsi sb θΨ)
        (WFF.unitBodyC hS co ho sb [] (Or.inl rfl)
          (kThetaR hS (.nec (.boxC A co ho)) θΨ)))] .bot := by
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ.boxIn)) :=
    Ctx.Presented.fresh_bound _ le_rfl
  refine Proof.ex_elim _ (.VTypeBox A) hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsi sb θΨ)
        (WFF.unitBodyC hS co ho sb [] (Or.inl rfl)
          (kThetaR hS (.nec (.boxC A co ho)) θΨ)))) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  refine Proof.ofSubset (Δ := [WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsi sb θΨ)
        (WFF.unitBodyC hS co ho sb [] (Or.inl rfl) (kThetaR hS (.nec (.boxC A co ho)) θΨ)))])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact List.mem_cons_self) ?_
  -- at the far world: `Ψ` here, and the backward returning possibility carrying the universal
  have H1 := Proof.conv (openFree_kPsi hu sb θΨ)
    (Proof.and_elim_l (Proof.lookup (Δ := [WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsi sb θΨ)
        (WFF.unitBodyC hS co ho sb [] (Or.inl rfl) (kThetaR hS (.nec (.boxC A co ho)) θΨ)))])
      List.mem_cons_self))
  have H2 := Proof.conv (openFree_unitBodyC hS co ho hu sb (kThetaR hS (.nec (.boxC A co ho)) θΨ))
    (Proof.and_elim_r (φ := WFF.openFree _ hu Ctx.NoSlots.slots (kPsi sb θΨ))
      (Proof.lookup (Δ := [WFF.openFree _ hu Ctx.NoSlots.slots
        (WFF.and (kPsi sb θΨ)
          (WFF.unitBodyC hS co ho sb [] (Or.inl rfl) (kThetaR hS (.nec (.boxC A co ho)) θΨ)))])
        List.mem_cons_self))
  have P2 := Proof.ret_realise hS hW .nec (.box C) _ Term.unit _ H2
  have P3 := Proof.ret_unitDC hS .nec [] (Or.inl rfl) _ _
    (Term.eta (VarSymb.root (.free (Ctx.Presented.bound Γ.boxIn))).inner A
      (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) co ho (thetaFst .VTypeOne θΨ) P2
    (Proof.conv (holeRead_thetaFst .VTypeOne _ _ _ θΨ).symm H1)
  refine Proof.retS_refute hS (.wit (.box C) .VTypeOne) _ _ ?_ P3
  -- back at home, opened at the realised part `u₂ = ⟨s, p⟩`: the universal against `p`'s return
  set Γ₁ := Γ.boxIn.insert (.free (Ctx.Presented.bound Γ.boxIn)) (.VTypeBox A)
  have hu₂ : Γ₁.boxIn.RootFresh (.free (Ctx.Presented.bound Γ₁.boxIn)) :=
    Ctx.Presented.fresh_bound _ le_rfl
  set Ξ := WFF.and (WFF.bodyRepl (RShape.realL Γ₁.boxIn (.box C) .VTypeOne).2
      (kPsi (compsSlot (Ctx.ref_insert_root _ _ _) (Ctx.Le.refl _) co ho).2
        (kThetaR hS (.nec (.boxC A co ho)) θΨ)))
    ((OutLeg.nec : OutLeg Γ₁).lift (WFF.unitBodyDC hS [] (Or.inl rfl)
      (Term.eta (VarSymb.root (.free (Ctx.Presented.bound Γ.boxIn))).inner A
        (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) co ho (thetaFst .VTypeOne θΨ)))
  refine Proof.imp_intro (Proof.ex_elim _ _ hu₂ (φ := WFF.openFree _ hu₂ Ctx.NoSlots.slots Ξ)
    (ψ := .bot) (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_)
  refine Proof.ofSubset (Δ := [WFF.openFree _ hu₂ Ctx.NoSlots.slots Ξ])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact List.mem_cons_self) ?_
  have K1 := Proof.conv (holeRead_kThetaR hS (.nec (.boxC A co ho)) _
      (Term.eta (VarSymb.step (.root (.free (Ctx.Presented.bound Γ₁.boxIn))) .fst).inner C
        (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))) θΨ)
    (Proof.conv (by rw [bodyRepl_realL_kPsi, openFree_kPsiF]; rfl)
      (Proof.and_elim_l (φ := WFF.openFree _ hu₂ Ctx.NoSlots.slots
        (WFF.bodyRepl (RShape.realL Γ₁.boxIn (.box C) .VTypeOne).2
          (kPsi (compsSlot (Ctx.ref_insert_root _ _ _) (Ctx.Le.refl _) co ho).2
            (kThetaR hS (.nec (.boxC A co ho)) θΨ))))
        (Proof.lookup (Δ := [WFF.openFree _ hu₂ Ctx.NoSlots.slots Ξ]) List.mem_cons_self)))
  have K2 := Proof.conv (openFree_unitBodyDC_thetaFst hS co ho hu₂ _ θΨ)
    (Proof.and_elim_r
      (Proof.lookup (Δ := [WFF.openFree _ hu₂ Ctx.NoSlots.slots Ξ]) List.mem_cons_self))
  have K3 := Proof.conv (instantiate_routeBody hS (.nec (.boxC A co ho)) _ _ θΨ
      (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))
    (Proof.all_elim _ (Term.eta (.step (.root (.free (Ctx.Presented.bound Γ₁.boxIn))) .snd)
      (.VTypeDia .VTypeOne) (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))) K1)
  refine Proof.imp_elim K3 (Proof.conv ?_ K2)
  exact WFF.retxS_congr hS _ _ _ (sig_mono _ (compsVal_eta _ co ho)) rfl

/-- ⭐⭐**Naming the route is derivable** (the route rule's elimination form, at a necessary shape
    with companions, its body given by home items and a hole formula).  Were the conclusion
    false, every fresh route would fail (`∀κ. ¬◇_κ[d ↦ t] Ψ`); `ret_unit` carries that out
    (`kThetaR`), and the far world refutes it (`Proof.kThetaR_refute`). -/
def Proof.ret_routeK {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} {a : Ann (A.compsFlat co)}
    (t : Term σ Γ (A.compsFlat co) a) {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1)
    (κ : ℕ) (hκ : Γ.RootFresh (.free κ)) {φ : WFF σ Γ 0}
    (p : Proof σ Γ Δ (WFF.retS hS (.nec (.boxC A co ho)) t (kPsi sb θΨ)))
    (q : Proof σ (Γ.insert (.free κ) (.VTypeDia .VTypeOne))
      (WFF.retxS hS (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩
          (.nec (.boxC A co ho)) (Term.weaken hκ.root _ t)
          (WFF.mono (((Ctx.le_insert hκ.root _).boxIn.trans
            (Ctx.le_boxIn_diaIn _ (.root (.free κ)))).insert (.bnd 0) _) (kPsi sb θΨ)) ::
        Δ.map (WFF.weaken hκ.root _)) (φ.weaken hκ.root _)) :
    Proof σ Γ Δ φ := by
  refine Proof.byContra ?_
  have e : WFF.retxS hS (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩
        (.nec (.boxC A co ho)) (Term.mono (Ctx.le_insert hκ.root _) t)
        ((OutLeg.pos (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩).lift
          (kPsiS (RShape.nec (.boxC A co ho)).ty
            (Term.mono (Ctx.le_insert hκ.root _).boxIn sb) θΨ)) =
      WFF.retxS hS (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩
        (.nec (.boxC A co ho)) (Term.weaken hκ.root _ t)
        (WFF.mono (((Ctx.le_insert hκ.root _).boxIn.trans
          (Ctx.le_boxIn_diaIn _ (.root (.free κ)))).insert (.bnd 0) _) (kPsi sb θΨ)) := by
    refine WFF.retxS_congr hS _ _ _ rfl ?_
    rw [show kPsiS (RShape.nec (.boxC A co ho)).ty
        (Term.mono (Ctx.le_insert hκ.root (.VTypeDia .VTypeOne)).boxIn sb) θΨ =
      kPsi (Term.mono (Ctx.le_insert hκ.root (.VTypeDia .VTypeOne)).boxIn sb) θΨ from rfl,
      ← mono_kPsi (Ctx.le_insert hκ.root (.VTypeDia .VTypeOne))]
    dsimp only [OutLeg.lift]
    rw [WFF.mono_mono]
  have h1 : Proof σ (Γ.insert (.free κ) (.VTypeDia .VTypeOne))
      ((φ.neg :: Δ).map (WFF.weaken hκ.root _))
      (WFF.openFree κ hκ Ctx.NoSlots.slots (routeBody hS (.nec (.boxC A co ho)) t sb θΨ)) := by
    rw [← WFF.instantiate_eta_openFree κ hκ Ctx.NoSlots.slots Ctx.NoSlots.slots,
      mono_routeBody hS (.nec (.boxC A co ho)) (Ctx.le_insert hκ.root (.VTypeDia .VTypeOne)),
      instantiate_routeBody,
      e]
    refine Proof.imp_intro (Proof.imp_elim
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)) ?_)
    refine Proof.ofSubset (fun ψ hψ => ?_) q
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hψ)
  have hall := Proof.all_intro κ _ hκ h1
  rw [WFF.bindFree_openFree] at hall
  have P1 := Proof.ret_unitC hS .nec co ho t (kPsi sb θΨ) sb [] (Or.inl rfl)
    (kThetaR hS (.nec (.boxC A co ho)) θΨ) (Proof.ofSubset (fun _ h => List.mem_cons_of_mem _ h) p)
    (Proof.conv (holeRead_kThetaR hS (.nec (.boxC A co ho)) t sb θΨ).symm hall)
  exact Proof.retS_refute_lift hS .nec (.nec (.boxC A co ho)) t _
    (Proof.kThetaR_refute hS hW co ho sb θΨ) P1

end Route


/-! ## The derivation, at a witnessed shape -/

section RouteW

variable (hS : ModalSys.BStrong = true) (hW : ModalSys.BStrongW = true) {A C X : VarType}
  (co : List (List Step)) (ho : A.CompOk co)

omit [ModalSys.NoFour] in
/-- Opening `kPsiS` at `u` reads `θΨ` at the home items and `u`. -/
theorem openFree_kPsiS {Γ : Ctx} [Γ.NoSlots] {u : ℕ} (hu : Γ.boxIn.RootFresh (.free u))
    {T : VarType} {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C T)) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (kPsiS T sb θΨ) =
      WFF.holeRead (Term.pair (Term.mono (Ctx.le_insert hu.root _) sb)
        (Term.eta (.root (.free u)) T (Ctx.ref_insert_root _ _ _))) θΨ := by
  unfold kPsiS kPsiV WFF.openFree
  rw [WFF.subst_holeAt, WFF.holeRead_eq_holeAt]
  exact WFF.holeAt_congr _ (sig_pair (subst_toFree_mono_sig hu sb)
    (Term.subst_eta_renAt _ _ _ _ (.root (.bnd 0)) (.root (.free u)) _ _
      (by exact Subst.toFree_root _ _ _ _ _))) θΨ

/-- A body over a witnessed slot, read at an object `y` of a view and the slot's necessary part. -/
def kPsiFV {V : Ctx} [V.NoSlots] {D B : VarType} (X' : VarType) {c : Ann D} (y : Term σ V D c)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd D (.VTypeBox B))) 1) :
    WFF σ (V.insert (.bnd 0) (RShape.wit (.box B) X').ty) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert _)
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root _) y)
      (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox B)
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ (.bnd 0) _))))
    θ

omit [ModalSys.NoFour] in
theorem bodyRepl_realL_kPsiV {V : Ctx} [V.NoSlots] {D B : VarType} (X' : VarType) {c : Ann D}
    (y : Term σ V D c) (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd D (.VTypeBox B))) 1) :
    WFF.bodyRepl (RShape.realL V (.box B) X').2 (kPsiV (.VTypeBox B) y θ) = kPsiFV X' y θ := by
  unfold WFF.bodyRepl kPsiV kPsiFV
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θ
  · rw [Term.subst_mono]
    refine Term.subst_ren _ _ _ _ (Subst.at_ren_of fun v U _ hv => ?_) y
    have hvr : v ≠ .root (.bnd 0) := fun h => by
      subst h
      rw [(Ctx.NoSlots.slots (Γ := V)).root] at hv
      cases hv
    rw [Subst.set_ne _ _ hvr]
    rfl
  · exact Term.subst_eta_tm _ _ _ _ _ _ _ (by rw [Subst.at_nonproj _ rfl, Subst.set_root]; rfl)

omit [ModalSys.NoFour] in
theorem openFree_kPsiFV {V : Ctx} [V.NoSlots] {u : ℕ} (hu : V.RootFresh (.free u))
    {D B : VarType} (X' : VarType) {c : Ann D} (y : Term σ V D c)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd D (.VTypeBox B))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (kPsiFV X' y θ) =
      WFF.holeRead (Term.pair (Term.mono (Ctx.le_insert hu.root _) y)
        (Term.eta (.step (.root (.free u)) .fst) (.VTypeBox B)
          (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))) θ := by
  have h0 : ((Subst.idRen (σ := σ) V).toFree 0 u (RShape.wit (.box B) X').ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  unfold kPsiFV WFF.openFree
  rw [WFF.subst_holeAt, WFF.holeRead_eq_holeAt]
  exact WFF.holeAt_congr _ (sig_pair (subst_toFree_mono_sig hu y)
    (Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl))) θ

omit [ModalSys.NoFour] in
/-- Opening the possible-part unit's conjunct at `u`: a returning possibility along `u`'s possible
    part whose body is `θ` read at `u`'s value — its necessary part's contents with companions and
    the part's content — and the inner slot. -/
theorem openFree_unitBodyDC {Γ : Ctx} [Γ.NoSlots] {u : ℕ} (hu : Γ.boxIn.RootFresh (.free u))
    {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (A.compsFlat co) X) (.VTypeBox C))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots
        (WFF.unitBodyDC (Γ := Γ) hS co ho sb [] (Or.inl rfl) θ) =
      WFF.retxS hS (.step (.root (.free u)) .snd) ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
        (.box C) (Term.mono (Ctx.le_insert hu.root _) sb)
        (kPsiV (V := (Γ.boxIn.insert (.free u) (RShape.wit (.box A) X).ty).diaIn
            (.step (.root (.free u)) .snd)) (.VTypeBox C)
          (Term.pair
            (compsSlot (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)) (Ctx.le_boxIn_diaIn _ _)
              co ho).2
            (Term.eta (.step (.step (.root (.free u)) .snd) .dia) X
              (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))))
          θ) := by
  have hu0 := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box A) X).ty
  have hsnd := Ctx.ref_snd_of hu0
  have hθ := Subst.ok_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn))
    (RShape.wit (.box A) X).ty hu.root
  have hc := Subst.coh_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn)) Subst.coh_idRen
    (Ctx.NoSlots.slots (Γ := Γ.boxIn)) (RShape.wit (.box A) X).ty hu.root
  have h0 : ((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box A) X).ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  have hw : (((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box A) X).ty
      hu.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .step (.root (.free u)) .snd := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hsl := ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insertFree u
    (RShape.wit (.box A) X).ty).diaIn (.step (.root (.free u)) .snd)
  unfold WFF.openFree WFF.unitBodyDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.step (.root (.free u)) .snd) rfl
    ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ hsl (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (subst_toFree_mono_sig hu _) ?_
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root Γ.boxIn (.free u) (RShape.wit (.box A) X).ty
  refine (WFF.holeAt_congr _ (sig_pair (sig_pair
    ((Term.subst_compsSlot _ _ (Ctx.ref_fst_of hT) _ _ _ _ (fun q C' hq hr => ?_) co ho).trans
      (mono_compsSlot (Ctx.ref_fst_of hT) (Ctx.le_boxIn_diaIn _ _)
        (Ctx.le_insert hsl.root (.VTypeBox C)) co ho).symm)
    (Term.subst_eta_renAt _ _ _ X _ (.step (.step (.root (.free u)) .snd) .dia) _
      ((Ctx.le_insert hsl.root (.VTypeBox C)).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of hT))) ?_))
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) θ).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by
        rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
      Subst.dia_eq_box_mono (Δ₁ := Γ.boxIn.insert (.bnd 0) (RShape.wit (.box A) X).ty) _ _ _ _ _
        (Ctx.ref_inner hr),
      Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q
        (by rw [Subst.at_proj _ _ rfl, h0]; rfl) hq)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  · unfold kPsiV
    refine WFF.holeAt_congr _ (sig_pair (sig_pair rfl ?_) rfl) θ
    exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm

omit [ModalSys.NoFour] in
/-- Opening the doubly witnessed unit's conjunct, carrying `thetaFst`: a returning possibility
    along the possible part, at the witnessed shape, whose body is `θΨ` read at the necessary part's
    contents. -/
theorem openFree_unitBodyWDC_thetaFst {Γ : Ctx} [Γ.NoSlots] {x : VarSymb}
    {u : ℕ} (hu : (Γ.diaIn x).RootFresh (.free u))
    {Xe : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u' : Term σ (Γ.diaIn x) X b₀)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty)) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots
        (WFF.unitBodyWDC (Γ := Γ) (x := x) hS [] (Or.inl rfl) sb u' co ho (thetaFst Xe θΨ)) =
      WFF.retxS hS (.step (.root (.free u)) .snd) ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
        (.wit (.boxC A co ho) X)
        (Term.pair (Term.mono ((Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert hu.root _))
            (compsVal sb co ho).2)
          (Term.mono (Ctx.le_insert hu.root _) u'))
        ((OutLeg.pos (.step (.root (.free u)) .snd)
            ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩).lift
          (kPsiS (Γ := (Γ.diaIn x).insert (.free u) (RShape.wit (.box C) Xe).ty)
            (RShape.wit (.box A) X).ty
            (Term.eta (VarSymb.step (.root (.free u)) .fst).inner C
              (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
            θΨ)) := by
  have hu0 := Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) (RShape.wit (.box C) Xe).ty
  have hsnd := Ctx.ref_snd_of hu0
  have hθ := Subst.ok_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.diaIn x))
    (RShape.wit (.box C) Xe).ty hu.root
  have hc := Subst.coh_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.diaIn x))
    Subst.coh_idRen (Ctx.NoSlots.slots (Γ := Γ.diaIn x)) (RShape.wit (.box C) Xe).ty hu.root
  have h0 : ((Subst.idRen (σ := σ) (Γ.diaIn x)).toFree 0 u (RShape.wit (.box C) Xe).ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  have hw : (((Subst.idRen (σ := σ) (Γ.diaIn x)).toFree 0 u (RShape.wit (.box C) Xe).ty
      hu.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .step (.root (.free u)) .snd := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hsl := ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insertFree u
    (RShape.wit (.box C) Xe).ty).diaIn (.step (.root (.free u)) .snd)
  unfold WFF.openFree WFF.unitBodyWDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.step (.root (.free u)) .snd) rfl
    ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ hsl (Subst.ok_dia hθ ⟨Xe, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨Xe, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ (subst_toFree_mono_sig hu u')) ?_
  · have e := subst_toFree_mono_sig (T := (RShape.wit (.box C) Xe).ty) hu
      (Term.mono (Ctx.le_boxIn_diaIn Γ x) (compsVal sb co ho).2)
    rwa [Term.mono_mono, Term.mono_mono] at e
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root (Γ.diaIn x) (.free u) (RShape.wit (.box C) Xe).ty
  refine (WFF.holeAt_congr _ (sig_pair (sig_pair
    (Term.subst_eta_renAt _ _ _ C _ (VarSymb.step (.root (.free u)) .fst).inner _
      ((Ctx.le_insert hsl.root _).ref ((Ctx.le_boxIn_diaIn _ _).ref
        (Ctx.ref_inner (Ctx.ref_fst_of hT)))) ?_)
    (Term.subst_eta_renAt _ _ _ Xe _ (.step (.step (.root (.free u)) .snd) .dia) _
      ((Ctx.le_insert hsl.root _).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of hT))) ?_))
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.dia_eq_box_mono (Δ₁ := (Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty)
        _ _ _ _ _ (Ctx.ref_inner (Ctx.ref_fst_of hu0)),
      Subst.box_at_inner_ren _ (w := .step (.root (.free u)) .fst)
        (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  · rw [holeAt_thetaFst]
    unfold kPsiS kPsiV
    dsimp only [OutLeg.lift]
    rw [WFF.mono_holeAt _ _ (((Ctx.NoSlots.slots (Γ := ((Γ.diaIn x).insert (.free u)
      (RShape.wit (.box C) Xe).ty).diaIn (.step (.root (.free u)) .snd))).insert _))]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
    · exact congrArg (Sigma.mk _) (by rw [Term.mono_mono, Term.mono_eta])
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm

omit [ModalSys.NoFour] in
/-- Weakening `kPsiS` weakens its home items. -/
theorem mono_kPsiS {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ') {T : VarType} {c : Ann C}
    (sb : Term σ Γ.boxIn C c) (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C T)) 1) :
    WFF.mono (h.boxIn.insert (.bnd 0) _) (kPsiS T sb θΨ) = kPsiS T (Term.mono h.boxIn sb) θΨ := by
  unfold kPsiS kPsiV
  rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).insert _)]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
  · rw [Term.mono_mono, Term.mono_mono]
  · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

/-- ⭐**The far world refutes the carried negation, at a witnessed shape**: as
    `Proof.kThetaR_refute`, the backward returning possibility running along the returned possible
    part (`ret_unitDC`), realised along it (`ret_realise`), and the doubly witnessed unit
    (`ret_unitWDC`) bringing `Ψ` back along the realised part. -/
def Proof.kThetaRW_refute {Γ : Ctx} [Γ.Presented] {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty)) 1) :
    Proof σ Γ.boxIn [WFF.ex (RShape.wit (.box A) X).ty
      (WFF.and (kPsiS (RShape.wit (.box A) X).ty sb θΨ)
        (WFF.unitBodyDC hS co ho sb [] (Or.inl rfl)
          (kThetaR hS (.wit (.boxC A co ho) X) θΨ)))] .bot := by
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ.boxIn)) :=
    Ctx.Presented.fresh_bound _ le_rfl
  refine Proof.ex_elim _ (RShape.wit (.box A) X).ty hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsiS (RShape.wit (.box A) X).ty sb θΨ)
        (WFF.unitBodyDC hS co ho sb [] (Or.inl rfl)
          (kThetaR hS (.wit (.boxC A co ho) X) θΨ)))) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  refine Proof.ofSubset (Δ := [WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsiS (RShape.wit (.box A) X).ty sb θΨ)
        (WFF.unitBodyDC hS co ho sb [] (Or.inl rfl)
          (kThetaR hS (.wit (.boxC A co ho) X) θΨ)))])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact List.mem_cons_self) ?_
  set Γ₁ := Γ.boxIn.insert (.free (Ctx.Presented.bound Γ.boxIn)) (RShape.wit (.box A) X).ty
  have hx : ∃ X', Γ₁.ref (.step (.root (.free (Ctx.Presented.bound Γ.boxIn))) .snd) =
      some (.VTypeDia X') := ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
  have H1 := Proof.conv (openFree_kPsiS hu sb θΨ)
    (Proof.and_elim_l (Proof.lookup (Δ := [WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsiS (RShape.wit (.box A) X).ty sb θΨ)
        (WFF.unitBodyDC hS co ho sb [] (Or.inl rfl)
          (kThetaR hS (.wit (.boxC A co ho) X) θΨ)))]) List.mem_cons_self))
  have H2 := Proof.conv (openFree_unitBodyDC hS co ho hu sb
      (kThetaR hS (.wit (.boxC A co ho) X) θΨ))
    (Proof.and_elim_r (φ := WFF.openFree _ hu Ctx.NoSlots.slots
        (kPsiS (RShape.wit (.box A) X).ty sb θΨ))
      (Proof.lookup (Δ := [WFF.openFree _ hu Ctx.NoSlots.slots
        (WFF.and (kPsiS (RShape.wit (.box A) X).ty sb θΨ)
          (WFF.unitBodyDC hS co ho sb [] (Or.inl rfl)
            (kThetaR hS (.wit (.boxC A co ho) X) θΨ)))]) List.mem_cons_self))
  have P2 := Proof.ret_realise hS hW (.pos _ hx) (.box C) _ Term.unit _ H2
  have P3 := Proof.ret_unitWDC hS hx [] (Or.inl rfl) _ _
    (Term.eta (VarSymb.step (.root (.free (Ctx.Presented.bound Γ.boxIn))) .fst).inner A
      (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
    (Term.eta (.step (.step (.root (.free (Ctx.Presented.bound Γ.boxIn))) .snd) .dia) X
      (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
    co ho (thetaFst .VTypeOne θΨ) P2
    (Proof.conv (holeRead_thetaFst .VTypeOne _ _ _ θΨ).symm H1)
  refine Proof.retxS_refute hS hx (.wit (.box C) .VTypeOne) _ _ ?_ P3
  -- in the possible part's view, opened at the realised part `u₂ = ⟨s, p⟩`
  set V := Γ₁.diaIn (.step (.root (.free (Ctx.Presented.bound Γ.boxIn))) .snd)
  have hu₂ : V.RootFresh (.free (Ctx.Presented.bound V)) := Ctx.Presented.fresh_bound _ le_rfl
  set y := Term.pair
    (compsSlot (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)) (Ctx.le_boxIn_diaIn _ _) co ho).2
    (Term.eta (.step (.step (.root (.free (Ctx.Presented.bound Γ.boxIn))) .snd) .dia) X
      (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
  set Ξ := WFF.and (WFF.bodyRepl (RShape.realL V (.box C) .VTypeOne).2
      (kPsiV (.VTypeBox C) y (kThetaR hS (.wit (.boxC A co ho) X) θΨ)))
    (WFF.unitBodyWDC hS [] (Or.inl rfl)
      (Term.eta (VarSymb.step (.root (.free (Ctx.Presented.bound Γ.boxIn))) .fst).inner A
        (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
      (Term.eta (.step (.step (.root (.free (Ctx.Presented.bound Γ.boxIn))) .snd) .dia) X
        (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
      co ho (thetaFst .VTypeOne θΨ))
  refine Proof.ex_elim _ _ hu₂ (φ := WFF.openFree _ hu₂ Ctx.NoSlots.slots Ξ) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  refine Proof.ofSubset (Δ := [WFF.openFree _ hu₂ Ctx.NoSlots.slots Ξ])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact List.mem_cons_self) ?_
  have K1 := Proof.conv (holeRead_kThetaR hS (.wit (.boxC A co ho) X) _
      (Term.eta (VarSymb.step (.root (.free (Ctx.Presented.bound V))) .fst).inner C
        (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))) θΨ)
    (Proof.conv (by rw [bodyRepl_realL_kPsiV, openFree_kPsiFV]; rfl)
      (Proof.and_elim_l (φ := WFF.openFree _ hu₂ Ctx.NoSlots.slots
        (WFF.bodyRepl (RShape.realL V (.box C) .VTypeOne).2
          (kPsiV (.VTypeBox C) y (kThetaR hS (.wit (.boxC A co ho) X) θΨ))))
        (Proof.lookup (Δ := [WFF.openFree _ hu₂ Ctx.NoSlots.slots Ξ]) List.mem_cons_self)))
  have K2 := Proof.conv (openFree_unitBodyWDC_thetaFst hS co ho hu₂ _ _ θΨ)
    (Proof.and_elim_r
      (Proof.lookup (Δ := [WFF.openFree _ hu₂ Ctx.NoSlots.slots Ξ]) List.mem_cons_self))
  have K3 := Proof.conv (instantiate_routeBody hS (.wit (.boxC A co ho) X) _ _ θΨ
      (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))
    (Proof.all_elim _ (Term.eta (.step (.root (.free (Ctx.Presented.bound V))) .snd)
      (.VTypeDia .VTypeOne) (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))) K1)
  refine Proof.imp_elim K3 (Proof.conv ?_ K2)
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ rfl) rfl
  exact (sig_mono _ (compsVal_eta _ co ho)).trans
    ((mono_compsSlot _ _ _ co ho).trans (mono_compsSlot _ _ _ co ho).symm)

/-- ⭐⭐**Naming the route is derivable at a witnessed shape** (the route rule's elimination
    form, at `◇[⟨d, e⟩ ↦ t]` with companions, the body given by home items and a hole formula), as
    `Proof.ret_routeK`, the carried universal going out with the possible-part unit. -/
def Proof.ret_routeKW {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    {a : Ann (.VTypeProd (A.compsFlat co) X)} (t : Term σ Γ (.VTypeProd (A.compsFlat co) X) a)
    {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty)) 1)
    (κ : ℕ) (hκ : Γ.RootFresh (.free κ)) {φ : WFF σ Γ 0}
    (p : Proof σ Γ Δ (WFF.retS hS (.wit (.boxC A co ho) X) t
      (kPsiS (RShape.wit (.box A) X).ty sb θΨ)))
    (q : Proof σ (Γ.insert (.free κ) (.VTypeDia .VTypeOne))
      (WFF.retxS hS (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩
          (.wit (.boxC A co ho) X) (Term.weaken hκ.root _ t)
          (WFF.mono (((Ctx.le_insert hκ.root _).boxIn.trans
            (Ctx.le_boxIn_diaIn _ (.root (.free κ)))).insert (.bnd 0) _)
            (kPsiS (RShape.wit (.box A) X).ty sb θΨ)) ::
        Δ.map (WFF.weaken hκ.root _)) (φ.weaken hκ.root _)) :
    Proof σ Γ Δ φ := by
  refine Proof.byContra ?_
  have e : WFF.retxS hS (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩
        (.wit (.boxC A co ho) X) (Term.mono (Ctx.le_insert hκ.root _) t)
        ((OutLeg.pos (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩).lift
          (kPsiS (RShape.wit (.boxC A co ho) X).ty
            (Term.mono (Ctx.le_insert hκ.root _).boxIn sb) θΨ)) =
      WFF.retxS hS (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root Γ (.free κ) _⟩
        (.wit (.boxC A co ho) X) (Term.weaken hκ.root _ t)
        (WFF.mono (((Ctx.le_insert hκ.root _).boxIn.trans
          (Ctx.le_boxIn_diaIn _ (.root (.free κ)))).insert (.bnd 0) _)
          (kPsiS (RShape.wit (.box A) X).ty sb θΨ)) := by
    refine WFF.retxS_congr hS _ _ _ rfl ?_
    rw [show kPsiS (RShape.wit (.boxC A co ho) X).ty
        (Term.mono (Ctx.le_insert hκ.root (.VTypeDia .VTypeOne)).boxIn sb) θΨ =
      kPsiS (RShape.wit (.box A) X).ty
        (Term.mono (Ctx.le_insert hκ.root (.VTypeDia .VTypeOne)).boxIn sb) θΨ from rfl,
      ← mono_kPsiS (Ctx.le_insert hκ.root (.VTypeDia .VTypeOne))]
    dsimp only [OutLeg.lift]
    rw [WFF.mono_mono]
  have h1 : Proof σ (Γ.insert (.free κ) (.VTypeDia .VTypeOne))
      ((φ.neg :: Δ).map (WFF.weaken hκ.root _))
      (WFF.openFree κ hκ Ctx.NoSlots.slots
        (routeBody hS (.wit (.boxC A co ho) X) t sb θΨ)) := by
    rw [← WFF.instantiate_eta_openFree κ hκ Ctx.NoSlots.slots Ctx.NoSlots.slots,
      mono_routeBody hS (.wit (.boxC A co ho) X) (Ctx.le_insert hκ.root (.VTypeDia .VTypeOne)),
      instantiate_routeBody, e]
    refine Proof.imp_intro (Proof.imp_elim
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)) ?_)
    refine Proof.ofSubset (fun ψ hψ => ?_) q
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hψ)
  have hall := Proof.all_intro κ _ hκ h1
  rw [WFF.bindFree_openFree] at hall
  have P1 := Proof.ret_unitDC hS .nec co ho t (kPsiS (RShape.wit (.box A) X).ty sb θΨ) sb []
    (Or.inl rfl) (kThetaR hS (.wit (.boxC A co ho) X) θΨ)
    (Proof.ofSubset (fun _ h => List.mem_cons_of_mem _ h) p)
    (Proof.conv (holeRead_kThetaR hS (.wit (.boxC A co ho) X) t sb θΨ).symm hall)
  exact Proof.retS_refute_lift hS .nec (.wit (.boxC A co ho) X) t _
    (Proof.kThetaRW_refute hS hW co ho sb θΨ) P1

end RouteW

/-! ## At a node, for every body -/

/-- A shape whose necessary part is one object with companions — every shape packs into one
    (`NShape.packed`), and naming the route is derived at these. -/
def _root_.V12M.RShape.boxed : RShape → Bool
  | .nec (.boxC _ _ _) => true
  | .wit (.boxC _ _ _) _ => true
  | _ => false

omit [ModalSys.NoFour] in
/-- At a node every body is a hole formula at the roots' items and the slot (`pack2`). -/
theorem kPsiS_pack2 [ModalSys.NoFour] {l : List VarType} {T : VarType}
    (Θ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) T) 1) :
    kPsiS (Γ := ctxOf l) T (tupT l).2 (pack2 l T Θ) = Θ :=
  (holeAt_tupT_pack2 (Ctx.Le.refl _) Θ).trans (WFF.mono_refl _ Θ)

/-- ⭐⭐**Naming the route at a node** (the route rule at a boxed shape, any body): the body is
    packed (`kPsiS_pack2`), and the route named by `Proof.ret_routeK` or `Proof.ret_routeKW`. -/
def Proof.ret_route_node (hS : ModalSys.BStrong = true) (hW : ModalSys.BStrongW = true)
    {l : List VarType} {Δ : List (WFF σ (ctxOf l) 0)} {S : RShape} (hb : S.boxed = true)
    {a : Ann S.flat} (t : Term σ (ctxOf l) S.flat a)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) S.ty) 1) (κ : ℕ)
    (hκ : (ctxOf l).RootFresh (.free κ)) {φ : WFF σ (ctxOf l) 0}
    (p : Proof σ (ctxOf l) Δ (WFF.retS hS S t Φ))
    (q : Proof σ ((ctxOf l).insert (.free κ) (.VTypeDia .VTypeOne))
      (WFF.retxS hS (.root (.free κ)) ⟨.VTypeOne, Ctx.ref_insert_root (ctxOf l) (.free κ) _⟩ S
          (Term.weaken hκ.root _ t)
          (WFF.mono (((Ctx.le_insert hκ.root _).boxIn.trans
            (Ctx.le_boxIn_diaIn _ (.root (.free κ)))).insert (.bnd 0) S.ty) Φ) ::
        Δ.map (WFF.weaken hκ.root _)) (φ.weaken hκ.root _)) :
    Proof σ (ctxOf l) Δ φ := by
  revert p q
  rw [← kPsiS_pack2 Φ]
  intro p q
  match S, hb with
  | .nec (.boxC A co ho), _ =>
      exact Proof.ret_routeK hS hW co ho t (tupT l).2 (pack2 l _ Φ) κ hκ p q
  | .wit (.boxC A co ho) X, _ =>
      exact Proof.ret_routeKW hS hW co ho t (tupT l).2 (pack2 l _ Φ) κ hκ p q
  | .nec (.prod _ _), h => exact absurd h Bool.false_ne_true
  | .wit (.prod _ _) _, h => exact absurd h Bool.false_ne_true

end BArrow

end V12M
