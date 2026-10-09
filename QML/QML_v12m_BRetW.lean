import QML.QML_v12m_BRetX

/-!
# QML v12m — strong B on the network: the forward invariant of a witness arrow

A witness child `k` of `p`, made for `◇_x φ`, is a plain child with `x ⇝ cx` committed at birth
(docs §11.17).  Its forward arrow carries the returning-possibility invariant at the returnable
shape `□(roots) × ◇X` (`RetInvW`): what `p` says of its committed roots' necessary object and of
`x` holds at `k` of a returning possibility valued at the roots' images and `cx`, the witness
coming back as a possible part.

* `liftBodyW`, `RetInvW`: the invariant.
* `RetInvW.birth`: with nothing committed back it holds at birth, from the seed's `□_x` transfer
  and the witnessed unit's base form (`Proof.ret_unitW_base`).
-/

namespace V12M

namespace BArrow

variable [ModalSys] {σ : Signature} [ModalSys.NoFour]

/-! ## The invariant -/

/-- A witness body's context: the reverse arrow's committed roots' `□` view, with the bound object
    of shape `□(roots) × ◇X`. -/
abbrev bodyCtxW (cls clt : List VarType) (X : VarType) : Ctx :=
  (ctxOf clt).boxIn.insert (.bnd 0) (RShape.prod (.box (bcT cls)) (.dia X)).ty

/-- The bound object's entry at the parent: the committed roots' necessary object, paired with
    the witness `x` itself. -/
abbrev liftEntryW {lv cls : List VarType} (hs : cls <:+ lv) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) : SubE σ (ctxOf lv) :=
  .tm (Term.pair (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
    (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx)))

/-- ⭐A witness body read at the parent: its `□` items go along the reverse arrow (`imgt`), its
    bound object to the pair of the committed roots' necessary object and `x`. -/
def liftBodyW {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtxW cls clt X) 1) :
    WFF σ (ctxOf lv) 0 :=
  WFF.subst (Subst.setIdx (arrowIdx imgt) (.bnd 0) (liftEntryW hs hx))
    ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx))
    (Subst.ok_set (ok_arrowS himgt) rfl)
    (Subst.coh_set (ok_arrowS himgt) (coh_arrowS himgt)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _) Ctx.NoSlots.slots Φ

/-- ⭐**The forward invariant of a witness arrow** `p → k` made for `◇_x` (docs §11.17): every
    body over the committed roots `cls` and the witness that `p` makes true, read there, is at `k`
    a returning possibility of shape `□(roots) × ◇X`, valued at the roots' images and at `cx` —
    the witness comes back as a possible part, realised along the way home with content `cx`. -/
def RetInvW (hS : ModalSys.BStrong = true) (tv tw : NodeSt σ) (cls : List VarType)
    (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ) (x : VarSymb) (X : VarType) (cx : ℕ) :
    Prop :=
  ∃ (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs) (ht : clt <:+ tw.l)
    (himgt : ImgOk clt (ctxOf tv.l) imgt) (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tw.l).ref (.root (.free cx)) = some X),
    ∀ Φ : WFF σ (bodyCtxW cls clt X) 1, liftBodyW hs himgt hx Φ ∈ tv.M →
      WFF.retS hS (.prod (.box (bcT cls)) (.dia X))
        (Term.pair (tupImgT cls imgs himgs).2 (Term.eta (.root (.free cx)) X hcx))
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ tw.M

/-! ## Birth -/

omit [ModalSys.NoFour] in
/-- Weakening the witnessed unit's base body weakens its terms. -/
theorem WFF.mono_unitBaseW {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {x : VarSymb} {A X : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X} (u : Term σ (Γ.diaIn x) X b₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (RShape.prod (.box A) (.dia X)).ty) 1) :
    WFF.mono (h.diaIn x) (WFF.unitBaseW hS sb u θ) =
      WFF.unitBaseW hS (Term.mono h.boxIn sb) (Term.mono (h.diaIn x) u) θ := by
  unfold WFF.unitBaseW
  refine WFF.retS_congr' hS _ ?_ ?_
  · change Term.pair (Term.mono _ (Term.mono _ sb)) (Term.mono _ u) =
      Term.pair (Term.mono _ (Term.mono _ sb)) (Term.mono _ u)
    simp only [Term.mono_mono]
  · rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := (Γ'.diaIn x).boxIn)).insert _),
      Term.mono_eta]

/-- ⭐**The forward arrow of a witness child at birth has the invariant**: with nothing committed
    back, a body true at the parent of the committed roots' necessary object and `x` is, by the
    witnessed unit's base form, `□_x`-necessarily a returning possibility bringing back both —
    which the seed's `□_x` transfer sends to the child. -/
theorem RetInvW.birth (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    {tv tw : NodeSt σ} {cls : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType}
    {cx : ℕ} (hv : Theory.IsMCS tv.M) (hs : cls <:+ tv.l) (himgs : ImgOk cls (ctxOf tw.l) imgs)
    (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tw.l).ref (.root (.free cx)) = some X)
    (htr : TransferX tv.M cls (ctxOf_le_of_suffix hs) hx tw.M imgs himgs cx hcx) :
    RetInvW hS tv tw cls imgs [] imgt x X cx := by
  have himgt : ImgOk [] (ctxOf tv.l) imgt := fun r hr => absurd hr (Nat.not_lt_zero r)
  refine ⟨hs, himgs, List.nil_suffix, himgt, hx, hcx, fun Φ hΦ => ?_⟩
  have hle := ctxOf_le_of_suffix hs
  have hx' : ∃ X', (ctxOf tv.l).ref x = some (.VTypeDia X') := ⟨X, hle.ref hx⟩
  have hread : WFF.holeRead (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT cls).2))
      (Term.diatm x hx' (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx)))))
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert _)
        (Term.pair Term.unit (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
        (pack2 [] (RShape.prod (.box (bcT cls)) (.dia X)).ty Φ)) = liftBodyW hs himgt hx Φ := by
    rw [WFF.holeRead_eq_holeAt, WFF.holeAt_holeAt_pairUnit, ← WFF.holeRead_eq_holeAt]
    exact holeRead_tupImgT_pack2 himgt _ Φ
  have hbox := hv.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hΦ,
    ⟨Proof.ret_unitW_base hS hB hx' _ _ _
      (Proof.conv hread.symm (Proof.lookup List.mem_cons_self))⟩⟩
  have hbox' : WFF.mono hle (WFF.boxx x ⟨X, hx⟩ (WFF.unitBaseW (Γ := ctxOf cls) hS (tupT cls).2
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx))
      (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Ctx.empty)).insert _)
        (Term.pair Term.unit (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
        (pack2 [] (RShape.prod (.box (bcT cls)) (.dia X)).ty Φ)))) ∈ tv.M := by
    refine (congrArg (· ∈ tv.M) ?_).mpr hbox
    change WFF.boxx x _ (WFF.mono (hle.diaIn x) _) = _
    rw [WFF.mono_unitBaseW hle, Term.mono_eta]
    rfl
  refine (congrArg (· ∈ tw.M) ?_).mp (htr _ hbox')
  unfold WFF.unitBaseW
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ _ imgs) _ (ok_arrowS himgs) _ (coh_arrowS himgs)
      (Subst.sim_of fun v T _ hv => ?_) _).trans (subst_arrow_tupT cls himgs)
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    exact .refl _
  · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by rw [Subst.at_nonproj _ rfl]; exact if_pos rfl)
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ (Term.subst_eta_renAt _ _ _ _ _ _ _
      (Ctx.ref_insert_root _ (.bnd 0) _) (Subst.under_at_slot _ _ _ _ _)) _).trans ?_
    rw [WFF.holeAt_holeAt_pairUnit]
    exact holeAt_tupT_pack2 (ctxOf_le_of_suffix (List.nil_suffix (l := tw.l))).boxIn Φ

/-! ## Packing a body along `x` -/

/-- ⭐Packing the roots and `x`'s content: the item `u.box` goes to its entry of the tuple at `b`,
    as `packS` sends it, and `x.dia` to `c`. -/
def packXS (σ : Signature) (Δ : Ctx) (l : List VarType) (b x c : VarSymb) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => .ren ((packBase l b u.rt).ext (encPath u.path ++ itemTail))
  | .step u .dia => if u = x then .ren c else .hide
  | _ => .hide

open Classical in
/-- Where `packXS` sends annotation indices: below `x.dia` to below `c`. -/
noncomputable def packXIdx (l : List VarType) (b x c : VarSymb) (a : VarSymb) : VarSymb :=
  if a.rt = x.rt ∧ (x.path ++ [Step.dia]) <+: a.path then
    c.ext (a.path.drop (x.path.length + 1))
  else packIdx l b a

theorem ok_packXS (l : List VarType) {Δ : Ctx} {b : VarSymb} (hb : Δ.ref b = some (bcT l))
    {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X)) {c : VarSymb}
    (hc : Δ.ref c = some X) :
    Subst.Ok ((ctxOf l).diaIn x) (packXS σ Δ l b x c) := by
  intro v T _ hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, hxT⟩
  · exact ok_packS (σ := σ) l hb (.step u .box) T rfl
      (by rw [Ctx.boxIn_box_of ModalSys.NoFour.keepOnly hu])
  · rw [hx] at hxT
    cases hxT
    change (if x = x then SubE.ren c else .hide).OkRef X
    rw [if_pos rfl]
    exact hc

theorem coh_packXS (l : List VarType) {Δ : Ctx} {b : VarSymb} (hb : Δ.ref b = some (bcT l))
    {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X)) {c : VarSymb}
    (hc : Δ.ref c = some X) :
    Subst.Coh (packXIdx l b x c) ((ctxOf l).diaIn x) (packXS σ Δ l b x c) := by
  have hxp := (reach_ppath hx).1
  refine Subst.coh_of (ok_packXS l hb hx hc) ?_
  intro v T _ hv p
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
  · have hup := (reach_ppath hu).1
    have hnot : ¬ (((VarSymb.step u .box).ext p).rt = x.rt ∧
        (x.path ++ [Step.dia]) <+: ((VarSymb.step u .box).ext p).path) := by
      rintro ⟨_, k, hk⟩
      rw [VarSymb.ext_path] at hk
      change x.path ++ [Step.dia] ++ k = u.path ++ [Step.box] ++ p at hk
      simp only [List.append_assoc, List.singleton_append] at hk
      exact absurd (ppath_level hxp hup rfl rfl hk).2.1 (by simp)
    change ((packBase l b u.rt).ext (encPath u.path ++ itemTail)).ext p = packXIdx l b x c _
    rw [packXIdx, if_neg hnot, packIdx, itemPath_item hup p, VarSymb.ext_rt,
      VarSymb.ext_append _ (encPath u.path ++ itemTail) p]
    rfl
  · change (if x = x then SubE.ren c else .hide).idxAlong p = _
    rw [if_pos rfl]
    have hpre : ((VarSymb.step x .dia).ext p).rt = x.rt ∧
        (x.path ++ [Step.dia]) <+: ((VarSymb.step x .dia).ext p).path :=
      ⟨VarSymb.ext_rt _ _, ⟨p, by rw [VarSymb.ext_path]; rfl⟩⟩
    change c.ext p = packXIdx l b x c _
    rw [packXIdx, if_pos hpre, VarSymb.ext_path]
    change _ = c.ext ((x.path ++ [Step.dia] ++ p).drop (x.path.length + 1))
    have hl : x.path.length + 1 = (x.path ++ [Step.dia]).length := by simp
    rw [hl, List.drop_left]

section Pack2X

variable (l : List VarType) (x : VarSymb) (X U : VarType)

/-- The hole's context for a body packed along `x`: the roots' tuple with `x`'s content, paired
    with the body's slot. -/
abbrev pack2XCtx : Ctx := Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd (bcT l) X) U)

omit [ModalSys.NoFour] in
theorem pack2XCtx_ff :
    (pack2XCtx l X U).ref (.step (.step (.root (.bnd 0)) .fst) .fst) = some (bcT l) := by
  simp only [Ctx.ref, Step.isProj, if_true]
  rfl

omit [ModalSys.NoFour] in
theorem pack2XCtx_fs :
    (pack2XCtx l X U).ref (.step (.step (.root (.bnd 0)) .fst) .snd) = some X := by
  simp only [Ctx.ref, Step.isProj, if_true]
  rfl

omit [ModalSys.NoFour] in
theorem pack2XCtx_snd : (pack2XCtx l X U).ref (.step (.root (.bnd 0)) .snd) = some U := by
  simp only [Ctx.ref, Step.isProj, if_true]
  rfl

/-- ⭐Packing a body over `l`'s view along `x` and a slot `e : U`. -/
def pack2XS : Subst σ (pack2XCtx l X U) :=
  (packXS σ _ l (.step (.step (.root (.bnd 0)) .fst) .fst) x
    (.step (.step (.root (.bnd 0)) .fst) .snd)).set (.bnd 0) (.ren (.step (.root (.bnd 0)) .snd))

/-- Where `pack2XS` sends annotation indices. -/
noncomputable def pack2XIdx : VarSymb → VarSymb :=
  Subst.setIdx (packXIdx l (.step (.step (.root (.bnd 0)) .fst) .fst) x
    (.step (.step (.root (.bnd 0)) .fst) .snd)) (.bnd 0)
    (.ren (.step (.root (.bnd 0)) .snd) : SubE σ (pack2XCtx l X U))

variable {l x X}

theorem ok_pack2XS (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Subst.Ok (((ctxOf l).diaIn x).insert (.bnd 0) U) (pack2XS (σ := σ) l x X U) :=
  Subst.ok_set (ok_packXS l (pack2XCtx_ff l X U) hx (pack2XCtx_fs l X U)) (pack2XCtx_snd l X U)

theorem coh_pack2XS (hx : (ctxOf l).ref x = some (.VTypeDia X)) :
    Subst.Coh (pack2XIdx (σ := σ) l x X U) (((ctxOf l).diaIn x).insert (.bnd 0) U)
      (pack2XS (σ := σ) l x X U) :=
  Subst.coh_set (ok_packXS l (pack2XCtx_ff l X U) hx (pack2XCtx_fs l X U))
    (coh_packXS l (pack2XCtx_ff l X U) hx (pack2XCtx_fs l X U))
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).rootFresh (le_refl 0)) (pack2XCtx_snd l X U)

/-- ⭐A body over `l`'s view along `x` with a slot, packed into a hole formula over the roots'
    tuple, `x`'s content and the slot. -/
noncomputable def pack2X (hx : (ctxOf l).ref x = some (.VTypeDia X))
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) U) 1) : WFF σ (pack2XCtx l X U) 1 :=
  WFF.subst (pack2XIdx (σ := σ) l x X U) (pack2XS l x X U) (ok_pack2XS U hx) (coh_pack2XS U hx)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).insert U) (Ctx.slotsFrom_empty.insert _) Φ

end Pack2X

/-- ⭐A body packed along `x`, read at the roots' images, `cx` and a term `B`: the body sent along
    the witness arrow, its slot set to `B`. -/
theorem holeRead_tupImgT_pack2X {l : List VarType} {x : VarSymb} {X U : VarType} {Δ : Ctx}
    [Δ.NoSlots] {img : ℕ → ℕ} (himg : ImgOk l Δ img) (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) {bb : Ann U} (B : Term σ Δ U bb)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) U) 1) :
    WFF.holeRead (Term.pair (Term.pair (tupImgT l img himg).2 (Term.eta (.root (.free cx)) X hcx))
        B) (pack2X U hx Φ) =
      WFF.subst (Subst.setIdx (arrowXIdx img x cx) (.bnd 0) (.tm B))
        ((arrowXS σ Δ img x cx).set (.bnd 0) (.tm B)) (Subst.ok_set (ok_arrowXS himg hx hcx) rfl)
        (Subst.coh_set (ok_arrowXS himg hx hcx) (coh_arrowXS himg hx hcx)
          ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).insert U) Ctx.NoSlots.slots Φ := by
  have hs : (Δ.insert (.bnd 0) (.VTypeProd (.VTypeProd (bcT l) X) U)).SlotsFrom 1 :=
    (Ctx.NoSlots.slots (Γ := Δ)).insert _
  unfold WFF.holeRead WFF.instantiate WFF.substRoot pack2X
  rw [WFF.subst_mono ((Ctx.empty_le _).insert (.bnd 0) _) _ _ _ (Ctx.slotsFrom_empty.insert _) hs]
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
      (.tm (Term.pair (Term.pair (tupImgT l img himg).2 (Term.eta (.root (.free cx)) X hcx))
        B))).at (.root (.bnd 0)) =
        .tm (Term.pair (Term.pair (tupImgT l img himg).2 (Term.eta (.root (.free cx)) X hcx))
          B) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    dsimp only [Subst.comp, pack2XS]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .refl _
  · have hv' : ((ctxOf l).diaIn x) v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    rcases diaIn_item hv' with ⟨u, rfl, hu⟩ | ⟨rfl, hxT⟩
    · obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
      dsimp only [Subst.comp, pack2XS]
      rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
      dsimp only [packXS, SubE.comp]
      have hz : Δ.ref (.root (imgRoot img u.rt)) = some (rootTy l r).bc := by
        rw [hr]; exact himg r hlt
      have hT := ref_item hu hR hz
      change SubE.Sim T (.ren (itemAt (imgRoot img u.rt) u)) _
      rw [hr] at hz hT ⊢
      change SubE.Sim T (.ren ((VarSymb.root (.free (img r))).ext (encPath u.path ++ itemTail)))
        (Subst.at _ ((((VarSymb.step (.root (.bnd 0)) .fst).step .fst).ext (tupPath l r)).ext
          (encPath u.path ++ itemTail)))
      have hb : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair (Term.pair
          (tupImgT l img himg).2 (Term.eta (.root (.free cx)) X hcx)) B))).at
          ((VarSymb.step (.root (.bnd 0)) .fst).step .fst) = .tm (tupImgT l img himg).2 := by
        rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
        rfl
      obtain ⟨T', hT', h1⟩ := at_tupPath_tupImgT _ l himg hb hlt
      refine sim_ren_at_ext _ _ ((PPath.encPath (reach_ppath hu).1).append PPath.itemTail) hT' hT
        ?_
      rw [h1]
      exact .ren_eta _ _
    · rw [hx] at hxT
      cases hxT
      dsimp only [Subst.comp, pack2XS]
      rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
      change SubE.Sim X (if x = x then SubE.ren (.root (.free cx)) else .hide)
        ((if x = x then SubE.ren (.step (.step (.root (.bnd 0)) .fst) .snd) else .hide).comp _ _ _)
      rw [if_pos rfl, if_pos rfl]
      dsimp only [SubE.comp]
      rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
      exact .ren_eta _ _

/-- ⭐A body packed along `x`, read at the roots' items, `x`'s content and its slot's η-expansion:
    the body, weakened. -/
theorem holeAt_tupT_pack2X {l : List VarType} {x : VarSymb} {X U : VarType} {Δ : Ctx}
    [Δ.NoSlots] (h : ((ctxOf l).diaIn x).Le Δ) (hx : (ctxOf l).ref x = some (.VTypeDia X))
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) U) 1) :
    WFF.holeAt ((Ctx.NoSlots.slots (Γ := Δ)).insert U)
      (Term.pair
        (Term.pair
          (Term.mono (((Ctx.le_boxIn_diaIn _ x).trans h).trans
            (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root U)) (tupT l).2)
          (Term.eta (x.step .dia) X
            ((h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root U)).ref
              (Ctx.ref_diaIn_of hx))))
        (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U)))
      (pack2X U hx Φ) = WFF.mono (h.insert (.bnd 0) U) Φ := by
  have hle := ((Ctx.le_boxIn_diaIn _ x).trans h).trans
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root U)
  unfold WFF.holeAt pack2X
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le (h.insert (.bnd 0) U))
    (Subst.coh_idS_le (h.insert (.bnd 0) U)) _ _ _ ?_ Φ).trans
    (WFF.subst_ren (h.insert (.bnd 0) U) _ _ _ _ _ (fun v _ _ => Subst.at_idS v) Φ)
  refine Subst.sim_of fun v T hlp hv => ?_
  have h0 : (Subst.single (σ := σ) (Δ := Δ.insert (.bnd 0) U) (.bnd 0)
      (.tm (Term.pair (Term.pair (Term.mono hle (tupT l).2)
          (Term.eta (x.step .dia) X ((h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root
            U)).ref (Ctx.ref_diaIn_of hx))))
        (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))))).at (.root (.bnd 0)) =
      .tm (Term.pair (Term.pair (Term.mono hle (tupT l).2)
          (Term.eta (x.step .dia) X ((h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root
            U)).ref (Ctx.ref_diaIn_of hx))))
        (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = U := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp, pack2XS]
    rw [Subst.set_root]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .ren_eta _ _
  · have hv' : ((ctxOf l).diaIn x) v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    rcases diaIn_item hv' with ⟨u, rfl, hu⟩ | ⟨rfl, hxT⟩
    · obtain ⟨r, hr, hlt, _⟩ := ref_rt hu
      dsimp only [Subst.comp, pack2XS]
      rw [Subst.set_ne _ _ hvr]
      dsimp only [packXS, SubE.comp]
      rw [hr]
      change SubE.Sim T _ (Subst.at _ ((((VarSymb.step (.root (.bnd 0)) .fst).step .fst).ext
        (tupPath l r)).ext (encPath u.path ++ itemTail)))
      have hb : (Subst.single (σ := σ) (Δ := Δ.insert (.bnd 0) U) (.bnd 0)
          (.tm (Term.pair (Term.pair (Term.mono hle (tupT l).2)
              (Term.eta (x.step .dia) X ((h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root
                U)).ref (Ctx.ref_diaIn_of hx))))
            (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))))).at
            ((VarSymb.step (.root (.bnd 0)) .fst).step .fst) = .tm (Term.mono hle (tupT l).2) := by
        rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
        rfl
      obtain ⟨R, hR, h1⟩ := at_tupPath_tupT _ l hle hb hlt
      have h2 := at_enc_tupB_mono hle _ ModalSys.T rfl hR h1 hu hr
      rw [at_item_of_tupB_base_mono hle _ _ hu ModalSys.T rfl h2, Term.mono_eta]
      exact .ren_eta _ _
    · rw [hx] at hxT
      cases hxT
      dsimp only [Subst.comp, pack2XS]
      rw [Subst.set_ne _ _ hvr]
      change SubE.Sim X _
        ((if x = x then SubE.ren (.step (.step (.root (.bnd 0)) .fst) .snd) else .hide).comp _ _ _)
      rw [if_pos rfl]
      dsimp only [SubE.comp]
      rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
      exact .ren_eta _ _

/-! ## Hole terms on pairs -/

omit [ModalSys.NoFour] in
/-- Filling a hole term's hole with a hole term. -/
theorem Term.holeAt_holeAt_sig {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    {C : VarType} {c : Ann C} (u : Term σ (Ctx.empty.insert (.bnd 0) B) C c) :
    (⟨_, Term.holeAt t (Term.holeAt s u)⟩ : Σ e, Term σ Γ C e) =
      ⟨_, Term.holeAt (Term.holeAt t s) u⟩ :=
  Term.subst_holeAt_sig (Subst.single (.bnd 0) (.tm t)) _ _ s u

omit [ModalSys.NoFour] in
/-- A pair's first component, read through the hole. -/
theorem Term.holeAt_pair_fst {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B}
    (p : Term σ Γ A a) (q : Term σ Γ B b) :
    (⟨_, Term.holeAt (Term.pair p q) (Term.eta (.step (.root (.bnd 0)) .fst) A
        (Ctx.ref_fst_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd A B))))⟩ :
        Σ e, Term σ Γ A e) = ⟨a, p⟩ :=
  Term.subst_eta_tm _ _ _ _ _ _ p (by
    rw [Subst.at_proj _ _ rfl]
    change SubE.proj (Subst.single (.bnd 0) _ (.root (.bnd 0))) .fst = _
    rw [show Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.pair p q)) (.root (.bnd 0)) =
      .tm (Term.pair p q) from if_pos rfl]
    rfl)

omit [ModalSys.NoFour] in
/-- A pair's second component, read through the hole. -/
theorem Term.holeAt_pair_snd {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B}
    (p : Term σ Γ A a) (q : Term σ Γ B b) :
    (⟨_, Term.holeAt (Term.pair p q) (Term.eta (.step (.root (.bnd 0)) .snd) B
        (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd A B))))⟩ :
        Σ e, Term σ Γ B e) = ⟨b, q⟩ :=
  Term.subst_eta_tm _ _ _ _ _ _ q (by
    rw [Subst.at_proj _ _ rfl]
    change SubE.proj (Subst.single (.bnd 0) _ (.root (.bnd 0))) .snd = _
    rw [show Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.pair p q)) (.root (.bnd 0)) =
      .tm (Term.pair p q) from if_pos rfl]
    rfl)

omit [ModalSys.NoFour] in
/-- The hole itself, read through the hole. -/
theorem Term.holeAt_eta_root {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a) :
    (⟨_, Term.holeAt t (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root Ctx.empty (.bnd 0) A))⟩ :
        Σ e, Term σ Γ A e) = ⟨a, t⟩ :=
  Term.subst_eta_tm _ _ _ _ _ _ t (by
    change Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm t) (.root (.bnd 0)) = _
    exact if_pos rfl)

/-- Two necessary objects, packed through the hole. -/
theorem Term.holeAt_pack {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B}
    (s : Term σ Γ.boxIn A a) (t : Term σ Γ.boxIn B b) :
    (⟨_, Term.holeAt (Term.pair (Term.boxtm s) (Term.boxtm t))
        (ShapeMap.pack (σ := σ) A B).obj.2⟩ :
        Σ e, Term σ Γ (.VTypeBox (.VTypeProd A B)) e) = ⟨_, Term.boxtm (Term.pair s t)⟩ := by
  have h0 : (Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (Term.pair (Term.boxtm s) (Term.boxtm t)))).at (.root (.bnd 0)) =
      .tm (Term.pair (Term.boxtm s) (Term.boxtm t)) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  exact sig_boxtm (sig_pair
    (Term.subst_eta_tm _ _ _ _ _ _ s
      (Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl)))
    (Term.subst_eta_tm _ _ _ _ _ _ t
      (Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl))))

omit [ModalSys.NoFour] in
/-- A hole term read at the slot's own η-expansion is the hole term weakened. -/
theorem Term.holeAt_eta_slot {V : Ctx} [V.NoSlots] {A : VarType} {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.holeAt (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root V (.bnd 0) A)) s⟩ :
        Σ c, Term σ (V.insert (.bnd 0) A) B c) =
      ⟨_, Term.mono ((Ctx.empty_le V).insert (.bnd 0) A) s⟩ := by
  unfold Term.holeAt
  have hle := (Ctx.empty_le V).insert (.bnd 0) A
  refine (Term.subst_congr _ (Subst.idS σ _) _ (Subst.ok_idS_le hle) _ (Subst.coh_idS_le hle)
    (Subst.sim_of fun v T _ hv => ?_) s).trans (Term.subst_idS_mono _ _ _ s)
  have hvr : v = .root (.bnd 0) := by
    by_contra hne
    simp [Ctx.insert, hne, Ctx.empty] at hv
  subst hvr
  obtain rfl : T = A := by simpa [Ctx.insert] using hv.symm
  change SubE.Sim _ (Subst.single _ _ (.root (.bnd 0))) (Subst.idS σ _ (.root (.bnd 0)))
  dsimp only [Subst.single, Subst.idS]
  rw [if_pos rfl]
  exact .eta_ren _ _

/-! ## Repacking the witness's shape after a companion -/

/-- ⭐The **witness shape's repacking**: `⟨⟨d, e⟩, b⟩ ↦ ⟨□⟨d, b⟩, e⟩` — a companion necessary
    object joins the necessary part, and the possible part stays. -/
def ShapeMap.repackW (C B X : VarType) :
    ShapeMap σ (.prod (.prod (.box C) (.dia X)) (.box B))
      (.prod (.box (.VTypeProd C B)) (.dia X)) :=
  .pair (.comp (.pair (.comp (.fst _ _) (.fst _ _)) (.snd _ _)) (.pack C B))
    (.comp (.fst _ _) (.snd _ _))

/-- The repacking on the object out there. -/
theorem ShapeMap.repackW_obj {Γ : Ctx} {C B X : VarType} {c : Ann C} {b : Ann B}
    {x : Ann (.VTypeDia X)} (s : Term σ Γ.boxIn C c) (e : Term σ Γ (.VTypeDia X) x)
    (t : Term σ Γ.boxIn B b) :
    (⟨_, Term.holeAt (Term.pair (Term.pair (Term.boxtm s) e) (Term.boxtm t))
        (ShapeMap.repackW (σ := σ) C B X).obj.2⟩ :
        Σ a, Term σ Γ (RShape.prod (.box (.VTypeProd C B)) (.dia X)).ty a) =
      ⟨_, Term.pair (Term.boxtm (Term.pair s t)) e⟩ := by
  refine sig_pair ?_ ?_
  · refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
    refine (Term.holeAt_congr_sig (sig_pair ((Term.holeAt_holeAt_sig _ _ _).trans
      ((Term.holeAt_congr_sig (Term.holeAt_pair_fst _ _) _).trans (Term.holeAt_pair_fst _ _)))
      (Term.holeAt_pair_snd _ _)) _).trans ?_
    exact Term.holeAt_pack s t
  · exact (Term.holeAt_holeAt_sig _ _ _).trans
      ((Term.holeAt_congr_sig (Term.holeAt_pair_fst _ _) _).trans (Term.holeAt_pair_snd _ _))

omit [ModalSys.NoFour] in
/-- The repacking on the value it comes back as. -/
theorem ShapeMap.repackW_val {Γ : Ctx} {C B X : VarType} {c : Ann C} {b : Ann B} {x : Ann X}
    (s : Term σ Γ C c) (e : Term σ Γ X x) (t : Term σ Γ B b) :
    (⟨_, Term.holeAt (Term.pair (Term.pair s e) t) (ShapeMap.repackW (σ := σ) C B X).val.2⟩ :
        Σ a, Term σ Γ (RShape.prod (.box (.VTypeProd C B)) (.dia X)).flat a) =
      ⟨_, Term.pair (Term.pair s t) e⟩ := by
  refine sig_pair ?_ ?_
  · refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
    refine (Term.holeAt_congr_sig (sig_pair ((Term.holeAt_holeAt_sig _ _ _).trans
      ((Term.holeAt_congr_sig (Term.holeAt_pair_fst _ _) _).trans (Term.holeAt_pair_fst _ _)))
      (Term.holeAt_pair_snd _ _)) _).trans ?_
    exact Term.holeAt_eta_root _
  · exact (Term.holeAt_holeAt_sig _ _ _).trans
      ((Term.holeAt_congr_sig (Term.holeAt_pair_fst _ _) _).trans (Term.holeAt_pair_snd _ _))

/-! ## A body over a companion step -/

section PairW

variable {V : Ctx} [V.NoSlots]

omit [ModalSys] [ModalSys.NoFour] in
/-- The view with the object's slot and a companion's. -/
theorem pairS_le (T : VarType) (B : VarType) :
    V.Le ((V.insert (.bnd 0) T).insert (.bnd 1) (.VTypeBox B)) :=
  (body_le _).trans (Ctx.le_insert (((Ctx.NoSlots.slots (Γ := V)).insert _).root) _)

omit [ModalSys.NoFour] in
/-- The object and its companion, paired: `⟨d, b⟩`. -/
def slotPair (S : RShape) (B : VarType) :
    Σ a, Term σ ((V.insert (.bnd 0) S.ty).insert (.bnd 1) (.VTypeBox B))
      (RShape.prod S (.box B)).ty a :=
  ⟨_, Term.pair
    (Term.eta (.root (.bnd 0)) S.ty
      ((Ctx.le_insert (((Ctx.NoSlots.slots (Γ := V)).insert _).root) _).ref
        (Ctx.ref_insert_root V (.bnd 0) S.ty)))
    (Term.eta (.root (.bnd 1)) (.VTypeBox B) (Ctx.ref_insert_root _ (.bnd 1) _))⟩

omit [ModalSys.NoFour] in
/-- ⭐A body over the shape `T`, as a body over an object of shape `S` and a companion `b : □B`,
    through a map `F` from `S × □B` to `T`: the body read at `F⟨d, b⟩`.  What `ret_extS` then
    `ret_map F` turn back into the body. -/
def WFF.pairUpW {S T : RShape} {B : VarType} (F : ShapeMap σ (.prod S (.box B)) T)
    (Φ : WFF σ (V.insert (.bnd 0) T.ty) 1) :
    WFF σ ((V.insert (.bnd 0) S.ty).insert (.bnd 1) (.VTypeBox B)) 2 :=
  WFF.subst (Subst.setIdx id (.bnd 0) (.tm (Term.holeAt (slotPair S B).2 F.obj.2)))
    ((Subst.idS σ _).set (.bnd 0) (.tm (Term.holeAt (slotPair S B).2 F.obj.2)))
    (Subst.ok_set (Subst.ok_idS_le (pairS_le S.ty B)) rfl)
    (Subst.coh_set (Subst.ok_idS_le (pairS_le S.ty B)) (Subst.coh_idS_le (pairS_le S.ty B))
      ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := V)).insert _) (((Ctx.NoSlots.slots (Γ := V)).insert _).insert _) Φ

omit [ModalSys.NoFour] in
/-- ⭐Splitting the companion step's pair undoes `pairUpW` up to `F`: the split body is the body
    with `F`'s object in its slot — `ret_map F`'s premise. -/
theorem WFF.bodySplit_mono_pairUpW {V' : Ctx} [V'.NoSlots] (h : V.Le V') {S T : RShape}
    {B : VarType} (F : ShapeMap σ (.prod S (.box B)) T) (Φ : WFF σ (V.insert (.bnd 0) T.ty) 1) :
    WFF.bodySplit
      (Term.eta (.step (.root (.bnd 0)) .fst) S.ty
        (Ctx.ref_fst_of (Ctx.ref_insert_root V' (.bnd 0) (RShape.prod S (.box B)).ty)))
      (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox B)
        (Ctx.ref_snd_of (Ctx.ref_insert_root V' (.bnd 0) (RShape.prod S (.box B)).ty)))
      (WFF.mono ((h.insert (.bnd 0) _).insert (.bnd 1) _) (WFF.pairUpW F Φ)) =
      WFF.bodyRepl (Term.mono ((Ctx.empty_le V').insert (.bnd 0) _) F.obj.2)
        (WFF.mono (h.insert (.bnd 0) _) Φ) := by
  unfold WFF.bodySplit WFF.pairUpW WFF.bodyRepl
  rw [WFF.mono_subst _ _ _ _ _ _ (((Ctx.NoSlots.slots (Γ := V')).insert _).insert _),
    WFF.subst_mono]
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = T.ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else V _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp, Subst.mono]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.mono, SubE.comp]
    rw [Term.subst_mono]
    refine SubE.sim_tm_sigma (Eq.symm ((Term.subst_holeAt_sig _ _ _ _ _).trans ?_))
    refine (Term.holeAt_congr_sig (sig_pair
      (Term.subst_eta_tm _ _ _ _ _ _ _ (by
        change (Subst.set _ _ _) (.root (.bnd 0)) = _
        rw [Subst.set_ne _ _ (fun h => by cases h), Subst.set_root]))
      (Term.subst_eta_tm _ _ _ _ _ _ _ (by
        change (Subst.set _ _ _) (.root (.bnd 1)) = _
        rw [Subst.set_root]))) _).trans ?_
    exact Term.holeAt_eta_slot _
  · have hv' : V v = some U := by
      change (if v = VarSymb.root (.bnd 0) then _ else V v) = _ at hv
      rwa [if_neg hvr] at hv
    have hv1 : v ≠ .root (.bnd 1) := fun h => by
      subst h
      rw [((Ctx.NoSlots.slots (Γ := V)).rootFresh (Nat.zero_le 1)).root] at hv'
      cases hv'
    dsimp only [Subst.comp, Subst.mono]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    dsimp only [Subst.idS, SubE.mono, SubE.comp]
    rw [Subst.at_nonproj _ hlp, Subst.set_ne _ _ hv1, Subst.set_ne _ _ hvr]
    exact .refl _

end PairW

/-! ## The parent's `∃`-introduction for a new root -/

section NewRootW

variable {lv cls clt : List VarType} {A : VarType} {x : VarSymb} {X : VarType}

/-- The middle term: the older roots' entry and the new root's slot, repacked. -/
def midTermW (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (A : VarType) :
    Σ a, Term σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox A.bc))
      (RShape.prod (.box (bcT (A :: cls))) (.dia X)).ty a :=
  ⟨_, Term.holeAt
    (Term.pair
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)
        (Term.pair (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
          (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx))))
      (Term.eta (.root (.bnd 0)) (.VTypeBox A.bc) (Ctx.ref_insert_root _ (.bnd 0) _)))
    (ShapeMap.repackW (σ := σ) (bcT cls) A.bc X).obj.2⟩

/-- The middle substitution: the reverse arrow, weakened past the `∃`'s slot, with the body's slot
    set to `midTermW`. -/
abbrev midSW (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (A : VarType)
    (imgt : ℕ → ℕ) : Subst σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox A.bc)) :=
  ((arrowS σ (ctxOf lv) imgt).mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)).set
    (.bnd 0) (.tm (midTermW hs hx A).2)

theorem ok_midSW (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) :
    Subst.Ok (bodyCtxW (A :: cls) clt X) (midSW (σ := σ) hs hx A imgt) :=
  Subst.ok_set (Subst.ok_mono (ok_arrowS himgt) _) rfl

theorem coh_midSW (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) :
    Subst.Coh (Subst.setIdx (arrowIdx imgt) (.bnd 0) (.tm (midTermW (σ := σ) hs hx A).2))
      (bodyCtxW (A :: cls) clt X) (midSW (σ := σ) hs hx A imgt) :=
  Subst.coh_set (Subst.ok_mono (ok_arrowS himgt) _) (Subst.coh_mono (coh_arrowS himgt) _)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl

/-- A non-slot variable of a witness body's context is an item of the reverse arrow's view. -/
theorem bodyW_item {cl clt : List VarType} {X : VarType} {v : VarSymb} {U : VarType}
    (hv : bodyCtxW cl clt X v = some U) (hvr : v ≠ .root (.bnd 0)) :
    ∃ u, v = .step u .box ∧ (ctxOf clt).ref u = some (.VTypeBox U) := by
  change (if v = VarSymb.root (.bnd 0) then _ else (ctxOf clt).boxIn v) = _ at hv
  rw [if_neg hvr] at hv
  exact boxIn_item hv

/-- ⭐**A new root's witness body is an `∃`-introduction of the older roots' one.**  Read at the
    parent, `∃b. pairUpW repackW Φ` over the older roots, at the new root's necessary object, is
    `Φ` over all of them: the repacking sends `⟨⟨□ā, x⟩, □a⟩` to `⟨□⟨ā, a⟩, x⟩`. -/
theorem liftBodyW_ex_pairUpW_mem {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs' : (A :: cls) <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtxW (A :: cls) clt X) 1)
    (h : liftBodyW hs' himgt (ref_old_of_ref hx) Φ ∈ M) :
    liftBodyW ((List.suffix_cons A cls).trans hs') himgt hx
      (WFF.ex (.VTypeBox A.bc) (WFF.pairUpW (ShapeMap.repackW (bcT cls) A.bc X) Φ)) ∈ M := by
  have hs : cls <:+ lv := (List.suffix_cons A cls).trans hs'
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact h, ⟨?_⟩⟩
  refine Proof.ex_intro _ (newItem hs') (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  refine Eq.symm ?_
  unfold WFF.instantiate WFF.substRoot WFF.pairUpW
  have hfr : (ctxOf lv) (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := ctxOf lv)).root
  rw [WFF.subst_comp _ _ (midSW hs hx A imgt) _ _ _ _ (ok_midSW hs hx himgt)
    (coh_midSW hs hx himgt) _ _ _ ?simA]
  case simA =>
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = (RShape.prod (.box (bcT (A :: cls))) (.dia X)).ty := by
        change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
        rw [if_pos rfl] at hv
        exact (Option.some.inj hv).symm
      dsimp only [Subst.comp]
      rw [show midSW (σ := σ) hs hx A imgt (.root (.bnd 0)) = .tm (midTermW hs hx A).2 from
        Subst.set_root _ _ _, Subst.set_root]
      dsimp only [SubE.comp]
      have h0 : (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).under (0 + 1) 0
          (.VTypeBox A.bc) hfr).at (.root (.bnd 0)) =
          .tm (Term.mono (Ctx.le_insert hfr _)
            (Term.pair (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
              (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx)))) := by
        rw [Subst.at_under_ne _ _ _ (fun h => by cases h)]
        change SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))) = _
        rw [Subst.set_root]
        rfl
      refine SubE.sim_tm_sigma (Eq.symm ((Term.subst_holeAt_sig _ _ _ _ _).trans ?_))
      exact Term.holeAt_congr_sig (sig_pair
        (Term.subst_eta_tm _ _ _ _ _ _ _ h0)
        (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_insert_root _ (.bnd 0) _)
          (Subst.under_at_slot _ (0 + 1) 0 _ hfr))) _
    · obtain ⟨u, rfl, hu⟩ := bodyW_item hv hvr
      dsimp only [Subst.comp]
      rw [show midSW (σ := σ) hs hx A imgt (.step u .box) =
        SubE.mono _ (arrowS σ (ctxOf lv) imgt (.step u .box)) from Subst.set_ne _ _ hvr,
        Subst.set_ne _ _ hvr]
      dsimp only [Subst.idS, SubE.comp]
      rw [Subst.at_nonproj _ hlp]
      dsimp only [Subst.under]
      rw [if_neg (fun h => by cases h), Subst.set_ne _ _ hvr]
      exact .refl _
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = (RShape.prod (.box (bcT (A :: cls))) (.dia X)).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [show midSW (σ := σ) hs hx A imgt (.root (.bnd 0)) = .tm (midTermW hs hx A).2 from
      Subst.set_root _ _ _, Subst.set_root]
    dsimp only [SubE.comp, liftEntryW]
    have hsg : (Subst.single (σ := σ) (.bnd 0) (.tm (newItem hs'))).at (.root (.bnd 0)) =
        .tm (newItem hs') := by
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
    refine SubE.sim_tm_sigma (Eq.symm ((Term.subst_holeAt_sig _ _ _ _ _).trans ?_))
    refine (Term.holeAt_congr_sig (sig_pair (Term.subst_single_mono_sig _ _)
      (Term.subst_eta_tm _ _ _ _ _ _ _ hsg)) _).trans ?_
    refine (ShapeMap.repackW_obj _ _ _).trans ?_
    refine congrArg (Sigma.mk _) ?_
    change Term.pair (Term.boxtm (Term.pair _ _)) _ =
      Term.pair (Term.boxtm (Term.pair (Term.mono _ (Term.mono _ _)) (Term.mono _ _))) _
    rw [Term.mono_mono]
  · obtain ⟨u, rfl, hu⟩ := bodyW_item hv hvr
    obtain ⟨r, hr, _, _⟩ := ref_rt hu
    dsimp only [Subst.comp]
    rw [show midSW (σ := σ) hs hx A imgt (.step u .box) =
      SubE.mono _ (arrowS σ (ctxOf lv) imgt (.step u .box)) from Subst.set_ne _ _ hvr,
      Subst.set_ne _ _ hvr]
    change SubE.Sim U (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
    rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
    exact .refl _

end NewRootW

/-! ## Realising the parent's next root along a witness arrow -/

section StepW

variable (hS : ModalSys.BStrong = true) {ts tt : NodeSt σ} {cl clt : List VarType}
  {img imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}

/-- The returning possibility a witness body over the roots with the next one becomes in the grown
    child: valued at the images, the fresh variable, and `cx`. -/
def retAtomW (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (Φ : WFF σ (bodyCtxW (nextTy ts.l cl :: cl) clt X) 1) :
    WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0 :=
  WFF.retS hS (.prod (.box (bcT (nextTy ts.l cl :: cl))) (.dia X))
    (Term.pair
      (tupImgT (nextTy ts.l cl :: cl) (extImg img cl.length tt.l.length) (imgOk_ext himg)).2
      (Term.eta (.root (.free cx)) X ((ctxOf_le_append [(nextTy ts.l cl).bc] tt.l).ref hcx)))
    (WFF.mono ((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).boxIn.insert (.bnd 0) _) Φ)

/-- What the child gains when the parent's next root is committed along a witness arrow. -/
def retSetW (hs' : (nextTy ts.l cl :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X) :
    Set (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0) :=
  {φ | ∃ Φ, liftBodyW hs' himgt (ref_old_of_ref hx) Φ ∈ ts.M ∧ φ = retAtomW hS himg ht hcx Φ}

/-- Finitely many of the gained atoms reduce to one, at the conjunction of their bodies. -/
theorem ret_listW (hs' : (nextTy ts.l cl :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X) (hv : Theory.IsMCS ts.M)
    (S : Set (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0)) :
    ∀ L : List (WFF σ (ctxOf ((nextTy ts.l cl).bc :: tt.l)) 0),
      (∀ δ ∈ L, δ ∈ S ∨ δ ∈ retSetW hS hs' himgt himg ht hx hcx) →
      ∃ Φ, liftBodyW hs' himgt (ref_old_of_ref hx) Φ ∈ ts.M ∧
        ∀ δ ∈ L, Theory.Derives (S ∪ {retAtomW hS himg ht hcx Φ}) δ
  | [], _ => ⟨.top, hv.top_mem, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Φ₀, hΦ₀, hL⟩ := ret_listW hs' himgt himg ht hx hcx hv S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := ctxOf_fresh (l := (nextTy ts.l cl).bc :: tt.l) le_rfl
      rcases h δ List.mem_cons_self with hS' | ⟨Φ₁, hΦ₁, rfl⟩
      · refine ⟨Φ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS')
        · exact hL d hd
      · have hand : ∀ Φ', Proof σ _ [retAtomW hS himg ht hcx (Φ₀.and Φ₁)]
              (retAtomW hS himg ht hcx Φ') →
            Theory.Derives (S ∪ {retAtomW hS himg ht hcx (Φ₀.and Φ₁)})
              (retAtomW hS himg ht hcx Φ') :=
          fun Φ' p => ⟨[_], fun x hx => by
            rw [List.mem_singleton.mp hx]; exact Or.inr rfl, ⟨p⟩⟩
        have h₀ := hand Φ₀ (Proof.ret_monoS hS .nec _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.box_all_and_left _ _ hu))
        have h₁ := hand Φ₁ (Proof.ret_monoS hS .nec _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.box_all_and_right _ _ hu))
        refine ⟨Φ₀.and Φ₁, hv.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.and_intro (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΦ₀
          · rw [List.mem_singleton.mp hx]; exact hΦ₁
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · refine Derives.trans (fun x hx => ?_) (hL d hd)
          rcases hx with hx | hx
          · exact Theory.Derives.of_mem (Or.inl hx)
          · rw [Set.mem_singleton_iff.mp hx]; exact h₀

/-- ⭐**The gained atoms are consistent with the child**: finitely many reduce to one body `Φ`
    (`ret_listW`); the parent has `∃b. pairUpW repackW Φ` at the older roots and `x`
    (`liftBodyW_ex_pairUpW_mem`), so by the invariant the child has
    `◇[⟨d, e⟩ ↦ ⟨ā', cx⟩] ∃b. pairUpW repackW Φ`; `ret_extS` names `b` by the fresh variable,
    and `ret_map` along the repacking turns the result into the atom
    (`bodySplit_mono_pairUpW`, `repackW_val`). -/
theorem retSetW_consistent (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Φ : WFF σ (bodyCtxW cl clt X) 1,
      liftBodyW ((List.suffix_cons _ _).trans hs') himgt hx Φ ∈ ts.M →
        WFF.retS hS (.prod (.box (bcT cl)) (.dia X))
          (Term.pair (tupImgT cl img himg).2 (Term.eta (.root (.free cx)) X hcx))
          (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ tt.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) '' tt.M ∪
      retSetW hS hs' himgt himg ht hx hcx) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨Φ, hΦ, hder⟩ := ret_listW hS hs' himgt himg ht hx hcx hv _ L hL
  have h₁ := hinv _ (liftBodyW_ex_pairUpW_mem hv hs' himgt hx Φ hΦ)
  have hu := ctxOf_fresh (l := tt.l) le_rfl
  have hle := ctxOf_le_of_suffix ht
  obtain ⟨Δ, hΔ, hq⟩ : Theory.Derives (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) ''
      tt.M ∪ {retAtomW hS himg ht hcx Φ}) .bot :=
    Derives.trans (fun y hy => hder y hy) ⟨L, fun y hy => hy, p⟩
  obtain ⟨Δ₀, h₀, h₁'⟩ := exists_hyps_cons_map (P := fun y => y ∈ tt.M)
    (fun y => WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) y)
    (retAtomW hS himg ht hcx Φ) Δ
    (fun δ hδ => by
      rcases hΔ δ hδ with ⟨y, hy, rfl⟩ | h
      · exact Or.inr ⟨y, hy, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨q'⟩ := Provable.mono h₁' hq
  obtain ⟨Δ₁, hΔ₁, ⟨pex⟩⟩ := Theory.Derives.of_mem (S := tt.M) h₁
  refine hw.1 ⟨Δ₁ ++ Δ₀, fun y hy => (List.mem_append.mp hy).elim (hΔ₁ y) (h₀ y), ⟨?_⟩⟩
  refine Proof.ret_extS hS .nec (S := .prod (.box (bcT cl)) (.dia X)) _
    (WFF.mono ((hle.boxIn.insert (.bnd 0) _).insert (.bnd 1) _)
      (WFF.pairUpW (ShapeMap.repackW (bcT cl) (nextTy ts.l cl).bc X) Φ))
    tt.l.length hu (φ := .bot) (Proof.ofSubset (fun y hy => List.mem_append_left _ hy) pex) ?_
  refine Proof.imp_elim (Proof.ofSubset (fun y hy => ?_) (Proof.imp_intro q')) ?_
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_right _ hz))
  refine Proof.conv ?_ (Proof.ret_map hS .nec (ShapeMap.repackW (bcT cl) (nextTy ts.l cl).bc X) _
    (WFF.mono ((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).boxIn.insert (.bnd 0) _) Φ)
    (Proof.conv (OutLeg.retS_congr' hS _ _ rfl ?_) (Proof.lookup List.mem_cons_self)))
  · refine WFF.retS_congr hS _ ?_ rfl
    rw [Term.holeRead_eq_holeAt]
    refine (ShapeMap.repackW_val _ _ _).trans
      (sig_pair (tupImgT_ext himg (imgOk_ext himg)).symm ?_)
    exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)
  · rw [WFF.bodySplit_mono_pairUpW hle.boxIn, WFF.mono_bodyRepl (Ctx.le_insert hu.root _).boxIn,
      Term.mono_mono, WFF.mono_mono]

/-- The child grown by the image of the parent's next root, along a witness arrow. -/
noncomputable def retStepW (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X) : NodeSt σ :=
  ⟨(nextTy ts.l cl).bc :: tt.l, complete (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) ''
    tt.M ∪ retSetW hS hs' himgt himg ht hx hcx)⟩

/-- ⭐**One realisation step along a witness arrow**: when the forward invariant holds, the grown
    child is maximal consistent, extends the old one, and the invariant holds for one more root.
    No `◇_x`-merging is needed: the witness rides along as the possible part. -/
theorem retStepW_ok (hs' : (nextTy ts.l cl :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvW hS ts tt cl img clt imgt x X cx) :
    Theory.IsMCS (retStepW hS hs' himgt himg ht hx hcx).M ∧
      Grows tt (retStepW hS hs' himgt himg ht hx hcx) ∧
      RetInvW hS ts (retStepW hS hs' himgt himg ht hx hcx) (nextTy ts.l cl :: cl)
        (extImg img cl.length tt.l.length) clt imgt x X cx := by
  obtain ⟨_, _, _, _, _, _, h⟩ := hinv
  have hcons := retSetW_consistent hS hs' himgt himg ht hx hcx hv hw h
  obtain ⟨hsub, hmcs⟩ := complete_spec hcons
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩,
    hs', imgOk_ext himg, ht.trans (List.suffix_cons _ _), himgt, ref_old_of_ref hx,
    (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l).ref hcx, fun Φ hΦ => ?_⟩
  exact hsub (Or.inr ⟨Φ, hΦ, rfl⟩)

end StepW

/-! ## Realising the child's next root along the way home along `x` -/

/-- `ret_ext`'s instance along a leg at a fresh `c`. -/
def retExtAtomO {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) (O : OutLeg Γ)
    {A B : VarType} {a : Ann A} (t : Term σ Γ A a)
    (Φ : WFF σ ((O.view.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2)
    (c : ℕ) (hc : Γ.RootFresh (.free c)) : WFF σ (Γ.insert (.free c) B) 0 :=
  (O.mono (Ctx.le_insert hc.root B)).ret hS
    (Term.pair (Term.weaken hc.root B t)
      (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B)))
    (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root B)).insert (.bnd 0) _) (WFF.bodySplit
      (Term.boxFst (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox (.VTypeProd A B))))
      (Term.boxSnd (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox (.VTypeProd A B))))
      Φ))

/-- `retExt_consistent` along any leg. -/
theorem retExtO_consistent {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.Consistent M) (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A B : VarType}
    {a : Ann A} (t : Term σ Γ A a)
    (Φ : WFF σ ((O.view.insert (.bnd 0) (.VTypeBox A)).insert (.bnd 1) (.VTypeBox B)) 2)
    (hex : Theory.Derives M (O.ret hS t (WFF.ex (.VTypeBox B) Φ))) {u : ℕ}
    (hu : Γ.RootFresh (.free u)) :
    Theory.Consistent (WFF.mono (Ctx.le_insert hu.root B) '' M ∪
      {retExtAtomO hS O t Φ u hu}) := by
  rintro ⟨Δ, hΔ, p⟩
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := fun x => x ∈ M)
    (fun x => WFF.mono (Ctx.le_insert hu.root B) x) (retExtAtomO hS O t Φ u hu) Δ
    (fun δ hδ => by
      rcases hΔ δ hδ with ⟨x, hx, rfl⟩ | h
      · exact Or.inr ⟨x, hx, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨q⟩ := Provable.mono h₁ p
  obtain ⟨Δ₁, hΔ₁, ⟨pex⟩⟩ := hex
  refine hM ⟨Δ₁ ++ Δ₀, fun x hx => (List.mem_append.mp hx).elim (hΔ₁ x) (h₀ x), ⟨?_⟩⟩
  refine Proof.ret_ext hS O t Φ u hu (φ := .bot)
    (Proof.ofSubset (fun x hx => List.mem_append_left _ hx) pex)
    (Proof.ofSubset (fun x hx => ?_) q)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_right _ hy))

section NewRootX

variable {lv cls clt : List VarType} {A : VarType} {x : VarSymb} {X : VarType} {cx : ℕ}

/-- The middle substitution along `x`: the witness arrow, weakened past the `∃`'s slot, with the
    body's slot set to `midTerm`. -/
abbrev midSX (hs : cls <:+ lv) (A : VarType) (imgt : ℕ → ℕ) (x : VarSymb) (cx : ℕ) :
    Subst σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox A.bc)) :=
  ((arrowXS σ (ctxOf lv) imgt x cx).mono
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)).set (.bnd 0) (.tm (midTerm hs A).2)

theorem ok_midSX (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) :
    Subst.Ok (bodyCtxX (A :: cls) clt x) (midSX (σ := σ) hs A imgt x cx) :=
  Subst.ok_set (Subst.ok_mono (ok_arrowXS himgt hx hcx) _) rfl

theorem coh_midSX (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) :
    Subst.Coh (Subst.setIdx (arrowXIdx imgt x cx) (.bnd 0) (.tm (midTerm (σ := σ) hs A).2))
      (bodyCtxX (A :: cls) clt x) (midSX (σ := σ) hs A imgt x cx) :=
  Subst.coh_set (Subst.ok_mono (ok_arrowXS himgt hx hcx) _)
    (Subst.coh_mono (coh_arrowXS himgt hx hcx) _)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).rootFresh (le_refl 0)) rfl

/-- ⭐**A new root's witness body along `x` is an `∃`-introduction of the older roots' one**, at
    the child: `liftBody_ex_pairUp_mem` with the witness arrow. -/
theorem liftBodyX_ex_pairUp_mem {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs' : (A :: cls) <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (Φ : WFF σ (bodyCtxX (A :: cls) clt x) 1)
    (h : liftBodyX hs' himgt hx hcx Φ ∈ M) :
    liftBodyX ((List.suffix_cons A cls).trans hs') himgt hx hcx
      (WFF.ex (.VTypeBox A.bc) (WFF.pairUp Φ)) ∈ M := by
  have hs : cls <:+ lv := (List.suffix_cons A cls).trans hs'
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact h, ⟨?_⟩⟩
  refine Proof.ex_intro _ (newItem hs') (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  refine Eq.symm ?_
  unfold WFF.instantiate WFF.substRoot WFF.pairUp liftBodyX
  have hfr : (ctxOf lv) (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := ctxOf lv)).root
  rw [WFF.subst_comp _ _ (midSX hs A imgt x cx) _ _ _ _ (ok_midSX hs himgt hx hcx)
    (coh_midSX hs himgt hx hcx) _ _ _ ?simA]
  case simA =>
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = .VTypeBox (bcT (A :: cls)) := by
        change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
        rw [if_pos rfl] at hv
        exact (Option.some.inj hv).symm
      dsimp only [Subst.comp]
      rw [show midSX (σ := σ) hs A imgt x cx (.root (.bnd 0)) = .tm (midTerm hs A).2 from
        Subst.set_root _ _ _, Subst.set_root]
      have h0 : (((arrowXS σ (ctxOf lv) imgt x cx).set (.bnd 0) (liftEntry hs)).under (0 + 1) 0
          (.VTypeBox A.bc) hfr).at (.root (.bnd 0)) =
          .tm (Term.boxtm (Term.mono ((Ctx.le_insert hfr _).boxIn)
            (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))) := by
        rw [Subst.at_under_ne _ _ _ (fun h => by cases h)]
        change SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))) = _
        rw [Subst.set_root]
        rfl
      dsimp only [SubE.comp]
      exact SubE.sim_tm_sigma (sig_boxtm (sig_pair
        (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h0))
        (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) _))
          (Subst.box_at_inner_ren _ (Subst.under_at_slot _ (0 + 1) 0 _ hfr))))).symm
    · dsimp only [Subst.comp]
      rw [show midSX (σ := σ) hs A imgt x cx v =
        SubE.mono _ (arrowXS σ (ctxOf lv) imgt x cx v) from Subst.set_ne _ _ hvr,
        Subst.set_ne _ _ hvr]
      dsimp only [Subst.idS, SubE.comp]
      rw [Subst.at_nonproj _ hlp]
      dsimp only [Subst.under]
      have hv1 : v ≠ .root (.bnd (0 + 1)) := by
        rcases bodyX_item hv hvr with ⟨u, rfl, _⟩ | ⟨rfl, _⟩ <;> exact fun h => by cases h
      rw [if_neg hv1, Subst.set_ne _ _ hvr]
      exact .refl _
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = .VTypeBox (bcT (A :: cls)) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [show midSX (σ := σ) hs A imgt x cx (.root (.bnd 0)) = .tm (midTerm hs A).2 from
      Subst.set_root _ _ _]
    dsimp only [SubE.comp]
    have hsg : (Subst.single (σ := σ) (.bnd 0) (.tm (newItem hs'))).at (.root (.bnd 0)) =
        .tm (newItem hs') := by
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
    have hsim : Subst.Sim (ctxOf cls).boxIn
        (Subst.single (σ := σ) (Δ := ctxOf lv) (.bnd 0) (.tm (newItem hs'))).box
        (Subst.idS σ (ctxOf lv).boxIn) := by
      refine Subst.sim_of fun v U _ hv => ?_
      obtain ⟨u, rfl, hu⟩ := boxIn_item hv
      obtain ⟨r, hr, _, _⟩ := ref_rt hu
      change SubE.Sim U ((Subst.single _ _).at u).unbox (.ren (.step u .box))
      rw [Subst.single_at_ne (by rw [hr]; exact fun h => by cases h)]
      change SubE.Sim U (.ren u.inner) _
      rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
      exact .refl _
    rw [Subst.set_root]
    refine SubE.sim_tm_sigma (sig_boxtm (sig_pair ?_
      (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ hsg)))).symm
    rw [Term.mono_mono, Term.mono_mono, Term.subst_mono]
    exact (Term.subst_congr _ _ _ (Subst.ok_idS_le (ctxOf_le_of_suffix hs).boxIn) _
      (Subst.coh_idS_le (ctxOf_le_of_suffix hs).boxIn) hsim _).trans
      (Term.subst_idS_mono (ctxOf_le_of_suffix hs).boxIn _ _ _)
  · dsimp only [Subst.comp]
    rw [show midSX (σ := σ) hs A imgt x cx v =
      SubE.mono _ (arrowXS σ (ctxOf lv) imgt x cx v) from Subst.set_ne _ _ hvr,
      Subst.set_ne _ _ hvr]
    rcases bodyX_item hv hvr with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
    · obtain ⟨r, hr, _, _⟩ := ref_rt hu
      change SubE.Sim U (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
      rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
      exact .refl _
    · rw [show arrowXS σ (ctxOf lv) imgt x cx (x.step Step.dia) = .ren (.root (.free cx)) from
        if_pos rfl]
      change SubE.Sim U (.ren (.root (.free cx))) ((Subst.single _ _).at (.root (.free cx)))
      rw [Subst.single_at_ne (fun h => by cases h)]
      exact .refl _

end NewRootX

omit [ModalSys.NoFour] in
/-- `□_x∀d.(Φ ∧ Ψ → Φ)`. -/
def Proof.boxx_all_and_left {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    (Φ Ψ : WFF σ ((Γ.diaIn x).insert (.bnd 0) A) 1) {u : ℕ} (hu : Γ.RootFresh (.free u)) :
    Proof σ Γ Δ (WFF.boxx x hx (WFF.all A (WFF.imp (WFF.and Φ Ψ) Φ))) := by
  have q : Proof σ (Γ.diaIn x) [] (WFF.all A (WFF.imp (WFF.and Φ Ψ) Φ)) := by
    have := Proof.all_intro (Δ := []) u A (hu.diaIn x)
      (φ := WFF.openFree u (hu.diaIn x) Ctx.NoSlots.slots (WFF.imp (WFF.and Φ Ψ) Φ))
      (Proof.imp_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self)))
    rwa [WFF.bindFree_openFree] at this
  exact Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.boxxK hx (Δ := []) q)

omit [ModalSys.NoFour] in
/-- `□_x∀d.(Φ ∧ Ψ → Ψ)`. -/
def Proof.boxx_all_and_right {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    (Φ Ψ : WFF σ ((Γ.diaIn x).insert (.bnd 0) A) 1) {u : ℕ} (hu : Γ.RootFresh (.free u)) :
    Proof σ Γ Δ (WFF.boxx x hx (WFF.all A (WFF.imp (WFF.and Φ Ψ) Ψ))) := by
  have q : Proof σ (Γ.diaIn x) [] (WFF.all A (WFF.imp (WFF.and Φ Ψ) Ψ)) := by
    have := Proof.all_intro (Δ := []) u A (hu.diaIn x)
      (φ := WFF.openFree u (hu.diaIn x) Ctx.NoSlots.slots (WFF.imp (WFF.and Φ Ψ) Ψ))
      (Proof.imp_intro (Proof.and_elim_r (Proof.lookup List.mem_cons_self)))
    rwa [WFF.bindFree_openFree] at this
  exact Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.boxxK hx (Δ := []) q)

section StepX

variable (hS : ModalSys.BStrong = true) {tk tp : NodeSt σ} {cls clt : List VarType}
  {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}

/-- The returning possibility along `x` a body over the child's roots with the next one becomes in
    the grown parent: valued at the images and the fresh variable. -/
def retAtomX (himgs : ImgOk cls (ctxOf tp.l) imgs) (ht : clt <:+ tp.l)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (Φ : WFF σ (bodyCtxX (nextTy tk.l cls :: cls) clt x) 1) :
    WFF σ (ctxOf ((nextTy tk.l cls).bc :: tp.l)) 0 :=
  (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).ref hx⟩ :
      OutLeg (ctxOf ((nextTy tk.l cls).bc :: tp.l))).ret hS
    (tupImgT (nextTy tk.l cls :: cls) (extImg imgs cls.length tp.l.length) (imgOk_ext himgs)).2
    (WFF.mono (((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).diaIn x).insert
      (.bnd 0) _) Φ)

/-- What the parent gains when the child's next root is committed along the way home. -/
def retSetX (hs' : (nextTy tk.l cls :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) : Set (WFF σ (ctxOf ((nextTy tk.l cls).bc :: tp.l)) 0) :=
  {φ | ∃ Φ, liftBodyX hs' himgt hx hcx Φ ∈ tk.M ∧ φ = retAtomX hS himgs ht hx Φ}

/-- Finitely many of the gained atoms reduce to one, at the conjunction of their bodies. -/
theorem ret_listX (hs' : (nextTy tk.l cls :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M)
    (S : Set (WFF σ (ctxOf ((nextTy tk.l cls).bc :: tp.l)) 0)) :
    ∀ L : List (WFF σ (ctxOf ((nextTy tk.l cls).bc :: tp.l)) 0),
      (∀ δ ∈ L, δ ∈ S ∨ δ ∈ retSetX hS hs' himgt hx hcx himgs ht) →
      ∃ Φ, liftBodyX hs' himgt hx hcx Φ ∈ tk.M ∧
        ∀ δ ∈ L, Theory.Derives (S ∪ {retAtomX hS himgs ht hx Φ}) δ
  | [], _ => ⟨.top, hk.top_mem, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Φ₀, hΦ₀, hL⟩ := ret_listX hs' himgt hx hcx himgs ht hk S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := ctxOf_fresh (l := (nextTy tk.l cls).bc :: tp.l) le_rfl
      rcases h δ List.mem_cons_self with hS' | ⟨Φ₁, hΦ₁, rfl⟩
      · refine ⟨Φ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS')
        · exact hL d hd
      · have hand : ∀ Φ', Proof σ _ [retAtomX hS himgs ht hx (Φ₀.and Φ₁)]
              (retAtomX hS himgs ht hx Φ') →
            Theory.Derives (S ∪ {retAtomX hS himgs ht hx (Φ₀.and Φ₁)})
              (retAtomX hS himgs ht hx Φ') :=
          fun Φ' p => ⟨[_], fun x hx => by
            rw [List.mem_singleton.mp hx]; exact Or.inr rfl, ⟨p⟩⟩
        have h₀ := hand Φ₀ (Proof.ret_mono hS (.pos x _) _ _ _
          (Proof.lookup List.mem_cons_self) (Proof.boxx_all_and_left _ _ _ hu))
        have h₁ := hand Φ₁ (Proof.ret_mono hS (.pos x _) _ _ _
          (Proof.lookup List.mem_cons_self) (Proof.boxx_all_and_right _ _ _ hu))
        refine ⟨Φ₀.and Φ₁, hk.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.and_intro (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΦ₀
          · rw [List.mem_singleton.mp hx]; exact hΦ₁
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · refine Derives.trans (fun x hx => ?_) (hL d hd)
          rcases hx with hx | hx
          · exact Theory.Derives.of_mem (Or.inl hx)
          · rw [Set.mem_singleton_iff.mp hx]; exact h₀

/-- ⭐**The gained atoms along `x` are consistent with the parent**: as `retSet_consistent`, with
    `ret_ext` along `x`. -/
theorem retSetX_consistent (hs' : (nextTy tk.l cls :: cls) <:+ tk.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M)
    (hinv : ∀ Φ : WFF σ (bodyCtxX cls clt x) 1,
      liftBodyX ((List.suffix_cons _ _).trans hs') himgt hx hcx Φ ∈ tk.M →
        (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩ : OutLeg (ctxOf tp.l)).ret hS
          (tupImgT cls imgs himgs).2
          (WFF.mono (((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _) Φ) ∈ tp.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [(nextTy tk.l cls).bc] tp.l) '' tp.M ∪
      retSetX hS hs' himgt hx hcx himgs ht) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨Φ, hΦ, hder⟩ := ret_listX hS hs' himgt hx hcx himgs ht hk _ L hL
  have h₁ := hinv _ (liftBodyX_ex_pairUp_mem hk hs' himgt hx hcx Φ hΦ)
  have hc := retExtO_consistent hp.1 hS (.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩) _ _
    (Theory.Derives.of_mem h₁) (ctxOf_fresh (l := tp.l) le_rfl)
  have heq : retExtAtomO hS (.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩)
      (tupImgT cls imgs himgs).2
      (WFF.mono ((((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _).insert (.bnd 1) _)
        (WFF.pairUp Φ)) tp.l.length (ctxOf_fresh le_rfl) = retAtomX hS himgs ht hx Φ := by
    unfold retExtAtomO retAtomX
    refine WFF.retxS_congr hS x _ (.box _) (tupImgT_ext himgs (imgOk_ext himgs)).symm ?_
    rw [WFF.bodySplit_mono_pairUp ((ctxOf_le_of_suffix ht).diaIn x), WFF.mono_mono]
  rw [heq] at hc
  exact hc (Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, p⟩)

/-- The parent grown by the image of the child's next root, along the way home along `x`. -/
noncomputable def retStepX (hs' : (nextTy tk.l cls :: cls) <:+ tk.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) : NodeSt σ :=
  ⟨(nextTy tk.l cls).bc :: tp.l, complete (WFF.mono (ctxOf_le_append [(nextTy tk.l cls).bc] tp.l)
    '' tp.M ∪ retSetX hS hs' himgt hx hcx himgs ht)⟩

/-- ⭐**One realisation step along the way home along `x`**: the grown parent is maximal
    consistent, extends the old one, and the invariant along `x` holds for one more root. -/
theorem retStepX_ok (hs' : (nextTy tk.l cls :: cls) <:+ tk.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M)
    (hinv : RetInvX hS tk tp cls imgs clt imgt x X cx) :
    Theory.IsMCS (retStepX hS hs' himgt hx hcx himgs ht).M ∧
      Grows tp (retStepX hS hs' himgt hx hcx himgs ht) ∧
      RetInvX hS tk (retStepX hS hs' himgt hx hcx himgs ht) (nextTy tk.l cls :: cls)
        (extImg imgs cls.length tp.l.length) clt imgt x X cx := by
  obtain ⟨_, _, _, _, _, _, h⟩ := hinv
  have hcons := retSetX_consistent hS hs' himgt hx hcx himgs ht hk hp h
  obtain ⟨hsub, hmcs⟩ := complete_spec hcons
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩,
    hs', imgOk_ext himgs, ht.trans (List.suffix_cons _ _), himgt, hx, hcx, fun Φ hΦ => ?_⟩
  exact hsub (Or.inr ⟨Φ, hΦ, rfl⟩)

end StepX

/-! ## Cross-arrow preservation along a witness arrow -/

omit [ModalSys.NoFour] in
/-- A returning possibility at any shape whose body refutes itself is absurd. -/
def Proof.retS_absurd {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (U : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1) {u : ℕ} (hu : Γ.RootFresh (.free u))
    (p : Proof σ Γ Δ (WFF.retS hS S t (WFF.and (WFF.neg U) U))) : Proof σ Γ Δ .bot := by
  have hd := Proof.ret_diaS hS .nec t _ p
  have q : Proof σ Γ.boxIn [] (WFF.neg (WFF.ex S.ty (WFF.and (WFF.neg U) U))) := by
    refine Proof.imp_intro (Proof.ex_elim u S.ty hu.boxIn
      (φ := WFF.openFree u hu.boxIn Ctx.NoSlots.slots (WFF.and (WFF.neg U) U)) (ψ := .bot)
      (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
        (Proof.lookup List.mem_cons_self)) ?_)
    exact Proof.imp_elim (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.and_elim_r (Proof.lookup List.mem_cons_self))
  exact Proof.imp_elim hd
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) q))

omit [ModalSys.NoFour] in
/-- Weakening the unit's conjunct along a possible part weakens its object. -/
theorem WFF.mono_unitBodyD {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {C X A : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd C X) (.VTypeBox A))) 1) :
    WFF.mono (h.boxIn.insert (.bnd 0) (RShape.prod (.box C) (.dia X)).ty)
        (WFF.unitBodyD hS sb θ) = WFF.unitBodyD hS (Term.mono h.boxIn sb) θ := by
  unfold WFF.unitBodyD
  refine WFF.retxS_congr' hS _ _ _ ?_ ?_
  · change Term.mono _ (Term.mono _ sb) = Term.mono _ (Term.mono _ sb)
    rw [Term.mono_mono, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _
      ((((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).insert _).diaIn _).insert _)]
    change WFF.holeAt _ (Term.pair (Term.pair (Term.mono _ (Term.eta _ _ _))
      (Term.mono _ (Term.eta _ _ _))) (Term.mono _ (Term.eta _ _ _))) θ = _
    rw [Term.mono_eta, Term.mono_eta, Term.mono_eta]

/-- ⭐The unit's conjunct along the possible part, at the reverse arrow's items and a body packed
    along `x`, read at the parent: the reverse arrow's returning possibility **along `x`**.  The
    possible part `⟨□ā, x⟩` puts the way back in `x`'s extent. -/
theorem liftBodyW_unitBodyD {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (hS : ModalSys.BStrong = true)
    (Φ : WFF σ (((ctxOf cls).diaIn x).insert (.bnd 0) (.VTypeBox (bcT clt))) 1) :
    liftBodyW hs himgt hx (WFF.unitBodyD (Γ := ctxOf clt) hS (tupT clt).2 (pack2X _ hx Φ)) =
      (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix hs).ref hx⟩ : OutLeg (ctxOf lv)).ret hS
        (tupImgT clt imgt himgt).2
        (WFF.mono (((ctxOf_le_of_suffix hs).diaIn x).insert (.bnd 0) _) Φ) := by
  have hle := ctxOf_le_of_suffix hs
  have hu := Ctx.ref_insert_root (ctxOf clt).boxIn (.bnd 0)
    (RShape.prod (.box (bcT cls)) (.dia X)).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ : Subst.Ok (bodyCtxW cls clt X)
      ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.ok_set (ok_arrowS himgt) rfl
  have hc : Subst.Coh (Subst.setIdx (arrowIdx imgt) (.bnd 0) (liftEntryW hs hx))
      (bodyCtxW cls clt X) ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.coh_set (ok_arrowS himgt) (coh_arrowS himgt)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl
  have hw : (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .snd)).idxAlong [] = x := rfl
  have hfst : ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .fst) =
      .tm (Term.boxtm (Term.mono hle.boxIn (tupT cls).2)) := by
    rw [Subst.at_proj _ _ rfl]
    change (Subst.set _ _ _ (.root (.bnd 0))).proj .fst = _
    rw [Subst.set_root]
    rfl
  unfold liftBodyW WFF.unitBodyD
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ x rfl ⟨X, hle.ref hx⟩
    ((Ctx.NoSlots.slots (Γ := ctxOf lv)).diaIn x) (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf lv) imgt) _ (ok_arrowS himgt) _
      (coh_arrowS himgt) ?_ _).trans (subst_arrow_tupT clt himgt)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ ?_ _).trans (holeAt_tupT_pack2X (hle.diaIn x) hx Φ)
    refine sig_pair (sig_pair ?_ ?_) ?_
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)
          (Term.mono (Ctx.le_boxIn_diaIn _ x) (Term.mono hle.boxIn (tupT cls).2))) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.dia_eq_box_mono (Δ₁ := (ctxOf clt).boxIn.insert (.bnd 0) _) _ _ x _ _
            (Ctx.ref_inner (Ctx.ref_fst_of hu)), Subst.box_at_inner_boxtm _ hfst]
        rfl
      · exact congrArg (Sigma.mk _) (by rw [Term.mono_mono, Term.mono_mono])
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)
          (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx)))) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
        dsimp only [Subst.dia]
        rw [if_pos rfl, Subst.at_proj _ _ rfl]
        change SubE.mono _ (SubE.diaBody x ((Subst.set _ _ _ (.root (.bnd 0))).proj .snd)) = _
        rw [Subst.set_root]
        change SubE.mono _ (SubE.diaBody x (SubE.tm (Term.diatm x _
          (Term.eta (x.step .dia) X _)))) = _
        rw [SubE.diaBody_diatm]
        rfl
      · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) 0 _ _)

/-- ⭐**Cross-arrow preservation along a witness arrow**: committing the parent's next root along
    the forward arrow keeps the way home's invariant along `x`, over the extended list.  Were the
    reverse returning possibility along `x` for `Φ` to fail at the parent, its negation would be
    a forward body (`liftBodyW_unitBodyD`), so the grown child would have `◇[⟨d, e⟩ ↦ y] ¬U`; `Φ`,
    read there, is `θ(y, □sb)` (`holeRead_tupImgT_pack2X`), and `ret_unitD` gives
    `◇[⟨d, e⟩ ↦ y](¬U ∧ U)`, which is absurd. -/
theorem retStepW_rev (hS : ModalSys.BStrong = true) {ts tt : NodeSt σ} {cl clt : List VarType}
    {img imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hs' : (nextTy ts.l cl :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvW hS ts tt cl img clt imgt x X cx) :
    RetInvX hS (retStepW hS hs' himgt himg ht hx hcx) ts clt imgt (nextTy ts.l cl :: cl)
      (extImg img cl.length tt.l.length) x X cx := by
  obtain ⟨_, _, _, _, _, _, h⟩ := hinv
  obtain ⟨hsub, hmcs⟩ := complete_spec (retSetW_consistent hS hs' himgt himg ht hx hcx hv hw h)
  have ht' : clt <:+ (nextTy ts.l cl).bc :: tt.l := ht.trans (List.suffix_cons _ _)
  have hx' : (ctxOf (nextTy ts.l cl :: cl)).ref x = some (.VTypeDia X) := ref_old_of_ref hx
  have hcx' := (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l).ref hcx
  refine ⟨ht', himgt, hs', imgOk_ext himg, hx', hcx', fun Φ hΦ => ?_⟩
  by_contra hn
  have hneg := hv.neg_mem_iff.mpr hn
  have hΨ : liftBodyW hs' himgt hx' (WFF.neg (WFF.unitBodyD (Γ := ctxOf clt) hS (tupT clt).2
      (pack2X _ hx' Φ))) ∈ ts.M := by
    change WFF.neg (liftBodyW hs' himgt hx' _) ∈ ts.M
    rw [liftBodyW_unitBodyD]
    exact hneg
  have hret := hsub (Or.inr ⟨_, hΨ, rfl⟩)
  have p₁ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [retAtomW hS himg ht hcx (WFF.neg (WFF.unitBodyD (Γ := ctxOf clt) hS (tupT clt).2
        (pack2X _ hx' Φ)))]
      (WFF.retS hS (.prod (.box (bcT (nextTy ts.l cl :: cl))) (.dia X))
        (Term.pair (tupImgT (nextTy ts.l cl :: cl) (extImg img cl.length tt.l.length)
            (imgOk_ext himg)).2 (Term.eta (.root (.free cx)) X hcx'))
        (WFF.neg (WFF.unitBodyD hS (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2)
          (pack2X _ hx' Φ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    unfold retAtomW
    refine congrArg (WFF.retS hS _ _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyD (ctxOf_le_of_suffix ht')]
  have p₂ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [liftBodyX ht' (imgOk_ext himg) hx' hcx' Φ]
      (WFF.holeRead (Term.pair (Term.pair (tupImgT (nextTy ts.l cl :: cl)
          (extImg img cl.length tt.l.length) (imgOk_ext himg)).2
          (Term.eta (.root (.free cx)) X hcx'))
        (Term.boxtm (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2)))
        (pack2X _ hx' Φ)) :=
    Proof.conv (holeRead_tupImgT_pack2X (imgOk_ext himg) hx' hcx' _ Φ).symm
      (Proof.lookup List.mem_cons_self)
  have p₃ : Proof σ (ctxOf ((nextTy ts.l cl).bc :: tt.l))
      [retAtomW hS himg ht hcx (WFF.neg (WFF.unitBodyD (Γ := ctxOf clt) hS (tupT clt).2
        (pack2X _ hx' Φ))), liftBodyX ht' (imgOk_ext himg) hx' hcx' Φ] .bot :=
    Proof.retS_absurd hS _ _ _ (ctxOf_fresh (l := (nextTy ts.l cl).bc :: tt.l) le_rfl)
      (Proof.ret_unitD hS _ _ _ _
        (Proof.ofSubset (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_self) p₁)
        (Proof.ofSubset (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_of_mem _ List.mem_cons_self) p₂))
  refine hmcs.1 ⟨_, fun y hy => ?_, ⟨p₃⟩⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hret
  · rw [List.mem_singleton.mp hy]
    exact hΦ

/-- ⭐The witnessed unit's conjunct at the forward arrow's items and the witness, with a packed
    witness body, read at the child: the forward arrow's returning possibility at the witness
    shape, valued at the images and `cx`. -/
theorem liftBodyX_unitBodyW {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (hS : ModalSys.BStrong = true)
    (Φ : WFF σ (bodyCtxW clt cls X) 1) :
    liftBodyX hs himgt hx hcx (WFF.unitBodyW (Γ := ctxOf clt) hS (tupT clt).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx))
        (pack2 cls (RShape.prod (.box (bcT clt)) (.dia X)).ty Φ)) =
      WFF.retS hS (.prod (.box (bcT clt)) (.dia X))
        (Term.pair (tupImgT clt imgt himgt).2 (Term.eta (.root (.free cx)) X hcx))
        (WFF.mono ((ctxOf_le_of_suffix hs).boxIn.insert (.bnd 0) _) Φ) := by
  unfold liftBodyX WFF.unitBodyW
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf lv) imgt) _ (ok_arrowS himgt) _
      (coh_arrowS himgt) ?_ _).trans (subst_arrow_tupT clt himgt)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [Term.subst_mono]
    refine Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_
    rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ (fun h => by cases h)]
    exact if_pos rfl
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_congr _ ?_ _).trans (holeAt_tupT_pack2 (ctxOf_le_of_suffix hs).boxIn Φ)
    refine sig_pair ?_ ?_
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).boxIn)).root _)
          (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2)) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.box_at_inner_boxtm _ (by
            change Subst.set _ _ _ (.root (.bnd 0)) = _
            exact Subst.set_root _ _ _)]
        rfl
      · rw [Term.mono_mono]
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ _ _ _ _)

/-- ⭐**Cross-arrow preservation along the way home along `x`**: committing the child's next root
    to the parent keeps the forward arrow's invariant, over the extended list.  Were the forward
    returning possibility for `Φ` to fail at the child, its negation would be a body along `x`
    (`liftBodyX_unitBodyW`), so the grown parent would have `◇_x[d ↦ y] ¬U`; `Φ`, read there, is
    `θ(y, □sb, x)` (`holeRead_tupImgT_pack2`), and `ret_unitW` gives `◇_x[d ↦ y](¬U ∧ U)`, which
    is absurd (`Proof.retx_absurd`). -/
theorem retStepX_rev (hS : ModalSys.BStrong = true) {tk tp : NodeSt σ} {cls clt : List VarType}
    {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hs' : (nextTy tk.l cls :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M)
    (hinv : RetInvX hS tk tp cls imgs clt imgt x X cx) :
    RetInvW hS (retStepX hS hs' himgt hx hcx himgs ht) tk clt imgt (nextTy tk.l cls :: cls)
      (extImg imgs cls.length tp.l.length) x X cx := by
  obtain ⟨_, _, _, _, _, _, h⟩ := hinv
  obtain ⟨hsub, hmcs⟩ := complete_spec (retSetX_consistent hS hs' himgt hx hcx himgs ht hk hp h)
  have ht' : clt <:+ (nextTy tk.l cls).bc :: tp.l := ht.trans (List.suffix_cons _ _)
  have hle := ctxOf_le_of_suffix ht'
  have hx'' : ∃ X', (ctxOf ((nextTy tk.l cls).bc :: tp.l)).ref x = some (.VTypeDia X') :=
    ⟨X, hle.ref hx⟩
  refine ⟨ht', himgt, hs', imgOk_ext himgs, hx, hcx, fun Φ hΦ => ?_⟩
  by_contra hn
  have hneg := hk.neg_mem_iff.mpr hn
  have hΨ : liftBodyX hs' himgt hx hcx (WFF.neg (WFF.unitBodyW (Γ := ctxOf clt) hS (tupT clt).2
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx))
      (pack2 (nextTy tk.l cls :: cls) (RShape.prod (.box (bcT clt)) (.dia X)).ty Φ))) ∈
      tk.M := by
    change WFF.neg (liftBodyX hs' himgt hx hcx _) ∈ tk.M
    rw [liftBodyX_unitBodyW]
    exact hneg
  have hret := hsub (Or.inr ⟨_, hΨ, rfl⟩)
  have p₁ : Proof σ (ctxOf ((nextTy tk.l cls).bc :: tp.l))
      [retAtomX hS himgs ht hx (WFF.neg (WFF.unitBodyW (Γ := ctxOf clt) hS (tupT clt).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx))
        (pack2 (nextTy tk.l cls :: cls) (RShape.prod (.box (bcT clt)) (.dia X)).ty Φ)))]
      (WFF.retx hS x hx''
        (tupImgT (nextTy tk.l cls :: cls) (extImg imgs cls.length tp.l.length)
          (imgOk_ext himgs)).2
        (WFF.neg (WFF.unitBodyW hS (Term.mono hle.boxIn (tupT clt).2)
          (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx)))
          (pack2 (nextTy tk.l cls :: cls) (RShape.prod (.box (bcT clt)) (.dia X)).ty Φ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    unfold retAtomX
    refine congrArg (WFF.retx hS x _ _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyW hle, Term.mono_eta]
  have p₂ : Proof σ (ctxOf ((nextTy tk.l cls).bc :: tp.l))
      [liftBodyW ht' (imgOk_ext himgs) hx Φ]
      (WFF.holeRead (Term.pair (tupImgT (nextTy tk.l cls :: cls)
          (extImg imgs cls.length tp.l.length) (imgOk_ext himgs)).2
        (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT clt).2))
          (Term.diatm x hx'' (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx))))))
        (pack2 (nextTy tk.l cls :: cls) (RShape.prod (.box (bcT clt)) (.dia X)).ty Φ)) :=
    Proof.conv (holeRead_tupImgT_pack2 (imgOk_ext himgs) _ Φ).symm
      (Proof.lookup List.mem_cons_self)
  have p₃ : Proof σ (ctxOf ((nextTy tk.l cls).bc :: tp.l))
      [retAtomX hS himgs ht hx (WFF.neg (WFF.unitBodyW (Γ := ctxOf clt) hS (tupT clt).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx))
        (pack2 (nextTy tk.l cls :: cls) (RShape.prod (.box (bcT clt)) (.dia X)).ty Φ))),
        liftBodyW ht' (imgOk_ext himgs) hx Φ] .bot :=
    Proof.retx_absurd hS hx'' _ _ (ctxOf_fresh (l := (nextTy tk.l cls).bc :: tp.l) le_rfl)
      (Proof.ret_unitW hS hx'' _ _ _ _ _
        (Proof.ofSubset (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_self) p₁)
        (Proof.ofSubset (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_of_mem _ List.mem_cons_self) p₂))
  refine hmcs.1 ⟨_, fun y hy => ?_, ⟨p₃⟩⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hret
  · rw [List.mem_singleton.mp hy]
    exact hΦ

/-! ## Growth -/

/-- A growing child keeps the forward invariant of a witness arrow. -/
theorem RetInvW.grow_tgt {hS : ModalSys.BStrong = true} {tv tw tw' : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvW hS tv tw cls imgs clt imgt x X cx) (hg : Grows tw tw') :
    RetInvW hS tv tw' cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs, himgs.mono hle, ht.trans hg.suf, himgt, hx, hle.ref hcx, fun Φ hΦ => ?_⟩
  have h' := hg.sub _ (hinv Φ hΦ)
  change WFF.retS hS _ (Term.mono hle _) (WFF.mono _ (WFF.mono _ Φ)) ∈ tw'.M at h'
  rw [WFF.mono_mono, WFF.retS_congr hS _ (sig_pair (tupImgT_mono hle cls imgs himgs)
    (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))) rfl] at h'
  exact h'

/-- A witness body read in a larger parent is the weakening of its reading. -/
theorem liftBodyW_mono {lv lv' cls clt : List VarType} (hs : cls <:+ lv) (hl : lv <:+ lv')
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtxW cls clt X) 1) :
    WFF.mono (ctxOf_le_of_suffix hl) (liftBodyW hs himgt hx Φ) =
      liftBodyW (hs.trans hl) (himgt.mono (ctxOf_le_of_suffix hl)) hx Φ := by
  unfold liftBodyW
  rw [WFF.mono_subst _ _ _ _ _ _ Ctx.NoSlots.slots]
  have heq : ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).mono
      (ctxOf_le_of_suffix hl) =
        (arrowS σ (ctxOf lv') imgt).set (.bnd 0) (liftEntryW (hs.trans hl) hx) := by
    funext v
    change SubE.mono _ (Subst.set _ _ _ v) = Subst.set _ _ _ v
    by_cases hv : v = .root (.bnd 0)
    · subst hv
      rw [Subst.set_root, Subst.set_root]
      change SubE.tm (Term.pair (Term.boxtm (Term.mono _ (Term.mono _ _)))
        (Term.mono _ (Term.eta _ _ _))) = _
      rw [Term.mono_mono, Term.mono_eta]
    · rw [Subst.set_ne _ _ hv, Subst.set_ne _ _ hv]
      match v with
      | .step u .box => rfl
      | .root _ => rfl
      | .step _ .fst => rfl
      | .step _ .snd => rfl
      | .step _ .dia => rfl
      | .step _ .here => rfl
      | .step _ .keep => rfl
  exact WFF.subst_congr _ _ _ _ _ _ _ _
    (Subst.sim_of fun v U _ _ => by rw [congrFun heq v]; exact .refl _) Φ

/-- A parent growing conservatively keeps the forward invariant of a witness arrow. -/
theorem RetInvW.grow_src {hS : ModalSys.BStrong = true} {tv tv' tw : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hv : Theory.IsMCS tv.M) (hv' : Theory.IsMCS tv'.M)
    (h : RetInvW hS tv tw cls imgs clt imgt x X cx) (hg : Grows tv tv') :
    RetInvW hS tv' tw cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs.trans hg.suf, himgs, ht, himgt.mono hle, hx, hcx, fun Φ hΦ => hinv Φ ?_⟩
  refine mem_of_mono_mem hle hv hv' hg.sub ?_
  rw [liftBodyW_mono hs hg.suf himgt hx Φ]
  exact hΦ

/-- A growing parent keeps the invariant along `x`. -/
theorem RetInvX.grow_tgt {hS : ModalSys.BStrong = true} {tk tp tp' : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvX hS tk tp cls imgs clt imgt x X cx) (hg : Grows tp tp') :
    RetInvX hS tk tp' cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs, himgs.mono hle, ht.trans hg.suf, himgt, hx, hcx, fun Φ hΦ => ?_⟩
  have h' := hg.sub _ (hinv Φ hΦ)
  change WFF.retxS hS x _ (.box _) (Term.mono hle _) (WFF.mono _ (WFF.mono _ Φ)) ∈ tp'.M at h'
  rw [WFF.mono_mono, WFF.retxS_congr hS x _ (.box _) (tupImgT_mono hle cls imgs himgs) rfl] at h'
  exact h'

/-- A witness body along `x` read in a larger child is the weakening of its reading. -/
theorem liftBodyX_mono {lv lv' cls clt : List VarType} (hs : cls <:+ lv) (hl : lv <:+ lv')
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (Φ : WFF σ (bodyCtxX cls clt x) 1) :
    WFF.mono (ctxOf_le_of_suffix hl) (liftBodyX hs himgt hx hcx Φ) =
      liftBodyX (hs.trans hl) (himgt.mono (ctxOf_le_of_suffix hl)) hx
        ((ctxOf_le_of_suffix hl).ref hcx) Φ := by
  unfold liftBodyX
  rw [WFF.mono_subst _ _ _ _ _ _ Ctx.NoSlots.slots]
  have heq : ((arrowXS σ (ctxOf lv) imgt x cx).set (.bnd 0) (liftEntry hs)).mono
      (ctxOf_le_of_suffix hl) =
        (arrowXS σ (ctxOf lv') imgt x cx).set (.bnd 0) (liftEntry (hs.trans hl)) := by
    funext v
    change SubE.mono _ (Subst.set _ _ _ v) = Subst.set _ _ _ v
    by_cases hv : v = .root (.bnd 0)
    · subst hv
      rw [Subst.set_root, Subst.set_root]
      change SubE.tm (Term.boxtm (Term.mono _ (Term.mono _ _))) = _
      rw [Term.mono_mono]
    · rw [Subst.set_ne _ _ hv, Subst.set_ne _ _ hv]
      match v with
      | .step u .box => rfl
      | .root _ => rfl
      | .step _ .fst => rfl
      | .step _ .snd => rfl
      | .step u .dia =>
          change SubE.mono _ (if u = x then _ else _) = if u = x then _ else _
          split <;> rfl
      | .step _ .here => rfl
      | .step _ .keep => rfl
  exact WFF.subst_congr _ _ _ _ _ _ _ _
    (Subst.sim_of fun v U _ _ => by rw [congrFun heq v]; exact .refl _) Φ

/-- A child growing conservatively keeps the invariant along `x`. -/
theorem RetInvX.grow_src {hS : ModalSys.BStrong = true} {tk tk' tp : NodeSt σ}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hk : Theory.IsMCS tk.M) (hk' : Theory.IsMCS tk'.M)
    (h : RetInvX hS tk tp cls imgs clt imgt x X cx) (hg : Grows tk tk') :
    RetInvX hS tk' tp cls imgs clt imgt x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  refine ⟨hs.trans hg.suf, himgs, ht, himgt.mono hle, hx, hle.ref hcx, fun Φ hΦ => hinv Φ ?_⟩
  refine mem_of_mono_mem hle hk hk' hg.sub ?_
  rw [liftBodyX_mono hs hg.suf himgt hx hcx Φ]
  exact hΦ

end BArrow

end V12M
