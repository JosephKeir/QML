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

end BArrow

end V12M
