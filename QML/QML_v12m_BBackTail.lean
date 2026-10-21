import QML.QML_v12m_BLimitRet
import QML.QML_v12m_RetForget
import QML.QML_v12m_BAliasW

/-!
# QML v12m — strong B: a `Back` atom's returns are interchangeable with its value

The forward law of the canonical "comes back as" (`BData.backRel`, `backRelX`; docs §11.20
`Att.back`): along an edge `s → k`, a `Back` carrier read out at `k` and home again is
interchangeable with the atom's value.  The network gives, for the edge's way home `k → s`, the
returning-possibility invariant (`RetAt`, `lretAt`); a body packing the tail formula of a test
formula `H` (`tailK H`) at the carrier's image holds at `k` trivially, and the counit with a
carrier (`ret_counitC`) brings it home as `tailK H` between the returned image and the value.

* `counitBodyC`, `liftBody_counitBodyC`, `liftBodyX_counitBodyC`: the counit's body over a leg's
  view, read at the far end; `mem_box_counit_tail`: its tail body holds there.
* ⭐`RetAt.toRetInv`, `RetAt.toRetInvX`: every form of the invariant gives the plain one (and, when
  the way back lies in a witness's extent, the one along the witness), by the forgetting lemmas
  at a node (`retx_forget_node`, `retD_forget_node`, `retxS_forget_node`, `retxD_forget_node`).
* ⭐⭐`back_tail`, `back_tailX`: rows 1 and 2 at a node — `K(⟨bdk sent home, t⟩)` for every `H`.
* `interch_of_tailK`: `K` at the packed test formula of `χ` gives agreement on `χ`.
* ⭐⭐`lbackRel`, `lbackRelX`, `bdataS`: the limit of a strong chain satisfies `backRel` and
  `backRelX`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Reading hole formulas at pairs -/

/-- A hole formula read at a pair is read at the pair with the slot in second place, the slot
    then filled. -/
theorem WFF.holeAt_pair_inst {Δ : Ctx} [Δ.NoSlots] {Y U : VarType} {p : Ann Y}
    (P : Term σ Δ Y p) {x : Ann U} (X : Term σ Δ U x)
    (G : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd Y U)) 1) :
    WFF.holeAt Ctx.NoSlots.slots (Term.pair P X) G =
      WFF.instantiate Ctx.NoSlots.slots X (WFF.holeAt ((Ctx.NoSlots.slots (Γ := Δ)).insert U)
        (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Δ)).root U) P)
          (Term.eta (.root (.bnd 0)) U (Ctx.ref_insert_root Δ (.bnd 0) U))) G) := by
  unfold WFF.instantiate WFF.substRoot WFF.holeAt
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ G).symm
  refine Subst.sim_of fun v T _ hv => ?_
  have hvr : v = .root (.bnd 0) := by
    by_contra hne
    simp [Ctx.insert, hne, Ctx.empty] at hv
  subst hvr
  obtain rfl : T = .VTypeProd Y U := by simpa [Ctx.insert] using hv.symm
  dsimp only [Subst.comp, Subst.single]
  rw [if_pos rfl, if_pos rfl]
  dsimp only [SubE.comp]
  exact SubE.sim_tm_sigma (sig_pair (Term.subst_single_mono_sig _ _).symm
    (Term.subst_eta_tm _ _ _ _ _ _ X (Subst.at_single_root _ _)).symm)

variable [ModalSys.NoFour]

/-- A non-slot variable of a `□` view is an item. -/
theorem boxIn_item' {Γ : Ctx} {v : VarSymb} {T : VarType} (h : Γ.boxIn v = some T) :
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

omit [ModalSys.NoFour] in
/-- Setting a root's entry does not change the substitution at addresses with another root. -/
theorem Subst.at_set_of_rt_ne {Δ : Ctx} (θ : Subst σ Δ) {r : Root} (E : SubE σ Δ) :
    ∀ {u : VarSymb}, u.rt ≠ r → (θ.set r E).at u = θ.at u
  | .root r', h => by
      change Subst.set θ r E (.root r') = θ (.root r')
      exact Subst.set_ne _ _ (fun e => h (by cases e; rfl))
  | .step u s, h => by
      change (if s.isProj then ((θ.set r E).at u).proj s else (θ.set r E) (.step u s)) =
        (if s.isProj then (θ.at u).proj s else θ (.step u s))
      rw [Subst.at_set_of_rt_ne θ E (u := u) h, Subst.set_ne _ _ (fun e => by cases e)]

/-! ## The counit with a carrier, at the plain leg -/

/-- `ret_counitC`'s body over a leg's view `V`: necessarily, `ψ` of the object and the carrier. -/
def counitBodyC {V : Ctx} [V.NoSlots] {A C : VarType} {c₀ : Ann C}
    (bd : Term σ V.boxIn C c₀) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A C)) 1) :
    WFF σ (V.insert (.bnd 0) (.VTypeBox A)) 1 :=
  WFF.box (WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert (.VTypeBox A)).boxIn
    (Term.pair (Term.eta (VarSymb.root (.bnd 0)).inner A
        (Ctx.ref_inner (Ctx.ref_insert_root V (.bnd 0) (.VTypeBox A))))
      (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root (.VTypeBox A)).boxIn)
        bd)) ψ)

/-- The counit's body read at the source: `ψ` of the committed roots' items and the carrier's
    image along the reverse arrow, necessarily. -/
theorem liftBody_counitBodyC {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {C : VarType} {c₀ : Ann C}
    (bd : Term σ (ctxOf clt).boxIn.boxIn C c₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (bcT cls) C)) 1) :
    liftBody hs himgt (counitBodyC bd ψ) =
      WFF.box (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2)
          (Term.subst (arrowIdx imgt) (arrowS σ (ctxOf lv) imgt).box
            (Subst.ok_box (ok_arrowS himgt)) (Subst.coh_box (ok_arrowS himgt) (coh_arrowS himgt))
            bd)) ψ) := by
  unfold liftBody counitBodyC
  simp only [WFF.subst]
  rw [WFF.subst_holeAt]
  refine congrArg WFF.box (WFF.holeAt_congr _ (sig_pair ?_ ?_) ψ)
  · exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ (by
      change Subst.set _ _ _ (.root (.bnd 0)) = _
      exact Subst.set_root _ _ _))
  · rw [Term.subst_mono]
    refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) bd
    obtain ⟨u, rfl, hu⟩ := boxIn_item' hv
    change SubE.Sim T ((Subst.at _ u).unbox) ((Subst.at _ u).unbox)
    rw [Subst.at_set_of_rt_ne _ _ (Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) hu)]
    exact .refl _

/-! ## Packed bodies read at the roots' items and any slot term -/

/-- ⭐A packed body read at the roots' items (weakened) and a term `X` in the slot's place: the body,
    weakened, with `X` in its slot (`holeAt_tupT_pack2` at any slot term). -/
theorem holeAt_tupT_pack2_repl {l : List VarType} {U T : VarType} {V : Ctx} [V.NoSlots]
    (h : (ctxOf l).boxIn.Le V) {x : Ann U} (X : Term σ (V.insert (.bnd 0) T) U x)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) U) 1) :
    WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert T)
      (Term.pair (Term.mono (h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root T))
          (tupT l).2) X)
      (pack2 l U Φ) = WFF.bodyRepl X (WFF.mono (h.insert (.bnd 0) U) Φ) := by
  have hle := h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root T)
  unfold WFF.holeAt pack2 WFF.bodyRepl
  rw [WFF.subst_mono]
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v S hlp hv => ?_
  have h0 : (Subst.single (σ := σ) (Δ := V.insert (.bnd 0) T) (.bnd 0)
      (.tm (Term.pair (Term.mono hle (tupT l).2) X))).at (.root (.bnd 0)) =
      .tm (Term.pair (Term.mono hle (tupT l).2) X) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : S = U := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp, pack2S]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .refl _
  · have hv' : (ctxOf l).boxIn v = some S := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    obtain ⟨u, rfl, hu⟩ := boxIn_item hv'
    obtain ⟨r, hr, hlt, _⟩ := ref_rt hu
    dsimp only [Subst.comp, pack2S]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    dsimp only [packS, SubE.comp]
    rw [hr]
    change SubE.Sim S _ (Subst.at _
      (((VarSymb.step (.root (.bnd 0)) .fst).ext (tupPath l r)).ext (encPath u.path ++ itemTail)))
    have hb : (Subst.single (σ := σ) (Δ := V.insert (.bnd 0) T) (.bnd 0)
        (.tm (Term.pair (Term.mono hle (tupT l).2) X))).at
          (.step (.root (.bnd 0)) .fst) = .tm (Term.mono hle (tupT l).2) := by
      rw [Subst.at_proj _ _ rfl, h0]
      rfl
    obtain ⟨R, hR, h1⟩ := at_tupPath_tupT _ l hle hb hlt
    have h2 := at_enc_tupB_mono hle _ ModalSys.T rfl hR h1 hu hr
    rw [at_item_of_tupB_base_mono hle _ _ hu ModalSys.T rfl h2, Term.mono_eta]
    exact .ren_eta _ _

/-- At a node, a body packed and read at the roots' items and a witnessed slot's first component is
    the body with that component in its slot (`kPsiF`'s form). -/
theorem kPsiF_pack2 {l : List VarType} {C X : VarType}
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox C)) 1) :
    kPsiF X (Γ := ctxOf l) (tupT l).2 (pack2 l (.VTypeBox C) Φ) =
      WFF.bodyRepl (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox C)
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ (.bnd 0) (RShape.wit (.box C) X).ty))) Φ := by
  unfold kPsiF
  exact (holeAt_tupT_pack2_repl (Ctx.Le.refl _) _ Φ).trans (WFF.mono_refl _ _ ▸ rfl)

/-! ## Every invariant gives the plain one -/

/-- The bound object's necessary part, as a term of a witnessed body. -/
abbrev fstEta (C X : VarType) {V : Ctx} :
    Term σ (V.insert (.bnd 0) (RShape.wit (.box C) X).ty) (.VTypeBox C)
      (Ann.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox C)) :=
  Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox C)
    (Ctx.ref_fst_of (Ctx.ref_insert_root _ (.bnd 0) (RShape.wit (.box C) X).ty))

/-- A witness body that reads only the necessary part, read at the source: the plain reading. -/
theorem liftBodyW_repl {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtx cls clt) 1) :
    liftBodyW hs himgt hx (WFF.bodyRepl (fstEta (bcT cls) X) Φ) = liftBody hs himgt Φ := by
  unfold liftBodyW liftBody WFF.bodyRepl
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox (bcT cls) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (Term.subst_eta_tm _ _ _ _ _ _ _ ?_).symm
    rw [Subst.at_proj _ _ rfl]
    change SubE.proj (Subst.set _ _ _ (.root (.bnd 0))) .fst = _
    rw [Subst.set_root]
    rfl
  · obtain ⟨u, rfl, _⟩ := body_item hlp hv hvr
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    dsimp only [Subst.idS, SubE.comp]
    rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ hvr]
    exact .refl _

/-- A doubly witnessed body that reads only the `□` view and the necessary part, read at the
    source: the plain reading. -/
theorem liftBodyWD_repl {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (Φ : WFF σ (bodyCtx cls clt) 1) :
    liftBodyWD hs himgt hx he hcxv (WFF.mono ((Ctx.le_boxIn_diaIn _ e).insert (.bnd 0) _)
        (WFF.bodyRepl (fstEta (bcT cls) X) Φ)) = liftBody hs himgt Φ := by
  unfold liftBodyWD liftBody
  rw [WFF.subst_mono (hΓ := (Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _)]
  unfold WFF.bodyRepl
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox (bcT cls) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (Term.subst_eta_tm _ _ _ _ _ _ _ ?_).symm
    rw [Subst.at_proj _ _ rfl]
    change SubE.proj (Subst.set _ _ _ (.root (.bnd 0))) .fst = _
    rw [Subst.set_root]
    rfl
  · obtain ⟨u, rfl, _⟩ := body_item hlp hv hvr
    dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    dsimp only [Subst.idS, SubE.comp]
    rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐**Forgetting a possible part at a node**, for any body over the `□` view. -/
def Proof.retD_forget_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {A X : VarType} {a : Ann A} (y : Term σ (ctxOf l) A a)
    {b : Ann X} (z : Term σ (ctxOf l) X b)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retS hS (.wit (.box A) X) (Term.pair y z)
      (WFF.bodyRepl (fstEta A X) Φ))) :
    Proof σ (ctxOf l) Δ (WFF.ret hS y Φ) :=
  Proof.conv (by rw [kPsi_pack2]) (Proof.retD_forget hS y z (tupT l).2
    (pack2 l (.VTypeBox A) Φ) (Proof.conv (by rw [kPsiF_pack2]) p))

/-- ⭐**Every form of the invariant gives the plain one** (docs §11.20): a body over the `□` view
    that the source makes true comes back as a plain returning possibility — the witnessed forms
    by forgetting the leg (`retx_forget`, `retxS_forget`) and the possible part
    (`retD_forget`). -/
theorem RetAt.toRetInv {hS : ModalSys.BStrong = true} {tv tw : NodeSt σ}
    (hw : Theory.IsMCS tw.M) {kv kw : Option (VarSymb × VarType)} {cv cw : ℕ}
    {cls : List VarType} {imgs : ℕ → ℕ} {clt : List VarType} {imgt : ℕ → ℕ}
    (h : RetAt hS tv tw kv kw cv cw cls imgs clt imgt) : RetInv hS tv tw cls imgs clt imgt := by
  rcases kv with _ | ⟨x, X⟩ <;> rcases kw with _ | ⟨e, E⟩
  · exact h
  · obtain ⟨hs, himgs, ht, himgt, he, hcx, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyX_lift]; exact hΦ)
    refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr, ⟨?_⟩⟩
    refine Proof.retx_forget_node hS ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ _ _
      (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    simp only [OutLeg.ret, OutLeg.retS, OutLeg.retSH, OutLeg.lift, WFF.mono_mono]
  · obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyW_repl]; exact hΦ)
    rw [WFF.mono_bodyRepl (ctxOf_le_of_suffix ht).boxIn, Term.mono_eta] at hr
    exact hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
      ⟨Proof.retD_forget_node hS _ _ _ (Proof.lookup List.mem_cons_self)⟩⟩
  · obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyWD_repl]; exact hΦ)
    refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr, ⟨?_⟩⟩
    refine Proof.retD_forget_node hS (tupImgT cls imgs himgs).2
      (Term.eta (.root (.free cv)) X hcxw) _ (Proof.conv ?_
        (Proof.retxS_forget_node hS ⟨E, (ctxOf_le_of_suffix ht).ref he⟩
          (Term.pair (tupImgT cls imgs himgs).2 (Term.eta (.root (.free cv)) X hcxw))
          (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _)
            (WFF.bodyRepl (fstEta (bcT cls) X) Φ))
          (Proof.conv ?_ (Proof.lookup List.mem_cons_self))))
    · rw [WFF.mono_bodyRepl (ctxOf_le_of_suffix ht).boxIn, Term.mono_eta]
    · simp only [OutLeg.lift, WFF.mono_mono]

/-! ## The tail body at the far end -/

omit [ModalSys.NoFour] in
/-- `K` holds of every diagonal pair, in any context with a fresh root. -/
def provable_tailK_diag' {Γ : Ctx} [Γ.NoSlots] {u : ℕ} (hu : Γ.RootFresh (.free u))
    {A T : VarType} {a : Ann A} (w : Term σ Γ A a)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A T)) 1) :
    Proof σ Γ [] (WFF.holeAt Ctx.NoSlots.slots (Term.pair w w) (tailK H)) := by
  rw [holeAt_tailK, ← WFF.bindFree_openFree u hu Ctx.NoSlots.slots
    (WFF.and (WFF.imp (tailAt w H) (tailAt w H)) (WFF.imp (tailAt w H) (tailAt w H)))]
  refine Proof.all_intro u T hu ?_
  change Proof σ _ [] (WFF.and
    (WFF.imp (WFF.openFree u hu Ctx.NoSlots.slots (tailAt w H))
      (WFF.openFree u hu Ctx.NoSlots.slots (tailAt w H)))
    (WFF.imp (WFF.openFree u hu Ctx.NoSlots.slots (tailAt w H))
      (WFF.openFree u hu Ctx.NoSlots.slots (tailAt w H))))
  exact .and_intro (.imp_intro (.lookup List.mem_cons_self))
    (.imp_intro (.lookup List.mem_cons_self))

/-- The tail body over the far end's committed roots: `K(⟨bdk, slot⟩)`, the carrier's image as a
    term over the roots' items. -/
def tailBody {cls : List VarType} {A U : VarType} {b : Ann A}
    (bdk : Term σ (ctxOf cls).boxIn A b)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A U)) 1) :
    WFF σ ((ctxOf cls).boxIn.insert (.bnd 0) A) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := (ctxOf cls).boxIn)).insert A)
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf cls).boxIn)).root A) bdk)
      (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A)))
    (tailK H)

/-- The counit's tail body read at the far end, at any image `img` of the carrier that is the
    weakened `bdk`: `□K(⟨u, u⟩)` for `u := bdk` — a theorem. -/
theorem mem_box_counit_tail {tv : NodeSt σ} (hv : Theory.IsMCS tv.M) {cls : List VarType}
    (hs : cls <:+ tv.l) {A U : VarType} {c : Ann A} (img : Term σ (ctxOf tv.l).boxIn A c)
    {b : Ann A} (bdk : Term σ (ctxOf cls).boxIn A b)
    (hbd : (⟨_, img⟩ : Σ e, Term σ (ctxOf tv.l).boxIn A e) =
      ⟨_, Term.mono (ctxOf_le_of_suffix hs).boxIn bdk⟩)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A U)) 1) :
    WFF.box (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2) img)
      (pack2 cls A (tailBody bdk H))) ∈ tv.M := by
  have hle := ctxOf_le_of_suffix hs
  rw [WFF.holeAt_pair_inst, Term.mono_mono, holeAt_tupT_pack2 hle.boxIn (tailBody bdk H)]
  unfold tailBody
  rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := (ctxOf tv.l).boxIn)).insert A)]
  simp only [Term.mono, Term.mono_mono, Term.mono_eta]
  have e := (WFF.holeAt_pair_inst (Term.mono hle.boxIn bdk) img (tailK H)).symm
  rw [Term.mono_mono] at e
  rw [e, WFF.holeAt_congr _ (sig_pair rfl hbd) (tailK H)]
  exact hv.closed ⟨[], fun _ h => absurd h List.not_mem_nil,
    ⟨Proof.K_box (Δ := []) (provable_tailK_diag' (ctxOf_fresh (l := tv.l) le_rfl).boxIn
      (Term.mono hle.boxIn bdk) H)⟩⟩

/-- ⭐**The counit's tail body holds at the far end**: read there, it is `□K(⟨u, u⟩)` for the
    carrier's image `u` — a theorem. -/
theorem mem_liftBody_counitBodyC_tail {tv : NodeSt σ} (hv : Theory.IsMCS tv.M)
    {cls clt : List VarType} (hs : cls <:+ tv.l) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf tv.l) imgt) {A U : VarType} {c₀ : Ann A}
    (bd : Term σ (ctxOf clt).boxIn.boxIn A c₀) {b : Ann A} (bdk : Term σ (ctxOf cls).boxIn A b)
    (hbd : (⟨_, Term.subst (arrowIdx imgt) (arrowS σ (ctxOf tv.l) imgt).box
        (Subst.ok_box (ok_arrowS himgt)) (Subst.coh_box (ok_arrowS himgt) (coh_arrowS himgt))
        bd⟩ : Σ e, Term σ (ctxOf tv.l).boxIn A e) =
      ⟨_, Term.mono (ctxOf_le_of_suffix hs).boxIn bdk⟩)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A U)) 1) :
    liftBody hs himgt (counitBodyC bd (pack2 cls A (tailBody bdk H))) ∈ tv.M := by
  rw [liftBody_counitBodyC]
  exact mem_box_counit_tail hv hs _ bdk hbd H

omit [ModalSys.NoFour] in
/-- Weakening the counit's body weakens its carrier. -/
theorem mono_counitBodyC {V V' : Ctx} [V.NoSlots] [V'.NoSlots] (h : V.Le V') {A C : VarType}
    {c₀ : Ann C} (bd : Term σ V.boxIn C c₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A C)) 1) :
    WFF.mono (h.insert (.bnd 0) (.VTypeBox A)) (counitBodyC bd ψ) =
      counitBodyC (Term.mono h.boxIn bd) ψ := by
  unfold counitBodyC
  simp only [WFF.mono]
  rw [WFF.mono_holeAt _ _ ((Ctx.NoSlots.slots (Γ := V')).insert (.VTypeBox A)).boxIn]
  refine congrArg WFF.box (WFF.holeAt_congr _ (sig_pair ?_ ?_) ψ)
  · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)
  · simp only [Term.mono_mono]

/-- The tail body sent along an arrow, its slot set to `t`: `K` at the carrier's image and `t`. -/
theorem subst_tailBody {cls : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk cls Δ img) {A U : VarType} {b : Ann A} (bdk : Term σ (ctxOf cls).boxIn A b)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A U)) 1) {a : Ann A} (t : Term σ Δ A a) :
    WFF.subst (Subst.setIdx (arrowIdx img) (.bnd 0) (.tm t))
        ((arrowS σ Δ img).set (.bnd 0) (.tm t)) (Subst.ok_set (ok_arrowS himg) rfl)
        (Subst.coh_set (ok_arrowS himg) (coh_arrowS himg)
          ((Ctx.NoSlots.slots (Γ := (ctxOf cls).boxIn)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := (ctxOf cls).boxIn)).insert A) Ctx.NoSlots.slots
        (tailBody bdk H) =
      WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.subst (arrowIdx img) (arrowS σ Δ img)
        (ok_arrowS himg) (coh_arrowS himg) bdk) t) (tailK H) := by
  unfold tailBody
  rw [WFF.subst_holeAt]
  refine WFF.holeAt_congr _ (sig_pair ?_ ?_) _
  · rw [Term.subst_mono]
    refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) bdk
    obtain ⟨u, rfl, -⟩ := boxIn_item' hv
    rw [Subst.set_ne _ _ (fun e => by cases e)]
    exact .refl _
  · exact Term.subst_eta_tm _ _ _ _ _ _ t (by
      change Subst.set _ _ _ (.root (.bnd 0)) = _
      exact Subst.set_root _ _ _)

/-- ⭐⭐**A `Back` atom's return is interchangeable with its value, at a node** (row 1, docs §11.20
    `Att.back`): along an arrow `k → s` with the invariant, a carrier `□□bd` that comes back as `t`
    at `s`, whose body sent to `k` is `bdk`, has `K(⟨bdk sent home, t⟩)` at `s` for every test
    formula `H` — the counit with a carrier (`ret_counitC`) at the tail body, which `k` has
    trivially (`mem_liftBody_counitBodyC_tail`). -/
theorem back_tail {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hk : Theory.IsMCS tk.M)
    (hs : Theory.IsMCS ts.M) {cls clt : List VarType} {imgs imgt : ℕ → ℕ}
    (h : RetInv hS tk ts cls imgs clt imgt) (hcs : cls <:+ tk.l)
    (himgs : ImgOk cls (ctxOf ts.l) imgs) (ht : clt <:+ ts.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) {A U : VarType} {c₀ : Ann A}
    (bd : Term σ (ctxOf clt).boxIn.boxIn A c₀) {b : Ann A} (bdk : Term σ (ctxOf cls).boxIn A b)
    (hbd : (⟨_, Term.subst (arrowIdx imgt) (arrowS σ (ctxOf tk.l) imgt).box
        (Subst.ok_box (ok_arrowS himgt)) (Subst.coh_box (ok_arrowS himgt) (coh_arrowS himgt))
        bd⟩ : Σ e, Term σ (ctxOf tk.l).boxIn A e) =
      ⟨_, Term.mono (ctxOf_le_of_suffix hcs).boxIn bdk⟩)
    {a : Ann A} (t : Term σ (ctxOf ts.l) A a)
    (hback : WFF.back hS .nec (Term.boxtm (Term.boxtm
      (Term.mono (ctxOf_le_of_suffix ht).boxIn.boxIn bd))) t ∈ ts.M)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A U)) 1) :
    WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.subst (arrowIdx imgs) (arrowS σ (ctxOf ts.l) imgs)
      (ok_arrowS himgs) (coh_arrowS himgs) bdk) t) (tailK H) ∈ ts.M := by
  obtain ⟨_, _, _, _, hinv⟩ := h
  have hr := hinv _ (mem_liftBody_counitBodyC_tail hk hcs himgt bd bdk hbd H)
  rw [mono_counitBodyC (ctxOf_le_of_suffix ht).boxIn] at hr
  have hc := hs.closed ⟨[_, _], fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hr
      · rw [List.mem_singleton.mp hy]; exact hback,
    ⟨Proof.ret_counitC hS .nec (tupImgT cls imgs himgs).2
      (Term.mono (ctxOf_le_of_suffix ht).boxIn.boxIn bd) t (pack2 cls A (tailBody bdk H))
      (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rwa [holeRead_tupImgT_pack2, subst_tailBody himgs] at hc

/-! ## Row 2: along the carrier's witness -/

/-- ⭐A body packed along `x`, read at the roots' items, `x`'s content and any slot term `Y`: the
    body, weakened, with `Y` in its slot (`holeAt_tupT_pack2X` at any slot term). -/
theorem holeAt_tupT_pack2X_repl {l : List VarType} {x : VarSymb} {X U T : VarType} {V : Ctx}
    [V.NoSlots] (h : ((ctxOf l).diaIn x).Le V) (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {y : Ann U} (Y : Term σ (V.insert (.bnd 0) T) U y)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) U) 1) :
    WFF.holeAt ((Ctx.NoSlots.slots (Γ := V)).insert T)
      (Term.pair
        (Term.pair
          (Term.mono (((Ctx.le_boxIn_diaIn _ x).trans h).trans
            (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root T)) (tupT l).2)
          (Term.eta (x.step .dia) X
            ((h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root T)).ref
              (Ctx.ref_diaIn_of hx))))
        Y)
      (pack2X U hx Φ) = WFF.bodyRepl Y (WFF.mono (h.insert (.bnd 0) U) Φ) := by
  have hle := ((Ctx.le_boxIn_diaIn _ x).trans h).trans
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root T)
  unfold WFF.holeAt pack2X WFF.bodyRepl
  rw [WFF.subst_mono]
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v S hlp hv => ?_
  have h0 : (Subst.single (σ := σ) (Δ := V.insert (.bnd 0) T) (.bnd 0)
      (.tm (Term.pair (Term.pair (Term.mono hle (tupT l).2)
          (Term.eta (x.step .dia) X ((h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root
            T)).ref (Ctx.ref_diaIn_of hx)))) Y))).at (.root (.bnd 0)) =
      .tm (Term.pair (Term.pair (Term.mono hle (tupT l).2)
          (Term.eta (x.step .dia) X ((h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root
            T)).ref (Ctx.ref_diaIn_of hx)))) Y) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : S = U := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp, pack2XS]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .refl _
  · have hv' : ((ctxOf l).diaIn x) v = some S := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    rcases diaIn_item hv' with ⟨u, rfl, hu⟩ | ⟨rfl, hxT⟩
    · obtain ⟨r, hr, hlt, _⟩ := ref_rt hu
      dsimp only [Subst.comp, pack2XS]
      rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
      dsimp only [packXS, SubE.comp]
      rw [hr]
      change SubE.Sim S _ (Subst.at _ ((((VarSymb.step (.root (.bnd 0)) .fst).step .fst).ext
        (tupPath l r)).ext (encPath u.path ++ itemTail)))
      have hb : (Subst.single (σ := σ) (Δ := V.insert (.bnd 0) T) (.bnd 0)
          (.tm (Term.pair (Term.pair (Term.mono hle (tupT l).2)
              (Term.eta (x.step .dia) X ((h.trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root
                T)).ref (Ctx.ref_diaIn_of hx)))) Y))).at
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
      rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
      change SubE.Sim X _
        ((if x = x then SubE.ren (.step (.step (.root (.bnd 0)) .fst) .snd) else .hide).comp _ _ _)
      rw [if_pos rfl]
      dsimp only [SubE.comp]
      rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
      exact .ren_eta _ _

/-- At a node, a body packed along `x` and read at the roots' items, `x`'s content and a witnessed
    slot's first component is the body with that component in its slot (`kPsiXF`'s form). -/
theorem kPsiXF_pack2X {l : List VarType} {x : VarSymb} {X C Xe : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox C)) 1) :
    kPsiXF Xe (Γ := ctxOf l) hX (tupT l).2 (pack2X (.VTypeBox C) hX Φ) =
      WFF.bodyRepl (fstEta C Xe) Φ := by
  unfold kPsiXF
  exact (holeAt_tupT_pack2X_repl (Ctx.Le.refl _) hX _ Φ).trans (WFF.mono_refl _ _ ▸ rfl)

/-- ⭐**Forgetting a possible part along a witness, at a node**, for any body over its view. -/
noncomputable def Proof.retxD_forget_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {x : VarSymb} {X C Xe : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X)) {c : Ann C} (y : Term σ (ctxOf l) C c)
    {b : Ann Xe} (z : Term σ (ctxOf l) Xe b)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox C)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) (Term.pair y z)
      (WFF.bodyRepl (fstEta C Xe) Φ))) :
    Proof σ (ctxOf l) Δ (WFF.retx hS x ⟨X, hX⟩ y Φ) :=
  Proof.conv (by rw [kPsiX_pack2X]) (Proof.retxD_forget hS hX y z (tupT l).2
    (pack2X (.VTypeBox C) hX Φ) (Proof.conv (by rw [kPsiXF_pack2X]) p))

/-- A doubly witnessed body that reads only the necessary part, read at the source: the reading
    along the target's witness. -/
theorem liftBodyWD_replX {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (Φ : WFF σ (bodyCtxX cls clt e) 1) :
    liftBodyWD hs himgt hx he hcxv (WFF.bodyRepl (fstEta (bcT cls) X) Φ) =
      liftBodyX hs himgt he hcxv Φ := by
  unfold liftBodyWD liftBodyX WFF.bodyRepl
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox (bcT cls) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (Term.subst_eta_tm _ _ _ _ _ _ _ ?_).symm
    rw [Subst.at_proj _ _ rfl]
    change SubE.proj (Subst.set _ _ _ (.root (.bnd 0))) .fst = _
    rw [Subst.set_root]
    rfl
  · dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    dsimp only [Subst.idS, SubE.comp]
    rcases bodyX_item hv hvr with ⟨u, rfl, _⟩ | ⟨rfl, _⟩
    · rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ hvr]
      exact .refl _
    · rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ hvr]
      exact .refl _

/-- ⭐**An invariant whose way back lies in a witness's extent gives the one along it**: the
    doubly witnessed form by forgetting the possible part (`retxD_forget`). -/
theorem RetAt.toRetInvX {hS : ModalSys.BStrong = true} {tv tw : NodeSt σ}
    (hw : Theory.IsMCS tw.M) {kv : Option (VarSymb × VarType)} {e : VarSymb} {E : VarType}
    {cv cw : ℕ} {cls : List VarType} {imgs : ℕ → ℕ} {clt : List VarType} {imgt : ℕ → ℕ}
    (h : RetAt hS tv tw kv (some (e, E)) cv cw cls imgs clt imgt) :
    RetInvX hS tv tw cls imgs clt imgt e E cw := by
  rcases kv with _ | ⟨x, X⟩
  · exact h
  · obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, he, hcxv, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyWD_replX]; exact hΦ)
    refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr, ⟨?_⟩⟩
    refine Proof.retxD_forget_node hS ((ctxOf_le_of_suffix ht).ref he)
      (tupImgT cls imgs himgs).2 (Term.eta (.root (.free cv)) X hcxw) _
      (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    rw [WFF.mono_bodyRepl ((ctxOf_le_of_suffix ht).diaIn e), Term.mono_eta]

/-! ## Every invariant with companions gives the plain one with companions -/

/-- ⭐**Forgetting a possible part at a node, with companions**, for any body over the `□`
    view. -/
def Proof.retD_forgetC_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {A X : VarType} (co : List (List Step)) (ho : A.CompOk co)
    {a : Ann (A.compsFlat co)} (y : Term σ (ctxOf l) (A.compsFlat co) a) {b : Ann X}
    (z : Term σ (ctxOf l) X b) (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retS hS (.wit (.boxC A co ho) X) (Term.pair y z)
      (WFF.bodyRepl (fstEta A X) Φ))) :
    Proof σ (ctxOf l) Δ (WFF.retS hS (.nec (.boxC A co ho)) y Φ) :=
  Proof.conv (by rw [kPsi_pack2]) (Proof.retD_forgetC hS co ho y z (tupT l).2
    (pack2 l (.VTypeBox A) Φ) (Proof.conv (by rw [kPsiF_pack2]) p))

/-- ⭐**Forgetting a possible part along a witness at a node, with companions**, for any body over
    its view. -/
noncomputable def Proof.retxD_forgetC_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {x : VarSymb} {X C Xe : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X)) (co : List (List Step)) (ho : C.CompOk co)
    {c : Ann (C.compsFlat co)} (y : Term σ (ctxOf l) (C.compsFlat co) c) {b : Ann Xe}
    (z : Term σ (ctxOf l) Xe b)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox C)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retxS hS x ⟨X, hX⟩ (.wit (.boxC C co ho) Xe) (Term.pair y z)
      (WFF.bodyRepl (fstEta C Xe) Φ))) :
    Proof σ (ctxOf l) Δ (WFF.retxS hS x ⟨X, hX⟩ (.nec (.boxC C co ho)) y Φ) :=
  Proof.conv (by rw [kPsiX_pack2X]) (Proof.retxD_forgetC hS hX co ho y z (tupT l).2
    (pack2X (.VTypeBox C) hX Φ) (Proof.conv (by rw [kPsiXF_pack2X]) p))

/-- ⭐**Every form of the invariant with companions gives the plain one with companions**
    (`RetAt.toRetInv` at `tupShape`): the witnessed forms by forgetting the leg
    (`retx_forgetC`, `retxS_forgetC`) and the possible part (`retD_forgetC`), keeping the tuple's
    companions. -/
theorem RetAtB.toRetInvB {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw : NodeSt σ} (hw : Theory.IsMCS tw.M) {kv kw : Option (VarSymb × VarType)} {cv cw : ℕ}
    {cls : List VarType} {imgs : ℕ → ℕ} {clt : List VarType} {imgt : ℕ → ℕ}
    (h : RetAtB hS b hb tv tw kv kw cv cw cls imgs clt imgt) :
    RetInvB hS b hb tv tw cls imgs clt imgt := by
  rcases kv with _ | ⟨x, X⟩ <;> rcases kw with _ | ⟨e, E⟩
  · exact h
  · obtain ⟨hs, himgs, ht, himgt, he, hcx, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyX_lift]; exact hΦ)
    refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr, ⟨?_⟩⟩
    refine Proof.retx_forgetC_node hS ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ _ _ _ _
      (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    simp only [OutLeg.retS, OutLeg.retSH, OutLeg.lift, WFF.mono_mono]
  · obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyW_repl]; exact hΦ)
    rw [WFF.mono_bodyRepl (ctxOf_le_of_suffix ht).boxIn, Term.mono_eta] at hr
    exact hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
      ⟨Proof.retD_forgetC_node hS _ _ _ _ _ (Proof.lookup List.mem_cons_self)⟩⟩
  · obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyWD_repl]; exact hΦ)
    refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr, ⟨?_⟩⟩
    refine Proof.retD_forgetC_node hS _ (VarType.compOk_compsAllB b hb _)
      (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB b hb _)).2
      (Term.eta (.root (.free cv)) X hcxw) _ (Proof.conv ?_
        (Proof.retxS_forgetC_node hS ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ _
          (VarType.compOk_compsAllB b hb _)
          (Term.pair (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB b hb _)).2
            (Term.eta (.root (.free cv)) X hcxw))
          (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _)
            (WFF.bodyRepl (fstEta (bcT cls) X) Φ))
          (Proof.conv ?_ (Proof.lookup List.mem_cons_self))))
    · rw [WFF.mono_bodyRepl (ctxOf_le_of_suffix ht).boxIn, Term.mono_eta]
    · simp only [OutLeg.lift, WFF.mono_mono]

/-- ⭐**An invariant with companions whose way back lies in a witness's extent gives the one along
    it** (`RetAt.toRetInvX` at `tupShape`, by `retxD_forgetC`). -/
theorem RetAtB.toRetInvXB {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw : NodeSt σ} (hw : Theory.IsMCS tw.M) {kv : Option (VarSymb × VarType)} {e : VarSymb}
    {E : VarType} {cv cw : ℕ} {cls : List VarType} {imgs : ℕ → ℕ} {clt : List VarType}
    {imgt : ℕ → ℕ} (h : RetAtB hS b hb tv tw kv (some (e, E)) cv cw cls imgs clt imgt) :
    RetInvXB hS b hb tv tw cls imgs clt imgt e E cw := by
  rcases kv with _ | ⟨x, X⟩
  · exact h
  · obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, he, hcxv, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyWD_replX]; exact hΦ)
    refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr, ⟨?_⟩⟩
    refine Proof.retxD_forgetC_node hS ((ctxOf_le_of_suffix ht).ref he) _ _
      (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB b hb _)).2
      (Term.eta (.root (.free cv)) X hcxw) _ (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    rw [WFF.mono_bodyRepl ((ctxOf_le_of_suffix ht).diaIn e), Term.mono_eta]

/-- The counit's body over a witness's view, read at the witness child: `ψ` of the committed
    roots' items and the carrier's image along the witness arrow, necessarily. -/
theorem liftBodyX_counitBodyC {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) {C : VarType} {c₀ : Ann C}
    (bd : Term σ ((ctxOf clt).diaIn x).boxIn C c₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (bcT cls) C)) 1) :
    liftBodyX hs himgt hx hcx (counitBodyC bd ψ) =
      WFF.box (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2)
          (Term.subst (arrowXIdx imgt x cx) (arrowXS σ (ctxOf lv) imgt x cx).box
            (Subst.ok_box (ok_arrowXS himgt hx hcx))
            (Subst.coh_box (ok_arrowXS himgt hx hcx) (coh_arrowXS himgt hx hcx)) bd)) ψ) := by
  unfold liftBodyX counitBodyC
  simp only [WFF.subst]
  rw [WFF.subst_holeAt]
  refine congrArg WFF.box (WFF.holeAt_congr _ (sig_pair ?_ ?_) ψ)
  · exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ (by
      change Subst.set _ _ _ (.root (.bnd 0)) = _
      exact Subst.set_root _ _ _))
  · rw [Term.subst_mono]
    refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) bd
    obtain ⟨u, rfl, hu⟩ := boxIn_item' hv
    change SubE.Sim T ((Subst.at _ u).unbox) ((Subst.at _ u).unbox)
    rw [Subst.at_set_of_rt_ne _ _ (Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).rootFresh (le_refl 0)) hu)]
    exact .refl _

/-- ⭐**The counit's tail body holds at the witness child**: read there, it is `□K(⟨u, u⟩)` for
    the carrier's image `u` along the witness arrow. -/
theorem mem_liftBodyX_counitBodyC_tail {tv : NodeSt σ} (hv : Theory.IsMCS tv.M)
    {cls clt : List VarType} (hs : cls <:+ tv.l) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf tv.l) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf tv.l).ref (.root (.free cx)) = some X) {A U : VarType} {c₀ : Ann A}
    (bd : Term σ ((ctxOf clt).diaIn x).boxIn A c₀) {b : Ann A}
    (bdk : Term σ (ctxOf cls).boxIn A b)
    (hbd : (⟨_, Term.subst (arrowXIdx imgt x cx) (arrowXS σ (ctxOf tv.l) imgt x cx).box
        (Subst.ok_box (ok_arrowXS himgt hx hcx))
        (Subst.coh_box (ok_arrowXS himgt hx hcx) (coh_arrowXS himgt hx hcx))
        bd⟩ : Σ e, Term σ (ctxOf tv.l).boxIn A e) =
      ⟨_, Term.mono (ctxOf_le_of_suffix hs).boxIn bdk⟩)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A U)) 1) :
    liftBodyX hs himgt hx hcx (counitBodyC bd (pack2 cls A (tailBody bdk H))) ∈ tv.M := by
  rw [liftBodyX_counitBodyC]
  exact mem_box_counit_tail hv hs _ bdk hbd H

/-- ⭐⭐**Row 2 at a node**: along an arrow `k → s` in the extent of `s`'s witness `y`, with the
    invariant along `y`, a carrier `◇_y□bd` that comes back as `t` at `s` has
    `K(⟨bdk sent home, t⟩)` at `s` for every test formula `H` (`ret_counitC` along `y`). -/
theorem back_tailX {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hk : Theory.IsMCS tk.M)
    (hs : Theory.IsMCS ts.M) {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {y : VarSymb}
    {Y : VarType} {cx : ℕ} (h : RetInvX hS tk ts cls imgs clt imgt y Y cx)
    (hcs : cls <:+ tk.l) (himgs : ImgOk cls (ctxOf ts.l) imgs) (ht : clt <:+ ts.l)
    (himgt : ImgOk clt (ctxOf tk.l) imgt) (hy : (ctxOf clt).ref y = some (.VTypeDia Y))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some Y) {A U : VarType} {c₀ : Ann A}
    (bd : Term σ ((ctxOf clt).diaIn y).boxIn A c₀) {b : Ann A}
    (bdk : Term σ (ctxOf cls).boxIn A b)
    (hbd : (⟨_, Term.subst (arrowXIdx imgt y cx) (arrowXS σ (ctxOf tk.l) imgt y cx).box
        (Subst.ok_box (ok_arrowXS himgt hy hcx))
        (Subst.coh_box (ok_arrowXS himgt hy hcx) (coh_arrowXS himgt hy hcx))
        bd⟩ : Σ e, Term σ (ctxOf tk.l).boxIn A e) =
      ⟨_, Term.mono (ctxOf_le_of_suffix hcs).boxIn bdk⟩)
    {a : Ann A} (t : Term σ (ctxOf ts.l) A a)
    (hback : WFF.back hS .pos (Term.diatm y ⟨Y, (ctxOf_le_of_suffix ht).ref hy⟩ (Term.boxtm
      (Term.mono ((ctxOf_le_of_suffix ht).diaIn y).boxIn bd))) t ∈ ts.M)
    (H : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A U)) 1) :
    WFF.holeAt Ctx.NoSlots.slots (Term.pair (Term.subst (arrowIdx imgs) (arrowS σ (ctxOf ts.l) imgs)
      (ok_arrowS himgs) (coh_arrowS himgs) bdk) t) (tailK H) ∈ ts.M := by
  obtain ⟨_, _, _, _, _, _, hinv⟩ := h
  have hr := hinv _ (mem_liftBodyX_counitBodyC_tail hk hcs himgt hy hcx bd bdk hbd H)
  rw [mono_counitBodyC ((ctxOf_le_of_suffix ht).diaIn y)] at hr
  have hc := hs.closed ⟨[_, _], fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hr
      · rw [List.mem_singleton.mp hy]; exact hback,
    ⟨Proof.ret_counitC hS (.pos y ⟨Y, (ctxOf_le_of_suffix ht).ref hy⟩)
      (tupImgT cls imgs himgs).2
      (Term.mono ((ctxOf_le_of_suffix ht).diaIn y).boxIn bd) t (pack2 cls A (tailBody bdk H))
      (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩
  rwa [holeRead_tupImgT_pack2, subst_tailBody himgs] at hc

/-! ## The limit: a `Back` atom's returns are interchangeable with its value -/

omit [ModalSys.NoFour] in
/-- ⭐`K` at a pair, for the packed test formula of a slot formula `χ`, makes the pair's terms agree
    on `χ` (`all_elim` at the tuple of the roots, `holeAt_pair_tupW_packRoots`). -/
theorem interch_of_tailK {lj : List VarType} {M : Set (WFF σ (ctxOf lj) 0)}
    (hM : Theory.IsMCS M) {A : VarType} {a a' : Ann A} (v : Term σ (ctxOf lj) A a)
    (w : Term σ (ctxOf lj) A a') (χ : WFF σ ((ctxOf lj).insert (.bnd 0) A) 1)
    (hK : WFF.holeAt Ctx.NoSlots.slots (Term.pair v w) (tailK (packRoots lj χ)) ∈ M) :
    WFF.instantiate Ctx.NoSlots.slots v χ ∈ M ↔ WFF.instantiate Ctx.NoSlots.slots w χ ∈ M := by
  rw [holeAt_tailK] at hK
  have hinst := hM.closed ⟨[_], fun _ h => by rw [List.mem_singleton.mp h]; exact hK,
    ⟨Proof.all_elim (tyT lj) (tupW lj).2 (Proof.lookup List.mem_cons_self)⟩⟩
  change WFF.and (WFF.imp (WFF.instantiate _ _ (tailAt _ _)) (WFF.instantiate _ _ (tailAt _ _)))
    (WFF.imp (WFF.instantiate _ _ (tailAt _ _)) (WFF.instantiate _ _ (tailAt _ _))) ∈ M at hinst
  rw [instantiate_tailAt, instantiate_tailAt, holeAt_pair_tupW_packRoots,
    holeAt_pair_tupW_packRoots] at hinst
  obtain ⟨h₁, h₂⟩ := hM.and_mem_iff.mp hinst
  exact ⟨hM.imp_mem_iff.mp h₁, hM.imp_mem_iff.mp h₂⟩

section Limit

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐⭐**Row 1 at the limit** (`BData.backRel`): along an edge `s → k`, a `Back` carrier `□□bd`
    of `s` read out at `k` and home again is interchangeable with the atom's value at every
    stage both reach — the invariant of the way home `k → s` (`lretAt`), reduced to the plain one
    (`RetAt.toRetInv`), gives the tail formula of each packed test formula (`back_tail`). -/
theorem lbackRel {s k : LW C.toFairChain} (h : LR C.toFairChain s k) {i : ℕ} {A : VarType}
    {a₀ : Ann A} (bd : Term σ (ctxOf (lat s i)).boxIn.boxIn A a₀) {a : Ann A}
    (t : Term σ (ctxOf (lat s i)) A a)
    (hmem : WFF.back hS .nec (Term.boxtm (Term.boxtm bd)) t ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M) :
    Canon.DTerm.Rel (S := (nodeWorld C.toFairChain s.1 s.2).sys)
      (T := (nodeWorld C.toFairChain s.1 s.2).T)
      ⟨lstg C.toFairChain k s (lstg C.toFairChain s k i), _,
        Term.subst (arrowIdx (limg C.toFairChain k s)) (arrowS σ _ (limg C.toFairChain k s))
          (ok_arrowS (limgOk C.toFairChain h.symm (lstg C.toFairChain s k i)))
          (coh_arrowS (limgOk C.toFairChain h.symm (lstg C.toFairChain s k i)))
          (Term.subst (arrowIdx (limg C.toFairChain s k))
            (arrowS σ _ (limg C.toFairChain s k)).box
            (Subst.ok_box (ok_arrowS (limgOk C.toFairChain h i)))
            (Subst.coh_box (ok_arrowS (limgOk C.toFairChain h i))
              (coh_arrowS (limgOk C.toFairChain h i))) bd)⟩
      ⟨i, a, t⟩ := by
  classical
  obtain ⟨cls, imgs, clt, imgt, hJs, hJag, his, hiag, hret⟩ :=
    lretAt C h.symm (lstg C.toFairChain s k i) i le_rfl
  have hsp := (lstg_spec C.toFairChain h i).1
  have hkp := (lstg_spec C.toFairChain h.symm (lstg C.toFairChain s k i)).1
  have hii : i ≤ lstg C.toFairChain k s (lstg C.toFairChain s k i) := by omega
  have hsl : (C.net (birth C.toFairChain s.2 +
      lstg C.toFairChain k s (lstg C.toFairChain s k i))).Live s.1 :=
    live_birth C.toFairChain s.2 (Nat.le_add_right _ _)
  have hkl : (C.net (birth C.toFairChain s.2 +
      lstg C.toFairChain k s (lstg C.toFairChain s k i))).Live k.1 :=
    live_birth C.toFairChain k.2 (by omega)
  have hsM := (C.good _).mcs s.1 hsl
  have hkM := (C.good _).mcs k.1 hkl
  have hinv := RetAt.toRetInv hsM hret
  obtain ⟨hcs, himgs, ht, himgt, -⟩ := id hinv
  intro j hj hj' χ
  have hK := back_tail hkM hsM hinv hcs himgs ht himgt
    (Term.mono (ctxOf_le_of_suffix his).boxIn.boxIn bd)
    (Term.mono (ctxOf_le_of_suffix hJs).boxIn
      (Term.subst (arrowIdx (limg C.toFairChain s k))
            (arrowS σ _ (limg C.toFairChain s k)).box
            (Subst.ok_box (ok_arrowS (limgOk C.toFairChain h i)))
            (Subst.coh_box (ok_arrowS (limgOk C.toFairChain h i))
              (coh_arrowS (limgOk C.toFairChain h i))) bd))
    ?hbd (Term.mono ((nodeWorld C.toFairChain s.1 s.2).le hii) t) ?hback
    (packRoots (lat s j) χ)
  case hbd =>
    have hok := (himgt.suffix his).congr hiag
    rw [Term.subst_mono, Term.mono_mono, Term.mono_subst]
    refine (Term.subst_congr (ι' := arrowIdx (limg C.toFairChain s k)) _ _ _
      (Subst.ok_box (ok_arrowS hok)) _ (Subst.coh_box (ok_arrowS hok) (coh_arrowS hok))
      (Subst.sim_box (sim_arrowS hiag)) bd).trans (Term.subst_congr _ _ _ _ _ _ ?_ bd).symm
    rw [← arrowS_mono (ctxOf_le_of_suffix (hJs.trans hcs))]
    exact Subst.sim_box_mono _ _
  case hback =>
    have hm := (nodeWorld C.toFairChain s.1 s.2).sub hii _ hmem
    rw [Term.mono_mono]
    exact hm
  have hKj := (nodeWorld C.toFairChain s.1 s.2).sub hj _ hK
  rw [WFF.mono_holeAt _ _ Ctx.NoSlots.slots] at hKj
  refine interch_of_tailK ((nodeWorld C.toFairChain s.1 s.2).mcs j) _ _ χ ?_
  refine (congrArg (· ∈ _) (WFF.holeAt_congr _ (sig_pair ?_ ?_) _)).mp hKj
  · refine sig_mono _ ?_
    rw [Term.subst_mono]
    exact Term.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
  · rw [Term.mono_mono]

/-- ⭐⭐**Row 2 at the limit** (`BData.backRelX`): along an edge `s → k` of the extent of `s`'s
    witness `y`, a `Back` carrier `◇_y□bd` read out at `k` and home again is interchangeable
    with the atom's value — the way home's invariant along `y` (`RetAt.toRetInvX`) and
    `back_tailX`. -/
theorem lbackRelX {s k : LW C.toFairChain} {i : ℕ} {A : VarType} {a₀ : Ann A} {y : VarSymb}
    {Y : VarType} (hy : (ctxOf (lat s i)).ref y = some (.VTypeDia Y))
    (bd : Term σ ((ctxOf (lat s i)).diaIn y).boxIn A a₀) {a : Ann A}
    (t : Term σ (ctxOf (lat s i)) A a)
    (hmem : WFF.back hS .pos (Term.diatm y ⟨Y, hy⟩ (Term.boxtm bd)) t ∈
      ((C.net (birth C.toFairChain s.2 + i)).st s.1).M)
    (hk : lkd C.toFairChain s k = some (y, Y)) :
    Canon.DTerm.Rel (S := (nodeWorld C.toFairChain s.1 s.2).sys)
      (T := (nodeWorld C.toFairChain s.1 s.2).T)
      ⟨lstg C.toFairChain k s (lstg C.toFairChain s k i), _,
        Term.subst (arrowIdx (limg C.toFairChain k s)) (arrowS σ _ (limg C.toFairChain k s))
          (ok_arrowS (limgOk C.toFairChain (lkdR hk).symm (lstg C.toFairChain s k i)))
          (coh_arrowS (limgOk C.toFairChain (lkdR hk).symm (lstg C.toFairChain s k i)))
          (Term.subst (arrowXIdx (limg C.toFairChain s k) y (lcx C.toFairChain s k))
            (arrowXS σ _ (limg C.toFairChain s k) y (lcx C.toFairChain s k)).box
            (Subst.ok_box (ok_arrowXS (limgOk C.toFairChain (lkdR hk) i) hy
              (lhcx C.toFairChain hk i)))
            (Subst.coh_box (ok_arrowXS (limgOk C.toFairChain (lkdR hk) i) hy
              (lhcx C.toFairChain hk i))
              (coh_arrowXS (limgOk C.toFairChain (lkdR hk) i) hy (lhcx C.toFairChain hk i))) bd)⟩
      ⟨i, a, t⟩ := by
  classical
  have h := lkdR hk
  obtain ⟨cls, imgs, clt, imgt, hJs, hJag, his, hiag, hret⟩ :=
    lretAt C h.symm (lstg C.toFairChain s k i) i le_rfl
  rw [hk] at hret
  have hsp := (lstg_spec C.toFairChain h i).1
  have hkp := (lstg_spec C.toFairChain h.symm (lstg C.toFairChain s k i)).1
  have hii : i ≤ lstg C.toFairChain k s (lstg C.toFairChain s k i) := by omega
  have hsl : (C.net (birth C.toFairChain s.2 +
      lstg C.toFairChain k s (lstg C.toFairChain s k i))).Live s.1 :=
    live_birth C.toFairChain s.2 (Nat.le_add_right _ _)
  have hkl : (C.net (birth C.toFairChain s.2 +
      lstg C.toFairChain k s (lstg C.toFairChain s k i))).Live k.1 :=
    live_birth C.toFairChain k.2 (by omega)
  have hsM := (C.good _).mcs s.1 hsl
  have hkM := (C.good _).mcs k.1 hkl
  have hinv := RetAt.toRetInvX hsM hret
  obtain ⟨hcs, himgs, ht, himgt, hy', hcx', -⟩ := id hinv
  intro j hj hj' χ
  have hK := back_tailX hkM hsM hinv hcs himgs ht himgt hy' hcx'
    (Term.mono ((ctxOf_le_of_suffix his).diaIn y).boxIn bd)
    (Term.mono (ctxOf_le_of_suffix hJs).boxIn
      (Term.subst (arrowXIdx (limg C.toFairChain s k) y (lcx C.toFairChain s k))
            (arrowXS σ _ (limg C.toFairChain s k) y (lcx C.toFairChain s k)).box
            (Subst.ok_box (ok_arrowXS (limgOk C.toFairChain (lkdR hk) i) hy
              (lhcx C.toFairChain hk i)))
            (Subst.coh_box (ok_arrowXS (limgOk C.toFairChain (lkdR hk) i) hy
              (lhcx C.toFairChain hk i))
              (coh_arrowXS (limgOk C.toFairChain (lkdR hk) i) hy (lhcx C.toFairChain hk i))) bd))
    ?hbd (Term.mono ((nodeWorld C.toFairChain s.1 s.2).le hii) t) ?hback
    (packRoots (lat s j) χ)
  case hbd =>
    have hok := (himgt.suffix his).congr hiag
    rw [Term.subst_mono, Term.mono_mono, Term.mono_subst]
    refine (Term.subst_congr (ι' := arrowXIdx (limg C.toFairChain s k) y (lcx C.toFairChain s k))
      _ _ _ (Subst.ok_box (ok_arrowXS hok hy hcx')) _
      (Subst.coh_box (ok_arrowXS hok hy hcx') (coh_arrowXS hok hy hcx'))
      (Subst.sim_box (sim_arrowXS hiag)) bd).trans (Term.subst_congr _ _ _ _ _ _ ?_ bd).symm
    rw [← arrowXS_mono (ctxOf_le_of_suffix (hJs.trans hcs))]
    exact Subst.sim_box_mono _ _
  case hback =>
    have hm := (nodeWorld C.toFairChain s.1 s.2).sub hii _ hmem
    rw [Term.mono_mono]
    exact hm
  have hKj := (nodeWorld C.toFairChain s.1 s.2).sub hj _ hK
  rw [WFF.mono_holeAt _ _ Ctx.NoSlots.slots] at hKj
  refine interch_of_tailK ((nodeWorld C.toFairChain s.1 s.2).mcs j) _ _ χ ?_
  refine (congrArg (· ∈ _) (WFF.holeAt_congr _ (sig_pair ?_ ?_) _)).mp hKj
  · refine sig_mono _ ?_
    rw [Term.subst_mono]
    exact Term.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
  · rw [Term.mono_mono]

/-- ⭐⭐**Strong B's canonical data**: the limit of a strong chain, its `Back` atoms'
    returns interchangeable with their values (`lbackRel`, `lbackRelX`). -/
noncomputable def bdataS : BData σ where
  W := LW C.toFairChain
  actual := ⟨[], 0, trivial⟩
  w s := nodeWorld C.toFairChain s.1 s.2
  R := LR C.toFairChain
  symm := LR.symm
  irrefl := LR.irrefl
  img := limg C.toFairChain
  stg := lstg C.toFairChain
  imgOk h i := limgOk C.toFairChain h i
  tr h i ψ hψ := ltr C.toFairChain h i ψ hψ
  ex s i ψ hψ := lex C.toFairChain s i ψ hψ
  lb := lbOfKd (lkd C.toFairChain)
  cx s t _ := lcx C.toFairChain s t
  lbR h := lkdR (lbOfKd_eq.mp h)
  lb_hcx h i := lhcx C.toFairChain (lbOfKd_eq.mp h) i
  lb_hxX h i X' h' := lhxX C.toFairChain (lbOfKd_eq.mp h) i X' h'
  lb_trX h i hx ψ hψ := ltrX C.toFairChain (lbOfKd_eq.mp h) i hx ψ hψ
  kd := lkd C.toFairChain
  kd_lb h := lbOfKd_eq.mpr h
  lb_kd h := lbOfKd_eq.mp h
  exX s i x X hx ψ hψ := lexX C.toFairChain s i x X hx ψ hψ
  unl h := lunl C.toFairChain h
  backRel _ _ _ _ _ bd _ t hmem _ hk := lbackRel C hk bd t hmem
  backRelX _ _ _ _ _ _ _ hy bd _ t hmem _ hk := lbackRelX C hy bd t hmem hk

end Limit

end BArrow

end V12M
