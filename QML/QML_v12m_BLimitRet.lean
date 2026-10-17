import QML.QML_v12m_BLimit
import QML.QML_v12m_BFairS

/-!
# QML v12m — strong B's limit: the returning-possibility invariant along an edge (T off)

Along an edge `v → w` of the limit, the network's invariant from `v` to `w` has one of four
forms, fixed by two pieces of the edge's data (docs §11.20, E1 step 3):
* `lkd v w`, the source's witness: its extent holds the edge, so it comes back as a possible part,
  with content `lcx v w` at `w`;
* `lkd w v`, the target's leg witness: the way back lies in its extent, with content `lcx w v` at
  `v`.

`RetAt` is that case split (`RetInv`, `RetInvW`, `RetInvX`, `RetInvWD`), and a child's `RetData` is
`RetAt` both ways (`RetData.retAt_fwd`, `RetData.retAt_back`).

* `RetAt.restrict`: shrink the target's committed list to a suffix and change the images to
  agreeing ones (a body over fewer roots is weakened into one over more).
* ⭐`lretAt`: at the round where the source's stage `J` is committed, after the target's stage `i`
  was, the edge carries `RetAt` with lists containing both stages and images agreeing with the
  limit's.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The invariant along an edge, by its witnesses -/

/-- ⭐**The returning-possibility invariant from `tv` to `tw`**, by the source's witness `kv` (a
    possible part, content `cv` at the target) and the target's leg witness `kw` (content `cw` at
    the source). -/
def RetAt (hS : ModalSys.BStrong = true) (tv tw : NodeSt σ)
    (kv kw : Option (VarSymb × VarType)) (cv cw : ℕ) (cls : List VarType) (imgs : ℕ → ℕ)
    (clt : List VarType) (imgt : ℕ → ℕ) : Prop :=
  match kv, kw with
  | none, none => RetInv hS tv tw cls imgs clt imgt
  | some (x, X), none => RetInvW hS tv tw cls imgs clt imgt x X cv
  | none, some (e, E) => RetInvX hS tv tw cls imgs clt imgt e E cw
  | some (x, X), some (e, E) => RetInvWD hS tv tw cls imgs clt imgt x X cv e E cw

/-- A child's forward arrow carries `RetAt`, by its kind and back kind. -/
theorem RetData.retAt_fwd {hS : ModalSys.BStrong = true} {tp tk : NodeSt σ}
    {kind bkd : Option (VarSymb × VarType)} {cx bcx : ℕ} {fcl : List VarType} {fimg : ℕ → ℕ}
    {bcl : List VarType} {bimg : ℕ → ℕ} (h : RetData hS tp tk kind bkd cx bcx fcl fimg bcl bimg) :
    RetAt hS tp tk kind bkd cx bcx fcl fimg bcl bimg := by
  rcases kind with _ | ⟨x, X⟩ <;> rcases bkd with _ | ⟨e, E⟩ <;> exact h.1

/-- A child's way home carries `RetAt`, its witnesses swapped. -/
theorem RetData.retAt_back {hS : ModalSys.BStrong = true} {tp tk : NodeSt σ}
    {kind bkd : Option (VarSymb × VarType)} {cx bcx : ℕ} {fcl : List VarType} {fimg : ℕ → ℕ}
    {bcl : List VarType} {bimg : ℕ → ℕ} (h : RetData hS tp tk kind bkd cx bcx fcl fimg bcl bimg) :
    RetAt hS tk tp bkd kind bcx cx bcl bimg fcl fimg := by
  rcases kind with _ | ⟨x, X⟩ <;> rcases bkd with _ | ⟨e, E⟩ <;> exact h.2

/-! ## Restricting the target's list -/

section Restrict

variable {lv cls clt clt' : List VarType} {imgt imgt' : ℕ → ℕ}

omit [ModalSys.NoFour] in
/-- Agreeing images send an item alike. -/
theorem sim_itemImg {T : VarType} {u : VarSymb} {U : VarType} (hu : (ctxOf clt').ref u = some U)
    (hag : ∀ r < clt'.length, imgt r = imgt' r) :
    SubE.Sim (σ := σ) (Δ := ctxOf lv) T (.ren (itemAt (imgRoot imgt u.rt) u))
      (.ren (itemAt (imgRoot imgt' u.rt) u)) := by
  obtain ⟨r, hr, hlt, _⟩ := ref_rt hu
  rw [hr, imgRoot, imgRoot, hag r hlt]
  exact .refl _

/-- A body over fewer of the target's roots, weakened, reads as the body itself. -/
theorem liftBody_restrict (hs : cls <:+ lv) (himgt : ImgOk clt (ctxOf lv) imgt)
    (himgt' : ImgOk clt' (ctxOf lv) imgt') (hsuf : clt' <:+ clt)
    (hag : ∀ r < clt'.length, imgt r = imgt' r) (Φ : WFF σ (bodyCtx cls clt') 1) :
    liftBody hs himgt (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) =
      liftBody hs himgt' Φ := by
  unfold liftBody
  rw [WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T hlp hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.set_root, Subst.set_root]
    exact .refl _
  · obtain ⟨u, rfl, hu⟩ := body_item hlp hv hvr
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact sim_itemImg hu hag

theorem liftBodyW_restrict (hs : cls <:+ lv) (himgt : ImgOk clt (ctxOf lv) imgt)
    (himgt' : ImgOk clt' (ctxOf lv) imgt') (hsuf : clt' <:+ clt)
    (hag : ∀ r < clt'.length, imgt r = imgt' r) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtxW cls clt' X) 1) :
    liftBodyW hs himgt hx (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) =
      liftBodyW hs himgt' hx Φ := by
  unfold liftBodyW
  rw [WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T hlp hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.set_root, Subst.set_root]
    exact .refl _
  · obtain ⟨u, rfl, hu⟩ := bodyW_item hv hvr
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact sim_itemImg hu hag

theorem liftBodyX_restrict (hs : cls <:+ lv) (himgt : ImgOk clt (ctxOf lv) imgt)
    (himgt' : ImgOk clt' (ctxOf lv) imgt') (hsuf : clt' <:+ clt)
    (hag : ∀ r < clt'.length, imgt r = imgt' r) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) (hx' : (ctxOf clt').ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : (ctxOf lv).ref (.root (.free cx)) = some X)
    (Φ : WFF σ (bodyCtxX cls clt' x) 1) :
    liftBodyX hs himgt hx hcx
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ) =
      liftBodyX hs himgt' hx' hcx Φ := by
  unfold liftBodyX
  rw [WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T hlp hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.set_root, Subst.set_root]
    exact .refl _
  · rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    rcases bodyX_item hv hvr with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
    · exact sim_itemImg hu hag
    · exact .refl _

theorem liftBodyWD_restrict (hs : cls <:+ lv) (himgt : ImgOk clt (ctxOf lv) imgt)
    (himgt' : ImgOk clt' (ctxOf lv) imgt') (hsuf : clt' <:+ clt)
    (hag : ∀ r < clt'.length, imgt r = imgt' r) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) (he' : (ctxOf clt').ref e = some (.VTypeDia E))
    {cxv : ℕ} (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E)
    (Φ : WFF σ (bodyCtxWD cls clt' e X) 1) :
    liftBodyWD hs himgt hx he hcxv
        (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn e).insert (.bnd 0) _) Φ) =
      liftBodyWD hs himgt' hx he' hcxv Φ := by
  unfold liftBodyWD
  rw [WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T hlp hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.set_root, Subst.set_root]
    exact .refl _
  · rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    rcases bodyWD_item hv hvr with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
    · exact sim_itemImg hu hag
    · exact .refl _

end Restrict

section RestrictInv

variable {hS : ModalSys.BStrong = true} {tv tw : NodeSt σ} {cls clt clt' : List VarType}
  {imgs imgs' imgt imgt' : ℕ → ℕ}

theorem RetInv.restrict (h : RetInv hS tv tw cls imgs clt imgt) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r) :
    RetInv hS tv tw cls imgs' clt' imgt' := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  have himgt' : ImgOk clt' (ctxOf tv.l) imgt' := (himgt.suffix hsuf).congr hagt
  have himgs' : ImgOk cls (ctxOf tw.l) imgs' := himgs.congr hags
  refine ⟨hs, himgs', hsuf.trans ht, himgt', fun Φ hΦ => ?_⟩
  have h1 := hinv (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) (by
    rw [liftBody_restrict hs himgt himgt' hsuf hagt]
    exact hΦ)
  rw [WFF.mono_mono, WFF.ret_congr hS (tupImgT_congr cls himgs himgs' hags) rfl] at h1
  exact h1

theorem RetInvW.restrict {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvW hS tv tw cls imgs clt imgt x X cx) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r) :
    RetInvW hS tv tw cls imgs' clt' imgt' x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have himgt' : ImgOk clt' (ctxOf tv.l) imgt' := (himgt.suffix hsuf).congr hagt
  have himgs' : ImgOk cls (ctxOf tw.l) imgs' := himgs.congr hags
  refine ⟨hs, himgs', hsuf.trans ht, himgt', hx, hcx, fun Φ hΦ => ?_⟩
  have h1 := hinv (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) (by
    rw [liftBodyW_restrict hs himgt himgt' hsuf hagt]
    exact hΦ)
  rw [WFF.mono_mono, WFF.retS_congr hS _
    (sig_pair (tupImgT_congr cls himgs himgs' hags) rfl) rfl] at h1
  exact h1

theorem RetInvX.restrict {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvX hS tv tw cls imgs clt imgt x X cx) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r)
    (hx' : (ctxOf clt').ref x = some (.VTypeDia X)) :
    RetInvX hS tv tw cls imgs' clt' imgt' x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have himgt' : ImgOk clt' (ctxOf tv.l) imgt' := (himgt.suffix hsuf).congr hagt
  have himgs' : ImgOk cls (ctxOf tw.l) imgs' := himgs.congr hags
  refine ⟨hs, himgs', hsuf.trans ht, himgt', hx', hcx, fun Φ hΦ => ?_⟩
  have h1 := hinv (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ) (by
    rw [liftBodyX_restrict hs himgt himgt' hsuf hagt hx hx' hcx]
    exact hΦ)
  change WFF.retxS hS x _ (.box _) _ (WFF.mono _ (WFF.mono _ Φ)) ∈ tw.M at h1
  rw [WFF.mono_mono, WFF.retxS_congr hS x _ (.box _) (tupImgT_congr cls himgs himgs' hags)
    rfl] at h1
  exact h1

theorem RetInvWD.restrict {x : VarSymb} {X : VarType} {cxw : ℕ} {e : VarSymb} {E : VarType}
    {cxv : ℕ} (h : RetInvWD hS tv tw cls imgs clt imgt x X cxw e E cxv) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r)
    (he' : (ctxOf clt').ref e = some (.VTypeDia E)) :
    RetInvWD hS tv tw cls imgs' clt' imgt' x X cxw e E cxv := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
  have himgt' : ImgOk clt' (ctxOf tv.l) imgt' := (himgt.suffix hsuf).congr hagt
  have himgs' : ImgOk cls (ctxOf tw.l) imgs' := himgs.congr hags
  refine ⟨hs, himgs', hsuf.trans ht, himgt', hx, hcxw, he', hcxv, fun Φ hΦ => ?_⟩
  have h1 := hinv (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn e).insert (.bnd 0) _) Φ) (by
    rw [liftBodyWD_restrict hs himgt himgt' hsuf hagt hx he he' hcxv]
    exact hΦ)
  have hv : (⟨_, Term.pair (tupImgT cls imgs himgs).2 (Term.eta (.root (.free cxw)) X hcxw)⟩ :
      Σ a, Term σ (ctxOf tw.l) (.VTypeProd (bcT cls) X) a) =
      ⟨_, Term.pair (tupImgT cls imgs' himgs').2 (Term.eta (.root (.free cxw)) X hcxw)⟩ := by
    rw [tupImgT_congr cls himgs himgs' hags]
  change WFF.retxS hS e _ (.wit _ _) _ (WFF.mono _ (WFF.mono _ Φ)) ∈ tw.M at h1
  rw [WFF.mono_mono, WFF.retxS_congr hS e _ (.wit _ _) hv rfl] at h1
  exact h1

/-- ⭐**Restricting `RetAt`** to a suffix of the target's committed list, with agreeing images; the
    target's leg witness must stay among the list's variables. -/
theorem RetAt.restrict {kv kw : Option (VarSymb × VarType)} {cv cw : ℕ}
    (h : RetAt hS tv tw kv kw cv cw cls imgs clt imgt) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r)
    (hw : ∀ e E, kw = some (e, E) → (ctxOf clt').ref e = some (.VTypeDia E)) :
    RetAt hS tv tw kv kw cv cw cls imgs' clt' imgt' := by
  rcases kv with _ | ⟨x, X⟩ <;> rcases kw with _ | ⟨e, E⟩
  · exact RetInv.restrict h hsuf hagt hags
  · exact RetInvX.restrict h hsuf hagt hags (hw e E rfl)
  · exact RetInvW.restrict h hsuf hagt hags
  · exact RetInvWD.restrict h hsuf hagt hags (hw e E rfl)

end RestrictInv

/-! ## The invariant along an edge, with companions -/

/-- ⭐**`RetAt` with the tuple's companions** (`RetInvB` and its forms); `RetAt` at `false`. -/
def RetAtB (hS : ModalSys.BStrong = true) (b : Bool) (hb : ModalSys.T = b) (tv tw : NodeSt σ)
    (kv kw : Option (VarSymb × VarType)) (cv cw : ℕ) (cls : List VarType) (imgs : ℕ → ℕ)
    (clt : List VarType) (imgt : ℕ → ℕ) : Prop :=
  match kv, kw with
  | none, none => RetInvB hS b hb tv tw cls imgs clt imgt
  | some (x, X), none => RetInvWB hS b hb tv tw cls imgs clt imgt x X cv
  | none, some (e, E) => RetInvXB hS b hb tv tw cls imgs clt imgt e E cw
  | some (x, X), some (e, E) => RetInvWDB hS b hb tv tw cls imgs clt imgt x X cv e E cw

/-- A child's forward arrow carries `RetAtB`. -/
theorem RetDataB.retAtB_fwd {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tp tk : NodeSt σ} {kind bkd : Option (VarSymb × VarType)} {cx bcx : ℕ}
    {fcl : List VarType} {fimg : ℕ → ℕ} {bcl : List VarType} {bimg : ℕ → ℕ}
    (h : RetDataB hS b hb tp tk kind bkd cx bcx fcl fimg bcl bimg) :
    RetAtB hS b hb tp tk kind bkd cx bcx fcl fimg bcl bimg := by
  rcases kind with _ | ⟨x, X⟩ <;> rcases bkd with _ | ⟨e, E⟩ <;> exact h.1

/-- A child's way home carries `RetAtB`, its witnesses swapped. -/
theorem RetDataB.retAtB_back {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tp tk : NodeSt σ} {kind bkd : Option (VarSymb × VarType)} {cx bcx : ℕ}
    {fcl : List VarType} {fimg : ℕ → ℕ} {bcl : List VarType} {bimg : ℕ → ℕ}
    (h : RetDataB hS b hb tp tk kind bkd cx bcx fcl fimg bcl bimg) :
    RetAtB hS b hb tk tp bkd kind bcx cx bcl bimg fcl fimg := by
  rcases kind with _ | ⟨x, X⟩ <;> rcases bkd with _ | ⟨e, E⟩ <;> exact h.2

/-- Forgetting the companions: `RetAt`. -/
theorem RetAtB.forget {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw : NodeSt σ} {kv kw : Option (VarSymb × VarType)} {cv cw : ℕ} {cls clt : List VarType}
    {imgs imgt : ℕ → ℕ} (hM : Theory.IsMCS tw.M)
    (h : RetAtB hS b hb tv tw kv kw cv cw cls imgs clt imgt) :
    RetAt hS tv tw kv kw cv cw cls imgs clt imgt := by
  rcases kv with _ | ⟨x, X⟩ <;> rcases kw with _ | ⟨e, E⟩
  · exact RetInvB.forget hM h
  · exact RetInvXB.forget hM h
  · exact RetInvWB.forget hM h
  · exact RetInvWDB.forget hM h

/-- Agreeing images give one tuple with companions. -/
theorem tupCompsImg_congr_eq {Δ : Ctx} (cls : List VarType) {img img' : ℕ → ℕ}
    (himg : ImgOk cls Δ img) (himg' : ImgOk cls Δ img')
    (hag : ∀ r, r < cls.length → img r = img' r) :
    ∀ (cs : List (List Step)) (hc : (bcT cls).CompOk cs),
      tupCompsImg (σ := σ) cls img himg cs hc = tupCompsImg cls img' himg' cs hc
  | [], _ => tupImgT_congr cls himg himg' hag
  | _ :: ps, hc => sig_pair (tupCompsImg_congr_eq cls himg himg' hag ps hc.tail)
      (Term.subst_congr _ _ _ _ _ _ (sim_arrowS hag) _)

theorem tupCompsImg_congr {Δ : Ctx} (cls : List VarType) {img img' : ℕ → ℕ}
    (himg : ImgOk cls Δ img) (himg' : ImgOk cls Δ img')
    (hag : ∀ r, r < cls.length → img r = img' r) (cs : List (List Step))
    (hc : (bcT cls).CompOk cs) :
    (⟨_, (tupCompsImg (σ := σ) cls img himg cs hc).2⟩ :
      Σ a, Term σ Δ ((bcT cls).compsFlat cs) a) = ⟨_, (tupCompsImg cls img' himg' cs hc).2⟩ := by
  rw [tupCompsImg_congr_eq cls himg himg' hag cs hc]

section RestrictInvB

variable {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b} {tv tw : NodeSt σ}
  {cls clt clt' : List VarType} {imgs imgs' imgt imgt' : ℕ → ℕ}

theorem RetInvB.restrict (h : RetInvB hS b hb tv tw cls imgs clt imgt) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r) :
    RetInvB hS b hb tv tw cls imgs' clt' imgt' := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  have himgt' : ImgOk clt' (ctxOf tv.l) imgt' := (himgt.suffix hsuf).congr hagt
  have himgs' : ImgOk cls (ctxOf tw.l) imgs' := himgs.congr hags
  refine ⟨hs, himgs', hsuf.trans ht, himgt', fun Φ hΦ => ?_⟩
  have h1 := hinv (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) (by
    rw [liftBody_restrict hs himgt himgt' hsuf hagt]
    exact hΦ)
  rw [WFF.mono_mono, WFF.retS_congr hS _
    (tupCompsImg_congr cls himgs himgs' hags _ _) rfl] at h1
  exact h1

theorem RetInvWB.restrict {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvWB hS b hb tv tw cls imgs clt imgt x X cx) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r) :
    RetInvWB hS b hb tv tw cls imgs' clt' imgt' x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have himgt' : ImgOk clt' (ctxOf tv.l) imgt' := (himgt.suffix hsuf).congr hagt
  have himgs' : ImgOk cls (ctxOf tw.l) imgs' := himgs.congr hags
  refine ⟨hs, himgs', hsuf.trans ht, himgt', hx, hcx, fun Φ hΦ => ?_⟩
  have h1 := hinv (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.insert (.bnd 0) _) Φ) (by
    rw [liftBodyW_restrict hs himgt himgt' hsuf hagt]
    exact hΦ)
  rw [WFF.mono_mono, WFF.retS_congr hS _
    (sig_pair (tupCompsImg_congr cls himgs himgs' hags _ _) rfl) rfl] at h1
  exact h1

theorem RetInvXB.restrict {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvXB hS b hb tv tw cls imgs clt imgt x X cx) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r)
    (hx' : (ctxOf clt').ref x = some (.VTypeDia X)) :
    RetInvXB hS b hb tv tw cls imgs' clt' imgt' x X cx := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  have himgt' : ImgOk clt' (ctxOf tv.l) imgt' := (himgt.suffix hsuf).congr hagt
  have himgs' : ImgOk cls (ctxOf tw.l) imgs' := himgs.congr hags
  refine ⟨hs, himgs', hsuf.trans ht, himgt', hx', hcx, fun Φ hΦ => ?_⟩
  have h1 := hinv (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn x).insert (.bnd 0) _) Φ) (by
    rw [liftBodyX_restrict hs himgt himgt' hsuf hagt hx hx' hcx]
    exact hΦ)
  change WFF.retxS hS x _ (.nec _) _ (WFF.mono _ (WFF.mono _ Φ)) ∈ tw.M at h1
  rw [WFF.mono_mono, WFF.retxS_congr hS x _ (.nec _)
    (tupCompsImg_congr cls himgs himgs' hags _ _) rfl] at h1
  exact h1

theorem RetInvWDB.restrict {x : VarSymb} {X : VarType} {cxw : ℕ} {e : VarSymb} {E : VarType}
    {cxv : ℕ} (h : RetInvWDB hS b hb tv tw cls imgs clt imgt x X cxw e E cxv)
    (hsuf : clt' <:+ clt) (hagt : ∀ r < clt'.length, imgt r = imgt' r)
    (hags : ∀ r < cls.length, imgs r = imgs' r) (he' : (ctxOf clt').ref e = some (.VTypeDia E)) :
    RetInvWDB hS b hb tv tw cls imgs' clt' imgt' x X cxw e E cxv := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
  have himgt' : ImgOk clt' (ctxOf tv.l) imgt' := (himgt.suffix hsuf).congr hagt
  have himgs' : ImgOk cls (ctxOf tw.l) imgs' := himgs.congr hags
  refine ⟨hs, himgs', hsuf.trans ht, himgt', hx, hcxw, he', hcxv, fun Φ hΦ => ?_⟩
  have h1 := hinv (WFF.mono (((ctxOf_le_of_suffix hsuf).diaIn e).insert (.bnd 0) _) Φ) (by
    rw [liftBodyWD_restrict hs himgt himgt' hsuf hagt hx he he' hcxv]
    exact hΦ)
  change WFF.retxS hS e _ (.wit _ _) _ (WFF.mono _ (WFF.mono _ Φ)) ∈ tw.M at h1
  rw [WFF.mono_mono, WFF.retxS_congr hS e _ (.wit _ _)
    (sig_pair (tupCompsImg_congr cls himgs himgs' hags _ _) rfl) rfl] at h1
  exact h1

/-- ⭐**Restricting `RetAtB`**, as `RetAt.restrict`. -/
theorem RetAtB.restrict {kv kw : Option (VarSymb × VarType)} {cv cw : ℕ}
    (h : RetAtB hS b hb tv tw kv kw cv cw cls imgs clt imgt) (hsuf : clt' <:+ clt)
    (hagt : ∀ r < clt'.length, imgt r = imgt' r) (hags : ∀ r < cls.length, imgs r = imgs' r)
    (hw : ∀ e E, kw = some (e, E) → (ctxOf clt').ref e = some (.VTypeDia E)) :
    RetAtB hS b hb tv tw kv kw cv cw cls imgs' clt' imgt' := by
  rcases kv with _ | ⟨x, X⟩ <;> rcases kw with _ | ⟨e, E⟩
  · exact RetInvB.restrict h hsuf hagt hags
  · exact RetInvXB.restrict h hsuf hagt hags (hw e E rfl)
  · exact RetInvWB.restrict h hsuf hagt hags
  · exact RetInvWDB.restrict h hsuf hagt hags (hw e E rfl)

end RestrictInvB

/-! ## The invariant at the limit -/

section Limit

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐**The returning-possibility invariant along an edge of the limit**: at the round where the
    source's stage `J` is committed to the target, after the target's stage `i` was committed back,
    the edge carries `RetAt` by its witnesses (`lkd`, `lcx`), with committed lists containing both
    stages and images agreeing with the limit's there. -/
theorem lretAt {v w : LW C.toFairChain} (h : LR C.toFairChain v w) (J i : ℕ)
    (hJ : lstg C.toFairChain w v i ≤ J) :
    ∃ (cls : List VarType) (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ),
      lat v J <:+ cls ∧ (∀ r < (lat v J).length, imgs r = limg C.toFairChain v w r) ∧
      lat w i <:+ clt ∧ (∀ r < (lat w i).length, imgt r = limg C.toFairChain w v r) ∧
      RetAt hS ((C.net (birth C.toFairChain w.2 + lstg C.toFairChain v w J)).st v.1)
        ((C.net (birth C.toFairChain w.2 + lstg C.toFairChain v w J)).st w.1)
        (lkd C.toFairChain v w) (lkd C.toFairChain w v) (lcx C.toFairChain v w)
        (lcx C.toFairChain w v) cls imgs clt imgt := by
  classical
  set m := birth C.toFairChain w.2 + lstg C.toFairChain v w J with hm
  have hJm := (lstg_spec C.toFairChain h J).1
  have hi := (lstg_spec C.toFairChain h.symm i).1
  have hm' : birth C.toFairChain v.2 + lstg C.toFairChain w v i ≤
      birth C.toFairChain w.2 + lstg C.toFairChain v w J := by omega
  have hext := C.ext hm'
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · -- `w` is a child of `v`: the child's forward arrow.
    obtain ⟨hsuf, hag, -⟩ := fwd_at C.toFairChain hc J
    obtain ⟨hsuf', hag', -⟩ := back_at C.toFairChain hc i
    have hwm : (C.net (birth C.toFairChain w.2 + lstg C.toFairChain v w J)).Live w.1 :=
      live_birth C.toFairChain w.2 (Nat.le_add_right _ _)
    have hwm' : (C.net (birth C.toFairChain v.2 + lstg C.toFairChain w v i)).Live w.1 :=
      live_birth C.toFairChain w.2 (by omega)
    refine ⟨_, _, _, _, hsuf, hag, hsuf'.trans (hext.bcl _ hwm'), fun r hr =>
      (hext.bimg _ hwm' r (lt_of_lt_of_le hr hsuf'.length_le)).trans (hag' r hr), ?_⟩
    have hr := (C.goodS _).ret c v.1 (by rw [← hc]; exact hwm)
    unfold NetSt.RetOk at hr
    rw [← hc] at hr
    have hb : birth C.toFairChain w.2 ≤ m := Nat.le_add_right _ _
    have e1 : lkd C.toFairChain v w = (C.net m).kind w.1 := by
      rw [lkd, if_pos ⟨c, hc⟩, kind_at C.toFairChain w hb]
    have e2 : lkd C.toFairChain w v = (C.net m).bkind w.1 := by
      rw [lkd, if_neg (not_fwd_of_back hc), if_pos ⟨c, hc⟩, bkind_at C.toFairChain w hb]
    have e3 : lcx C.toFairChain v w = (C.net m).cx w.1 := by
      rw [lcx, if_pos ⟨c, hc⟩, cx_at C.toFairChain w hb]
    have e4 : lcx C.toFairChain w v = (C.net m).bcx w.1 := by
      rw [lcx, if_neg (not_fwd_of_back hc), bcx_at C.toFairChain w hb]
    rw [e1, e2, e3, e4]
    exact hr.retAt_fwd
  · -- `v` is a child of `w`: the child's way home.
    obtain ⟨hsuf, hag, -⟩ := back_at C.toFairChain hc J
    obtain ⟨hsuf', hag', -⟩ := fwd_at C.toFairChain hc i
    have hvm : (C.net (birth C.toFairChain w.2 + lstg C.toFairChain v w J)).Live v.1 :=
      live_birth C.toFairChain v.2 (by omega)
    have hvm' : (C.net (birth C.toFairChain v.2 + lstg C.toFairChain w v i)).Live v.1 :=
      live_birth C.toFairChain v.2 (Nat.le_add_right _ _)
    refine ⟨_, _, _, _, hsuf, hag, hsuf'.trans (hext.fcl _ hvm'), fun r hr =>
      (hext.fimg _ hvm' r (lt_of_lt_of_le hr hsuf'.length_le)).trans (hag' r hr), ?_⟩
    have hr := (C.goodS _).ret c w.1 (by rw [← hc]; exact hvm)
    unfold NetSt.RetOk at hr
    rw [← hc] at hr
    have hb : birth C.toFairChain v.2 ≤ m := by omega
    have e1 : lkd C.toFairChain v w = (C.net m).bkind v.1 := by
      rw [lkd, if_neg (not_fwd_of_back hc), if_pos ⟨c, hc⟩, bkind_at C.toFairChain v hb]
    have e2 : lkd C.toFairChain w v = (C.net m).kind v.1 := by
      rw [lkd, if_pos ⟨c, hc⟩, kind_at C.toFairChain v hb]
    have e3 : lcx C.toFairChain v w = (C.net m).bcx v.1 := by
      rw [lcx, if_neg (not_fwd_of_back hc), bcx_at C.toFairChain v hb]
    have e4 : lcx C.toFairChain w v = (C.net m).cx v.1 := by
      rw [lcx, if_pos ⟨c, hc⟩, cx_at C.toFairChain v hb]
    rw [e1, e2, e3, e4]
    exact hr.retAt_back

/-- ⭐**The invariant with companions along an edge of the limit**, as `lretAt`: `RetAtB` at
    the round where the source's stage `J` is committed to the target, after the target's stage
    `i` was committed back. -/
theorem lretAtB {v w : LW C.toFairChain} (h : LR C.toFairChain v w) (J i : ℕ)
    (hJ : lstg C.toFairChain w v i ≤ J) :
    ∃ (cls : List VarType) (imgs : ℕ → ℕ) (clt : List VarType) (imgt : ℕ → ℕ),
      lat v J <:+ cls ∧ (∀ r < (lat v J).length, imgs r = limg C.toFairChain v w r) ∧
      lat w i <:+ clt ∧ (∀ r < (lat w i).length, imgt r = limg C.toFairChain w v r) ∧
      RetAtB hS ModalSys.T rfl ((C.net (birth C.toFairChain w.2 + lstg C.toFairChain v w J)).st v.1)
        ((C.net (birth C.toFairChain w.2 + lstg C.toFairChain v w J)).st w.1)
        (lkd C.toFairChain v w) (lkd C.toFairChain w v) (lcx C.toFairChain v w)
        (lcx C.toFairChain w v) cls imgs clt imgt := by
  classical
  set m := birth C.toFairChain w.2 + lstg C.toFairChain v w J with hm
  have hJm := (lstg_spec C.toFairChain h J).1
  have hi := (lstg_spec C.toFairChain h.symm i).1
  have hm' : birth C.toFairChain v.2 + lstg C.toFairChain w v i ≤
      birth C.toFairChain w.2 + lstg C.toFairChain v w J := by omega
  have hext := C.ext hm'
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · -- `w` is a child of `v`: the child's forward arrow.
    obtain ⟨hsuf, hag, -⟩ := fwd_at C.toFairChain hc J
    obtain ⟨hsuf', hag', -⟩ := back_at C.toFairChain hc i
    have hwm : (C.net (birth C.toFairChain w.2 + lstg C.toFairChain v w J)).Live w.1 :=
      live_birth C.toFairChain w.2 (Nat.le_add_right _ _)
    have hwm' : (C.net (birth C.toFairChain v.2 + lstg C.toFairChain w v i)).Live w.1 :=
      live_birth C.toFairChain w.2 (by omega)
    refine ⟨_, _, _, _, hsuf, hag, hsuf'.trans (hext.bcl _ hwm'), fun r hr =>
      (hext.bimg _ hwm' r (lt_of_lt_of_le hr hsuf'.length_le)).trans (hag' r hr), ?_⟩
    have hr := (C.goodS _).retB c v.1 (by rw [← hc]; exact hwm)
    unfold NetSt.RetOkB at hr
    rw [← hc] at hr
    have hb : birth C.toFairChain w.2 ≤ m := Nat.le_add_right _ _
    have e1 : lkd C.toFairChain v w = (C.net m).kind w.1 := by
      rw [lkd, if_pos ⟨c, hc⟩, kind_at C.toFairChain w hb]
    have e2 : lkd C.toFairChain w v = (C.net m).bkind w.1 := by
      rw [lkd, if_neg (not_fwd_of_back hc), if_pos ⟨c, hc⟩, bkind_at C.toFairChain w hb]
    have e3 : lcx C.toFairChain v w = (C.net m).cx w.1 := by
      rw [lcx, if_pos ⟨c, hc⟩, cx_at C.toFairChain w hb]
    have e4 : lcx C.toFairChain w v = (C.net m).bcx w.1 := by
      rw [lcx, if_neg (not_fwd_of_back hc), bcx_at C.toFairChain w hb]
    rw [e1, e2, e3, e4]
    exact hr.retAtB_fwd
  · -- `v` is a child of `w`: the child's way home.
    obtain ⟨hsuf, hag, -⟩ := back_at C.toFairChain hc J
    obtain ⟨hsuf', hag', -⟩ := fwd_at C.toFairChain hc i
    have hvm : (C.net (birth C.toFairChain w.2 + lstg C.toFairChain v w J)).Live v.1 :=
      live_birth C.toFairChain v.2 (by omega)
    have hvm' : (C.net (birth C.toFairChain v.2 + lstg C.toFairChain w v i)).Live v.1 :=
      live_birth C.toFairChain v.2 (Nat.le_add_right _ _)
    refine ⟨_, _, _, _, hsuf, hag, hsuf'.trans (hext.fcl _ hvm'), fun r hr =>
      (hext.fimg _ hvm' r (lt_of_lt_of_le hr hsuf'.length_le)).trans (hag' r hr), ?_⟩
    have hr := (C.goodS _).retB c w.1 (by rw [← hc]; exact hvm)
    unfold NetSt.RetOkB at hr
    rw [← hc] at hr
    have hb : birth C.toFairChain v.2 ≤ m := by omega
    have e1 : lkd C.toFairChain v w = (C.net m).bkind v.1 := by
      rw [lkd, if_neg (not_fwd_of_back hc), if_pos ⟨c, hc⟩, bkind_at C.toFairChain v hb]
    have e2 : lkd C.toFairChain w v = (C.net m).kind v.1 := by
      rw [lkd, if_pos ⟨c, hc⟩, kind_at C.toFairChain v hb]
    have e3 : lcx C.toFairChain v w = (C.net m).bcx v.1 := by
      rw [lcx, if_neg (not_fwd_of_back hc), bcx_at C.toFairChain v hb]
    have e4 : lcx C.toFairChain w v = (C.net m).cx v.1 := by
      rw [lcx, if_pos ⟨c, hc⟩, cx_at C.toFairChain v hb]
    rw [e1, e2, e3, e4]
    exact hr.retAtB_back

end Limit

end BArrow

end V12M
