import QML.QML_v12m_BRetTruth

/-!
# QML v12m — B's canonical model: `ret` truth ⇒ membership at witnessed shapes

The witnessed shapes' truth case (docs §11.20, slice 4).  A true atom's object out there has a
possible part `diatm x u` with `u` any term of `x`'s view; the forward invariant of the witness
edge (`RetInvW`) brings back `⟨□roots, x⟩`, and β on the possible part (`Proof.ret_mapD`) at the
content `u` packed over the roots and `x`'s content (`packXT`) moves it to `diatm x u`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Hole terms -/

omit [ModalSys.NoFour] in
/-- ⭐A closed hole term substituted where the slot is a term is the hole term at it. -/
theorem Term.subst_closed_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {A : VarType}
    (h : (Ctx.empty.insert (.bnd 0) A).Le Γ) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) {a : Ann A} {t : Term σ Δ A a} (h0 : θ (.root (.bnd 0)) = .tm t)
    {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.subst ι θ hθ hc (Term.mono h s)⟩ : Σ c, Term σ Δ B c) = ⟨_, Term.holeAt t s⟩ := by
  rw [Term.subst_mono]
  unfold Term.holeAt
  refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) s
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    rw [h0, show Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm t) (.root (.bnd 0)) = .tm t from
      if_pos rfl]
    exact .refl _
  · change (if v = VarSymb.root (.bnd 0) then _ else Ctx.empty v) = _ at hv
    rw [if_neg hvr] at hv
    cases hv

/-- ⭐A body with its slot replaced by a hole term, read along an arrow with the slot filled by
    `g`, is the body read with the slot filled by the hole term at `g`. -/
theorem readArrow_bodyRepl {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {A : VarType} {a : Ann A} (g : Term σ Δ A a) {B : VarType}
    {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    (Ψ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) B) 1) :
    readArrow himg g (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) A) s) Ψ) =
      readArrow himg (Term.holeAt g s) Ψ := by
  unfold readArrow WFF.bodyRepl
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ψ
  refine Subst.sim_of fun v T _ hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = B := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ ((arrowS σ Δ img).set (.bnd 0) _ (.root (.bnd 0)))
      ((((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))).comp _ _ _)
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    exact SubE.sim_tm_sigma (Eq.symm (Term.subst_closed_sig _ _ _ _ (Subst.set_root _ _ _) s))
  · have hv' : (ctxOf l).boxIn v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    obtain ⟨w, rfl, hw⟩ := boxIn_item' hv'
    change SubE.Sim T ((arrowS σ Δ img).set (.bnd 0) _ (.step w .box))
      ((((Subst.idS σ _).set (.bnd 0) _) (.step w .box)).comp _ _ _)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim T _ ((Subst.set _ _ _).at (.step w .box))
    rw [Subst.at_set_of_rt_ne _ _ (Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0))
      ((Ctx.ref_nonproj _ rfl).trans hv'))]
    exact .refl _

omit [ModalSys.NoFour] in
/-- The witnessed lift of a necessary map, at a pair: the map at the necessary part, the possible
    part kept. -/
theorem holeAt_liftObj_wit {Γ : Ctx} {M T : NShape} {X : VarType} (F : ShapeMap σ M T)
    {a : Ann M.ty} (p : Term σ Γ M.ty a) {b : Ann (.VTypeDia X)} (q : Term σ Γ (.VTypeDia X) b) :
    (⟨_, Term.holeAt (Term.pair p q) (ShapeMap.liftObj (.wit M X) F).2⟩ :
      Σ c, Term σ Γ (RShape.wit T X).ty c) = ⟨_, Term.pair (Term.holeAt p F.obj.2) q⟩ := by
  change (⟨_, Term.pair (Term.holeAt _ (Term.holeAt _ F.obj.2)) (Term.holeAt _ _)⟩ :
    Σ c, Term σ Γ (RShape.wit T X).ty c) = _
  refine sig_pair ((Term.holeAt_holeAt_sig _ _ _).trans
    (Term.holeAt_congr_sig (Term.holeAt_pair_fst p q) _)) (Term.holeAt_pair_snd p q)

omit [ModalSys.NoFour] in
theorem sig_diatm {Γ : Ctx} {A : VarType} {x : VarSymb} {hx hx' : ∃ X, Γ.ref x = some (.VTypeDia X)}
    {a a' : Ann A} {t : Term σ (Γ.diaIn x) A a} {t' : Term σ (Γ.diaIn x) A a'}
    (h : (⟨a, t⟩ : Σ c, Term σ (Γ.diaIn x) A c) = ⟨a', t'⟩) :
    (⟨_, Term.diatm x hx t⟩ : Σ c, Term σ Γ (.VTypeDia A) c) = ⟨_, Term.diatm x hx' t'⟩ := by
  cases h
  rfl

omit [ModalSys.NoFour] in
/-- Substituting a possible term whose witness's image is known. -/
theorem Term.subst_diatm_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {v : VarSymb}
    (hv : ∃ X, Γ.ref v = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (t : Term σ (Γ.diaIn v) A a) {y : VarSymb} (hy : ι v = y)
    (hw : (θ.at v).idxAlong [] = y) (hθd : Subst.Ok (Γ.diaIn v) (θ.dia v y))
    (hcd : Subst.Coh ι (Γ.diaIn v) (θ.dia v y)) (hy' : ∃ X, Δ.ref y = some (.VTypeDia X)) :
    (⟨_, Term.subst ι θ hθ hc (Term.diatm v hv t)⟩ : Σ c, Term σ Δ (.VTypeDia A) c) =
      ⟨_, Term.diatm y hy' (Term.subst ι (θ.dia v y) hθd hcd t)⟩ := by
  subst hy
  rfl

/-- ⭐**β on the possible part, at a necessary object paired with a witness**: the witness
    becomes the possible object with its worlds and content `h` of the object's contents and
    its own. -/
theorem holeAt_possObj {Γ : Ctx} {C X Z : VarType} {b : Ann Z}
    (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b) {c : Ann C}
    (sb : Term σ Γ.boxIn C c) {x : VarSymb} (hxr : Γ.ref x = some (.VTypeDia X)) :
    (⟨_, Term.holeAt (Term.pair (Term.boxtm sb) (Term.eta x (.VTypeDia X) hxr))
      (ShapeMap.possObj h).2⟩ : Σ e, Term σ Γ (RShape.wit (.box C) Z).ty e) =
      ⟨_, Term.pair (Term.boxtm sb) (Term.diatm x ⟨X, hxr⟩ (Term.holeAt
        (Term.pair (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb)
          (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hxr))) h))⟩ := by
  unfold Term.holeAt ShapeMap.possObj
  dsimp only
  refine sig_pair (Term.holeAt_pair_fst _ _) ?_
  refine (Term.subst_diatm_sig _ ?hθ ?hc _ _ (y := x) ?hy ?hw ?hθd
    ?hcd ⟨X, hxr⟩).trans (sig_diatm ?_)
  case hy => rfl
  case hw => rfl
  case hθd =>
    exact Subst.ok_dia (Subst.ok_single (Ctx.empty_le Γ)
      (show (SubE.tm (σ := σ) (Term.pair (Term.boxtm sb) (Term.eta x (.VTypeDia X) hxr))).OkRef _
        from rfl)) ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ rfl
  case hcd =>
    exact Subst.coh_dia (Subst.ok_single (Ctx.empty_le Γ)
      (show (SubE.tm (σ := σ) (Term.pair (Term.boxtm sb) (Term.eta x (.VTypeDia X) hxr))).OkRef _
        from rfl))
      (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl)
      ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
  refine (Term.subst_holeAt_sig _ _ _ _ _).trans (Term.holeAt_congr_sig ?_ h)
  refine sig_pair (Term.subst_eta_tm _ _ _ _ _ _ (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb)
    ?h1) (Term.subst_eta_tm _ _ _ _ _ _
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hxr)) ?h2)
  case h1 =>
    rw [VarSymb.inner_box ModalSys.NoFour.keepOnly, Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [Subst.at_proj _ _ rfl]
    dsimp only [Subst.at]
    rw [show Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (Term.pair (Term.boxtm sb) (Term.eta x (.VTypeDia X) hxr))) (.root (.bnd 0)) =
      .tm (Term.pair (Term.boxtm sb) (Term.eta x (.VTypeDia X) hxr)) from if_pos rfl]
    rfl
  case h2 =>
    rw [Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl]
    dsimp only [Subst.at]
    rw [show Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
      (.tm (Term.pair (Term.boxtm sb) (Term.eta x (.VTypeDia X) hxr))) (.root (.bnd 0)) =
      .tm (Term.pair (Term.boxtm sb) (Term.eta x (.VTypeDia X) hxr)) from if_pos rfl]
    change SubE.diaBody x (SubE.tm (Term.diatm x _ _)) = _
    rw [SubE.diaBody_diatm]

/-! ## Packing a term along a witness -/

omit [ModalSys.NoFour] in
theorem packXCtx_fst (l : List VarType) (X : VarType) :
    (Ctx.empty.insert (.bnd 0) (.VTypeProd (bcT l) X)).ref (.step (.root (.bnd 0)) .fst) =
      some (bcT l) :=
  Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)

omit [ModalSys.NoFour] in
theorem packXCtx_snd (l : List VarType) (X : VarType) :
    (Ctx.empty.insert (.bnd 0) (.VTypeProd (bcT l) X)).ref (.step (.root (.bnd 0)) .snd) =
      some X :=
  Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)

/-- ⭐A term of `x`'s view over `l`, packed into a hole term over the roots' tuple and `x`'s
    content (`packXS`, as `pack2X` packs formulas). -/
noncomputable def packXT (l : List VarType) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) {Z : VarType} {c : Ann Z}
    (u : Term σ ((ctxOf l).diaIn x) Z c) :
    Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (bcT l) X)) Z
      (c.mapIdx (packXIdx l (.step (.root (.bnd 0)) .fst) x (.step (.root (.bnd 0)) .snd))) :=
  Term.subst (packXIdx l (.step (.root (.bnd 0)) .fst) x (.step (.root (.bnd 0)) .snd))
    (packXS σ _ l (.step (.root (.bnd 0)) .fst) x (.step (.root (.bnd 0)) .snd))
    (ok_packXS l (packXCtx_fst l X) hx (packXCtx_snd l X))
    (coh_packXS l (packXCtx_fst l X) hx (packXCtx_snd l X)) u

/-- ⭐A packed term read at the roots' items and `x`'s content, weakened: the term, weakened. -/
theorem holeAt_packXT {l : List VarType} {x : VarSymb} {X : VarType} {Δ : Ctx}
    (h : ((ctxOf l).diaIn x).Le Δ) (hx : (ctxOf l).ref x = some (.VTypeDia X)) {Z : VarType}
    {c : Ann Z} (u : Term σ ((ctxOf l).diaIn x) Z c) :
    (⟨_, Term.holeAt (Term.pair (Term.mono ((Ctx.le_boxIn_diaIn _ x).trans h) (tupT l).2)
        (Term.eta (x.step .dia) X (h.ref (Ctx.ref_diaIn_of hx)))) (packXT l hx u)⟩ :
      Σ e, Term σ Δ Z e) = ⟨_, Term.mono h u⟩ := by
  have hle := (Ctx.le_boxIn_diaIn _ x).trans h
  unfold Term.holeAt packXT
  refine (Term.subst_comp_sig _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le h)
    (Subst.coh_idS_le h) ?_ u).trans (Term.subst_idS_mono h _ _ u)
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair (Term.mono hle (tupT l).2)
      (Term.eta (x.step .dia) X (h.ref (Ctx.ref_diaIn_of hx)))))).at (.root (.bnd 0)) =
      .tm (Term.pair (Term.mono hle (tupT l).2)
        (Term.eta (x.step .dia) X (h.ref (Ctx.ref_diaIn_of hx)))) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  refine Subst.sim_of fun v T _ hv => ?_
  rcases diaIn_item hv with ⟨w, rfl, hw⟩ | ⟨rfl, hxT⟩
  · obtain ⟨r, hr, hlt, _⟩ := ref_rt hw
    change SubE.Sim T (.ren (.step w .box))
      ((Subst.single (.bnd 0) _).at
        ((packBase l (.step (.root (.bnd 0)) .fst) w.rt).ext (encPath w.path ++ itemTail)))
    rw [hr]
    change SubE.Sim T _ ((Subst.single (.bnd 0) _).at
      ((((VarSymb.root (.bnd 0)).step .fst).ext (tupPath l r)).ext (encPath w.path ++ itemTail)))
    have hb : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair (Term.mono hle (tupT l).2)
        (Term.eta (x.step .dia) X (h.ref (Ctx.ref_diaIn_of hx)))))).at
        ((VarSymb.root (.bnd 0)).step .fst) = .tm (Term.mono hle (tupT l).2) := by
      rw [Subst.at_proj _ _ rfl, h0]
      rfl
    obtain ⟨R, hR, h1⟩ := at_tupPath_tupT _ l hle hb hlt
    have h2 := at_enc_tupB_mono hle _ ModalSys.T rfl hR h1 hw hr
    rw [at_item_of_tupB_base_mono hle _ _ hw ModalSys.T rfl h2, Term.mono_eta]
    exact .ren_eta _ _
  · rw [hx] at hxT
    cases hxT
    change SubE.Sim X (.ren (.step x .dia))
      ((if x = x then SubE.ren (.step (.root (.bnd 0)) .snd) else .hide).comp _ _ _)
    rw [if_pos rfl]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .ren_eta _ _

/-- ⭐A packed term read at the roots' images and `cx`: the term sent along the witness
    arrow. -/
theorem holeRead_tupImgT_packXT {l : List VarType} {x : VarSymb} {X : VarType} {Δ : Ctx}
    [Δ.NoSlots] {img : ℕ → ℕ} (himg : ImgOk l Δ img) (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) {Z : VarType} {c : Ann Z}
    (u : Term σ ((ctxOf l).diaIn x) Z c) :
    (⟨_, Term.holeRead (Term.pair (tupImgT l img himg).2 (Term.eta (.root (.free cx)) X hcx))
        (packXT l hx u)⟩ : Σ e, Term σ Δ Z e) =
      ⟨_, Term.subst (arrowXIdx img x cx) (arrowXS σ Δ img x cx) (ok_arrowXS himg hx hcx)
        (coh_arrowXS himg hx hcx) u⟩ := by
  unfold Term.holeRead packXT
  rw [Term.subst_mono]
  refine Term.subst_comp_sig _ _ (arrowXS σ Δ img x cx) _ _ _ _ (ok_arrowXS himg hx hcx)
    (coh_arrowXS himg hx hcx) ?_ u
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair (tupImgT l img himg).2
      (Term.eta (.root (.free cx)) X hcx)))).at (.root (.bnd 0)) =
      .tm (Term.pair (tupImgT l img himg).2 (Term.eta (.root (.free cx)) X hcx)) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  refine Subst.sim_of fun v T _ hv => ?_
  rcases diaIn_item hv with ⟨w, rfl, hw⟩ | ⟨rfl, hxT⟩
  · obtain ⟨r, hr, hlt, hR⟩ := ref_rt hw
    change SubE.Sim T (.ren (itemAt (imgRoot img w.rt) w))
      ((Subst.single (.bnd 0) _).at
        ((packBase l (.step (.root (.bnd 0)) .fst) w.rt).ext (encPath w.path ++ itemTail)))
    have hz : Δ.ref (.root (imgRoot img w.rt)) = some (rootTy l r).bc := by
      rw [hr]; exact himg r hlt
    have hT := ref_item hw hR hz
    rw [hr] at hz hT ⊢
    change SubE.Sim T (.ren ((VarSymb.root (.free (img r))).ext (encPath w.path ++ itemTail)))
      ((Subst.single (.bnd 0) _).at
        ((((VarSymb.root (.bnd 0)).step .fst).ext (tupPath l r)).ext (encPath w.path ++ itemTail)))
    have hb : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair (tupImgT l img himg).2
        (Term.eta (.root (.free cx)) X hcx)))).at ((VarSymb.root (.bnd 0)).step .fst) =
        .tm (tupImgT l img himg).2 := by
      rw [Subst.at_proj _ _ rfl, h0]
      rfl
    obtain ⟨T', hT', h1⟩ := at_tupPath_tupImgT _ l himg hb hlt
    refine sim_ren_at_ext _ _ ((PPath.encPath (reach_ppath hw).1).append PPath.itemTail) hT' hT ?_
    rw [h1]
    exact .ren_eta _ _
  · rw [hx] at hxT
    cases hxT
    change SubE.Sim X (if x = x then SubE.ren (.root (.free cx)) else .hide)
      ((if x = x then SubE.ren (.step (.root (.bnd 0)) .snd) else .hide).comp _ _ _)
    rw [if_pos rfl, if_pos rfl]
    dsimp only [SubE.comp]
    rw [Subst.at_proj _ _ rfl, h0]
    exact .ren_eta _ _

/-! ## At a node -/

omit [ModalSys.NoFour] in
/-- The witnessed lift of a necessary map on values, at a pair. -/
theorem holeAt_liftVal_wit {Γ : Ctx} {M T : NShape} {X : VarType} (F : ShapeMap σ M T)
    {a : Ann M.flat} (p : Term σ Γ M.flat a) {b : Ann X} (q : Term σ Γ X b) :
    (⟨_, Term.holeAt (Term.pair p q) (ShapeMap.liftVal (.wit M X) F).2⟩ :
      Σ c, Term σ Γ (RShape.wit T X).flat c) = ⟨_, Term.pair (Term.holeAt p F.val.2) q⟩ := by
  change (⟨_, Term.pair (Term.holeAt _ (Term.holeAt _ F.val.2)) (Term.holeAt _ _)⟩ :
    Σ c, Term σ Γ (RShape.wit T X).flat c) = _
  refine sig_pair ((Term.holeAt_holeAt_sig _ _ _).trans
    (Term.holeAt_congr_sig (Term.holeAt_pair_fst p q) _)) (Term.holeAt_pair_snd p q)

omit [ModalSys.NoFour] in
/-- β on the possible part, on a pair of values. -/
theorem holeAt_possVal {Γ : Ctx} {C X Z : VarType} {b : Ann Z}
    (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b) {c : Ann C}
    (p : Term σ Γ C c) {d : Ann X} (q : Term σ Γ X d) :
    (⟨_, Term.holeAt (Term.pair p q) (ShapeMap.possVal h).2⟩ :
      Σ e, Term σ Γ (RShape.wit (.box C) Z).flat e) =
      ⟨_, Term.pair p (Term.holeAt (Term.pair p q) h)⟩ := by
  change (⟨_, Term.pair (Term.holeAt _ _) (Term.holeAt _ h)⟩ :
    Σ e, Term σ Γ (RShape.wit (.box C) Z).flat e) = _
  exact sig_pair (Term.holeAt_pair_fst p q) rfl

omit [ModalSys.NoFour] in
/-- β on the possible part with companions, on a pair of values: the necessary part's value
    kept, the content's mapped at its contents (read along the first components) and the
    content. -/
theorem holeAt_possValC {Γ : Ctx} {C X Z : VarType} {b : Ann Z}
    (h : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) Z b) :
    ∀ (cs : List (List Step)) (hcs : C.CompOk cs) {c : Ann (C.compsFlat cs)}
      (p : Term σ Γ (C.compsFlat cs) c) {d : Ann X} (q : Term σ Γ X d),
      (⟨_, Term.holeAt (Term.pair p q) (ShapeMap.possValC h cs hcs).2⟩ :
        Σ e, Term σ Γ (RShape.wit (.boxC C cs hcs) Z).flat e) =
        ⟨_, Term.pair p (Term.holeAt (Term.pair (Term.holeAt (Term.pair p q)
          (Term.eta ((VarSymb.step (.root (.bnd 0)) .fst).ext (compsFst cs)) C
            (Ctx.ref_compsFst cs (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))) q) h)⟩
  | [], _, _, p, _, q => (holeAt_possVal h p q).trans
      (sig_pair rfl (Term.holeAt_congr_sig (sig_pair (Term.holeAt_pair_fst p q).symm rfl) h))
  | _ :: _, _, _, p, _, q => by
      change (⟨_, Term.pair (Term.holeAt (Term.pair p q) (Term.eta _ _ _))
        (Term.holeAt (Term.pair p q) (Term.holeAt (Term.pair (Term.eta _ _ _)
          (Term.eta _ _ _)) h))⟩ : Σ e, Term σ Γ _ e) = _
      exact sig_pair (Term.holeAt_pair_fst p q) ((Term.holeAt_holeAt_sig _ _ _).trans
        (Term.holeAt_congr_sig (sig_pair rfl (Term.holeAt_pair_snd p q)) h))

/-- ⭐⭐**A witnessed returning possibility from its far end, at a node**: along a witness arrow
    `k → s` made for `x`, with its forward invariant, `Φ(⟨N, diatm x u⟩)` at `k` (read along the
    reverse arrow), for the object `N` some items make and any term `u` of `x`'s view, is
    `◇[d ↦ the items sent home; e ⇝ u sent home] Φ(d, e)` at `s`.  The invariant at the body
    pulled back along both maps; then β on the possible part at `u` packed (`ret_mapD`,
    `packXT`), and `ret_map` along the packing map. -/
theorem ret_of_invW {bb : Bool} {hbb : ModalSys.T = bb}
    {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hsM : Theory.IsMCS ts.M)
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvWB hS bb hbb tk ts cls imgs clt imgt x X cx) {N : NShape}
    (n : NItems σ (ctxOf cls).boxIn N) {Z : VarType} {c : Ann Z}
    (u : Term σ ((ctxOf cls).diaIn x) Z c)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (hmem : ∃ (hs : cls <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
      (hx : (ctxOf cls).ref x = some (.VTypeDia X)),
      readArrow himgt (Term.pair (n.mono (ctxOf_le_of_suffix hs)).obj.2
        (Term.diatm x ⟨X, (ctxOf_le_of_suffix hs).ref hx⟩
          (Term.mono ((ctxOf_le_of_suffix hs).diaIn x) u))) Φ ∈ tk.M) :
    ∃ (himgs : ImgOk cls (ctxOf ts.l) imgs) (ht : clt <:+ ts.l)
      (hx : (ctxOf cls).ref x = some (.VTypeDia X))
      (hcx : (ctxOf ts.l).ref (.root (.free cx)) = some X),
      WFF.retS hS (.wit N Z)
        (Term.pair (n.subst (arrowIdx imgs) (arrowS σ (ctxOf ts.l) imgs) (ok_arrowS himgs)
            (coh_arrowS himgs)).2
          (Term.subst (arrowXIdx imgs x cx) (arrowXS σ (ctxOf ts.l) imgs x cx)
            (ok_arrowXS himgs hx hcx) (coh_arrowXS himgs hx hcx) u))
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ ts.M := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  obtain ⟨hs', himgt', hx', hm⟩ := hmem
  refine ⟨himgs, ht, hx, hcx, ?_⟩
  have hle := ctxOf_le_of_suffix hs
  set F := packMapC bb hbb cls n
  set S₀ : RShape := .wit (tupShape bb hbb cls) Z
  set hU := packXT cls hx u
  have hr := hinv (WFF.bodyRepl
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (ShapeMap.possObj hU).2)
    (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (ShapeMap.liftObj S₀ F).2) Φ))
    (by
      change readArrow himgt (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT cls).2))
        (Term.eta x (.VTypeDia X) (hle.ref hx))) _ ∈ tk.M
      rw [readArrow_bodyRepl, readArrow_bodyRepl]
      refine (congrArg (· ∈ tk.M) (readArrow_sig himgt ?_ Φ)).mpr hm
      refine (Term.holeAt_congr_sig (holeAt_possObj hU _ (hle.ref hx)) _).trans
        ((holeAt_liftObj_wit F _ _).trans (sig_pair ?_ (sig_diatm ?_)))
      · exact subst_packMapC_obj _ _ _ hle (by
          change Subst.single _ _ (.root (.bnd 0)) = _
          exact if_pos rfl) n
      · refine (Term.holeAt_congr_sig (sig_pair (by rw [Term.mono_mono]) rfl) hU).trans ?_
        exact holeAt_packXT (hle.diaIn x) hx u)
  simp only [WFF.mono_bodyRepl (ctxOf_le_of_suffix ht).boxIn, Term.mono_mono] at hr
  have hc := hsM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
    ⟨Proof.ret_map hS .nec (S := S₀) F _
      (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ)
      (Proof.ret_mapD hS .nec hU _ _ (Proof.lookup List.mem_cons_self))⟩⟩
  refine (congrArg (· ∈ ts.M) (OutLeg.retS_congr hS .nec (.wit N Z) ?_ rfl)).mp hc
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  refine (Term.holeAt_congr_sig (holeAt_possValC hU _ _ _ _) _).trans
    ((holeAt_liftVal_wit F _ _).trans (sig_pair ?_ ?_))
  · rw [← Term.holeRead_eq_holeAt]
    exact holeRead_tupCompsImg_packMapC himgs bb hbb n
  · refine (Term.holeAt_congr_sig (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _
      (at_compsFst_tupCompsImg cls imgs himgs _ _ _ _ (by
        rw [Subst.at_proj _ _ rfl, Subst.at_nonproj _ rfl, Subst.single_root]; rfl))) rfl) hU).trans
      ?_
    rw [← Term.holeRead_eq_holeAt]
    exact holeRead_tupImgT_packXT himgs hx hcx u

/-- A body with its slot replaced by a hole term, read along a witness arrow with the slot
    filled by `g`, is the body read with the slot filled by the hole term at `g`. -/
theorem readArrowX_bodyRepl {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) {A : VarType} {a : Ann A}
    (g : Term σ Δ A a) {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    (Ψ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) B) 1) :
    readArrowX himg hx hcx g
        (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) A) s) Ψ) =
      readArrowX himg hx hcx (Term.holeAt g s) Ψ := by
  unfold readArrowX WFF.bodyRepl
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ψ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = B := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ ((arrowXS σ Δ img x cx).set (.bnd 0) _ (.root (.bnd 0)))
      ((((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))).comp _ _ _)
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    exact SubE.sim_tm_sigma (Eq.symm (Term.subst_closed_sig _ _ _ _ (Subst.set_root _ _ _) s))
  · have hv' : ((ctxOf l).diaIn x) v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    change SubE.Sim T ((arrowXS σ Δ img x cx).set (.bnd 0) _ v)
      ((((Subst.idS σ _).set (.bnd 0) _) v).comp _ _ _)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim T _ ((Subst.set _ _ _).at v)
    rw [Subst.at_set_of_rt_ne _ _ (Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).rootFresh (le_refl 0))
      ((Ctx.ref_nonproj _ hlp).trans hv')), Subst.at_nonproj _ hlp]
    exact .refl _

/-- ⭐⭐**A doubly witnessed returning possibility from its far end, at a node**: as `ret_of_invW`,
    with the source's way out along the target's witness `e` (`RetInvWD`, read along the witness
    arrow, `readArrowX_bodyRepl`). -/
theorem ret_of_invWD {bb : Bool} {hbb : ModalSys.T = bb}
    {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hsM : Theory.IsMCS ts.M)
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ}
    {e : VarSymb} {E : VarType} {cxv : ℕ}
    (h : RetInvWDB hS bb hbb tk ts cls imgs clt imgt x X cxw e E cxv) {N : NShape}
    (n : NItems σ (ctxOf cls).boxIn N) {Z : VarType} {c : Ann Z}
    (u : Term σ ((ctxOf cls).diaIn x) Z c)
    (Φ : WFF σ (((ctxOf clt).diaIn e).insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (hmem : ∃ (hs : cls <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
      (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (he : (ctxOf clt).ref e = some (.VTypeDia E))
      (hcxv : (ctxOf tk.l).ref (.root (.free cxv)) = some E),
      readArrowX himgt he hcxv (Term.pair (n.mono (ctxOf_le_of_suffix hs)).obj.2
        (Term.diatm x ⟨X, (ctxOf_le_of_suffix hs).ref hx⟩
          (Term.mono ((ctxOf_le_of_suffix hs).diaIn x) u))) Φ ∈ tk.M) :
    ∃ (himgs : ImgOk cls (ctxOf ts.l) imgs) (ht : clt <:+ ts.l)
      (hx : (ctxOf cls).ref x = some (.VTypeDia X))
      (hcx : (ctxOf ts.l).ref (.root (.free cxw)) = some X)
      (he' : (ctxOf ts.l).ref e = some (.VTypeDia E)),
      (OutLeg.pos e ⟨E, he'⟩ : OutLeg (ctxOf ts.l)).retS hS (.wit N Z)
        (Term.pair (n.subst (arrowIdx imgs) (arrowS σ (ctxOf ts.l) imgs) (ok_arrowS himgs)
            (coh_arrowS himgs)).2
          (Term.subst (arrowXIdx imgs x cxw) (arrowXS σ (ctxOf ts.l) imgs x cxw)
            (ok_arrowXS himgs hx hcx) (coh_arrowXS himgs hx hcx) u))
        (WFF.mono (((ctxOf_le_of_suffix ht).diaIn e).insert (.bnd 0) _) Φ) ∈ ts.M := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
  obtain ⟨hs', himgt', hx', he'', hcxv', hm⟩ := hmem
  refine ⟨himgs, ht, hx, hcxw, (ctxOf_le_of_suffix ht).ref he, ?_⟩
  have hle := ctxOf_le_of_suffix hs
  set F := packMapC bb hbb cls n
  set S₀ : RShape := .wit (tupShape bb hbb cls) Z
  set hU := packXT cls hx u
  have hr := hinv (WFF.bodyRepl
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (ShapeMap.possObj hU).2)
    (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (ShapeMap.liftObj S₀ F).2) Φ))
    (by
      change readArrowX himgt he hcxv (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT cls).2))
        (Term.eta x (.VTypeDia X) (hle.ref hx))) _ ∈ tk.M
      rw [readArrowX_bodyRepl, readArrowX_bodyRepl]
      refine (congrArg (· ∈ tk.M) (readArrowX_sig himgt he hcxv ?_ Φ)).mpr hm
      refine (Term.holeAt_congr_sig (holeAt_possObj hU _ (hle.ref hx)) _).trans
        ((holeAt_liftObj_wit F _ _).trans (sig_pair ?_ (sig_diatm ?_)))
      · exact subst_packMapC_obj _ _ _ hle (by
          change Subst.single _ _ (.root (.bnd 0)) = _
          exact if_pos rfl) n
      · refine (Term.holeAt_congr_sig (sig_pair (by rw [Term.mono_mono]) rfl) hU).trans ?_
        exact holeAt_packXT (hle.diaIn x) hx u)
  simp only [WFF.mono_bodyRepl ((ctxOf_le_of_suffix ht).diaIn e), Term.mono_mono] at hr
  have hc := hsM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
    ⟨Proof.ret_map hS (.pos e ⟨E, (ctxOf_le_of_suffix ht).ref he⟩) (S := S₀) F _
      (WFF.mono (((ctxOf_le_of_suffix ht).diaIn e).insert (.bnd 0) _) Φ)
      (Proof.ret_mapD hS (.pos e ⟨E, (ctxOf_le_of_suffix ht).ref he⟩) hU _ _
        (Proof.lookup List.mem_cons_self))⟩⟩
  refine (congrArg (· ∈ ts.M) (OutLeg.retS_congr hS _ (.wit N Z) ?_ rfl)).mp hc
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  refine (Term.holeAt_congr_sig (holeAt_possValC hU _ _ _ _) _).trans
    ((holeAt_liftVal_wit F _ _).trans (sig_pair ?_ ?_))
  · rw [← Term.holeRead_eq_holeAt]
    exact holeRead_tupCompsImg_packMapC himgs bb hbb n
  · refine (Term.holeAt_congr_sig (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _
      (at_compsFst_tupCompsImg cls imgs himgs _ _ _ _ (by
        rw [Subst.at_proj _ _ rfl, Subst.at_nonproj _ rfl, Subst.single_root]; rfl))) rfl) hU).trans
      ?_
    rw [← Term.holeRead_eq_holeAt]
    exact holeRead_tupImgT_packXT himgs hx hcxw u

/-! ## The invariant at the limit -/

/-- A witness body over the `□` view, lifted along the target's witness `e`, read by the doubly
    witnessed lift: the witness body read by the plain one. -/
theorem liftBodyWD_lift {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (Φ : WFF σ (bodyCtxW cls clt X) 1) :
    liftBodyWD hs himgt hx he hcxv (WFF.mono ((Ctx.le_boxIn_diaIn _ e).insert (.bnd 0) _) Φ) =
      liftBodyW hs himgt hx Φ := by
  unfold liftBodyWD liftBodyW
  rw [WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T hlp hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.set_root, Subst.set_root]
    exact .refl _
  · obtain ⟨u, rfl, _⟩ := bodyW_item hv hvr
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    exact .refl _

/-- ⭐**The invariant of a witness edge gives the forward witness one**: when the way back is
    witnessed too, by forgetting its leg (`retxS_forget_node`). -/
theorem RetAt.toRetInvW {hS : ModalSys.BStrong = true} {tv tw : NodeSt σ}
    (hw : Theory.IsMCS tw.M) {x : VarSymb} {X : VarType} {kw : Option (VarSymb × VarType)}
    {cv cw : ℕ} {cls : List VarType} {imgs : ℕ → ℕ} {clt : List VarType} {imgt : ℕ → ℕ}
    (h : RetAt hS tv tw (some (x, X)) kw cv cw cls imgs clt imgt) :
    RetInvW hS tv tw cls imgs clt imgt x X cv := by
  rcases kw with _ | ⟨e, E⟩
  · exact h
  · obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, hx, hcxw, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyWD_lift]; exact hΦ)
    refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr, ⟨?_⟩⟩
    refine Proof.retxS_forget_node hS ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ _ _
      (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    simp only [OutLeg.lift, WFF.mono_mono]

/-- ⭐**The invariant with companions of a witness edge gives the forward witness one** (as
    `RetAt.toRetInvW`, by `retxS_forgetC_node`). -/
theorem RetAtB.toRetInvWB {hS : ModalSys.BStrong = true} {b : Bool} {hb : ModalSys.T = b}
    {tv tw : NodeSt σ} (hw : Theory.IsMCS tw.M) {x : VarSymb} {X : VarType}
    {kw : Option (VarSymb × VarType)} {cv cw : ℕ} {cls : List VarType} {imgs : ℕ → ℕ}
    {clt : List VarType} {imgt : ℕ → ℕ}
    (h : RetAtB hS b hb tv tw (some (x, X)) kw cv cw cls imgs clt imgt) :
    RetInvWB hS b hb tv tw cls imgs clt imgt x X cv := by
  rcases kw with _ | ⟨e, E⟩
  · exact h
  · obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, hinv⟩ := h
    refine ⟨hs, himgs, ht, himgt, hx, hcxw, fun Φ hΦ => ?_⟩
    have hr := hinv _ (by rw [liftBodyWD_lift]; exact hΦ)
    refine hw.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr, ⟨?_⟩⟩
    refine Proof.retxS_forgetC_node hS ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ _
      (VarType.compOk_compsAllB b hb _) _ _ (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
    simp only [OutLeg.lift, WFF.mono_mono]

namespace BData

/-- ⭐**Witnessed returning possibilities from the far end** (plain leg): along an arrow `s → k`
    whose way back is a witness edge of `k` made for `x`, `Φ(⟨N, diatm x u⟩)` at `k` (read along
    the arrow), for the object `N` some items make and any term `u` of `x`'s view, is
    `◇[d ↦ the items sent home; e ⇝ u sent home] Φ(d, e)` at `s`.  The limit of a strong chain
    has it (`bdataS_retInW`). -/
def RetInW (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s k : B.W} (h : B.R s k) {x : VarSymb} {X : VarType} (hk : B.lb k s x = some X) {i : ℕ}
    {N : NShape} {Z : VarType} (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0)
      (RShape.wit N Z).ty) 1) {j : ℕ} (hj : B.stg s k i ≤ j)
    (hx : ((B.w k).ctx j).ref x = some (.VTypeDia X)) (n : NItems σ ((B.w k).ctx j).boxIn N)
    {c : Ann Z} (u : Term σ (((B.w k).ctx j).diaIn x) Z c),
    readArrow ((B.imgOk h i).mono ((B.w k).le hj)) (Term.pair n.obj.2 (Term.diatm x ⟨X, hx⟩ u))
      Φ ∈ (B.w k).M j →
      ∃ hiK : i ≤ B.stg k s j,
        WFF.retS hS (.wit N Z)
          (Term.pair (n.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm h) j)) (coh_arrowS (B.imgOk (B.symm h) j))).2
            (Term.subst (arrowXIdx (B.img k s) x (B.cx k s x))
              (arrowXS σ _ (B.img k s) x (B.cx k s x))
              (ok_arrowXS (B.imgOk (B.symm h) j) hx (B.lb_hcx hk j))
              (coh_arrowXS (B.imgOk (B.symm h) j) hx (B.lb_hcx hk j)) u))
          (WFF.mono (((B.w s).le hiK).boxIn.insert (.bnd 0) _) Φ) ∈ (B.w s).M (B.stg k s j)

/-- ⭐**Doubly witnessed returning possibilities from the far end**: as `RetInW`, along an arrow
    `s → k` of `y`'s extent (the leg's witness). -/
def RetInWX (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s k : B.W} {y : VarSymb} {Y : VarType} (hky : B.lb s k y = some Y) {x : VarSymb}
    {X : VarType} (hkx : B.lb k s x = some X) {i : ℕ}
    (hy : ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape} {Z : VarType}
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (RShape.wit N Z).ty) 1) {j : ℕ}
    (hj : B.stg s k i ≤ j) (hx : ((B.w k).ctx j).ref x = some (.VTypeDia X))
    (n : NItems σ ((B.w k).ctx j).boxIn N) {c : Ann Z} (u : Term σ (((B.w k).ctx j).diaIn x) Z c),
    readArrowX ((B.imgOk (B.lbR hky) i).mono ((B.w k).le hj)) hy
        (((B.w k).le hj).ref (B.lb_hcx hky i)) (Term.pair n.obj.2 (Term.diatm x ⟨X, hx⟩ u)) Φ ∈
      (B.w k).M j →
      ∃ hiK : i ≤ B.stg k s j,
        (OutLeg.pos y ⟨Y, ((B.w s).le hiK).ref hy⟩ : OutLeg ((B.w s).ctx (B.stg k s j))).retS hS
          (.wit N Z)
          (Term.pair (n.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
              (ok_arrowS (B.imgOk (B.symm (B.lbR hky)) j))
              (coh_arrowS (B.imgOk (B.symm (B.lbR hky)) j))).2
            (Term.subst (arrowXIdx (B.img k s) x (B.cx k s x))
              (arrowXS σ _ (B.img k s) x (B.cx k s x))
              (ok_arrowXS (B.imgOk (B.symm (B.lbR hky)) j) hx (B.lb_hcx hkx j))
              (coh_arrowXS (B.imgOk (B.symm (B.lbR hky)) j) hx (B.lb_hcx hkx j)) u))
          (WFF.mono ((((B.w s).le hiK).diaIn y).insert (.bnd 0) _) Φ) ∈ (B.w s).M (B.stg k s j)

end BData

section Limit

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀) (E : LimitEx C.toFairChain)

/-- ⭐⭐**The limit has witnessed returning possibilities from the far end**: the way home's
    invariant (`lretAtB`), a witness edge's (`RetAtB.toRetInvWB`), at a node (`ret_of_invW`). -/
theorem bdataS_retInW : (bdataS C E).RetInW hS := by
  classical
  intro s k h x X hk i N Z Φ j hj hx n c u hm
  replace hk := lbOfKd_eq.mp hk
  obtain ⟨cls, imgs, clt, imgt, hJs, hJag, his, hiag, hret⟩ := lretAtB C h.symm j i hj
  have hsp := (lstg_spec C.toFairChain h i).1
  have hkp := (lstg_spec C.toFairChain h.symm j).1
  have hiK : i ≤ lstg C.toFairChain k s j := by
    change lstg C.toFairChain s k i ≤ j at hj
    omega
  have hsl : (C.net (birth C.toFairChain s.2 + lstg C.toFairChain k s j)).Live s.1 :=
    live_birth C.toFairChain s.2 (Nat.le_add_right _ _)
  have hsM := (C.good _).mcs s.1 hsl
  have hk' : lkd C.toFairChain k s = some (x, X) := hk
  rw [hk'] at hret
  have hinv := RetAtB.toRetInvWB hsM hret
  obtain ⟨hcs, -, ht, himgt, -⟩ := id hinv
  have hg := grow_stage C.toFairChain k j (m := birth C.toFairChain s.2 +
    lstg C.toFairChain k s j) hkp
  have hm' := hg.sub _ hm
  rw [readArrow_mono_congr his _ _ himgt (fun r hr => (hiag r hr).symm)] at hm'
  obtain ⟨himgs, ht', hx', hcx, hr⟩ := ret_of_invW hsM hinv
    (n.mono (ctxOf_le_of_suffix hJs)) (Term.mono ((ctxOf_le_of_suffix hJs).diaIn x) u) _
    ⟨hcs, himgt, (ctxOf_le_of_suffix hJs).ref hx, by
      refine (congrArg (· ∈ _) (readArrow_sig _ ?_ _)).mp hm'
      refine sig_pair ?_ (sig_diatm ?_)
      · rw [NItems.mono_mono, NItems.obj_mono]
      · rw [Term.mono_mono]⟩
  refine ⟨hiK, (congrArg (· ∈ _) (OutLeg.retS_congr hS .nec (.wit N Z) ?_ ?_)).mp hr⟩
  · refine sig_pair ?_ ?_
    · rw [NItems.subst_mono]
      exact NItems.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
    · rw [Term.subst_mono]
      exact Term.subst_congr _ _ _ _ _ _ (sim_arrowXS hJag) _
  · rw [WFF.mono_mono]

/-- ⭐⭐**The limit has doubly witnessed returning possibilities from the far end**: the way
    home's invariant is the doubly witnessed one (`lretAtB`), at a node (`ret_of_invWD`). -/
theorem bdataS_retInWX : (bdataS C E).RetInWX hS := by
  classical
  intro s k y Y hky x X hkx i hy N Z Φ j hj hx n c u hm
  replace hky := lbOfKd_eq.mp hky
  replace hkx := lbOfKd_eq.mp hkx
  have h : LR C.toFairChain s k := lkdR hky
  obtain ⟨cls, imgs, clt, imgt, hJs, hJag, his, hiag, hret⟩ := lretAtB C h.symm j i hj
  have hsp := (lstg_spec C.toFairChain h i).1
  have hkp := (lstg_spec C.toFairChain h.symm j).1
  have hiK : i ≤ lstg C.toFairChain k s j := by
    change lstg C.toFairChain s k i ≤ j at hj
    omega
  have hsl : (C.net (birth C.toFairChain s.2 + lstg C.toFairChain k s j)).Live s.1 :=
    live_birth C.toFairChain s.2 (Nat.le_add_right _ _)
  have hsM := (C.good _).mcs s.1 hsl
  have hky' : lkd C.toFairChain s k = some (y, Y) := hky
  have hkx' : lkd C.toFairChain k s = some (x, X) := hkx
  rw [hky', hkx'] at hret
  have hinv : RetInvWDB hS ModalSys.T rfl _ _ cls imgs clt imgt x X _ y Y _ := hret
  obtain ⟨hcs, -, ht, himgt, -, -, hyc, hcyc, -⟩ := id hinv
  have hg := grow_stage C.toFairChain k j (m := birth C.toFairChain s.2 +
    lstg C.toFairChain k s j) hkp
  have hm' := hg.sub _ hm
  rw [readArrowX_mono_congr his _ _ himgt (fun r hr => (hiag r hr).symm) _ hyc _ hcyc] at hm'
  obtain ⟨himgs, ht', hx', hcx, hy', hr⟩ := ret_of_invWD hsM hinv
    (n.mono (ctxOf_le_of_suffix hJs)) (Term.mono ((ctxOf_le_of_suffix hJs).diaIn x) u) _
    ⟨hcs, himgt, (ctxOf_le_of_suffix hJs).ref hx, hyc, hcyc, by
      refine (congrArg (· ∈ _) (readArrowX_sig _ _ _ ?_ _)).mp hm'
      refine sig_pair ?_ (sig_diatm ?_)
      · rw [NItems.mono_mono, NItems.obj_mono]
      · rw [Term.mono_mono]⟩
  refine ⟨hiK, (congrArg (· ∈ _) (OutLeg.retS_congr hS _ (.wit N Z) ?_ ?_)).mp hr⟩
  · refine sig_pair ?_ ?_
    · rw [NItems.subst_mono]
      exact NItems.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
    · rw [Term.subst_mono]
      exact Term.subst_congr _ _ _ _ _ _ (sim_arrowXS hJag) _
  · rw [WFF.mono_mono]

end Limit

omit [ModalSys.NoFour] in
/-- ⭐Every term of a witnessed shape's type is a pair of some items' object and a possible term:
    `⟨N, diatm x u⟩`. -/
theorem exists_wit {Γ : Ctx} (N : NShape) (Z : VarType)
    {c : Ann (RShape.wit N Z).ty}
    (g : Term σ Γ (RShape.wit N Z).ty c) :
    ∃ (n : NItems σ Γ.boxIn N) (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
      (c' : Ann Z) (u : Term σ (Γ.diaIn x) Z c'),
      (⟨c, g⟩ : Σ e, Term σ Γ (RShape.wit N Z).ty e) =
        ⟨_, Term.pair n.obj.2 (Term.diatm x hx u)⟩ := by
  match g with
  | .pair g₁ (.diatm x hx u) =>
      obtain ⟨n, hn⟩ := NItems.exists_obj N g₁
      exact ⟨n, x, hx, _, u, sig_pair hn.symm rfl⟩

namespace BData

variable {B : BData σ}

/-- ⭐⭐**`ret` at a witnessed shape at the own arrow, truth ⇒ membership** (T; plain leg).  The
    object here is a pair of some items' object and a possible object `p`, both definable; the way
    home being the identity, `ComesBack`'s witness clause is `Here(p, t₂)` (`Model.Realised`), in
    the theory by the induction hypothesis.  As `mem_ret_of_sat_here`, through the packed
    object, now by `ret_hereWC` and `ret_map` along the unpacking map with the possible part
    carried (`holeAt_liftObj_wit`, `holeAt_liftVal_wit`). -/
theorem mem_ret_of_sat_here_wit (hS : ModalSys.BStrong = true) (hInj : B.ImgInj)
    (hT : ModalSys.T = true) {s : B.W} {i : ℕ} {N : NShape} {Z : VarType}
    {a : Ann (RShape.wit N Z).flat} (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (e : B.frame.Dom (RShape.wit N Z).ty s)
    (hΦ : B.model.sat (((B.canonEnv s i).boxPush (B.model.frame.reflAcc hT s)).extend (.bnd 0) e)
      Φ)
    (hcb : B.model.ComesBack (.wit N Z) e (B.model.frame.refl hT s)
      (Model.interp (B.canonEnv s i) t)) :
    (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈ (B.w s).M i := by
  have hsz : (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0).size =
      Φ.size + (RShape.wit N Z).flat.eqRecSize + 1 := rfl
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom (RShape.wit N Z).ty s e
  obtain ⟨_, g₁, _, g₂, hgp⟩ := getP_prod_some g
  obtain ⟨n, hn⟩ := NItems.exists_obj N g₁
  obtain ⟨_, t₁, _, t₂, ht⟩ := getP_prod_some t
  set J := max j₀ i
  have hj₀ : j₀ ≤ J := le_max_left _ _
  have hiJ : i ≤ J := le_max_right _ _
  set n' := n.mono ((B.w s).le hj₀)
  set p := (B.w s).liftT hj₀ g₂
  set u := Term.mono ((B.w s).le hiJ) t₂
  have hE : Model.interp (B.canonEnv s J)
      (Term.pair ((B.w s).liftT hj₀ g₁) ((B.w s).liftT hj₀ g₂)) = e := by
    rw [← interp_lift hg hj₀]
    exact congrArg (fun x => Model.interp (B.canonEnv s J) ((B.w s).liftT hj₀ x.2)) hgp.symm
  have he₁ : Model.interp (B.canonEnv s J) n'.obj.2 = e.1 := by
    have hn' : n'.obj = ⟨_, (B.w s).liftT hj₀ g₁⟩ := by
      rw [NItems.obj_mono, hn]
      rfl
    have hE₁ : Model.interp (B.canonEnv s J) ((B.w s).liftT hj₀ g₁) = e.1 := congrArg Prod.fst hE
    exact (congrArg (fun x : Σ c, Term σ ((B.w s).ctx J) N.ty c =>
      Model.interp (B.canonEnv s J) x.2) hn').trans hE₁
  have he₂ : Model.interp (B.canonEnv s J) p = e.2 := congrArg Prod.snd hE
  have hu : Model.interp (B.canonEnv s J) u = (Model.interp (B.canonEnv s i) t).2 :=
    (Model.interp_mono (canonEnv_le s hiJ) t₂).trans
      (congrArg (fun x : Σ c, Term σ ((B.w s).ctx i) (RShape.wit N Z).flat c =>
        (Model.interp (B.canonEnv s i) x.2).2) ht).symm
  -- the witness is realised here
  have hhere : WFF.here hT p u ∈ (B.w s).M J := by
    refine (IH s J _ (by
      rw [hsz]
      change Z.eqRecSize + 1 < Φ.size + (N.flat.eqRecSize + Z.eqRecSize + 1) + 1
      omega)).mp ?_
    change Model.Realised hT (Model.interp _ p) (Model.interp _ u)
    rw [he₂, hu]
    exact hcb.2
  -- the packed object, and the unpacking map
  set sb := n'.pack.2
  set F := unpackAt (σ := σ) hT N
    (Term.eta (.root (.bnd 0)) N.packTy (Ctx.ref_insert_root _ _ _))
  have hobj : (⟨_, Term.holeAt (Term.boxtm sb) F.obj.2⟩ : Σ c, Term σ ((B.w s).ctx J) N.ty c) =
      n'.obj :=
    holeAt_unpackAt_obj hT sb N _ n' (Term.holeAt_eta_root sb)
  have hFe₁ : B.model.holeVal F.obj.2 (Model.interp (B.canonEnv s J) (Term.boxtm sb)) = e.1 := by
    rw [← Model.interp_holeAt]
    exact (congrArg (fun x => Model.interp (B.canonEnv s J) x.2) hobj).trans he₁
  set S₀ : RShape := .wit (.boxC N.packTy _ (VarType.compOk_compsAllB true hT N.packTy)) Z
  have hFe : B.model.holeVal (ShapeMap.liftObj S₀ F).2
      (Model.interp (B.canonEnv s J) (Term.pair (Term.boxtm sb) p)) = e := by
    have h1 : Model.interp (B.canonEnv s J) (Term.holeAt (Term.boxtm sb) F.obj.2) = e.1 := by
      rw [Model.interp_holeAt]; exact hFe₁
    rw [← Model.interp_holeAt]
    refine (congrArg (fun x => Model.interp (B.canonEnv s J) x.2)
      (holeAt_liftObj_wit F (Term.boxtm sb) p)).trans ?_
    exact Prod.ext h1 he₂
  -- the body at the packed object
  set Φ' := WFF.mono (((B.w s).le hiJ).boxIn.insert (.bnd 0) _) Φ with hΦ'
  set Ψ := WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
    (ShapeMap.liftObj S₀ F).2) Φ' with hΨ
  have hsat : B.model.sat (B.canonEnv s J)
      (WFF.hereRead hT (Term.pair (Term.boxtm sb) p) Ψ) := by
    rw [Model.sat_hereRead hT (B.noProjLast s J)]
    refine (Model.sat_bodyRepl (Ctx.noProjLast_boxIn _) _ _ Φ' _).mpr ?_
    rw [Model.interp_mono (Model.Env.extend_agree (h := Ctx.empty_le _)
      (env := Model.Env.empty _) (fun _ _ h => nomatch h) (.bnd 0) _)]
    have hFe' : Model.interp ((Model.Env.empty (M := B.model) s).extend (.bnd 0)
        (Model.interp (B.canonEnv s J) (Term.pair (Term.boxtm sb) p)))
        (ShapeMap.liftObj S₀ F).2 = e := hFe
    rw [hFe']
    exact (Model.sat_mono (Model.Env.extend_agree
      (Model.Env.boxPush_agree (canonEnv_le s hiJ) (B.model.frame.reflAcc hT s)) (.bnd 0) e)
      Φ).mpr hΦ
  have hmb := (IH s J _ (by
    rw [WFF.size_hereRead, hsz, hΨ, hΦ']
    unfold WFF.bodyRepl
    rw [WFF.size_subst, WFF.size_mono]
    omega)).mp hsat
  -- the own arrow's rule at the packed object, then the unpacking map
  set V := Term.collapse (Ctx.collapses_boxIn_self hT ((B.w s).ctx J))
    (compsVal sb (N.packTy.compsAllB true) (VarType.compOk_compsAllB true hT _)).2
  have hmem : WFF.retS hS (.wit N Z) (Term.holeRead (Term.pair V u)
      (ShapeMap.liftVal S₀ F).2) Φ' ∈ (B.w s).M J :=
    BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hhere
        · rw [List.mem_singleton.mp hψ]; exact hmb)
      ⟨Proof.ret_map hS .nec (S := S₀) F _ Φ'
        (Proof.ret_hereWC hS hT sb _ _ p u Ψ (Proof.lookup List.mem_cons_self)
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  refine mem_ret_of_ind hS hInj (B.exists_R_of_T hT s) (S := .wit N Z) hiJ _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec, hsz]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _))).mp hs) hmem ?_
  -- the value denotes the object's readings home, and the content's value
  have hv : Model.interp (B.canonEnv s J) (Term.holeRead (Term.pair V u)
      (ShapeMap.liftVal S₀ F).2) =
      (B.model.NRead N e.1 (B.model.frame.refl hT s), Model.interp (B.canonEnv s J) u) := by
    rw [Term.holeRead_eq_holeAt]
    refine (congrArg (fun x => Model.interp (B.canonEnv s J) x.2)
      (holeAt_liftVal_wit F V u)).trans ?_
    refine Prod.ext ?_ rfl
    change Model.interp _ (Term.holeAt V F.val.2) = _
    rw [Model.interp_holeAt, Model.interp_collapse (Model.Env.collapseAgree_self hT _)]
    refine (congrArg (B.model.holeVal F.val.2)
      (Model.interp_compsVal (M := B.model) (B.canonEnv s J) sb s (B.model.frame.refl hT s)
        (N.packTy.compsAllB true) (VarType.compOk_compsAllB true hT _))).trans ?_
    rw [holeVal_unpackAt_compsRead hT, hFe₁]
  have hI : B.Ind (Model.interp (B.canonEnv s J) (Term.holeRead (Term.pair V u)
      (ShapeMap.liftVal S₀ F).2)) (Model.interp (B.canonEnv s i) t) := by
    rw [hv, hu]
    exact ind_pair
      (Model.ind_NRead (M := B.model) (fun h₁ h₂ => ind_pair h₁ h₂) N e.1 _ _ hcb.1)
      (B.Ind_refl _)
  rw [interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon t (Model.Env.Agree.refl' _)] at hI
  exact hI

/-- ⭐⭐**`ret` at a witnessed shape, truth ⇒ membership** (plain leg; strong B).  A true
    `◇[⟨d, e⟩ ↦ t] Φ(d, e)` has an arrow `s → k` (the own arrow: `mem_ret_of_sat_here_wit`)
    and an object there, `⟨N, diatm x u⟩` for some items and a term `u` of `x`'s view
    (`exists_wit`), with `Φ`.  The way home lies in `x`'s extent, so it is a witness edge of `k`
    made for `x` (`canonEnv_extent`, `dia_beta`); the body at `k` is in the theory by the
    induction hypothesis; the way home gives the atom valued at the items and `u` sent home
    (`RetInW`); and those are `Ind` to `t` (`ind_of_nComesBack`, `diaPush_canon_at`,
    `ind_pair`), so the value moves to `t` (`mem_ret_of_ind`). -/
theorem mem_ret_of_sat_wit (hS : ModalSys.BStrong = true) (hInj : B.ImgInj)
    (hRW : B.RetInW hS) {s : B.W} {i : ℕ} {N : NShape} {Z : VarType}
    {a : Ann (RShape.wit N Z).flat} (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : B.model.sat (B.canonEnv s i) (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0)) :
    (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈ (B.w s).M i := by
  have hsz : (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0).size =
      Φ.size + (RShape.wit N Z).flat.eqRecSize + 1 := rfl
  obtain ⟨⟨k, ⟨rk⟩⟩, e, hΦ, r, hcb⟩ := h
  rcases rk with hR | ⟨hT, rfl⟩
  swap
  · exact mem_ret_of_sat_here_wit hS hInj hT t Φ IH e hΦ hcb
  have hr' : B.RT k s := r
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom (RShape.wit N Z).ty k e
  obtain ⟨n, x, ⟨X, hX⟩, c', u, hgeq⟩ := exists_wit N Z g
  have hj₀ : j₀ ≤ max j₀ (B.stg s k i) := le_max_left _ _
  have hj : B.stg s k i ≤ max j₀ (B.stg s k i) := le_max_right _ _
  set J := max j₀ (B.stg s k i)
  have hX' : ((B.w k).ctx J).ref x = some (.VTypeDia X) := ((B.w k).le hj₀).ref hX
  set n' := n.mono ((B.w k).le hj₀)
  set u' := Term.mono (((B.w k).le hj₀).diaIn x) u
  have he : Model.interp (B.canonEnv k J)
      (Term.pair n'.obj.2 (Term.diatm x ⟨X, hX'⟩ u')) = e := by
    rw [← interp_lift hg hj₀]
    have e1 := congrArg (fun p : Σ c, Term σ ((B.w k).ctx j₀) (RShape.wit N Z).ty c =>
      Model.interp (B.canonEnv k J) ((B.w k).liftT hj₀ p.2)) hgeq
    refine Eq.trans ?_ e1.symm
    have e2 := congrArg (fun p : Σ c, Term σ ((B.w k).ctx J) N.ty c =>
      Model.interp (B.canonEnv k J) p.2) (NItems.obj_mono ((B.w k).le hj₀) n)
    exact Prod.ext e2 rfl
  have hsatb : B.model.sat (B.canonEnv k J)
      (readArrow ((B.imgOk hR i).mono ((B.w k).le hj))
        (Term.pair n'.obj.2 (Term.diatm x ⟨X, hX'⟩ u')) Φ) := by
    rw [sat_readArrow, he, ← boxPush_canon_at s i ⟨k, ⟨Or.inl hR⟩⟩ hR hj]
    exact hΦ
  have hmb := (IH k _ _ (by
    rw [hsz]; unfold readArrow; rw [WFF.size_subst]; omega)).mp hsatb
  subst he
  obtain ⟨hcbN, hcbD⟩ := hcb
  have hD : B.model.posEval ((Model.interp (B.canonEnv k J)
      (Term.pair n'.obj.2 (Term.diatm x ⟨X, hX'⟩ u'))).2 : B.model.frame.Pos Z k) =
      ⟨_, fun w' => Model.interp ((B.canonEnv k J).diaPush x hX' w') u'⟩ :=
    Model.dia_beta _ _ hX' u'
  revert hcbD
  generalize B.model.posEval ((Model.interp (B.canonEnv k J)
      (Term.pair n'.obj.2 (Term.diatm x ⟨X, hX'⟩ u'))).2 : B.model.frame.Pos Z k) = Q at hD ⊢
  subst hD
  rintro ⟨hmem, hcont⟩
  have hext : (⟨s, ⟨r⟩⟩ : B.Acc k) ∈ B.extent k x := canonEnv_extent k J hX' ▸ hmem
  rcases hext with ⟨X₁, hk⟩ | ⟨hnR, -⟩
  swap
  · exact absurd (B.symm hR) hnR
  obtain rfl := B.lb_hxX hk J X hX'
  obtain ⟨hiK, hret⟩ := hRW hR hk Φ hj hX' n' u' hmb
  refine mem_ret_of_ind hS hInj (S := .wit N Z) ⟨k, hR⟩ hiK _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec, hsz]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _))).mp hs) hret ?_
  have hcont' : B.Ind (Model.interp (B.canonEnv s (B.stg k s J))
      (Term.subst (arrowXIdx (B.img k s) x (B.cx k s x)) (arrowXS σ _ (B.img k s) x (B.cx k s x))
        (ok_arrowXS (B.imgOk (B.symm hR) J) hX' (B.lb_hcx hk J))
        (coh_arrowXS (B.imgOk (B.symm hR) J) hX' (B.lb_hcx hk J)) u'))
      (Model.interp (B.canonEnv s i) t).2 := by
    rw [Model.interp_subst _ _ _ (Ctx.noProjLast_diaIn _ x)]
    dsimp only at hcont
    rw [diaPush_canon_at k J hX' ⟨⟨s, ⟨r⟩⟩, hmem⟩ hk le_rfl] at hcont
    exact hcont
  have hI := ind_pair (ind_of_nComesBack hR hr' n' hcbN) hcont'
  rw [← interp_canon _ (Model.Env.Agree.refl' (B.canonEnv s (B.stg k s J))),
    ← interp_canon t (Model.Env.Agree.refl' (B.canonEnv s i))]
  exact hI

/-- ⭐⭐**`ret` along a witness at a witnessed shape at the own arrow, truth ⇒ membership** (T): as
    `mem_retx_of_sat_here` (the realised witness `y`, the body abstracted), with the possible
    part's `Here(p, t₂)` as in `mem_ret_of_sat_here_wit`, by `ret_hereXWC`. -/
theorem mem_retx_of_sat_here_wit (hS : ModalSys.BStrong = true) (hInj : B.ImgInj)
    (hT : ModalSys.T = true) {s : B.W} {i : ℕ} {y : VarSymb}
    (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape} {Z : VarType}
    {a : Ann (RShape.wit N Z).flat} (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ :
        WFF σ _ 0).size → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    {Y : VarType} (hY : ((B.w s).ctx i).ref y = some (.VTypeDia Y))
    (hm : B.model.frame.reflAcc hT s ∈ (B.model.posEval ((B.canonEnv s i).ref y hY)).1)
    (e : B.frame.Dom (RShape.wit N Z).ty s)
    (hΦ : B.model.sat (((B.canonEnv s i).diaPush y hY ⟨_, hm⟩).extend (.bnd 0) e) Φ)
    (hcb : B.model.ComesBack (.wit N Z) e (B.model.frame.refl hT s)
      (Model.interp (B.canonEnv s i) t)) :
    ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈
      (B.w s).M i := by
  have hsz : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ :
      WFF σ _ 0).size = Φ.size + (RShape.wit N Z).flat.eqRecSize + 1 := rfl
  have hr : (B.w s).Realised y :=
    (mem_extent_self (canonEnv_extent s i hY ▸ hm) fun ⟨_, hk⟩ => B.irrefl s (B.lbR hk)).2
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom (RShape.wit N Z).ty s e
  obtain ⟨_, g₁, _, g₂, hgp⟩ := getP_prod_some g
  obtain ⟨n, hn⟩ := NItems.exists_obj N g₁
  obtain ⟨_, t₁, _, t₂, ht⟩ := getP_prod_some t
  set J := max j₀ i
  set J' := max J hr.data.i₀
  have hJJ' : J ≤ J' := le_max_left _ _
  have hj₀ : j₀ ≤ J' := (le_max_left _ _).trans hJJ'
  have hiJ : i ≤ J := le_max_right _ _
  have hiJ' : i ≤ J' := hiJ.trans hJJ'
  have hYJ : ((B.w s).ctx J).ref y = some (.VTypeDia Y) := ((B.w s).le hiJ).ref hY
  have hYJ' : ((B.w s).ctx J').ref y = some (.VTypeDia Y) := ((B.w s).le hJJ').ref hYJ
  have hyJ' : ∃ Y, ((B.w s).ctx J').ref y = some (.VTypeDia Y) := ⟨Y, hYJ'⟩
  have hmJ : B.model.frame.reflAcc hT s ∈ (B.model.posEval ((B.canonEnv s J).ref y hYJ)).1 := by
    rw [canonEnv_extent] at hm ⊢
    exact hm
  have hmJ' : B.model.frame.reflAcc hT s ∈
      (B.model.posEval ((B.canonEnv s J').ref y hYJ')).1 := by
    rw [canonEnv_extent] at hm ⊢
    exact hm
  -- the witness `y`'s realisation here, and its value
  set bdJ := Term.eta (σ := σ) (.step y .dia) Y (Ctx.ref_diaIn_of hYJ)
  set bd := Term.eta (σ := σ) (.step y .dia) Y (Ctx.ref_diaIn_of hYJ')
  set t₀ := (B.realTerm hr (Ctx.Le.refl _) ⟨Y, hYJ⟩ bdJ).2
  have hh : WFF.here hT (Term.diatm y hyJ' bd) t₀ ∈ (B.w s).M J' := by
    have h := mem_here_real hr hYJ bdJ
    change WFF.here _ (Term.diatm y _ (Term.mono _ (Term.eta _ _ _))) _ ∈ _ at h
    rwa [Term.mono_eta] at h
  have hcont : Model.interp ((B.canonEnv s J').diaPush y hYJ' ⟨_, hmJ'⟩) bd =
      Model.interp (B.canonEnv s J') t₀ := by
    rw [show bd = Term.mono (((B.w s).le hJJ').diaIn y) bdJ from (Term.mono_eta _ _ _ _).symm,
      Model.interp_mono (Model.Env.diaPush_agree (canonEnv_le s hJJ') hYJ ⟨_, hmJ⟩ hmJ'),
      interp_dia_self hr (fun {_Γ'} {_b} u {_k} {_e'} {_env'} hag' => interp_canon u hag')
        (fun _ _ _ => rfl) hYJ hT hmJ bdJ]
    exact (interp_canon t₀ (fun _ _ _ => rfl)).symm
  -- the object's parts, and the content's value
  set n' := n.mono ((B.w s).le hj₀)
  set p := (B.w s).liftT hj₀ g₂
  set u := Term.mono ((B.w s).le hiJ') t₂
  have hE : Model.interp (B.canonEnv s J')
      (Term.pair ((B.w s).liftT hj₀ g₁) ((B.w s).liftT hj₀ g₂)) = e := by
    rw [← interp_lift hg hj₀]
    exact congrArg (fun x => Model.interp (B.canonEnv s J') ((B.w s).liftT hj₀ x.2)) hgp.symm
  have he₁ : Model.interp (B.canonEnv s J') n'.obj.2 = e.1 := by
    have hn' : n'.obj = ⟨_, (B.w s).liftT hj₀ g₁⟩ := by
      rw [NItems.obj_mono, hn]
      rfl
    have hE₁ : Model.interp (B.canonEnv s J') ((B.w s).liftT hj₀ g₁) = e.1 := congrArg Prod.fst hE
    exact (congrArg (fun x : Σ c, Term σ ((B.w s).ctx J') N.ty c =>
      Model.interp (B.canonEnv s J') x.2) hn').trans hE₁
  have he₂ : Model.interp (B.canonEnv s J') p = e.2 := congrArg Prod.snd hE
  have hu : Model.interp (B.canonEnv s J') u = (Model.interp (B.canonEnv s i) t).2 :=
    (Model.interp_mono (canonEnv_le s hiJ') t₂).trans
      (congrArg (fun x : Σ c, Term σ ((B.w s).ctx i) (RShape.wit N Z).flat c =>
        (Model.interp (B.canonEnv s i) x.2).2) ht).symm
  -- the possible part is realised here
  have hhere : WFF.here hT p u ∈ (B.w s).M J' := by
    refine (IH s J' _ (by
      rw [hsz]
      change Z.eqRecSize + 1 < Φ.size + (N.flat.eqRecSize + Z.eqRecSize + 1) + 1
      omega)).mp ?_
    change Model.Realised hT (Model.interp _ p) (Model.interp _ u)
    rw [he₂, hu]
    exact hcb.2
  -- the packed object, and the unpacking map
  set sb := n'.pack.2
  set F := unpackAt (σ := σ) hT N
    (Term.eta (.root (.bnd 0)) N.packTy (Ctx.ref_insert_root _ _ _))
  have hobj : (⟨_, Term.holeAt (Term.boxtm sb) F.obj.2⟩ : Σ c, Term σ ((B.w s).ctx J') N.ty c) =
      n'.obj :=
    holeAt_unpackAt_obj hT sb N _ n' (Term.holeAt_eta_root sb)
  have hFe₁ : B.model.holeVal F.obj.2 (Model.interp (B.canonEnv s J') (Term.boxtm sb)) = e.1 := by
    rw [← Model.interp_holeAt]
    exact (congrArg (fun x => Model.interp (B.canonEnv s J') x.2) hobj).trans he₁
  set S₀ : RShape := .wit (.boxC N.packTy _ (VarType.compOk_compsAllB true hT N.packTy)) Z
  have hFe : B.model.holeVal (ShapeMap.liftObj S₀ F).2
      (Model.interp (B.canonEnv s J') (Term.pair (Term.boxtm sb) p)) = e := by
    have h1 : Model.interp (B.canonEnv s J') (Term.holeAt (Term.boxtm sb) F.obj.2) = e.1 := by
      rw [Model.interp_holeAt]; exact hFe₁
    rw [← Model.interp_holeAt]
    refine (congrArg (fun x => Model.interp (B.canonEnv s J') x.2)
      (holeAt_liftObj_wit F (Term.boxtm sb) p)).trans ?_
    exact Prod.ext h1 he₂
  -- the body at the packed object, abstracted
  set Φ' := WFF.mono ((((B.w s).le hiJ').diaIn y).insert (.bnd 0) _) Φ with hΦ'
  set Ψ := WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
    (ShapeMap.liftObj S₀ F).2) Φ' with hΨ
  set χ := WFF.bodyAbsA y hYJ' Ψ with hχ
  have hsat : B.model.sat (B.canonEnv s J')
      (WFF.hereRead hT (Term.pair t₀ (Term.pair (Term.boxtm sb) p)) χ) := by
    rw [Model.sat_hereRead hT (B.noProjLast s J')]
    have hpp : Model.interp (B.canonEnv s J') (Term.pair t₀ (Term.pair (Term.boxtm sb) p)) =
        (Model.interp ((B.canonEnv s J').diaPush y hYJ' ⟨_, hmJ'⟩) bd,
          Model.interp (B.canonEnv s J') (Term.pair (Term.boxtm sb) p)) :=
      Prod.ext hcont.symm rfl
    rw [hpp]
    refine (Model.sat_viewBody_here' (B.canonEnv s J') hT hyJ' hYJ' bd χ hmJ' _).mp ?_
    rw [hχ, WFF.viewBody_bodyAbsA]
    refine (Model.sat_bodyRepl (Ctx.noProjLast_diaIn _ y) _ _ Φ' _).mpr ?_
    rw [Model.interp_mono (Model.Env.extend_agree (h := Ctx.empty_le _)
      (env := Model.Env.empty _) (fun _ _ h => nomatch h) (.bnd 0) _)]
    have hFe' : Model.interp ((Model.Env.empty (M := B.model) s).extend (.bnd 0)
        (Model.interp (B.canonEnv s J') (Term.pair (Term.boxtm sb) p)))
        (ShapeMap.liftObj S₀ F).2 = e := hFe
    rw [hFe']
    exact (Model.sat_mono (Model.Env.extend_agree
      (Model.Env.diaPush_agree (canonEnv_le s hiJ') hY ⟨_, hm⟩ hmJ') (.bnd 0) e) Φ).mpr hΦ
  have hmb := (IH s J' _ (by
    rw [WFF.size_hereRead, hsz, hχ]
    unfold WFF.bodyAbsA
    rw [WFF.size_subst, hΨ]
    unfold WFF.bodyRepl
    rw [WFF.size_subst, hΦ', WFF.size_mono]
    omega)).mp hsat
  -- the own arrow's rule along `y` at the packed object, then the unpacking map
  set V := Term.collapse (Ctx.collapses_boxIn_self hT ((B.w s).ctx J'))
    (compsVal sb (N.packTy.compsAllB true) (VarType.compOk_compsAllB true hT _)).2
  have hpf : Proof σ ((B.w s).ctx J')
      [WFF.here hT (Term.diatm y hyJ' bd) t₀, WFF.here hT p u,
        WFF.hereRead hT (Term.pair t₀ (Term.pair (Term.boxtm sb) p)) χ]
      ((OutLeg.pos y hyJ' : OutLeg ((B.w s).ctx J')).retS hS S₀ (Term.pair V u) Ψ) := by
    have h := Proof.ret_hereXWC (Δ := [WFF.here hT (Term.diatm y hyJ' bd) t₀, WFF.here hT p u,
      WFF.hereRead hT (Term.pair t₀ (Term.pair (Term.boxtm sb) p)) χ]) hS hT y hyJ' bd t₀ sb
      (N.packTy.compsAllB true) (VarType.compOk_compsAllB true hT N.packTy) p u χ
      (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [hχ, WFF.viewBody_bodyAbsA] at h
    exact h
  have hmem : (OutLeg.pos y hyJ' : OutLeg ((B.w s).ctx J')).retS hS (.wit N Z)
      (Term.holeRead (Term.pair V u) (ShapeMap.liftVal S₀ F).2) Φ' ∈ (B.w s).M J' :=
    BWorld.mem_of_provable (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hh
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hhere
        · rw [List.mem_singleton.mp hψ]; exact hmb)
      ⟨Proof.ret_map hS (.pos y hyJ') (S := S₀) F _ Φ' hpf⟩
  refine mem_retx_of_ind hS hInj (B.exists_R_of_T hT s) (S := .wit N Z) hiJ' hy _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec, hsz]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _))).mp hs) hmem ?_
  -- the value denotes the object's readings home, and the content's value
  have hv : Model.interp (B.canonEnv s J') (Term.holeRead (Term.pair V u)
      (ShapeMap.liftVal S₀ F).2) =
      (B.model.NRead N e.1 (B.model.frame.refl hT s), Model.interp (B.canonEnv s J') u) := by
    rw [Term.holeRead_eq_holeAt]
    refine (congrArg (fun x => Model.interp (B.canonEnv s J') x.2)
      (holeAt_liftVal_wit F V u)).trans ?_
    refine Prod.ext ?_ rfl
    change Model.interp _ (Term.holeAt V F.val.2) = _
    rw [Model.interp_holeAt, Model.interp_collapse (Model.Env.collapseAgree_self hT _)]
    refine (congrArg (B.model.holeVal F.val.2)
      (Model.interp_compsVal (M := B.model) (B.canonEnv s J') sb s (B.model.frame.refl hT s)
        (N.packTy.compsAllB true) (VarType.compOk_compsAllB true hT _))).trans ?_
    rw [holeVal_unpackAt_compsRead hT, hFe₁]
  have hI : B.Ind (Model.interp (B.canonEnv s J') (Term.holeRead (Term.pair V u)
      (ShapeMap.liftVal S₀ F).2)) (Model.interp (B.canonEnv s i) t) := by
    rw [hv, hu]
    exact ind_pair
      (Model.ind_NRead (M := B.model) (fun h₁ h₂ => ind_pair h₁ h₂) N e.1 _ _ hcb.1)
      (B.Ind_refl _)
  rw [interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon t (Model.Env.Agree.refl' _)] at hI
  exact hI

/-- ⭐⭐**`ret` along a witness at a witnessed shape, truth ⇒ membership** (strong B): as
    `mem_ret_of_sat_wit`, along an arrow of `y`'s extent (the own arrow:
    `mem_retx_of_sat_here_wit`) (`RetInWX`, `diaPush_canon_at`,
    `mem_retx_of_ind`). -/
theorem mem_retx_of_sat_wit (hS : ModalSys.BStrong = true) (hInj : B.ImgInj)
    (hRWX : B.RetInWX hS) {s : B.W} {i : ℕ} {y : VarSymb}
    (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape} {Z : VarType}
    {a : Ann (RShape.wit N Z).flat} (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ :
        WFF σ _ 0).size → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ : WFF σ _ 0)) :
    ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈
      (B.w s).M i := by
  have hsz : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.wit N Z) t Φ :
      WFF σ _ 0).size = Φ.size + (RShape.wit N Z).flat.eqRecSize + 1 := rfl
  obtain ⟨Y, hY, a₁, e, hΦ, r, hcb⟩ := h
  obtain ⟨⟨k, ⟨rk⟩⟩, ha⟩ := a₁
  have hext : (⟨k, ⟨rk⟩⟩ : B.Acc s) ∈ B.extent s y := canonEnv_extent s i hY ▸ ha
  rcases hext with ⟨Y', hky⟩ | ⟨hnR, -⟩
  swap
  · rcases rk with hR | ⟨hT, rfl⟩
    · exact absurd hR hnR
    · exact mem_retx_of_sat_here_wit hS hInj hT hy t Φ IH hY ha e hΦ hcb
  obtain rfl := B.lb_hxX hky i Y hY
  have hR := B.lbR hky
  have hr' : B.RT k s := r
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom (RShape.wit N Z).ty k e
  obtain ⟨n, x, ⟨X, hX⟩, c', u, hgeq⟩ := exists_wit N Z g
  have hj₀ : j₀ ≤ max j₀ (B.stg s k i) := le_max_left _ _
  have hj : B.stg s k i ≤ max j₀ (B.stg s k i) := le_max_right _ _
  set J := max j₀ (B.stg s k i)
  have hX' : ((B.w k).ctx J).ref x = some (.VTypeDia X) := ((B.w k).le hj₀).ref hX
  set n' := n.mono ((B.w k).le hj₀)
  set u' := Term.mono (((B.w k).le hj₀).diaIn x) u
  have he : Model.interp (B.canonEnv k J)
      (Term.pair n'.obj.2 (Term.diatm x ⟨X, hX'⟩ u')) = e := by
    rw [← interp_lift hg hj₀]
    have e1 := congrArg (fun p : Σ c, Term σ ((B.w k).ctx j₀) (RShape.wit N Z).ty c =>
      Model.interp (B.canonEnv k J) ((B.w k).liftT hj₀ p.2)) hgeq
    refine Eq.trans ?_ e1.symm
    have e2 := congrArg (fun p : Σ c, Term σ ((B.w k).ctx J) N.ty c =>
      Model.interp (B.canonEnv k J) p.2) (NItems.obj_mono ((B.w k).le hj₀) n)
    exact Prod.ext e2 rfl
  have hsatb : B.model.sat (B.canonEnv k J)
      (readArrowX ((B.imgOk hR i).mono ((B.w k).le hj)) hY ((B.w k).le hj |>.ref (B.lb_hcx hky i))
        (Term.pair n'.obj.2 (Term.diatm x ⟨X, hX'⟩ u')) Φ) := by
    rw [sat_readArrowX, he, ← diaPush_canon_at s i hY ⟨⟨k, ⟨rk⟩⟩, ha⟩ hky hj]
    exact hΦ
  have hmb := (IH k _ _ (by
    rw [hsz]; unfold readArrowX; rw [WFF.size_subst]; omega)).mp hsatb
  subst he
  obtain ⟨hcbN, hcbD⟩ := hcb
  have hD : B.model.posEval ((Model.interp (B.canonEnv k J)
      (Term.pair n'.obj.2 (Term.diatm x ⟨X, hX'⟩ u'))).2 : B.model.frame.Pos Z k) =
      ⟨_, fun w' => Model.interp ((B.canonEnv k J).diaPush x hX' w') u'⟩ :=
    Model.dia_beta _ _ hX' u'
  revert hcbD
  generalize B.model.posEval ((Model.interp (B.canonEnv k J)
      (Term.pair n'.obj.2 (Term.diatm x ⟨X, hX'⟩ u'))).2 : B.model.frame.Pos Z k) = Q at hD ⊢
  subst hD
  rintro ⟨hmem, hcont⟩
  have hext' : (⟨s, ⟨r⟩⟩ : B.Acc k) ∈ B.extent k x := canonEnv_extent k J hX' ▸ hmem
  rcases hext' with ⟨X₁, hkx⟩ | ⟨hnR, -⟩
  swap
  · exact absurd (B.symm hR) hnR
  obtain rfl := B.lb_hxX hkx J X hX'
  obtain ⟨hiK, hret⟩ := hRWX hky hkx hY Φ hj hX' n' u' hmb
  refine mem_retx_of_ind hS hInj (S := .wit N Z) ⟨k, hR⟩ hiK hy _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec, hsz]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _))).mp hs) hret ?_
  have hcont' : B.Ind (Model.interp (B.canonEnv s (B.stg k s J))
      (Term.subst (arrowXIdx (B.img k s) x (B.cx k s x)) (arrowXS σ _ (B.img k s) x (B.cx k s x))
        (ok_arrowXS (B.imgOk (B.symm hR) J) hX' (B.lb_hcx hkx J))
        (coh_arrowXS (B.imgOk (B.symm hR) J) hX' (B.lb_hcx hkx J)) u'))
      (Model.interp (B.canonEnv s i) t).2 := by
    rw [Model.interp_subst _ _ _ (Ctx.noProjLast_diaIn _ x)]
    dsimp only at hcont
    rw [diaPush_canon_at k J hX' ⟨⟨s, ⟨r⟩⟩, hmem⟩ hkx le_rfl] at hcont
    exact hcont
  have hI := ind_pair (ind_of_nComesBack hR hr' n' hcbN) hcont'
  rw [← interp_canon _ (Model.Env.Agree.refl' (B.canonEnv s (B.stg k s J))),
    ← interp_canon t (Model.Env.Agree.refl' (B.canonEnv s i))]
  exact hI

end BData

end BArrow

end V12M
