import QML.QML_v12m_BBackLimit

/-!
# QML v12m — B's canonical model: the returning possibility's truth cases (strong B, T off)

The truth lemma's `ret` cases (docs §11.20, "Step 5 begun"), built a slice at a time.

* `packT`: a term of a node's `□` view packed into a hole term over the tuple of its roots'
  items, as `pack` packs formulas; read at the tuple it is the term (`holeRead_tupT_packT`), at
  the tuple of the images the term sent along the arrow (`holeRead_tupImgT_packT`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Packing terms -/

/-- ⭐A term of the `□` view of `ctxOf l`, packed into a hole term over the tuple of the roots'
    items. -/
def packT (l : List VarType) {A : VarType} {b : Ann A} (u : Term σ (ctxOf l).boxIn A b) :
    Term σ (Ctx.empty.insert (.bnd 0) (bcT l)) A (b.mapIdx (packIdx l (.root (.bnd 0)))) :=
  Term.subst (packIdx l (.root (.bnd 0))) (packS σ (packCtx l) l (.root (.bnd 0)))
    (ok_packS l (packCtx_ref l)) (coh_packS l (packCtx_ref l)) u

/-- ⭐A term of the `□` view is its packing read at the tuple of all the roots' items. -/
theorem holeRead_tupT_packT (l : List VarType) {A : VarType} {b : Ann A}
    (u : Term σ (ctxOf l).boxIn A b) :
    (⟨_, Term.holeRead (tupT l).2 (packT l u)⟩ : Σ b', Term σ (ctxOf l).boxIn A b') = ⟨b, u⟩ := by
  unfold Term.holeRead packT
  rw [Term.subst_mono]
  refine (Term.subst_comp_sig _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS ?_ u).trans
    ((Term.subst_idS_mono (Ctx.Le.refl _) _ _ u).trans (congrArg (Sigma.mk _) (Term.mono_refl _ u)))
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨w, rfl, hw⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, _⟩ := ref_rt hw
  change SubE.Sim T (.ren (.step w .box))
    ((Subst.single (.bnd 0) (.tm (tupT l).2)).at
      ((packBase l (.root (.bnd 0)) w.rt).ext (encPath w.path ++ itemTail)))
  rw [hr]
  change SubE.Sim T _ ((Subst.single (.bnd 0) _).at
    (((VarSymb.root (.bnd 0)).ext (tupPath l r)).ext (encPath w.path ++ itemTail)))
  have h0 : (Subst.single (σ := σ) (Δ := (ctxOf l).boxIn) (.bnd 0)
      (.tm (tupT l).2)).at (.root (.bnd 0)) = .tm (Term.mono (Ctx.Le.refl _) (tupT l).2) := by
    rw [Term.mono_refl]
    change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
    exact if_pos rfl
  obtain ⟨R, hR, h1⟩ := at_tupPath_tupT _ l _ h0 hlt
  rw [Term.mono_refl] at h1
  have h2 := at_enc_tupB _ ModalSys.T rfl hR h1 hw hr
  rw [at_item_of_tupB_base _ _ hw ModalSys.T rfl h2]
  exact .ren_eta _ _

/-- ⭐A packed term read at the tuple of the roots' images is the term sent along the arrow. -/
theorem holeRead_tupImgT_packT {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {A : VarType} {b : Ann A} (u : Term σ (ctxOf l).boxIn A b) :
    (⟨_, Term.holeRead (tupImgT l img himg).2 (packT l u)⟩ : Σ b', Term σ Δ A b') =
      ⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg) u⟩ := by
  unfold Term.holeRead packT
  rw [Term.subst_mono]
  refine Term.subst_comp_sig _ _ (arrowS σ Δ img) _ _ _ _ (ok_arrowS himg) (coh_arrowS himg) ?_ u
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨w, rfl, hw⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, hR⟩ := ref_rt hw
  change SubE.Sim T (.ren (itemAt (imgRoot img w.rt) w))
    ((Subst.single (.bnd 0) (.tm (tupImgT l img himg).2)).at
      ((packBase l (.root (.bnd 0)) w.rt).ext (encPath w.path ++ itemTail)))
  have hz : Δ.ref (.root (imgRoot img w.rt)) = some (rootTy l r).bc := by
    rw [hr]; exact himg r hlt
  have hT := ref_item hw hR hz
  rw [hr] at hz hT ⊢
  change SubE.Sim T (.ren ((VarSymb.root (.free (img r))).ext (encPath w.path ++ itemTail)))
    ((Subst.single (.bnd 0) _).at
      (((VarSymb.root (.bnd 0)).ext (tupPath l r)).ext (encPath w.path ++ itemTail)))
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
      (.tm (tupImgT l img himg).2)).at (.root (.bnd 0)) = .tm (tupImgT l img himg).2 := by
    change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
    exact if_pos rfl
  obtain ⟨T', hT', h1⟩ := at_tupPath_tupImgT _ l himg h0 hlt
  refine sim_ren_at_ext _ _ ((PPath.encPath (reach_ppath hw).1).append PPath.itemTail) hT' hT ?_
  rw [h1]
  exact .ren_eta _ _

/-- ⭐A packed term read at the roots' items, weakened into a larger context: the term, weakened. -/
theorem holeAt_tupT_packT_mono {l : List VarType} {Δ : Ctx} (hle : (ctxOf l).boxIn.Le Δ)
    {A : VarType} {b : Ann A} (u : Term σ (ctxOf l).boxIn A b) :
    (⟨_, Term.holeAt (Term.mono hle (tupT l).2) (packT l u)⟩ : Σ b', Term σ Δ A b') =
      ⟨_, Term.mono hle u⟩ := by
  unfold Term.holeAt packT
  refine (Term.subst_comp_sig _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le hle)
    (Subst.coh_idS_le hle) ?_ u).trans (Term.subst_idS_mono hle _ _ u)
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨w, rfl, hw⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, _⟩ := ref_rt hw
  change SubE.Sim T (.ren (.step w .box))
    ((Subst.single (.bnd 0) (.tm (Term.mono hle (tupT l).2))).at
      ((packBase l (.root (.bnd 0)) w.rt).ext (encPath w.path ++ itemTail)))
  rw [hr]
  change SubE.Sim T _ ((Subst.single (.bnd 0) _).at
    (((VarSymb.root (.bnd 0)).ext (tupPath l r)).ext (encPath w.path ++ itemTail)))
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
      (.tm (Term.mono hle (tupT l).2))).at (.root (.bnd 0)) = .tm (Term.mono hle (tupT l).2) := by
    change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
    exact if_pos rfl
  obtain ⟨R, hR, h1⟩ := at_tupPath_tupT _ l hle h0 hlt
  have h2 := at_enc_tupB_mono hle _ ModalSys.T rfl hR h1 hw hr
  rw [at_item_of_tupB_base_mono hle _ _ hw ModalSys.T rfl h2, Term.mono_eta]
  exact .ren_eta _ _

omit [ModalSys.NoFour] in
theorem sig_holeAt {Γ : Ctx} {A : VarType} {a a' : Ann A} {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    (h : (⟨a, t⟩ : Σ c, Term σ Γ A c) = ⟨a', t'⟩) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.holeAt t s⟩ : Σ c, Term σ Γ B c) = ⟨_, Term.holeAt t' s⟩ := by
  cases h
  rfl

/-! ## A body read along an arrow, its slot filled -/

/-- ⭐A body over the `□` view of `l` with a slot, read along an arrow (`img`) into `Δ`, its slot
    filled by `g`. -/
def readArrow {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ} (himg : ImgOk l Δ img)
    {B : VarType} {c : Ann B} (g : Term σ Δ B c) (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) B) 1) :
    WFF σ Δ 0 :=
  WFF.subst (Subst.setIdx (arrowIdx img) (.bnd 0) (.tm g))
    ((arrowS σ Δ img).set (.bnd 0) (.tm g))
    (Subst.ok_set (ok_arrowS himg) rfl)
    (Subst.coh_set (ok_arrowS himg) (coh_arrowS himg)
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert _) Ctx.NoSlots.slots Φ

/-- ⭐**The body `Φ(□u[D])` read at the far end** is `Φ(□u)` read along the reverse arrow: packing
    `u` over the committed roots' tuple and reading it at the tuple's items gives `u` back
    (`holeAt_tupT_packT_mono`). -/
theorem liftBody_bodyRepl_hole {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {A : VarType} {b : Ann A}
    (u : Term σ (ctxOf cls).boxIn A b)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) :
    liftBody hs himgt (WFF.bodyRepl
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (ShapeMap.hole (packT cls u)).obj.2) Φ) =
      readArrow himgt (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn u)) Φ := by
  unfold liftBody WFF.bodyRepl readArrow
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T _ hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = .VTypeBox A := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) _ (.root (.bnd 0)))
      ((((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))).comp _ _ _)
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (Eq.symm ?_)
    rw [Term.subst_mono]
    change (⟨_, Term.boxtm (Term.subst _ _ _ _ (Term.holeAt _ (packT cls u)))⟩ :
      Σ c, Term σ (ctxOf lv) (.VTypeBox A) c) = _
    refine sig_boxtm ?_
    refine (Term.subst_holeAt_sig _ _ _ _ _).trans ?_
    refine (sig_holeAt (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ (by
      change Subst.set _ _ _ (.root (.bnd 0)) = _
      exact Subst.set_root _ _ _))) _).trans ?_
    exact holeAt_tupT_packT_mono _ u
  · have hv' : (ctxOf clt).boxIn v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    obtain ⟨w, rfl, hw⟩ := boxIn_item' hv'
    change SubE.Sim T ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) _ (.step w .box))
      ((((Subst.idS σ _).set (.bnd 0) _) (.step w .box)).comp _ _ _)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim T _ ((Subst.set _ _ _).at (.step w .box))
    rw [Subst.at_set_of_rt_ne _ _ (Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0))
      ((Ctx.ref_nonproj _ rfl).trans hv'))]
    exact .refl _

/-- ⭐⭐**A returning possibility from its far end, at a node**: along an arrow `k → s` with the
    invariant, `Φ(□u)` at `k` (read along the reverse arrow) is `◇[d ↦ u sent home] Φ(d)` at `s` —
    the invariant at the body `Φ(□u[D])` (`liftBody_bodyRepl_hole`), then `ret_map` along the hole
    of the packed `u` (`holeRead_tupImgT_packT`). -/
theorem ret_of_inv {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hsM : Theory.IsMCS ts.M)
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} (h : RetInv hS tk ts cls imgs clt imgt)
    {A : VarType} {b : Ann A} (u : Term σ (ctxOf cls).boxIn A b)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox A)) 1)
    (hmem : ∃ (hs : cls <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt),
      readArrow himgt (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn u)) Φ ∈ tk.M) :
    ∃ (himgs : ImgOk cls (ctxOf ts.l) imgs) (ht : clt <:+ ts.l),
      WFF.ret hS (Term.subst (arrowIdx imgs) (arrowS σ (ctxOf ts.l) imgs) (ok_arrowS himgs)
        (coh_arrowS himgs) u)
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ ts.M := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  obtain ⟨hs', himgt', hm⟩ := hmem
  refine ⟨himgs, ht, ?_⟩
  have hr := hinv (WFF.bodyRepl
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (ShapeMap.hole (packT cls u)).obj.2) Φ)
    (by rw [liftBody_bodyRepl_hole]; exact hm)
  rw [WFF.mono_bodyRepl (ctxOf_le_of_suffix ht).boxIn, Term.mono_mono] at hr
  have hc := hsM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
    ⟨Proof.ret_map hS .nec (S := .nec (.box (bcT cls))) (ShapeMap.hole (packT cls u))
      (tupImgT cls imgs himgs).2 (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ)
      (Proof.lookup List.mem_cons_self)⟩⟩
  exact (congrArg (· ∈ ts.M) (OutLeg.retS_congr hS .nec (.box A)
    (holeRead_tupImgT_packT himgs u) rfl)).mp hc

/-- Reading a body along an arrow, then weakening, is reading the weakened body along any arrow
    that agrees on its roots. -/
theorem readArrow_mono_congr {l l' : List VarType} (hl : l <:+ l') {Δ Δ' : Ctx} [Δ.NoSlots]
    [Δ'.NoSlots] (hΔ : Δ.Le Δ') {img img' : ℕ → ℕ} (himg : ImgOk l Δ img)
    (himg' : ImgOk l' Δ' img') (hag : ∀ r < l.length, img r = img' r) {B : VarType} {c : Ann B}
    (g : Term σ Δ B c) (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) B) 1) :
    WFF.mono hΔ (readArrow himg g Φ) =
      readArrow himg' (Term.mono hΔ g)
        (WFF.mono ((ctxOf_le_of_suffix hl).boxIn.insert (.bnd 0) B) Φ) := by
  unfold readArrow
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim T (SubE.mono hΔ (Subst.set _ _ _ (.root (.bnd 0))))
      (Subst.set _ _ _ (.root (.bnd 0)))
    rw [Subst.set_root, Subst.set_root]
    exact .refl _
  · have hv' : (ctxOf l).boxIn v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    obtain ⟨w, rfl, hw⟩ := boxIn_item hv'
    obtain ⟨r, hr, hlt, _⟩ := ref_rt hw
    change SubE.Sim T (SubE.mono hΔ (Subst.set _ _ _ (.step w .box)))
      (Subst.set _ _ _ (.step w .box))
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim T (.ren (itemAt (imgRoot img w.rt) w)) (.ren (itemAt (imgRoot img' w.rt) w))
    rw [hr, imgRoot, imgRoot, hag r hlt]
    exact .refl _

namespace BData

variable (B : BData σ) (hS : ModalSys.BStrong = true)

/-- ⭐**Returning possibilities from the far end** (plain leg, `□` shape): along an arrow `s → k`,
    `Φ(□u)` at `k` (read along the arrow) is `◇[d ↦ u sent home] Φ(d)` at `s`.  The limit of a
    strong chain has it (`bdataS_retIn`). -/
def RetIn : Prop :=
  ∀ {s k : B.W} (h : B.R s k) {i : ℕ} {A : VarType}
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (.VTypeBox A)) 1) {j : ℕ}
    (hj : B.stg s k i ≤ j) {b : Ann A} (u : Term σ ((B.w k).ctx j).boxIn A b),
    readArrow ((B.imgOk h i).mono ((B.w k).le hj)) (Term.boxtm u) Φ ∈ (B.w k).M j →
      ∃ hiK : i ≤ B.stg k s j,
        WFF.ret hS (Term.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
          (ok_arrowS (B.imgOk (B.symm h) j)) (coh_arrowS (B.imgOk (B.symm h) j)) u)
          (WFF.mono (((B.w s).le hiK).boxIn.insert (.bnd 0) _) Φ) ∈ (B.w s).M (B.stg k s j)

end BData

section Limit

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐⭐**The limit has returning possibilities from the far end**: the invariant of the way home
    `k → s` (`lretAt`, reduced by `RetAt.toRetInv`), at a node (`ret_of_inv`). -/
theorem bdataS_retIn (hT : ModalSys.T = false) : (bdataS C hT).RetIn hS := by
  classical
  intro s k h i A Φ j hj b u hm
  obtain ⟨cls, imgs, clt, imgt, hJs, hJag, his, hiag, hret⟩ := lretAt C h.symm j i hj
  have hsp := (lstg_spec C.toFairChain h i).1
  have hkp := (lstg_spec C.toFairChain h.symm j).1
  have hiK : i ≤ lstg C.toFairChain k s j := by
    change lstg C.toFairChain s k i ≤ j at hj
    omega
  have hsl : (C.net (birth C.toFairChain s.2 + lstg C.toFairChain k s j)).Live s.1 :=
    live_birth C.toFairChain s.2 (Nat.le_add_right _ _)
  have hsM := (C.good _).mcs s.1 hsl
  have hinv := RetAt.toRetInv hsM hret
  obtain ⟨hcs, -, ht, himgt, -⟩ := id hinv
  -- what `k` has at stage `j`, grown to the round of the invariant
  have hg := grow_stage C.toFairChain k j (m := birth C.toFairChain s.2 +
    lstg C.toFairChain k s j) hkp
  have hm' := hg.sub _ hm
  rw [readArrow_mono_congr his _ _ himgt (fun r hr => (hiag r hr).symm)] at hm'
  obtain ⟨himgs, ht', hr⟩ := ret_of_inv hsM hinv
    (Term.mono (ctxOf_le_of_suffix hJs).boxIn u) _
    ⟨hcs, himgt, by
      convert hm' using 2
      change _ = Term.boxtm (Term.mono _ u)
      rw [Term.mono_mono]⟩
  refine ⟨hiK, (congrArg (· ∈ _) (OutLeg.retS_congr hS .nec (.box A) ?_ ?_)).mp hr⟩
  · rw [Term.subst_mono]
    exact Term.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
  · rw [WFF.mono_mono]

end Limit

end BArrow

end V12M
