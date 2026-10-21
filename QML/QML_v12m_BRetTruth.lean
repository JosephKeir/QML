import QML.QML_v12m_BItems

/-!
# QML v12m — B's canonical model: the returning possibility's truth cases (strong B)

The truth lemma's `ret` cases (docs §11.20, "Step 5 begun"), built a slice at a time.

* `packT`: a term of a node's `□` view packed into a hole term over the tuple of its roots'
  items, as `pack` packs formulas; read at the tuple it is the term (`holeRead_tupT_packT`), at
  the tuple of the images the term sent along the arrow (`holeRead_tupImgT_packT`).
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model σ}

/-- Substituting a term for one more root extends the substituted environment by its value. -/
theorem substEnv_set_tm {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) {r : Root} {T : VarType}
    {a : Ann T} (g : Term σ Δ T a) :
    substEnv (θ.set r (.tm g)) (Subst.ok_set hθ rfl) (hnp.insert r T) env =
      (substEnv θ hθ hnp env).extend r (interp env g) := by
  funext v U hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [Env.extend_root _ _ _ hv]
    exact entryVal_congr env (Subst.set_root θ r (.tm g)) _ (show (SubE.tm g).OkRef T from rfl)
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [Env.extend_ne (substEnv θ hθ hnp env) _ _ hv hvr hv']
    exact entryVal_congr env (Subst.set_ne θ _ hvr) _ _

end Model

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

/-! ## The tuple's value with companions through `holeC` -/

omit [ModalSys.NoFour] in
/-- A sigma equation of terms is one of entries. -/
theorem SubE.tm_eq_of_sig {Δ : Ctx} {T : VarType} {a b : Ann T} {s : Term σ Δ T a}
    {t : Term σ Δ T b} (h : (⟨a, s⟩ : Σ c, Term σ Δ T c) = ⟨b, t⟩) :
    (SubE.tm s : SubE σ Δ) = SubE.tm t := by
  cases h
  rfl

omit [ModalSys.NoFour] in
/-- ⭐The index map of a substitution on a `□` view whose entries sit at its items: below an
    item, along its entry. -/
def itemIdx {Δ : Ctx} (θ : Subst σ Δ) (a : VarSymb) : VarSymb :=
  match cutBox a.path with
  | some (p, q) => (θ (.step ((VarSymb.root a.rt).ext p) .box)).idxAlong q
  | none => a

/-- A substitution on a `□` view whose items have projection paths is coherent with its item
    index map. -/
theorem coh_itemIdx {Γ Δ : Ctx} {θ : Subst σ Δ} (hθ : Subst.Ok Γ.boxIn θ)
    (hpp : ∀ (u : VarSymb) (T : VarType), Γ.ref u = some (.VTypeBox T) →
      ∀ s ∈ u.path, s.isProj = true) :
    Subst.Coh (itemIdx θ) Γ.boxIn θ := by
  refine Subst.coh_of hθ ?_
  intro v T _ hv q
  match v with
  | .step u .box =>
      obtain ⟨-, hu⟩ := Ctx.boxIn_box hv
      change _ = itemIdx θ ((VarSymb.step u .box).ext q)
      unfold itemIdx
      rw [VarSymb.ext_path, show (VarSymb.step u .box).path = u.path ++ [.box] from rfl,
        List.append_assoc, List.singleton_append, cutBox_proj u.path q (hpp u T hu)]
      dsimp only
      rw [VarSymb.ext_rt, show (VarSymb.step u .box).rt = u.rt from rfl, VarSymb.root_ext_path]
  | .step u .keep =>
      exact absurd ((Ctx.boxIn_keep hv).1.symm.trans ModalSys.NoFour.noFour) (by decide)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

omit [ModalSys.NoFour] in
/-- ⭐An item's reading under two substitutions is its entry composed. -/
theorem sim_tm_subst_eta_comp {ι₁ ι₂ : VarSymb → VarSymb} {Γ Δ₁ Δ₂ : Ctx} (θ₁ : Subst σ Δ₁)
    (hθ₁ : Subst.Ok Γ θ₁) (hc₁ : Subst.Coh ι₁ Γ θ₁) (θ₂ : Subst σ Δ₂) (hθ₂ : Subst.Ok Δ₁ θ₂)
    (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) {v : VarSymb} {T : VarType} (hv : Γ.ref v = some T) :
    SubE.Sim T (.tm (Term.subst ι₂ θ₂ hθ₂ hc₂ (Term.subst ι₁ θ₁ hθ₁ hc₁ (Term.eta v T hv))))
      ((θ₁.at v).comp θ₂ hθ₂ hc₂) := by
  have hok := Subst.okRef_at hθ₁ hv
  generalize he : θ₁.at v = E at hok ⊢
  cases E with
  | tm s =>
      cases hok
      rw [SubE.tm_eq_of_sig (sig_subst θ₂ hθ₂ hc₂ (Term.subst_eta_tm θ₁ hθ₁ hc₁ T v hv s he))]
      exact .refl _
  | ren w =>
      rw [SubE.tm_eq_of_sig (sig_subst θ₂ hθ₂ hc₂
        (Term.subst_eta_renAt θ₁ hθ₁ hc₁ T v w hv hok he))]
      change SubE.Sim T _ (θ₂.at w)
      have hok₂ := Subst.okRef_at hθ₂ hok
      generalize he₂ : θ₂.at w = E₂ at hok₂ ⊢
      cases E₂ with
      | tm s' =>
          cases hok₂
          rw [SubE.tm_eq_of_sig (Term.subst_eta_tm θ₂ hθ₂ hc₂ T w hok s' he₂)]
          exact .refl _
      | ren w' =>
          rw [SubE.tm_eq_of_sig (Term.subst_eta_renAt θ₂ hθ₂ hc₂ T w w' hok hok₂ he₂)]
          exact .eta_ren _ _
      | hide => exact hok₂.elim
  | hide => exact hok.elim

omit [ModalSys.NoFour] in
/-- The items of the view of `d : □A` have projection paths. -/
theorem ref_insert_box_ppath (A : VarType) (u : VarSymb) (T : VarType)
    (hu : (Ctx.empty.insert (.bnd 0) (.VTypeBox A)).ref u = some (.VTypeBox T)) :
    ∀ s ∈ u.path, s.isProj = true :=
  (Ctx.ref_insert_box hu).2.1

omit [ModalSys.NoFour] in
theorem sig_compVal {Γ : Ctx} {A : VarType} {a₀ a₁ : Ann A} {sb : Term σ Γ.boxIn A a₀}
    {sb' : Term σ Γ.boxIn A a₁} (e : (⟨_, sb⟩ : Σ c, Term σ Γ.boxIn A c) = ⟨_, sb'⟩)
    (p : List Step) {ps : List (List Step)} (h : A.CompOk (p :: ps)) :
    compVal sb p h = compVal sb' p h := by
  cases e
  rfl

/-- ⭐⭐**`holeC` at the tuple's value with companions**: the items sent home with their
    companions.  Both sides are substitutions of `compVal` over the bound object's view: the
    companion renaming then the tuple's value, and the tuple object then the arrow; they agree on
    every item (`at_compsFst_tupCompsImg`, `at_compsIdx_tupCompsImg`, `sim_tm_subst_eta_comp`). -/
theorem holeAt_tupCompsImg_holeCVal {cls : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk cls Δ img) (b : Bool) (hb : ModalSys.T = b) {A : VarType} {a : Ann A}
    (u : Term σ (ctxOf cls).boxIn A a) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs),
      (⟨_, Term.holeAt (tupCompsImg cls img himg ((bcT cls).compsAllB b)
          (VarType.compOk_compsAllB b hb (bcT cls))).2
          (holeCVal (packT cls u) b hb ModalSys.NoFour.noFour cs h).2⟩ :
        Σ c, Term σ Δ (A.compsFlat cs) c) =
        ⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
          (compsVal u cs h).2⟩
  | [], _ => by
      change (⟨_, Term.holeAt _ (Term.holeAt _ (packT cls u))⟩ : Σ c, Term σ Δ A c) = _
      refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
      have e₁ : (⟨_, Term.holeAt (tupCompsImg cls img himg ((bcT cls).compsAllB b)
          (VarType.compOk_compsAllB b hb (bcT cls))).2 (Term.eta ((VarSymb.root (.bnd 0)).ext
            (compsFst ((bcT cls).compsAllB b))) (bcT cls)
            (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _)))⟩ : Σ c, Term σ Δ (bcT cls) c) =
          tupImgT cls img himg := by
        unfold Term.holeAt
        refine Term.subst_eta_tm _ _ _ _ _ _ _ (at_compsFst_tupCompsImg cls img himg _
          ((bcT cls).compsAllB b) (VarType.compOk_compsAllB b hb (bcT cls)) _ ?_)
        rw [Subst.at_nonproj _ rfl]; exact Subst.single_root _ _
      refine (Term.holeAt_congr_sig e₁ _).trans ?_
      rw [← Term.holeRead_eq_holeAt]
      exact holeRead_tupImgT_packT himg u
  | p :: ps, h => by
      refine sig_pair (holeAt_tupCompsImg_holeCVal himg b hb u ps h.tail) ?_
      -- the companion `p`
      set W := (tupCompsImg cls img himg _ (VarType.compOk_compsAllB b hb (bcT cls))).2
      have hu := Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox (bcT cls))
      set sb : Term σ (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))).boxIn A _ :=
        Term.holeAt (Term.eta (VarSymb.root (.bnd 0)).inner (bcT cls) (Ctx.ref_inner hu))
          (packT cls u)
      have hp1 := h.single List.mem_cons_self
      set X := (compVal sb p hp1).2
      -- the tuple object, and its view
      set θ : Subst σ (ctxOf cls) := Subst.single (.bnd 0) (.tm (Term.boxtm (tupT cls).2))
      have hθ : Subst.Ok (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))) θ :=
        Subst.ok_single (Ctx.empty_le _) rfl
      have hcθ : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm (Term.boxtm (tupT cls).2)))
          (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))) θ :=
        Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le _) rfl
      have hpp := ref_insert_box_ppath (bcT cls)
      -- the left side: the renaming, then the tuple's value
      set θW : Subst σ Δ := Subst.single (.bnd 0) (.tm W)
      have hθW : Subst.Ok (Ctx.empty.insert (.bnd 0) ((bcT cls).compsFlat
          ((bcT cls).compsAllB b))) θW := Subst.ok_single (Ctx.empty_le _) rfl
      have hcθW : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm W)) (Ctx.empty.insert (.bnd 0)
          ((bcT cls).compsFlat ((bcT cls).compsAllB b))) θW :=
        Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le _) rfl
      have hR := ok_compsRen (σ := σ) ModalSys.NoFour.noFour (bcT cls) b hb
      have hcR := coh_compsRen (σ := σ) ModalSys.NoFour.noFour (bcT cls) b hb
      have hL₃ : Subst.Ok (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))).boxIn
          ((compsRen σ _ ((bcT cls).compsAllB b)).comp θW hθW hcθW) :=
        fun v T hl hv => SubE.okRef_comp θW hθW hcθW (hR v T hl hv)
      have eL : (⟨_, Term.holeAt W (Term.subst (compsRenIdx _) (compsRen σ _ _) hR hcR X)⟩ :
          Σ c, Term σ Δ _ c) = ⟨_, Term.subst _ _ hL₃ (coh_itemIdx hL₃ hpp) X⟩ :=
        Term.subst_comp_sig _ θW _ hR hcR hθW hcθW hL₃ (coh_itemIdx hL₃ hpp)
          (fun _ _ _ => .refl _) X
      -- the right side: the tuple object, then the arrow
      have hR₃ : Subst.Ok (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))).boxIn
          (θ.box.comp (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)) :=
        fun v T hl hv => SubE.okRef_comp _ _ _ (Subst.ok_box hθ v T hl hv)
      have hub : (⟨_, Term.subst _ θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hcθ) sb⟩ :
          Σ c, Term σ (ctxOf cls).boxIn A c) = ⟨_, u⟩ := by
        refine (Term.subst_holeAt_sig _ _ _ _ _).trans ?_
        refine (Term.holeAt_congr_sig (Term.subst_eta_tm _ _ _ _ _ _ _
          (Subst.box_at_inner_boxtm θ (by
            rw [Subst.at_nonproj _ rfl]; exact Subst.single_root _ _))) _).trans ?_
        rw [← Term.holeRead_eq_holeAt]
        exact holeRead_tupT_packT cls u
      have eR : (⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
          (compVal u p hp1).2⟩ : Σ c, Term σ Δ _ c) =
          ⟨_, Term.subst _ _ hR₃ (coh_itemIdx hR₃ hpp) X⟩ := by
        rw [← sig_compVal hub p hp1]
        refine (sig_subst _ _ _ (subst_compVal_sig θ hθ hcθ sb p hp1).symm).trans ?_
        exact Term.subst_comp_sig _ _ _ _ _ _ _ hR₃ (coh_itemIdx hR₃ hpp) (fun _ _ _ => .refl _) X
      refine eL.trans (Eq.trans ?_ eR.symm)
      -- the two agree on every item of the view
      refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) X
      match v with
      | .step w .box =>
          obtain ⟨-, hw⟩ := Ctx.boxIn_box hv
          obtain ⟨hrt, -, hc⟩ := Ctx.ref_insert_box hw
          have hθv : compsRen σ (Ctx.empty.insert (.bnd 0) ((bcT cls).compsFlat
              ((bcT cls).compsAllB b))) ((bcT cls).compsAllB b) (.step w .box) =
              .ren (compsItemAddr ((bcT cls).compsAllB b) w.path) := by
            dsimp only [compsRen]
            rw [if_pos hrt]
          change SubE.Sim T ((compsRen σ _ _ (.step w .box)).comp θW hθW hcθW)
            ((θ.box (.step w .box)).comp _ _ _)
          rw [hθv]
          change SubE.Sim T (θW.at _) _
          have hv' : (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))).boxIn.ref
              (.step w .box) = some T := hv
          have hS := sim_tm_subst_eta_comp θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hcθ)
            (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg) hv'
          rw [Subst.at_nonproj θ.box (v := .step w .box) rfl] at hS
          have hw₀ := VarSymb.root_ext_path w
          rcases hc with ⟨hpath, rfl⟩ | ⟨hT, q, hpath, hq⟩
          · rw [hrt, hpath] at hw₀
            obtain rfl : w = .root (.bnd 0) := hw₀.symm
            rw [show compsItemAddr ((bcT cls).compsAllB b) (VarSymb.root (Root.bnd 0)).path =
                (VarSymb.root (.bnd 0)).ext (compsFst ((bcT cls).compsAllB b)) from rfl,
              at_compsFst_tupCompsImg cls img himg θW _ _ _
                (by rw [Subst.at_nonproj _ rfl]; exact Subst.single_root _ _)]
            refine (congrArg (SubE.Sim _ · _) (SubE.tm_eq_of_sig ?_)).mp hS
            refine (sig_subst _ _ _ (Term.subst_eta_tm _ _ _ _ _ _ _ (by
              rw [← VarSymb.inner_box ModalSys.NoFour.keepOnly]
              exact Subst.box_at_inner_boxtm θ (by
                rw [Subst.at_nonproj _ rfl]; exact Subst.single_root _ _)))).trans ?_
            exact subst_arrow_tupT cls himg
          · rw [hrt, hpath] at hw₀
            subst hw₀
            have hm : q ∈ (bcT cls).compsAllB b := by
              rw [← hb, hT]
              exact VarType.mem_hereChains _ q hq
            obtain rfl : T = ((bcT cls).compAt q).getD .VTypeOne := by rw [hq]; rfl
            rw [show compsItemAddr ((bcT cls).compsAllB b)
                ((VarSymb.root (Root.bnd 0)).ext (.here :: q)).path =
                (VarSymb.root (.bnd 0)).ext (compsIdx ((bcT cls).compsAllB b) q) by
                  rw [VarSymb.ext_path]; rfl,
              at_compsIdx_tupCompsImg cls img himg θW _ _ _
                (by rw [Subst.at_nonproj _ rfl]; exact Subst.single_root _ _) q hm]
            refine (congrArg (SubE.Sim _ · _) (SubE.tm_eq_of_sig ?_)).mp hS
            refine sig_subst _ _ _ (sig_subst _ _ _ (eta_addr_congr ?_ _
              (Ctx.ref_inner (Ctx.ref_compMem hT (VarType.mem_hereChains _ q hq) hu))))
            rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
            rfl
      | .step _ .keep =>
          exact absurd ((Ctx.boxIn_keep hv).1.symm.trans ModalSys.NoFour.noFour) (by decide)
      | .root _ => cases hv
      | .step _ .fst => cases hv
      | .step _ .snd => cases hv
      | .step _ .dia => cases hv
      | .step _ .here => cases hv

/-- ⭐The **packing map with companions** of items over the committed roots: from the one
    necessary object holding all the roots' items, with all its companions, to the object the
    items make — `holeC` of `packT` at each `□`. -/
def packMapC (b : Bool) (hb : ModalSys.T = b) (cls : List VarType) : {N : NShape} →
    NItems σ (ctxOf cls).boxIn N → ShapeMap σ (tupShape b hb cls) N
  | .boxC _ cs h, ⟨_, u⟩ => .holeC (packT cls u) b hb ModalSys.NoFour.noFour cs h
  | .prod _ _, (n₁, n₂) => .pair (packMapC b hb cls n₁) (packMapC b hb cls n₂)

/-- ⭐The packing map's object, read where the bound object is the roots' items: the object the
    items make. -/
theorem subst_packMapC_obj {b : Bool} {hb : ModalSys.T = b} {cls : List VarType}
    {ι : VarSymb → VarSymb} {Δ : Ctx}
    (θ : Subst σ Δ) (hθ : Subst.Ok (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))) θ)
    (hc : Subst.Coh ι (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))) θ)
    (hle : (ctxOf cls).Le Δ)
    (h0 : θ.at (.root (.bnd 0)) = .tm (Term.boxtm (Term.mono hle.boxIn (tupT cls).2))) :
    {N : NShape} → (n : NItems σ (ctxOf cls).boxIn N) →
    (⟨_, Term.subst ι θ hθ hc (packMapC b hb cls n).obj.2⟩ : Σ c, Term σ Δ N.ty c) =
      (n.mono hle).obj
  | .boxC _ _ _, ⟨_, u⟩ => by
      change (⟨_, Term.boxtm (Term.subst _ _ _ _ (Term.holeAt _ (packT cls u)))⟩ :
        Σ c, Term σ Δ (.VTypeBox _) c) = _
      refine sig_boxtm ?_
      refine (Term.subst_holeAt_sig _ _ _ _ _).trans ?_
      refine (sig_holeAt (Term.subst_eta_tm _ _ _ _ _ _ _
        (Subst.box_at_inner_boxtm _ h0)) _).trans ?_
      exact holeAt_tupT_packT_mono _ u
  | .prod _ _, (n₁, n₂) =>
      sig_pair (subst_packMapC_obj θ hθ hc hle h0 n₁) (subst_packMapC_obj θ hθ hc hle h0 n₂)

/-- ⭐**The packing map's value at the tuple of the roots' images with companions**: the items
    sent along the arrow with their companions (`holeAt_tupCompsImg_holeCVal` at each `□`). -/
theorem holeRead_tupCompsImg_packMapC {cls : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk cls Δ img) (b : Bool) (hb : ModalSys.T = b) : {N : NShape} →
    (n : NItems σ (ctxOf cls).boxIn N) →
    (⟨_, Term.holeRead (tupCompsImg cls img himg ((bcT cls).compsAllB b)
        (VarType.compOk_compsAllB b hb (bcT cls))).2 (packMapC b hb cls n).val.2⟩ :
      Σ c, Term σ Δ N.flat c) =
      n.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
  | .boxC _ cs h, ⟨_, u⟩ => by
      rw [Term.holeRead_eq_holeAt]
      exact holeAt_tupCompsImg_holeCVal himg b hb u cs h
  | .prod _ _, (n₁, n₂) =>
      sig_pair (holeRead_tupCompsImg_packMapC himg b hb n₁)
        (holeRead_tupCompsImg_packMapC himg b hb n₂)

/-! ## The returning possibility as a slot formula -/

section RetSlot

variable {Γ : Ctx} [Γ.NoSlots]

omit [ModalSys.NoFour] in
theorem slots_insert_boxIn : ((Γ.insert (.bnd 0) T).boxIn).SlotsFrom 1 :=
  ((Ctx.NoSlots.slots (Γ := Γ)).insert T).boxIn

/-- The body of a returning possibility, its slot moved one binder out (`bnd 0 ↦ bnd 1`), in the
    context with the value's slot. -/
def bodyUp {T : VarType} (S : RShape) (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1) :
    WFF σ ((Γ.insert (.bnd 0) T).boxIn.insert (.bnd 1) S.ty) 2 :=
  WFF.subst (VarSymb.shiftSlot id 0 1)
    ((Subst.idS σ (Γ.insert (.bnd 0) T).boxIn).under 0 1 S.ty (slots_insert_boxIn.root))
    (Subst.ok_under (Subst.ok_idS_le (Ctx.le_insert
      (Ctx.NoSlots.slots (Γ := Γ)).root T).boxIn) _ _)
    (Subst.coh_under (Subst.ok_idS_le (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root T).boxIn)
      (Subst.coh_idS_le (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root T).boxIn)
      (Ctx.NoSlots.slots (Γ := Γ)).boxIn _ _)
    ((Ctx.NoSlots.slots (Γ := Γ)).boxIn.insert _) (slots_insert_boxIn.insert _) Φ

/-- ⭐`◇[d ↦ z] Φ(d)` with the value `z` a slot: the slot formula of a returning possibility. -/
def WFF.retSlot (hS : ModalSys.BStrong = true) (S : RShape)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1) : WFF σ (Γ.insert (.bnd 0) S.flat) 1 :=
  WFF.retS hS S (Term.eta (.root (.bnd 0)) S.flat (Ctx.ref_insert_root Γ (.bnd 0) S.flat))
    (bodyUp S Φ)

/-- ⭐Instantiating the slot formula of a returning possibility gives it, valued at the term. -/
theorem WFF.instantiate_retSlot (hS : ModalSys.BStrong = true) (S : RShape)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1) {a : Ann S.flat} (z : Term σ Γ S.flat a) :
    WFF.instantiate Ctx.NoSlots.slots z (WFF.retSlot hS S Φ) = WFF.retS hS S z Φ := by
  unfold WFF.instantiate WFF.substRoot WFF.retSlot bodyUp
  simp only [WFF.subst]
  refine OutLeg.retS_congr (O := .nec) hS S
    (Term.subst_eta_tm _ _ _ _ _ _ z (Subst.at_single_root _ _)) ?_
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ Φ).trans
    (WFF.subst_id _ _ _ Φ)
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim U (Subst.idS σ _ (.root (.bnd 0)))
      ((Subst.under _ 0 1 _ _ (.root (.bnd 0))).comp _ _ _)
    rw [show Subst.under (Subst.idS σ (Γ.insert (.bnd 0) S.flat).boxIn) 0 1 S.ty
      slots_insert_boxIn.root (.root (.bnd 0)) = .ren (.root (.bnd 1)) from if_pos rfl]
    dsimp only [SubE.comp]
    change SubE.Sim U _ (Subst.under _ 1 0 _ _ (.root (.bnd 1)))
    rw [show ∀ θ h, Subst.under (σ := σ) (Δ := Γ.boxIn) θ 1 0 S.ty h (.root (.bnd 1)) =
      .ren (.root (.bnd 0)) from fun _ _ => if_pos rfl]
    exact .refl _
  · have hv' : Γ.boxIn v = some U := by simpa [Ctx.insert, hvr] using hv
    obtain ⟨w, rfl, hw⟩ := boxIn_item' hv'
    have hw0 : w.rt ≠ .bnd 0 :=
      Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hw
    change SubE.Sim U (Subst.idS σ _ (.step w .box))
      ((Subst.under _ 0 1 _ _ (.step w .box)).comp _ _ _)
    rw [show Subst.under (Subst.idS σ (Γ.insert (.bnd 0) S.flat).boxIn) 0 1 S.ty
      slots_insert_boxIn.root (.step w .box) = .ren (.step w .box) from if_neg hvr]
    dsimp only [SubE.comp]
    rw [Subst.at_nonproj _ rfl]
    rw [show ∀ θ h, Subst.under (σ := σ) (Δ := Γ.boxIn) θ 1 0 S.ty h (.step w .box) =
      (θ (.step w .box)).mono (Ctx.le_insert h S.ty) from fun _ _ => if_neg (by
        intro e; cases e)]
    change SubE.Sim U _ (SubE.mono _ ((Subst.at _ w).unbox))
    rw [Subst.single_at_ne hw0]
    change SubE.Sim U (.ren (.step w .box)) (.ren w.inner)
    rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
    exact .refl _

end RetSlot

/-! ## Along a witness: the slot formula -/

section RetxSlot

omit [ModalSys.NoFour] in
/-- ⭐**Substituting through a returning possibility along a witness the substitution fixes**: the
    witness stays, and the body goes under the witness's view. -/
theorem WFF.subst_retxS_fix {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hS : ModalSys.BStrong = true) {y : VarSymb} (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y))
    {S : RShape} {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Φ : WFF σ ((Γ.diaIn y).insert (.bnd d) S.ty) (d + 1)) (hιy : ι y = y)
    (hy' : ∃ Y, Δ.ref y = some (.VTypeDia Y))
    (hok : Subst.Ok ((Γ.diaIn y).insert (.bnd d) S.ty)
      ((θ.dia y y).under d d' S.ty (hΔ.diaIn y).root))
    (hcoh : Subst.Coh (VarSymb.shiftSlot ι d d') ((Γ.diaIn y).insert (.bnd d) S.ty)
      ((θ.dia y y).under d d' S.ty (hΔ.diaIn y).root)) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.retxS hS y hy S t Φ) =
      WFF.retxS hS y hy' S (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d') ((θ.dia y y).under d d' S.ty (hΔ.diaIn y).root)
          hok hcoh ((hΓ.diaIn y).insert _) ((hΔ.diaIn y).insert _) Φ) := by
  have aux : ∀ (y₁ : VarSymb) (_e : y₁ = y) (P₁ : ∃ Y, Δ.ref y₁ = some (.VTypeDia Y))
      (OK₁ : Subst.Ok ((Γ.diaIn y).insert (.bnd d) S.ty)
        ((θ.dia y y₁).under d d' S.ty (hΔ.diaIn y₁).root))
      (COH₁ : Subst.Coh (VarSymb.shiftSlot ι d d') ((Γ.diaIn y).insert (.bnd d) S.ty)
        ((θ.dia y y₁).under d d' S.ty (hΔ.diaIn y₁).root)),
      WFF.retxS hS y₁ P₁ S (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d') ((θ.dia y y₁).under d d' S.ty (hΔ.diaIn y₁).root)
          OK₁ COH₁ ((hΓ.diaIn y).insert _) ((hΔ.diaIn y₁).insert _) Φ) =
      WFF.retxS hS y hy' S (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d') ((θ.dia y y).under d d' S.ty (hΔ.diaIn y).root)
          hok hcoh ((hΓ.diaIn y).insert _) ((hΔ.diaIn y).insert _) Φ) := by
    intro y₁ e _ _ _
    subst e
    rfl
  exact aux (ι y) hιy _ _ _

variable {Γ : Ctx} [Γ.NoSlots]

/-- The body of a returning possibility along `y`, its slot moved one binder out. -/
def bodyUpX {T : VarType} (y : VarSymb) (S : RShape)
    (Φ : WFF σ ((Γ.diaIn y).insert (.bnd 0) S.ty) 1) :
    WFF σ (((Γ.insert (.bnd 0) T).diaIn y).insert (.bnd 1) S.ty) 2 :=
  WFF.subst (VarSymb.shiftSlot id 0 1)
    ((Subst.idS σ ((Γ.insert (.bnd 0) T).diaIn y)).under 0 1 S.ty
      (((Ctx.NoSlots.slots (Γ := Γ)).insert T).diaIn y).root)
    (Subst.ok_under (Subst.ok_idS_le ((Ctx.le_insert
      (Ctx.NoSlots.slots (Γ := Γ)).root T).diaIn y)) _ _)
    (Subst.coh_under (Subst.ok_idS_le ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root T).diaIn y))
      (Subst.coh_idS_le ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root T).diaIn y))
      ((Ctx.NoSlots.slots (Γ := Γ)).diaIn y) _ _)
    (((Ctx.NoSlots.slots (Γ := Γ)).diaIn y).insert _)
    ((((Ctx.NoSlots.slots (Γ := Γ)).insert T).diaIn y).insert _) Φ

/-- ⭐`◇_y[d ↦ z] Φ(d)` with the value `z` a slot. -/
def WFF.retxSlot (hS : ModalSys.BStrong = true) (y : VarSymb)
    (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) (S : RShape)
    (Φ : WFF σ ((Γ.diaIn y).insert (.bnd 0) S.ty) 1) : WFF σ (Γ.insert (.bnd 0) S.flat) 1 :=
  WFF.retxS hS y (hy.imp fun _ h => (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _).ref h) S
    (Term.eta (.root (.bnd 0)) S.flat (Ctx.ref_insert_root Γ (.bnd 0) S.flat)) (bodyUpX y S Φ)

/-- ⭐Instantiating the slot formula of a returning possibility along `y` gives it. -/
theorem WFF.instantiate_retxSlot (hS : ModalSys.BStrong = true) (y : VarSymb)
    (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) (S : RShape)
    (Φ : WFF σ ((Γ.diaIn y).insert (.bnd 0) S.ty) 1) {a : Ann S.flat} (z : Term σ Γ S.flat a) :
    WFF.instantiate Ctx.NoSlots.slots z (WFF.retxSlot hS y hy S Φ) = WFF.retxS hS y hy S z Φ := by
  have hy0 : y.rt ≠ .bnd 0 := hy.elim fun _ h =>
    Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) h
  have hιy : Subst.singleIdx (σ := σ) (Δ := Γ) (.bnd 0) (.tm z) y = y := if_neg hy0
  have hw : ((Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm z)).at y).idxAlong [] = y := by
    rw [Subst.single_at_ne hy0]
    rfl
  have hyS : ∃ Y, (Γ.insert (.bnd 0) S.flat).ref y = some (.VTypeDia Y) :=
    hy.imp fun _ h => (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root _).ref h
  have hθ := Subst.ok_single (σ := σ) (r := .bnd 0) (Ctx.Le.refl Γ) (e := .tm z) (T := S.flat) rfl
  have hc := Subst.coh_single (σ := σ) ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0))
    (Ctx.Le.refl Γ) (e := .tm z) (T := S.flat) rfl
  have hcoh := Subst.coh_under (Subst.ok_dia hθ hyS (hc y _ hyS.choose_spec []))
    (Subst.coh_dia hθ hc hyS)
    (((Ctx.NoSlots.slots (Γ := Γ)).insert S.flat).diaIn y) S.ty
    ((Ctx.NoSlots.slots (Γ := Γ)).diaIn (Subst.singleIdx (.bnd 0) (.tm z) y)).root
  simp only [VarSymb.ext_nil] at hcoh
  rw [hιy] at hcoh
  unfold WFF.instantiate WFF.substRoot WFF.retxSlot
  rw [WFF.subst_retxS_fix _ _ _ _ _ hS hyS _ _ hιy hy (Subst.ok_under (Subst.ok_dia hθ hyS hw) _ _)
    hcoh]
  refine OutLeg.retS_congr (O := .pos y hy) hS S
    (Term.subst_eta_tm _ _ _ _ _ _ z (Subst.at_single_root _ _)) ?_
  unfold bodyUpX
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ Φ).trans
    (WFF.subst_id _ _ _ Φ)
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim U (Subst.idS σ _ (.root (.bnd 0)))
      ((Subst.under _ 0 1 _ _ (.root (.bnd 0))).comp _ _ _)
    rw [show ∀ θ h, Subst.under (σ := σ) (Δ := (Γ.insert (.bnd 0) S.flat).diaIn y) θ 0 1 S.ty h
      (.root (.bnd 0)) = .ren (.root (.bnd 1)) from fun _ _ => if_pos rfl]
    dsimp only [SubE.comp]
    change SubE.Sim U _ (Subst.under _ 1 0 _ _ (.root (.bnd 1)))
    rw [show ∀ θ h, Subst.under (σ := σ) (Δ := Γ.diaIn y) θ 1 0 S.ty h (.root (.bnd 1)) =
      .ren (.root (.bnd 0)) from fun _ _ => if_pos rfl]
    exact .refl _
  · have hv' : (Γ.diaIn y) v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ .bnd 0 := Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := Γ)).diaIn y |>.rootFresh (le_refl 0))
      ((Ctx.ref_nonproj _ hlp).trans hv')
    change SubE.Sim U (Subst.idS σ _ v) ((Subst.under _ 0 1 _ _ v).comp _ _ _)
    rw [show ∀ θ h, Subst.under (σ := σ) (Δ := (Γ.insert (.bnd 0) S.flat).diaIn y) θ 0 1 S.ty h
      v = (θ v).mono (Ctx.le_insert h S.ty) from fun _ _ => if_neg hvr]
    dsimp only [Subst.idS, SubE.mono, SubE.comp]
    rw [Subst.at_nonproj _ hlp]
    rw [show ∀ θ h, Subst.under (σ := σ) (Δ := Γ.diaIn y) θ 1 0 S.ty h v =
      (θ v).mono (Ctx.le_insert h S.ty) from fun _ _ => if_neg (fun e => by
        rw [e, (((Ctx.NoSlots.slots (Γ := Γ)).diaIn y).rootFresh (Nat.zero_le 1)).root] at hv'
        cases hv')]
    match v, hv' with
    | .step u .dia, hv' =>
        change (if u = y then _ else none) = _ at hv'
        split_ifs at hv' with huy
        subst huy
        change SubE.Sim U _ (SubE.mono _ (if u = u then _ else _))
        rw [if_pos rfl, Subst.single_at_ne hy0]
        exact .refl _
    | .step u .box, hv' =>
        have hu0 : u.rt ≠ .bnd 0 := hrt
        change SubE.Sim U _ (SubE.mono _ (SubE.mono _ (Subst.at _ u).unbox))
        rw [Subst.single_at_ne hu0]
        change SubE.Sim U (.ren (.step u .box)) (.ren u.inner)
        rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
        exact .refl _
    | .step u .keep, hv' =>
        exact absurd (Ctx.boxIn_keep ((Ctx.ref_nonproj _ rfl).trans hv')).1
          (by simp [ModalSys.NoFour.noFour])

end RetxSlot

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

/-- A body read along an arrow depends on the slot term only as a dependent pair. -/
theorem readArrow_sig {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {B : VarType} {c c' : Ann B} {g : Term σ Δ B c} {g' : Term σ Δ B c'}
    (h : (⟨c, g⟩ : Σ c, Term σ Δ B c) = ⟨c', g'⟩)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) B) 1) :
    readArrow himg g Φ = readArrow himg g' Φ := by
  cases h
  rfl

/-- ⭐**The body `Φ(N[D])` read at the far end** is `Φ` read along the reverse arrow, its slot
    filled by the object the items make: packing the items over the committed roots' tuple and
    reading them at the tuple's items gives them back (`subst_packMapC_obj`). -/
theorem liftBody_bodyRepl_packMapC {bb : Bool} {hbb : ModalSys.T = bb}
    {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {N : NShape} (n : NItems σ (ctxOf cls).boxIn N)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) N.ty) 1) :
    liftBody hs himgt (WFF.bodyRepl
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (packMapC bb hbb cls n).obj.2) Φ) =
      readArrow himgt (n.mono (ctxOf_le_of_suffix hs)).obj.2 Φ := by
  unfold liftBody WFF.bodyRepl readArrow
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T _ hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = N.ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) _ (.root (.bnd 0)))
      ((((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))).comp _ _ _)
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (Eq.symm ?_)
    rw [Term.subst_mono]
    exact subst_packMapC_obj _ _ _ _ (by
      change Subst.set _ _ _ (.root (.bnd 0)) = _
      exact Subst.set_root _ _ _) n
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
    invariant, `Φ(N)` at `k` (read along the reverse arrow), for the object `N` some items make, is
    `◇[d ↦ the items sent home] Φ(d)` at `s` — the invariant at the body `Φ(N[D])`
    (`liftBody_bodyRepl_packMapC`), then `ret_map` along the packing map
    (`holeRead_tupCompsImg_packMapC`). -/
theorem ret_of_invB {bb : Bool} {hbb : ModalSys.T = bb}
    {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hsM : Theory.IsMCS ts.M)
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} (h : RetInvB hS bb hbb tk ts cls imgs clt imgt)
    {N : NShape} (n : NItems σ (ctxOf cls).boxIn N)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) N.ty) 1)
    (hmem : ∃ (hs : cls <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt),
      readArrow himgt (n.mono (ctxOf_le_of_suffix hs)).obj.2 Φ ∈ tk.M) :
    ∃ (himgs : ImgOk cls (ctxOf ts.l) imgs) (ht : clt <:+ ts.l),
      WFF.retS hS (.nec N)
        (n.subst (arrowIdx imgs) (arrowS σ (ctxOf ts.l) imgs) (ok_arrowS himgs)
          (coh_arrowS himgs)).2
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ ts.M := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  obtain ⟨hs', himgt', hm⟩ := hmem
  refine ⟨himgs, ht, ?_⟩
  have hr := hinv (WFF.bodyRepl
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (packMapC bb hbb cls n).obj.2) Φ)
    (by rw [liftBody_bodyRepl_packMapC]; exact hm)
  rw [WFF.mono_bodyRepl (ctxOf_le_of_suffix ht).boxIn, Term.mono_mono] at hr
  have hc := hsM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
    ⟨Proof.ret_map hS .nec (S := .nec (tupShape bb hbb cls)) (packMapC bb hbb cls n)
      (tupCompsImg cls imgs himgs ((bcT cls).compsAllB bb)
        (VarType.compOk_compsAllB bb hbb (bcT cls))).2
      (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ)
      (Proof.lookup List.mem_cons_self)⟩⟩
  exact (congrArg (· ∈ ts.M) (OutLeg.retS_congr hS .nec (.nec N)
    (holeRead_tupCompsImg_packMapC himgs bb hbb n) rfl)).mp hc


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

/-- ⭐A body read along an arrow, its slot filled, is true where the body is true in the
    environment the arrow induces, extended by the slot term's value. -/
theorem sat_readArrow {M : Model σ} {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {w : M.frame.W} (env : M.Env Δ w) {B : VarType} {c : Ann B}
    (g : Term σ Δ B c) (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) B) 1) :
    M.sat env (readArrow himg g Φ) ↔
      M.sat ((Model.substEnv (arrowS σ Δ img) (ok_arrowS himg) (Ctx.noProjLast_boxIn _) env).extend
        (.bnd 0) (Model.interp env g)) Φ := by
  unfold readArrow
  rw [Model.sat_subst _ _ _ _ _ ((Ctx.noProjLast_boxIn _).insert (.bnd 0) B),
    Model.substEnv_set_tm]

namespace BData

variable {B : BData σ}

/-- Pushing the canonical environment along an arrow is the arrow's substituted environment of
    the target's canonical environment at any later stage. -/
theorem boxPush_canon_at (s : B.W) (i : ℕ) (a : B.Acc s) (hR : B.R s a.1) {j : ℕ}
    (hj : B.stg s a.1 i ≤ j) :
    (B.canonEnv s i).boxPush a = Model.substEnv (arrowS σ ((B.w a.1).ctx j) (B.img s a.1))
      (ok_arrowS ((B.imgOk hR i).mono ((B.w a.1).le hj))) (Ctx.noProjLast_boxIn _)
      (B.canonEnv a.1 j) := by
  rw [boxPush_canon s i a hR]
  funext v T hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  exact Model.Env.ref_agree (canonEnv_le a.1 hj) _ _

/-- ⭐**Moving a returning possibility's value along canonical `Ind`**: the decoder and the
    induction hypothesis at `eqRec` (`ret_eq`) to and from the representatives, and the
    representatives' interchangeability at the slot formula `◇[d ↦ z] Φ(d)`
    (`WFF.instantiate_retSlot`). -/
theorem mem_ret_of_ind (hS : ModalSys.BStrong = true) (hInj : B.ImgInj) {s : B.W}
    (harr : ∃ k, B.R s k) {S : RShape} {i K : ℕ} (hiK : i ≤ K) {bv : Ann S.flat}
    (v : Term σ ((B.w s).ctx K) S.flat bv) {a : Ann S.flat} (t : Term σ ((B.w s).ctx i) S.flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) S.ty) 1)
    (IH : ∀ (L : ℕ) {c : Ann S.flat} (u u' : Term σ ((B.w s).ctx L) S.flat c),
      B.model.sat (B.canonEnv s L) (eqRec S.flat u u' : WFF σ _ 0) →
        (eqRec S.flat u u' : WFF σ _ 0) ∈ (B.w s).M L)
    (hmem : WFF.retS hS S v (WFF.mono (((B.w s).le hiK).boxIn.insert (.bnd 0) _) Φ) ∈ (B.w s).M K)
    (hind : B.Ind (B.toDom S.flat s (B.rden s K (Ctx.Le.refl _) v) (definable_rden _ _))
      (B.toDom S.flat s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _))) :
    WFF.retS hS S t Φ ∈ (B.w s).M i := by
  obtain ⟨⟨i₁, a₁, u₁⟩, ⟨i₂, a₂, u₂⟩, h₁, h₂, hrel⟩ := hind
  rw [fromDom_toDom] at h₁ h₂
  have e₁ : B.toDom S.flat s (B.rden s K (Ctx.Le.refl _) v) (definable_rden _ _) =
      B.toDom S.flat s (B.rden s i₁ (Ctx.Le.refl _) u₁) (definable_rden _ _) :=
    toDom_congr h₁.symm _ _
  have e₂ : B.toDom S.flat s (B.rden s i₂ (Ctx.Le.refl _) u₂) (definable_rden _ _) =
      B.toDom S.flat s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) :=
    toDom_congr h₂ _ _
  obtain rfl := ann_eq_of_toDom hS hInj harr _ _ e₁
  obtain rfl := ann_eq_of_toDom hS hInj harr _ _ e₂
  set L := max (max K i₁) i₂
  have hKL : K ≤ L := le_max_of_le_left (le_max_left _ _)
  have h₁L : i₁ ≤ L := le_max_of_le_left (le_max_right _ _)
  have h₂L : i₂ ≤ L := le_max_right _ _
  have hiL : i ≤ L := hiK.trans hKL
  have hm₁ := (BWorld.mem_lift hKL).mp hmem
  have hq₁ := IH L _ _ (sat_eqRec_lift hKL h₁L _ _ e₁)
  have hr₁ : WFF.retS hS S (Term.mono ((B.w s).le h₁L) u₁)
      (WFF.mono (((B.w s).le hiL).boxIn.insert (.bnd 0) _) Φ) ∈ (B.w s).M L := by
    refine BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hm₁
      · rw [List.mem_singleton.mp hψ]; exact hq₁)
      ⟨Proof.conv ?_ (Proof.ret_eqS hS .nec (S := S) _ _ _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
    change WFF.retS hS _ _ (WFF.mono _ (WFF.mono _ Φ)) = _
    rw [WFF.mono_mono]
  have hI₁ := WFF.instantiate_retSlot (Γ := (B.w s).ctx L) hS S
    (WFF.mono (((B.w s).le hiL).boxIn.insert (.bnd 0) _) Φ) (Term.mono ((B.w s).le h₁L) u₁)
  have hI₂ := WFF.instantiate_retSlot (Γ := (B.w s).ctx L) hS S
    (WFF.mono (((B.w s).le hiL).boxIn.insert (.bnd 0) _) Φ) (Term.mono ((B.w s).le h₂L) u₂)
  have hr₂ : WFF.retS hS S (Term.mono ((B.w s).le h₂L) u₂)
      (WFF.mono (((B.w s).le hiL).boxIn.insert (.bnd 0) _) Φ) ∈ (B.w s).M L :=
    (congrArg (· ∈ (B.w s).M L) hI₂).mp ((hrel L h₁L h₂L (WFF.retSlot hS S
      (WFF.mono (((B.w s).le hiL).boxIn.insert (.bnd 0) _) Φ))).mp
      ((congrArg (· ∈ (B.w s).M L) hI₁).mpr hr₁))
  have hq₂ := IH L _ _ (sat_eqRec_lift h₂L hiL _ _ e₂)
  refine (BWorld.mem_lift hiL).mpr (BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hr₂
      · rw [List.mem_singleton.mp hψ]; exact hq₂)
    ⟨Proof.ret_eqS hS .nec (S := S) _ _ _ (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩)


/-- Pushing the canonical environment along a witness arrow is the arrow's substituted
    environment of the target's canonical environment at any later stage. -/
theorem diaPush_canon_at (s : B.W) (i : ℕ) {y : VarSymb} {Y : VarType}
    (hr : ((B.w s).ctx i).ref y = some (.VTypeDia Y))
    (a : (B.model.posEval ((B.canonEnv s i).ref y hr)).1) (hk : B.kd s a.1.1 = some (y, Y))
    {j : ℕ} (hj : B.stg s a.1.1 i ≤ j) :
    (B.canonEnv s i).diaPush y hr a = Model.substEnv (arrowXS σ ((B.w a.1.1).ctx j)
      (B.img s a.1.1) y (B.cx s a.1.1 y))
      (ok_arrowXS ((B.imgOk (B.kdR hk) i).mono ((B.w a.1.1).le hj)) hr
        (((B.w a.1.1).le hj).ref (B.hcx hk i)))
      (Ctx.noProjLast_diaIn _ y) (B.canonEnv a.1.1 j) := by
  rw [diaPush_canon s i hr a ⟨Y, B.kd_lb hk⟩]
  funext v T hv
  rcases diaIn_item hv with ⟨w, rfl, hw⟩ | ⟨rfl, _⟩
  · exact Model.Env.ref_agree (canonEnv_le a.1.1 hj) _ _
  · simp only [Model.substEnv, arrowXS]
    exact Model.Env.ref_agree (canonEnv_le a.1.1 hj) _ _

/-- ⭐**Moving a returning possibility's value along canonical `Ind`, along a witness**: as
    `mem_ret_of_ind`, at the slot formula `◇_y[d ↦ z] Φ(d)` (`WFF.instantiate_retxSlot`). -/
theorem mem_retx_of_ind (hS : ModalSys.BStrong = true) (hInj : B.ImgInj) {s : B.W}
    (harr : ∃ k, B.R s k) {S : RShape} {i K : ℕ} (hiK : i ≤ K) {y : VarSymb}
    (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {bv : Ann S.flat}
    (v : Term σ ((B.w s).ctx K) S.flat bv) {a : Ann S.flat} (t : Term σ ((B.w s).ctx i) S.flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) S.ty) 1)
    (IH : ∀ (L : ℕ) {c : Ann S.flat} (u u' : Term σ ((B.w s).ctx L) S.flat c),
      B.model.sat (B.canonEnv s L) (eqRec S.flat u u' : WFF σ _ 0) →
        (eqRec S.flat u u' : WFF σ _ 0) ∈ (B.w s).M L)
    (hmem : (OutLeg.pos y (hy.imp fun _ h => ((B.w s).le hiK).ref h) :
      OutLeg ((B.w s).ctx K)).retS hS S v
        (WFF.mono ((((B.w s).le hiK).diaIn y).insert (.bnd 0) _) Φ) ∈ (B.w s).M K)
    (hind : B.Ind (B.toDom S.flat s (B.rden s K (Ctx.Le.refl _) v) (definable_rden _ _))
      (B.toDom S.flat s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _))) :
    (OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS S t Φ ∈ (B.w s).M i := by
  obtain ⟨⟨i₁, a₁, u₁⟩, ⟨i₂, a₂, u₂⟩, h₁, h₂, hrel⟩ := hind
  rw [fromDom_toDom] at h₁ h₂
  have e₁ : B.toDom S.flat s (B.rden s K (Ctx.Le.refl _) v) (definable_rden _ _) =
      B.toDom S.flat s (B.rden s i₁ (Ctx.Le.refl _) u₁) (definable_rden _ _) :=
    toDom_congr h₁.symm _ _
  have e₂ : B.toDom S.flat s (B.rden s i₂ (Ctx.Le.refl _) u₂) (definable_rden _ _) =
      B.toDom S.flat s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) :=
    toDom_congr h₂ _ _
  obtain rfl := ann_eq_of_toDom hS hInj harr _ _ e₁
  obtain rfl := ann_eq_of_toDom hS hInj harr _ _ e₂
  set L := max (max K i₁) i₂
  have hKL : K ≤ L := le_max_of_le_left (le_max_left _ _)
  have h₁L : i₁ ≤ L := le_max_of_le_left (le_max_right _ _)
  have h₂L : i₂ ≤ L := le_max_right _ _
  have hiL : i ≤ L := hiK.trans hKL
  have hyL : ∃ Y, ((B.w s).ctx L).ref y = some (.VTypeDia Y) :=
    hy.imp fun _ h => ((B.w s).le hiL).ref h
  have hm₁ := (BWorld.mem_lift hKL).mp hmem
  have hq₁ := IH L _ _ (sat_eqRec_lift hKL h₁L _ _ e₁)
  have hr₁ : (OutLeg.pos y hyL : OutLeg ((B.w s).ctx L)).retS hS S (Term.mono ((B.w s).le h₁L) u₁)
      (WFF.mono ((((B.w s).le hiL).diaIn y).insert (.bnd 0) _) Φ) ∈ (B.w s).M L := by
    refine BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hm₁
      · rw [List.mem_singleton.mp hψ]; exact hq₁)
      ⟨Proof.ret_eqS hS (.pos y hyL) (S := S) _ _
        (WFF.mono ((((B.w s).le hiL).diaIn y).insert (.bnd 0) _) Φ) (Proof.conv ?_
        (Proof.lookup List.mem_cons_self))
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    change WFF.retxS hS _ _ _ _ (WFF.mono _ (WFF.mono _ Φ)) = _
    rw [WFF.mono_mono]
    rfl
  have hI₁ := WFF.instantiate_retxSlot (Γ := (B.w s).ctx L) hS y hyL S
    (WFF.mono ((((B.w s).le hiL).diaIn y).insert (.bnd 0) _) Φ) (Term.mono ((B.w s).le h₁L) u₁)
  have hI₂ := WFF.instantiate_retxSlot (Γ := (B.w s).ctx L) hS y hyL S
    (WFF.mono ((((B.w s).le hiL).diaIn y).insert (.bnd 0) _) Φ) (Term.mono ((B.w s).le h₂L) u₂)
  have hr₂ : (OutLeg.pos y hyL : OutLeg ((B.w s).ctx L)).retS hS S (Term.mono ((B.w s).le h₂L) u₂)
      (WFF.mono ((((B.w s).le hiL).diaIn y).insert (.bnd 0) _) Φ) ∈ (B.w s).M L :=
    (congrArg (· ∈ (B.w s).M L) hI₂).mp ((hrel L h₁L h₂L (WFF.retxSlot hS y hyL S
      (WFF.mono ((((B.w s).le hiL).diaIn y).insert (.bnd 0) _) Φ))).mp
      ((congrArg (· ∈ (B.w s).M L) hI₁).mpr hr₁))
  have hq₂ := IH L _ _ (sat_eqRec_lift h₂L hiL _ _ e₂)
  refine (BWorld.mem_lift hiL).mpr (BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hr₂
      · rw [List.mem_singleton.mp hψ]; exact hq₂)
    ⟨Proof.ret_eqS hS (.pos y hyL) (S := S) _ _ _ (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩)
end BData

/-! ## Along a witness: reading, the invariant, the limit -/

/-- ⭐A body over a witness's view with a slot, read along a witness arrow into `Δ` (`x`'s content
    to `cx`), its slot filled by `g`. -/
noncomputable def readArrowX {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) {B : VarType} {c : Ann B}
    (g : Term σ Δ B c) (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) B) 1) : WFF σ Δ 0 :=
  WFF.subst (Subst.setIdx (arrowXIdx img x cx) (.bnd 0) (.tm g))
    ((arrowXS σ Δ img x cx).set (.bnd 0) (.tm g))
    (Subst.ok_set (ok_arrowXS himg hx hcx) rfl)
    (Subst.coh_set (ok_arrowXS himg hx hcx) (coh_arrowXS himg hx hcx)
      ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf l).diaIn x)).insert _) Ctx.NoSlots.slots Φ

theorem sat_readArrowX {M : Model σ} {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) {w : M.frame.W} (env : M.Env Δ w)
    {B : VarType} {c : Ann B} (g : Term σ Δ B c)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) B) 1) :
    M.sat env (readArrowX himg hx hcx g Φ) ↔
      M.sat ((Model.substEnv (arrowXS σ Δ img x cx) (ok_arrowXS himg hx hcx)
        (Ctx.noProjLast_diaIn _ x) env).extend (.bnd 0) (Model.interp env g)) Φ := by
  unfold readArrowX
  rw [Model.sat_subst _ _ _ _ _ ((Ctx.noProjLast_diaIn _ x).insert (.bnd 0) B),
    Model.substEnv_set_tm]

theorem readArrowX_mono_congr {l l' : List VarType} (hl : l <:+ l') {Δ Δ' : Ctx} [Δ.NoSlots]
    [Δ'.NoSlots] (hΔ : Δ.Le Δ') {img img' : ℕ → ℕ} (himg : ImgOk l Δ img)
    (himg' : ImgOk l' Δ' img') (hag : ∀ r < l.length, img r = img' r) {x : VarSymb}
    {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    (hx' : (ctxOf l').ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : Δ.ref (.root (.free cx)) = some X) (hcx' : Δ'.ref (.root (.free cx)) = some X)
    {B : VarType} {c : Ann B} (g : Term σ Δ B c)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) B) 1) :
    WFF.mono hΔ (readArrowX himg hx hcx g Φ) =
      readArrowX himg' hx' hcx' (Term.mono hΔ g)
        (WFF.mono (((ctxOf_le_of_suffix hl).diaIn x).insert (.bnd 0) B) Φ) := by
  unfold readArrowX
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) Φ
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim T (SubE.mono hΔ (Subst.set _ _ _ (.root (.bnd 0))))
      (Subst.set _ _ _ (.root (.bnd 0)))
    rw [Subst.set_root, Subst.set_root]
    exact .refl _
  · have hv' : ((ctxOf l).diaIn x) v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    change SubE.Sim T (SubE.mono hΔ (Subst.set _ _ _ v)) (Subst.set _ _ _ v)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    rcases diaIn_item hv' with ⟨w, rfl, hw⟩ | ⟨rfl, _⟩
    · obtain ⟨r, hr, hlt, _⟩ := ref_rt hw
      change SubE.Sim T (.ren (itemAt (imgRoot img w.rt) w)) (.ren (itemAt (imgRoot img' w.rt) w))
      rw [hr, imgRoot, imgRoot, hag r hlt]
      exact .refl _
    · change SubE.Sim T (SubE.mono hΔ (if x = x then _ else _)) (if x = x then _ else _)
      rw [if_pos rfl, if_pos rfl]
      exact .refl _

/-- A body read along a witness arrow depends on the slot term only as a dependent pair. -/
theorem readArrowX_sig {l : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) {B : VarType} {c c' : Ann B}
    {g : Term σ Δ B c} {g' : Term σ Δ B c'} (h : (⟨c, g⟩ : Σ c, Term σ Δ B c) = ⟨c', g'⟩)
    (Φ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) B) 1) :
    readArrowX himg hx hcx g Φ = readArrowX himg hx hcx g' Φ := by
  cases h
  rfl

/-- ⭐The body `Φ(N[D])` over a witness's view, read at the witness child, is `Φ` read along the
    witness arrow, its slot filled by the object the items make. -/
theorem liftBodyX_bodyRepl_packMapC {bb : Bool} {hbb : ModalSys.T = bb}
    {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) {N : NShape}
    (n : NItems σ (ctxOf cls).boxIn N) (Φ : WFF σ (((ctxOf clt).diaIn x).insert (.bnd 0) N.ty) 1) :
    liftBodyX hs himgt hx hcx (WFF.bodyRepl
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (packMapC bb hbb cls n).obj.2) Φ) =
      readArrowX himgt hx hcx (n.mono (ctxOf_le_of_suffix hs)).obj.2 Φ := by
  unfold liftBodyX WFF.bodyRepl readArrowX
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = N.ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    change SubE.Sim _ ((arrowXS σ (ctxOf lv) imgt x cx).set (.bnd 0) _ (.root (.bnd 0)))
      ((((Subst.idS σ _).set (.bnd 0) _) (.root (.bnd 0))).comp _ _ _)
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma (Eq.symm ?_)
    rw [Term.subst_mono]
    exact subst_packMapC_obj _ _ _ _ (by
      change Subst.set _ _ _ (.root (.bnd 0)) = _
      exact Subst.set_root _ _ _) n
  · have hv' : ((ctxOf clt).diaIn x) v = some T := by
      change (if v = VarSymb.root (.bnd 0) then _ else _) = _ at hv
      rwa [if_neg hvr] at hv
    change SubE.Sim T ((arrowXS σ (ctxOf lv) imgt x cx).set (.bnd 0) _ v)
      ((((Subst.idS σ _).set (.bnd 0) _) v).comp _ _ _)
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    change SubE.Sim T _ ((Subst.set _ _ _).at v)
    rw [Subst.at_set_of_rt_ne _ _ (Ctx.ref_rt_ne
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).rootFresh (le_refl 0))
      ((Ctx.ref_nonproj _ hlp).trans hv')), Subst.at_nonproj _ hlp]
    exact .refl _

/-- ⭐⭐**A returning possibility along a witness from its far end, at a node**: along a witness
    arrow's way home with the invariant along the witness, `Φ(N)` at the far end, for the object
    `N` some items make, is `◇_x[d ↦ the items sent home] Φ(d)` at home. -/
theorem retx_of_invB {bb : Bool} {hbb : ModalSys.T = bb}
    {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hsM : Theory.IsMCS ts.M)
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvXB hS bb hbb tk ts cls imgs clt imgt x X cx) {N : NShape}
    (n : NItems σ (ctxOf cls).boxIn N)
    (Φ : WFF σ (((ctxOf clt).diaIn x).insert (.bnd 0) N.ty) 1)
    (hmem : ∃ (hs : cls <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
      (hx : (ctxOf clt).ref x = some (.VTypeDia X))
      (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X),
      readArrowX himgt hx hcx (n.mono (ctxOf_le_of_suffix hs)).obj.2 Φ ∈ tk.M) :
    ∃ (himgs : ImgOk cls (ctxOf ts.l) imgs) (ht : clt <:+ ts.l)
      (hx' : (ctxOf ts.l).ref x = some (.VTypeDia X)),
      (OutLeg.pos x ⟨X, hx'⟩ : OutLeg (ctxOf ts.l)).retS hS (.nec N)
        (n.subst (arrowIdx imgs) (arrowS σ (ctxOf ts.l) imgs) (ok_arrowS himgs)
          (coh_arrowS himgs)).2
        (WFF.mono (((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _) Φ) ∈ ts.M := by
  obtain ⟨hs, himgs, ht, himgt, hx, hcx, hinv⟩ := h
  obtain ⟨hs', himgt', hx'', hcx', hm⟩ := hmem
  refine ⟨himgs, ht, (ctxOf_le_of_suffix ht).ref hx, ?_⟩
  have hr := hinv (WFF.bodyRepl
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (packMapC bb hbb cls n).obj.2) Φ)
    (by rw [liftBodyX_bodyRepl_packMapC]; exact hm)
  rw [WFF.mono_bodyRepl ((ctxOf_le_of_suffix ht).diaIn x), Term.mono_mono] at hr
  have hc := hsM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
    ⟨Proof.ret_map hS (.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩) (S := .nec (tupShape bb hbb cls))
      (packMapC bb hbb cls n) (tupCompsImg cls imgs himgs ((bcT cls).compsAllB bb)
        (VarType.compOk_compsAllB bb hbb (bcT cls))).2
      (WFF.mono (((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _) Φ)
      (Proof.lookup List.mem_cons_self)⟩⟩
  exact (congrArg (· ∈ ts.M) (OutLeg.retS_congr hS _ (.nec N)
    (holeRead_tupCompsImg_packMapC himgs bb hbb n) rfl)).mp hc


namespace BData

variable (B : BData σ) (hS : ModalSys.BStrong = true)

/-- ⭐**Returning possibilities from the far end** (plain leg, necessary shapes): along an arrow
    `s → k`, `Φ(N)` at `k` (read along the arrow), for the object `N` some items make, is
    `◇[d ↦ the items sent home] Φ(d)` at `s`.  The limit of a strong chain has it
    (`bdataS_retIn`). -/
def RetIn : Prop :=
  ∀ {s k : B.W} (h : B.R s k) {i : ℕ} {N : NShape}
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) N.ty) 1) {j : ℕ}
    (hj : B.stg s k i ≤ j) (n : NItems σ ((B.w k).ctx j).boxIn N),
    readArrow ((B.imgOk h i).mono ((B.w k).le hj)) n.obj.2 Φ ∈ (B.w k).M j →
      ∃ hiK : i ≤ B.stg k s j,
        WFF.retS hS (.nec N) (n.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
          (ok_arrowS (B.imgOk (B.symm h) j)) (coh_arrowS (B.imgOk (B.symm h) j))).2
          (WFF.mono (((B.w s).le hiK).boxIn.insert (.bnd 0) _) Φ) ∈ (B.w s).M (B.stg k s j)

end BData

namespace BData

variable {B : BData σ}

/-- Canonical `Ind` is a congruence for pairing (as in `BData.indInvariant`). -/
theorem ind_pair {s : B.W} {A C : VarType} {a a' : B.frame.Dom A s} {b b' : B.frame.Dom C s}
    (h₁ : B.Ind a a') (h₂ : B.Ind b b') : B.Ind (A := .VTypeProd A C) (a, b) (a', b') := by
  obtain ⟨u₁, u₁', h₁, h₁', r₁⟩ := h₁
  obtain ⟨u₂, u₂', h₂, h₂', r₂⟩ := h₂
  refine ⟨⟨max u₁.i u₂.i, _, Term.pair (u₁.lift _ (le_max_left _ _))
      (u₂.lift _ (le_max_right _ _))⟩,
    ⟨max u₁'.i u₂'.i, _, Term.pair (u₁'.lift _ (le_max_left _ _))
      (u₂'.lift _ (le_max_right _ _))⟩, ?_, ?_, Canon.DTerm.Rel.pair r₁ r₂ _ _ _ _ _ _⟩
  · exact Prod.ext ((rden_lift (le_max_left u₁.i u₂.i) u₁.t).trans h₁)
      ((rden_lift (le_max_right u₁.i u₂.i) u₂.t).trans h₂)
  · exact Prod.ext ((rden_lift (le_max_left u₁'.i u₂'.i) u₁'.t).trans h₁')
      ((rden_lift (le_max_right u₁'.i u₂'.i) u₂'.t).trans h₂')

/-- ⭐**Coming back, canonically**: the object some items make at `k` comes back along the way
    home `k → s` as `o` exactly when the items sent home with their companions are `Ind` to it,
    componentwise: the arrow image of `compsVal` is the object's readings (`boxPush_canon_at`,
    `interp_compsVal`), `Ind` to `o` (`ind_compsRead`; pairs by `ind_pair`). -/
theorem ind_of_nComesBack {s k : B.W} (hR : B.R s k) (r : B.RT k s) {j : ℕ} {N : NShape}
    (n : NItems σ ((B.w k).ctx j).boxIn N) {o : B.frame.Dom N.flat s}
    (h : B.model.NComesBack N (Model.interp (B.canonEnv k j) n.obj.2) r o) :
    B.Ind (Model.interp (B.canonEnv s (B.stg k s j))
      (n.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
        (ok_arrowS (B.imgOk (B.symm hR) j)) (coh_arrowS (B.imgOk (B.symm hR) j))).2) o := by
  induction N with
  | boxC A cs hcs =>
      obtain ⟨_, u⟩ := n
      change B.Ind (Model.interp (B.canonEnv s (B.stg k s j))
        (Term.subst _ _ _ _ (compsVal u cs hcs).2)) o
      rw [Model.interp_subst _ _ _ (Ctx.noProjLast_boxIn _),
        ← boxPush_canon_at k _ ⟨s, ⟨r⟩⟩ (B.symm hR) le_rfl, Model.interp_compsVal]
      exact Model.ind_compsRead (M := B.model) (fun h₁ h₂ => ind_pair h₁ h₂) A
        (Model.interp (B.canonEnv k j) (Term.boxtm u)) r cs hcs o h
  | prod R S ihR ihS =>
      obtain ⟨n₁, n₂⟩ := n
      exact ind_pair (ihR n₁ h.1) (ihS n₂ h.2)

/-- ⭐⭐**`ret` at the own arrow, truth ⇒ membership** (T; plain leg, necessary shapes).  The
    object out there is here, made by some items (`definable_fromDom`, `NItems.exists_obj`).
    Packed into one `□` (`NItems.pack`) and read back by the unpacking map (`unpackAt`,
    `holeAt_unpackAt_obj`), the body at the packed object is in the theory by the induction
    hypothesis (`sat_hereRead`, `sat_bodyRepl`); `ret_hereC` at the packed object with all its
    companions, then `ret_map` along the unpacking map, give a value denoting the object's
    readings home (`interp_compsVal`, `holeVal_unpackAt_compsRead`), `Ind` to `t` (`ind_NRead`):
    so the value moves to `t` (`mem_ret_of_ind`). -/
theorem mem_ret_of_sat_here (hS : ModalSys.BStrong = true) (hInj : B.ImgInj)
    (hT : ModalSys.T = true) {s : B.W} {i : ℕ} {N : NShape} {a : Ann N.flat}
    (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.retS hS (.nec N) t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (e : B.frame.Dom N.ty s)
    (hΦ : B.model.sat (((B.canonEnv s i).boxPush (B.model.frame.reflAcc hT s)).extend (.bnd 0) e)
      Φ)
    (hInd : B.model.NComesBack N e (B.model.frame.refl hT s) (Model.interp (B.canonEnv s i) t)) :
    (WFF.retS hS (.nec N) t Φ : WFF σ _ 0) ∈ (B.w s).M i := by
  have hsz : (WFF.retS hS (.nec N) t Φ : WFF σ _ 0).size = Φ.size + N.flat.eqRecSize + 1 := rfl
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom N.ty s e
  obtain ⟨n, hn⟩ := NItems.exists_obj N g
  set J := max j₀ i
  have hj₀ : j₀ ≤ J := le_max_left _ _
  have hiJ : i ≤ J := le_max_right _ _
  set n' := n.mono ((B.w s).le hj₀)
  have he : Model.interp (B.canonEnv s J) n'.obj.2 = e := by
    have hn' : n'.obj = ⟨_, (B.w s).liftT hj₀ g⟩ := by
      rw [NItems.obj_mono, hn]
      rfl
    rw [← interp_lift hg hj₀]
    exact congrArg (fun x => Model.interp (B.canonEnv s J) x.2) hn'
  -- the packed object, and the unpacking map
  set sb := n'.pack.2
  set F := unpackAt (σ := σ) hT N
    (Term.eta (.root (.bnd 0)) N.packTy (Ctx.ref_insert_root _ _ _))
  have hobj : (⟨_, Term.holeAt (Term.boxtm sb) F.obj.2⟩ : Σ c, Term σ ((B.w s).ctx J) N.ty c) =
      n'.obj :=
    holeAt_unpackAt_obj hT sb N _ n' (Term.holeAt_eta_root sb)
  have hFe : B.model.holeVal F.obj.2 (Model.interp (B.canonEnv s J) (Term.boxtm sb)) = e := by
    rw [← Model.interp_holeAt]
    exact (congrArg (fun x => Model.interp (B.canonEnv s J) x.2) hobj).trans he
  -- the body at the packed object
  set Φ' := WFF.mono (((B.w s).le hiJ).boxIn.insert (.bnd 0) _) Φ with hΦ'
  set Ψ := WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) F.obj.2) Φ' with hΨ
  have hsat : B.model.sat (B.canonEnv s J) (WFF.hereRead hT (Term.boxtm sb) Ψ) := by
    rw [Model.sat_hereRead hT (B.noProjLast s J)]
    refine (Model.sat_bodyRepl (Ctx.noProjLast_boxIn _) _ _ Φ' _).mpr ?_
    rw [Model.interp_mono (Model.Env.extend_agree (h := Ctx.empty_le _)
      (env := Model.Env.empty _) (fun _ _ h => nomatch h) (.bnd 0) _)]
    have hFe' : Model.interp ((Model.Env.empty (M := B.model) s).extend (.bnd 0)
        (Model.interp (B.canonEnv s J) (Term.boxtm sb))) F.obj.2 = e := hFe
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
  have hmem : WFF.retS hS (.nec N) (Term.holeRead V F.val.2) Φ' ∈ (B.w s).M J :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hmb)
      ⟨Proof.ret_map hS .nec (S := .nec (.boxC N.packTy _ _)) F V Φ'
        (Proof.ret_hereC hS hT sb _ _ Ψ (Proof.lookup List.mem_cons_self))⟩
  refine mem_ret_of_ind hS hInj (B.exists_R_of_T hT s) (S := .nec N) hiJ _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec, hsz]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _))).mp hs) hmem ?_
  -- the value denotes the object's readings home
  have hv : Model.interp (B.canonEnv s J) (Term.holeRead V F.val.2) =
      B.model.NRead N e (B.model.frame.refl hT s) := by
    rw [Model.interp_holeRead (B.noProjLast s J),
      Model.interp_collapse (Model.Env.collapseAgree_self hT _)]
    refine (congrArg (B.model.holeVal F.val.2)
      (Model.interp_compsVal (M := B.model) (B.canonEnv s J) sb s (B.model.frame.refl hT s)
        (N.packTy.compsAllB true) (VarType.compOk_compsAllB true hT _))).trans ?_
    rw [holeVal_unpackAt_compsRead hT, hFe]
  have hI : B.Ind (Model.interp (B.canonEnv s J) (Term.holeRead V F.val.2))
      (Model.interp (B.canonEnv s i) t) := by
    rw [hv]
    exact Model.ind_NRead (M := B.model) (fun h₁ h₂ => ind_pair h₁ h₂) N e _ _ hInd
  rw [interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon t (Model.Env.Agree.refl' _)] at hI
  exact hI

/-- ⭐⭐**`ret`, truth ⇒ membership** (plain leg, necessary shapes; strong B).  A true
    `◇[d ↦ t] Φ(d)` has an arrow `s → k` (the own arrow: `mem_ret_of_sat_here`) and an object
    there with `Φ`, coming back `Ind` to `t`.
    The object is a term's denotation, made by some items (`definable_fromDom`,
    `NItems.exists_obj`); the body at `k` is in the theory by the induction hypothesis
    (`sat_readArrow`, `boxPush_canon_at`); the way home gives `◇[d ↦ the items sent home] Φ(d)` at
    `s` (`RetIn`); and the items sent home are `Ind` to `t` (`ind_of_nComesBack`), so the value
    moves to `t` (`mem_ret_of_ind`). -/
theorem mem_ret_of_sat_nec (hS : ModalSys.BStrong = true) (hInj : B.ImgInj) (hRI : B.RetIn hS)
    {s : B.W} {i : ℕ} {N : NShape} {a : Ann N.flat} (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < (WFF.retS hS (.nec N) t Φ : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : B.model.sat (B.canonEnv s i) (WFF.retS hS (.nec N) t Φ : WFF σ _ 0)) :
    (WFF.retS hS (.nec N) t Φ : WFF σ _ 0) ∈ (B.w s).M i := by
  have hsz : (WFF.retS hS (.nec N) t Φ : WFF σ _ 0).size = Φ.size + N.flat.eqRecSize + 1 := rfl
  obtain ⟨⟨k, ⟨rk⟩⟩, e, hΦ, r, hInd⟩ := h
  rcases rk with hR | ⟨hT, rfl⟩
  swap
  · exact mem_ret_of_sat_here hS hInj hT t Φ IH e hΦ hInd
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom N.ty k e
  obtain ⟨n, hn⟩ := NItems.exists_obj N g
  have hj₀ : j₀ ≤ max j₀ (B.stg s k i) := le_max_left _ _
  have hj : B.stg s k i ≤ max j₀ (B.stg s k i) := le_max_right _ _
  have he : Model.interp (B.canonEnv k (max j₀ (B.stg s k i)))
      (n.mono ((B.w k).le hj₀)).obj.2 = e := by
    have hn' : (n.mono ((B.w k).le hj₀)).obj = ⟨_, (B.w k).liftT hj₀ g⟩ := by
      rw [NItems.obj_mono, hn]
      rfl
    rw [← interp_lift hg hj₀]
    exact congrArg (fun x => Model.interp (B.canonEnv k (max j₀ (B.stg s k i))) x.2) hn'
  have hsatb : B.model.sat (B.canonEnv k (max j₀ (B.stg s k i)))
      (readArrow ((B.imgOk hR i).mono ((B.w k).le hj))
        (n.mono ((B.w k).le hj₀)).obj.2 Φ) := by
    rw [sat_readArrow, he, ← boxPush_canon_at s i ⟨k, ⟨Or.inl hR⟩⟩ hR hj]
    exact hΦ
  have hmb := (IH k _ _ (by
    rw [hsz]; unfold readArrow; rw [WFF.size_subst]; omega)).mp hsatb
  obtain ⟨hiK, hret⟩ := hRI hR Φ hj _ hmb
  refine mem_ret_of_ind hS hInj (S := .nec N) ⟨k, hR⟩ hiK _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec, hsz]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _))).mp hs) hret ?_
  have hr' : B.RT k s := r
  change B.model.NComesBack N e r _ at hInd
  rw [← he] at hInd
  have hI := ind_of_nComesBack hR hr' _ hInd
  rw [interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon t (Model.Env.Agree.refl' _)] at hI
  exact hI

/-- ⭐**Returning possibilities along a witness from the far end** (necessary shapes): along an
    arrow `s → k` of `y`'s extent, `Φ(N)` at `k` (read along the witness arrow), for the object
    `N` some items make, is `◇_y[d ↦ the items sent home] Φ(d)` at `s`.  The limit of a strong
    chain has it (`bdataS_retInX`). -/
def RetInX (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s k : B.W} {y : VarSymb} {Y : VarType} (hk : B.kd s k = some (y, Y)) {i : ℕ}
    (hy : ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape}
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) N.ty) 1) {j : ℕ}
    (hj : B.stg s k i ≤ j) (n : NItems σ ((B.w k).ctx j).boxIn N),
    readArrowX ((B.imgOk (B.kdR hk) i).mono ((B.w k).le hj)) hy (((B.w k).le hj).ref (B.hcx hk i))
      n.obj.2 Φ ∈ (B.w k).M j →
      ∃ hiK : i ≤ B.stg k s j,
        (OutLeg.pos y ⟨Y, ((B.w s).le hiK).ref hy⟩ : OutLeg ((B.w s).ctx (B.stg k s j))).retS hS
          (.nec N) (n.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
            (ok_arrowS (B.imgOk (B.symm (B.kdR hk)) j))
            (coh_arrowS (B.imgOk (B.symm (B.kdR hk)) j))).2
          (WFF.mono ((((B.w s).le hiK).diaIn y).insert (.bnd 0) _) Φ) ∈ (B.w s).M (B.stg k s j)

/-- ⭐⭐**`ret` along a witness at the own arrow, truth ⇒ membership** (T; necessary shapes).  The
    own arrow lies in `y`'s extent only for a realised witness (network arrows never loop,
    `B.irrefl`), whose `Here` atom is in the theory (`mem_here_real`), with a value denoting the
    content here (`interp_dia_self`).  The body along `y` is the view body of its abstraction
    (`WFF.viewBody_bodyAbsA`, `sat_viewBody_here'`); then as `mem_ret_of_sat_here`, by
    `ret_hereXC` and `ret_map` along the unpacking map. -/
theorem mem_retx_of_sat_here (hS : ModalSys.BStrong = true) (hInj : B.ImgInj)
    (hT : ModalSys.T = true) {s : B.W} {i : ℕ} {y : VarSymb}
    (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape} {a : Ann N.flat}
    (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ :
        WFF σ _ 0).size → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    {Y : VarType} (hY : ((B.w s).ctx i).ref y = some (.VTypeDia Y))
    (hm : B.model.frame.reflAcc hT s ∈ (B.model.posEval ((B.canonEnv s i).ref y hY)).1)
    (e : B.frame.Dom N.ty s)
    (hΦ : B.model.sat (((B.canonEnv s i).diaPush y hY ⟨_, hm⟩).extend (.bnd 0) e) Φ)
    (hInd : B.model.NComesBack N e (B.model.frame.refl hT s) (Model.interp (B.canonEnv s i) t)) :
    ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0) ∈
      (B.w s).M i := by
  have hsz : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ :
      WFF σ _ 0).size = Φ.size + N.flat.eqRecSize + 1 := rfl
  have hr : (B.w s).Realised y :=
    (mem_extent_self (canonEnv_extent s i hY ▸ hm) fun ⟨_, hk⟩ => B.irrefl s (B.lbR hk)).2
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom N.ty s e
  obtain ⟨n, hn⟩ := NItems.exists_obj N g
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
  -- the witness's realisation here, and its value
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
  -- the packed object, and the unpacking map
  set n' := n.mono ((B.w s).le hj₀)
  have he : Model.interp (B.canonEnv s J') n'.obj.2 = e := by
    have hn' : n'.obj = ⟨_, (B.w s).liftT hj₀ g⟩ := by
      rw [NItems.obj_mono, hn]
      rfl
    rw [← interp_lift hg hj₀]
    exact congrArg (fun x => Model.interp (B.canonEnv s J') x.2) hn'
  set sb := n'.pack.2
  set F := unpackAt (σ := σ) hT N
    (Term.eta (.root (.bnd 0)) N.packTy (Ctx.ref_insert_root _ _ _))
  have hobj : (⟨_, Term.holeAt (Term.boxtm sb) F.obj.2⟩ : Σ c, Term σ ((B.w s).ctx J') N.ty c) =
      n'.obj :=
    holeAt_unpackAt_obj hT sb N _ n' (Term.holeAt_eta_root sb)
  have hFe : B.model.holeVal F.obj.2 (Model.interp (B.canonEnv s J') (Term.boxtm sb)) = e := by
    rw [← Model.interp_holeAt]
    exact (congrArg (fun x => Model.interp (B.canonEnv s J') x.2) hobj).trans he
  -- the body at the packed object, abstracted
  set Φ' := WFF.mono ((((B.w s).le hiJ').diaIn y).insert (.bnd 0) _) Φ with hΦ'
  set Ψ := WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) F.obj.2) Φ' with hΨ
  set χ := WFF.bodyAbsA y hYJ' Ψ with hχ
  have hsat : B.model.sat (B.canonEnv s J')
      (WFF.hereRead hT (Term.pair t₀ (Term.boxtm sb)) χ) := by
    rw [Model.sat_hereRead hT (B.noProjLast s J')]
    have hp : Model.interp (B.canonEnv s J') (Term.pair t₀ (Term.boxtm sb)) =
        (Model.interp ((B.canonEnv s J').diaPush y hYJ' ⟨_, hmJ'⟩) bd,
          Model.interp (B.canonEnv s J') (Term.boxtm sb)) := Prod.ext hcont.symm rfl
    rw [hp]
    refine (Model.sat_viewBody_here' (B.canonEnv s J') hT hyJ' hYJ' bd χ hmJ' _).mp ?_
    rw [hχ, WFF.viewBody_bodyAbsA]
    refine (Model.sat_bodyRepl (Ctx.noProjLast_diaIn _ y) _ _ Φ' _).mpr ?_
    rw [Model.interp_mono (Model.Env.extend_agree (h := Ctx.empty_le _)
      (env := Model.Env.empty _) (fun _ _ h => nomatch h) (.bnd 0) _)]
    have hFe' : Model.interp ((Model.Env.empty (M := B.model) s).extend (.bnd 0)
        (Model.interp (B.canonEnv s J') (Term.boxtm sb))) F.obj.2 = e := hFe
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
      [WFF.here hT (Term.diatm y hyJ' bd) t₀, WFF.hereRead hT (Term.pair t₀ (Term.boxtm sb)) χ]
      ((OutLeg.pos y hyJ' : OutLeg ((B.w s).ctx J')).retS hS
        (.nec (.boxC N.packTy _ (VarType.compOk_compsAllB true hT N.packTy))) V Ψ) := by
    have h := Proof.ret_hereXC (Δ := [WFF.here hT (Term.diatm y hyJ' bd) t₀,
      WFF.hereRead hT (Term.pair t₀ (Term.boxtm sb)) χ]) hS hT y hyJ' bd t₀ sb
      (N.packTy.compsAllB true)
      (VarType.compOk_compsAllB true hT N.packTy) χ (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [hχ, WFF.viewBody_bodyAbsA] at h
    exact h
  have hmem : (OutLeg.pos y hyJ' : OutLeg ((B.w s).ctx J')).retS hS (.nec N)
      (Term.holeRead V F.val.2) Φ' ∈ (B.w s).M J' :=
    BWorld.mem_of_provable (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hh
        · rw [List.mem_singleton.mp hψ]; exact hmb)
      ⟨Proof.ret_map hS (.pos y hyJ') (S := .nec (.boxC N.packTy _ _)) F V Φ' hpf⟩
  refine mem_retx_of_ind hS hInj (B.exists_R_of_T hT s) (S := .nec N) hiJ' hy _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec, hsz]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _))).mp hs) hmem ?_
  -- the value denotes the object's readings home
  have hv : Model.interp (B.canonEnv s J') (Term.holeRead V F.val.2) =
      B.model.NRead N e (B.model.frame.refl hT s) := by
    rw [Model.interp_holeRead (B.noProjLast s J'),
      Model.interp_collapse (Model.Env.collapseAgree_self hT _)]
    refine (congrArg (B.model.holeVal F.val.2)
      (Model.interp_compsVal (M := B.model) (B.canonEnv s J') sb s (B.model.frame.refl hT s)
        (N.packTy.compsAllB true) (VarType.compOk_compsAllB true hT _))).trans ?_
    rw [holeVal_unpackAt_compsRead hT, hFe]
  have hI : B.Ind (Model.interp (B.canonEnv s J') (Term.holeRead V F.val.2))
      (Model.interp (B.canonEnv s i) t) := by
    rw [hv]
    exact Model.ind_NRead (M := B.model) (fun h₁ h₂ => ind_pair h₁ h₂) N e _ _ hInd
  rw [interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon t (Model.Env.Agree.refl' _)] at hI
  exact hI

/-- ⭐⭐**`ret` along a witness, truth ⇒ membership** (necessary shapes; strong B): as
    `mem_ret_of_sat_nec`, along an arrow of `y`'s extent (a witness arrow, T being off) with the
    invariant along `y` (`RetInX`, `diaPush_canon_at`, `mem_retx_of_ind`). -/
theorem mem_retx_of_sat (hS : ModalSys.BStrong = true) (hInj : B.ImgInj)
    (hRX : B.RetInX hS) {s : B.W} {i : ℕ} {y : VarSymb}
    (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape} {a : Ann N.flat}
    (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ :
        WFF σ _ 0).size → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0)) :
    ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0) ∈
      (B.w s).M i := by
  have hsz : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ :
      WFF σ _ 0).size = Φ.size + N.flat.eqRecSize + 1 := rfl
  obtain ⟨Y, hY, a₁, e, hΦ, r, hInd⟩ := h
  have hext : a₁.1 ∈ B.extent s y := canonEnv_extent s i hY ▸ a₁.2
  rcases hext with ⟨X', hk⟩ | ⟨hnR, -⟩
  swap
  · obtain ⟨⟨k, ⟨rk⟩⟩, ha⟩ := a₁
    rcases rk with hR | ⟨hT, rfl⟩
    · exact absurd hR hnR
    · exact mem_retx_of_sat_here hS hInj hT hy t Φ IH hY ha e hΦ hInd
  replace hk := B.lb_kd hk
  obtain rfl := B.hxX hk i Y hY
  have hR := B.kdR hk
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom N.ty a₁.1.1 e
  obtain ⟨n, hn⟩ := NItems.exists_obj N g
  have hj₀ : j₀ ≤ max j₀ (B.stg s a₁.1.1 i) := le_max_left _ _
  have hj : B.stg s a₁.1.1 i ≤ max j₀ (B.stg s a₁.1.1 i) := le_max_right _ _
  have he : Model.interp (B.canonEnv a₁.1.1 (max j₀ (B.stg s a₁.1.1 i)))
      (n.mono ((B.w a₁.1.1).le hj₀)).obj.2 = e := by
    have hn' : (n.mono ((B.w a₁.1.1).le hj₀)).obj = ⟨_, (B.w a₁.1.1).liftT hj₀ g⟩ := by
      rw [NItems.obj_mono, hn]
      rfl
    rw [← interp_lift hg hj₀]
    exact congrArg (fun x => Model.interp (B.canonEnv a₁.1.1 (max j₀ (B.stg s a₁.1.1 i))) x.2) hn'
  have hsatb : B.model.sat (B.canonEnv a₁.1.1 (max j₀ (B.stg s a₁.1.1 i)))
      (readArrowX ((B.imgOk hR i).mono ((B.w a₁.1.1).le hj)) hY
        (((B.w a₁.1.1).le hj).ref (B.hcx hk i))
        (n.mono ((B.w a₁.1.1).le hj₀)).obj.2 Φ) := by
    rw [sat_readArrowX, he, ← diaPush_canon_at s i hY a₁ hk hj]
    exact hΦ
  have hmb := (IH a₁.1.1 _ _ (by
    rw [hsz]; unfold readArrowX; rw [WFF.size_subst]; omega)).mp hsatb
  obtain ⟨hiK, hret⟩ := hRX hk hY Φ hj _ hmb
  refine mem_retx_of_ind hS hInj (S := .nec N) ⟨a₁.1.1, hR⟩ hiK hy _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec, hsz]; exact Nat.lt_succ_of_le (Nat.le_add_left _ _))).mp hs) hret ?_
  have hr' : B.RT a₁.1.1 s := r
  change B.model.NComesBack N e r _ at hInd
  rw [← he] at hInd
  have hI := ind_of_nComesBack hR hr' _ hInd
  rw [interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon t (Model.Env.Agree.refl' _)] at hI
  exact hI

end BData

section Limit

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐⭐**The limit has returning possibilities from the far end**: the invariant of the way home
    `k → s` (`lretAtB`, reduced by `RetAtB.toRetInvB`), at a node (`ret_of_invB`). -/
theorem bdataS_retIn : (bdataS C).RetIn hS := by
  classical
  intro s k h i N Φ j hj n hm
  obtain ⟨cls, imgs, clt, imgt, hJs, hJag, his, hiag, hret⟩ := lretAtB C h.symm j i hj
  have hsp := (lstg_spec C.toFairChain h i).1
  have hkp := (lstg_spec C.toFairChain h.symm j).1
  have hiK : i ≤ lstg C.toFairChain k s j := by
    change lstg C.toFairChain s k i ≤ j at hj
    omega
  have hsl : (C.net (birth C.toFairChain s.2 + lstg C.toFairChain k s j)).Live s.1 :=
    live_birth C.toFairChain s.2 (Nat.le_add_right _ _)
  have hsM := (C.good _).mcs s.1 hsl
  have hinv := RetAtB.toRetInvB hsM hret
  obtain ⟨hcs, -, ht, himgt, -⟩ := id hinv
  -- what `k` has at stage `j`, grown to the round of the invariant
  have hg := grow_stage C.toFairChain k j (m := birth C.toFairChain s.2 +
    lstg C.toFairChain k s j) hkp
  have hm' := hg.sub _ hm
  rw [readArrow_mono_congr his _ _ himgt (fun r hr => (hiag r hr).symm)] at hm'
  obtain ⟨himgs, ht', hr⟩ := ret_of_invB hsM hinv
    (n.mono (ctxOf_le_of_suffix hJs)) _
    ⟨hcs, himgt, by
      rw [NItems.mono_mono, readArrow_sig _ (NItems.obj_mono _ n)]
      exact hm'⟩
  refine ⟨hiK, (congrArg (· ∈ _) (OutLeg.retS_congr hS .nec (.nec N) ?_ ?_)).mp hr⟩
  · rw [NItems.subst_mono]
    exact NItems.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
  · rw [WFF.mono_mono]

/-- ⭐⭐**The limit has returning possibilities along a witness from the far end**: the way home's
    invariant along the witness (`lretAtB`, `RetAtB.toRetInvXB`), at a node (`retx_of_invB`). -/
theorem bdataS_retInX : (bdataS C).RetInX hS := by
  classical
  intro s k y Y hk i hy N Φ j hj n hm
  have h : LR C.toFairChain s k := lkdR hk
  obtain ⟨cls, imgs, clt, imgt, hJs, hJag, his, hiag, hret⟩ := lretAtB C h.symm j i hj
  have hsp := (lstg_spec C.toFairChain h i).1
  have hkp := (lstg_spec C.toFairChain h.symm j).1
  have hiK : i ≤ lstg C.toFairChain k s j := by
    change lstg C.toFairChain s k i ≤ j at hj
    omega
  have hsl : (C.net (birth C.toFairChain s.2 + lstg C.toFairChain k s j)).Live s.1 :=
    live_birth C.toFairChain s.2 (Nat.le_add_right _ _)
  have hsM := (C.good _).mcs s.1 hsl
  have hk' : lkd C.toFairChain s k = some (y, Y) := hk
  rw [hk'] at hret
  have hinv := RetAtB.toRetInvXB hsM hret
  obtain ⟨hcs, -, ht, himgt, hxc, hcxc, -⟩ := id hinv
  have hg := grow_stage C.toFairChain k j (m := birth C.toFairChain s.2 +
    lstg C.toFairChain k s j) hkp
  have hm' := hg.sub _ hm
  rw [readArrowX_mono_congr his _ _ himgt (fun r hr => (hiag r hr).symm) _ hxc _ hcxc] at hm'
  obtain ⟨himgs, ht', hx', hr⟩ := retx_of_invB hsM hinv
    (n.mono (ctxOf_le_of_suffix hJs)) _
    ⟨hcs, himgt, hxc, hcxc, by
      rw [NItems.mono_mono, readArrowX_sig _ _ _ (NItems.obj_mono _ n)]
      exact hm'⟩
  refine ⟨hiK, (congrArg (· ∈ _) (OutLeg.retS_congr hS _ (.nec N) ?_ ?_)).mp hr⟩
  · rw [NItems.subst_mono]
    exact NItems.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
  · rw [WFF.mono_mono]

end Limit

end BArrow

end V12M
