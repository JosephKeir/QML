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

omit [ModalSys.NoFour] in
theorem sig_holeAt {Γ : Ctx} {A : VarType} {a a' : Ann A} {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    (h : (⟨a, t⟩ : Σ c, Term σ Γ A c) = ⟨a', t'⟩) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.holeAt t s⟩ : Σ c, Term σ Γ B c) = ⟨_, Term.holeAt t' s⟩ := by
  cases h
  rfl

/-! ## Items of a necessary shape -/

/-- ⭐The **items of a necessary shape** over a `□` view `V`: one term of `V` for each `□`. -/
def NTerms (σ : Signature) (V : Ctx) : NShape → Type
  | .box A => Σ b, Term σ V A b
  | .boxC _ (_ :: _) _ => PEmpty
  | .prod R S => NTerms σ V R × NTerms σ V S

namespace NTerms

variable {V V' : Ctx}

/-- Weakening the items. -/
def mono (h : V.Le V') : {N : NShape} → NTerms σ V N → NTerms σ V' N
  | .box _, ⟨_, u⟩ => ⟨_, Term.mono h u⟩
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) => (mono h n₁, mono h n₂)

/-- ⭐The necessary object they make: `□u` for each item, paired. -/
def obj {Γ : Ctx} : {N : NShape} → NTerms σ Γ.boxIn N → Σ c, Term σ Γ N.ty c
  | .box _, ⟨_, u⟩ => ⟨_, Term.boxtm u⟩
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) => ⟨_, Term.pair (obj n₁).2 (obj n₂).2⟩

/-- ⭐The value they make along a substitution (the way home): each item sent along it, paired. -/
def subst (ι : VarSymb → VarSymb) {Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok V θ)
    (hc : Subst.Coh ι V θ) : {N : NShape} → NTerms σ V N → Σ c, Term σ Δ N.flat c
  | .box _, ⟨_, u⟩ => ⟨_, Term.subst ι θ hθ hc u⟩
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) => ⟨_, Term.pair (subst ι θ hθ hc n₁).2 (subst ι θ hθ hc n₂).2⟩

omit [ModalSys.NoFour] in
/-- ⭐Every term of a necessary shape's type is the object of its items (T off: no companions). -/
theorem exists_obj {Γ : Ctx} (hT : ModalSys.T = false) : (N : NShape) → {c : Ann N.ty} →
    (g : Term σ Γ N.ty c) → ∃ n : NTerms σ Γ.boxIn N, n.obj = ⟨c, g⟩
  | .box _, _, .boxtm u => ⟨⟨_, u⟩, rfl⟩
  | .boxC _ (_ :: _) h, _, _ =>
      absurd ((h.resolve_left (List.cons_ne_nil _ _)).1.symm.trans hT) (by decide)
  | .prod R S, _, .pair g₁ g₂ => by
      obtain ⟨n₁, h₁⟩ := exists_obj hT R g₁
      obtain ⟨n₂, h₂⟩ := exists_obj hT S g₂
      exact ⟨(n₁, n₂), sig_pair h₁ h₂⟩

omit [ModalSys.NoFour] in
theorem obj_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') : {N : NShape} → (n : NTerms σ Γ.boxIn N) →
    (n.mono h.boxIn).obj = ⟨_, Term.mono h n.obj.2⟩
  | .box _, ⟨_, _⟩ => rfl
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) => sig_pair (obj_mono h n₁) (obj_mono h n₂)

omit [ModalSys.NoFour] in
theorem mono_mono {V'' : Ctx} (h : V.Le V') (h' : V'.Le V'') : {N : NShape} →
    (n : NTerms σ V N) → (n.mono h).mono h' = n.mono (h.trans h')
  | .box _, ⟨_, u⟩ => by
      change (⟨_, Term.mono h' (Term.mono h u)⟩ : Σ b, Term σ V'' _ b) = ⟨_, _⟩
      rw [Term.mono_mono]
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) => Prod.ext (mono_mono h h' n₁) (mono_mono h h' n₂)

omit [ModalSys.NoFour] in
theorem subst_mono {ι : VarSymb → VarSymb} {Δ : Ctx} (h : V.Le V') (θ : Subst σ Δ)
    (hθ : Subst.Ok V' θ) (hc : Subst.Coh ι V' θ) : {N : NShape} → (n : NTerms σ V N) →
    (n.mono h).subst ι θ hθ hc = n.subst ι θ (hθ.restrict h) (hc.restrict h)
  | .box _, ⟨_, u⟩ => by
      change (⟨_, Term.subst ι θ hθ hc (Term.mono h u)⟩ : Σ b, Term σ Δ _ b) = ⟨_, _⟩
      rw [Term.subst_mono]
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) => sig_pair (subst_mono h θ hθ hc n₁) (subst_mono h θ hθ hc n₂)

omit [ModalSys.NoFour] in
theorem subst_congr {ι ι' : VarSymb → VarSymb} {Δ : Ctx} (θ θ' : Subst σ Δ)
    (hθ : Subst.Ok V θ) (hθ' : Subst.Ok V θ') (hc : Subst.Coh ι V θ) (hc' : Subst.Coh ι' V θ')
    (hs : Subst.Sim V θ θ') : {N : NShape} → (n : NTerms σ V N) →
    n.subst ι θ hθ hc = n.subst ι' θ' hθ' hc'
  | .box _, ⟨_, u⟩ => Term.subst_congr θ θ' hθ hθ' hc hc' hs u
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) =>
      sig_pair (subst_congr θ θ' hθ hθ' hc hc' hs n₁) (subst_congr θ θ' hθ hθ' hc hc' hs n₂)

end NTerms

/-- ⭐The **packing map** of items over the committed roots: from the one necessary object holding
    all the roots' items to the object the items make — a hole term (`packT`) at each `□`. -/
def packMap (cls : List VarType) : {N : NShape} → NTerms σ (ctxOf cls).boxIn N →
    ShapeMap σ (.box (bcT cls)) N
  | .box _, ⟨_, u⟩ => .hole (packT cls u)
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) => .pair (packMap cls n₁) (packMap cls n₂)

/-- ⭐The packing map's object, read where the bound object is the roots' items: the object the
    items make (`holeAt_tupT_packT_mono` at each `□`). -/
theorem subst_packMap_obj {cls : List VarType} {ι : VarSymb → VarSymb} {Δ : Ctx}
    (θ : Subst σ Δ) (hθ : Subst.Ok (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))) θ)
    (hc : Subst.Coh ι (Ctx.empty.insert (.bnd 0) (.VTypeBox (bcT cls))) θ)
    (hle : (ctxOf cls).boxIn.Le Δ.boxIn)
    (h0 : θ.at (.root (.bnd 0)) = .tm (Term.boxtm (Term.mono hle (tupT cls).2))) :
    {N : NShape} → (n : NTerms σ (ctxOf cls).boxIn N) →
    (⟨_, Term.subst ι θ hθ hc (packMap cls n).obj.2⟩ : Σ c, Term σ Δ N.ty c) = (n.mono hle).obj
  | .box _, ⟨_, u⟩ => by
      change (⟨_, Term.boxtm (Term.subst _ _ _ _ (Term.holeAt _ (packT cls u)))⟩ :
        Σ c, Term σ Δ (.VTypeBox _) c) = _
      refine sig_boxtm ?_
      refine (Term.subst_holeAt_sig _ _ _ _ _).trans ?_
      refine (sig_holeAt (Term.subst_eta_tm _ _ _ _ _ _ _
        (Subst.box_at_inner_boxtm _ h0)) _).trans ?_
      exact holeAt_tupT_packT_mono _ u
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) =>
      sig_pair (subst_packMap_obj θ hθ hc hle h0 n₁) (subst_packMap_obj θ hθ hc hle h0 n₂)

/-- ⭐The packing map's value at the tuple of the roots' images: the items sent along the arrow
    (`holeRead_tupImgT_packT` at each `□`). -/
theorem holeRead_tupImgT_packMap {cls : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk cls Δ img) : {N : NShape} → (n : NTerms σ (ctxOf cls).boxIn N) →
    (⟨_, Term.holeRead (tupImgT cls img himg).2 (packMap cls n).val.2⟩ :
      Σ c, Term σ Δ N.flat c) =
      n.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
  | .box _, ⟨_, u⟩ => holeRead_tupImgT_packT himg u
  | .boxC _ (_ :: _) _, n => PEmpty.elim n
  | .prod _ _, (n₁, n₂) =>
      sig_pair (holeRead_tupImgT_packMap himg n₁) (holeRead_tupImgT_packMap himg n₂)

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
    reading them at the tuple's items gives them back (`subst_packMap_obj`). -/
theorem liftBody_bodyRepl_packMap {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {N : NShape} (n : NTerms σ (ctxOf cls).boxIn N)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) N.ty) 1) :
    liftBody hs himgt (WFF.bodyRepl
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (packMap cls n).obj.2) Φ) =
      readArrow himgt (n.mono (ctxOf_le_of_suffix hs).boxIn).obj.2 Φ := by
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
    exact subst_packMap_obj _ _ _ _ (by
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
    (`liftBody_bodyRepl_packMap`), then `ret_map` along the packing map
    (`holeRead_tupImgT_packMap`). -/
theorem ret_of_inv {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hsM : Theory.IsMCS ts.M)
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} (h : RetInv hS tk ts cls imgs clt imgt)
    {N : NShape} (n : NTerms σ (ctxOf cls).boxIn N)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) N.ty) 1)
    (hmem : ∃ (hs : cls <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt),
      readArrow himgt (n.mono (ctxOf_le_of_suffix hs).boxIn).obj.2 Φ ∈ tk.M) :
    ∃ (himgs : ImgOk cls (ctxOf ts.l) imgs) (ht : clt <:+ ts.l),
      WFF.retS hS (.nec N)
        (n.subst (arrowIdx imgs) (arrowS σ (ctxOf ts.l) imgs) (ok_arrowS himgs)
          (coh_arrowS himgs)).2
        (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ) ∈ ts.M := by
  obtain ⟨hs, himgs, ht, himgt, hinv⟩ := h
  obtain ⟨hs', himgt', hm⟩ := hmem
  refine ⟨himgs, ht, ?_⟩
  have hr := hinv (WFF.bodyRepl
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (packMap cls n).obj.2) Φ)
    (by rw [liftBody_bodyRepl_packMap]; exact hm)
  rw [WFF.mono_bodyRepl (ctxOf_le_of_suffix ht).boxIn, Term.mono_mono] at hr
  have hc := hsM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
    ⟨Proof.ret_map hS .nec (S := .nec (.box (bcT cls))) (packMap cls n)
      (tupImgT cls imgs himgs).2 (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Φ)
      (Proof.lookup List.mem_cons_self)⟩⟩
  exact (congrArg (· ∈ ts.M) (OutLeg.retS_congr hS .nec (.nec N)
    (holeRead_tupImgT_packMap himgs n) rfl)).mp hc

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
      (B.img s a.1.1) y (B.cx s a.1.1))
      (ok_arrowXS ((B.imgOk (B.kdR hk) i).mono ((B.w a.1.1).le hj)) hr
        (((B.w a.1.1).le hj).ref (B.hcx hk i)))
      (Ctx.noProjLast_diaIn _ y) (B.canonEnv a.1.1 j) := by
  rw [diaPush_canon s i hr a ⟨Y, hk⟩]
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
theorem liftBodyX_bodyRepl_packMap {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) {N : NShape}
    (n : NTerms σ (ctxOf cls).boxIn N) (Φ : WFF σ (((ctxOf clt).diaIn x).insert (.bnd 0) N.ty) 1) :
    liftBodyX hs himgt hx hcx (WFF.bodyRepl
        (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (packMap cls n).obj.2) Φ) =
      readArrowX himgt hx hcx (n.mono (ctxOf_le_of_suffix hs).boxIn).obj.2 Φ := by
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
    exact subst_packMap_obj _ _ _ _ (by
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
theorem retx_of_inv {hS : ModalSys.BStrong = true} {tk ts : NodeSt σ} (hsM : Theory.IsMCS ts.M)
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (h : RetInvX hS tk ts cls imgs clt imgt x X cx) {N : NShape}
    (n : NTerms σ (ctxOf cls).boxIn N)
    (Φ : WFF σ (((ctxOf clt).diaIn x).insert (.bnd 0) N.ty) 1)
    (hmem : ∃ (hs : cls <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
      (hx : (ctxOf clt).ref x = some (.VTypeDia X))
      (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X),
      readArrowX himgt hx hcx (n.mono (ctxOf_le_of_suffix hs).boxIn).obj.2 Φ ∈ tk.M) :
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
    (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) (packMap cls n).obj.2) Φ)
    (by rw [liftBodyX_bodyRepl_packMap]; exact hm)
  rw [WFF.mono_bodyRepl ((ctxOf_le_of_suffix ht).diaIn x), Term.mono_mono] at hr
  have hc := hsM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hr,
    ⟨Proof.ret_map hS (.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩) (S := .nec (.box (bcT cls)))
      (packMap cls n) (tupImgT cls imgs himgs).2
      (WFF.mono (((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _) Φ)
      (Proof.lookup List.mem_cons_self)⟩⟩
  exact (congrArg (· ∈ ts.M) (OutLeg.retS_congr hS _ (.nec N)
    (holeRead_tupImgT_packMap himgs n) rfl)).mp hc

namespace BData

variable (B : BData σ) (hS : ModalSys.BStrong = true)

/-- ⭐**Returning possibilities from the far end** (plain leg, necessary shapes): along an arrow
    `s → k`, `Φ(N)` at `k` (read along the arrow), for the object `N` some items make, is
    `◇[d ↦ the items sent home] Φ(d)` at `s`.  The limit of a strong chain has it
    (`bdataS_retIn`). -/
def RetIn : Prop :=
  ∀ {s k : B.W} (h : B.R s k) {i : ℕ} {N : NShape}
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) N.ty) 1) {j : ℕ}
    (hj : B.stg s k i ≤ j) (n : NTerms σ ((B.w k).ctx j).boxIn N),
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
    home `k → s` as `o` exactly when the items sent home are `Ind` to it, componentwise
    (`Model.box_beta`, `boxPush_canon_at`, `interp_subst`; pairs by `ind_pair`). -/
theorem ind_of_nComesBack {s k : B.W} (hR : B.R s k) (r : B.RT k s) {j : ℕ} {N : NShape}
    (n : NTerms σ ((B.w k).ctx j).boxIn N) {o : B.frame.Dom N.flat s}
    (h : B.model.NComesBack N (Model.interp (B.canonEnv k j) n.obj.2) r o) :
    B.Ind (Model.interp (B.canonEnv s (B.stg k s j))
      (n.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
        (ok_arrowS (B.imgOk (B.symm hR) j)) (coh_arrowS (B.imgOk (B.symm hR) j))).2) o := by
  induction N with
  | boxC A cs _ =>
      rcases cs with _ | ⟨_, _⟩
      swap
      · exact PEmpty.elim n
      obtain ⟨_, u⟩ := n
      change B.Ind (B.model.necEval (Model.interp _ (Term.boxtm u)) ⟨s, ⟨r⟩⟩) o at h
      rw [Model.box_beta, boxPush_canon_at k _ ⟨s, ⟨r⟩⟩ (B.symm hR) le_rfl,
        ← Model.interp_subst] at h
      exact h
  | prod R S ihR ihS =>
      obtain ⟨n₁, n₂⟩ := n
      exact ind_pair (ihR n₁ h.1) (ihS n₂ h.2)

/-- ⭐⭐**`ret`, truth ⇒ membership** (plain leg, necessary shapes; strong B, T off).  A true
    `◇[d ↦ t] Φ(d)` has an arrow `s → k` and an object there with `Φ`, coming back `Ind` to `t`.
    The object is a term's denotation, made by some items (`definable_fromDom`,
    `NTerms.exists_obj`); the body at `k` is in the theory by the induction hypothesis
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
  have hR := R_of_RT_strong hS rk
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom N.ty k e
  obtain ⟨n, hn⟩ := NTerms.exists_obj (B.noT_of_strong hS) N g
  have hj₀ : j₀ ≤ max j₀ (B.stg s k i) := le_max_left _ _
  have hj : B.stg s k i ≤ max j₀ (B.stg s k i) := le_max_right _ _
  have he : Model.interp (B.canonEnv k (max j₀ (B.stg s k i)))
      (n.mono ((B.w k).le hj₀).boxIn).obj.2 = e := by
    have hn' : (n.mono ((B.w k).le hj₀).boxIn).obj = ⟨_, (B.w k).liftT hj₀ g⟩ := by
      rw [NTerms.obj_mono, hn]
      rfl
    rw [← interp_lift hg hj₀]
    exact congrArg (fun x => Model.interp (B.canonEnv k (max j₀ (B.stg s k i))) x.2) hn'
  have hsatb : B.model.sat (B.canonEnv k (max j₀ (B.stg s k i)))
      (readArrow ((B.imgOk hR i).mono ((B.w k).le hj))
        (n.mono ((B.w k).le hj₀).boxIn).obj.2 Φ) := by
    rw [sat_readArrow, he, ← boxPush_canon_at s i ⟨k, ⟨rk⟩⟩ hR hj]
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
    (hj : B.stg s k i ≤ j) (n : NTerms σ ((B.w k).ctx j).boxIn N),
    readArrowX ((B.imgOk (B.kdR hk) i).mono ((B.w k).le hj)) hy (((B.w k).le hj).ref (B.hcx hk i))
      n.obj.2 Φ ∈ (B.w k).M j →
      ∃ hiK : i ≤ B.stg k s j,
        (OutLeg.pos y ⟨Y, ((B.w s).le hiK).ref hy⟩ : OutLeg ((B.w s).ctx (B.stg k s j))).retS hS
          (.nec N) (n.subst (arrowIdx (B.img k s)) (arrowS σ _ (B.img k s))
            (ok_arrowS (B.imgOk (B.symm (B.kdR hk)) j))
            (coh_arrowS (B.imgOk (B.symm (B.kdR hk)) j))).2
          (WFF.mono ((((B.w s).le hiK).diaIn y).insert (.bnd 0) _) Φ) ∈ (B.w s).M (B.stg k s j)

/-- ⭐⭐**`ret` along a witness, truth ⇒ membership** (necessary shapes; strong B, T off): as
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
  · exact absurd (R_of_RT_strong hS a₁.1.2.down) hnR
  obtain rfl := B.hxX hk i Y hY
  have hR := B.kdR hk
  obtain ⟨j₀, c₀, g, hg⟩ := B.definable_fromDom N.ty a₁.1.1 e
  obtain ⟨n, hn⟩ := NTerms.exists_obj (B.noT_of_strong hS) N g
  have hj₀ : j₀ ≤ max j₀ (B.stg s a₁.1.1 i) := le_max_left _ _
  have hj : B.stg s a₁.1.1 i ≤ max j₀ (B.stg s a₁.1.1 i) := le_max_right _ _
  have he : Model.interp (B.canonEnv a₁.1.1 (max j₀ (B.stg s a₁.1.1 i)))
      (n.mono ((B.w a₁.1.1).le hj₀).boxIn).obj.2 = e := by
    have hn' : (n.mono ((B.w a₁.1.1).le hj₀).boxIn).obj = ⟨_, (B.w a₁.1.1).liftT hj₀ g⟩ := by
      rw [NTerms.obj_mono, hn]
      rfl
    rw [← interp_lift hg hj₀]
    exact congrArg (fun x => Model.interp (B.canonEnv a₁.1.1 (max j₀ (B.stg s a₁.1.1 i))) x.2) hn'
  have hsatb : B.model.sat (B.canonEnv a₁.1.1 (max j₀ (B.stg s a₁.1.1 i)))
      (readArrowX ((B.imgOk hR i).mono ((B.w a₁.1.1).le hj)) hY
        (((B.w a₁.1.1).le hj).ref (B.hcx hk i))
        (n.mono ((B.w a₁.1.1).le hj₀).boxIn).obj.2 Φ) := by
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
    `k → s` (`lretAt`, reduced by `RetAt.toRetInv`), at a node (`ret_of_inv`). -/
theorem bdataS_retIn (hT : ModalSys.T = false) : (bdataS C hT).RetIn hS := by
  classical
  intro s k h i N Φ j hj n hm
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
    (n.mono (ctxOf_le_of_suffix hJs).boxIn) _
    ⟨hcs, himgt, by
      rw [NTerms.mono_mono, readArrow_sig _ (NTerms.obj_mono _ n)]
      exact hm'⟩
  refine ⟨hiK, (congrArg (· ∈ _) (OutLeg.retS_congr hS .nec (.nec N) ?_ ?_)).mp hr⟩
  · rw [NTerms.subst_mono]
    exact NTerms.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
  · rw [WFF.mono_mono]

/-- ⭐⭐**The limit has returning possibilities along a witness from the far end**: the way home's
    invariant along the witness (`lretAt`, `RetAt.toRetInvX`), at a node (`retx_of_inv`). -/
theorem bdataS_retInX (hT : ModalSys.T = false) : (bdataS C hT).RetInX hS := by
  classical
  intro s k y Y hk i hy N Φ j hj n hm
  have h : LR C.toFairChain s k := lkdR hk
  obtain ⟨cls, imgs, clt, imgt, hJs, hJag, his, hiag, hret⟩ := lretAt C h.symm j i hj
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
  have hinv := RetAt.toRetInvX hsM hret
  obtain ⟨hcs, -, ht, himgt, hxc, hcxc, -⟩ := id hinv
  have hg := grow_stage C.toFairChain k j (m := birth C.toFairChain s.2 +
    lstg C.toFairChain k s j) hkp
  have hm' := hg.sub _ hm
  rw [readArrowX_mono_congr his _ _ himgt (fun r hr => (hiag r hr).symm) _ hxc _ hcxc] at hm'
  obtain ⟨himgs, ht', hx', hr⟩ := retx_of_inv hsM hinv
    (n.mono (ctxOf_le_of_suffix hJs).boxIn) _
    ⟨hcs, himgt, hxc, hcxc, by
      rw [NTerms.mono_mono, readArrowX_sig _ _ _ (NTerms.obj_mono _ n)]
      exact hm'⟩
  refine ⟨hiK, (congrArg (· ∈ _) (OutLeg.retS_congr hS _ (.nec N) ?_ ?_)).mp hr⟩
  · rw [NTerms.subst_mono]
    exact NTerms.subst_congr _ _ _ _ _ _ (sim_arrowS hJag) _
  · rw [WFF.mono_mono]

end Limit

end BArrow

end V12M
