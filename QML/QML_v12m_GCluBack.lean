import QML.QML_v12m_GCluModel
import QML.QML_v12m_RetGPack

/-!
# QML v12m — 5 on the growing tree: what comes back, at the far world

Strong B on the cluster (`docs/v12-modal-extensions.md` §11, "Strong B on S5").  An atom's round
trip at an arrow is proved here, with no induction hypothesis: the home term of the value at the
arrow's end is that value's root preimage kept down the world's own path, and at the far world the
tie `Proof.back_of_tie` asks for is between two names of one term.

* `WFF.boxHole`, `WFF.holeAt_boxHole`: `□` of a hole formula is a hole formula.
* `pTrW_holeAt`: translating along a path a hole formula's reading is reading it at the
  translated term.
* `dia_mem_of_path`: what a far world has of a formula's preimage is possible here.
* `preTB_at`, `preTB_pTrK`, `pTrK_mono`, `tr_kept`, `preTB_compBd`: preimages at any later stage;
  a kept root term's preimage is itself; a kept carrier translates to a kept carrier.
* ⭐`tie_nec`: the tie's possibility, from any arrow.
* ⭐`cRet_of_mem_nec`: a `Back` atom's own data make the round trip, so its model `Ret` holds.
* `pTrXKW_holeAt`, `grealW`, `dia_mem_of_real`: the same along a witness, whose arrows are all
  realised under T; ⭐`tie_pos`: the tie's possibility from an arrow of the witness's extent;
  ⭐`cRet_of_mem_pos`: so along a witness too.
-/

namespace V12M

variable [ModalSys]

/-- `□ψ` on a hole of type `□X`: necessarily, `ψ` of the object. -/
def WFF.boxHole {σ : Signature} {X : VarType} (ψ : WFF σ (Ctx.empty.insert (.bnd 0) X) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeBox X)) 1 :=
  WFF.box (WFF.holeAt (Ctx.slotsFrom_empty.insert (.VTypeBox X)).boxIn
    (Term.eta (VarSymb.root (.bnd 0)).inner X
      (Ctx.ref_inner (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeBox X)))) ψ)

theorem WFF.holeAt_boxHole {σ : Signature} {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {X : VarType}
    {a : Ann X} (t : Term σ Γ.boxIn X a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) X) 1) :
    WFF.holeAt hs (Term.boxtm t) (WFF.boxHole ψ) = WFF.box (WFF.holeAt hs.boxIn t ψ) := by
  have hat := Subst.at_single_root (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.boxtm t))
  change WFF.box _ = _
  exact congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _
    (Term.subst_eta_tm _ _ _ _ _ _ t (Subst.box_at_inner_boxtm _ hat)) ψ))

/-- Realising a hole formula's reading is reading it at the realised term. -/
theorem WFF.realiseAtA_holeAt {σ : Signature} {Γ : Ctx} [Γ.Presented] (hT : ModalSys.T = true)
    (x : VarSymb) {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A)) {a₀ : Ann A}
    (t₀ : Term σ Γ A a₀) {T : VarType} {b : Ann T} (u : Term σ (Γ.diaIn x) T b)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) T) 1) :
    WFF.realiseAtA hT x hxA t₀ (WFF.holeAt Ctx.NoSlots.slots u ψ) =
      WFF.holeAt Ctx.NoSlots.slots (Term.realiseAtA hT x hxA t₀ u) ψ := by
  unfold WFF.realiseAtA WFF.hereRead WFF.diaAbsA
  rw [WFF.subst_holeAt, WFF.collapse_holeAt _ _ ((Ctx.NoSlots.slots (Γ := Γ)).insert A),
    WFF.collapse_hole]
  exact WFF.subst_holeAt _ _ _ _ _ _ ψ

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Hole formulas along a path -/

variable (hM₀ : Theory.IsMCS M₀)

/-- ⭐Translating a hole formula's reading along a path is reading it at the translated term. -/
theorem pTrW_holeAt : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) {X : VarType} {a : Ann X} (u : Term σ ((ctxOf (glat s i)).kView none) X a)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) X) 1),
    pTrW hM₀ s t P h hP i (WFF.holeAt Ctx.NoSlots.slots u ψ) =
      WFF.holeAt Ctx.NoSlots.slots (pTr hM₀ s t P h hP i u).2 ψ
  | _, _, [], _, _, _, _, _, u, ψ => by
      change WFF.mono _ (WFF.collapse _ _ (WFF.holeAt _ u ψ)) =
        WFF.holeAt _ (Term.mono _ (Term.collapse _ u)) ψ
      rw [WFF.collapse_holeAt _ _ Ctx.NoSlots.slots, WFF.collapse_hole,
        WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots]
  | _, _, [_], _, _, _, _, _, u, ψ => WFF.subst_holeAt _ _ _ _ _ u ψ
  | s, t, c :: c' :: P, h, _, i, _, _, u, ψ => by
      change pTrW hM₀ _ t (c' :: P) h _ _
        (WFF.subst _ _ _ _ _ _ (WFF.shift _ _ (WFF.holeAt _ u ψ))) = _
      rw [WFF.shift_holeAt _ _ Ctx.NoSlots.slots, WFF.shift_hole, WFF.subst_holeAt]
      exact pTrW_holeAt (stepW s c (born_step h)) t (c' :: P) h _ _ _ ψ

theorem pTrW_neg : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) (φ : WFF σ ((ctxOf (glat s i)).kView none) 0),
    pTrW hM₀ s t P h hP i φ.neg = (pTrW hM₀ s t P h hP i φ).neg
  | _, _, [], _, _, _, _ => rfl
  | _, _, [_], _, _, _, _ => rfl
  | _, t, _ :: c' :: P, h, _, _, _ => pTrW_neg _ t (c' :: P) h _ _ _

/-- ⭐**What a far world has of a formula's preimage is possible here.**  Otherwise its negation is
    necessary here, so at the root, whose path carries it to the far world (`box_pathO_iff`,
    `box_mem_path`). -/
theorem dia_mem_of_path (hX : CluFlags) (s : GW hF M₀) (i : ℕ) (v : GW hF M₀) (P : List ℕ)
    (h : v.1 = nodeOf (groot hF M₀).1 P) (hP : PathOk P) {R : ℕ} (hR : rstg s i ≤ R)
    (χ : WFF σ (ctxOf (glat s i)).boxIn 0)
    (hmem : pTrW hM₀ (groot hF M₀) v P h hP R
        (WFF.mono (gle hM₀ (groot hF M₀) hR).boxIn (preWP (rpre hX hM₀ s i) χ)) ∈
      (gw hM₀ v).M (pstg (groot hF M₀) v P h R)) :
    (WFF.box χ.neg).neg ∈ (gw hM₀ s).M i := by
  refine ((gw hM₀ s).mcs i).neg_mem_iff.mpr fun hn => ?_
  have h₁ := (box_pathO_iff hX.five hX.fourS hX.fourSW hM₀ (rpath s) (groot hF M₀) s
    (rpath_eq s) i χ.neg).mpr hn
  have h₂ := (gMs_mono_iff hM₀ (groot hF M₀) hR _).mp h₁
  have h₃ := box_mem_path hM₀ (groot hF M₀) v P h hP R _ h₂
  have e : pTrW hM₀ (groot hF M₀) v P h hP R
      (WFF.mono (gle hM₀ (groot hF M₀) hR).boxIn (preWP (rpre hX hM₀ s i) χ.neg)) =
      (pTrW hM₀ (groot hF M₀) v P h hP R
        (WFF.mono (gle hM₀ (groot hF M₀) hR).boxIn (preWP (rpre hX hM₀ s i) χ))).neg :=
    pTrW_neg hM₀ _ _ _ _ _ _ _
  rw [e] at h₃
  exact ((gw hM₀ v).mcs _).neg_mem_iff.mp h₃ hmem

/-! ## Terms along a path -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A pair under `□` goes through a chain componentwise. -/
theorem GTr.app_boxtm_pair {Γ Δ : Ctx} (C : GTr σ Γ Δ) {A B : VarType} {a a' : Ann A}
    {c c' : Ann B} {x : Term σ Γ.boxIn A a} {y : Term σ Γ.boxIn B c} {x' : Term σ Δ.boxIn A a'}
    {y' : Term σ Δ.boxIn B c'} (hx : C.app (.boxtm x) = ⟨_, .boxtm x'⟩)
    (hy : C.app (.boxtm y) = ⟨_, .boxtm y'⟩) :
    C.app (.boxtm (.pair x y)) = ⟨_, .boxtm (.pair x' y')⟩ := by
  rw [GTr.app_boxtm] at hx hy ⊢
  rw [GTr.app_pair]
  exact sig_boxtm (sig_pair (sig_boxtm_inj hx) (sig_boxtm_inj hy))

/-- A pair under `□` translates componentwise. -/
theorem pTr_boxtm_pair (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) {A C : VarType} {a a' : Ann A} {c c' : Ann C}
    {x : Term σ ((ctxOf (glat s i)).kView none).boxIn A a}
    {y : Term σ ((ctxOf (glat s i)).kView none).boxIn C c}
    {x' : Term σ (ctxOf (glat t (pstg s t P h i))).boxIn A a'}
    {y' : Term σ (ctxOf (glat t (pstg s t P h i))).boxIn C c'}
    (hx : pTr hM₀ s t P h hP i (.boxtm x) = ⟨_, .boxtm x'⟩)
    (hy : pTr hM₀ s t P h hP i (.boxtm y) = ⟨_, .boxtm y'⟩) :
    pTr hM₀ s t P h hP i (.boxtm (.pair x y)) = ⟨_, .boxtm (.pair x' y')⟩ := by
  rw [pTr_app] at hx hy ⊢
  exact GTr.app_boxtm_pair _ hx hy

/-- A world's preimage of a term, read at any later root stage, is the renaming there. -/
theorem preTB_at (hX : CluFlags) (s : GW hF M₀) {i j R : ℕ} (hR : rstg s j ≤ R)
    (e : (ctxOf (glat s i)).Le (ctxOf (glat s j))) {A : VarType} {a : Ann A}
    (u : Term σ (ctxOf (glat s i)).boxIn A a) :
    (⟨_, Term.mono (gle hM₀ (groot hF M₀) hR).boxIn (preTB hX hM₀ s j (Term.mono e.boxIn u)).2⟩ :
        Σ c, Term σ (ctxOf (glat (groot hF M₀) R)).boxIn A c) =
      ⟨_, Term.subst (eIdx (ofRen (preI (rorig s))))
        (eS σ (ctxOf (glat (groot hF M₀) R)).boxIn (ofRen (preI (rorig s))))
        (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI
          fun z T hz hk => rpre_le hX hM₀ s hR z T (e.ref hz) hk)))
        (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI
          fun z T hz hk => rpre_le hX hM₀ s hR z T (e.ref hz) hk))) u⟩ := by
  change (⟨_, Term.mono _ (Term.subst _ _ _ _ (Term.mono e.boxIn u))⟩ : Σ c, Term σ _ _ c) = _
  rw [Term.mono_subst]
  refine (Term.subst_congr (ι' := eIdx (ofRen (preI (rorig s)))) _ _ _
    (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI (rpre_le hX hM₀ s hR))))
    _ (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI (rpre_le hX hM₀ s hR))))
    (sim_eS_mono (l := glat s j) (k := none) _
      (entOk_ofRen (itemOk_preI (rpre hX hM₀ s j)))) _).trans ?_
  rw [Term.subst_mono]

/-- A term's preimage does not depend on the stage it is taken at. -/
theorem preTB_lift (hX : CluFlags) (s : GW hF M₀) {i I R : ℕ} (hI : i ≤ I)
    (h₁ : rstg s i ≤ R) (h₂ : rstg s I ≤ R) {A : VarType} {a : Ann A}
    (u : Term σ (ctxOf (glat s i)).boxIn A a) :
    (⟨_, Term.mono (gle hM₀ (groot hF M₀) h₂).boxIn
        (preTB hX hM₀ s I (Term.mono (gle hM₀ s hI).boxIn u)).2⟩ :
        Σ c, Term σ (ctxOf (glat (groot hF M₀) R)).boxIn A c) =
      ⟨_, Term.mono (gle hM₀ (groot hF M₀) h₁).boxIn (preTB hX hM₀ s i u).2⟩ := by
  have e := preTB_at hM₀ hX s h₁ (Ctx.Le.refl _) u
  rw [Term.mono_refl] at e
  exact (preTB_at hM₀ hX s h₂ (gle hM₀ s hI) u).trans e.symm

/-- A possible term's preimage does not depend on the stage it is taken at. -/
theorem preTD_stage (hX : CluFlags) (s : GW hF M₀) {i I R : ℕ} (hI : i ≤ I)
    (h₁ : rstg s i ≤ R) (h₂ : rstg s I ≤ R) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (u : Term σ ((ctxOf (glat s i)).diaIn x) A a) :
    (⟨_, Term.mono ((gle hM₀ (groot hF M₀) h₂).kView (some (rorig s x)))
        (preTD hX hM₀ s I (hx.imp fun _ e => (gle hM₀ s hI).ref e)
          (Term.mono ((gle hM₀ s hI).diaIn x) u)).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) R)).kView (some (rorig s x))) A c) =
      ⟨_, Term.mono ((gle hM₀ (groot hF M₀) h₁).kView (some (rorig s x)))
        (preTD hX hM₀ s i hx u).2⟩ := by
  have e := preTD_lift hX hM₀ s (Ctx.Le.refl _) (Ctx.Le.refl _) h₁ h₁ hx u
  have e' := preTD_lift hX hM₀ s (Ctx.Le.refl _) (gle hM₀ s hI) h₁ h₂ hx u
  rw [Term.mono_refl] at e
  exact e'.trans e.symm

/-- ⭐**A root term kept down a world's path has the term as its preimage** (R4): the renaming
    is `porig ∘ pnm`, which is weakening (`round_trip`). -/
theorem preTB_pTrK (hX : CluFlags) (s : GW hF M₀) {I R R₀ : ℕ} (hR : rstg s I ≤ R) (hR₀ : R₀ ≤ R)
    (e : (ctxOf (glat s (pstg (groot hF M₀) s (rpath s) (rpath_eq s) R₀))).Le
      (ctxOf (glat s I))) {A : VarType} {a : Ann A}
    (r : Term σ (ctxOf (glat (groot hF M₀) R₀)).boxIn A a) :
    (⟨_, Term.mono (gle hM₀ (groot hF M₀) hR).boxIn (preTB hX hM₀ s I
        (Term.mono e.boxIn (pTrK hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) R₀ r).2)).2⟩ :
        Σ c, Term σ (ctxOf (glat (groot hF M₀) R)).boxIn A c) =
      ⟨_, Term.mono (gle hM₀ (groot hF M₀) hR₀).boxIn r⟩ := by
  have hrt : ∀ z T, (ctxOf (glat (groot hF M₀) R₀)).ref z = some T → T.keepable = true →
      (ctxOf (glat (groot hF M₀) R)).ref ((rorig s ∘ rnm s) z) = some T := fun z T hz hk =>
    rpre_le hX hM₀ s hR _ T (e.ref (pnm_ok hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) R₀ z T
      hz hk)) hk
  refine (preTB_at hM₀ hX s hR e _).trans ?_
  refine (sig_subst_cong _ _ _ (tr_pathK hX hM₀ _ _ _ _ _ r)).trans ?_
  refine (Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
    fun u st _ hst _ => ?_) r).trans (round_trip hX.five hM₀ (rpath s) (groot hF M₀) s
      (rpath_eq s) R₀ hrt hR₀ r)
  obtain ⟨u', e'⟩ := preI_step (rnm s) u st
  exact ⟨u', st, e', hst, by rw [← e', preI_comp]⟩

/-- Keeping a later stage along a path is weakening the kept translation. -/
theorem pTrK_mono (hX : CluFlags) (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P)
    {i i' : ℕ} (hii : i ≤ i') {A : VarType} {a : Ann A}
    (b : Term σ (ctxOf (glat s i)).boxIn A a) :
    (⟨_, Term.mono (gle hM₀ t (pstg_monotone hM₀ s t P h hii)).boxIn (pTrK hM₀ s t P h i b).2⟩ :
        Σ c, Term σ (ctxOf (glat t (pstg s t P h i'))).boxIn A c) =
      pTrK hM₀ s t P h i' (Term.mono (gle hM₀ s hii).boxIn b) := by
  rw [tr_pathK hX hM₀, tr_pathK hX hM₀]
  change (⟨_, Term.mono _ (Term.subst _ _ _ _ b)⟩ : Σ c, Term σ _ _ c) =
    ⟨_, Term.subst _ _ _ _ (Term.mono _ b)⟩
  rw [Term.mono_subst, Term.subst_mono]
  exact Term.subst_congr _ _ _ _ _ _ (sim_eS_mono (l := glat s i) (k := none) _
    (entOk_ofRen (itemOk_preI (pnm_ok hX hM₀ P s t h i)))) b

/-- What a world's term is, kept from its root preimage, at a later root stage. -/
theorem pTrK_home (hX : CluFlags) (v : GW hF M₀) (h : v.1 = nodeOf (groot hF M₀).1 (rpath v))
    {K R : ℕ} (hR₀ : rstg v K ≤ R) (hKL : K ≤ pstg (groot hF M₀) v (rpath v) h R) {A : VarType}
    {g₀ : Ann A} (g : Term σ (ctxOf (glat v K)).boxIn A g₀) :
    (⟨_, (pTrK hM₀ (groot hF M₀) v (rpath v) h R
        (Term.mono (gle hM₀ (groot hF M₀) hR₀).boxIn (preTB hX hM₀ v K g).2)).2⟩ :
        Σ c, Term σ (ctxOf (glat v (pstg (groot hF M₀) v (rpath v) h R))).boxIn A c) =
      ⟨_, Term.mono (gle hM₀ v hKL).boxIn g⟩ := by
  refine (pTrK_mono hM₀ hX (rpath v) (groot hF M₀) v h hR₀ _).symm.trans ?_
  refine (sig_mono _ (pTrK_pre hX hM₀ v K g)).trans ?_
  exact congrArg (Sigma.mk _) (Term.mono_mono _ _ _)

/-- A world's term kept down another's path denotes what it does. -/
theorem cden_home (hX : CluFlags) (s v : GW hF M₀) {K I : ℕ}
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I) {A : VarType} {g₀ : Ann A}
    (g : Term σ (ctxOf (glat v K)).boxIn A g₀) :
    cden hM₀ hX s I (Ctx.Le.refl _) (.boxtm (Term.mono (gle hM₀ s hJI).boxIn
        (pTrK hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K)
          (preTB hX hM₀ v K g).2).2)) =
      cden hM₀ hX v K (Ctx.Le.refl _) (.boxtm g) := by
  have e₁ := (cden_mono (hM₀ := hM₀) hX (gle hM₀ s hJI) (.boxtm (pTrK hM₀ (groot hF M₀) s (rpath s)
    (rpath_eq s) (rstg v K) (preTB hX hM₀ v K g).2).2) s I (Ctx.Le.refl _)).trans
    (cden_congr (hM₀ := hM₀) hX _ s _ (pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K)) _
      (Ctx.Le.refl _))
  have e₂ := cden_sigma (hM₀ := hM₀) hX (s := s)
    (i := pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K)) (Ctx.Le.refl _)
    (sig_boxtm (tr_pathK hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg v K)
      (preTB hX hM₀ v K g).2))
  have e₃ := cden_named_box hX hM₀ s (rstg v K)
    (pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K))
    (pnm_ok hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg v K))
    (preTB hX hM₀ v K g).2
  have e₄ := cden_box_eq (hM₀ := hM₀) hX v K (Ctx.Le.refl _) g
  rw [Term.mono_refl] at e₄
  exact e₁.trans (e₂.trans (e₃.trans e₄.symm))

/-- ⭐**A kept carrier translates to a kept carrier**: `tr_path` with the kept term's own kept form,
    the renaming commuting with 4's shift (`shiftCorr_preI`). -/
theorem tr_kept (hX : CluFlags) (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P)
    (hP : PathOk P) (i : ℕ) {A : VarType} {a : Ann A}
    (r : Term σ (ctxOf (glat s i)).boxIn A a) :
    pTr hM₀ s t P h hP i (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) r)))) =
      ⟨_, .boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (pTrK hM₀ s t P h i r).2))⟩ := by
  rw [tr_path hX hM₀, tr_pathK hX hM₀]
  exact sig_boxtm (sig_boxtm (Term.shift_subst (Ctx.shifts_boxIn_boxIn hF _)
    (Ctx.shifts_boxIn_boxIn hF _) _ _ _ _ _ _ (shiftCorr_preI (hF := hF) _ (ok_eS_kView (k := none)
      (entOk_ofRen (itemOk_preI (pnm_ok hX hM₀ P s t h i))))) r).symm)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Weakening a kept carrier keeps the weakening. -/
theorem mono_kept {Γ Γ' : Ctx} (h : Γ.Le Γ') {C : VarType} {k₀ : Ann C}
    (k : Term σ Γ.boxIn C k₀) :
    (⟨_, Term.mono h.boxIn (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ)
        (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) k))))⟩ :
        Σ c, Term σ Γ'.boxIn (.VTypeBox (.VTypeBox C)) c) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ') (.boxtm (Term.shift
        (Ctx.shifts_boxIn_boxIn hF Γ') (Term.mono h.boxIn k))))⟩ := by
  refine sig_boxtm ?_
  rw [Term.shift_mono (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF _) h.boxIn
    h.boxIn.boxIn]
  exact (congrArg (Sigma.mk _) (Term.shift_mono (Ctx.shifts_boxIn_boxIn hF _)
    (Ctx.shifts_boxIn_boxIn hF _) h.boxIn h.boxIn.boxIn _)).symm

/-- A kept term keeps along a path as a kept term. -/
theorem tr_keptK₁ (hX : CluFlags) (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    {A : VarType} {a : Ann A} (r : Term σ (ctxOf (glat s i)).boxIn A a) :
    pTrK hM₀ s t P h i (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) r)) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (pTrK hM₀ s t P h i r).2)⟩ := by
  rw [tr_pathK hX hM₀, tr_pathK hX hM₀]
  exact sig_boxtm (Term.shift_subst (Ctx.shifts_boxIn_boxIn hF _)
    (Ctx.shifts_boxIn_boxIn hF _) _ _ _ _ _ _ (shiftCorr_preI (hF := hF) _ (ok_eS_kView (k := none)
      (entOk_ofRen (itemOk_preI (pnm_ok hX hM₀ P s t h i))))) r).symm

/-- A kept carrier keeps along a path as a kept carrier. -/
theorem tr_keptK (hX : CluFlags) (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    {A : VarType} {a : Ann A} (r : Term σ (ctxOf (glat s i)).boxIn A a) :
    pTrK hM₀ s t P h i (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) r)))) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (.boxtm (Term.shift
        (Ctx.shifts_boxIn_boxIn hF _) (pTrK hM₀ s t P h i r).2)))⟩ :=
  (tr_keptK₁ hM₀ hX P s t h i _).trans
    (sig_boxtm (sig_shift_cong _ (tr_keptK₁ hM₀ hX P s t h i r)))

/-- The preimage of a kept carrier is the kept carrier of the preimage. -/
theorem preTB_compBd (hX : CluFlags) (s : GW hF M₀) (I : ℕ) {R : ℕ} (hR : rstg s I ≤ R)
    {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat s I)).boxIn A a) :
    (⟨_, Term.mono (gle hM₀ (groot hF M₀) hR).boxIn
        (preTB hX hM₀ s I (.boxtm (compBd hF .nec b).2)).2⟩ :
        Σ c, Term σ (ctxOf (glat (groot hF M₀) R)).boxIn (.VTypeBox (.VTypeBox A)) c) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (.boxtm (Term.shift
        (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ (groot hF M₀) hR).boxIn (preTB hX hM₀ s I b).2))))⟩ := by
  have e₁ : (⟨_, (compBd hF .nec b).2⟩ : Σ c, Term σ _ (.VTypeBox A) c) =
      ⟨_, Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))⟩ :=
    congrArg (Sigma.mk _) (Term.mono_refl _ _)
  have e₂ := preTB_sigma hX hM₀ s I (sig_boxtm e₁)
  have e₃ := e₂.trans ((preTB_shift hX hM₀ s I
    (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))).trans
    (sig_boxtm (sig_shift_cong _ (preTB_shift hX hM₀ s I b))))
  refine (sig_mono (gle hM₀ (groot hF M₀) hR).boxIn e₃).trans (sig_boxtm ?_)
  rw [Term.shift_mono (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF _)
    (gle hM₀ (groot hF M₀) hR).boxIn (gle hM₀ (groot hF M₀) hR).boxIn.boxIn]
  exact (congrArg (Sigma.mk _) (Term.shift_mono (Ctx.shifts_boxIn_boxIn hF _)
    (Ctx.shifts_boxIn_boxIn hF _) (gle hM₀ (groot hF M₀) hR).boxIn
    (gle hM₀ (groot hF M₀) hR).boxIn.boxIn _)).symm

/-- The preimage of a kept carrier, written out. -/
theorem preTB_kept (hX : CluFlags) (s : GW hF M₀) (I : ℕ) {R : ℕ} (hR : rstg s I ≤ R)
    {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat s I)).boxIn A a) :
    (⟨_, Term.mono (gle hM₀ (groot hF M₀) hR).boxIn
        (preTB hX hM₀ s I (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
          (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))))).2⟩ :
        Σ c, Term σ (ctxOf (glat (groot hF M₀) R)).boxIn (.VTypeBox (.VTypeBox A)) c) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (.boxtm (Term.shift
        (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ (groot hF M₀) hR).boxIn (preTB hX hM₀ s I b).2))))⟩ := by
  have e₁ : (⟨_, (compBd hF .nec b).2⟩ : Σ c, Term σ _ (.VTypeBox A) c) =
      ⟨_, Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))⟩ :=
    congrArg (Sigma.mk _) (Term.mono_refl _ _)
  exact (sig_mono _ (preTB_sigma hX hM₀ s I (sig_boxtm e₁))).symm.trans
    (preTB_compBd hM₀ hX s I hR b)

/-! ## The tie -/

/-- ⭐⭐**The tie, from any arrow** (strong B, T + 4): `g` the body of the carrier's value at the
    far world `v`.  Its root preimage kept down `s`'s path is a home term `b`, and at `v` the kept
    carrier of `b` and `g` are one term, so the tie there is `Proof.back_shift`.  Home by
    `dia_mem_of_path`.  `b` denotes what `g` does (`cden_named_box`, `cden_box_eq`). -/
theorem tie_nec (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (s : GW hF M₀) (i : ℕ) (v : GW hF M₀) (P : List ℕ) (h : v.1 = nodeOf (groot hF M₀).1 P)
    (hP : PathOk P) {A : VarType} {a₀ : Ann A} (bd : Term σ (ctxOf (glat s i)).boxIn.boxIn A a₀)
    {g₀ : Ann A} (g : Term σ (ctxOf (glat v (pstg (groot hF M₀) v P h (rstg s i)))).boxIn A g₀)
    (hg : pTr hM₀ (groot hF M₀) v P h hP (rstg s i) (preTB hX hM₀ s i (.boxtm bd)).2 =
      ⟨_, .boxtm g⟩) :
    ∃ (I : ℕ) (hI : i ≤ I) (b₀ : Ann A) (b : Term σ (ctxOf (glat s I)).boxIn A b₀),
      (OutLeg.nec : OutLeg (ctxOf (glat s I))).dia (WFF.box (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair (Term.mono (gle hM₀ s hI).boxIn.boxIn bd) (compBd hF .nec b).2)
        (WFF.backDup hS hF A))) ∈ (gw hM₀ s).M I ∧
      cden hM₀ hX s I (Ctx.Le.refl _) (.boxtm b) =
        cden hM₀ hX v _ (Ctx.Le.refl _) (.boxtm g) := by
  obtain rfl : P = rpath v := nodeOf_inj (h.symm.trans (rpath_eq v))
  let K := pstg (groot hF M₀) v (rpath v) h (rstg s i)
  let r₀ := (preTB hX hM₀ v K g).2
  let J := pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K)
  let b₁ := (pTrK hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) r₀).2
  let I := max i J
  let R := max (rstg s I) (max (rstg v K) (rstg s i))
  have hiI : i ≤ I := le_max_left _ _
  have hJI : J ≤ I := le_max_right _ _
  have hRI : rstg s I ≤ R := le_max_left _ _
  have hR₀ : rstg v K ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRi : rstg s i ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨I, hiI, _, Term.mono (gle hM₀ s hJI).boxIn b₁, ?_, ?_⟩
  · let g' := Term.mono (gle hM₀ v (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRi)).boxIn g
    have hx : pTr hM₀ (groot hF M₀) v (rpath v) h hP R (Term.mono (gle hM₀ (groot hF M₀) hRI).boxIn
        (preTB hX hM₀ s I (.boxtm (Term.mono (gle hM₀ s hiI).boxIn.boxIn bd))).2) =
        ⟨_, .boxtm g'⟩ := by
      refine (pTr_sigma hM₀ _ _ _ _ hP _
        (preTB_lift hM₀ hX s hiI hRi hRI (.boxtm bd))).trans ?_
      refine (pTr_mono hM₀ _ _ _ h hP hRi _).symm.trans ?_
      have key : ∀ p : Σ c, Term σ (ctxOf (glat v K)) (.VTypeBox A) c, p = ⟨_, .boxtm g⟩ →
          (⟨_, Term.mono (gle hM₀ v (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRi)) p.2⟩ :
            Σ c, Term σ _ (.VTypeBox A) c) = ⟨_, .boxtm g'⟩ := by
        rintro _ rfl
        rfl
      exact key _ hg
    have hpk := pTrK_home hM₀ hX v h hR₀ (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRi) g
    have hy : pTr hM₀ (groot hF M₀) v (rpath v) h hP R (Term.mono (gle hM₀ (groot hF M₀) hRI).boxIn
        (preTB hX hM₀ s I (.boxtm (compBd hF .nec (Term.mono (gle hM₀ s hJI).boxIn b₁)).2)).2) =
        ⟨_, .boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) g'))⟩ := by
      refine (pTr_sigma hM₀ _ _ _ _ hP _ ((preTB_compBd hM₀ hX s I hRI _).trans (sig_boxtm
        (sig_shift_cong _ (sig_boxtm (sig_shift_cong _
          (preTB_pTrK hM₀ hX s hRI hR₀ (gle hM₀ s hJI) r₀))))))).trans ?_
      exact (tr_kept hM₀ hX (rpath v) _ _ h hP R _).trans
        (sig_boxtm (sig_boxtm (sig_shift_cong _ hpk)))
    change (WFF.box (WFF.box (WFF.holeAt Ctx.NoSlots.slots _ _)).neg).neg ∈ _
    rw [← WFF.holeAt_boxHole Ctx.NoSlots.slots]
    refine dia_mem_of_path hM₀ hX s I v (rpath v) h hP hRI _ ?_
    have e₁ : ∀ {X : VarType} {x : Ann X} (T : Term σ (ctxOf (glat s I)).boxIn X x)
        (Ψ : WFF σ (Ctx.empty.insert (.bnd 0) X) 1),
        preWP (rpre hX hM₀ s I) (WFF.holeAt Ctx.NoSlots.slots T Ψ) =
          WFF.holeAt Ctx.NoSlots.slots (preTB hX hM₀ s I T).2 Ψ :=
      fun T Ψ => WFF.subst_holeAt _ _ _ _ _ T Ψ
    have hpair := pTr_boxtm_pair hM₀ _ _ _ h hP R hx hy
    rw [e₁, WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots, pTrW_holeAt hM₀]
    refine (congrArg (· ∈ _) (WFF.holeAt_congr Ctx.NoSlots.slots hpair _)).mpr ?_
    rw [WFF.holeAt_boxHole, WFF.holeAt_backDup]
    exact (gw hM₀ v).mem_of_provable (Δ := []) (fun _ hψ => by cases hψ)
      ⟨Proof.K_box (Δ := []) (Proof.back_shift hS hT hF g')⟩
  · exact cden_home hM₀ hX s v hJI g

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A term of a `□` type is a `boxtm`. -/
theorem exists_boxtm {Γ : Ctx} {A : VarType} (p : Σ c, Term σ Γ (.VTypeBox A) c) :
    ∃ (g₀ : Ann A) (g : Term σ Γ.boxIn A g₀), p = ⟨_, .boxtm g⟩ := by
  obtain ⟨_, t⟩ := p
  cases t with
  | boxtm g => exact ⟨_, g, rfl⟩

/-- ⭐⭐**A `Back` atom comes back in the model** (`.nec`).  At each arrow the tie gives a home
    term `k` denoting what the carrier's value does (`tie_nec`), so `Back (k.dup) t` holds
    (`Proof.back_of_tie`), and with it `k` read here is related to `t` (`BWorld.back_here_rel`).
    No induction hypothesis: the truth lemma's `Back` case is this one way round. -/
theorem cRet_of_mem_nec (hX : CluFlags) (hS : ModalSys.BStrong = true) (s : GW hF M₀) (i : ℕ)
    {A : VarType} {a₀ : Ann A} (bd : Term σ (ctxOf (glat s i)).boxIn.boxIn A a₀) {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a)
    (hmem : WFF.back hS .nec (.boxtm (.boxtm bd)) t ∈ (gw hM₀ s).M i) :
    cRet hM₀ hX (cTag hM₀ hX .nec (ctoDom hM₀ hX _ s
        (cden hM₀ hX s i (Ctx.Le.refl _) (.boxtm (.boxtm bd))) (cdefinable_den hX _ _)))
      (cData hM₀ hX .nec (ctoDom hM₀ hX _ s
        (cden hM₀ hX s i (Ctx.Le.refl _) (.boxtm (.boxtm bd))) (cdefinable_den hX _ _))).1
      (cData hM₀ hX .nec (ctoDom hM₀ hX _ s
        (cden hM₀ hX s i (Ctx.Le.refl _) (.boxtm (.boxtm bd))) (cdefinable_den hX _ _))).2
      (ctoDom hM₀ hX A s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _)) := by
  have hT := hX.bT (hX.bS hS)
  have hR : GR (groot hF M₀) s := (carrows hF M₀).refl hT s
  refine ⟨⟨⟨⟨s, ⟨hR⟩⟩, trivial⟩⟩, fun b => ⟨hR, fun _ => ?_,
    fun hnT => absurd (hT.symm.trans hnT) (by decide)⟩,
    .inr ⟨hS, i, .nec, _, _, _, _, hmem, rfl, rfl, rfl⟩⟩
  obtain ⟨g₀, g, hg⟩ := exists_boxtm (pTr hM₀ (groot hF M₀) b.1.1 (pathOf b.1.2.down)
    (pathOf_eq b.1.2.down) (pathOf_ok b.1.2.down) (rstg s i) (preTB hX hM₀ s i (.boxtm bd)).2)
  obtain ⟨I, hI, b₀, k, hdia, hden⟩ := tie_nec hM₀ hX hS hT s i b.1.1 _ _ _ bd g hg
  have hatom : WFF.back hS .nec (.boxtm (.boxtm (Term.mono (gle hM₀ s hI).boxIn.boxIn bd)))
      (Term.mono (gle hM₀ s hI) t) ∈ (gw hM₀ s).M I := (gw hM₀ s).sub hI _ hmem
  have hback : WFF.back hS .nec (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) k)))
      (Term.mono (gle hM₀ s hI) t) ∈ (gw hM₀ s).M I :=
    BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hatom
      · rw [List.mem_singleton.mp hψ]
        exact hdia)
      ⟨Proof.back_of_tie hS hT hF .nec k _ _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  refine ⟨⟨I, _, Term.collapse (Ctx.collapses_boxIn_self hT _) (Term.collapse
      (Ctx.collapses_boxIn_self hT _) (Term.shift (Ctx.shifts_boxIn_boxIn hF _) k))⟩,
    ⟨I, _, Term.mono (gle hM₀ s hI) t⟩, ?_, ?_, BWorld.back_here_rel (gw hM₀ s) hS hT _ _ hback⟩
  · change _ = cfromDom hM₀ hX A s (ctoDom hM₀ hX A s _ _)
    rw [cfromDom_toDom]
    have e₁ := cden_sigma (hM₀ := hM₀) hX (s := s) (i := I) (Ctx.Le.refl _)
      (sig_collapse_cong (Ctx.collapses_boxIn_self hT _) (Term.collapse_shift_boxIn hT hF k))
    have e₂ : cden hM₀ hX b.1.1 _ (Ctx.Le.refl _) (.boxtm g) =
        cden hM₀ hX s i (Ctx.Le.refl _) (.boxtm (.boxtm bd)) b.1 := by
      change _ = cden hM₀ hX b.1.1 _ (Ctx.Le.refl _) (pTr hM₀ (groot hF M₀) b.1.1
        (pathOf b.1.2.down) (pathOf_eq b.1.2.down) (pathOf_ok b.1.2.down) (rstg s i)
        (preTB hX hM₀ s i (Term.mono (Ctx.Le.refl _).boxIn (.boxtm bd))).2).2
      rw [Term.mono_refl]
      exact (cden_sigma hX _ hg).symm
    exact e₁.trans ((cden_boxtm_own hX hT s I k hR).symm.trans
      ((congrFun hden ⟨s, ⟨hR⟩⟩).trans (congrFun e₂ ⟨s, ⟨hR⟩⟩)))
  · exact (cden_lift hX hI t).trans (cfromDom_toDom hM₀ hX A s _ _).symm

/-! ## Along a witness -/

/-- Translating a hole formula's reading into a kept witness's view is reading it at the
    translated term. -/
theorem pTrXKW_holeAt : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {T : VarType}
    {a : Ann T} (u : Term σ ((ctxOf (glat s i)).kView (some x)) T a)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) T) 1),
    pTrXKW hM₀ s t P h i x hx (WFF.holeAt Ctx.NoSlots.slots u ψ) =
      WFF.holeAt Ctx.NoSlots.slots (pTrXK hM₀ s t P h i x hx u).2 ψ
  | _, _, [], _, _, _, _, _, _, u, ψ =>
      WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots u ψ
  | _, _, [_], _, _, _, _, _, _, u, ψ => by
      change WFF.subst _ _ _ _ _ _ (WFF.shift _ _ (WFF.holeAt _ u ψ)) = _
      rw [WFF.shift_holeAt _ _ Ctx.NoSlots.slots, WFF.shift_hole, WFF.subst_holeAt]
      rfl
  | s, t, c :: c' :: P, h, _, _, _, _, _, u, ψ => by
      change pTrXKW hM₀ _ t (c' :: P) h _ _ _
        (WFF.subst _ _ _ _ _ _ (WFF.shift _ _ (WFF.holeAt _ u ψ))) = _
      rw [WFF.shift_holeAt _ _ Ctx.NoSlots.slots, WFF.shift_hole, WFF.subst_holeAt]
      exact pTrXKW_holeAt (stepW s c (born_step h)) t (c' :: P) h _ _ _ _ ψ

/-- A formula of a realised witness's view, realised (`grealT`'s form). -/
noncomputable def grealW {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y))
    (χ : WFF σ ((ctxOf (glat t j)).diaIn y) 0) : WFF σ (ctxOf (glat t (max j hr.data.i₀))) 0 :=
  WFF.realiseAtA hr.data.hT y
    (hr.data.hdeclOf _ (hy.imp fun _ h => (gle hM₀ t (le_max_left _ _)).ref h))
    (Term.mono (gle hM₀ t (le_max_right _ _)) hr.data.t₀)
    (WFF.mono ((gle hM₀ t (le_max_left _ _)).diaIn y) χ)

theorem grealW_neg {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y))
    (χ : WFF σ ((ctxOf (glat t j)).diaIn y) 0) :
    grealW hM₀ hr hy χ.neg = (grealW hM₀ hr hy χ).neg :=
  WFF.realiseAtA_neg _ _ _ _ _

theorem grealW_holeAt {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y)) {T : VarType} {a : Ann T}
    (u : Term σ ((ctxOf (glat t j)).diaIn y) T a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) T) 1) :
    grealW hM₀ hr hy (WFF.holeAt Ctx.NoSlots.slots u ψ) =
      WFF.holeAt Ctx.NoSlots.slots (grealT hr (Ctx.Le.refl _) hy u).2 ψ := by
  unfold grealW
  rw [WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots, WFF.realiseAtA_holeAt]
  rfl

/-- What is necessary along a realised witness is true, realised (`Proof.here_elimAtA`). -/
theorem grealW_of_boxx {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y))
    (χ : WFF σ ((ctxOf (glat t j)).diaIn y) 0) (hb : WFF.boxx y hy χ ∈ (gw hM₀ t).M j) :
    grealW hM₀ hr hy χ ∈ (gw hM₀ t).M (max j hr.data.i₀) := by
  have hj : j ≤ max j hr.data.i₀ := le_max_left _ _
  have hK : hr.data.i₀ ≤ max j hr.data.i₀ := le_max_right _ _
  have hdecl := hr.data.hdeclOf _ (hy.imp fun _ h => (gle hM₀ t hj).ref h)
  refine BWorld.mem_of_provable (Δ := [WFF.hereAt hr.data.hT _ hdecl
      (Term.mono (gle hM₀ t hK) hr.data.t₀), WFF.mono (gle hM₀ t hj) (WFF.boxx _ hy χ)]) ?_
    ⟨Proof.here_elimAtA hr.data.hT _ hdecl _ _ (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  intro φ hφ
  rcases List.mem_cons.mp hφ with rfl | hφ'
  · exact BWorld.mem_T.mp (hr.data.hhereAt (gw hM₀ t).mcsT _ hK hdecl)
  · rw [List.mem_singleton.mp hφ']
    exact (BWorld.mem_lift hj).mp hb

/-- ⭐**What a realising far world has of a formula's preimage is possible here, along the
    witness.**  Otherwise `□_y ¬χ` holds here, so at the root, whose path keeps it to the far
    world, where it is realised (`dia_pathO_iff`, `boxx_mem_pathK`, `grealW_of_boxx`). -/
theorem dia_mem_of_real (hX : CluFlags) (s : GW hF M₀) (i : ℕ) {y : VarSymb} {Y : VarType}
    (hr : (ctxOf (glat s i)).ref y = some (.VTypeDia Y)) (v : GW hF M₀) (P : List ℕ)
    (h : v.1 = nodeOf (groot hF M₀).1 P) {R : ℕ} (hR : rstg s i ≤ R)
    (hrl : (gw hM₀ v).Realised (kw (groot hF M₀) v P h (rorig s y)))
    (χ : WFF σ ((ctxOf (glat s i)).diaIn y) 0)
    (hmem : grealW hM₀ hrl (kw_decl hM₀ (groot hF M₀) v P h R
        ((rorig_ref hX hM₀ s i ⟨Y, hr⟩).imp fun _ e => (gle hM₀ (groot hF M₀) hR).ref e))
      (pTrXKW hM₀ (groot hF M₀) v P h R (rorig s y)
        ((rorig_ref hX hM₀ s i ⟨Y, hr⟩).imp fun _ e => (gle hM₀ (groot hF M₀) hR).ref e)
        (WFF.mono ((gle hM₀ (groot hF M₀) hR).kView (some (rorig s y)))
          (preWPX (rpre hX hM₀ s i) hr χ))) ∈ (gw hM₀ v).M _) :
    WFF.dia y ⟨Y, hr⟩ χ ∈ (gw hM₀ s).M i := by
  by_contra hnot
  have hpath := dia_pathO_iff hX.five hX.fourS hX.fourSW hM₀
    (rpath s) (groot hF M₀) s (rpath_eq s) i hr χ
  have hnot' : ¬ WFF.dia (rorig s y) (rorig_ref hX hM₀ s i ⟨Y, hr⟩)
      (preWPX (rpre hX hM₀ s i) hr χ) ∈ (gw hM₀ (groot hF M₀)).M (rstg s i) :=
    fun hd => hnot (hpath.mp hd)
  have hbx : WFF.boxx (rorig s y) (rorig_ref hX hM₀ s i ⟨Y, hr⟩)
      (preWPX (rpre hX hM₀ s i) hr χ).neg ∈ (gw hM₀ (groot hF M₀)).M (rstg s i) :=
    BWorld.mem_of_provable (Δ := [(WFF.dia (rorig s y) (rorig_ref hX hM₀ s i ⟨Y, hr⟩)
        (preWPX (rpre hX hM₀ s i) hr χ)).neg])
      (fun ψ hψ => by
        rw [List.mem_singleton.mp hψ]
        exact ((gw hM₀ (groot hF M₀)).mcs _).neg_mem_iff.mpr hnot')
      ⟨Proof.boxx_neg_of_not_dia (Γ := (gw hM₀ (groot hF M₀)).ctx (rstg s i)) _ _ _⟩
  have h₂ := (gMs_mono_iff hM₀ (groot hF M₀) hR _).mp hbx
  have hbK := boxx_mem_pathK (hM₀ := hM₀) (groot hF M₀) v P h R (rorig s y)
    ((rorig_ref hX hM₀ s i ⟨Y, hr⟩).imp fun _ e => (gle hM₀ (groot hF M₀) hR).ref e)
    (WFF.mono ((gle hM₀ (groot hF M₀) hR).kView (some (rorig s y)))
      (preWPX (rpre hX hM₀ s i) hr χ)).neg h₂
  rw [pTrXKW_neg] at hbK
  have hn := grealW_of_boxx hM₀ hrl _ _ hbK
  rw [grealW_neg] at hn
  exact ((gw hM₀ v).mcs _).neg_mem_iff.mp hn hmem

/-- Realising a term of the `□` view is collapsing it. -/
theorem grealT_box {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y)) {T : VarType} {b : Ann T}
    (Y : Term σ (ctxOf (glat t j)).boxIn T b) :
    grealT hr (Ctx.Le.refl _) hy (Term.mono (Ctx.le_boxIn_diaIn _ y) Y) =
      ⟨_, Term.collapse (Ctx.collapses_boxIn_self hr.data.hT _)
        (Term.mono (gle hM₀ t (le_max_left _ _)).boxIn Y)⟩ := by
  have e := Term.realiseAtA_mono_boxIn hr.data.hT y
    (hr.data.hdeclOf _ (hy.imp fun _ h => (gle hM₀ t (le_max_left _ _)).ref h))
    (Term.mono (gle hM₀ t (le_max_right _ _)) hr.data.t₀)
    (Term.mono (gle hM₀ t (le_max_left _ _)).boxIn Y)
  rw [Term.mono_mono] at e
  simp only [grealT]
  rw [Term.mono_mono]
  exact e

/-- Keeping and realising, as one chain. -/
theorem real_app {t : GW hF M₀} (s : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hr : (gw hM₀ t).Realised (kw s t P h x))
    (hy : ∃ Y, (ctxOf (glat t (pstg s t P h i))).ref (kw s t P h x) = some (.VTypeDia Y))
    {A : VarType} {a : Ann A} (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a) :
    grealT hr (Ctx.Le.refl _) hy (pTrXK hM₀ s t P h i x hx u).2 =
      ((ptrXKC hM₀ s t P h i x hx).comp (grealC hM₀ hr _ hy)).app u := by
  rw [GTr.app_comp, ← pTrXK_app]
  rfl

/-- ⭐⭐**The tie, from an arrow of a witness's extent** (`tie_nec` along `◇_y`): under T the arrow
    is realised, so the carrier's value there is its body kept and realised.  With `b` that value's
    root preimage kept down `s`'s path, the kept carrier of `b` realises to the value's own, so the
    tie, realised, is `Proof.back_shift`.  Home by `dia_mem_of_real`. -/
theorem tie_pos (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (s : GW hF M₀) (i : ℕ) {y : VarSymb} {Y : VarType}
    (hr : (ctxOf (glat s i)).ref y = some (.VTypeDia Y)) (v : GW hF M₀) (P : List ℕ)
    (h : v.1 = nodeOf (groot hF M₀).1 P)
    (hrl : (gw hM₀ v).Realised (kw (groot hF M₀) v P h (rorig s y))) {A : VarType} {a₀ : Ann A}
    (bd : Term σ ((ctxOf (glat s i)).diaIn y).boxIn A a₀) {g₀ : Ann A}
    (g : Term σ (ctxOf (glat v (max (pstg (groot hF M₀) v P h (rstg s i)) hrl.data.i₀))).boxIn
      A g₀)
    (hg : grealT hrl (Ctx.Le.refl _) (kw_decl hM₀ (groot hF M₀) v P h (rstg s i)
        (rorig_ref hX hM₀ s i ⟨Y, hr⟩))
      (pTrXK hM₀ (groot hF M₀) v P h (rstg s i) (rorig s y) (rorig_ref hX hM₀ s i ⟨Y, hr⟩)
        (preTD hX hM₀ s i ⟨Y, hr⟩ (.boxtm bd)).2).2 = ⟨_, .boxtm g⟩) :
    ∃ (I : ℕ) (hI : i ≤ I) (hy : ∃ Y, (ctxOf (glat s I)).ref y = some (.VTypeDia Y)) (b₀ : Ann A)
      (b : Term σ (ctxOf (glat s I)).boxIn A b₀),
      (OutLeg.pos y hy).dia (WFF.box (WFF.holeAt Ctx.NoSlots.slots
        (Term.pair (Term.mono ((gle hM₀ s hI).diaIn y).boxIn bd) (compBd hF (.pos y hy) b).2)
        (WFF.backDup hS hF A))) ∈ (gw hM₀ s).M I ∧
      cden hM₀ hX s I (Ctx.Le.refl _) (.boxtm b) =
        cden hM₀ hX v _ (Ctx.Le.refl _) (.boxtm g) := by
  obtain rfl : P = rpath v := nodeOf_inj (h.symm.trans (rpath_eq v))
  let K := max (pstg (groot hF M₀) v (rpath v) h (rstg s i)) hrl.data.i₀
  let r₀ := (preTB hX hM₀ v K g).2
  let J := pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K)
  let b₁ := (pTrK hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) r₀).2
  let I := max i J
  let R := max (rstg s I) (max (rstg v K) (rstg s i))
  have hiI : i ≤ I := le_max_left _ _
  have hJI : J ≤ I := le_max_right _ _
  have hRI : rstg s I ≤ R := le_max_left _ _
  have hR₀ : rstg v K ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRi : rstg s i ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hrI := (gle hM₀ s hiI).ref hr
  have hx₀ := rorig_ref hX hM₀ s i ⟨Y, hr⟩
  have hxR : ∃ X, (ctxOf (glat (groot hF M₀) R)).ref (rorig s y) = some (.VTypeDia X) :=
    hx₀.imp fun _ e => (gle hM₀ (groot hF M₀) hRi).ref e
  have hy₀ := kw_decl hM₀ (groot hF M₀) v (rpath v) h (rstg s i) hx₀
  have hyL := kw_decl hM₀ (groot hF M₀) v (rpath v) h R hxR
  refine ⟨I, hiI, ⟨Y, hrI⟩, _, Term.mono (gle hM₀ s hJI).boxIn b₁, ?_, cden_home hM₀ hX s v hJI g⟩
  let L := pstg (groot hF M₀) v (rpath v) h R
  have hLL : L ≤ max L hrl.data.i₀ := le_max_left _ _
  have hKL : K ≤ L := (le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath v) (groot hF M₀) v
    (rpath_eq v) K).trans (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hR₀)
  let g' := Term.mono (gle hM₀ v (hKL.trans hLL)).boxIn g
  let bk := Term.mono (gle hM₀ s hJI).boxIn b₁
  let Xs := Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s I)))
    (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s I))) bk)))
  let rr := Term.mono (gle hM₀ (groot hF M₀) hR₀).boxIn r₀
  let Xr := Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat (groot hF M₀) R)))
    (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat (groot hF M₀) R))) rr)))
  have hx : grealT hrl (Ctx.Le.refl _) hyL (pTrXK hM₀ (groot hF M₀) v (rpath v) h R (rorig s y) hxR
      (Term.mono ((gle hM₀ (groot hF M₀) hRI).kView (some (rorig s y)))
        (preTD hX hM₀ s I ⟨Y, hrI⟩ (.boxtm (Term.mono ((gle hM₀ s hiI).diaIn y).boxIn bd))).2)).2 =
      ⟨_, .boxtm g'⟩ := by
    have e₂ := pTrXK_sigma hM₀ (groot hF M₀) v (rpath v) h R (rorig s y) hxR
      (preTD_stage hM₀ hX s hiI hRi hRI ⟨Y, hr⟩ (.boxtm bd))
    have e₃ := pTrXK_mono hM₀ (groot hF M₀) v (rpath v) h hRi (rorig s y) hx₀
      (preTD hX hM₀ s i ⟨Y, hr⟩ (.boxtm bd)).2
    have e₄ := grealT_mono hrl (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRi) hy₀ hyL _ _ e₃
    refine (grealT_sigma hrl _ hyL e₂).trans (e₄.symm.trans ?_)
    have key : ∀ p : Σ c, Term σ (ctxOf (glat v K)) (.VTypeBox A) c, p = ⟨_, .boxtm g⟩ →
        (⟨_, Term.mono (gle hM₀ v (max_le_max (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRi)
          (le_refl _))) p.2⟩ : Σ c, Term σ _ (.VTypeBox A) c) = ⟨_, .boxtm g'⟩ := by
      rintro _ rfl
      rfl
    exact key _ hg
  have hc : grealT hrl (Ctx.Le.refl _) hyL (pTrXK hM₀ (groot hF M₀) v (rpath v) h R (rorig s y) hxR
      (Term.mono ((gle hM₀ (groot hF M₀) hRI).kView (some (rorig s y)))
        (preTD hX hM₀ s I ⟨Y, hrI⟩ (Term.mono (Ctx.le_boxIn_diaIn _ y) Xs)).2)).2 =
      ⟨_, .boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) g'))⟩ := by
    have e₀ := preTD_box hX hM₀ (Ctx.Le.refl _) ⟨Y, hrI⟩ Xs
    rw [Term.mono_refl, Term.mono_refl] at e₀
    have hb : (⟨_, Term.mono (gle hM₀ (groot hF M₀) hRI).boxIn (preTB hX hM₀ s I Xs).2⟩ :
        Σ c, Term σ _ _ c) = ⟨_, Xr⟩ :=
      (preTB_kept hM₀ hX s I hRI bk).trans (sig_boxtm (sig_shift_cong _ (sig_boxtm
        (sig_shift_cong _ (preTB_pTrK hM₀ hX s hRI hR₀ (gle hM₀ s hJI) r₀)))))
    have hd : (⟨_, Term.mono ((gle hM₀ (groot hF M₀) hRI).kView (some (rorig s y)))
          (preTD hX hM₀ s I ⟨Y, hrI⟩ (Term.mono (Ctx.le_boxIn_diaIn _ y) Xs)).2⟩ :
          Σ c, Term σ _ _ c) = ⟨_, Term.mono (Ctx.le_boxIn_diaIn _ (rorig s y)) Xr⟩ := by
      refine (sig_mono _ e₀).trans ?_
      refine Eq.trans ?_ (sig_mono (Ctx.le_boxIn_diaIn _ (rorig s y)) hb)
      rw [Term.mono_mono, Term.mono_mono]
    have e₂ := (pTrXK_sigma hM₀ (groot hF M₀) v (rpath v) h R (rorig s y) hxR hd).trans
      ((pTrXK_box (hM₀ := hM₀) (groot hF M₀) v (rpath v) h R (rorig s y) hxR Xr).trans
        (sig_mono _ (tr_keptK hM₀ hX (rpath v) (groot hF M₀) v h R rr)))
    refine (grealT_sigma hrl _ hyL e₂).trans ((grealT_box hM₀ hrl hyL _).trans ?_)
    have hpk := (sig_mono (gle hM₀ v hLL).boxIn (pTrK_home hM₀ hX v h hR₀ hKL g)).trans
      (congrArg (Sigma.mk _) (Term.mono_mono _ _ g))
    exact (sig_collapse_cong _ (mono_kept (hF := hF) (gle hM₀ v hLL) _)).trans
      ((Term.collapse_boxtm_shift hT hF _).trans
        (sig_boxtm (sig_boxtm (sig_shift_cong _ hpk))))
  have hpair := (real_app hM₀ (groot hF M₀) (rpath v) h R (rorig s y) hxR hrl hyL _).trans
    (GTr.app_boxtm_pair _
      ((real_app hM₀ (groot hF M₀) (rpath v) h R (rorig s y) hxR hrl hyL _).symm.trans hx)
      ((real_app hM₀ (groot hF M₀) (rpath v) h R (rorig s y) hxR hrl hyL _).symm.trans hc))
  change WFF.dia y _ (WFF.box (WFF.holeAt Ctx.NoSlots.slots _ _)) ∈ _
  rw [← WFF.holeAt_boxHole Ctx.NoSlots.slots]
  refine dia_mem_of_real hM₀ hX s I hrI v (rpath v) h hRI hrl _ ?_
  have e₁ : ∀ {X : VarType} {x : Ann X} (T : Term σ ((ctxOf (glat s I)).diaIn y) X x)
      (Ψ : WFF σ (Ctx.empty.insert (.bnd 0) X) 1),
      preWPX (rpre hX hM₀ s I) hrI (WFF.holeAt Ctx.NoSlots.slots T Ψ) =
        WFF.holeAt Ctx.NoSlots.slots (preTD hX hM₀ s I ⟨Y, hrI⟩ T).2 Ψ :=
    fun T Ψ => WFF.subst_holeAt _ _ _ _ _ T Ψ
  rw [e₁, WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots, pTrXKW_holeAt hM₀,
    grealW_holeAt hM₀]
  refine (congrArg (· ∈ _) (WFF.holeAt_congr Ctx.NoSlots.slots hpair _)).mpr ?_
  rw [WFF.holeAt_boxHole, WFF.holeAt_backDup]
  exact (gw hM₀ v).mem_of_provable (Δ := []) (fun _ hψ => by cases hψ)
    ⟨Proof.K_box (Δ := []) (Proof.back_shift hS hT hF g')⟩

/-- ⭐⭐**A `Back` atom comes back in the model** (`.pos`), as `cRet_of_mem_nec`: under T every
    arrow of the extent is realised, and `tie_pos` gives the home term.  The leg's nonemptiness
    is the truth of `◇_y ⊤`, which the truth lemma supplies. -/
theorem cRet_of_mem_pos (hX : CluFlags) (hS : ModalSys.BStrong = true) (s : GW hF M₀) (i : ℕ)
    {y : VarSymb} {Y : VarType} (hr : (ctxOf (glat s i)).ref y = some (.VTypeDia Y)) {A : VarType}
    {a₀ : Ann A} (bd : Term σ ((ctxOf (glat s i)).diaIn y).boxIn A a₀) {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a)
    (hmem : WFF.back hS .pos (.diatm y ⟨Y, hr⟩ (.boxtm bd)) t ∈ (gw hM₀ s).M i)
    (hne : ∃ b : CAcc hF M₀, GMem hM₀ (groot hF M₀) b.1 (pathOf b.2.down) (pathOf_eq b.2.down)
      (rorig s y)) :
    cRet hM₀ hX (cTag hM₀ hX .pos (ctoDom hM₀ hX _ s
        (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm y ⟨Y, hr⟩ (.boxtm bd))) (cdefinable_den hX _ _)))
      (cData hM₀ hX .pos (ctoDom hM₀ hX _ s
        (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm y ⟨Y, hr⟩ (.boxtm bd))) (cdefinable_den hX _ _))).1
      (cData hM₀ hX .pos (ctoDom hM₀ hX _ s
        (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm y ⟨Y, hr⟩ (.boxtm bd))) (cdefinable_den hX _ _))).2
      (ctoDom hM₀ hX A s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _)) := by
  have hT := hX.bT (hX.bS hS)
  have hR : GR (groot hF M₀) s := (carrows hF M₀).refl hT s
  obtain ⟨b₀', hb₀'⟩ := hne
  refine ⟨⟨⟨b₀', hb₀'⟩⟩, fun b => ⟨hR, fun _ => ?_,
    fun hnT => absurd (hT.symm.trans hnT) (by decide)⟩,
    .inr ⟨hS, i, .pos, _, _, _, _, hmem, rfl, rfl, rfl⟩⟩
  have hm : GMem hM₀ (groot hF M₀) b.1.1 (pathOf b.1.2.down) (pathOf_eq b.1.2.down) (rorig s y) :=
    b.2
  have hrl := hm.resolve_right fun h => absurd (hT.symm.trans h.1) (by decide)
  have hx₀ := rorig_ref hX hM₀ s i ⟨Y, hr⟩
  obtain ⟨g₀, g, hg⟩ := exists_boxtm (grealT hrl (Ctx.Le.refl _)
    (kw_decl hM₀ (groot hF M₀) b.1.1 (pathOf b.1.2.down) (pathOf_eq b.1.2.down) (rstg s i) hx₀)
    (pTrXK hM₀ (groot hF M₀) b.1.1 (pathOf b.1.2.down) (pathOf_eq b.1.2.down) (rstg s i)
      (rorig s y) hx₀ (preTD hX hM₀ s i ⟨Y, hr⟩ (.boxtm bd)).2).2)
  obtain ⟨I, hI, hy, b₀, k, hdia, hden⟩ := tie_pos hM₀ hX hS hT s i hr b.1.1 _ _ hrl bd g hg
  have hatom : WFF.back hS .pos (.diatm y hy (.boxtm (Term.mono ((gle hM₀ s hI).diaIn y).boxIn bd)))
      (Term.mono (gle hM₀ s hI) t) ∈ (gw hM₀ s).M I := (gw hM₀ s).sub hI _ hmem
  have hback : WFF.back hS .nec (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) k)))
      (Term.mono (gle hM₀ s hI) t) ∈ (gw hM₀ s).M I :=
    BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hatom
      · rw [List.mem_singleton.mp hψ]
        exact hdia)
      ⟨Proof.back_of_tie hS hT hF (.pos y hy) k _ _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  refine ⟨⟨I, _, Term.collapse (Ctx.collapses_boxIn_self hT _) (Term.collapse
      (Ctx.collapses_boxIn_self hT _) (Term.shift (Ctx.shifts_boxIn_boxIn hF _) k))⟩,
    ⟨I, _, Term.mono (gle hM₀ s hI) t⟩, ?_, ?_, BWorld.back_here_rel (gw hM₀ s) hS hT _ _ hback⟩
  · change _ = cfromDom hM₀ hX A s (ctoDom hM₀ hX A s _ _)
    rw [cfromDom_toDom]
    have e₁ := cden_sigma (hM₀ := hM₀) hX (s := s) (i := I) (Ctx.Le.refl _)
      (sig_collapse_cong (Ctx.collapses_boxIn_self hT _) (Term.collapse_shift_boxIn hT hF k))
    have e₂ : cden hM₀ hX b.1.1 _ (Ctx.Le.refl _) (.boxtm g) =
        (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm y ⟨Y, hr⟩ (.boxtm bd))).c ⟨b.1, b.2⟩ := by
      rw [cden_dia_c_pos hX hM₀ s i hr (.boxtm bd) b.1 b.2 hrl, Term.mono_refl]
      exact (cden_sigma hX _ hg).symm
    exact e₁.trans ((cden_boxtm_own hX hT s I k hR).symm.trans
      ((congrFun hden ⟨s, ⟨hR⟩⟩).trans (congrFun e₂ ⟨s, ⟨hR⟩⟩)))
  · exact (cden_lift hX hI t).trans (cfromDom_toDom hM₀ hX A s _ _).symm

end GArrow

end V12M
