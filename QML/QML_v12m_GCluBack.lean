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
  rw [GTr.app_boxtm] at hx hy ⊢
  rw [GTr.app_pair]
  exact sig_boxtm (sig_pair (sig_boxtm_inj hx) (sig_boxtm_inj hy))

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
    have hpk : (⟨_, (pTrK hM₀ (groot hF M₀) v (rpath v) h R
        (Term.mono (gle hM₀ (groot hF M₀) hR₀).boxIn r₀)).2⟩ :
        Σ c, Term σ (ctxOf (glat v (pstg (groot hF M₀) v (rpath v) h R))).boxIn A c) =
        ⟨_, g'⟩ := by
      refine (pTrK_mono hM₀ hX (rpath v) (groot hF M₀) v h hR₀ r₀).symm.trans ?_
      refine (sig_mono _ (pTrK_pre hX hM₀ v K g)).trans ?_
      exact congrArg (Sigma.mk _) (Term.mono_mono _ _ _)
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
  · have e₁ : cden hM₀ hX s I (Ctx.Le.refl _) (.boxtm (Term.mono (gle hM₀ s hJI).boxIn b₁)) =
        cden hM₀ hX s J (Ctx.Le.refl _) (.boxtm b₁) :=
      (cden_mono hX (gle hM₀ s hJI) (.boxtm b₁) s I _).trans (cden_congr hX _ s _ _ _ _)
    have e₂ := cden_sigma (hM₀ := hM₀) hX (s := s) (i := J) (Ctx.Le.refl _)
      (sig_boxtm (tr_pathK hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg v K) r₀))
    have e₃ := cden_named_box hX hM₀ s (rstg v K) J
      (pnm_ok hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg v K)) r₀
    have e₄ := cden_box_eq (hM₀ := hM₀) hX v K (Ctx.Le.refl _) g
    rw [Term.mono_refl] at e₄
    exact e₁.trans (e₂.trans (e₃.trans e₄.symm))

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

end GArrow

end V12M
