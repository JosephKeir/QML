import QML.QML_v12m_GCluPush
import QML.QML_v12m_GCluBack

/-!
# QML v12m — 5 on the growing tree: the returning possibilities

Strong B on the cluster (`docs/v12-modal-extensions.md`, "Strong B on S5").  Both directions of the
truth lemma at `retS` and `retxS` read one arrow of a leg at its far world.

* ⭐`FarLeg`: an arrow of a leg, read at its far world: a chain of terms, a translation of formulas
  commuting with hole formulas and conjunction, the semantics of the translation, and the way home
  (`FarLeg.dia_of`).  `farNec` and `farPos` are the two legs; under T every arrow of an extent is
  realised, so `farPos` reads the kept witness and realises it.
* `cTies_tm`, ⭐`packTies_tm`: an object's ties to its own packing, at terms.
* `mem_ret_of_indC`: a returning possibility's value moves along `cInd`.
* `homeT`, `FarKept`, `kept_nec`, `kept_pos`: a kept home term reads at the far world as what it
  was made from.
* ⭐`ret_core`: what is true at the far end of an arrow, with the packing of a boxed object, is a
  returning possibility here.
* `cindCongr`: canonical `Ind` is a congruence, before the truth lemma.
* ⭐⭐`mem_ret_of_satN`: a true returning possibility of a necessary shape is in the theory.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hM₀ : Theory.IsMCS M₀)

/-! ## Conjunctions along a path -/

theorem pTrW_and : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) (φ ψ : WFF σ ((ctxOf (glat s i)).kView none) 0),
    pTrW hM₀ s t P h hP i (.and φ ψ) = .and (pTrW hM₀ s t P h hP i φ) (pTrW hM₀ s t P h hP i ψ)
  | _, _, [], _, _, _, _, _ => rfl
  | _, _, [_], _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, _ =>
      pTrW_and (stepW s c (born_step h)) t (c' :: P) h _ _ _ _

theorem pTrXKW_and : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (φ ψ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    pTrXKW hM₀ s t P h i x hx (.and φ ψ) =
      .and (pTrXKW hM₀ s t P h i x hx φ) (pTrXKW hM₀ s t P h i x hx ψ)
  | _, _, [], _, _, _, _, _, _ => rfl
  | _, _, [_], _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, _, _ =>
      pTrXKW_and (stepW s c (born_step h)) t (c' :: P) h _ _ _ _ _

theorem grealW_and {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y))
    (φ ψ : WFF σ ((ctxOf (glat t j)).diaIn y) 0) :
    grealW hM₀ hr hy (.and φ ψ) = .and (grealW hM₀ hr hy φ) (grealW hM₀ hr hy ψ) := rfl

theorem size_grealW {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y))
    (χ : WFF σ ((ctxOf (glat t j)).diaIn y) 0) : (grealW hM₀ hr hy χ).size = χ.size :=
  (WFF.size_realiseAtA _ _ _ _ _).trans (WFF.size_mono _ _)

/-- ⭐A realised witness's view, read at the world: realising a formula is reading it along the own
    arrow. -/
theorem sat_grealW (hX : CluFlags) (hT : ModalSys.T = true) (t : GW hF M₀) {z : VarSymb}
    {Z : VarType} {j : ℕ} (hz : (ctxOf (glat t j)).ref z = some (.VTypeDia Z))
    (hR : CR t) (hrl : (gw hM₀ t).Realised z)
    (hmz : (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈
      ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX t j).ref z hz)).1)
    (χ : WFF σ ((ctxOf (glat t j)).diaIn z) 0) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX t (max j hrl.data.i₀))
        (grealW hM₀ hrl ⟨Z, hz⟩ χ) ↔
      (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX t j).diaPush z hz ⟨_, hmz⟩) χ := by
  have hZA : Z = hrl.data.A := by
    have h1 := (hrl.data.hdeclOf _ ⟨Z, hz⟩).symm.trans hz
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hZA
  have hj : j ≤ max j hrl.data.i₀ := le_max_left _ _
  have hK : hrl.data.i₀ ≤ max j hrl.data.i₀ := le_max_right _ _
  have hdecl := (gle hM₀ t hj).ref hz
  have hm' := (ccanon_own_mem hX hT t _ hdecl hR).mpr hrl
  exact (Model.sat_realiseAtA hT (ccanonEnv hM₀ hX t _) (Ctx.Presented.noProjLast _) hdecl
    (Term.mono (gle hM₀ t hK) hrl.data.t₀) hm' (ccanon_cont_real hX t hrl hK hdecl hR hm')
    (WFF.mono ((gle hM₀ t hj).diaIn _) χ)).trans
    (Model.sat_mono (Model.Env.diaPush_agree (ccanonEnv_le hX t hj) hz ⟨_, hmz⟩ hm') χ)

/-! ## A leg's arrow, at its far world -/

/-- ⭐**An arrow of a leg, read at its far world.**  A chain of terms; a translation of formulas
    that commutes with conjunction and hole formulas and keeps sizes; what the translation means;
    and the way home: what the far world has of a formula's translation is possible along the
    leg. -/
structure FarLeg (hX : CluFlags) (s : GW hF M₀) (I : ℕ) (O : OutLeg (ctxOf (glat s I)))
    (a : O.Arr (ccanonEnv hM₀ hX s I)) where
  /-- The far world's stage. -/
  L : ℕ
  /-- The chain of terms. -/
  C : GTr σ O.view (ctxOf (glat (O.acc (ccanonEnv hM₀ hX s I) a).1 L))
  npl : C.NPL
  ag : CAgree hM₀ hX C (O.push (ccanonEnv hM₀ hX s I) a)
  /-- The translation of formulas. -/
  trW : WFF σ O.view 0 → WFF σ (ctxOf (glat (O.acc (ccanonEnv hM₀ hX s I) a).1 L)) 0
  size_trW : ∀ χ, (trW χ).size = χ.size
  trW_and : ∀ φ ψ, trW (.and φ ψ) = .and (trW φ) (trW ψ)
  trW_hole : ∀ {X : VarType} {x₀ : Ann X} (u : Term σ O.view X x₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) X) 1),
    trW (WFF.holeAt Ctx.NoSlots.slots u ψ) = WFF.holeAt Ctx.NoSlots.slots (C.app u).2 ψ
  dia_of : ∀ χ, trW χ ∈ (gw hM₀ (O.acc (ccanonEnv hM₀ hX s I) a).1).M L →
    O.dia χ ∈ (gw hM₀ s).M I
  sat_trW : ∀ χ, (cmodel hF hM₀ hX).sat (O.push (ccanonEnv hM₀ hX s I) a) χ ↔
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX (O.acc (ccanonEnv hM₀ hX s I) a).1 L) (trW χ)

/-- The plain leg's arrow: the world's preimage, then the root's path. -/
noncomputable def farNec (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ)
    (a : CAcc hF M₀) :
    FarLeg hM₀ hX s I .nec a where
  L := pstg (groot hF M₀) a.1 (cpath a.2.down) (cpath_eq a.2.down) (rstg s I)
  C := preC hM₀ hX s I a (cpathOk hT a.2.down)
  npl := npl_preC hM₀ hX s I a _
  ag := cagree_boxPush hX (.nil _) _ (cagree_canon hX s I) a _
  trW χ := pTrW hM₀ (groot hF M₀) a.1 (cpath a.2.down) (cpath_eq a.2.down) (cpathOk hT a.2.down)
    (rstg s I) (preWP (rpre hX hM₀ s I) χ)
  size_trW χ := (size_pTrW hM₀ _ _ _ _ _ _ _).trans (size_preWP (hM₀ := hM₀) hX s I χ)
  trW_and φ ψ := pTrW_and hM₀ _ _ _ _ _ _ _ _
  trW_hole {X _} u ψ := by
    have e : preWP (rpre hX hM₀ s I) (WFF.holeAt Ctx.NoSlots.slots u ψ) =
        WFF.holeAt Ctx.NoSlots.slots (preTB hX hM₀ s I u).2 ψ := WFF.subst_holeAt _ _ _ _ _ u ψ
    rw [e, pTrW_holeAt hM₀]
    exact WFF.holeAt_congr _ (preC_app hM₀ hX s I a _ u).symm ψ
  dia_of χ h := dia_mem_of_path hM₀ hX s I a.1 _ _ _ (le_refl _) χ (by rw [WFF.mono_refl]; exact h)
  sat_trW χ := sat_boxPush_c hX s I a _ _ _ rfl χ

/-- Under T every arrow of an extent is realised. -/
theorem real_of_ext (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ) {y : VarSymb}
    {Y : VarType} (hr : (ctxOf (glat s I)).ref y = some (.VTypeDia Y))
    (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s I).ref y hr)).1) :
    (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 (cpath a.1.2.down) (cpath_eq a.1.2.down)
      (rorig s y)) :=
  ((ccanon_mem_iff hX s I hr a.1).mp a.2).resolve_right
    fun h => absurd (hT.symm.trans h.1) (by decide)

/-- A witness's arrow: the world's preimage, the root's path keeping the witness, then its
    realisation at the end. -/
noncomputable def farPos (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ)
    {y : VarSymb} (hy : ∃ Y, (ctxOf (glat s I)).ref y = some (.VTypeDia Y))
    (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s I).ref y hy.choose_spec)).1) :
    FarLeg hM₀ hX s I (.pos y hy) a where
  L := max (pstg (groot hF M₀) a.1.1 (cpath a.1.2.down) (cpath_eq a.1.2.down) (rstg s I))
    (real_of_ext hM₀ hX hT s I hy.choose_spec a).data.i₀
  C := (preXKC hM₀ hX s I hy a.1).comp (grealC hM₀ (real_of_ext hM₀ hX hT s I hy.choose_spec a) _
    (kw_decl hM₀ (groot hF M₀) a.1.1 _ (cpath_eq a.1.2.down) (rstg s I)
      (rorig_ref hX hM₀ s I hy)))
  npl := GTr.npl_comp _ _ (npl_preXKC hM₀ hX s I hy a.1) (npl_grealC hM₀ _ _ _)
  ag := cagree_diaPushR hX (.nil _) _ (cagree_canon hX s I) hy.choose_spec a
    (real_of_ext hM₀ hX hT s I hy.choose_spec a)
  trW χ := grealW hM₀ (real_of_ext hM₀ hX hT s I hy.choose_spec a)
    (kw_decl hM₀ (groot hF M₀) a.1.1 _ (cpath_eq a.1.2.down) (rstg s I)
      (rorig_ref hX hM₀ s I hy))
    (pTrXKW hM₀ (groot hF M₀) a.1.1 (cpath a.1.2.down) (cpath_eq a.1.2.down) (rstg s I)
      (rorig s y) (rorig_ref hX hM₀ s I hy) (preWPX (rpre hX hM₀ s I) hy.choose_spec χ))
  size_trW χ := (size_grealW hM₀ _ _ _).trans ((size_pTrXKW (hM₀ := hM₀) _ _ _ _ _ _ _ _).trans
    (size_preWPX (hM₀ := hM₀) hX s I _ χ))
  trW_and φ ψ := by
    change grealW hM₀ _ _ (pTrXKW hM₀ _ _ _ _ _ _ _ (.and _ _)) = _
    rw [pTrXKW_and hM₀]
    rfl
  trW_hole {X _} u ψ := by
    have e : preWPX (rpre hX hM₀ s I) hy.choose_spec (WFF.holeAt Ctx.NoSlots.slots u ψ) =
        WFF.holeAt Ctx.NoSlots.slots (preTD hX hM₀ s I hy u).2 ψ := WFF.subst_holeAt _ _ _ _ _ u ψ
    change grealW hM₀ _ _ (pTrXKW hM₀ _ _ _ _ _ _ _ _) = _
    rw [e, pTrXKW_holeAt hM₀, grealW_holeAt hM₀]
    exact WFF.holeAt_congr _ (real_app hM₀ (groot hF M₀) _ _ (rstg s I) (rorig s y) _ _ _ _) ψ
  dia_of χ h := by
    refine dia_mem_of_real hM₀ hX s I hy.choose_spec a.1.1 _ _ (le_refl _)
      (real_of_ext hM₀ hX hT s I hy.choose_spec a) χ ?_
    rw [WFF.mono_refl]
    exact h
  sat_trW χ := by
    obtain ⟨Z, hz⟩ := kw_decl hM₀ (groot hF M₀) a.1.1 _ (cpath_eq a.1.2.down) (rstg s I)
      (rorig_ref hX hM₀ s I hy)
    have hR : CR a.1.1 := (carrows hF M₀).refl hT a.1.1
    have hrl := real_of_ext hM₀ hX hT s I hy.choose_spec a
    have hmz := (ccanon_own_mem hX hT a.1.1 _ hz hR).mpr hrl
    exact (sat_diaPush_cK hX s I hy.choose_spec a _ (cpath_eq a.1.2.down) rfl hrl hz hR hmz
      χ).trans (sat_grealW hM₀ hX hT a.1.1 hz hR hrl hmz _).symm

/-! ## Ties at terms -/

section Ties

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A companion's entry, from a necessary object's. -/
theorem at_ext_tm (hT : ModalSys.T = true) {Δ : Ctx} (θ : Subst σ Δ) (p : List Step) :
    ∀ {A : VarType} {v : VarSymb} {a : Ann A} (s : Term σ Δ A a) {C : VarType},
      A.compAt p = some C → θ.at v = .tm s →
      ∃ (w₀ : Ann C) (w : Term σ Δ.boxIn C w₀), θ.at (v.ext p) = .tm (.boxtm w) := by
  induction p with
  | nil =>
      intro A v a s C hC hv
      cases A <;> simp only [VarType.compAt, reduceCtorEq, Option.some.injEq] at hC
      subst hC
      cases s with
      | boxtm w => exact ⟨_, w, hv⟩
  | cons st q ih =>
      intro A v a s C hC hv
      cases A <;> cases st <;> simp only [VarType.compAt, reduceCtorEq] at hC
      · cases s with
        | pair s₁ s₂ => exact ih s₁ hC (by rw [Subst.at_proj θ v rfl, hv]; rfl)
      · cases s with
        | pair s₁ s₂ => exact ih s₂ hC (by rw [Subst.at_proj θ v rfl, hv]; rfl)
      · cases s with
        | boxtm w =>
            exact ih (Term.collapse (Ctx.collapses_boxIn_self hT Δ) w) hC
              (by rw [Subst.at_proj θ v rfl, hv]; exact SubE.proj_boxtm_here w hT)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Two substitutions agreeing at an address agree along a companion's path. -/
theorem at_ext_congr {Δ : Ctx} (θ θ' : Subst σ Δ) (p : List Step) :
    ∀ {A : VarType} {v v' : VarSymb} {C : VarType}, A.compAt p = some C → θ.at v = θ'.at v' →
      θ.at (v.ext p) = θ'.at (v'.ext p) := by
  induction p with
  | nil => intro _ _ _ _ _ hv; exact hv
  | cons st q ih =>
      intro A v v' C hC hv
      cases A <;> cases st <;> simp only [VarType.compAt, reduceCtorEq] at hC
      · exact ih hC (by rw [Subst.at_proj θ v rfl, Subst.at_proj θ' v' rfl, hv])
      · exact ih hC (by rw [Subst.at_proj θ v rfl, Subst.at_proj θ' v' rfl, hv])
      · exact ih hC (by rw [Subst.at_proj θ v rfl, Subst.at_proj θ' v' rfl, hv])

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- ⭐One companion's tie, read at a term: the value's last part, with the object's own companion
    kept. -/
theorem cTies_step {Γ Ω : Ctx} [Γ.NoSlots] {d : ℕ} {ι : VarSymb → VarSymb} (θ : Subst σ Γ)
    (hθ : Subst.Ok Ω θ) (hc : Subst.Coh ι Ω θ) (hs : Ω.SlotsFrom d) (hs' : Γ.SlotsFrom 0)
    (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    {A : VarType} {a₀ : Ann A} (E₀ : Term σ Γ.boxIn A a₀) (e : VarSymb)
    (he : Ω.ref e = some (.VTypeBox A)) (hat : θ.at e = .tm (.boxtm E₀)) (q : List Step)
    (ps : List (List Step)) (h : A.CompOk (q :: ps)) (z : VarSymb)
    (hz : Ω.boxIn.ref z = some (A.compsFlat (q :: ps))) {s₀ : Ann (A.compsFlat ps)}
    (S : Term σ Γ.boxIn (A.compsFlat ps) s₀) {y₀ : Ann ((A.compAt q).getD .VTypeOne)}
    (y : Term σ Γ.boxIn ((A.compAt q).getD .VTypeOne) y₀)
    (hzat : θ.box.at z = .tm (Term.pair S y)) :
    WFF.subst ι θ hθ hc hs hs' (WFF.cTies hS hF hs e he (q :: ps) h z hz) =
      WFF.and (WFF.box (WFF.holeAt Ctx.NoSlots.slots (Term.pair y
          (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (compVal E₀ q h).2)))
          (WFF.backDup hS hF _)))
        (WFF.subst ι θ hθ hc hs hs' (WFF.cTies hS hF hs e he ps h.tail _ (Ctx.ref_fst_of hz))) := by
  obtain ⟨-, hall, -⟩ := h.resolve_left (List.cons_ne_nil _ _)
  have hq := compAt_getD (hall q List.mem_cons_self)
  let θ' := Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.boxtm E₀))
  have hr : θ'.at (.root (.bnd 0)) = .tm (Term.boxtm E₀) := Subst.at_single_root _ _
  obtain ⟨w₀, w, hw⟩ := at_ext_tm hT θ' (.here :: q) (Term.boxtm E₀)
    (A := .VTypeBox A) hq hr
  have hY : θ.at ((VarSymb.step e .here).ext q) = .tm (Term.boxtm w) :=
    (at_ext_congr θ θ' (.here :: q) (A := .VTypeBox A) hq (hat.trans hr.symm)).trans hw
  have hcv : compVal E₀ q h = ⟨_, w⟩ :=
    Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ' hw)
  have ha : θ.box.at (.step z .snd) = .tm y := by
    rw [Subst.at_proj _ _ rfl, hzat]
    rfl
  have hb : θ.box.at (.step ((VarSymb.step e .here).ext q) .keep) =
      .tm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) w)) := by
    rw [Subst.box_at_keep, hY]
    exact SubE.keepE_tm w hF
  refine congrArg (WFF.and · _) (congrArg WFF.box ((WFF.subst_holeAt θ.box (Subst.ok_box hθ)
    (Subst.coh_box hθ hc) hs.boxIn hs'.boxIn
    (Term.pair (Term.eta (.step z .snd) _ (Ctx.ref_snd_of hz))
      (Term.eta (.step ((VarSymb.step e .here).ext q) .keep) (.VTypeBox _)
        (Ctx.ref_keep_of' hF (h.ref_head he) rfl))) (WFF.backDup hS hF _)).trans
    (WFF.holeAt_congr _ (sig_pair (Term.subst_eta_tm _ _ _ _ _ _ _ ha)
      ((Term.subst_eta_tm _ _ _ _ _ _ _ hb).trans
        (sig_boxtm (sig_shift_cong _ hcv.symm)))) _)))

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- ⭐Each companion's tie, at a term: `Proof.back_shift` at the companion's contents. -/
theorem cTies_tm {Γ Ω : Ctx} [Γ.NoSlots] {d : ℕ} {ι : VarSymb → VarSymb} (θ : Subst σ Γ)
    (hθ : Subst.Ok Ω θ) (hc : Subst.Coh ι Ω θ) (hs : Ω.SlotsFrom d) (hs' : Γ.SlotsFrom 0)
    (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true) (hF : ModalSys.Four = true)
    {Δ : List (WFF σ Γ 0)} {A : VarType} {a₀ : Ann A} (E₀ : Term σ Γ.boxIn A a₀) (e : VarSymb)
    (he : Ω.ref e = some (.VTypeBox A)) (hat : θ.at e = .tm (.boxtm E₀)) :
    (cs : List (List Step)) → (h : A.CompOk cs) → (z : VarSymb) →
    (hz : Ω.boxIn.ref z = some (A.compsFlat cs)) →
    θ.box.at z = .tm (compsVal E₀ cs h).2 →
    Nonempty (Proof σ Γ Δ (WFF.subst ι θ hθ hc hs hs' (WFF.cTies hS hF hs e he cs h z hz)))
  | [], _, _, _, _ => ⟨Proof.top_intro⟩
  | q :: ps, h, z, hz, hzat => by
      obtain ⟨hrec⟩ := cTies_tm θ hθ hc hs hs' hS hT hF E₀ e he hat ps h.tail _
        (Ctx.ref_fst_of hz) (by rw [Subst.at_proj _ _ rfl, hzat]; rfl)
      refine ⟨Proof.conv (cTies_step θ hθ hc hs hs' hS hT hF E₀ e he hat q ps h z hz _ _ hzat).symm
        (Proof.and_intro ?_ hrec)⟩
      exact Proof.nec (Proof.conv (WFF.holeAt_backDup hS hF _ _ _).symm
        (Proof.back_shift hS hT hF _))

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- ⭐**An object's ties to its own packing**, at any term. -/
theorem packTies_tm (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (hF : ModalSys.Four = true) {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} {A : VarType}
    (cs : List (List Step)) (h : A.CompOk cs) {a₀ : Ann A} (E₀ : Term σ Γ.boxIn A a₀) :
    Nonempty (Proof σ Γ Δ (WFF.holeAt Ctx.NoSlots.slots
      (Term.pair (Term.boxtm E₀) (Term.boxtm (compsVal E₀ cs h).2))
      (WFF.packTies hS hF (.boxC A cs h)))) := by
  have hr := Subst.at_single_root (σ := σ) (Δ := Γ) (.bnd 0)
    (.tm (Term.pair (Term.boxtm E₀) (Term.boxtm (compsVal E₀ cs h).2)))
  exact cTies_tm _ _ _ _ _ hS hT hF E₀ _ _ (by rw [Subst.at_proj _ _ rfl, hr]; rfl) cs h _ _
    (Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, hr]; rfl))

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem compsBase_compsVal {Γ : Ctx} {A : VarType} {a₀ : Ann A} (E₀ : Term σ Γ.boxIn A a₀) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs),
      compsBase cs (compsVal E₀ cs h).2 = ⟨_, E₀⟩
  | [], _ => rfl
  | _ :: ps, h => compsBase_compsVal E₀ ps h.tail

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- The base object goes through a chain. -/
theorem app_compsBase {Γ Δ : Ctx} {A : VarType} (C : GTr σ Γ Δ) :
    ∀ (cs : List (List Step)) {b : Ann (A.compsFlat cs)} (s : Term σ Γ (A.compsFlat cs) b),
      C.app (compsBase cs s).2 = compsBase cs (C.app s).2
  | [], _, _ => rfl
  | q :: ps, _, .pair t y => by
      have e := app_compsBase C ps t
      change C.app (compsBase ps t).2 = compsBase (q :: ps) (C.app (Term.pair t y)).2
      rw [GTr.app_pair]
      exact e

end Ties

/-! ## Moving a value -/

variable {hM₀} in
/-- One value at two stages means one annotation (`ann_eq_of_cden`). -/
theorem ann_eq_of_toDomC (hX : CluFlags) (hT : ModalSys.T = true) {s : GW hF M₀} {A : VarType}
    {i i' : ℕ} {a a' : Ann A} (t : Term σ (ctxOf (glat s i)) A a)
    (t' : Term σ (ctxOf (glat s i')) A a')
    (h : ctoDom hM₀ hX A s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _) =
      ctoDom hM₀ hX A s (cden hM₀ hX s i' (Ctx.Le.refl _) t') (cdefinable_den hX _ _)) :
    a = a' := by
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  exact ann_eq_of_cden hX hT (Term.mono ((gw hM₀ s).le hK) t) (Term.mono ((gw hM₀ s).le hK') t')
    ((cden_lift hX hK t).trans ((ctoDom_inj hX h).trans (cden_lift hX hK' t').symm))

variable {hM₀} in
/-- Denotations equal at a common stage make the equation true there. -/
theorem sat_eqRec_liftC (hX : CluFlags) {s : GW hF M₀} {A : VarType} {i i' K : ℕ} (hK : i ≤ K)
    (hK' : i' ≤ K) {a : Ann A} (t : Term σ (ctxOf (glat s i)) A a)
    (t' : Term σ (ctxOf (glat s i')) A a)
    (h : ctoDom hM₀ hX A s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _) =
      ctoDom hM₀ hX A s (cden hM₀ hX s i' (Ctx.Le.refl _) t') (cdefinable_den hX _ _)) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s K)
      (eqRec A (Term.mono ((gw hM₀ s).le hK) t) (Term.mono ((gw hM₀ s).le hK') t') :
        WFF σ _ 0) := by
  rw [Model.sat_eqRec, interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
    interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
  exact ctoDom_congr hX ((cden_lift hX hK t).trans ((ctoDom_inj hX h).trans
    (cden_lift hX hK' t').symm)) _ _

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Weakening a leg twice is weakening it once. -/
theorem retS_mono_mono {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : Γ₁.Le Γ₂) (h₂ : Γ₂.Le Γ₃)
    (hS : ModalSys.BStrong = true) (O : OutLeg Γ₁) (R : RShape) {b : Ann R.flat}
    (v : Term σ Γ₂ R.flat b) (Φ : WFF σ (O.view.insert (.bnd 0) R.ty) 1) :
    (WFF.mono h₂ ((O.mono h₁).retS hS R v
      (WFF.mono ((OutLeg.le_view_mono h₁ O).insert (.bnd 0) _) Φ)) : WFF σ Γ₃ 0) =
      (O.mono (h₁.trans h₂)).retS hS R (Term.mono h₂ v)
        (WFF.mono ((OutLeg.le_view_mono (h₁.trans h₂) O).insert (.bnd 0) _) Φ) := by
  cases O with
  | nec =>
      change WFF.retS hS _ _ (WFF.mono _ (WFF.mono _ Φ)) = _
      rw [WFF.mono_mono]
      rfl
  | pos y hy =>
      change WFF.retxS hS _ _ _ _ (WFF.mono _ (WFF.mono _ Φ)) = _
      rw [WFF.mono_mono]
      rfl

variable {hM₀} in
/-- ⭐**A returning possibility's value moves along `cInd`** (`BData.mem_ret_of_ind`), along either
    leg: related representatives are interchangeable in the slot formula `◇[d ↦ z] Φ(d)`
    (`OutLeg.instantiate_retSlot`), and one denotation is one annotation, so `eqRec` is true and in
    the theory. -/
theorem mem_ret_of_indC (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    {s : GW hF M₀} {R : RShape} {i K : ℕ} (hiK : i ≤ K) (O : OutLeg (ctxOf (glat s i)))
    {bv : Ann R.flat} (v : Term σ (ctxOf (glat s K)) R.flat bv) {a : Ann R.flat}
    (t : Term σ (ctxOf (glat s i)) R.flat a) (Φ : WFF σ (O.view.insert (.bnd 0) R.ty) 1)
    (IH : ∀ (L : ℕ) {c : Ann R.flat} (u u' : Term σ (ctxOf (glat s L)) R.flat c),
      (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s L) (eqRec R.flat u u' : WFF σ _ 0) →
        (eqRec R.flat u u' : WFF σ _ 0) ∈ (gw hM₀ s).M L)
    (hmem : (O.mono (gle hM₀ s hiK)).retS hS R v
      (WFF.mono ((OutLeg.le_view_mono (gle hM₀ s hiK) O).insert (.bnd 0) _) Φ) ∈ (gw hM₀ s).M K)
    (hind : cInd hM₀ hX (ctoDom hM₀ hX R.flat s (cden hM₀ hX s K (Ctx.Le.refl _) v)
        (cdefinable_den hX _ _))
      (ctoDom hM₀ hX R.flat s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _))) :
    O.retS hS R t Φ ∈ (gw hM₀ s).M i := by
  obtain ⟨⟨i₁, a₁, u₁⟩, ⟨i₂, a₂, u₂⟩, h₁, h₂, hrel⟩ := hind
  rw [cfromDom_toDom] at h₁ h₂
  have e₁ : ctoDom hM₀ hX R.flat s (cden hM₀ hX s K (Ctx.Le.refl _) v) (cdefinable_den hX _ _) =
      ctoDom hM₀ hX R.flat s (cden hM₀ hX s i₁ (Ctx.Le.refl _) u₁) (cdefinable_den hX _ _) :=
    ctoDom_congr hX h₁.symm _ _
  have e₂ : ctoDom hM₀ hX R.flat s (cden hM₀ hX s i₂ (Ctx.Le.refl _) u₂)
      (cdefinable_den hX _ _) =
      ctoDom hM₀ hX R.flat s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _) :=
    ctoDom_congr hX h₂ _ _
  obtain rfl := ann_eq_of_toDomC hX hT _ _ e₁
  obtain rfl := ann_eq_of_toDomC hX hT _ _ e₂
  let L := max (max K i₁) i₂
  have hKL : K ≤ L := le_max_of_le_left (le_max_left _ _)
  have h₁L : i₁ ≤ L := le_max_of_le_left (le_max_right _ _)
  have h₂L : i₂ ≤ L := le_max_right _ _
  have hiL : i ≤ L := hiK.trans hKL
  have hLK : (ctxOf (glat s K)).Le (ctxOf (glat s L)) := gle hM₀ s hKL
  let OL := O.mono (gle hM₀ s hiL)
  let ΦL := WFF.mono ((OutLeg.le_view_mono (gle hM₀ s hiL) O).insert (.bnd 0) R.ty) Φ
  have hm₁ : OL.retS hS R (Term.mono hLK v) ΦL ∈ (gw hM₀ s).M L := by
    have h := (BWorld.mem_lift hKL).mp hmem
    change WFF.mono (gle hM₀ s hKL) _ ∈ _ at h
    rw [retS_mono_mono] at h
    exact h
  have hq₁ := IH L _ _ (sat_eqRec_liftC hX hKL h₁L _ _ e₁)
  have hr₁ : OL.retS hS R (Term.mono ((gw hM₀ s).le h₁L) u₁) ΦL ∈ (gw hM₀ s).M L :=
    BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hm₁
      · rw [List.mem_singleton.mp hψ]
        exact hq₁)
      ⟨Proof.ret_eqS hS OL _ _ _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  have hI₁ := OutLeg.instantiate_retSlot hS OL R ΦL (Term.mono ((gw hM₀ s).le h₁L) u₁)
  have hI₂ := OutLeg.instantiate_retSlot hS OL R ΦL (Term.mono ((gw hM₀ s).le h₂L) u₂)
  have hr₂ : OL.retS hS R (Term.mono ((gw hM₀ s).le h₂L) u₂) ΦL ∈ (gw hM₀ s).M L :=
    (congrArg (· ∈ (gw hM₀ s).M L) hI₂).mp ((hrel L h₁L h₂L (OutLeg.retSlot hS OL R ΦL)).mp
      ((congrArg (· ∈ (gw hM₀ s).M L) hI₁).mpr hr₁))
  have hq₂ := IH L _ _ (sat_eqRec_liftC hX h₂L hiL _ _ e₂)
  refine (BWorld.mem_lift hiL).mpr ?_
  change WFF.mono (gle hM₀ s hiL) _ ∈ _
  rw [OutLeg.mono_retS]
  exact BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hr₂
      · rw [List.mem_singleton.mp hψ]
        exact hq₂)
    ⟨Proof.ret_eqS hS OL _ _ _ (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-! ## A kept home term, at the far world -/

/-- The home term of a far world's term: its root preimage kept down the world's path. -/
noncomputable abbrev homeT (hX : CluFlags) (s v : GW hF M₀) {K : ℕ} {A : VarType} {c₀ : Ann A}
    (c : Term σ (ctxOf (glat v K)).boxIn A c₀) :
    Σ b, Term σ (ctxOf (glat s (pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K)))).boxIn
      A b :=
  pTrK hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) (preTB hX hM₀ v K c).2

/-- The preimage of a kept home term, at a root stage above both. -/
theorem preTB_home (hX : CluFlags) (s v : GW hF M₀) {I K R : ℕ}
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I) (hRI : rstg s I ≤ R)
    (hR₀ : rstg v K ≤ R) {A : VarType} {c₀ : Ann A} (c : Term σ (ctxOf (glat v K)).boxIn A c₀) :
    (⟨_, Term.mono (gle hM₀ (groot hF M₀) hRI).boxIn (preTB hX hM₀ s I (.boxtm (Term.shift
        (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v c).2)))).2⟩ :
        Σ b, Term σ (ctxOf (glat (groot hF M₀) R)).boxIn (.VTypeBox A) b) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ (groot hF M₀) hR₀).boxIn (preTB hX hM₀ v K c).2))⟩ := by
  refine (sig_mono _ (preTB_shift hX hM₀ s I _)).trans ?_
  refine Eq.trans (sig_boxtm (congrArg (Sigma.mk _) (Term.shift_mono
    (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF _)
    (gle hM₀ (groot hF M₀) hRI).boxIn (gle hM₀ (groot hF M₀) hRI).boxIn.boxIn _).symm)) ?_
  exact sig_boxtm (sig_shift_cong _ (preTB_pTrK hM₀ hX s hRI hR₀ (gle hM₀ s hJI) _))

/-- What a kept home term reads as at the far world: at some later stage, what it was made from. -/
def FarKept {hX : CluFlags} {s : GW hF M₀} {I : ℕ} {O : OutLeg (ctxOf (glat s I))}
    {a : O.Arr (ccanonEnv hM₀ hX s I)} (F : FarLeg hM₀ hX s I O a) {A : VarType} {b₀ : Ann A}
    (bk : Term σ (ctxOf (glat s I)).boxIn A b₀) {K : ℕ} {c₀ : Ann A}
    (c : Term σ (ctxOf (glat (O.acc (ccanonEnv hM₀ hX s I) a).1 K)).boxIn A c₀) : Prop :=
  ∃ (L' : ℕ) (hL : F.L ≤ L') (hK : K ≤ L'),
    (⟨_, Term.mono (gle hM₀ (O.acc (ccanonEnv hM₀ hX s I) a).1 hL) (F.C.app (Term.mono O.le_view
      (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) bk)))).2⟩ :
      Σ e, Term σ (ctxOf (glat (O.acc (ccanonEnv hM₀ hX s I) a).1 L')) (.VTypeBox A) e) =
    ⟨_, .boxtm (Term.mono (gle hM₀ (O.acc (ccanonEnv hM₀ hX s I) a).1 hK).boxIn c)⟩

/-- A kept home term along a path. -/
theorem kept_path (hX : CluFlags) (s : GW hF M₀) (I : ℕ) (v : GW hF M₀) (P : List ℕ)
    (h : v.1 = nodeOf (groot hF M₀).1 P) (hP : PathOk P) {K : ℕ} {A : VarType} {c₀ : Ann A}
    (c : Term σ (ctxOf (glat v K)).boxIn A c₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I) :
    ∃ (L' : ℕ) (hL : pstg (groot hF M₀) v P h (rstg s I) ≤ L') (hK : K ≤ L'),
      (⟨_, Term.mono (gle hM₀ v hL) (pTr hM₀ (groot hF M₀) v P h hP (rstg s I)
        (preTB hX hM₀ s I (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
          (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v c).2)))).2).2⟩ :
        Σ e, Term σ (ctxOf (glat v L')) (.VTypeBox A) e) =
      ⟨_, .boxtm (Term.mono (gle hM₀ v hK).boxIn c)⟩ := by
  obtain rfl : P = rpath v := nodeOf_inj (h.symm.trans (rpath_eq v))
  let R := max (rstg s I) (rstg v K)
  have hRI : rstg s I ≤ R := le_max_left _ _
  have hR₀ : rstg v K ≤ R := le_max_right _ _
  have hL := pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRI
  have hK : K ≤ pstg (groot hF M₀) v (rpath v) h R :=
    (le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath v) (groot hF M₀) v (rpath_eq v) K).trans
      (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hR₀)
  refine ⟨_, hL, hK, ?_⟩
  refine (pTr_mono hM₀ _ _ _ h hP hRI _).trans ?_
  refine (pTr_sigma hM₀ _ _ _ _ hP _ (preTB_home hM₀ hX s v hJI hRI hR₀ c)).trans ?_
  refine (tr_path hX hM₀ _ _ _ h hP R _).trans ?_
  exact sig_boxtm ((tr_pathK hX hM₀ _ _ _ h R _).symm.trans (pTrK_home hM₀ hX v h hR₀ hK c))

/-- A kept home term along the plain leg. -/
theorem kept_nec (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ)
    (a : CAcc hF M₀) {K : ℕ} {A : VarType}
    {c₀ : Ann A} (c : Term σ (ctxOf (glat a.1 K)).boxIn A c₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg a.1 K) ≤ I) :
    FarKept hM₀ (farNec hM₀ hX hT s I a)
      (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s a.1 c).2) c := by
  obtain ⟨L', hL, hK, e⟩ := kept_path hM₀ hX s I a.1 _ (cpath_eq a.2.down) (cpathOk hT a.2.down) c
    hJI
  refine ⟨L', hL, hK, ?_⟩
  refine Eq.trans ?_ e
  refine sig_mono _ ?_
  have e₀ : (⟨_, Term.mono (OutLeg.nec : OutLeg (ctxOf (glat s I))).le_view
      (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s a.1 c).2)))⟩ :
      Σ e, Term σ (ctxOf (glat s I)).boxIn (.VTypeBox A) e) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
        (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s a.1 c).2))⟩ :=
    congrArg (Sigma.mk _) (Term.mono_refl _ _)
  exact (preC_app hM₀ hX s I a _ _).trans
    (pTr_sigma hM₀ _ _ _ _ (cpathOk hT a.2.down) _ (preTB_sigma hX hM₀ s I e₀))

/-- A kept home term along a witness whose arrow is realised. -/
theorem kept_real (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ) {y : VarSymb}
    (hy : ∃ Y, (ctxOf (glat s I)).ref y = some (.VTypeDia Y)) (v : GW hF M₀) (P : List ℕ)
    (h : v.1 = nodeOf (groot hF M₀).1 P)
    (hrl : (gw hM₀ v).Realised (kw (groot hF M₀) v P h (rorig s y))) {K : ℕ} {A : VarType}
    {c₀ : Ann A} (c : Term σ (ctxOf (glat v K)).boxIn A c₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I) :
    ∃ (L' : ℕ) (hL : max (pstg (groot hF M₀) v P h (rstg s I)) hrl.data.i₀ ≤ L') (hK : K ≤ L'),
      (⟨_, Term.mono (gle hM₀ v hL) (grealT hrl (Ctx.Le.refl _)
        (kw_decl hM₀ (groot hF M₀) v P h (rstg s I) (rorig_ref hX hM₀ s I hy))
        (pTrXK hM₀ (groot hF M₀) v P h (rstg s I) (rorig s y) (rorig_ref hX hM₀ s I hy)
          (preTD hX hM₀ s I hy (Term.mono (Ctx.le_boxIn_diaIn _ y)
            (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
              (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v c).2))))).2).2).2⟩ :
        Σ e, Term σ (ctxOf (glat v L')) (.VTypeBox A) e) =
      ⟨_, .boxtm (Term.mono (gle hM₀ v hK).boxIn c)⟩ := by
  obtain rfl : P = rpath v := nodeOf_inj (h.symm.trans (rpath_eq v))
  let R := max (rstg s I) (rstg v K)
  have hRI : rstg s I ≤ R := le_max_left _ _
  have hR₀ : rstg v K ≤ R := le_max_right _ _
  have hLm := pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hRI
  have hKm : K ≤ pstg (groot hF M₀) v (rpath v) h R :=
    (le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath v) (groot hF M₀) v (rpath_eq v) K).trans
      (pstg_monotone hM₀ (groot hF M₀) v (rpath v) h hR₀)
  have hx₀ := rorig_ref hX hM₀ s I hy
  have hxR : ∃ X, (ctxOf (glat (groot hF M₀) R)).ref (rorig s y) = some (.VTypeDia X) :=
    hx₀.imp fun _ e => (gle hM₀ (groot hF M₀) hRI).ref e
  have hy₀ := kw_decl hM₀ (groot hF M₀) v (rpath v) h (rstg s I) hx₀
  have hyR := kw_decl hM₀ (groot hF M₀) v (rpath v) h R hxR
  have hLL : pstg (groot hF M₀) v (rpath v) h R ≤
      max (pstg (groot hF M₀) v (rpath v) h R) hrl.data.i₀ := le_max_left _ _
  refine ⟨_, max_le_max hLm (le_refl _), hKm.trans hLL, ?_⟩
  let bk := Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s v c).2
  let Xs := Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s I))) bk)
  let rr := Term.mono (gle hM₀ (groot hF M₀) hR₀).boxIn (preTB hX hM₀ v K c).2
  let Xr := Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat (groot hF M₀) R))) rr)
  have e₀ := preTD_box hX hM₀ (Ctx.Le.refl _) hy Xs
  rw [Term.mono_refl, Term.mono_refl] at e₀
  have hb : (⟨_, Term.mono (gle hM₀ (groot hF M₀) hRI).boxIn (preTB hX hM₀ s I Xs).2⟩ :
      Σ c, Term σ _ _ c) = ⟨_, Xr⟩ := preTB_home hM₀ hX s v hJI hRI hR₀ c
  have hd : (⟨_, Term.mono ((gle hM₀ (groot hF M₀) hRI).kView (some (rorig s y)))
        (preTD hX hM₀ s I hy (Term.mono (Ctx.le_boxIn_diaIn _ y) Xs)).2⟩ :
        Σ c, Term σ _ _ c) = ⟨_, Term.mono (Ctx.le_boxIn_diaIn _ (rorig s y)) Xr⟩ := by
    refine (sig_mono _ e₀).trans ?_
    refine Eq.trans ?_ (sig_mono (Ctx.le_boxIn_diaIn _ (rorig s y)) hb)
    rw [Term.mono_mono, Term.mono_mono]
  have e₂ := (pTrXK_mono hM₀ (groot hF M₀) v (rpath v) h hRI (rorig s y) hx₀
    (preTD hX hM₀ s I hy (Term.mono (Ctx.le_boxIn_diaIn _ y) Xs)).2).trans
    ((pTrXK_sigma hM₀ (groot hF M₀) v (rpath v) h R (rorig s y) hxR hd).trans
      (pTrXK_box (hM₀ := hM₀) (groot hF M₀) v (rpath v) h R (rorig s y) hxR Xr))
  refine (grealT_mono hrl hLm _ hyR _ _ e₂).trans ?_
  refine (grealT_box hM₀ hrl hyR _).trans ?_
  have hpk := (sig_mono (gle hM₀ v hLL).boxIn (pTrK_home hM₀ hX v h hR₀ hKm c)).trans
    (congrArg (Sigma.mk _) (Term.mono_mono _ _ c))
  have ek := (sig_mono (gle hM₀ v hLL).boxIn (tr_keptK₁ hM₀ hX (rpath v) (groot hF M₀) v h R rr))
  refine (sig_collapse_cong _ ek).trans ?_
  have es : (⟨_, Term.mono (gle hM₀ v hLL).boxIn (.boxtm (Term.shift
      (Ctx.shifts_boxIn_boxIn hF _) (pTrK hM₀ (groot hF M₀) v (rpath v) h R rr).2))⟩ :
      Σ e, Term σ _ (.VTypeBox A) e) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.mono (gle hM₀ v hLL).boxIn
        (pTrK hM₀ (groot hF M₀) v (rpath v) h R rr).2))⟩ :=
    sig_boxtm (congrArg (Sigma.mk _) (Term.shift_mono (Ctx.shifts_boxIn_boxIn hF _)
      (Ctx.shifts_boxIn_boxIn hF _) (gle hM₀ v hLL).boxIn (gle hM₀ v hLL).boxIn.boxIn _).symm)
  refine (sig_collapse_cong _ es).trans ((Term.collapse_boxtm_shift hT hF _).trans ?_)
  exact sig_boxtm hpk

/-- A kept home term along a witness. -/
theorem kept_pos (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (I : ℕ) {y : VarSymb}
    (hy : ∃ Y, (ctxOf (glat s I)).ref y = some (.VTypeDia Y))
    (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s I).ref y hy.choose_spec)).1) {K : ℕ}
    {A : VarType} {c₀ : Ann A} (c : Term σ (ctxOf (glat a.1.1 K)).boxIn A c₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg a.1.1 K) ≤ I) :
    FarKept hM₀ (farPos hM₀ hX hT s I hy a)
      (Term.mono (gle hM₀ s hJI).boxIn (homeT hM₀ hX s a.1.1 c).2) c := by
  obtain ⟨L', hL, hK, e⟩ := kept_real hM₀ hX hT s I hy a.1.1 _ (cpath_eq a.1.2.down)
    (real_of_ext hM₀ hX hT s I hy.choose_spec a) c hJI
  refine ⟨L', hL, hK, Eq.trans ?_ e⟩
  exact sig_mono _ (real_app hM₀ (groot hF M₀) _ _ (rstg s I) (rorig s y) _ _ _ _).symm

/-! ## `Ind` is a congruence -/

/-- A representative of an object is one of the value under a hole term, filled. -/
theorem cden_holeAt (hX : CluFlags) {s : GW hF M₀} {A : VarType} {o : (cframe hF hM₀ hX).Dom A s}
    (u : Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A)
    (hu : cden hM₀ hX s u.i (Ctx.Le.refl _) u.t = cfromDom hM₀ hX A s o)
    {C : VarType} {c : Ann C} (hh : Term σ (Ctx.empty.insert (.bnd 0) A) C c) :
    cden hM₀ hX s u.i (Ctx.Le.refl _) (Term.holeAt u.t hh) =
      cfromDom hM₀ hX C s ((cmodel hF hM₀ hX).holeVal hh o) := by
  have e1 := interp_ccanon hX (hM₀ := hM₀) (Term.holeAt u.t hh) (env := ccanonEnv hM₀ hX s u.i)
    (e := Ctx.Le.refl _) (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)
  have e2 : Model.interp (ccanonEnv hM₀ hX s u.i) u.t = o := by
    rw [interp_ccanon hX u.t (env := ccanonEnv hM₀ hX s u.i) (e := Ctx.Le.refl _)
      (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
    exact (ctoDom_congr hX hu _ _).trans (ctoDom_fromDom hM₀ hX A s o)
  rw [Model.interp_holeAt, e2] at e1
  rw [e1, cfromDom_toDom]

/-- ⭐Canonical `Ind` is a congruence, before the truth lemma: related representatives stay related
    under hole terms and pairing (`DTerm.Rel.holeAt`, `DTerm.Rel.pair`). -/
theorem cindCongr (hX : CluFlags) : (cmodel hF hM₀ hX).IndCongr where
  map := by
    intro A C c hh s o o' hi
    refine ⟨fun hT => ?_, fun hT => by rw [hi.2 hT]⟩
    obtain ⟨u, u', hu, hu', hrel⟩ := hi.1 hT
    exact ⟨⟨u.i, _, Term.holeAt u.t hh⟩, ⟨u'.i, _, Term.holeAt u'.t hh⟩,
      cden_holeAt hM₀ hX u hu hh, cden_holeAt hM₀ hX u' hu' hh, hrel.holeAt hh⟩
  pair := by
    intro A C s a a' b b' ha hb
    refine ⟨fun hT => ?_, fun hT => by rw [ha.2 hT, hb.2 hT]⟩
    obtain ⟨u₁, u₁', h₁, h₁', r₁⟩ := ha.1 hT
    obtain ⟨u₂, u₂', h₂, h₂', r₂⟩ := hb.1 hT
    refine ⟨⟨max u₁.i u₂.i, _, Term.pair (u₁.lift _ (le_max_left _ _))
        (u₂.lift _ (le_max_right _ _))⟩,
      ⟨max u₁'.i u₂'.i, _, Term.pair (u₁'.lift _ (le_max_left _ _))
        (u₂'.lift _ (le_max_right _ _))⟩, ?_, ?_, Canon.DTerm.Rel.pair r₁ r₂ _ _ _ _ _ _⟩
    · exact Prod.ext ((cden_lift hX (le_max_left u₁.i u₂.i) u₁.t).trans h₁)
        ((cden_lift hX (le_max_right u₁.i u₂.i) u₂.t).trans h₂)
    · exact Prod.ext ((cden_lift hX (le_max_left u₁'.i u₂'.i) u₁'.t).trans h₁')
        ((cden_lift hX (le_max_right u₁'.i u₂'.i) u₂'.t).trans h₂')

/-! ## From the far world to here -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem compsBase_sig {Δ : Ctx} {A : VarType} (cs : List (List Step))
    {p q : Σ b, Term σ Δ (A.compsFlat cs) b} (h : p = q) :
    compsBase cs p.2 = compsBase cs q.2 := by
  subst h
  rfl

/-- ⭐⭐**Truth at the far end is a returning possibility here** (T + 4, strong B), along either leg,
    at a boxed object with companions.  The object's packing has a home term, kept to the far world
    as itself (`FarKept`).  There the body is true, so in the theory, and the ties are theorems
    (`packTies_tm`); `FarLeg.dia_of` brings both home, and `Proof.retC_unlift` makes them a
    returning possibility, its value the kept term read here. -/
theorem ret_core (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (s : GW hF M₀) (I : ℕ) (O : OutLeg (ctxOf (glat s I))) (a : O.Arr (ccanonEnv hM₀ hX s I))
    (F : FarLeg hM₀ hX s I O a) {A : VarType} {cs : List (List Step)} (h : A.CompOk cs) {K : ℕ}
    {e₀ : Ann A} (E₀ : Term σ (ctxOf (glat (O.acc (ccanonEnv hM₀ hX s I) a).1 K)).boxIn A e₀)
    {b₀ : Ann (A.compsFlat cs)} (bk : Term σ (ctxOf (glat s I)).boxIn (A.compsFlat cs) b₀)
    (hk : FarKept hM₀ F bk (compsVal E₀ cs h).2)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (hΦ : (cmodel hF hM₀ hX).sat ((O.push (ccanonEnv hM₀ hX s I) a).extend (.bnd 0)
      (ctoDom hM₀ hX _ _ (cden hM₀ hX _ K (Ctx.Le.refl _) (.boxtm E₀))
        (cdefinable_den hX _ _))) Φ)
    (IH : ∀ ψ : WFF σ (ctxOf (glat (O.acc (ccanonEnv hM₀ hX s I) a).1 F.L)) 0,
      ψ.size ≤ Φ.size → ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX _ F.L) ψ ↔
        ψ ∈ (gw hM₀ (O.acc (ccanonEnv hM₀ hX s I) a).1).M F.L)) :
    O.retS hS (.nec (.boxC A cs h)) (Term.collapse (Ctx.collapses_boxIn_self hT _) bk) Φ ∈
      (gw hM₀ s).M I := by
  obtain ⟨L', hL, hK, hkept⟩ := hk
  let v := (O.acc (ccanonEnv hM₀ hX s I) a).1
  let s₀ := Term.mono O.le_view.boxIn (Term.shift (Ctx.shifts_boxIn_boxIn hF _) bk)
  let c := (compsVal E₀ cs h).2
  have hs' : (⟨_, Term.mono (gle hM₀ v hL).boxIn (F.C.box.app s₀).2⟩ : Σ e, Term σ _ _ e) =
      ⟨_, Term.mono (gle hM₀ v hK).boxIn c⟩ :=
    sig_boxtm_inj ((sig_mono (gle hM₀ v hL) (GTr.app_boxtm F.C s₀)).symm.trans hkept)
  have hbase : (⟨_, Term.mono (gle hM₀ v hL).boxIn (compsBase cs (F.C.box.app s₀).2).2⟩ :
      Σ e, Term σ _ A e) = ⟨_, Term.mono (gle hM₀ v hK).boxIn E₀⟩ :=
    (app_compsBase (.mono (gle hM₀ v hL).boxIn (.nil _)) cs (F.C.box.app s₀).2).trans
      ((compsBase_sig cs hs').trans
        ((app_compsBase (.mono (gle hM₀ v hK).boxIn (.nil _)) cs c).symm.trans
          (sig_mono _ (compsBase_compsVal E₀ cs h))))
  let bs := (compsBase cs s₀).2
  have hB : F.C.app (.boxtm bs) = ⟨_, .boxtm (compsBase cs (F.C.box.app s₀).2).2⟩ :=
    (GTr.app_boxtm F.C bs).trans (sig_boxtm (app_compsBase F.C.box cs s₀))
  have hB' : (⟨_, Term.mono (gle hM₀ v hL) (F.C.app (.boxtm bs)).2⟩ : Σ e, Term σ _ _ e) =
      ⟨_, .boxtm (Term.mono (gle hM₀ v hK).boxIn E₀)⟩ :=
    (sig_mono _ hB).trans (sig_boxtm hbase)
  have hval : Model.interp (O.push (ccanonEnv hM₀ hX s I) a) (.boxtm bs) =
      ctoDom hM₀ hX _ _ (cden hM₀ hX _ K (Ctx.Le.refl _) (.boxtm E₀)) (cdefinable_den hX _ _) := by
    rw [interp_ctr hX (.boxtm bs) F.C F.ag F.npl O.noProjLast]
    refine ctoDom_congr hX ?_ _ _
    exact (cden_lift hX hL (F.C.app (.boxtm bs)).2).symm.trans
      ((cden_sigma hX _ hB').trans (cden_lift hX hK (.boxtm E₀)))
  have hd : O.dia (WFF.instantiate Ctx.NoSlots.slots (.boxtm s₀)
      (WFF.packedBody (N := .boxC A cs h) hS hF Φ)) ∈ (gw hM₀ s).M I := by
    rw [WFF.instantiate_packedBody_boxC hS hF h Φ s₀]
    refine F.dia_of _ ?_
    rw [F.trW_and, ((gw hM₀ v).mcs _).and_mem_iff]
    constructor
    · refine (IH _ ?_).mp ((F.sat_trW _).mp ((Model.sat_instantiate _ O.noProjLast _ _ Φ).mpr ?_))
      · rw [F.size_trW, WFF.size_instantiate]
      · rw [hval]
        exact hΦ
    · rw [F.trW_hole]
      have hT' : (⟨_, Term.mono (gle hM₀ v hL)
          (F.C.app (Term.pair (.boxtm bs) (.boxtm s₀))).2⟩ : Σ e, Term σ _ _ e) =
          ⟨_, Term.pair (.boxtm (Term.mono (gle hM₀ v hK).boxIn E₀))
            (.boxtm (Term.mono (gle hM₀ v hK).boxIn c))⟩ := by
        rw [GTr.app_pair]
        exact sig_pair hB' hkept
      obtain ⟨hth⟩ := packTies_tm (Γ := ctxOf (glat v K)) (Δ := []) hS hT hF cs h E₀
      have h1 := (gw hM₀ v).mem_of_provable (Δ := []) (fun _ hψ => by cases hψ) ⟨hth⟩
      have h2 := (BWorld.mem_lift hK).mp h1
      rw [WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots] at h2
      refine (BWorld.mem_lift hL).mpr ?_
      rw [WFF.mono_holeAt _ Ctx.NoSlots.slots Ctx.NoSlots.slots]
      exact (congrArg (· ∈ _) (WFF.holeAt_congr Ctx.NoSlots.slots hT' _)).mpr h2
  have hc : (ctxOf (glat s I)).RootFresh (.free (glat s I).length) := ctxOf_fresh le_rfl
  exact (gw hM₀ s).mem_of_provable (Δ := [_]) (fun ψ hψ => by
      rw [List.mem_singleton.mp hψ]
      exact hd)
    ⟨Proof.retC_unlift hS hT hF O h bk _ Φ _ hc _ (OutLeg.rootFresh hc O)
      (Proof.conv (OutLeg.back_congr hS .nec (congrArg (Sigma.mk _) (Term.mono_refl _ _)) rfl)
        (Proof.back_keep hS hT hF .nec bk (Proof.dia_top hT)))
      (Proof.lookup List.mem_cons_self)⟩

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- An arrow of a witness's extent, and what holds along it, at a later context. -/
theorem sat_diaPush_lift {M : Model σ} {Γ Γ' : Ctx} (h : Γ.Le Γ') {w : M.frame.W}
    {env : M.Env Γ w} {env' : M.Env Γ' w} (hag : Model.Env.Agree h env env') {y : VarSymb}
    {X X' : VarType} (h₁ : Γ.ref y = some (.VTypeDia X)) (h₂ : Γ'.ref y = some (.VTypeDia X'))
    (a₁ : (M.posEval (env.ref y h₁)).1) {T : VarType} (e : M.frame.Dom T a₁.1.1)
    (Φ : WFF σ ((Γ.diaIn y).insert (.bnd 0) T) 1)
    (hΦ : M.sat ((env.diaPush y h₁ a₁).extend (.bnd 0) e) Φ) :
    ∃ hm : a₁.1 ∈ (M.posEval (env'.ref y h₂)).1,
      M.sat ((env'.diaPush y h₂ ⟨a₁.1, hm⟩).extend (.bnd 0) e)
        (WFF.mono ((h.diaIn y).insert (.bnd 0) T) Φ) := by
  obtain rfl : X = X' := by
    have e' := (h.ref h₁).symm.trans h₂
    simpa using e'
  have href := Model.Env.ref_agree hag y h₁
  have hm : a₁.1 ∈ (M.posEval (env'.ref y h₂)).1 := by
    rw [← href]
    exact a₁.2
  exact ⟨hm, (Model.sat_mono (Model.Env.extend_agree (Model.Env.diaPush_agree hag h₁ a₁ hm)
    (.bnd 0) e) Φ).mpr hΦ⟩

/-- `ret_core` at a later stage, for either leg. -/
theorem ret_lift_core (hX : CluFlags) (hS : ModalSys.BStrong = true) (hT : ModalSys.T = true)
    (s : GW hF M₀) {i I : ℕ} (hiI : i ≤ I) (O : OutLeg (ctxOf (glat s i)))
    (a : O.Arr (ccanonEnv hM₀ hX s i)) {A : VarType} {cs : List (List Step)} (h : A.CompOk cs)
    {K : ℕ} {e₀ : Ann A}
    (E₀ : Term σ (ctxOf (glat (O.acc (ccanonEnv hM₀ hX s i) a).1 K)).boxIn A e₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s)
      (rstg (O.acc (ccanonEnv hM₀ hX s i) a).1 K) ≤ I)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (hΦ : (cmodel hF hM₀ hX).sat ((O.push (ccanonEnv hM₀ hX s i) a).extend (.bnd 0)
      (ctoDom hM₀ hX _ _ (cden hM₀ hX _ K (Ctx.Le.refl _) (.boxtm E₀))
        (cdefinable_den hX _ _))) Φ)
    (IH : ∀ (L : ℕ) (ψ : WFF σ (ctxOf (glat (O.acc (ccanonEnv hM₀ hX s i) a).1 L)) 0),
      ψ.size ≤ Φ.size → ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX _ L) ψ ↔
        ψ ∈ (gw hM₀ (O.acc (ccanonEnv hM₀ hX s i) a).1).M L)) :
    (O.mono (gle hM₀ s hiI)).retS hS (.nec (.boxC A cs h))
      (Term.collapse (Ctx.collapses_boxIn_self hT _) (Term.mono (gle hM₀ s hJI).boxIn
        (homeT hM₀ hX s _ (compsVal E₀ cs h).2).2))
      (WFF.mono ((OutLeg.le_view_mono (gle hM₀ s hiI) O).insert (.bnd 0) _) Φ) ∈
      (gw hM₀ s).M I := by
  cases O with
  | nec =>
      exact ret_core hM₀ hX hS hT s I .nec a (farNec hM₀ hX hT s I a) h E₀ _
        (kept_nec hM₀ hX hT s I a _ hJI) _
        ((Model.sat_mono (Model.Env.extend_agree (Model.Env.boxPush_agree
          (ccanonEnv_le hX s hiI) a) (.bnd 0) _) Φ).mpr hΦ)
        (fun ψ hψ => IH _ ψ (by rwa [WFF.size_mono] at hψ))
  | pos y hy =>
      have hy' : ∃ Y, (ctxOf (glat s I)).ref y = some (.VTypeDia Y) :=
        hy.imp fun _ e => (gle hM₀ s hiI).ref e
      obtain ⟨hm, hΦ'⟩ := sat_diaPush_lift (gle hM₀ s hiI) (ccanonEnv_le hX s hiI)
        hy.choose_spec hy'.choose_spec a _ Φ hΦ
      exact ret_core hM₀ hX hS hT s I (.pos y hy') ⟨a.1, hm⟩ (farPos hM₀ hX hT s I hy' ⟨a.1, hm⟩) h
        E₀ _ (kept_pos hM₀ hX hT s I hy' ⟨a.1, hm⟩ _ hJI) _ hΦ'
        (fun ψ hψ => IH _ ψ (by rwa [WFF.size_mono] at hψ))

/-- What a kept home term of a packing reads as here: the packed object's readings home. -/
theorem comps_home (hX : CluFlags) (hT : ModalSys.T = true) (s v : GW hF M₀)
    (r : (cframe hF hM₀ hX).R v s) {A : VarType} {cs : List (List Step)} (h : A.CompOk cs) {K I : ℕ}
    {e₀ : Ann A} (E₀ : Term σ (ctxOf (glat v K)).boxIn A e₀)
    (hJI : pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K) ≤ I) :
    (cmodel hF hM₀ hX).compsRead A cs h
        (ctoDom hM₀ hX _ _ (cden hM₀ hX v K (Ctx.Le.refl _) (.boxtm E₀)) (cdefinable_den hX _ _))
        r =
      ctoDom hM₀ hX _ s (cden hM₀ hX s I (Ctx.Le.refl _) (Term.collapse
        (Ctx.collapses_boxIn_self hT _) (Term.mono (gle hM₀ s hJI).boxIn
          (homeT hM₀ hX s v (compsVal E₀ cs h).2).2))) (cdefinable_den hX _ _) := by
  have hR : CR s := (carrows hF M₀).refl hT s
  rw [← interp_ccanon hX (.boxtm E₀) (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
    ← Model.interp_compsVal (ccanonEnv hM₀ hX v K) E₀ s r cs h,
    ← Model.box_beta (ccanonEnv hM₀ hX v K) (compsVal E₀ cs h).2 ⟨s, ⟨r⟩⟩,
    interp_ccanon hX (.boxtm (compsVal E₀ cs h).2) (Model.Env.Agree.refl' _)
      (Ctx.Presented.noProjLast _)]
  refine ctoDom_congr hX ?_ _ _
  exact (congrFun (cden_home hM₀ hX s v hJI (compsVal E₀ cs h).2).symm ⟨s, ⟨hR⟩⟩).trans
    (cden_boxtm_own hX hT s I _ hR)

/-- ⭐⭐**A true returning possibility of a necessary shape is in the theory** (strong B), along
    either leg (`BData.mem_ret_of_sat_nec`, with no network).  The object out there is packed
    (`packG`) and `ret_lift_core` makes a returning possibility of the packing here; `ret_map`
    along `unpackG` gives the shape back, and the value moves to `t` (`mem_ret_of_indC`). -/
theorem mem_ret_of_satN (hX : CluFlags) (hS : ModalSys.BStrong = true) {s : GW hF M₀} {i : ℕ}
    (O : OutLeg (ctxOf (glat s i))) (N : NShape) {a : Ann N.flat}
    (t : Term σ (ctxOf (glat s i)) N.flat a) (Φ : WFF σ (O.view.insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : GW hF M₀) (K : ℕ) (φ : WFF σ (ctxOf (glat s' K)) 0),
      φ.size < Φ.size + N.flat.eqRecSize + 1 →
        ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s' K) φ ↔ φ ∈ (gw hM₀ s').M K))
    (hsat : (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) (O.retS hS (.nec N) t Φ : WFF σ _ 0)) :
    (O.retS hS (.nec N) t Φ : WFF σ _ 0) ∈ (gw hM₀ s).M i := by
  have hT := hX.bT hS
  obtain ⟨a₀, e, hΦ, r, hr⟩ := (OutLeg.sat_retS (M := cmodel hF hM₀ hX) (d := 0) hS
    (ccanonEnv hM₀ hX s i) O (.nec N) t Φ).mp hsat
  obtain ⟨K, e₀, g, hg⟩ := cdefinable_fromDom hM₀ hX N.ty _ e
  obtain ⟨_, E₀, hE⟩ := exists_boxtm (A := N.packTy)
    ⟨_, Term.holeAt g (packG (σ := σ) N).obj.2⟩
  let v := (O.acc (ccanonEnv hM₀ hX s i) a₀).1
  have hge : Model.interp (ccanonEnv hM₀ hX v K) g = e := by
    rw [interp_ccanon hX g (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
    exact (ctoDom_congr hX hg _ _).trans (ctoDom_fromDom hM₀ hX N.ty _ e)
  have hep : ctoDom hM₀ hX _ _ (cden hM₀ hX v K (Ctx.Le.refl _) (.boxtm E₀))
      (cdefinable_den hX _ _) = (cmodel hF hM₀ hX).holeVal (packG (σ := σ) N).obj.2 e := by
    rw [← interp_ccanon hX (.boxtm E₀) (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
      ← hge, ← Model.interp_holeAt]
    exact (congrArg (fun x => Model.interp (ccanonEnv hM₀ hX v K) x.2) hE).symm
  have hup : (cmodel hF hM₀ hX).holeVal (unpackG (σ := σ) N).obj.2
      ((cmodel hF hM₀ hX).holeVal (packG (σ := σ) N).obj.2 e) = e := by
    rw [← hge, ← Model.interp_holeAt, ← Model.interp_holeAt]
    exact congrArg (fun x => Model.interp (ccanonEnv hM₀ hX v K) x.2)
      (holeAt_packG_unpackG N g)
  let Φ₁ := WFF.bodyRepl (Term.mono ((Ctx.empty_le O.view).insert (.bnd 0) _)
    (unpackG (σ := σ) N).obj.2) Φ
  have hΦ₁ : (cmodel hF hM₀ hX).sat ((O.push (ccanonEnv hM₀ hX s i) a₀).extend (.bnd 0)
      (ctoDom hM₀ hX _ _ (cden hM₀ hX v K (Ctx.Le.refl _) (.boxtm E₀))
        (cdefinable_den hX _ _))) Φ₁ := by
    refine (Model.sat_bodyRepl O.noProjLast _ _ Φ _).mpr ?_
    rw [Model.interp_mono (Model.Env.extend_agree (h := Ctx.empty_le O.view)
      (env := Model.Env.empty _) (env' := O.push (ccanonEnv hM₀ hX s i) a₀)
      (fun _ _ h => nomatch h) (.bnd 0) _), hep]
    rw [show Model.interp _ _ = _ from hup]
    exact hΦ
  let J := pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg v K)
  have hiI : i ≤ max i J := le_max_left _ _
  have hJI : J ≤ max i J := le_max_right _ _
  have hsz : Φ₁.size = Φ.size := WFF.size_subst _ _ _ _ _ _
  have hcore := ret_lift_core hM₀ hX hS hT s hiI O a₀ N.packOk E₀ hJI Φ₁ hΦ₁
    (fun L ψ hψ => IH _ L ψ (by omega))
  let V := Term.collapse (Ctx.collapses_boxIn_self hT _) (Term.mono (gle hM₀ s hJI).boxIn
    (homeT hM₀ hX s v (compsVal E₀ N.packComps N.packOk).2).2)
  let O' := O.mono (gle hM₀ s hiI)
  let Φ' := WFF.mono ((OutLeg.le_view_mono (gle hM₀ s hiI) O).insert (.bnd 0) N.ty) Φ
  have hmap : O'.retS hS (.nec N) (Term.holeRead V (unpackG (σ := σ) N).val.2) Φ' ∈
      (gw hM₀ s).M (max i J) := by
    refine (gw hM₀ s).mem_of_provable (Δ := [_]) (fun ψ hψ => by
      rw [List.mem_singleton.mp hψ]
      exact hcore) ⟨Proof.ret_map hS O' (S := .nec N.packed) (T := N) (unpackG N) V Φ'
        (Proof.conv ?_ (Proof.lookup List.mem_cons_self))⟩
    refine congrArg (O'.retS hS (.nec N.packed) V) ?_
    refine (WFF.mono_bodyRepl (OutLeg.le_view_mono (gle hM₀ s hiI) O) _ Φ).trans ?_
    rw [Term.mono_mono]
    rfl
  have hb := Model.ShapeMap.comesBack (cindCongr hM₀ hX) (packG (σ := σ) N) e r _ hr
  rw [← hep] at hb
  have hI := Model.ind_compsRead (M := cmodel hF hM₀ hX) (cindCongr hM₀ hX).pair N.packTy _ r
    N.packComps N.packOk _ hb
  rw [comps_home hM₀ hX hT s v r N.packOk E₀ hJI] at hI
  have hI₂ := (cindCongr hM₀ hX).map (unpackG (σ := σ) N).val.2 hI
  have e₁ : (cmodel hF hM₀ hX).holeVal (unpackG (σ := σ) N).val.2
      (ctoDom hM₀ hX (N.packTy.compsFlat N.packComps) s
        (cden hM₀ hX s (max i J) (Ctx.Le.refl _) V) (cdefinable_den hX _ _)) =
      ctoDom hM₀ hX _ s (cden hM₀ hX s (max i J) (Ctx.Le.refl _)
        (Term.holeRead V (unpackG (σ := σ) N).val.2)) (cdefinable_den hX _ _) :=
    (congrArg ((cmodel hF hM₀ hX).holeVal (unpackG (σ := σ) N).val.2)
      (interp_ccanon hX V (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).symm).trans
      ((Model.interp_holeRead (Ctx.Presented.noProjLast _) _ V _).symm.trans
        (interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)))
  have e₂ : (cmodel hF hM₀ hX).holeVal (unpackG (σ := σ) N).val.2
      ((cmodel hF hM₀ hX).holeVal (packG (σ := σ) N).val.2
        (Model.interp (ccanonEnv hM₀ hX s i) t)) =
      ctoDom hM₀ hX _ s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _) := by
    rw [← Model.interp_holeAt, ← Model.interp_holeAt,
      ← interp_ccanon hX t (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
    exact congrArg (fun x => Model.interp (ccanonEnv hM₀ hX s i) x.2)
      (holeAt_packG_unpackG_val N t)
  rw [e₁, e₂] at hI₂
  exact mem_ret_of_indC (R := .nec N) hX hS hT hiI O _ t Φ
    (fun L _ u u' hs => (IH s L _ (by
      rw [WFF.size_eqRec]; change N.flat.eqRecSize < _; omega)).mp hs) hmap (hI₂.1 hT)

end GArrow

end V12M
