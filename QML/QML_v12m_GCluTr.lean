import QML.QML_v12m_GCluDom

/-!
# QML v12m — 5 on the growing tree: the path translation's round trip

`docs/v12-modal-extensions.md` §3 5, "Paper check: the path translation's round trip".  Under 4's
keep being the identity, a root term read along an arrow and back through the arrow end's
preimage must be the root term again.

* ⭐`sim_edge_nm`, `tr_edge`: along an edge, translating a shifted `□`-view term is renaming it
  by the names (`nm`), up to η — only the kept items' entries are read, and each names an
  address.  The mirror of `sim_pre_edge`.
* `pstgN_eq`: the two path stage functions agree.
* ⭐`tr_path`: along a path, translating a kept `□`-view term is renaming it by the path names.
* ⭐`cden_tr`: so a kept root term read along an arrow denotes what the root term does.
* The `◇` half: `sim_edge_nmX`, `tr_edgeX_body`, `tr_edgeX`, ⭐`tr_pathX`, ⭐`cden_trX` — the
  witness's image is the name of the kept witness (`idx_names`).
* ⭐`tr_pathXK`, ⭐`pTrXK_pre`: a world's possible term read at the root and kept back along the
  world's path is the term, so a content at the world's own arrow is the realisation
  (`cden_own_mem`, `cden_own_content`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- The names along an edge depend only on the child's node. -/
theorem nm_congr {t t' : GW hF M₀} (e : t.1 = t'.1) : nm t = nm t' := by
  funext v
  unfold nm
  rw [e]

/-- The two path stage functions agree. -/
theorem pstgN_eq : ∀ (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (i : ℕ),
    pstgN P s t h i = pstg s t P h i
  | [], _, _, _, _ => rfl
  | [c], s, t, h, i =>
      congrArg (fun w => glstg s w i) (gw_eq (s := t) (t := stepW s c (born_step h)) h.symm)
  | c :: c' :: P, s, t, h, i =>
      pstgN_eq (c' :: P) (stepW s c (born_step h)) t h (glstg s (stepW s c (born_step h)) i)

/-- The names of an edge keep the type of every reachable keepable address. -/
theorem nm_ok (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t)
    (i : ℕ) : ∀ z T, (ctxOf (glat s i)).ref z = some T → T.keepable = true →
      (ctxOf (glat t (glstg s t i))).ref (nm t z) = some T :=
  fun z _ hz hkp => names_ref' hM₀ h hz hkp (nm_spec hX.five t z)

/-- ⭐**Along an edge, the edge read through 4's shift is renaming by the names**, up to η: an
    item `u.box` or `u.keep` reads the entry of `u.keep`, which names `nm t u`. -/
theorem sim_edge_nm (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀}
    (h : GCh hF M₀ s t) (i : ℕ) :
    Subst.Sim (ctxOf (glat s i)).boxIn (Subst.atShift (edgeBox s t i))
      (eS σ (ctxOf (glat t (glstg s t i))).boxIn (ofRen (preI (nm t)))) := by
  refine Subst.sim_of fun v T hl hv => ?_
  obtain ⟨u, st, rfl, -, -⟩ := boxIn_item hv
  rw [show eS σ (ctxOf (glat t (glstg s t i))).boxIn (ofRen (preI (nm t))) (.step u st) =
    .ren (preI (nm t) (.step u st)) from eS_item _ hl]
  change SubE.Sim T ((edgeBox s t i).at (VarSymb.shift 0 (.step u st))) _
  have hn := nm_spec hX.five t u
  match st, hv with
  | .box, hv =>
      obtain ⟨hk, hz⟩ := Ctx.boxIn_box hv
      rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
      change SubE.Sim T (((eS σ _ (fmapL hF M₀ t.1)).at (.step u .keep)).unbox)
        (.ren (.step (nm t u) .box))
      rw [Subst.at_nonproj _ rfl, eS_item _ rfl]
      rcases hn with he | ⟨L, U, hz', he⟩
      · rw [he]
        change SubE.Sim T (.ren (nm t u).inner) _
        rw [VarSymb.inner_box hk]
        exact .refl _
      · obtain ⟨rfl, hz'', e⟩ := entOf_names_tm hM₀ h i hz rfl hz' he
        rw [e]
        change SubE.Sim T (.tm (Term.eta (nm t u).inner T (Ctx.ref_inner hz''))) _
        generalize Ctx.ref_inner hz'' = hp
        revert hp
        rw [VarSymb.inner_box hk]
        exact fun hp => .eta_ren _ hp
  | .keep, hv =>
      obtain ⟨hF', hz, hkp⟩ := Ctx.boxIn_keep hv
      rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
      change SubE.Sim T (((eS σ _ (fmapL hF M₀ t.1)).at (.step u .keep)).keepE)
        (.ren (.step (nm t u) .keep))
      rw [Subst.at_nonproj _ rfl, eS_item _ rfl]
      rcases hn with he | ⟨L, U, hz', he⟩
      · rw [he]
        exact .refl _
      · obtain ⟨rfl, hz'', e⟩ := entOf_names_tm hM₀ h i hz hkp hz' he
        rw [e]
        exact keepE_eta_sim hF' hz'' hkp
  | .fst, hv => cases hv
  | .snd, hv => cases hv
  | .dia, hv => cases hv
  | .here, hv => cases hv

/-- ⭐**Along an edge, translating a shifted `□`-view term is renaming it by the names.** -/
theorem tr_edge (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t)
    (i : ℕ) {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat s i)).boxIn A a) :
    (⟨_, Term.subst (eIdx (fmapL hF M₀ t.1)) (edgeBox s t i) (ok_edgeBox hM₀ h i)
        (coh_edgeBox hM₀ h i) (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)⟩ :
        Σ c, Term σ (ctxOf (glat t (glstg s t i))).boxIn A c) =
      ⟨_, Term.subst (eIdx (ofRen (preI (nm t))))
        (eS σ (ctxOf (glat t (glstg s t i))).boxIn (ofRen (preI (nm t))))
        (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI (nm_ok hX hM₀ h i))))
        (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI (nm_ok hX hM₀ h i))))
        b⟩ :=
  (Term.subst_shift (Ctx.shifts_boxIn_boxIn hF _) _ _ _ (Subst.atShift (edgeBox s t i))
    (Subst.ok_atShift (Ctx.shifts_boxIn_boxIn hF _) (ok_edgeBox hM₀ h i))
    (Subst.coh_atShift (Ctx.shifts_boxIn_boxIn hF _) (ok_edgeBox hM₀ h i)
      (coh_edgeBox hM₀ h i) (levels_boxIn _))
    (Subst.preShift_atShift _ _) b).trans
  (Term.subst_congr _ _ _ _ _ _ (sim_edge_nm hX hM₀ h i) b)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem sig_subst_cong {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {T : VarType} {a a' : Ann T}
    {x : Term σ Γ T a} {y : Term σ Γ T a'} (e : (⟨a, x⟩ : Σ c, Term σ Γ T c) = ⟨a', y⟩) :
    (⟨_, Term.subst ι θ hθ hc x⟩ : Σ c, Term σ Δ T c) = ⟨_, Term.subst ι θ hθ hc y⟩ := by
  cases e
  rfl

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem sig_shift_cong {k : ℕ} {Γ Γ' : Ctx} (C : Ctx.Shifts k Γ Γ') {T : VarType}
    {a a' : Ann T} {x : Term σ Γ T a} {y : Term σ Γ T a'}
    (e : (⟨a, x⟩ : Σ c, Term σ Γ T c) = ⟨a', y⟩) :
    (⟨_, Term.shift C x⟩ : Σ c, Term σ Γ' T c) = ⟨_, Term.shift C y⟩ := by
  cases e
  rfl

/-- The path names keep the type of every reachable keepable address, at the path's stage. -/
theorem pnm_ok (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (P : List ℕ) (s t : GW hF M₀)
    (h : t.1 = nodeOf s.1 P) (i : ℕ) :
    ∀ z T, (ctxOf (glat s i)).ref z = some T → T.keepable = true →
      (ctxOf (glat t (pstg s t P h i))).ref (pnm P s t h z) = some T :=
  fun z T hz hkp => pstgN_eq P s t h i ▸ pnm_ref hX.five hM₀ P s t h i z T hz hkp

/-- ⭐**Along a path, translating a kept `□`-view term is renaming it by the path names.**  By
    induction on the path: the edge is `tr_edge`; at a step, 4's shift commutes with the edge's
    `□` lift (`Term.shift_shift_same`, `Subst.shiftCorr_box_box`), so what goes on along the
    rest is again a kept term. -/
theorem tr_path (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ)
      {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat s i)).boxIn A a),
      pTr hM₀ s t P h hP i (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)) =
        ⟨_, Term.boxtm (Term.subst (eIdx (ofRen (preI (pnm P s t h))))
          (eS σ (ctxOf (glat t (pstg s t P h i))).boxIn (ofRen (preI (pnm P s t h))))
          (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI
            (pnm_ok hX hM₀ P s t h i))))
          (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI
            (pnm_ok hX hM₀ P s t h i)))) b)⟩
  | [], s, t, h, hP, i, _, _, b => by
      have hT := hP.T_of_nil
      obtain rfl : t = s := gw_eq h
      have e₁ := sig_boxtm ((Term.collapse_shift_self (m := 0)
        (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat t i)))
        (Ctx.collapses_boxIn_self hT (ctxOf (glat t i))).boxIn (Ctx.Le.refl _) b).trans
        (congrArg (Sigma.mk _) (Term.mono_refl _ b)))
      change (⟨_, Term.mono (glat_le_of_eq h i) (Term.collapse
        (Ctx.collapses_boxIn_self hT (ctxOf (glat t i)))
        (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)))⟩ : Σ c, Term σ _ _ c) = _
      rw [Term.mono_refl]
      exact e₁.trans (sig_boxtm (subst_preI_id _ _ _).symm)
  | [c], s, t, h, _, i, _, _, b => by
      refine (sig_boxtm (tr_edge hX hM₀ (s := s) (t := t) ⟨c, h⟩ i b)).trans
        (sig_boxtm (Term.subst_congr _ _ _ _ _ _ ?_ b))
      have e : pnm [c] s t h = nm t := by
        funext v
        exact congrFun (nm_congr (t := stepW s c (born_step h)) (t' := t) h.symm) v
      rw [e]
      exact fun _ _ _ => .refl _
  | c :: c' :: P, s, t, h, _, i, A, _, b => by
      have hch : GCh hF M₀ s (stepW s c (born_step h)) := ⟨c, rfl⟩
      have key : (⟨_, Term.subst (eIdx (fmapL hF M₀ (c :: s.1)))
            (edgeBox s (stepW s c (born_step h)) i) (ok_edgeBox hM₀ hch i)
            (coh_edgeBox hM₀ hch i) (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
              (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b)))⟩ :
            Σ e, Term σ ((ctxOf (glat (stepW s c (born_step h))
              (glstg s (stepW s c (born_step h)) i))).kView none) (.VTypeBox A) e) =
          ⟨_, Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
            (Term.subst (eIdx (ofRen (preI (nm (stepW s c (born_step h))))))
              (eS σ (ctxOf (glat (stepW s c (born_step h))
                (glstg s (stepW s c (born_step h)) i))).boxIn
                (ofRen (preI (nm (stepW s c (born_step h))))))
              (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI
                (nm_ok hX hM₀ hch i))))
              (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI
                (nm_ok hX hM₀ hch i)))) b))⟩ := by
        refine sig_boxtm ?_
        refine (sig_subst_cong _ _ _ (Term.shift_shift_same _
          (Ctx.shifts_boxIn_boxIn hF (ctxOf (glat s i)).boxIn) _ b).symm).trans ?_
        refine (Term.shift_subst (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF _)
          (edgeBox s (stepW s c (born_step h)) i) (ok_edgeBox hM₀ hch i) (coh_edgeBox hM₀ hch i)
          _ _ _ (Subst.shiftCorr_box_box hF (ok_eS_kView (gentOk_box hM₀ hch i)))
          _).symm.trans ?_
        exact sig_shift_cong _ (tr_edge hX hM₀ hch i b)
      refine (pTr_sigma hM₀ _ t (c' :: P) h pathOk_cons _ key).trans ?_
      refine (tr_path hX hM₀ (c' :: P) (stepW s c (born_step h)) t h pathOk_cons _ _).trans ?_
      refine sig_boxtm (Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
        fun u st _ hst _ => ?_) b)
      obtain ⟨u', e⟩ := preI_step (nm (stepW s c (born_step h))) u st
      exact ⟨u', st, e, hst, by rw [← e, preI_comp]; rfl⟩

/-- ⭐**The path translation's round trip** (`□`): a kept root term read along an arrow, at the
    arrow's end, denotes what the root term does — the translation is renaming by the names
    (`tr_path`), and a named root term denotes what it does (`cden_named_box`). -/
theorem cden_tr (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf (groot hF M₀).1 P) (hP : PathOk P) (i : ℕ) {A : VarType} {a : Ann A}
    (b : Term σ (ctxOf (glat (groot hF M₀) i)).boxIn A a) :
    cden hM₀ hX t (pstg (groot hF M₀) t P h i) (Ctx.Le.refl _)
        (pTr hM₀ (groot hF M₀) t P h hP i
          (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))).2 =
      cden hM₀ hX (groot hF M₀) i (Ctx.Le.refl _) (.boxtm b) := by
  obtain rfl : P = rpath t := nodeOf_inj (h.symm.trans (rpath_eq t))
  exact (cden_sigma hX _ (tr_path hX hM₀ _ _ t h hP i b)).trans
    (cden_named_box hX hM₀ t i _ (pnm_ok hX hM₀ _ _ t h i) b)

/-! ## Kept translations, and reading a world's own terms along its path -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem sig_collapse_cong {k : ℕ} {Γ Γ' : Ctx} (C : Ctx.Collapses k Γ Γ') {T : VarType}
    {a a' : Ann T} {x : Term σ Γ T a} {y : Term σ Γ T a'}
    (e : (⟨a, x⟩ : Σ c, Term σ Γ T c) = ⟨a', y⟩) :
    (⟨_, Term.collapse C x⟩ : Σ c, Term σ Γ' T c) = ⟨_, Term.collapse C y⟩ := by
  cases e
  rfl

theorem pTrK_sigma (hM₀ : Theory.IsMCS M₀) (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (i : ℕ) {A : VarType} {a a' : Ann A}
    {u : Term σ ((ctxOf (glat s i)).kView none) A a}
    {u' : Term σ ((ctxOf (glat s i)).kView none) A a'}
    (e : (⟨a, u⟩ : Σ b : Ann A, Term σ ((ctxOf (glat s i)).kView none) A b) = ⟨a', u'⟩) :
    pTrK hM₀ s t P h i u = pTrK hM₀ s t P h i u' := by
  cases e
  rfl

/-- ⭐**A kept translation along a path is renaming by the path names.** -/
theorem tr_pathK (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (i : ℕ) {A : VarType} {a : Ann A}
      (b : Term σ (ctxOf (glat s i)).boxIn A a),
      pTrK hM₀ s t P h i b =
        ⟨_, Term.subst (eIdx (ofRen (preI (pnm P s t h))))
          (eS σ (ctxOf (glat t (pstg s t P h i))).boxIn (ofRen (preI (pnm P s t h))))
          (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI
            (pnm_ok hX hM₀ P s t h i))))
          (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI
            (pnm_ok hX hM₀ P s t h i)))) b⟩
  | [], s, t, h, i, _, _, b => by
      obtain rfl : t = s := gw_eq h
      change (⟨_, Term.mono ((glat_le_of_eq h i).kView none) b⟩ : Σ c, Term σ _ _ c) = _
      rw [Term.mono_refl]
      exact (subst_preI_id _ _ _).symm
  | [c], s, t, h, i, _, _, b => by
      refine (tr_edge hX hM₀ (s := s) (t := t) ⟨c, h⟩ i b).trans
        (Term.subst_congr _ _ _ _ _ _ ?_ b)
      have e : pnm [c] s t h = nm t := by
        funext v
        exact congrFun (nm_congr (t := stepW s c (born_step h)) (t' := t) h.symm) v
      rw [e]
      exact fun _ _ _ => .refl _
  | c :: c' :: P, s, t, h, i, A, _, b => by
      have hch : GCh hF M₀ s (stepW s c (born_step h)) := ⟨c, rfl⟩
      refine (pTrK_sigma hM₀ _ t (c' :: P) h _ (tr_edge hX hM₀ hch i b)).trans ?_
      refine (tr_pathK hX hM₀ (c' :: P) (stepW s c (born_step h)) t h _ _).trans ?_
      refine Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
        fun u st _ hst _ => ?_) b
      obtain ⟨u', e⟩ := preI_step (nm (stepW s c (born_step h))) u st
      exact ⟨u', st, e, hst, by rw [← e, preI_comp]; rfl⟩

/-- The stage a path's origins read a stage at commits it again along the path. -/
theorem le_pstg_pstgO (hV : ModalSys.Five = true) (hS : ModalSys.fourL = true)
    (hW : ModalSys.fourLW = true) (hM₀ : Theory.IsMCS M₀) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (j : ℕ),
      j ≤ pstg s t P h (pstgO P s t h j)
  | [], _, _, _, _ => le_refl _
  | [c], s, ⟨k, hk⟩, h, j => by
      change k = c :: s.1 at h
      subst h
      exact (estg_spec hV hS hW hM₀ (t := stepW s c hk) ⟨c, rfl⟩ j).1
  | c :: c' :: P, s, t, h, j => by
      have hch : GCh hF M₀ s (stepW s c (born_step h)) := ⟨c, rfl⟩
      exact (le_pstg_pstgO hV hS hW hM₀ (c' :: P) (stepW s c (born_step h)) t h j).trans
        (pstg_monotone hM₀ _ t (c' :: P) h (estg_spec hV hS hW hM₀ hch _).1)

/-- ⭐**A world's `□`-view term, read at the root and kept back along the world's path, is the
    term**: the renaming is `rnm ∘ rorig`, which fixes every η-faithful item (`rnm_rorig`). -/
theorem pTrK_pre (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) {A : VarType}
    {a : Ann A} (b : Term σ (ctxOf (glat s i)).boxIn A a) :
    (⟨_, (pTrK hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) (rstg s i)
        (preTB hX hM₀ s i b).2).2⟩ :
        Σ c, Term σ (ctxOf (glat s (pstg (groot hF M₀) s (rpath s) (rpath_eq s)
          (rstg s i)))).boxIn A c) =
      ⟨a, Term.mono (gle hM₀ s (le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath s)
        (groot hF M₀) s (rpath_eq s) i)).boxIn b⟩ := by
  set K := pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg s i)
  have hiK : i ≤ K := le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath s)
    (groot hF M₀) s (rpath_eq s) i
  have hle := (gle hM₀ s hiK).boxIn
  have hrt : ∀ z T, (ctxOf (glat s i)).ref z = some T → T.keepable = true →
      (ctxOf (glat s K)).ref ((rnm s ∘ rorig s) z) = some T := fun z T hz hkp =>
    pnm_ok hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg s i) _ T
      (rpre hX hM₀ s i z T hz hkp) hkp
  have e0 : (⟨_, (pTrK hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) (rstg s i)
        (preTB hX hM₀ s i b).2).2⟩ : Σ c, Term σ (ctxOf (glat s K)).boxIn A c) =
      ⟨_, Term.subst (eIdx (ofRen (preI (rnm s ∘ rorig s))))
        (eS σ (ctxOf (glat s K)).boxIn (ofRen (preI (rnm s ∘ rorig s))))
        (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hrt)))
        (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hrt))) b⟩ := by
    rw [tr_pathK hX hM₀]
    refine Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
      fun u st _ hst _ => ?_) b
    obtain ⟨u', e⟩ := preI_step (rorig s) u st
    exact ⟨u', st, e, hst, by rw [← e, preI_comp]⟩
  refine e0.trans ((Term.subst_congrF _ (Subst.idS σ _) _ (Subst.ok_idS_le hle) _
    (Subst.coh_idS_le hle) (Subst.simF_of fun v T hl hv hTe => ?_) b).trans
    (Term.subst_idS_mono hle _ _ b))
  match v, hl, hv with
  | .step u .box, hl, hv =>
      have hu := Ctx.boxIn_step_box hv
      rw [eS_item _ rfl]
      change SubE.Sim T (.ren (.step (rnm s (rorig s u)) .box)) (.ren _)
      rw [rnm_rorig hX.five hX.fourS hX.fourSW hM₀ s ⟨i, hu⟩ rfl hTe]
      exact .refl _
  | .step u .keep, hl, hv =>
      obtain ⟨-, hu, hkp⟩ := Ctx.boxIn_keep hv
      rw [eS_item _ rfl]
      change SubE.Sim T (.ren (.step (rnm s (rorig s u)) .keep)) (.ren _)
      rw [rnm_rorig hX.five hX.fourS hX.fourSW hM₀ s ⟨i, hu⟩ hkp hTe]
      exact .refl _
  | .root _, _, hv => cases hv
  | .step _ .fst, _, hv => cases hv
  | .step _ .snd, _, hv => cases hv
  | .step _ .dia, _, hv => cases hv
  | .step _ .here, _, hv => cases hv

/-- ⭐**Reading a world's `□`-view term at the world's own arrow is collapsing it** (T): the
    translation is its kept translation collapsed (`collapse_pTrK`), and the kept translation of
    the preimage is the term (`pTrK_pre`). -/
theorem cden_collapse (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (hT : ModalSys.T = true)
    (s : GW hF M₀) (i : ℕ) {P : List ℕ} (h : s.1 = nodeOf (groot hF M₀).1 P) (hP : PathOk P)
    {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat s i)).boxIn A a) :
    cden hM₀ hX s (pstg (groot hF M₀) s P h (rstg s i)) (Ctx.Le.refl _)
        (pTr hM₀ (groot hF M₀) s P h hP (rstg s i) (preTB hX hM₀ s i b).2).2 =
      cden hM₀ hX s i (Ctx.Le.refl _)
        (Term.collapse (Ctx.collapses_boxIn_self hT _) b) := by
  obtain rfl : P = rpath s := nodeOf_inj (h.symm.trans (rpath_eq s))
  set K := pstg (groot hF M₀) s (rpath s) h (rstg s i)
  have hiK : i ≤ K := le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath s)
    (groot hF M₀) s (rpath_eq s) i
  have e₀ := pTrK_pre hX hM₀ s i b
  have e₁ := (collapse_pTrK (hM₀ := hM₀) hT (groot hF M₀) s (rpath s) h hP (rstg s i)
    (preTB hX hM₀ s i b).2).symm
  refine (cden_sigma hX _ e₁).trans ?_
  refine (cden_sigma hX _ (sig_collapse_cong (Ctx.collapses_boxIn_self hT _) e₀)).trans ?_
  rw [Term.collapse_mono (Ctx.collapses_boxIn_self hT (ctxOf (glat s i)))
    (Ctx.collapses_boxIn_self hT _) _ (gle hM₀ s hiK), cden_mono]
  exact cden_congr hX _ _ _ _ _ _

/-! ## The `◇` half -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Substituting into a possible term, with the witness's image as a variable (its index is
    known only propositionally). -/
theorem sig_subst_diatm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (b : Term σ (Γ.diaIn x) A a) (y : VarSymb) (hy : ι x = y)
    (hyP : ∃ Y, Δ.ref y = some (.VTypeDia Y)) (p : Subst.Ok (Γ.diaIn x) (θ.dia x y))
    (q : Subst.Coh ι (Γ.diaIn x) (θ.dia x y)) :
    (⟨_, Term.subst ι θ hθ hc (.diatm x hx b)⟩ : Σ c, Term σ Δ (.VTypeDia A) c) =
      ⟨_, .diatm y hyP (Term.subst ι (θ.dia x y) p q b)⟩ := by
  subst hy
  rfl

/-- ⭐**Along an edge, the edge's `◇_{x.keep}` view read through `four_dia`'s shift is renaming
    by the names**, at the name of `x`: the mirror of `sim_preX_edge`. -/
theorem sim_edge_nmX (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀}
    (h : GCh hF M₀ s t) (i : ℕ) {x : VarSymb} {X : VarType}
    (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) :
    Subst.Sim ((ctxOf (glat s i)).diaIn x) (Subst.atShift (edgeDia s t i x (nm t x)))
      (eS σ ((ctxOf (glat t (glstg s t i))).diaIn (nm t x)) (ofRen (preIX (nm t) x))) := by
  have hn := nm_spec hX.five t x
  refine Subst.sim_of fun v T hl hv => ?_
  obtain ⟨u, st, rfl, -, -⟩ := kView_item (k := some x) hv
  rw [eS_item _ hl]
  generalize hvs : VarSymb.step u st = v at *
  change SubE.Sim T ((edgeDia s t i x (nm t x)).at (v.shift 0)) (.ren (preIX (nm t) x v))
  by_cases hvx : v = .step x .dia
  · subst hvx
    have hT : T = X := Option.some.inj (hv.symm.trans
      ((Ctx.ref_nonproj _ (v := .step x .dia) rfl).symm.trans (Ctx.ref_diaIn_of hx)))
    subst hT
    rw [show preIX (nm t) x (.step x .dia) = .step (nm t x) .dia from if_pos rfl,
      VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
    change SubE.Sim T (if VarSymb.step x .keep = .step x .keep then
      ((edgeS s t i).at (.step x .keep)).diaBody (nm t x) else .hide) _
    rw [if_pos rfl, Subst.at_nonproj _ rfl, edgeS, eS_item _ rfl]
    rcases hn with he | ⟨L, U, hz', he⟩
    · rw [he]
      exact .refl _
    · obtain ⟨rfl, hz'', e⟩ := entOf_names_tm hM₀ h i hx rfl hz' he
      rw [e]
      unfold Term.eta
      rw [SubE.diaBody_diatm]
      exact .eta_ren _ _
  · rw [show preIX (nm t) x v = preI (nm t) v from if_neg hvx]
    have hb := diaIn_boxIn_of_ne' hv hvx
    rw [Subst.dia_eq_box_mono (edgeS s t i) (.step x .keep) (nm t x) _ T
      (Ctx.shifts_boxIn_boxIn hF _ _ T ((Ctx.ref_nonproj _ hl).trans hb))]
    have H := sim_edge_nm hX hM₀ h i v T ((Ctx.ref_nonproj _ hl).trans hb)
    rw [Subst.at_nonproj (eS σ _ (ofRen (preI (nm t)))) hl, Subst.at_atShift] at H
    subst hvs
    rw [eS_item _ hl] at H
    exact H.mono _

/-- The body of a kept possible term, translated along an edge, is renamed by the names. -/
theorem tr_edgeX_body (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀}
    (h : GCh hF M₀ s t) (i : ℕ) {x : VarSymb} {X : VarType}
    (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (c : Term σ ((ctxOf (glat s i)).diaIn x) A a) :
    (⟨_, Term.subst (eIdx (fmapL hF M₀ t.1)) (edgeDia s t i x (nm t x))
        (ok_edgeDia hM₀ h i hx (nm_spec hX.five t x))
        (coh_edgeDia hM₀ h i hx (nm_spec hX.five t x))
        (Term.shift (Ctx.shifts_diaIn_keep hF _ x) c)⟩ :
        Σ e, Term σ ((ctxOf (glat t (glstg s t i))).diaIn (nm t x)) A e) =
      ⟨_, Term.subst (eIdx (ofRen (preIX (nm t) x)))
        (eS σ ((ctxOf (glat t (glstg s t i))).diaIn (nm t x)) (ofRen (preIX (nm t) x)))
        (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx (nm_ok hX hM₀ h i))))
        (coh_eS_kView (k := some x)
          (entOk_ofRen (itemOk_preIX hx (nm_ok hX hM₀ h i)))) c⟩ :=
  (Term.subst_shift (Ctx.shifts_diaIn_keep hF _ x) _ _ _
    (Subst.atShift (edgeDia s t i x (nm t x)))
    (Subst.ok_atShift (Ctx.shifts_diaIn_keep hF _ x)
      (ok_edgeDia hM₀ h i hx (nm_spec hX.five t x)))
    (Subst.coh_atShift (Ctx.shifts_diaIn_keep hF _ x)
      (ok_edgeDia hM₀ h i hx (nm_spec hX.five t x))
      (coh_edgeDia hM₀ h i hx (nm_spec hX.five t x)) (levels_diaIn _ _))
    (Subst.preShift_atShift _ _) c).trans
  (Term.subst_congr _ _ _ _ _ _ (sim_edge_nmX hX hM₀ h i hx) c)

/-- ⭐**Along an edge, translating a kept possible term is renaming it by the names**, at the
    name of its witness. -/
theorem tr_edgeX (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t)
    (i : ℕ) {x : VarSymb} {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (c : Term σ ((ctxOf (glat s i)).diaIn x) A a) :
    (⟨_, Term.subst (eIdx (fmapL hF M₀ t.1)) (edgeS s t i)
        (ok_eS_kView (gentOk_box hM₀ h i)) (coh_eS_kView (gentOk_box hM₀ h i))
        (.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
          (Term.shift (Ctx.shifts_diaIn_keep hF _ x) c))⟩ :
        Σ e, Term σ (ctxOf (glat t (glstg s t i))) (.VTypeDia A) e) =
      ⟨_, .diatm (nm t x) ⟨X, nm_ok hX hM₀ h i x _ hx rfl⟩
        (Term.subst (eIdx (ofRen (preIX (nm t) x)))
          (eS σ ((ctxOf (glat t (glstg s t i))).diaIn (nm t x)) (ofRen (preIX (nm t) x)))
          (ok_eS_kView (k := some x)
            (entOk_ofRen (itemOk_preIX hx (nm_ok hX hM₀ h i))))
          (coh_eS_kView (k := some x)
            (entOk_ofRen (itemOk_preIX hx (nm_ok hX hM₀ h i)))) c)⟩ :=
  (sig_subst_diatm _ _ _ _ _ (nm t x) (idx_names hM₀ h i hx (nm_spec hX.five t x))
    ⟨X, nm_ok hX hM₀ h i x _ hx rfl⟩ (ok_edgeDia hM₀ h i hx (nm_spec hX.five t x))
    (coh_edgeDia hM₀ h i hx (nm_spec hX.five t x))).trans
  (sig_diatm (tr_edgeX_body hX hM₀ h i hx c))

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A possible term renamed by equal maps is one term. -/
theorem sig_diatm_ren_congr {Γ Δ : Ctx} {x : VarSymb} {A : VarType} {a : Ann A}
    (c : Term σ (Γ.diaIn x) A a) :
    ∀ (f g : VarSymb → VarSymb) (_e : f = g)
      (hf : ∃ Y, Δ.ref (f x) = some (.VTypeDia Y)) (hg : ∃ Y, Δ.ref (g x) = some (.VTypeDia Y))
      (pf : Subst.Ok (Γ.diaIn x) (eS σ (Δ.diaIn (f x)) (ofRen (preIX f x))))
      (qf : Subst.Coh (eIdx (ofRen (σ := σ) (preIX f x))) (Γ.diaIn x)
        (eS σ (Δ.diaIn (f x)) (ofRen (preIX f x))))
      (pg : Subst.Ok (Γ.diaIn x) (eS σ (Δ.diaIn (g x)) (ofRen (preIX g x))))
      (qg : Subst.Coh (eIdx (ofRen (σ := σ) (preIX g x))) (Γ.diaIn x)
        (eS σ (Δ.diaIn (g x)) (ofRen (preIX g x)))),
      (⟨_, .diatm (f x) hf (Term.subst (eIdx (ofRen (preIX f x)))
          (eS σ (Δ.diaIn (f x)) (ofRen (preIX f x))) pf qf c)⟩ :
          Σ e, Term σ Δ (.VTypeDia A) e) =
        ⟨_, .diatm (g x) hg (Term.subst (eIdx (ofRen (preIX g x)))
          (eS σ (Δ.diaIn (g x)) (ofRen (preIX g x))) pg qg c)⟩ := by
  intro f g e _ _ _ _ _ _
  subst e
  rfl

/-- ⭐**Along a path, translating a kept possible term is renaming it by the path names**, at
    the path name of its witness.  The step as `tr_path`'s, with the `◇` views'
    correspondence (`Subst.shiftCorr_dia_keep`) and the kept witness's index
    (`Subst.coh_keep_dia`, `Subst.idx_box_keep_dia`), as `four_dia`'s substitution case. -/
theorem tr_pathX (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ)
      {x : VarSymb} {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
      {A : VarType} {a : Ann A} (c : Term σ ((ctxOf (glat s i)).diaIn x) A a),
      pTr hM₀ s t P h hP i (.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
          (Term.shift (Ctx.shifts_diaIn_keep hF _ x) c)) =
        ⟨_, .diatm (pnm P s t h x) ⟨X, pnm_ok hX hM₀ P s t h i x _ hx rfl⟩
          (Term.subst (eIdx (ofRen (preIX (pnm P s t h) x)))
            (eS σ ((ctxOf (glat t (pstg s t P h i))).diaIn (pnm P s t h x))
              (ofRen (preIX (pnm P s t h) x)))
            (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx
              (pnm_ok hX hM₀ P s t h i))))
            (coh_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx
              (pnm_ok hX hM₀ P s t h i)))) c)⟩
  | [], s, t, h, hP, i, x, X, hx, _, _, b => by
      have hT := hP.T_of_nil
      obtain rfl : t = s := gw_eq h
      have hsh := sig_diatm (hx := ⟨X, hx⟩) (hx' := ⟨X, hx⟩)
        ((Term.collapse_shift_self (m := 0) (Ctx.shifts_diaIn_keep hF (ctxOf (glat t i)) x)
          ((Ctx.collapses_boxIn_self hT (ctxOf (glat t i))).diaIn (.step x .keep))
          (Ctx.Le.refl _) b).trans (congrArg (Sigma.mk _) (Term.mono_refl _ b)))
      change (⟨_, Term.mono (glat_le_of_eq h i) (Term.collapse
        (Ctx.collapses_boxIn_self hT (ctxOf (glat t i))) (Term.diatm _ _ _))⟩ :
        Σ c, Term σ _ _ c) = _
      rw [Term.mono_refl]
      exact hsh.trans (sig_diatm (subst_preIX_id _ _ _).symm)
  | [c], s, t, h, _, i, x, X, hx, _, _, b => by
      refine (tr_edgeX hX hM₀ (s := s) (t := t) ⟨c, h⟩ i hx b).trans ?_
      exact sig_diatm_ren_congr b _ _
        (funext fun v => congrFun (nm_congr (t := t) (t' := stepW s c (born_step h)) h) v)
        _ _ _ _ _ _
  | c :: c' :: P, s, t, h, _, i, x, X, hx, A, _, b => by
      have hch : GCh hF M₀ s (stepW s c (born_step h)) := ⟨c, rfl⟩
      have hθ := ok_eS_kView (gentOk_box hM₀ hch i)
      have hc := coh_eS_kView (gentOk_box hM₀ hch i)
      have hxk : ((ctxOf (glat s i)).kView none).ref (.step x .keep) = some (.VTypeDia X) :=
        Ctx.boxIn_keep_of' hF hx rfl
      have hidx := idx_names hM₀ hch i hx (nm_spec hX.five _ x)
      have hy : eIdx (fmapL hF M₀ (c :: s.1)) (.step (.step x .keep) .keep) =
          .step (nm (stepW s c (born_step h)) x) .keep := by
        exact (Subst.coh_keep_dia hθ hc hxk).trans
          (congrArg (fun w => VarSymb.step w .keep) hidx)
      have hwk : ((eS σ (ctxOf (glat (stepW s c (born_step h))
          (glstg s (stepW s c (born_step h)) i))) (fmapL hF M₀ (c :: s.1))).box.at
            (.step (.step x .keep) .keep)).idxAlong [] =
          .step (nm (stepW s c (born_step h)) x) .keep := by
        exact (Subst.idx_box_keep_dia hF hθ hc hxk).trans
          (congrArg (fun w => VarSymb.step w .keep) hidx)
      have hxk' := Ctx.exists_keep_dia hF ⟨X, hxk⟩
      have p := Subst.ok_dia (Subst.ok_box hθ) hxk' hwk
      have q : Subst.Coh (eIdx (fmapL hF M₀ (c :: s.1)))
          (((ctxOf (glat s i)).kView none).boxIn.diaIn (.step (.step x .keep) .keep))
          ((eS σ (ctxOf (glat (stepW s c (born_step h))
            (glstg s (stepW s c (born_step h)) i))) (fmapL hF M₀ (c :: s.1))).box.dia
            (.step (.step x .keep) .keep) (.step (nm (stepW s c (born_step h)) x) .keep)) :=
        hy ▸ Subst.coh_dia (Subst.ok_box hθ) (Subst.coh_box hθ hc) hxk'
      have hnx := nm_ok hX hM₀ hch i x _ hx rfl
      have key : (⟨_, Term.subst (eIdx (fmapL hF M₀ (c :: s.1)))
            (edgeBox s (stepW s c (born_step h)) i) (ok_edgeBox hM₀ hch i)
            (coh_edgeBox hM₀ hch i) (Term.shift (Ctx.shifts_boxIn_boxIn hF _)
              (.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
                (Term.shift (Ctx.shifts_diaIn_keep hF _ x) b)))⟩ :
            Σ e, Term σ ((ctxOf (glat (stepW s c (born_step h))
              (glstg s (stepW s c (born_step h)) i))).kView none) (.VTypeDia A) e) =
          ⟨_, .diatm (.step (nm (stepW s c (born_step h)) x) .keep)
            (Ctx.exists_keep_dia hF ⟨X, hnx⟩)
            (Term.shift (Ctx.shifts_diaIn_keep hF _ (nm (stepW s c (born_step h)) x))
              (Term.subst (eIdx (ofRen (preIX (nm (stepW s c (born_step h))) x)))
                (eS σ ((ctxOf (glat (stepW s c (born_step h))
                  (glstg s (stepW s c (born_step h)) i))).diaIn
                    (nm (stepW s c (born_step h)) x))
                  (ofRen (preIX (nm (stepW s c (born_step h))) x)))
                (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx
                  (nm_ok hX hM₀ hch i))))
                (coh_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx
                  (nm_ok hX hM₀ hch i)))) b))⟩ := by
        refine (sig_subst_diatm _ _ _ _ _ _ hy (Ctx.exists_keep_dia hF ⟨X, hnx⟩) p q).trans ?_
        refine sig_diatm ?_
        refine (sig_subst_cong _ p q (Term.shift_shift_same
          (Ctx.shifts_diaIn_keep hF _ x)
          (Ctx.shifts_diaIn_keep hF ((ctxOf (glat s i)).kView none) (.step x .keep)) _
          b).symm).trans ?_
        refine (Term.shift_subst (Ctx.shifts_diaIn_keep hF _ (.step x .keep))
          (Ctx.shifts_diaIn_keep hF _ (nm (stepW s c (born_step h)) x))
          (edgeDia s (stepW s c (born_step h)) i x (nm (stepW s c (born_step h)) x))
          (ok_edgeDia hM₀ hch i hx (nm_spec hX.five _ x))
          (coh_edgeDia hM₀ hch i hx (nm_spec hX.five _ x)) _ p q
          (Subst.shiftCorr_dia_keep hF hθ ⟨X, hxk⟩ (hc _ _ hxk [] |>.trans hidx)) _).symm.trans ?_
        exact sig_shift_cong _ (tr_edgeX_body hX hM₀ hch i hx b)
      refine (pTr_sigma hM₀ _ t (c' :: P) h pathOk_cons _ key).trans ?_
      refine (tr_pathX hX hM₀ (c' :: P) (stepW s c (born_step h)) t h pathOk_cons _ hnx
        _).trans ?_
      refine sig_diatm (Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
        fun u st _ hst hv => ?_) b)
      have hcomp := preIX_comp (pnm (c' :: P) (stepW s c (born_step h)) t h)
        (nm (stepW s c (born_step h))) (v := .step u st) hst hv
      by_cases hvx : VarSymb.step u st = .step x .dia
      · have e : preIX (nm (stepW s c (born_step h))) x (.step u st) =
            .step (nm (stepW s c (born_step h)) x) .dia := by
          unfold preIX
          rw [if_pos hvx]
        exact ⟨_, .dia, e, rfl, by rw [← e, hcomp]; rfl⟩
      · obtain ⟨u', e'⟩ := preI_step (nm (stepW s c (born_step h))) u st
        have e : preIX (nm (stepW s c (born_step h))) x (.step u st) = .step u' st := by
          unfold preIX
          rw [if_neg hvx, e']
        exact ⟨u', st, e, hst, by rw [← e, hcomp]; rfl⟩

/-- ⭐**The path translation's round trip** (`◇`): a kept root possible term read along an
    arrow, at the arrow's end, denotes what the root term does (`tr_pathX`, `cden_named_dia`). -/
theorem cden_trX (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf (groot hF M₀).1 P) (hP : PathOk P) (i : ℕ) {x : VarSymb} {X : VarType}
    (hx : (ctxOf (glat (groot hF M₀) i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (c : Term σ ((ctxOf (glat (groot hF M₀) i)).diaIn x) A a) :
    cden hM₀ hX t (pstg (groot hF M₀) t P h i) (Ctx.Le.refl _)
        (pTr hM₀ (groot hF M₀) t P h hP i (.diatm (.step x .keep)
          (Ctx.exists_keep_dia hF ⟨X, hx⟩) (Term.shift (Ctx.shifts_diaIn_keep hF _ x) c))).2 =
      cden hM₀ hX (groot hF M₀) i (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ c) := by
  obtain rfl : P = rpath t := nodeOf_inj (h.symm.trans (rpath_eq t))
  exact (cden_sigma hX _ (tr_pathX hX hM₀ _ _ t h hP i hx c)).trans
    (cden_named_dia hX hM₀ t i _ hx (pnm_ok hX hM₀ _ _ t h i) c)

/-! ## The contents at a world's own arrow -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A possible term's witness is read off the term. -/
theorem sig_diatm_wit {Γ : Ctx} {x y : VarSymb} {hx : ∃ X, Γ.ref x = some (.VTypeDia X)}
    {hy : ∃ X, Γ.ref y = some (.VTypeDia X)} {A : VarType} {b b' : Ann A}
    {u : Term σ (Γ.diaIn x) A b} {u' : Term σ (Γ.diaIn y) A b'}
    (h : (⟨_, .diatm x hx u⟩ : Σ e, Term σ Γ (.VTypeDia A) e) = ⟨_, .diatm y hy u'⟩) : x = y := by
  cases h
  rfl

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Renaming possible terms that are one term, by one map. -/
theorem sig_diatm_ren_term (f : VarSymb → VarSymb) {Γ Δ : Ctx} {y y' : VarSymb} {A : VarType}
    {b b' : Ann A} {u : Term σ (Γ.diaIn y) A b} {u' : Term σ (Γ.diaIn y') A b'}
    {hy : ∃ X, Γ.ref y = some (.VTypeDia X)} {hy' : ∃ X, Γ.ref y' = some (.VTypeDia X)}
    (E : (⟨_, .diatm y hy u⟩ : Σ e, Term σ Γ (.VTypeDia A) e) = ⟨_, .diatm y' hy' u'⟩)
    (hf : ∃ Y, Δ.ref (f y) = some (.VTypeDia Y)) (hf' : ∃ Y, Δ.ref (f y') = some (.VTypeDia Y))
    (p : Subst.Ok (Γ.diaIn y) (eS σ (Δ.diaIn (f y)) (ofRen (preIX f y))))
    (q : Subst.Coh (eIdx (ofRen (σ := σ) (preIX f y))) (Γ.diaIn y)
      (eS σ (Δ.diaIn (f y)) (ofRen (preIX f y))))
    (p' : Subst.Ok (Γ.diaIn y') (eS σ (Δ.diaIn (f y')) (ofRen (preIX f y'))))
    (q' : Subst.Coh (eIdx (ofRen (σ := σ) (preIX f y'))) (Γ.diaIn y')
      (eS σ (Δ.diaIn (f y')) (ofRen (preIX f y')))) :
    (⟨_, .diatm (f y) hf (Term.subst (eIdx (ofRen (preIX f y)))
        (eS σ (Δ.diaIn (f y)) (ofRen (preIX f y))) p q u)⟩ : Σ e, Term σ Δ (.VTypeDia A) e) =
      ⟨_, .diatm (f y') hf' (Term.subst (eIdx (ofRen (preIX f y')))
        (eS σ (Δ.diaIn (f y')) (ofRen (preIX f y'))) p' q' u')⟩ := by
  cases E
  rfl

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A possible term whose body's entries are read in the view of an equal witness. -/
theorem sig_diatm_view_congr {Γ Δ : Ctx} {x : VarSymb} {A : VarType} {a : Ann A}
    (c : Term σ (Γ.diaIn x) A a) (ι : VarSymb → VarSymb) (g : VarSymb → LEnt σ) :
    ∀ (y : VarSymb) (_e : y = x) (hy : ∃ Y, Δ.ref y = some (.VTypeDia Y))
      (hx : ∃ Y, Δ.ref x = some (.VTypeDia Y))
      (p : Subst.Ok (Γ.diaIn x) (eS σ (Δ.diaIn y) g))
      (q : Subst.Coh ι (Γ.diaIn x) (eS σ (Δ.diaIn y) g))
      (p' : Subst.Ok (Γ.diaIn x) (eS σ (Δ.diaIn x) g))
      (q' : Subst.Coh ι (Γ.diaIn x) (eS σ (Δ.diaIn x) g)),
      (⟨_, .diatm y hy (Term.subst ι (eS σ (Δ.diaIn y) g) p q c)⟩ :
          Σ e, Term σ Δ (.VTypeDia A) e) =
        ⟨_, .diatm x hx (Term.subst ι (eS σ (Δ.diaIn x) g) p' q' c)⟩ := by
  intro y e
  subst e
  intros
  rfl

/-- Along an edge, the kept translation of a possible term's content, under its witness's image,
    is renaming by the names at the witness's name. -/
theorem tr_edgeXK (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t)
    (i : ℕ) {x : VarSymb} {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (c : Term σ ((ctxOf (glat s i)).diaIn x) A a)
    (hw : ∃ Z, (ctxOf (glat t (glstg s t i))).ref (wit t x) = some (.VTypeDia Z)) :
    (⟨_, .diatm (wit t x) hw (Term.subst (eIdx (fmapL hF M₀ t.1))
        ((eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).dia (.step x .keep) (wit t x))
        (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ h i)) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
          ((coh_eS_kView (gentOk_box hM₀ h i))
            (.step x .keep) _ (Ctx.exists_keep_dia hF ⟨X, hx⟩).choose_spec []))
        (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ h i))
          (coh_eS_kView (gentOk_box hM₀ h i)) (Ctx.exists_keep_dia hF ⟨X, hx⟩))
        (Term.shift (Ctx.shifts_diaIn_keep hF _ x) c))⟩ :
        Σ e, Term σ (ctxOf (glat t (glstg s t i))) (.VTypeDia A) e) =
      ⟨_, .diatm (nm t x) ⟨X, nm_ok hX hM₀ h i x _ hx rfl⟩
        (Term.subst (eIdx (ofRen (preIX (nm t) x)))
          (eS σ ((ctxOf (glat t (glstg s t i))).diaIn (nm t x)) (ofRen (preIX (nm t) x)))
          (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx (nm_ok hX hM₀ h i))))
          (coh_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx (nm_ok hX hM₀ h i)))) c)⟩ :=
  (sig_subst_diatm _ (ok_eS_kView (gentOk_box hM₀ h i)) (coh_eS_kView (gentOk_box hM₀ h i))
    (Ctx.exists_keep_dia hF ⟨X, hx⟩) _ (wit t x) rfl hw _ _).symm.trans (tr_edgeX hX hM₀ h i hx c)

/-- ⭐**A kept content along a path is renaming by the path names**, at the path name of the
    witness (stated under the `◇`, where the two names of the witness are one term). -/
theorem tr_pathXK (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (i : ℕ) {x : VarSymb} {X : VarType}
      (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
      (c : Term σ ((ctxOf (glat s i)).diaIn x) A a),
      (⟨_, .diatm (kw s t P h x) (kw_decl hM₀ s t P h i ⟨X, hx⟩)
          (pTrXK hM₀ s t P h i x ⟨X, hx⟩ c).2⟩ :
          Σ e, Term σ (ctxOf (glat t (pstg s t P h i))) (.VTypeDia A) e) =
        ⟨_, .diatm (pnm P s t h x) ⟨X, pnm_ok hX hM₀ P s t h i x _ hx rfl⟩
          (Term.subst (eIdx (ofRen (preIX (pnm P s t h) x)))
            (eS σ ((ctxOf (glat t (pstg s t P h i))).diaIn (pnm P s t h x))
              (ofRen (preIX (pnm P s t h) x)))
            (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx
              (pnm_ok hX hM₀ P s t h i))))
            (coh_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hx
              (pnm_ok hX hM₀ P s t h i)))) c)⟩
  | [], s, t, h, i, x, X, hx, _, _, b => by
      obtain rfl : t = s := gw_eq h
      refine sig_diatm ?_
      refine (congrArg (Sigma.mk _) (Term.mono_refl _ b)).trans ?_
      exact (subst_preIX_id _ _ _).symm
  | [c], s, t, h, i, x, X, hx, _, _, b => by
      refine (tr_edgeXK hX hM₀ (s := s) (t := t) ⟨c, h⟩ i hx b _).trans ?_
      exact sig_diatm_ren_congr b _ _
        (funext fun v => congrFun (nm_congr (t := t) (t' := stepW s c (born_step h)) h) v)
        _ _ _ _ _ _
  | c :: c' :: P, s, t, h, i, x, X, hx, A, _, b => by
      have hch : GCh hF M₀ s (stepW s c (born_step h)) := ⟨c, rfl⟩
      have hw : wit (stepW s c (born_step h)) x = nm (stepW s c (born_step h)) x :=
        idx_names hM₀ hch i hx (nm_spec hX.five _ x)
      have hnx := nm_ok hX hM₀ hch i x _ hx rfl
      have hwx : (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i))).ref
          (wit (stepW s c (born_step h)) x) = some (.VTypeDia X) := hw ▸ hnx
      refine (tr_pathXK hX hM₀ (c' :: P) (stepW s c (born_step h)) t h _ hwx
        (eTrKX hM₀ s c (born_step h) i x ⟨X, hx⟩ b).2).trans ?_
      refine (sig_diatm_ren_term (pnm (c' :: P) (stepW s c (born_step h)) t h)
        (tr_edgeXK hX hM₀ hch i hx b ⟨X, hwx⟩) _
        ⟨X, pnm_ok hX hM₀ (c' :: P) (stepW s c (born_step h)) t h _ _ _ hnx rfl⟩ _ _
        (ok_eS_kView (k := some _) (entOk_ofRen (itemOk_preIX hnx
          (pnm_ok hX hM₀ (c' :: P) (stepW s c (born_step h)) t h _))))
        (coh_eS_kView (k := some _) (entOk_ofRen (itemOk_preIX hnx
          (pnm_ok hX hM₀ (c' :: P) (stepW s c (born_step h)) t h _))))).trans ?_
      refine sig_diatm (Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
        fun u st _ hst hv => ?_) b)
      have hcomp := preIX_comp (pnm (c' :: P) (stepW s c (born_step h)) t h)
        (nm (stepW s c (born_step h))) (v := .step u st) hst hv
      by_cases hvx : VarSymb.step u st = .step x .dia
      · have e : preIX (nm (stepW s c (born_step h))) x (.step u st) =
            .step (nm (stepW s c (born_step h)) x) .dia := by
          unfold preIX
          rw [if_pos hvx]
        exact ⟨_, .dia, e, rfl, by rw [← e, hcomp]; rfl⟩
      · obtain ⟨u', e'⟩ := preI_step (nm (stepW s c (born_step h))) u st
        have e : preIX (nm (stepW s c (born_step h))) x (.step u st) = .step u' st := by
          unfold preIX
          rw [if_neg hvx, e']
        exact ⟨u', st, e, hst, by rw [← e, hcomp]; rfl⟩

/-- ⭐**A world's possible term, read at the root and kept back along the world's path, is the
    term** (the `◇` half of `pTrK_pre`). -/
theorem pTrXK_pre (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) {x : VarSymb}
    {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (c : Term σ ((ctxOf (glat s i)).diaIn x) A a) :
    (⟨_, .diatm (kw (groot hF M₀) s (rpath s) (rpath_eq s) (rorig s x))
        (kw_decl hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) (rstg s i)
          (rorig_ref hX hM₀ s i ⟨X, hx⟩))
        (pTrXK hM₀ (groot hF M₀) s (rpath s) (rpath_eq s) (rstg s i) (rorig s x)
          (rorig_ref hX hM₀ s i ⟨X, hx⟩) (preTD hX hM₀ s i ⟨X, hx⟩ c).2).2⟩ :
        Σ e, Term σ (ctxOf (glat s (pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg s i))))
          (.VTypeDia A) e) =
      ⟨_, Term.mono (gle hM₀ s (le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath s)
        (groot hF M₀) s (rpath_eq s) i)) (.diatm x ⟨X, hx⟩ c)⟩ := by
  set K := pstg (groot hF M₀) s (rpath s) (rpath_eq s) (rstg s i)
  have hiK : i ≤ K := le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath s)
    (groot hF M₀) s (rpath_eq s) i
  have hle := (gle hM₀ s hiK).diaIn x
  have hrx : (ctxOf (glat (groot hF M₀) (rstg s i))).ref (rorig s x) = some (.VTypeDia X) :=
    rpre hX hM₀ s i x _ hx rfl
  have hrt : ∀ z T, (ctxOf (glat s i)).ref z = some T → T.keepable = true →
      (ctxOf (glat s K)).ref ((rnm s ∘ rorig s) z) = some T := fun z T hz hkp =>
    pnm_ok hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg s i) _ T
      (rpre hX hM₀ s i z T hz hkp) hkp
  have hgx : (rnm s ∘ rorig s) x = x :=
    rnm_rorig hX.five hX.fourS hX.fourSW hM₀ s ⟨i, hx⟩ rfl rfl
  have hit := itemOk_preIX hx hrt
  have e₁ := tr_pathXK hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg s i) hrx
    (preTD hX hM₀ s i ⟨X, hx⟩ c).2
  refine e₁.trans ?_
  have e₂ : (⟨_, Term.subst (eIdx (ofRen (preIX (rnm s) (rorig s x))))
        (eS σ ((ctxOf (glat s K)).diaIn (rnm s (rorig s x))) (ofRen (preIX (rnm s) (rorig s x))))
        (ok_eS_kView (k := some (rorig s x)) (entOk_ofRen (itemOk_preIX hrx
          (pnm_ok hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg s i)))))
        (coh_eS_kView (k := some (rorig s x)) (entOk_ofRen (itemOk_preIX hrx
          (pnm_ok hX hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) (rstg s i)))))
        (preTD hX hM₀ s i ⟨X, hx⟩ c).2⟩ :
        Σ e, Term σ ((ctxOf (glat s K)).diaIn (rnm s (rorig s x))) A e) =
      ⟨_, Term.subst (eIdx (ofRen (preIX (rnm s ∘ rorig s) x)))
        (eS σ ((ctxOf (glat s K)).diaIn ((rnm s ∘ rorig s) x))
          (ofRen (preIX (rnm s ∘ rorig s) x)))
        (ok_eS_kView (k := some x) (entOk_ofRen hit))
        (coh_eS_kView (k := some x) (entOk_ofRen hit)) c⟩ := by
    refine Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
      fun u st _ hst hv => ?_) c
    have hcomp := preIX_comp (rnm s) (rorig s) (v := .step u st) hst hv
    by_cases hvx : VarSymb.step u st = .step x .dia
    · have e : preIX (rorig s) x (.step u st) = .step (rorig s x) .dia := by
        unfold preIX
        rw [if_pos hvx]
      exact ⟨_, .dia, e, rfl, by rw [← e, hcomp]⟩
    · obtain ⟨u', e'⟩ := preI_step (rorig s) u st
      have e : preIX (rorig s) x (.step u st) = .step u' st := by
        unfold preIX
        rw [if_neg hvx, e']
      exact ⟨u', st, e, hst, by rw [← e, hcomp]⟩
  refine (sig_diatm (hx' := ⟨X, hrt x _ hx rfl⟩) e₂).trans ?_
  have hit' : ItemOk ((ctxOf (glat s i)).diaIn x) ((ctxOf (glat s K)).diaIn x)
      (preIX (rnm s ∘ rorig s) x) := by
    have h' := hit
    rwa [hgx] at h'
  refine (sig_diatm_view_congr c _ _ _ hgx _ ⟨X, (gle hM₀ s hiK).ref hx⟩ _ _
    (ok_eS_kView (k := some x) (entOk_ofRen hit'))
    (coh_eS_kView (k := some x) (entOk_ofRen hit'))).trans ?_
  refine sig_diatm ((Term.subst_congrF _ (Subst.idS σ _) _ (Subst.ok_idS_le hle) _
    (Subst.coh_idS_le hle) (Subst.simF_of fun v T hl hv hTe => ?_) c).trans
    (Term.subst_idS_mono hle _ _ c))
  by_cases hvx : v = .step x .dia
  · subst hvx
    rw [eS_item _ rfl]
    change SubE.Sim T (.ren (preIX (rnm s ∘ rorig s) x (.step x .dia))) (.ren _)
    rw [show preIX (rnm s ∘ rorig s) x (.step x .dia) = .step ((rnm s ∘ rorig s) x) .dia by
      unfold preIX
      rw [if_pos rfl], hgx]
    exact .refl _
  have hb := diaIn_boxIn_of_ne' hv hvx
  have hpre : preIX (rnm s ∘ rorig s) x v = preI (rnm s ∘ rorig s) v := by
    unfold preIX
    rw [if_neg hvx]
  match v, hl, hb, hpre with
  | .step u .box, hl, hb, hpre =>
      have hu := Ctx.boxIn_step_box hb
      rw [eS_item _ rfl]
      change SubE.Sim T (.ren (preIX (rnm s ∘ rorig s) x (.step u .box))) (.ren _)
      rw [hpre]
      change SubE.Sim T (.ren (.step (rnm s (rorig s u)) .box)) (.ren _)
      rw [rnm_rorig hX.five hX.fourS hX.fourSW hM₀ s ⟨i, hu⟩ rfl hTe]
      exact .refl _
  | .step u .keep, hl, hb, hpre =>
      obtain ⟨-, hu, hkp⟩ := Ctx.boxIn_keep hb
      rw [eS_item _ rfl]
      change SubE.Sim T (.ren (preIX (rnm s ∘ rorig s) x (.step u .keep))) (.ren _)
      rw [hpre]
      change SubE.Sim T (.ren (.step (rnm s (rorig s u)) .keep)) (.ren _)
      rw [rnm_rorig hX.five hX.fourS hX.fourSW hM₀ s ⟨i, hu⟩ hkp hTe]
      exact .refl _
  | .root _, _, hb, _ => cases hb
  | .step _ .fst, _, hb, _ => cases hb
  | .step _ .snd, _, hb, _ => cases hb
  | .step _ .dia, _, hb, _ => cases hb
  | .step _ .here, _, hb, _ => cases hb

/-- The root's name, kept back along a world's path, is the world's address. -/
theorem kw_rorig (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) {x : VarSymb}
    {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {P : List ℕ}
    (h : s.1 = nodeOf (groot hF M₀).1 P) : kw (groot hF M₀) s P h (rorig s x) = x := by
  obtain rfl : P = rpath s := nodeOf_inj (h.symm.trans (rpath_eq s))
  exact sig_diatm_wit (pTrXK_pre hX hM₀ s i hx (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)))

/-- Realising possible terms that are one term denotes alike. -/
theorem cden_grealT_congr (hX : CluFlags) {M : Theory.IsMCS M₀} {t : GW hF M₀} {K : ℕ}
    {y y' : VarSymb} (hr : (gw M t).Realised y) (hr' : (gw M t).Realised y')
    (hy : ∃ Y, (ctxOf (glat t K)).ref y = some (.VTypeDia Y))
    (hy' : ∃ Y, (ctxOf (glat t K)).ref y' = some (.VTypeDia Y)) {A : VarType} {b b' : Ann A}
    {u : Term σ ((ctxOf (glat t K)).diaIn y) A b} {u' : Term σ ((ctxOf (glat t K)).diaIn y') A b'}
    (E : (⟨_, .diatm y hy u⟩ : Σ e, Term σ (ctxOf (glat t K)) (.VTypeDia A) e) =
      ⟨_, .diatm y' hy' u'⟩) :
    cden M hX t _ (Ctx.Le.refl _) (grealT hr (Ctx.Le.refl _) hy u).2 =
      cden M hX t _ (Ctx.Le.refl _) (grealT hr' (Ctx.Le.refl _) hy' u').2 := by
  cases E
  rfl

/-- ⭐**A possible term's realised content, read through the root along the world's own path, is
    its realisation here.** -/
theorem cden_real_pre (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) {x : VarSymb}
    {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (c : Term σ ((ctxOf (glat s i)).diaIn x) A a) {P : List ℕ}
    (h : s.1 = nodeOf (groot hF M₀).1 P)
    (hr' : (gw hM₀ s).Realised (kw (groot hF M₀) s P h (rorig s x)))
    (hr : (gw hM₀ s).Realised x) :
    cden hM₀ hX s _ (Ctx.Le.refl _) (grealT hr' (Ctx.Le.refl _)
        (kw_decl hM₀ (groot hF M₀) s P h (rstg s i) (rorig_ref hX hM₀ s i ⟨X, hx⟩))
        (pTrXK hM₀ (groot hF M₀) s P h (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hx⟩)
          (preTD hX hM₀ s i ⟨X, hx⟩ c).2).2).2 =
      cden hM₀ hX s _ (Ctx.Le.refl _) (grealT hr (Ctx.Le.refl _) ⟨X, hx⟩ c).2 := by
  obtain rfl : P = rpath s := nodeOf_inj (h.symm.trans (rpath_eq s))
  have hiK : i ≤ pstg (groot hF M₀) s (rpath s) h (rstg s i) :=
    le_pstg_pstgO hX.five hX.fourS hX.fourSW hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i
  have hxK := (gle hM₀ s hiK).ref hx
  refine (cden_grealT_congr hX hr' hr _ ⟨X, hxK⟩
    (u' := Term.mono ((gle hM₀ s hiK).diaIn x) c) (pTrXK_pre hX hM₀ s i hx c)).trans ?_
  refine (cden_sigma hX _ (grealT_mono hr hiK ⟨X, hx⟩ ⟨X, hxK⟩ c _ rfl).symm).trans ?_
  rw [cden_mono]
  exact cden_congr hX _ _ _ _ _ _

open Classical in
/-- A possible term's content along an arrow it realises. -/
theorem cden_dia_c_pos (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {x : VarSymb} {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (c : Term σ ((ctxOf (glat s i)).diaIn x) A a) (b : CAcc hF M₀)
    (hb : b ∈ (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ c)).E)
    (hr : (gw hM₀ b.1).Realised
      (kw (groot hF M₀) b.1 (cpath b.2.down) (cpath_eq b.2.down) (rorig s x))) :
    (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ c)).c ⟨b, hb⟩ =
      cden hM₀ hX b.1 _ (Ctx.Le.refl _) (grealT hr (Ctx.Le.refl _)
        (kw_decl hM₀ (groot hF M₀) b.1 (cpath b.2.down) (cpath_eq b.2.down) (rstg s i)
          (rorig_ref hX hM₀ s i ⟨X, hx⟩))
        (pTrXK hM₀ (groot hF M₀) b.1 (cpath b.2.down) (cpath_eq b.2.down) (rstg s i)
          (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hx⟩)
          (preTD hX hM₀ s i ⟨X, hx⟩ (Term.mono ((Ctx.Le.refl _).diaIn x) c)).2).2).2 :=
  dif_pos hr

/-- ⭐**Under T a world's own arrow is in a possible term's extent exactly when the world realises
    the witness.** -/
theorem cden_own_mem (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (hT : ModalSys.T = true)
    (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (c : Term σ ((ctxOf (glat s i)).diaIn x) A a) (hR : CR s) :
    (⟨s, ⟨hR⟩⟩ : CAcc hF M₀) ∈ (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ c)).E ↔
      (gw hM₀ s).Realised x := by
  change GMem hM₀ (groot hF M₀) s (cpath hR) (cpath_eq hR) (rorig s x) ↔ _
  rw [gmem_T hT, kw_rorig hX hM₀ s i hx]

/-- ⭐**A possible term's content at a world's own arrow is its realisation** (`pTrXK_pre`). -/
theorem cden_own_content (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {x : VarSymb} {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (c : Term σ ((ctxOf (glat s i)).diaIn x) A a) (hR : CR s)
    (hm : (⟨s, ⟨hR⟩⟩ : CAcc hF M₀) ∈ (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ c)).E)
    (hr : (gw hM₀ s).Realised x) :
    (cden hM₀ hX s i (Ctx.Le.refl _) (.diatm x ⟨X, hx⟩ c)).c ⟨⟨s, ⟨hR⟩⟩, hm⟩ =
      cden hM₀ hX s _ (Ctx.Le.refl _) (grealT hr (Ctx.Le.refl _) ⟨X, hx⟩ c).2 := by
  have hr' : (gw hM₀ s).Realised
      (kw (groot hF M₀) s (cpath hR) (cpath_eq hR) (rorig s x)) := by
    rw [kw_rorig hX hM₀ s i hx]
    exact hr
  refine (cden_dia_c_pos hX hM₀ s i hx c ⟨s, ⟨hR⟩⟩ hm hr').trans ?_
  rw [Term.mono_refl]
  exact cden_real_pre hX hM₀ s i hx c (cpath_eq hR) hr' hr

end GArrow

end V12M
