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
      obtain ⟨-, hz⟩ := Ctx.boxIn_box hv
      rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
      change SubE.Sim T (((eS σ _ (fmapL hF M₀ t.1)).at (.step u .keep)).unbox)
        (.ren (.step (nm t u) .box))
      rw [Subst.at_nonproj _ rfl, eS_item _ rfl]
      rcases hn with he | ⟨L, U, hz', he⟩
      · rw [he]
        change SubE.Sim T (.ren (nm t u).inner) _
        rw [VarSymb.inner_box hX.keepOnly]
        exact .refl _
      · obtain ⟨rfl, hz'', e⟩ := entOf_names_tm hM₀ h i hz rfl hz' he
        rw [e]
        change SubE.Sim T (.tm (Term.eta (nm t u).inner T (Ctx.ref_inner hz''))) _
        generalize Ctx.ref_inner hz'' = hp
        revert hp
        rw [VarSymb.inner_box hX.keepOnly]
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
        exact keepE_eta_sim hX.keepOnly hF' hz'' hkp
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
        (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly (nm_ok hX hM₀ h i))))
        (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly (nm_ok hX hM₀ h i))))
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
          (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly
            (pnm_ok hX hM₀ P s t h i))))
          (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly
            (pnm_ok hX hM₀ P s t h i)))) b)⟩
  | [], _, _, _, hP, _, _, _, _ => absurd hP.T_of_nil (by rw [hX.noT]; decide)
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
              (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly
                (nm_ok hX hM₀ hch i))))
              (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly
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

end GArrow

end V12M
