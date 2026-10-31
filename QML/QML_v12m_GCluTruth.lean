import QML.QML_v12m_GCluTerm

/-!
# QML v12m — 5 on the growing tree: the cluster model's truth lemma

As `GTruth` for the growing tree (`docs/v12-modal-extensions.md` §3 5, "The truth lemma: design
check against `GTruth`").  Pushing from intermediate worlds is never needed: an environment
agreeing with a chain of substitutions and shifts satisfies a formula exactly when the chain's
end satisfies its translation, link by link (`Model.sat_subst`, `Model.sat_shift`).

* `cenvOf`: an environment agreeing with a chain, by construction; `eq_substEnv_of_cagree`,
  `shiftAgree_of_cagree`: a substitution link and a shift link, semantically.
* ⭐`sat_ptrC`, ⭐`sat_ptrXC`, ⭐`sat_ptrXKC`: along a path, an environment agreeing with the
  path's chain satisfies a formula exactly when the end's environment satisfies its translation.
* `sat_boxPush_c`, `sat_diaPush_c`, `sat_diaPush_cK`: pushing from a world is its preimage, then
  the root's path, the last along an arrow whose end realises the kept witness.
* `cdia_real_not_boxx`, `cdia_sat_child`, ⭐`chere_truth`: under T, as the tree's.
* ⭐`ctruth`: the truth lemma, `□` and `◇` through `box_pathO_iff` and `dia_pathO_iff`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hM₀ : Theory.IsMCS M₀)

/-! ## Chains, semantically -/

/-- An environment agreeing with a chain, by construction. -/
noncomputable def cenvOf (hX : CluFlags) {Γ : Ctx} {t : GW hF M₀} {k : ℕ}
    (D : GTr σ Γ (ctxOf (glat t k))) (hΓ : Γ.NoProjLast) : (cmodel hF hM₀ hX).Env Γ t :=
  fun v T hv => ctoDom hM₀ hX T t (cden hM₀ hX t k (Ctx.Le.refl _)
    (D.app (Term.eta v T ((Ctx.ref_nonproj Γ (hΓ v T hv)).trans hv))).2) (cdefinable_den hX _ _)

variable {hM₀}

theorem cagree_envOf (hX : CluFlags) {Γ : Ctx} {t : GW hF M₀} {k : ℕ}
    (D : GTr σ Γ (ctxOf (glat t k))) (hΓ : Γ.NoProjLast) :
    CAgree hM₀ hX D (cenvOf hM₀ hX D hΓ) :=
  cagree_of_raw hX _ _ fun _ _ _ _ => rfl

/-- An environment agreeing with a substitution link is the substituted environment. -/
theorem eq_substEnv_of_cagree (hX : CluFlags) {Γ Δ : Ctx} (hnp : Γ.NoProjLast)
    {t : GW hF M₀} {j : ℕ} {ι : VarSymb → VarSymb} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (D : GTr σ Δ (ctxOf (glat t j))) (hD : D.NPL) (hΔ : Δ.NoProjLast)
    (env : (cmodel hF hM₀ hX).Env Γ t) (hag : CAgree hM₀ hX (.sub θ hθ hc D) env)
    (env' : (cmodel hF hM₀ hX).Env Δ t) (hag' : CAgree hM₀ hX D env') :
    env = Model.substEnv θ hθ hnp env' := by
  funext v T hv
  have hlp := hnp v T hv
  have href : Γ.ref v = some T := (Ctx.ref_nonproj Γ hlp).trans hv
  rw [← Model.Env.ref_of_nonproj env hlp href hv, hag v T href,
    ← Model.Env.ref_of_nonproj (Model.substEnv θ hθ hnp env') hlp href hv,
    ← Model.interp_eta, ← Model.interp_subst θ hθ hc, interp_ctr hX _ D hag' hD hΔ]
  rfl

/-- An environment agreeing with a shift link agrees across the shift. -/
theorem shiftAgree_of_cagree (hX : CluFlags) {k : ℕ} {Γ Γ' : Ctx} (h : Ctx.Shifts k Γ Γ')
    {t : GW hF M₀} {j : ℕ} (D : GTr σ Γ' (ctxOf (glat t j)))
    (env : (cmodel hF hM₀ hX).Env Γ t) (hag : CAgree hM₀ hX (.sh h D) env)
    (env' : (cmodel hF hM₀ hX).Env Γ' t) (hag' : CAgree hM₀ hX D env') :
    Model.Env.ShiftAgree h env env' := by
  intro v T hv
  rw [hag v T hv, hag' (v.shift k) T (h v T hv)]
  exact ctoDom_congr hX (cden_sigma hX _ (D.app_sigma (Term.shift_eta h v T hv))) _ _

/-! ## Along a path -/

/-- ⭐**Along a path, an environment agreeing with the path's chain satisfies a formula exactly
    when the end's canonical environment satisfies its translation.** -/
theorem sat_ptrC (hX : CluFlags) : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P)
    (hP : PathOk P) (i : ℕ) (env : (cmodel hF hM₀ hX).Env ((ctxOf (glat s i)).kView none) t),
    CAgree hM₀ hX (ptrC hM₀ s t P h hP i) env →
    ∀ φ : WFF σ ((ctxOf (glat s i)).kView none) 0,
      ((cmodel hF hM₀ hX).sat env φ ↔
        (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX t (pstg s t P h i)) (pTrW hM₀ s t P h hP i φ))
  | s, t, [], h, hP, i, env, hag, φ => by
      have hT := hP.T_of_nil
      obtain rfl : t = s := gw_eq h
      change _ ↔ (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX t i) (WFF.mono (glat_le_of_eq h i)
        (WFF.collapse (Ctx.collapses_boxIn_self hT _) Ctx.NoSlots.slots φ))
      rw [Model.sat_mono (env := ccanonEnv hM₀ hX t i) (env' := ccanonEnv hM₀ hX t i)
        (fun _ _ _ => rfl)]
      refine (Model.sat_collapse Ctx.NoSlots.slots (fun v T hv => ?_) φ).symm
      rw [hag v T hv, cagree_canon hX t i _ T _]
      refine ctoDom_congr hX ?_ _ _
      change cden hM₀ hX t i (Ctx.Le.refl _) (Term.mono (glat_le_of_eq h i)
        (Term.collapse (Ctx.collapses_boxIn_self hT _) (Term.eta v T hv))) = _
      rw [Term.mono_refl]
      exact cden_sigma hX _ (Term.collapse_eta _ _ _ _)
  | s, t, [c], h, _, i, env, hag, φ => by
      rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_boxIn _) _ _ _ (.nil _) (by trivial)
        (Ctx.Presented.noProjLast _) env hag _ (cagree_canon hX t _)]
      exact (Model.sat_subst _ _ (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) Ctx.NoSlots.slots
        Ctx.NoSlots.slots _ _ φ).symm
  | s, t, c :: c' :: P, h, _, i, env, hag, φ => by
      have hb := born_step h
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hD := npl_ptrC hM₀ (stepW s c hb) t (c' :: P) h pathOk_cons
        (glstg s (stepW s c hb) i)
      set D₁ := GTr.sub (Subst.box _) (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        (ptrC hM₀ (stepW s c hb) t (c' :: P) h pathOk_cons (glstg s (stepW s c hb) i))
      have hag₁ := cagree_envOf (hM₀ := hM₀) hX D₁ (Ctx.noProjLast_boxIn _)
      refine (Model.sat_shift Ctx.NoSlots.slots
        (shiftAgree_of_cagree hX _ D₁ env hag _ hag₁) φ).symm.trans ?_
      have hag₂ := cagree_envOf (hM₀ := hM₀) hX (ptrC hM₀ (stepW s c hb) t (c' :: P) h pathOk_cons
        (glstg s (stepW s c hb) i)) (Ctx.noProjLast_boxIn _)
      rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_boxIn _) _ _ _ _ hD
        (Ctx.noProjLast_boxIn _) _ hag₁ _ hag₂]
      refine (Model.sat_subst _ _ (Subst.coh_box hθ hc) Ctx.NoSlots.slots Ctx.NoSlots.slots _ _
        _).symm.trans ?_
      exact sat_ptrC hX (stepW s c hb) t (c' :: P) h pathOk_cons _ _ hag₂ _

/-- ⭐**Along a path in a witness's extent, an environment agreeing with the path's chain
    satisfies a formula of the witness's view exactly when the end satisfies its translation.** -/
theorem sat_ptrXC (hX : CluFlags) : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P)
    (i : ℕ) (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x)
    (env : (cmodel hF hM₀ hX).Env ((ctxOf (glat s i)).kView (some x)) t),
    CAgree hM₀ hX (ptrXC hM₀ s t P h i x hx hm) env →
    ∀ φ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0,
      ((cmodel hF hM₀ hX).sat env φ ↔
        (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX t (pstg s t P h i))
          (pTrXW hM₀ s t P h i x hx hm φ))
  | _, _, [], _, _, _, _, hm, _, _, _ => hm.elim
  | s, t, [c], h, i, x, _, hm, env, hag, φ => by
      rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_diaIn _ _) _ _ _ (.nil _) (by trivial)
        (Ctx.Presented.noProjLast _) env hag _ (cagree_canon hX t _)]
      exact (Model.sat_subst _ _ (coh_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i)) Ctx.NoSlots.slots
        Ctx.NoSlots.slots _ _ φ).symm
  | s, t, c :: c' :: P, h, i, x, hx, hm, env, hag, φ => by
      have hb := born_step h
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hD := npl_ptrXC hM₀ (stepW s c hb) t (c' :: P) h (glstg s (stepW s c hb) i)
        (wit (stepW s c hb) x) (wit_ref hM₀ hb i hx) hm
      set D₁ := GTr.sub (Subst.dia _ (.step x .keep) (wit (stepW s c hb) x))
        (Subst.ok_dia hθ (Ctx.exists_keep_dia hF hx)
          (hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
        (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx))
        (ptrXC hM₀ (stepW s c hb) t (c' :: P) h (glstg s (stepW s c hb) i)
          (wit (stepW s c hb) x) (wit_ref hM₀ hb i hx) hm)
      have hag₁ := cagree_envOf (hM₀ := hM₀) hX D₁ (Ctx.noProjLast_diaIn _ _)
      refine (Model.sat_shift Ctx.NoSlots.slots
        (shiftAgree_of_cagree hX _ D₁ env hag _ hag₁) φ).symm.trans ?_
      have hag₂ := cagree_envOf (hM₀ := hM₀) hX (ptrXC hM₀ (stepW s c hb) t (c' :: P) h
        (glstg s (stepW s c hb) i) (wit (stepW s c hb) x) (wit_ref hM₀ hb i hx) hm)
        (Ctx.noProjLast_diaIn _ _)
      rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_diaIn _ _) _ _ _ _ hD
        (Ctx.noProjLast_diaIn _ _) _ hag₁ _ hag₂]
      refine (Model.sat_subst _ _ (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx))
        Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ _).symm.trans ?_
      exact sat_ptrXC hX (stepW s c hb) t (c' :: P) h _ _ _ hm _ hag₂ _

/-- ⭐**Along a path, with the witness kept, an environment agreeing with the path's chain followed
    by a further chain `D` satisfies a formula of the witness's view exactly when an environment
    agreeing with `D` satisfies its kept translation.** -/
theorem sat_ptrXKC (hX : CluFlags) : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P)
    (i : ℕ) (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {j : ℕ}
    (D : GTr σ ((ctxOf (glat t (pstg s t P h i))).kView (some (kw s t P h x)))
      (ctxOf (glat t j))) (_hD : D.NPL)
    (env : (cmodel hF hM₀ hX).Env ((ctxOf (glat s i)).kView (some x)) t)
    (env₂ : (cmodel hF hM₀ hX).Env ((ctxOf (glat t (pstg s t P h i))).kView
      (some (kw s t P h x))) t),
    CAgree hM₀ hX ((ptrXKC hM₀ s t P h i x hx).comp D) env → CAgree hM₀ hX D env₂ →
    ∀ φ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0,
      ((cmodel hF hM₀ hX).sat env φ ↔ (cmodel hF hM₀ hX).sat env₂ (pTrXKW hM₀ s t P h i x hx φ))
  | s, t, [], h, i, x, hx, _, D, _, env, env₂, hag, hag₂, φ => by
      refine (Model.sat_mono (fun v T hv => ?_) φ).symm
      have hlp := Ctx.noProjLast_diaIn _ _ v T hv
      rw [← cenv_ref_raw hX env hlp hv,
        ← cenv_ref_raw hX env₂ hlp (((glat_le_of_eq h i).kView _) v T hv), hag v T _, hag₂ v T _]
      refine ctoDom_congr hX ?_ _ _
      change cden hM₀ hX t _ (Ctx.Le.refl _) (D.app (Term.mono ((glat_le_of_eq h i).kView (some x))
        (Term.eta v T ((Ctx.ref_nonproj _ hlp).trans hv)))).2 = _
      exact cden_sigma hX _ (D.app_sigma (congrArg (Sigma.mk _) (Term.mono_eta _ v T _)))
  | s, t, [c], h, i, x, hx, _, D, hD, env, env₂, hag, hag₂, φ => by
      have hθ := ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      set D₁ := GTr.sub ((eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).dia (.step x .keep)
          (wit t x))
        (Subst.ok_dia hθ (Ctx.exists_keep_dia hF hx)
          (hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
        (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx)) D
      have hag₁ := cagree_envOf (hM₀ := hM₀) hX D₁ (Ctx.noProjLast_diaIn _ _)
      refine (Model.sat_shift Ctx.NoSlots.slots
        (shiftAgree_of_cagree hX _ D₁ env hag _ hag₁) φ).symm.trans ?_
      rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_diaIn _ _) _ _ _ _ hD
        (Ctx.noProjLast_diaIn _ _) _ hag₁ _ hag₂]
      exact (Model.sat_subst _ _ (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx))
        Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ _).symm
  | s, t, c :: c' :: P, h, i, x, hx, _, D, hD, env, env₂, hag, hag₂, φ => by
      have hb := born_step h
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hD' := GTr.npl_comp _ _ (npl_ptrXKC hM₀ (stepW s c hb) t (c' :: P) h
        (glstg s (stepW s c hb) i) (wit (stepW s c hb) x) (wit_ref hM₀ hb i hx)) hD
      set D₁ := GTr.sub ((eS σ (ctxOf (glat (stepW s c hb) (glstg s (stepW s c hb) i)))
          (fmapL hF M₀ (c :: s.1))).dia (.step x .keep) (wit (stepW s c hb) x))
        (Subst.ok_dia hθ (Ctx.exists_keep_dia hF hx)
          (hc (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
        (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx))
        ((ptrXKC hM₀ (stepW s c hb) t (c' :: P) h (glstg s (stepW s c hb) i)
          (wit (stepW s c hb) x) (wit_ref hM₀ hb i hx)).comp D)
      have hag₁ := cagree_envOf (hM₀ := hM₀) hX D₁ (Ctx.noProjLast_diaIn _ _)
      refine (Model.sat_shift Ctx.NoSlots.slots
        (shiftAgree_of_cagree hX _ D₁ env hag _ hag₁) φ).symm.trans ?_
      have hag₃ := cagree_envOf (hM₀ := hM₀) hX ((ptrXKC hM₀ (stepW s c hb) t (c' :: P) h
        (glstg s (stepW s c hb) i) (wit (stepW s c hb) x) (wit_ref hM₀ hb i hx)).comp D)
        (Ctx.noProjLast_diaIn _ _)
      rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_diaIn _ _) _ _ _ _ hD'
        (Ctx.noProjLast_diaIn _ _) _ hag₁ _ hag₃]
      refine (Model.sat_subst _ _ (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF hx))
        Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ _).symm.trans ?_
      exact sat_ptrXKC hX (stepW s c hb) t (c' :: P) h _ _ _ D hD _ env₂ hag₃ hag₂ _

/-! ## Pushing from a world -/

/-- ⭐**A world's `□` view along an arrow satisfies a formula exactly when the arrow's end
    satisfies its preimage translated along the root's path**: the pushed environment agrees
    with the world's preimage, then the root's path (`cagree_boxPush`). -/
theorem sat_boxPush_c (hX : CluFlags) (s : GW hF M₀) (i : ℕ) (a : CAcc hF M₀) (P : List ℕ)
    (h : a.1.1 = nodeOf (groot hF M₀).1 P) (hP : PathOk P) (e : pathOf a.2.down = P)
    (χ : WFF σ ((ctxOf (glat s i)).kView none) 0) :
    (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).boxPush a) χ ↔
      (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX a.1 (pstg (groot hF M₀) a.1 P h (rstg s i)))
        (pTrW hM₀ (groot hF M₀) a.1 P h hP (rstg s i) (preWP (rpre hX hM₀ s i) χ)) := by
  subst e
  have hag : CAgree hM₀ hX (preC hM₀ hX s i a) ((ccanonEnv hM₀ hX s i).boxPush a) :=
    cagree_boxPush hX (.nil _) _ (cagree_canon hX s i) a
  have hag' := cagree_envOf (hM₀ := hM₀) hX (ptrC hM₀ (groot hF M₀) a.1 (pathOf a.2.down)
    (pathOf_eq a.2.down) (pathOf_ok a.2.down) (rstg s i)) (Ctx.noProjLast_boxIn _)
  rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_boxIn _) _ _ _ _ (npl_ptrC hM₀ _ _ _ _ _ _)
    (Ctx.noProjLast_boxIn _) _ hag _ hag']
  refine (Model.sat_subst _ _ (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI
    (rpre hX hM₀ s i)))) Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ χ).symm.trans ?_
  exact sat_ptrC hX _ _ _ _ _ _ _ hag' _

/-- An arrow is in a canonical possible object's extent exactly when it is in the extent of the
    witness's origin at the root. -/
theorem ccanon_mem_iff (hX : CluFlags) (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) (b : CAcc hF M₀) :
    b ∈ ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x hr)).1 ↔
      GMem hM₀ (groot hF M₀) b.1 (pathOf b.2.down) (pathOf_eq b.2.down) (rorig s x) := by
  rw [cagree_canon hX s i x _ hr]
  exact Iff.rfl

/-- ⭐Under T, a world's own arrow is in a canonical possible object's extent exactly when the
    world realises the witness. -/
theorem ccanon_own_mem (hX : CluFlags) (hT : ModalSys.T = true) (t : GW hF M₀) (K : ℕ)
    {z : VarSymb} {Z : VarType} (hz : (ctxOf (glat t K)).ref z = some (.VTypeDia Z))
    (hR : GR (groot hF M₀) t) :
    (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈ ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX t K).ref z hz)).1 ↔
      (gw hM₀ t).Realised z := by
  rw [cagree_canon hX t K z _ hz]
  exact cden_own_mem hX hM₀ hT t K hz _ hR

/-- ⭐The realisation's chain agrees with the canonical environment pushed along the world's own
    arrow (`cagree_diaPushR`, `cden_real_pre`). -/
theorem cagree_own (hX : CluFlags) (t : GW hF M₀) (K : ℕ) {z : VarSymb} {Z : VarType}
    (hz : (ctxOf (glat t K)).ref z = some (.VTypeDia Z)) (hr : (gw hM₀ t).Realised z)
    (hR : GR (groot hF M₀) t)
    (hm : (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈
      ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX t K).ref z hz)).1) :
    CAgree hM₀ hX (grealC hM₀ hr K ⟨Z, hz⟩) ((ccanonEnv hM₀ hX t K).diaPush z hz ⟨_, hm⟩) := by
  have hr' : (gw hM₀ t).Realised (kw (groot hF M₀) t (pathOf hR) (pathOf_eq hR) (rorig t z)) := by
    rw [kw_rorig hX hM₀ t K hz]
    exact hr
  have h₀ := cagree_diaPushR hX (.nil _) _ (cagree_canon hX t K) hz ⟨_, hm⟩ hr'
  intro v T hv
  rw [h₀ v T hv]
  refine ctoDom_congr hX ?_ _ _
  rw [GTr.app_comp, GTr.app_comp, preXKC_app, ← grealT_app, ← grealT_app]
  exact cden_real_pre hX hM₀ t K hz _ (pathOf_eq hR) hr' hr

/-- ⭐**A world's `◇_x` view along an arrow of `x`'s extent satisfies a formula exactly when the
    arrow's end satisfies its preimage translated along the root's path for `x`'s origin.** -/
theorem sat_diaPush_c (hX : CluFlags) (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x hr)).1) (P : List ℕ)
    (h : a.1.1.1 = nodeOf (groot hF M₀).1 P) (e : pathOf a.1.2.down = P)
    (hrl : ¬ (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 P h (rorig s x)))
    (hm : InExt (groot hF M₀) a.1.1 P h (rorig s x))
    (χ : WFF σ ((ctxOf (glat s i)).diaIn x) 0) :
    (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).diaPush x hr a) χ ↔
      (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX a.1.1 (pstg (groot hF M₀) a.1.1 P h (rstg s i)))
        (pTrXW hM₀ (groot hF M₀) a.1.1 P h (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hr⟩)
          hm (preWPX (rpre hX hM₀ s i) hr χ)) := by
  subst e
  have hag : CAgree hM₀ hX (preXC hM₀ hX s i ⟨X, hr⟩ a.1 hm)
      ((ccanonEnv hM₀ hX s i).diaPush x hr a) :=
    cagree_diaPush hX (.nil _) _ (cagree_canon hX s i) hr a hrl hm
  have hag' := cagree_envOf (hM₀ := hM₀) hX (ptrXC hM₀ (groot hF M₀) a.1.1 (pathOf a.1.2.down)
    (pathOf_eq a.1.2.down) (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hr⟩) hm)
    (Ctx.noProjLast_diaIn _ _)
  rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_diaIn _ _) _ _ _ _ (npl_ptrXC hM₀ _ _ _ _ _ _ _ hm)
    (Ctx.noProjLast_diaIn _ _) _ hag _ hag']
  refine (Model.sat_subst _ _ (coh_eS_kView (k := some x) (entOk_ofRen
    (itemOk_rpreX hX hM₀ s i ⟨X, hr⟩))) Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ χ).symm.trans ?_
  exact sat_ptrXC hX _ _ _ _ _ _ _ hm _ hag' _

/-- ⭐**A world's `◇_x` view along an arrow whose end realises the kept witness satisfies a formula
    exactly when the end's own arrow in the kept witness's view satisfies its preimage's kept
    translation.** -/
theorem sat_diaPush_cK (hX : CluFlags) (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x hr)).1) (P : List ℕ)
    (h : a.1.1.1 = nodeOf (groot hF M₀).1 P) (e : pathOf a.1.2.down = P)
    (hrl : (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 P h (rorig s x))) {Z : VarType}
    (hz : (ctxOf (glat a.1.1 (pstg (groot hF M₀) a.1.1 P h (rstg s i)))).ref
      (kw (groot hF M₀) a.1.1 P h (rorig s x)) = some (.VTypeDia Z))
    (hR : GR (groot hF M₀) a.1.1)
    (hmz : (⟨a.1.1, ⟨hR⟩⟩ : CAcc hF M₀) ∈ ((cmodel hF hM₀ hX).posEval
      ((ccanonEnv hM₀ hX a.1.1 (pstg (groot hF M₀) a.1.1 P h (rstg s i))).ref _ hz)).1)
    (χ : WFF σ ((ctxOf (glat s i)).diaIn x) 0) :
    (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).diaPush x hr a) χ ↔
      (cmodel hF hM₀ hX).sat
        ((ccanonEnv hM₀ hX a.1.1 (pstg (groot hF M₀) a.1.1 P h (rstg s i))).diaPush _ hz ⟨_, hmz⟩)
        (pTrXKW hM₀ (groot hF M₀) a.1.1 P h (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hr⟩)
          (preWPX (rpre hX hM₀ s i) hr χ)) := by
  subst e
  have hD := npl_grealC hM₀ hrl _ ⟨Z, hz⟩
  have hag : CAgree hM₀ hX ((preXKC hM₀ hX s i ⟨X, hr⟩ a.1).comp (grealC hM₀ hrl _ ⟨Z, hz⟩))
      ((ccanonEnv hM₀ hX s i).diaPush x hr a) :=
    cagree_diaPushR hX (.nil _) _ (cagree_canon hX s i) hr a hrl
  have hag₂ := cagree_own hX a.1.1 _ hz hrl hR hmz
  have hag' := cagree_envOf (hM₀ := hM₀) hX ((ptrXKC hM₀ (groot hF M₀) a.1.1 (pathOf a.1.2.down)
    (pathOf_eq a.1.2.down) (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hr⟩)).comp
      (grealC hM₀ hrl _ ⟨Z, hz⟩)) (Ctx.noProjLast_diaIn _ _)
  rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_diaIn _ _) _ _ _ _
    (GTr.npl_comp _ _ (npl_ptrXKC hM₀ _ _ _ _ _ _ _) hD) (Ctx.noProjLast_diaIn _ _) _ hag _ hag']
  refine (Model.sat_subst _ _ (coh_eS_kView (k := some x) (entOk_ofRen
    (itemOk_rpreX hX hM₀ s i ⟨X, hr⟩))) Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ χ).symm.trans ?_
  exact sat_ptrXKC hX _ _ _ _ _ _ _ _ hD _ _ hag' hag₂ _

/-! ## Atoms, stages, lifts -/

/-- The truth lemma for atoms. -/
theorem relSat_ccanon (hX : CluFlags) : ∀ {Γ : Ctx} {n : ℕ} (ρ : Rel σ Γ n) {s : GW hF M₀}
    {i : ℕ} {e : Γ.Le (ctxOf (glat s i))} {env : (cmodel hF hM₀ hX).Env Γ s},
    Model.Env.Agree e env (ccanonEnv hM₀ hX s i) → Γ.NoProjLast →
    ∀ (args : Fin n → (gw hM₀ s).D) (ts : Fin n → Term σ Γ .Var .var),
      (∀ k, args k = (gw hM₀ s).cls i (Term.mono e (ts k))) →
      (Model.relSat env ρ args ↔
        WFF.mono e (.atom ((Spine.ofFn ts).fillR ρ)) ∈ (gw hM₀ s).M i)
  | _, _, .R ⟨r, rfl⟩, s, i, e, _, _, _, args, ts, hts => by
      change (gw hM₀ s).canonRel r (fun k => args (Fin.cast rfl k)) ↔ _
      rw [WFF.mono_fillR, Spine.mono_ofFn,
        show (fun k => args (Fin.cast rfl k)) = fun k => (gw hM₀ s).cls i (Term.mono e (ts k)) from
          funext fun k => hts k,
        BWorld.canonRel_cls]
      rfl
  | _, _, .eval ρ t, s, i, e, env, hag, hΓ, args, ts, hts => by
      change Model.relSat env ρ (Fin.cons (Model.interp env t) args) ↔ _
      have h0 : Model.interp env t = (gw hM₀ s).cls i (Term.mono e t) :=
        (interp_ccanon hX t hag hΓ).trans (cden_var_mono hX e t)
      rw [relSat_ccanon hX ρ hag hΓ (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
        (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
      rfl

/-- The canonical environment at a later stage agrees with the one at an earlier stage. -/
theorem ccanonEnv_le (hX : CluFlags) (s : GW hF M₀) {i j : ℕ} (hij : i ≤ j) :
    Model.Env.Agree ((gw hM₀ s).le hij) (ccanonEnv hM₀ hX s i) (ccanonEnv hM₀ hX s j) :=
  fun v T hv => ctoDom_congr hX (by
    rw [show Term.eta (σ := σ) v T _ = Term.mono ((gw hM₀ s).le hij) (Term.eta v T _) from
      (Term.mono_eta _ v T _).symm, cden_mono]
    exact cden_congr hX _ _ _ _ _ _) _ _

/-- A denotable object is the value of a term at a later stage. -/
theorem cinterp_lift (hX : CluFlags) {A : VarType} {s : GW hF M₀} {i i' : ℕ} {a : Ann A}
    {t' : Term σ (ctxOf (glat s i')) A a} {o : (cframe hF hM₀ hX).Dom A s}
    (ht' : cden hM₀ hX s i' (Ctx.Le.refl _) t' = cfromDom hM₀ hX A s o) (hK : i' ≤ i) :
    Model.interp (ccanonEnv hM₀ hX s i) ((gw hM₀ s).liftT hK t') = o :=
  (interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).trans
    ((ctoDom_congr hX ((cden_mono hX _ t' s _ _).trans ((cden_congr hX t' s _ i' _ _).trans ht'))
      _ _).trans (ctoDom_fromDom hM₀ hX A s o))

/-! ## The realised possibilities -/

theorem size_preWP (hX : CluFlags) (s : GW hF M₀) (i : ℕ)
    (χ : WFF σ ((ctxOf (glat s i)).kView none) 0) :
    (preWP (rpre hX hM₀ s i) χ).size = χ.size :=
  WFF.size_subst _ _ _ _ _ _

theorem size_preWPX (hX : CluFlags) (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (χ : WFF σ ((ctxOf (glat s i)).diaIn x) 0) :
    (preWPX (rpre hX hM₀ s i) hr χ).size = χ.size :=
  WFF.size_subst _ _ _ _ _ _

variable (hF hM₀) in
/-- The truth lemma below a size, at every world and stage: what the `◇` case receives. -/
abbrev CTruthBelow (hX : CluFlags) (n : ℕ) : Prop :=
  ∀ (t : GW hF M₀) (j : ℕ) (φ : WFF σ (ctxOf (glat t j)) 0), φ.size < n →
    ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX t j) φ ↔ φ ∈ (gw hM₀ t).M j)

/-- Under T, a realised witness's possible object has, along the world's own arrow, the datum's
    content, read at any stage above it. -/
theorem ccanon_cont_real (hX : CluFlags) (t : GW hF M₀) {y : VarSymb}
    (hrl : (gw hM₀ t).Realised y) {K : ℕ} (hK : hrl.data.i₀ ≤ K)
    (hdecl : (ctxOf (glat t K)).ref y = some (.VTypeDia hrl.data.A))
    (hR : GR (groot hF M₀) t)
    (hm : (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈
      ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX t K).ref y hdecl)).1) :
    ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX t K).ref y hdecl)).2 ⟨_, hm⟩ =
      Model.interp (ccanonEnv hM₀ hX t K) (Term.mono (gle hM₀ t hK) hrl.data.t₀) := by
  have hpq := cagree_canon (hM₀ := hM₀) hX t K y _ hdecl
  have hm₁ := hpq ▸ hm
  rw [Model.posEval_snd_congr hpq ⟨_, hm⟩ hm₁,
    Model.interp_mono (ccanonEnv_le hX t hK) hrl.data.t₀,
    interp_ccanon hX hrl.data.t₀ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
  exact ctoDom_congr hX ((cden_own_content hX hM₀ t K hdecl _ hR hm₁ hrl).trans
    (cden_grealT_eta hX hrl ⟨_, hdecl⟩ (Ctx.ref_diaIn_of hdecl))) _ _

/-- ⭐**Under T, what holds in a witness's view along an arrow whose end realises the kept witness
    is not `□_x`-impossible** (`gdia_real_not_boxx`, from the witness's origin at the root). -/
theorem cdia_real_not_boxx (hX : CluFlags) (hT : ModalSys.T = true) {n : ℕ}
    (IH : CTruthBelow hF hM₀ hX n) (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x hr)).1)
    (hrl : (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 (pathOf a.1.2.down)
      (pathOf_eq a.1.2.down) (rorig s x)))
    (χ : WFF σ ((ctxOf (glat s i)).diaIn x) 0) (hχs : χ.size < n)
    (hsat : (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).diaPush x hr a) χ)
    (hbx : WFF.boxx (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hr⟩)
      (preWPX (rpre hX hM₀ s i) hr χ).neg ∈ (gw hM₀ (groot hF M₀)).M (rstg s i)) : False := by
  set t := a.1.1 with ht
  have hR : GR (groot hF M₀) t := (carrows hF M₀).refl hT t
  set P := pathOf a.1.2.down with hPd
  have hPe : t.1 = nodeOf (groot hF M₀).1 P := pathOf_eq a.1.2.down
  obtain ⟨Z, hz⟩ := kw_decl hM₀ (groot hF M₀) t P hPe (rstg s i) (rorig_ref hX hM₀ s i ⟨X, hr⟩)
  have hZA : Z = hrl.data.A := by
    have h1 := (hrl.data.hdeclOf _ ⟨Z, hz⟩).symm.trans hz
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hZA
  have hmz := (ccanon_own_mem hX hT t _ hz hR).mpr hrl
  have hs₁ := (sat_diaPush_cK hX s i hr a P hPe rfl hrl hz hR hmz χ).mp hsat
  have hj : pstg (groot hF M₀) t P hPe (rstg s i) ≤
      max (pstg (groot hF M₀) t P hPe (rstg s i)) hrl.data.i₀ := le_max_left _ _
  have hK : hrl.data.i₀ ≤ max (pstg (groot hF M₀) t P hPe (rstg s i)) hrl.data.i₀ :=
    le_max_right _ _
  have hdecl := (gle hM₀ t hj).ref hz
  have hm' := (ccanon_own_mem hX hT t _ hdecl hR).mpr hrl
  have hsatR := (Model.sat_realiseAtA hT (ccanonEnv hM₀ hX t _) (Ctx.Presented.noProjLast _) hdecl
    (Term.mono (gle hM₀ t hK) hrl.data.t₀) hm' (ccanon_cont_real hX t hrl hK hdecl hR hm')
    (WFF.mono ((gle hM₀ t hj).diaIn _) (pTrXKW hM₀ (groot hF M₀) t P hPe (rstg s i) (rorig s x)
      (rorig_ref hX hM₀ s i ⟨X, hr⟩) (preWPX (rpre hX hM₀ s i) hr χ)))).mpr
    ((Model.sat_mono (Model.Env.diaPush_agree (ccanonEnv_le hX t hj) hz ⟨_, hmz⟩ hm') _).mpr hs₁)
  have hrm := (IH t _ _ (by
    rw [WFF.size_realiseAtA, WFF.size_mono, size_pTrXKW, size_preWPX (hM₀ := hM₀) hX]
    exact hχs)).mp hsatR
  have hbK := boxx_mem_pathK (hM₀ := hM₀) (groot hF M₀) t P hPe (rstg s i) (rorig s x)
    (rorig_ref hX hM₀ s i ⟨X, hr⟩) _ hbx
  rw [pTrXKW_neg] at hbK
  have hn : WFF.realiseAtA hT _ hdecl (Term.mono (gle hM₀ t hK) hrl.data.t₀)
      (WFF.mono ((gle hM₀ t hj).diaIn _) (pTrXKW hM₀ (groot hF M₀) t P hPe (rstg s i) (rorig s x)
        (rorig_ref hX hM₀ s i ⟨X, hr⟩) (preWPX (rpre hX hM₀ s i) hr χ))).neg ∈
        (gw hM₀ t).M _ := by
    refine BWorld.mem_of_provable (Δ := [WFF.hereAt hT _ hdecl
        (Term.mono (gle hM₀ t hK) hrl.data.t₀), WFF.mono (gle hM₀ t hj) (WFF.boxx _ ⟨_, hz⟩
          (pTrXKW hM₀ (groot hF M₀) t P hPe (rstg s i) (rorig s x)
            (rorig_ref hX hM₀ s i ⟨X, hr⟩) (preWPX (rpre hX hM₀ s i) hr χ)).neg)]) ?_
      ⟨Proof.here_elimAtA hT _ hdecl _ _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ'
    · exact BWorld.mem_T.mp (hrl.data.hhereAt (gw hM₀ t).mcsT _ hK hdecl)
    · rw [List.mem_singleton.mp hφ']
      exact (BWorld.mem_lift hj).mp hbK
  rw [WFF.realiseAtA_neg] at hn
  exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hn hrm

/-- ⭐**Under T, a possible formula of the root's theory holds along the edge made for its
    witness** (`gdia_sat_child`), read at any world whose witness it is the origin of. -/
theorem cdia_sat_child (hX : CluFlags) (hT : ModalSys.T = true) {n : ℕ}
    (IH : CTruthBelow hF hM₀ hX n) (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (h : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (χ : WFF σ ((ctxOf (glat s i)).diaIn x) 0) (hχs : χ.size < n)
    (hmem : WFF.dia (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩) (preWPX (rpre hX hM₀ s i) h χ) ∈
      (gw hM₀ (groot hF M₀)).M (rstg s i)) :
    ∃ a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1,
      (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).diaPush x h a) χ := by
  have hrx : (ctxOf (glat (groot hF M₀) (rstg s i))).ref (rorig s x) = some (.VTypeDia X) :=
    rpre hX hM₀ s i x _ h rfl
  obtain ⟨t, ⟨c, hc⟩, hk, ⟨y, hfy⟩, ⟨b, hfd⟩, hm⟩ := glexX hM₀ (groot hF M₀) (rstg s i)
    (rorig s x) X hrx _ hmem
  have hwy : wit t (rorig s x) = y := wit_of_inl (reach_ppath hrx).1 hfy
  have hfk : fmapL hF M₀ t.1 (.step (rorig s x) .keep) = .inl (wit t (rorig s x)) := by
    rw [hwy]
    exact hfy
  have hR : GR (groot hF M₀) t := ⟨[c], pathOk_cons, hc⟩
  have hrl : (gw hM₀ t).Realised (wit t (rorig s x)) :=
    grealised_wit hM₀ hT ⟨c, hc⟩ hk (rstg s i) hrx
  have hmt : (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈
      ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1 :=
    (ccanon_mem_iff hX s i h _).mpr ((gmem_path hR (P := [c]) hc).mpr (Or.inl hrl))
  refine ⟨⟨_, hmt⟩, ?_⟩
  have hwd : (ctxOf (glat t (glstg (groot hF M₀) t (rstg s i)))).ref (wit t (rorig s x)) =
      some (.VTypeDia X) := by
    have := ok_eS_kView (gentOk_box hM₀ ⟨c, hc⟩ (rstg s i)) (.step (rorig s x) .keep)
      (.VTypeDia X) rfl ((Ctx.ref_nonproj _ rfl).symm.trans (Ctx.ref_keep_of' hF hrx
        VarType.keepable_dia))
    rw [eS_item _ rfl, hfk] at this
    exact this
  have hbd : (ctxOf (glat t (glstg (groot hF M₀) t (rstg s i)))).ref b = some X := by
    have := ok_eS_kView (l := glat (groot hF M₀) (rstg s i)) (k := some (rorig s x))
      (hk ▸ gentOk hM₀ ⟨c, hc⟩ (rstg s i)) (.step (rorig s x) .dia) X rfl
      ((Ctx.ref_nonproj _ rfl).symm.trans (Ctx.ref_diaIn_of hrx))
    rw [eS_item _ rfl, hfd] at this
    exact this
  have hRr : GR (groot hF M₀) t := (carrows hF M₀).refl hT t
  have hmz := (ccanon_own_mem hX hT t _ hwd hRr).mpr hrl
  have hsatK : (cmodel hF hM₀ hX).sat
      ((ccanonEnv hM₀ hX t (glstg (groot hF M₀) t (rstg s i))).diaPush _ hwd ⟨_, hmz⟩)
      (pTrXKW hM₀ (groot hF M₀) t [c] hc (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩)
        (preWPX (rpre hX hM₀ s i) h χ)) := by
    have hmK : WFF.realiseAtA hT (wit t (rorig s x)) hwd (Term.eta b X hbd)
        (pTrXKW hM₀ (groot hF M₀) t [c] hc (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩)
          (preWPX (rpre hX hM₀ s i) h χ)) ∈
        (gw hM₀ t).M (glstg (groot hF M₀) t (rstg s i)) := by
      rw [gchild_real (hM₀ := hM₀) hT hc hk (rstg s i) hrx hfk hfd hwd hbd _]
      exact hm
    have hXA : X = hrl.data.A := by
      have h1 := (hrl.data.hdeclOf _ ⟨X, hwd⟩).symm.trans hwd
      simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
      exact h1.symm
    subst hXA
    have hj : glstg (groot hF M₀) t (rstg s i) ≤
        max (glstg (groot hF M₀) t (rstg s i)) hrl.data.i₀ := le_max_left _ _
    have hK : hrl.data.i₀ ≤ max (glstg (groot hF M₀) t (rstg s i)) hrl.data.i₀ := le_max_right _ _
    have hdecl := (gle hM₀ t hj).ref hwd
    have hbK := (gle hM₀ t hj).ref hbd
    have hH₁ : WFF.hereAt hT (wit t (rorig s x)) hdecl (Term.eta b _ hbK) ∈ (gw hM₀ t).M _ := by
      have := (BWorld.mem_lift hj).mp
        (gchild_here (hM₀ := hM₀) hT hc hk (rstg s i) hrx hfk hfd hwd hbd)
      change WFF.here hT (Term.mono _ (Term.eta _ _ _)) (Term.mono _ (Term.eta _ _ _)) ∈ _ at this
      rwa [Term.mono_eta, Term.mono_eta] at this
    have hH₂ := BWorld.mem_T.mp (hrl.data.hhereAt (gw hM₀ t).mcsT _ hK hdecl)
    have hR₁ : WFF.realiseAtA hT (wit t (rorig s x)) hdecl (Term.eta b _ hbK)
        (WFF.mono ((gle hM₀ t hj).diaIn _) (pTrXKW hM₀ (groot hF M₀) t [c] hc (rstg s i)
          (rorig s x) (rorig_ref hX hM₀ s i ⟨_, h⟩) (preWPX (rpre hX hM₀ s i) h χ))) ∈
          (gw hM₀ t).M _ := by
      have := (BWorld.mem_lift hj).mp hmK
      rwa [WFF.mono_realiseAtA hT (gle hM₀ t hj) hwd hdecl, Term.mono_eta] at this
    have hR₂ : WFF.realiseAtA hT (wit t (rorig s x)) hdecl (Term.mono (gle hM₀ t hK) hrl.data.t₀)
        (WFF.mono ((gle hM₀ t hj).diaIn _) (pTrXKW hM₀ (groot hF M₀) t [c] hc (rstg s i)
          (rorig s x) (rorig_ref hX hM₀ s i ⟨_, h⟩) (preWPX (rpre hX hM₀ s i) h χ))) ∈
          (gw hM₀ t).M _ :=
      BWorld.mem_of_provable (Δ := [_, _, _]) (fun φ hφ => by
          rcases List.mem_cons.mp hφ with rfl | hφ
          · exact hH₁
          rcases List.mem_cons.mp hφ with rfl | hφ
          · exact hH₂
          · rw [List.mem_singleton.mp hφ]
            exact hR₁)
        ⟨Proof.here_subst hT _ _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
          (Proof.lookup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
    have hm' := (ccanon_own_mem hX hT t _ hdecl hRr).mpr hrl
    have hsatR := (IH t _ _ (by
      rw [WFF.size_realiseAtA, WFF.size_mono, size_pTrXKW, size_preWPX (hM₀ := hM₀) hX]
      exact hχs)).mpr hR₂
    have hs₁ := (Model.sat_realiseAtA hT (ccanonEnv hM₀ hX t _) (Ctx.Presented.noProjLast _) hdecl
      (Term.mono (gle hM₀ t hK) hrl.data.t₀) hm' (ccanon_cont_real hX t hrl hK hdecl hRr hm')
      _).mp hsatR
    exact (Model.sat_mono (Model.Env.diaPush_agree (ccanonEnv_le hX t hj) hwd ⟨_, hmz⟩ hm') _).mp
      hs₁
  have hPe : pathOf hR = [c] := pathOf_of hR hc
  have hrl' : (gw hM₀ (⟨⟨t, ⟨hR⟩⟩, hmt⟩ :
      ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1).1.1).Realised
      (kw (groot hF M₀) t [c] hc (rorig s x)) := hrl
  exact (sat_diaPush_cK hX s i h ⟨_, hmt⟩ [c] hc hPe hrl' hwd hRr hmz χ).mpr hsatK

/-! ## What `Here` says -/

variable (hM₀) in
/-- The truth lemma at the equations of one type: what the `here` case receives. -/
abbrev CEqTruth (hX : CluFlags) (s : GW hF M₀) (A : VarType) : Prop :=
  ∀ (K : ℕ) {b : Ann A} (u u' : Term σ (ctxOf (glat s K)) A b),
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s K) (eqRec A u u' : WFF σ (ctxOf (glat s K)) 0) ↔
      eqRec A u u' ∈ (gw hM₀ s).M K

/-- ⭐**Equal denotations carry `Here` facts** (`ghere_transfer`). -/
theorem chere_transfer (hX : CluFlags) (hT : ModalSys.T = true) {s : GW hF M₀} {A : VarType}
    (IH : CEqTruth hM₀ hX s A) {K : ℕ} {c : Ann (.VTypeDia A)}
    (S : Term σ (ctxOf (glat s K)) (.VTypeDia A) c) {b b' : Ann A}
    (r : Term σ (ctxOf (glat s K)) A b) (r' : Term σ (ctxOf (glat s K)) A b')
    (he : cden hM₀ hX s K (Ctx.Le.refl _) r = cden hM₀ hX s K (Ctx.Le.refl _) r')
    (hmem : WFF.here hT S r ∈ (gw hM₀ s).M K) :
    WFF.here hT S r' ∈ (gw hM₀ s).M K := by
  obtain rfl := ann_eq_of_cden hX hT r r' he
  have heq : eqRec A r r' ∈ (gw hM₀ s).M K := by
    refine (IH K r r').mp ((Model.sat_eqRec _ A r r').mpr ?_)
    rw [interp_ccanon hX r (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
      interp_ccanon hX r' (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
    exact ctoDom_congr hX he _ _
  refine BWorld.mem_of_provable (Δ := [WFF.here hT S r, eqRec A r r']) (fun ψ hψ => ?_)
    ⟨Proof.here_eq hT S r r' (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hmem
  · rw [List.mem_singleton.mp hψ]
    exact heq

/-- Under T, a realised witness's view along the world's own arrow reads a body as the body
    realised by the datum's content (`ginterp_dia_self`). -/
theorem cinterp_dia_self (hX : CluFlags) (hT : ModalSys.T = true) {s : GW hF M₀} {i : ℕ}
    {x : VarSymb} (hr : (gw hM₀ s).Realised x) {X : VarType}
    (h : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : (cmodel hF hM₀ hX).frame.reflAcc hT s ∈
      ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1)
    {A : VarType} {β : Ann A} (bd : Term σ ((ctxOf (glat s i)).diaIn x) A β) :
    Model.interp ((ccanonEnv hM₀ hX s i).diaPush x h ⟨_, hm⟩) bd =
      ctoDom hM₀ hX A s (cden hM₀ hX s (max i hr.data.i₀) (Ctx.Le.refl _)
        (grealT hr (Ctx.Le.refl _) ⟨X, h⟩ bd).2) (cdefinable_den hX _ _) := by
  have hXA : X = hr.data.A := by
    have h1 := (hr.data.hdeclOf _ ⟨X, h⟩).symm.trans h
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hXA
  have hj : i ≤ max i hr.data.i₀ := le_max_left _ _
  have hK : hr.data.i₀ ≤ max i hr.data.i₀ := le_max_right _ _
  have hdecl : (ctxOf (glat s (max i hr.data.i₀))).ref x = some (.VTypeDia hr.data.A) :=
    (gle hM₀ s hj).ref h
  have hR : GR (groot hF M₀) s := (carrows hF M₀).refl hT s
  have hm' := (ccanon_own_mem hX hT s _ hdecl hR).mpr hr
  calc Model.interp ((ccanonEnv hM₀ hX s i).diaPush x h ⟨_, hm⟩) bd
      = Model.interp ((ccanonEnv hM₀ hX s _).diaPush x hdecl ⟨_, hm'⟩)
          (Term.mono ((gle hM₀ s hj).diaIn x) bd) :=
        (Model.interp_mono (Model.Env.diaPush_agree (ccanonEnv_le hX s hj) h ⟨_, hm⟩ hm') bd).symm
    _ = Model.interp (ccanonEnv hM₀ hX s _) (Term.realiseAtA hT x hdecl
          (Term.mono (gle hM₀ s hK) hr.data.t₀) (Term.mono ((gle hM₀ s hj).diaIn x) bd)) :=
        (Model.interp_realiseAtA hT (ccanonEnv hM₀ hX s _) (Ctx.Presented.noProjLast _) hdecl
          (Term.mono (gle hM₀ s hK) hr.data.t₀) hm' (ccanon_cont_real hX s hr hK hdecl hR hm')
          _).symm
    _ = _ := interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)

/-- ⭐⭐**The truth lemma's `here` case** (`ghere_truth`). -/
theorem chere_truth (hX : CluFlags) (hT : ModalSys.T = true) {s : GW hF M₀} {i : ℕ}
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType}
    {β : Ann A} (bd : Term σ ((ctxOf (glat s i)).diaIn x) A β) {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a) (IH : CEqTruth hM₀ hX s A) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i)
        (WFF.here hT (Term.diatm x hx bd) t : WFF σ _ 0) ↔
      WFF.here hT (Term.diatm x hx bd) t ∈ (gw hM₀ s).M i := by
  obtain ⟨X, h⟩ := id hx
  rw [Model.sat_here_diatm hT (ccanonEnv hM₀ hX s i) hx h t bd]
  have hD : Model.interp (ccanonEnv hM₀ hX s i) t =
      ctoDom hM₀ hX A s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _) :=
    interp_ccanon hX t (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)
  have hR : GR (groot hF M₀) s := (carrows hF M₀).refl hT s
  constructor
  · rintro ⟨hm, hind⟩
    obtain ⟨u, u', hu, hu', hrel⟩ := hind.1 hT
    have hr : (gw hM₀ s).Realised x := (ccanon_own_mem hX hT s i h hR).mp hm
    rw [cinterp_dia_self hX hT hr h hm bd, cfromDom_toDom] at hu
    rw [hD, cfromDom_toDom] at hu'
    have hkK : max i hr.data.i₀ ≤ max (max i hr.data.i₀) (max u.i u'.i) := le_max_left _ _
    have hiK : i ≤ max (max i hr.data.i₀) (max u.i u'.i) := (le_max_left _ _).trans hkK
    have huK : u.i ≤ max (max i hr.data.i₀) (max u.i u'.i) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hu'K : u'.i ≤ max (max i hr.data.i₀) (max u.i u'.i) :=
      (le_max_right _ _).trans (le_max_right _ _)
    have h₁ : WFF.here hT (Term.mono (gle hM₀ s hiK) (Term.diatm x hx bd))
        (Term.mono (gle hM₀ s hkK) (grealT hr (Ctx.Le.refl _) hx bd).2) ∈
          (gw hM₀ s).M (max (max i hr.data.i₀) (max u.i u'.i)) := by
      have := (BWorld.mem_lift hkK).mp (gmem_here_real hr h bd)
      change WFF.here hT (Term.mono _ (Term.mono _ (Term.diatm x hx bd))) _ ∈ (gw hM₀ s).M _
        at this
      rwa [Term.mono_mono] at this
    have h₂ := chere_transfer hX hT IH _ _ (u.lift _ huK)
      ((cden_lift hX hkK _).trans (hu.symm.trans (cden_lift hX huK u.t).symm)) h₁
    have h₃ : WFF.here hT (Term.mono (gle hM₀ s hiK) (Term.diatm x hx bd)) (u'.lift _ hu'K) ∈
        (gw hM₀ s).M (max (max i hr.data.i₀) (max u.i u'.i)) := by
      have key := hrel _ huK hu'K (WFF.here hT
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots
          (Γ := ctxOf (glat s (max (max i hr.data.i₀) (max u.i u'.i))))).root A)
          (Term.mono (gle hM₀ s hiK) (Term.diatm x hx bd)))
        (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A)))
      rw [WFF.instantiate_here_slot, WFF.instantiate_here_slot] at key
      exact key.mp h₂
    have h₄ := chere_transfer hX hT IH _ _ (Term.mono (gle hM₀ s hiK) t)
      ((cden_lift hX hu'K u'.t).trans (hu'.trans (cden_lift hX hiK t).symm)) h₃
    exact (BWorld.mem_lift hiK).mpr h₄
  · intro hmem
    have hr : (gw hM₀ s).Realised x := (gw hM₀ s).datum_of_here hT h bd t hmem
    have hm : (cmodel hF hM₀ hX).frame.reflAcc hT s ∈
        ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1 :=
      (ccanon_own_mem hX hT s i h hR).mpr hr
    refine ⟨hm, fun _ => ⟨_, ⟨i, a, t⟩, ?_, ?_, grel_here hT hx bd t hr hmem⟩, fun hnT => ?_⟩
    · rw [cinterp_dia_self hX hT hr h hm bd, cfromDom_toDom]
    · rw [hD, cfromDom_toDom]
    · rw [hT] at hnT
      cases hnT

/-! ## The truth lemma -/

/-- ⭐**The truth lemma below a size, at every world and stage.** -/
theorem ctruth_lt (hX : CluFlags) :
    ∀ (n : ℕ) (s : GW hF M₀) (i : ℕ) (φ : WFF σ (ctxOf (glat s i)) 0), φ.size < n →
    ((cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) φ ↔ φ ∈ (gw hM₀ s).M i)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, i, φ, hφ => by
      cases φ with
      | atom ρ =>
          change Model.relSat (ccanonEnv hM₀ hX s i) ρ Fin.elim0 ↔ _
          rw [relSat_ccanon hX ρ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)
            Fin.elim0 Fin.elim0 (fun k => k.elim0)]
          change WFF.mono (Ctx.Le.refl _) (.atom ρ) ∈ (gw hM₀ s).M i ↔ _
          rw [WFF.mono_refl]
      | eq t u =>
          change Model.interp (ccanonEnv hM₀ hX s i) t =
            Model.interp (ccanonEnv hM₀ hX s i) u ↔ _
          rw [interp_ccanon hX t (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
            interp_ccanon hX u (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
          change cden hM₀ hX s i (Ctx.Le.refl _) t = cden hM₀ hX s i (Ctx.Le.refl _) u ↔ _
          rw [cden_var_cls, cden_var_cls, BWorld.cls_eq_iff (le_refl i) (le_refl i)]
          change WFF.eq (Term.mono ((gw hM₀ s).le (le_refl i)) t)
            (Term.mono ((gw hM₀ s).le (le_refl i)) u) ∈ (gw hM₀ s).M i ↔ _
          rw [Term.mono_refl, Term.mono_refl]
      | top => exact ⟨fun _ => ((gw hM₀ s).mcs i).top_mem, fun _ => trivial⟩
      | bot => exact ⟨False.elim, fun h => ((gw hM₀ s).mcs i).bot_not_mem h⟩
      | here hT S t =>
          cases S with
          | diatm x hx bd =>
              exact chere_truth hX hT hx bd t
                (fun K _ u u' => ctruth_lt hX n s K _ (by
                  rw [WFF.size_eqRec]; simp only [WFF.size] at hφ; omega))
      | back hB _ _ _ => exact (hX.absBS hB).elim
      | retS hB _ _ _ => exact (hX.absBS hB).elim
      | retxS hB _ _ _ _ _ => exact (hX.absBS hB).elim
      | and φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∧ _ ↔ _
          rw [ctruth_lt hX n s i φ h₁, ctruth_lt hX n s i ψ h₂, ((gw hM₀ s).mcs i).and_mem_iff]
      | or φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∨ _ ↔ _
          rw [ctruth_lt hX n s i φ h₁, ctruth_lt hX n s i ψ h₂, ((gw hM₀ s).mcs i).or_mem_iff]
      | imp φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (_ → _) ↔ _
          rw [ctruth_lt hX n s i φ h₁, ctruth_lt hX n s i ψ h₂, ((gw hM₀ s).mcs i).imp_mem_iff]
      | all A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ o : (cframe hF hM₀ hX).Dom A s,
            (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨i', hi, a, t, hmem⟩ := (gw hM₀ s).allW (((gw hM₀ s).mcs i).neg_mem_iff.mpr hnot)
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hi) (.bnd 0)
              (Model.interp (ccanonEnv hM₀ hX s i') t)) ψ).mpr (hsat _)
            have hs₂ := (Model.sat_instantiate (ccanonEnv hM₀ hX s i')
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots t _).mpr hs₁
            have hs₃ := (ctruth_lt hX n s i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (((gw hM₀ s).mcs i').neg_mem_iff.mp hmem) hs₃
          · intro hmem o
            obtain ⟨i', a, t', ht'⟩ := cdefinable_fromDom hM₀ hX A s o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hinst : WFF.instantiate Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t')
                (WFF.mono (((gw hM₀ s).le hK).insert (.bnd 0) A) ψ) ∈ (gw hM₀ s).M (i ⊔ i') :=
              BWorld.mem_of_provable
                (Δ := [WFF.all A (WFF.mono (((gw hM₀ s).le hK).insert (.bnd 0) A) ψ)])
                (fun χ hχ => by
                  rw [List.mem_singleton.mp hχ]
                  exact (BWorld.mem_lift hK).mp hmem)
                ⟨Proof.all_elim A ((gw hM₀ s).liftT hK' t') (Proof.lookup List.mem_cons_self)⟩
            have hs := (ctruth_lt hX n s (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hinst
            have hs₁ := (Model.sat_instantiate (ccanonEnv hM₀ hX s (i ⊔ i'))
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t') _).mp hs
            rw [cinterp_lift hX ht' hK'] at hs₁
            exact (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hK) (.bnd 0) o)
              ψ).mp hs₁
      | ex A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ o : (cframe hF hM₀ hX).Dom A s,
            (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · rintro ⟨o, hsat⟩
            obtain ⟨i', a, t', ht'⟩ := cdefinable_fromDom hM₀ hX A s o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hK) (.bnd 0) o)
              ψ).mpr hsat
            rw [← cinterp_lift hX ht' hK'] at hs₁
            have hs₂ := (Model.sat_instantiate (ccanonEnv hM₀ hX s (i ⊔ i'))
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t') _).mpr hs₁
            have hmemK := (ctruth_lt hX n s (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (BWorld.mem_lift hK).mpr (BWorld.mem_of_provable
              (Δ := [WFF.instantiate Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t')
                (WFF.mono (((gw hM₀ s).le hK).insert (.bnd 0) A) ψ)])
              (fun χ hχ => by
                rw [List.mem_singleton.mp hχ]
                exact hmemK)
              ⟨Proof.ex_intro A ((gw hM₀ s).liftT hK' t') (Proof.lookup List.mem_cons_self)⟩)
          · intro hmem
            obtain ⟨i', hi, a, t, hmem'⟩ := (gw hM₀ s).exW_term hmem
            refine ⟨Model.interp (ccanonEnv hM₀ hX s i') t, ?_⟩
            have hs := (ctruth_lt hX n s i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hmem'
            have hs₁ := (Model.sat_instantiate (ccanonEnv hM₀ hX s i') (Ctx.Presented.noProjLast _)
              Ctx.NoSlots.slots t _).mp hs
            exact (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hi) (.bnd 0) _)
              ψ).mp hs₁
      | box χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          have hpath := box_pathO_iff hX.five hX.fourS hX.fourSW hM₀ (rpath s)
            (groot hF M₀) s (rpath_eq s) i χ
          change (∀ a : CAcc hF M₀,
            (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).boxPush a) χ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            have hn' : WFF.box (preWP (rpre hX hM₀ s i) χ) ∉
                (gw hM₀ (groot hF M₀)).M (rstg s i) := fun h => hnot (hpath.mp h)
            obtain ⟨t, ⟨c, hc⟩, -, hneg⟩ := glex hM₀ (groot hF M₀) (rstg s i) _ hn'
            have hR : GR (groot hF M₀) t := ⟨[c], pathOk_cons, hc⟩
            have h1 := (sat_boxPush_c hX s i ⟨t, ⟨hR⟩⟩ [c] hc pathOk_cons (pathOf_of hR hc)
              χ).mp (hsat ⟨t, ⟨hR⟩⟩)
            have h2 := (ctruth_lt hX n t _ _ (by
              rw [size_pTrW, size_preWP (hM₀ := hM₀) hX]; exact hχs)).mp h1
            exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem a
            refine (sat_boxPush_c hX s i a (pathOf a.2.down) (pathOf_eq a.2.down)
              (pathOf_ok a.2.down) rfl χ).mpr ?_
            exact (ctruth_lt hX n a.1 _ _ (by
              rw [size_pTrW, size_preWP (hM₀ := hM₀) hX]; exact hχs)).mpr
              (box_mem_path hM₀ (groot hF M₀) a.1 _ (pathOf_eq a.2.down) (pathOf_ok a.2.down)
                (rstg s i) _ (hpath.mpr hmem))
      | dia x hx χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
            (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1),
              (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).diaPush x h a) χ) ↔ _
          have IH : CTruthBelow hF hM₀ hX n := fun t j φ hφ => ctruth_lt hX n t j φ hφ
          constructor
          · rintro ⟨X, h, a, hsat⟩
            by_contra hnot
            have hpath := dia_pathO_iff hX.five hX.fourS hX.fourSW hM₀
              (rpath s) (groot hF M₀) s (rpath_eq s) i h χ
            have hnot' : ¬ WFF.dia (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩)
                (preWPX (rpre hX hM₀ s i) h χ) ∈
                (gw hM₀ (groot hF M₀)).M (rstg s i) := fun hd => hnot (hpath.mp hd)
            have hbx : WFF.boxx (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩)
                (preWPX (rpre hX hM₀ s i) h χ).neg ∈
                (gw hM₀ (groot hF M₀)).M (rstg s i) :=
              BWorld.mem_of_provable (Δ := [(WFF.dia (rorig s x) (rorig_ref hX hM₀ s i ⟨X, h⟩)
                  (preWPX (rpre hX hM₀ s i) h χ)).neg])
                (fun ψ hψ => by
                  rw [List.mem_singleton.mp hψ]
                  exact ((gw hM₀ (groot hF M₀)).mcs _).neg_mem_iff.mpr hnot')
                ⟨Proof.boxx_neg_of_not_dia (Γ := (gw hM₀ (groot hF M₀)).ctx (rstg s i)) _ _ _⟩
            have hg := (ccanon_mem_iff hX s i h a.1).mp a.2
            by_cases hrl : (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 (pathOf a.1.2.down)
                (pathOf_eq a.1.2.down) (rorig s x))
            · exact cdia_real_not_boxx hX hrl.T IH s i h a hrl χ hχs hsat hbx
            obtain ⟨-, hm⟩ := Or.resolve_left hg hrl
            have h1 := (sat_diaPush_c hX s i h a _ (pathOf_eq a.1.2.down) rfl hrl hm χ).mp hsat
            have h2 := (ctruth_lt hX n a.1.1 _ _ (by
              rw [size_pTrXW, size_preWPX (hM₀ := hM₀) hX]; exact hχs)).mp h1
            have hneg := boxx_mem_path (hM₀ := hM₀) (groot hF M₀) a.1.1 _ (pathOf_eq a.1.2.down)
              (rstg s i) (rorig s x) _ hm _ hbx
            rw [pTrXW_neg] at hneg
            exact ((gw hM₀ a.1.1).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem
            obtain ⟨X, h⟩ := id hx
            have hpath := dia_pathO_iff hX.five hX.fourS hX.fourSW hM₀
              (rpath s) (groot hF M₀) s (rpath_eq s) i h χ
            by_cases hT : ModalSys.T = true
            · obtain ⟨a, ha⟩ := cdia_sat_child hX hT IH s i h χ hχs (hpath.mpr hmem)
              exact ⟨X, h, a, ha⟩
            have hnT : ModalSys.T = false := Bool.eq_false_iff.mpr hT
            obtain ⟨t, ⟨c, hc⟩, hk, -, -, hm'⟩ := glexX hM₀ (groot hF M₀) (rstg s i) (rorig s x) X
              (rpre hX hM₀ s i x _ h rfl) _ (hpath.mpr hmem)
            have hR : GR (groot hF M₀) t := ⟨[c], pathOk_cons, hc⟩
            have hmt : (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈
                ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1 :=
              (ccanon_mem_iff hX s i h _).mpr (.inr ⟨hnT,
                inExt_pathOf hR (show InExt (groot hF M₀) t [c] hc (rorig s x) from hk)⟩)
            exact ⟨X, h, ⟨_, hmt⟩, (sat_diaPush_c hX s i h ⟨_, hmt⟩ [c] hc (pathOf_of hR hc)
              ((gw hM₀ t).not_realised hnT) hk χ).mpr ((ctruth_lt hX n t _ _ (by
                rw [size_pTrXW, size_preWPX (hM₀ := hM₀) hX]; exact hχs)).mpr hm')⟩

/-- ⭐**The truth lemma** for the cluster model. -/
theorem ctruth (hX : CluFlags) (s : GW hF M₀) (i : ℕ) (φ : WFF σ (ctxOf (glat s i)) 0) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) φ ↔ φ ∈ (gw hM₀ s).M i :=
  ctruth_lt hX (φ.size + 1) s i φ (Nat.lt_succ_self _)

end GArrow

end V12M
