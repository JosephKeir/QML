import QML.QML_v12m_GCluTerm

/-!
# QML v12m — 5 on the growing tree: the cluster model's truth lemma

As `GTruth` for the growing tree, T off (`docs/v12-modal-extensions.md` §3 5, "The truth lemma:
design check against `GTruth`").  Pushing from intermediate worlds is never needed: an
environment agreeing with a chain of substitutions and shifts satisfies a formula exactly when
the chain's end satisfies its translation, link by link (`Model.sat_subst`, `Model.sat_shift`).

* `cenvOf`: an environment agreeing with a chain, by construction; `eq_substEnv_of_cagree`,
  `shiftAgree_of_cagree`: a substitution link and a shift link, semantically.
* ⭐`sat_ptrC`, ⭐`sat_ptrXC`: along a path, an environment agreeing with the path's chain
  satisfies a formula exactly when the end's canonical environment satisfies its translation.
* `sat_boxPush_c`, `sat_diaPush_c`: pushing from a world is its preimage, then the root's path.
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
  | _, _, [], _, hP, _, _, _, _ => (hX.absT hP.T_of_nil).elim
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
      InExt (groot hF M₀) b.1 (pathOf b.2.down) (pathOf_eq b.2.down) (rorig s x) := by
  rw [cagree_canon hX s i x _ hr]
  exact Iff.rfl

/-- ⭐**A world's `◇_x` view along an arrow of `x`'s extent satisfies a formula exactly when the
    arrow's end satisfies its preimage translated along the root's path for `x`'s origin.** -/
theorem sat_diaPush_c (hX : CluFlags) (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (a : ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x hr)).1) (P : List ℕ)
    (h : a.1.1.1 = nodeOf (groot hF M₀).1 P) (e : pathOf a.1.2.down = P)
    (hm : InExt (groot hF M₀) a.1.1 P h (rorig s x))
    (χ : WFF σ ((ctxOf (glat s i)).diaIn x) 0) :
    (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s i).diaPush x hr a) χ ↔
      (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX a.1.1 (pstg (groot hF M₀) a.1.1 P h (rstg s i)))
        (pTrXW hM₀ (groot hF M₀) a.1.1 P h (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hr⟩)
          hm (preWPX (rpre hX hM₀ s i) hr χ)) := by
  subst e
  have hag : CAgree hM₀ hX (preXC hM₀ hX s i ⟨X, hr⟩ a.1 hm)
      ((ccanonEnv hM₀ hX s i).diaPush x hr a) :=
    cagree_diaPush hX (.nil _) _ (cagree_canon hX s i) hr a hm
  have hag' := cagree_envOf (hM₀ := hM₀) hX (ptrXC hM₀ (groot hF M₀) a.1.1 (pathOf a.1.2.down)
    (pathOf_eq a.1.2.down) (rstg s i) (rorig s x) (rorig_ref hX hM₀ s i ⟨X, hr⟩) hm)
    (Ctx.noProjLast_diaIn _ _)
  rw [eq_substEnv_of_cagree hX (Ctx.noProjLast_diaIn _ _) _ _ _ _ (npl_ptrXC hM₀ _ _ _ _ _ _ _ hm)
    (Ctx.noProjLast_diaIn _ _) _ hag _ hag']
  refine (Model.sat_subst _ _ (coh_eS_kView (k := some x) (entOk_ofRen
    (itemOk_rpreX hX hM₀ s i ⟨X, hr⟩))) Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ χ).symm.trans ?_
  exact sat_ptrXC hX _ _ _ _ _ _ _ hm _ hag' _

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

/-! ## The truth lemma -/

theorem size_preWP (hX : CluFlags) (s : GW hF M₀) (i : ℕ)
    (χ : WFF σ ((ctxOf (glat s i)).kView none) 0) :
    (preWP (rpre hX hM₀ s i) χ).size = χ.size :=
  WFF.size_subst _ _ _ _ _ _

theorem size_preWPX (hX : CluFlags) (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (χ : WFF σ ((ctxOf (glat s i)).diaIn x) 0) :
    (preWPX (rpre hX hM₀ s i) hr χ).size = χ.size :=
  WFF.size_subst _ _ _ _ _ _

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
      | here hT _ _ => exact (hX.absT hT).elim
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
          constructor
          · rintro ⟨X, h, a, hsat⟩
            by_contra hnot
            have hpath := dia_pathO_iff hX.five hX.fourS hX.fourSW hM₀
              (rpath s) (groot hF M₀) s (rpath_eq s) i h χ
            have hm := (ccanon_mem_iff hX s i h a.1).mp a.2
            have h1 := (sat_diaPush_c hX s i h a _ (pathOf_eq a.1.2.down) rfl hm χ).mp hsat
            have h2 := (ctruth_lt hX n a.1.1 _ _ (by
              rw [size_pTrXW, size_preWPX (hM₀ := hM₀) hX]; exact hχs)).mp h1
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
            have hneg := boxx_mem_path (hM₀ := hM₀) (groot hF M₀) a.1.1 _ (pathOf_eq a.1.2.down)
              (rstg s i) (rorig s x) _ hm _ hbx
            rw [pTrXW_neg] at hneg
            exact ((gw hM₀ a.1.1).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem
            obtain ⟨X, h⟩ := id hx
            have hpath := dia_pathO_iff hX.five hX.fourS hX.fourSW hM₀
              (rpath s) (groot hF M₀) s (rpath_eq s) i h χ
            obtain ⟨t, ⟨c, hc⟩, hk, -, -, hm'⟩ := glexX hM₀ (groot hF M₀) (rstg s i) (rorig s x) X
              (rpre hX hM₀ s i x _ h rfl) _ (hpath.mpr hmem)
            have hR : GR (groot hF M₀) t := ⟨[c], pathOk_cons, hc⟩
            have hmt : (⟨t, ⟨hR⟩⟩ : CAcc hF M₀) ∈
                ((cmodel hF hM₀ hX).posEval ((ccanonEnv hM₀ hX s i).ref x h)).1 :=
              (ccanon_mem_iff hX s i h _).mpr
                (inExt_pathOf hR (show InExt (groot hF M₀) t [c] hc (rorig s x) from hk))
            exact ⟨X, h, ⟨_, hmt⟩, (sat_diaPush_c hX s i h ⟨_, hmt⟩ [c] hc (pathOf_of hR hc) hk
              χ).mpr ((ctruth_lt hX n t _ _ (by
                rw [size_pTrXW, size_preWPX (hM₀ := hM₀) hX]; exact hχs)).mpr hm')⟩

/-- ⭐**The truth lemma** for the K45 cluster model. -/
theorem ctruth (hX : CluFlags) (s : GW hF M₀) (i : ℕ) (φ : WFF σ (ctxOf (glat s i)) 0) :
    (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s i) φ ↔ φ ∈ (gw hM₀ s).M i :=
  ctruth_lt hX (φ.size + 1) s i φ (Nat.lt_succ_self _)

end GArrow

end V12M
