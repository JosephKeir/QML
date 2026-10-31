import QML.QML_v12m_GCluWShape

/-!
# QML v12m — 5 on the growing tree: the cluster model's truth lemma for terms

As `GCanonTerm` for the growing tree (`docs/v12-modal-extensions.md` §3 5, "The truth lemma:
design check against `GTruth`").

* `preC`, `preXC`, `preXKC`: pushing along an arrow from a world: its preimage, then the root's
  path translation (`ptrC`, `ptrXC`, `ptrXKC`) — `cden`'s own definition at a modal type.
* `CAgree C env`: every address reads as the denotation of its η-expansion translated by `C`;
  it passes into `□` along an arrow (`cagree_boxPush`) and into `◇_x` along an arrow of `x`'s
  extent (`cagree_diaPush`), or along one whose end realises the kept witness
  (`cagree_diaPushR`), the chain growing by `preC`, `preXC`, `preXKC` and the realisation.
* `ccanonEnv`, and under T its shapes (`cInvW_canon`, `envShape_ctr`): an environment agreeing
  with a chain reads as the canonical shapes pulled back along it.
* ⭐`interp_ctr`: in an environment agreeing with a chain, a term's value is the denotation of
  its translation; ⭐`interp_ccanon`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hM₀ : Theory.IsMCS M₀)

/-! ## Pushing from a world -/

/-- Pushing from a world into `□` along an arrow: the world's preimage, then the root's path. -/
noncomputable def preC (hX : CluFlags) (w : GW hF M₀) (k : ℕ) (a : CAcc hF M₀) :
    GTr σ (ctxOf (glat w k)).boxIn
      (ctxOf (glat a.1 (pstg (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down)
        (rstg w k)))) :=
  .sub (eS σ (ctxOf (glat (groot hF M₀) (rstg w k))).boxIn (ofRen (preI (rorig w))))
    (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI (rpre hX hM₀ w k))))
    (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI (rpre hX hM₀ w k))))
    (ptrC hM₀ (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (pathOf_ok a.2.down)
      (rstg w k))

theorem preC_app (hX : CluFlags) (w : GW hF M₀) (k : ℕ) (a : CAcc hF M₀) {A : VarType}
    {b : Ann A} (t : Term σ (ctxOf (glat w k)).boxIn A b) :
    (preC hM₀ hX w k a).app t =
      pTr hM₀ (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (pathOf_ok a.2.down)
        (rstg w k) (preTB hX hM₀ w k t).2 :=
  (pTr_app hM₀ _ _ _ _ _ _ _).symm

/-- Pushing from a world into `◇_x` along an arrow of `x`'s extent. -/
noncomputable def preXC (hX : CluFlags) (w : GW hF M₀) (k : ℕ) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat w k)).ref x = some (.VTypeDia X)) (a : CAcc hF M₀)
    (hm : InExt (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rorig w x)) :
    GTr σ ((ctxOf (glat w k)).diaIn x)
      (ctxOf (glat a.1 (pstg (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down)
        (rstg w k)))) :=
  .sub (eS σ ((ctxOf (glat (groot hF M₀) (rstg w k))).diaIn (rorig w x))
      (ofRen (preIX (rorig w) x)))
    (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_rpreX hX hM₀ w k hx)))
    (coh_eS_kView (k := some x) (entOk_ofRen (itemOk_rpreX hX hM₀ w k hx)))
    (ptrXC hM₀ (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rstg w k)
      (rorig w x) (rorig_ref hX hM₀ w k hx) hm)

theorem preXC_app (hX : CluFlags) (w : GW hF M₀) (k : ℕ) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat w k)).ref x = some (.VTypeDia X)) (a : CAcc hF M₀)
    (hm : InExt (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rorig w x))
    {A : VarType} {b : Ann A} (t : Term σ ((ctxOf (glat w k)).diaIn x) A b) :
    (preXC hM₀ hX w k hx a hm).app t =
      pTrX hM₀ (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rstg w k)
        (rorig w x) (rorig_ref hX hM₀ w k hx) hm (preTD hX hM₀ w k hx t).2 :=
  (pTrX_app hM₀ _ _ _ _ _ _ _ hm _).symm

/-- Pushing from a world into `◇_x` along an arrow whose end realises the kept witness. -/
noncomputable def preXKC (hX : CluFlags) (w : GW hF M₀) (k : ℕ) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat w k)).ref x = some (.VTypeDia X)) (a : CAcc hF M₀) :
    GTr σ ((ctxOf (glat w k)).diaIn x)
      ((ctxOf (glat a.1 (pstg (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down)
        (rstg w k)))).kView (some (kw (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down)
          (rorig w x)))) :=
  .sub (eS σ ((ctxOf (glat (groot hF M₀) (rstg w k))).diaIn (rorig w x))
      (ofRen (preIX (rorig w) x)))
    (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_rpreX hX hM₀ w k hx)))
    (coh_eS_kView (k := some x) (entOk_ofRen (itemOk_rpreX hX hM₀ w k hx)))
    (ptrXKC hM₀ (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rstg w k)
      (rorig w x) (rorig_ref hX hM₀ w k hx))

theorem preXKC_app (hX : CluFlags) (w : GW hF M₀) (k : ℕ) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat w k)).ref x = some (.VTypeDia X)) (a : CAcc hF M₀)
    {A : VarType} {b : Ann A} (t : Term σ ((ctxOf (glat w k)).diaIn x) A b) :
    (preXKC hM₀ hX w k hx a).app t =
      pTrXK hM₀ (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rstg w k)
        (rorig w x) (rorig_ref hX hM₀ w k hx) (preTD hX hM₀ w k hx t).2 :=
  (pTrXK_app hM₀ _ _ _ _ _ _ _ _).symm

theorem npl_preXKC (hX : CluFlags) (w : GW hF M₀) (k : ℕ) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat w k)).ref x = some (.VTypeDia X)) (a : CAcc hF M₀) :
    (preXKC hM₀ hX w k hx a).NPL :=
  ⟨Ctx.noProjLast_diaIn _ _, npl_ptrXKC hM₀ _ _ _ _ _ _ _⟩

theorem npl_preC (hX : CluFlags) (w : GW hF M₀) (k : ℕ) (a : CAcc hF M₀) :
    (preC hM₀ hX w k a).NPL :=
  ⟨Ctx.noProjLast_boxIn _, npl_ptrC hM₀ _ _ _ _ _ _⟩

theorem npl_preXC (hX : CluFlags) (w : GW hF M₀) (k : ℕ) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat w k)).ref x = some (.VTypeDia X)) (a : CAcc hF M₀)
    (hm : InExt (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rorig w x)) :
    (preXC hM₀ hX w k hx a hm).NPL :=
  ⟨Ctx.noProjLast_diaIn _ _, npl_ptrXC hM₀ _ _ _ _ _ _ _ hm⟩

/-! ## Agreement through a chain -/

/-- ⭐**Agreement through a chain**: every address reads as the denotation of its η-expansion
    translated by the chain. -/
def CAgree (hX : CluFlags) {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (cmodel hF hM₀ hX).Env Γ w) : Prop :=
  ∀ v T (hv : Γ.ref v = some T), env.ref v hv =
    ctoDom hM₀ hX T w (cden hM₀ hX w k (Ctx.Le.refl _) (C.app (Term.eta v T hv)).2)
      (cdefinable_den hX _ _)

variable {hM₀}

/-- Agreement at the visible addresses gives agreement at every reachable one. -/
theorem cagree_of_raw (hX : CluFlags) {Γ : Ctx} {w : GW hF M₀} {k : ℕ}
    (C : GTr σ Γ (ctxOf (glat w k))) (env : (cmodel hF hM₀ hX).Env Γ w)
    (h : ∀ v T (hlp : v.lastProj = false) (hv : Γ v = some T), env v T hv =
      ctoDom hM₀ hX T w (cden hM₀ hX w k (Ctx.Le.refl _)
        (C.app (Term.eta v T ((Ctx.ref_nonproj Γ hlp).trans hv))).2) (cdefinable_den hX _ _)) :
    CAgree hM₀ hX C env := by
  intro v
  induction v with
  | root r => intro T hv; exact h _ _ rfl hv
  | step v st ih =>
      intro T hv
      by_cases hs : st.isProj = true
      · rw [Model.Env.ref, dif_pos hs]
        split
        · rename_i U hU
          rw [ih U hU]
          have hT : U.step st = some T := by
            rw [Ctx.ref_step_proj _ _ hs, hU] at hv
            exact hv
          cases st with
          | fst =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              exact ctoDom_congr hX (congrArg Prod.fst (cden_sigma hX (Ctx.Le.refl _)
                (GTr.app_pair C _ _))) _ _
          | snd =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              exact ctoDom_congr hX (congrArg Prod.snd (cden_sigma hX (Ctx.Le.refl _)
                (GTr.app_pair C _ _))) _ _
          | here =>
              cases U <;> simp only [VarType.step, reduceCtorEq] at hT
              rename_i A
              obtain ⟨hT₁, rfl⟩ := VarType.step_here hT
              change ctoDom hM₀ hX _ w (cden hM₀ hX w k (Ctx.Le.refl _)
                (C.app (Term.eta v (.VTypeBox A) hU)).2 ⟨w, ⟨(carrows hF M₀).refl hT₁ w⟩⟩) _ = _
              refine ctoDom_congr hX ?_ _ _
              refine (congrFun (cden_sigma hX (Ctx.Le.refl _)
                (GTr.app_boxtm C (Term.eta v.inner A (Ctx.ref_inner hU)))) _).trans ?_
              refine (cden_boxtm_own hX hT₁ w k _ _).trans ?_
              exact (cden_sigma hX _ ((C.app_sigma ((Term.collapse_eta _ _ _ _).trans
                (Term.eta_congr (VarSymb.inner_collapse_zero v) _ _ _))).symm.trans
                (GTr.app_collapse hT₁ C _))).symm
          | box => cases hs
          | dia => cases hs
          | keep => cases hs
        · rename_i hU
          rw [Ctx.ref_step_proj _ _ hs, hU] at hv
          cases hv
      · rw [Model.Env.ref, dif_neg hs]
        exact h _ _ (show (VarSymb.step v st).lastProj = false from
          Bool.eq_false_iff.mpr hs) _

theorem CRPos.c_congr {A : VarType} {C : CAcc hF M₀ → Type} {o o' : CRPos A C} (e : o = o')
    (b : CAcc hF M₀) (h : b ∈ o.E) (h' : b ∈ o'.E) : o.c ⟨b, h⟩ = o'.c ⟨b, h'⟩ := by
  subst e
  rfl

/-- ⭐**Agreement passes into `□` along an arrow**, the chain growing by the world's preimage and
    the root's path. -/
theorem cagree_boxPush (hX : CluFlags) {Γ : Ctx} {w : GW hF M₀} {k : ℕ}
    (C : GTr σ Γ (ctxOf (glat w k))) (env : (cmodel hF hM₀ hX).Env Γ w)
    (hag : CAgree hM₀ hX C env) (a : CAcc hF M₀) :
    CAgree hM₀ hX (C.box.comp (preC hM₀ hX w k a)) (env.boxPush a) := by
  refine cagree_of_raw hX _ _ fun v T hlp hv => ?_
  match v, hv with
  | .step u .box, hv =>
      have hu : Γ.ref u = some (.VTypeBox T) := Ctx.boxIn_step_box hv
      have hk : ModalSys.keepOnly = false := by
        cases hk : ModalSys.keepOnly
        · rfl
        · change (if ModalSys.keepOnly then none else _) = _ at hv
          rw [if_pos hk] at hv
          cases hv
      change (cmodel hF hM₀ hX).necEval (env.ref u hu) a = _
      rw [hag u _ hu]
      refine ctoDom_congr hX ?_ _ _
      rw [GTr.app_comp, preC_app]
      refine (congrFun (cden_sigma hX (Ctx.Le.refl _) (GTr.app_boxtm C _)) a).trans ?_
      change cden hM₀ hX a.1 _ (Ctx.Le.refl _) (pTr hM₀ (groot hF M₀) a.1 _ _ _ (rstg w k)
        (preTB hX hM₀ w k (Term.mono (Ctx.Le.refl _).boxIn
          (C.box.app (Term.eta u.inner T (Ctx.ref_inner hu))).2)).2).2 = _
      rw [Term.mono_refl]
      exact cden_sigma hX _ (pTr_sigma hM₀ _ _ _ _ _ _ (preTB_sigma hX hM₀ w k
        (C.box.app_sigma (Term.eta_congr (VarSymb.inner_box hk) T _ _))))
  | .step u .keep, hv =>
      obtain ⟨hF', hu, hkp⟩ := Ctx.boxIn_keep hv
      change (cmodel hF hM₀ hX).necEval (GFunc.eval (cops hF hM₀ hX) (GFunc.keep hF' hkp) w
        (env.ref u hu)) a = _
      rw [hag u _ hu, ceval_toDom]
      refine ctoDom_congr hX ?_ _ _
      change (crawEval hM₀ hX (GFunc.keep hF' hkp) w (cden hM₀ hX w k (Ctx.Le.refl _)
        (C.app (Term.eta u T hu)).2)) a = _
      rw [← cden_applyG, GTr.app_comp, preC_app]
      refine (congrFun (cden_sigma hX (Ctx.Le.refl _) ((GTr.applyG_app _ C _).trans
        ((C.app_sigma (applyG_keep_eta (hF := hF) hkp u hu)).trans
          (GTr.app_boxtm C _)))) a).trans ?_
      change cden hM₀ hX a.1 _ (Ctx.Le.refl _) (pTr hM₀ (groot hF M₀) a.1 _ _ _ (rstg w k)
        (preTB hX hM₀ w k (Term.mono (Ctx.Le.refl _).boxIn
          (C.box.app (Term.eta (.step u .keep) T _)).2)).2).2 = _
      rw [Term.mono_refl]
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

theorem preTD_sigma (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType}
    {a a' : Ann A} {y : Term σ ((ctxOf (glat s i)).diaIn x) A a}
    {z : Term σ ((ctxOf (glat s i)).diaIn x) A a'}
    (h : (⟨a, y⟩ : Σ c, Term σ ((ctxOf (glat s i)).diaIn x) A c) = ⟨a', z⟩) :
    (⟨_, (preTD hX hM₀ s i hx y).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView (some (rorig s x))) A c) =
      ⟨_, (preTD hX hM₀ s i hx z).2⟩ := by
  cases h
  rfl

/-- The `□` part of a witness's view reads as along the plain arrow. -/
theorem cagree_diaPush_box (hX : CluFlags) {Γ : Ctx} {w : GW hF M₀} {k : ℕ}
    (C : GTr σ Γ (ctxOf (glat w k))) (env : (cmodel hF hM₀ hX).Env Γ w)
    (hag : CAgree hM₀ hX C env) {x : VarSymb} {X : VarType} (hr : Γ.ref x = some (.VTypeDia X))
    (a : CAcc hF M₀)
    (hm : InExt (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rorig w (C.idx x)))
    (v : VarSymb) {T : VarType} (hv : Γ.boxIn.ref v = some T)
    (hv' : (Γ.diaIn x).ref v = some T) :
    (env.boxPush a).ref v hv =
      ctoDom hM₀ hX T a.1 (cden hM₀ hX a.1 _ (Ctx.Le.refl _)
        (((C.dia x ⟨X, hr⟩).comp (preXC hM₀ hX w k (C.idx_decl ⟨X, hr⟩) a hm)).app
          (Term.eta v T hv')).2) (cdefinable_den hX _ _) := by
  rw [cagree_boxPush hX C env hag a v T hv]
  refine ctoDom_congr hX ?_ _ _
  rw [GTr.app_comp, GTr.app_comp, preC_app, preXC_app]
  refine cden_sigma hX _ ((pTrX_box (hM₀ := hM₀) (groot hF M₀) a.1 _ _ (pathOf_ok a.2.down)
    (rstg w k) _ _ hm _).symm.trans (pTrX_sigma hM₀ _ _ _ _ _ _ _ hm ?_))
  have e1 : (C.dia x ⟨X, hr⟩).app (Term.eta v T hv') =
      ⟨_, Term.mono (Ctx.le_boxIn_diaIn _ (C.idx x)) (C.box.app (Term.eta v T hv)).2⟩ :=
    ((C.dia x _).app_sigma (congrArg (Sigma.mk _)
      (Term.mono_eta (Ctx.le_boxIn_diaIn Γ x) v T hv)).symm).trans
      (GTr.dia_box_mono C x _ (Term.eta v T hv))
  have e2 := preTD_box hX hM₀ (Ctx.Le.refl (ctxOf (glat w k))) (C.idx_decl ⟨X, hr⟩)
    (C.box.app (Term.eta v T hv)).2
  rw [Term.mono_refl, Term.mono_refl] at e2
  exact e2.symm.trans (preTD_sigma hX hM₀ w k _ (congrArg (fun p => (⟨p.1, p.2⟩ : Σ c, _))
    e1).symm)

/-- ⭐**Agreement passes into `◇_x` along an arrow of `x`'s extent** not realising the kept
    witness, the chain growing by the world's preimage and the root's path for the witness's
    origin. -/
theorem cagree_diaPush (hX : CluFlags) {Γ : Ctx} {w : GW hF M₀} {k : ℕ}
    (C : GTr σ Γ (ctxOf (glat w k))) (env : (cmodel hF hM₀ hX).Env Γ w)
    (hag : CAgree hM₀ hX C env) {x : VarSymb} {X : VarType} (hr : Γ.ref x = some (.VTypeDia X))
    (a : ((cmodel hF hM₀ hX).posEval (env.ref x hr)).1)
    (hrl : ¬ (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 (pathOf a.1.2.down)
      (pathOf_eq a.1.2.down) (rorig w (C.idx x))))
    (hm : InExt (groot hF M₀) a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down)
      (rorig w (C.idx x))) :
    CAgree hM₀ hX ((C.dia x ⟨X, hr⟩).comp (preXC hM₀ hX w k (C.idx_decl ⟨X, hr⟩) a.1 hm))
      (env.diaPush x hr a) := by
  refine cagree_of_raw hX _ _ fun v T hlp hv => ?_
  match v, hv with
  | .step u .dia, hv =>
      have hu : u = x := by
        change (if u = x then _ else none) = some T at hv
        split_ifs at hv with h
        exact h
      subst hu
      have hXT := Ctx.diaIn_step_dia hr hv
      subst hXT
      simp only [Model.Env.diaPush]
      have hpq := hag u _ hr
      have hm₁ : a.1 ∈ ((cmodel hF hM₀ hX).posEval (ctoDom hM₀ hX _ w
          (cden hM₀ hX w k (Ctx.Le.refl _) (C.app (Term.eta u _ hr)).2)
          (cdefinable_den hX _ _))).1 := hpq ▸ a.2
      rw [Model.posEval_snd_congr hpq a hm₁]
      change ctoDom hM₀ hX X a.1.1 ((cden hM₀ hX w k (Ctx.Le.refl _)
        (C.app (Term.eta u _ hr)).2).c ⟨a.1, hm₁⟩) _ = _
      refine ctoDom_congr hX ?_ _ _
      have e := cden_sigma (hM₀ := hM₀) hX (Ctx.Le.refl _)
        (GTr.app_diatm C u ⟨X, hr⟩ (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)))
      refine (CRPos.c_congr e a.1 hm₁ (e ▸ (hm₁ : a.1 ∈ (cden hM₀ hX w k (Ctx.Le.refl _)
        (C.app (Term.diatm u ⟨X, hr⟩
          (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)))).2).E))).trans ?_
      refine (cden_dia_c_neg hX w k _ _ _ _ a.1 _ hrl).trans ?_
      change cden hM₀ hX a.1.1 _ (Ctx.Le.refl _) (pTrX hM₀ (groot hF M₀) a.1.1 _ _ (rstg w k) _ _
        hm (preTD hX hM₀ w k _ (Term.mono (Ctx.Le.refl _) ((C.dia u ⟨X, hr⟩).app
          (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr))).2)).2).2 = _
      rw [Term.mono_refl, GTr.app_comp, preXC_app]
  | .step u .box, hv =>
      exact cagree_diaPush_box hX C env hag hr a.1 hm (.step u .box)
        ((Ctx.ref_nonproj _ rfl).trans hv) ((Ctx.ref_nonproj _ rfl).trans hv)
  | .step u .keep, hv =>
      exact cagree_diaPush_box hX C env hag hr a.1 hm (.step u .keep)
        ((Ctx.ref_nonproj _ rfl).trans hv) ((Ctx.ref_nonproj _ rfl).trans hv)
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

/-- The `□` part of a witness's view reads as along the plain arrow, where the arrow's end
    realises the kept witness: realisation collapses it (`cden_grealT_mono_boxIn`). -/
theorem cagree_diaPushR_box (hX : CluFlags) {Γ : Ctx} {w : GW hF M₀} {k : ℕ}
    (C : GTr σ Γ (ctxOf (glat w k))) (env : (cmodel hF hM₀ hX).Env Γ w)
    (hag : CAgree hM₀ hX C env) {x : VarSymb} {X : VarType} (hr : Γ.ref x = some (.VTypeDia X))
    (a : CAcc hF M₀)
    (hrl : (gw hM₀ a.1).Realised (kw (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down)
      (rorig w (C.idx x))))
    (v : VarSymb) {T : VarType} (hv : Γ.boxIn.ref v = some T)
    (hv' : (Γ.diaIn x).ref v = some T) :
    (env.boxPush a).ref v hv =
      ctoDom hM₀ hX T a.1 (cden hM₀ hX a.1 _ (Ctx.Le.refl _)
        ((((C.dia x ⟨X, hr⟩).comp (preXKC hM₀ hX w k (C.idx_decl ⟨X, hr⟩) a)).comp
          (grealC hM₀ hrl _ (kw_decl hM₀ (groot hF M₀) a.1 _ (pathOf_eq a.2.down) (rstg w k)
            (rorig_ref hX hM₀ w k (C.idx_decl ⟨X, hr⟩))))).app (Term.eta v T hv')).2)
        (cdefinable_den hX _ _) := by
  rw [cagree_boxPush hX C env hag a v T hv]
  refine ctoDom_congr hX ?_ _ _
  rw [GTr.app_comp, GTr.app_comp, GTr.app_comp, preC_app, preXKC_app, ← grealT_app]
  have e1 : (C.dia x ⟨X, hr⟩).app (Term.eta v T hv') =
      ⟨_, Term.mono (Ctx.le_boxIn_diaIn _ (C.idx x)) (C.box.app (Term.eta v T hv)).2⟩ :=
    ((C.dia x _).app_sigma (congrArg (Sigma.mk _)
      (Term.mono_eta (Ctx.le_boxIn_diaIn Γ x) v T hv)).symm).trans
      (GTr.dia_box_mono C x _ (Term.eta v T hv))
  have e2 := preTD_box hX hM₀ (Ctx.Le.refl (ctxOf (glat w k))) (C.idx_decl ⟨X, hr⟩)
    (C.box.app (Term.eta v T hv)).2
  rw [Term.mono_refl, Term.mono_refl] at e2
  have e3 : (⟨_, (preTD hX hM₀ w k (C.idx_decl ⟨X, hr⟩)
      ((C.dia x ⟨X, hr⟩).app (Term.eta v T hv')).2).2⟩ :
      Σ c, Term σ ((ctxOf (glat (groot hF M₀) (rstg w k))).kView
        (some (rorig w (C.idx x)))) T c) =
      ⟨_, Term.mono (Ctx.le_boxIn_diaIn _ (rorig w (C.idx x)))
        (preTB hX hM₀ w k (C.box.app (Term.eta v T hv)).2).2⟩ :=
    (preTD_sigma hX hM₀ w k _ (congrArg (fun p => (⟨p.1, p.2⟩ : Σ c, _)) e1)).trans e2
  refine Eq.trans ?_ (cden_sigma hX _ (grealT_sigma hrl _ _ ((pTrXK_sigma hM₀ _ _ _ _ _ _ _
    e3).trans (pTrXK_box _ _ _ _ _ _ _ _)))).symm
  rw [cden_grealT_mono_boxIn hX]
  exact (cden_sigma hX _ (collapse_pTrK hrl.T _ _ _ _ (pathOf_ok a.2.down) _ _)).symm

/-- ⭐Agreement passes into `◇_x` along an arrow whose end realises the kept witness: the chain
    grows by the world's preimage, the kept path and the realisation. -/
theorem cagree_diaPushR (hX : CluFlags) {Γ : Ctx} {w : GW hF M₀} {k : ℕ}
    (C : GTr σ Γ (ctxOf (glat w k))) (env : (cmodel hF hM₀ hX).Env Γ w)
    (hag : CAgree hM₀ hX C env) {x : VarSymb} {X : VarType} (hr : Γ.ref x = some (.VTypeDia X))
    (a : ((cmodel hF hM₀ hX).posEval (env.ref x hr)).1)
    (hrl : (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 (pathOf a.1.2.down)
      (pathOf_eq a.1.2.down) (rorig w (C.idx x)))) :
    CAgree hM₀ hX (((C.dia x ⟨X, hr⟩).comp (preXKC hM₀ hX w k (C.idx_decl ⟨X, hr⟩) a.1)).comp
      (grealC hM₀ hrl _ (kw_decl hM₀ (groot hF M₀) a.1.1 _ (pathOf_eq a.1.2.down) (rstg w k)
        (rorig_ref hX hM₀ w k (C.idx_decl ⟨X, hr⟩))))) (env.diaPush x hr a) := by
  refine cagree_of_raw hX _ _ fun v T hlp hv => ?_
  match v, hv with
  | .step u .dia, hv =>
      have hu : u = x := by
        change (if u = x then _ else none) = some T at hv
        split_ifs at hv with h
        exact h
      subst hu
      have hXT := Ctx.diaIn_step_dia hr hv
      subst hXT
      simp only [Model.Env.diaPush]
      have hpq := hag u _ hr
      have hm₁ : a.1 ∈ ((cmodel hF hM₀ hX).posEval (ctoDom hM₀ hX _ w
          (cden hM₀ hX w k (Ctx.Le.refl _) (C.app (Term.eta u _ hr)).2)
          (cdefinable_den hX _ _))).1 := hpq ▸ a.2
      rw [Model.posEval_snd_congr hpq a hm₁]
      change ctoDom hM₀ hX X a.1.1 ((cden hM₀ hX w k (Ctx.Le.refl _)
        (C.app (Term.eta u _ hr)).2).c ⟨a.1, hm₁⟩) _ = _
      refine ctoDom_congr hX ?_ _ _
      have e := cden_sigma (hM₀ := hM₀) hX (Ctx.Le.refl _)
        (GTr.app_diatm C u ⟨X, hr⟩ (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)))
      refine (CRPos.c_congr e a.1 hm₁ (e ▸ (hm₁ : a.1 ∈ (cden hM₀ hX w k (Ctx.Le.refl _)
        (C.app (Term.diatm u ⟨X, hr⟩
          (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)))).2).E))).trans ?_
      refine (cden_dia_c_pos' hX w k _ _ _ _ a.1 _ hrl).trans ?_
      rw [GTr.app_comp, GTr.app_comp, preXKC_app, ← grealT_app]
      change cden hM₀ hX a.1.1 _ (Ctx.Le.refl _) (grealT hrl (Ctx.Le.refl _) _
        (pTrXK hM₀ (groot hF M₀) a.1.1 _ _ (rstg w k) _ _ (preTD hX hM₀ w k _
          (Term.mono (Ctx.Le.refl _) ((C.dia u ⟨X, hr⟩).app
            (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr))).2)).2).2).2 = _
      rw [Term.mono_refl]
  | .step u .box, hv =>
      exact cagree_diaPushR_box hX C env hag hr a.1 hrl (.step u .box)
        ((Ctx.ref_nonproj _ rfl).trans hv) ((Ctx.ref_nonproj _ rfl).trans hv)
  | .step u .keep, hv =>
      exact cagree_diaPushR_box hX C env hag hr a.1 hrl (.step u .keep)
        ((Ctx.ref_nonproj _ rfl).trans hv) ((Ctx.ref_nonproj _ rfl).trans hv)
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

/-! ## The canonical environment -/

variable (hM₀) in
/-- ⭐The canonical environment: every visible address denotes its η-expansion. -/
noncomputable def ccanonEnv (hX : CluFlags) (s : GW hF M₀) (i : ℕ) :
    (cmodel hF hM₀ hX).Env (ctxOf (glat s i)) s :=
  fun v T hv => ctoDom hM₀ hX T s (cden hM₀ hX s i (Ctx.Le.refl _) (Term.eta v T
    ((Ctx.ref_nonproj _ (Ctx.Presented.noProjLast _ v T hv)).trans hv))) (cdefinable_den hX _ _)

theorem cagree_canon (hX : CluFlags) (s : GW hF M₀) (i : ℕ) :
    CAgree hM₀ hX (.nil _) (ccanonEnv hM₀ hX s i) :=
  cagree_of_raw hX _ _ fun _ _ _ _ => rfl

/-! ## Shapes -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- An η-annotation renamed along its positions is the renamed address's. -/
theorem Ann.mapIdx_eta_of (hko : ModalSys.keepOnly = true) (g : VarSymb → VarSymb) :
    ∀ (T : VarType) (y y' : VarSymb), (∀ π : List Step, g (y.ext π) = y'.ext π) →
      (Ann.eta y T).mapIdx g = Ann.eta y' T
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A B, y, y', h => by
      change Ann.prod _ _ = Ann.prod _ _
      rw [Ann.mapIdx_eta_of hko g A (.step y .fst) (.step y' .fst) fun π => h (.fst :: π),
        Ann.mapIdx_eta_of hko g B (.step y .snd) (.step y' .snd) fun π => h (.snd :: π)]
  | .VTypeBox A, y, y', h => by
      change Ann.box _ = Ann.box _
      rw [VarSymb.inner_keepOnly hko, VarSymb.inner_keepOnly hko,
        Ann.mapIdx_eta_of hko g A _ _ fun π => h (.keep :: .here :: π)]
  | .VTypeDia A, y, y', h => by
      change Ann.dia _ _ = Ann.dia _ _
      rw [Ann.mapIdx_eta_of hko g A (.step y .dia) (.step y' .dia) fun π => h (.dia :: π),
        show g y = y' from h []]

/-- A keepable address's annotation, read at the root, is its origin's. -/
theorem mapIdx_eta_preIx (hko : ModalSys.keepOnly = true) (s : GW hF M₀) {y : VarSymb}
    (hy : PPath y.path) {T : VarType} (hk : T.keepable = true) :
    (Ann.eta y T).mapIdx (preIx s) = Ann.eta (rorig s y) T := by
  cases T with
  | VTypeDia A =>
      change Ann.dia _ _ = Ann.dia _ _
      rw [preIx_ppath s hy,
        Ann.mapIdx_eta_of hko _ A (.step y .dia) (.step (rorig s y) .dia)
          fun π => preIx_lvl s hy rfl π]
  | VTypeBox A =>
      change Ann.box _ = Ann.box _
      rw [VarSymb.inner_keepOnly hko, VarSymb.inner_keepOnly hko]
      exact congrArg _ (Ann.mapIdx_eta_of hko _ A _ _ fun π => preIx_lvl s hy rfl (.here :: π))
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd _ _ => cases hk

variable (hM₀) in
/-- The canonical environment's shapes. -/
noncomputable abbrev cEw (hX : CluFlags) (hSh : ModalSys.shaped = true) (w : GW hF M₀) (k : ℕ) :
    Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) (ctxOf (glat w k)) w :=
  Model.envShape hSh (ccanonEnv hM₀ hX w k)

theorem cEw_wf (hX : CluFlags) (hSh : ModalSys.shaped = true) (w : GW hF M₀) (k : ℕ) :
    (cEw hM₀ hX hSh w k).WF [] :=
  Model.envShape_wf (M := cmodel hF hM₀ hX) hSh (ccanonEnv hM₀ hX w k)

/-- ⭐**The canonical environment reads each keepable address at its origin's shape.** -/
theorem cInvW_canon (hX : CluFlags) (hSh : ModalSys.shaped = true) (w : GW hF M₀) (k : ℕ) :
    CInvW w (cEw hM₀ hX hSh w k) 0 := by
  have hT := hX.T_of_shaped hSh
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  intro y T h
  have hpp := (reach_ppath h).1
  refine ⟨levels_pp hpp, ⟨y, T, [], ⟨k, h⟩, hpp, rfl, rfl, rfl⟩, fun hk => ?_⟩
  have hk' : T.keepable = true := hk.resolve_left (by omega)
  rw [preIx_ppath w hpp]
  have hd := rpre hX hM₀ w k y T h hk'
  refine ⟨⟨rorig w y, T, [], ⟨_, hd⟩, (reach_ppath hd).1, rfl, rfl, rfl⟩, ?_⟩
  refine (Model.ref_envShape hSh (ccanonEnv hM₀ hX w k) y h).trans ?_
  rw [cagree_canon hX w k y T h]
  refine (cdomShape_toDom hM₀ hX hSh T w _ _).trans ?_
  exact (crawShape_cden hX hM₀ hT w k _ _).trans
    (congrArg (annC w) (mapIdx_eta_preIx hko w hpp hk'))

/-- ⭐⭐**Under T, one denotation means one annotation.** -/
theorem ann_eq_of_cden (hX : CluFlags) (hT : ModalSys.T = true) {s : GW hF M₀} {i : ℕ}
    {A : VarType} {a a' : Ann A} (t : Term σ (ctxOf (glat s i)) A a)
    (t' : Term σ (ctxOf (glat s i)) A a')
    (h : cden hM₀ hX s i (Ctx.Le.refl _) t = cden hM₀ hX s i (Ctx.Le.refl _) t') : a = a' := by
  have hSh := ModalSys.shaped_of_T hT
  have hI := cInvW_canon (hM₀ := hM₀) hX hSh s i
  refine ann_eq_of_termShpW hX.five hX.fourS hX.fourSW hM₀ hT hI t t' ?_
  rw [termShp_annW hX.five hX.fourS hX.fourSW hM₀ hT hI t,
    termShp_annW hX.five hX.fourS hX.fourSW hM₀ hT hI t',
    ← crawShape_cden hX hM₀ hT s i (Ctx.Le.refl _) t,
    ← crawShape_cden hX hM₀ hT s i (Ctx.Le.refl _) t', h]

/-- An environment's reading at a declared address is its raw value, where no projection is last. -/
theorem cenv_ref_raw (hX : CluFlags) {Γ : Ctx} {w : GW hF M₀} (env : (cmodel hF hM₀ hX).Env Γ w)
    {v : VarSymb} {T : VarType} (hlp : v.lastProj = false) (hv : Γ v = some T) :
    env.ref v ((Ctx.ref_nonproj Γ hlp).trans hv) = env v T hv := by
  match v, hlp with
  | .root _, _ => rfl
  | .step v st, e =>
      have e' : st.isProj = false := e
      exact Model.Env.ref_nonproj' env (by rw [e']; decide) _

/-- ⭐Under T, **the shapes of an environment agreeing with a chain are the canonical shapes
    pulled back along it**: each address's value is its η-expansion's image's denotation, whose
    shape is the image's annotation's (`crawShape_cden`), the image's canonical shape
    (`termShp_annW`). -/
theorem envShape_ctr (hX : CluFlags) (hSh : ModalSys.shaped = true) {Γ : Ctx} {w : GW hF M₀}
    {k : ℕ} {C : GTr σ Γ (ctxOf (glat w k))} {env : (cmodel hF hM₀ hX).Env Γ w}
    (hag : CAgree hM₀ hX C env) (hC : C.NPL) (hΓ : Γ.NoProjLast) :
    Model.envShape hSh env =
      pullC (F := carrows hF M₀) (Root := fun _ => VarSymb) C hC (cEw hM₀ hX hSh w k) := by
  have hT := hX.T_of_shaped hSh
  funext v T hv
  have hlp := hΓ v T hv
  change Model.domSh hSh (env v T hv) = _
  rw [← cenv_ref_raw hX env hlp hv, hag v T _]
  refine (cdomShape_toDom hM₀ hX hSh T w _ _).trans ?_
  refine (crawShape_cden hX hM₀ hT w k _ _).trans ?_
  refine (termShp_annW hX.five hX.fourS hX.fourSW hM₀ hT (cInvW_canon (hM₀ := hM₀) hX hSh w k)
    (C.app (Term.eta v T ((Ctx.ref_nonproj Γ hlp).trans hv))).2).symm.trans ?_
  refine (termShp_gtr C hC _ (cEw_wf (hM₀ := hM₀) hX hSh w k) _).trans ?_
  rw [Model.termShp_eta]
  match v, hlp with
  | .root _, _ => rfl
  | .step v' st, e =>
      have e' : st.isProj = false := e
      exact Model.ShEnv.ref_nonproj _ _ (by rw [e']; decide) _

/-! ## The truth lemma for terms -/

mutual
  theorem interpFunc_ctr (hX : CluFlags) : ∀ {Γ : Ctx} {n : ℕ} (g : Func σ Γ n) {w : GW hF M₀}
      {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k))) {env : (cmodel hF hM₀ hX).Env Γ w},
      CAgree hM₀ hX C env → C.NPL → Γ.NoProjLast → ∀ (args : Fin n → (gw hM₀ w).D)
        (ts : Fin n → Term σ (ctxOf (glat w k)) .Var .var),
        (∀ j, args j = (gw hM₀ w).cls k (ts j)) →
        Model.interpFunc env g args =
          (gw hM₀ w).cls k (.func ((Spine.ofFn ts).fill (C.appF g)))
    | _, _, .F ⟨f, rfl⟩, w, k, C, env, _, _, _, args, ts, hts => by
        rw [GTr.appF_F]
        change (gw hM₀ w).canonFunc f (fun j => args (Fin.cast rfl j)) = _
        rw [show (fun j => args (Fin.cast rfl j)) = fun j => (gw hM₀ w).cls k (ts j) from
            funext fun j => hts j, BWorld.canonFunc_cls]
    | _, _, .eval g t, w, k, C, env, hag, hC, hΓ, args, ts, hts => by
        change Model.interpFunc env g (Fin.cons (Model.interp env t) args) = _
        have h0 : Model.interp env t = (gw hM₀ w).cls k (Canon.varTerm (C.app t)) := by
          rw [interp_ctr hX t C hag hC hΓ]
          refine ((cden_varTerm (hM₀ := hM₀) hX w k (Ctx.Le.refl _) (C.app t)).symm.trans
            (cden_var_mono hX _ _)).trans ?_
          rw [Term.mono_refl]
        rw [interpFunc_ctr hX g C hag hC hΓ (Fin.cons (Model.interp env t) args)
          (Fin.cons (Canon.varTerm (C.app t)) ts)
          (fun j => by cases j using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons,
          GTr.appF_eval]
        rfl
    termination_by _ _ g => g.size
    decreasing_by
      all_goals simp only [Func.size]
      all_goals omega

  /-- ⭐**The truth lemma for terms**: in an environment agreeing with a chain, a term's value is
      the denotation of its translation. -/
  theorem interp_ctr (hX : CluFlags) : ∀ {Γ : Ctx} {A : VarType} {a : Ann A} (X : Term σ Γ A a)
      {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
      {env : (cmodel hF hM₀ hX).Env Γ w},
      CAgree hM₀ hX C env → C.NPL → Γ.NoProjLast →
      Model.interp env X =
        ctoDom hM₀ hX A w (cden hM₀ hX w k (Ctx.Le.refl _) (C.app X).2) (cdefinable_den hX _ _)
    | _, _, _, .var v hv, _, _, _, _, hag, _, _ => hag v .Var hv
    | _, _, _, .func f, w, k, C, env, hag, hC, hΓ => by
        change Model.interpFunc env f Fin.elim0 =
          cden hM₀ hX w k (Ctx.Le.refl _) (C.app (.func f)).2
        rw [interpFunc_ctr hX f C hag hC hΓ Fin.elim0 Fin.elim0 (fun j => j.elim0),
          cden_sigma hX (Ctx.Le.refl _) (GTr.app_func C f)]
        change _ = (gw hM₀ w).cls k (Term.mono (Ctx.Le.refl _) (.func (C.appF f)))
        rw [Term.mono_refl]
        rfl
    | _, _, _, .unit, _, _, _, _, _, _, _ => rfl
    | _, _, _, .pair s t, _, _, C, _, hag, hC, hΓ =>
        Prod.ext ((interp_ctr hX s C hag hC hΓ).trans (ctoDom_congr hX (congrArg Prod.fst
            (cden_sigma hX (Ctx.Le.refl _) (GTr.app_pair C s t))).symm _ _))
          ((interp_ctr hX t C hag hC hΓ).trans (ctoDom_congr hX (congrArg Prod.snd
            (cden_sigma hX (Ctx.Le.refl _) (GTr.app_pair C s t))).symm _ _))
    | _, _, _, .boxtm X, w, k, C, env, hag, hC, _ => by
        apply (cmodel hF hM₀ hX).nec_inj
        funext a
        rw [Model.box_beta, interp_ctr hX X _ (cagree_boxPush hX C env hag a)
          (GTr.npl_comp _ _ (GTr.npl_box C) (npl_preC hM₀ hX _ _ _)) (Ctx.noProjLast_boxIn _)]
        refine ctoDom_congr hX ?_ _ _
        rw [GTr.app_comp, preC_app]
        refine Eq.symm ((congrFun (cden_sigma hX (Ctx.Le.refl _) (GTr.app_boxtm C X)) a).trans ?_)
        change cden hM₀ hX a.1 _ (Ctx.Le.refl _) (pTr hM₀ (groot hF M₀) a.1 _ _ _ (rstg w k)
          (preTB hX hM₀ w k (Term.mono (Ctx.Le.refl _).boxIn (C.box.app X).2)).2).2 = _
        rw [Term.mono_refl]
    | _, _, _, .diatm x hx Y, w, k, C, env, hag, hC, hΓ => by
        obtain ⟨X', hr⟩ := id hx
        refine (cmodel hF hM₀ hX).pos_inj ?_ fun hSh => ?_
        swap
        · have hT := hX.T_of_shaped hSh
          refine (Model.domSh_interp hSh env (.diatm x hx Y)).trans ?_
          rw [envShape_ctr hX hSh hag hC hΓ]
          exact (termShp_gtr C hC _ (cEw_wf (hM₀ := hM₀) hX hSh w k) _).symm.trans
            ((termShp_annW hX.five hX.fourS hX.fourSW hM₀ hT
              (cInvW_canon (hM₀ := hM₀) hX hSh w k) (C.app (.diatm x hx Y)).2).trans
              (crawShape_cden hX hM₀ hT w k _ _).symm)
        rw [Model.dia_beta env hx hr Y]
        have e2 := cden_sigma (hM₀ := hM₀) hX (Ctx.Le.refl _)
          (GTr.app_diatm C x hx (Term.eta (.step x .dia) X' (Ctx.ref_diaIn_of hr)))
        have hpq : env.ref x hr = ctoDom hM₀ hX _ w (cden hM₀ hX w k (Ctx.Le.refl _)
            (.diatm (C.idx x) (C.idx_decl hx) ((C.dia x hx).app
              (Term.eta (.step x .dia) X' (Ctx.ref_diaIn_of hr))).2)) (cdefinable_den hX _ _) :=
          (hag x _ hr).trans (ctoDom_congr hX e2 _ _)
        rw [ctoDom_congr hX (cden_sigma hX (Ctx.Le.refl _) (GTr.app_diatm C x hx Y)) _
          (cdefinable_den hX _ _)]
        refine Model.posSec_ext hpq _ _ fun a => ?_
        have key : ∀ b, b ∈ ((cmodel hF hM₀ hX).posEval (env.ref x hr)).1 →
            GMem hM₀ (groot hF M₀) b.1 (pathOf b.2.down) (pathOf_eq b.2.down)
              (rorig w (C.idx x)) := by
          rw [hpq]
          exact fun _ hb => hb
        by_cases hrl : (gw hM₀ a.1.1).Realised (kw (groot hF M₀) a.1.1 (pathOf a.1.2.down)
            (pathOf_eq a.1.2.down) (rorig w (C.idx x)))
        · rw [interp_ctr hX Y _ (cagree_diaPushR hX C env hag hr a hrl)
            (GTr.npl_comp _ _ (GTr.npl_comp _ _ (GTr.npl_dia C x _)
              (npl_preXKC hM₀ hX _ _ _ _)) (npl_grealC hM₀ hrl _ _)) (Ctx.noProjLast_diaIn _ _)]
          refine ctoDom_congr hX ?_ _ _
          rw [GTr.app_comp, GTr.app_comp, preXKC_app, ← grealT_app]
          refine Eq.trans ?_ (cden_dia_c_pos' hX w k _ _ _ _ a.1 _ hrl).symm
          change _ = cden hM₀ hX a.1.1 _ (Ctx.Le.refl _) (grealT hrl (Ctx.Le.refl _) _
            (pTrXK hM₀ (groot hF M₀) a.1.1 _ _ (rstg w k) _ _ (preTD hX hM₀ w k _
              (Term.mono (Ctx.Le.refl _) ((C.dia x hx).app Y).2)).2).2).2
          rw [Term.mono_refl]
        have hm := (Or.resolve_left (key a.1 a.2) hrl).2
        rw [interp_ctr hX Y _ (cagree_diaPush hX C env hag hr a hrl hm)
          (GTr.npl_comp _ _ (GTr.npl_dia C x _) (npl_preXC hM₀ hX _ _ _ _ hm))
          (Ctx.noProjLast_diaIn _ _)]
        refine ctoDom_congr hX ?_ _ _
        rw [GTr.app_comp, preXC_app]
        refine Eq.trans ?_ (cden_dia_c_neg hX w k _ _ _ _ a.1 _ hrl).symm
        change _ = cden hM₀ hX a.1.1 _ (Ctx.Le.refl _) (pTrX hM₀ (groot hF M₀) a.1.1 _ _
          (rstg w k) _ _ hm (preTD hX hM₀ w k _ (Term.mono (Ctx.Le.refl _)
            ((C.dia x hx).app Y).2)).2).2
        rw [Term.mono_refl]
    termination_by _ _ _ X => X.size
    decreasing_by
      all_goals simp only [Term.size]
      all_goals omega
end

/-- ⭐**In an environment agreeing with the canonical one, a term's value is its denotation.** -/
theorem interp_ccanon (hX : CluFlags) {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {s : GW hF M₀} {i : ℕ} {e : Γ.Le (ctxOf (glat s i))} {env : (cmodel hF hM₀ hX).Env Γ s}
    (hag : Model.Env.Agree e env (ccanonEnv hM₀ hX s i)) (hΓ : Γ.NoProjLast) :
    Model.interp env t = ctoDom hM₀ hX A s (cden hM₀ hX s i e t) (cdefinable_den hX e t) := by
  have hag' : CAgree hM₀ hX (.mono e (.nil _)) env := fun v T hv => by
    rw [Model.Env.ref_agree hag v hv, cagree_canon hX s i v T (e.ref hv)]
    exact ctoDom_congr hX (cden_sigma hX _ (congrArg (Sigma.mk _) (Term.mono_eta e v T hv)).symm)
      _ _
  rw [interp_ctr hX t _ hag' trivial hΓ]
  exact ctoDom_congr hX ((cden_mono hX e t s i (Ctx.Le.refl _)).trans rfl) _ _

end GArrow

end V12M
