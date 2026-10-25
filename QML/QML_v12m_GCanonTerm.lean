import QML.QML_v12m_GTrShape

/-!
# QML v12m — the growing tree's canonical model: the truth lemma for terms

* A path's translations are chains (`ptrC`, `ptrXC`, `ptrXKC`; `pTr_app`, `pTrX_app`,
  `pTrXK_app`), and so is a realisation (`grealC`, `grealT_app`).
* `GAgree C env`: every address reads as the denotation of its η-expansion translated by `C`.
  It passes into `□` along an arrow (`gagree_boxPush`) and into `◇_x` along an arrow of `x`'s
  extent, the chain growing by the arrow's path (`gagree_diaPush`), and, where the arrow's end
  realises the kept witness, by the kept path and the realisation (`gagree_diaPushR`).
* ⭐`interp_gtr`: in an environment agreeing with a chain, a term's value is the denotation of its
  translation — by induction on the term alone.  An edge sends a lifted item to a **term**, so the
  pushed environment cannot be compared with the target's canonical one by substitution without
  the lemma for that term; agreement through chains compares it with the denotation instead.
* `gcanonEnv`, `interp_gcanon`: the canonical environment, and the lemma for it.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Paths as chains -/

variable (hM₀ : Theory.IsMCS M₀)

/-- A path's translation of a `□` view, as a chain. -/
noncomputable def ptrC : (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → PathOk P →
    (i : ℕ) → GTr σ ((ctxOf (glat s i)).kView none) (ctxOf (glat t (pstg s t P h i)))
  | _, _, [], h, hP, i =>
      .col (Ctx.collapses_boxIn_self hP.T_of_nil _) (.mono (glat_le_of_eq h i) (.nil _))
  | _, t, [c], h, _, i =>
      .sub (eS σ _ (fmapL hF M₀ t.1)) (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
        (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (.nil _)
  | s, t, c :: c' :: P, h, _, i =>
      .sh (Ctx.shifts_boxIn_boxIn hF _)
        (.sub (eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).box
          (Subst.ok_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          (Subst.coh_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          (ptrC (stepW s c (born_step h)) t (c' :: P) h (pathOk_cons)
            (glstg s (stepW s c (born_step h)) i)))

theorem pTr_app : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat s i)).kView none) A a),
    pTr hM₀ s t P h hP i b = (ptrC hM₀ s t P h hP i).app b
  | _, _, [], _, _, _, _, _, _ => rfl
  | _, _, [_], _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, _, _ =>
      pTr_app (stepW s c (born_step h)) t (c' :: P) h (pathOk_cons) _ _

/-- A path's translation of a witness's view, as a chain. -/
noncomputable def ptrXC : (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → (i : ℕ) →
    (x : VarSymb) → (∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) → InExt s t P h x →
    GTr σ ((ctxOf (glat s i)).kView (some x)) (ctxOf (glat t (pstg s t P h i)))
  | _, _, [], _, _, _, _, hm => hm.elim
  | _, t, [c], h, i, _, _, hm =>
      .sub (eS σ _ (fmapL hF M₀ t.1)) (ok_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i))
        (coh_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i)) (.nil _)
  | s, t, c :: c' :: P, h, i, x, hx, hm =>
      .sh (Ctx.shifts_diaIn_keep hF _ x)
        (.sub ((eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).dia (.step x .keep) (wit (stepW s c (born_step h)) x))
          (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx)
            ((coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
              (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
          (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx))
          (ptrXC (stepW s c (born_step h)) t (c' :: P) h (glstg s (stepW s c (born_step h)) i)
            (wit (stepW s c (born_step h)) x) (wit_ref hM₀ (born_step h) i hx) hm))

theorem pTrX_app : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x) {A : VarType} {a : Ann A}
    (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a),
    pTrX hM₀ s t P h i x hx hm u = (ptrXC hM₀ s t P h i x hx hm).app u
  | _, _, [], _, _, _, _, hm, _, _, _ => hm.elim
  | _, _, [_], _, _, _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, hm, _, _, _ =>
      pTrX_app (stepW s c (born_step h)) t (c' :: P) h _ _ _ hm _

/-- A path's translation of a witness's view with the witness kept, as a chain. -/
noncomputable def ptrXKC : (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) →
    (i : ℕ) → (x : VarSymb) → (∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) →
    GTr σ ((ctxOf (glat s i)).kView (some x))
      ((ctxOf (glat t (pstg s t P h i))).kView (some (kw s t P h x)))
  | _, _, [], h, i, _, _ => .mono ((glat_le_of_eq h i).kView _) (.nil _)
  | _, t, [c], h, i, x, hx =>
      .sh (Ctx.shifts_diaIn_keep hF _ x)
        (.sub ((eS σ (ctxOf (glat t (glstg _ t i))) (fmapL hF M₀ t.1)).dia (.step x .keep)
            (wit t x))
          (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (Ctx.exists_keep_dia hF hx)
            ((coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
              (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
          (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
            (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (Ctx.exists_keep_dia hF hx)) (.nil _))
  | s, t, c :: c' :: P, h, i, x, hx =>
      .sh (Ctx.shifts_diaIn_keep hF _ x)
        (.sub ((eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).dia (.step x .keep) (wit (stepW s c (born_step h)) x))
          (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx)
            ((coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
              (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
          (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx))
          (ptrXKC (stepW s c (born_step h)) t (c' :: P) h (glstg s (stepW s c (born_step h)) i)
            (wit (stepW s c (born_step h)) x) (wit_ref hM₀ (born_step h) i hx)))

theorem pTrXK_app : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a),
    pTrXK hM₀ s t P h i x hx u = (ptrXKC hM₀ s t P h i x hx).app u
  | _, _, [], _, _, _, _, _, _, _ => rfl
  | _, _, [_], _, _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, _, _, _ =>
      pTrXK_app (stepW s c (born_step h)) t (c' :: P) h _ _ _ _

/-- ⭐**A realisation, as a chain**: abstract the witness's content, collapse the `□` view and
    substitute the datum's content (`Term.realiseAtA`), after weakening to a stage above the
    datum's. -/
noncomputable def grealC {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) (j : ℕ)
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y)) :
    GTr σ ((ctxOf (glat t j)).diaIn y) (ctxOf (glat t (max j hr.data.i₀))) :=
  .mono ((gle hM₀ t (le_max_left _ _)).diaIn y)
    (.sub (Subst.diaAbsA σ ((ctxOf (glat t (max j hr.data.i₀))).boxIn.insert (.bnd 0) hr.data.A) y)
      (Subst.ok_diaAbsA (hr.data.hdeclOf _ (hy.imp fun _ h => (gle hM₀ t (le_max_left _ _)).ref h))
        ((inferInstance : (ctxOf (glat t (max j hr.data.i₀))).Presented).not_below
          (hr.data.hdeclOf _ (hy.imp fun _ h => (gle hM₀ t (le_max_left _ _)).ref h)) rfl)
        ((Ctx.NoSlots.slots (Γ := (ctxOf (glat t (max j hr.data.i₀))).boxIn)).root))
      (Subst.coh_diaAbsA (hr.data.hdeclOf _ (hy.imp fun _ h => (gle hM₀ t (le_max_left _ _)).ref h))
        ((inferInstance : (ctxOf (glat t (max j hr.data.i₀))).Presented).not_below
          (hr.data.hdeclOf _ (hy.imp fun _ h => (gle hM₀ t (le_max_left _ _)).ref h)) rfl)
        (inferInstance : (ctxOf (glat t (max j hr.data.i₀))).Presented).viewFresh
        ((Ctx.NoSlots.slots (Γ := (ctxOf (glat t (max j hr.data.i₀))).boxIn)).root))
      (.col ((Ctx.collapses_boxIn_self hr.data.hT (ctxOf (glat t (max j hr.data.i₀)))).insert
          ((Ctx.NoSlots.slots (Γ := (ctxOf (glat t (max j hr.data.i₀))).boxIn)).rootFresh
            (le_refl 0)) hr.data.A)
        (.sub (Subst.single (.bnd 0) (.tm (Term.mono (gle hM₀ t (le_max_right _ _)) hr.data.t₀)))
          (Subst.ok_single (Ctx.Le.refl _) rfl)
          (Subst.coh_single
            ((Ctx.NoSlots.slots (Γ := ctxOf (glat t (max j hr.data.i₀)))).rootFresh (le_refl 0))
            (Ctx.Le.refl _) rfl)
          (.nil _))))

theorem grealT_app {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y)) {A : VarType} {a : Ann A}
    (b : Term σ ((ctxOf (glat t j)).diaIn y) A a) :
    grealT hr (Ctx.Le.refl _) hy b = (grealC hM₀ hr j hy).app b :=
  rfl

/-! ## The chains start from views -/

theorem npl_ptrC : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ), (ptrC hM₀ s t P h hP i).NPL
  | _, _, [], _, _, _ => ⟨Ctx.noProjLast_boxIn _, trivial⟩
  | _, _, [_], _, _, _ => ⟨Ctx.noProjLast_boxIn _, trivial⟩
  | s, t, c :: c' :: P, h, _, _ =>
      ⟨Ctx.noProjLast_boxIn _, Ctx.noProjLast_boxIn _,
        npl_ptrC (stepW s c (born_step h)) t (c' :: P) h _ _⟩

theorem npl_ptrXC : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x), (ptrXC hM₀ s t P h i x hx hm).NPL
  | _, _, [], _, _, _, _, hm => hm.elim
  | _, _, [_], _, _, _, _, _ => ⟨Ctx.noProjLast_diaIn _ _, trivial⟩
  | s, t, c :: c' :: P, h, _, _, _, hm =>
      ⟨Ctx.noProjLast_diaIn _ _, Ctx.noProjLast_diaIn _ _,
        npl_ptrXC (stepW s c (born_step h)) t (c' :: P) h _ _ _ hm⟩

theorem npl_ptrXKC : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)),
    (ptrXKC hM₀ s t P h i x hx).NPL
  | _, _, [], _, _, _, _ => trivial
  | _, _, [_], _, _, _, _ => ⟨Ctx.noProjLast_diaIn _ _, Ctx.noProjLast_diaIn _ _, trivial⟩
  | s, t, c :: c' :: P, h, _, _, _ =>
      ⟨Ctx.noProjLast_diaIn _ _, Ctx.noProjLast_diaIn _ _,
        npl_ptrXKC (stepW s c (born_step h)) t (c' :: P) h _ _ _⟩

theorem npl_grealC {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) (j : ℕ)
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y)) : (grealC hM₀ hr j hy).NPL :=
  ⟨Ctx.noProjLast_diaIn _ _, (Ctx.noProjLast_boxIn _).insert _ _,
    (Ctx.Presented.noProjLast _).insert _ _, trivial⟩

/-! ## Agreement through a chain -/

variable [ModalSys.NoSym]

/-- ⭐**Agreement through a chain**: every address reads as the denotation of its η-expansion
    translated by the chain. -/
def GAgree {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) : Prop :=
  ∀ v T (hv : Γ.ref v = some T), env.ref v hv =
    gtoDom hM₀ T w (grden hM₀ w k (Ctx.Le.refl _) (C.app (Term.eta v T hv)).2)
      (gdefinable_rden _ _)

variable {hM₀}

/-- Agreement at the visible addresses gives agreement at every reachable one. -/
theorem gagree_of_raw {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w)
    (h : ∀ v T (hlp : v.lastProj = false) (hv : Γ v = some T), env v T hv =
      gtoDom hM₀ T w (grden hM₀ w k (Ctx.Le.refl _)
        (C.app (Term.eta v T ((Ctx.ref_nonproj Γ hlp).trans hv))).2) (gdefinable_rden _ _)) :
    GAgree hM₀ C env := by
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
              exact gtoDom_congr (congrArg Prod.fst (grden_sigma (Ctx.Le.refl _)
                (GTr.app_pair C _ _))) _ _
          | snd =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              exact gtoDom_congr (congrArg Prod.snd (grden_sigma (Ctx.Le.refl _)
                (GTr.app_pair C _ _))) _ _
          | here =>
              cases U <;> simp only [VarType.step, reduceCtorEq] at hT
              rename_i A
              obtain ⟨hT₁, rfl⟩ := VarType.step_here hT
              change gtoDom hM₀ _ w (grden hM₀ w k (Ctx.Le.refl _)
                (C.app (Term.eta v (.VTypeBox A) hU)).2 ⟨w, ⟨grefl hT₁ w⟩⟩) _ = _
              refine gtoDom_congr ?_ _ _
              refine (congrFun (grden_sigma (Ctx.Le.refl _)
                (GTr.app_boxtm C (Term.eta v.inner A (Ctx.ref_inner hU)))) _).trans ?_
              rw [grden_boxtm_path (Ctx.Le.refl _) _ w (grefl hT₁ w) [] rfl (Or.inr hT₁)]
              change grden hM₀ w k (Ctx.Le.refl _) (Term.mono (glat_le_of_eq rfl k)
                (Term.collapse (Ctx.collapses_boxIn_self hT₁ _)
                  (Term.mono (Ctx.Le.refl _).boxIn (C.box.app _).2))) = _
              rw [Term.mono_refl, Term.mono_refl]
              exact (grden_sigma _ ((C.app_sigma ((Term.collapse_eta _ _ _ _).trans
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

omit [ModalSys.NoSym] in
theorem GRPos.c_congr {s : GW hF M₀} {A : VarType} {C : GAcc hF M₀ s → Type}
    {o o' : GRPos s A C} (e : o = o')
    (b : GAcc hF M₀ s) (h : b ∈ o.E) (h' : b ∈ o'.E) : o.c ⟨b, h⟩ = o'.c ⟨b, h'⟩ := by
  subst e
  rfl

/-- ⭐Agreement passes into `□` along an arrow, the chain growing by the arrow's path. -/
theorem gagree_boxPush {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) (a : GAcc hF M₀ w) :
    GAgree hM₀ (C.box.comp (ptrC hM₀ w a.1 (pathOf a.2.down) (pathOf_eq a.2.down)
      (pathOf_ok a.2.down) k)) (env.boxPush a) := by
  refine gagree_of_raw _ _ fun v T hlp hv => ?_
  match v, hv with
  | .step u .box, hv =>
      have hu : Γ.ref u = some (.VTypeBox T) := Ctx.boxIn_step_box hv
      have hk : ModalSys.keepOnly = false := by
        cases hk : ModalSys.keepOnly
        · rfl
        · change (if ModalSys.keepOnly then none else _) = _ at hv
          rw [if_pos hk] at hv
          cases hv
      change (gmodel hF hM₀).necEval (env.ref u hu) a = _
      rw [hag u _ hu]
      refine gtoDom_congr ?_ _ _
      rw [GTr.app_comp, ← pTr_app]
      refine (congrFun (grden_sigma (Ctx.Le.refl _) (GTr.app_boxtm C _)) a).trans ?_
      change grden hM₀ a.1 _ (Ctx.Le.refl _) (pTr hM₀ w a.1 _ _ _ k
        (Term.mono (Ctx.Le.refl _).boxIn
          (C.box.app (Term.eta u.inner T (Ctx.ref_inner hu))).2)).2 = _
      rw [Term.mono_refl]
      exact grden_sigma _ (pTr_sigma hM₀ _ _ _ _ _ _
        (C.box.app_sigma (Term.eta_congr (VarSymb.inner_box hk) T _ _)))
  | .step u .keep, hv =>
      obtain ⟨hF', hu, hkp⟩ := Ctx.boxIn_keep hv
      change (gmodel hF hM₀).necEval (GFunc.eval (gops hF hM₀) (GFunc.keep hF' hkp) w
        (env.ref u hu)) a = _
      rw [hag u _ hu, geval_toDom]
      refine gtoDom_congr ?_ _ _
      change (grawEval hM₀ (GFunc.keep hF' hkp) w (grden hM₀ w k (Ctx.Le.refl _)
        (C.app (Term.eta u T hu)).2)) a = _
      rw [← grden_applyG, GTr.app_comp, ← pTr_app]
      refine (congrFun (grden_sigma (Ctx.Le.refl _) ((GTr.applyG_app _ C _).trans
        ((C.app_sigma (applyG_keep_eta (hF := hF) hkp u hu)).trans
          (GTr.app_boxtm C _)))) a).trans ?_
      change grden hM₀ a.1 _ (Ctx.Le.refl _) (pTr hM₀ w a.1 _ _ _ k
        (Term.mono (Ctx.Le.refl _).boxIn (C.box.app (Term.eta (.step u .keep) T _)).2)).2 = _
      rw [Term.mono_refl]
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .dia, hv => cases hv
  | .step _ .here, hv => cases hv

/-- The `□` part of a witness's view reads as along the plain arrow. -/
theorem gagree_diaPush_box {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (a : GAcc hF M₀ w)
    (hm : InExt w a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (C.idx x)) (v : VarSymb)
    {T : VarType} (hv : Γ.boxIn.ref v = some T) (hv' : (Γ.diaIn x).ref v = some T) :
    (env.boxPush a).ref v hv =
      gtoDom hM₀ T a.1 (grden hM₀ a.1 _ (Ctx.Le.refl _)
        (((C.dia x ⟨X, hr⟩).comp (ptrXC hM₀ w a.1 (pathOf a.2.down) (pathOf_eq a.2.down) k
          (C.idx x) (C.idx_decl ⟨X, hr⟩) hm)).app (Term.eta v T hv')).2) (gdefinable_rden _ _) := by
  rw [gagree_boxPush C env hag a v T hv]
  refine gtoDom_congr ?_ _ _
  rw [GTr.app_comp, GTr.app_comp, ← pTr_app, ← pTrX_app]
  refine grden_sigma _ ((pTrX_box (hM₀ := hM₀) w a.1 _ _ (pathOf_ok a.2.down) k _ _ hm _).symm.trans
    (pTrX_sigma hM₀ _ _ _ _ _ _ _ hm ?_))
  refine (GTr.dia_box_mono C x ⟨X, hr⟩ (Term.eta v T hv)).symm.trans ?_
  exact (C.dia x _).app_sigma (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))

/-- ⭐Agreement passes into `◇_x` along an arrow of `x`'s extent. -/
theorem gagree_diaPush {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (a : ((gmodel hF hM₀).posEval (env.ref x hr)).1)
    (hrl : ¬ (gw hM₀ a.1.1).Realised (kw w a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down)
      (C.idx x)))
    (hm : InExt w a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) (C.idx x)) :
    GAgree hM₀ ((C.dia x ⟨X, hr⟩).comp (ptrXC hM₀ w a.1.1 (pathOf a.1.2.down)
      (pathOf_eq a.1.2.down) k (C.idx x) (C.idx_decl ⟨X, hr⟩) hm)) (env.diaPush x hr a) := by
  refine gagree_of_raw _ _ fun v T hlp hv => ?_
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
      have hm₁ : a.1 ∈ ((gmodel hF hM₀).posEval (gtoDom hM₀ _ w (grden hM₀ w k (Ctx.Le.refl _)
          (C.app (Term.eta u _ hr)).2) (gdefinable_rden _ _))).1 := hpq ▸ a.2
      rw [Model.posEval_snd_congr hpq a hm₁]
      change gtoDom hM₀ X a.1.1 ((grden hM₀ w k (Ctx.Le.refl _) (C.app (Term.eta u _ hr)).2).c
        ⟨a.1, hm₁⟩) _ = _
      refine gtoDom_congr ?_ _ _
      have e := grden_sigma (hM₀ := hM₀) (Ctx.Le.refl _)
        (GTr.app_diatm C u ⟨X, hr⟩ (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)))
      refine (GRPos.c_congr e a.1 hm₁ (e ▸ (hm₁ : a.1 ∈ (grden hM₀ w k (Ctx.Le.refl _)
        (C.app (Term.diatm u ⟨X, hr⟩
          (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)))).2).E))).trans ?_
      refine (dif_neg hrl).trans ?_
      change grden hM₀ a.1.1 _ (Ctx.Le.refl _) (pTrX hM₀ w a.1.1 _ _ k _ _ hm
        (Term.mono (Ctx.Le.refl _) ((C.dia u ⟨X, hr⟩).app
          (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr))).2)).2 = _
      rw [Term.mono_refl, GTr.app_comp, ← pTrX_app]
  | .step u .box, hv =>
      exact gagree_diaPush_box C env hag hr a.1 hm (.step u .box) ((Ctx.ref_nonproj _ rfl).trans hv)
        ((Ctx.ref_nonproj _ rfl).trans hv)
  | .step u .keep, hv =>
      exact gagree_diaPush_box C env hag hr a.1 hm (.step u .keep)
        ((Ctx.ref_nonproj _ rfl).trans hv) ((Ctx.ref_nonproj _ rfl).trans hv)
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

/-- The `□` part of a witness's view reads, along an arrow whose end realises the kept witness,
    as along the plain arrow: realising a `□` view's term collapses it
    (`grden_grealT_mono_boxIn`), and collapsing the kept translation is the translation
    (`collapse_pTrK`). -/
theorem gagree_diaPushR_box {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (a : GAcc hF M₀ w)
    (hrl : (gw hM₀ a.1).Realised (kw w a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (C.idx x)))
    (v : VarSymb) {T : VarType} (hv : Γ.boxIn.ref v = some T) (hv' : (Γ.diaIn x).ref v = some T) :
    (env.boxPush a).ref v hv =
      gtoDom hM₀ T a.1 (grden hM₀ a.1 _ (Ctx.Le.refl _)
        ((((C.dia x ⟨X, hr⟩).comp (ptrXKC hM₀ w a.1 (pathOf a.2.down) (pathOf_eq a.2.down) k
          (C.idx x) (C.idx_decl ⟨X, hr⟩))).comp (grealC hM₀ hrl _
            (kw_decl hM₀ w a.1 _ (pathOf_eq a.2.down) k (C.idx_decl ⟨X, hr⟩)))).app
              (Term.eta v T hv')).2) (gdefinable_rden _ _) := by
  rw [gagree_boxPush C env hag a v T hv]
  refine gtoDom_congr ?_ _ _
  rw [GTr.app_comp, GTr.app_comp, GTr.app_comp, ← pTr_app, ← pTrXK_app, ← grealT_app]
  have h₁ := (GTr.dia_box_mono C x ⟨X, hr⟩ (Term.eta v T hv)).symm.trans
    ((C.dia x _).app_sigma (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)))
  refine Eq.trans ?_ (grden_sigma _ (grealT_sigma hrl _ _ ((pTrXK_sigma hM₀ _ _ _ _ _ _ _
    h₁).symm.trans (pTrXK_box _ _ _ _ _ _ _ _)))).symm
  rw [grden_grealT_mono_boxIn]
  exact (grden_sigma _ (collapse_pTrK hrl.T _ _ _ _ (pathOf_ok a.2.down) _ _)).symm

/-- ⭐Agreement passes into `◇_x` along an arrow whose end realises the kept witness: the chain
    grows by the kept path and the realisation. -/
theorem gagree_diaPushR {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (a : ((gmodel hF hM₀).posEval (env.ref x hr)).1)
    (hrl : (gw hM₀ a.1.1).Realised (kw w a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down)
      (C.idx x))) :
    GAgree hM₀ (((C.dia x ⟨X, hr⟩).comp (ptrXKC hM₀ w a.1.1 (pathOf a.1.2.down)
      (pathOf_eq a.1.2.down) k (C.idx x) (C.idx_decl ⟨X, hr⟩))).comp (grealC hM₀ hrl _
        (kw_decl hM₀ w a.1.1 _ (pathOf_eq a.1.2.down) k (C.idx_decl ⟨X, hr⟩))))
      (env.diaPush x hr a) := by
  refine gagree_of_raw _ _ fun v T hlp hv => ?_
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
      have hm₁ : a.1 ∈ ((gmodel hF hM₀).posEval (gtoDom hM₀ _ w (grden hM₀ w k (Ctx.Le.refl _)
          (C.app (Term.eta u _ hr)).2) (gdefinable_rden _ _))).1 := hpq ▸ a.2
      rw [Model.posEval_snd_congr hpq a hm₁]
      change gtoDom hM₀ X a.1.1 ((grden hM₀ w k (Ctx.Le.refl _) (C.app (Term.eta u _ hr)).2).c
        ⟨a.1, hm₁⟩) _ = _
      refine gtoDom_congr ?_ _ _
      have e := grden_sigma (hM₀ := hM₀) (Ctx.Le.refl _)
        (GTr.app_diatm C u ⟨X, hr⟩ (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)))
      refine (GRPos.c_congr e a.1 hm₁ (e ▸ (hm₁ : a.1 ∈ (grden hM₀ w k (Ctx.Le.refl _)
        (C.app (Term.diatm u ⟨X, hr⟩
          (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr)))).2).E))).trans ?_
      refine (dif_pos hrl).trans ?_
      rw [GTr.app_comp, GTr.app_comp, ← pTrXK_app, ← grealT_app]
      change grden hM₀ a.1.1 _ (Ctx.Le.refl _) (grealT hrl (Ctx.Le.refl _) _
        (pTrXK hM₀ w a.1.1 _ _ k _ _ (Term.mono (Ctx.Le.refl _) ((C.dia u ⟨X, hr⟩).app
          (Term.eta (.step u .dia) X (Ctx.ref_diaIn_of hr))).2)).2).2 = _
      rw [Term.mono_refl]
  | .step u .box, hv =>
      exact gagree_diaPushR_box C env hag hr a.1 hrl (.step u .box)
        ((Ctx.ref_nonproj _ rfl).trans hv) ((Ctx.ref_nonproj _ rfl).trans hv)
  | .step u .keep, hv =>
      exact gagree_diaPushR_box C env hag hr a.1 hrl (.step u .keep)
        ((Ctx.ref_nonproj _ rfl).trans hv) ((Ctx.ref_nonproj _ rfl).trans hv)
  | .root _, hv => cases hv
  | .step _ .fst, hv => cases hv
  | .step _ .snd, hv => cases hv
  | .step _ .here, hv => cases hv

/-- An environment's reading at a declared address is its raw value, where no projection is last. -/
theorem env_ref_raw {Γ : Ctx} {w : GW hF M₀} (env : (gmodel hF hM₀).Env Γ w) {v : VarSymb}
    {T : VarType} (hlp : v.lastProj = false) (hv : Γ v = some T) :
    env.ref v ((Ctx.ref_nonproj Γ hlp).trans hv) = env v T hv := by
  match v, hlp with
  | .root _, _ => rfl
  | .step v st, e =>
      have e' : st.isProj = false := e
      exact Model.Env.ref_nonproj' env (by rw [e']; decide) _

/-- ⭐Under T, **the shapes of an environment agreeing with a chain are the canonical shapes
    pulled back along it**: each address's value is its η-expansion's image's denotation, whose
    stored shape is that image's canonical shape (`grawShape_grden`, `termShp_gtr`). -/
theorem envShape_gtr (hSh : ModalSys.shaped = true) {Γ : Ctx} {w : GW hF M₀} {k : ℕ}
    {C : GTr σ Γ (ctxOf (glat w k))} {env : (gmodel hF hM₀).Env Γ w} (hag : GAgree hM₀ C env)
    (hC : C.NPL) (hΓ : Γ.NoProjLast) :
    Model.envShape hSh env = pullC C hC (famEnv cEnv (ctxOf (glat w k)) w) := by
  funext v T hv
  have hlp := hΓ v T hv
  change Model.domSh hSh (env v T hv) = _
  rw [← env_ref_raw env hlp hv, hag v T _]
  refine (gdomShape_toDom hM₀ hSh T w _ _).trans ?_
  rw [grawShape_grden, termShp_gtr C hC _ (famEnv_wf (fun t v T => cEnv_wf t v T) _ w),
    Model.termShp_eta]
  match v, hlp with
  | .root _, _ => rfl
  | .step v' st, e =>
      have e' : st.isProj = false := e
      exact Model.ShEnv.ref_nonproj _ _ (by rw [e']; decide) _

/-! ## The truth lemma for terms -/

mutual
  theorem interpFunc_gtr : ∀ {Γ : Ctx} {n : ℕ} (g : Func σ Γ n) {w : GW hF M₀} {k : ℕ}
      (C : GTr σ Γ (ctxOf (glat w k))) {env : (gmodel hF hM₀).Env Γ w}, GAgree hM₀ C env →
      C.NPL → Γ.NoProjLast → ∀ (args : Fin n → (gw hM₀ w).D)
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
          rw [interp_gtr t C hag hC hΓ]
          refine ((grden_varTerm (hM₀ := hM₀) w k (Ctx.Le.refl _) (C.app t)).symm.trans
            (grden_var_mono _ _)).trans ?_
          rw [Term.mono_refl]
        rw [interpFunc_gtr g C hag hC hΓ (Fin.cons (Model.interp env t) args)
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
  theorem interp_gtr : ∀ {Γ : Ctx} {A : VarType} {a : Ann A} (X : Term σ Γ A a) {w : GW hF M₀}
      {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k))) {env : (gmodel hF hM₀).Env Γ w},
      GAgree hM₀ C env → C.NPL → Γ.NoProjLast →
      Model.interp env X =
        gtoDom hM₀ A w (grden hM₀ w k (Ctx.Le.refl _) (C.app X).2) (gdefinable_rden _ _)
    | _, _, _, .var v hv, _, _, _, _, hag, _, _ => hag v .Var hv
    | _, _, _, .func f, w, k, C, env, hag, hC, hΓ => by
        change Model.interpFunc env f Fin.elim0 = grden hM₀ w k (Ctx.Le.refl _) (C.app (.func f)).2
        rw [interpFunc_gtr f C hag hC hΓ Fin.elim0 Fin.elim0 (fun j => j.elim0),
          grden_sigma (Ctx.Le.refl _) (GTr.app_func C f)]
        change _ = (gw hM₀ w).cls k (Term.mono (Ctx.Le.refl _) (.func (C.appF f)))
        rw [Term.mono_refl]
        rfl
    | _, _, _, .unit, _, _, _, _, _, _, _ => rfl
    | _, _, _, .pair s t, _, _, C, _, hag, hC, hΓ =>
        Prod.ext ((interp_gtr s C hag hC hΓ).trans (gtoDom_congr (congrArg Prod.fst
            (grden_sigma (Ctx.Le.refl _) (GTr.app_pair C s t))).symm _ _))
          ((interp_gtr t C hag hC hΓ).trans (gtoDom_congr (congrArg Prod.snd
            (grden_sigma (Ctx.Le.refl _) (GTr.app_pair C s t))).symm _ _))
    | _, _, _, .boxtm X, w, k, C, env, hag, hC, _ => by
        apply (gmodel hF hM₀).nec_inj
        funext a
        rw [Model.box_beta, interp_gtr X _ (gagree_boxPush C env hag a)
          (GTr.npl_comp _ _ (GTr.npl_box C) (npl_ptrC hM₀ _ _ _ _ _ _)) (Ctx.noProjLast_boxIn _)]
        refine gtoDom_congr ?_ _ _
        rw [GTr.app_comp, ← pTr_app]
        refine Eq.symm ((congrFun (grden_sigma (Ctx.Le.refl _) (GTr.app_boxtm C X)) a).trans ?_)
        change grden hM₀ a.1 _ (Ctx.Le.refl _) (pTr hM₀ w a.1 _ _ _ k
          (Term.mono (Ctx.Le.refl _).boxIn (C.box.app X).2)).2 = _
        rw [Term.mono_refl]
    | _, _, _, .diatm x hx Y, w, k, C, env, hag, hC, hΓ => by
        obtain ⟨X', hr⟩ := id hx
        refine (gmodel hF hM₀).pos_inj ?_ fun hSh => ?_
        swap
        · refine (Model.domSh_interp hSh env (.diatm x hx Y)).trans ?_
          rw [envShape_gtr hSh hag hC hΓ,
            ← termShp_gtr C hC _ (famEnv_wf (fun t v T => cEnv_wf t v T) _ w)]
          exact (grawShape_grden (gT_of_shaped hSh) w k (Ctx.Le.refl _) _).symm
        rw [Model.dia_beta env hx hr Y]
        have e2 := grden_sigma (hM₀ := hM₀) (Ctx.Le.refl _)
          (GTr.app_diatm C x hx (Term.eta (.step x .dia) X' (Ctx.ref_diaIn_of hr)))
        have hpq : env.ref x hr = gtoDom hM₀ _ w (grden hM₀ w k (Ctx.Le.refl _)
            (.diatm (C.idx x) (C.idx_decl hx) ((C.dia x hx).app
              (Term.eta (.step x .dia) X' (Ctx.ref_diaIn_of hr))).2)) (gdefinable_rden _ _) :=
          (hag x _ hr).trans (gtoDom_congr e2 _ _)
        rw [gtoDom_congr (grden_sigma (Ctx.Le.refl _) (GTr.app_diatm C x hx Y)) _
          (gdefinable_rden _ _)]
        refine Model.posSec_ext hpq _ _ fun a => ?_
        have key : ∀ b, b ∈ ((gmodel hF hM₀).posEval (env.ref x hr)).1 →
            GMem hM₀ w b.1 (pathOf b.2.down) (pathOf_eq b.2.down) (C.idx x) := by
          rw [hpq]
          exact fun _ hb => hb
        by_cases hrl : (gw hM₀ a.1.1).Realised
            (kw w a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) (C.idx x))
        · rw [interp_gtr Y _ (gagree_diaPushR C env hag hr a hrl)
            (GTr.npl_comp _ _ (GTr.npl_comp _ _ (GTr.npl_dia C x _) (npl_ptrXKC hM₀ _ _ _ _ _ _ _))
              (npl_grealC hM₀ hrl _ _)) (Ctx.noProjLast_diaIn _ _)]
          refine gtoDom_congr ?_ _ _
          rw [GTr.app_comp, GTr.app_comp, ← pTrXK_app, ← grealT_app]
          refine Eq.trans ?_ (dif_pos hrl).symm
          change _ = grden hM₀ a.1.1 _ (Ctx.Le.refl _) (grealT hrl (Ctx.Le.refl _) _
            (pTrXK hM₀ w a.1.1 _ _ k _ _ (Term.mono (Ctx.Le.refl _) ((C.dia x hx).app Y).2)).2).2
          rw [Term.mono_refl]
        have hm := (Or.resolve_left (key a.1 a.2) hrl).2
        rw [interp_gtr Y _ (gagree_diaPush C env hag hr a hrl hm)
          (GTr.npl_comp _ _ (GTr.npl_dia C x _) (npl_ptrXC hM₀ _ _ _ _ _ _ _ hm))
          (Ctx.noProjLast_diaIn _ _)]
        refine gtoDom_congr ?_ _ _
        rw [GTr.app_comp, ← pTrX_app]
        refine Eq.trans ?_ (dif_neg hrl).symm
        change _ = grden hM₀ a.1.1 _ (Ctx.Le.refl _) (pTrX hM₀ w a.1.1 _ _ k _ _ hm
          (Term.mono (Ctx.Le.refl _) ((C.dia x hx).app Y).2)).2
        rw [Term.mono_refl]
    termination_by _ _ _ X => X.size
    decreasing_by
      all_goals simp only [Term.size]
      all_goals omega
end

/-! ## The canonical environment -/

variable (hM₀) in
/-- ⭐The canonical environment: every visible address denotes its η-expansion. -/
noncomputable def gcanonEnv (s : GW hF M₀) (i : ℕ) : (gmodel hF hM₀).Env (ctxOf (glat s i)) s :=
  fun v T hv => gtoDom hM₀ T s (grden hM₀ s i (Ctx.Le.refl _) (Term.eta v T
    ((Ctx.ref_nonproj _ (Ctx.Presented.noProjLast _ v T hv)).trans hv))) (gdefinable_rden _ _)

theorem gagree_canon (s : GW hF M₀) (i : ℕ) : GAgree hM₀ (.nil _) (gcanonEnv hM₀ s i) :=
  gagree_of_raw _ _ fun _ _ _ _ => rfl

/-- ⭐**In an environment agreeing with the canonical one, a term's value is its denotation.** -/
theorem interp_gcanon {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a) {s : GW hF M₀}
    {i : ℕ} {e : Γ.Le (ctxOf (glat s i))} {env : (gmodel hF hM₀).Env Γ s}
    (hag : Model.Env.Agree e env (gcanonEnv hM₀ s i)) (hΓ : Γ.NoProjLast) :
    Model.interp env t = gtoDom hM₀ A s (grden hM₀ s i e t) (gdefinable_rden e t) := by
  have hag' : GAgree hM₀ (.mono e (.nil _)) env := fun v T hv => by
    rw [Model.Env.ref_agree hag v hv, gagree_canon s i v T (e.ref hv)]
    exact gtoDom_congr (grden_sigma _ (congrArg (Sigma.mk _) (Term.mono_eta e v T hv)).symm) _ _
  rw [interp_gtr t _ hag' trivial hΓ]
  exact gtoDom_congr ((grden_mono e t s i (Ctx.Le.refl _)).trans rfl) _ _

end GArrow

end V12M
