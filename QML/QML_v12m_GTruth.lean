import QML.QML_v12m_GCanonTerm
import QML.QML_v12m_Completeness

/-!
# QML v12m — the growing tree's canonical model: the truth lemma

* `pTrW`, `pTrXW`: a path's translations of formulas, as `pTr`, `pTrX` of terms.
* Along one edge the canonical environment pushed into a view **is** the target's canonical
  environment read through the edge's entries (`gcanon_boxPush_edge`, `gcanon_diaPush_edge`): the
  truth lemma for terms holds at every term, the entries' among them.
* ⭐`sat_boxPush_path`, `sat_diaPush_path`: along a path, the view satisfies a formula exactly when
  the end's canonical environment satisfies its translation — semantically, by `sat_shift_twoBox`
  and `Env.shiftAgree_diaKeep` for the first edge kept.
* `box_mem_path`, `boxx_mem_path`: what is necessary is translated into every descendant
  (`four_box`, `four_dia` and the edges' transfers).
* ⭐`gtruth`: the truth lemma.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Translating formulas along a path -/

variable (hM₀ : Theory.IsMCS M₀)

/-- ⭐A `□` view's formula translated along a path. -/
noncomputable def pTrW : (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → P ≠ [] →
    (i : ℕ) → WFF σ ((ctxOf (glat s i)).kView none) 0 → WFF σ (ctxOf (glat t (pstg s t P h i))) 0
  | _, _, [], _, hP, _, _ => absurd rfl hP
  | _, t, [c], h, _, i, φ =>
      WFF.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots φ
  | s, t, c :: c' :: P, h, _, i, φ =>
      pTrW (stepW s c (born_step h)) t (c' :: P) h (List.cons_ne_nil _ _)
        (glstg s (stepW s c (born_step h)) i)
        (WFF.subst (eIdx (fmapL hF M₀ (c :: s.1)))
          (eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).box
          (Subst.ok_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          (Subst.coh_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          Ctx.NoSlots.slots Ctx.NoSlots.slots
          (WFF.shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots φ))

theorem size_pTrW : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : P ≠ [])
    (i : ℕ) (φ : WFF σ ((ctxOf (glat s i)).kView none) 0),
    (pTrW hM₀ s t P h hP i φ).size = φ.size
  | _, _, [], _, hP, _, _ => absurd rfl hP
  | _, _, [_], _, _, _, _ => WFF.size_subst _ _ _ _ _ _
  | s, t, c :: c' :: P, h, _, _, φ =>
      (size_pTrW (stepW s c (born_step h)) t (c' :: P) h (List.cons_ne_nil _ _) _ _).trans
        ((WFF.size_subst _ _ _ _ _ _).trans (WFF.size_shift _ _ φ))

/-- ⭐**What is necessary is translated into every descendant**: `four_box`, then the first
    edge's transfer, then the rest of the path. -/
theorem box_mem_path : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : P ≠ [])
    (i : ℕ) (φ : WFF σ ((ctxOf (glat s i)).kView none) 0), .box φ ∈ (gw hM₀ s).M i →
    pTrW hM₀ s t P h hP i φ ∈ (gw hM₀ t).M (pstg s t P h i)
  | _, _, [], _, hP, _, _, _ => absurd rfl hP
  | _, _, [c], h, _, i, φ, hφ => gltr hM₀ ⟨c, h⟩ i φ hφ
  | s, t, c :: c' :: P, h, _, i, φ, hφ => by
      have h4 : WFF.box (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots φ)) ∈
          (gw hM₀ s).M i :=
        BWorld.mem_of_provable (Δ := [.box φ])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hφ)
          ⟨Proof.four_box hF (Proof.lookup List.mem_cons_self)⟩
      exact box_mem_path (stepW s c (born_step h)) t (c' :: P) h (List.cons_ne_nil _ _) _ _
        (gltr hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i _ h4)

/-! ## Views along an edge -/

variable [ModalSys.NoT] [ModalSys.NoSym] {hM₀}

/-- Agreement into `□` along an arrow, for any path to its end. -/
theorem gagree_boxPush_path {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) (t : GW hF M₀) (hR : GR w t)
    (P : List ℕ) (h : t.1 = nodeOf w.1 P) (hP : P ≠ []) :
    GAgree hM₀ (C.box.comp (ptrC hM₀ w t P h hP k)) (env.boxPush ⟨t, ⟨hR⟩⟩) := by
  obtain rfl := pathOf_of hR h
  exact gagree_boxPush C env hag ⟨t, ⟨hR⟩⟩

/-- An environment agreeing with a substitution's chain is the substituted canonical
    environment. -/
theorem eq_substEnv_of_gagree {Γ : Ctx} [Γ.NoSlots] (hnp : Γ.NoProjLast) {t : GW hF M₀} {j : ℕ}
    {ι : VarSymb → VarSymb} (θ : Subst σ (ctxOf (glat t j))) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (env : (gmodel hF hM₀).Env Γ t)
    (hag : GAgree hM₀ (.sub θ hθ hc (.nil _)) env) :
    env = Model.substEnv θ hθ hnp (gcanonEnv hM₀ t j) := by
  funext v T hv
  have hlp := hnp v T hv
  have href : Γ.ref v = some T := (Ctx.ref_nonproj Γ hlp).trans hv
  rw [← Model.Env.ref_of_nonproj env hlp href hv, hag v T href,
    ← Model.Env.ref_of_nonproj (Model.substEnv θ hθ hnp (gcanonEnv hM₀ t j)) hlp href hv,
    ← Model.interp_eta, ← Model.interp_subst θ hθ hc,
    interp_gcanon _ (Model.Env.Agree.refl' _)]
  rfl

/-- ⭐**Along an edge, the canonical environment pushed into `□` is the target's read through
    the edge.** -/
theorem gcanon_boxPush_edge (s t : GW hF M₀) (c : ℕ) (h : t.1 = nodeOf s.1 [c]) (i : ℕ)
    (hR : GR s t) :
    (gcanonEnv hM₀ s i).boxPush ⟨t, ⟨hR⟩⟩ =
      Model.substEnv (eS σ _ (fmapL hF M₀ t.1)) (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
        (Ctx.noProjLast_boxIn _) (gcanonEnv hM₀ t (glstg s t i)) :=
  eq_substEnv_of_gagree _ _ _ (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) _
    (gagree_boxPush_path (.nil _) _ (gagree_canon s i) t hR [c] h (List.cons_ne_nil _ _))

/-- ⭐**Along a path, the `□` view satisfies a formula exactly when the end satisfies its
    translation.** -/
theorem sat_boxPush_path : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P)
    (hP : P ≠ []) (i : ℕ) (hR : GR s t) (φ : WFF σ ((ctxOf (glat s i)).kView none) 0),
    (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).boxPush ⟨t, ⟨hR⟩⟩) φ ↔
      (gmodel hF hM₀).sat (gcanonEnv hM₀ t (pstg s t P h i)) (pTrW hM₀ s t P h hP i φ)
  | _, _, [], _, hP, _, _, _ => absurd rfl hP
  | s, t, [c], h, _, i, hR, φ => by
      rw [gcanon_boxPush_edge s t c h i hR]
      exact (Model.sat_subst _ _ (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) Ctx.NoSlots.slots
        Ctx.NoSlots.slots _ _ φ).symm
  | s, t, c :: c' :: P, h, _, i, hR, φ => by
      have hb := born_step h
      have e : GR s (stepW s c hb) := ⟨[c], List.cons_ne_nil _ _, rfl⟩
      have q : GR (stepW s c hb) t := ⟨c' :: P, List.cons_ne_nil _ _, h⟩
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      refine (Model.sat_shift_twoBox hF (gcanonEnv hM₀ s i) Ctx.NoSlots.slots φ
        ⟨_, ⟨e⟩⟩ ⟨t, ⟨q⟩⟩).symm.trans ?_
      rw [gcanon_boxPush_edge s (stepW s c hb) c rfl i e, ← Model.substEnv_box _ hθ]
      refine (Model.sat_subst _ _ (Subst.coh_box hθ hc) Ctx.NoSlots.slots Ctx.NoSlots.slots _ _
        _).symm.trans ?_
      exact sat_boxPush_path (stepW s c hb) t (c' :: P) h (List.cons_ne_nil _ _) _ q _

/-! ## Witnesses' views along a path -/

variable (hM₀) in
/-- ⭐A witness's view's formula translated along a path in its extent. -/
noncomputable def pTrXW : (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → (i : ℕ) →
    (x : VarSymb) → (∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) → InExt s t P h x →
    WFF σ ((ctxOf (glat s i)).kView (some x)) 0 → WFF σ (ctxOf (glat t (pstg s t P h i))) 0
  | _, _, [], _, _, _, _, hm, _ => hm.elim
  | _, t, [c], h, i, _, _, hm, χ =>
      WFF.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i)) (coh_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots χ
  | s, t, c :: c' :: P, h, i, x, hx, hm, χ =>
      pTrXW (stepW s c (born_step h)) t (c' :: P) h (glstg s (stepW s c (born_step h)) i)
        (wit (stepW s c (born_step h)) x) (wit_ref hM₀ (born_step h) i hx) hm
        (WFF.subst (eIdx (fmapL hF M₀ (c :: s.1)))
          ((eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).dia (.step x .keep) (wit (stepW s c (born_step h)) x))
          (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx)
            ((coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
              (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
          (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx))
          Ctx.NoSlots.slots Ctx.NoSlots.slots
          (WFF.shift (Ctx.shifts_diaIn_keep hF _ x) Ctx.NoSlots.slots χ))

omit [ModalSys.NoT] [ModalSys.NoSym] in
theorem size_pTrXW : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x) (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    (pTrXW hM₀ s t P h i x hx hm χ).size = χ.size
  | _, _, [], _, _, _, _, hm, _ => hm.elim
  | _, _, [_], _, _, _, _, _, _ => WFF.size_subst _ _ _ _ _ _
  | s, t, c :: c' :: P, h, _, _, _, hm, χ =>
      (size_pTrXW (stepW s c (born_step h)) t (c' :: P) h _ _ _ hm _).trans
        ((WFF.size_subst _ _ _ _ _ _).trans (WFF.size_shift _ _ χ))

omit [ModalSys.NoT] [ModalSys.NoSym] in
theorem pTrXW_neg : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x) (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    pTrXW hM₀ s t P h i x hx hm χ.neg = (pTrXW hM₀ s t P h i x hx hm χ).neg
  | _, _, [], _, _, _, _, hm, _ => hm.elim
  | _, _, [_], _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, hm, _ =>
      pTrXW_neg (stepW s c (born_step h)) t (c' :: P) h _ _ _ hm _

omit [ModalSys.NoT] [ModalSys.NoSym] in
/-- ⭐**What holds throughout a possible object's extent is translated into every arrow of it**:
    `four_dia`, then the first edge's transfer, then the rest of the path. -/
theorem boxx_mem_path : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x) (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    WFF.boxx x hx χ ∈ (gw hM₀ s).M i →
    pTrXW hM₀ s t P h i x hx hm χ ∈ (gw hM₀ t).M (pstg s t P h i)
  | _, _, [], _, _, _, _, hm, _, _ => hm.elim
  | _, _, [c], h, i, x, hx, hm, χ, hχ => by
      obtain ⟨X, hX⟩ := hx
      exact gltrX hM₀ ⟨c, h⟩ hm i hX χ hχ
  | s, t, c :: c' :: P, h, i, x, hx, hm, χ, hχ => by
      have h4 : WFF.box (WFF.boxx (.step x .keep) (Ctx.exists_keep_dia hF hx)
          (WFF.shift (Ctx.shifts_diaIn_keep hF _ x) Ctx.NoSlots.slots χ)) ∈ (gw hM₀ s).M i :=
        BWorld.mem_of_provable (Δ := [WFF.boxx x hx χ])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hχ)
          ⟨Proof.four_dia hF hx (Proof.lookup List.mem_cons_self)⟩
      exact boxx_mem_path (stepW s c (born_step h)) t (c' :: P) h _ _ _ hm _
        (gltr hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i _ h4)

omit [ModalSys.NoT] [ModalSys.NoSym] in
theorem inExt_pathOf {s t : GW hF M₀} (hR : GR s t) {P : List ℕ} {h : t.1 = nodeOf s.1 P}
    {x : VarSymb} (hm : InExt s t P h x) : InExt s t (pathOf hR) (pathOf_eq hR) x := by
  obtain rfl := pathOf_of hR h
  exact hm

/-- The canonical extent of a witness: the paths in it. -/
theorem gcanon_mem_iff (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) (a : GAcc hF M₀ s) :
    a ∈ ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x hr)).1 ↔
      InExt s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) x := by
  rw [gagree_canon s i x _ hr]
  exact Iff.rfl

/-- Agreement into `◇_x` along an arrow of the extent, for any path to its end. -/
theorem gagree_diaPush_path {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (t : GW hF M₀) (hR : GR w t)
    (hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ w) ∈ ((gmodel hF hM₀).posEval (env.ref x hr)).1)
    (P : List ℕ) (h : t.1 = nodeOf w.1 P) (hm : InExt w t P h (C.idx x)) :
    GAgree hM₀ ((C.dia x ⟨X, hr⟩).comp (ptrXC hM₀ w t P h k (C.idx x) (C.idx_decl ⟨X, hr⟩) hm))
      (env.diaPush x hr ⟨_, hmt⟩) := by
  obtain rfl := pathOf_of hR h
  exact gagree_diaPush C env hag hr ⟨_, hmt⟩ hm

/-- ⭐**Along an edge made for a witness, the canonical environment pushed into its view is the
    target's read through the edge.** -/
theorem gcanon_diaPush_edge (s t : GW hF M₀) (c : ℕ) (h : t.1 = nodeOf s.1 [c]) (i : ℕ)
    {x : VarSymb} {X : VarType} (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hR : GR s t) (hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x hr)).1) (hk : lkd t = some x) :
    (gcanonEnv hM₀ s i).diaPush x hr ⟨_, hmt⟩ =
      Model.substEnv (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (l := glat s i) (k := some x) (hk ▸ gentOk hM₀ ⟨c, h⟩ i))
        (Ctx.noProjLast_diaIn (ctxOf (glat s i)) x) (gcanonEnv hM₀ t (glstg s t i)) :=
  eq_substEnv_of_gagree _ _ _ (coh_eS_kView (hk ▸ gentOk hM₀ ⟨c, h⟩ i)) _
    (gagree_diaPush_path (.nil _) _ (gagree_canon s i) hr t hR hmt [c] h hk)

theorem sat_diaPush_congr {Γ : Ctx} {w : GW hF M₀} {env₁ env₂ : (gmodel hF hM₀).Env Γ w}
    (e : env₁ = env₂) {y : VarSymb} {Y : VarType} (hy : Γ.ref y = some (.VTypeDia Y))
    (b : GAcc hF M₀ w) (h₁ : b ∈ ((gmodel hF hM₀).posEval (env₁.ref y hy)).1)
    (h₂ : b ∈ ((gmodel hF hM₀).posEval (env₂.ref y hy)).1) (φ : WFF σ (Γ.diaIn y) 0) :
    (gmodel hF hM₀).sat (env₁.diaPush y hy ⟨b, h₁⟩) φ ↔
      (gmodel hF hM₀).sat (env₂.diaPush y hy ⟨b, h₂⟩) φ := by
  subst e
  exact Iff.rfl

/-- ⭐**Along a path in a witness's extent, its view satisfies a formula exactly when the end
    satisfies its translation.** -/
theorem sat_diaPush_path : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) {X : VarType} (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hR : GR s t) (hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x hr)).1)
    (hm : InExt s t P h x) (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).diaPush x hr ⟨_, hmt⟩) χ ↔
      (gmodel hF hM₀).sat (gcanonEnv hM₀ t (pstg s t P h i)) (pTrXW hM₀ s t P h i x ⟨X, hr⟩ hm χ)
  | _, _, [], _, _, _, _, _, _, _, hm, _ => hm.elim
  | s, t, [c], h, i, x, _, hr, hR, hmt, hm, χ => by
      rw [gcanon_diaPush_edge s t c h i hr hR hmt hm]
      exact (Model.sat_subst _ _ (coh_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i)) Ctx.NoSlots.slots
        Ctx.NoSlots.slots _ _ χ).symm
  | s, t, c :: c' :: P, h, i, x, X, hr, hR, hmt, hm, χ => by
      have hb := born_step h
      have e : GR s (stepW s c hb) := ⟨[c], List.cons_ne_nil _ _, rfl⟩
      have q : GR (stepW s c hb) t := ⟨c' :: P, List.cons_ne_nil _ _, h⟩
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hyk : (ctxOf (glat s i)).boxIn.ref (.step x .keep) = some (.VTypeDia X) :=
        Ctx.ref_keep_of' hF hr VarType.keepable_dia
      have hw := hc (.step x .keep) _ hyk []
      obtain ⟨Z, hr₁⟩ := wit_ref hM₀ hb i ⟨X, hr⟩
      have hwm : (⟨t, ⟨q⟩⟩ : GAcc hF M₀ (stepW s c hb)) ∈ ((gmodel hF hM₀).posEval
          ((gcanonEnv hM₀ (stepW s c hb) (glstg s (stepW s c hb) i)).ref _ hr₁)).1 :=
        (gcanon_mem_iff (stepW s c hb) _ hr₁ ⟨t, ⟨q⟩⟩).mpr (inExt_pathOf q
          (show InExt (stepW s c hb) t (c' :: P) h (wit (stepW s c hb) x) from hm))
      have hm₃ : (⟨t, ⟨q⟩⟩ : GAcc hF M₀ (stepW s c hb)) ∈ ((gmodel hF hM₀).posEval
          ((Model.substEnv _ hθ (Ctx.noProjLast_boxIn _)
            (gcanonEnv hM₀ (stepW s c hb) (glstg s (stepW s c hb) i))).ref (.step x .keep)
              hyk)).1 := by
        rw [Model.substEnv_ref, Model.entryVal_dia_ext _ _ hw hr₁]
        exact hwm
      have hsub := Model.substEnv_dia _ hθ (Ctx.noProjLast_boxIn _)
        (gcanonEnv hM₀ (stepW s c hb) (glstg s (stepW s c hb) i)) (Ctx.exists_keep_dia hF ⟨X, hr⟩)
        hyk hr₁ hw ⟨_, hwm⟩ hm₃
      have hm₂ : (⟨t, ⟨q⟩⟩ : GAcc hF M₀ (stepW s c hb)) ∈ ((gmodel hF hM₀).posEval
          (((gcanonEnv hM₀ s i).boxPush ⟨_, ⟨e⟩⟩).ref (.step x .keep) hyk)).1 := by
        rw [gcanon_boxPush_edge s (stepW s c hb) c rfl i e]
        exact hm₃
      refine (Model.sat_shift Ctx.NoSlots.slots (Model.Env.shiftAgree_diaKeep hF
        (gcanonEnv hM₀ s i) hr ⟨_, ⟨e⟩⟩ ⟨t, ⟨q⟩⟩ hmt hyk hm₂) χ).symm.trans ?_
      refine (sat_diaPush_congr (gcanon_boxPush_edge s (stepW s c hb) c rfl i e) hyk _ hm₂
        hm₃ _).trans ?_
      rw [← hsub]
      refine (Model.sat_subst _ _ (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF ⟨X, hr⟩))
        Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ _).symm.trans ?_
      exact sat_diaPush_path (stepW s c hb) t (c' :: P) h _ _ hr₁ q hwm hm _

/-! ## The truth lemma -/

/-- The truth lemma for atoms. -/
theorem relSat_gcanon : ∀ {Γ : Ctx} {n : ℕ} (ρ : Rel σ Γ n) {s : GW hF M₀} {i : ℕ}
    {e : Γ.Le (ctxOf (glat s i))} {env : (gmodel hF hM₀).Env Γ s},
    Model.Env.Agree e env (gcanonEnv hM₀ s i) →
    ∀ (args : Fin n → (gw hM₀ s).D) (ts : Fin n → Term σ Γ .Var .var),
      (∀ k, args k = (gw hM₀ s).cls i (Term.mono e (ts k))) →
      (Model.relSat env ρ args ↔
        WFF.mono e (.atom ((Spine.ofFn ts).fillR ρ)) ∈ (gw hM₀ s).M i)
  | _, _, .R ⟨r, rfl⟩, s, i, e, _, _, args, ts, hts => by
      change (gw hM₀ s).canonRel r (fun k => args (Fin.cast rfl k)) ↔ _
      rw [WFF.mono_fillR, Spine.mono_ofFn,
        show (fun k => args (Fin.cast rfl k)) = fun k => (gw hM₀ s).cls i (Term.mono e (ts k)) from
          funext fun k => hts k,
        BWorld.canonRel_cls]
      rfl
  | _, _, .eval ρ t, s, i, e, env, hag, args, ts, hts => by
      change Model.relSat env ρ (Fin.cons (Model.interp env t) args) ↔ _
      have h0 : Model.interp env t = (gw hM₀ s).cls i (Term.mono e t) :=
        (interp_gcanon t hag).trans (grden_var_mono e t)
      rw [relSat_gcanon ρ hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
        (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
      rfl

/-- The canonical environment at a later stage agrees with the one at an earlier stage. -/
theorem gcanonEnv_le (s : GW hF M₀) {i j : ℕ} (hij : i ≤ j) :
    Model.Env.Agree ((gw hM₀ s).le hij) (gcanonEnv hM₀ s i) (gcanonEnv hM₀ s j) :=
  fun v T hv => gtoDom_congr (by
    rw [show Term.eta (σ := σ) v T _ = Term.mono ((gw hM₀ s).le hij) (Term.eta v T _) from
      (Term.mono_eta _ v T _).symm, grden_mono]
    exact grden_congr _ _ _ _ _ _) _ _

/-- A denotable object is the value of a term at a later stage. -/
theorem ginterp_lift {A : VarType} {s : GW hF M₀} {i i' : ℕ} {a : Ann A}
    {t' : Term σ (ctxOf (glat s i')) A a} {o : (gframe hF hM₀).Dom A s}
    (ht' : grden hM₀ s i' (Ctx.Le.refl _) t' = gfromDom hM₀ A s o) (hK : i' ≤ i) :
    Model.interp (gcanonEnv hM₀ s i) ((gw hM₀ s).liftT hK t') = o :=
  (interp_gcanon _ (Model.Env.Agree.refl' _)).trans
    ((gtoDom_congr ((grden_mono _ t' s _ _).trans ((grden_congr t' s _ i' _ _).trans ht')) _
      _).trans (gtoDom_fromDom hM₀ A s o))

theorem gtruth_lt :
    ∀ (n : ℕ) (s : GW hF M₀) (i : ℕ) (φ : WFF σ (ctxOf (glat s i)) 0), φ.size < n →
    ((gmodel hF hM₀).sat (gcanonEnv hM₀ s i) φ ↔ φ ∈ (gw hM₀ s).M i)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, i, φ, hφ => by
      cases φ with
      | atom ρ =>
          change Model.relSat (gcanonEnv hM₀ s i) ρ Fin.elim0 ↔ _
          rw [relSat_gcanon ρ (Model.Env.Agree.refl' _) Fin.elim0 Fin.elim0 (fun k => k.elim0)]
          change WFF.mono (Ctx.Le.refl _) (.atom ρ) ∈ (gw hM₀ s).M i ↔ _
          rw [WFF.mono_refl]
      | eq t u =>
          change Model.interp (gcanonEnv hM₀ s i) t = Model.interp (gcanonEnv hM₀ s i) u ↔ _
          rw [interp_gcanon t (Model.Env.Agree.refl' _), interp_gcanon u (Model.Env.Agree.refl' _)]
          change grden hM₀ s i (Ctx.Le.refl _) t = grden hM₀ s i (Ctx.Le.refl _) u ↔ _
          rw [grden_var_cls, grden_var_cls, BWorld.cls_eq_iff (le_refl i) (le_refl i)]
          change WFF.eq (Term.mono ((gw hM₀ s).le (le_refl i)) t)
            (Term.mono ((gw hM₀ s).le (le_refl i)) u) ∈ (gw hM₀ s).M i ↔ _
          rw [Term.mono_refl, Term.mono_refl]
      | top => exact ⟨fun _ => ((gw hM₀ s).mcs i).top_mem, fun _ => trivial⟩
      | bot => exact ⟨False.elim, fun h => ((gw hM₀ s).mcs i).bot_not_mem h⟩
      | here hT _ _ => exact (absT hT).elim
      | back hB _ _ _ => exact (absBS hB).elim
      | retS hB _ _ _ => exact (absBS hB).elim
      | retxS hB _ _ _ _ _ => exact (absBS hB).elim
      | and φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∧ _ ↔ _
          rw [gtruth_lt n s i φ h₁, gtruth_lt n s i ψ h₂, ((gw hM₀ s).mcs i).and_mem_iff]
      | or φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∨ _ ↔ _
          rw [gtruth_lt n s i φ h₁, gtruth_lt n s i ψ h₂, ((gw hM₀ s).mcs i).or_mem_iff]
      | imp φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (_ → _) ↔ _
          rw [gtruth_lt n s i φ h₁, gtruth_lt n s i ψ h₂, ((gw hM₀ s).mcs i).imp_mem_iff]
      | all A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ o : (gframe hF hM₀).Dom A s,
            (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨i', hi, a, t, hmem⟩ := (gw hM₀ s).allW (((gw hM₀ s).mcs i).neg_mem_iff.mpr hnot)
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (gcanonEnv_le s hi) (.bnd 0)
              (Model.interp (gcanonEnv hM₀ s i') t)) ψ).mpr (hsat _)
            have hs₂ := (Model.sat_instantiate (gcanonEnv hM₀ s i')
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots t _).mpr hs₁
            have hs₃ := (gtruth_lt n s i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (((gw hM₀ s).mcs i').neg_mem_iff.mp hmem) hs₃
          · intro hmem o
            obtain ⟨i', a, t', ht'⟩ := gdefinable_fromDom hM₀ A s o
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
            have hs := (gtruth_lt n s (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hinst
            have hs₁ := (Model.sat_instantiate (gcanonEnv hM₀ s (i ⊔ i'))
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t') _).mp hs
            rw [ginterp_lift ht' hK'] at hs₁
            exact (Model.sat_mono (Model.Env.extend_agree (gcanonEnv_le s hK) (.bnd 0) o)
              ψ).mp hs₁
      | ex A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ o : (gframe hF hM₀).Dom A s,
            (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · rintro ⟨o, hsat⟩
            obtain ⟨i', a, t', ht'⟩ := gdefinable_fromDom hM₀ A s o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (gcanonEnv_le s hK) (.bnd 0) o)
              ψ).mpr hsat
            rw [← ginterp_lift ht' hK'] at hs₁
            have hs₂ := (Model.sat_instantiate (gcanonEnv hM₀ s (i ⊔ i'))
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots ((gw hM₀ s).liftT hK' t') _).mpr hs₁
            have hmemK := (gtruth_lt n s (i ⊔ i') _
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
            refine ⟨Model.interp (gcanonEnv hM₀ s i') t, ?_⟩
            have hs := (gtruth_lt n s i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hmem'
            have hs₁ := (Model.sat_instantiate (gcanonEnv hM₀ s i') (Ctx.Presented.noProjLast _)
              Ctx.NoSlots.slots t _).mp hs
            exact (Model.sat_mono (Model.Env.extend_agree (gcanonEnv_le s hi) (.bnd 0) _)
              ψ).mp hs₁
      | box χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ a : GAcc hF M₀ s,
            (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).boxPush a) χ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨t, ⟨c, hc⟩, -, hneg⟩ := glex hM₀ s i χ hnot
            have hR : GR s t := ⟨[c], List.cons_ne_nil _ _, hc⟩
            have h1 := (sat_boxPush_path s t [c] hc (List.cons_ne_nil _ _) i hR χ).mp
              (hsat ⟨t, ⟨hR⟩⟩)
            have h2 := (gtruth_lt n t _ _ (by rw [size_pTrW]; exact hχs)).mp h1
            exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem a
            obtain ⟨t, ⟨hR⟩⟩ := a
            refine (sat_boxPush_path s t _ (pathOf_eq hR) (pathOf_ne hR) i hR χ).mpr ?_
            exact (gtruth_lt n t _ _ (by rw [size_pTrW]; exact hχs)).mpr
              (box_mem_path hM₀ s t _ (pathOf_eq hR) (pathOf_ne hR) i χ hmem)
      | dia x hx χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
            (a : ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x h)).1),
              (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).diaPush x h a) χ) ↔ _
          constructor
          · rintro ⟨X, h, ⟨⟨t, ⟨hR⟩⟩, hmt⟩, hsat⟩
            have hm := (gcanon_mem_iff s i h ⟨t, ⟨hR⟩⟩).mp hmt
            have h1 := (sat_diaPush_path s t _ (pathOf_eq hR) i x h hR hmt hm χ).mp hsat
            have h2 := (gtruth_lt n t _ _ (by rw [size_pTrXW]; exact hχs)).mp h1
            by_contra hnot
            have hbx : WFF.boxx x hx χ.neg ∈ (gw hM₀ s).M i :=
              BWorld.mem_of_provable (Δ := [(WFF.dia x hx χ).neg])
                (fun ψ hψ => by
                  rw [List.mem_singleton.mp hψ]
                  exact ((gw hM₀ s).mcs i).neg_mem_iff.mpr hnot)
                ⟨Proof.boxx_neg_of_not_dia (Γ := (gw hM₀ s).ctx i) x hx χ⟩
            have hneg := boxx_mem_path s t _ (pathOf_eq hR) i x hx hm χ.neg hbx
            rw [pTrXW_neg] at hneg
            exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem
            obtain ⟨X, h⟩ := id hx
            obtain ⟨t, ⟨c, hc⟩, hk, hm⟩ := glexX hM₀ s i x X h χ hmem
            have hR : GR s t := ⟨[c], List.cons_ne_nil _ _, hc⟩
            have hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
                ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x h)).1 :=
              (gcanon_mem_iff s i h _).mpr (inExt_pathOf hR (show InExt s t [c] hc x from hk))
            exact ⟨X, h, ⟨_, hmt⟩, (sat_diaPush_path s t [c] hc i x h hR hmt hk χ).mpr
              ((gtruth_lt n t _ _ (by rw [size_pTrXW]; exact hχs)).mpr hm)⟩

/-- ⭐**The truth lemma** for the growing tree's canonical model. -/
theorem gtruth (s : GW hF M₀) (i : ℕ) (φ : WFF σ (ctxOf (glat s i)) 0) :
    (gmodel hF hM₀).sat (gcanonEnv hM₀ s i) φ ↔ φ ∈ (gw hM₀ s).M i :=
  gtruth_lt (φ.size + 1) s i φ (Nat.lt_succ_self _)

end GArrow

end V12M
