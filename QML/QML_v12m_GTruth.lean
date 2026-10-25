import QML.QML_v12m_GCanonTerm
import QML.QML_v12m_Completeness
import QML.QML_v12m_SubstRealise
import QML.QML_v12m_GLeafInj

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

/-- Under T the `□`-lift is on whenever the `◇`-lift is: the systems the growing tree's `here`
    case covers (docs §3 4, "Diagnosis": the `FourStrongW`-only system with T is still open).
    Without T there is nothing to ask (`ModalSys.NoT`). -/
class ModalSys.FourCoh [ModalSys] : Prop where
  strong : ModalSys.T = true → ModalSys.FourStrongW = true → ModalSys.FourStrong = true

instance ModalSys.FourCoh.of_noT [ModalSys] [ModalSys.NoT] : ModalSys.FourCoh :=
  ⟨fun hT => (absT hT).elim⟩

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Translating formulas along a path -/

variable (hM₀ : Theory.IsMCS M₀)

/-- ⭐A `□` view's formula translated along a path. -/
noncomputable def pTrW : (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → PathOk P →
    (i : ℕ) → WFF σ ((ctxOf (glat s i)).kView none) 0 → WFF σ (ctxOf (glat t (pstg s t P h i))) 0
  | _, _, [], h, hP, i, φ =>
      WFF.mono (glat_le_of_eq h i)
        (WFF.collapse (Ctx.collapses_boxIn_self hP.T_of_nil _) Ctx.NoSlots.slots φ)
  | _, t, [c], h, _, i, φ =>
      WFF.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots φ
  | s, t, c :: c' :: P, h, _, i, φ =>
      pTrW (stepW s c (born_step h)) t (c' :: P) h (pathOk_cons)
        (glstg s (stepW s c (born_step h)) i)
        (WFF.subst (eIdx (fmapL hF M₀ (c :: s.1)))
          (eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).box
          (Subst.ok_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          (Subst.coh_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          Ctx.NoSlots.slots Ctx.NoSlots.slots
          (WFF.shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots φ))

theorem size_pTrW : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) (φ : WFF σ ((ctxOf (glat s i)).kView none) 0),
    (pTrW hM₀ s t P h hP i φ).size = φ.size
  | _, _, [], _, _, _, φ => (WFF.size_mono _ _).trans (WFF.size_collapse _ _ φ)
  | _, _, [_], _, _, _, _ => WFF.size_subst _ _ _ _ _ _
  | s, t, c :: c' :: P, h, _, _, φ =>
      (size_pTrW (stepW s c (born_step h)) t (c' :: P) h (pathOk_cons) _ _).trans
        ((WFF.size_subst _ _ _ _ _ _).trans (WFF.size_shift _ _ φ))

/-- ⭐**What is necessary is translated into every descendant**: `four_box`, then the first
    edge's transfer, then the rest of the path. -/
theorem box_mem_path : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P)
    (i : ℕ) (φ : WFF σ ((ctxOf (glat s i)).kView none) 0), .box φ ∈ (gw hM₀ s).M i →
    pTrW hM₀ s t P h hP i φ ∈ (gw hM₀ t).M (pstg s t P h i)
  | s, t, [], h, hP, i, φ, hφ => by
      have hT := hP.T_of_nil
      obtain rfl : t = s := gw_eq h
      have hc : WFF.collapse (Ctx.collapses_boxIn_self hT _) Ctx.NoSlots.slots φ ∈
          (gw hM₀ t).M i :=
        BWorld.mem_of_provable (Δ := [.box φ])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hφ)
          ⟨Proof.T_box hT (Proof.lookup List.mem_cons_self)⟩
      refine (BWorld.mem_mono_congr (w := gw hM₀ t) (glat_le_of_eq h i) (Ctx.Le.refl _)).mpr ?_
      rw [WFF.mono_refl]
      exact hc
  | _, _, [c], h, _, i, φ, hφ => gltr hM₀ ⟨c, h⟩ i φ hφ
  | s, t, c :: c' :: P, h, _, i, φ, hφ => by
      have h4 : WFF.box (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots φ)) ∈
          (gw hM₀ s).M i :=
        BWorld.mem_of_provable (Δ := [.box φ])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hφ)
          ⟨Proof.four_box hF (Proof.lookup List.mem_cons_self)⟩
      exact box_mem_path (stepW s c (born_step h)) t (c' :: P) h (pathOk_cons) _ _
        (gltr hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i _ h4)

/-! ## Views along an edge -/

variable [ModalSys.NoSym] {hM₀}

/-- Agreement into `□` along an arrow, for any path to its end. -/
theorem gagree_boxPush_path {Γ : Ctx} {w : GW hF M₀} {k : ℕ} (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) (t : GW hF M₀) (hR : GR w t)
    (P : List ℕ) (h : t.1 = nodeOf w.1 P) (hP : PathOk P) :
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
    interp_gcanon _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
  rfl

/-- ⭐**Along an edge, the canonical environment pushed into `□` is the target's read through
    the edge.** -/
theorem gcanon_boxPush_edge (s t : GW hF M₀) (c : ℕ) (h : t.1 = nodeOf s.1 [c]) (i : ℕ)
    (hR : GR s t) :
    (gcanonEnv hM₀ s i).boxPush ⟨t, ⟨hR⟩⟩ =
      Model.substEnv (eS σ _ (fmapL hF M₀ t.1)) (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
        (Ctx.noProjLast_boxIn _) (gcanonEnv hM₀ t (glstg s t i)) :=
  eq_substEnv_of_gagree _ _ _ (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) _
    (gagree_boxPush_path (.nil _) _ (gagree_canon s i) t hR [c] h (pathOk_cons))

/-- ⭐**Along a path, the `□` view satisfies a formula exactly when the end satisfies its
    translation.** -/
theorem sat_boxPush_path : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P)
    (hP : PathOk P) (i : ℕ) (hR : GR s t) (φ : WFF σ ((ctxOf (glat s i)).kView none) 0),
    (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).boxPush ⟨t, ⟨hR⟩⟩) φ ↔
      (gmodel hF hM₀).sat (gcanonEnv hM₀ t (pstg s t P h i)) (pTrW hM₀ s t P h hP i φ)
  | s, t, [], h, hP, i, hR, φ => by
      have hT := hP.T_of_nil
      obtain rfl : t = s := gw_eq h
      change _ ↔ (gmodel hF hM₀).sat (gcanonEnv hM₀ t i) (WFF.mono (glat_le_of_eq h i)
        (WFF.collapse (Ctx.collapses_boxIn_self hT _) Ctx.NoSlots.slots φ))
      rw [Model.sat_mono (env := gcanonEnv hM₀ t i) (env' := gcanonEnv hM₀ t i)
        (fun _ _ _ => rfl)]
      exact (Model.sat_collapse Ctx.NoSlots.slots (Model.Env.collapseAgree_self hT _) φ).symm
  | s, t, [c], h, _, i, hR, φ => by
      rw [gcanon_boxPush_edge s t c h i hR]
      exact (Model.sat_subst _ _ (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) Ctx.NoSlots.slots
        Ctx.NoSlots.slots _ _ φ).symm
  | s, t, c :: c' :: P, h, _, i, hR, φ => by
      have hb := born_step h
      have e : GR s (stepW s c hb) := ⟨[c], pathOk_cons, rfl⟩
      have q : GR (stepW s c hb) t := ⟨c' :: P, pathOk_cons, h⟩
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      refine (Model.sat_shift_twoBox hF (gcanonEnv hM₀ s i) Ctx.NoSlots.slots φ
        ⟨_, ⟨e⟩⟩ ⟨t, ⟨q⟩⟩).symm.trans ?_
      rw [gcanon_boxPush_edge s (stepW s c hb) c rfl i e, ← Model.substEnv_box _ hθ]
      refine (Model.sat_subst _ _ (Subst.coh_box hθ hc) Ctx.NoSlots.slots Ctx.NoSlots.slots _ _
        _).symm.trans ?_
      exact sat_boxPush_path (stepW s c hb) t (c' :: P) h (pathOk_cons) _ q _

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

omit [ModalSys.NoSym] in
theorem size_pTrXW : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x) (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    (pTrXW hM₀ s t P h i x hx hm χ).size = χ.size
  | _, _, [], _, _, _, _, hm, _ => hm.elim
  | _, _, [_], _, _, _, _, _, _ => WFF.size_subst _ _ _ _ _ _
  | s, t, c :: c' :: P, h, _, _, _, hm, χ =>
      (size_pTrXW (stepW s c (born_step h)) t (c' :: P) h _ _ _ hm _).trans
        ((WFF.size_subst _ _ _ _ _ _).trans (WFF.size_shift _ _ χ))

omit [ModalSys.NoSym] in
theorem pTrXW_neg : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : InExt s t P h x) (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    pTrXW hM₀ s t P h i x hx hm χ.neg = (pTrXW hM₀ s t P h i x hx hm χ).neg
  | _, _, [], _, _, _, _, hm, _ => hm.elim
  | _, _, [_], _, _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, hm, _ =>
      pTrXW_neg (stepW s c (born_step h)) t (c' :: P) h _ _ _ hm _

omit [ModalSys.NoSym] in
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

omit [ModalSys.NoSym] in
theorem inExt_pathOf {s t : GW hF M₀} (hR : GR s t) {P : List ℕ} {h : t.1 = nodeOf s.1 P}
    {x : VarSymb} (hm : InExt s t P h x) : InExt s t (pathOf hR) (pathOf_eq hR) x := by
  obtain rfl := pathOf_of hR h
  exact hm

/-- The canonical extent of a witness: the paths in it. -/
theorem gcanon_mem_iff (s : GW hF M₀) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) (a : GAcc hF M₀ s) :
    a ∈ ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x hr)).1 ↔
      GMem hM₀ s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) x := by
  rw [gagree_canon s i x _ hr]
  exact Iff.rfl

/-- Without T, agreement into `◇_x` along an arrow of the extent, for any path to its end. -/
theorem gagree_diaPush_path (hnT : ModalSys.T = false) {Γ : Ctx} {w : GW hF M₀} {k : ℕ}
    (C : GTr σ Γ (ctxOf (glat w k)))
    (env : (gmodel hF hM₀).Env Γ w) (hag : GAgree hM₀ C env) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (t : GW hF M₀) (hR : GR w t)
    (hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ w) ∈ ((gmodel hF hM₀).posEval (env.ref x hr)).1)
    (P : List ℕ) (h : t.1 = nodeOf w.1 P) (hm : InExt w t P h (C.idx x)) :
    GAgree hM₀ ((C.dia x ⟨X, hr⟩).comp (ptrXC hM₀ w t P h k (C.idx x) (C.idx_decl ⟨X, hr⟩) hm))
      (env.diaPush x hr ⟨_, hmt⟩) := by
  obtain rfl := pathOf_of hR h
  exact gagree_diaPush C env hag hr ⟨_, hmt⟩ (BWorld.not_realised hnT) hm

/-- ⭐**Without T, along an edge made for a witness, the canonical environment pushed into its
    view is the target's read through the edge.** -/
theorem gcanon_diaPush_edge (hnT : ModalSys.T = false) (s t : GW hF M₀) (c : ℕ)
    (h : t.1 = nodeOf s.1 [c]) (i : ℕ)
    {x : VarSymb} {X : VarType} (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hR : GR s t) (hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x hr)).1) (hk : lkd t = some x) :
    (gcanonEnv hM₀ s i).diaPush x hr ⟨_, hmt⟩ =
      Model.substEnv (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (l := glat s i) (k := some x) (hk ▸ gentOk hM₀ ⟨c, h⟩ i))
        (Ctx.noProjLast_diaIn (ctxOf (glat s i)) x) (gcanonEnv hM₀ t (glstg s t i)) :=
  eq_substEnv_of_gagree _ _ _ (coh_eS_kView (hk ▸ gentOk hM₀ ⟨c, h⟩ i)) _
    (gagree_diaPush_path hnT (.nil _) _ (gagree_canon s i) hr t hR hmt [c] h hk)

theorem sat_diaPush_congr {Γ : Ctx} {w : GW hF M₀} {env₁ env₂ : (gmodel hF hM₀).Env Γ w}
    (e : env₁ = env₂) {y : VarSymb} {Y : VarType} (hy : Γ.ref y = some (.VTypeDia Y))
    (b : GAcc hF M₀ w) (h₁ : b ∈ ((gmodel hF hM₀).posEval (env₁.ref y hy)).1)
    (h₂ : b ∈ ((gmodel hF hM₀).posEval (env₂.ref y hy)).1) (φ : WFF σ (Γ.diaIn y) 0) :
    (gmodel hF hM₀).sat (env₁.diaPush y hy ⟨b, h₁⟩) φ ↔
      (gmodel hF hM₀).sat (env₂.diaPush y hy ⟨b, h₂⟩) φ := by
  subst e
  exact Iff.rfl

/-- ⭐**Without T, along a path in a witness's extent, its view satisfies a formula exactly when
    the end satisfies its translation.** -/
theorem sat_diaPush_path (hnT : ModalSys.T = false) : ∀ (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) {X : VarType} (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hR : GR s t) (hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x hr)).1)
    (hm : InExt s t P h x) (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).diaPush x hr ⟨_, hmt⟩) χ ↔
      (gmodel hF hM₀).sat (gcanonEnv hM₀ t (pstg s t P h i)) (pTrXW hM₀ s t P h i x ⟨X, hr⟩ hm χ)
  | _, _, [], _, _, _, _, _, _, _, hm, _ => hm.elim
  | s, t, [c], h, i, x, _, hr, hR, hmt, hm, χ => by
      rw [gcanon_diaPush_edge hnT s t c h i hr hR hmt hm]
      exact (Model.sat_subst _ _ (coh_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i)) Ctx.NoSlots.slots
        Ctx.NoSlots.slots _ _ χ).symm
  | s, t, c :: c' :: P, h, i, x, X, hr, hR, hmt, hm, χ => by
      have hb := born_step h
      have e : GR s (stepW s c hb) := ⟨[c], pathOk_cons, rfl⟩
      have q : GR (stepW s c hb) t := ⟨c' :: P, pathOk_cons, h⟩
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hyk : (ctxOf (glat s i)).boxIn.ref (.step x .keep) = some (.VTypeDia X) :=
        Ctx.ref_keep_of' hF hr VarType.keepable_dia
      have hw := hc (.step x .keep) _ hyk []
      obtain ⟨Z, hr₁⟩ := wit_ref hM₀ hb i ⟨X, hr⟩
      have hwm : (⟨t, ⟨q⟩⟩ : GAcc hF M₀ (stepW s c hb)) ∈ ((gmodel hF hM₀).posEval
          ((gcanonEnv hM₀ (stepW s c hb) (glstg s (stepW s c hb) i)).ref _ hr₁)).1 :=
        (gcanon_mem_iff (stepW s c hb) _ hr₁ ⟨t, ⟨q⟩⟩).mpr (.inr ⟨hnT, inExt_pathOf q
          (show InExt (stepW s c hb) t (c' :: P) h (wit (stepW s c hb) x) from hm)⟩)
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
      exact sat_diaPush_path hnT (stepW s c hb) t (c' :: P) h _ _ hr₁ q hwm hm _

/-! ## Witnesses' views kept along a path (T) -/

variable (hM₀) in
/-- ⭐A witness's view's formula translated along a path with the witness kept (`pTrXK`'s steps,
    for formulas). -/
noncomputable def pTrXKW : (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) →
    (i : ℕ) → (x : VarSymb) → (∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) →
    WFF σ ((ctxOf (glat s i)).kView (some x)) 0 →
      WFF σ ((ctxOf (glat t (pstg s t P h i))).kView (some (kw s t P h x))) 0
  | _, _, [], h, i, _, _, χ => WFF.mono ((glat_le_of_eq h i).kView _) χ
  | _, t, [c], h, i, x, hx, χ =>
      WFF.subst (eIdx (fmapL hF M₀ t.1))
        ((eS σ (ctxOf (glat t (glstg _ t i))) (fmapL hF M₀ t.1)).dia (.step x .keep) (wit t x))
        (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (Ctx.exists_keep_dia hF hx)
          ((coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
            (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
        (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
          (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (Ctx.exists_keep_dia hF hx))
        Ctx.NoSlots.slots Ctx.NoSlots.slots
        (WFF.shift (Ctx.shifts_diaIn_keep hF _ x) Ctx.NoSlots.slots χ)
  | s, t, c :: c' :: P, h, i, x, hx, χ =>
      pTrXKW (stepW s c (born_step h)) t (c' :: P) h (glstg s (stepW s c (born_step h)) i)
        (wit (stepW s c (born_step h)) x) (wit_ref hM₀ (born_step h) i hx)
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

omit [ModalSys.NoSym] in
theorem size_pTrXKW : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    (pTrXKW hM₀ s t P h i x hx χ).size = χ.size
  | _, _, [], _, _, _, _, χ => WFF.size_mono _ χ
  | _, _, [_], _, _, _, _, χ => (WFF.size_subst _ _ _ _ _ _).trans (WFF.size_shift _ _ χ)
  | s, t, c :: c' :: P, h, _, _, _, χ =>
      (size_pTrXKW (stepW s c (born_step h)) t (c' :: P) h _ _ _ _).trans
        ((WFF.size_subst _ _ _ _ _ _).trans (WFF.size_shift _ _ χ))

omit [ModalSys.NoSym] in
theorem pTrXKW_neg : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    pTrXKW hM₀ s t P h i x hx χ.neg = (pTrXKW hM₀ s t P h i x hx χ).neg
  | _, _, [], _, _, _, _, _ => rfl
  | _, _, [_], _, _, _, _, _ => rfl
  | s, t, c :: c' :: P, h, _, _, _, _ =>
      pTrXKW_neg (stepW s c (born_step h)) t (c' :: P) h _ _ _ _

omit [ModalSys.NoSym] in
/-- ⭐**What holds throughout a possible object's extent holds of the kept witness at every
    descendant**: `four_dia`, then the plain transfer along each edge (`gltr`). -/
theorem boxx_mem_pathK : ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (i : ℕ)
    (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    WFF.boxx x hx χ ∈ (gw hM₀ s).M i →
    WFF.boxx (kw s t P h x) (kw_decl hM₀ s t P h i hx) (pTrXKW hM₀ s t P h i x hx χ) ∈
      (gw hM₀ t).M (pstg s t P h i)
  | s, t, [], h, i, x, hx, χ, hχ => by
      obtain rfl : t = s := gw_eq h
      have e := (BWorld.mem_mono_congr (w := gw hM₀ t) (glat_le_of_eq h i) (Ctx.Le.refl _)
        (φ := WFF.boxx x hx χ)).mpr (by rw [WFF.mono_refl]; exact hχ)
      exact e
  | s, t, [c], h, i, x, hx, χ, hχ => by
      have h4 : WFF.box (WFF.boxx (.step x .keep) (Ctx.exists_keep_dia hF hx)
          (WFF.shift (Ctx.shifts_diaIn_keep hF _ x) Ctx.NoSlots.slots χ)) ∈ (gw hM₀ s).M i :=
        BWorld.mem_of_provable (Δ := [WFF.boxx x hx χ])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hχ)
          ⟨Proof.four_dia hF hx (Proof.lookup List.mem_cons_self)⟩
      exact gltr hM₀ ⟨c, h⟩ i _ h4
  | s, t, c :: c' :: P, h, i, x, hx, χ, hχ => by
      have h4 : WFF.box (WFF.boxx (.step x .keep) (Ctx.exists_keep_dia hF hx)
          (WFF.shift (Ctx.shifts_diaIn_keep hF _ x) Ctx.NoSlots.slots χ)) ∈ (gw hM₀ s).M i :=
        BWorld.mem_of_provable (Δ := [WFF.boxx x hx χ])
          (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hχ)
          ⟨Proof.four_dia hF hx (Proof.lookup List.mem_cons_self)⟩
      exact boxx_mem_pathK (stepW s c (born_step h)) t (c' :: P) h _ _ _ _
        (gltr hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i _ h4)

omit [ModalSys.NoSym] in
/-- Membership in a canonical extent depends on the path only through its end. -/
theorem gmem_path {s t : GW hF M₀} (hR : GR s t) {P : List ℕ} (h : t.1 = nodeOf s.1 P)
    {x : VarSymb} :
    GMem hM₀ s t (pathOf hR) (pathOf_eq hR) x ↔ GMem hM₀ s t P h x := by
  obtain rfl := pathOf_of hR h
  exact Iff.rfl

/-- ⭐**Under T, along an arrow whose end realises the kept witness, the witness's view satisfies a
    formula exactly when the end's own arrow in the kept witness's view satisfies its kept
    translation**: the first edge kept (`Env.shiftAgree_diaKeep`), substituted (`substEnv_dia`),
    then the rest of the path. -/
theorem sat_diaPush_pathK (hT : ModalSys.T = true) : ∀ (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (i : ℕ) (x : VarSymb) {X : VarType}
    (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) (hR : GR s t)
    (hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x hr)).1) {Z : VarType}
    (hz : (ctxOf (glat t (pstg s t P h i))).ref (kw s t P h x) = some (.VTypeDia Z))
    (hmz : (⟨t, ⟨grefl hT t⟩⟩ : GAcc hF M₀ t) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ t (pstg s t P h i)).ref _ hz)).1)
    (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0),
    (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).diaPush x hr ⟨_, hmt⟩) χ ↔
      (gmodel hF hM₀).sat ((gcanonEnv hM₀ t (pstg s t P h i)).diaPush _ hz ⟨_, hmz⟩)
        (pTrXKW hM₀ s t P h i x ⟨X, hr⟩ χ)
  | s, t, [], h, i, x, X, hr, hR, hmt, Z, hz, hmz, χ => by
      obtain rfl : t = s := gw_eq h
      obtain rfl : Z = X := by
        have e := hz.symm.trans hr
        simp only [Option.some.injEq, VarType.VTypeDia.injEq] at e
        exact e
      exact (Model.sat_mono (Model.Env.diaPush_agree (h := glat_le_of_eq h i)
        (env := gcanonEnv hM₀ t i) (env' := gcanonEnv hM₀ t i) (fun _ _ _ => rfl) hr ⟨_, hmt⟩
        hmz) χ).symm
  | s, t, [c], h, i, x, X, hr, hR, hmt, Z, hz, hmz, χ => by
      have e : GR s t := ⟨[c], pathOk_cons, h⟩
      have q : GR t t := grefl hT t
      have hθ := ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)
      have hyk : (ctxOf (glat s i)).boxIn.ref (.step x .keep) = some (.VTypeDia X) :=
        Ctx.ref_keep_of' hF hr VarType.keepable_dia
      have hw := hc (.step x .keep) _ hyk []
      have hm₃ : (⟨t, ⟨q⟩⟩ : GAcc hF M₀ t) ∈ ((gmodel hF hM₀).posEval
          ((Model.substEnv _ hθ (Ctx.noProjLast_boxIn _)
            (gcanonEnv hM₀ t (glstg s t i))).ref (.step x .keep) hyk)).1 := by
        rw [Model.substEnv_ref, Model.entryVal_dia_ext _ _ hw hz]
        exact hmz
      have hsub := Model.substEnv_dia _ hθ (Ctx.noProjLast_boxIn _)
        (gcanonEnv hM₀ t (glstg s t i)) (Ctx.exists_keep_dia hF ⟨X, hr⟩) hyk hz hw ⟨_, hmz⟩ hm₃
      have hm₂ : (⟨t, ⟨q⟩⟩ : GAcc hF M₀ t) ∈ ((gmodel hF hM₀).posEval
          (((gcanonEnv hM₀ s i).boxPush ⟨_, ⟨e⟩⟩).ref (.step x .keep) hyk)).1 := by
        rw [gcanon_boxPush_edge s t c h i e]
        exact hm₃
      refine (Model.sat_shift Ctx.NoSlots.slots (Model.Env.shiftAgree_diaKeep hF
        (gcanonEnv hM₀ s i) hr ⟨_, ⟨e⟩⟩ ⟨t, ⟨q⟩⟩ hmt hyk hm₂) χ).symm.trans ?_
      refine (sat_diaPush_congr (gcanon_boxPush_edge s t c h i e) hyk _ hm₂ hm₃ _).trans ?_
      rw [← hsub]
      exact (Model.sat_subst _ _ (Subst.coh_dia hθ hc (Ctx.exists_keep_dia hF ⟨X, hr⟩))
        Ctx.NoSlots.slots Ctx.NoSlots.slots _ _ _).symm
  | s, t, c :: c' :: P, h, i, x, X, hr, hR, hmt, Z, hz, hmz, χ => by
      have hb := born_step h
      have e : GR s (stepW s c hb) := ⟨[c], pathOk_cons, rfl⟩
      have q : GR (stepW s c hb) t := ⟨c' :: P, pathOk_cons, h⟩
      have hθ := ok_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hc := coh_eS_kView (gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i)
      have hyk : (ctxOf (glat s i)).boxIn.ref (.step x .keep) = some (.VTypeDia X) :=
        Ctx.ref_keep_of' hF hr VarType.keepable_dia
      have hw := hc (.step x .keep) _ hyk []
      obtain ⟨Z₁, hr₁⟩ := wit_ref hM₀ hb i ⟨X, hr⟩
      have hwm : (⟨t, ⟨q⟩⟩ : GAcc hF M₀ (stepW s c hb)) ∈ ((gmodel hF hM₀).posEval
          ((gcanonEnv hM₀ (stepW s c hb) (glstg s (stepW s c hb) i)).ref _ hr₁)).1 :=
        (gcanon_mem_iff (stepW s c hb) _ hr₁ ⟨t, ⟨q⟩⟩).mpr ((gmem_path q h).mpr
          ((gmem_path hR h).mp ((gcanon_mem_iff s i hr ⟨t, ⟨hR⟩⟩).mp hmt)))
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
      exact sat_diaPush_pathK hT (stepW s c hb) t (c' :: P) h _ _ hr₁ q hwm hz hmz _

/-! ## Along an edge made for a witness (T) -/

omit [ModalSys.NoSym] in
/-- ⭐**Along an edge made for a witness, the child's reading of a formula of the witness's view is
    the realisation, at the child's content, of the formula translated with the witness kept**:
    the formula is the realisation of its kept shift at the content (`realiseAtA_shift_keep`, at the
    parent's `◇_x` view), and the edge renames the kept witness (`WFF.subst_realiseAtA`). -/
theorem gchild_real (hT : ModalSys.T = true) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = nodeOf s.1 [c]) {x : VarSymb} (hk : lkd t = some x) (i : ℕ) {X : VarType}
    (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hfk : fmapL hF M₀ t.1 (.step x .keep) = .inl (wit t x)) {b : VarSymb}
    (hfd : fmapL hF M₀ t.1 (.step x .dia) = .inl b)
    (hwd : (ctxOf (glat t (glstg s t i))).ref (wit t x) = some (.VTypeDia X))
    (hbd : (ctxOf (glat t (glstg s t i))).ref b = some X)
    (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0) :
    WFF.realiseAtA hT (wit t x) hwd (Term.eta b X hbd) (pTrXKW hM₀ s t [c] hc i x ⟨X, hx⟩ χ) =
      pTrXW hM₀ s t [c] hc i x ⟨X, hx⟩ hk χ := by
  have hk'' : ((ctxOf (glat s i)).diaIn x).ref (.step x .keep) = some (.VTypeDia X) :=
    (Ctx.le_boxIn_diaIn _ x).ref (Ctx.ref_keep_of' hF hx VarType.keepable_dia)
  have hdia : ((ctxOf (glat s i)).diaIn x).ref (.step x .dia) = some X := Ctx.ref_diaIn_of hx
  have e₀ := WFF.realiseAtA_shift_keep hT hF hx (Ctx.Le.refl _) hk'' hdia χ
  rw [WFF.mono_refl] at e₀
  have hθ := ok_eS_kView (l := glat s i) (k := some x) (hk ▸ gentOk hM₀ ⟨c, hc⟩ i)
  have hcθ := coh_eS_kView (l := glat s i) (k := some x) (hk ▸ gentOk hM₀ ⟨c, hc⟩ i)
  change _ = WFF.subst _ _ hθ hcθ Ctx.NoSlots.slots Ctx.NoSlots.slots χ
  have hren : (eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).at (.step x .keep) =
      .ren (eIdx (fmapL hF M₀ t.1) (.step x .keep)) := by
    rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfk]
    rfl
  have hη := Term.subst_eta_renAt _ hθ hcθ X (.step x .dia) b hdia hbd (by
    rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfd]
    rfl)
  conv_rhs => rw [← e₀]
  rw [WFF.subst_realiseAtA hT _ hθ hcθ hk'' hwd hren]
  have hbody : WFF.subst (eIdx (fmapL hF M₀ t.1))
      ((eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).dia (.step x .keep)
        (eIdx (fmapL hF M₀ t.1) (.step x .keep)))
      (Subst.ok_dia hθ ⟨_, hk''⟩ (by rw [hren]; rfl)) (Subst.coh_dia hθ hcθ ⟨_, hk''⟩)
      Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.mono (((Ctx.le_boxIn_diaIn _ x).trans (Ctx.Le.refl _)).diaIn (.step x .keep))
        (WFF.shift (Ctx.shifts_diaIn_keep hF _ x) Ctx.NoSlots.slots χ)) =
      pTrXKW hM₀ s t [c] hc i x ⟨X, hx⟩ χ := by
    rw [WFF.subst_mono]
    rfl
  rw [hbody]
  unfold WFF.realiseAtA
  exact WFF.hereRead_congr hT hη.symm _

omit [ModalSys.NoSym] in
/-- ⭐**Along an edge made for a witness, the kept witness is realised by the child's content**:
    `here_keep` at the η-expansion of the content, transferred along the edge (`gltrX`). -/
theorem gchild_here (hT : ModalSys.T = true) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = nodeOf s.1 [c]) {x : VarSymb} (hk : lkd t = some x) (i : ℕ) {X : VarType}
    (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hfk : fmapL hF M₀ t.1 (.step x .keep) = .inl (wit t x)) {b : VarSymb}
    (hfd : fmapL hF M₀ t.1 (.step x .dia) = .inl b)
    (hwd : (ctxOf (glat t (glstg s t i))).ref (wit t x) = some (.VTypeDia X))
    (hbd : (ctxOf (glat t (glstg s t i))).ref b = some X) :
    WFF.hereAt hT (wit t x) hwd (Term.eta b X hbd) ∈ (gw hM₀ t).M (glstg s t i) := by
  have hmem : WFF.hereKeep hT hF x ⟨X, hx⟩ (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)) ∈
      (gw hM₀ s).M i :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h)
      ⟨Proof.here_keep hT hF x ⟨X, hx⟩ _⟩
  have h₁ := gltrX hM₀ ⟨c, hc⟩ hk i hx _ hmem
  have hθ := ok_eS_kView (l := glat s i) (k := some x) (hk ▸ gentOk hM₀ ⟨c, hc⟩ i)
  have hcθ := coh_eS_kView (l := glat s i) (k := some x) (hk ▸ gentOk hM₀ ⟨c, hc⟩ i)
  have hθb := ok_eS_kView (gentOk_box hM₀ ⟨c, hc⟩ i)
  have hcθb := coh_eS_kView (gentOk_box hM₀ ⟨c, hc⟩ i)
  have hren : (eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).at (.step x .keep) =
      .ren (eIdx (fmapL hF M₀ t.1) (.step x .keep)) := by
    rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfk]
    rfl
  have hobj := Term.subst_eta_renAt _ hθ hcθ X (.step x .dia) b (Ctx.ref_diaIn_of hx) hbd (by
    rw [Subst.at_nonproj _ rfl, eS_item _ rfl, hfd]
    rfl)
  have hs₀ : (⟨_, Term.shift (Ctx.shifts_diaIn_keep hF _ x)
        (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx))⟩ :
        Σ b, Term σ ((ctxOf (glat s i)).boxIn.diaIn (.step x .keep)) X b) =
      ⟨_, Term.eta (.step (.step x .keep) .dia) X
        (Ctx.ref_diaIn_of (Ctx.ref_keep_of' hF hx VarType.keepable_dia))⟩ :=
    (Term.shift_eta _ _ _ _).trans
      (Term.eta_congr (VarSymb.shift_level_zero (s := .dia) rfl) _ _ _)
  have hdk : ((eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).dia (.step x .keep)
      (eIdx (fmapL hF M₀ t.1) (.step x .keep))).at (.step (.step x .keep) .dia) =
      .ren (.step (wit t x) .dia) := by
    rw [Subst.at_nonproj _ (rfl : (VarSymb.step (VarSymb.step x .keep) .dia).lastProj = false)]
    change (if VarSymb.step x .keep = VarSymb.step x .keep then
      ((eS σ _ (fmapL hF M₀ t.1)).at (.step x .keep)).diaBody _ else .hide) = _
    rw [if_pos rfl, hren]
    rfl
  have hok := Subst.ok_dia hθb (Ctx.exists_keep_dia hF ⟨X, hx⟩) (by rw [hren])
  have hcoh := Subst.coh_dia hθb hcθb (Ctx.exists_keep_dia hF ⟨X, hx⟩)
  have hs₁ := Term.subst_eta_renAt _ hok hcoh X (.step (.step x .keep) .dia) (.step (wit t x) .dia)
    (Ctx.ref_diaIn_of (Ctx.ref_keep_of' hF hx VarType.keepable_dia)) (Ctx.ref_diaIn_of hwd) hdk
  have hsubj : (⟨_, Term.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1)) hθ hcθ
        (Term.mono (Ctx.le_boxIn_diaIn _ x) (Term.diatm (.step x .keep)
          (Ctx.exists_keep_dia hF ⟨X, hx⟩) (Term.shift (Ctx.shifts_diaIn_keep hF _ x)
            (Term.eta (.step x .dia) X (Ctx.ref_diaIn_of hx)))))⟩ :
        Σ b, Term σ (ctxOf (glat t (glstg s t i))) (.VTypeDia X) b) =
      ⟨_, Term.eta (wit t x) (.VTypeDia X) hwd⟩ := by
    rw [Term.subst_mono]
    exact sig_diatm ((sig_subst _ hok hcoh hs₀).trans hs₁)
  convert h₁ using 1
  exact (WFF.here_congr hT hsubj hobj).symm

/-! ## The truth lemma -/

/-- The truth lemma for atoms. -/
theorem relSat_gcanon : ∀ {Γ : Ctx} {n : ℕ} (ρ : Rel σ Γ n) {s : GW hF M₀} {i : ℕ}
    {e : Γ.Le (ctxOf (glat s i))} {env : (gmodel hF hM₀).Env Γ s},
    Model.Env.Agree e env (gcanonEnv hM₀ s i) → Γ.NoProjLast →
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
        (interp_gcanon t hag hΓ).trans (grden_var_mono e t)
      rw [relSat_gcanon ρ hag hΓ (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
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
  (interp_gcanon _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)).trans
    ((gtoDom_congr ((grden_mono _ t' s _ _).trans ((grden_congr t' s _ i' _ _).trans ht')) _
      _).trans (gtoDom_fromDom hM₀ A s o))

/-- The truth lemma below a size, at every world and stage: what the `◇` case receives. -/
abbrev GTruthBelow (n : ℕ) : Prop :=
  ∀ (t : GW hF M₀) (j : ℕ) (φ : WFF σ (ctxOf (glat t j)) 0), φ.size < n →
    ((gmodel hF hM₀).sat (gcanonEnv hM₀ t j) φ ↔ φ ∈ (gw hM₀ t).M j)

/-- Under T, a realised witness's possible object has, along the world's own arrow, the datum's
    content, read at any stage above it. -/
theorem gcanon_cont_real (hT : ModalSys.T = true) (t : GW hF M₀) {y : VarSymb}
    (hrl : (gw hM₀ t).Realised y) {K : ℕ} (hK : hrl.data.i₀ ≤ K)
    (hdecl : (ctxOf (glat t K)).ref y = some (.VTypeDia hrl.data.A))
    (hm : (⟨t, ⟨grefl hT t⟩⟩ : GAcc hF M₀ t) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ t K).ref y hdecl)).1) :
    ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ t K).ref y hdecl)).2 ⟨_, hm⟩ =
      Model.interp (gcanonEnv hM₀ t K) (Term.mono (gle hM₀ t hK) hrl.data.t₀) := by
  have hpq := gagree_canon (hM₀ := hM₀) t K y _ hdecl
  rw [Model.posEval_snd_congr hpq ⟨_, hm⟩ (hpq ▸ hm),
    Model.interp_mono (gcanonEnv_le t hK) hrl.data.t₀,
    interp_gcanon hrl.data.t₀ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
  exact gtoDom_congr (grden_eta_real hrl hdecl _) _ _

/-- ⭐**Under T, what holds in a witness's view along an arrow whose end realises the kept witness
    is not `□_x`-impossible** (the tree's `dia_truth_tFour`): along the path the view is the end's
    own arrow in the kept witness's view (`sat_diaPush_pathK`), whose formula holds of the datum's
    content (`Model.sat_realiseAtA`), while `□_x` of its negation goes along the path
    (`boxx_mem_pathK`) and is realised there (`Proof.here_elimAtA`). -/
theorem gdia_real_not_boxx (hT : ModalSys.T = true) {n : ℕ}
    (IH : GTruthBelow (hF := hF) (hM₀ := hM₀) n) (s t : GW hF M₀) (i : ℕ) (x : VarSymb)
    {X : VarType} (hr : (ctxOf (glat s i)).ref x = some (.VTypeDia X)) (hR : GR s t)
    (hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x hr)).1)
    (hrl : (gw hM₀ t).Realised (kw s t (pathOf hR) (pathOf_eq hR) x))
    (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0) (hχs : χ.size < n)
    (hsat : (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).diaPush x hr ⟨_, hmt⟩) χ)
    (hbx : WFF.boxx x ⟨X, hr⟩ χ.neg ∈ (gw hM₀ s).M i) : False := by
  obtain ⟨Z, hz⟩ := kw_decl hM₀ s t (pathOf hR) (pathOf_eq hR) i ⟨X, hr⟩
  have hZA : Z = hrl.data.A := by
    have h1 := (hrl.data.hdeclOf _ ⟨Z, hz⟩).symm.trans hz
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hZA
  have hmz : (⟨t, ⟨grefl hT t⟩⟩ : GAcc hF M₀ t) ∈ ((gmodel hF hM₀).posEval
      ((gcanonEnv hM₀ t (pstg s t (pathOf hR) (pathOf_eq hR) i)).ref _ hz)).1 :=
    (gcanon_mem_iff t _ hz _).mpr ((gmem_path (grefl hT t) (P := []) rfl).mpr (Or.inl hrl))
  have hs₁ := (sat_diaPush_pathK hT s t (pathOf hR) (pathOf_eq hR) i x hr hR hmt hz hmz χ).mp hsat
  have hj : pstg s t (pathOf hR) (pathOf_eq hR) i ≤
      max (pstg s t (pathOf hR) (pathOf_eq hR) i) hrl.data.i₀ := le_max_left _ _
  have hK : hrl.data.i₀ ≤ max (pstg s t (pathOf hR) (pathOf_eq hR) i) hrl.data.i₀ :=
    le_max_right _ _
  have hdecl : (ctxOf (glat t (max (pstg s t (pathOf hR) (pathOf_eq hR) i) hrl.data.i₀))).ref
      (kw s t (pathOf hR) (pathOf_eq hR) x) = some (.VTypeDia hrl.data.A) :=
    (gle hM₀ t hj).ref hz
  have hm' : (⟨t, ⟨grefl hT t⟩⟩ : GAcc hF M₀ t) ∈ ((gmodel hF hM₀).posEval
      ((gcanonEnv hM₀ t _).ref _ hdecl)).1 :=
    (gcanon_mem_iff t _ hdecl _).mpr ((gmem_path (grefl hT t) (P := []) rfl).mpr (Or.inl hrl))
  have hsatR := (Model.sat_realiseAtA hT (gcanonEnv hM₀ t _) (Ctx.Presented.noProjLast _) hdecl
    (Term.mono (gle hM₀ t hK) hrl.data.t₀) hm' (gcanon_cont_real hT t hrl hK hdecl hm')
    (WFF.mono ((gle hM₀ t hj).diaIn _) (pTrXKW hM₀ s t (pathOf hR) (pathOf_eq hR) i x ⟨X, hr⟩
      χ))).mpr
    ((Model.sat_mono (Model.Env.diaPush_agree (gcanonEnv_le t hj) hz ⟨_, hmz⟩ hm') _).mpr hs₁)
  have hrm := (IH t _ _ (by rw [WFF.size_realiseAtA, WFF.size_mono, size_pTrXKW]; exact hχs)).mp
    hsatR
  have hbK := boxx_mem_pathK (hM₀ := hM₀) s t (pathOf hR) (pathOf_eq hR) i x ⟨X, hr⟩ χ.neg hbx
  rw [pTrXKW_neg] at hbK
  have hn : WFF.realiseAtA hT _ hdecl (Term.mono (gle hM₀ t hK) hrl.data.t₀)
      (WFF.mono ((gle hM₀ t hj).diaIn _)
        (pTrXKW hM₀ s t (pathOf hR) (pathOf_eq hR) i x ⟨X, hr⟩ χ)).neg ∈ (gw hM₀ t).M _ := by
    refine BWorld.mem_of_provable (Δ := [WFF.hereAt hT _ hdecl
        (Term.mono (gle hM₀ t hK) hrl.data.t₀), WFF.mono (gle hM₀ t hj) (WFF.boxx _ ⟨_, hz⟩
          (pTrXKW hM₀ s t (pathOf hR) (pathOf_eq hR) i x ⟨X, hr⟩ χ).neg)]) ?_
      ⟨Proof.here_elimAtA hT _ hdecl _ _ (Proof.lookup List.mem_cons_self)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ'
    · exact BWorld.mem_T.mp (hrl.data.hhereAt (gw hM₀ t).mcsT _ hK hdecl)
    · rw [List.mem_singleton.mp hφ']
      exact (BWorld.mem_lift hj).mp hbK
  rw [WFF.realiseAtA_neg] at hn
  exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hn hrm

/-- ⭐**Under T, a possible formula of the theory holds along the edge made for its witness**: the
    child realises the kept witness (`grealised_wit`), its reading of the formula is the
    realisation at its content of the kept translation (`gchild_real`), which `here_subst` moves to
    the datum's content (`gchild_here`), where it holds (`Model.sat_realiseAtA`). -/
theorem gdia_sat_child (hT : ModalSys.T = true) {n : ℕ}
    (IH : GTruthBelow (hF := hF) (hM₀ := hM₀) n) (s : GW hF M₀) (i : ℕ) (x : VarSymb)
    {X : VarType} (h : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (χ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0) (hχs : χ.size < n)
    (hmem : WFF.dia x ⟨X, h⟩ χ ∈ (gw hM₀ s).M i) :
    ∃ a : ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x h)).1,
      (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).diaPush x h a) χ := by
  obtain ⟨t, ⟨c, hc⟩, hk, ⟨y, hfy⟩, ⟨b, hfd⟩, hm⟩ := glexX hM₀ s i x X h χ hmem
  have hwy : wit t x = y := wit_of_inl (reach_ppath h).1 hfy
  have hfk : fmapL hF M₀ t.1 (.step x .keep) = .inl (wit t x) := by rw [hwy]; exact hfy
  have hR : GR s t := ⟨[c], pathOk_cons, hc⟩
  have hrl : (gw hM₀ t).Realised (wit t x) := grealised_wit hM₀ hT ⟨c, hc⟩ hk i h
  have hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x h)).1 :=
    (gcanon_mem_iff s i h _).mpr ((gmem_path hR (P := [c]) hc).mpr (Or.inl hrl))
  refine ⟨⟨_, hmt⟩, ?_⟩
  have hwd : (ctxOf (glat t (glstg s t i))).ref (wit t x) = some (.VTypeDia X) := by
    have := ok_eS_kView (gentOk_box hM₀ ⟨c, hc⟩ i) (.step x .keep) (.VTypeDia X) rfl
      ((Ctx.ref_nonproj _ rfl).symm.trans (Ctx.ref_keep_of' hF h VarType.keepable_dia))
    rw [eS_item _ rfl, hfk] at this
    exact this
  have hbd : (ctxOf (glat t (glstg s t i))).ref b = some X := by
    have := ok_eS_kView (l := glat s i) (k := some x) (hk ▸ gentOk hM₀ ⟨c, hc⟩ i)
      (.step x .dia) X rfl ((Ctx.ref_nonproj _ rfl).symm.trans (Ctx.ref_diaIn_of h))
    rw [eS_item _ rfl, hfd] at this
    exact this
  have hmz : (⟨t, ⟨grefl hT t⟩⟩ : GAcc hF M₀ t) ∈ ((gmodel hF hM₀).posEval
      ((gcanonEnv hM₀ t (glstg s t i)).ref (wit t x) hwd)).1 :=
    (gcanon_mem_iff t _ hwd _).mpr ((gmem_path (grefl hT t) (P := []) rfl).mpr (Or.inl hrl))
  refine (sat_diaPush_pathK hT s t [c] hc i x h hR hmt hwd hmz χ).mpr ?_
  have hmK : WFF.realiseAtA hT (wit t x) hwd (Term.eta b X hbd)
      (pTrXKW hM₀ s t [c] hc i x ⟨X, h⟩ χ) ∈ (gw hM₀ t).M (glstg s t i) := by
    rw [gchild_real (hM₀ := hM₀) hT hc hk i h hfk hfd hwd hbd χ]
    exact hm
  have hXA : X = hrl.data.A := by
    have h1 := (hrl.data.hdeclOf _ ⟨X, hwd⟩).symm.trans hwd
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hXA
  have hj : glstg s t i ≤ max (glstg s t i) hrl.data.i₀ := le_max_left _ _
  have hK : hrl.data.i₀ ≤ max (glstg s t i) hrl.data.i₀ := le_max_right _ _
  have hdecl : (ctxOf (glat t (max (glstg s t i) hrl.data.i₀))).ref (wit t x) =
      some (.VTypeDia hrl.data.A) := (gle hM₀ t hj).ref hwd
  have hbK : (ctxOf (glat t (max (glstg s t i) hrl.data.i₀))).ref b = some hrl.data.A :=
    (gle hM₀ t hj).ref hbd
  -- the child's content and the datum's both realise the kept witness, at one stage
  have hH₁ : WFF.hereAt hT (wit t x) hdecl (Term.eta b _ hbK) ∈ (gw hM₀ t).M _ := by
    have := (BWorld.mem_lift hj).mp (gchild_here (hM₀ := hM₀) hT hc hk i h hfk hfd hwd hbd)
    change WFF.here hT (Term.mono _ (Term.eta _ _ _)) (Term.mono _ (Term.eta _ _ _)) ∈ _ at this
    rwa [Term.mono_eta, Term.mono_eta] at this
  have hH₂ := BWorld.mem_T.mp (hrl.data.hhereAt (gw hM₀ t).mcsT _ hK hdecl)
  have hR₁ : WFF.realiseAtA hT (wit t x) hdecl (Term.eta b _ hbK)
      (WFF.mono ((gle hM₀ t hj).diaIn _) (pTrXKW hM₀ s t [c] hc i x ⟨_, h⟩ χ)) ∈
        (gw hM₀ t).M _ := by
    have := (BWorld.mem_lift hj).mp hmK
    rwa [WFF.mono_realiseAtA hT (gle hM₀ t hj) hwd hdecl, Term.mono_eta] at this
  have hR₂ : WFF.realiseAtA hT (wit t x) hdecl (Term.mono (gle hM₀ t hK) hrl.data.t₀)
      (WFF.mono ((gle hM₀ t hj).diaIn _) (pTrXKW hM₀ s t [c] hc i x ⟨_, h⟩ χ)) ∈
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
  have hm' : (⟨t, ⟨grefl hT t⟩⟩ : GAcc hF M₀ t) ∈ ((gmodel hF hM₀).posEval
      ((gcanonEnv hM₀ t _).ref _ hdecl)).1 :=
    (gcanon_mem_iff t _ hdecl _).mpr ((gmem_path (grefl hT t) (P := []) rfl).mpr (Or.inl hrl))
  have hsatR := (IH t _ _ (by rw [WFF.size_realiseAtA, WFF.size_mono, size_pTrXKW]; exact hχs)).mpr
    hR₂
  have hs₁ := (Model.sat_realiseAtA hT (gcanonEnv hM₀ t _) (Ctx.Presented.noProjLast _) hdecl
    (Term.mono (gle hM₀ t hK) hrl.data.t₀) hm' (gcanon_cont_real hT t hrl hK hdecl hm') _).mp
    hsatR
  exact (Model.sat_mono (Model.Env.diaPush_agree (gcanonEnv_le t hj) hwd ⟨_, hmz⟩ hm') _).mp hs₁

/-! ## What `Here` says -/

variable (hM₀) in
/-- The truth lemma at the equations of one type: what the `here` case receives from the
    induction (B's `EqTruth`). -/
abbrev GEqTruth (s : GW hF M₀) (A : VarType) : Prop :=
  ∀ (K : ℕ) {b : Ann A} (u u' : Term σ (ctxOf (glat s K)) A b),
    (gmodel hF hM₀).sat (gcanonEnv hM₀ s K) (eqRec A u u' : WFF σ (ctxOf (glat s K)) 0) ↔
      eqRec A u u' ∈ (gw hM₀ s).M K

/-- ⭐**Equal denotations carry `Here` facts** (B's `here_transfer`): tags determine annotations
    (`ann_eq_of_grden`), so the two contents can be equated (`eqRec`, by the truth lemma at a
    smaller formula), and `Proof.here_eq` moves the atom. -/
theorem ghere_transfer (hT : ModalSys.T = true)
    (hS : ModalSys.FourStrongW = true → ModalSys.FourStrong = true) {s : GW hF M₀} {A : VarType}
    (IH : GEqTruth hM₀ s A) {K : ℕ} {c : Ann (.VTypeDia A)}
    (S : Term σ (ctxOf (glat s K)) (.VTypeDia A) c) {b b' : Ann A}
    (r : Term σ (ctxOf (glat s K)) A b) (r' : Term σ (ctxOf (glat s K)) A b')
    (he : grden hM₀ s K (Ctx.Le.refl _) r = grden hM₀ s K (Ctx.Le.refl _) r')
    (hmem : WFF.here hT S r ∈ (gw hM₀ s).M K) :
    WFF.here hT S r' ∈ (gw hM₀ s).M K := by
  obtain rfl := ann_eq_of_grden hT hS hM₀ r r' he
  have heq : eqRec A r r' ∈ (gw hM₀ s).M K := by
    refine (IH K r r').mp ((Model.sat_eqRec _ A r r').mpr ?_)
    rw [interp_gcanon r (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
      interp_gcanon r' (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
    exact gtoDom_congr he _ _
  refine BWorld.mem_of_provable (Δ := [WFF.here hT S r, eqRec A r r']) (fun ψ hψ => ?_)
    ⟨Proof.here_eq hT S r r' (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hmem
  · rw [List.mem_singleton.mp hψ]
    exact heq

/-- Under T, a realised witness's view along the world's own arrow reads a body as the body
    realised by the datum's content (B's `interp_dia_self`). -/
theorem ginterp_dia_self (hT : ModalSys.T = true) {s : GW hF M₀} {i : ℕ} {x : VarSymb}
    (hr : (gw hM₀ s).Realised x) {X : VarType} (h : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (hm : (gmodel hF hM₀).frame.reflAcc hT s ∈
      ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x h)).1)
    {A : VarType} {β : Ann A} (bd : Term σ ((ctxOf (glat s i)).diaIn x) A β) :
    Model.interp ((gcanonEnv hM₀ s i).diaPush x h ⟨_, hm⟩) bd =
      gtoDom hM₀ A s (grden hM₀ s (max i hr.data.i₀) (Ctx.Le.refl _)
        (grealT hr (Ctx.Le.refl _) ⟨X, h⟩ bd).2) (gdefinable_rden _ _) := by
  have hXA : X = hr.data.A := by
    have h1 := (hr.data.hdeclOf _ ⟨X, h⟩).symm.trans h
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  subst hXA
  have hj : i ≤ max i hr.data.i₀ := le_max_left _ _
  have hK : hr.data.i₀ ≤ max i hr.data.i₀ := le_max_right _ _
  have hdecl : (ctxOf (glat s (max i hr.data.i₀))).ref x = some (.VTypeDia hr.data.A) :=
    (gle hM₀ s hj).ref h
  have hm' : (⟨s, ⟨grefl hT s⟩⟩ : GAcc hF M₀ s) ∈ ((gmodel hF hM₀).posEval
      ((gcanonEnv hM₀ s _).ref x hdecl)).1 :=
    (gcanon_mem_iff s _ hdecl _).mpr ((gmem_path (grefl hT s) (P := []) rfl).mpr (Or.inl hr))
  calc Model.interp ((gcanonEnv hM₀ s i).diaPush x h ⟨_, hm⟩) bd
      = Model.interp ((gcanonEnv hM₀ s _).diaPush x hdecl ⟨_, hm'⟩)
          (Term.mono ((gle hM₀ s hj).diaIn x) bd) :=
        (Model.interp_mono (Model.Env.diaPush_agree (gcanonEnv_le s hj) h ⟨_, hm⟩ hm') bd).symm
    _ = Model.interp (gcanonEnv hM₀ s _) (Term.realiseAtA hT x hdecl
          (Term.mono (gle hM₀ s hK) hr.data.t₀) (Term.mono ((gle hM₀ s hj).diaIn x) bd)) :=
        (Model.interp_realiseAtA hT (gcanonEnv hM₀ s _) (Ctx.Presented.noProjLast _) hdecl
          (Term.mono (gle hM₀ s hK) hr.data.t₀) hm' (gcanon_cont_real hT s hr hK hdecl hm')
          _).symm
    _ = _ := interp_gcanon _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)

/-- ⭐⭐**The truth lemma's `here` case** (B's `here_truth`), with the `□`-lift on whenever the
    `◇`-lift is.  Satisfaction says the witness is realised and its content along the world's own
    arrow is indistinguishable from `t`'s value; membership says the theory co-names them.
    *Membership ⇒ truth*: the atom makes the witness realised and relates its realisation and `t`
    (`grel_here`).  *Truth ⇒ membership*: related representatives carry the atom from the realised
    body to `t`, one equal denotation at a time (`ghere_transfer`) and across the relation
    once. -/
theorem ghere_truth (hT : ModalSys.T = true)
    (hS : ModalSys.FourStrongW = true → ModalSys.FourStrong = true) {s : GW hF M₀} {i : ℕ}
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType}
    {β : Ann A} (bd : Term σ ((ctxOf (glat s i)).diaIn x) A β) {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a) (IH : GEqTruth hM₀ s A) :
    (gmodel hF hM₀).sat (gcanonEnv hM₀ s i) (WFF.here hT (Term.diatm x hx bd) t : WFF σ _ 0) ↔
      WFF.here hT (Term.diatm x hx bd) t ∈ (gw hM₀ s).M i := by
  obtain ⟨X, h⟩ := id hx
  rw [Model.sat_here_diatm hT (gcanonEnv hM₀ s i) hx h t bd]
  have hD : Model.interp (gcanonEnv hM₀ s i) t =
      gtoDom hM₀ A s (grden hM₀ s i (Ctx.Le.refl _) t) (gdefinable_rden _ _) :=
    interp_gcanon t (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)
  constructor
  · rintro ⟨hm, hind⟩
    obtain ⟨u, u', hu, hu', hrel⟩ := hind.1 hT
    have hr : (gw hM₀ s).Realised x := by
      have := (gmem_path (grefl hT s) (P := []) rfl).mp ((gcanon_mem_iff s i h _).mp hm)
      refine this.resolve_right fun h' => ?_
      rw [hT] at h'
      cases h'.1
    rw [ginterp_dia_self hT hr h hm bd, gfromDom_toDom] at hu
    rw [hD, gfromDom_toDom] at hu'
    -- one stage for everything
    have hkK : max i hr.data.i₀ ≤ max (max i hr.data.i₀) (max u.i u'.i) := le_max_left _ _
    have hiK : i ≤ max (max i hr.data.i₀) (max u.i u'.i) := (le_max_left _ _).trans hkK
    have huK : u.i ≤ max (max i hr.data.i₀) (max u.i u'.i) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hu'K : u'.i ≤ max (max i hr.data.i₀) (max u.i u'.i) :=
      (le_max_right _ _).trans (le_max_right _ _)
    -- the realised body is co-named with the subject, at the common stage
    have h₁ : WFF.here hT (Term.mono (gle hM₀ s hiK) (Term.diatm x hx bd))
        (Term.mono (gle hM₀ s hkK) (grealT hr (Ctx.Le.refl _) hx bd).2) ∈
          (gw hM₀ s).M (max (max i hr.data.i₀) (max u.i u'.i)) := by
      have := (BWorld.mem_lift hkK).mp (gmem_here_real hr h bd)
      change WFF.here hT (Term.mono _ (Term.mono _ (Term.diatm x hx bd))) _ ∈ (gw hM₀ s).M _
        at this
      rwa [Term.mono_mono] at this
    -- carried to the representative `u`, then across the relation to `u'`
    have h₂ := ghere_transfer hT hS IH _ _ (u.lift _ huK)
      ((grden_lift hkK _).trans (hu.symm.trans (grden_lift huK u.t).symm)) h₁
    have h₃ : WFF.here hT (Term.mono (gle hM₀ s hiK) (Term.diatm x hx bd)) (u'.lift _ hu'K) ∈
        (gw hM₀ s).M (max (max i hr.data.i₀) (max u.i u'.i)) := by
      have key := hrel _ huK hu'K (WFF.here hT
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots
          (Γ := ctxOf (glat s (max (max i hr.data.i₀) (max u.i u'.i))))).root A)
          (Term.mono (gle hM₀ s hiK) (Term.diatm x hx bd)))
        (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A)))
      rw [WFF.instantiate_here_slot, WFF.instantiate_here_slot] at key
      exact key.mp h₂
    -- and to `t`
    have h₄ := ghere_transfer hT hS IH _ _ (Term.mono (gle hM₀ s hiK) t)
      ((grden_lift hu'K u'.t).trans (hu'.trans (grden_lift hiK t).symm)) h₃
    exact (BWorld.mem_lift hiK).mpr h₄
  · intro hmem
    have hr : (gw hM₀ s).Realised x := (gw hM₀ s).datum_of_here hT h bd t hmem
    have hm : (gmodel hF hM₀).frame.reflAcc hT s ∈
        ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x h)).1 :=
      (gcanon_mem_iff s i h _).mpr ((gmem_path (grefl hT s) (P := []) rfl).mpr (Or.inl hr))
    refine ⟨hm, fun _ => ⟨_, ⟨i, a, t⟩, ?_, ?_, grel_here hT hx bd t hr hmem⟩, fun hnT => ?_⟩
    · rw [ginterp_dia_self hT hr h hm bd, gfromDom_toDom]
    · rw [hD, gfromDom_toDom]
    · rw [hT] at hnT
      cases hnT

theorem gtruth_lt [ModalSys.FourCoh] :
    ∀ (n : ℕ) (s : GW hF M₀) (i : ℕ) (φ : WFF σ (ctxOf (glat s i)) 0), φ.size < n →
    ((gmodel hF hM₀).sat (gcanonEnv hM₀ s i) φ ↔ φ ∈ (gw hM₀ s).M i)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, i, φ, hφ => by
      cases φ with
      | atom ρ =>
          change Model.relSat (gcanonEnv hM₀ s i) ρ Fin.elim0 ↔ _
          rw [relSat_gcanon ρ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)
            Fin.elim0 Fin.elim0 (fun k => k.elim0)]
          change WFF.mono (Ctx.Le.refl _) (.atom ρ) ∈ (gw hM₀ s).M i ↔ _
          rw [WFF.mono_refl]
      | eq t u =>
          change Model.interp (gcanonEnv hM₀ s i) t = Model.interp (gcanonEnv hM₀ s i) u ↔ _
          rw [interp_gcanon t (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _),
            interp_gcanon u (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
          change grden hM₀ s i (Ctx.Le.refl _) t = grden hM₀ s i (Ctx.Le.refl _) u ↔ _
          rw [grden_var_cls, grden_var_cls, BWorld.cls_eq_iff (le_refl i) (le_refl i)]
          change WFF.eq (Term.mono ((gw hM₀ s).le (le_refl i)) t)
            (Term.mono ((gw hM₀ s).le (le_refl i)) u) ∈ (gw hM₀ s).M i ↔ _
          rw [Term.mono_refl, Term.mono_refl]
      | top => exact ⟨fun _ => ((gw hM₀ s).mcs i).top_mem, fun _ => trivial⟩
      | bot => exact ⟨False.elim, fun h => ((gw hM₀ s).mcs i).bot_not_mem h⟩
      | here hT S t =>
          cases S with
          | diatm x hx bd =>
              exact ghere_truth hT (ModalSys.FourCoh.strong hT) hx bd t
                (fun K _ u u' => gtruth_lt n s K _ (by
                  rw [WFF.size_eqRec]; simp only [WFF.size] at hφ; omega))
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
            have hR : GR s t := ⟨[c], pathOk_cons, hc⟩
            have h1 := (sat_boxPush_path s t [c] hc (pathOk_cons) i hR χ).mp
              (hsat ⟨t, ⟨hR⟩⟩)
            have h2 := (gtruth_lt n t _ _ (by rw [size_pTrW]; exact hχs)).mp h1
            exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem a
            obtain ⟨t, ⟨hR⟩⟩ := a
            refine (sat_boxPush_path s t _ (pathOf_eq hR) (pathOf_ok hR) i hR χ).mpr ?_
            exact (gtruth_lt n t _ _ (by rw [size_pTrW]; exact hχs)).mpr
              (box_mem_path hM₀ s t _ (pathOf_eq hR) (pathOf_ok hR) i χ hmem)
      | dia x hx χ =>
          have hχs : χ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ (X : VarType) (h : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
            (a : ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x h)).1),
              (gmodel hF hM₀).sat ((gcanonEnv hM₀ s i).diaPush x h a) χ) ↔ _
          have IH : GTruthBelow (hF := hF) (hM₀ := hM₀) n :=
            fun t j φ hφ => gtruth_lt n t j φ hφ
          constructor
          · rintro ⟨X, h, ⟨⟨t, ⟨hR⟩⟩, hmt⟩, hsat⟩
            by_contra hnot
            have hbx : WFF.boxx x hx χ.neg ∈ (gw hM₀ s).M i :=
              BWorld.mem_of_provable (Δ := [(WFF.dia x hx χ).neg])
                (fun ψ hψ => by
                  rw [List.mem_singleton.mp hψ]
                  exact ((gw hM₀ s).mcs i).neg_mem_iff.mpr hnot)
                ⟨Proof.boxx_neg_of_not_dia (Γ := (gw hM₀ s).ctx i) x hx χ⟩
            have hg := (gcanon_mem_iff s i h ⟨t, ⟨hR⟩⟩).mp hmt
            by_cases hrl : (gw hM₀ t).Realised (kw s t (pathOf hR) (pathOf_eq hR) x)
            · exact gdia_real_not_boxx hrl.T IH s t i x h hR hmt hrl χ hχs hsat hbx
            obtain ⟨hnT, hm⟩ := Or.resolve_left hg hrl
            have h1 := (sat_diaPush_path hnT s t _ (pathOf_eq hR) i x h hR hmt hm χ).mp hsat
            have h2 := (gtruth_lt n t _ _ (by rw [size_pTrXW]; exact hχs)).mp h1
            have hneg := boxx_mem_path s t _ (pathOf_eq hR) i x hx hm χ.neg hbx
            rw [pTrXW_neg] at hneg
            exact ((gw hM₀ t).mcs _).neg_mem_iff.mp hneg h2
          · intro hmem
            obtain ⟨X, h⟩ := id hx
            by_cases hT : ModalSys.T = true
            · obtain ⟨a, ha⟩ := gdia_sat_child hT IH s i x h χ hχs hmem
              exact ⟨X, h, a, ha⟩
            have hnT : ModalSys.T = false := Bool.eq_false_iff.mpr hT
            obtain ⟨t, ⟨c, hc⟩, hk, -, -, hm⟩ := glexX hM₀ s i x X h χ hmem
            have hR : GR s t := ⟨[c], pathOk_cons, hc⟩
            have hmt : (⟨t, ⟨hR⟩⟩ : GAcc hF M₀ s) ∈
                ((gmodel hF hM₀).posEval ((gcanonEnv hM₀ s i).ref x h)).1 :=
              (gcanon_mem_iff s i h _).mpr (.inr ⟨hnT,
                inExt_pathOf hR (show InExt s t [c] hc x from hk)⟩)
            exact ⟨X, h, ⟨_, hmt⟩, (sat_diaPush_path hnT s t [c] hc i x h hR hmt hk
              χ).mpr
              ((gtruth_lt n t _ _ (by rw [size_pTrXW]; exact hχs)).mpr hm)⟩

/-- ⭐**The truth lemma** for the growing tree's canonical model. -/
theorem gtruth [ModalSys.FourCoh] (s : GW hF M₀) (i : ℕ) (φ : WFF σ (ctxOf (glat s i)) 0) :
    (gmodel hF hM₀).sat (gcanonEnv hM₀ s i) φ ↔ φ ∈ (gw hM₀ s).M i :=
  gtruth_lt (φ.size + 1) s i φ (Nat.lt_succ_self _)

end GArrow

end V12M
