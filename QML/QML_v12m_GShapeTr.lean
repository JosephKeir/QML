import QML.QML_v12m_GSelf

/-!
# QML v12m — the growing tree: shapes of translated terms

A term translated along a path (`pTr`) has, in any well-formed environment at the path's end,
the shape of the term itself in an environment **pulled back** along the path (`pullP`,
⭐`pTr_pullP`): the
step lemmas for substitution (`termShp_subst`), shifting (`termShp_shift`), collapsing
(`termShp_collapse`) and weakening (`termShp_mono`) compose along the path's edges.  The pulled
environment reads each item as the shape of the item's translation (`pull_item`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hF M₀) in
/-- Shape environments over the growing tree. -/
abbrev GEnv (Γ : Ctx) (t : GW hF M₀) : Type :=
  Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Γ t

/-! ## The pulled environments -/

section Pull

omit [Countable σ.FuncSyms] [Countable σ.RelSyms]

variable {F : Arrows.{0, 0} σ} {Root : F.W → Type} [Arrows.RootKeep F Root]

theorem entryShp_wf [Arrows.RootKeepLaws F Root] {Δ : Ctx} {t : F.W}
    {ρ : Model.ShEnv F Root Δ t} (hρ : ρ.WF []) :
    ∀ (e : SubE σ Δ) {T : VarType} (h : e.OkRef T),
      Model.ShWF (F := F) (Root := Root) [] (Model.entryShp ρ 0 e h)
  | .ren w, _, h => Model.ShEnv.wf_ref' (k := 0) hρ rfl w h
  | .tm s, _, h => by
      cases h
      exact Model.shWF_termShp hρ s
  | .hide, _, h => h.elim

theorem substShEnv_wf [Arrows.RootKeepLaws F Root] {Γ Δ : Ctx} {t : F.W} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hnp : Γ.NoProjLast) {ρ : Model.ShEnv F Root Δ t} (hρ : ρ.WF []) :
    (Model.substShEnv θ hθ hnp ρ 0).WF [] :=
  fun v _ _ => entryShp_wf hρ (θ v) _

/-- The environment a shift pulls back: each address read at its shift. -/
noncomputable def shiftPull {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂) (hnp : Γ₁.NoProjLast)
    {t : F.W} (ρ : Model.ShEnv F Root Γ₂ t) : Model.ShEnv F Root Γ₁ t :=
  fun v T hv => ρ.ref 0 (v.shift k) (h v T ((Ctx.ref_nonproj Γ₁ (hnp v T hv)).trans hv))

theorem shiftPull_agree {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂) (hnp : Γ₁.NoProjLast)
    {t : F.W} (ρ : Model.ShEnv F Root Γ₂ t) :
    Model.ShEnv.ShiftAgree h (shiftPull h hnp ρ) ρ 0 :=
  Model.ShEnv.ShiftAgree.of_raw fun _ _ _ _ => rfl

theorem shiftPull_wf [Arrows.RootKeepLaws F Root] {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂)
    (hnp : Γ₁.NoProjLast) {t : F.W} {ρ : Model.ShEnv F Root Γ₂ t} (hρ : ρ.WF []) :
    (shiftPull h hnp ρ).WF [] :=
  fun _ _ _ => Model.ShEnv.wf_ref' (k := 0) hρ rfl _ _

end Pull

/-- The environment collapsing the `□` view pulls back: the view's shapes collapsed. -/
noncomputable abbrev colPull (hT : ModalSys.T = true) {Γ : Ctx} {t : GW hF M₀}
    (ρ : GEnv hF M₀ Γ t) : GEnv hF M₀ Γ.boxIn t :=
  (ρ.boxPush 0).mapLeaves (Arrows.Leaf.collapse hT 0)

theorem colPull_wf (hT : ModalSys.T = true) {Γ : Ctx} {t : GW hF M₀} {ρ : GEnv hF M₀ Γ t}
    (hρ : ρ.WF []) : (colPull hT ρ).WF [] := by
  intro v T hv
  have h := Model.ShEnv.wf_boxPush' (k := 0) hρ rfl v T hv
  exact Shp.wf_map (Arrows.Leaf.collapse hT 0) [true] []
    (fun r ℓ hℓ => Arrows.Leaf.wf_collapse hT [] r ℓ hℓ) [] _ h

/-! ## Along a path -/

/-- ⭐**The environment a path pulls back**: collapsing along the empty path, an edge's entries
    along an edge, and along `c :: P` the first edge's `□`-lifted entries after a shift. -/
noncomputable def pullP (hM₀ : Theory.IsMCS M₀) :
    (P : List ℕ) → (s t : GW hF M₀) → (h : t.1 = nodeOf s.1 P) → PathOk P → (i : ℕ) →
      GEnv hF M₀ (ctxOf (glat t (pstg s t P h i))) t →
        GEnv hF M₀ ((ctxOf (glat s i)).kView none) t
  | [], _, _, h, hP, i, ρ => colPull hP.T_of_nil (fun v T hv => ρ v T (glat_le_of_eq h i v T hv))
  | [c], _, t, h, _, i, ρ =>
      Model.substShEnv (eS σ _ (fmapL hF M₀ t.1)) (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
        (Ctx.noProjLast_boxIn _) ρ 0
  | c :: c' :: P, s, t, h, _, i, ρ =>
      shiftPull (Ctx.shifts_boxIn_boxIn hF _) (Ctx.noProjLast_boxIn _)
        (Model.substShEnv
          (eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).box
          (Subst.ok_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          (Ctx.noProjLast_boxIn _)
          (pullP hM₀ (c' :: P) (stepW s c (born_step h)) t h pathOk_cons _ ρ) 0)

theorem pullP_wf (hM₀ : Theory.IsMCS M₀) : ∀ (P : List ℕ) (s t : GW hF M₀)
    (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ)
    {ρ : GEnv hF M₀ (ctxOf (glat t (pstg s t P h i))) t}, ρ.WF [] →
      (pullP hM₀ P s t h hP i ρ).WF []
  | [], _, _, _, hP, _, _, hρ => colPull_wf hP.T_of_nil (fun v T _ => hρ v T _)
  | [_], _, _, _, _, _, _, hρ => substShEnv_wf _ _ _ hρ
  | _ :: c' :: P, _, t, h, _, _, _, hρ =>
      shiftPull_wf _ _ (substShEnv_wf _ _ _ (pullP_wf hM₀ (c' :: P) _ t h pathOk_cons _ hρ))

/-- ⭐**A translated term's shape is the term's shape in the pulled environment.** -/
theorem pTr_pullP (hM₀ : Theory.IsMCS M₀) : ∀ (P : List ℕ) (s t : GW hF M₀)
    (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ)
    (ρ : GEnv hF M₀ (ctxOf (glat t (pstg s t P h i))) t), ρ.WF [] →
      ∀ {A : VarType} {a : Ann A} (X : Term σ ((ctxOf (glat s i)).kView none) A a),
        Model.termShp ρ 0 (pTr hM₀ s t P h hP i X).2 =
          Model.termShp (pullP hM₀ P s t h hP i ρ) 0 X
  | [], s, t, h, hP, i, ρ, _, _, _, X => by
      have hT := hP.T_of_nil
      let ρm : GEnv hF M₀ (ctxOf (glat s i)) t := fun v T hv => ρ v T (glat_le_of_eq h i v T hv)
      have hag : Model.ShEnv.Agree (glat_le_of_eq h i) ρm ρ := fun _ _ _ => rfl
      change Model.termShp ρ 0 (Term.mono _ (Term.collapse _ X)) = _
      rw [Model.termShp_mono hag 0,
        Model.termShp_collapse (Model.ShEnv.collapseAgree_self hT ρm 0)]
      rfl
  | [_], _, _, _, _, _, ρ, hρ, _, _, X =>
      Model.termShp_subst _ _ _ (Ctx.noProjLast_boxIn _) ρ 0 (lw := []) rfl (fun _ => hρ) X
  | c :: c' :: P, s, t, h, _, i, ρ, hρ, _, _, X => by
      change Model.termShp ρ 0 (pTr hM₀ _ t (c' :: P) h pathOk_cons _ _).2 = _
      rw [pTr_pullP hM₀ (c' :: P) _ t h pathOk_cons _ ρ hρ,
        Model.termShp_subst _ _ _ (Ctx.noProjLast_boxIn _) _ 0 (lw := []) rfl
          (fun _ => pullP_wf hM₀ (c' :: P) _ t h pathOk_cons _ hρ),
        Model.termShp_shift (shiftPull_agree _ (Ctx.noProjLast_boxIn _) _)]
      rfl

/-- The pulled environment reads an item as the shape of the item's translation. -/
theorem pull_item {Γ : Ctx} {t : GW hF M₀} (hnp : Γ.NoProjLast) {ρ' : GEnv hF M₀ Γ t}
    {f : ∀ {A : VarType} {a : Ann A}, Term σ Γ A a → GShape hF M₀ t A}
    (hf : ∀ {A : VarType} {a : Ann A} (X : Term σ Γ A a), f X = Model.termShp ρ' 0 X)
    {w : VarSymb} {T : VarType} (hw : Γ w = some T) :
    ρ' w T hw = f (Term.eta w T ((Ctx.ref_nonproj Γ (hnp w T hw)).trans hw)) := by
  rw [hf, Model.termShp_eta]
  match w, hw, hnp w T hw with
  | .root _, _, _ => rfl
  | .step v st, hw', e =>
      have e' : st.isProj = false := e
      exact (Model.ShEnv.ref_nonproj _ _ (by rw [e']; decide) _).symm

end GArrow

end V12M
