import QML.QML_v12m_GTr

/-!
# QML v12m — chains and shapes

Under T possible objects carry shapes, so the truth lemma for terms compares the shape of a
term's value in an environment agreeing with a chain with the stored shape of the chain's image
(`interp_gtr`).  The chain's steps pull a shape environment back, as a path's do (`pullP`):

* `GTr.NPL`: the contexts its substitutions, shifts and collapses start from have no projection
  as a last step (views always do; `npl_box`, `npl_dia`, `npl_comp`);
* `pullC`: the environment a chain pulls back — `substShEnv` at a substitution, the shifted
  (`shiftPull`) or collapsed (`colPullG`) reading at a shift or a collapse, the restriction at a
  weakening;
* ⭐`termShp_gtr`: the shape of a chain's image is the term's shape in the pulled environment.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

namespace GTr

/-- The contexts a chain's substitutions, shifts and collapses start from have no projection as a
    last step. -/
def NPL : {Γ Δ : Ctx} → GTr σ Γ Δ → Prop
  | _, _, .nil _ => True
  | Γ, _, .sub _ _ _ C => Γ.NoProjLast ∧ C.NPL
  | Γ, _, .sh _ C => Γ.NoProjLast ∧ C.NPL
  | _, _, .mono _ C => C.NPL
  | Γ, _, .col _ C => Γ.NoProjLast ∧ C.NPL

theorem npl_comp : ∀ {Γ Δ Δ' : Ctx} (C : GTr σ Γ Δ) (D : GTr σ Δ Δ'), C.NPL → D.NPL →
    (C.comp D).NPL
  | _, _, _, .nil _, _, _, hD => hD
  | _, _, _, .sub _ _ _ C, D, hC, hD => ⟨hC.1, npl_comp C D hC.2 hD⟩
  | _, _, _, .sh _ C, D, hC, hD => ⟨hC.1, npl_comp C D hC.2 hD⟩
  | _, _, _, .mono _ C, D, hC, hD => npl_comp C D hC hD
  | _, _, _, .col _ C, D, hC, hD => ⟨hC.1, npl_comp C D hC.2 hD⟩

/-- A chain's `□` view starts every step from a `□` view. -/
theorem npl_box : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ), C.box.NPL
  | _, _, .nil _ => trivial
  | _, _, .sub _ _ _ C => ⟨Ctx.noProjLast_boxIn _, npl_box C⟩
  | _, _, .sh _ C => ⟨Ctx.noProjLast_boxIn _, npl_box C⟩
  | _, _, .mono _ C => npl_box C
  | _, _, .col _ C => ⟨Ctx.noProjLast_boxIn _, npl_box C⟩

/-- A chain's `◇_x` view starts every step from a `◇` view. -/
theorem npl_dia : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)), (C.dia x hx).NPL
  | _, _, .nil _, _, _ => trivial
  | _, _, .sub _ _ _ C, _, _ => ⟨Ctx.noProjLast_diaIn _ _, npl_dia C _ _⟩
  | _, _, .sh _ C, _, _ => ⟨Ctx.noProjLast_diaIn _ _, npl_dia C _ _⟩
  | _, _, .mono _ C, _, _ => npl_dia C _ _
  | _, _, .col _ C, _, _ => ⟨Ctx.noProjLast_diaIn _ _, npl_dia C _ _⟩

end GTr

variable {F : Arrows.{0, 0} σ} {Root : F.W → Type} [Arrows.RootKeep F Root]

/-! ## The pulled environment -/

/-- The environment a collapse pulls back: each address read at its collapse. -/
noncomputable def colPullG {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂)
    (hnp : Γ₁.NoProjLast) {t : F.W} (ρ : Model.ShEnv F Root Γ₂ t) : Model.ShEnv F Root Γ₁ t :=
  fun v T hv => ρ.ref 0 (v.collapse k) (h v T ((Ctx.ref_nonproj Γ₁ (hnp v T hv)).trans hv))

theorem colPullG_agree {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) (hnp : Γ₁.NoProjLast)
    {t : F.W} (ρ : Model.ShEnv F Root Γ₂ t) :
    Model.ShEnv.CollapseAgree h (colPullG h hnp ρ) ρ 0 :=
  Model.ShEnv.CollapseAgree.of_raw fun _ _ _ _ => rfl

theorem colPullG_wf [Arrows.RootKeepLaws F Root] {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.Collapses k Γ₁ Γ₂) (hnp : Γ₁.NoProjLast) {t : F.W} {ρ : Model.ShEnv F Root Γ₂ t}
    (hρ : ρ.WF []) : (colPullG h hnp ρ).WF [] :=
  fun _ _ _ => Model.ShEnv.wf_ref' (k := 0) hρ rfl _ _

/-- ⭐**The environment a chain pulls back**. -/
noncomputable def pullC {t : F.W} : {Γ Δ : Ctx} → (C : GTr σ Γ Δ) → C.NPL →
    Model.ShEnv F Root Δ t → Model.ShEnv F Root Γ t
  | _, _, .nil _, _, ρ => ρ
  | _, _, .sub θ hθ _ C, hC, ρ => Model.substShEnv θ hθ hC.1 (pullC C hC.2 ρ) 0
  | _, _, .sh h C, hC, ρ => shiftPull h hC.1 (pullC C hC.2 ρ)
  | _, _, .mono h C, hC, ρ => fun v T hv => pullC C hC ρ v T (h v T hv)
  | _, _, .col h C, hC, ρ => colPullG h hC.1 (pullC C hC.2 ρ)

theorem pullC_wf [Arrows.RootKeepLaws F Root] {t : F.W} : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ)
    (hC : C.NPL) {ρ : Model.ShEnv F Root Δ t}, ρ.WF [] → (pullC C hC ρ).WF []
  | _, _, .nil _, _, _, hρ => hρ
  | _, _, .sub θ hθ _ C, hC, _, hρ => substShEnv_wf θ hθ hC.1 (pullC_wf C hC.2 hρ)
  | _, _, .sh h C, hC, _, hρ => shiftPull_wf h hC.1 (pullC_wf C hC.2 hρ)
  | _, _, .mono _ C, hC, _, hρ => fun v T _ => pullC_wf C hC hρ v T _
  | _, _, .col h C, hC, _, hρ => colPullG_wf h hC.1 (pullC_wf C hC.2 hρ)

/-- ⭐**The shape of a chain's image is the term's shape in the pulled environment.** -/
theorem termShp_gtr [Arrows.RootKeepLaws F Root] {t : F.W} : ∀ {Γ Δ : Ctx} (C : GTr σ Γ Δ)
    (hC : C.NPL) (ρ : Model.ShEnv F Root Δ t), ρ.WF [] →
    ∀ {A : VarType} {a : Ann A} (X : Term σ Γ A a),
      Model.termShp ρ 0 (C.app X).2 = Model.termShp (pullC C hC ρ) 0 X
  | _, _, .nil _, _, _, _, _, _, _ => rfl
  | _, _, .sub θ hθ hc C, hC, ρ, hρ, _, _, X => by
      change Model.termShp ρ 0 (C.app (Term.subst _ θ hθ hc X)).2 = _
      rw [termShp_gtr C hC.2 ρ hρ, Model.termShp_subst θ hθ hc hC.1 _ 0 (lw := []) rfl
        (fun _ => pullC_wf C hC.2 hρ) X]
      rfl
  | _, _, .sh h C, hC, ρ, hρ, _, _, X => by
      change Model.termShp ρ 0 (C.app (Term.shift h X)).2 = _
      rw [termShp_gtr C hC.2 ρ hρ, Model.termShp_shift (shiftPull_agree h hC.1 _)]
      rfl
  | _, _, .mono h C, hC, ρ, hρ, _, _, X => by
      change Model.termShp ρ 0 (C.app (Term.mono h X)).2 = _
      rw [termShp_gtr C hC ρ hρ,
        Model.termShp_mono (ρ := fun v T hv => pullC C hC ρ v T (h v T hv)) (fun _ _ _ => rfl)]
      rfl
  | _, _, .col h C, hC, ρ, hρ, _, _, X => by
      change Model.termShp ρ 0 (C.app (Term.collapse h X)).2 = _
      rw [termShp_gtr C hC.2 ρ hρ, Model.termShp_collapse (colPullG_agree h hC.1 _)]
      rfl

end GArrow

end V12M
