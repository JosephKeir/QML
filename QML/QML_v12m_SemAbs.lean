import QML.QML_v12m_SemStrongT
import QML.QML_v12m_Abs

/-!
# QML v12m — the semantics of realisation at an arbitrary address (strong T)

The three semantic facts `QML_v12m_SemStrongT` proves for a realised **root**, now for an arbitrary
declared `◇`-typed address, since `QML_v12m_Abs` abstracts a view there:

* ⭐`Model.Env.substEnv_diaAbsA`: the environment the abstraction induces at the world where the
  witness is realised is the environment pushed into its `◇` view;
* ⭐`Model.interp_realiseAtA` and ⭐`Model.sat_realiseAtA`: so a term or formula of the view denotes,
  or holds, exactly as its realisation does here.

The proofs are the root ones, with `Subst.diaIn_casesA` in place of `Subst.diaIn_cases` and the
freshness hypothesis replaced by what the presentation gives (`Ctx.Presented.not_below`).
-/

namespace V12M

variable [ModalSys] {σ : Signature} {M : Model.{0, 0} σ}

namespace Model

/-- The environment abstraction induces, at the world where the witness is realised, is the
    environment pushed into its `◇` view there. -/
theorem Env.substEnv_diaAbsA (hT : ModalSys.T = true) {Γ : Ctx} [Γ.Presented] {w : M.frame.W}
    (env : M.Env Γ w) {x : VarSymb} {A : VarType}
    (hcA : Γ.ref x = some (.VTypeDia A))
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    (hmem : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hcA)).1)
    (hcont : (M.posEval (env.ref x hcA)).2 ⟨M.frame.reflAcc hT w, hmem⟩ =
      interp env t₀) :
    substEnv (Subst.diaAbsA σ (Γ.boxIn.insert (.bnd 0) A) x)
        (Subst.ok_diaAbsA hcA (Ctx.Presented.not_below inferInstance hcA rfl)
          ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root))
        (Ctx.noProjLast_diaIn Γ x)
        ((env.boxPush (M.frame.reflAcc hT w)).extend (.bnd 0) (interp env t₀)) =
      env.diaPush x hcA ⟨M.frame.reflAcc hT w, hmem⟩ := by
  funext v T hv
  rcases Subst.diaIn_casesA hcA (Ctx.Presented.not_below inferInstance hcA rfl) hv with
    ⟨rfl, rfl⟩ | ⟨_, hb, hen, hroot⟩
  · refine (entryVal_congr _ (show Subst.diaAbsA σ (Γ.boxIn.insert (.bnd 0) T) x
        (.step x .dia) = .ren (.root (.bnd 0)) from if_pos rfl) _
      (Ctx.ref_insert_root _ (.bnd 0) T)).trans ?_
    refine (Env.extend_root (env.boxPush (M.frame.reflAcc hT w)) (.bnd 0) (interp env t₀)
      (by simp [Ctx.insert])).trans ?_
    exact hcont.symm
  · have hbr : (Γ.boxIn.insert (.bnd 0) A) v = some T := by
      change (if v = .root (.bnd 0) then some A else Γ.boxIn v) = some T
      rw [if_neg (hroot (.bnd 0))]
      exact hb
    refine (entryVal_congr _ (hen (Γ.boxIn.insert (.bnd 0) A)) _
      ((Ctx.ref_nonproj _ (Ctx.noProjLast_diaIn Γ x v T hv)).trans hbr)).trans ?_
    refine (Env.ref_of_nonproj _ (Ctx.noProjLast_diaIn Γ x v T hv) _ hbr).trans ?_
    refine (Env.extend_ne (env.boxPush (M.frame.reflAcc hT w)) (.bnd 0) (interp env t₀) hbr
      (hroot (.bnd 0)) hb).trans ?_
    match v with
    | .step _ .box => rfl
    | .step _ .keep => rfl
    | .root _ => exact absurd rfl (hroot _)
    | .step _ .fst => cases hb
    | .step _ .snd => cases hb
    | .step _ .dia => cases hb
    | .step _ .here => cases hb

/-- ⭐At the world where the witness is realised, a term of its `◇` view denotes what its
    realisation denotes here. -/
theorem interp_realiseAtA (hT : ModalSys.T = true) {Γ : Ctx} [Γ.Presented] {w : M.frame.W}
    (env : M.Env Γ w) (hnp : Γ.NoProjLast) {x : VarSymb} {A : VarType}
    (hcA : Γ.ref x = some (.VTypeDia A))
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    (hmem : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hcA)).1)
    (hcont : (M.posEval (env.ref x hcA)).2 ⟨M.frame.reflAcc hT w, hmem⟩ =
      interp env t₀)
    {T : VarType} {b : Ann T} (t : Term σ (Γ.diaIn x) T b) :
    interp env (Term.realiseAtA hT x hcA t₀ t) =
      interp (env.diaPush x hcA ⟨M.frame.reflAcc hT w, hmem⟩) t := by
  simp only [Term.realiseAtA, Term.hereRead, Term.diaAbsA]
  rw [interp_subst _ _ _ (hnp.insert (.bnd 0) A) env, substEnv_single_tm env hnp (.bnd 0) t₀,
    interp_collapse ((Env.collapseAgree_self hT env).extend
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (interp env t₀)),
    interp_subst _ _ _ (Ctx.noProjLast_diaIn Γ x) _,
    Env.substEnv_diaAbsA hT env hcA t₀ hmem hcont]

/-- ⭐The same for formulas: at the world where the witness is realised, a formula of its `◇` view
    holds exactly when its realisation holds here.  This is what the canonical model's truth lemma
    needs at the world itself. -/
theorem sat_realiseAtA (hT : ModalSys.T = true) {Γ : Ctx} [Γ.Presented] {w : M.frame.W}
    (env : M.Env Γ w) (hnp : Γ.NoProjLast) {x : VarSymb} {A : VarType}
    (hcA : Γ.ref x = some (.VTypeDia A))
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    (hmem : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hcA)).1)
    (hcont : (M.posEval (env.ref x hcA)).2 ⟨M.frame.reflAcc hT w, hmem⟩ =
      interp env t₀)
    (χ : WFF σ (Γ.diaIn x) 0) :
    M.sat env (WFF.realiseAtA hT x hcA t₀ χ) ↔
      M.sat (env.diaPush x hcA ⟨M.frame.reflAcc hT w, hmem⟩) χ := by
  refine (sat_instantiate env hnp Ctx.NoSlots.slots t₀ _).trans ?_
  refine (sat_collapse ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
    ((Env.collapseAgree_self hT env).extend
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (interp env t₀)) _).trans ?_
  refine (sat_subst _ _ _ Ctx.NoSlots.slots ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
    (Ctx.noProjLast_diaIn Γ x) _ χ).trans ?_
  rw [Env.substEnv_diaAbsA hT env hcA t₀ hmem hcont]


end Model

end V12M
