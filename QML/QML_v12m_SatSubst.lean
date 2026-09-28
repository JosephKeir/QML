import QML.QML_v12m_SemSubst

/-!
# QML v12m — semantics of substitution (formulas)

⭐`sat_subst`: a substituted formula holds in an environment exactly when the formula holds in the
substituted environment.  The binder case uses `substEnv_under` (the substituted environment of
`θ.under` is the substituted environment of `θ`, extended); the modal cases use `substEnv_box`
and `substEnv_dia`.
-/

namespace V12M

variable [ModalSys]

omit [ModalSys] in
theorem Ctx.NoProjLast.insert {Γ : Ctx} (h : Γ.NoProjLast) (r : Root) (T : VarType) :
    (Γ.insert r T).NoProjLast := by
  intro v U hv
  by_cases hvr : v = .root r
  · subst hvr
    rfl
  · exact h v U (by simpa [Ctx.insert, hvr] using hv)

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

theorem Env.agree_extend {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {r : Root}
    (h : Δ (.root r) = none) {T : VarType} (o : M.frame.Dom T w) :
    Env.Agree (Ctx.le_insert h T) env (env.extend r o) := fun v U hv =>
  (Env.extend_ne env r o _ (fun he => by subst he; rw [h] at hv; cases hv) hv).symm

theorem substEnv_under {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) {d d' : ℕ} (T : VarType)
    (h : Δ (.root (.bnd d')) = none) (o : M.frame.Dom T w) :
    substEnv (θ.under d d' T h) (Subst.ok_under hθ T h) (hnp.insert (.bnd d) T)
        (env.extend (.bnd d') o) =
      (substEnv θ hθ hnp env).extend (.bnd d) o := by
  funext v U hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [Env.extend_root (substEnv θ hθ hnp env) _ o hv]
    exact (entryVal_congr _
      (show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl) _
      (Ctx.ref_insert_root Δ _ T)).trans (Env.extend_root env _ o (Ctx.ref_insert_root Δ _ T))
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [Env.extend_ne (substEnv θ hθ hnp env) _ o hv hvr hv']
    exact (entryVal_congr _
      (show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr) _
      (SubE.okRef_mono _ (hθ v U (hnp v U hv') hv'))).trans
      (entryVal_mono (Env.agree_extend env h o) _ _)

theorem relSat_subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hnp : Γ.NoProjLast) {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {n : ℕ} (ρ : Rel σ Γ n) (args : Fin n → M.frame.D w),
      relSat env (Rel.subst ι θ hθ hc ρ) args ↔ relSat (substEnv θ hθ hnp env) ρ args
  | _, .R _, _ => Iff.rfl
  | _, .eval ρ t, args => by
      change relSat env (Rel.subst ι θ hθ hc ρ)
          (Fin.cons (interp env (Term.subst ι θ hθ hc t)) args) ↔
        relSat (substEnv θ hθ hnp env) ρ (Fin.cons (interp (substEnv θ hθ hnp env) t) args)
      rw [interp_subst θ hθ hc hnp env t]
      exact relSat_subst θ hθ hc hnp env ρ _

/-- ⭐**Substitution lemma** for formulas. -/
theorem sat_subst : ∀ {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hnp : Γ.NoProjLast) {w : M.frame.W} (env : M.Env Δ w) (φ : WFF σ Γ d),
    M.sat env (WFF.subst ι θ hθ hc hΓ hΔ φ) ↔ M.sat (substEnv θ hθ hnp env) φ
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .atom ρ =>
      relSat_subst θ hθ hc hnp env ρ Fin.elim0
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .eq t s => by
      change interp env (Term.subst _ θ hθ hc t) = interp env (Term.subst _ θ hθ hc s) ↔ _
      rw [interp_subst θ hθ hc hnp env t, interp_subst θ hθ hc hnp env s]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .top => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => Iff.rfl
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .and φ ψ =>
      and_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ) (sat_subst θ hθ hc hΓ hΔ hnp env ψ)
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .or φ ψ =>
      or_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ) (sat_subst θ hθ hc hΓ hΔ hnp env ψ)
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .imp φ ψ =>
      imp_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ) (sat_subst θ hθ hc hΓ hΔ hnp env ψ)
  | _, _, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .all T φ =>
      forall_congr' fun o =>
        (sat_subst (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
          (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T)
          (hnp.insert (.bnd d) T) (env.extend (.bnd d') o) φ).trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_under θ hθ hnp env T hΔ.root o)))
  | _, _, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .ex T φ =>
      exists_congr fun o =>
        (sat_subst (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
          (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T)
          (hnp.insert (.bnd d) T) (env.extend (.bnd d') o) φ).trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_under θ hθ hnp env T hΔ.root o)))
  | _, Γ, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .box φ =>
      forall_congr' fun w' =>
        (sat_subst θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn
          (Ctx.noProjLast_boxIn Γ) (env.boxPush w') φ).trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_box θ hθ hnp env w')))
  | ι, Γ, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .dia x hx φ => by
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      constructor
      · rintro ⟨Y, hr₁, w', hsat⟩
        obtain ⟨X, hr⟩ := hx
        have hE : (M.posEval (env.ref (ι x) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref x hr)).1 := by
          rw [substEnv_ref θ hθ hnp env x hr, entryVal_dia_ext env _ hw hr₁]
        refine ⟨X, hr, ⟨w'.1, hE ▸ w'.2⟩, ?_⟩
        rw [← substEnv_dia θ hθ hnp env ⟨X, hr⟩ hr hr₁ hw w' _]
        exact (sat_subst (θ.dia x (ι x)) (Subst.ok_dia hθ ⟨X, hr⟩ hw)
          (Subst.coh_dia hθ hc ⟨X, hr⟩) (hΓ.diaIn x) (hΔ.diaIn (ι x))
          (Ctx.noProjLast_diaIn Γ x) (env.diaPush (ι x) hr₁ w') φ).mp hsat
      · rintro ⟨X, hr, w₂, hsat⟩
        obtain ⟨Y, hr₁⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hw
        have hE : (M.posEval (env.ref (ι x) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref x hr)).1 := by
          rw [substEnv_ref θ hθ hnp env x hr, entryVal_dia_ext env _ hw hr₁]
        refine ⟨Y, hr₁, ⟨w₂.1, hE.symm ▸ w₂.2⟩, ?_⟩
        refine (sat_subst (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hΓ.diaIn x) (hΔ.diaIn (ι x)) (Ctx.noProjLast_diaIn Γ x)
          (env.diaPush (ι x) hr₁ ⟨w₂.1, hE.symm ▸ w₂.2⟩) φ).mpr ?_
        rw [substEnv_dia θ hθ hnp env hx hr hr₁ hw ⟨w₂.1, hE.symm ▸ w₂.2⟩ w₂.2]
        exact hsat
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .here hT hA s t => by
      change Model.Realised hT (interp env (Term.subst _ θ hθ hc s))
        (interp env (Term.subst _ θ hθ hc t)) ↔ _
      rw [interp_subst θ hθ hc hnp env s, interp_subst θ hθ hc hnp env t]
      exact Iff.rfl

end Model

end V12M
