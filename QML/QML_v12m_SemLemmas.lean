import QML.QML_v12m_InterpLemmas
import QML.QML_v12m_Eq

/-!
# QML v12m — semantics: weakening, and equality means equality

* `interp_mono` / `sat_mono`: values and satisfaction are unchanged by weakening, for
  environments that agree on the smaller context (`Env.Agree`).
* ⭐`sat_eqRec`: the defined equality `eqRec T t s` holds exactly when `t` and `s` have the same
  value.  At `□A` and `◇A` this is extensionality of the carriers (`nec_inj`, `pos_inj`) together
  with the β laws; at `◇A` the classical reading of `□_x = ¬◇_x¬` is used.

The modal cases never look inside the compilation: only the β laws are used.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u} σ}

/-! ## Agreeing environments -/

/-- Two environments agree along an inclusion of contexts. -/
def Env.Agree {Γ Γ' : Ctx} (h : Γ.Le Γ') {w : M.frame.W} (env : M.Env Γ w)
    (env' : M.Env Γ' w) : Prop :=
  ∀ v T (hv : Γ v = some T), env v T hv = env' v T (h v T hv)

theorem Env.ref_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Env.Agree h env env') :
    ∀ (v : VarSymb) {T : VarType} (hv : Γ.ref v = some T), env.ref v hv = env'.ref v (h.ref hv)
  | .root r, _, hv => hag (.root r) _ hv
  | .step v s, T, hv => by
      by_cases hs : s.isProj = true
      · rw [Env.ref, Env.ref, dif_pos hs, dif_pos hs]
        split
        · rename_i U hU
          split
          · rename_i U' hU'
            have hUU : U' = U := Option.some.inj (hU'.symm.trans (h.ref hU))
            subst hUU
            rw [Env.ref_agree hag v hU]
          · rename_i hU'
            exfalso
            rw [h.ref hU] at hU'
            cases hU'
        · rename_i hU
          exfalso
          rw [Ctx.ref_step_proj Γ v hs, hU] at hv
          cases hv
      · rw [Env.ref, Env.ref, dif_neg hs, dif_neg hs]
        exact hag _ _ _

theorem Env.boxPush_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Env.Agree h env env') (w' : M.frame.Acc w) :
    Env.Agree h.boxIn (env.boxPush w') (env'.boxPush w') := by
  intro v T hv
  match v with
  | .step u .box =>
      change M.necEval (env.ref u (Ctx.boxIn_step_box hv)) w' =
        M.necEval (env'.ref u (h.ref (Ctx.boxIn_step_box hv))) w'
      rw [Env.ref_agree hag u (Ctx.boxIn_step_box hv)]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

theorem Env.extend_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Env.Agree h env env') (r : Root) {T : VarType}
    (o : M.frame.Dom T w) : Env.Agree (h.insert r T) (env.extend r o) (env'.extend r o) := by
  intro v U hv
  by_cases hvr : v = .root r
  · change (if hvr : v = .root r then _ else _) = (if hvr : v = .root r then _ else _)
    rw [dif_pos hvr, dif_pos hvr]
  · change (if hvr : v = .root r then _ else _) = (if hvr : v = .root r then _ else _)
    rw [dif_neg hvr, dif_neg hvr]
    exact hag _ _ _

theorem posEval_snd_congr {A : VarType} {w : M.frame.W} {p q : M.frame.Pos A w} (hpq : p = q)
    (w₁ : (M.posEval p).1) (hm : w₁.1 ∈ (M.posEval q).1) :
    (M.posEval p).2 w₁ = (M.posEval q).2 ⟨w₁.1, hm⟩ := by
  subst hpq
  rfl

theorem Env.diaPush_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Env.Agree h env env') {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (w₁ : (M.posEval (env.ref x hr)).1)
    (hm : w₁.1 ∈ (M.posEval (env'.ref x (h.ref hr))).1) :
    Env.Agree (h.diaIn x) (env.diaPush x hr w₁) (env'.diaPush x (h.ref hr) ⟨w₁.1, hm⟩) := by
  intro v T hv
  match v with
  | .step u .dia =>
      simp only [Env.diaPush]
      have hXT := Ctx.diaIn_step_dia hr hv
      subst hXT
      exact posEval_snd_congr (Env.ref_agree hag x hr) w₁ hm
  | .step u .box => exact Env.boxPush_agree hag w₁.1 (.step u .box) T hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

theorem posSec_ext {X A : VarType} {w : M.frame.W} {p q : M.frame.Pos X w} (hpq : p = q)
    (f : (w' : (M.posEval p).1) → M.frame.Dom A w'.1.1)
    (g : (w' : (M.posEval q).1) → M.frame.Dom A w'.1.1)
    (hfg : ∀ w' : (M.posEval p).1, f w' = g ⟨w'.1, hpq ▸ w'.2⟩) :
    (⟨(M.posEval p).1, f⟩ : M.frame.PosSec A w) = ⟨(M.posEval q).1, g⟩ := by
  subst hpq
  exact congrArg (Sigma.mk _) (funext hfg)

/-! ## Weakening -/

mutual
  theorem interpFunc_mono {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
      {env' : M.Env Γ' w} (hag : Env.Agree h env env') :
      ∀ {n : ℕ} (g : Func σ Γ n) (args : Fin n → M.frame.D w),
        interpFunc env' (Func.mono h g) args = interpFunc env g args
    | _, .F _, _ => rfl
    | _, .eval g t, args => by
        change interpFunc env' (Func.mono h g) (Fin.cons (interp env' (Term.mono h t)) args) =
          interpFunc env g (Fin.cons (interp env t) args)
        rw [interp_mono hag t, interpFunc_mono hag g]

  /-- ⭐Values are unchanged by weakening. -/
  theorem interp_mono {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
      {env' : M.Env Γ' w} (hag : Env.Agree h env env') :
      ∀ {T : VarType} {a : Ann T} (t : Term σ Γ T a), interp env' (Term.mono h t) = interp env t
    | _, _, .var v hv => (Env.ref_agree hag v hv).symm
    | _, _, .func f => interpFunc_mono hag f Fin.elim0
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change (interp env' (Term.mono h s), interp env' (Term.mono h t)) =
          (interp env s, interp env t)
        rw [interp_mono hag s, interp_mono hag t]
    | _, _, .boxtm t => by
        apply M.nec_inj
        funext w'
        change M.necEval (interp env' (Term.boxtm (Term.mono h.boxIn t))) w' = _
        rw [box_beta, box_beta, interp_mono (Env.boxPush_agree hag w') t]
    | _, _, .diatm x hx t => by
        obtain ⟨X, hr⟩ := hx
        apply M.pos_inj
        change M.posEval (interp env' (Term.diatm x _ (Term.mono (h.diaIn x) t))) = _
        rw [dia_beta env' _ (h.ref hr), dia_beta env _ hr]
        symm
        exact posSec_ext (Env.ref_agree hag x hr)
          (fun w₁ => interp (env.diaPush x hr w₁) t)
          (fun w₂ => interp (env'.diaPush x (h.ref hr) w₂) (Term.mono (h.diaIn x) t))
          (fun w₁ => (interp_mono (Env.diaPush_agree hag hr w₁ _) t).symm)
end

theorem relSat_mono {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Env.Agree h env env') :
    ∀ {n : ℕ} (ρ : Rel σ Γ n) (args : Fin n → M.frame.D w),
      relSat env' (Rel.mono h ρ) args ↔ relSat env ρ args
  | _, .R _, _ => Iff.rfl
  | _, .eval ρ t, args => by
      change relSat env' (Rel.mono h ρ) (Fin.cons (interp env' (Term.mono h t)) args) ↔
        relSat env ρ (Fin.cons (interp env t) args)
      rw [interp_mono hag t]
      exact relSat_mono hag ρ _

/-- ⭐Satisfaction is unchanged by weakening. -/
theorem sat_mono : ∀ {Γ Γ' : Ctx} {h : Γ.Le Γ'} {d : ℕ} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w}, Env.Agree h env env' → (φ : WFF σ Γ d) →
    (M.sat env' (WFF.mono h φ) ↔ M.sat env φ)
  | _, _, _, _, _, _, _, hag, .atom ρ => relSat_mono hag ρ Fin.elim0
  | _, _, _, _, _, _, _, hag, .eq t s => by
      change interp _ (Term.mono _ t) = interp _ (Term.mono _ s) ↔ _
      rw [interp_mono hag t, interp_mono hag s]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, .top => Iff.rfl
  | _, _, _, _, _, _, _, _, .bot => Iff.rfl
  | _, _, _, _, _, _, _, hag, .and φ ψ => and_congr (sat_mono hag φ) (sat_mono hag ψ)
  | _, _, _, _, _, _, _, hag, .or φ ψ => or_congr (sat_mono hag φ) (sat_mono hag ψ)
  | _, _, _, _, _, _, _, hag, .imp φ ψ => imp_congr (sat_mono hag φ) (sat_mono hag ψ)
  | _, _, _, d, _, _, _, hag, .all _ φ =>
      forall_congr' fun o => sat_mono (Env.extend_agree hag (.bnd d) o) φ
  | _, _, _, d, _, _, _, hag, .ex _ φ =>
      exists_congr fun o => sat_mono (Env.extend_agree hag (.bnd d) o) φ
  | _, _, _, _, _, _, _, hag, .box φ =>
      forall_congr' fun w' => sat_mono (Env.boxPush_agree hag w') φ
  | _, _, h, _, _, env, env', hag, .dia x hx φ => by
      constructor
      · rintro ⟨X, h', w₂, hsat⟩
        obtain ⟨X₀, hr⟩ := hx
        have hXX : X₀ = X := by
          have h₂ := h.ref hr
          rw [h'] at h₂
          cases h₂
          rfl
        subst hXX
        have href := Env.ref_agree hag x hr
        refine ⟨X₀, hr, ⟨w₂.1, by rw [href]; exact w₂.2⟩, ?_⟩
        exact (sat_mono (Env.diaPush_agree hag hr ⟨w₂.1, _⟩ w₂.2) φ).mp hsat
      · rintro ⟨X, hr, w₁, hsat⟩
        have href := Env.ref_agree hag x hr
        exact ⟨X, h.ref hr, ⟨w₁.1, by rw [← href]; exact w₁.2⟩,
          (sat_mono (Env.diaPush_agree hag hr w₁ _) φ).mpr hsat⟩

/-! ## Equality -/

/-- ⭐The defined equality holds exactly when the values are equal. -/
theorem sat_eqRec : ∀ {Γ : Ctx} {d : ℕ} {w : M.frame.W} (env : M.Env Γ w) (T : VarType)
    {a : Ann T} (t s : Term σ Γ T a),
    M.sat env (eqRec T t s : WFF σ Γ d) ↔ interp env t = interp env s
  | _, _, _, env, .Var, .var, t, s => iff_of_eq (congrArg (M.sat env) (eqRec_Var t s))
  | _, _, _, _, .VTypeOne, .one, .unit, .unit => ⟨fun _ => rfl, fun _ => trivial⟩
  | _, _, _, env, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change M.sat env (eqRec A t₁ s₁) ∧ M.sat env (eqRec B t₂ s₂) ↔
        (interp env t₁, interp env t₂) = (interp env s₁, interp env s₂)
      rw [sat_eqRec env A t₁ s₁, sat_eqRec env B t₂ s₂, Prod.mk.injEq]
  | _, _, w, env, .VTypeBox A, .box _, .boxtm t, .boxtm s => by
      change (∀ w' : M.frame.Acc w, M.sat (env.boxPush w') (eqRec A t s)) ↔ _
      rw [forall_congr' fun w' => sat_eqRec (env.boxPush w') A t s]
      constructor
      · intro hall
        apply M.nec_inj
        funext w'
        rw [box_beta, box_beta]
        exact hall w'
      · intro heq w'
        rw [← box_beta, ← box_beta, heq]
  | _, _, _, env, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s => by
      obtain ⟨X, hr⟩ := hx
      constructor
      · intro hno
        apply M.pos_inj
        rw [dia_beta env _ hr, dia_beta env _ hr]
        refine Sigma.ext rfl (heq_of_eq (funext fun w' => ?_))
        by_contra hne
        exact hno ⟨X, hr, w', fun hsat => hne ((sat_eqRec _ A t s).mp hsat)⟩
      · rintro heq ⟨X', hr', w', hneg⟩
        apply hneg
        have hpos := congrArg M.posEval heq
        rw [dia_beta env _ hr', dia_beta env _ hr'] at hpos
        exact (sat_eqRec _ A t s).mpr (congrFun (eq_of_heq (Sigma.mk.inj hpos).2) w')

end Model

end V12M
