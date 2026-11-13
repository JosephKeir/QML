import QML.QML_v12m_SemShape
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

variable {σ : Signature} {M : Model.{u, v} σ}

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
      by_cases hs : s.isStruct = true
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
  | .step u .keep =>
      have hk := Ctx.boxIn_keep hv
      change M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hk.1 hk.2.2) w (env.ref u hk.2.1))
          w' =
        M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hk.1 hk.2.2) w
          (env'.ref u (h.ref hk.2.1))) w'
      rw [Env.ref_agree hag u hk.2.1]
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
  | .step u .keep => exact Env.boxPush_agree hag w₁.1 (.step u .keep) T hv
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

/-- Two environments' witnesses agree along an inclusion of contexts. -/
def Env.WitAgree {Γ Γ' : Ctx} (h : Γ.Le Γ') {w : M.frame.W} (env : M.Env Γ w)
    (env' : M.Env Γ' w) : Prop :=
  ∀ y X (hy : Γ.wit y = some X), env.wit y X hy = env'.wit y X (h.wit y X hy)

theorem posPart_congr {X : VarType} {w : M.frame.W} {p q : M.frame.Dom (.VTypeDia X) w}
    (hpq : p = q) (w' : M.frame.Acc w) :
    (⟨w' ∈ (M.posEval p).1, fun hm => (M.posEval p).2 ⟨w', hm⟩⟩ : Part (M.frame.Dom X w'.1)) =
      ⟨w' ∈ (M.posEval q).1, fun hm => (M.posEval q).2 ⟨w', hm⟩⟩ := by
  subst hpq
  rfl

/-- Into a `□` the witnesses are read off the possible objects, so they agree when these do. -/
theorem Env.boxPush_witAgree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Env.Agree h env env') (w' : M.frame.Acc w) :
    Env.WitAgree h.boxIn (env.boxPush w') (env'.boxPush w') := fun y _ hy =>
  posPart_congr (Env.ref_agree hag y (Ctx.boxIn_wit.mp hy).2) w'

theorem Env.diaPush_witAgree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Env.Agree h env env') {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (w₁ : (M.posEval (env.ref x hr)).1)
    (hm : w₁.1 ∈ (M.posEval (env'.ref x (h.ref hr))).1) :
    Env.WitAgree (h.diaIn x) (env.diaPush x hr w₁) (env'.diaPush x (h.ref hr) ⟨w₁.1, hm⟩) :=
  Env.boxPush_witAgree hag w₁.1

theorem Env.optPush_agree {Γ Γ' : Ctx} {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Env.Agree h env env') {y : VarSymb} {X : VarType}
    (hy : Γ.wit y = some X) (hd : (env.wit y X hy).Dom) (hd' : (env'.wit y X (h.wit y X hy)).Dom)
    (hc : (env'.wit y X (h.wit y X hy)).get hd' = (env.wit y X hy).get hd) :
    Env.Agree (h.optIn y) (env.optPush y hy hd) (env'.optPush y (h.wit y X hy) hd') := by
  intro v T hv
  by_cases hvy : v = .step y .dia
  · subst hvy
    change (if hv' : VarSymb.step y .dia = .step y .dia then _ else _) =
      (if hv' : VarSymb.step y .dia = .step y .dia then _ else _)
    rw [dif_pos rfl, dif_pos rfl]
    have hXT : X = T := by rw [Ctx.optIn_content hy] at hv; exact Option.some.inj hv
    subst hXT
    exact hc.symm
  · change (if hv' : v = .step y .dia then _ else _) = (if hv' : v = .step y .dia then _ else _)
    rw [dif_neg hvy, dif_neg hvy]
    exact hag _ _ _

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
        refine M.pos_inj ?_ fun hSh => ?_
        · change M.posEval (interp env' (Term.diatm x _ (Term.mono (h.diaIn x) t))) = _
          rw [dia_beta env' _ (h.ref hr), dia_beta env _ hr]
          symm
          exact posSec_ext (Env.ref_agree hag x hr)
            (fun w₁ => interp (env.diaPush x hr w₁) t)
            (fun w₂ => interp (env'.diaPush x (h.ref hr) w₂) (Term.mono (h.diaIn x) t))
            (fun w₁ => (interp_mono (Env.diaPush_agree hag hr w₁ _) t).symm)
        · change domSh hSh (interp env' (Term.mono h (Term.diatm x _ t))) =
            domSh hSh (interp env (Term.diatm x _ t))
          rw [domSh_interp, domSh_interp]
          exact termShp_mono (fun v T hv => congrArg (domSh hSh) (hag v T hv)) 0 _
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
    (_hw : ModalSys.Opt = true → Env.WitAgree h env env' := by wit_triv) →
    (M.sat env' (WFF.mono h φ) ↔ M.sat env φ)
  | _, _, _, _, _, _, _, hag, .atom ρ, hw => relSat_mono hag ρ Fin.elim0
  | _, _, _, _, _, _, _, hag, .eq t s, hw => by
      change interp _ (Term.mono _ t) = interp _ (Term.mono _ s) ↔ _
      rw [interp_mono hag t, interp_mono hag s]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, .top, _ => Iff.rfl
  | _, _, _, _, _, _, _, _, .bot, _ => Iff.rfl
  | _, _, _, _, _, _, _, hag, .and φ ψ, hw => and_congr (sat_mono hag φ hw) (sat_mono hag ψ hw)
  | _, _, _, _, _, _, _, hag, .or φ ψ, hw => or_congr (sat_mono hag φ hw) (sat_mono hag ψ hw)
  | _, _, _, _, _, _, _, hag, .imp φ ψ, hw => imp_congr (sat_mono hag φ hw) (sat_mono hag ψ hw)
  | _, _, _, d, _, _, _, hag, .all _ φ, hw =>
      forall_congr' fun o => sat_mono (Env.extend_agree hag (.bnd d) o) φ hw
  | _, _, _, d, _, _, _, hag, .ex _ φ, hw =>
      exists_congr fun o => sat_mono (Env.extend_agree hag (.bnd d) o) φ hw
  | _, _, _, _, _, _, _, hag, .box φ, hw =>
      forall_congr' fun w' => sat_mono (Env.boxPush_agree hag w') φ
        (fun _ => Env.boxPush_witAgree hag w')
  | _, _, h, _, _, env, env', hag, .dia x hx φ, hw => by
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
        exact (sat_mono (Env.diaPush_agree hag hr ⟨w₂.1, _⟩ w₂.2) φ
          (fun _ => Env.diaPush_witAgree hag hr _ _)).mp hsat
      · rintro ⟨X, hr, w₁, hsat⟩
        have href := Env.ref_agree hag x hr
        exact ⟨X, h.ref hr, ⟨w₁.1, by rw [← href]; exact w₁.2⟩,
          (sat_mono (Env.diaPush_agree hag hr w₁ _) φ
          (fun _ => Env.diaPush_witAgree hag hr _ _)).mpr hsat⟩
  | _, _, h, _, _, env, env', hag, .optx hO .arrow y hy φ, hw => by
      have hw' := hw hO
      obtain ⟨X₀, hy₀⟩ := hy
      constructor
      · rintro ⟨X, h', hd, hsat⟩
        have hXX : X₀ = X := by
          have h₂ := h.wit y X₀ hy₀
          rw [h'] at h₂
          cases h₂
          rfl
        subst hXX
        have he := hw' y X₀ hy₀
        have hd₀ : (env.wit y X₀ hy₀).Dom := by rw [he]; exact hd
        have hc : (env'.wit y X₀ h').get hd = (env.wit y X₀ hy₀).get hd₀ :=
          Part.get_eq_of_mem (he ▸ Part.get_mem hd₀) hd
        exact ⟨X₀, hy₀, hd₀,
          (sat_mono (Env.optPush_agree hag hy₀ hd₀ hd hc) φ (fun _ => hw')).mp hsat⟩
      · rintro ⟨X, hy', hd, hsat⟩
        have he := hw' y X hy'
        have hd' : (env'.wit y X (h.wit y X hy')).Dom := by rw [← he]; exact hd
        refine ⟨X, h.wit y X hy', hd', ?_⟩
        have hc : (env'.wit y X (h.wit y X hy')).get hd' = (env.wit y X hy').get hd :=
          Part.get_eq_of_mem (he ▸ Part.get_mem hd) hd'
        exact (sat_mono (Env.optPush_agree hag hy' hd hd' hc) φ (fun _ => hw')).mpr hsat
  | _, _, _, _, _, _, _, _, .optx _ .ident _ hyI _, _ => (hyI.elim fun _ h => Ctx.witT_stage h).elim
  | _, _, _, _, _, _, _, hag, .here hT s t, hw => by
      change Model.Realised hT (interp _ (Term.mono _ s)) (interp _ (Term.mono _ t)) ↔ _
      rw [interp_mono hag s, interp_mono hag t]
      exact Iff.rfl
  | _, _, _, _, _, _, _, hag, .back hB L s t, hw => by
      change Model.Backs L (interp _ (Term.mono _ s)) (interp _ (Term.mono _ t)) ↔ _
      rw [interp_mono hag s, interp_mono hag t]
      exact Iff.rfl
  | _, _, _, d, _, _, _, hag, .retS hB S t Φ, hw =>
      exists_congr fun a => exists_congr fun e =>
        and_congr (sat_mono (Env.extend_agree (Env.boxPush_agree hag a) (.bnd d) e) Φ
          (fun _ => Env.boxPush_witAgree hag a))
          (by rw [interp_mono hag t])
  | _, _, h, d, _, env, env', hag, .retxS hB y hy S t Φ, hw => by
      constructor
      · rintro ⟨Y, h', a, e, hsat, hr⟩
        obtain ⟨Y₀, hy₀⟩ := hy
        have hYY : Y₀ = Y := by
          have h₂ := h.ref hy₀
          rw [h'] at h₂
          cases h₂
          rfl
        subst hYY
        have href := Env.ref_agree hag y hy₀
        refine ⟨Y₀, hy₀, ⟨a.1, by rw [href]; exact a.2⟩, e, ?_, ?_⟩
        · exact (sat_mono (Env.extend_agree (Env.diaPush_agree hag hy₀ ⟨a.1, _⟩ a.2) (.bnd d) e)
            Φ (fun _ => Env.diaPush_witAgree hag hy₀ _ _)).mp hsat
        · rw [interp_mono hag t] at hr
          exact hr
      · rintro ⟨Y, hr', a, e, hsat, hr⟩
        have href := Env.ref_agree hag y hr'
        refine ⟨Y, h.ref hr', ⟨a.1, by rw [← href]; exact a.2⟩, e,
          (sat_mono (Env.extend_agree (Env.diaPush_agree hag hr' a _) (.bnd d) e) Φ
            (fun _ => Env.diaPush_witAgree hag hr' _ _)).mpr hsat, ?_⟩
        rw [interp_mono hag t]
        exact hr
  | _, _, _, d, _, _, _, hag, .link hV hF t Φ, hw =>
      forall_congr' fun a => by
        rw [interp_mono hag t]
        exact sat_mono (Env.extend_agree (Env.boxPush_agree hag a) (.bnd d) _) Φ
          (fun _ => Env.boxPush_witAgree hag a)
  | _, _, h, d, _, env, env', hag, .linkx hV hF y hy t Φ, hw => by
      constructor
      · rintro ⟨Y, h', a, hsat⟩
        obtain ⟨Y₀, hy₀⟩ := hy
        have hYY : Y₀ = Y := by
          have h₂ := h.ref hy₀
          rw [h'] at h₂
          cases h₂
          rfl
        subst hYY
        have href := Env.ref_agree hag y hy₀
        refine ⟨Y₀, hy₀, ⟨a.1, by rw [href]; exact a.2⟩, ?_⟩
        rw [interp_mono hag t] at hsat
        exact (sat_mono (Env.extend_agree (Env.diaPush_agree hag hy₀ ⟨a.1, _⟩ a.2) (.bnd d) _)
          Φ (fun _ => Env.diaPush_witAgree hag hy₀ _ _)).mp hsat
      · rintro ⟨Y, hr', a, hsat⟩
        have href := Env.ref_agree hag y hr'
        refine ⟨Y, h.ref hr', ⟨a.1, by rw [← href]; exact a.2⟩, ?_⟩
        rw [interp_mono hag t]
        exact (sat_mono (Env.extend_agree (Env.diaPush_agree hag hr' a _) (.bnd d) _) Φ
          (fun _ => Env.diaPush_witAgree hag hr' _ _)).mpr hsat

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
        refine M.pos_inj ?_ fun hSh => ?_
        · rw [dia_beta env _ hr, dia_beta env _ hr]
          refine Sigma.ext rfl (heq_of_eq (funext fun w' => ?_))
          by_contra hne
          exact hno ⟨X, hr, w', fun hsat => hne ((sat_eqRec _ A t s).mp hsat)⟩
        · change domSh hSh (interp env (Term.diatm x _ t)) =
            domSh hSh (interp env (Term.diatm x _ s))
          rw [domSh_interp, domSh_interp]
          exact termShp_ann _ 0 _ _
      · rintro heq ⟨X', hr', w', hneg⟩
        apply hneg
        have hpos := congrArg M.posEval heq
        rw [dia_beta env _ hr', dia_beta env _ hr'] at hpos
        exact (sat_eqRec _ A t s).mpr (congrFun (eq_of_heq (Sigma.mk.inj hpos).2) w')
end Model

end V12M
