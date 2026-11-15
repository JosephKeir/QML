import QML.QML_v12m_SemCollapse
import QML.QML_v12m_ReadNames

/-!
# QML v12m — reading at names does not change values

The term-level semantics of `readNames` (docs §12.36, step 4), mirroring `SemCollapse`: two
environments **agree across a reading at names** when every address has, in the second, the value
it has in the first after renaming (`Env.ReadAgree`); the agreement passes into `□` and `◇` pushes;
and then ⭐`Model.interp_readNames`: a term read at the names has the value the term had.

With `Opt` on (where reading at names is used) possible objects carry no shapes, so the term case
needs no shape agreement.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-- Two environments at one world agree across a reading at names. -/
def Env.ReadAgree {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) {w : M.frame.W} (env₁ : M.Env Γ₁ w) (env₂ : M.Env Γ₂ w) :
    Prop :=
  ∀ v T (hv : Γ₁.ref v = some T), env₁.ref v hv = env₂.ref (v.readNames ν k) (h v T hv)

variable {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.ReadsNames ν k Γ₁ Γ₂}
  {w : M.frame.W} {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w}

/-- It suffices to check the visible non-projection addresses. -/
theorem Env.ReadAgree.of_raw
    (hvis : ∀ v T (hlp : v.lastProj = false) (hv : Γ₁ v = some T),
      env₁ v T hv = env₂.ref (v.readNames ν k) (h v T ((Ctx.ref_nonproj Γ₁ hlp).trans hv))) :
    Env.ReadAgree h env₁ env₂ := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · have hv₂ : Γ₂.ref (.step (v.readNames ν k) s) = some T := by
          rw [← VarSymb.readNames_struct hs]
          exact h _ T hv
        rw [Env.ref_congr env₂ (VarSymb.readNames_struct hs) _ hv₂, Env.ref, Env.ref, dif_pos hs,
          dif_pos hs]
        split
        · rename_i U hU
          split
          · rename_i U' hU'
            have hUU : U' = U := Option.some.inj (hU'.symm.trans (h v U hU))
            subst hUU
            rw [ih U' hU]
          · rename_i hU'
            exfalso
            rw [h v U hU] at hU'
            cases hU'
        · rename_i hU
          exfalso
          rw [Ctx.ref_step_proj Γ₁ v hs, hU] at hv
          cases hv
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [Env.ref, dif_neg hs]
        exact hvis _ _ hlp _

theorem Env.ReadAgree.boxPush (hag : Env.ReadAgree h env₁ env₂) (w' : M.frame.Acc w) :
    Env.ReadAgree h.boxIn (env₁.boxPush w') (env₂.boxPush w') := by
  refine Env.ReadAgree.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      rw [Env.ref_congr _ (VarSymb.readNames_level_succ (s := .box) rfl) _
        (Ctx.ref_boxIn_of hk (h u _ hu)), Env.ref,
        dif_neg (by decide : ¬ Step.box.isStruct = true)]
      change M.necEval (env₁.ref u hu) w' = M.necEval (env₂.ref (u.readNames ν k) (h u _ hu)) w'
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      rw [Env.ref_congr _ (VarSymb.readNames_level_succ (s := .keep) rfl) _
        (Ctx.ref_keep_of' hF (h u _ hu) hk), Env.ref,
        dif_neg (by decide : ¬ Step.keep.isStruct = true)]
      change M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF hk) w (env₁.ref u hu)) w' =
        M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF hk) w
          (env₂.ref (u.readNames ν k) (h u _ hu))) w'
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

theorem Env.ReadAgree.diaPush (hag : Env.ReadAgree h env₁ env₂) {x : VarSymb}
    {X : VarType} (hr : Γ₁.ref x = some (.VTypeDia X)) (w₁ : (M.posEval (env₁.ref x hr)).1)
    (hm : w₁.1 ∈ (M.posEval (env₂.ref (x.readNames ν k) (h x _ hr))).1) :
    Env.ReadAgree (h.diaIn x) (env₁.diaPush x hr w₁)
      (env₂.diaPush (x.readNames ν k) (h x _ hr) ⟨w₁.1, hm⟩) := by
  refine Env.ReadAgree.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      have hux : u = x := by
        change (if u = x then _ else none) = some T at hv
        split_ifs at hv with h'
        exact h'
      subst hux
      have hXT := Ctx.diaIn_step_dia hr hv
      subst hXT
      rw [Env.ref_congr _ (VarSymb.readNames_level_succ (s := .dia) rfl) _
        (Ctx.ref_diaIn_of (h u _ hr)), Env.ref, dif_neg (by decide : ¬ Step.dia.isStruct = true)]
      simp only [Env.diaPush]
      exact posEval_snd_congr (hag u _ hr) w₁ hm
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ₁) hv
      rw [Env.ref_congr _ (VarSymb.readNames_level_succ (s := .box) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_boxIn_of hk (h u _ hu))), Env.ref,
        dif_neg (by decide : ¬ Step.box.isStruct = true)]
      change M.necEval (env₁.ref u hu) w₁.1 =
        M.necEval (env₂.ref (u.readNames ν k) (h u _ hu)) w₁.1
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ₁) hv
      rw [Env.ref_congr _ (VarSymb.readNames_level_succ (s := .keep) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_keep_of' hF (h u _ hu) hk)), Env.ref,
        dif_neg (by decide : ¬ Step.keep.isStruct = true)]
      change M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF hk) w (env₁.ref u hu)) w₁.1 =
        M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF hk) w
          (env₂.ref (u.readNames ν k) (h u _ hu))) w₁.1
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

mutual
  theorem interpFunc_readNames (hO : ModalSys.Opt = true) {ν : VarSymb → Option VarSymb}
      {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.ReadsNames ν k Γ₁ Γ₂} {w : M.frame.W}
      {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hag : Env.ReadAgree h env₁ env₂) :
      ∀ {n : ℕ} (g : Func σ Γ₁ n) (args : Fin n → M.frame.D w),
        interpFunc env₂ (Func.readNames h g) args = interpFunc env₁ g args
    | _, .F _, _ => rfl
    | _, .eval g t, args => by
        change interpFunc env₂ (Func.readNames h g)
            (Fin.cons (interp env₂ (Term.readNames h t)) args) =
          interpFunc env₁ g (Fin.cons (interp env₁ t) args)
        rw [interp_readNames hO hag t, interpFunc_readNames hO hag g]

  /-- ⭐**Reading at names does not change values**, in agreeing environments. -/
  theorem interp_readNames (hO : ModalSys.Opt = true) {ν : VarSymb → Option VarSymb} {k : ℕ}
      {Γ₁ Γ₂ : Ctx} {h : Ctx.ReadsNames ν k Γ₁ Γ₂} {w : M.frame.W}
      {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hag : Env.ReadAgree h env₁ env₂) :
      ∀ {T : VarType} {a : Ann T} (t : Term σ Γ₁ T a),
        interp env₂ (Term.readNames h t) = interp env₁ t
    | _, _, .var v hv => (hag v _ hv).symm
    | _, _, .func f => interpFunc_readNames hO hag f Fin.elim0
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change (interp env₂ (Term.readNames h s), interp env₂ (Term.readNames h t)) =
          (interp env₁ s, interp env₁ t)
        rw [interp_readNames hO hag s, interp_readNames hO hag t]
    | _, _, .boxtm t => by
        apply M.nec_inj
        funext w'
        change M.necEval (interp env₂ (Term.boxtm (Term.readNames h.boxIn t))) w' = _
        rw [box_beta, box_beta, interp_readNames hO (hag.boxPush w') t]
    | _, _, .diatm x hx t => by
        obtain ⟨X, hr⟩ := hx
        refine M.pos_inj ?_ fun hSh => absurd hO (by rw [ModalSys.noOpt_of_shaped hSh]; decide)
        change M.posEval (interp env₂
          (Term.diatm (x.readNames ν k) _ (Term.readNames (h.diaIn x) t))) = _
        rw [dia_beta env₂ _ (h x _ hr), dia_beta env₁ _ hr]
        exact posSec_ext (hag x _ hr).symm
          (fun w₂ => interp (env₂.diaPush (x.readNames ν k) (h x _ hr) w₂)
            (Term.readNames (h.diaIn x) t))
          (fun w₁ => interp (env₁.diaPush x hr w₁) t)
          (fun w₂ => interp_readNames hO (hag.diaPush hr ⟨w₂.1, (hag x _ hr).symm ▸ w₂.2⟩ w₂.2) t)
end

end Model

end V12M
