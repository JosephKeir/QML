import QML.QML_v12m_EqHDef
import QML.QML_v12m_SemHere

/-!
# QML v12m — `≡` is identity (the model class with `Opt` on)

⭐`Model.sat_eqH`: with `Opt` on, `t ≡ s` holds exactly when the two terms denote the same
object, at every type and across annotations (docs §12.4).  By recursion on the type.  At `◇`
types the formula says the two witnesses are present along the same arrows, with `≡` contents
there, and possible objects are their sections: with `Opt` on there are no shapes
(`ModalSys.shaped_false_of_opt`), so `Model.pos_inj` is extensional.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-- ⭐**`≡` is identity.** -/
theorem sat_eqH (hO : ModalSys.Opt = true) : ∀ {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (T : VarType) {a b : Ann T} (t : Term σ Γ T a) (s : Term σ Γ T b),
    M.sat env (eqH hO T t s : WFF σ Γ 0) ↔ interp env t = interp env s
  | _, _, env, .Var, .var, .var, t, s => iff_of_eq (congrArg (M.sat env) (eqH_Var hO t s))
  | _, _, _, .VTypeOne, .one, .one, .unit, .unit => ⟨fun _ => rfl, fun _ => trivial⟩
  | _, _, env, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change M.sat env (eqH hO A t₁ s₁) ∧ M.sat env (eqH hO B t₂ s₂) ↔
        (interp env t₁, interp env t₂) = (interp env s₁, interp env s₂)
      rw [sat_eqH hO env A t₁ s₁, sat_eqH hO env B t₂ s₂, Prod.mk.injEq]
  | _, w, env, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => by
      change (∀ w' : M.frame.Acc w, M.sat (env.boxPush w') (eqH hO A t s)) ↔ _
      rw [forall_congr' fun w' => sat_eqH hO (env.boxPush w') A t s]
      constructor
      · intro hall
        apply M.nec_inj
        funext w'
        rw [box_beta, box_beta]
        exact hall w'
      · intro heq w'
        rw [← box_beta, ← box_beta, heq]
  | Γ, w, env, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t, .diatm _ hx' s => by
      obtain ⟨X, hr⟩ := id hx
      obtain ⟨X', hr'⟩ := id hx'
      have hw : Γ.boxIn.wit x = some X := Ctx.boxIn_wit.mpr ⟨hO, hr⟩
      have hw' : Γ.boxIn.wit x' = some X' := Ctx.boxIn_wit.mpr ⟨hO, hr'⟩
      -- The inner `≡`, read in the two `◇` views.
      have key : ∀ (a : M.frame.Acc w) (hm : a ∈ (M.posEval (env.ref x hr)).1)
          (hm' : a ∈ (M.posEval (env.ref x' hr')).1),
          M.sat (((env.boxPush a).optPush x hw hm).optPush x'
              ((Ctx.le_optIn _ x).wit _ _ hw') hm')
            (eqH hO A (Term.mono (Ctx.le_optIn _ x')
                (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t))
              (Term.mono ((Ctx.le_optIn _ x).optIn x')
                (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s)) : WFF σ _ 0) ↔
            interp (env.diaPush x hr ⟨a, hm⟩) t = interp (env.diaPush x' hr' ⟨a, hm'⟩) s := by
        intro a hm hm'
        rw [sat_eqH hO _ A,
          interp_mono (Env.agree_optPush _ ((Ctx.le_optIn _ x).wit _ _ hw') hm'),
          interp_mono (Env.diaPush_agree_optPush env hO hr ⟨a, hm⟩),
          interp_mono (Env.optPush_agree (Env.agree_optPush (env.boxPush a) hw hm) hw' hm' hm'
            rfl),
          interp_mono (Env.diaPush_agree_optPush env hO hr' ⟨a, hm'⟩)]
      have hsh : ∀ hS : ModalSys.shaped = true,
          M.shape hS (interp env (Term.diatm x hx t)) =
            M.shape hS (interp env (Term.diatm x' hx' s)) :=
        fun hS => absurd hS (by rw [ModalSys.shaped_false_of_opt hO]; decide)
      constructor
      · intro hsat
        have hboth : ∀ a : M.frame.Acc w, a ∈ (M.posEval (env.ref x hr)).1 ∨
            a ∈ (M.posEval (env.ref x' hr')).1 →
            ∃ (hm : a ∈ (M.posEval (env.ref x hr)).1)
              (hm' : a ∈ (M.posEval (env.ref x' hr')).1),
              interp (env.diaPush x hr ⟨a, hm⟩) t = interp (env.diaPush x' hr' ⟨a, hm'⟩) s := by
          intro a hor
          obtain ⟨X₁, h₁, hd₁, X₂, h₂, hd₂, hin⟩ := hsat a (hor.elim
            (fun hm => Or.inl ⟨X, hw, hm, trivial⟩) (fun hm' => Or.inr ⟨X', hw', hm', trivial⟩))
          obtain rfl : X = X₁ := Option.some.inj (hw.symm.trans h₁)
          obtain rfl : X' = X₂ :=
            Option.some.inj (((Ctx.le_optIn _ x).wit _ _ hw').symm.trans h₂)
          exact ⟨hd₁, hd₂, (key a hd₁ hd₂).mp hin⟩
        refine M.pos_inj ?_ hsh
        rw [dia_beta env hx hr, dia_beta env hx' hr']
        refine posSec_ext' (Set.ext fun a => ⟨fun hm => (hboth a (.inl hm)).2.1,
          fun hm' => (hboth a (.inr hm')).1⟩) fun a hm hm' => ?_
        exact (hboth a (.inl hm)).2.2
      · intro heq a hor
        have hpos := congrArg M.posEval heq
        rw [dia_beta env hx hr, dia_beta env hx' hr'] at hpos
        obtain ⟨hE, hf⟩ := posSec_of_eq hpos
        have hE' : ∀ a, a ∈ (M.posEval (env.ref x hr)).1 ↔ a ∈ (M.posEval (env.ref x' hr')).1 :=
          fun a => by
            have hE₀ : (M.posEval (env.ref x hr)).1 = (M.posEval (env.ref x' hr')).1 := hE
            rw [hE₀]
        have hm : a ∈ (M.posEval (env.ref x hr)).1 := by
          rcases hor with ⟨X₁, h₁, hd₁, -⟩ | ⟨X₂, h₂, hd₂, -⟩
          · obtain rfl : X = X₁ := Option.some.inj (hw.symm.trans h₁)
            exact hd₁
          · obtain rfl : X' = X₂ := Option.some.inj (hw'.symm.trans h₂)
            exact (hE' a).mpr hd₂
        have hm' := (hE' a).mp hm
        exact ⟨X, hw, hm, X', (Ctx.le_optIn _ x).wit _ _ hw', hm', (key a hm hm').mpr (hf a hm hm')⟩

end Model

end V12M
