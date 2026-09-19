import QML.QML_v12m_BCanonDom

/-!
# QML v12m — B's canonical model: the function algebra

The function algebra acts on raw objects (`rawEval`) as in the staged model; `extract` and `dup`
do not arise (no T, no 4).  ⭐`rden_applyG`: denoting a map applied to a term is applying the map to
the denotation.  Along an arrow this is `applyG_subst` — applying a map commutes with translation —
and for `strength` the witness arrow agrees with the plain arrow on the `□` view
(`subst_arrowX_box`).  So definable objects are closed under the algebra (`definable_rawEval`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoTFour] {B : BData σ}

theorem noT : ModalSys.T = true → False := fun h => by
  rw [ModalSys.NoTFour.noT] at h
  cases h

theorem noFour : ModalSys.Four = true → False := fun h => by
  rw [ModalSys.NoTFour.noFour] at h
  cases h

variable (B)

/-- ⭐The function algebra on raw objects. -/
noncomputable def rawEval :
    {A C : VarType} → GFunc σ A C → (s : B.W) → B.RDom A s → B.RDom C s
  | _, _, .id _, _, o => o
  | _, _, .comp g f, s, o => rawEval g s (rawEval f s o)
  | _, _, .fst, _, o => o.1
  | _, _, .snd, _, o => o.2
  | _, _, .pair f g, s, o => (rawEval f s o, rawEval g s o)
  | _, _, .unit _, _, _ => PUnit.unit
  | _, _, .func f args, s, o => (B.w s).canonFunc f (fun k => rawEval (args k) s o)
  | _, _, .boxMap f, _, o => fun a => rawEval f a.1 (o a)
  | _, _, .boxPair _ _, _, o => fun a => (o.1 a, o.2 a)
  | _, _, .boxUnit, _, _ => fun _ => PUnit.unit
  | _, _, .diaMap f, _, o => ⟨o.1, fun a => rawEval f a.1.1 (o.2 a)⟩
  | _, _, .strength _ _, _, o => ⟨o.2.1, fun a => (o.1 a.1, o.2.2 a)⟩
  | _, _, .extract hT, _, _ => (noT hT).elim
  | _, _, .dup hF, _, _ => (noFour hF).elim

variable {B}

theorem rden_varTerm {Γ : Ctx} (s : B.W) (i : ℕ) (e : Γ.Le ((B.w s).ctx i)) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b), B.rden s i e (Canon.varTerm p) = B.rden s i e p.2
  | ⟨.var, _⟩ => rfl

theorem rden_var_mono {Γ : Ctx} {s : B.W} {i : ℕ} (e : Γ.Le ((B.w s).ctx i)) :
    ∀ u : Term σ Γ .Var .var, B.rden s i e u = (B.w s).cls i (Term.mono e u)
  | .var _ _ => rfl
  | .func _ => rfl

/-- The witness arrow agrees with the plain arrow on the `□` view. -/
theorem subst_arrowX_box {Γ : Ctx} {Δ : Ctx} {img : ℕ → ℕ} {x : VarSymb} {cx : ℕ}
    (hθ : Subst.Ok (Γ.diaIn x) (arrowXS σ Δ img x cx))
    (hc : Subst.Coh (arrowXIdx img x cx) (Γ.diaIn x) (arrowXS σ Δ img x cx))
    (hθ' : Subst.Ok Γ.boxIn (arrowS σ Δ img)) (hc' : Subst.Coh (arrowIdx img) Γ.boxIn
      (arrowS σ Δ img)) {A : VarType} {a : Ann A} (b : Term σ Γ.boxIn A a) :
    (⟨_, Term.subst (arrowXIdx img x cx) (arrowXS σ Δ img x cx) hθ hc
        (Term.mono (Ctx.le_boxIn_diaIn Γ x) b)⟩ : Σ a', Term σ Δ A a') =
      ⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) hθ' hc' b⟩ := by
  rw [Term.subst_mono]
  refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v T _ hv => ?_) b
  match v with
  | .step u .box => exact .refl _
  | .step u .keep =>
      obtain ⟨hF, _⟩ := Ctx.boxIn_keep hv
      exact (noFour hF).elim
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- ⭐Denoting a map applied to a term is applying the map to the denotation. -/
theorem rden_applyG :
    ∀ {A C : VarType} (g : GFunc σ A C) {Γ : Ctx} {a : Ann A} (t : Term σ Γ A a)
      (s : B.W) (i : ℕ) (e : Γ.Le ((B.w s).ctx i)),
    B.rden s i e (Canon.applyG g t).2 = B.rawEval g s (B.rden s i e t)
  | _, _, .id _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, t, s, i, e =>
      (rden_applyG g _ s i e).trans (congrArg (B.rawEval g s) (rden_applyG f t s i e))
  | _, _, .fst, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .snd, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .pair f g, _, _, t, s, i, e =>
      Prod.ext (rden_applyG f t s i e) (rden_applyG g t s i e)
  | _, _, .unit _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, t, s, i, e => by
      change B.rden s i e (.func _) =
        (B.w s).canonFunc f (fun k => B.rawEval (args k) s (B.rden s i e t))
      have hk : (fun k => B.rawEval (args k) s (B.rden s i e t)) =
          fun k => (B.w s).cls i (Term.mono e (Canon.varTerm (Canon.applyG (args k) t))) := by
        funext k
        rw [← rden_applyG (args k) t s i e, ← rden_varTerm, rden_var_mono]
      rw [hk, BWorld.canonFunc_cls, rden_var_mono, Term.mono_fill, Spine.mono_ofFn]
      rfl
  | _, _, .boxMap f, _, _, .boxtm b, s, i, e => funext fun a => by
      change B.rden a.1 _ _ (Term.subst _ _ _ _ (Canon.applyG f b).2) =
        B.rawEval f a.1 (B.rden a.1 _ _ (Term.subst _ _ _ _ b))
      rw [← rden_applyG f _ a.1 _ _, Canon.applyG_subst]
  | _, _, .boxPair _ _, _, _, .pair (.boxtm b) (.boxtm c), _, _, _ => rfl
  | _, _, .boxUnit, _, _, .unit, _, _, _ => rfl
  | _, _, .diaMap f, _, _, .diatm x hx c, s, i, e =>
      congrArg (Sigma.mk _) (funext fun a => by
        change B.rden a.1.1 _ _ (Term.subst _ _ _ _ (Canon.applyG f c).2) =
          B.rawEval f a.1.1 (B.rden a.1.1 _ _ (Term.subst _ _ _ _ c))
        rw [← rden_applyG f _ a.1.1 _ _, Canon.applyG_subst])
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c), s, i, e =>
      congrArg (Sigma.mk _) (funext fun a => by
        change (B.rden a.1.1 _ _ (Term.subst _ _ _ _ (Term.mono (Ctx.le_boxIn_diaIn Γ x) b)),
          B.rden a.1.1 _ _ (Term.subst _ _ _ _ c)) =
          (B.rden a.1.1 _ _ (Term.subst _ _ _ _ b), B.rden a.1.1 _ _ (Term.subst _ _ _ _ c))
        refine Prod.ext ?_ rfl
        exact rden_sigma _ (subst_arrowX_box _ _ _ _ b))
  | _, _, .extract hT, _, _, _, _, _, _ => (noT hT).elim
  | _, _, .dup hF, _, _, _, _, _, _ => (noFour hF).elim

/-- ⭐Definable objects are closed under the function algebra. -/
theorem definable_rawEval {A C : VarType} (g : GFunc σ A C) {s : B.W} {o : B.RDom A s}
    (h : B.Definable A s o) : B.Definable C s (B.rawEval g s o) := by
  obtain ⟨i, a, t, rfl⟩ := h
  exact ⟨i, _, (Canon.applyG g t).2, rden_applyG g t s i _⟩

end BData

end BArrow

end V12M
