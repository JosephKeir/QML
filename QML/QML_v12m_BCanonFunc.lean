import QML.QML_v12m_BCanonDom

/-!
# QML v12m — B's canonical model: the function algebra

The function algebra acts on raw objects (`rawEval`) as in the staged model; `extract` reads a
necessary object at the world's own arrow (under T), and `dup` does not arise (4 is off).
⭐`rden_applyG`: denoting a map applied to a term is applying the map to
the denotation.  Along an arrow this is `applyG_subst` — applying a map commutes with translation —
and for `strength` the witness arrow agrees with the plain arrow on the `□` view
(`subst_arrowX_box`).  So definable objects are closed under the algebra (`definable_rawEval`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFour] {B : BData σ}

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
  | _, _, .diaMap f, _, o =>
      ⟨o.1, fun a => rawEval f a.1.1 (o.2 a),
        fun hSh => .dia (o.3 hSh).label (GFunc.shp f 1 (o.3 hSh).body)⟩
  | _, _, .strength _ _, _, o =>
      ⟨o.2.1, fun a => (o.1 a.1, o.2.2 a),
        fun hSh => .dia (o.2.3 hSh).label
          (.prod (Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb)
            fun a => B.rawShape hSh (o.1 a)) (o.2.3 hSh).body)⟩
  | _, _, .extract hT, s, o => o ⟨s, ⟨Or.inr ⟨hT, rfl⟩⟩⟩
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

/-- Applying a definable map commutes with realising under a world's own arrow. -/
theorem applyG_realTerm {A C : VarType} (g : GFunc σ A C) {s : B.W} {x : VarSymb}
    (hr : (B.w s).Realised x) {Γ : Ctx} {i : ℕ} (e : Γ.Le ((B.w s).ctx i))
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    B.realTerm hr e hx (Canon.applyG g t).2 = Canon.applyG g (B.realTerm hr e hx t).2 := by
  simp only [realTerm]
  rw [Canon.applyG_realiseAtA, Canon.applyG_mono]

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
  | _, _, .boxMap f, Γ, _, .boxtm b, s, i, e => funext fun a => by
      change B.rden s i e (.boxtm (Canon.applyG f b).2) a =
        B.rawEval f a.1 (B.rden s i e (.boxtm b) a)
      by_cases hR : B.R s a.1
      · simp only [rden, dif_pos hR]
        rw [← rden_applyG f _ a.1 _ _, Canon.applyG_subst]
      · simp only [rden, dif_neg hR]
        exact (rden_sigma _ (Canon.applyG_collapse f
          (Ctx.collapses_boxIn_self (self_of_not_R hR).1 Γ) b)).symm.trans
          (rden_applyG f _ a.1 i _)
  | _, _, .boxPair _ _, _, _, .pair (.boxtm b) (.boxtm c), s, i, e => funext fun a => by
      change B.rden s i e (.boxtm (.pair b c)) a =
        (B.rden s i e (.boxtm b) a, B.rden s i e (.boxtm c) a)
      by_cases hR : B.R s a.1
      · simp only [rden, dif_pos hR]
        rfl
      · simp only [rden, dif_neg hR]
        rfl
  | _, _, .boxUnit, _, _, .unit, _, _, _ => rfl
  | _, _, .diaMap f, Γ, _, .diatm x hx c, s, i, e =>
      RPos.congr_cont (funext fun a => by
        by_cases hk : ∃ X, B.kd s a.1.1 = some (x, X)
        · simp only [rden, dif_pos hk]
          rw [← rden_applyG f _ a.1.1 _ _, Canon.applyG_subst]
        · simp only [rden, dif_neg hk]
          exact (rden_sigma _ (applyG_realTerm f _ e hx c)).trans (rden_applyG f _ a.1.1 _ _))
        fun _ => Canon.termShp_applyG (.diaMap f) (.diatm x hx c) (B.cEnv Γ s) 0
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c), s, i, e =>
      RPos.congr_cont (funext fun a => by
        change _ = (B.rden s i e (.boxtm b) a.1, (B.rden s i e (.diatm x hx c)).2 a)
        by_cases hk : ∃ X, B.kd s a.1.1 = some (x, X)
        · have hR : B.R s a.1.1 := B.kdR hk.choose_spec
          simp only [rden, dif_pos hk, dif_pos hR]
          refine Prod.ext ?_ rfl
          exact rden_sigma _ (subst_arrowX_box _ _ _ _ b)
        · obtain ⟨hnR, hr⟩ := mem_extent_self a.2 hk
          simp only [rden, dif_neg hk, dif_neg hnR]
          rw [rden_realTerm_pair]
          refine Prod.ext ?_ rfl
          exact rden_realTerm_mono_boxIn hr e hx b _ _)
        fun hSh =>
          (Canon.termShp_applyG (.strength _ _) (.pair (.boxtm b) (.diatm x hx c))
            (B.cEnv Γ s) 0).trans (by
            change _ = Shp.dia _ (Shp.prod (B.rawShape hSh (B.rden s i e (.boxtm b))).inner _)
            rw [rawShape_rden hSh s i e (.boxtm b)]
            rfl)
  | _, _, .extract hT, _, _, .boxtm b, s, i, e => by
      change B.rden s i e (Term.collapse _ b) = B.rden s i e (.boxtm b) ⟨s, ⟨Or.inr ⟨hT, rfl⟩⟩⟩
      simp only [rden, dif_neg (B.irrefl s)]
  | _, _, .dup hF, _, _, _, _, _, _ => (noFour hF).elim

/-- ⭐Definable objects are closed under the function algebra. -/
theorem definable_rawEval {A C : VarType} (g : GFunc σ A C) {s : B.W} {o : B.RDom A s}
    (h : B.Definable A s o) : B.Definable C s (B.rawEval g s o) := by
  obtain ⟨i, a, t, rfl⟩ := h
  exact ⟨i, _, (Canon.applyG g t).2, rden_applyG g t s i _⟩

end BData

end BArrow

end V12M
