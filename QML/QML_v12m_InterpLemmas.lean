import QML.QML_v12m_Interp

/-!
# QML v12m — the interpretation: compilation is faithful, and the β laws

* `Term.compile_eval`: a compiled term, evaluated on the tuple of a support, is the term's value.
* ⭐`box_beta`: a necessary term's value at an accessible world is its body's value there.
* ⭐`dia_beta`: a possible term's extent is its witness's, and its content at each world of that
  extent is its body's value there.

After these, the compilation is an implementation detail: every later lemma uses the β laws.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u} σ}

theorem eval_ofEq {A B : VarType} (h : A = B) {w : M.frame.W} (a : M.frame.Dom A w) :
    GFunc.eval M.ops (GFunc.ofEq (σ := σ) h) w a =
      cast (congrArg (fun T => M.frame.Dom T w) h) a := by
  subst h
  rfl

theorem eval_proj {U T : VarType} {s : Step} (hs : s.isProj = true) (h : U.step s = some T)
    {w : M.frame.W} (a : M.frame.Dom U w) :
    GFunc.eval M.ops (GFunc.proj (σ := σ) hs h) w a = M.stepObj hs h a := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · obtain ⟨hT, rfl⟩ := VarType.step_here h
    exact M.necExtract_eval hT a

theorem lookup_eval {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ (L : Supp Δ) (v : VarSymb) {T : VarType} (h : Δ v = some T)
      (hm : v ∈ List.map PSigma.fst L),
      GFunc.eval M.ops (Supp.lookup (σ := σ) L v h hm) w (env.bundle L) = env v T h
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | ⟨v', T', h'⟩ :: L, v, T, h, hm => by
      by_cases hvv : v' = v
      · subst hvv
        have hT : T' = T := Option.some.inj (h'.symm.trans h)
        subst hT
        rw [Supp.lookup, dif_pos rfl]
        simp only [GFunc.eval, eval_ofEq, cast_eq, Env.bundle]
      · rw [Supp.lookup, dif_neg hvv]
        simp only [GFunc.eval, Env.bundle]
        exact lookup_eval env L v h _

theorem refGF_eval {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (L : Supp Δ) :
    ∀ (v : VarSymb) {T : VarType} (h : Δ.ref v = some T)
      (hm : v.base ∈ List.map PSigma.fst L),
      GFunc.eval M.ops (Supp.refGF (σ := σ) L v h hm) w (env.bundle L) = env.ref v h
  | .root r, _, h, hm => lookup_eval env L (.root r) h hm
  | .step v s, T, h, hm => by
      by_cases hs : s.isProj = true
      · rw [Supp.refGF, Env.ref, dif_pos hs, dif_pos hs]
        split
        · rename_i U hU
          simp only [GFunc.eval]
          rw [refGF_eval env L v hU, eval_proj]
          split
          · rename_i U' hU'
            have hUU : U = U' := Option.some.inj (hU.symm.trans hU')
            subst hUU
            rfl
          · rename_i hU'
            exfalso
            rw [hU] at hU'
            cases hU'
        · rename_i hU
          exfalso
          rw [Ctx.ref_step_proj Δ v hs, hU] at h
          cases h
      · rw [Supp.refGF, Env.ref, dif_neg hs, dif_neg hs]
        exact lookup_eval env L _ _ _

theorem gatherBox_eval {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (L : Supp Δ) :
    ∀ (L' : Supp Δ.boxIn) (hL : ∀ e ∈ Supp.outerBox L', e.1 ∈ List.map PSigma.fst L),
      GFunc.eval M.ops (Supp.gatherBox (σ := σ) L L' hL) w (env.bundle L) = env.necBundle L'
  | [], _ => rfl
  | ⟨.step u .box, T, h⟩ :: L', hL => by
      simp only [Supp.gatherBox, GFunc.eval, Env.necBundle]
      rw [refGF_eval, gatherBox_eval env L L']
  | ⟨.step u .keep, T, h⟩ :: L', hL => by
      simp only [Supp.gatherBox, GFunc.eval, Env.necBundle]
      rw [refGF_eval, gatherBox_eval env L L']
  | ⟨.root _, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .fst, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .snd, _, h⟩ :: _, _ => by cases h
  | ⟨.step _ .dia, _, h⟩ :: _, _ => by cases h

theorem necBundle_eval {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (w' : M.frame.Acc w) :
    ∀ (L : Supp Δ.boxIn), M.necEval (env.necBundle L) w' = (env.boxPush w').bundle L
  | [] => rfl
  | ⟨.step u .box, T, h⟩ :: L =>
      (M.necPair_eval _ _ w').trans (Prod.ext rfl (necBundle_eval env w' L))
  | ⟨.step u .keep, T, h⟩ :: L =>
      (M.necPair_eval _ _ w').trans (Prod.ext rfl (necBundle_eval env w' L))
  | ⟨.root _, _, h⟩ :: _ => by cases h
  | ⟨.step _ .fst, _, h⟩ :: _ => by cases h
  | ⟨.step _ .snd, _, h⟩ :: _ => by cases h
  | ⟨.step _ .dia, _, h⟩ :: _ => by cases h

theorem assemble_eval {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {x : VarSymb} {X : VarType}
    (hr : Δ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x hr)).1) :
    ∀ (L : Supp (Δ.diaIn x)),
      GFunc.eval M.ops (Supp.assemble (σ := σ) hr L) w'.1.1
          (((env.boxPush w'.1).bundle (Supp.boxPart L), (M.posEval (env.ref x hr)).2 w') :
            M.frame.Dom (.VTypeProd (Supp.ty (Supp.boxPart L)) X) w'.1.1) =
        (env.diaPush x hr w').bundle L
  | [] => rfl
  | ⟨.step u .box, T, h⟩ :: L =>
      Prod.ext rfl (assemble_eval env hr w' L)
  | ⟨.step u .keep, T, h⟩ :: L =>
      Prod.ext rfl (assemble_eval env hr w' L)
  | ⟨.step u .dia, T, h⟩ :: L => by
      have hXT := Ctx.diaIn_step_dia hr h
      subst hXT
      refine Prod.ext ?_ (assemble_eval env hr w' L)
      simp only [Supp.assemble, GFunc.eval, eval_ofEq, cast_eq]
      rfl
  | ⟨.root _, _, h⟩ :: _ => by cases h
  | ⟨.step _ .fst, _, h⟩ :: _ => by cases h
  | ⟨.step _ .snd, _, h⟩ :: _ => by cases h

mutual
  theorem Func.compile_eval {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (L : Supp Δ) :
      ∀ {n : ℕ} (g : Func σ Δ n) (hL : ∀ e ∈ Func.bases g, e.1 ∈ List.map PSigma.fst L)
        (args : Fin n → GFunc σ (Supp.ty L) .Var),
      GFunc.eval M.ops (Func.compile L g hL args) w (env.bundle L) =
        interpFunc env g (fun i => GFunc.eval M.ops (args i) w (env.bundle L))
    | _, .F _, _, _ => rfl
    | _, .eval g t, hL, args => by
        rw [Func.compile, Func.compile_eval env L g]
        simp only [interpFunc]
        congr 1
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          exact Term.compile_eval env L t _
        · simp only [Fin.cons_succ]

  /-- ⭐Compilation is faithful. -/
  theorem Term.compile_eval {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (L : Supp Δ) :
      ∀ {T : VarType} {a : Ann T} (t : Term σ Δ T a)
        (hL : ∀ e ∈ Term.bases t, e.1 ∈ List.map PSigma.fst L),
      GFunc.eval M.ops (Term.compile L t hL) w (env.bundle L) = interp env t
    | _, _, .var v hv, _ => refGF_eval env L v hv _
    | _, _, .func f, hL => by
        rw [Term.compile, Func.compile_eval env L f]
        simp only [interp]
        congr 1
        funext i
        exact i.elim0
    | _, _, .unit, _ => rfl
    | _, _, .pair s t, hL => by
        simp only [Term.compile, GFunc.eval, interp]
        rw [Term.compile_eval env L s, Term.compile_eval env L t]
    | _, _, .boxtm t, hL => by
        simp only [Term.compile, GFunc.eval, interp]
        rw [gatherBox_eval]
    | _, _, .diatm x hx t, hL => by
        simp only [Term.compile, interp]
        split
        · simp only [GFunc.eval]
          rw [gatherBox_eval, refGF_eval]
        all_goals
          rename_i heq
          exfalso
          obtain ⟨_, h⟩ := hx
          rw [heq] at h
          cases h
end

/-- ⭐**Box β**: a necessary term, read at an accessible world, is its body there. -/
theorem box_beta {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {A : VarType} {a : Ann A}
    (t : Term σ Δ.boxIn A a) (w' : M.frame.Acc w) :
    M.necEval (interp env (Term.boxtm t)) w' = interp (env.boxPush w') t := by
  simp only [interp]
  rw [M.necMap_eval, necBundle_eval, Term.compile_eval]

/-- ⭐**Diamond β**: a possible term has its witness's extent, and at each world of it the
    body's value. -/
theorem dia_beta {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {x : VarSymb} {X : VarType}
    (hx : ∃ X, Δ.ref x = some (.VTypeDia X)) (hr : Δ.ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (t : Term σ (Δ.diaIn x) A a) :
    M.posEval (interp env (Term.diatm x hx t)) =
      ⟨(M.posEval (env.ref x hr)).1, fun w' => interp (env.diaPush x hr w') t⟩ := by
  simp only [interp]
  split
  · rename_i X' hr'
    have hXX : X' = X := by
      rw [hr] at hr'
      cases hr'
      rfl
    subst hXX
    rw [M.posMap_eval, M.posMap_eval, M.posStrength_eval]
    refine Sigma.ext rfl (heq_of_eq (funext fun w' => ?_))
    dsimp only
    rw [necBundle_eval, assemble_eval, Term.compile_eval]
  all_goals
    rename_i heq
    exfalso
    rw [hr] at heq
    cases heq

end Model

end V12M
