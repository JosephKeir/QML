import QML.QML_v12m_SemLemmas
import QML.QML_v12m_SubstCongr

/-!
# QML v12m — semantics of collapsing (weak T)

Collapsing moves syntax from a `□` view to the current level.  Semantically it changes nothing,
provided the two environments agree across the collapse (`Env.CollapseAgree`): every reachable
address of the view has the value of its collapsed address.

* Agreement passes into `□` and `◇_x` views and under binders.
* ⭐`Env.collapseAgree_self`: under T, the `□` view pushed to the current world itself (reflexivity)
  agrees with the environment across the collapse — `u.box` there is `u` evaluated here, which is
  `u.here`.
* ⭐`interp_collapse`, ⭐`sat_collapse`; hence `sat_boxHere`, the semantic content of the T rule.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-! ## Environment helpers -/

theorem Env.ref_congr {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {v v' : VarSymb} (e : v = v')
    {T : VarType} (h : Γ.ref v = some T) (h' : Γ.ref v' = some T) :
    env.ref v h = env.ref v' h' := by
  subst e
  rfl

/-- Pushed into `□`, the contents address of `u` holds `u` evaluated at the accessible world.
    (Under T and 4 it is the kept copy read there, by `necDup_eval`.) -/
theorem Env.ref_inner {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (w' : M.frame.Acc w)
    {u : VarSymb} {A : VarType} (hu : Γ.ref u = some (.VTypeBox A))
    (h : Γ.boxIn.ref u.inner = some A) :
    (env.boxPush w').ref u.inner h = M.necEval (env.ref u hu) w' := by
  cases hk : ModalSys.keepOnly with
  | false =>
      rw [Env.ref_congr _ (VarSymb.inner_box hk) _ (Ctx.ref_boxIn_of hk hu), Env.ref,
        dif_neg (by decide : ¬ Step.box.isProj = true)]
      rfl
  | true =>
      obtain ⟨hT, hF⟩ := ModalSys.keepOnly_flags hk
      have hkeep : Γ.boxIn.ref (.step u .keep) = some (.VTypeBox A) := Ctx.ref_keep_of hF hu
      have hhs : Step.here.isProj = true := rfl
      rw [Env.ref_congr _ (VarSymb.inner_keepOnly hk) _ (Ctx.ref_here_of hT hkeep), Env.ref,
        dif_pos hhs]
      split
      · rename_i U hU
        have hUU : U = .VTypeBox A := Option.some.inj (hU.symm.trans hkeep)
        subst hUU
        change M.necEval (M.necEval (M.ops.necDup hF (env.ref u hu)) w')
          ⟨w'.1, ⟨M.frame.refl hT w'.1⟩⟩ = _
        rw [M.necDup_eval, M.frame.trans_refl hT hF]
      · rename_i hU
        exfalso
        rw [hU] at hkeep
        cases hkeep

theorem Env.ref_of_nonproj {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    ∀ {v : VarSymb} {T : VarType} (_hlp : v.lastProj = false) (h : Γ.ref v = some T)
      (h' : Γ v = some T), env.ref v h = env v T h'
  | .root _, _, _, _, _ => rfl
  | .step v s, T, hlp, h, h' => by
      have hs : ¬ s.isProj = true := fun hh => by
        change s.isProj = false at hlp
        rw [hh] at hlp
        cases hlp
      rw [Env.ref, dif_neg hs]

theorem Env.extend_root {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) (h : (Γ.insert r T) (.root r) = some T) :
    env.extend r o (.root r) T h = o := by
  unfold Env.extend
  rw [dif_pos rfl]

theorem Env.extend_ne {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) {v : VarSymb} {U : VarType} (h : (Γ.insert r T) v = some U)
    (hvr : v ≠ .root r) (h' : Γ v = some U) : env.extend r o v U h = env v U h' := by
  unfold Env.extend
  rw [dif_neg hvr]

/-- Declaring a root does not change the value of an address rooted elsewhere. -/
theorem Env.ref_extend_ne {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {r : Root} {T : VarType}
    (o : M.frame.Dom T w) :
    ∀ {v : VarSymb} {U : VarType} (hv : (Γ.insert r T).ref v = some U) (hv' : Γ.ref v = some U),
      v.rt ≠ r → (env.extend r o).ref v hv = env.ref v hv'
  | .root r', U, hv, hv', hne => by
      change (env.extend r o) (.root r') U hv = env (.root r') U hv'
      exact Env.extend_ne env r o hv (fun he => hne (by cases he; rfl)) hv'
  | .step v s, U, hv, hv', hne => by
      have hne' : v.rt ≠ r := hne
      by_cases hs : s.isProj = true
      · rw [Env.ref, Env.ref, dif_pos hs, dif_pos hs]
        split
        · rename_i U₁ hU₁
          split
          · rename_i U₂ hU₂
            have hUU : U₂ = U₁ := by
              rw [Ctx.ref_insert_ne T hne'] at hU₁
              exact Option.some.inj (hU₂.symm.trans hU₁)
            subst hUU
            rw [Env.ref_extend_ne env o hU₁ hU₂ hne']
          · rename_i hU₂
            exfalso
            rw [Ctx.ref_insert_ne T hne'] at hU₁
            rw [hU₁] at hU₂
            cases hU₂
        · rename_i hU₁
          exfalso
          rw [Ctx.ref_step_proj _ v hs, hU₁] at hv
          cases hv
      · rw [Env.ref, Env.ref, dif_neg hs, dif_neg hs]
        exact Env.extend_ne env r o _ (fun he => by cases he) _

/-! ## Agreement across a collapse -/

/-- Two environments at one world agree across a collapse. -/
def Env.CollapseAgree {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) {w : M.frame.W}
    (env₁ : M.Env Γ₁ w) (env₂ : M.Env Γ₂ w) : Prop :=
  ∀ v T (hv : Γ₁.ref v = some T), env₁.ref v hv = env₂.ref (v.collapse k) (h v T hv)

variable {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {w : M.frame.W}
  {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w}

/-- It suffices to check the visible non-projection addresses. -/
theorem Env.CollapseAgree.of_raw
    (hvis : ∀ v T (hlp : v.lastProj = false) (hv : Γ₁ v = some T),
      env₁ v T hv = env₂.ref (v.collapse k) (h v T ((Ctx.ref_nonproj Γ₁ hlp).trans hv))) :
    Env.CollapseAgree h env₁ env₂ := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · have hv₂ : Γ₂.ref (.step (v.collapse k) s) = some T := by
          rw [← VarSymb.collapse_proj hs]
          exact h _ T hv
        rw [Env.ref_congr env₂ (VarSymb.collapse_proj hs) _ hv₂, Env.ref, Env.ref, dif_pos hs,
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

theorem Env.CollapseAgree.boxPush (hag : Env.CollapseAgree h env₁ env₂) (w' : M.frame.Acc w) :
    Env.CollapseAgree h.boxIn (env₁.boxPush w') (env₂.boxPush w') := by
  refine Env.CollapseAgree.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .box) rfl) _
        (Ctx.ref_boxIn_of hk (h u _ hu)), Env.ref,
        dif_neg (by decide : ¬ Step.box.isProj = true)]
      change M.necEval (env₁.ref u hu) w' = M.necEval (env₂.ref (u.collapse k) (h u _ hu)) w'
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .keep) rfl) _
        (Ctx.ref_keep_of hF (h u _ hu)), Env.ref, dif_neg (by decide : ¬ Step.keep.isProj = true)]
      change M.necEval (GFunc.eval M.ops (GFunc.dup (σ := σ) hF) w (env₁.ref u hu)) w' =
        M.necEval (GFunc.eval M.ops (GFunc.dup (σ := σ) hF) w
          (env₂.ref (u.collapse k) (h u _ hu))) w'
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem Env.CollapseAgree.diaPush (hag : Env.CollapseAgree h env₁ env₂) {x : VarSymb}
    {X : VarType} (hr : Γ₁.ref x = some (.VTypeDia X)) (w₁ : (M.posEval (env₁.ref x hr)).1)
    (hm : w₁.1 ∈ (M.posEval (env₂.ref (x.collapse k) (h x _ hr))).1) :
    Env.CollapseAgree (h.diaIn x) (env₁.diaPush x hr w₁)
      (env₂.diaPush (x.collapse k) (h x _ hr) ⟨w₁.1, hm⟩) := by
  refine Env.CollapseAgree.of_raw ?_
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
      rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .dia) rfl) _
        (Ctx.ref_diaIn_of (h u _ hr)), Env.ref, dif_neg (by decide : ¬ Step.dia.isProj = true)]
      simp only [Env.diaPush]
      exact posEval_snd_congr (hag u _ hr) w₁ hm
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ₁) hv
      rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .box) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_boxIn_of hk (h u _ hu))), Env.ref,
        dif_neg (by decide : ¬ Step.box.isProj = true)]
      change M.necEval (env₁.ref u hu) w₁.1 =
        M.necEval (env₂.ref (u.collapse k) (h u _ hu)) w₁.1
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep (Γ := Γ₁) hv
      rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .keep) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_keep_of hF (h u _ hu))), Env.ref,
        dif_neg (by decide : ¬ Step.keep.isProj = true)]
      change M.necEval (GFunc.eval M.ops (GFunc.dup (σ := σ) hF) w (env₁.ref u hu)) w₁.1 =
        M.necEval (GFunc.eval M.ops (GFunc.dup (σ := σ) hF) w
          (env₂.ref (u.collapse k) (h u _ hu))) w₁.1
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem Env.CollapseAgree.extend (hag : Env.CollapseAgree h env₁ env₂) {r : Root}
    (hr : Γ₁.RootFresh r) {T : VarType} (o : M.frame.Dom T w) :
    Env.CollapseAgree (h.insert hr T) (env₁.extend r o) (env₂.extend r o) := by
  refine Env.CollapseAgree.of_raw ?_
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    change (env₁.extend r o) (.root r) T hv = (env₂.extend r o) (.root r) T _
    rw [Env.extend_root, Env.extend_root]
  · have hv' : Γ₁ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ r := fun he => by
      rw [hr v he] at hv'
      cases hv'
    have href : Γ₁.ref v = some U := (Ctx.ref_nonproj Γ₁ hlp).trans hv'
    rw [Env.extend_ne env₁ r o hv hvr hv', ← Env.ref_of_nonproj env₁ hlp href hv', hag v U href,
      Env.ref_extend_ne env₂ o _ (h v U href) (by rwa [VarSymb.collapse_rt])]

/-- ⭐Under T, the `□` view at the current world agrees with the environment across the
    collapse. -/
theorem Env.collapseAgree_self (hT : ModalSys.T = true) {Γ : Ctx} (env : M.Env Γ w) :
    Env.CollapseAgree (Ctx.collapses_boxIn_self hT Γ) (env.boxPush ⟨w, ⟨M.frame.refl hT w⟩⟩)
      env := by
  refine Env.CollapseAgree.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      have hhs : Step.here.isProj = true := rfl
      rw [Env.ref_congr env (VarSymb.collapse_level_zero (s := .box) rfl (by decide)) _
        (Ctx.ref_here_of hT hu), Env.ref, dif_pos hhs]
      split
      · rename_i U hU
        have hUU : U = .VTypeBox T := Option.some.inj (hU.symm.trans hu)
        subst hUU
        rfl
      · rename_i hU
        exfalso
        rw [hU] at hu
        cases hu
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      rw [Env.ref_congr env (VarSymb.collapse_keep_zero (v := u)) _ hu]
      change M.necEval (M.ops.necDup hF (env.ref u hu)) ⟨w, ⟨M.frame.refl hT w⟩⟩ = env.ref u hu
      apply M.nec_inj
      funext s
      rw [M.necDup_eval, M.frame.refl_trans hT hF]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-! ## Shapes across a collapse -/

theorem ShEnv.ref_congr {Γ : Ctx} {w' : M.frame.W} (ρ : ShEnv M.frame M.RootPoss Γ w') (j : ℕ)
    {v v' : VarSymb}
    (e : v = v') {T : VarType} (hv : Γ.ref v = some T) (hv' : Γ.ref v' = some T) :
    ρ.ref j v hv = ρ.ref j v' hv' := by
  subst e
  rfl

/-- Two shape environments agree across a collapse, at one depth. -/
def ShEnv.CollapseAgree {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) {w' : M.frame.W}
    (ρ₁ : ShEnv M.frame M.RootPoss Γ₁ w') (ρ₂ : ShEnv M.frame M.RootPoss Γ₂ w') (j : ℕ) : Prop :=
  ∀ v T (hv : Γ₁.ref v = some T), ρ₁.ref j v hv = ρ₂.ref j (v.collapse k) (h v T hv)

theorem ShEnv.CollapseAgree.of_raw {ρ₁ : ShEnv M.frame M.RootPoss Γ₁ w}
    {ρ₂ : ShEnv M.frame M.RootPoss Γ₂ w} {j : ℕ}
    (hvis : ∀ v T (hlp : v.lastProj = false) (hv : Γ₁ v = some T),
      ρ₁ v T hv = ρ₂.ref j (v.collapse k) (h v T ((Ctx.ref_nonproj Γ₁ hlp).trans hv))) :
    ShEnv.CollapseAgree h ρ₁ ρ₂ j := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ₁.ref v = some U := by
          rw [Ctx.ref_step_proj Γ₁ v hs] at hv
          cases hU : Γ₁.ref v with
          | none => rw [hU] at hv; cases hv
          | some U => exact ⟨U, rfl⟩
        have hv₂ : Γ₂.ref (.step (v.collapse k) s) = some T := by
          rw [← VarSymb.collapse_proj hs]
          exact h _ T hv
        rw [ShEnv.ref_congr ρ₂ j (VarSymb.collapse_proj hs) _ hv₂, ShEnv.ref_proj ρ₁ j hs hU hv,
          ShEnv.ref_proj ρ₂ j hs (h v U hU) hv₂, ih U hU]
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [ShEnv.ref_nonproj ρ₁ j hs hv]
        exact hvis _ _ hlp _

theorem ShEnv.CollapseAgree.boxPush {ρ₁ : ShEnv M.frame M.RootPoss Γ₁ w}
    {ρ₂ : ShEnv M.frame M.RootPoss Γ₂ w} {j : ℕ}
    (hag : ShEnv.CollapseAgree h ρ₁ ρ₂ j) :
    ShEnv.CollapseAgree h.boxIn (ρ₁.boxPush j) (ρ₂.boxPush j) (j + 1) := by
  refine ShEnv.CollapseAgree.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .box) rfl) _
        (Ctx.ref_boxIn_of hk (h u _ hu)),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.box.isProj = true)]
      change (ρ₁.ref j u hu).inner = (ρ₂.ref j (u.collapse k) (h u _ hu)).inner
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .keep) rfl) _
        (Ctx.ref_keep_of hF (h u _ hu)),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
      change (GFunc.shp (GFunc.dup (σ := σ) hF) j (ρ₁.ref j u hu)).inner =
        (GFunc.shp (GFunc.dup (σ := σ) hF) j (ρ₂.ref j (u.collapse k) (h u _ hu))).inner
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem ShEnv.CollapseAgree.diaPush {ρ₁ : ShEnv M.frame M.RootPoss Γ₁ w}
    {ρ₂ : ShEnv M.frame M.RootPoss Γ₂ w} {j : ℕ}
    (hag : ShEnv.CollapseAgree h ρ₁ ρ₂ j) {x : VarSymb} {X : VarType}
    (hr : Γ₁.ref x = some (.VTypeDia X)) :
    ShEnv.CollapseAgree (h.diaIn x) (ρ₁.diaPush j x hr) (ρ₂.diaPush j (x.collapse k) (h x _ hr))
      (j + 1) := by
  refine ShEnv.CollapseAgree.of_raw ?_
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
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .dia) rfl) _
        (Ctx.ref_diaIn_of (h u _ hr)),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.dia.isProj = true)]
      simp only [ShEnv.diaPush]
      rw [hag u _ hr]
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ₁) hv
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .box) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_boxIn_of hk (h u _ hu))),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.box.isProj = true)]
      change (ρ₁.ref j u hu).inner = (ρ₂.ref j (u.collapse k) (h u _ hu)).inner
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep (Γ := Γ₁) hv
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .keep) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_keep_of hF (h u _ hu))),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
      change (GFunc.shp (GFunc.dup (σ := σ) hF) j (ρ₁.ref j u hu)).inner =
        (GFunc.shp (GFunc.dup (σ := σ) hF) j (ρ₂.ref j (u.collapse k) (h u _ hu))).inner
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- ⭐Collapsing does not change shapes. -/
theorem termShp_collapse {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {w : M.frame.W}
    {ρ₁ : ShEnv M.frame M.RootPoss Γ₁ w} {ρ₂ : ShEnv M.frame M.RootPoss Γ₂ w} {j : ℕ}
    (hag : ShEnv.CollapseAgree h ρ₁ ρ₂ j) :
    ∀ {T : VarType} {a : Ann T} (t : Term σ Γ₁ T a),
      termShp ρ₂ j (Term.collapse h t) = termShp ρ₁ j t
  | _, _, .var _ _ => rfl
  | _, _, .func _ => rfl
  | _, _, .unit => rfl
  | _, _, .pair s t => by
      change Shp.prod (termShp ρ₂ j (Term.collapse h s)) (termShp ρ₂ j (Term.collapse h t)) = _
      rw [termShp_collapse hag s, termShp_collapse hag t]
      rfl
  | _, _, .boxtm t => by
      change Shp.box (termShp (ρ₂.boxPush j) (j + 1) (Term.collapse h.boxIn t)) = _
      rw [termShp_collapse hag.boxPush t]
      rfl
  | _, _, .diatm x hx t => by
      obtain ⟨X, hr⟩ := id hx
      change termShp ρ₂ j (Term.diatm (x.collapse k) _ (Term.collapse (h.diaIn x) t)) = _
      rw [termShp_diatm ρ₂ j (h x _ hr), termShp_diatm ρ₁ j hr,
        termShp_collapse (hag.diaPush hr) t, hag x _ hr]

/-- Environments agreeing across a collapse have shape environments agreeing across it. -/
theorem Env.CollapseAgree.shape (hag : Env.CollapseAgree h env₁ env₂) (hT : ModalSys.T = true) :
    ShEnv.CollapseAgree h (envShape hT env₁) (envShape hT env₂) 0 := by
  intro v T hv
  rw [ref_envShape, ref_envShape, hag v T hv]

end Model

/-! ## Values and satisfaction are unchanged -/

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

mutual
  theorem interpFunc_collapse {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {w : M.frame.W}
      {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hag : Env.CollapseAgree h env₁ env₂) :
      ∀ {n : ℕ} (g : Func σ Γ₁ n) (args : Fin n → M.frame.D w),
        interpFunc env₂ (Func.collapse h g) args = interpFunc env₁ g args
    | _, .F _, _ => rfl
    | _, .eval g t, args => by
        change interpFunc env₂ (Func.collapse h g)
            (Fin.cons (interp env₂ (Term.collapse h t)) args) =
          interpFunc env₁ g (Fin.cons (interp env₁ t) args)
        rw [interp_collapse hag t, interpFunc_collapse hag g]

  /-- ⭐Collapsing does not change values. -/
  theorem interp_collapse {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {w : M.frame.W}
      {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hag : Env.CollapseAgree h env₁ env₂) :
      ∀ {T : VarType} {a : Ann T} (t : Term σ Γ₁ T a),
        interp env₂ (Term.collapse h t) = interp env₁ t
    | _, _, .var v hv => (hag v _ hv).symm
    | _, _, .func f => interpFunc_collapse hag f Fin.elim0
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change (interp env₂ (Term.collapse h s), interp env₂ (Term.collapse h t)) =
          (interp env₁ s, interp env₁ t)
        rw [interp_collapse hag s, interp_collapse hag t]
    | _, _, .boxtm t => by
        apply M.nec_inj
        funext w'
        change M.necEval (interp env₂ (Term.boxtm (Term.collapse h.boxIn t))) w' = _
        rw [box_beta, box_beta, interp_collapse (hag.boxPush w') t]
    | _, _, .diatm x hx t => by
        obtain ⟨X, hr⟩ := hx
        refine M.pos_inj ?_ fun hT => ?_
        swap
        · change domSh hT (interp env₂ (Term.collapse h (Term.diatm x _ t))) =
            domSh hT (interp env₁ (Term.diatm x _ t))
          rw [domSh_interp, domSh_interp]
          exact termShp_collapse (hag.shape hT) _
        change M.posEval (interp env₂
          (Term.diatm (x.collapse k) _ (Term.collapse (h.diaIn x) t))) = _
        rw [dia_beta env₂ _ (h x _ hr), dia_beta env₁ _ hr]
        exact posSec_ext (hag x _ hr).symm
          (fun w₂ => interp (env₂.diaPush (x.collapse k) (h x _ hr) w₂)
            (Term.collapse (h.diaIn x) t))
          (fun w₁ => interp (env₁.diaPush x hr w₁) t)
          (fun w₂ => interp_collapse (hag.diaPush hr ⟨w₂.1, (hag x _ hr).symm ▸ w₂.2⟩ w₂.2) t)
end

theorem relSat_collapse {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {w : M.frame.W}
    {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hag : Env.CollapseAgree h env₁ env₂) :
    ∀ {n : ℕ} (ρ : Rel σ Γ₁ n) (args : Fin n → M.frame.D w),
      relSat env₂ (Rel.collapse h ρ) args ↔ relSat env₁ ρ args
  | _, .R _, _ => Iff.rfl
  | _, .eval ρ t, args => by
      change relSat env₂ (Rel.collapse h ρ) (Fin.cons (interp env₂ (Term.collapse h t)) args) ↔
        relSat env₁ ρ (Fin.cons (interp env₁ t) args)
      rw [interp_collapse hag t]
      exact relSat_collapse hag ρ _

/-- ⭐Collapsing does not change satisfaction. -/
theorem sat_collapse : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {d : ℕ}
    {w : M.frame.W} {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hs : Γ₁.SlotsFrom d),
    Env.CollapseAgree h env₁ env₂ → (φ : WFF σ Γ₁ d) →
    (M.sat env₂ (WFF.collapse h hs φ) ↔ M.sat env₁ φ)
  | _, _, _, _, _, _, _, _, _, hag, .atom ρ => relSat_collapse hag ρ Fin.elim0
  | _, _, _, _, _, _, _, _, _, hag, .eq t s => by
      change interp _ (Term.collapse _ t) = interp _ (Term.collapse _ s) ↔ _
      rw [interp_collapse hag t, interp_collapse hag s]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .top => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .bot => Iff.rfl
  | _, _, _, _, _, _, _, _, hs, hag, .and φ ψ =>
      and_congr (sat_collapse hs hag φ) (sat_collapse hs hag ψ)
  | _, _, _, _, _, _, _, _, hs, hag, .or φ ψ =>
      or_congr (sat_collapse hs hag φ) (sat_collapse hs hag ψ)
  | _, _, _, _, _, _, _, _, hs, hag, .imp φ ψ =>
      imp_congr (sat_collapse hs hag φ) (sat_collapse hs hag ψ)
  | _, _, _, _, _, _, _, _, hs, hag, .all _ φ =>
      forall_congr' fun o => sat_collapse (hs.insert _) (hag.extend (hs.rootFresh le_rfl) o) φ
  | _, _, _, _, _, _, _, _, hs, hag, .ex _ φ =>
      exists_congr fun o => sat_collapse (hs.insert _) (hag.extend (hs.rootFresh le_rfl) o) φ
  | _, _, _, _, _, _, _, _, hs, hag, .box φ =>
      forall_congr' fun w' => sat_collapse hs.boxIn (hag.boxPush w') φ
  | k, _, _, h, _, _, env₁, env₂, hs, hag, .dia x hx φ => by
      constructor
      · rintro ⟨X, h₂, w₂, hsat⟩
        obtain ⟨X₀, hr⟩ := hx
        have hXX : X₀ = X := by
          have e := h x _ hr
          rw [h₂] at e
          cases e
          rfl
        subst hXX
        have href := hag x _ hr
        refine ⟨X₀, hr, ⟨w₂.1, by rw [href]; exact w₂.2⟩, ?_⟩
        exact (sat_collapse (hs.diaIn x) (hag.diaPush hr ⟨w₂.1, _⟩ w₂.2) φ).mp hsat
      · rintro ⟨X, hr, w₁, hsat⟩
        have href := hag x _ hr
        exact ⟨X, h x _ hr, ⟨w₁.1, by rw [← href]; exact w₁.2⟩,
          (sat_collapse (hs.diaIn x) (hag.diaPush hr w₁ _) φ).mpr hsat⟩
  | _, _, _, _, _, _, _, _, _, hag, .here hT s t => by
      change Model.Realised hT (interp _ (Term.collapse _ s)) (interp _ (Term.collapse _ t)) ↔ _
      rw [interp_collapse hag s, interp_collapse hag t]
      exact Iff.rfl

/-- ⭐The semantic content of the T rule: a collapsed `□`-body holds exactly when the body holds
    at the current world. -/
theorem sat_boxHere (hT : ModalSys.T = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (hs : Γ.boxIn.SlotsFrom 0) (φ : WFF σ Γ.boxIn 0) :
    M.sat env (WFF.collapse (Ctx.collapses_boxIn_self hT Γ) hs φ) ↔
      M.sat (env.boxPush ⟨w, ⟨M.frame.refl hT w⟩⟩) φ :=
  sat_collapse hs (Env.collapseAgree_self hT env) φ

end Model

end V12M
