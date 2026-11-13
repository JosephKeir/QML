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
        dif_neg (by decide : ¬ Step.box.isStruct = true)]
      rfl
  | true =>
      obtain ⟨hT, hF⟩ := ModalSys.keepOnly_flags hk
      have hkeep : Γ.boxIn.ref (.step u .keep) = some (.VTypeBox A) := Ctx.ref_keep_of hF hu
      have hhs : Step.here.isStruct = true := rfl
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
      have hs : ¬ s.isStruct = true := fun hh => by
        change s.isStruct = false at hlp
        rw [hh] at hlp
        cases hlp
      rw [Env.ref, dif_neg hs]

theorem Env.extend_root {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) (h : (Γ.insert r T) (.root r) = some T) :
    env.extend r o (.root r) T h = o := by
  change (if hv : VarSymb.root r = .root r then _ else _) = o
  rw [dif_pos rfl]

theorem Env.extend_ne {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) {v : VarSymb} {U : VarType} (h : (Γ.insert r T) v = some U)
    (hvr : v ≠ .root r) (h' : Γ v = some U) : env.extend r o v U h = env v U h' := by
  change (if hv : v = .root r then _ else _) = env v U h'
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
      by_cases hs : s.isStruct = true
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
      by_cases hs : s.isStruct = true
      · have hv₂ : Γ₂.ref (.step (v.collapse k) s) = some T := by
          rw [← VarSymb.collapse_proj (Step.isProj_of_isStruct hs)]
          exact h _ T hv
        rw [Env.ref_congr env₂ (VarSymb.collapse_proj (Step.isProj_of_isStruct hs)) _ hv₂,
          Env.ref, Env.ref, dif_pos hs,
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
        dif_neg (by decide : ¬ Step.box.isStruct = true)]
      change M.necEval (env₁.ref u hu) w' = M.necEval (env₂.ref (u.collapse k) (h u _ hu)) w'
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .keep) rfl) _
        (Ctx.ref_keep_of' hF (h u _ hu) hk), Env.ref,
        dif_neg (by decide : ¬ Step.keep.isStruct = true)]
      change M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF hk) w (env₁.ref u hu)) w' =
        M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF hk) w
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
        (Ctx.ref_diaIn_of (h u _ hr)), Env.ref, dif_neg (by decide : ¬ Step.dia.isStruct = true)]
      simp only [Env.diaPush]
      exact posEval_snd_congr (hag u _ hr) w₁ hm
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ₁) hv
      rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .box) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_boxIn_of hk (h u _ hu))), Env.ref,
        dif_neg (by decide : ¬ Step.box.isStruct = true)]
      change M.necEval (env₁.ref u hu) w₁.1 =
        M.necEval (env₂.ref (u.collapse k) (h u _ hu)) w₁.1
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ₁) hv
      rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .keep) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_keep_of' hF (h u _ hu) hk)), Env.ref,
        dif_neg (by decide : ¬ Step.keep.isStruct = true)]
      change M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF hk) w (env₁.ref u hu)) w₁.1 =
        M.necEval (GFunc.eval M.ops (GFunc.keep (σ := σ) hF hk) w
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
  · have hv' : Γ₁ v = some U := Ctx.insert_ne_some hv hvr
    have hrt : v.rt ≠ r := fun he => by
      rw [hr v he] at hv'
      cases hv'
    have href : Γ₁.ref v = some U := (Ctx.ref_nonproj Γ₁ hlp).trans hv'
    rw [Env.extend_ne env₁ r o hv hvr hv', ← Env.ref_of_nonproj env₁ hlp href hv', hag v U href,
      Env.ref_extend_ne env₂ o _ (h v U href) (by rwa [VarSymb.collapse_rt])]

/-! ## Environments respecting their contents (M2, docs §12.30) -/

/-- Into the view of a witness, an environment respecting it agrees with itself. -/
theorem Env.agree_optPush {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w)
    {z : VarSymb} {Z : VarType} (hz : Δ.wit z = some Z) (hd : (env.wit z Z hz).Dom) :
    Env.Agree (Ctx.le_optIn Δ z) env (env.optPush z hz hd) := by
  intro v T hv
  by_cases hvz : v = .step z .dia
  · subst hvz
    have hTZ : T = Z := by
      rcases Δ.wit_dia z Z hz with h' | h'
      · rw [h'] at hv
        cases hv
      · rw [h'] at hv
        exact (Option.some.inj hv).symm
    subst hTZ
    obtain ⟨hd', he⟩ := env.opened z T hz hv
    rw [he]
    change _ = (if hv' : VarSymb.step z .dia = .step z .dia then _ else _)
    rw [dif_pos rfl]
  · change _ = (if hv' : v = .step z .dia then _ else _)
    rw [dif_neg hvz]

theorem Env.agree_extend {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {r : Root}
    (h : Δ (.root r) = none) {T : VarType} (o : M.frame.Dom T w) :
    Env.Agree (Ctx.le_insert h T) env (env.extend r o) := fun v U hv =>
  (Env.extend_ne env r o _ (fun he => by subst he; rw [h] at hv; cases hv) hv).symm


/-- Without T and `Opt` together there is no identity content to respect. -/
theorem Env.openedT_off {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (h : ¬ (ModalSys.T = true ∧ ModalSys.Opt = true)) : env.OpenedT :=
  fun _ _ hz _ => absurd ⟨(Ctx.witT_spec hz).1, (Ctx.witT_spec hz).2.1⟩ h

/-- With `Opt` off there is no identity content to respect. -/
theorem Env.openedT_noOpt [ModalSys.NoOpt] {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    env.OpenedT :=
  env.openedT_off fun h => absurd h.2 (by rw [ModalSys.NoOpt.noOpt]; decide)

theorem Env.OpenedT.extend {Γ : Ctx} {w : M.frame.W} {env : M.Env Γ w} (hop : env.OpenedT)
    {r : Root} (h : Γ (.root r) = none) {T : VarType} (o : M.frame.Dom T w) :
    (env.extend r o).OpenedT :=
  Env.OpenedT.of_agree (Env.agree_extend env h o)
    (fun _ _ hv => Ctx.insert_ne_some hv (fun he => by cases he)) hop

theorem Env.openedT_boxPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (w' : M.frame.Acc w) :
    (env.boxPush w').OpenedT := fun _ _ _ hv => by cases hv

theorem Env.openedT_diaPush {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (x : VarSymb)
    {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x hx)).1) :
    (env.diaPush x hx w').OpenedT := fun _ _ _ hv => by cases hv

theorem Env.OpenedT.optPush {Γ : Ctx} {w : M.frame.W} {env : M.Env Γ w} (hop : env.OpenedT)
    {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X) (hd : (env.wit y X hy).Dom) :
    (env.optPush y hy hd).OpenedT :=
  Env.OpenedT.of_agree (Env.agree_optPush env hy hd)
    (fun _ _ hv => by rwa [Ctx.optIn_ne (fun he => by cases he)] at hv) hop

/-- Into the identity view, an environment respecting its identity contents agrees with itself. -/
theorem Env.agree_optPushT {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (hop : env.OpenedT)
    {z : VarSymb} {Z : VarType} (hz : Δ.witT z = some Z) (hd : (env.witT z hz).Dom) :
    Env.Agree (Ctx.le_optInT Δ z) env (env.optPushT z hz hd) := by
  intro v T hv
  by_cases hvz : v = .step z .at
  · subst hvz
    have h₁ := Ctx.refAll_of_ref Δ z (Ctx.witT_spec hz).2.2
    rw [Δ.at_coh z _ hv] at h₁
    cases h₁
    obtain ⟨hd', he⟩ := hop z _ hz hv
    rw [he]
    change _ = (if hv' : VarSymb.step z .at = .step z .at then _ else _)
    rw [dif_pos rfl]
  · change _ = (if hv' : v = .step z .at then _ else _)
    rw [dif_neg hvz]

/-- The identity view respects its identity contents: the new one by construction. -/
theorem Env.OpenedT.optPushT {Γ : Ctx} {w : M.frame.W} {env : M.Env Γ w} (hop : env.OpenedT)
    {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X) (hd : (env.witT y hy).Dom) :
    (env.optPushT y hy hd).OpenedT := by
  have hag := Env.agree_optPushT env hop hy hd
  intro z Z hz hv
  by_cases hzy : z = y
  · subst hzy
    have hZX : X = Z := Option.some.inj (((Ctx.le_optInT Γ z).witT hy).symm.trans hz)
    subst hZX
    have he := Env.witT_agree hag hy hz
    refine ⟨he.symm ▸ hd, ?_⟩
    change (if hv' : VarSymb.step z .at = .step z .at then _ else _) = _
    rw [dif_pos rfl]
    exact (Part.get_eq_of_mem (he.symm ▸ Part.get_mem hd) _).symm
  · have hne : VarSymb.step z .at ≠ .step y .at := fun he => hzy (by cases he; rfl)
    exact hop.of_agree_at hag hz hv (by rwa [Ctx.optInT_ne hne] at hv)

/-! ## Witnesses across a collapse (M2, docs §12.30) -/

/-- ⭐**What a collapse needs with `Opt` on**, beyond the objects: along the collapsed arrow a
    witness's value is the identity witness's (`◇⁰_y` collapses to `◇⁰ᵀ_y`), further in the
    collapsed witness's; and the target respects its identity contents and has no slot from `d`
    on (so its own insertions are fresh). -/
structure Env.CollapseOpt {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) (d : ℕ)
    {w : M.frame.W} (env₁ : M.Env Γ₁ w) (env₂ : M.Env Γ₂ w) : Prop where
  zero : ∀ y X (hy : Γ₁.wit y = some X) (hk : k = 0),
    env₁.wit y X hy = env₂.witT y ((h.wit y X hy).1 hk)
  succ : ∀ y X (hy : Γ₁.wit y = some X) k' (hk : k = k' + 1),
    env₁.wit y X hy = env₂.wit (y.collapse k') X ((h.wit y X hy).2 k' hk)
  opened : env₂.OpenedT
  slots : Γ₂.SlotsFrom d

theorem Env.CollapseOpt.boxPush {d : ℕ} (hag : Env.CollapseAgree h env₁ env₂)
    (ho : Env.CollapseOpt h d env₁ env₂) (w' : M.frame.Acc w) :
    Env.CollapseOpt h.boxIn d (env₁.boxPush w') (env₂.boxPush w') where
  zero _ _ _ hk := absurd hk (Nat.succ_ne_zero k)
  succ y X hy k' hk := by
    obtain rfl : k = k' := Nat.succ.inj hk
    change posPart (env₁.ref y _) w' = posPart (env₂.ref (y.collapse k) _) w'
    rw [hag y _ (Ctx.boxIn_wit.mp hy).2]
  opened := env₂.openedT_boxPush w'
  slots := ho.slots.boxIn

theorem Env.CollapseOpt.diaPush {d : ℕ} (hag : Env.CollapseAgree h env₁ env₂)
    (ho : Env.CollapseOpt h d env₁ env₂) {x : VarSymb} {X : VarType}
    (hr : Γ₁.ref x = some (.VTypeDia X)) (w₁ : (M.posEval (env₁.ref x hr)).1)
    (hm : w₁.1 ∈ (M.posEval (env₂.ref (x.collapse k) (h x _ hr))).1) :
    Env.CollapseOpt (h.diaIn x) d (env₁.diaPush x hr w₁)
      (env₂.diaPush (x.collapse k) (h x _ hr) ⟨w₁.1, hm⟩) where
  zero _ _ _ hk := absurd hk (Nat.succ_ne_zero k)
  succ y X hy k' hk := by
    obtain rfl : k = k' := Nat.succ.inj hk
    change posPart (env₁.ref y _) w₁.1 = posPart (env₂.ref (y.collapse k) _) w₁.1
    rw [hag y _ (Ctx.boxIn_wit.mp hy).2]
  opened := env₂.openedT_diaPush _ _ _
  slots := ho.slots.diaIn _

theorem Env.CollapseOpt.extend {d d' : ℕ} (ho : Env.CollapseOpt h d env₁ env₂) {r : Root}
    (hr : Γ₁.RootFresh r) (hr₂ : Γ₂ (.root r) = none) {T : VarType}
    (hs' : (Γ₂.insert r T).SlotsFrom d') (o : M.frame.Dom T w) :
    Env.CollapseOpt (h.insert hr T) d' (env₁.extend r o) (env₂.extend r o) where
  zero y X hy hk := (ho.zero y X hy hk).trans
    (Env.witT_agree (Env.agree_extend env₂ hr₂ o) _ _).symm
  succ y X hy k' hk := ho.succ y X hy k' hk
  opened := ho.opened.extend hr₂ o
  slots := hs'

theorem Env.CollapseAgree.optPush_succ {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses (k + 1) Γ₁ Γ₂}
    {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} {d : ℕ} (hag : Env.CollapseAgree h env₁ env₂)
    (ho : Env.CollapseOpt h d env₁ env₂) {y : VarSymb} {X : VarType} (hy : Γ₁.wit y = some X)
    (hd₁ : (env₁.wit y X hy).Dom) (hd₂ : (env₂.wit (y.collapse k) X ((h.wit y X hy).2 k rfl)).Dom) :
    Env.CollapseAgree (h.optIn_succ hy) (env₁.optPush y hy hd₁)
      (env₂.optPush (y.collapse k) ((h.wit y X hy).2 k rfl) hd₂) := by
  have he := ho.succ y X hy k rfl
  refine Env.CollapseAgree.of_raw ?_
  intro v T hlp hv
  by_cases hc : v = .step y .dia
  · subst hc
    have hXT : X = T := by rw [Ctx.optIn_content hy] at hv; exact Option.some.inj hv
    subst hXT
    rw [Env.ref_congr _ (VarSymb.collapse_level_succ (s := .dia) rfl) _
        ((Ctx.ref_nonproj _ rfl).trans (Ctx.optIn_content ((h.wit y X hy).2 k rfl))), Env.ref,
      dif_neg (by decide : ¬ Step.dia.isStruct = true)]
    change (if hv' : VarSymb.step y .dia = .step y .dia then _ else _) =
      (if hv' : VarSymb.step (y.collapse k) .dia = .step (y.collapse k) .dia then _ else _)
    rw [dif_pos rfl, dif_pos rfl]
    exact (Part.get_eq_of_mem (he ▸ Part.get_mem hd₁) hd₂).symm
  · have hv₁ : Γ₁ v = some T := by rwa [Ctx.optIn_ne hc] at hv
    change (if hv' : v = .step y .dia then _ else _) = _
    rw [dif_neg hc]
    have href : Γ₁.ref v = some T := (Ctx.ref_nonproj Γ₁ hlp).trans hv₁
    rw [← Env.ref_of_nonproj env₁ hlp href hv₁, hag v T href]
    exact Env.ref_agree (Env.agree_optPush env₂ _ hd₂) _ (h v T href)

theorem Env.CollapseOpt.optPush_succ {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses (k + 1) Γ₁ Γ₂}
    {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} {d : ℕ} (ho : Env.CollapseOpt h d env₁ env₂)
    {y : VarSymb} {X : VarType} (hy : Γ₁.wit y = some X) (hd₁ : (env₁.wit y X hy).Dom)
    (hd₂ : (env₂.wit (y.collapse k) X ((h.wit y X hy).2 k rfl)).Dom) :
    Env.CollapseOpt (h.optIn_succ hy) d (env₁.optPush y hy hd₁)
      (env₂.optPush (y.collapse k) ((h.wit y X hy).2 k rfl) hd₂) where
  zero _ _ _ hk := absurd hk (Nat.succ_ne_zero k)
  succ y' X' hy' k' hk := ho.succ y' X' hy' k' hk
  opened := ho.opened.optPush _ hd₂
  slots := ho.slots.optIn _

theorem Env.CollapseAgree.optPush_zero {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses 0 Γ₁ Γ₂}
    {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} {d : ℕ} (hag : Env.CollapseAgree h env₁ env₂)
    (ho : Env.CollapseOpt h d env₁ env₂) (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType}
    (hy : Γ₁.wit y = some X) (hd₁ : (env₁.wit y X hy).Dom)
    (hd₂ : (env₂.witT y ((h.wit y X hy).1 rfl)).Dom) :
    Env.CollapseAgree (h.optIn_zero hO hy) (env₁.optPush y hy hd₁)
      (env₂.optPushT y ((h.wit y X hy).1 rfl) hd₂) := by
  have he := ho.zero y X hy rfl
  refine Env.CollapseAgree.of_raw ?_
  intro v T hlp hv
  by_cases hc : v = .step y .dia
  · subst hc
    have hXT : X = T := by rw [Ctx.optIn_content hy] at hv; exact Option.some.inj hv
    subst hXT
    rw [Env.ref_congr _ (VarSymb.collapse_dia_zero_opt hO) _
        ((Ctx.ref_nonproj _ rfl).trans (Ctx.optInT_content ((h.wit y X hy).1 rfl))), Env.ref,
      dif_neg (by decide : ¬ Step.at.isStruct = true)]
    change (if hv' : VarSymb.step y .dia = .step y .dia then _ else _) =
      (if hv' : VarSymb.step y .at = .step y .at then _ else _)
    rw [dif_pos rfl, dif_pos rfl]
    exact (Part.get_eq_of_mem (he ▸ Part.get_mem hd₁) hd₂).symm
  · have hv₁ : Γ₁ v = some T := by rwa [Ctx.optIn_ne hc] at hv
    change (if hv' : v = .step y .dia then _ else _) = _
    rw [dif_neg hc]
    have href : Γ₁.ref v = some T := (Ctx.ref_nonproj Γ₁ hlp).trans hv₁
    rw [← Env.ref_of_nonproj env₁ hlp href hv₁, hag v T href]
    exact Env.ref_agree (Env.agree_optPushT env₂ ho.opened _ hd₂) _ (h v T href)

theorem Env.CollapseOpt.optPush_zero {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses 0 Γ₁ Γ₂}
    {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} {d : ℕ} (ho : Env.CollapseOpt h d env₁ env₂)
    (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType} (hy : Γ₁.wit y = some X)
    (hd₁ : (env₁.wit y X hy).Dom) (hd₂ : (env₂.witT y ((h.wit y X hy).1 rfl)).Dom) :
    Env.CollapseOpt (h.optIn_zero hO hy) d (env₁.optPush y hy hd₁)
      (env₂.optPushT y ((h.wit y X hy).1 rfl) hd₂) where
  zero y' X' hy' hk := (ho.zero y' X' hy' hk).trans
    (Env.witT_agree (Env.agree_optPushT env₂ ho.opened _ hd₂) _ _).symm
  succ _ _ _ k' hk := absurd hk.symm (Nat.succ_ne_zero k')
  opened := ho.opened.optPushT _ hd₂
  slots := ho.slots.optInT _

theorem Env.CollapseAgree.optPushT {d : ℕ} (hag : Env.CollapseAgree h env₁ env₂)
    (ho : Env.CollapseOpt h d env₁ env₂) {y : VarSymb} {X : VarType} (hy : Γ₁.witT y = some X)
    (hd₁ : (env₁.witT y hy).Dom) (hd₂ : (env₂.witT (y.collapse k) (h.witT hy)).Dom) :
    Env.CollapseAgree (h.optInT hy) (env₁.optPushT y hy hd₁)
      (env₂.optPushT (y.collapse k) (h.witT hy) hd₂) := by
  have he : env₁.witT y hy = env₂.witT (y.collapse k) (h.witT hy) := by
    unfold Env.witT
    rw [hag y _ (Ctx.witT_spec hy).2.2]
  refine Env.CollapseAgree.of_raw ?_
  intro v T hlp hv
  by_cases hc : v = .step y .at
  · subst hc
    have hXT : X = T := by rw [Ctx.optInT_content hy] at hv; exact Option.some.inj hv
    subst hXT
    rw [Env.ref_congr _ (VarSymb.collapse_proj (s := .at) rfl) _
        ((Ctx.ref_nonproj _ rfl).trans (Ctx.optInT_content (h.witT hy))), Env.ref,
      dif_neg (by decide : ¬ Step.at.isStruct = true)]
    change (if hv' : VarSymb.step y .at = .step y .at then _ else _) =
      (if hv' : VarSymb.step (y.collapse k) .at = .step (y.collapse k) .at then _ else _)
    rw [dif_pos rfl, dif_pos rfl]
    exact (Part.get_eq_of_mem (he ▸ Part.get_mem hd₁) hd₂).symm
  · have hv₁ : Γ₁ v = some T := by rwa [Ctx.optInT_ne hc] at hv
    change (if hv' : v = .step y .at then _ else _) = _
    rw [dif_neg hc]
    have href : Γ₁.ref v = some T := (Ctx.ref_nonproj Γ₁ hlp).trans hv₁
    rw [← Env.ref_of_nonproj env₁ hlp href hv₁, hag v T href]
    exact Env.ref_agree (Env.agree_optPushT env₂ ho.opened _ hd₂) _ (h v T href)

theorem Env.CollapseOpt.optPushT {d : ℕ} (ho : Env.CollapseOpt h d env₁ env₂) {y : VarSymb}
    {X : VarType} (hy : Γ₁.witT y = some X) (hd₁ : (env₁.witT y hy).Dom)
    (hd₂ : (env₂.witT (y.collapse k) (h.witT hy)).Dom) :
    Env.CollapseOpt (h.optInT hy) d (env₁.optPushT y hy hd₁)
      (env₂.optPushT (y.collapse k) (h.witT hy) hd₂) where
  zero y' X' hy' hk := (ho.zero y' X' hy' hk).trans
    (Env.witT_agree (Env.agree_optPushT env₂ ho.opened _ hd₂) _ _).symm
  succ y' X' hy' k' hk := ho.succ y' X' hy' k' hk
  opened := ho.opened.optPushT _ hd₂
  slots := ho.slots.optInT _

omit [ModalSys] in
/-- Two sections with the same extent and the same contents are equal. -/
theorem sec_ext {α : Type*} {β : α → Type*} {E₁ E₂ : Set α} {f₁ : (b : E₁) → β b.1}
    {f₂ : (b : E₂) → β b.1} (hE : E₁ = E₂)
    (hf : ∀ (b : α) (h₁ : b ∈ E₁) (h₂ : b ∈ E₂), f₁ ⟨b, h₁⟩ = f₂ ⟨b, h₂⟩) :
    (⟨E₁, f₁⟩ : Σ E : Set α, (b : E) → β b.1) = ⟨E₂, f₂⟩ := by
  subst hE
  congr
  funext b
  exact hf b.1 b.2 b.2

/-- ⭐Under T and 4, **a possible object kept along the identity is itself**: the extent by
    `refl_trans`, the contents unchanged, the labels by the root action's identity law. -/
theorem posKeep_refl (hT : ModalSys.T = true) (hF : ModalSys.Four = true) {A : VarType}
    {w : M.frame.W} (x : M.frame.Pos A w) :
    M.necEval (M.ops.posKeep hF x) (M.frame.reflAcc hT w) = x := by
  apply M.posFull_inj
  rw [M.posKeep_full]
  refine Prod.ext ?_ (funext fun hS => ?_)
  · dsimp only
    refine sec_ext (β := fun a : M.frame.Acc w => M.frame.Dom A a.1)
      (Set.ext fun b => ?_) (fun b h₁ h₂ => ?_)
    · change (⟨b.1, ⟨M.frame.trans hF (M.frame.refl hT w) b.2.down⟩⟩ : M.frame.Acc w) ∈
          (M.posFull x).1.1 ↔ b ∈ (M.posFull x).1.1
      rw [M.frame.refl_trans hT hF]
    · change (M.posFull x).1.2 ⟨⟨b.1, ⟨M.frame.trans hF (M.frame.refl hT w) b.2.down⟩⟩, _⟩ =
        (M.posFull x).1.2 ⟨b, h₂⟩
      generalize_proofs p₁
      revert p₁
      rw [M.frame.refl_trans hT hF]
      intro p₁
      rfl
  · have e : Arrows.Leaf.keepAlong (F := M.frame.toArrows) (Root := M.RootPoss) hF
        (M.frame.reflAcc hT w) = id := funext (Arrows.Leaf.keepAlong_refl hT hF)
    dsimp only
    rw [e, Shp.map_id]

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
      have hhs : Step.here.isStruct = true := rfl
      rw [Env.ref_congr env (VarSymb.collapse_level_zero (s := .box) rfl (by decide) (by decide)) _
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
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      rw [Env.ref_congr env (VarSymb.collapse_keep_zero (v := u)) _ hu]
      cases T with
      | VTypeBox A =>
          change M.necEval (M.ops.necDup hF (env.ref u hu)) ⟨w, ⟨M.frame.refl hT w⟩⟩ =
            env.ref u hu
          apply M.nec_inj
          funext s
          rw [M.necDup_eval, M.frame.refl_trans hT hF]
      | VTypeDia A =>
          change M.necEval (M.ops.posKeep hF (env.ref u hu)) (M.frame.reflAcc hT w) = env.ref u hu
          exact posKeep_refl hT hF (env.ref u hu)
      | _ => cases hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- ⭐Under T with `Opt`, the `◇_x` view at the identity arrow agrees with `x`'s identity view
    across the collapse (`Ctx.collapses_diaIn_optInT`): a possible term's body read at the
    current world. -/
theorem Env.collapseAgree_diaIn_optInT (hT : ModalSys.T = true) (hO : ModalSys.Opt = true)
    {Γ : Ctx} (env : M.Env Γ w) (hop : env.OpenedT) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X))
    (hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hr)).1)
    (hd : (env.witT x (Ctx.witT_of hT hO hr)).Dom) :
    Env.CollapseAgree (Ctx.collapses_diaIn_optInT hT hO Γ hr) (env.diaPush x hr ⟨_, hm⟩)
      (env.optPushT x (Ctx.witT_of hT hO hr) hd) := by
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
      rw [Env.ref_congr _ (VarSymb.collapse_dia_zero_opt hO) _
          ((Ctx.ref_nonproj _ rfl).trans (Ctx.optInT_content (Ctx.witT_of hT hO hr))), Env.ref,
        dif_neg (by decide : ¬ Step.at.isStruct = true)]
      change _ = (if hv' : VarSymb.step u .at = .step u .at then _ else _)
      rw [dif_pos rfl]
      rfl
  | .step u .box =>
      have hvb : Γ.boxIn (.step u .box) = some T := hv
      have hrb : Γ.boxIn.ref (.step u .box) = some T := (Ctx.ref_nonproj _ rfl).trans hvb
      have h₁ := Env.collapseAgree_self hT env (.step u .box) T hrb
      rw [Env.ref_of_nonproj (env.boxPush (M.frame.reflAcc hT w)) rfl hrb hvb] at h₁
      exact h₁.trans (Env.ref_agree (Env.agree_optPushT env hop _ hd) _ _)
  | .step u .keep =>
      exact absurd hO (by rw [ModalSys.noOpt_of_Four (Ctx.boxIn_keep (Γ := Γ) hv).1]; decide)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv
  | .step _ .at => cases hv

end Model

namespace Model

variable {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}
  [Arrows.RootKeep F Root]
  {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {w : F.W}

/-! ## Shapes across a collapse -/

theorem ShEnv.ref_congr {Γ : Ctx} {w' : F.W} (ρ : ShEnv F Root Γ w') (j : ℕ)
    {v v' : VarSymb}
    (e : v = v') {T : VarType} (hv : Γ.ref v = some T) (hv' : Γ.ref v' = some T) :
    ρ.ref j v hv = ρ.ref j v' hv' := by
  subst e
  rfl

/-- Two shape environments agree across a collapse, at one depth. -/
def ShEnv.CollapseAgree {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) {w' : F.W}
    (ρ₁ : ShEnv F Root Γ₁ w') (ρ₂ : ShEnv F Root Γ₂ w') (j : ℕ) : Prop :=
  ∀ v T (hv : Γ₁.ref v = some T), ρ₁.ref j v hv = ρ₂.ref j (v.collapse k) (h v T hv)

theorem ShEnv.CollapseAgree.of_raw {ρ₁ : ShEnv F Root Γ₁ w}
    {ρ₂ : ShEnv F Root Γ₂ w} {j : ℕ}
    (hvis : ∀ v T (hlp : v.lastProj = false) (hv : Γ₁ v = some T),
      ρ₁ v T hv = ρ₂.ref j (v.collapse k) (h v T ((Ctx.ref_nonproj Γ₁ hlp).trans hv))) :
    ShEnv.CollapseAgree h ρ₁ ρ₂ j := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ₁.ref v = some U := by
          rw [Ctx.ref_step_proj Γ₁ v hs] at hv
          cases hU : Γ₁.ref v with
          | none => rw [hU] at hv; cases hv
          | some U => exact ⟨U, rfl⟩
        have hv₂ : Γ₂.ref (.step (v.collapse k) s) = some T := by
          rw [← VarSymb.collapse_proj (Step.isProj_of_isStruct hs)]
          exact h _ T hv
        rw [ShEnv.ref_congr ρ₂ j (VarSymb.collapse_proj (Step.isProj_of_isStruct hs)) _ hv₂,
          ShEnv.ref_proj ρ₁ j hs hU hv,
          ShEnv.ref_proj ρ₂ j hs (h v U hU) hv₂, ih U hU]
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [ShEnv.ref_nonproj ρ₁ j hs hv]
        exact hvis _ _ hlp _

theorem ShEnv.CollapseAgree.boxPush {ρ₁ : ShEnv F Root Γ₁ w}
    {ρ₂ : ShEnv F Root Γ₂ w} {j : ℕ}
    (hag : ShEnv.CollapseAgree h ρ₁ ρ₂ j) :
    ShEnv.CollapseAgree h.boxIn (ρ₁.boxPush j) (ρ₂.boxPush j) (j + 1) := by
  refine ShEnv.CollapseAgree.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .box) rfl) _
        (Ctx.ref_boxIn_of hk (h u _ hu)),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.box.isStruct = true)]
      change (ρ₁.ref j u hu).inner = (ρ₂.ref j (u.collapse k) (h u _ hu)).inner
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .keep) rfl) _
        (Ctx.ref_keep_of' hF (h u _ hu) hk),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isStruct = true)]
      change (GFunc.shp (GFunc.keep (σ := σ) hF hk) j (ρ₁.ref j u hu)).inner =
        (GFunc.shp (GFunc.keep (σ := σ) hF hk) j (ρ₂.ref j (u.collapse k) (h u _ hu))).inner
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem ShEnv.CollapseAgree.diaPush {ρ₁ : ShEnv F Root Γ₁ w}
    {ρ₂ : ShEnv F Root Γ₂ w} {j : ℕ}
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
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.dia.isStruct = true)]
      simp only [ShEnv.diaPush]
      rw [hag u _ hr]
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ₁) hv
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .box) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_boxIn_of hk (h u _ hu))),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.box.isStruct = true)]
      change (ρ₁.ref j u hu).inner = (ρ₂.ref j (u.collapse k) (h u _ hu)).inner
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ₁) hv
      rw [ShEnv.ref_congr _ _ (VarSymb.collapse_level_succ (s := .keep) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_keep_of' hF (h u _ hu) hk)),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isStruct = true)]
      change (GFunc.shp (GFunc.keep (σ := σ) hF hk) j (ρ₁.ref j u hu)).inner =
        (GFunc.shp (GFunc.keep (σ := σ) hF hk) j (ρ₂.ref j (u.collapse k) (h u _ hu))).inner
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- ⭐Collapsing does not change shapes. -/
theorem termShp_collapse {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {w : F.W}
    {ρ₁ : ShEnv F Root Γ₁ w} {ρ₂ : ShEnv F Root Γ₂ w} {j : ℕ}
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

end Model

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}
  {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Collapses k Γ₁ Γ₂} {w : M.frame.W}
  {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w}

/-- Environments agreeing across a collapse have shape environments agreeing across it. -/
theorem Env.CollapseAgree.shape (hag : Env.CollapseAgree h env₁ env₂)
    (hSh : ModalSys.shaped = true) :
    ShEnv.CollapseAgree h (envShape hSh env₁) (envShape hSh env₂) 0 := by
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
        refine M.pos_inj ?_ fun hSh => ?_
        swap
        · change domSh hSh (interp env₂ (Term.collapse h (Term.diatm x _ t))) =
            domSh hSh (interp env₁ (Term.diatm x _ t))
          rw [domSh_interp, domSh_interp]
          exact termShp_collapse (hag.shape hSh) _
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
    (_ho : ModalSys.Opt = true → Env.CollapseOpt h d env₁ env₂ := by wit_triv) →
    (M.sat env₂ (WFF.collapse h hs φ) ↔ M.sat env₁ φ)
  | _, _, _, _, _, _, _, _, _, hag, .atom ρ, _ => relSat_collapse hag ρ Fin.elim0
  | 0, _, _, h, _, _, env₁, env₂, hs, hag, .optx hO .arrow y hy φ, ho => by
      have hO' := ho hO
      obtain ⟨X₀, hy₀⟩ := hy
      have he := hO'.zero y X₀ hy₀ rfl
      constructor
      · rintro ⟨X, h₂, hd, hsat⟩
        obtain rfl : X₀ = X := Option.some.inj (((h.wit y X₀ hy₀).1 rfl).symm.trans h₂)
        have hd₁ : (env₁.wit y X₀ hy₀).Dom := by rw [he]; exact hd
        refine ⟨X₀, hy₀, hd₁, ?_⟩
        exact (sat_collapse (hs.optIn y) (hag.optPush_zero hO' hO hy₀ hd₁ hd) φ
          (fun _ => hO'.optPush_zero hO hy₀ hd₁ hd)).mp hsat
      · rintro ⟨X, hy', hd₁, hsat⟩
        obtain rfl : X₀ = X := Option.some.inj (hy₀.symm.trans hy')
        have hd : (env₂.witT y ((h.wit y X₀ hy₀).1 rfl)).Dom := by rw [← he]; exact hd₁
        refine ⟨X₀, (h.wit y X₀ hy₀).1 rfl, hd, ?_⟩
        exact (sat_collapse (hs.optIn y) (hag.optPush_zero hO' hO hy₀ hd₁ hd) φ
          (fun _ => hO'.optPush_zero hO hy₀ hd₁ hd)).mpr hsat
  | k + 1, _, _, h, _, _, env₁, env₂, hs, hag, .optx hO .arrow y hy φ, ho => by
      have hO' := ho hO
      obtain ⟨X₀, hy₀⟩ := hy
      have he := hO'.succ y X₀ hy₀ k rfl
      constructor
      · rintro ⟨X, h₂, hd, hsat⟩
        obtain rfl : X₀ = X := Option.some.inj (((h.wit y X₀ hy₀).2 k rfl).symm.trans h₂)
        have hd₁ : (env₁.wit y X₀ hy₀).Dom := by rw [he]; exact hd
        refine ⟨X₀, hy₀, hd₁, ?_⟩
        exact (sat_collapse (hs.optIn y) (hag.optPush_succ hO' hy₀ hd₁ hd) φ
          (fun _ => hO'.optPush_succ hy₀ hd₁ hd)).mp hsat
      · rintro ⟨X, hy', hd₁, hsat⟩
        obtain rfl : X₀ = X := Option.some.inj (hy₀.symm.trans hy')
        have hd : (env₂.wit (y.collapse k) X₀ ((h.wit y X₀ hy₀).2 k rfl)).Dom := by
          rw [← he]; exact hd₁
        refine ⟨X₀, (h.wit y X₀ hy₀).2 k rfl, hd, ?_⟩
        exact (sat_collapse (hs.optIn y) (hag.optPush_succ hO' hy₀ hd₁ hd) φ
          (fun _ => hO'.optPush_succ hy₀ hd₁ hd)).mpr hsat
  | k, _, _, h, _, _, env₁, env₂, hs, hag, .optx hO .ident y hy φ, ho => by
      have hO' := ho hO
      obtain ⟨X₀, hy₀⟩ := hy
      have he : env₁.witT y hy₀ = env₂.witT (y.collapse k) (h.witT hy₀) := by
        unfold Env.witT
        rw [hag y _ (Ctx.witT_spec hy₀).2.2]
      constructor
      · rintro ⟨X, h₂, hd, hsat⟩
        obtain rfl : X₀ = X := Option.some.inj ((h.witT hy₀).symm.trans h₂)
        have hd₁ : (env₁.witT y hy₀).Dom := by rw [he]; exact hd
        refine ⟨X₀, hy₀, hd₁, ?_⟩
        exact (sat_collapse (hs.optInT y) (hag.optPushT hO' hy₀ hd₁ hd) φ
          (fun _ => hO'.optPushT hy₀ hd₁ hd)).mp hsat
      · rintro ⟨X, hy', hd₁, hsat⟩
        obtain rfl : X₀ = X := Option.some.inj (hy₀.symm.trans hy')
        have hd : (env₂.witT (y.collapse k) (h.witT hy₀)).Dom := by rw [← he]; exact hd₁
        refine ⟨X₀, h.witT hy₀, hd, ?_⟩
        exact (sat_collapse (hs.optInT y) (hag.optPushT hO' hy₀ hd₁ hd) φ
          (fun _ => hO'.optPushT hy₀ hd₁ hd)).mpr hsat
  | _, _, _, _, _, _, _, _, _, hag, .eq t s, _ => by
      change interp _ (Term.collapse _ t) = interp _ (Term.collapse _ s) ↔ _
      rw [interp_collapse hag t, interp_collapse hag s]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .top, _ => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .bot, _ => Iff.rfl
  | _, _, _, _, _, _, _, _, hs, hag, .and φ ψ, ho =>
      and_congr (sat_collapse hs hag φ ho) (sat_collapse hs hag ψ ho)
  | _, _, _, _, _, _, _, _, hs, hag, .or φ ψ, ho =>
      or_congr (sat_collapse hs hag φ ho) (sat_collapse hs hag ψ ho)
  | _, _, _, _, _, _, _, _, hs, hag, .imp φ ψ, ho =>
      imp_congr (sat_collapse hs hag φ ho) (sat_collapse hs hag ψ ho)
  | _, _, _, _, _, _, _, _, hs, hag, .all _ φ, ho =>
      forall_congr' fun o => sat_collapse (hs.insert _) (hag.extend (hs.rootFresh le_rfl) o) φ
        fun hO => (ho hO).extend (hs.rootFresh le_rfl) ((ho hO).slots.rootFresh le_rfl).root
          ((ho hO).slots.insert _) o
  | _, _, _, _, _, _, _, _, hs, hag, .ex _ φ, ho =>
      exists_congr fun o => sat_collapse (hs.insert _) (hag.extend (hs.rootFresh le_rfl) o) φ
        fun hO => (ho hO).extend (hs.rootFresh le_rfl) ((ho hO).slots.rootFresh le_rfl).root
          ((ho hO).slots.insert _) o
  | _, _, _, _, _, _, _, _, hs, hag, .box φ, ho =>
      forall_congr' fun w' => sat_collapse hs.boxIn (hag.boxPush w') φ
        fun hO => (ho hO).boxPush hag w'
  | k, _, _, h, _, _, env₁, env₂, hs, hag, .dia x hx φ, ho => by
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
        exact (sat_collapse (hs.diaIn x) (hag.diaPush hr ⟨w₂.1, _⟩ w₂.2) φ
          fun hO => (ho hO).diaPush hag hr ⟨w₂.1, _⟩ w₂.2).mp hsat
      · rintro ⟨X, hr, w₁, hsat⟩
        have href := hag x _ hr
        exact ⟨X, h x _ hr, ⟨w₁.1, by rw [← href]; exact w₁.2⟩,
          (sat_collapse (hs.diaIn x) (hag.diaPush hr w₁ _) φ
            fun hO => (ho hO).diaPush hag hr w₁ _).mpr hsat⟩
  | _, _, _, _, _, _, _, _, _, hag, .here hT s t, _ => by
      change Model.Realised hT (interp _ (Term.collapse _ s)) (interp _ (Term.collapse _ t)) ↔ _
      rw [interp_collapse hag s, interp_collapse hag t]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, _, hag, .back hB L s t, _ => by
      change Model.Backs L (interp _ (Term.collapse _ s)) (interp _ (Term.collapse _ t)) ↔ _
      rw [interp_collapse hag s, interp_collapse hag t]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, hs, hag, .retS hB S t Φ, _ =>
      exists_congr fun a => exists_congr fun e =>
        and_congr (sat_collapse (hs.boxIn.insert _)
            ((hag.boxPush a).extend (hs.boxIn.rootFresh le_rfl) e) Φ)
          (by rw [interp_collapse hag t])
  | k, _, _, h, _, _, env₁, env₂, hs, hag, .retxS hB y hy S t Φ, _ => by
      constructor
      · rintro ⟨Y, h₂, a, e, hsat, hr⟩
        obtain ⟨Y₀, hy₀⟩ := hy
        have hYY : Y₀ = Y := by
          have e' := h y _ hy₀
          rw [h₂] at e'
          cases e'
          rfl
        subst hYY
        have href := hag y _ hy₀
        refine ⟨Y₀, hy₀, ⟨a.1, by rw [href]; exact a.2⟩, e, ?_, ?_⟩
        · exact (sat_collapse ((hs.diaIn y).insert _)
            ((hag.diaPush hy₀ ⟨a.1, _⟩ a.2).extend ((hs.diaIn y).rootFresh le_rfl) e) Φ).mp hsat
        · rw [interp_collapse hag t] at hr
          exact hr
      · rintro ⟨Y, hr', a, e, hsat, hr⟩
        have href := hag y _ hr'
        refine ⟨Y, h y _ hr', ⟨a.1, by rw [← href]; exact a.2⟩, e,
          (sat_collapse ((hs.diaIn y).insert _)
            ((hag.diaPush hr' a _).extend ((hs.diaIn y).rootFresh le_rfl) e) Φ).mpr hsat, ?_⟩
        rw [interp_collapse hag t]
        exact hr
  | _, _, _, _, _, _, _, _, hs, hag, .link hV hF t Φ, _ =>
      forall_congr' fun a => by
        rw [interp_collapse hag t]
        exact sat_collapse (hs.boxIn.insert _)
          ((hag.boxPush a).extend (hs.boxIn.rootFresh le_rfl) _) Φ
  | k, _, _, h, _, _, env₁, env₂, hs, hag, .linkx hV hF y hy t Φ, _ => by
      constructor
      · rintro ⟨Y, h₂, a, hsat⟩
        obtain ⟨Y₀, hy₀⟩ := hy
        have hYY : Y₀ = Y := by
          have e' := h y _ hy₀
          rw [h₂] at e'
          cases e'
          rfl
        subst hYY
        have href := hag y _ hy₀
        refine ⟨Y₀, hy₀, ⟨a.1, by rw [href]; exact a.2⟩, ?_⟩
        rw [interp_collapse hag t] at hsat
        exact (sat_collapse ((hs.diaIn y).insert _)
          ((hag.diaPush hy₀ ⟨a.1, _⟩ a.2).extend ((hs.diaIn y).rootFresh le_rfl) _) Φ).mp hsat
      · rintro ⟨Y, hr', a, hsat⟩
        have href := hag y _ hr'
        refine ⟨Y, h y _ hr', ⟨a.1, by rw [← href]; exact a.2⟩, ?_⟩
        rw [interp_collapse hag t]
        exact (sat_collapse ((hs.diaIn y).insert _)
          ((hag.diaPush hr' a _).extend ((hs.diaIn y).rootFresh le_rfl) _) Φ).mpr hsat

/-- ⭐The semantic content of the T rule: a collapsed `□`-body holds exactly when the body holds
    at the current world. -/
theorem sat_boxHere (hT : ModalSys.T = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (hs : Γ.boxIn.SlotsFrom 0) (φ : WFF σ Γ.boxIn 0)
    (ho : ModalSys.Opt = true → env.OpenedT ∧ Γ.SlotsFrom 0 := by wit_triv) :
    M.sat env (WFF.collapse (Ctx.collapses_boxIn_self hT Γ) hs φ) ↔
      M.sat (env.boxPush ⟨w, ⟨M.frame.refl hT w⟩⟩) φ :=
  sat_collapse hs (Env.collapseAgree_self hT env) φ fun hO =>
    ⟨fun _ _ _ _ => rfl, fun _ _ _ k' hk => absurd hk.symm (Nat.succ_ne_zero k'), (ho hO).1,
      (ho hO).2⟩

end Model

end V12M
