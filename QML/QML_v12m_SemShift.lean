import QML.QML_v12m_SemCollapse

/-!
# QML v12m — semantics of shifting (weak 4)

Shifting moves syntax one view further in.  Semantically it changes nothing, provided the two
environments agree across the shift (`Env.ShiftAgree`): every reachable address of the first view
has the value of its shifted address.

* Agreement passes into `□` and `◇_x` views and under binders.
* ⭐`Env.shiftAgree_twoBox`: under 4, the `□` view pushed to a world `s` two steps away agrees,
  across the shift, with the `□□` view pushed through the intermediate world `v` — `u.box` is `u`
  read at `s`, which is `u` kept at `v` and read at `s` (`u.keep.box`).
* ⭐`interp_shift`, ⭐`sat_shift`; hence `sat_shift_twoBox`, the semantic content of the 4 rule.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-! ## Agreement across a shift -/

/-- Two environments at one world agree across a shift. -/
def Env.ShiftAgree {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂) {w : M.frame.W}
    (env₁ : M.Env Γ₁ w) (env₂ : M.Env Γ₂ w) : Prop :=
  ∀ v T (hv : Γ₁.ref v = some T), env₁.ref v hv = env₂.ref (v.shift k) (h v T hv)

variable {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Shifts k Γ₁ Γ₂} {w : M.frame.W}
  {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w}

/-- It suffices to check the visible non-projection addresses. -/
theorem Env.ShiftAgree.of_raw
    (hvis : ∀ v T (hlp : v.lastProj = false) (hv : Γ₁ v = some T),
      env₁ v T hv = env₂.ref (v.shift k) (h v T ((Ctx.ref_nonproj Γ₁ hlp).trans hv))) :
    Env.ShiftAgree h env₁ env₂ := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · have hv₂ : Γ₂.ref (.step (v.shift k) s) = some T := by
          rw [← VarSymb.shift_proj hs]
          exact h _ T hv
        rw [Env.ref_congr env₂ (VarSymb.shift_proj hs) _ hv₂, Env.ref, Env.ref, dif_pos hs,
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

theorem Env.ShiftAgree.boxPush (hag : Env.ShiftAgree h env₁ env₂) (w' : M.frame.Acc w) :
    Env.ShiftAgree h.boxIn (env₁.boxPush w') (env₂.boxPush w') := by
  refine Env.ShiftAgree.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      rw [Env.ref_congr _ (VarSymb.shift_level_succ (s := .box) rfl) _
        (Ctx.ref_boxIn_of hk (h u _ hu)), Env.ref,
        dif_neg (by decide : ¬ Step.box.isProj = true)]
      change M.necEval (env₁.ref u hu) w' = M.necEval (env₂.ref (u.shift k) (h u _ hu)) w'
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      rw [Env.ref_congr _ (VarSymb.shift_level_succ (s := .keep) rfl) _
        (Ctx.ref_keep_of hF (h u _ hu)), Env.ref, dif_neg (by decide : ¬ Step.keep.isProj = true)]
      change M.necEval (GFunc.eval M.ops (GFunc.dup (σ := σ) hF) w (env₁.ref u hu)) w' =
        M.necEval (GFunc.eval M.ops (GFunc.dup (σ := σ) hF) w
          (env₂.ref (u.shift k) (h u _ hu))) w'
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem Env.ShiftAgree.diaPush (hag : Env.ShiftAgree h env₁ env₂) {x : VarSymb}
    {X : VarType} (hr : Γ₁.ref x = some (.VTypeDia X)) (w₁ : (M.posEval (env₁.ref x hr)).1)
    (hm : w₁.1 ∈ (M.posEval (env₂.ref (x.shift k) (h x _ hr))).1) :
    Env.ShiftAgree (h.diaIn x) (env₁.diaPush x hr w₁)
      (env₂.diaPush (x.shift k) (h x _ hr) ⟨w₁.1, hm⟩) := by
  refine Env.ShiftAgree.of_raw ?_
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
      rw [Env.ref_congr _ (VarSymb.shift_level_succ (s := .dia) rfl) _
        (Ctx.ref_diaIn_of (h u _ hr)), Env.ref, dif_neg (by decide : ¬ Step.dia.isProj = true)]
      simp only [Env.diaPush]
      exact posEval_snd_congr (hag u _ hr) w₁ hm
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ₁) hv
      rw [Env.ref_congr _ (VarSymb.shift_level_succ (s := .box) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_boxIn_of hk (h u _ hu))), Env.ref,
        dif_neg (by decide : ¬ Step.box.isProj = true)]
      change M.necEval (env₁.ref u hu) w₁.1 = M.necEval (env₂.ref (u.shift k) (h u _ hu)) w₁.1
      rw [hag u _ hu]
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep (Γ := Γ₁) hv
      rw [Env.ref_congr _ (VarSymb.shift_level_succ (s := .keep) rfl) _
        ((Ctx.le_boxIn_diaIn Γ₂ _).ref (Ctx.ref_keep_of hF (h u _ hu))), Env.ref,
        dif_neg (by decide : ¬ Step.keep.isProj = true)]
      change M.necEval (GFunc.eval M.ops (GFunc.dup (σ := σ) hF) w (env₁.ref u hu)) w₁.1 =
        M.necEval (GFunc.eval M.ops (GFunc.dup (σ := σ) hF) w
          (env₂.ref (u.shift k) (h u _ hu))) w₁.1
      rw [hag u _ hu]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem Env.ShiftAgree.extend (hag : Env.ShiftAgree h env₁ env₂) {r : Root}
    (hr : Γ₁.RootFresh r) {T : VarType} (o : M.frame.Dom T w) :
    Env.ShiftAgree (h.insert hr T) (env₁.extend r o) (env₂.extend r o) := by
  refine Env.ShiftAgree.of_raw ?_
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
      Env.ref_extend_ne env₂ o _ (h v U href) (by rwa [VarSymb.shift_rt])]

/-- ⭐Under 4, the `□` view at a world two steps away agrees, across the shift, with the `□□`
    view through the intermediate world. -/
theorem Env.shiftAgree_twoBox (hF : ModalSys.Four = true) {Γ : Ctx} (env : M.Env Γ w)
    (v : M.frame.Acc w) (s : M.frame.Acc v.1) :
    Env.ShiftAgree (Ctx.shifts_boxIn_boxIn hF Γ)
      (env.boxPush ⟨s.1, ⟨M.frame.trans hF v.2.down s.2.down⟩⟩)
      ((env.boxPush v).boxPush s) := by
  refine Env.ShiftAgree.of_raw ?_
  intro x T _ hx
  match x with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hx
      rw [Env.ref_congr _ (VarSymb.shift_level_zero (s := .box) rfl) _
        (Ctx.ref_boxIn_of hk (Ctx.ref_keep_of hF hu)), Env.ref,
        dif_neg (by decide : ¬ Step.box.isProj = true)]
      change M.necEval (env.ref u hu) ⟨s.1, _⟩ =
        M.necEval ((env.boxPush v).ref (.step u .keep) (Ctx.ref_keep_of hF hu)) s
      rw [Env.ref, dif_neg (by decide : ¬ Step.keep.isProj = true)]
      change _ = M.necEval (M.necEval (M.ops.necDup hF (env.ref u hu)) v) s
      rw [M.necDup_eval]
  | .step u .keep =>
      obtain ⟨_, hu, A, rfl⟩ := Ctx.boxIn_keep hx
      rw [Env.ref_congr _ (VarSymb.shift_level_zero (s := .keep) rfl) _
        (Ctx.ref_keep_of hF (Ctx.ref_keep_of hF hu)), Env.ref,
        dif_neg (by decide : ¬ Step.keep.isProj = true)]
      change M.necEval (M.ops.necDup hF (env.ref u hu)) ⟨s.1, _⟩ =
        M.necEval (M.ops.necDup hF ((env.boxPush v).ref (.step u .keep)
          (Ctx.ref_keep_of hF hu))) s
      rw [Env.ref, dif_neg (by decide : ¬ Step.keep.isProj = true)]
      change _ = M.necEval (M.ops.necDup hF (M.necEval (M.ops.necDup hF (env.ref u hu)) v)) s
      apply M.nec_inj
      funext t
      rw [M.necDup_eval, M.necDup_eval, M.necDup_eval, M.frame.trans_assoc hF]
  | .root _ => cases hx
  | .step _ .fst => cases hx
  | .step _ .snd => cases hx
  | .step _ .dia => cases hx
  | .step _ .here => cases hx

end Model

/-! ## Values and satisfaction are unchanged -/

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

mutual
  theorem interpFunc_shift {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Shifts k Γ₁ Γ₂} {w : M.frame.W}
      {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hag : Env.ShiftAgree h env₁ env₂) :
      ∀ {n : ℕ} (g : Func σ Γ₁ n) (args : Fin n → M.frame.D w),
        interpFunc env₂ (Func.shift h g) args = interpFunc env₁ g args
    | _, .F _, _ => rfl
    | _, .eval g t, args => by
        change interpFunc env₂ (Func.shift h g)
            (Fin.cons (interp env₂ (Term.shift h t)) args) =
          interpFunc env₁ g (Fin.cons (interp env₁ t) args)
        rw [interp_shift hag t, interpFunc_shift hag g]

  /-- ⭐Shifting does not change values. -/
  theorem interp_shift {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Shifts k Γ₁ Γ₂} {w : M.frame.W}
      {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hag : Env.ShiftAgree h env₁ env₂) :
      ∀ {T : VarType} {a : Ann T} (t : Term σ Γ₁ T a),
        interp env₂ (Term.shift h t) = interp env₁ t
    | _, _, .var v hv => (hag v _ hv).symm
    | _, _, .func f => interpFunc_shift hag f Fin.elim0
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change (interp env₂ (Term.shift h s), interp env₂ (Term.shift h t)) =
          (interp env₁ s, interp env₁ t)
        rw [interp_shift hag s, interp_shift hag t]
    | _, _, .boxtm t => by
        apply M.nec_inj
        funext w'
        change M.necEval (interp env₂ (Term.boxtm (Term.shift h.boxIn t))) w' = _
        rw [box_beta, box_beta, interp_shift (hag.boxPush w') t]
    | _, _, .diatm x hx t => by
        obtain ⟨X, hr⟩ := hx
        apply M.pos_inj
        change M.posEval (interp env₂
          (Term.diatm (x.shift k) _ (Term.shift (h.diaIn x) t))) = _
        rw [dia_beta env₂ _ (h x _ hr), dia_beta env₁ _ hr]
        exact posSec_ext (hag x _ hr).symm
          (fun w₂ => interp (env₂.diaPush (x.shift k) (h x _ hr) w₂)
            (Term.shift (h.diaIn x) t))
          (fun w₁ => interp (env₁.diaPush x hr w₁) t)
          (fun w₂ => interp_shift (hag.diaPush hr ⟨w₂.1, (hag x _ hr).symm ▸ w₂.2⟩ w₂.2) t)
end

theorem relSat_shift {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Shifts k Γ₁ Γ₂} {w : M.frame.W}
    {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hag : Env.ShiftAgree h env₁ env₂) :
    ∀ {n : ℕ} (ρ : Rel σ Γ₁ n) (args : Fin n → M.frame.D w),
      relSat env₂ (Rel.shift h ρ) args ↔ relSat env₁ ρ args
  | _, .R _, _ => Iff.rfl
  | _, .eval ρ t, args => by
      change relSat env₂ (Rel.shift h ρ) (Fin.cons (interp env₂ (Term.shift h t)) args) ↔
        relSat env₁ ρ (Fin.cons (interp env₁ t) args)
      rw [interp_shift hag t]
      exact relSat_shift hag ρ _

/-- ⭐Shifting does not change satisfaction. -/
theorem sat_shift : ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} {h : Ctx.Shifts k Γ₁ Γ₂} {d : ℕ}
    {w : M.frame.W} {env₁ : M.Env Γ₁ w} {env₂ : M.Env Γ₂ w} (hs : Γ₁.SlotsFrom d),
    Env.ShiftAgree h env₁ env₂ → (φ : WFF σ Γ₁ d) →
    (M.sat env₂ (WFF.shift h hs φ) ↔ M.sat env₁ φ)
  | _, _, _, _, _, _, _, _, _, hag, .atom ρ => relSat_shift hag ρ Fin.elim0
  | _, _, _, _, _, _, _, _, _, hag, .eq t s => by
      change interp _ (Term.shift _ t) = interp _ (Term.shift _ s) ↔ _
      rw [interp_shift hag t, interp_shift hag s]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .top => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, .bot => Iff.rfl
  | _, _, _, _, _, _, _, _, hs, hag, .and φ ψ =>
      and_congr (sat_shift hs hag φ) (sat_shift hs hag ψ)
  | _, _, _, _, _, _, _, _, hs, hag, .or φ ψ =>
      or_congr (sat_shift hs hag φ) (sat_shift hs hag ψ)
  | _, _, _, _, _, _, _, _, hs, hag, .imp φ ψ =>
      imp_congr (sat_shift hs hag φ) (sat_shift hs hag ψ)
  | _, _, _, _, _, _, _, _, hs, hag, .all _ φ =>
      forall_congr' fun o => sat_shift (hs.insert _) (hag.extend (hs.rootFresh le_rfl) o) φ
  | _, _, _, _, _, _, _, _, hs, hag, .ex _ φ =>
      exists_congr fun o => sat_shift (hs.insert _) (hag.extend (hs.rootFresh le_rfl) o) φ
  | _, _, _, _, _, _, _, _, hs, hag, .box φ =>
      forall_congr' fun w' => sat_shift hs.boxIn (hag.boxPush w') φ
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
        exact (sat_shift (hs.diaIn x) (hag.diaPush hr ⟨w₂.1, _⟩ w₂.2) φ).mp hsat
      · rintro ⟨X, hr, w₁, hsat⟩
        have href := hag x _ hr
        exact ⟨X, h x _ hr, ⟨w₁.1, by rw [← href]; exact w₁.2⟩,
          (sat_shift (hs.diaIn x) (hag.diaPush hr w₁ _) φ).mpr hsat⟩
  | _, _, _, _, _, _, _, _, _, hag, .here hT s t => by
      change Model.Realised hT (interp _ (Term.shift _ s)) (interp _ (Term.shift _ t)) ↔ _
      rw [interp_shift hag s, interp_shift hag t]
      exact Iff.rfl

/-- ⭐The semantic content of the 4 rule: a shifted `□`-body holds two steps in exactly when the
    body holds at the composite step. -/
theorem sat_shift_twoBox (hF : ModalSys.Four = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
    (hs : Γ.boxIn.SlotsFrom 0) (φ : WFF σ Γ.boxIn 0) (v : M.frame.Acc w) (s : M.frame.Acc v.1) :
    M.sat ((env.boxPush v).boxPush s) (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) hs φ) ↔
      M.sat (env.boxPush ⟨s.1, ⟨M.frame.trans hF v.2.down s.2.down⟩⟩) φ :=
  sat_shift hs (Env.shiftAgree_twoBox hF env v s) φ

end Model

end V12M
