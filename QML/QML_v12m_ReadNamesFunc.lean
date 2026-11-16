import QML.QML_v12m_TCanonRead
import QML.QML_v12m_CanonFunc

/-!
# QML v12m — reading at names: the function algebra

What the canonical tree with T needs of `readNames` beyond typing (docs §12.36, step 4), all
mirroring `collapse`'s versions:

* `Ctx.RefNoAt`: no reachable address has an `at` step; it passes into views.  ⭐
  `Term.readNames_noAt`: reading at names then fixes a term (up to weakening).
* `VarSymb.RNC`: the side condition under which ⭐**reading at names commutes with collapsing**
  (`VarSymb.readNames_collapse`, `Term.readNames_collapse`).  Collapsing turns `u.dia` into `u.at`,
  which a later reading would rename when `u` is named, so the commutation is not universal; `RNC`
  rules out exactly the configurations reached at level 0.  It holds of every address of a `□` view
  at level 0 (`Ctx.refRNC_boxIn_zero`) and passes into views, which is what `extract` needs.
* ⭐`applyG_readNames`: applying a definable map commutes with reading at names.
-/

namespace V12M

variable [ModalSys]

/-! ## No reachable `at` step -/

/-- No address the context reaches has an `at` step. -/
def Ctx.RefNoAt (Γ : Ctx) : Prop := ∀ v T, Γ.ref v = some T → v.NoAt

omit [ModalSys] in
theorem Step.ne_at_of_isStruct {s : Step} (hs : s.isStruct = true) : s ≠ .at := by
  rintro rfl
  cases hs

/-- A context declaring no `at` step reaches none. -/
theorem Ctx.RefNoAt.of_noAt {Γ : Ctx} (h : Γ.NoAt) : Γ.RefNoAt := by
  intro v
  induction v with
  | root _ => intro _ _; trivial
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.ref u with
        | none => rw [hU] at hv; cases hv
        | some U => exact ⟨Step.ne_at_of_isStruct hs, ih U hU⟩
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        exact h _ _ hv

theorem Ctx.RefNoAt.boxIn {Γ : Ctx} (h : Γ.RefNoAt) : Γ.boxIn.RefNoAt := by
  intro v
  induction v with
  | root _ => intro _ _; trivial
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.boxIn.ref u with
        | none => rw [hU] at hv; cases hv
        | some U => exact ⟨Step.ne_at_of_isStruct hs, ih U hU⟩
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        cases s with
        | box => exact ⟨nofun, h u _ (Ctx.boxIn_box hv).2⟩
        | keep => exact ⟨nofun, h u _ (Ctx.boxIn_keep hv).2.1⟩
        | _ => first | exact absurd rfl hs | cases hv

theorem Ctx.RefNoAt.diaIn {Γ : Ctx} (h : Γ.RefNoAt) (x : VarSymb) : (Γ.diaIn x).RefNoAt := by
  intro v
  induction v with
  | root _ => intro _ _; trivial
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : (Γ.diaIn x).ref u with
        | none => rw [hU] at hv; cases hv
        | some U => exact ⟨Step.ne_at_of_isStruct hs, ih U hU⟩
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        cases s with
        | dia =>
            change (if u = x then (match Γ.ref x with
              | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
            split_ifs at hv with hux
            subst hux
            cases hx : Γ.ref u with
            | none => rw [hx] at hv; cases hv
            | some U => exact ⟨nofun, h u U hx⟩
        | box => exact ⟨nofun, h u _ (Ctx.boxIn_box (Γ := Γ) hv).2⟩
        | keep => exact ⟨nofun, h u _ (Ctx.boxIn_keep (Γ := Γ) hv).2.1⟩
        | _ => first | exact absurd rfl hs | cases hv

/-! ## Reading at names fixes a term with no `at` step -/

/-- Every address the context reaches is fixed by reading at names at level `k`. -/
def Ctx.RefFix (ν : VarSymb → Option VarSymb) (k : ℕ) (Γ : Ctx) : Prop :=
  ∀ v T, Γ.ref v = some T → v.readNames ν k = v

theorem Ctx.RefNoAt.refFix {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ : Ctx} (h : Γ.RefNoAt) :
    Γ.RefFix ν k :=
  fun v T hv => VarSymb.readNames_noAt (h v T hv)

/-- ⭐With no top-level identity reading, every reachable address is fixed at level 0. -/
theorem Ctx.RefFix.of_noTopAt {ν : VarSymb → Option VarSymb} {Γ : Ctx} (h : Γ.NoTopAt) :
    Γ.RefFix ν 0 := by
  intro v
  induction v with
  | root _ => intro _ _; rfl
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.ref u with
        | none => rw [hU] at hv; cases hv
        | some U => rw [VarSymb.readNames_struct hs, ih U hU]
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        exact VarSymb.readNames_raw h (Bool.eq_false_iff.mpr hs) hv

theorem Ctx.RefFix.boxIn {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ : Ctx} (h : Γ.RefFix ν k) :
    Γ.boxIn.RefFix ν (k + 1) := by
  intro v
  induction v with
  | root _ => intro _ _; rfl
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.boxIn.ref u with
        | none => rw [hU] at hv; cases hv
        | some U => rw [VarSymb.readNames_struct hs, ih U hU]
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        have hl := Ctx.boxIn_level hv
        rw [VarSymb.readNames_level_succ hl]
        cases s with
        | box => rw [h u _ (Ctx.boxIn_box hv).2]
        | keep => rw [h u _ (Ctx.boxIn_keep hv).2.1]
        | dia => cases (show (none : Option VarType) = some T from hv)
        | _ => cases hl

theorem Ctx.RefFix.diaIn {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ : Ctx} (h : Γ.RefFix ν k)
    (x : VarSymb) : (Γ.diaIn x).RefFix ν (k + 1) := by
  intro v
  induction v with
  | root _ => intro _ _; rfl
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : (Γ.diaIn x).ref u with
        | none => rw [hU] at hv; cases hv
        | some U => rw [VarSymb.readNames_struct hs, ih U hU]
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        have hl := Ctx.diaIn_level hv
        rw [VarSymb.readNames_level_succ hl]
        cases s with
        | dia =>
            change (if u = x then (match Γ.ref x with
              | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
            split_ifs at hv with hux
            subst hux
            cases hx : Γ.ref u with
            | none => rw [hx] at hv; cases hv
            | some U => rw [h u U hx]
        | box => rw [h u _ (Ctx.boxIn_box (Γ := Γ) hv).2]
        | keep => rw [h u _ (Ctx.boxIn_keep (Γ := Γ) hv).2.1]
        | _ => cases hl

mutual
  theorem Func.readNames_noAt {σ : Signature} {ν : VarSymb → Option VarSymb} {k : ℕ}
      {Γ₁ Γ₂ : Ctx} (h : Ctx.ReadsNames ν k Γ₁ Γ₂) (l : Γ₁.Le Γ₂) (hna : Γ₁.RefFix ν k) :
      {n : ℕ} → (f : Func σ Γ₁ n) → Func.readNames h f = Func.mono l f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.readNames h g) (Term.readNames h t) =
          Func.eval (Func.mono l g) (Term.mono l t)
        rw [Func.readNames_noAt h l hna g,
          eq_of_heq (Sigma.mk.inj (Term.readNames_noAt h l hna t)).2]
    termination_by structural _ f => f

  /-- ⭐Reading at names fixes a term whose context reaches no `at` step. -/
  theorem Term.readNames_noAt {σ : Signature} {ν : VarSymb → Option VarSymb} {k : ℕ}
      {Γ₁ Γ₂ : Ctx} (h : Ctx.ReadsNames ν k Γ₁ Γ₂) (l : Γ₁.Le Γ₂) (hna : Γ₁.RefFix ν k) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      (⟨_, Term.readNames h t⟩ : Σ b, Term σ Γ₂ T b) = ⟨_, Term.mono l t⟩
    | _, _, .var v hv => sig_var (hna v _ hv) _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.readNames h f)⟩ : Σ b, Term σ Γ₂ .Var b) =
          ⟨_, Term.func (Func.mono l f)⟩
        rw [Func.readNames_noAt h l hna f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.readNames_noAt h l hna s) (Term.readNames_noAt h l hna t)
    | _, _, .boxtm t => sig_boxtm (Term.readNames_noAt h.boxIn l.boxIn hna.boxIn t)
    | _, _, .diatm x hx t => by
        have hxe : x.readNames ν k = x := by
          obtain ⟨X, hX⟩ := hx
          exact hna x _ hX
        have key : ∀ (y : VarSymb) (_hy : x = y) (P : ∃ X, Γ₂.ref y = some (.VTypeDia X))
            (h' : Ctx.ReadsNames ν (k + 1) (Γ₁.diaIn x) (Γ₂.diaIn y)),
            (⟨_, Term.diatm y P (Term.readNames h' t)⟩ : Σ b, Term σ Γ₂ _ b) =
              ⟨_, Term.mono l (Term.diatm x hx t)⟩ := by
          intro y hy P h'
          subst hy
          exact sig_diatm (Term.readNames_noAt h' (l.diaIn x) (hna.diaIn x) t)
        exact key _ hxe.symm _ _
    termination_by structural _ _ t => t
end

/-! ## Reading an η-expansion -/

theorem VarSymb.inner_readNames_succ {ν : VarSymb → Option VarSymb} {k : ℕ} (w : VarSymb) :
    w.inner.readNames ν (k + 1) = (w.readNames ν k).inner := by
  by_cases hk : ModalSys.keepOnly = true
  · rw [VarSymb.inner_keepOnly hk, VarSymb.inner_keepOnly hk,
      VarSymb.readNames_proj (s := .here) rfl (fun h => by cases h.2),
      VarSymb.readNames_level_succ (s := .keep) rfl]
  · have hk' : ModalSys.keepOnly = false := Bool.eq_false_iff.mpr hk
    rw [VarSymb.inner_box hk', VarSymb.inner_box hk', VarSymb.readNames_level_succ (s := .box) rfl]

/-- Reading an η-expansion at names expands the renamed address. -/
theorem Term.readNames_eta {σ : Signature} {ν : VarSymb → Option VarSymb} :
    ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.ReadsNames ν k Γ₁ Γ₂) (w : VarSymb) (T : VarType)
      (hw : Γ₁.ref w = some T),
    (⟨_, Term.readNames h (Term.eta (σ := σ) w T hw)⟩ : Σ b, Term σ Γ₂ T b) =
      ⟨_, Term.eta (w.readNames ν k) T (h w T hw)⟩
  | _, _, _, _, _, .Var, _ => rfl
  | _, _, _, _, _, .VTypeOne, _ => rfl
  | _, _, _, h, w, .VTypeProd A B, hw =>
      sig_pair
        ((Term.readNames_eta h (.step w .fst) A (Ctx.ref_fst_of hw)).trans
          (Term.eta_congr (VarSymb.readNames_proj (s := .fst) rfl (fun h => by cases h.2)) A _ _))
        ((Term.readNames_eta h (.step w .snd) B (Ctx.ref_snd_of hw)).trans
          (Term.eta_congr (VarSymb.readNames_proj (s := .snd) rfl (fun h => by cases h.2)) B _ _))
  | _, _, _, h, w, .VTypeBox A, hw =>
      sig_boxtm ((Term.readNames_eta h.boxIn w.inner A (Ctx.ref_inner hw)).trans
        (Term.eta_congr (VarSymb.inner_readNames_succ w) A _ _))
  | _, _, _, h, w, .VTypeDia A, hw =>
      sig_diatm ((Term.readNames_eta (h.diaIn w) (.step w .dia) A (Ctx.ref_diaIn_of hw)).trans
        (Term.eta_congr (VarSymb.readNames_level_succ (s := .dia) rfl) A _ _))

/-! ## Reading at names commutes with collapsing -/

namespace VarSymb

/-- ⭐The side condition for reading at names to commute with collapsing at level `m`: along the
    recursion of both, an `at` step met at level 0 is not on a named witness after collapsing, and
    a `dia` step collapsed at level 0 (to `at`) is not on a named witness. -/
def RNC (ν : VarSymb → Option VarSymb) : ℕ → VarSymb → Prop
  | _, .root _ => True
  | m, .step u s =>
      if s.isProj then (m = 0 → s = .at → ν (u.collapse 0) = none) ∧ RNC ν m u
      else match m with
        | 0 => s = .dia → ν u = none
        | m + 1 => RNC ν m u

theorem RNC_proj {ν : VarSymb → Option VarSymb} {m : ℕ} {u : VarSymb} {s : Step}
    (hs : s.isProj = true) :
    RNC ν m (.step u s) ↔ (m = 0 → s = .at → ν (u.collapse 0) = none) ∧ RNC ν m u := by
  simp only [RNC, hs, if_true]

theorem RNC_level_zero {ν : VarSymb → Option VarSymb} {u : VarSymb} {s : Step}
    (hs : s.isProj = false) : RNC ν 0 (.step u s) ↔ (s = .dia → ν u = none) := by
  simp only [RNC, hs, Bool.false_eq_true, if_false]

theorem RNC_level_succ {ν : VarSymb → Option VarSymb} {m : ℕ} {u : VarSymb} {s : Step}
    (hs : s.isProj = false) : RNC ν (m + 1) (.step u s) ↔ RNC ν m u := by
  simp only [RNC, hs, Bool.false_eq_true, if_false]

/-- ⭐**Reading at names commutes with collapsing**, under `RNC`. -/
theorem readNames_collapse {ν : VarSymb → Option VarSymb} (j : ℕ) :
    ∀ (m : ℕ) (v : VarSymb), v.RNC ν m →
      (v.readNames ν (j + m + 1)).collapse m = (v.collapse m).readNames ν (j + m)
  | _, .root _, _ => rfl
  | m, .step u s, h => by
      by_cases hs : s.isProj = true
      · obtain ⟨h0, hu⟩ := (RNC_proj hs).mp h
        rw [readNames_proj hs (fun hk => absurd hk.1 (by omega)), collapse_proj hs,
          collapse_proj hs]
        by_cases hk : j + m = 0 ∧ s = .at
        · obtain ⟨hjm, rfl⟩ := hk
          obtain rfl : m = 0 := by omega
          obtain rfl : j = 0 := by omega
          rw [readNames_at_unnamed (h0 rfl rfl), readNames_collapse 0 0 u hu]
        · rw [readNames_proj hs hk, readNames_collapse j m u hu]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        rw [readNames_level_succ hs']
        cases m with
        | zero =>
            have hd := (RNC_level_zero hs').mp h
            cases s with
            | box =>
                rw [collapse_level_zero (s := .box) rfl (by decide) (by decide),
                  collapse_level_zero (s := .box) rfl (by decide) (by decide),
                  readNames_proj (s := .here) rfl (fun h => by cases h.2)]
            | keep => rfl
            | dia =>
                rw [collapse_dia_zero, collapse_dia_zero]
                by_cases hk : j + 0 = 0 ∧ Step.diaZero = .at
                · obtain ⟨hj, hz⟩ := hk
                  obtain rfl : j = 0 := by omega
                  rw [hz, readNames_at_unnamed (hd rfl)]
                · rw [readNames_proj Step.diaZero_isProj hk]
            | _ => exact absurd rfl hs
        | succ m =>
            rw [collapse_level_succ hs', collapse_level_succ hs',
              show j + (m + 1) = (j + m) + 1 by omega, readNames_level_succ hs',
              readNames_collapse j m u ((RNC_level_succ hs').mp h)]

end VarSymb

/-- Every address a context reaches satisfies `RNC` at level `m`. -/
def Ctx.RefRNC (ν : VarSymb → Option VarSymb) (m : ℕ) (Γ : Ctx) : Prop :=
  ∀ v T, Γ.ref v = some T → v.RNC ν m

/-- An address reached by struct steps from one satisfying `RNC` at a positive level does. -/
theorem VarSymb.RNC_struct_succ {ν : VarSymb → Option VarSymb} {m : ℕ} {u : VarSymb} {s : Step}
    (hs : s.isStruct = true) (h : u.RNC ν (m + 1)) : (VarSymb.step u s).RNC ν (m + 1) :=
  (VarSymb.RNC_proj (Step.isProj_of_isStruct hs)).mpr ⟨fun h0 => absurd h0 (by omega), h⟩

/-- ⭐**Every address of a `□` view satisfies `RNC` at level 0**: it ends in a level step followed
    by structural steps only. -/
theorem Ctx.refRNC_boxIn_zero (ν : VarSymb → Option VarSymb) (Γ : Ctx) :
    Γ.boxIn.RefRNC ν 0 := by
  intro v
  induction v with
  | root _ => intro _ _; trivial
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.boxIn.ref u with
        | none => rw [hU] at hv; cases hv
        | some U =>
            exact (VarSymb.RNC_proj (Step.isProj_of_isStruct hs)).mpr
              ⟨fun _ hat => absurd hat (Step.ne_at_of_isStruct hs), ih U hU⟩
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        have hl := Ctx.boxIn_level hv
        exact (VarSymb.RNC_level_zero hl).mpr fun hd => by subst hd; cases hv

theorem Ctx.RefRNC.boxIn {ν : VarSymb → Option VarSymb} {m : ℕ} {Γ : Ctx}
    (h : Γ.RefRNC ν m) : Γ.boxIn.RefRNC ν (m + 1) := by
  intro v
  induction v with
  | root _ => intro _ _; trivial
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.boxIn.ref u with
        | none => rw [hU] at hv; cases hv
        | some U => exact VarSymb.RNC_struct_succ hs (ih U hU)
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        have hl := Ctx.boxIn_level hv
        refine (VarSymb.RNC_level_succ hl).mpr ?_
        cases s with
        | box => exact h u _ (Ctx.boxIn_box hv).2
        | keep => exact h u _ (Ctx.boxIn_keep hv).2.1
        | dia => cases (show (none : Option VarType) = some T from hv)
        | _ => cases hl

theorem Ctx.RefRNC.diaIn {ν : VarSymb → Option VarSymb} {m : ℕ} {Γ : Ctx}
    (h : Γ.RefRNC ν m) (x : VarSymb) : (Γ.diaIn x).RefRNC ν (m + 1) := by
  intro v
  induction v with
  | root _ => intro _ _; trivial
  | step u s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : (Γ.diaIn x).ref u with
        | none => rw [hU] at hv; cases hv
        | some U => exact VarSymb.RNC_struct_succ hs (ih U hU)
      · rw [Ctx.ref_step_nonproj _ _ hs] at hv
        have hl := Ctx.diaIn_level hv
        refine (VarSymb.RNC_level_succ hl).mpr ?_
        cases s with
        | dia =>
            change (if u = x then (match Γ.ref x with
              | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
            split_ifs at hv with hux
            subst hux
            cases hx : Γ.ref u with
            | none => rw [hx] at hv; cases hv
            | some U => exact h u U hx
        | box => exact h u _ (Ctx.boxIn_box (Γ := Γ) hv).2
        | keep => exact h u _ (Ctx.boxIn_keep (Γ := Γ) hv).2.1
        | _ => cases hl

mutual
  theorem Func.readNames_collapse {σ : Signature} {ν : VarSymb → Option VarSymb} {j m : ℕ}
      {Γa Γb Γc Γd : Ctx} (hA : Ctx.ReadsNames ν (j + m + 1) Γa Γb)
      (C₁ : Ctx.Collapses m Γa Γc) (C₂ : Ctx.Collapses m Γb Γd)
      (hB : Ctx.ReadsNames ν (j + m) Γc Γd) (hr : Γa.RefRNC ν m) :
      {n : ℕ} → (f : Func σ Γa n) →
      Func.collapse C₂ (Func.readNames hA f) = Func.readNames hB (Func.collapse C₁ f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.collapse C₂ (Func.readNames hA g))
            (Term.collapse C₂ (Term.readNames hA t)) =
          Func.eval (Func.readNames hB (Func.collapse C₁ g))
            (Term.readNames hB (Term.collapse C₁ t))
        rw [Func.readNames_collapse hA C₁ C₂ hB hr g,
          eq_of_heq (Sigma.mk.inj (Term.readNames_collapse hA C₁ C₂ hB hr t)).2]
    termination_by structural _ f => f

  /-- ⭐**Reading at names commutes with collapsing**, on a context whose addresses satisfy
      `RNC`. -/
  theorem Term.readNames_collapse {σ : Signature} {ν : VarSymb → Option VarSymb} {j m : ℕ}
      {Γa Γb Γc Γd : Ctx} (hA : Ctx.ReadsNames ν (j + m + 1) Γa Γb)
      (C₁ : Ctx.Collapses m Γa Γc) (C₂ : Ctx.Collapses m Γb Γd)
      (hB : Ctx.ReadsNames ν (j + m) Γc Γd) (hr : Γa.RefRNC ν m) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γa T a) →
      (⟨_, Term.collapse C₂ (Term.readNames hA t)⟩ : Σ b, Term σ Γd T b) =
        ⟨_, Term.readNames hB (Term.collapse C₁ t)⟩
    | _, _, .var v hv => sig_var (VarSymb.readNames_collapse j m v (hr v _ hv)) _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.collapse C₂ (Func.readNames hA f))⟩ :
            Σ b, Term σ Γd .Var b) = ⟨_, Term.func (Func.readNames hB (Func.collapse C₁ f))⟩
        rw [Func.readNames_collapse hA C₁ C₂ hB hr f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.readNames_collapse hA C₁ C₂ hB hr s)
          (Term.readNames_collapse hA C₁ C₂ hB hr t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.readNames_collapse (m := m + 1) hA.boxIn C₁.boxIn C₂.boxIn hB.boxIn
          hr.boxIn t)
    | _, _, .diatm y hy t => by
        obtain ⟨Y, hY⟩ := hy
        have key : ∀ (z : VarSymb) (_hz : z = (y.readNames ν (j + m + 1)).collapse m)
            (P : ∃ X, Γd.ref z = some (.VTypeDia X))
            (h' : Ctx.ReadsNames ν (j + m + 1) (Γc.diaIn (y.collapse m)) (Γd.diaIn z)),
            (⟨_, Term.collapse C₂ (Term.readNames hA (Term.diatm y ⟨Y, hY⟩ t))⟩ :
              Σ b, Term σ Γd _ b) =
              ⟨_, Term.diatm z P (Term.readNames h' (Term.collapse (C₁.diaIn y) t))⟩ := by
          intro z hz P h'
          subst hz
          exact sig_diatm (Term.readNames_collapse (m := m + 1) (hA.diaIn y) (C₁.diaIn y)
            (C₂.diaIn _) h' (hr.diaIn y) t)
        exact key _ (VarSymb.readNames_collapse j m y (hr y _ hY)).symm _ _
    termination_by structural _ _ t => t
end

/-! ## Applying a definable map commutes with reading at names -/

section Apply

open Canon

variable {σ : Signature}

/-- A spine read at names. -/
def Spine.readNames {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) : {n : ℕ} → Spine σ Γ₁ n → Spine σ Γ₂ n
  | _, .nil => .nil
  | _, .cons t S => .cons (Term.readNames h t) (S.readNames h)

theorem Func.readNames_fill {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) :
    ∀ {n : ℕ} (S : Spine σ Γ₁ n) (f : Func σ Γ₁ n),
      Func.readNames h (S.fill f) = (S.readNames h).fill (Func.readNames h f)
  | _, .nil, _ => rfl
  | _, .cons t S, f => Func.readNames_fill h S (.eval f t)

theorem Spine.readNames_ofFn {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) :
    ∀ {n : ℕ} (ts : Fin n → Term σ Γ₁ .Var .var),
      (Spine.ofFn ts).readNames h = Spine.ofFn (fun k => Term.readNames h (ts k))
  | 0, _ => rfl
  | _ + 1, ts => congrArg (Spine.cons _) (Spine.readNames_ofFn h (fun k => ts k.succ))

theorem varTerm_readNames {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ₁ .Var b),
      varTerm (⟨p.1.readNames ν k, Term.readNames h p.2⟩ : Σ b : Ann .Var, Term σ Γ₂ .Var b) =
        Term.readNames h (varTerm p)
  | ⟨.var, _⟩ => rfl

/-- ⭐**Applying a definable map commutes with reading at names** (with `Opt` on: 4 is off). -/
theorem applyG_readNames (hO : ModalSys.Opt = true) :
    ∀ {A B : VarType} (g : GFunc σ A B) {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
      (h : Ctx.ReadsNames ν k Γ₁ Γ₂) {a : Ann A} (t : Term σ Γ₁ A a),
    applyG g (Term.readNames h t) =
      ⟨(applyG g t).1.readNames ν k, Term.readNames h (applyG g t).2⟩
  | _, _, .id _, _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, _, _, h, _, t => by
      have hf := applyG_readNames hO f h t
      simp only [applyG]
      rw [hf]
      exact applyG_readNames hO g h _
  | _, _, .fst, _, _, _, _, _, _, .pair _ _ => rfl
  | _, _, .snd, _, _, _, _, _, _, .pair _ _ => rfl
  | _, _, .pair f g, _, _, _, _, h, _, t => by
      have hf := applyG_readNames hO f h t
      have hg := applyG_readNames hO g h t
      simp only [applyG, Term.readNames]
      rw [hf, hg]
      rfl
  | _, _, .unit _, _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, _, _, h, _, t => by
      have hj : ∀ j, varTerm (applyG (args j) (Term.readNames h t)) =
          Term.readNames h (varTerm (applyG (args j) t)) := fun j => by
        rw [applyG_readNames hO (args j) h t]
        exact varTerm_readNames h _
      simp only [applyG, Term.readNames]
      rw [Func.readNames_fill, Spine.readNames_ofFn]
      simp only [hj]
      rfl
  | _, _, .boxMap f, _, _, _, _, h, _, .boxtm b => by
      have hf := applyG_readNames hO f h.boxIn b
      simp only [applyG, Term.readNames]
      rw [hf]
      rfl
  | _, _, .boxPair _ _, _, _, _, _, _, _, .pair (.boxtm _) (.boxtm _) => rfl
  | _, _, .boxUnit, _, _, _, _, _, _, .unit => rfl
  | _, _, .diaMap f, _, _, _, _, h, _, .diatm x _ c => by
      have hf := applyG_readNames hO f (h.diaIn x) c
      simp only [applyG, Term.readNames]
      rw [hf]
      rfl
  | _, _, .strength _ _, _, _, Γ₁, Γ₂, h, _, .pair (.boxtm b) (.diatm x _ c) => by
      simp only [applyG, Term.readNames]
      rw [Term.readNames_mono h.boxIn (h.diaIn x) (Ctx.le_boxIn_diaIn Γ₁ x)
        (Ctx.le_boxIn_diaIn Γ₂ _) b]
      rfl
  | _, _, .extract hT, _, k, Γ₁, Γ₂, h, _, .boxtm b => by
      simp only [applyG, Term.readNames]
      exact Term.readNames_collapse (j := k) (m := 0) h.boxIn
        (Ctx.collapses_boxIn_self hT Γ₁) (Ctx.collapses_boxIn_self hT Γ₂) h
        (Ctx.refRNC_boxIn_zero _ Γ₁) b
  | _, _, .dup hF, _, _, _, _, _, _, _ =>
      absurd hO (by rw [ModalSys.noOpt_of_Four hF]; decide)
  | _, _, .dkeep hF, _, _, _, _, _, _, _ =>
      absurd hO (by rw [ModalSys.noOpt_of_Four hF]; decide)

end Apply

end V12M

namespace V12M

variable [ModalSys]

/-- Reading at names keeps a formula's size. -/
theorem WFF.size_readNames {σ : Signature} {ν : VarSymb → Option VarSymb}
    (hν : ∀ y n, ν y = some n → ∀ e, n.rt ≠ .bnd e) :
    ∀ {k : ℕ} {Γ₁ Γ₂ : Ctx} {d : ℕ} (h : Ctx.ReadsNames ν k Γ₁ Γ₂) (hs : Γ₁.SlotsFrom d)
      (φ : WFF σ Γ₁ d), (WFF.readNames hν h hs φ).size = φ.size
  | _, _, _, _, _, _, .atom _ => rfl
  | _, _, _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, h, hs, .and φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_readNames hν h hs φ) (WFF.size_readNames hν h hs ψ)
  | _, _, _, _, h, hs, .or φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_readNames hν h hs φ) (WFF.size_readNames hν h hs ψ)
  | _, _, _, _, h, hs, .imp φ ψ =>
      congrArg₂ (· + · + 1) (WFF.size_readNames hν h hs φ) (WFF.size_readNames hν h hs ψ)
  | _, _, _, _, _, _, .all _ φ => congrArg (· + 1) (WFF.size_readNames hν _ _ φ)
  | _, _, _, _, _, _, .ex _ φ => congrArg (· + 1) (WFF.size_readNames hν _ _ φ)
  | _, _, _, _, _, _, .box φ => congrArg (· + 1) (WFF.size_readNames hν _ _ φ)
  | _, _, _, _, _, _, .dia _ _ φ => congrArg (· + 1) (WFF.size_readNames hν _ _ φ)
  | _, _, _, _, _, _, .here _ _ _ _ => rfl
  | _, _, _, _, _, _, .back _ _ _ _ => rfl
  | _, _, _, _, _, _, .retS _ S _ Φ =>
      congrArg (· + S.flat.eqRecSize + 1) (WFF.size_readNames hν _ _ Φ)
  | _, _, _, _, _, _, .retxS _ _ _ S _ Φ =>
      congrArg (· + S.flat.eqRecSize + 1) (WFF.size_readNames hν _ _ Φ)
  | _, _, _, _, _, _, .link _ _ _ Φ => congrArg (· + 1) (WFF.size_readNames hν _ _ Φ)
  | _, _, _, _, _, _, .linkx _ _ _ _ _ Φ => congrArg (· + 1) (WFF.size_readNames hν _ _ Φ)
  | _, _, _, _, _, _, .optx _ .arrow _ _ φ => congrArg (· + 1) (WFF.size_readNames hν _ _ φ)
  | _, _, _, _, _, _, .optx _ .ident _ _ φ => congrArg (· + 1) (WFF.size_readNames hν _ _ φ)

end V12M
