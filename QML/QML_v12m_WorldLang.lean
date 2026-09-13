import QML.QML_v12m_StageSys

/-!
# QML v12m — the language of a world

A world's language grows in two directions:

* its **base** `base m` grows with `m`: the empty context or a presented starting context at the
  actual world, and at a world reached through a modality the view (`□` or `◇_x`) of more and more
  of the outer world's language;
* its **own variables**: the `j`-th is `ρ j : τ j`, with distinct names fresh for every base.

The context at stage `(m, j)` is `base m` with the first `j` own variables (`ctx`).  Every stage is
presented, the stages grow along the product order, and they form a stage system (`sys`), so the
theory of sentences applies.

* `WorldLang.const`: a fixed presented base (the actual world);
* `WorldLang.boxChild`, `WorldLang.diaChild`: the base is the `□` / `◇_x` view of the outer
  language along its diagonal, which eventually contains every view of every outer stage
  (`view_le_boxChild`, `view_le_diaChild`).
-/

namespace V12M

variable [ModalSys]

/-! ## Stages over any base -/

omit [ModalSys] in
theorem Ctx.stage_base_le {B B' : Ctx} (h : B.Le B') (τ : ℕ → VarType) (ρ : ℕ → ℕ) :
    ∀ j, (B.stage τ ρ j).Le (B'.stage τ ρ j)
  | 0 => h
  | j + 1 => (Ctx.stage_base_le h τ ρ j).insert _ _

omit [ModalSys] in
theorem Ctx.stage_le_succ {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} (hρ : Function.Injective ρ)
    (hB : ∀ n, B.RootFresh (.free (ρ n))) (j : ℕ) : (B.stage τ ρ j).Le (B.stage τ ρ (j + 1)) :=
  Ctx.le_insert (Ctx.stage_fresh hρ hB le_rfl).root _

omit [ModalSys] in
theorem Ctx.stage_le_of_le {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} (hρ : Function.Injective ρ)
    (hB : ∀ n, B.RootFresh (.free (ρ n))) {j j' : ℕ} (h : j ≤ j') :
    (B.stage τ ρ j).Le (B.stage τ ρ j') := by
  induction h with
  | refl => exact Ctx.Le.refl _
  | step _ ih => exact ih.trans (Ctx.stage_le_succ hρ hB _)

omit [ModalSys] in
/-- Names other than the stage variables stay fresh. -/
theorem Ctx.stage_fresh_of {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} {u : ℕ}
    (hB : B.RootFresh (.free u)) (hu : ∀ n, ρ n ≠ u) : ∀ j, (B.stage τ ρ j).RootFresh (.free u)
  | 0 => hB
  | j + 1 => (Ctx.stage_fresh_of hB hu j).insert_ne (fun he => hu j (Root.free.inj he)) _

omit [ModalSys] in
/-- The stages depend only on the types of the variables declared so far. -/
theorem Ctx.stage_congr {B : Ctx} {τ τ' : ℕ → VarType} {ρ : ℕ → ℕ} :
    ∀ {j : ℕ}, (∀ i < j, τ i = τ' i) → B.stage τ ρ j = B.stage τ' ρ j
  | 0, _ => rfl
  | j + 1, h => by
      change (B.stage τ ρ j).insert (.free (ρ j)) (τ j) =
        (B.stage τ' ρ j).insert (.free (ρ j)) (τ' j)
      rw [Ctx.stage_congr (fun i hi => h i (Nat.lt_succ_of_lt hi)), h j (Nat.lt_succ_self j)]

/-- Every stage over a presented base is presented. -/
def Ctx.stagePresented {B : Ctx} [B.Presented] (τ : ℕ → VarType) (ρ : ℕ → ℕ) :
    ∀ j, (B.stage τ ρ j).Presented
  | 0 => inferInstanceAs B.Presented
  | j + 1 =>
      haveI := Ctx.stagePresented (B := B) τ ρ j
      inferInstanceAs ((B.stage τ ρ j).insert (.free (ρ j)) (τ j)).Presented

/-! ## World languages -/

/-- The language of a world: a growing presented base, and its own variables `ρ j : τ j`. -/
structure WorldLang where
  base : ℕ → Ctx
  base_le : ∀ m, (base m).Le (base (m + 1))
  basePres : ∀ m, (base m).Presented
  τ : ℕ → VarType
  ρ : ℕ → ℕ
  ρ_inj : Function.Injective ρ
  fresh : ∀ m n, (base m).RootFresh (.free (ρ n))

namespace WorldLang

variable (L : WorldLang)

/-- The context at stage `(m, j)`: the base `base m` with the first `j` own variables. -/
def ctx (i : ℕ × ℕ) : Ctx := (L.base i.1).stage L.τ L.ρ i.2

instance (m : ℕ) : (L.base m).Presented := L.basePres m

instance (i : ℕ × ℕ) : (L.ctx i).Presented := Ctx.stagePresented L.τ L.ρ i.2

theorem base_mono {m m' : ℕ} (h : m ≤ m') : (L.base m).Le (L.base m') := by
  induction h with
  | refl => exact Ctx.Le.refl _
  | step _ ih => exact ih.trans (L.base_le _)

theorem ctx_le {i j : ℕ × ℕ} (h : i ≤ j) : (L.ctx i).Le (L.ctx j) :=
  (Ctx.stage_le_of_le L.ρ_inj (L.fresh i.1) h.2).trans
    (Ctx.stage_base_le (L.base_mono h.1) L.τ L.ρ j.2)

/-- The stages as a stage system. -/
def sys : StageSys (ℕ × ℕ) := ⟨L.ctx, L.ctx_le, fun _ => inferInstance⟩

theorem ctx_zero (m : ℕ) : L.ctx (m, 0) = L.base m := rfl

theorem ctx_succ (m j : ℕ) :
    L.ctx (m, j + 1) = (L.ctx (m, j)).insert (.free (L.ρ j)) (L.τ j) :=
  rfl

/-- The own variables not yet declared are fresh. -/
theorem fresh_ctx {m j n : ℕ} (h : j ≤ n) : (L.ctx (m, j)).RootFresh (.free (L.ρ n)) :=
  Ctx.stage_fresh L.ρ_inj (L.fresh m) h

theorem ctx_le_succ (m j : ℕ) : (L.ctx (m, j)).Le (L.ctx (m, j + 1)) :=
  Ctx.le_insert (L.fresh_ctx le_rfl).root _

theorem base_le_ctx (m j : ℕ) : (L.base m).Le (L.ctx (m, j)) :=
  L.ctx_le (i := (m, 0)) ⟨le_rfl, Nat.zero_le j⟩

/-- A name fresh for every base and never an own variable is fresh at every stage. -/
theorem fresh_ctx_of {u : ℕ} (hB : ∀ m, (L.base m).RootFresh (.free u))
    (hu : ∀ n, L.ρ n ≠ u) (i : ℕ × ℕ) : (L.ctx i).RootFresh (.free u) :=
  Ctx.stage_fresh_of (hB i.1) hu i.2

/-- The same language with other types for its own variables. -/
def withTypes (τ' : ℕ → VarType) : WorldLang := { L with τ := τ' }

theorem withTypes_ctx {τ' : ℕ → VarType} {m j : ℕ} (h : ∀ i < j, L.τ i = τ' i) :
    (L.withTypes τ').ctx (m, j) = L.ctx (m, j) :=
  (Ctx.stage_congr h).symm

/-! ## Constructions -/

/-- A fixed presented base: the language of the actual world. -/
def const (Γ : Ctx) [Γ.Presented] (τ : ℕ → VarType) (ρ : ℕ → ℕ) (hρ : Function.Injective ρ)
    (hfresh : ∀ n, Γ.RootFresh (.free (ρ n))) : WorldLang where
  base _ := Γ
  base_le _ := Ctx.Le.refl Γ
  basePres _ := inferInstance
  τ := τ
  ρ := ρ
  ρ_inj := hρ
  fresh _ := hfresh

/-- The diagonal of a language: stage `(m, m)`. -/
theorem diag_le (m : ℕ) : (L.ctx (m, m)).Le (L.ctx (m + 1, m + 1)) :=
  L.ctx_le ⟨Nat.le_succ m, Nat.le_succ m⟩

theorem le_diag {i : ℕ × ℕ} {k : ℕ} (h₁ : i.1 ≤ k) (h₂ : i.2 ≤ k) :
    (L.ctx i).Le (L.ctx (k, k)) :=
  L.ctx_le ⟨h₁, h₂⟩

/-- The language of a world reached through `□`: its base is the `□` view of the outer
    language. -/
def boxChild (τ' : ℕ → VarType) (ρ' : ℕ → ℕ) (hρ' : Function.Injective ρ')
    (hfresh : ∀ m n, (L.ctx (m, m)).RootFresh (.free (ρ' n))) : WorldLang where
  base m := (L.ctx (m, m)).boxIn
  base_le m := (L.diag_le m).boxIn
  basePres _ := inferInstance
  τ := τ'
  ρ := ρ'
  ρ_inj := hρ'
  fresh m n := (hfresh m n).boxIn

/-- The language of a world reached through `◇_x`: its base is the `◇_x` view of the outer
    language. -/
def diaChild (x : VarSymb) (τ' : ℕ → VarType) (ρ' : ℕ → ℕ) (hρ' : Function.Injective ρ')
    (hfresh : ∀ m n, (L.ctx (m, m)).RootFresh (.free (ρ' n))) : WorldLang where
  base m := (L.ctx (m, m)).diaIn x
  base_le m := (L.diag_le m).diaIn x
  basePres _ := inferInstance
  τ := τ'
  ρ := ρ'
  ρ_inj := hρ'
  fresh m n := (hfresh m n).diaIn x

/-- Every `□` view of an outer stage is part of the `□` child's language from some stage on. -/
theorem view_le_boxChild {τ' : ℕ → VarType} {ρ' : ℕ → ℕ} {hρ' : Function.Injective ρ'}
    {hfresh : ∀ m n, (L.ctx (m, m)).RootFresh (.free (ρ' n))} {i : ℕ × ℕ} {k j : ℕ}
    (h₁ : i.1 ≤ k) (h₂ : i.2 ≤ k) :
    (L.ctx i).boxIn.Le ((L.boxChild τ' ρ' hρ' hfresh).ctx (k, j)) :=
  (L.le_diag h₁ h₂).boxIn.trans ((L.boxChild τ' ρ' hρ' hfresh).base_le_ctx k j)

/-- Every `◇_x` view of an outer stage is part of the `◇_x` child's language from some stage on. -/
theorem view_le_diaChild {x : VarSymb} {τ' : ℕ → VarType} {ρ' : ℕ → ℕ}
    {hρ' : Function.Injective ρ'} {hfresh : ∀ m n, (L.ctx (m, m)).RootFresh (.free (ρ' n))}
    {i : ℕ × ℕ} {k j : ℕ} (h₁ : i.1 ≤ k) (h₂ : i.2 ≤ k) :
    (L.ctx i).diaIn x |>.Le ((L.diaChild x τ' ρ' hρ' hfresh).ctx (k, j)) :=
  ((L.le_diag h₁ h₂).diaIn x).trans ((L.diaChild x τ' ρ' hρ' hfresh).base_le_ctx k j)

end WorldLang

end V12M
