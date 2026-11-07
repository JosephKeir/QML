import QML.QML_v12m_GKToND

/-!
# QML v12m — the subformula property for GK

⭐`GK.subformula`: a cut-free GK derivation of `Δ ⇒ Θ` can be read as one in which **every sequent
consists of subformulas of `Δ ⇒ Θ`** (`GKS`), in Gentzen's sense for predicate logic
(`GSub`): the least family of formulas containing the end sequent and closed under
* immediate subformulas of `∧`, `∨`, `→`, the bodies of `□` and `◇_x` (read in their views),
* instances of a quantifier's body: at any term, or opened at an eigenvariable,
* the bookkeeping of contexts: weakening by a fresh variable, a `□`-body moved into a `◇_x` view,
  and (under 4) a `□` view formula moved into a `◇_x` view,
* under 4, the copies one view in: `□(shift φ)` of `□φ`, and `◇_{y.keep}(shift θ)` of `◇_y θ`
  (`cp4`, `kp4`: K4's `□φ` in its own premise, shifted to the view),
* and the atoms `ref` and `repl` introduce: reflexive equations `t = t`, and `P(s)` from members
  `t = s` and `P(t)` (as in Negri and von Plato's G3 with equality).

`GSub.weight_le`: every member is an atom or no heavier than a formula of the end sequent.  With
`GK.provable_iff_der`: every ND-provable sequent of K, KD, K4 and KD4 has such an analytic
derivation
(`GK.subformula_of_provable`).
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-- ⭐**Subformulas of a sequent** `E` over `Γ₀`, in Gentzen's sense, across the contexts a
    derivation passes through. -/
inductive GSub {Γ₀ : Ctx} (E : List (WFF σ Γ₀ 0)) : (Γ : Ctx) → WFF σ Γ 0 → Prop where
  | mem {φ : WFF σ Γ₀ 0} : φ ∈ E → GSub E Γ₀ φ
  | refl_eq {Γ : Ctx} (t : Term σ Γ .Var .var) : GSub E Γ (.eq t t)
  | repl {Γ : Ctx} [Γ.NoSlots] {Q : WFF σ (Γ.insert (.bnd 0) .Var) 1} (hQ : Q.IsAtom)
      (t s : Term σ Γ .Var .var) : GSub E Γ (.eq t s) →
      GSub E Γ (WFF.instantiate Ctx.NoSlots.slots t Q) →
      GSub E Γ (WFF.instantiate Ctx.NoSlots.slots s Q)
  | and_l {Γ : Ctx} {φ ψ : WFF σ Γ 0} : GSub E Γ (φ.and ψ) → GSub E Γ φ
  | and_r {Γ : Ctx} {φ ψ : WFF σ Γ 0} : GSub E Γ (φ.and ψ) → GSub E Γ ψ
  | or_l {Γ : Ctx} {φ ψ : WFF σ Γ 0} : GSub E Γ (φ.or ψ) → GSub E Γ φ
  | or_r {Γ : Ctx} {φ ψ : WFF σ Γ 0} : GSub E Γ (φ.or ψ) → GSub E Γ ψ
  | imp_l {Γ : Ctx} {φ ψ : WFF σ Γ 0} : GSub E Γ (φ.imp ψ) → GSub E Γ φ
  | imp_r {Γ : Ctx} {φ ψ : WFF σ Γ 0} : GSub E Γ (φ.imp ψ) → GSub E Γ ψ
  | all_inst {Γ : Ctx} [Γ.NoSlots] {T : VarType} {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T}
      (t : Term σ Γ T a) : GSub E Γ (.all T φ) → GSub E Γ (WFF.instantiate Ctx.NoSlots.slots t φ)
  | ex_inst {Γ : Ctx} [Γ.NoSlots] {T : VarType} {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T}
      (t : Term σ Γ T a) : GSub E Γ (.ex T φ) → GSub E Γ (WFF.instantiate Ctx.NoSlots.slots t φ)
  | all_eigen {Γ : Ctx} [Γ.NoSlots] {u : ℕ} {T : VarType} (hu : Γ.RootFresh (.free u))
      {φ : WFF σ (Γ.insert (.free u) T) 0} :
      GSub E Γ (.all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ)) → GSub E (Γ.insert (.free u) T) φ
  | ex_eigen {Γ : Ctx} [Γ.NoSlots] {u : ℕ} {T : VarType} (hu : Γ.RootFresh (.free u))
      {φ : WFF σ (Γ.insert (.free u) T) 0} :
      GSub E Γ (.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ)) → GSub E (Γ.insert (.free u) T) φ
  | weaken {Γ : Ctx} {u : ℕ} {T : VarType} (hu : Γ.RootFresh (.free u)) {δ : WFF σ Γ 0} :
      GSub E Γ δ → GSub E (Γ.insert (.free u) T) (WFF.weaken hu.root T δ)
  | box {Γ : Ctx} {φ : WFF σ Γ.boxIn 0} : GSub E Γ (WFF.box (Γ := Γ) φ) → GSub E Γ.boxIn φ
  | box_dia {Γ : Ctx} {φ : WFF σ Γ.boxIn 0} (x : VarSymb) :
      GSub E Γ (WFF.box (Γ := Γ) φ) → GSub E (Γ.diaIn x) (WFF.mono (Ctx.le_boxIn_diaIn Γ x) φ)
  | dia {Γ : Ctx} {x : VarSymb} {hx : ∃ X, Γ.ref x = some (.VTypeDia X)}
      {φ : WFF σ (Γ.diaIn x) 0} : GSub E Γ (.dia x hx φ) → GSub E (Γ.diaIn x) φ
  | view_dia {Γ : Ctx} [Γ.NoSlots] {φ : WFF σ Γ.boxIn 0} (x : VarSymb) :
      GSub E Γ.boxIn φ → GSub E (Γ.diaIn x) (WFF.mono (Ctx.le_boxIn_diaIn Γ x) φ)
  | box_keep {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) {φ : WFF σ Γ.boxIn 0} :
      GSub E Γ (WFF.box (Γ := Γ) φ) →
      GSub E Γ.boxIn (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ))
  | dia_keep {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) {y : VarSymb}
      {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)} {θ : WFF σ (Γ.diaIn y) 0} :
      GSub E Γ (.dia y hy θ) →
      GSub E Γ.boxIn (WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
        (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots θ))

/-! ## Subformulas are no heavier -/

/-- Weakening keeps the weight, in any context. -/
theorem WFF.weight_mono' : ∀ {Γ Γ' : Ctx} {d : ℕ} (h : Γ.Le Γ') (φ : WFF σ Γ d),
    (WFF.mono h φ).weight = φ.weight
  | _, _, _, _, .atom _ => rfl
  | _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, .top => rfl
  | _, _, _, _, .bot => rfl
  | _, _, _, h, .and φ ψ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' h φ, WFF.weight_mono' h ψ]
  | _, _, _, h, .or φ ψ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' h φ, WFF.weight_mono' h ψ]
  | _, _, _, h, .imp φ ψ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' h φ, WFF.weight_mono' h ψ]
  | _, _, _, h, .all T φ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' _ φ]
  | _, _, _, h, .ex T φ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' _ φ]
  | _, _, _, h, .box φ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' _ φ]
  | _, _, _, h, .dia x hx φ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' _ φ]
  | _, _, _, _, .here _ _ _ => rfl
  | _, _, _, _, .back _ _ _ _ => rfl
  | _, _, _, h, .retS _ _ _ Φ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' _ Φ]
  | _, _, _, h, .retxS _ _ _ _ _ Φ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' _ Φ]
  | _, _, _, h, .link _ _ _ Φ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' _ Φ]
  | _, _, _, h, .linkx _ _ _ _ _ Φ => by
      simp only [WFF.mono, WFF.weight]; rw [WFF.weight_mono' _ Φ]

theorem WFF.weight_bindFree {Γ : Ctx} {d : ℕ} (u : ℕ) (hu : Γ.RootFresh (.free u))
    (hs : Γ.SlotsFrom d) (T : VarType) (φ : WFF σ (Γ.insert (.free u) T) d) :
    (WFF.bindFree u hu hs T φ).weight = φ.weight := by
  unfold WFF.bindFree WFF.renameRoot
  exact WFF.weight_subst _ _ _ _ _ φ

/-- ⭐**Subformulas are no heavier**: every member of `GSub E` is an atom or no heavier than a
    formula of `E`. -/
theorem GSub.weight_le {Γ₀ : Ctx} {E : List (WFF σ Γ₀ 0)} {Γ : Ctx} {φ : WFF σ Γ 0}
    (h : GSub E Γ φ) : φ.IsAtom ∨ ∃ ψ ∈ E, φ.weight ≤ ψ.weight := by
  induction h with
  | mem h => exact .inr ⟨_, h, le_rfl⟩
  | refl_eq t => exact .inl trivial
  | repl hQ t s _ _ _ _ => exact .inl hQ.instantiate
  | and_l _ ih | and_r _ ih | or_l _ ih | or_r _ ih | imp_l _ ih | imp_r _ ih =>
      rcases ih with h | ⟨ψ, hψ, hw⟩
      · simp [WFF.IsAtom] at h
      · exact .inr ⟨ψ, hψ, by simp only [WFF.weight] at hw; omega⟩
  | all_inst t _ ih | ex_inst t _ ih =>
      rcases ih with h | ⟨ψ, hψ, hw⟩
      · simp [WFF.IsAtom] at h
      · exact .inr ⟨ψ, hψ, by rw [WFF.weight_instantiate]; simp only [WFF.weight] at hw; omega⟩
  | all_eigen hu _ ih | ex_eigen hu _ ih =>
      rcases ih with h | ⟨ψ, hψ, hw⟩
      · simp [WFF.IsAtom] at h
      · refine .inr ⟨ψ, hψ, ?_⟩
        simp only [WFF.weight, WFF.weight_bindFree] at hw
        omega
  | weaken hu _ ih =>
      rcases ih with h | ⟨ψ, hψ, hw⟩
      · left
        revert h
        rename_i δ _
        cases δ <;> simp [WFF.IsAtom, WFF.weaken, WFF.mono]
      · exact .inr ⟨ψ, hψ, by unfold WFF.weaken; rw [WFF.weight_mono']; exact hw⟩
  | box _ ih | box_dia _ _ ih | dia _ ih =>
      rcases ih with h | ⟨ψ, hψ, hw⟩
      · simp [WFF.IsAtom] at h
      · refine .inr ⟨ψ, hψ, ?_⟩
        simp only [WFF.weight] at hw
        try rw [WFF.weight_mono']
        omega
  | view_dia x _ ih =>
      rcases ih with h | ⟨ψ, hψ, hw⟩
      · left
        revert h
        rename_i φ _
        cases φ <;> simp [WFF.IsAtom, WFF.mono]
      · exact .inr ⟨ψ, hψ, by rw [WFF.weight_mono']; exact hw⟩
  | box_keep hF _ ih | dia_keep hF _ ih =>
      rcases ih with h | ⟨ψ, hψ, hw⟩
      · simp [WFF.IsAtom] at h
      · refine .inr ⟨ψ, hψ, ?_⟩
        simp only [WFF.weight, WFF.weight_shift] at hw ⊢
        omega

/-- The boxed hypotheses' copies are subformulas. -/
theorem GSub.copies_box {Γ₀ : Ctx} {E : List (WFF σ Γ₀ 0)} {Γ : Ctx} [Γ.NoSlots]
    {Δ₁ : List (WFF σ Γ.boxIn 0)} (h : ∀ χ ∈ Δ₁, GSub E Γ (WFF.box (Γ := Γ) χ)) :
    ∀ c ∈ cp4 Δ₁, GSub E Γ.boxIn c := by
  intro c hc
  unfold cp4 at hc
  split at hc
  · next hF =>
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hc
    exact (h χ hχ).box_keep hF
  · exact absurd hc List.not_mem_nil

/-- The conclusions' copies are subformulas. -/
theorem GSub.copies_dia {Γ₀ : Ctx} {E : List (WFF σ Γ₀ 0)} {Γ : Ctx} [Γ.NoSlots]
    {L : List (WFF σ Γ 0)} (h : ∀ A ∈ L, GSub E Γ A) : ∀ c ∈ kp4 L, GSub E Γ.boxIn c := by
  intro c hc
  unfold kp4 at hc
  split at hc
  · next hF =>
    obtain ⟨A, hA, hcA⟩ := List.mem_flatMap.mp hc
    cases A
    case dia y hy θ =>
      rw [List.mem_singleton.mp hcA]
      exact (h _ hA).dia_keep hF
    all_goals exact absurd hcA List.not_mem_nil
  · exact absurd hc List.not_mem_nil

/-- Every formula of a sequent belongs to a family. -/
def SeqIn (P : (Γ : Ctx) → WFF σ Γ 0 → Prop) (Γ : Ctx) (Δ Θ : List (WFF σ Γ 0)) : Prop :=
  (∀ φ ∈ Δ, P Γ φ) ∧ ∀ φ ∈ Θ, P Γ φ

/-- ⭐**GK with every sequent in a family `P`**: GK's rules, each conclusion required to lie in
    `P`. -/
inductive GKS (σ : Signature) (P : (Γ : Ctx) → WFF σ Γ 0 → Prop) :
    ℕ → (Γ : Ctx) → List (WFF σ Γ 0) → List (WFF σ Γ 0) → Prop where
  | ax {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ) (A : WFF σ Γ 0)
      (hA : A.IsAtom) : A ∈ Δ → A ∈ Θ → GKS σ P n Γ Δ Θ
  | botL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ) :
      .bot ∈ Δ → GKS σ P n Γ Δ Θ
  | topR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ) :
      .top ∈ Θ → GKS σ P n Γ Δ Θ
  | andL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (hS : SeqIn P Γ Δ Θ) :
      φ.and ψ ∈ Δ → GKS σ P n Γ (φ :: ψ :: Δ) Θ → GKS σ P (n + 1) Γ Δ Θ
  | andR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (hS : SeqIn P Γ Δ Θ) :
      φ.and ψ ∈ Θ → GKS σ P n Γ Δ (φ :: Θ) → GKS σ P n Γ Δ (ψ :: Θ) → GKS σ P (n + 1) Γ Δ Θ
  | orL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (hS : SeqIn P Γ Δ Θ) :
      φ.or ψ ∈ Δ → GKS σ P n Γ (φ :: Δ) Θ → GKS σ P n Γ (ψ :: Δ) Θ → GKS σ P (n + 1) Γ Δ Θ
  | orR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (hS : SeqIn P Γ Δ Θ) :
      φ.or ψ ∈ Θ → GKS σ P n Γ Δ (φ :: ψ :: Θ) → GKS σ P (n + 1) Γ Δ Θ
  | impL {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (hS : SeqIn P Γ Δ Θ) :
      φ.imp ψ ∈ Δ → GKS σ P n Γ Δ (φ :: Θ) → GKS σ P n Γ (ψ :: Δ) Θ → GKS σ P (n + 1) Γ Δ Θ
  | impR {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0} (hS : SeqIn P Γ Δ Θ) :
      φ.imp ψ ∈ Θ → GKS σ P n Γ (φ :: Δ) (ψ :: Θ) → GKS σ P (n + 1) Γ Δ Θ
  | allL {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ)
      (T : VarType) {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) :
      .all T φ ∈ Δ → GKS σ P n Γ (WFF.instantiate Ctx.NoSlots.slots t φ :: Δ) Θ →
      GKS σ P (n + 1) Γ Δ Θ
  | allR {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ) (u : ℕ)
      (T : VarType) (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} :
      .all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ) ∈ Θ →
      GKS σ P n (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T))
        (φ :: Θ.map (WFF.weaken hu.root T)) →
      GKS σ P (n + 1) Γ Δ Θ
  | exL {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ) (u : ℕ)
      (T : VarType) (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} :
      .ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ) ∈ Δ →
      GKS σ P n (Γ.insert (.free u) T) (φ :: Δ.map (WFF.weaken hu.root T))
        (Θ.map (WFF.weaken hu.root T)) →
      GKS σ P (n + 1) Γ Δ Θ
  | exR {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ)
      (T : VarType) {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T} (t : Term σ Γ T a) :
      .ex T φ ∈ Θ → GKS σ P n Γ Δ (WFF.instantiate Ctx.NoSlots.slots t φ :: Θ) →
      GKS σ P (n + 1) Γ Δ Θ
  | ref {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ)
      (t : Term σ Γ .Var .var) : GKS σ P n Γ (.eq t t :: Δ) Θ → GKS σ P (n + 1) Γ Δ Θ
  | repl {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ)
      {Q : WFF σ (Γ.insert (.bnd 0) .Var) 1} (hQ : Q.IsAtom) (t s : Term σ Γ .Var .var) :
      .eq t s ∈ Δ → WFF.instantiate Ctx.NoSlots.slots t Q ∈ Δ →
      GKS σ P n Γ (WFF.instantiate Ctx.NoSlots.slots s Q :: Δ) Θ → GKS σ P (n + 1) Γ Δ Θ
  | boxR {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ)
      {Δ₁ : List (WFF σ Γ.boxIn 0)} {φ : WFF σ Γ.boxIn 0} {L : List (WFF σ Γ 0)} :
      WFF.box (Γ := Γ) φ ∈ Θ → (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) → L ⊆ Θ →
      GKS σ P n Γ.boxIn (Δ₁ ++ cp4 Δ₁) (φ :: kp4 L) → GKS σ P (n + 1) Γ Δ Θ
  | diaL {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ)
      (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {ψ : WFF σ (Γ.diaIn x) 0}
      {Δ₁ : List (WFF σ Γ.boxIn 0)} {Θ₁ : List (WFF σ (Γ.diaIn x) 0)} {L : List (WFF σ Γ 0)} :
      .dia x hx ψ ∈ Δ → (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) → (∀ χ ∈ Θ₁, .dia x hx χ ∈ Θ) →
      L ⊆ Θ →
      GKS σ P n (Γ.diaIn x) (ψ :: (Δ₁ ++ cp4 Δ₁).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
        (Θ₁ ++ (kp4 L).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) →
      GKS σ P (n + 1) Γ Δ Θ
  | serial {n : ℕ} {Γ : Ctx} [Γ.NoSlots] {Δ Θ : List (WFF σ Γ 0)} (hS : SeqIn P Γ Δ Θ)
      (hD : ModalSys.D = true) {Δ₁ : List (WFF σ Γ.boxIn 0)} {L : List (WFF σ Γ 0)} :
      (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) → L ⊆ Θ →
      GKS σ P n Γ.boxIn (Δ₁ ++ cp4 Δ₁) (kp4 L) → GKS σ P (n + 1) Γ Δ Θ

namespace GKS

variable {P : (Γ : Ctx) → WFF σ Γ 0 → Prop}

/-- Forgetting the family. -/
theorem toGK {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (d : GKS σ P n Γ Δ Θ) :
    GK σ n Γ Δ Θ := by
  induction d with
  | ax _ A hA h₁ h₂ => exact .ax A hA h₁ h₂
  | botL _ h => exact .botL h
  | topR _ h => exact .topR h
  | andL _ h _ ih => exact .andL h ih
  | andR _ h _ _ ih₁ ih₂ => exact .andR h ih₁ ih₂
  | orL _ h _ _ ih₁ ih₂ => exact .orL h ih₁ ih₂
  | orR _ h _ ih => exact .orR h ih
  | impL _ h _ _ ih₁ ih₂ => exact .impL h ih₁ ih₂
  | impR _ h _ ih => exact .impR h ih
  | allL _ T t h _ ih => exact .allL T t h ih
  | allR _ u T hu h _ ih => exact .allR u T hu h ih
  | exL _ u T hu h _ ih => exact .exL u T hu h ih
  | exR _ T t h _ ih => exact .exR T t h ih
  | ref _ t _ ih => exact .ref t ih
  | repl _ hQ t s h₁ h₂ _ ih => exact .repl hQ t s h₁ h₂ ih
  | boxR _ h₁ h₂ h₃ _ ih => exact .boxR h₁ h₂ h₃ ih
  | diaL _ x hx h₁ h₂ h₃ h₄ _ ih => exact .diaL x hx h₁ h₂ h₃ h₄ ih
  | serial _ hD h₂ h₃ _ ih => exact .serial hD h₂ h₃ ih

end GKS

namespace GK

variable {Γ₀ : Ctx} {E : List (WFF σ Γ₀ 0)}

/-- ⭐**The subformula property**: a cut-free derivation whose end sequent lies in the
    subformulas of `E` has every sequent there. -/
theorem subformula {n : ℕ} {Γ : Ctx} {Δ Θ : List (WFF σ Γ 0)} (d : GK σ n Γ Δ Θ) :
    SeqIn (GSub E) Γ Δ Θ → GKS σ (GSub E) n Γ Δ Θ := by
  induction d with
  | ax A hA h₁ h₂ => exact fun hS => .ax hS A hA h₁ h₂
  | botL h => exact fun hS => .botL hS h
  | topR h => exact fun hS => .topR hS h
  | andL h _ ih =>
      intro hS
      refine .andL hS h (ih ⟨fun χ hχ => ?_, hS.2⟩)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (hS.1 _ h).and_l
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (hS.1 _ h).and_r
      · exact hS.1 χ hχ
  | andR h _ _ ih₁ ih₂ =>
      intro hS
      refine .andR hS h (ih₁ ⟨hS.1, fun χ hχ => ?_⟩) (ih₂ ⟨hS.1, fun χ hχ => ?_⟩)
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.2 _ h).and_l, hS.2 χ hχ]
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.2 _ h).and_r, hS.2 χ hχ]
  | orL h _ _ ih₁ ih₂ =>
      intro hS
      refine .orL hS h (ih₁ ⟨fun χ hχ => ?_, hS.2⟩) (ih₂ ⟨fun χ hχ => ?_, hS.2⟩)
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.1 _ h).or_l, hS.1 χ hχ]
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.1 _ h).or_r, hS.1 χ hχ]
  | orR h _ ih =>
      intro hS
      refine .orR hS h (ih ⟨hS.1, fun χ hχ => ?_⟩)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (hS.2 _ h).or_l
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (hS.2 _ h).or_r
      · exact hS.2 χ hχ
  | impL h _ _ ih₁ ih₂ =>
      intro hS
      refine .impL hS h (ih₁ ⟨hS.1, fun χ hχ => ?_⟩) (ih₂ ⟨fun χ hχ => ?_, hS.2⟩)
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.1 _ h).imp_l, hS.2 χ hχ]
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.1 _ h).imp_r, hS.1 χ hχ]
  | impR h _ ih =>
      intro hS
      refine .impR hS h (ih ⟨fun χ hχ => ?_, fun χ hχ => ?_⟩)
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.2 _ h).imp_l, hS.1 χ hχ]
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.2 _ h).imp_r, hS.2 χ hχ]
  | allL T t h _ ih =>
      intro hS
      refine .allL hS T t h (ih ⟨fun χ hχ => ?_, hS.2⟩)
      rcases List.mem_cons.mp hχ with rfl | hχ
      exacts [(hS.1 _ h).all_inst t, hS.1 χ hχ]
  | allR u T hu h _ ih =>
      intro hS
      refine .allR hS u T hu h (ih ⟨fun χ hχ => ?_, fun χ hχ => ?_⟩)
      · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hχ
        exact (hS.1 δ hδ).weaken hu
      · rcases List.mem_cons.mp hχ with rfl | hχ
        · exact (hS.2 _ h).all_eigen hu
        · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hχ
          exact (hS.2 δ hδ).weaken hu
  | exL u T hu h _ ih =>
      intro hS
      refine .exL hS u T hu h (ih ⟨fun χ hχ => ?_, fun χ hχ => ?_⟩)
      · rcases List.mem_cons.mp hχ with rfl | hχ
        · exact (hS.1 _ h).ex_eigen hu
        · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hχ
          exact (hS.1 δ hδ).weaken hu
      · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hχ
        exact (hS.2 δ hδ).weaken hu
  | exR T t h _ ih =>
      intro hS
      refine .exR hS T t h (ih ⟨hS.1, fun χ hχ => ?_⟩)
      rcases List.mem_cons.mp hχ with rfl | hχ
      exacts [(hS.2 _ h).ex_inst t, hS.2 χ hχ]
  | ref t _ ih =>
      intro hS
      refine .ref hS t (ih ⟨fun χ hχ => ?_, hS.2⟩)
      rcases List.mem_cons.mp hχ with rfl | hχ
      exacts [.refl_eq t, hS.1 χ hχ]
  | repl hQ t s h₁ h₂ _ ih =>
      intro hS
      refine .repl hS hQ t s h₁ h₂ (ih ⟨fun χ hχ => ?_, hS.2⟩)
      rcases List.mem_cons.mp hχ with rfl | hχ
      exacts [.repl hQ t s (hS.1 _ h₁) (hS.1 _ h₂), hS.1 χ hχ]
  | boxR h₁ h₂ h₃ _ ih =>
      intro hS
      have hb := GSub.copies_box fun χ hχ => hS.1 _ (h₂ χ hχ)
      have hk := GSub.copies_dia fun A hA => hS.2 _ (h₃ hA)
      refine .boxR hS h₁ h₂ h₃ (ih ⟨fun χ hχ => ?_, fun χ hχ => ?_⟩)
      · rcases List.mem_append.mp hχ with hχ | hχ
        exacts [(hS.1 _ (h₂ χ hχ)).box, hb χ hχ]
      · rcases List.mem_cons.mp hχ with rfl | hχ
        exacts [(hS.2 _ h₁).box, hk χ hχ]
  | serial hD h₂ h₃ _ ih =>
      intro hS
      have hb := GSub.copies_box fun χ hχ => hS.1 _ (h₂ χ hχ)
      have hk := GSub.copies_dia fun A hA => hS.2 _ (h₃ hA)
      refine .serial hS hD h₂ h₃ (ih ⟨fun χ hχ => ?_, hk⟩)
      rcases List.mem_append.mp hχ with hχ | hχ
      exacts [(hS.1 _ (h₂ χ hχ)).box, hb χ hχ]
  | diaL x hx h₁ h₂ h₃ h₄ _ ih =>
      intro hS
      have hb := GSub.copies_box fun χ hχ => hS.1 _ (h₂ χ hχ)
      have hk := GSub.copies_dia fun A hA => hS.2 _ (h₄ hA)
      refine .diaL hS x hx h₁ h₂ h₃ h₄ (ih ⟨fun χ hχ => ?_, fun χ hχ => ?_⟩)
      · rcases List.mem_cons.mp hχ with rfl | hχ
        · exact (hS.1 _ h₁).dia
        · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hχ
          rcases List.mem_append.mp hδ with hδ | hδ
          exacts [(hS.1 _ (h₂ δ hδ)).box_dia x, (hb δ hδ).view_dia x]
      · rcases List.mem_append.mp hχ with hχ | hχ
        · exact (hS.2 _ (h₃ χ hχ)).dia
        · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hχ
          exact (hk δ hδ).view_dia x

/-- ⭐**Analytic derivations of every ND-provable sequent** of K, KD, K4 and KD4: a cut-free
    derivation whose every sequent consists of subformulas of the end sequent. -/
theorem subformula_of_provable [ModalSys.GKSys] {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    {φ : WFF σ Γ 0} (p : Provable Δ φ) : ∃ n, GKS σ (GSub (Δ ++ [φ])) n Γ Δ [φ] := by
  obtain ⟨n, d⟩ := provable_iff_der.mp p
  exact ⟨n, d.subformula ⟨fun χ hχ => .mem (List.mem_append_left _ hχ),
    fun χ hχ => .mem (List.mem_append_right _ hχ)⟩⟩

end GK

end V12M
