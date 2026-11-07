import QML.QML_v12m_GKSubst
import QML.QML_v12m_Stages

/-!
# QML v12m — cut is admissible in GK

⭐`GK.cut`: from `Δ ⇒ A, Θ` and `A, Δ ⇒ Θ`, `Δ ⇒ Θ`, over any presented context.  The proof is
Kleene's for G3 with principal formulas kept: induction on the weight of `A`, then on the sum of
the heights (`GK.CutIH`).
* If `A` is not principal in the left derivation's last rule, the cut moves up into its premises,
  or vanishes (an axiom; a modal rule, whose premise does not see the conclusion's context).
* Otherwise it is principal on the right too (`GK.LeftPrin`) or moves up there
  (`GK.permRight`).
* Both principal: the cut against each premise first (the same formula, a smaller height, since
  principal formulas are kept), then on the components (a lighter formula).  At a quantifier the
  eigenvariable is replaced by the term (`GK.subst`, `GK.instEigenR`/`GK.instEigenL`), which
  keeps the weight (`WFF.weight_subst`).  At `□`/`◇_x` the premises are cut in the view, after
  moving the `□`-view premise into the `◇_x` view (`GK.monoCtx`); two `◇` formulas meet only
  with the same witness.
* Atoms are principal on the right only in axioms, where the atom is already a hypothesis; so
  `repl`, on atoms, never needs a reduction of its own.
-/

namespace V12M

variable [ModalSys] {σ : Signature}

/-! ## Weight under substitution -/

/-- ⭐Substitution keeps the weight: terms do not count. -/
theorem WFF.weight_subst : ∀ {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (φ : WFF σ Γ d), (WFF.subst ι θ hθ hc hΓ hΔ φ).weight = φ.weight
  | _, _, _, _, _, _, _, _, _, _, .atom _ => rfl
  | _, _, _, _, _, _, _, _, _, _, .eq _ _ => rfl
  | _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .and φ ψ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst θ hθ hc hΓ hΔ φ, WFF.weight_subst θ hθ hc hΓ hΔ ψ]
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .or φ ψ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst θ hθ hc hΓ hΔ φ, WFF.weight_subst θ hθ hc hΓ hΔ ψ]
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .imp φ ψ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst θ hθ hc hΓ hΔ φ, WFF.weight_subst θ hθ hc hΓ hΔ ψ]
  | _, _, _, _, _, _, _, _, _, _, .all _ φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .ex _ φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .box φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .dia _ _ φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .here _ _ _ => rfl
  | _, _, _, _, _, _, _, _, _, _, .back _ _ _ _ => rfl
  | _, _, _, _, _, _, _, _, _, _, .retS _ _ _ Φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ Φ]
  | _, _, _, _, _, _, _, _, _, _, .retxS _ _ _ _ _ Φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ Φ]
  | _, _, _, _, _, _, _, _, _, _, .link _ _ _ Φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ Φ]
  | _, _, _, _, _, _, _, _, _, _, .linkx _ _ _ _ _ Φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ Φ]

theorem WFF.weight_instantiate {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {T : VarType} {a : Ann T}
    (t : Term σ Γ T a) (φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) :
    (WFF.instantiate hs t φ).weight = φ.weight :=
  WFF.weight_subst _ _ _ _ _ φ

/-- Weakening keeps the weight. -/
theorem WFF.weight_mono {Γ Γ' : Ctx} [Γ'.NoSlots] (h : Γ.Le Γ') (φ : WFF σ Γ 0) :
    (WFF.mono h φ).weight = φ.weight := by
  rw [← WFF.subst_ren h (Subst.idRen Γ') (Subst.ok_idRen.restrict h) (Subst.coh_idRen.restrict h)
    ((Ctx.NoSlots.slots (Γ := Γ')).of_le h) Ctx.NoSlots.slots (fun v _ _ => Subst.at_idRen v) φ]
  exact WFF.weight_subst _ _ _ _ _ φ

theorem WFF.IsAtom.instantiate {Γ : Ctx} {d : ℕ} {hs : Γ.SlotsFrom d} {T : VarType} {a : Ann T}
    {t : Term σ Γ T a} {P : WFF σ (Γ.insert (.bnd d) T) (d + 1)} (hP : P.IsAtom) :
    (WFF.instantiate hs t P).IsAtom := by
  unfold WFF.instantiate WFF.substRoot
  exact WFF.IsAtom.subst hP

/-! ## Replacing an eigenvariable by a term -/

section Eigen

variable {Γ : Ctx} [Γ.NoSlots] {u : ℕ} (hu : Γ.RootFresh (.free u)) {T : VarType} {a : Ann T}
  (t : Term σ Γ T a)

/-- The substitution `u ↦ t`. -/
abbrev eigenS (φ : WFF σ (Γ.insert (.free u) T) 0) : WFF σ Γ 0 :=
  WFF.subst (Subst.singleIdx (.free u) (.tm t)) (Subst.single (.free u) (.tm t))
    (Subst.ok_single (Ctx.Le.refl Γ) rfl) (Subst.coh_single hu (Ctx.Le.refl Γ) rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots φ

/-- `u ↦ t` undoes weakening by `u`. -/
theorem eigenS_weaken (δ : WFF σ Γ 0) : eigenS hu t (WFF.weaken hu.root T δ) = δ := by
  have hs : Γ.SlotsFrom 0 := Ctx.NoSlots.slots
  unfold eigenS WFF.weaken
  rw [WFF.subst_mono _ _ _ _ hs]
  refine (WFF.subst_ren (Ctx.Le.refl Γ) _ _ _ _ _ (fun v U hv => ?_) δ).trans (WFF.mono_refl _ δ)
  exact Subst.single_at_ne (Ctx.ref_rt_ne hu hv)

/-- `u ↦ t` on the body of `∀u`/`∃u` is instantiating at `t`. -/
theorem eigenS_body (φ : WFF σ (Γ.insert (.free u) T) 0) :
    eigenS hu t φ =
      WFF.instantiate Ctx.NoSlots.slots t (WFF.bindFree u hu Ctx.NoSlots.slots T φ) := by
  have e := WFF.instantiate_bindFree (Ctx.Le.refl Γ) u hu t φ
  rw [WFF.mono_refl] at e
  exact e.symm

theorem eigenS_comp_weaken : eigenS hu t ∘ WFF.weaken hu.root T = id :=
  funext fun δ => eigenS_weaken hu t δ

end Eigen

namespace GK

/-- `∀R`'s premise with the eigenvariable replaced by a term. -/
theorem instEigenR {n : ℕ} {Γ : Ctx} [Γ.Presented] {u : ℕ} (hu : Γ.RootFresh (.free u))
    {T : VarType} {a : Ann T} (t : Term σ Γ T a) {Δ Θ : List (WFF σ Γ 0)}
    {φ : WFF σ (Γ.insert (.free u) T) 0}
    (p : GK σ n (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T))
      (φ :: Θ.map (WFF.weaken hu.root T))) :
    GK σ n Γ Δ (WFF.instantiate Ctx.NoSlots.slots t (WFF.bindFree u hu Ctx.NoSlots.slots T φ) :: Θ)
    := by
  have q := p.subst (Subst.single (.free u) (.tm t)) (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single hu (Ctx.Le.refl Γ) rfl) Ctx.NoSlots.slots
  have e := eigenS_body hu t φ
  unfold eigenS at e
  rw [List.map_cons, List.map_map, List.map_map, eigenS_comp_weaken hu t, List.map_id,
    List.map_id, e] at q
  exact q

/-- `∃L`'s premise with the eigenvariable replaced by a term. -/
theorem instEigenL {n : ℕ} {Γ : Ctx} [Γ.Presented] {u : ℕ} (hu : Γ.RootFresh (.free u))
    {T : VarType} {a : Ann T} (t : Term σ Γ T a) {Δ Θ : List (WFF σ Γ 0)}
    {φ : WFF σ (Γ.insert (.free u) T) 0}
    (p : GK σ n (Γ.insert (.free u) T) (φ :: Δ.map (WFF.weaken hu.root T))
      (Θ.map (WFF.weaken hu.root T))) :
    GK σ n Γ (WFF.instantiate Ctx.NoSlots.slots t (WFF.bindFree u hu Ctx.NoSlots.slots T φ) :: Δ) Θ
    := by
  have q := p.subst (Subst.single (.free u) (.tm t)) (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single hu (Ctx.Le.refl Γ) rfl) Ctx.NoSlots.slots
  have e := eigenS_body hu t φ
  unfold eigenS at e
  rw [List.map_cons, List.map_map, List.map_map, eigenS_comp_weaken hu t, List.map_id,
    List.map_id, e] at q
  exact q

/-- Weakening by an eigenvariable's declaration. -/
theorem weakenCtx {n : ℕ} {Γ : Ctx} [Γ.Presented] {u : ℕ} (hu : Γ.RootFresh (.free u))
    (T : VarType) {Δ Θ : List (WFF σ Γ 0)} (p : GK σ n Γ Δ Θ) :
    GK σ n (Γ.insert (.free u) T) (Δ.map (WFF.weaken hu.root T)) (Θ.map (WFF.weaken hu.root T)) :=
  haveI := Ctx.Presented.insertFree inferInstance u hu T
  p.monoCtx (Ctx.le_insert hu.root T)

/-- Two derivations at a common height. -/
theorem both {k₁ k₂ : ℕ} {Γ₁ Γ₂ : Ctx} {Δ₁ Θ₁ : List (WFF σ Γ₁ 0)} {Δ₂ Θ₂ : List (WFF σ Γ₂ 0)}
    (e₁ : GK σ k₁ Γ₁ Δ₁ Θ₁) (e₂ : GK σ k₂ Γ₂ Δ₂ Θ₂) :
    GK σ (max k₁ k₂) Γ₁ Δ₁ Θ₁ ∧ GK σ (max k₁ k₂) Γ₂ Δ₂ Θ₂ :=
  ⟨e₁.mono_height (le_max_left _ _), e₂.mono_height (le_max_right _ _)⟩

/-- List inclusions between rearrangements. -/
macro "lsub" : tactic =>
  `(tactic| first
    | exact fun _ h => h
    | (intro a ha
       clear * - ha
       try simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_append,
         List.mem_singleton] at ha ⊢
       tauto))

/-! ## The induction -/

/-- The induction hypothesis: cut on a lighter formula at any heights, or on one as heavy with a
    smaller sum of heights. -/
def CutIH (σ : Signature) (w s : ℕ) : Prop :=
  ∀ {Γ : Ctx} [Γ.Presented] (A : WFF σ Γ 0) {n m : ℕ} {Δ Θ : List (WFF σ Γ 0)},
    (A.weight < w ∨ A.weight = w ∧ n + m < s) →
    GK σ n Γ Δ (A :: Θ) → GK σ m Γ (A :: Δ) Θ → ∃ k, GK σ k Γ Δ Θ

/-- ⭐**The cut formula principal on the left of the right derivation**, with that rule's
    premises.  Indexed by the formula, so a case analysis keeps only the matching rules. -/
inductive LeftPrin (σ : Signature) {Γ : Ctx} :
    WFF σ Γ 0 → ℕ → List (WFF σ Γ 0) → List (WFF σ Γ 0) → Prop where
  | and {φ ψ : WFF σ Γ 0} {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → GK σ m' Γ (φ :: ψ :: φ.and ψ :: Δ) Θ → LeftPrin σ (φ.and ψ) m Δ Θ
  | or {φ ψ : WFF σ Γ 0} {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → GK σ m' Γ (φ :: φ.or ψ :: Δ) Θ → GK σ m' Γ (ψ :: φ.or ψ :: Δ) Θ →
      LeftPrin σ (φ.or ψ) m Δ Θ
  | imp {φ ψ : WFF σ Γ 0} {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → GK σ m' Γ (φ.imp ψ :: Δ) (φ :: Θ) → GK σ m' Γ (ψ :: φ.imp ψ :: Δ) Θ →
      LeftPrin σ (φ.imp ψ) m Δ Θ
  | all [Γ.NoSlots] {T : VarType} {φ : WFF σ (Γ.insert (.bnd 0) T) 1} {a : Ann T}
      {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} (t : Term σ Γ T a) :
      m' < m → GK σ m' Γ (WFF.instantiate Ctx.NoSlots.slots t φ :: .all T φ :: Δ) Θ →
      LeftPrin σ (.all T φ) m Δ Θ
  | ex [Γ.NoSlots] {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} (u : ℕ) (T : VarType)
      (hu : Γ.RootFresh (.free u)) {φ : WFF σ (Γ.insert (.free u) T) 0} :
      m' < m →
      GK σ m' (Γ.insert (.free u) T)
        (φ :: (WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ) :: Δ).map
          (WFF.weaken hu.root T))
        (Θ.map (WFF.weaken hu.root T)) →
      LeftPrin σ (.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ)) m Δ Θ
  | box {φ φ' : WFF σ Γ.boxIn 0} {Δ₁ : List (WFF σ Γ.boxIn 0)} {m m' : ℕ}
      {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → WFF.box (Γ := Γ) φ' ∈ Θ →
      (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ WFF.box (Γ := Γ) φ :: Δ) → GK σ m' Γ.boxIn Δ₁ [φ'] →
      LeftPrin σ (WFF.box φ) m Δ Θ
  | boxDia {φ : WFF σ Γ.boxIn 0} (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
      {ψ : WFF σ (Γ.diaIn x) 0} {Δ₁ : List (WFF σ Γ.boxIn 0)}
      {Θ₁ : List (WFF σ (Γ.diaIn x) 0)} {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → .dia x hx ψ ∈ Δ →
      (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ WFF.box (Γ := Γ) φ :: Δ) →
      (∀ χ ∈ Θ₁, .dia x hx χ ∈ Θ) →
      GK σ m' (Γ.diaIn x) (ψ :: Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) Θ₁ →
      LeftPrin σ (WFF.box φ) m Δ Θ
  | dia (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {ψ : WFF σ (Γ.diaIn x) 0}
      {Δ₁ : List (WFF σ Γ.boxIn 0)} {Θ₁ : List (WFF σ (Γ.diaIn x) 0)} {m m' : ℕ}
      {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) → (∀ χ ∈ Θ₁, .dia x hx χ ∈ Θ) →
      GK σ m' (Γ.diaIn x) (ψ :: Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) Θ₁ →
      LeftPrin σ (.dia x hx ψ) m Δ Θ

/-- ⭐**The cut moves up the right derivation** until the cut formula is principal there.  The
    cut formula is not an atom (those are settled at the left derivation's axioms) and not `⊥`
    (never principal on the right). -/
theorem permRight {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] (A : WFF σ Γ 0) {n m : ℕ}
    {Δ Θ : List (WFF σ Γ 0)} (hw : A.weight = w) (hs : n + m = s) (hA : ¬ A.IsAtom)
    (hb : A ≠ .bot) (d₁ : GK σ n Γ Δ (A :: Θ)) (d₂ : GK σ m Γ (A :: Δ) Θ) :
    (∃ k, GK σ k Γ Δ Θ) ∨ LeftPrin σ A m Δ Θ := by
  cases d₂ with
  | ax P hP h₁ h₂ =>
      rcases List.mem_cons.mp h₁ with he | h₁
      · exact absurd (he ▸ hP) hA
      · exact .inl ⟨0, .ax P hP h₁ h₂⟩
  | botL h =>
      rcases List.mem_cons.mp h with he | h
      · exact absurd he.symm hb
      · exact .inl ⟨0, .botL h⟩
  | topR h => exact .inl ⟨0, .topR h⟩
  | @andL _ _ _ _ φ ψ h r =>
      rcases List.mem_cons.mp h with he | h
      · subst he; exact .inr (.and (Nat.lt_succ_self _) r)
      · obtain ⟨k, e⟩ := ih A (Δ := φ :: ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
          (d₁.weaken (by lsub) (by lsub)) (r.weaken (by lsub) (by lsub))
        exact .inl ⟨_, .andL h e⟩
  | @andR _ _ _ _ φ ψ h r₁ r₂ =>
      obtain ⟨k₁, e₁⟩ := ih A (Δ := Δ) (Θ := φ :: Θ) (.inr ⟨hw, by omega⟩)
        (d₁.weaken (by lsub) (by lsub)) r₁
      obtain ⟨k₂, e₂⟩ := ih A (Δ := Δ) (Θ := ψ :: Θ) (.inr ⟨hw, by omega⟩)
        (d₁.weaken (by lsub) (by lsub)) r₂
      exact .inl ⟨_, .andR h (both e₁ e₂).1 (both e₁ e₂).2⟩
  | @orL _ _ _ _ φ ψ h r₁ r₂ =>
      rcases List.mem_cons.mp h with he | h
      · subst he; exact .inr (.or (Nat.lt_succ_self _) r₁ r₂)
      · obtain ⟨k₁, e₁⟩ := ih A (Δ := φ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
          (d₁.weaken (by lsub) (by lsub)) (r₁.weaken (by lsub) (by lsub))
        obtain ⟨k₂, e₂⟩ := ih A (Δ := ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
          (d₁.weaken (by lsub) (by lsub)) (r₂.weaken (by lsub) (by lsub))
        exact .inl ⟨_, .orL h (both e₁ e₂).1 (both e₁ e₂).2⟩
  | @orR _ _ _ _ φ ψ h r =>
      obtain ⟨k, e⟩ := ih A (Δ := Δ) (Θ := φ :: ψ :: Θ) (.inr ⟨hw, by omega⟩)
        (d₁.weaken (by lsub) (by lsub)) r
      exact .inl ⟨_, .orR h e⟩
  | @impL _ _ _ _ φ ψ h r₁ r₂ =>
      rcases List.mem_cons.mp h with he | h
      · subst he; exact .inr (.imp (Nat.lt_succ_self _) r₁ r₂)
      · obtain ⟨k₁, e₁⟩ := ih A (Δ := Δ) (Θ := φ :: Θ) (.inr ⟨hw, by omega⟩)
          (d₁.weaken (by lsub) (by lsub)) r₁
        obtain ⟨k₂, e₂⟩ := ih A (Δ := ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
          (d₁.weaken (by lsub) (by lsub)) (r₂.weaken (by lsub) (by lsub))
        exact .inl ⟨_, .impL h (both e₁ e₂).1 (both e₁ e₂).2⟩
  | @impR _ _ _ _ φ ψ h r =>
      obtain ⟨k, e⟩ := ih A (Δ := φ :: Δ) (Θ := ψ :: Θ) (.inr ⟨hw, by omega⟩)
        (d₁.weaken (by lsub) (by lsub)) (r.weaken (by lsub) (by lsub))
      exact .inl ⟨_, .impR h e⟩
  | @allL _ _ _ _ _ T φ _ t h r =>
      rcases List.mem_cons.mp h with he | h
      · subst he; exact .inr (.all t (Nat.lt_succ_self _) r)
      · obtain ⟨k, e⟩ := ih A (Δ := WFF.instantiate Ctx.NoSlots.slots t φ :: Δ) (Θ := Θ)
          (.inr ⟨hw, by omega⟩) (d₁.weaken (by lsub) (by lsub)) (r.weaken (by lsub) (by lsub))
        exact .inl ⟨_, .allL T t h e⟩
  | @allR _ _ _ _ _ u T hu φ h r =>
      haveI := Ctx.Presented.insertFree inferInstance u hu T
      obtain ⟨k, e⟩ := ih (WFF.weaken hu.root T A) (Δ := Δ.map (WFF.weaken hu.root T))
        (Θ := φ :: Θ.map (WFF.weaken hu.root T))
        (.inr ⟨(WFF.weight_mono _ A).trans hw, by omega⟩)
        ((weakenCtx hu T d₁).weaken (fun _ h => h) (by lsub)) r
      exact .inl ⟨_, .allR u T hu h e⟩
  | @exL _ _ _ _ _ u T hu φ h r =>
      rcases List.mem_cons.mp h with he | h
      · subst he; exact .inr (.ex u T hu (Nat.lt_succ_self _) r)
      · haveI := Ctx.Presented.insertFree inferInstance u hu T
        obtain ⟨k, e⟩ := ih (WFF.weaken hu.root T A)
          (Δ := φ :: Δ.map (WFF.weaken hu.root T)) (Θ := Θ.map (WFF.weaken hu.root T))
          (.inr ⟨(WFF.weight_mono _ A).trans hw, by omega⟩)
          ((weakenCtx hu T d₁).weaken (by lsub) (fun _ h => h)) (r.weaken (by lsub) (fun _ h => h))
        exact .inl ⟨_, .exL u T hu h e⟩
  | @exR _ _ _ _ _ T φ _ t h r =>
      obtain ⟨k, e⟩ := ih A (Δ := Δ) (Θ := WFF.instantiate Ctx.NoSlots.slots t φ :: Θ)
        (.inr ⟨hw, by omega⟩) (d₁.weaken (by lsub) (by lsub)) r
      exact .inl ⟨_, .exR T t h e⟩
  | ref t r =>
      obtain ⟨k, e⟩ := ih A (Δ := .eq t t :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
        (d₁.weaken (by lsub) (by lsub)) (r.weaken (by lsub) (by lsub))
      exact .inl ⟨_, .ref t e⟩
  | @repl _ _ _ _ _ P hP t s' h₁ h₂ r =>
      have h₁' : WFF.eq t s' ∈ Δ := (List.mem_cons.mp h₁).resolve_left
        fun he => hA (he ▸ trivial)
      have h₂' := (List.mem_cons.mp h₂).resolve_left fun he => hA (he ▸ hP.instantiate)
      obtain ⟨k, e⟩ := ih A (Δ := WFF.instantiate Ctx.NoSlots.slots s' P :: Δ) (Θ := Θ)
        (.inr ⟨hw, by omega⟩) (d₁.weaken (by lsub) (by lsub)) (r.weaken (by lsub) (by lsub))
      exact .inl ⟨_, .repl hP t s' h₁' h₂' e⟩
  | @boxR _ _ _ _ Δ₁ φ h₁ h₂ r =>
      by_cases hall : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ
      · exact .inl ⟨_, .boxR h₁ hall r⟩
      · push_neg at hall
        obtain ⟨χ, hχ, hn⟩ := hall
        have he := (List.mem_cons.mp (h₂ χ hχ)).resolve_right hn
        subst he
        exact .inr (.box (Nat.lt_succ_self _) h₁ h₂ r)
  | @diaL _ _ _ _ x hx ψ Δ₁ Θ₁ h₁ h₂ h₃ r =>
      rcases List.mem_cons.mp h₁ with he | h₁'
      · subst he
        refine .inr (.dia x hx (Nat.lt_succ_self _) (fun χ hχ => ?_) h₃ r)
        exact (List.mem_cons.mp (h₂ χ hχ)).resolve_left fun he => by cases he
      · by_cases hall : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ
        · exact .inl ⟨_, .diaL x hx h₁' hall h₃ r⟩
        · push_neg at hall
          obtain ⟨χ, hχ, hn⟩ := hall
          have he := (List.mem_cons.mp (h₂ χ hχ)).resolve_right hn
          subst he
          exact .inr (.boxDia x hx (Nat.lt_succ_self _) h₁' h₂ h₃ r)

/-- The members of `Δ₁` whose box is in `Δ`. -/
abbrev boxedIn {Γ : Ctx} (Δ : List (WFF σ Γ 0)) (Δ₁ : List (WFF σ Γ.boxIn 0)) :
    List (WFF σ Γ.boxIn 0) :=
  Δ₁.filter fun χ => decide (WFF.box (Γ := Γ) χ ∈ Δ)

theorem boxedIn_sub {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {Δ₁ : List (WFF σ Γ.boxIn 0)}
    {φ : WFF σ Γ.boxIn 0} (h : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ WFF.box (Γ := Γ) φ :: Δ) :
    ∀ χ ∈ Δ₁, χ = φ ∨ χ ∈ boxedIn Δ Δ₁ := by
  intro χ hχ
  by_cases hb : WFF.box (Γ := Γ) χ ∈ Δ
  · exact .inr (List.mem_filter.mpr ⟨hχ, decide_eq_true hb⟩)
  · exact .inl (WFF.box.inj ((List.mem_cons.mp (h χ hχ)).resolve_right hb))

theorem boxedIn_mem {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {Δ₁ : List (WFF σ Γ.boxIn 0)}
    {χ : WFF σ Γ.boxIn 0} (h : χ ∈ boxedIn Δ Δ₁) : WFF.box (Γ := Γ) χ ∈ Δ :=
  of_decide_eq_true (List.mem_filter.mp h).2

/-- ⭐**One step of cut elimination**, given the induction hypothesis. -/
theorem cut_step {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] (A : WFF σ Γ 0)
    {n m : ℕ} {Δ Θ : List (WFF σ Γ 0)} (hw : A.weight = w) (hs : n + m = s)
    (d₁ : GK σ n Γ Δ (A :: Θ)) (d₂ : GK σ m Γ (A :: Δ) Θ) : ∃ k, GK σ k Γ Δ Θ := by
  have D₁ := d₁
  cases d₁ with
  | ax P hP h₁ h₂ =>
      rcases List.mem_cons.mp h₂ with he | h₂
      · subst he
        refine ⟨_, d₂.weaken (fun a ha => ?_) (fun _ h => h)⟩
        rcases List.mem_cons.mp ha with rfl | ha
        exacts [h₁, ha]
      · exact ⟨0, .ax P hP h₁ h₂⟩
  | botL h => exact ⟨0, .botL h⟩
  | topR h =>
      rcases List.mem_cons.mp h with he | h
      · subst he
        rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
          D₁ d₂ with done | lp
        · exact done
        · cases lp
      · exact ⟨0, .topR h⟩
  | @andL _ _ _ _ φ ψ h p =>
      obtain ⟨k, e⟩ := ih A (Δ := φ :: ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩) p
        (d₂.weaken (by lsub) (by lsub))
      exact ⟨_, .andL h e⟩
  | @andR _ _ _ _ φ ψ h p q =>
      rcases List.mem_cons.mp h with he | h
      · subst he
        rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
          D₁ d₂ with done | lp
        · exact done
        · cases lp with
          | and hm r =>
            obtain ⟨k₁, e₁⟩ := ih (φ.and ψ) (Δ := Δ) (Θ := φ :: Θ) (.inr ⟨hw, by omega⟩)
              (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
            obtain ⟨k₂, e₂⟩ := ih (φ.and ψ) (Δ := Δ) (Θ := ψ :: Θ) (.inr ⟨hw, by omega⟩)
              (q.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
            obtain ⟨k₃, e₃⟩ := ih (φ.and ψ) (Δ := φ :: ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
              (D₁.weaken (by lsub) (by lsub)) (r.weaken (by lsub) (by lsub))
            obtain ⟨k₄, e₄⟩ := ih ψ (Δ := φ :: Δ) (Θ := Θ)
              (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
              (e₂.weaken (by lsub) (by lsub)) (e₃.weaken (by lsub) (by lsub))
            exact ih φ (Δ := Δ) (Θ := Θ) (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
              e₁ e₄
      · obtain ⟨k₁, e₁⟩ := ih A (Δ := Δ) (Θ := φ :: Θ) (.inr ⟨hw, by omega⟩)
          (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
        obtain ⟨k₂, e₂⟩ := ih A (Δ := Δ) (Θ := ψ :: Θ) (.inr ⟨hw, by omega⟩)
          (q.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
        exact ⟨_, .andR h (both e₁ e₂).1 (both e₁ e₂).2⟩
  | @orL _ _ _ _ φ ψ h p q =>
      obtain ⟨k₁, e₁⟩ := ih A (Δ := φ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩) p
        (d₂.weaken (by lsub) (by lsub))
      obtain ⟨k₂, e₂⟩ := ih A (Δ := ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩) q
        (d₂.weaken (by lsub) (by lsub))
      exact ⟨_, .orL h (both e₁ e₂).1 (both e₁ e₂).2⟩
  | @orR _ _ _ _ φ ψ h p =>
      rcases List.mem_cons.mp h with he | h
      · subst he
        rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
          D₁ d₂ with done | lp
        · exact done
        · cases lp with
          | or hm r₁ r₂ =>
            obtain ⟨k₁, e₁⟩ := ih (φ.or ψ) (Δ := Δ) (Θ := φ :: ψ :: Θ) (.inr ⟨hw, by omega⟩)
              (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
            obtain ⟨k₂, e₂⟩ := ih (φ.or ψ) (Δ := φ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
              (D₁.weaken (by lsub) (by lsub)) (r₁.weaken (by lsub) (by lsub))
            obtain ⟨k₃, e₃⟩ := ih (φ.or ψ) (Δ := ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
              (D₁.weaken (by lsub) (by lsub)) (r₂.weaken (by lsub) (by lsub))
            obtain ⟨k₄, e₄⟩ := ih ψ (Δ := Δ) (Θ := φ :: Θ)
              (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
              (e₁.weaken (by lsub) (by lsub)) (e₃.weaken (by lsub) (by lsub))
            exact ih φ (Δ := Δ) (Θ := Θ) (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
              e₄ e₂
      · obtain ⟨k, e⟩ := ih A (Δ := Δ) (Θ := φ :: ψ :: Θ) (.inr ⟨hw, by omega⟩)
          (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
        exact ⟨_, .orR h e⟩
  | @impL _ _ _ _ φ ψ h p q =>
      obtain ⟨k₁, e₁⟩ := ih A (Δ := Δ) (Θ := φ :: Θ) (.inr ⟨hw, by omega⟩)
        (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
      obtain ⟨k₂, e₂⟩ := ih A (Δ := ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩) q
        (d₂.weaken (by lsub) (by lsub))
      exact ⟨_, .impL h (both e₁ e₂).1 (both e₁ e₂).2⟩
  | @impR _ _ _ _ φ ψ h p =>
      rcases List.mem_cons.mp h with he | h
      · subst he
        rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
          D₁ d₂ with done | lp
        · exact done
        · cases lp with
          | imp hm r₁ r₂ =>
            obtain ⟨k₁, e₁⟩ := ih (φ.imp ψ) (Δ := Δ) (Θ := φ :: Θ) (.inr ⟨hw, by omega⟩)
              (D₁.weaken (by lsub) (by lsub)) r₁
            obtain ⟨k₂, e₂⟩ := ih (φ.imp ψ) (Δ := ψ :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
              (D₁.weaken (by lsub) (by lsub)) (r₂.weaken (by lsub) (by lsub))
            obtain ⟨k₃, e₃⟩ := ih (φ.imp ψ) (Δ := φ :: Δ) (Θ := ψ :: Θ) (.inr ⟨hw, by omega⟩)
              (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
            obtain ⟨k₄, e₄⟩ := ih ψ (Δ := φ :: Δ) (Θ := Θ)
              (.inl (by rw [← hw]; simp only [WFF.weight]; omega)) e₃
              (e₂.weaken (by lsub) (by lsub))
            exact ih φ (Δ := Δ) (Θ := Θ) (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
              e₁ e₄
      · obtain ⟨k, e⟩ := ih A (Δ := φ :: Δ) (Θ := ψ :: Θ) (.inr ⟨hw, by omega⟩)
          (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
        exact ⟨_, .impR h e⟩
  | @allL _ _ _ _ _ T φ _ t h p =>
      obtain ⟨k, e⟩ := ih A (Δ := WFF.instantiate Ctx.NoSlots.slots t φ :: Δ) (Θ := Θ)
        (.inr ⟨hw, by omega⟩) p (d₂.weaken (by lsub) (by lsub))
      exact ⟨_, .allL T t h e⟩
  | @allR _ _ _ _ _ u T hu φ h p =>
      rcases List.mem_cons.mp h with he | h
      · subst he
        rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
          D₁ d₂ with done | lp
        · exact done
        · cases lp with
          | all t hm r =>
            have p' := instEigenR hu t (Δ := Δ)
              (Θ := WFF.all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ) :: Θ) p
            obtain ⟨k₁, e₁⟩ := ih (WFF.all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ))
              (Δ := WFF.instantiate Ctx.NoSlots.slots t
                (WFF.bindFree u hu Ctx.NoSlots.slots T φ) :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
              (D₁.weaken (by lsub) (by lsub)) (r.weaken (by lsub) (by lsub))
            obtain ⟨k₂, e₂⟩ := ih (WFF.all T (WFF.bindFree u hu Ctx.NoSlots.slots T φ))
              (Δ := Δ) (Θ := WFF.instantiate Ctx.NoSlots.slots t
                (WFF.bindFree u hu Ctx.NoSlots.slots T φ) :: Θ) (.inr ⟨hw, by omega⟩)
              (p'.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
            exact ih _ (Δ := Δ) (Θ := Θ)
              (.inl (by rw [WFF.weight_instantiate, ← hw]; simp only [WFF.weight]; omega)) e₂ e₁
      · haveI := Ctx.Presented.insertFree inferInstance u hu T
        obtain ⟨k, e⟩ := ih (WFF.weaken hu.root T A) (Δ := Δ.map (WFF.weaken hu.root T))
          (Θ := φ :: Θ.map (WFF.weaken hu.root T))
          (.inr ⟨(WFF.weight_mono _ A).trans hw, by omega⟩)
          (p.weaken (fun _ h => h) (by lsub)) ((weakenCtx hu T d₂).weaken (by lsub) (by lsub))
        exact ⟨_, .allR u T hu h e⟩
  | @exL _ _ _ _ _ u T hu φ h p =>
      haveI := Ctx.Presented.insertFree inferInstance u hu T
      obtain ⟨k, e⟩ := ih (WFF.weaken hu.root T A) (Δ := φ :: Δ.map (WFF.weaken hu.root T))
        (Θ := Θ.map (WFF.weaken hu.root T))
        (.inr ⟨(WFF.weight_mono _ A).trans hw, by omega⟩)
        (p.weaken (fun _ h => h) (by lsub)) ((weakenCtx hu T d₂).weaken (by lsub) (fun _ h => h))
      exact ⟨_, .exL u T hu h e⟩
  | @exR _ _ _ _ _ T φ _ t h p =>
      rcases List.mem_cons.mp h with he | h
      · subst he
        rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
          D₁ d₂ with done | lp
        · exact done
        · cases lp with
          | @ex _ _ _ _ _ u T' hu φ' hm r =>
            have r' := instEigenL hu t
              (Δ := WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ') :: Δ) (Θ := Θ) r
            obtain ⟨k₁, e₁⟩ := ih (WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ')) (Δ := Δ)
              (Θ := WFF.instantiate Ctx.NoSlots.slots t
                (WFF.bindFree u hu Ctx.NoSlots.slots T φ') :: Θ) (.inr ⟨hw, by omega⟩)
              (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
            obtain ⟨k₂, e₂⟩ := ih (WFF.ex T (WFF.bindFree u hu Ctx.NoSlots.slots T φ'))
              (Δ := WFF.instantiate Ctx.NoSlots.slots t
                (WFF.bindFree u hu Ctx.NoSlots.slots T φ') :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩)
              (D₁.weaken (by lsub) (by lsub)) (r'.weaken (by lsub) (by lsub))
            exact ih _ (Δ := Δ) (Θ := Θ)
              (.inl (by rw [WFF.weight_instantiate, ← hw]; simp only [WFF.weight]; omega)) e₁ e₂
      · obtain ⟨k, e⟩ := ih A (Δ := Δ) (Θ := WFF.instantiate Ctx.NoSlots.slots t φ :: Θ)
          (.inr ⟨hw, by omega⟩) (p.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))
        exact ⟨_, .exR T t h e⟩
  | ref t p =>
      obtain ⟨k, e⟩ := ih A (Δ := .eq t t :: Δ) (Θ := Θ) (.inr ⟨hw, by omega⟩) p
        (d₂.weaken (by lsub) (by lsub))
      exact ⟨_, .ref t e⟩
  | @repl _ _ _ _ _ P hP t s' h₁ h₂ p =>
      obtain ⟨k, e⟩ := ih A (Δ := WFF.instantiate Ctx.NoSlots.slots s' P :: Δ) (Θ := Θ)
        (.inr ⟨hw, by omega⟩) p (d₂.weaken (by lsub) (by lsub))
      exact ⟨_, .repl hP t s' h₁ h₂ e⟩
  | @boxR _ _ _ _ Δ₁ φ h₁ h₂ p =>
      rcases List.mem_cons.mp h₁ with he | h₁
      · subst he
        rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
          D₁ d₂ with done | lp
        · exact done
        · have hlt : φ.weight < w := by rw [← hw]; simp only [WFF.weight]; omega
          cases lp with
          | @box _ φ' Δ₂ _ _ _ _ hm h₁' h₂' r =>
            have hr : Δ₂ ⊆ φ :: (Δ₁ ++ boxedIn Δ Δ₂) := fun χ hχ => by
              rcases boxedIn_sub h₂' χ hχ with rfl | hχ
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_append_right _ hχ)
            obtain ⟨k, e⟩ := ih φ (Γ := Γ.boxIn) (Δ := Δ₁ ++ boxedIn Δ Δ₂) (Θ := [φ'])
              (.inl hlt) (p.weaken (by lsub) (by lsub)) (r.weaken hr (fun _ h => h))
            refine ⟨_, .boxR h₁' (fun χ hχ => ?_) e⟩
            rcases List.mem_append.mp hχ with hχ | hχ
            exacts [h₂ χ hχ, boxedIn_mem hχ]
          | @boxDia _ x hx ψ Δ₂ Θ₂ _ _ _ _ hm hψ h₂' h₃' r =>
            have p' := p.monoCtx (Ctx.le_boxIn_diaIn Γ x)
            have hl : Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) ⊆
                ψ :: (Δ₁ ++ boxedIn Δ Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) := fun a ha => by
              obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
              exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_left _ hb))
            have hr : ψ :: Δ₂.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) ⊆
                WFF.mono (Ctx.le_boxIn_diaIn Γ x) φ ::
                  ψ :: (Δ₁ ++ boxedIn Δ Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) :=
              fun a ha => by
                rcases List.mem_cons.mp ha with rfl | ha
                · exact List.mem_cons_of_mem _ List.mem_cons_self
                · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
                  rcases boxedIn_sub h₂' b hb with rfl | hb
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_map_of_mem (List.mem_append_right _ hb)))
            obtain ⟨k, e⟩ := ih (WFF.mono (Ctx.le_boxIn_diaIn Γ x) φ) (Γ := Γ.diaIn x)
              (Δ := ψ :: (Δ₁ ++ boxedIn Δ Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
              (Θ := Θ₂) (.inl (by rw [WFF.weight_mono]; exact hlt))
              (p'.weaken hl (by lsub)) (r.weaken hr (fun _ h => h))
            refine ⟨_, .diaL x hx hψ (fun χ hχ => ?_) h₃' e⟩
            rcases List.mem_append.mp hχ with hχ | hχ
            exacts [h₂ χ hχ, boxedIn_mem hχ]
      · exact ⟨_, .boxR h₁ h₂ p⟩
  | @diaL _ _ _ _ x hx ψ Δ₁ Θ₁ h₁ h₂ h₃ p =>
      by_cases hall : ∀ χ ∈ Θ₁, WFF.dia x hx χ ∈ Θ
      · exact ⟨_, .diaL x hx h₁ h₂ hall p⟩
      · push_neg at hall
        obtain ⟨χ₀, hχ₀, hn⟩ := hall
        have he := (List.mem_cons.mp (h₃ χ₀ hχ₀)).resolve_right hn
        subst he
        rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
          D₁ d₂ with done | lp
        · exact done
        · cases lp with
          | @dia _ _ _ Δ₂ Θ₂ _ _ _ _ hm h₂' h₃' r =>
            have hsub : ∀ χ ∈ Θ₁,
                χ = χ₀ ∨ χ ∈ Θ₁.filter fun χ => decide (WFF.dia x hx χ ∈ Θ) := by
              intro χ hχ
              by_cases hd : WFF.dia x hx χ ∈ Θ
              · exact .inr (List.mem_filter.mpr ⟨hχ, decide_eq_true hd⟩)
              · exact .inl (eq_of_heq (WFF.dia.inj
                  ((List.mem_cons.mp (h₃ χ hχ)).resolve_right hd)).2)
            have hl₁ : ψ :: Δ₁.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) ⊆
                ψ :: (Δ₁ ++ Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) := fun a ha => by
              rcases List.mem_cons.mp ha with rfl | ha
              · exact List.mem_cons_self
              · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
                exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_left _ hb))
            have hl₂ : Θ₁ ⊆
                χ₀ :: (Θ₁.filter (fun χ => decide (WFF.dia x hx χ ∈ Θ)) ++ Θ₂) := fun a ha => by
              rcases hsub a ha with rfl | ha
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)
            have hr : χ₀ :: Δ₂.map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) ⊆
                χ₀ :: ψ :: (Δ₁ ++ Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) := fun a ha => by
              rcases List.mem_cons.mp ha with rfl | ha
              · exact List.mem_cons_self
              · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_map_of_mem (List.mem_append_right _ hb)))
            obtain ⟨k, e⟩ := ih χ₀ (Γ := Γ.diaIn x)
              (Δ := ψ :: (Δ₁ ++ Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
              (Θ := Θ₁.filter (fun χ => decide (WFF.dia x hx χ ∈ Θ)) ++ Θ₂)
              (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
              (p.weaken hl₁ hl₂) (r.weaken hr (by lsub))
            refine ⟨_, .diaL x hx h₁ (fun χ hχ => ?_) (fun χ hχ => ?_) e⟩
            · rcases List.mem_append.mp hχ with hχ | hχ
              exacts [h₂ χ hχ, h₂' χ hχ]
            · rcases List.mem_append.mp hχ with hχ | hχ
              · exact of_decide_eq_true (List.mem_filter.mp hχ).2
              · exact h₃' χ hχ

/-- The induction, on the weight and then on the sum of the heights. -/
theorem cutIH_all : ∀ w s, CutIH σ w s := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ihw =>
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ihs =>
      intro Γ _ A n m Δ Θ hlt d₁ d₂
      rcases hlt with hlt | ⟨heq, hlt⟩
      · exact cut_step (ihw _ hlt (n + m)) A rfl rfl d₁ d₂
      · exact cut_step (ihs _ hlt) A heq rfl d₁ d₂

/-- ⭐**Cut is admissible** in GK: from `Δ ⇒ A, Θ` and `A, Δ ⇒ Θ`, `Δ ⇒ Θ`, over any presented
    context. -/
theorem cut {Γ : Ctx} [Γ.Presented] (A : WFF σ Γ 0) {n m : ℕ} {Δ Θ : List (WFF σ Γ 0)}
    (d₁ : GK σ n Γ Δ (A :: Θ)) (d₂ : GK σ m Γ (A :: Δ) Θ) : ∃ k, GK σ k Γ Δ Θ :=
  cut_step (cutIH_all _ _) A rfl rfl d₁ d₂

/-- Cut with separate contexts: from `Δ₁ ⇒ A, Θ₁` and `A, Δ₂ ⇒ Θ₂`, `Δ₁, Δ₂ ⇒ Θ₁, Θ₂`. -/
theorem cut' {Γ : Ctx} [Γ.Presented] (A : WFF σ Γ 0) {n m : ℕ}
    {Δ₁ Θ₁ Δ₂ Θ₂ : List (WFF σ Γ 0)} (d₁ : GK σ n Γ Δ₁ (A :: Θ₁)) (d₂ : GK σ m Γ (A :: Δ₂) Θ₂) :
    ∃ k, GK σ k Γ (Δ₁ ++ Δ₂) (Θ₁ ++ Θ₂) :=
  cut A (d₁.weaken (by lsub) (by lsub)) (d₂.weaken (by lsub) (by lsub))

end GK

end V12M
