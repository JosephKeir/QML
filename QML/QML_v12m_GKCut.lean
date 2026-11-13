import QML.QML_v12m_GKShift
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
  moving the `□`-view premise into the `◇_x` view (`GK.Into`); two `◇` formulas meet only
  with the same witness.
* Under 4 a premise also has the cut formula's 4-copy (`□(shift φ)` on the left, or
  `◇_{y.keep}(shift θ)` on the right), as heavy as the cut formula.  It is cut first, against the
  other side's conclusion **re-derived one view in**: that side's premise shifted (`GK.shiftD`),
  the rule applied in the view (`GK.boxCut`, `GK.copyCut`).  The re-derivation is as high as the
  other side's derivation and the copy's premise is lower, so the sum of heights drops.
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
  | _, _, _, _, _, _, _, _, _, _, .optx _ .arrow _ _ φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ φ]
  | _, _, _, _, _, _, _, _, _, _, .optx _ .ident _ _ φ => by
      simp only [WFF.subst, WFF.weight]
      rw [WFF.weight_subst _ _ _ _ _ φ]

theorem WFF.weight_instantiate {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {T : VarType} {a : Ann T}
    (t : Term σ Γ T a) (φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) :
    (WFF.instantiate hs t φ).weight = φ.weight :=
  WFF.weight_subst _ _ _ _ _ φ

/-- Weakening keeps the weight. -/
theorem WFF.weight_mono {Γ Γ' : Ctx} [Γ'.NoSlots] (h : Γ.Le Γ') (φ : WFF σ Γ 0) :
    (WFF.mono h φ).weight = φ.weight := by
  rw [← WFF.subst_ren h (Subst.idRen Γ') (Subst.ok_idRen.restrict h) (Subst.coh_idRen.restrict h)
    ((Ctx.NoSlots.slots (Γ := Γ')).of_le h) Ctx.NoSlots.slots (fun v _ _ => Subst.at_idRen v) φ
    (fun _ _ _ _ => rfl)]
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
  refine (WFF.subst_ren (Ctx.Le.refl Γ) _ _ _ _ _ (fun v U hv => ?_) δ (fun _ _ _ _ => rfl)).trans
    (WFF.mono_refl _ δ)
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

/-- Where the `□` view's derivations go: the `□` view itself, or a `◇_x` view (`GK.monoCtx`). -/
structure Into (σ : Signature) (Γ V : Ctx) where
  M : WFF σ Γ.boxIn 0 → WFF σ V 0
  weight : ∀ χ, (M χ).weight = χ.weight
  tr : ∀ {k : ℕ} {Δ Θ : List (WFF σ Γ.boxIn 0)}, GK σ k Γ.boxIn Δ Θ →
    GK σ k V (Δ.map M) (Θ.map M)

def Into.self (Γ : Ctx) : Into σ Γ Γ.boxIn :=
  ⟨id, fun _ => rfl, fun p => by rw [List.map_id, List.map_id]; exact p⟩

def Into.dia (Γ : Ctx) [Γ.Presented] (x : VarSymb) : Into σ Γ (Γ.diaIn x) :=
  ⟨WFF.mono (Ctx.le_boxIn_diaIn Γ x), WFF.weight_mono _, fun p => p.monoCtx _⟩

theorem Into.self_M (Γ : Ctx) : (Into.self (σ := σ) Γ).M = id := rfl

theorem Into.dia_M (Γ : Ctx) [Γ.Presented] (x : VarSymb) :
    (Into.dia (σ := σ) Γ x).M = WFF.mono (Ctx.le_boxIn_diaIn Γ x) := rfl

/-- List inclusions between rearrangements with copies, optionally through one inclusion. -/
macro "lsub4" : tactic =>
  `(tactic|
    (intro a ha
     clear * - ha
     try simp only [Into.self_M, Into.dia_M, List.map_id, id_eq, List.map_append, List.map_cons,
       List.map_nil, cp4_append, kp4_append, List.mem_cons, List.mem_append,
       List.mem_singleton] at ha ⊢
     tauto))

macro "lsub4" " using " h:term : tactic =>
  `(tactic|
    (intro a ha
     have hh := @$h a
     clear * - ha hh
     try simp only [Into.self_M, Into.dia_M, List.map_id, id_eq, List.map_append, List.map_cons,
       List.map_nil, cp4_append, kp4_append, List.mem_cons, List.mem_append,
       List.mem_singleton] at ha hh ⊢
     tauto))

/-! ## The copies -/

theorem mem_cp4 {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) {Δ₁ : List (WFF σ Γ.boxIn 0)}
    {χ : WFF σ Γ.boxIn 0} (h : χ ∈ Δ₁) :
    WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots χ) ∈ cp4 Δ₁ := by
  unfold cp4; rw [dif_pos hF]; exact List.mem_map_of_mem h

theorem mem_kp4 {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) {L : List (WFF σ Γ 0)}
    {y : VarSymb} {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)} {θ : WFF σ (Γ.diaIn y) 0}
    (h : WFF.dia y hy θ ∈ L) :
    WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots θ) ∈ kp4 L := by
  unfold kp4; rw [dif_pos hF]; exact List.mem_flatMap.mpr ⟨_, h, List.mem_singleton_self _⟩

/-- The members of `L` in `Θ` carry every copy of `L` but `A`'s. -/
theorem kp4_split {Γ : Ctx} [Γ.NoSlots] {A : WFF σ Γ 0} {L Θ : List (WFF σ Γ 0)}
    (h : L ⊆ A :: Θ) : kp4 L ⊆ kp4 [A] ++ kp4 (L.filter fun χ => decide (χ ∈ Θ)) := by
  unfold kp4; split
  · intro a ha
    obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
    by_cases hbΘ : b ∈ Θ
    · exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨b, List.mem_filter.mpr ⟨hb, decide_eq_true hbΘ⟩, ha⟩)
    · have he := (List.mem_cons.mp (h hb)).resolve_right hbΘ
      subst he
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨b, List.mem_singleton_self _, ha⟩)
  · exact fun _ h => h

theorem kp4_drop {Γ : Ctx} [Γ.NoSlots] {A : WFF σ Γ 0} {L Θ : List (WFF σ Γ 0)}
    (h : L ⊆ A :: Θ) (hk : kp4 [A] = []) :
    kp4 L ⊆ kp4 (L.filter fun χ => decide (χ ∈ Θ)) := by
  have e := kp4_split h
  rwa [hk, List.nil_append] at e

theorem filter_sub {Γ : Ctx} {L Θ : List (WFF σ Γ 0)} :
    L.filter (fun χ => decide (χ ∈ Θ)) ⊆ Θ :=
  fun _ h => of_decide_eq_true (List.mem_filter.mp h).2

/-- Only a `◇` formula has a copy. -/
theorem kp4_single_ne {Γ : Ctx} [Γ.NoSlots] {A : WFF σ Γ 0} (h : kp4 [A] ≠ []) :
    ∃ y hy θ, A = WFF.dia y hy θ := by
  unfold kp4 at h
  split at h
  · cases A
    case dia y hy θ => exact ⟨y, hy, θ, rfl⟩
    all_goals exact absurd rfl h
  · exact absurd rfl h

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
  | box [Γ.NoSlots] {φ : WFF σ Γ.boxIn 0} (φ' : WFF σ Γ.boxIn 0) (Δ₂ : List (WFF σ Γ.boxIn 0))
      (L₂ : List (WFF σ Γ 0)) {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → WFF.box (Γ := Γ) φ' ∈ Θ →
      (∀ χ ∈ Δ₂, WFF.box (Γ := Γ) χ ∈ WFF.box (Γ := Γ) φ :: Δ) → L₂ ⊆ Θ →
      GK σ m' Γ.boxIn (Δ₂ ++ cp4 Δ₂) (φ' :: kp4 L₂) → LeftPrin σ (WFF.box φ) m Δ Θ
  | boxSerial [Γ.NoSlots] {φ : WFF σ Γ.boxIn 0} (hD : ModalSys.D = true)
      (Δ₂ : List (WFF σ Γ.boxIn 0)) (L₂ : List (WFF σ Γ 0)) {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → (∀ χ ∈ Δ₂, WFF.box (Γ := Γ) χ ∈ WFF.box (Γ := Γ) φ :: Δ) → L₂ ⊆ Θ →
      GK σ m' Γ.boxIn (Δ₂ ++ cp4 Δ₂) (kp4 L₂) → LeftPrin σ (WFF.box φ) m Δ Θ
  | boxDia [Γ.NoSlots] {φ : WFF σ Γ.boxIn 0} (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
      (ψ : WFF σ (Γ.diaIn x) 0) (Δ₂ : List (WFF σ Γ.boxIn 0)) (Θ₂ : List (WFF σ (Γ.diaIn x) 0))
      (L₂ : List (WFF σ Γ 0)) {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → .dia x hx ψ ∈ Δ →
      (∀ χ ∈ Δ₂, WFF.box (Γ := Γ) χ ∈ WFF.box (Γ := Γ) φ :: Δ) →
      (∀ χ ∈ Θ₂, .dia x hx χ ∈ Θ) → L₂ ⊆ Θ →
      GK σ m' (Γ.diaIn x) (ψ :: (Δ₂ ++ cp4 Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
        (Θ₂ ++ (kp4 L₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) →
      LeftPrin σ (WFF.box φ) m Δ Θ
  | dia [Γ.NoSlots] (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
      {ψ : WFF σ (Γ.diaIn x) 0} (Δ₂ : List (WFF σ Γ.boxIn 0)) (Θ₂ : List (WFF σ (Γ.diaIn x) 0))
      (L₂ : List (WFF σ Γ 0)) {m m' : ℕ} {Δ Θ : List (WFF σ Γ 0)} :
      m' < m → (∀ χ ∈ Δ₂, WFF.box (Γ := Γ) χ ∈ Δ) → (∀ χ ∈ Θ₂, .dia x hx χ ∈ Θ) → L₂ ⊆ Θ →
      GK σ m' (Γ.diaIn x) (ψ :: (Δ₂ ++ cp4 Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
        (Θ₂ ++ (kp4 L₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) →
      LeftPrin σ (.dia x hx ψ) m Δ Θ

/-- A rule's boxed hypotheses either avoid the cut formula or it is one of them. -/
theorem split_boxes {Γ : Ctx} {A : WFF σ Γ 0} {Δ : List (WFF σ Γ 0)}
    {Δ₁ : List (WFF σ Γ.boxIn 0)} (h : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ A :: Δ) :
    (∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) ∨ ∃ φ, A = WFF.box φ := by
  by_cases hall : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ
  · exact .inl hall
  · push_neg at hall
    obtain ⟨χ, hχ, hn⟩ := hall
    exact .inr ⟨χ, ((List.mem_cons.mp (h χ hχ)).resolve_right hn).symm⟩

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
  | boxR h₁ h₂ h₃ r =>
      rcases split_boxes h₂ with hall | ⟨φ, rfl⟩
      · exact .inl ⟨_, .boxR h₁ hall h₃ r⟩
      · exact .inr (.box _ _ _ (Nat.lt_succ_self _) h₁ h₂ h₃ r)
  | serial hD h₂ h₃ r =>
      rcases split_boxes h₂ with hall | ⟨φ, rfl⟩
      · exact .inl ⟨_, .serial hD hall h₃ r⟩
      · exact .inr (.boxSerial hD _ _ (Nat.lt_succ_self _) h₂ h₃ r)
  | diaL x hx h₁ h₂ h₃ h₄ r =>
      rcases List.mem_cons.mp h₁ with he | h₁'
      · subst he
        refine .inr (.dia x hx _ _ _ (Nat.lt_succ_self _) (fun χ hχ => ?_) h₃ h₄ r)
        exact (List.mem_cons.mp (h₂ χ hχ)).resolve_left fun he => by cases he
      · rcases split_boxes h₂ with hall | ⟨φ, rfl⟩
        · exact .inl ⟨_, .diaL x hx h₁' hall h₃ h₄ r⟩
        · exact .inr (.boxDia x hx _ _ _ _ (Nat.lt_succ_self _) h₁' h₂ h₃ h₄ r)

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

theorem box_hr {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ.boxIn 0}
    {Δ₁ Δ₂ : List (WFF σ Γ.boxIn 0)}
    (h : ∀ χ ∈ Δ₂, WFF.box (Γ := Γ) χ ∈ WFF.box (Γ := Γ) φ :: Δ) :
    Δ₂ ++ cp4 Δ₂ ⊆ φ :: (cp4 [φ] ++ ((Δ₁ ++ boxedIn Δ Δ₂) ++ cp4 (Δ₁ ++ boxedIn Δ Δ₂))) := by
  have h' : Δ₂ ⊆ [φ] ++ boxedIn Δ Δ₂ := fun χ hχ => by
    rcases boxedIn_sub h χ hχ with rfl | hb
    · exact List.mem_append_left _ (List.mem_singleton_self _)
    · exact List.mem_append_right _ hb
  have hc := cp4_sub h'
  rw [cp4_append] at hc
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp (h' ha) with ha | ha
    · rw [List.mem_singleton.mp ha]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ ha)))
  · rcases List.mem_append.mp (hc ha) with ha | ha
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)
    · refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ ?_))
      rw [cp4_append]; exact List.mem_append_right _ ha

/-! ## The modal reductions -/

/-- ⭐**`□φ` principal on both sides**, in the view `V` the right premise lives in.  Under 4 the
    right premise also has `□(shift φ)`: cut it first, against the left conclusion re-derived
    inside the `□` view (the left premise shifted, then `□R` there); then cut `φ`. -/
theorem boxCut {w s : ℕ} (ih : CutIH σ w s) {Γ V : Ctx} [Γ.Presented] [V.Presented]
    (I : Into σ Γ V) {φ : WFF σ Γ.boxIn 0} (hw : (WFF.box (Γ := Γ) φ).weight = w) {n' m' : ℕ}
    (hs : n' + 1 + m' < s) {Δ₁ : List (WFF σ Γ.boxIn 0)} {L₁ : List (WFF σ Γ 0)}
    (p : GK σ n' Γ.boxIn (Δ₁ ++ cp4 Δ₁) (φ :: kp4 L₁)) {Δ' Θ' Δr : List (WFF σ V 0)}
    (h₁ : (Δ₁ ++ cp4 Δ₁).map I.M ⊆ Δ') (h₂ : (kp4 L₁).map I.M ⊆ Θ')
    (hr : Δr ⊆ I.M φ :: ((cp4 [φ]).map I.M ++ Δ')) (r : GK σ m' V Δr Θ') :
    ∃ k, GK σ k V Δ' Θ' := by
  have hφ : (I.M φ).weight < w := by rw [I.weight, ← hw]; simp only [WFF.weight]; omega
  have hp : GK σ n' V Δ' (I.M φ :: Θ') := (I.tr p).weaken h₁ (by
    rw [List.map_cons]; exact List.cons_subset_cons _ h₂)
  obtain ⟨k, e⟩ : ∃ k, GK σ k V (I.M φ :: Δ') Θ' := by
    by_cases hF : ModalSys.Four = true
    · have hc : cp4 [φ] =
          [WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ)] := by
        unfold cp4; rw [dif_pos hF]; rfl
      obtain ⟨Lv, hlv⟩ := Ctx.Presented.leveled Γ.boxIn
      have q := p.shiftD (Ctx.shifts_boxIn_boxIn hF Γ) hlv
      rw [List.map_append, shift_cp4 hF, List.map_cons, shift_kp4 hF] at q
      have D : GK σ (n' + 1) Γ.boxIn (Δ₁ ++ cp4 Δ₁)
          (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ) :: kp4 L₁) :=
        .boxR List.mem_cons_self (fun χ hχ => by
            obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
            exact List.mem_append_right _ (mem_cp4 hF hχ₀))
          (fun _ h => List.mem_cons_of_mem _ h) q
      rw [hc] at hr
      refine ih (I.M (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots φ)))
        (Δ := I.M φ :: Δ') (Θ := Θ') (.inr ⟨?_, by omega⟩) ((I.tr D).weaken ?_ ?_)
        (r.weaken ?_ (fun _ h => h))
      · rw [I.weight, ← hw]; simp only [WFF.weight, WFF.weight_shift]
      · exact fun a ha => List.mem_cons_of_mem _ (h₁ ha)
      · rw [List.map_cons]; exact List.cons_subset_cons _ h₂
      · intro a ha
        rcases List.mem_cons.mp (hr ha) with rfl | h
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_append.mp h with h | h
          · rw [List.map_cons, List.map_nil, List.mem_singleton] at h
            subst h
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    · rw [cp4_of_not (Bool.eq_false_iff.mpr hF), List.map_nil, List.nil_append] at hr
      exact ⟨_, r.weaken hr (fun _ h => h)⟩
  exact ih (I.M φ) (.inl hφ) hp e

/-- ⭐**A `◇_y θ`'s copy `◇_{y.keep}(shift θ)` cut out of a premise** in the view `V`, against the
    right conclusion re-derived inside the `□` view (its premise shifted into the `◇_{y.keep}`
    view, then `◇_xL` there).  Without 4 there is no copy. -/
theorem copyCut {w s : ℕ} (ih : CutIH σ w s) {Γ V : Ctx} [Γ.Presented] [V.Presented]
    (I : Into σ Γ V) {y : VarSymb} {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)}
    {θ : WFF σ (Γ.diaIn y) 0} (hw : (WFF.dia y hy θ).weight = w) {n' m' : ℕ}
    (hs : n' + (m' + 1) < s) {Δ₂ : List (WFF σ Γ.boxIn 0)} {Θ₂ : List (WFF σ (Γ.diaIn y) 0)}
    {L₂ : List (WFF σ Γ 0)}
    (r : GK σ m' (Γ.diaIn y) (θ :: (Δ₂ ++ cp4 Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ y)))
      (Θ₂ ++ (kp4 L₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ y))))
    {Δp Θp Θ' : List (WFF σ V 0)} (hp : Θp ⊆ (kp4 [WFF.dia y hy θ]).map I.M ++ Θ')
    (p : GK σ n' V Δp Θp) :
    ∃ k, GK σ k V (Δp ++ (Δ₂ ++ cp4 Δ₂).map I.M)
      (Θ' ++ (kp4 (Θ₂.map (WFF.dia y hy) ++ L₂)).map I.M) := by
  by_cases hF : ModalSys.Four = true
  swap
  · rw [kp4_of_not (Bool.eq_false_iff.mpr hF), List.map_nil, List.nil_append] at hp
    exact ⟨_, p.weaken (fun _ h => List.mem_append_left _ h)
      (fun _ h => List.mem_append_left _ (hp h))⟩
  -- the right premise one view further in
  obtain ⟨Lv, hlv⟩ := Ctx.Presented.leveled (Γ.diaIn y)
  have q := r.shiftD (Ctx.shifts_diaIn_keep hF Γ y) hlv
  have hcomm : ∀ X : List (WFF σ Γ.boxIn 0),
      (X.map (WFF.mono (Ctx.le_boxIn_diaIn Γ y))).map
          (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots) =
        (X.map (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots)).map
          (WFF.mono (Ctx.le_boxIn_diaIn Γ.boxIn (.step y .keep))) := fun X => by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun χ _ => shift_mono_diaIn hF y χ
  have e₁ : (θ :: (Δ₂ ++ cp4 Δ₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ y))).map
        (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots) =
      WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots θ ::
        (Δ₂.map (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots) ++
          cp4 (Δ₂.map (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots))).map
          (WFF.mono (Ctx.le_boxIn_diaIn Γ.boxIn (.step y .keep))) := by
    rw [List.map_cons, hcomm]
    congr 2
    rw [List.map_append, shift_cp4 hF]
  have e₂ : (Θ₂ ++ (kp4 L₂).map (WFF.mono (Ctx.le_boxIn_diaIn Γ y))).map
        (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots) =
      Θ₂.map (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots) ++
        (kp4 (kp4 L₂)).map (WFF.mono (Ctx.le_boxIn_diaIn Γ.boxIn (.step y .keep))) := by
    rw [List.map_append, hcomm, shift_kp4 hF]
  rw [e₁, e₂] at q
  -- the right conclusion, kept: `◇_{y.keep}(shift θ)` on the left
  have E : GK σ (m' + 1) Γ.boxIn
      (WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
        (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots θ) :: (Δ₂ ++ cp4 Δ₂))
      (kp4 (Θ₂.map (WFF.dia y hy) ++ L₂)) :=
    .diaL (.step y .keep) (Ctx.exists_keep_dia hF hy) List.mem_cons_self
      (fun χ hχ => by
        obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (mem_cp4 hF hχ₀)))
      (fun χ hχ => by
        obtain ⟨χ₀, hχ₀, rfl⟩ := List.mem_map.mp hχ
        exact mem_kp4 hF (List.mem_append_left _ (List.mem_map_of_mem hχ₀)))
      (kp4_sub fun _ h => List.mem_append_right _ h) q
  have hk : kp4 [WFF.dia y hy θ] = [WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots θ)] := by
    unfold kp4; rw [dif_pos hF]; rfl
  rw [hk, List.map_cons, List.map_nil, List.singleton_append] at hp
  refine ih (I.M (WFF.dia (.step y .keep) (Ctx.exists_keep_dia hF hy)
      (WFF.shift (Ctx.shifts_diaIn_keep hF Γ y) Ctx.NoSlots.slots θ)))
    (Δ := Δp ++ (Δ₂ ++ cp4 Δ₂).map I.M)
    (Θ := Θ' ++ (kp4 (Θ₂.map (WFF.dia y hy) ++ L₂)).map I.M) (.inr ⟨?_, by omega⟩)
    (p.weaken (fun _ h => List.mem_append_left _ h) ?_) ((I.tr E).weaken ?_ ?_)
  · rw [I.weight, ← hw]; simp only [WFF.weight, WFF.weight_shift]
  · intro a ha
    rcases List.mem_cons.mp (hp ha) with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
  · rw [List.map_cons]
    exact List.cons_subset_cons _ fun _ h => List.mem_append_right _ h
  · exact fun _ h => List.mem_append_right _ h

/-- `□φ` principal in a left `□R`: the right derivation's rule boxes `φ`. -/
theorem boxPrin {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] {φ : WFF σ Γ.boxIn 0}
    {n' m : ℕ} {Δ Θ : List (WFF σ Γ 0)} (hw : (WFF.box (Γ := Γ) φ).weight = w)
    (hs : n' + 1 + m = s) {Δ₁ : List (WFF σ Γ.boxIn 0)} {L₁ : List (WFF σ Γ 0)}
    (h₂ : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) (h₃ : L₁ ⊆ WFF.box φ :: Θ)
    (p : GK σ n' Γ.boxIn (Δ₁ ++ cp4 Δ₁) (φ :: kp4 L₁)) (lp : LeftPrin σ (WFF.box φ) m Δ Θ) :
    ∃ k, GK σ k Γ Δ Θ := by
  have hL₁ := kp4_drop h₃ (by unfold kp4; split <;> rfl)
  have hb : ∀ {Δ₂ : List (WFF σ Γ.boxIn 0)}, ∀ χ ∈ Δ₁ ++ boxedIn Δ Δ₂, WFF.box (Γ := Γ) χ ∈ Δ :=
    fun χ hχ => (List.mem_append.mp hχ).elim (h₂ χ) fun h => boxedIn_mem h
  have hL : ∀ {L₂ : List (WFF σ Γ 0)}, L₂ ⊆ Θ →
      (L₁.filter fun χ => decide (χ ∈ Θ)) ++ L₂ ⊆ Θ := fun h a ha =>
    (List.mem_append.mp ha).elim (fun h' => filter_sub h') (fun h' => h h')
  cases lp with
  | box φ' Δ₂ L₂ hm h₁' h₂' h₃' r =>
      have U := box_hr (Δ₁ := Δ₁) h₂'
      obtain ⟨k, e⟩ := boxCut ih (Into.self Γ) hw (by omega) p
        (Δ' := (Δ₁ ++ boxedIn Δ Δ₂) ++ cp4 (Δ₁ ++ boxedIn Δ Δ₂))
        (Θ' := φ' :: kp4 ((L₁.filter fun χ => decide (χ ∈ Θ)) ++ L₂))
        (by lsub4) (by lsub4 using hL₁) (by simpa only [Into.self_M, List.map_id, id_eq] using U)
        (r.weaken (fun _ h => h) (by lsub4))
      exact ⟨_, .boxR h₁' hb (hL h₃') e⟩
  | boxSerial hD Δ₂ L₂ hm h₂' h₃' r =>
      have U := box_hr (Δ₁ := Δ₁) h₂'
      obtain ⟨k, e⟩ := boxCut ih (Into.self Γ) hw (by omega) p
        (Δ' := (Δ₁ ++ boxedIn Δ Δ₂) ++ cp4 (Δ₁ ++ boxedIn Δ Δ₂))
        (Θ' := kp4 ((L₁.filter fun χ => decide (χ ∈ Θ)) ++ L₂))
        (by lsub4) (by lsub4 using hL₁) (by simpa only [Into.self_M, List.map_id, id_eq] using U)
        (r.weaken (fun _ h => h) (by lsub4))
      exact ⟨_, .serial hD hb (hL h₃') e⟩
  | boxDia x hx ψ Δ₂ Θ₂ L₂ hm hψ h₂' h₃' h₄' r =>
      have U := List.map_subset (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) (box_hr (Δ₁ := Δ₁) h₂')
      have hL₁' := List.map_subset (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) hL₁
      obtain ⟨k, e⟩ := boxCut ih (Into.dia Γ x) hw (by omega) p
        (Δ' := ψ :: ((Δ₁ ++ boxedIn Δ Δ₂) ++ cp4 (Δ₁ ++ boxedIn Δ Δ₂)).map
          (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
        (Θ' := Θ₂ ++ (kp4 ((L₁.filter fun χ => decide (χ ∈ Θ)) ++ L₂)).map
          (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
        (by lsub4) (by lsub4 using hL₁') (by lsub4 using U) (r.weaken (fun _ h => h) (by lsub4))
      exact ⟨_, .diaL x hx hψ hb h₃' (hL h₄') e⟩

/-- The new copy list's members are conclusions: a `◇_y θ`'s, and the right rule's. -/
theorem dia_hL {Γ : Ctx} {y : VarSymb} {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)}
    {Θ L₁ L₂ : List (WFF σ Γ 0)} {Θ₂ : List (WFF σ (Γ.diaIn y) 0)}
    (h₃' : ∀ χ ∈ Θ₂, WFF.dia y hy χ ∈ Θ) (h₄' : L₂ ⊆ Θ) :
    (L₁.filter fun χ => decide (χ ∈ Θ)) ++ (Θ₂.map (WFF.dia y hy) ++ L₂) ⊆ Θ := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact filter_sub h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      exact h₃' b hb
    · exact h₄' h

/-- `◇_y θ` from a left `□R`'s copies, principal in a right `◇_yL`. -/
theorem diaPrinBoxR {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] {y : VarSymb}
    {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)} {θ : WFF σ (Γ.diaIn y) 0} {n' m : ℕ}
    {Δ Θ : List (WFF σ Γ 0)} (hw : (WFF.dia y hy θ).weight = w) (hs : n' + 1 + m = s)
    {Δ₁ : List (WFF σ Γ.boxIn 0)} {φ : WFF σ Γ.boxIn 0} {L₁ : List (WFF σ Γ 0)}
    (h₁ : WFF.box (Γ := Γ) φ ∈ Θ) (h₂ : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ)
    (h₃ : L₁ ⊆ WFF.dia y hy θ :: Θ) (p : GK σ n' Γ.boxIn (Δ₁ ++ cp4 Δ₁) (φ :: kp4 L₁))
    (lp : LeftPrin σ (WFF.dia y hy θ) m Δ Θ) : ∃ k, GK σ k Γ Δ Θ := by
  cases lp with
  | dia _ _ Δ₂ Θ₂ L₂ hm h₂' h₃' h₄' r =>
      have hp : φ :: kp4 L₁ ⊆ (kp4 [WFF.dia y hy θ]).map (Into.self Γ).M ++
          (φ :: kp4 (L₁.filter fun χ => decide (χ ∈ Θ))) := by
        rw [Into.self_M, List.map_id]
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_append_right _ List.mem_cons_self
        · rcases List.mem_append.mp (kp4_split h₃ ha) with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      obtain ⟨k, e⟩ := copyCut ih (Into.self Γ) hw (by omega) r hp p
      have hb : ∀ χ ∈ Δ₁ ++ Δ₂, WFF.box (Γ := Γ) χ ∈ Δ :=
        fun χ hχ => (List.mem_append.mp hχ).elim (h₂ χ) (h₂' χ)
      exact ⟨_, .boxR h₁ hb (dia_hL h₃' h₄') (e.weaken (by lsub4) (by lsub4))⟩

/-- `◇_y θ` from a left `serial`'s copies, principal in a right `◇_yL`. -/
theorem diaPrinSerial {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] {y : VarSymb}
    {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)} {θ : WFF σ (Γ.diaIn y) 0} {n' m : ℕ}
    {Δ Θ : List (WFF σ Γ 0)} (hw : (WFF.dia y hy θ).weight = w) (hs : n' + 1 + m = s)
    (hD : ModalSys.D = true) {Δ₁ : List (WFF σ Γ.boxIn 0)} {L₁ : List (WFF σ Γ 0)}
    (h₂ : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) (h₃ : L₁ ⊆ WFF.dia y hy θ :: Θ)
    (p : GK σ n' Γ.boxIn (Δ₁ ++ cp4 Δ₁) (kp4 L₁)) (lp : LeftPrin σ (WFF.dia y hy θ) m Δ Θ) :
    ∃ k, GK σ k Γ Δ Θ := by
  cases lp with
  | dia _ _ Δ₂ Θ₂ L₂ hm h₂' h₃' h₄' r =>
      have hp : kp4 L₁ ⊆ (kp4 [WFF.dia y hy θ]).map (Into.self Γ).M ++
          kp4 (L₁.filter fun χ => decide (χ ∈ Θ)) := by
        rw [Into.self_M, List.map_id]; exact kp4_split h₃
      obtain ⟨k, e⟩ := copyCut ih (Into.self Γ) hw (by omega) r hp p
      have hb : ∀ χ ∈ Δ₁ ++ Δ₂, WFF.box (Γ := Γ) χ ∈ Δ :=
        fun χ hχ => (List.mem_append.mp hχ).elim (h₂ χ) (h₂' χ)
      exact ⟨_, .serial hD hb (dia_hL h₃' h₄') (e.weaken (by lsub4) (by lsub4))⟩

/-- `◇_y θ` from a left `◇_xL` (its copies, or `x = y` and `θ` among its conclusions), principal
    in a right `◇_yL`: the copy is cut first, then `θ`. -/
theorem diaPrinDiaL {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] {y : VarSymb}
    {hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)} {θ : WFF σ (Γ.diaIn y) 0} {n' m : ℕ}
    {Δ Θ : List (WFF σ Γ 0)} (hw : (WFF.dia y hy θ).weight = w) (hs : n' + 1 + m = s)
    (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {ψ : WFF σ (Γ.diaIn x) 0}
    {Δ₁ : List (WFF σ Γ.boxIn 0)} {Θ₁ : List (WFF σ (Γ.diaIn x) 0)} {L₁ : List (WFF σ Γ 0)}
    (h₁ : WFF.dia x hx ψ ∈ Δ) (h₂ : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ)
    (h₃ : ∀ χ ∈ Θ₁, WFF.dia x hx χ ∈ WFF.dia y hy θ :: Θ) (h₄ : L₁ ⊆ WFF.dia y hy θ :: Θ)
    (p : GK σ n' (Γ.diaIn x) (ψ :: (Δ₁ ++ cp4 Δ₁).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
      (Θ₁ ++ (kp4 L₁).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x))))
    (lp : LeftPrin σ (WFF.dia y hy θ) m Δ Θ) : ∃ k, GK σ k Γ Δ Θ := by
  cases lp with
  | dia _ _ Δ₂ Θ₂ L₂ hm h₂' h₃' h₄' r =>
      have hp : Θ₁ ++ (kp4 L₁).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)) ⊆
          (kp4 [WFF.dia y hy θ]).map (Into.dia Γ x).M ++
            (Θ₁ ++ (kp4 (L₁.filter fun χ => decide (χ ∈ Θ))).map
              (WFF.mono (Ctx.le_boxIn_diaIn Γ x))) := by
        rw [Into.dia_M]
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact List.mem_append_right _ (List.mem_append_left _ h)
        · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
          rcases List.mem_append.mp (kp4_split h₄ hb) with h | h
          · exact List.mem_append_left _ (List.mem_map_of_mem h)
          · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem h))
      obtain ⟨k, p₁⟩ := copyCut ih (Into.dia Γ x) hw (by omega) r hp p
      rw [Into.dia_M] at p₁
      have hb : ∀ χ ∈ Δ₁ ++ Δ₂, WFF.box (Γ := Γ) χ ∈ Δ :=
        fun χ hχ => (List.mem_append.mp hχ).elim (h₂ χ) (h₂' χ)
      by_cases hK : ∀ χ ∈ Θ₁, WFF.dia x hx χ ∈ Θ
      · exact ⟨_, .diaL x hx h₁ hb hK (dia_hL h₃' h₄') (p₁.weaken (by lsub4) (by lsub4))⟩
      -- `x = y` and `θ` is among the left rule's conclusions: cut it too
      push_neg at hK
      obtain ⟨χ₀, hχ₀, hn⟩ := hK
      obtain ⟨rfl, hχ⟩ := WFF.dia.inj ((List.mem_cons.mp (h₃ χ₀ hχ₀)).resolve_right hn)
      cases eq_of_heq hχ
      have hΘ₁ : Θ₁ ⊆ χ₀ :: Θ₁.filter fun χ => decide (WFF.dia x hx χ ∈ Θ) := fun χ hχ => by
        by_cases hd : WFF.dia x hx χ ∈ Θ
        · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hχ, decide_eq_true hd⟩)
        · rw [eq_of_heq (WFF.dia.inj ((List.mem_cons.mp (h₃ χ hχ)).resolve_right hd)).2]
          exact List.mem_cons_self
      have hΘf : ∀ χ ∈ (Θ₁.filter fun χ => decide (WFF.dia x hx χ ∈ Θ)) ++ Θ₂,
          WFF.dia x hx χ ∈ Θ := fun χ hχ =>
        (List.mem_append.mp hχ).elim (fun h => of_decide_eq_true (List.mem_filter.mp h).2)
          (h₃' χ)
      obtain ⟨k₂, e⟩ := ih χ₀ (Γ := Γ.diaIn x)
        (Δ := ψ :: ((Δ₁ ++ Δ₂) ++ cp4 (Δ₁ ++ Δ₂)).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
        (Θ := ((Θ₁.filter fun χ => decide (WFF.dia x hx χ ∈ Θ)) ++ Θ₂) ++
          (kp4 ((L₁.filter fun χ => decide (χ ∈ Θ)) ++ (Θ₂.map (WFF.dia x hx) ++ L₂))).map
            (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
        (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
        (p₁.weaken (by lsub4) (by lsub4 using hΘ₁)) (r.weaken (by lsub4) (by lsub4))
      exact ⟨_, .diaL x hx h₁ hb hΘf (dia_hL h₃' h₄') e⟩

/-- A left `□R`: `□φ` principal, or a `◇` copy, or the cut vanishes. -/
theorem leftBoxR {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] (A : WFF σ Γ 0)
    {n' m : ℕ} {Δ Θ : List (WFF σ Γ 0)} (hw : A.weight = w) (hs : n' + 1 + m = s)
    (D₁ : GK σ (n' + 1) Γ Δ (A :: Θ)) (d₂ : GK σ m Γ (A :: Δ) Θ)
    {Δ₁ : List (WFF σ Γ.boxIn 0)} {φ : WFF σ Γ.boxIn 0} {L₁ : List (WFF σ Γ 0)}
    (h₁ : WFF.box (Γ := Γ) φ ∈ A :: Θ) (h₂ : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ)
    (h₃ : L₁ ⊆ A :: Θ) (p : GK σ n' Γ.boxIn (Δ₁ ++ cp4 Δ₁) (φ :: kp4 L₁)) :
    ∃ k, GK σ k Γ Δ Θ := by
  rcases List.mem_cons.mp h₁ with he | _
  · subst he
    rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
      D₁ d₂ with done | lp
    · exact done
    · exact boxPrin ih hw hs h₂ h₃ p lp
  · rename_i h₁'
    by_cases hk : kp4 [A] = []
    · exact ⟨_, .boxR h₁' h₂ filter_sub
        (p.weaken (fun _ h => h) (List.cons_subset_cons _ (kp4_drop h₃ hk)))⟩
    · obtain ⟨y, hy, θ, rfl⟩ := kp4_single_ne hk
      rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
        D₁ d₂ with done | lp
      · exact done
      · exact diaPrinBoxR ih hw hs h₁' h₂ h₃ p lp

/-- A left `serial`: a `◇` copy, or the cut vanishes. -/
theorem leftSerial {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] (A : WFF σ Γ 0)
    {n' m : ℕ} {Δ Θ : List (WFF σ Γ 0)} (hw : A.weight = w) (hs : n' + 1 + m = s)
    (D₁ : GK σ (n' + 1) Γ Δ (A :: Θ)) (d₂ : GK σ m Γ (A :: Δ) Θ) (hD : ModalSys.D = true)
    {Δ₁ : List (WFF σ Γ.boxIn 0)} {L₁ : List (WFF σ Γ 0)}
    (h₂ : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ) (h₃ : L₁ ⊆ A :: Θ)
    (p : GK σ n' Γ.boxIn (Δ₁ ++ cp4 Δ₁) (kp4 L₁)) : ∃ k, GK σ k Γ Δ Θ := by
  by_cases hk : kp4 [A] = []
  · exact ⟨_, .serial hD h₂ filter_sub (p.weaken (fun _ h => h) (kp4_drop h₃ hk))⟩
  · obtain ⟨y, hy, θ, rfl⟩ := kp4_single_ne hk
    rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
      D₁ d₂ with done | lp
    · exact done
    · exact diaPrinSerial ih hw hs hD h₂ h₃ p lp

/-- A left `◇_xL`: the cut formula among its conclusions or copies, or the cut vanishes. -/
theorem leftDiaL {w s : ℕ} (ih : CutIH σ w s) {Γ : Ctx} [Γ.Presented] (A : WFF σ Γ 0)
    {n' m : ℕ} {Δ Θ : List (WFF σ Γ 0)} (hw : A.weight = w) (hs : n' + 1 + m = s)
    (D₁ : GK σ (n' + 1) Γ Δ (A :: Θ)) (d₂ : GK σ m Γ (A :: Δ) Θ)
    (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {ψ : WFF σ (Γ.diaIn x) 0}
    {Δ₁ : List (WFF σ Γ.boxIn 0)} {Θ₁ : List (WFF σ (Γ.diaIn x) 0)} {L₁ : List (WFF σ Γ 0)}
    (h₁ : WFF.dia x hx ψ ∈ Δ) (h₂ : ∀ χ ∈ Δ₁, WFF.box (Γ := Γ) χ ∈ Δ)
    (h₃ : ∀ χ ∈ Θ₁, WFF.dia x hx χ ∈ A :: Θ) (h₄ : L₁ ⊆ A :: Θ)
    (p : GK σ n' (Γ.diaIn x) (ψ :: (Δ₁ ++ cp4 Δ₁).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))
      (Θ₁ ++ (kp4 L₁).map (WFF.mono (Ctx.le_boxIn_diaIn Γ x)))) :
    ∃ k, GK σ k Γ Δ Θ := by
  have hcase : ((∀ χ ∈ Θ₁, WFF.dia x hx χ ∈ Θ) ∧ kp4 [A] = []) ∨
      ∃ y hy θ, A = WFF.dia y hy θ := by
    by_cases hK : ∀ χ ∈ Θ₁, WFF.dia x hx χ ∈ Θ
    · by_cases hk : kp4 [A] = []
      · exact .inl ⟨hK, hk⟩
      · exact .inr (kp4_single_ne hk)
    · push_neg at hK
      obtain ⟨χ, hχ, hn⟩ := hK
      exact .inr ⟨x, hx, χ, ((List.mem_cons.mp (h₃ χ hχ)).resolve_right hn).symm⟩
  rcases hcase with ⟨hK, hk⟩ | ⟨y, hy, θ, rfl⟩
  · refine ⟨_, .diaL x hx h₁ h₂ hK (filter_sub (L := L₁)) (p.weaken (fun _ h => h) fun a ha => ?_)⟩
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.map_subset _ (kp4_drop h₄ hk) h)
  · rcases permRight ih _ hw hs (fun h => by simp [WFF.IsAtom] at h) (fun h => by cases h)
      D₁ d₂ with done | lp
    · exact done
    · exact diaPrinDiaL ih hw hs x hx h₁ h₂ h₃ h₄ p lp

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
  | boxR h₁ h₂ h₃ p => exact leftBoxR ih A hw hs D₁ d₂ h₁ h₂ h₃ p
  | serial hD h₂ h₃ p => exact leftSerial ih A hw hs D₁ d₂ hD h₂ h₃ p
  | diaL x hx h₁ h₂ h₃ h₄ p => exact leftDiaL ih A hw hs D₁ d₂ x hx h₁ h₂ h₃ h₄ p

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
