import QML.QML_v12_ProofSubst

/-!
# QML v12 — stage systems and their theories of sentences

A **stage system** is a family of presented contexts indexed by a preorder, growing along it.
Formulas move to later stages by weakening, and so do proofs (`Proof.mono`), whatever the growth
is: new variables, or new addresses exposed in a modal view of a growing outer context.

A **sentence** is a formula at some stage.  A set of sentences derives a formula at stage `i`
when finitely many of its members available at `i`, lifted there, prove it (`atStage`); it is
consistent when it is consistent at every stage.  Over a directed index:

* ⭐`StageSys.lindenbaum`: every consistent set of sentences extends to a maximal consistent one;
* maximal consistent sets are closed under derivation, contain `φ` or `¬φ` at each stage, do not
  depend on the stage a sentence is stated at, and satisfy the membership laws of the connectives.
-/

namespace V12

/-- A family of presented contexts growing along a preorder. -/
structure StageSys (I : Type) [Preorder I] where
  ctx : I → Ctx
  le : ∀ {i j : I}, i ≤ j → (ctx i).Le (ctx j)
  pres : ∀ i, (ctx i).Presented

/-- Along a chain, finitely many conditions each met by some member are met by one member. -/
theorem chain_exists_mem_of_list {α β : Type} {c : Set (Set α)} (hc : IsChain (· ⊆ ·) c)
    (hne : c.Nonempty) {P : Set α → β → Prop} (hP : ∀ {s t : Set α}, s ⊆ t → ∀ b, P s b → P t b) :
    ∀ l : List β, (∀ b ∈ l, ∃ s ∈ c, P s b) → ∃ s ∈ c, ∀ b ∈ l, P s b
  | [], _ => by
      obtain ⟨s, hs⟩ := hne
      exact ⟨s, hs, fun _ h => absurd h List.not_mem_nil⟩
  | b :: l, h => by
      obtain ⟨t, ht, hbt⟩ := h b List.mem_cons_self
      obtain ⟨s, hs, hls⟩ := chain_exists_mem_of_list hc hne hP l
        (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
      rcases eq_or_ne s t with rfl | hst
      · refine ⟨s, hs, fun b' hb' => ?_⟩
        rcases List.mem_cons.mp hb' with rfl | h'
        · exact hbt
        · exact hls b' h'
      · rcases hc hs ht hst with hle | hle
        · refine ⟨t, ht, fun b' hb' => ?_⟩
          rcases List.mem_cons.mp hb' with rfl | h'
          · exact hbt
          · exact hP hle b' (hls b' h')
        · refine ⟨s, hs, fun b' hb' => ?_⟩
          rcases List.mem_cons.mp hb' with rfl | h'
          · exact hP hle _ hbt
          · exact hls b' h'

namespace StageSys

variable {I : Type} [Preorder I] (S : StageSys I) {σ : Signature}

instance (i : I) : (S.ctx i).Presented := S.pres i

variable {S}

/-! ## Moving formulas and proofs to later stages -/

/-- A formula moved to a later stage. -/
def lift {i j : I} (h : i ≤ j) (φ : WFF σ (S.ctx i) 0) : WFF σ (S.ctx j) 0 :=
  WFF.mono (S.le h) φ

theorem lift_lift {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) (φ : WFF σ (S.ctx i) 0) :
    lift h₂ (lift h₁ φ) = lift (h₁.trans h₂) φ :=
  WFF.mono_mono _ _ φ

theorem lift_refl {i : I} (h : i ≤ i) (φ : WFF σ (S.ctx i) 0) : lift h φ = φ :=
  WFF.mono_refl _ φ

theorem lift_neg {i j : I} (h : i ≤ j) (φ : WFF σ (S.ctx i) 0) :
    lift h φ.neg = (lift h φ).neg :=
  rfl

/-- ⭐Provability survives moving to a later stage. -/
theorem provable_lift {i j : I} (h : i ≤ j) {Δ : List (WFF σ (S.ctx i) 0)}
    {φ : WFF σ (S.ctx i) 0} (p : Provable Δ φ) : Provable (Δ.map (lift h)) (lift h φ) :=
  Provable.monoCtx (S.le h) p

/-! ## Theories of sentences -/

variable (S σ) in
/-- A sentence: a formula at some stage. -/
abbrev Sentence : Type := Σ i : I, WFF σ (S.ctx i) 0

/-- The members of `T` available at stage `i`, lifted there. -/
def atStage (T : Set (S.Sentence σ)) (i : I) : Set (WFF σ (S.ctx i) 0) :=
  {ψ | ∃ s ∈ T, ∃ h : s.1 ≤ i, lift h s.2 = ψ}

/-- Consistent at every stage. -/
def Consistent (T : Set (S.Sentence σ)) : Prop := ∀ i, Theory.Consistent (atStage T i)

/-- Maximal consistent. -/
def IsMCS (T : Set (S.Sentence σ)) : Prop :=
  Consistent T ∧ ∀ s, Consistent (insert s T) → s ∈ T

variable {T T' : Set (S.Sentence σ)}

theorem atStage_mono (h : T ⊆ T') (i : I) : atStage T i ⊆ atStage T' i :=
  fun _ ⟨s, hs, hsi, e⟩ => ⟨s, h hs, hsi, e⟩

theorem mem_atStage {i j : I} {φ : WFF σ (S.ctx i) 0} (hφ : ⟨i, φ⟩ ∈ T) (h : i ≤ j) :
    lift h φ ∈ atStage T j :=
  ⟨⟨i, φ⟩, hφ, h, rfl⟩

theorem mem_atStage_self {i : I} {φ : WFF σ (S.ctx i) 0} (h : ⟨i, φ⟩ ∈ T) :
    φ ∈ atStage T i :=
  ⟨⟨i, φ⟩, h, le_rfl, lift_refl _ _⟩

theorem atStage_lift {i j : I} {ψ : WFF σ (S.ctx i) 0} (hψ : ψ ∈ atStage T i) (h : i ≤ j) :
    lift h ψ ∈ atStage T j := by
  obtain ⟨s, hs, hsi, rfl⟩ := hψ
  exact ⟨s, hs, hsi.trans h, (lift_lift hsi h s.2).symm⟩

theorem derives_lift {i j : I} {φ : WFF σ (S.ctx i) 0} (hd : Theory.Derives (atStage T i) φ)
    (h : i ≤ j) : Theory.Derives (atStage T j) (lift h φ) := by
  obtain ⟨Δ, hΔ, p⟩ := hd
  refine ⟨Δ.map (lift h), fun ψ hψ => ?_, provable_lift h p⟩
  obtain ⟨ψ₀, hψ₀, rfl⟩ := List.mem_map.mp hψ
  exact atStage_lift (hΔ ψ₀ hψ₀) h

/-- Consistency at a stage gives consistency at every earlier stage. -/
theorem consistent_of_le {i j : I} (hc : Theory.Consistent (atStage T j)) (h : i ≤ j) :
    Theory.Consistent (atStage T i) :=
  fun hd => hc (derives_lift hd h)

theorem atStage_insert_le {s : S.Sentence σ} {i : I} (h : s.1 ≤ i) :
    atStage (insert s T) i ⊆ insert (lift h s.2) (atStage T i) := by
  rintro ψ ⟨s', hs', h', rfl⟩
  rcases Set.mem_insert_iff.mp hs' with rfl | hs'
  · exact Or.inl rfl
  · exact Or.inr ⟨s', hs', h', rfl⟩

theorem atStage_insert_not_le {s : S.Sentence σ} {i : I} (h : ¬ s.1 ≤ i) :
    atStage (insert s T) i ⊆ atStage T i := by
  rintro ψ ⟨s', hs', h', rfl⟩
  rcases Set.mem_insert_iff.mp hs' with rfl | hs'
  · exact absurd h' h
  · exact ⟨s', hs', h', rfl⟩

theorem consistent_sUnion {c : Set (Set (S.Sentence σ))} (hc : IsChain (· ⊆ ·) c)
    (hne : c.Nonempty) (hcons : ∀ t ∈ c, Consistent t) : Consistent (⋃₀ c) := by
  rintro i ⟨Δ, hΔ, p⟩
  obtain ⟨t, ht, hsub⟩ := chain_exists_mem_of_list hc hne
    (P := fun t ψ => ψ ∈ atStage t i) (fun hle ψ hψ => atStage_mono hle i hψ) Δ
    (fun ψ hψ => by
      obtain ⟨s, hs, hsi, e⟩ := hΔ ψ hψ
      obtain ⟨t, ht, hst⟩ := Set.mem_sUnion.mp hs
      exact ⟨t, ht, s, hst, hsi, e⟩)
  exact hcons t ht i ⟨Δ, hsub, p⟩

/-- ⭐**Lindenbaum** for sentences. -/
theorem lindenbaum (hT : Consistent T) : ∃ M, T ⊆ M ∧ IsMCS M := by
  obtain ⟨M, hTM, hmax⟩ := zorn_subset_nonempty {U | T ⊆ U ∧ Consistent U}
    (fun c hcU hchain hne => by
      refine ⟨⋃₀ c, ⟨?_, consistent_sUnion hchain hne (fun s hs => (hcU hs).2)⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩
      obtain ⟨s, hs⟩ := hne
      exact (hcU hs).1.trans (Set.subset_sUnion_of_mem hs))
    T ⟨subset_rfl, hT⟩
  refine ⟨M, hTM, hmax.prop.2, fun s hs => ?_⟩
  exact hmax.2 ⟨hTM.trans (Set.subset_insert _ _), hs⟩ (Set.subset_insert _ _) (Set.mem_insert _ _)

/-! ## Maximal consistent sets -/

theorem derives_of_mems {i : I} {Δ : List (WFF σ (S.ctx i) 0)} {φ : WFF σ (S.ctx i) 0}
    (hs : ∀ ψ ∈ Δ, (⟨i, ψ⟩ : S.Sentence σ) ∈ T) (p : Provable Δ φ) :
    Theory.Derives (atStage T i) φ :=
  ⟨Δ, fun ψ hψ => mem_atStage_self (hs ψ hψ), p⟩

namespace IsMCS

variable (hT : IsMCS T)
include hT

/-- Closed under derivation. -/
theorem closed {i : I} {φ : WFF σ (S.ctx i) 0} (hd : Theory.Derives (atStage T i) φ) :
    (⟨i, φ⟩ : S.Sentence σ) ∈ T := by
  apply hT.2
  intro j
  by_cases hij : i ≤ j
  · refine Theory.Consistent.mono (atStage_insert_le (s := ⟨i, φ⟩) hij) ?_
    intro hbot
    exact hT.1 j ((Theory.Derives.deduction hbot).mp (derives_lift hd hij))
  · exact (hT.1 j).mono (atStage_insert_not_le hij)

theorem bot_not_mem {i : I} : (⟨i, .bot⟩ : S.Sentence σ) ∉ T :=
  fun h => hT.1 i (Theory.Derives.of_mem (mem_atStage_self h))

theorem top_mem {i : I} : (⟨i, .top⟩ : S.Sentence σ) ∈ T :=
  hT.closed ⟨[], fun _ h => absurd h List.not_mem_nil, Provable.top⟩

theorem mem_or_neg_mem [IsDirected I (· ≤ ·)] {i : I} (φ : WFF σ (S.ctx i) 0) :
    (⟨i, φ⟩ : S.Sentence σ) ∈ T ∨ (⟨i, φ.neg⟩ : S.Sentence σ) ∈ T := by
  by_contra h
  rw [not_or] at h
  have h₁ : ¬ Consistent (insert ⟨i, φ⟩ T) := fun hc => h.1 (hT.2 _ hc)
  have h₂ : ¬ Consistent (insert ⟨i, φ.neg⟩ T) := fun hc => h.2 (hT.2 _ hc)
  simp only [Consistent, not_forall] at h₁ h₂
  obtain ⟨j₁, hj₁⟩ := h₁
  obtain ⟨j₂, hj₂⟩ := h₂
  have e₁ : i ≤ j₁ := by
    by_contra hn
    exact hj₁ ((hT.1 j₁).mono (atStage_insert_not_le hn))
  have e₂ : i ≤ j₂ := by
    by_contra hn
    exact hj₂ ((hT.1 j₂).mono (atStage_insert_not_le hn))
  have d₁ : Theory.Derives (atStage T j₁) (lift e₁ φ).neg :=
    Theory.derives_neg_of_not_consistent fun hc => hj₁ (hc.mono (atStage_insert_le e₁))
  have d₂ : Theory.Derives (atStage T j₂) (lift e₂ φ.neg).neg :=
    Theory.derives_neg_of_not_consistent fun hc => hj₂ (hc.mono (atStage_insert_le e₂))
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) j₁ j₂
  have D₁ := derives_lift d₁ hk₁
  have D₂ := derives_lift d₂ hk₂
  simp only [lift_neg, lift_lift] at D₁ D₂
  exact hT.1 _ (D₂.mp D₁)

theorem neg_mem_iff [IsDirected I (· ≤ ·)] {i : I} {φ : WFF σ (S.ctx i) 0} :
    (⟨i, φ.neg⟩ : S.Sentence σ) ∈ T ↔ (⟨i, φ⟩ : S.Sentence σ) ∉ T :=
  ⟨fun hn h => hT.1 i ((Theory.Derives.of_mem (mem_atStage_self hn)).mp
      (Theory.Derives.of_mem (mem_atStage_self h))),
    fun h => (hT.mem_or_neg_mem φ).resolve_left h⟩

/-- Membership does not depend on the stage a sentence is stated at. -/
theorem mem_lift_iff [IsDirected I (· ≤ ·)] {i j : I} (h : i ≤ j) {φ : WFF σ (S.ctx i) 0} :
    (⟨j, lift h φ⟩ : S.Sentence σ) ∈ T ↔ (⟨i, φ⟩ : S.Sentence σ) ∈ T := by
  have up : ∀ {χ : WFF σ (S.ctx i) 0}, (⟨i, χ⟩ : S.Sentence σ) ∈ T →
      (⟨j, lift h χ⟩ : S.Sentence σ) ∈ T :=
    fun hχ => hT.closed (Theory.Derives.of_mem (mem_atStage hχ h))
  refine ⟨fun hj => ?_, up⟩
  by_contra hi
  exact (hT.neg_mem_iff.mp (up (hT.neg_mem_iff.mpr hi))) hj

theorem imp_mem_iff [IsDirected I (· ≤ ·)] {i : I} {φ ψ : WFF σ (S.ctx i) 0} :
    (⟨i, φ.imp ψ⟩ : S.Sentence σ) ∈ T ↔
      ((⟨i, φ⟩ : S.Sentence σ) ∈ T → (⟨i, ψ⟩ : S.Sentence σ) ∈ T) := by
  constructor
  · intro h hφ
    exact hT.closed ((Theory.Derives.of_mem (mem_atStage_self h)).mp
      (Theory.Derives.of_mem (mem_atStage_self hφ)))
  · intro h
    by_cases hφ : (⟨i, φ⟩ : S.Sentence σ) ∈ T
    · exact hT.closed (derives_of_mems (Δ := [ψ])
        (fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact h hφ)
        (Provable.imp_intro (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))))
    · exact hT.closed (derives_of_mems (Δ := [φ.neg])
        (fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact hT.neg_mem_iff.mpr hφ)
        (Provable.imp_intro (Provable.bot_elim (Provable.mp
          (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
          (Provable.of_mem List.mem_cons_self)))))

theorem and_mem_iff {i : I} {φ ψ : WFF σ (S.ctx i) 0} :
    (⟨i, φ.and ψ⟩ : S.Sentence σ) ∈ T ↔
      (⟨i, φ⟩ : S.Sentence σ) ∈ T ∧ (⟨i, ψ⟩ : S.Sentence σ) ∈ T := by
  constructor
  · intro h
    obtain ⟨Δ, hΔ, p⟩ := Theory.Derives.of_mem (mem_atStage_self h)
    exact ⟨hT.closed ⟨Δ, hΔ, Provable.and_elim_l p⟩, hT.closed ⟨Δ, hΔ, Provable.and_elim_r p⟩⟩
  · rintro ⟨hφ, hψ⟩
    exact hT.closed (derives_of_mems (Δ := [φ, ψ])
      (fun θ hθ => by
        rcases List.mem_cons.mp hθ with rfl | hθ
        · exact hφ
        · rw [List.mem_singleton.mp hθ]; exact hψ)
      (Provable.and_intro (Provable.of_mem List.mem_cons_self)
        (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem or_mem_iff [IsDirected I (· ≤ ·)] {i : I} {φ ψ : WFF σ (S.ctx i) 0} :
    (⟨i, φ.or ψ⟩ : S.Sentence σ) ∈ T ↔
      (⟨i, φ⟩ : S.Sentence σ) ∈ T ∨ (⟨i, ψ⟩ : S.Sentence σ) ∈ T := by
  constructor
  · intro h
    by_cases hφ : (⟨i, φ⟩ : S.Sentence σ) ∈ T
    · exact Or.inl hφ
    · refine Or.inr (hT.closed (derives_of_mems (Δ := [φ.or ψ, φ.neg]) (fun θ hθ => ?_) ?_))
      · rcases List.mem_cons.mp hθ with rfl | hθ
        · exact h
        · rw [List.mem_singleton.mp hθ]; exact hT.neg_mem_iff.mpr hφ
      · exact Provable.or_elim (Provable.of_mem List.mem_cons_self)
          (Provable.bot_elim (Provable.mp
            (Provable.of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
            (Provable.of_mem List.mem_cons_self)))
          (Provable.of_mem List.mem_cons_self)
  · rintro (hφ | hψ)
    · exact hT.closed (derives_of_mems (Δ := [φ])
        (fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact hφ)
        (Provable.or_intro_l (Provable.of_mem List.mem_cons_self)))
    · exact hT.closed (derives_of_mems (Δ := [ψ])
        (fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact hψ)
        (Provable.or_intro_r (Provable.of_mem List.mem_cons_self)))

end IsMCS

end StageSys

end V12
