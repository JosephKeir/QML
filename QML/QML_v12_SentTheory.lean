import QML.QML_v12_Stages

/-!
# QML v12 — theories of sentences over a staged language

A **sentence** is a formula at some stage.  A set of sentences derives a formula at stage `m`
when finitely many of its members, lifted to stage `m`, prove it (`atStage`); it is consistent
when it is consistent at every stage.

* ⭐`Lang.lindenbaum`: every consistent set of sentences extends to a maximal consistent one;
* maximal consistent sets are closed under derivation, contain `φ` or `¬φ` at each stage, are
  invariant under lifting, and satisfy the membership laws of the connectives.
-/

namespace V12

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

namespace Lang

variable {L : Lang} {σ : Signature}

/-- A sentence: a formula at some stage. -/
abbrev Sentence (L : Lang) (σ : Signature) : Type := Σ k : ℕ, WFF σ (L.ctx k) 0

/-- The members of `T` available at stage `m`, lifted there. -/
def atStage (T : Set (L.Sentence σ)) (m : ℕ) : Set (WFF σ (L.ctx m) 0) :=
  {ψ | ∃ s ∈ T, ∃ h : s.1 ≤ m, lift h s.2 = ψ}

/-- Consistent at every stage. -/
def Consistent (T : Set (L.Sentence σ)) : Prop := ∀ m, Theory.Consistent (atStage T m)

/-- Maximal consistent. -/
def IsMCS (T : Set (L.Sentence σ)) : Prop := Consistent T ∧ ∀ s, Consistent (insert s T) → s ∈ T

variable {T T' : Set (L.Sentence σ)}

theorem atStage_mono (h : T ⊆ T') (m : ℕ) : atStage T m ⊆ atStage T' m :=
  fun _ ⟨s, hs, hsm, e⟩ => ⟨s, h hs, hsm, e⟩

theorem mem_atStage {k m : ℕ} {φ : WFF σ (L.ctx k) 0} (hφ : ⟨k, φ⟩ ∈ T) (h : k ≤ m) :
    lift h φ ∈ atStage T m :=
  ⟨⟨k, φ⟩, hφ, h, rfl⟩

theorem atStage_lift {k m : ℕ} {ψ : WFF σ (L.ctx k) 0} (hψ : ψ ∈ atStage T k) (h : k ≤ m) :
    lift h ψ ∈ atStage T m := by
  obtain ⟨s, hs, hsk, rfl⟩ := hψ
  exact ⟨s, hs, hsk.trans h, (lift_lift hsk h s.2).symm⟩

theorem derives_lift {k m : ℕ} {φ : WFF σ (L.ctx k) 0} (hd : Theory.Derives (atStage T k) φ)
    (h : k ≤ m) : Theory.Derives (atStage T m) (lift h φ) := by
  obtain ⟨Δ, hΔ, p⟩ := hd
  refine ⟨Δ.map (lift h), fun ψ hψ => ?_, Provable.lift h p⟩
  obtain ⟨ψ₀, hψ₀, rfl⟩ := List.mem_map.mp hψ
  exact atStage_lift (hΔ ψ₀ hψ₀) h

theorem consistent_of_le {k m : ℕ} (hc : Theory.Consistent (atStage T m)) (h : k ≤ m) :
    Theory.Consistent (atStage T k) :=
  fun hd => hc (derives_lift hd h)

theorem atStage_insert_le {s : L.Sentence σ} {m : ℕ} (h : s.1 ≤ m) :
    atStage (insert s T) m ⊆ insert (lift h s.2) (atStage T m) := by
  rintro ψ ⟨s', hs', h', rfl⟩
  rcases Set.mem_insert_iff.mp hs' with rfl | hs'
  · exact Or.inl rfl
  · exact Or.inr ⟨s', hs', h', rfl⟩

theorem atStage_insert_lt {s : L.Sentence σ} {m : ℕ} (h : ¬ s.1 ≤ m) :
    atStage (insert s T) m ⊆ atStage T m := by
  rintro ψ ⟨s', hs', h', rfl⟩
  rcases Set.mem_insert_iff.mp hs' with rfl | hs'
  · exact absurd h' h
  · exact ⟨s', hs', h', rfl⟩

theorem consistent_sUnion {c : Set (Set (L.Sentence σ))} (hc : IsChain (· ⊆ ·) c)
    (hne : c.Nonempty) (hcons : ∀ t ∈ c, Consistent t) : Consistent (⋃₀ c) := by
  rintro m ⟨Δ, hΔ, p⟩
  obtain ⟨t, ht, hsub⟩ := chain_exists_mem_of_list hc hne
    (P := fun t ψ => ψ ∈ atStage t m) (fun hle ψ hψ => atStage_mono hle m hψ) Δ
    (fun ψ hψ => by
      obtain ⟨s, hs, hsm, e⟩ := hΔ ψ hψ
      obtain ⟨t, ht, hst⟩ := Set.mem_sUnion.mp hs
      exact ⟨t, ht, s, hst, hsm, e⟩)
  exact hcons t ht m ⟨Δ, hsub, p⟩

/-- ⭐**Lindenbaum** for sentences. -/
theorem lindenbaum (hT : Consistent T) : ∃ M, T ⊆ M ∧ IsMCS M := by
  obtain ⟨M, hTM, hmax⟩ := zorn_subset_nonempty {S | T ⊆ S ∧ Consistent S}
    (fun c hcS hchain hne => by
      refine ⟨⋃₀ c, ⟨?_, consistent_sUnion hchain hne (fun s hs => (hcS hs).2)⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩
      obtain ⟨s, hs⟩ := hne
      exact (hcS hs).1.trans (Set.subset_sUnion_of_mem hs))
    T ⟨subset_rfl, hT⟩
  refine ⟨M, hTM, hmax.prop.2, fun s hs => ?_⟩
  exact hmax.2 ⟨hTM.trans (Set.subset_insert _ _), hs⟩ (Set.subset_insert _ _) (Set.mem_insert _ _)

/-! ## Maximal consistent sets of sentences -/

theorem mem_atStage_self {k : ℕ} {φ : WFF σ (L.ctx k) 0} (h : ⟨k, φ⟩ ∈ T) : φ ∈ atStage T k :=
  ⟨⟨k, φ⟩, h, le_rfl, lift_refl _ _⟩

namespace IsMCS

variable (hT : IsMCS T)
include hT

omit hT in
theorem derives_of_mems {m : ℕ} {Δ : List (WFF σ (L.ctx m) 0)} {φ : WFF σ (L.ctx m) 0}
    (hs : ∀ ψ ∈ Δ, (⟨m, ψ⟩ : L.Sentence σ) ∈ T) (p : Provable Δ φ) :
    Theory.Derives (atStage T m) φ :=
  ⟨Δ, fun ψ hψ => mem_atStage_self (hs ψ hψ), p⟩

/-- Closed under derivation. -/
theorem closed {m : ℕ} {φ : WFF σ (L.ctx m) 0} (hd : Theory.Derives (atStage T m) φ) :
    (⟨m, φ⟩ : L.Sentence σ) ∈ T := by
  apply hT.2
  intro m'
  by_cases hm : m ≤ m'
  · refine Theory.Consistent.mono (atStage_insert_le (s := ⟨m, φ⟩) hm) ?_
    intro hbot
    exact hT.1 m' ((Theory.Derives.deduction hbot).mp (derives_lift hd hm))
  · exact (hT.1 m').mono (atStage_insert_lt hm)

theorem bot_not_mem {m : ℕ} : (⟨m, .bot⟩ : L.Sentence σ) ∉ T :=
  fun h => hT.1 m (Theory.Derives.of_mem (mem_atStage_self h))

theorem top_mem {m : ℕ} : (⟨m, .top⟩ : L.Sentence σ) ∈ T :=
  hT.closed ⟨[], fun _ h => absurd h List.not_mem_nil, Provable.top⟩

theorem mem_or_neg_mem {m : ℕ} (φ : WFF σ (L.ctx m) 0) :
    (⟨m, φ⟩ : L.Sentence σ) ∈ T ∨ (⟨m, φ.neg⟩ : L.Sentence σ) ∈ T := by
  by_contra h
  rw [not_or] at h
  have h₁ : ¬ Consistent (insert ⟨m, φ⟩ T) := fun hc => h.1 (hT.2 _ hc)
  have h₂ : ¬ Consistent (insert ⟨m, φ.neg⟩ T) := fun hc => h.2 (hT.2 _ hc)
  simp only [Consistent, not_forall] at h₁ h₂
  obtain ⟨m₁, hm₁⟩ := h₁
  obtain ⟨m₂, hm₂⟩ := h₂
  have e₁ : m ≤ m₁ := by
    by_contra hlt
    exact hm₁ ((hT.1 m₁).mono (atStage_insert_lt hlt))
  have e₂ : m ≤ m₂ := by
    by_contra hlt
    exact hm₂ ((hT.1 m₂).mono (atStage_insert_lt hlt))
  have d₁ : Theory.Derives (atStage T m₁) (lift e₁ φ).neg :=
    Theory.derives_neg_of_not_consistent fun hc => hm₁ (hc.mono (atStage_insert_le e₁))
  have d₂ : Theory.Derives (atStage T m₂) (lift e₂ φ.neg).neg :=
    Theory.derives_neg_of_not_consistent fun hc => hm₂ (hc.mono (atStage_insert_le e₂))
  have D₁ := derives_lift d₁ (le_max_left m₁ m₂)
  have D₂ := derives_lift d₂ (le_max_right m₁ m₂)
  simp only [lift_neg, lift_lift] at D₁ D₂
  exact hT.1 _ (D₂.mp D₁)

theorem neg_mem_iff {m : ℕ} {φ : WFF σ (L.ctx m) 0} :
    (⟨m, φ.neg⟩ : L.Sentence σ) ∈ T ↔ (⟨m, φ⟩ : L.Sentence σ) ∉ T :=
  ⟨fun hn h => hT.1 m ((Theory.Derives.of_mem (mem_atStage_self hn)).mp (Theory.Derives.of_mem (mem_atStage_self h))),
    fun h => (hT.mem_or_neg_mem φ).resolve_left h⟩

/-- Membership does not depend on the stage a sentence is stated at. -/
theorem mem_lift_iff {k m : ℕ} (h : k ≤ m) {φ : WFF σ (L.ctx k) 0} :
    (⟨m, lift h φ⟩ : L.Sentence σ) ∈ T ↔ (⟨k, φ⟩ : L.Sentence σ) ∈ T := by
  have up : ∀ {χ : WFF σ (L.ctx k) 0}, (⟨k, χ⟩ : L.Sentence σ) ∈ T →
      (⟨m, lift h χ⟩ : L.Sentence σ) ∈ T :=
    fun hχ => hT.closed (Theory.Derives.of_mem (mem_atStage hχ h))
  refine ⟨fun hm => ?_, up⟩
  by_contra hk
  exact (hT.neg_mem_iff.mp (up ((hT.neg_mem_iff).mpr hk))) hm

theorem imp_mem_iff {m : ℕ} {φ ψ : WFF σ (L.ctx m) 0} :
    (⟨m, φ.imp ψ⟩ : L.Sentence σ) ∈ T ↔
      ((⟨m, φ⟩ : L.Sentence σ) ∈ T → (⟨m, ψ⟩ : L.Sentence σ) ∈ T) := by
  constructor
  · intro h hφ
    exact hT.closed ((Theory.Derives.of_mem (mem_atStage_self h)).mp (Theory.Derives.of_mem (mem_atStage_self hφ)))
  · intro h
    by_cases hφ : (⟨m, φ⟩ : L.Sentence σ) ∈ T
    · exact hT.closed (derives_of_mems (Δ := [ψ])
        (fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact h hφ)
        (Provable.imp_intro (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))))
    · exact hT.closed (derives_of_mems (Δ := [φ.neg])
        (fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact hT.neg_mem_iff.mpr hφ)
        (Provable.imp_intro (Provable.bot_elim (Provable.mp
          (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
          (Provable.of_mem List.mem_cons_self)))))

theorem and_mem_iff {m : ℕ} {φ ψ : WFF σ (L.ctx m) 0} :
    (⟨m, φ.and ψ⟩ : L.Sentence σ) ∈ T ↔
      (⟨m, φ⟩ : L.Sentence σ) ∈ T ∧ (⟨m, ψ⟩ : L.Sentence σ) ∈ T := by
  constructor
  · intro h
    have hd := Theory.Derives.of_mem (mem_atStage_self h)
    obtain ⟨Δ, hΔ, p⟩ := hd
    exact ⟨hT.closed ⟨Δ, hΔ, Provable.and_elim_l p⟩, hT.closed ⟨Δ, hΔ, Provable.and_elim_r p⟩⟩
  · rintro ⟨hφ, hψ⟩
    exact hT.closed (derives_of_mems (Δ := [φ, ψ])
      (fun θ hθ => by
        rcases List.mem_cons.mp hθ with rfl | hθ
        · exact hφ
        · rw [List.mem_singleton.mp hθ]; exact hψ)
      (Provable.and_intro (Provable.of_mem List.mem_cons_self)
        (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem or_mem_iff {m : ℕ} {φ ψ : WFF σ (L.ctx m) 0} :
    (⟨m, φ.or ψ⟩ : L.Sentence σ) ∈ T ↔
      (⟨m, φ⟩ : L.Sentence σ) ∈ T ∨ (⟨m, ψ⟩ : L.Sentence σ) ∈ T := by
  constructor
  · intro h
    by_cases hφ : (⟨m, φ⟩ : L.Sentence σ) ∈ T
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

end Lang

end V12
