import QML.QML_v12m_Eq
import Mathlib.Order.Zorn

/-!
# QML v12m — theories over a context

The finitary proof theory completeness is built from, over a fixed context:

* `Provable Δ φ` — provability as a proposition, with the rules as lemmas;
* `Theory.Derives S φ` — finitely many members of `S` prove `φ`; `Theory.Consistent`,
  `Theory.IsMCS`;
* ⭐`Theory.lindenbaum` — every consistent theory extends to a maximal consistent one (Zorn);
* the membership laws of maximal consistent theories for the connectives.
-/

namespace V12M

variable [ModalSys]

/-- Provability, as a proposition. -/
def Provable {σ : Signature} {Γ : Ctx} (Δ : List (WFF σ Γ 0)) (φ : WFF σ Γ 0) : Prop :=
  Nonempty (Proof σ Γ Δ φ)

namespace Provable

variable {σ : Signature} {Γ : Ctx} {Δ Δ' : List (WFF σ Γ 0)} {φ ψ χ : WFF σ Γ 0}

theorem mono (h : ∀ θ ∈ Δ, θ ∈ Δ') (p : Provable Δ φ) : Provable Δ' φ :=
  p.map (Proof.ofSubset h)

theorem of_mem (h : φ ∈ Δ) : Provable Δ φ := ⟨Proof.lookup h⟩

theorem mp (p : Provable Δ (φ.imp ψ)) (q : Provable Δ φ) : Provable Δ ψ :=
  p.elim fun p => q.elim fun q => ⟨.imp_elim p q⟩

theorem imp_intro (p : Provable (φ :: Δ) ψ) : Provable Δ (φ.imp ψ) := p.map .imp_intro

theorem cut (p : Provable Δ φ) (q : Provable (φ :: Δ) ψ) : Provable Δ ψ := mp (imp_intro q) p

theorem bot_elim (p : Provable Δ .bot) : Provable Δ φ := p.map (.bot_elim φ)

theorem top : Provable Δ (.top : WFF σ Γ 0) := ⟨.top_intro⟩

theorem and_intro (p : Provable Δ φ) (q : Provable Δ ψ) : Provable Δ (φ.and ψ) :=
  p.elim fun p => q.elim fun q => ⟨.and_intro p q⟩

theorem and_elim_l (p : Provable Δ (φ.and ψ)) : Provable Δ φ := p.map .and_elim_l

theorem and_elim_r (p : Provable Δ (φ.and ψ)) : Provable Δ ψ := p.map .and_elim_r

theorem or_intro_l (p : Provable Δ φ) : Provable Δ (φ.or ψ) := p.map (.or_intro_l ψ)

theorem or_intro_r (p : Provable Δ ψ) : Provable Δ (φ.or ψ) := p.map (.or_intro_r φ)

theorem or_elim (p : Provable Δ (φ.or ψ)) (q : Provable (φ :: Δ) χ) (r : Provable (ψ :: Δ) χ) :
    Provable Δ χ :=
  p.elim fun p => q.elim fun q => r.elim fun r => ⟨.or_elim p q r⟩

theorem lem (φ : WFF σ Γ 0) : Provable Δ (φ.or φ.neg) := ⟨.lem φ⟩

theorem byContra (p : Provable (φ.neg :: Δ) .bot) : Provable Δ φ :=
  or_elim (lem φ) (of_mem List.mem_cons_self) (bot_elim p)

end Provable

namespace Theory

variable {σ : Signature} {Γ : Ctx}

/-- Finitely many members of `S` prove `φ`. -/
def Derives (S : Set (WFF σ Γ 0)) (φ : WFF σ Γ 0) : Prop :=
  ∃ Δ : List (WFF σ Γ 0), (∀ ψ ∈ Δ, ψ ∈ S) ∧ Provable Δ φ

def Consistent (S : Set (WFF σ Γ 0)) : Prop := ¬ Derives S .bot

/-- Maximal consistent. -/
def IsMCS (S : Set (WFF σ Γ 0)) : Prop := Consistent S ∧ ∀ φ, Consistent (insert φ S) → φ ∈ S

variable {S S' : Set (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0}

theorem Derives.mono (h : S ⊆ S') : Derives S φ → Derives S' φ
  | ⟨Δ, hΔ, p⟩ => ⟨Δ, fun θ hθ => h (hΔ θ hθ), p⟩

theorem Derives.of_mem (h : φ ∈ S) : Derives S φ :=
  ⟨[φ], fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact h, Provable.of_mem List.mem_cons_self⟩

theorem Derives.mp : Derives S (φ.imp ψ) → Derives S φ → Derives S ψ
  | ⟨Δ₁, h₁, p₁⟩, ⟨Δ₂, h₂, p₂⟩ =>
      ⟨Δ₁ ++ Δ₂, fun θ hθ => (List.mem_append.mp hθ).elim (h₁ θ) (h₂ θ),
        Provable.mp (p₁.mono fun _ h => List.mem_append_left _ h)
          (p₂.mono fun _ h => List.mem_append_right _ h)⟩

/-- The deduction theorem. -/
theorem Derives.deduction : Derives (insert φ S) ψ → Derives S (φ.imp ψ)
  | ⟨Δ, hΔ, p⟩ =>
      ⟨Δ.filter (fun θ => θ ≠ φ),
        fun θ hθ => by
          have hθ' := List.mem_filter.mp hθ
          have hne : θ ≠ φ := by simpa using hθ'.2
          rcases hΔ θ hθ'.1 with h | h
          · exact absurd h hne
          · exact h,
        Provable.imp_intro (p.mono fun θ hθ => by
          by_cases h : θ = φ
          · subst h
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hθ, by simpa using h⟩))⟩

theorem Consistent.mono (h : S ⊆ S') (hc : Consistent S') : Consistent S :=
  fun hd => hc (hd.mono h)

theorem derives_neg_of_not_consistent (h : ¬ Consistent (insert φ S)) : Derives S φ.neg :=
  Derives.deduction (not_not.mp h)

/-- The Lindenbaum branching step. -/
theorem Consistent.insert_or (hc : Consistent S) (φ : WFF σ Γ 0) :
    Consistent (insert φ S) ∨ Consistent (insert φ.neg S) := by
  by_contra h
  rw [not_or] at h
  exact hc ((derives_neg_of_not_consistent h.2).mp (derives_neg_of_not_consistent h.1))

theorem exists_mem_chain_of_list {c : Set (Set (WFF σ Γ 0))} (hc : IsChain (· ⊆ ·) c)
    (hne : c.Nonempty) :
    ∀ Δ : List (WFF σ Γ 0), (∀ ψ ∈ Δ, ψ ∈ ⋃₀ c) → ∃ s ∈ c, ∀ ψ ∈ Δ, ψ ∈ s
  | [], _ => by
      obtain ⟨s, hs⟩ := hne
      exact ⟨s, hs, fun _ h => absurd h List.not_mem_nil⟩
  | ψ :: Δ, h => by
      obtain ⟨t, ht, hψt⟩ := Set.mem_sUnion.mp (h ψ List.mem_cons_self)
      obtain ⟨s, hs, hΔs⟩ :=
        exists_mem_chain_of_list hc hne Δ (fun θ hθ => h θ (List.mem_cons_of_mem _ hθ))
      rcases eq_or_ne s t with rfl | hst
      · exact ⟨s, hs, fun θ hθ => (List.mem_cons.mp hθ).elim (fun e => e ▸ hψt) (hΔs θ)⟩
      · rcases hc hs ht hst with hle | hle
        · exact ⟨t, ht, fun θ hθ => (List.mem_cons.mp hθ).elim (fun e => e ▸ hψt)
            (fun h' => hle (hΔs θ h'))⟩
        · exact ⟨s, hs, fun θ hθ => (List.mem_cons.mp hθ).elim (fun e => e ▸ hle hψt) (hΔs θ)⟩

theorem consistent_sUnion {c : Set (Set (WFF σ Γ 0))} (hc : IsChain (· ⊆ ·) c)
    (hne : c.Nonempty) (hcons : ∀ s ∈ c, Consistent s) : Consistent (⋃₀ c) := by
  rintro ⟨Δ, hΔ, p⟩
  obtain ⟨s, hs, hsub⟩ := exists_mem_chain_of_list hc hne Δ hΔ
  exact hcons s hs ⟨Δ, hsub, p⟩

/-- ⭐**Lindenbaum**: every consistent theory has a maximal consistent extension. -/
theorem lindenbaum (hS : Consistent S) : ∃ M, S ⊆ M ∧ IsMCS M := by
  obtain ⟨M, hSM, hmax⟩ := zorn_subset_nonempty {T | S ⊆ T ∧ Consistent T}
    (fun c hcS hchain hne => by
      refine ⟨⋃₀ c, ⟨?_, consistent_sUnion hchain hne (fun s hs => (hcS hs).2)⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩
      obtain ⟨s, hs⟩ := hne
      exact (hcS hs).1.trans (Set.subset_sUnion_of_mem hs))
    S ⟨subset_rfl, hS⟩
  refine ⟨M, hSM, hmax.prop.2, fun φ hφ => ?_⟩
  exact hmax.2 ⟨hSM.trans (Set.subset_insert _ _), hφ⟩ (Set.subset_insert _ _) (Set.mem_insert _ _)

/-! ## Maximal consistent theories -/

namespace IsMCS

variable (hM : IsMCS S)
include hM

theorem closed (hd : Derives S φ) : φ ∈ S := by
  by_contra hφ
  exact hM.1 ((derives_neg_of_not_consistent fun hc => hφ (hM.2 φ hc)).mp hd)

theorem bot_not_mem : (.bot : WFF σ Γ 0) ∉ S := fun h => hM.1 (Derives.of_mem h)

theorem top_mem : (.top : WFF σ Γ 0) ∈ S := hM.closed ⟨[], fun _ h => absurd h List.not_mem_nil,
  Provable.top⟩

theorem mem_or_neg_mem (φ : WFF σ Γ 0) : φ ∈ S ∨ φ.neg ∈ S :=
  (hM.1.insert_or φ).imp (hM.2 φ) (hM.2 _)

theorem neg_mem_iff : φ.neg ∈ S ↔ φ ∉ S :=
  ⟨fun hn h => hM.1 ((Derives.of_mem hn).mp (Derives.of_mem h)),
    fun h => (hM.mem_or_neg_mem φ).resolve_left h⟩

theorem imp_mem_iff : φ.imp ψ ∈ S ↔ (φ ∈ S → ψ ∈ S) := by
  constructor
  · intro h hφ
    exact hM.closed ((Derives.of_mem h).mp (Derives.of_mem hφ))
  · intro h
    by_cases hφ : φ ∈ S
    · exact hM.closed ⟨[ψ], fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact h hφ,
        Provable.imp_intro (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    · exact hM.closed ⟨[φ.neg], fun θ hθ => by
          rw [List.mem_singleton.mp hθ]
          exact (hM.neg_mem_iff).mpr hφ,
        Provable.imp_intro (Provable.bot_elim (Provable.mp
          (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
          (Provable.of_mem List.mem_cons_self)))⟩

theorem and_mem_iff : φ.and ψ ∈ S ↔ φ ∈ S ∧ ψ ∈ S := by
  constructor
  · intro h
    exact ⟨hM.closed ⟨[φ.and ψ], fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact h,
        Provable.and_elim_l (Provable.of_mem List.mem_cons_self)⟩,
      hM.closed ⟨[φ.and ψ], fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact h,
        Provable.and_elim_r (Provable.of_mem List.mem_cons_self)⟩⟩
  · rintro ⟨hφ, hψ⟩
    exact hM.closed ⟨[φ, ψ], fun θ hθ => by
        rcases List.mem_cons.mp hθ with rfl | hθ
        · exact hφ
        · rw [List.mem_singleton.mp hθ]; exact hψ,
      Provable.and_intro (Provable.of_mem List.mem_cons_self)
        (Provable.of_mem (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem or_mem_iff : φ.or ψ ∈ S ↔ φ ∈ S ∨ ψ ∈ S := by
  constructor
  · intro h
    by_cases hφ : φ ∈ S
    · exact Or.inl hφ
    · refine Or.inr (hM.closed ⟨[φ.or ψ, φ.neg], fun θ hθ => ?_, ?_⟩)
      · rcases List.mem_cons.mp hθ with rfl | hθ
        · exact h
        · rw [List.mem_singleton.mp hθ]; exact (hM.neg_mem_iff).mpr hφ
      · exact Provable.or_elim (Provable.of_mem List.mem_cons_self)
          (Provable.bot_elim (Provable.mp
            (Provable.of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
            (Provable.of_mem List.mem_cons_self)))
          (Provable.of_mem List.mem_cons_self)
  · rintro (hφ | hψ)
    · exact hM.closed ⟨[φ], fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact hφ,
        Provable.or_intro_l (Provable.of_mem List.mem_cons_self)⟩
    · exact hM.closed ⟨[ψ], fun θ hθ => by rw [List.mem_singleton.mp hθ]; exact hψ,
        Provable.or_intro_r (Provable.of_mem List.mem_cons_self)⟩

end IsMCS

end Theory

end V12M
