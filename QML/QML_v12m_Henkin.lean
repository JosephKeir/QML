import QML.QML_v12m_WorldLang
import QML.QML_v12m_Countable
import QML.QML_v12m_RetMono

/-!
# QML v12m — the Henkin construction: the chain

The language of a world is built together with its theory.  At step `n` the construction has
declared `n` own variables, with types `l` (newest first), and holds a set of sentences over the
contexts `ctxL m l` (stage `m` of the base, all `n` variables).  Step `n`:

1. reads an enumerated formula `query n` (at an earlier own stage, lifted to the current one);
2. adds it if that keeps the theory consistent, and otherwise adds its negation (`choice`);
3. declares the next variable `ρ n`: if the added formula is `∃x:A. ψ` or `¬∀x:A. ψ`, at the
   type `A`, with the witness sentence `ψ[ρ n]` or `¬ψ[ρ n]`; otherwise, under strong T, as a
   witness `ρ n : ◇A` for an enumerated term `t : A` (`termQ n`) with all its hypotheses
   `WFF.retHyp` (`retSet`, consistent by `T_dia`); and otherwise at the unit type, which is always
   inhabited (`witStep`, `retStep`).

Declaring a variable asserts that its type is inhabited, so the types cannot be fixed in
advance: they are chosen as the witnesses are needed.  Keeping them as a list, newest first,
makes each new context literally an insertion into the previous one.

⭐`consistent_chain`: every stage of the chain is consistent, if the starting theory is.
-/

namespace V12M

variable [ModalSys]

/-! ## Generic facts -/

namespace StageSys

variable {I : Type} [Preorder I] {S : StageSys I} {σ : Signature} {T T' : Set (S.Sentence σ)}

theorem Consistent.mono_set (h : T ⊆ T') (hc : Consistent T') : Consistent T :=
  fun i => (hc i).mono (atStage_mono h i)

theorem consistent_insert_of_derives (hT : Consistent T) {i : I} {φ : WFF σ (S.ctx i) 0}
    (hd : Theory.Derives (atStage T i) φ) : Consistent (insert ⟨i, φ⟩ T) := by
  intro j
  by_cases hij : i ≤ j
  · refine Theory.Consistent.mono (atStage_insert_le (s := ⟨i, φ⟩) hij) ?_
    intro hbot
    exact hT j ((Theory.Derives.deduction hbot).mp (derives_lift hd hij))
  · exact (hT j).mono (atStage_insert_not_le hij)

/-- Adding a formula or its negation keeps a theory consistent. -/
theorem consistent_insert_or [IsDirected I (· ≤ ·)] (hT : Consistent T) {i : I}
    (φ : WFF σ (S.ctx i) 0) : Consistent (insert ⟨i, φ⟩ T) ∨ Consistent (insert ⟨i, φ.neg⟩ T) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h₁, h₂⟩ := h
  simp only [Consistent, not_forall] at h₁ h₂
  obtain ⟨j₁, hj₁⟩ := h₁
  obtain ⟨j₂, hj₂⟩ := h₂
  have e₁ : i ≤ j₁ := by
    by_contra hn
    exact hj₁ ((hT j₁).mono (atStage_insert_not_le hn))
  have e₂ : i ≤ j₂ := by
    by_contra hn
    exact hj₂ ((hT j₂).mono (atStage_insert_not_le hn))
  have d₁ : Theory.Derives (atStage T j₁) (lift e₁ φ).neg :=
    Theory.derives_neg_of_not_consistent fun hc => hj₁ (hc.mono (atStage_insert_le e₁))
  have d₂ : Theory.Derives (atStage T j₂) (lift e₂ φ.neg).neg :=
    Theory.derives_neg_of_not_consistent fun hc => hj₂ (hc.mono (atStage_insert_le e₂))
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) j₁ j₂
  have D₁ := derives_lift d₁ hk₁
  have D₂ := derives_lift d₂ hk₂
  simp only [lift_neg, lift_lift] at D₁ D₂
  exact hT _ (D₂.mp D₁)

end StageSys

omit [ModalSys] in
/-- Hypotheses drawn from `{w} ∪ f '' P` come from a list over `P`. -/
theorem exists_hyps_cons_map {α β : Type} {P : α → Prop} (f : α → β) (w : β) :
    ∀ Δ : List β, (∀ δ ∈ Δ, δ = w ∨ ∃ x, P x ∧ f x = δ) →
      ∃ Δ₀ : List α, (∀ x ∈ Δ₀, P x) ∧ ∀ δ ∈ Δ, δ ∈ w :: Δ₀.map f
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: Δ, h => by
      obtain ⟨Δ₀, h₀, h₁⟩ :=
        exists_hyps_cons_map f w Δ (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with rfl | ⟨x, hx, rfl⟩
      · refine ⟨Δ₀, h₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_cons_self
        · exact h₁ d hd
      · refine ⟨x :: Δ₀, fun y hy => ?_, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact h₀ y hy
        · rcases List.mem_cons.mp hd with rfl | hd
          · exact List.mem_cons_of_mem _ List.mem_cons_self
          · rcases List.mem_cons.mp (h₁ d hd) with rfl | hd'
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd')

omit [ModalSys] in
/-- Hypotheses drawn from `range g ∪ f '' P` come from two lists. -/
theorem exists_hyps_two {α γ β : Type} {P : α → Prop} (f : α → β) (g : γ → β) :
    ∀ Δ : List β, (∀ δ ∈ Δ, (∃ z, g z = δ) ∨ ∃ x, P x ∧ f x = δ) →
      ∃ (Γ₀ : List γ) (Δ₀ : List α), (∀ x ∈ Δ₀, P x) ∧ ∀ δ ∈ Δ, δ ∈ Γ₀.map g ++ Δ₀.map f
  | [], _ => ⟨[], [], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: Δ, h => by
      obtain ⟨Γ₀, Δ₀, h₀, h₁⟩ :=
        exists_hyps_two f g Δ (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rcases h δ List.mem_cons_self with ⟨z, rfl⟩ | ⟨x, hx, rfl⟩
      · refine ⟨z :: Γ₀, Δ₀, h₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_append_left _ List.mem_cons_self
        · rcases List.mem_append.mp (h₁ d hd) with h' | h'
          · exact List.mem_append_left _ (List.mem_cons_of_mem _ h')
          · exact List.mem_append_right _ h'
      · refine ⟨Γ₀, x :: Δ₀, fun y hy => ?_, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact h₀ y hy
        · rcases List.mem_cons.mp hd with rfl | hd
          · exact List.mem_append_right _ List.mem_cons_self
          · rcases List.mem_append.mp (h₁ d hd) with h' | h'
            · exact List.mem_append_left _ h'
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')

omit [ModalSys] in
/-- Hypotheses drawn from `f '' P` come from a list over `P`. -/
theorem exists_hyps_map {α β : Type} {P : α → Prop} (f : α → β) :
    ∀ Δ : List β, (∀ δ ∈ Δ, ∃ x, P x ∧ f x = δ) →
      ∃ Δ₀ : List α, (∀ x ∈ Δ₀, P x) ∧ ∀ δ ∈ Δ, δ ∈ Δ₀.map f
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: Δ, h => by
      obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_map f Δ (fun d hd => h d (List.mem_cons_of_mem _ hd))
      obtain ⟨x, hx, rfl⟩ := h δ List.mem_cons_self
      refine ⟨x :: Δ₀, fun y hy => ?_, fun d hd => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact h₀ y hy
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h₁ d hd)

namespace Subst

variable {σ : Signature} {Δ : Ctx}

theorem toFree_root (θ : Subst σ Δ) (d u : ℕ) (T : VarType) (h : Δ (.root (.free u)) = none) :
    θ.toFree d u T h (.root (.bnd d)) = .ren (.root (.free u)) :=
  if_pos rfl

theorem toFree_ne (θ : Subst σ Δ) {d : ℕ} (u : ℕ) (T : VarType) (h : Δ (.root (.free u)) = none)
    {v : VarSymb} (hv : v ≠ .root (.bnd d)) :
    θ.toFree d u T h v = (θ v).mono (Ctx.le_insert h T) :=
  if_neg hv

end Subst

/-- Opening commutes with weakening. -/
theorem WFF.mono_openFree {σ : Signature} {Γ Γ' : Ctx} {T : VarType} (h : Γ.Le Γ') {u : ℕ}
    (hu : Γ.RootFresh (.free u)) (hu' : Γ'.RootFresh (.free u)) (hs : Γ.SlotsFrom 0)
    (hs' : Γ'.SlotsFrom 0) (ψ : WFF σ (Γ.insert (.bnd 0) T) 1) :
    WFF.mono (h.insert (.free u) T) (WFF.openFree u hu hs ψ) =
      WFF.openFree u hu' hs' (WFF.mono (h.insert (.bnd 0) T) ψ) := by
  unfold WFF.openFree
  rw [WFF.mono_subst, WFF.subst_mono]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
  refine Subst.sim_of ?_
  intro v U _ _
  rw [Subst.mono_apply]
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [Subst.toFree_root, Subst.toFree_root]
    exact .refl _
  · rw [Subst.toFree_ne _ _ _ _ hvr, Subst.toFree_ne _ _ _ _ hvr]
    exact .refl _

/-- Proof by contradiction, as a proof. -/
def Proof.byContra {σ : Signature} {Γ : Ctx} {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (p : Proof σ Γ (φ.neg :: Δ) .bot) : Proof σ Γ Δ φ :=
  .or_elim (.lem φ) (Proof.lookup List.mem_cons_self) (.bot_elim φ p)

/-- `¬∀x ψ ⊢ ∃x ¬ψ`. -/
def Proof.exNeg_of_negAll {σ : Signature} {Γ : Ctx} [Γ.Presented] {A : VarType}
    (ψ : WFF σ (Γ.insert (.bnd 0) A) 1) : Proof σ Γ [(WFF.all A ψ).neg] (WFF.ex A ψ.neg) :=
  have hu : Γ.RootFresh (.free (Ctx.Presented.bound Γ)) := Ctx.Presented.fresh _ le_rfl
  have hs : Γ.SlotsFrom 0 := Ctx.NoSlots.slots
  have inner : Proof σ (Γ.insert (.free (Ctx.Presented.bound Γ)) A)
      [(WFF.openFree _ hu hs ψ).neg, WFF.weaken hu.root A (WFF.ex A ψ.neg).neg,
        WFF.weaken hu.root A (WFF.all A ψ).neg] .bot :=
    .imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))
      (Proof.ex_intro A (Term.eta (.root (.free _)) A (Ctx.ref_insert_root Γ _ A))
        (Proof.conv (WFF.instantiate_eta_openFree _ hu hs Ctx.NoSlots.slots ψ.neg).symm
          (Proof.lookup List.mem_cons_self)))
  have hall : Proof σ Γ [(WFF.ex A ψ.neg).neg, (WFF.all A ψ).neg] (WFF.all A ψ) :=
    Proof.conv (congrArg (WFF.all A) (WFF.bindFree_openFree _ hu hs ψ))
      (Proof.all_intro _ A hu (Proof.byContra inner))
  Proof.byContra (.imp_elim (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)) hall)

instance {σ : Signature} {Γ : Ctx} {d : ℕ} : Nonempty (WFF σ Γ d) := ⟨.top⟩

/-- A fixed enumeration of the formulas over a context. -/
noncomputable def enumF {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
    (Γ : Ctx) : ℕ → WFF σ Γ 0 :=
  Classical.choose (exists_surjective_nat (WFF σ Γ 0))

theorem enumF_surjective {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
    (Γ : Ctx) : Function.Surjective (enumF (σ := σ) Γ) :=
  Classical.choose_spec (exists_surjective_nat (WFF σ Γ 0))

instance {σ : Signature} {Γ : Ctx} : Nonempty (Σ A : VarType, Σ a : Ann A, Term σ Γ A a) :=
  ⟨⟨.VTypeOne, .one, .unit⟩⟩

/-- A fixed enumeration of the terms over a context, of every type (for strong T witnesses). -/
noncomputable def enumT {σ : Signature} [Countable σ.FuncSyms] (Γ : Ctx) :
    ℕ → Σ A : VarType, Σ a : Ann A, Term σ Γ A a :=
  Classical.choose (exists_surjective_nat (Σ A : VarType, Σ a : Ann A, Term σ Γ A a))

theorem enumT_surjective {σ : Signature} [Countable σ.FuncSyms] (Γ : Ctx) :
    Function.Surjective (enumT (σ := σ) Γ) :=
  Classical.choose_spec (exists_surjective_nat (Σ A : VarType, Σ a : Ann A, Term σ Γ A a))

/-! ## Contexts along the construction -/

namespace WorldLang

variable (L : WorldLang)

/-- Stage `m` of the base with the own variables of types `l`, newest first. -/
def ctxL (m : ℕ) : List VarType → Ctx
  | [] => L.base m
  | A :: l => (ctxL m l).insert (.free (L.ρ l.length)) A

instance presL (m : ℕ) : ∀ l, (L.ctxL m l).Presented
  | [] => inferInstanceAs (L.base m).Presented
  | A :: l =>
      haveI := presL m l
      inferInstanceAs ((L.ctxL m l).insert (.free (L.ρ l.length)) A).Presented

theorem ctxL_fresh {m n : ℕ} : ∀ {l : List VarType}, l.length ≤ n →
    (L.ctxL m l).RootFresh (.free (L.ρ n))
  | [], _ => L.fresh m n
  | A :: l, h => by
      have h' : l.length + 1 ≤ n := h
      exact (ctxL_fresh (Nat.le_of_succ_le h')).insert_ne (fun he => by
        have := L.ρ_inj (Root.free.inj he)
        omega) A

theorem ctxL_le_cons (m : ℕ) (A : VarType) (l : List VarType) :
    (L.ctxL m l).Le (L.ctxL m (A :: l)) :=
  Ctx.le_insert (L.ctxL_fresh le_rfl).root A

theorem ctxL_base_le {m m' : ℕ} (h : m ≤ m') : ∀ l, (L.ctxL m l).Le (L.ctxL m' l)
  | [] => L.base_mono h
  | A :: l => (ctxL_base_le h l).insert _ A

theorem ctxL_drop_le (m : ℕ) : ∀ (k : ℕ) (l : List VarType), (L.ctxL m (l.drop k)).Le (L.ctxL m l)
  | 0, _ => Ctx.Le.refl _
  | _ + 1, [] => Ctx.Le.refl _
  | k + 1, A :: l => (ctxL_drop_le m k l).trans (L.ctxL_le_cons m A l)

/-- The contexts with a fixed list of own variables, as a stage system over the base. -/
abbrev pre (l : List VarType) : StageSys ℕ :=
  ⟨fun m => L.ctxL m l, fun h => L.ctxL_base_le h l, fun m => L.presL m l⟩

variable {L} {σ : Signature}

/-- A theory, grown by one declaration. -/
def grow (l : List VarType) (A : VarType) (S : Set ((L.pre l).Sentence σ)) :
    Set ((L.pre (A :: l)).Sentence σ) :=
  (fun s => ⟨s.1, WFF.mono (L.ctxL_le_cons s.1 A l) s.2⟩) '' S

theorem mem_grow {l : List VarType} {A : VarType} {S : Set ((L.pre l).Sentence σ)} {m : ℕ}
    {φ : WFF σ (L.ctxL m l) 0} (h : (⟨m, φ⟩ : (L.pre l).Sentence σ) ∈ S) :
    (⟨m, WFF.mono (L.ctxL_le_cons m A l) φ⟩ : (L.pre (A :: l)).Sentence σ) ∈ grow l A S :=
  ⟨⟨m, φ⟩, h, rfl⟩

theorem grow_mono {l : List VarType} {A : VarType} {S S' : Set ((L.pre l).Sentence σ)}
    (h : S ⊆ S') : grow l A S ⊆ grow l A S' :=
  Set.image_mono h

theorem mem_atStage_grow {l : List VarType} {A : VarType} {S : Set ((L.pre l).Sentence σ)}
    {m : ℕ} {ψ : WFF σ (L.ctxL m (A :: l)) 0}
    (h : ψ ∈ StageSys.atStage (grow l A S) m) :
    ∃ ψ₀, ψ₀ ∈ StageSys.atStage S m ∧ WFF.mono (L.ctxL_le_cons m A l) ψ₀ = ψ := by
  obtain ⟨s, ⟨s₀, hs₀, rfl⟩, hle, rfl⟩ := h
  exact ⟨StageSys.lift hle s₀.2, ⟨s₀, hs₀, hle, rfl⟩,
    (WFF.mono_mono _ _ _).trans (WFF.mono_mono _ _ _).symm⟩

/-! ## One step -/

/-- A declaration of unit type keeps a theory consistent. -/
theorem consistent_grow_unit {l : List VarType} {S : Set ((L.pre l).Sentence σ)}
    (hS : StageSys.Consistent S) : StageSys.Consistent (grow l .VTypeOne S ∪ ∅) := by
  rw [Set.union_empty]
  rintro m ⟨Δ, hΔ, p⟩
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_map (P := fun x => x ∈ StageSys.atStage S m)
    (fun x => WFF.mono (L.ctxL_le_cons m .VTypeOne l) x) Δ
    (fun δ hδ => mem_atStage_grow (hΔ δ hδ))
  obtain ⟨q⟩ := Provable.mono h₁ p
  have hu : (L.ctxL m l).RootFresh (.free (L.ρ l.length)) := L.ctxL_fresh le_rfl
  exact hS m ⟨Δ₀, h₀, ⟨Proof.ex_elim (L.ρ l.length) .VTypeOne hu (φ := .top) (ψ := .bot)
    (Proof.ex_intro .VTypeOne .unit .top_intro) (Proof.weak _ q)⟩⟩

/-- The witness of an existential keeps a theory consistent. -/
theorem consistent_grow_ex {l : List VarType} {S : Set ((L.pre l).Sentence σ)}
    (hS : StageSys.Consistent S) {m : ℕ} {A : VarType}
    {ψ : WFF σ ((L.ctxL m l).insert (.bnd 0) A) 1}
    (hψ : (⟨m, .ex A ψ⟩ : (L.pre l).Sentence σ) ∈ S) :
    StageSys.Consistent (grow l A S ∪
      {⟨m, WFF.openFree (L.ρ l.length) (L.ctxL_fresh le_rfl) Ctx.NoSlots.slots ψ⟩}) := by
  have key : ∀ m', m ≤ m' → Theory.Consistent (StageSys.atStage (grow l A S ∪
      {⟨m, WFF.openFree (L.ρ l.length) (L.ctxL_fresh le_rfl) Ctx.NoSlots.slots ψ⟩}) m') := by
    rintro m' hm ⟨Δ, hΔ, p⟩
    have hu : (L.ctxL m' l).RootFresh (.free (L.ρ l.length)) := L.ctxL_fresh le_rfl
    have hs : (L.ctxL m' l).SlotsFrom 0 := Ctx.NoSlots.slots
    have hcases : ∀ δ ∈ Δ, δ = WFF.openFree (L.ρ l.length) hu hs
        (WFF.mono ((L.ctxL_base_le hm l).insert (.bnd 0) A) ψ) ∨
        ∃ x, x ∈ StageSys.atStage S m' ∧ WFF.mono (L.ctxL_le_cons m' A l) x = δ := by
      intro δ hδ
      obtain ⟨s, hs', hle, rfl⟩ := hΔ δ hδ
      rcases hs' with hs' | hs'
      · exact Or.inr (mem_atStage_grow ⟨s, hs', hle, rfl⟩)
      · rw [Set.mem_singleton_iff] at hs'
        subst hs'
        exact Or.inl (WFF.mono_openFree (L.ctxL_base_le hle l) (L.ctxL_fresh le_rfl) hu
          Ctx.NoSlots.slots hs ψ)
    obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := fun x => x ∈ StageSys.atStage S m')
      (fun x => WFF.mono (L.ctxL_le_cons m' A l) x) _ Δ hcases
    obtain ⟨q⟩ := Provable.mono h₁ p
    have hex : WFF.ex A (WFF.mono ((L.ctxL_base_le hm l).insert (.bnd 0) A) ψ) ∈
        StageSys.atStage S m' :=
      ⟨⟨m, .ex A ψ⟩, hψ, hm, rfl⟩
    refine hS m' ⟨WFF.ex A (WFF.mono ((L.ctxL_base_le hm l).insert (.bnd 0) A) ψ) :: Δ₀,
      fun x hx => ?_, ⟨Proof.ex_elim (L.ρ l.length) A hu
        (φ := WFF.openFree (L.ρ l.length) hu hs
          (WFF.mono ((L.ctxL_base_le hm l).insert (.bnd 0) A) ψ)) (ψ := .bot)
        (Proof.conv (congrArg (WFF.ex A) (WFF.bindFree_openFree (L.ρ l.length) hu hs
          (WFF.mono ((L.ctxL_base_le hm l).insert (.bnd 0) A) ψ)).symm)
          (Proof.lookup List.mem_cons_self))
        (Proof.ofSubset (fun x hx => ?_) q)⟩⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hex
      · exact h₀ x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy))
  intro m'
  rcases le_total m m' with hm | hm
  · exact key m' hm
  · exact StageSys.consistent_of_le (key m le_rfl) hm

/-- The witness of a negated universal keeps a theory consistent. -/
theorem consistent_grow_negAll {l : List VarType} {S : Set ((L.pre l).Sentence σ)}
    (hS : StageSys.Consistent S) {m : ℕ} {A : VarType}
    {ψ : WFF σ ((L.ctxL m l).insert (.bnd 0) A) 1}
    (hψ : (⟨m, (WFF.all A ψ).neg⟩ : (L.pre l).Sentence σ) ∈ S) :
    StageSys.Consistent (grow l A S ∪
      {⟨m, WFF.openFree (L.ρ l.length) (L.ctxL_fresh le_rfl) Ctx.NoSlots.slots ψ.neg⟩}) := by
  have hS' : StageSys.Consistent (insert (⟨m, WFF.ex A ψ.neg⟩ : (L.pre l).Sentence σ) S) :=
    StageSys.consistent_insert_of_derives hS
      ⟨[(WFF.all A ψ).neg], fun x hx => by
        rw [List.mem_singleton.mp hx]
        exact StageSys.mem_atStage_self hψ, ⟨Proof.exNeg_of_negAll ψ⟩⟩
  exact (consistent_grow_ex hS' (Set.mem_insert _ _)).mono_set
    (Set.union_subset_union_left _ (grow_mono (Set.subset_insert _ _)))

/-! ## Strong T witnesses -/

theorem ρ_succ_ne (l : List VarType) : L.ρ (l.length + 1) ≠ L.ρ l.length := fun e => by
  have := L.ρ_inj e
  omega

variable (L) in
/-- The strong T hypotheses of a witness `ρ l.length : ◇A` for the term `t`: every
    `WFF.retHyp` at every stage from `m` on, with parameter name `ρ (l.length + 1)`.  All later
    stages are included because a hole formula there may mention that stage's base constants. -/
def retSet (hT : ModalSys.T = true) (l : List VarType) (m : ℕ) {A : VarType} {a : Ann A}
    (t : Term σ (L.ctxL m l) A a) : Set ((L.pre (.VTypeDia A :: l)).Sentence σ) :=
  {s | ∃ (m' : ℕ) (hm : m ≤ m') (B : VarType)
      (ψ : WFF σ (((L.ctxL m' l).insert (.free (L.ρ (l.length + 1))) B).boxIn.insert (.bnd 0) A)
        1),
      s = ⟨m', WFF.retHyp hT (Term.mono (L.ctxL_base_le hm l) t) (L.ρ l.length)
        (L.ρ (l.length + 1)) (L.ctxL_fresh le_rfl) (L.ctxL_fresh (Nat.le_succ _))
        (ρ_succ_ne l) B ψ⟩}

/-- ⭐A strong T witness for a term keeps a theory consistent: a derivation of `⊥` uses finitely many
    of its hypotheses, each lifted to one stage, where they are `WFF.retHyp` instances
    (`WFF.mono_retHyp`) and `T_dia` discharges the witness. -/
theorem consistent_grow_ret (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true)
    {l : List VarType} {S : Set ((L.pre l).Sentence σ)} (hS : StageSys.Consistent S) {m : ℕ}
    {A : VarType} {a : Ann A} (t : Term σ (L.ctxL m l) A a) :
    StageSys.Consistent (grow l (.VTypeDia A) S ∪ L.retSet hT l m t) := by
  have key : ∀ M, m ≤ M →
      Theory.Consistent (StageSys.atStage (grow l (.VTypeDia A) S ∪ L.retSet hT l m t) M) := by
    rintro M hM ⟨Δ, hΔ, p⟩
    have hc : (L.ctxL M l).RootFresh (.free (L.ρ l.length)) := L.ctxL_fresh le_rfl
    have hy : (L.ctxL M l).RootFresh (.free (L.ρ (l.length + 1))) := L.ctxL_fresh (Nat.le_succ _)
    let g : (Σ B : VarType,
        WFF σ (((L.ctxL M l).insert (.free (L.ρ (l.length + 1))) B).boxIn.insert (.bnd 0) A) 1) →
        WFF σ (L.ctxL M (.VTypeDia A :: l)) 0 := fun z =>
      WFF.retHyp hT (Term.mono (L.ctxL_base_le hM l) t) (L.ρ l.length) (L.ρ (l.length + 1)) hc hy
        (ρ_succ_ne l) z.1 z.2
    have hcases : ∀ δ ∈ Δ, (∃ z, g z = δ) ∨
        ∃ x, x ∈ StageSys.atStage S M ∧ WFF.mono (L.ctxL_le_cons M (.VTypeDia A) l) x = δ := by
      intro δ hδ
      obtain ⟨s, hs, hle, rfl⟩ := hΔ δ hδ
      rcases hs with hs | hs
      · exact Or.inr (mem_atStage_grow ⟨s, hs, hle, rfl⟩)
      · obtain ⟨m', hm', B, ψ, rfl⟩ := hs
        refine Or.inl ⟨⟨B, WFF.mono
          (((L.ctxL_base_le hle l).insert (.free (L.ρ (l.length + 1))) B).boxIn.insert (.bnd 0) A)
          ψ⟩, ?_⟩
        change _ = WFF.mono ((L.ctxL_base_le hle l).insert (.free (L.ρ l.length)) (.VTypeDia A)) _
        rw [WFF.mono_retHyp hT (L.ctxL_base_le hle l) _ (L.ctxL_fresh le_rfl) hc
          (L.ctxL_fresh (Nat.le_succ _)) hy (ρ_succ_ne l) B ψ, Term.mono_mono]
    obtain ⟨Ψ, Δ₀, h₀, h₁⟩ := exists_hyps_two (P := fun x => x ∈ StageSys.atStage S M)
      (fun x => WFF.mono (L.ctxL_le_cons M (.VTypeDia A) l) x) g Δ hcases
    obtain ⟨q⟩ := Provable.mono h₁ p
    exact hS M ⟨Δ₀, h₀, ⟨Proof.T_dia hT hTS A (Term.mono (L.ctxL_base_le hM l) t) _ _ hc hy
      (ρ_succ_ne l) (φ := .bot) Ψ q⟩⟩
  intro M
  rcases le_total m M with hM | hM
  · exact key M hM
  · exact StageSys.consistent_of_le (key m le_rfl) hM

variable (L) in
/-- The declaration made when no witness is needed: under strong T (with weak T), a witness for
    the term `t` with all its hypotheses; otherwise a variable of unit type. -/
noncomputable def retStep (m : ℕ) (l : List VarType)
    (tq : Σ A : VarType, Σ a : Ann A, Term σ (L.ctxL m l) A a) :
    Σ A : VarType, Set ((L.pre (A :: l)).Sentence σ) :=
  if h : ModalSys.T = true ∧ ModalSys.TStrong = true then
    ⟨.VTypeDia tq.1, L.retSet h.1 l m tq.2.2⟩
  else ⟨.VTypeOne, ∅⟩

theorem consistent_retStep {l : List VarType} {S : Set ((L.pre l).Sentence σ)}
    (hS : StageSys.Consistent S) (m : ℕ)
    (tq : Σ A : VarType, Σ a : Ann A, Term σ (L.ctxL m l) A a) :
    StageSys.Consistent (grow l (L.retStep m l tq).1 S ∪ (L.retStep m l tq).2) := by
  by_cases h : ModalSys.T = true ∧ ModalSys.TStrong = true
  · have e : L.retStep m l tq = ⟨.VTypeDia tq.1, L.retSet h.1 l m tq.2.2⟩ := dif_pos h
    rw [e]
    exact consistent_grow_ret h.1 h.2 hS tq.2.2
  · have e : L.retStep m l tq = ⟨.VTypeOne, ∅⟩ := dif_neg h
    rw [e]
    exact consistent_grow_unit hS

variable (L) in
/-- The declaration made after adding `χ`, and its witness sentences: the witness of an
    existential or a negated universal, and otherwise `retStep` for the step's term `tq`. -/
noncomputable def witStep (m : ℕ) (l : List VarType)
    (tq : Σ A : VarType, Σ a : Ann A, Term σ (L.ctxL m l) A a) :
    WFF σ (L.ctxL m l) 0 → Σ A : VarType, Set ((L.pre (A :: l)).Sentence σ)
  | .ex A ψ => ⟨A, {⟨m, WFF.openFree (L.ρ l.length) (L.ctxL_fresh le_rfl) Ctx.NoSlots.slots ψ⟩}⟩
  | .imp (.all A ψ) .bot =>
      ⟨A, {⟨m, WFF.openFree (L.ρ l.length) (L.ctxL_fresh le_rfl) Ctx.NoSlots.slots ψ.neg⟩}⟩
  | _ => L.retStep m l tq

section Chain

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- A state of the construction: the types of the own variables so far, newest first, and the
    theory. -/
structure HState (L : WorldLang) (σ : Signature) where
  l : List VarType
  S : Set ((L.pre l).Sentence σ)

/-- Step `n` reads the `k`-th formula and the `k'`-th term at base stage `m` and own stage `j`,
    where `n = ⟪j, ⟪m, ⟪k, k'⟫⟫⟫`. -/
def decJ (n : ℕ) : ℕ := n.unpair.1

def decM (n : ℕ) : ℕ := n.unpair.2.unpair.1

def decK (n : ℕ) : ℕ := n.unpair.2.unpair.2

/-- The formula index read at step `n`. -/
def decKF (n : ℕ) : ℕ := (decK n).unpair.1

/-- The term index read at step `n`. -/
def decKT (n : ℕ) : ℕ := (decK n).unpair.2

variable (L) in
/-- The formula read at step `n`, lifted to all current own variables. -/
noncomputable def query (n : ℕ) (l : List VarType) : WFF σ (L.ctxL (decM n) l) 0 :=
  WFF.mono (L.ctxL_drop_le _ (n - decJ n) l) (enumF _ (decKF n))

variable (L) in
/-- The term read at step `n`, lifted to all current own variables. -/
noncomputable def termQ (n : ℕ) (l : List VarType) :
    Σ A : VarType, Σ a : Ann A, Term σ (L.ctxL (decM n) l) A a :=
  ⟨_, _, Term.mono (L.ctxL_drop_le _ (n - decJ n) l)
    (enumT (L.ctxL (decM n) (l.drop (n - decJ n))) (decKT n)).2.2⟩

variable (L) in
open Classical in
/-- The query if it keeps the theory consistent, otherwise its negation. -/
noncomputable def choice (n : ℕ) (st : HState L σ) : WFF σ (L.ctxL (decM n) st.l) 0 :=
  if StageSys.Consistent (insert (⟨decM n, L.query n st.l⟩ : (L.pre st.l).Sentence σ) st.S)
  then L.query n st.l else (L.query n st.l).neg

variable (L) in
/-- Step `n` of the construction. -/
noncomputable def step (n : ℕ) (st : HState L σ) : HState L σ :=
  ⟨(L.witStep (decM n) st.l (L.termQ n st.l) (L.choice n st)).1 :: st.l,
    grow st.l _ (insert ⟨decM n, L.choice n st⟩ st.S) ∪
      (L.witStep (decM n) st.l (L.termQ n st.l) (L.choice n st)).2⟩

variable (L) in
/-- The construction from a starting theory over the base. -/
noncomputable def chain (S₀ : Set ((L.pre []).Sentence σ)) : ℕ → HState L σ
  | 0 => ⟨[], S₀⟩
  | n + 1 => L.step n (chain S₀ n)

theorem choice_cases (n : ℕ) (st : HState L σ) :
    L.choice n st = L.query n st.l ∨ L.choice n st = (L.query n st.l).neg := by
  unfold choice
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem consistent_choice (n : ℕ) (st : HState L σ) (hS : StageSys.Consistent st.S) :
    StageSys.Consistent (insert (⟨decM n, L.choice n st⟩ : (L.pre st.l).Sentence σ) st.S) := by
  unfold choice
  split_ifs with h
  · exact h
  · exact (StageSys.consistent_insert_or hS _).resolve_left h

/-- One step keeps the theory consistent. -/
theorem consistent_step (n : ℕ) (st : HState L σ) (hS : StageSys.Consistent st.S) :
    StageSys.Consistent (L.step n st).S := by
  have h₁ := consistent_choice n st hS
  have hmem : (⟨decM n, L.choice n st⟩ : (L.pre st.l).Sentence σ) ∈
      insert ⟨decM n, L.choice n st⟩ st.S :=
    Set.mem_insert _ _
  change StageSys.Consistent (grow st.l _ (insert ⟨decM n, L.choice n st⟩ st.S) ∪
    (L.witStep (decM n) st.l (L.termQ n st.l) (L.choice n st)).2)
  generalize L.choice n st = χ at h₁ hmem ⊢
  cases χ with
  | ex A ψ => exact consistent_grow_ex h₁ hmem
  | imp φ₁ φ₂ =>
      cases φ₁ with
      | all A ψ =>
          cases φ₂ with
          | bot => exact consistent_grow_negAll h₁ hmem
          | _ => exact consistent_retStep h₁ _ _
      | _ => exact consistent_retStep h₁ _ _
  | _ => exact consistent_retStep h₁ _ _

/-- ⭐Every stage of the construction is consistent. -/
theorem consistent_chain {S₀ : Set ((L.pre []).Sentence σ)} (hS₀ : StageSys.Consistent S₀) :
    ∀ n, StageSys.Consistent (L.chain S₀ n).S
  | 0 => hS₀
  | n + 1 => consistent_step n _ (consistent_chain hS₀ n)

/-! ## Shape of the chain -/

theorem chain_succ_l (S₀ : Set ((L.pre []).Sentence σ)) (n : ℕ) :
    (L.chain S₀ (n + 1)).l =
      (L.witStep (decM n) (L.chain S₀ n).l (L.termQ n (L.chain S₀ n).l)
        (L.choice n (L.chain S₀ n))).1 :: (L.chain S₀ n).l :=
  rfl

theorem length_chain (S₀ : Set ((L.pre []).Sentence σ)) : ∀ n, (L.chain S₀ n).l.length = n
  | 0 => rfl
  | n + 1 => by
      rw [chain_succ_l, List.length_cons, length_chain S₀ n]

theorem drop_chain (S₀ : Set ((L.pre []).Sentence σ)) {j : ℕ} :
    ∀ {n : ℕ}, j ≤ n → (L.chain S₀ n).l.drop (n - j) = (L.chain S₀ j).l
  | n, h => by
      induction n with
      | zero =>
          have hj : j = 0 := Nat.le_zero.mp h
          subst hj
          rfl
      | succ n ih =>
          rcases Nat.lt_or_ge n j with hn | hn
          · have hj : j = n + 1 := by omega
            subst hj
            simp
          · rw [show n + 1 - j = (n - j) + 1 by omega, chain_succ_l, List.drop_succ_cons, ih hn]

theorem chain_le (S₀ : Set ((L.pre []).Sentence σ)) {n N : ℕ} (h : n ≤ N) (m : ℕ) :
    (L.ctxL m (L.chain S₀ n).l).Le (L.ctxL m (L.chain S₀ N).l) := by
  induction h with
  | refl => exact Ctx.Le.refl _
  | step _ ih => exact ih.trans (L.ctxL_le_cons m _ _)

/-- Sentences stay in the theory, lifted, at every later step. -/
theorem mem_chain_mono (S₀ : Set ((L.pre []).Sentence σ)) {n N : ℕ} (h : n ≤ N) {m : ℕ}
    {φ : WFF σ (L.ctxL m (L.chain S₀ n).l) 0}
    (hφ : (⟨m, φ⟩ : (L.pre (L.chain S₀ n).l).Sentence σ) ∈ (L.chain S₀ n).S) :
    (⟨m, WFF.mono (chain_le S₀ h m) φ⟩ : (L.pre (L.chain S₀ N).l).Sentence σ) ∈
      (L.chain S₀ N).S := by
  induction h with
  | refl =>
      rw [WFF.mono_refl]
      exact hφ
  | @step N hN ih =>
      have e : WFF.mono (chain_le S₀ (Nat.le.step hN) m) φ =
          WFF.mono (L.ctxL_le_cons m _ _) (WFF.mono (chain_le S₀ hN m) φ) :=
        (WFF.mono_mono _ _ φ).symm
      rw [e]
      exact Or.inl (mem_grow (Set.mem_insert_of_mem _ ih))

/-- The formula chosen at step `n` is in the theory from step `n + 1` on. -/
theorem choice_mem (S₀ : Set ((L.pre []).Sentence σ)) (n : ℕ) :
    (⟨decM n, WFF.mono (L.ctxL_le_cons (decM n)
        (L.witStep (decM n) (L.chain S₀ n).l (L.termQ n (L.chain S₀ n).l)
          (L.choice n (L.chain S₀ n))).1 (L.chain S₀ n).l)
        (L.choice n (L.chain S₀ n))⟩ :
      (L.pre (L.chain S₀ (n + 1)).l).Sentence σ) ∈ (L.chain S₀ (n + 1)).S :=
  Or.inl (mem_grow (Set.mem_insert _ _))

end Chain

end WorldLang

end V12M
