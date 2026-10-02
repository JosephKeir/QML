import QML.QML_v12m_Completeness

/-!
# QML v12m — model existence, strong completeness and compactness

The canonical construction starts from an arbitrary consistent set of sentences (`World.ofHenkin`),
so completeness extends from sequents to sets of premises of any size.

* ⭐`model_existence`: every consistent set of formulas in a presented context has a model.
* ⭐`strong_completeness`: a formula true in every model of a set of premises is derivable from
  finitely many of them.
* ⭐`compactness`: a set of formulas is satisfiable if every finite subset is.
* ⭐`realise_type` (proof-theoretic, no completeness used): a set of formulas that derives
  `∃y. χ₁(y) ∧ … ∧ χₙ(y)` for every finite part of a type stays consistent when one fresh variable
  is made to satisfy the whole type.

The first three hold for every combination of the flags, over a countable signature; the last
needs neither countability nor a presented context.
-/

namespace V12M

variable [ModalSys]

universe u v

variable {σ : Signature}

/-- A set of formulas is **consistent** when no finite list drawn from it derives `⊥`. -/
def WFF.SetConsistent {Γ : Ctx} (S : Set (WFF σ Γ 0)) : Prop :=
  ∀ Δ : List (WFF σ Γ 0), (∀ ψ ∈ Δ, ψ ∈ S) → ¬ Provable Δ .bot

/-- A set of formulas is **satisfiable** when some model, world and environment make it true. -/
def WFF.SetSatisfiable {Γ : Ctx} (S : Set (WFF σ Γ 0)) : Prop :=
  ∃ (M : Model.{0, 0} σ) (_ : M.IndInvariant) (w : M.frame.W) (env : M.Env Γ w),
    ∀ ψ ∈ S, M.sat env ψ

/-! ## Realising a type by a fresh variable

A proof-theoretic fact, needed where completeness is not yet available: the back-and-forth
construction for B (`docs/v12-arrow-canonical.md` §6) applies it in the B system itself, whose
completeness is what the construction is for, so it cannot go through `model_existence`. It is
stated for an arbitrary set of formulas; nothing about worlds is needed. -/

/-- The conjunction of a list of formulas (`⊤` for the empty list). -/
def WFF.conjL {Γ : Ctx} {d : ℕ} : List (WFF σ Γ d) → WFF σ Γ d
  | [] => .top
  | φ :: L => .and φ (WFF.conjL L)

theorem Provable.of_conjL {Γ : Ctx} {Δ : List (WFF σ Γ 0)} :
    ∀ {L : List (WFF σ Γ 0)} {x : WFF σ Γ 0}, x ∈ L → Provable Δ (WFF.conjL L) → Provable Δ x
  | y :: L, x, hx, p => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact p.and_elim_l
      · exact Provable.of_conjL hx p.and_elim_r

/-- Whatever a list derives, a list deriving each of its members derives too. -/
theorem Provable.of_all {Γ : Ctx} {Δ : List (WFF σ Γ 0)} :
    ∀ {Λ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}, (∀ x ∈ Λ, Provable Δ x) → Provable Λ φ →
      Provable Δ φ
  | [], _, _, p => Provable.mono (fun _ h => by simp at h) p
  | x :: Λ, _, h, p =>
      Provable.mp (Provable.of_all (fun y hy => h y (List.mem_cons_of_mem _ hy))
        (Provable.imp_intro p)) (h x List.mem_cons_self)

theorem WFF.openFree_conjL {Γ : Ctx} {T : VarType} (u : ℕ) (hu : Γ.RootFresh (.free u))
    (hs : Γ.SlotsFrom 0) :
    ∀ L : List (WFF σ (Γ.insert (.bnd 0) T) 1),
      WFF.openFree u hu hs (WFF.conjL L) = WFF.conjL (L.map (WFF.openFree u hu hs))
  | [] => rfl
  | _ :: L => congrArg (WFF.and _) (WFF.openFree_conjL u hu hs L)

omit [ModalSys] in
/-- A list drawn from the union of two images splits into a list drawn from each. -/
theorem List.split_images {α β γ : Type*} (f : α → γ) (g : β → γ) (P : Set α) (Q : Set β) :
    ∀ Λ : List γ, (∀ x ∈ Λ, x ∈ f '' P ∪ g '' Q) →
      ∃ (Λ₁ : List α) (Λ₂ : List β), (∀ a ∈ Λ₁, a ∈ P) ∧ (∀ b ∈ Λ₂, b ∈ Q) ∧
        ∀ x ∈ Λ, x ∈ Λ₁.map f ++ Λ₂.map g
  | [], _ => ⟨[], [], by simp, by simp, by simp⟩
  | x :: Λ, h => by
      obtain ⟨Λ₁, Λ₂, h₁, h₂, hΛ⟩ := List.split_images f g P Q Λ
        (fun y hy => h y (List.mem_cons_of_mem _ hy))
      rcases h x List.mem_cons_self with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · refine ⟨a :: Λ₁, Λ₂, ?_, h₂, ?_⟩
        · intro a' ha'
          rcases List.mem_cons.mp ha' with rfl | ha'
          · exact ha
          · exact h₁ a' ha'
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_append_left _ List.mem_cons_self
          · rcases List.mem_append.mp (hΛ y hy) with h | h
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
            · exact List.mem_append_right _ h
      · refine ⟨Λ₁, b :: Λ₂, h₁, ?_, ?_⟩
        · intro b' hb'
          rcases List.mem_cons.mp hb' with rfl | hb'
          · exact hb
          · exact h₂ b' hb'
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_append_right _ List.mem_cons_self
          · rcases List.mem_append.mp (hΛ y hy) with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- ⭐**Realising a type by a fresh variable.** Let `S` be consistent, and `p` a set of formulas in
    one hole such that `S` derives `∃y. χ₁(y) ∧ … ∧ χₙ(y)` for every finite list of members of `p`.
    Then `S` together with every `χ(u)`, `χ ∈ p`, is consistent, for any fresh `u`: one variable
    realises the whole of `p` at once.

    This is the step of the back-and-forth construction that turns a finitely satisfiable
    back-type (`Canon.finite_piece`, `Canon.backType_extend`) into a realiser. `χ(u)` is
    `WFF.openFree u χ`, which is the instantiation at `u`'s η-expansion
    (`WFF.instantiate_eta_openFree`). -/
theorem realise_type {Γ : Ctx} [Γ.NoSlots] {S : Set (WFF σ Γ 0)} (hS : WFF.SetConsistent S)
    {A : VarType} (p : Set (WFF σ (Γ.insert (.bnd 0) A) 1))
    (hp : ∀ Δ : List (WFF σ (Γ.insert (.bnd 0) A) 1), (∀ χ ∈ Δ, χ ∈ p) →
      ∃ Θ : List (WFF σ Γ 0), (∀ ψ ∈ Θ, ψ ∈ S) ∧ Provable Θ (.ex A (WFF.conjL Δ)))
    (u : ℕ) (hu : Γ.RootFresh (.free u)) :
    WFF.SetConsistent (WFF.weaken hu.root A '' S ∪
      WFF.openFree u hu Ctx.NoSlots.slots '' p) := by
  intro Λ hΛ q
  -- Split the hypotheses into the weakened members of `S` and the instances of `p`.
  obtain ⟨Θ₀, Δ, hΘ₀, hΔ, hsplit⟩ := List.split_images _ _ S p Λ hΛ
  obtain ⟨Θ₁, hΘ₁, ⟨q₁⟩⟩ := hp Δ hΔ
  -- In the context with `u`: the conjunction of the instances, with `Θ₀`, derives `⊥` …
  have q₂ : Provable (WFF.openFree u hu Ctx.NoSlots.slots (WFF.conjL Δ) ::
      (Θ₀ ++ Θ₁).map (WFF.weaken hu.root A)) .bot := by
    refine Provable.of_all (fun x hx => ?_) (Provable.mono hsplit q)
    rcases List.mem_append.mp hx with hx | hx
    · exact Provable.of_mem (List.mem_cons_of_mem _
        (List.mem_map.mpr (by
          obtain ⟨θ, hθ, rfl⟩ := List.mem_map.mp hx
          exact ⟨θ, List.mem_append_left _ hθ, rfl⟩)))
    · rw [WFF.openFree_conjL] at *
      exact Provable.of_conjL hx (Provable.of_mem List.mem_cons_self)
  obtain ⟨q₂⟩ := q₂
  -- … so `∃`-elimination at the fresh `u` refutes `∃y. ⋀Δ(y)`, which `Θ₁` derives.
  refine hS (Θ₀ ++ Θ₁) (fun ψ hψ => ?_) ⟨Proof.ex_elim u A hu
    (φ := WFF.openFree u hu Ctx.NoSlots.slots (WFF.conjL Δ)) (ψ := .bot) ?_ q₂⟩
  · rcases List.mem_append.mp hψ with h | h
    · exact hΘ₀ ψ h
    · exact hΘ₁ ψ h
  · rw [WFF.bindFree_openFree]
    exact Proof.ofSubset (fun ψ h => List.mem_append_right _ h) q₁

variable [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoB]

/-- ⭐**Model existence.** Every consistent set of formulas in a presented context is satisfiable:
    the canonical model built over it, at its first world, in the canonical environment. -/
theorem model_existence {Γ : Ctx} [Γ.Presented] {S : Set (WFF σ Γ 0)}
    (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S := by
  have hfresh : ∀ d n, Γ.RootFresh (.free (Canon.names (Ctx.Presented.bound Γ) d n)) :=
    fun _ _ => Ctx.Presented.fresh_bound _ (Nat.le_add_right _ _)
  let L₀ : WorldLang := WorldLang.const Γ (fun _ => .VTypeOne)
    (Canon.names (Ctx.Presented.bound Γ) 0) (Canon.names_injective _ _) (hfresh 0)
  let S₀ : Set ((L₀.pre []).Sentence σ) := {s | ∃ ψ ∈ S, s = ⟨0, ψ⟩}
  have hS₀ : StageSys.Consistent S₀ := by
    rintro m ⟨Δ', hΔ', p⟩
    refine hS Δ' (fun δ hδ => ?_) p
    obtain ⟨s, ⟨ψ, hψ, rfl⟩, hle, rfl⟩ := hΔ' δ hδ
    convert hψ using 1
    exact WFF.mono_refl _ _
  let w₀ : Canon.World σ (Ctx.Presented.bound Γ) :=
    Canon.World.ofHenkin 0 L₀ (fun _ => rfl) (fun _ d n _ => hfresh d n) S₀ hS₀
  exact ⟨Canon.model w₀, Model.indInvariant_of_eq fun _ _ h => h, w₀,
    Canon.canonEnv w₀ w₀ (0, 0), fun ψ hψ =>
    (Canon.truth w₀ w₀ (0, 0) ψ).mpr (WorldLang.subset_finalT S₀ ⟨ψ, hψ, rfl⟩)⟩

/-- ⭐**Strong completeness.** If a formula holds in every model, world and environment satisfying a
    set of premises, then it is derivable from finitely many of them. -/
theorem strong_completeness {Γ : Ctx} [Γ.Presented] {S : Set (WFF σ Γ 0)}
    {φ : WFF σ Γ 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      (∀ ψ ∈ S, M.sat env ψ) → M.sat env φ) :
    ∃ Δ : List (WFF σ Γ 0), (∀ ψ ∈ Δ, ψ ∈ S) ∧ Provable Δ φ := by
  by_contra hno
  -- The premises together with `¬φ` are consistent …
  have hcons : WFF.SetConsistent (insert φ.neg S) := by
    intro Δ hΔ p
    refine hno ⟨Δ.filter (· ≠ φ.neg), fun ψ hψ => ?_, Provable.byContra (Provable.mono ?_ p)⟩
    · obtain ⟨hψΔ, hne⟩ := List.mem_filter.mp hψ
      exact (Set.mem_insert_iff.mp (hΔ ψ hψΔ)).resolve_left (by simpa using hne)
    · intro θ hθ
      by_cases h : θ = φ.neg
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hθ, by simpa using h⟩)
  -- … so they have a model, in which `φ` fails.
  obtain ⟨M, hM, w, env, hsat⟩ := model_existence hcons
  exact hsat φ.neg (Set.mem_insert _ _)
    (hval M hM env (fun ψ hψ => hsat ψ (Set.mem_insert_of_mem _ hψ)))

/-- ⭐**Compactness.** A set of formulas in a presented context is satisfiable if every finite
    subset is — in models of any universe. -/
theorem compactness {Γ : Ctx} [Γ.Presented] {S : Set (WFF σ Γ 0)}
    (hfin : ∀ Δ : List (WFF σ Γ 0), (∀ ψ ∈ Δ, ψ ∈ S) →
      ∃ (M : Model.{u, v} σ) (_ : M.IndInvariant) (w : M.frame.W) (env : M.Env Γ w),
        ∀ ψ ∈ Δ, M.sat env ψ) :
    WFF.SetSatisfiable S := by
  refine model_existence fun Δ hΔ ⟨p⟩ => ?_
  obtain ⟨M, hM, w, env, hsat⟩ := hfin Δ hΔ
  exact Model.soundness p M hM env (Ctx.Presented.noProjLast Γ) hsat

end V12M
