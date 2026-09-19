import QML.QML_v12m_Completeness

/-!
# QML v12m — model existence, strong completeness and compactness

The canonical construction starts from an arbitrary consistent set of sentences (`World.ofHenkin`),
so completeness extends from sequents to sets of premises of any size.

* ⭐`model_existence`: every consistent set of formulas in a presented context has a model.
* ⭐`strong_completeness`: a formula true in every model of a set of premises is derivable from
  finitely many of them.
* ⭐`compactness`: a set of formulas is satisfiable if every finite subset is.

All three hold for every combination of the flags, over a countable signature.
-/

namespace V12M

variable [ModalSys]

universe u

variable {σ : Signature}

/-- A set of formulas is **consistent** when no finite list drawn from it derives `⊥`. -/
def WFF.SetConsistent {Γ : Ctx} (S : Set (WFF σ Γ 0)) : Prop :=
  ∀ Δ : List (WFF σ Γ 0), (∀ ψ ∈ Δ, ψ ∈ S) → ¬ Provable Δ .bot

/-- A set of formulas is **satisfiable** when some model, world and environment make it true. -/
def WFF.SetSatisfiable {Γ : Ctx} (S : Set (WFF σ Γ 0)) : Prop :=
  ∃ (M : Model.{0} σ) (w : M.frame.W) (env : M.Env Γ w), ∀ ψ ∈ S, M.sat env ψ

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐**Model existence.** Every consistent set of formulas in a presented context is satisfiable:
    the canonical model built over it, at its first world, in the canonical environment. -/
theorem model_existence {Γ : Ctx} [Γ.Presented] {S : Set (WFF σ Γ 0)}
    (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S := by
  have hfresh : ∀ d n, Γ.RootFresh (.free (Canon.names (Ctx.Presented.bound Γ) d n)) :=
    fun _ _ => Ctx.Presented.fresh _ (Nat.le_add_right _ _)
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
  exact ⟨Canon.model w₀, w₀, Canon.canonEnv w₀ w₀ (0, 0), fun ψ hψ =>
    (Canon.truth w₀ w₀ (0, 0) ψ).mpr (WorldLang.subset_finalT S₀ ⟨ψ, hψ, rfl⟩)⟩

/-- ⭐**Strong completeness.** If a formula holds in every model, world and environment satisfying a
    set of premises, then it is derivable from finitely many of them. -/
theorem strong_completeness {Γ : Ctx} [Γ.Presented] {S : Set (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (hval : ∀ (M : Model.{0} σ) {w : M.frame.W} (env : M.Env Γ w),
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
  obtain ⟨M, w, env, hsat⟩ := model_existence hcons
  exact hsat φ.neg (Set.mem_insert _ _)
    (hval M env (fun ψ hψ => hsat ψ (Set.mem_insert_of_mem _ hψ)))

/-- ⭐**Compactness.** A set of formulas in a presented context is satisfiable if every finite
    subset is — in models of any universe. -/
theorem compactness {Γ : Ctx} [Γ.Presented] {S : Set (WFF σ Γ 0)}
    (hfin : ∀ Δ : List (WFF σ Γ 0), (∀ ψ ∈ Δ, ψ ∈ S) →
      ∃ (M : Model.{u} σ) (w : M.frame.W) (env : M.Env Γ w), ∀ ψ ∈ Δ, M.sat env ψ) :
    WFF.SetSatisfiable S := by
  refine model_existence fun Δ hΔ ⟨p⟩ => ?_
  obtain ⟨M, w, env, hsat⟩ := hfin Δ hΔ
  exact Model.soundness p M env (Ctx.Presented.noProjLast Γ) hsat

end V12M
