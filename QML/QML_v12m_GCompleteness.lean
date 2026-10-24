import QML.QML_v12m_GTruth

/-!
# QML v12m — completeness for 4 on the growing tree

With 4 on and T and B off (`ModalSys.NoT`, `ModalSys.NoSym`; D free in either strength, strong 4
in either or both forms): ⭐`completenessG`, a sequent in a context of declared variables
(`ctxOf l₀`, the root's starting language) valid in every model is provable.  Its negation extends
to a maximal consistent theory `M₀`; the growing tree from `M₀` gives the canonical model
(`gmodel`), a model proper since its `Ind` is equality (`gmodel_indInvariant`), whose root
satisfies at its first stage exactly the root's theory (`gtruth`), which contains `M₀`
(⭐`exists_canonG`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoT]
  [ModalSys.NoSym]

/-- The canonical model is a model proper: its `Ind` is equality. -/
theorem gmodel_indInvariant (hF : ModalSys.Four = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (hM₀ : Theory.IsMCS M₀) : (gmodel hF hM₀).IndInvariant :=
  Model.indInvariant_of_eq (fun _ _ h => h) fun hS => (absBS hS).elim

/-- ⭐⭐**The growing tree's canonical model over a maximal consistent theory**: its root
    satisfies, at its first stage, exactly its theory, which contains `M₀`. -/
theorem exists_canonG (hF : ModalSys.Four = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (hM₀ : Theory.IsMCS M₀) :
    ∃ hle : (ctxOf l₀).Le (ctxOf (glat (groot hF M₀) 0)),
      (∀ φ : WFF σ (ctxOf (glat (groot hF M₀) 0)) 0,
        (gmodel hF hM₀).sat (gcanonEnv hM₀ (groot hF M₀) 0) φ ↔
          φ ∈ (gw hM₀ (groot hF M₀)).M 0) ∧
      ∀ ψ ∈ M₀, WFF.mono hle ψ ∈ (gw hM₀ (groot hF M₀)).M 0 := by
  have hg := (ext_gnet hF hM₀ (Nat.zero_le (gbirth hF M₀ (groot hF M₀).2 + 0))).grows [] trivial
  exact ⟨ctxOf_le_of_suffix hg.suf, gtruth (groot hF M₀) 0,
    fun ψ hψ => hg.sub ψ (show ψ ∈ ((gnet hF M₀ 0).st []).M from hψ)⟩

/-- ⭐**Completeness for 4** (T and B off; D and strong 4 free): in a context of declared
    variables, a sequent that holds in every model, at every world, in every environment, is
    provable. -/
theorem completenessG (hF : ModalSys.Four = true) {l₀ : List VarType}
    {Δ : List (WFF σ (ctxOf l₀) 0)} {φ : WFF σ (ctxOf l₀) 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant →
      ∀ {w : M.frame.W} (env : M.Env (ctxOf l₀) w),
      (ctxOf l₀).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  by_contra hnp
  let S : Set (WFF σ (ctxOf l₀) 0) := {ψ | ψ ∈ Δ} ∪ {φ.neg}
  have hS : Theory.Consistent S := by
    rintro ⟨L, hL, p⟩
    refine hnp (Provable.byContra (Provable.mono (fun δ hδ => ?_) p))
    rcases hL δ hδ with h | h
    · exact List.mem_cons_of_mem _ h
    · rw [Set.mem_singleton_iff.mp h]
      exact List.mem_cons_self
  obtain ⟨hSM, hM₀⟩ := complete_spec hS
  obtain ⟨hle, htruth, hmem₀⟩ := exists_canonG hF hM₀
  let env₀ : (gmodel hF hM₀).Env (ctxOf l₀) (groot hF _) := fun v T hv =>
    gcanonEnv hM₀ (groot hF _) 0 v T (hle v T hv)
  have hag : Model.Env.Agree hle env₀ (gcanonEnv hM₀ (groot hF _) 0) := fun _ _ _ => rfl
  have hmem : ∀ ψ ∈ S, WFF.mono hle ψ ∈ (gw hM₀ (groot hF _)).M 0 :=
    fun ψ hψ => hmem₀ ψ (hSM hψ)
  have hsat := hval (gmodel hF hM₀) (gmodel_indInvariant hF hM₀) env₀
    (Ctx.Presented.noProjLast _) fun ψ hψ =>
      (Model.sat_mono hag ψ).mp ((htruth _).mpr (hmem ψ (Or.inl hψ)))
  have hφ := (htruth _).mp ((Model.sat_mono hag φ).mpr hsat)
  exact ((gw hM₀ (groot hF _)).mcs 0).neg_mem_iff.mp (hmem φ.neg (Or.inr rfl)) hφ

/-- ⭐**Soundness and completeness for 4** (T and B off), in a context of declared variables. -/
theorem provable_iff_validG (hF : ModalSys.Four = true) {l₀ : List VarType}
    {Δ : List (WFF σ (ctxOf l₀) 0)} {φ : WFF σ (ctxOf l₀) 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant →
      ∀ {w : M.frame.W} (env : M.Env (ctxOf l₀) w),
      (ctxOf l₀).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  ⟨fun ⟨p⟩ M hM _ env => Model.soundness p M hM env (Ctx.Presented.tame _), completenessG hF⟩

end GArrow

end V12M
