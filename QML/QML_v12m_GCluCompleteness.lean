import QML.QML_v12m_GCluInd
import QML.QML_v12m_GFlat

/-!
# QML v12m — completeness for K45, KD45 and S5: the cluster model

With 4, weak 5 and both lifts of 4 on (`CluFlags`; D and T in either strength, weak B under T,
strong B off), the
cluster model over a maximal consistent theory satisfies it at the root (⭐`exists_canonC`), so
a consistent set is satisfiable (`model_existenceC`), and every well-formed presented context
has the metatheorems: strong completeness (`strong_completenessC`), completeness
(⭐`completenessC_presented`) and compactness (`compactnessC`).  Presentations are flattened
into world languages by the growing tree's child edges (`CtxExpr.gchain`), as for 4.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐⭐**The cluster model over a maximal consistent theory**: its root satisfies, at its first
    stage, exactly its theory, which contains `M₀`. -/
theorem exists_canonC (hF : ModalSys.Four = true) (hX : CluFlags) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (hM₀ : Theory.IsMCS M₀) :
    ∃ hle : (ctxOf l₀).Le (ctxOf (glat (groot hF M₀) 0)),
      (∀ φ : WFF σ (ctxOf (glat (groot hF M₀) 0)) 0,
        (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX (groot hF M₀) 0) φ ↔
          φ ∈ (gw hM₀ (groot hF M₀)).M 0) ∧
      ∀ ψ ∈ M₀, WFF.mono hle ψ ∈ (gw hM₀ (groot hF M₀)).M 0 := by
  have hg := (ext_gnet hF hM₀ (Nat.zero_le (gbirth hF M₀ (groot hF M₀).2 + 0))).grows [] trivial
  exact ⟨ctxOf_le_of_suffix hg.suf, ctruth hX (groot hF M₀) 0,
    fun ψ hψ => hg.sub ψ (show ψ ∈ ((gnet hF M₀ 0).st []).M from hψ)⟩

/-- Model existence at a world language: the cluster model over a maximal consistent extension
    satisfies the set at its root. -/
theorem model_existenceC_ctxOf (hF : ModalSys.Four = true) (hX : CluFlags) {l₀ : List VarType}
    {S : Set (WFF σ (ctxOf l₀) 0)} (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S := by
  obtain ⟨hSM, hM₀⟩ := complete_spec (setConsistent_iff.mp hS)
  obtain ⟨hle, htruth, hmem₀⟩ := exists_canonC hF hX hM₀
  have hag : Model.Env.Agree hle
      (fun v T hv => ccanonEnv hM₀ hX (groot hF _) 0 v T (hle v T hv))
      (ccanonEnv hM₀ hX (groot hF _) 0) := fun _ _ _ => rfl
  exact ⟨cmodel hF hM₀ hX, cmodel_indInvariant hM₀ hX hF, groot hF _,
    fun v T hv => ccanonEnv hM₀ hX (groot hF _) 0 v T (hle v T hv),
    fun ψ hψ => (Model.sat_mono hag ψ).mp ((htruth _).mpr (hmem₀ ψ (hSM hψ)))⟩

/-- ⭐**Model existence for K45, KD45 and S5** in every presented context whose presentation is
    well-formed. -/
theorem model_existenceC (hF : ModalSys.Four = true) (hX : CluFlags) (e : CtxExpr) (he : e.Wf)
    {S : Set (WFF σ e.denote 0)} (hS : WFF.SetConsistent S) : WFF.SetSatisfiable S :=
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  ((e.gchain hF he.1 he.2).2.toFlat).setSatisfiable
    (model_existenceC_ctxOf hF hX (((e.gchain hF he.1 he.2).2.toFlat).setConsistent hS))

/-- ⭐**Strong completeness for K45, KD45 and S5**: a formula true in every model, world and
    environment satisfying a set of premises is derivable from finitely many of them. -/
theorem strong_completenessC (hF : ModalSys.Four = true) (hX : CluFlags) (e : CtxExpr)
    (he : e.Wf) {S : Set (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env e.denote w),
      (∀ ψ ∈ S, M.sat env ψ) → M.sat env φ) :
    ∃ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) ∧ Provable Δ φ := by
  by_contra hno
  have hcons : WFF.SetConsistent (insert φ.neg S) := by
    intro Δ hΔ p
    refine hno ⟨Δ.filter (· ≠ φ.neg), fun ψ hψ => ?_, Provable.byContra (Provable.mono ?_ p)⟩
    · obtain ⟨hψΔ, hne⟩ := List.mem_filter.mp hψ
      exact (Set.mem_insert_iff.mp (hΔ ψ hψΔ)).resolve_left (by simpa using hne)
    · intro θ hθ
      by_cases h : θ = φ.neg
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hθ, by simpa using h⟩)
  obtain ⟨M, hM, w, env, hsat⟩ := model_existenceC hF hX e he hcons
  exact hsat φ.neg (Set.mem_insert _ _)
    (hval M hM env fun ψ hψ => hsat ψ (Set.mem_insert_of_mem _ hψ))

/-- ⭐**Completeness for K45, KD45 and S5** in every presented context whose presentation is
    well-formed: a sequent valid in every model is provable. -/
theorem completenessC_presented (hF : ModalSys.Four = true) (hX : CluFlags) (e : CtxExpr)
    (he : e.Wf) {Δ : List (WFF σ e.denote 0)} {φ : WFF σ e.denote 0}
    (hval : ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W}
      (env : M.Env e.denote w),
      e.denote.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  obtain ⟨Δ', hΔ', p⟩ := strong_completenessC hF hX e he (S := {ψ | ψ ∈ Δ})
    fun M hM _ env hS => hval M hM env (Ctx.Presented.noProjLast _) hS
  exact Provable.mono hΔ' p

/-- ⭐**Compactness for K45, KD45 and S5**: a set of formulas is satisfiable when every finite subset
    is — in models of any universe. -/
theorem compactnessC (hF : ModalSys.Four = true) (hX : CluFlags) (e : CtxExpr) (he : e.Wf)
    {S : Set (WFF σ e.denote 0)}
    (hfin : ∀ Δ : List (WFF σ e.denote 0), (∀ ψ ∈ Δ, ψ ∈ S) →
      ∃ (M : Model.{u, v} σ) (_ : M.IndInvariant) (w : M.frame.W) (env : M.Env e.denote w),
        ∀ ψ ∈ Δ, M.sat env ψ) :
    WFF.SetSatisfiable S := by
  letI : e.denote.Presented := ⟨e, he.1, rfl⟩
  refine model_existenceC hF hX e he fun Δ hΔ ⟨p⟩ => ?_
  obtain ⟨M, hM, w, env, hsat⟩ := hfin Δ hΔ
  exact Model.soundness p M hM env (Ctx.Presented.tame _) (Ctx.Presented.noProjLast _) hsat

end GArrow

end V12M
