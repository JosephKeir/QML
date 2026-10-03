import QML.QML_v12m_BInd
import QML.QML_v12m_BLimit

/-!
# QML v12m — completeness for weak B

With 4 off and strong T off (`ModalSys.NoFourNoTS`: weak T allowed, D and strong D free), and with
the weak B rule: ⭐`completenessB`, a sequent in a context of declared variables (`ctxOf l₀`, the
root world's starting language) valid in every model is provable.  Its negation extends to a
maximal consistent theory `M₀`; the network grown from `M₀` gives the canonical data (`bdata`),
whose model satisfies at the root exactly the root's theory (`BData.truth`) and is a model proper
(`BData.indInvariant`), and the root's theory contains `M₀`.

A presented context whose presentation uses `boxIn` or `diaIn` is not of this shape: its variables
are view items, not roots.  `QML_v12m_BRename` and `QML_v12m_BFlat` reduce those to this theorem
(`completenessB_presented`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoFourNoTS]

/-- ⭐**Completeness for weak B**: in a context of declared variables, a sequent that holds in
    every model, at every world, in every environment, is provable. -/
theorem completenessB (hB : ModalSys.B = true) {l₀ : List VarType} {Δ : List (WFF σ (ctxOf l₀) 0)}
    {φ : WFF σ (ctxOf l₀) 0}
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
  let B := bdata hB hM₀
  let s : B.W := B.actual
  have hle : (ctxOf l₀).Le ((B.w s).ctx 0) :=
    ctxOf_le_of_suffix (lang_suffix hB (complete_spec hS).2 (Nat.zero_le _) trivial)
  let env₀ : B.model.Env (ctxOf l₀) s := fun v T hv => B.canonEnv s 0 v T (hle v T hv)
  have hag : Model.Env.Agree hle env₀ (B.canonEnv s 0) := fun _ _ _ => rfl
  have hg := (ext_net hB hM₀ (Nat.zero_le (birth (complete S) s.2 + 0))).grows [] trivial
  have hmem : ∀ ψ ∈ S, WFF.mono hle ψ ∈ (B.w s).M 0 := fun ψ hψ =>
    hg.sub ψ (show ψ ∈ ((net (complete S) 0).st []).M from hSM hψ)
  have hsat := hval B.model BData.indInvariant env₀
    (Ctx.Presented.noProjLast _) fun ψ hψ =>
    (Model.sat_mono hag ψ).mp ((BData.truth s 0 _).mpr (hmem ψ (Or.inl hψ)))
  have hφ := (BData.truth s 0 _).mp ((Model.sat_mono hag φ).mpr hsat)
  exact ((B.w s).mcs 0).neg_mem_iff.mp (hmem φ.neg (Or.inr rfl)) hφ

/-- ⭐**Soundness and completeness for weak B**, in a context of declared variables. -/
theorem provable_iff_validB (hB : ModalSys.B = true) {l₀ : List VarType}
    {Δ : List (WFF σ (ctxOf l₀) 0)}
    {φ : WFF σ (ctxOf l₀) 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant →
      ∀ {w : M.frame.W} (env : M.Env (ctxOf l₀) w),
      (ctxOf l₀).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  ⟨fun ⟨p⟩ M hM _ env => Model.soundness p M hM env (Ctx.Presented.tame _), completenessB hB⟩

end BArrow

end V12M
