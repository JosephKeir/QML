import QML.QML_v12m_BInd
import QML.QML_v12m_BLimit
import QML.QML_v12m_BRetCongr

/-!
# QML v12m — completeness for B

With 4 off (`ModalSys.NoFour`: T and D free, each in either strength; strong B with T off), and
with the weak B rule: ⭐`completenessB`, a sequent in a context of declared variables (`ctxOf l₀`,
the root world's starting language) valid in every model is provable.  Its negation extends to a
maximal consistent theory `M₀`; the network grown from `M₀` gives the canonical data — weak B's
(`bdata`) or, under strong B, strong B's (`bdataS`) — whose model satisfies at the root exactly
the root's theory (`BData.truth`) and is a model proper (`BData.indInvariant`), and the root's
theory contains `M₀` (⭐`exists_canonB`).

A presented context whose presentation uses `boxIn` or `diaIn` is not of this shape: its variables
are view items, not roots.  `QML_v12m_BRename` and `QML_v12m_BFlat` reduce those to this theorem
(`completenessB_presented`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoFour]

/-- ⭐⭐**B's canonical model over a maximal consistent theory**: a model proper whose root
    satisfies, at its first stage, exactly its theory, which contains `M₀`.  Weak B's network
    (`bdata`), or strong B's (`bdataS`, T off by `NoFour`) with its truth cases
    (`bdataS_strongTruth`) and congruence (`BData.retCongr`). -/
theorem exists_canonB (hB : ModalSys.B = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (hM₀ : Theory.IsMCS M₀) :
    ∃ (B : BData σ) (s : B.W) (hle : (ctxOf l₀).Le ((B.w s).ctx 0)),
      B.model.IndInvariant ∧
      (∀ φ : WFF σ ((B.w s).ctx 0) 0, B.model.sat (B.canonEnv s 0) φ ↔ φ ∈ (B.w s).M 0) ∧
      ∀ ψ ∈ M₀, WFF.mono hle ψ ∈ (B.w s).M 0 := by
  cases hBS : ModalSys.BStrong with
  | false =>
      let B := bdata (weakChain hB hM₀) hBS
      have hST : ∀ hS : ModalSys.BStrong = true, B.StrongTruth hS :=
        fun hS => absurd (hBS.symm.trans hS) (by decide)
      let s : B.W := B.actual
      have hg := (ext_net hB hM₀ (Nat.zero_le (birth (weakChain hB hM₀) s.2 + 0))).grows [] trivial
      exact ⟨B, s, ctxOf_le_of_suffix ((weakChain hB hM₀).lang_suffix (Nat.zero_le _) trivial),
        BData.indInvariant hST fun hS => absurd (hBS.symm.trans hS) (by decide),
        BData.truth hST s 0, fun ψ hψ => hg.sub ψ (show ψ ∈ ((net M₀ 0).st []).M from hψ)⟩
  | true =>
      have hT := ModalSys.NoFour.noTStrong hBS
      let C := strongChainS hBS hB hT hM₀
      let B := bdataS C hT
      let s : B.W := B.actual
      have hg := (ext_netS hBS hB hT hM₀
        (Nat.zero_le (birth C.toFairChain s.2 + 0))).grows [] trivial
      exact ⟨B, s, ctxOf_le_of_suffix (C.lang_suffix (Nat.zero_le _) trivial),
        bdataS_indInvariant C hT hB, BData.truth (bdataS_strongTruth C hT hB) s 0,
        fun ψ hψ => hg.sub ψ (show ψ ∈ ((netS hBS M₀ 0).st []).M from hψ)⟩

/-- ⭐**Completeness for B** (weak, or strong with T off): in a context of declared variables, a
    sequent that holds in every model, at every world, in every environment, is provable. -/
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
  obtain ⟨B, s, hle, hInv, htruth, hmem₀⟩ := exists_canonB hB hM₀
  let env₀ : B.model.Env (ctxOf l₀) s := fun v T hv => B.canonEnv s 0 v T (hle v T hv)
  have hag : Model.Env.Agree hle env₀ (B.canonEnv s 0) := fun _ _ _ => rfl
  have hmem : ∀ ψ ∈ S, WFF.mono hle ψ ∈ (B.w s).M 0 := fun ψ hψ => hmem₀ ψ (hSM hψ)
  have hsat := hval B.model hInv env₀ (Ctx.Presented.noProjLast _) fun ψ hψ =>
    (Model.sat_mono hag ψ).mp ((htruth _).mpr (hmem ψ (Or.inl hψ)))
  have hφ := (htruth _).mp ((Model.sat_mono hag φ).mpr hsat)
  exact ((B.w s).mcs 0).neg_mem_iff.mp (hmem φ.neg (Or.inr rfl)) hφ

/-- ⭐**Soundness and completeness for B**, in a context of declared variables. -/
theorem provable_iff_validB (hB : ModalSys.B = true) {l₀ : List VarType}
    {Δ : List (WFF σ (ctxOf l₀) 0)}
    {φ : WFF σ (ctxOf l₀) 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant →
      ∀ {w : M.frame.W} (env : M.Env (ctxOf l₀) w),
      (ctxOf l₀).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  ⟨fun ⟨p⟩ M hM _ env => Model.soundness p M hM env (Ctx.Presented.tame _), completenessB hB⟩

end BArrow

end V12M
