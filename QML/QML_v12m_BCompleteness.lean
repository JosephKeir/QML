import QML.QML_v12m_BTruth
import QML.QML_v12m_BLimit

/-!
# QML v12m — completeness for weak B

Without T and 4, and with the weak B rule: ⭐`completenessB`, a sequent of closed formulas valid in
every model is provable.  Its negation extends to a maximal consistent theory `M₀`; the network
grown from `M₀` gives the canonical data (`bdata`), whose model satisfies at the root exactly the
root's theory (`BData.truth`), and the root's theory contains `M₀`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour]

/-- ⭐**Completeness for weak B**: a sequent of closed formulas that holds in every model, at every
    world, is provable. -/
theorem completenessB (hB : ModalSys.B = true) {Δ : List (WFF σ (ctxOf []) 0)}
    {φ : WFF σ (ctxOf []) 0}
    (hval : ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env (ctxOf []) w),
      (ctxOf []).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ) :
    Provable Δ φ := by
  by_contra hnp
  let S : Set (WFF σ (ctxOf []) 0) := {ψ | ψ ∈ Δ} ∪ {φ.neg}
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
  have hle : (ctxOf []).Le ((B.w s).ctx 0) := ctxOf_le_of_suffix List.nil_suffix
  let env₀ : B.model.Env (ctxOf []) s := fun v T hv => B.canonEnv s 0 v T (hle v T hv)
  have hag : Model.Env.Agree hle env₀ (B.canonEnv s 0) := fun _ _ _ => rfl
  have hg := (ext_net hB hM₀ (Nat.zero_le (birth (complete S) s.2 + 0))).grows [] trivial
  have hmem : ∀ ψ ∈ S, WFF.mono hle ψ ∈ (B.w s).M 0 := fun ψ hψ =>
    hg.sub ψ (show ψ ∈ ((net (complete S) 0).st []).M from hSM hψ)
  have hsat := hval B.model env₀ (Ctx.Presented.noProjLast _) fun ψ hψ =>
    (Model.sat_mono hag ψ).mp ((BData.truth s 0 _).mpr (hmem ψ (Or.inl hψ)))
  have hφ := (BData.truth s 0 _).mp ((Model.sat_mono hag φ).mpr hsat)
  exact ((B.w s).mcs 0).neg_mem_iff.mp (hmem φ.neg (Or.inr rfl)) hφ

/-- ⭐**Soundness and completeness for weak B**, for sequents of closed formulas. -/
theorem provable_iff_validB (hB : ModalSys.B = true) {Δ : List (WFF σ (ctxOf []) 0)}
    {φ : WFF σ (ctxOf []) 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ) {w : M.frame.W} (env : M.Env (ctxOf []) w),
      (ctxOf []).NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  ⟨fun ⟨p⟩ => Model.soundness p, completenessB hB⟩

end BArrow

end V12M
