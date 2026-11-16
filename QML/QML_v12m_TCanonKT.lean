import QML.QML_v12m_TCanonCompleteness
import QML.QML_v12m_GKEq

/-!
# QML v12m — KT and KDT with `Opt`: soundness and completeness, named

The general theorem (`OCanon.provable_iff_validT`) holds for any system `Opt` allows, strong T
included.  Here it is instantiated at the concrete systems, which confirms that its hypotheses are
met with T on:

* `ModalSys.KTOpt` (`QML_v12m_GKEq`, where GK's cut and Craig are stated for it): T and `Opt`;
* `ModalSys.KDTOpt`: T, D and `Opt`;
* `ModalSys.KTSOpt`: T, strong T and `Opt`.
-/

namespace V12M

/-- The system KDT with the box view of possible objects. -/
def ModalSys.KDTOpt : ModalSys :=
  { T := true, Four := false, TStrong := false, D := true, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := false, FiveStrong := false, Opt := true }

/-- KT with strong T and the box view of possible objects. -/
def ModalSys.KTSOpt : ModalSys :=
  { T := true, Four := false, TStrong := true, D := false, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := false, FiveStrong := false, Opt := true }

section KT

attribute [local instance] ModalSys.KTOpt

/-- ⭐**KT with `Opt` is sound and complete**: over a countable signature, a sequent in a presented
    context with no identity view opened at its top is provable exactly when it holds in every
    model. -/
theorem OCanon.provable_iff_valid_KT {σ : Signature} [Countable σ.FuncSyms]
    [Countable σ.RelSyms] {Γ : Ctx} [Γ.Presented] (hΓ : Γ.NoTopAt) {Δ : List (WFF σ Γ 0)}
    {φ : WFF σ Γ 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      Γ.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  OCanon.provable_iff_validT rfl hΓ

end KT

section KDT

attribute [local instance] ModalSys.KDTOpt

/-- ⭐**KDT with `Opt` is sound and complete**, in the same sense. -/
theorem OCanon.provable_iff_valid_KDT {σ : Signature} [Countable σ.FuncSyms]
    [Countable σ.RelSyms] {Γ : Ctx} [Γ.Presented] (hΓ : Γ.NoTopAt) {Δ : List (WFF σ Γ 0)}
    {φ : WFF σ Γ 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      Γ.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  OCanon.provable_iff_validT rfl hΓ

end KDT

section KTS

attribute [local instance] ModalSys.KTSOpt

/-- ⭐**KT with strong T and `Opt` is sound and complete**, in the same sense. -/
theorem OCanon.provable_iff_valid_KTS {σ : Signature} [Countable σ.FuncSyms]
    [Countable σ.RelSyms] {Γ : Ctx} [Γ.Presented] (hΓ : Γ.NoTopAt) {Δ : List (WFF σ Γ 0)}
    {φ : WFF σ Γ 0} :
    Provable Δ φ ↔ ∀ (M : Model.{0, 0} σ), M.IndInvariant → ∀ {w : M.frame.W} (env : M.Env Γ w),
      Γ.NoProjLast → (∀ ψ ∈ Δ, M.sat env ψ) → M.sat env φ :=
  OCanon.provable_iff_validT rfl hΓ

end KTS

end V12M
