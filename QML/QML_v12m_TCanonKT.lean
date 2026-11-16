import QML.QML_v12m_TCanonCompleteness
import QML.QML_v12m_GKEq

/-!
# QML v12m — KT and KDT with `Opt`: soundness and completeness, named

The general theorem (`OCanon.provable_iff_validT`) holds for any system `Opt` allows with strong T
off.  Here it is instantiated at the concrete systems, which confirms that its hypotheses are met
with T on:

* `ModalSys.KTOpt` (`QML_v12m_GKEq`, where GK's cut and Craig are stated for it): T and `Opt`;
* `ModalSys.KDTOpt`: T, D and `Opt`.
-/

namespace V12M

/-- The system KDT with the box view of possible objects. -/
def ModalSys.KDTOpt : ModalSys :=
  { T := true, Four := false, TStrong := false, D := true, DStrong := false, B := false,
    BStrong := false, BStrongW := false, FourStrong := false, FourStrongW := false,
    Five := false, FiveStrong := false, Opt := true }

instance ModalSys.weakTO_KT : @ModalSys.WeakTO ModalSys.KTOpt :=
  @ModalSys.WeakTO.mk ModalSys.KTOpt fun _ => rfl

instance ModalSys.weakTO_KDT : @ModalSys.WeakTO ModalSys.KDTOpt :=
  @ModalSys.WeakTO.mk ModalSys.KDTOpt fun _ => rfl

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

end V12M
