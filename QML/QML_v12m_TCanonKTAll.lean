import QML.QML_v12m_TCanonOpenT

/-!
# QML v12m — KT and KDT with `Opt`: soundness and completeness for every presented context

`provable_iff_validO` (route 2, `QML_v12m_TCanonOpenT`) at the concrete systems `ModalSys.KTOpt`
and `ModalSys.KDTOpt`.
-/

namespace V12M

section KT

attribute [local instance] ModalSys.KTOpt

/-- ⭐**KT with `Opt` is sound and complete for every presented context.** -/
theorem provable_iff_validO_KT {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
    {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
    Provable Δ φ ↔ ValidO Δ φ :=
  provable_iff_validO rfl

end KT

section KDT

attribute [local instance] ModalSys.KDTOpt

/-- ⭐**KDT with `Opt` is sound and complete for every presented context.** -/
theorem provable_iff_validO_KDT {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
    {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
    Provable Δ φ ↔ ValidO Δ φ :=
  provable_iff_validO rfl

end KDT

end V12M
