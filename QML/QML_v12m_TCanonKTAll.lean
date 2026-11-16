import QML.QML_v12m_TCanonOpenT

/-!
# QML v12m — KT, KDT and strong KT with `Opt`: complete for every presented context

`provable_iff_validO` (route 2, `QML_v12m_TCanonOpenT`) at the concrete systems `ModalSys.KTOpt`,
`ModalSys.KDTOpt` and `ModalSys.KTSOpt` (strong T).
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

section KTS

attribute [local instance] ModalSys.KTSOpt

/-- ⭐**KT with strong T and `Opt` is sound and complete for every presented context.** -/
theorem provable_iff_validO_KTS {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
    {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} {φ : WFF σ Γ 0} :
    Provable Δ φ ↔ ValidO Δ φ :=
  provable_iff_validO rfl

end KTS

end V12M
