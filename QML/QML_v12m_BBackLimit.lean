import QML.QML_v12m_BBackTruth
import QML.QML_v12m_BBackTail
import QML.QML_v12m_BDecodeLimit

/-!
# QML v12m — the limit has fresh witness arrows

The limit of any fair chain with children satisfies `BData.CxFresh`: a true `◇_y ⊤` at a stage
gets a witness child made after the stage's variables were committed (`lexX_fresh`), so they reach
the child under the identity, and its content variable is the parent's length then, past all of
them.  Strong B's limit has it from its existence data (`LimitEx.cxFresh`).  With
`bdata_imgInj` this is what the row-2 `back` case asks of the canonical data
(`BData.mem_back_of_sat`).

* ⭐`bdata_cxFresh`, `bdataS_cxFresh`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour] {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

section Fair

variable (C : FairChain M₀)

/-- ⭐The limit of a fair chain has fresh witness arrows. -/
theorem bdata_cxFresh (hc : Children C.net) (hW : ModalSys.BStrong = false) :
    (bdata C hc hW).CxFresh :=
  fun hy h => lexX_fresh C hc _ _ _ _ hy h

end Fair

section Strong

variable {hS : ModalSys.BStrong = true} (C : StrongChain hS M₀)
  (E : LimitEx C.toFairChain)

/-- Strong B's canonical data has fresh witness arrows. -/
theorem bdataS_cxFresh : (bdataS C E).CxFresh :=
  fun hy h => E.cxFresh _ _ _ _ hy h

/-- Strong B's canonical data has injective images. -/
theorem bdataS_imgInj : (bdataS C E).ImgInj :=
  fun h i _ _ hr hr' e => limg_inj C.toFairChain h i hr hr' e

end Strong

end BArrow

end V12M
