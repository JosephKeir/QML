import QML.QML_v12m_BDecode
import QML.QML_v12m_BLimit

/-!
# QML v12m — the limit has injective images

The limit of any fair chain satisfies the T-free decoder's hypothesis (`BData.ImgInj`): every
network of the chain has injective images (`FairChain.inj`), and the limit's images agree with a
network's where they are committed (`limg_inj`).  So without T, tags determine annotations in
the canonical model at every world with an arrow out (`bdata_ann_eq_of_rden_noT`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour] {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- ⭐The limit of a fair chain has injective images. -/
theorem bdata_imgInj (C : FairChain M₀) : (bdata C).ImgInj :=
  fun h i _ _ hr hr' e => limg_inj C h i hr hr' e

/-- ⭐⭐**Tags determine annotations in the canonical model, without T**: two terms of a world's
    language with one denotation have one annotation, at a world with an arrow out. -/
theorem bdata_ann_eq_of_rden_noT (C : FairChain M₀) (hT : ModalSys.T = false)
    (hSh : ModalSys.shaped = true) {s : (bdata C).W} {i : ℕ} (harr : ∃ t, (bdata C).R s t)
    {A : VarType} {a a' : Ann A} (t : Term σ (((bdata C).w s).ctx i) A a)
    (t' : Term σ (((bdata C).w s).ctx i) A a')
    (h : (bdata C).rden s i (Ctx.Le.refl _) t = (bdata C).rden s i (Ctx.Le.refl _) t') :
    a = a' :=
  BData.ann_eq_of_rden_ctx_noT hT hSh (bdata_imgInj C) harr t t' h

end BArrow

end V12M
