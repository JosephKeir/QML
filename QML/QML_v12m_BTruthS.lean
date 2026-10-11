import QML.QML_v12m_BRetOut

/-!
# QML v12m — B's canonical model: the strong B cases of the truth lemma (T off)

The truth lemma (`BData.truth`) takes its `Back` and returning-possibility cases as a hypothesis
(`BData.StrongTruth`).  Here they are assembled from both directions of each case:

* `Back` (`mem_back_of_sat`, `sat_back_of_mem`), its carrier `□□A` or `◇□A` read as a body;
* `ret` and `retx` at necessary shapes (`mem_ret_of_sat_nec`, `mem_retx_of_sat`,
  `sat_retS_nec_of_mem`, `sat_retxS_nec_of_mem`) and at witnessed shapes
  (`mem_ret_of_sat_wit`, `mem_retx_of_sat_wit`, `sat_retS_wit_of_mem`, `sat_retxS_wit_of_mem`).

⭐`BData.strongTruth_of` does this from the fields a `BData` needs, and ⭐`bdataS_strongTruth`
supplies them for the limit of a strong chain.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

namespace BData

variable {B : BData σ}

/-- ⭐**The strong B cases of the truth lemma**, from the fields of the canonical data. -/
theorem strongTruth_of (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hInj : B.ImgInj) (hCx : B.CxFresh) (hRI : B.RetIn hS) (hRIX : B.RetInX hS)
    (hRW : B.RetInW hS) (hRWX : B.RetInWX hS) (hRO : B.RetOut hS) (hROX : B.RetOutX hS)
    (hROD : B.RetOutD hS) (hROXD : B.RetOutXD hS) : B.StrongTruth hS where
  back := by
    intro s i L A b a c t IH
    refine ⟨fun h => ?_, sat_back_of_mem hS c t⟩
    cases L with
    | nec =>
        match c with
        | .boxtm (.boxtm bd) =>
            exact mem_back_of_sat hS hB hInj hCx .nec bd t (fun K φ hφ => IH s K φ hφ) h
    | pos =>
        match c with
        | .diatm y hy (.boxtm bd) =>
            exact mem_back_of_sat hS hB hInj hCx (.pos y hy) bd t (fun K φ hφ => IH s K φ hφ) h
  retS := by
    intro s i S a t Φ IH
    cases S with
    | nec N => exact ⟨mem_ret_of_sat_nec hS hInj hRI t Φ IH, sat_retS_nec_of_mem hS hRO t Φ IH⟩
    | wit N Z =>
        exact ⟨mem_ret_of_sat_wit hS hInj hRW t Φ IH, sat_retS_wit_of_mem hS hROD t Φ IH⟩
  retxS := by
    intro s i y hy S a t Φ IH
    cases S with
    | nec N =>
        exact ⟨mem_retx_of_sat hS hInj hRIX hy t Φ IH, sat_retxS_nec_of_mem hS hROX hy t Φ IH⟩
    | wit N Z =>
        exact ⟨mem_retx_of_sat_wit hS hInj hRWX hy t Φ IH,
          sat_retxS_wit_of_mem hS hROXD hy t Φ IH⟩

end BData

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀)

/-- ⭐⭐**The limit of a strong chain has the strong B cases of the truth lemma** (T off). -/
theorem bdataS_strongTruth (hT : ModalSys.T = false) (hB : ModalSys.B = true) :
    ∀ hS' : ModalSys.BStrong = true, (bdataS C hT).StrongTruth hS' := fun _ =>
  BData.strongTruth_of hS hB (bdataS_imgInj C hT) (bdataS_cxFresh C hT) (bdataS_retIn C hT)
    (bdataS_retInX C hT) (bdataS_retInW C hT) (bdataS_retInWX C hT) (bdataS_retOut C hT)
    (bdataS_retOutX C hT) (bdataS_retOutD C hT) (bdataS_retOutXD C hT)

end BArrow

end V12M
