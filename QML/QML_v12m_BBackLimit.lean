import QML.QML_v12m_BBackTruth
import QML.QML_v12m_BBackTail
import QML.QML_v12m_BDecodeLimit

/-!
# QML v12m — the limit has fresh witness arrows

The limit of any fair chain satisfies `BData.CxFresh`: a true `◇_y ⊤` at a stage gets a witness
child (`child_dia`) made after the stage's variables were committed, so they reach the child under
the identity, and its content variable is the parent's length then, past all of them.  With
`bdata_imgInj` this is what the row-2 `back` case asks of the canonical data
(`BData.mem_back_of_sat`).

* ⭐`lexX_fresh`, ⭐`bdata_cxFresh`, `bdataS_cxFresh`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour] {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

section Fair

variable (C : FairChain M₀)

/-- ⭐A true `◇_x ⊤` has a witness edge whose content variable is no image of the stage's
    variables: the child made for it sees them under the identity, below its content. -/
theorem lexX_fresh (s : LW C) (i : ℕ) (x : VarSymb) (X : VarType)
    (hx : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (hψ : WFF.dia x ⟨X, hx⟩ (.top : WFF σ _ 0) ∈ ((C.net (birth C s.2 + i)).st s.1).M) :
    ∃ t : LW C, lkd C s t = some (x, X) ∧ ∀ r < (lat s i).length, limg C s t r ≠ lcx C s t := by
  classical
  obtain ⟨m, _, hsuf, X', hX, M', hnot, hlive, hst, hkind, hcxe, hfcl, hfimg, hmem⟩ :=
    C.child_dia (live_birth C s.2 (Nat.le_add_right _ i)) hψ
  obtain rfl : X' = X := by
    have h1 := (ctxOf_le_of_suffix hsuf).ref hx
    rw [hX] at h1
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1
  let t : LW C := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have hbt' : birth C t.2 ≤ m + 1 := birth_le t.2 hlive
  have hkd : lkd C s t = some (x, X') := by
    rw [lkd, if_pos ⟨_, hc⟩, ← kind_at C t hbt']
    exact hkind
  have hlcx : lcx C s t = ((C.net m).st s.1).l.length := by
    rw [lcx, if_pos ⟨_, hc⟩]
    exact (cx_at C t hbt').symm.trans hcxe
  refine ⟨t, hkd, fun r hr => ?_⟩
  have hr' : r < ((C.net m).st s.1).l.length := lt_of_lt_of_le hr hsuf.length_le
  have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
    rw [hc, hfcl]
    exact hr'
  rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C hlive hlen, hfimg, hlcx]
  exact Nat.ne_of_lt hr'

/-- ⭐The limit of a fair chain has fresh witness arrows. -/
theorem bdata_cxFresh (hW : ModalSys.BStrong = false) : (bdata C hW).CxFresh :=
  fun hy h => lexX_fresh C _ _ _ _ hy h

end Fair

section Strong

variable {hS : ModalSys.BStrong = true} (C : StrongChain hS M₀)

/-- Strong B's canonical data has fresh witness arrows. -/
theorem bdataS_cxFresh : (bdataS C).CxFresh :=
  fun hy h => lexX_fresh C.toFairChain _ _ _ _ hy h

/-- Strong B's canonical data has injective images. -/
theorem bdataS_imgInj : (bdataS C).ImgInj :=
  fun h i _ _ hr hr' e => limg_inj C.toFairChain h i hr hr' e

end Strong

end BArrow

end V12M
