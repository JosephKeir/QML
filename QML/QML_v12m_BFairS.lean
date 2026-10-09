import QML.QML_v12m_BNetS
import QML.QML_v12m_BFair

/-!
# QML v12m — strong B on the network: the chain is fair (T off)

Strong B's chain (`netS`) performs every step infinitely often (`strongOpChain`), so it is a fair
chain (⭐`strongChain`) and the limit (`bdata`) applies to it.  Its realisation steps are strong
B's (`realFS`, `realBS`), which commit the next variable as weak B's do (`realFS_fcl`,
`realBS_bcl`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour] {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

theorem realFS_fcl (hS : ModalSys.BStrong = true) (N : NetSt σ) (c : ℕ) (p : Node) :
    (N.realFS hS (c :: p)).fcl (c :: p) =
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p)
      else N.fcl (c :: p) := by
  simp only [NetSt.realFS]
  split_ifs
  · exact Function.update_self _ _ _
  · rfl

theorem realBS_bcl (hS : ModalSys.BStrong = true) (N : NetSt σ) (c : ℕ) (p : Node) :
    (N.realBS hS (c :: p)).bcl (c :: p) =
      if (N.bcl (c :: p)).length < (N.st (c :: p)).l.length then
        nextTy (N.st (c :: p)).l (N.bcl (c :: p)) :: N.bcl (c :: p)
      else N.bcl (c :: p) := by
  simp only [NetSt.realBS]
  split_ifs
  · exact Function.update_self _ _ _
  · rfl

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

theorem netS_succ_of {hS : ModalSys.BStrong = true} {n : ℕ} {o : OpS σ} (h : schedS n = o) :
    netS hS M₀ (n + 1) = (netS hS M₀ n).applyOpT hS o := by
  rw [← h]
  rfl

/-- Strong B's chain performs every step infinitely often (T off). -/
noncomputable def strongOpChain (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hT : ModalSys.T = false) (hM₀ : Theory.IsMCS M₀) : OpChain M₀ where
  net := netS hS M₀
  zero := rfl
  good n := (goodS_netS hS hB hT hM₀ n).good
  ext := ext_netS hS hB hT hM₀
  henk s o m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inl (.inl (s, o))) m
    exact ⟨n, hmn, fun hl => by
      rw [netS_succ_of hs]
      simp only [NetSt.applyOpT, NetSt.applyOpS, if_pos hl]⟩
  child s o m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inl (.inr (.inl (s, o)))) m
    exact ⟨n, hmn, fun hl => by
      rw [netS_succ_of hs]
      simp only [NetSt.applyOpT, NetSt.applyOpS, if_pos hl]⟩
  fwd c p m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inl (.inr (.inr (.inl (c :: p))))) m
    refine ⟨n, hmn, fun hl => ?_⟩
    rw [netS_succ_of hs]
    simp only [NetSt.applyOpT, NetSt.applyOpS, if_pos hl]
    exact realFS_fcl hS _ _ _
  back c p m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inl (.inr (.inr (.inr (c :: p))))) m
    refine ⟨n, hmn, fun hl => ?_⟩
    rw [netS_succ_of hs]
    simp only [NetSt.applyOpT, NetSt.applyOpS, if_pos hl]
    exact realBS_bcl hS _ _ _

/-- ⭐Strong B's chain is fair (T off). -/
noncomputable def strongChain (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hT : ModalSys.T = false) (hM₀ : Theory.IsMCS M₀) : FairChain M₀ :=
  (strongOpChain hS hB hT hM₀).toFair

end BArrow

end V12M
