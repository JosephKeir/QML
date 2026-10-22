import QML.QML_v12m_BNetInjS
import QML.QML_v12m_BFair

/-!
# QML v12m — strong B on the network: the chain is fair

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

/-- Every network of strong B's chain has injective images. -/
theorem inj_netS (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hM₀ : Theory.IsMCS M₀) : ∀ n, (netS hS M₀ n).InjOk
  | 0 => NetSt.InjOk.init M₀
  | n + 1 => (inj_netS hS hB hM₀ n).applyOpT (goodS_netS hS hB hM₀ n) (schedS n)

theorem netS_succ_of {hS : ModalSys.BStrong = true} {n : ℕ} {o : OpS σ} (h : schedS n = o) :
    netS hS M₀ (n + 1) = (netS hS M₀ n).applyOpT hS o := by
  rw [← h]
  rfl

/-- Strong B's chain performs every step infinitely often. -/
noncomputable def strongOpChain (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hM₀ : Theory.IsMCS M₀) : OpChain M₀ where
  net := netS hS M₀
  zero := rfl
  good n := (goodS_netS hS hB hM₀ n).good
  inj := inj_netS hS hB hM₀
  backX n c p hl := by
    have hr := (goodS_netS hS hB hM₀ n).ret c p hl
    have hp := (goodS_netS hS hB hM₀ n).mcs p hl.1
    have hk := (goodS_netS hS hB hM₀ n).mcs _ hl
    unfold NetSt.RetOk at hr
    cases hbk : (netS hS M₀ n).bkind (c :: p) with
    | none => trivial
    | some eX =>
        obtain ⟨e, X⟩ := eX
        rw [hbk] at hr
        cases hkd : (netS hS M₀ n).kind (c :: p) with
        | none =>
            rw [hkd] at hr
            obtain ⟨ht, himgt, hx, hcx, htr⟩ := RetInvX.transferX hS hp hk hr.1
            exact ⟨ht, himgt, hx, hcx, htr⟩
        | some xX =>
            obtain ⟨x, X'⟩ := xX
            rw [hkd] at hr
            obtain ⟨ht, himgt, hx, hcx, htr⟩ := RetInvWD.transferX hS hp hk hr.1
            exact ⟨ht, himgt, hx, hcx, htr⟩
  ext := ext_netS hS hB hM₀
  henk s o m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inl (.inl (s, o))) m
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

/-- ⭐Strong B's chain is fair. -/
noncomputable def strongChain (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hM₀ : Theory.IsMCS M₀) : FairChain M₀ :=
  (strongOpChain hS hB hM₀).toFair

/-- Strong B's chain performs every child step, but under rows 3–4. -/
theorem childSteps_netS (hS : ModalSys.BStrong = true) (hW : ModalSys.BStrongW = false) :
    ChildSteps (netS hS M₀) :=
  ⟨fun s o m => by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inl (.inr (.inl (s, o)))) m
    exact ⟨n, hmn, fun hl => by
      rw [netS_succ_of hs]
      simp only [NetSt.applyOpT, NetSt.applyOpS, if_pos hl, hW, Bool.false_eq_true,
        ↓reduceIte]⟩⟩

theorem strongChain_children (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hM₀ : Theory.IsMCS M₀) (hW : ModalSys.BStrongW = false) :
    Children (strongChain hS hB hM₀).net :=
  (strongOpChain hS hB hM₀).children (childSteps_netS hS hW)

/-! ## Strong chains -/

/-- ⭐**What strong B's canonical model needs of a chain**, beyond fairness: every network keeps
    strong B's invariants, and every alias and every returning successor is made at some later
    round (if its node is alive then), as `OpChain` says of weak B's operations.  Children as
    weak B's (`Children`), and the returning successors without a back witness (`retOp`,
    `retXOp`, `retDOp`), only for rows 1–2: rows 3–4 label every edge both ways. -/
structure StrongChain (hS : ModalSys.BStrong = true) (M₀ : Set (WFF σ (ctxOf l₀) 0))
    extends FairChain M₀ where
  goodS : ∀ n, (net n).GoodS hS
  children : ModalSys.BStrongW = false → Children net
  aliasOp : ∀ (s : Node) (o : NetSt.AliasObl σ) (m : ℕ), ∃ n, m ≤ n ∧
    ((net n).Live s → net (n + 1) = (net n).mkAlias s o)
  retOp : ModalSys.BStrongW = false → ∀ (s : Node) (o : NetSt.RetOblC σ) (m : ℕ), ∃ n, m ≤ n ∧
    ((net n).Live s → net (n + 1) = (net n).mkRetC hS s o)
  retXOp : ModalSys.BStrongW = false → ∀ (s : Node) (o : NetSt.RetOblXC σ) (m : ℕ), ∃ n, m ≤ n ∧
    ((net n).Live s → net (n + 1) = (net n).mkRetXC hS s o)
  retDOp : ModalSys.BStrongW = false → ∀ (s : Node) (o : NetSt.RetOblDC σ) (m : ℕ), ∃ n, m ≤ n ∧
    ((net n).Live s → net (n + 1) = (net n).mkRetDC hS s o)
  retXDOp : ∀ (s : Node) (o : NetSt.RetOblXDC σ) (m : ℕ), ∃ n, m ≤ n ∧
    ((net n).Live s → net (n + 1) = (net n).mkRetXDC hS s o)
  /-- Under rows 3–4 every returning possibility along `□` has its route named. -/
  routeOp : ModalSys.BStrongW = true → ∀ (s : Node) (o : NetSt.RouteObl σ) (m : ℕ),
    ∃ n, m ≤ n ∧ ((net n).Live s → net (n + 1) = (net n).mkRoute hS s o)

/-- ⭐Strong B's chain is a strong chain. -/
noncomputable def strongChainS (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hM₀ : Theory.IsMCS M₀) : StrongChain hS M₀ where
  toFairChain := strongChain hS hB hM₀
  goodS := goodS_netS hS hB hM₀
  children hW := strongChain_children hS hB hM₀ hW
  aliasOp s o m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inr (.inl (s, o))) m
    exact ⟨n, hmn, fun hl => by
      change netS hS M₀ (n + 1) = _
      rw [netS_succ_of hs]
      exact if_pos hl⟩
  retOp hW s o m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inr (.inr (.inl (s, o)))) m
    exact ⟨n, hmn, fun hl => by
      change netS hS M₀ (n + 1) = _
      rw [netS_succ_of hs]
      exact (if_pos hl).trans (if_neg (by rw [hW]; decide))⟩
  retXOp hW s o m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inr (.inr (.inr (.inl (s, o))))) m
    exact ⟨n, hmn, fun hl => by
      change netS hS M₀ (n + 1) = _
      rw [netS_succ_of hs]
      exact (if_pos hl).trans (if_neg (by rw [hW]; decide))⟩
  retDOp hW s o m := by
    obtain ⟨n, hmn, hs⟩ := schedS_after (σ := σ) (.inr (.inr (.inr (.inr (.inl (s, o)))))) m
    exact ⟨n, hmn, fun hl => by
      change netS hS M₀ (n + 1) = _
      rw [netS_succ_of hs]
      exact (if_pos hl).trans (if_neg (by rw [hW]; decide))⟩
  retXDOp s o m := by
    obtain ⟨n, hmn, hs⟩ :=
      schedS_after (σ := σ) (.inr (.inr (.inr (.inr (.inr (.inl (s, o))))))) m
    exact ⟨n, hmn, fun hl => by
      change netS hS M₀ (n + 1) = _
      rw [netS_succ_of hs]
      exact if_pos hl⟩
  routeOp hW s o m := by
    obtain ⟨n, hmn, hs⟩ :=
      schedS_after (σ := σ) (.inr (.inr (.inr (.inr (.inr (.inr (s, o))))))) m
    exact ⟨n, hmn, fun hl => by
      change netS hS M₀ (n + 1) = _
      rw [netS_succ_of hs]
      exact (if_pos hl).trans (if_pos hW)⟩

end BArrow

end V12M
