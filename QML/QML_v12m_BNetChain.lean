import QML.QML_v12m_BNetChild

/-!
# QML v12m — B's arrow model: the chain of networks

A fair schedule of operations (`sched`: every operation recurs infinitely often) applied from a
one-node network gives a chain of networks (`net`), each `Good` (⭐`good_net`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-- An obligation: a formula over a list of a node's variables. -/
abbrev Obl (σ : Signature) := Σ l : List VarType, WFF σ (ctxOf l) 0

/-- An operation: a Henkin witness or a child for an obligation at a node, or realising forward
    or back along a child's arrows. -/
abbrev Op (σ : Signature) := (Node × Obl σ) ⊕ (Node × Obl σ) ⊕ Node ⊕ Node

instance : Nonempty (Op σ) := ⟨.inr (.inr (.inl []))⟩

section Sched

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- An enumeration of the operations. -/
noncomputable def enumOp : ℕ → Op σ :=
  Classical.choose (exists_surjective_nat (Op σ))

theorem enumOp_surjective : Function.Surjective (enumOp (σ := σ)) :=
  Classical.choose_spec (exists_surjective_nat (Op σ))

/-- ⭐The schedule: round `n` performs operation `n.unpair.1`, so each recurs forever. -/
noncomputable def sched (n : ℕ) : Op σ := enumOp n.unpair.1

/-- Every operation is scheduled at some round at or after any given one. -/
theorem sched_after (o : Op σ) (m : ℕ) : ∃ n, m ≤ n ∧ sched n = o := by
  obtain ⟨e, he⟩ := enumOp_surjective o
  refine ⟨Nat.pair e m, Nat.right_le_pair e m, ?_⟩
  simp [sched, Nat.unpair_pair, he]

end Sched

namespace NetSt

open Classical in
/-- Perform one operation, at a live node only. -/
noncomputable def applyOp [ModalSys.NoFour] (N : NetSt σ) : Op σ → NetSt σ
  | .inl (s, o) => if N.Live s then N.henk s o else N
  | .inr (.inl (s, o)) => if N.Live s then N.mkChild s o else N
  | .inr (.inr (.inl k)) => if N.Live k then N.realF k else N
  | .inr (.inr (.inr k)) => if N.Live k then N.realB k else N

theorem Good.applyOp [ModalSys.NoFour] (hB : ModalSys.B = true) {N : NetSt σ} (hN : N.Good)
    (o : Op σ) : (N.applyOp o).Good := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | k
  · simp only [NetSt.applyOp]
    split_ifs with h
    · exact hN.henk h o
    · exact hN
  · simp only [NetSt.applyOp]
    split_ifs with h
    · exact hN.mkChild hB h o
    · exact hN
  · simp only [NetSt.applyOp]
    split_ifs with h
    · exact hN.realF h
    · exact hN
  · simp only [NetSt.applyOp]
    split_ifs with h
    · exact hN.realB h
    · exact hN

/-- The network of one world with theory `M₀` over no variables. -/
def init {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) : NetSt σ where
  st := fun _ => ⟨l₀, M₀⟩
  nch := fun _ => 0
  kind := fun _ => none
  cx := fun _ => 0
  bkind := fun _ => none
  fcl := fun _ => []
  fimg := fun _ => id
  bcl := fun _ => []
  bimg := fun _ => id

theorem init_live {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} :
    ∀ {k : Node}, (init M₀).Live k → k = []
  | [], _ => rfl
  | _ :: _, h => absurd h.2 (Nat.not_lt_zero _)

theorem Good.init [ModalSys.NoFour] {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
    (h : Theory.IsMCS M₀) :
    (init M₀).Good :=
  ⟨fun _ _ => h, fun _ _ hk => absurd (init_live hk) (by simp),
    fun _ _ hk => absurd (init_live hk) (by simp)⟩

end NetSt

section Chain

variable [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoFour]

/-- ⭐The chain of networks from a root theory `M₀`. -/
noncomputable def net {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0)) : ℕ → NetSt σ
  | 0 => NetSt.init M₀
  | n + 1 => (net M₀ n).applyOp (sched n)

/-- ⭐Every network of the chain is good. -/
theorem good_net (hB : ModalSys.B = true) {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
    (h : Theory.IsMCS M₀) : ∀ n, (net M₀ n).Good
  | 0 => NetSt.Good.init h
  | n + 1 => (good_net hB h n).applyOp hB (sched n)

end Chain

end BArrow

end V12M
