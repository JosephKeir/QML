import QML.QML_v12m_BRetChildXD

/-!
# QML v12m — strong B on the network: the operations and the chain (T off)

All of L4e's operations together (docs §11.17, §11.20):
* weak B's (Henkin witnesses, children for `□`/`◇_x` formulas) and strong B's realisation steps
  (`applyOpS`);
* aliases (`mkAlias`);
* the four returning successors: plain (`mkRet`), along a witness (`mkRetX`), with a possible
  part (`mkRetD`), and both (`mkRetXD`).

`OpS` is their sum, `schedS` a fair schedule (every operation recurs forever), and `netS` the chain
from a root theory: ⭐`goodS_netS` (every network keeps strong B's invariants, T off) and `ext_netS`.
`Back` atoms need no operation of their own (§11.20, "L4e, fifth part").
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-- ⭐An operation under strong B: weak B's, an alias, or a child for a returning possibility (plain,
    along a witness, with a possible part, or both), at a node. -/
abbrev OpS (σ : Signature) :=
  Op σ ⊕ (Node × NetSt.AliasObl σ) ⊕ (Node × NetSt.RetObl σ) ⊕ (Node × NetSt.RetOblX σ) ⊕
    (Node × NetSt.RetOblD σ) ⊕ (Node × NetSt.RetOblXD σ)

instance : Nonempty (OpS σ) := ⟨.inl (.inr (.inr (.inl [])))⟩

section SchedS

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- An enumeration of the operations under strong B. -/
noncomputable def enumOpS : ℕ → OpS σ :=
  Classical.choose (exists_surjective_nat (OpS σ))

theorem enumOpS_surjective : Function.Surjective (enumOpS (σ := σ)) :=
  Classical.choose_spec (exists_surjective_nat (OpS σ))

/-- ⭐The schedule under strong B: round `n` performs operation `n.unpair.1`, so each recurs
    forever. -/
noncomputable def schedS (n : ℕ) : OpS σ := enumOpS n.unpair.1

/-- Every operation is scheduled at some round at or after any given one. -/
theorem schedS_after (o : OpS σ) (m : ℕ) : ∃ n, m ≤ n ∧ schedS n = o := by
  obtain ⟨e, he⟩ := enumOpS_surjective o
  refine ⟨Nat.pair e m, Nat.right_le_pair e m, ?_⟩
  simp [schedS, Nat.unpair_pair, he]

end SchedS

variable [ModalSys.NoFour]

namespace NetSt

open Classical in
/-- Perform one operation under strong B, at a live node only. -/
noncomputable def applyOpT (hS : ModalSys.BStrong = true) (N : NetSt σ) : OpS σ → NetSt σ
  | .inl o => N.applyOpS hS o
  | .inr (.inl (s, o)) => if N.Live s then N.mkAlias s o else N
  | .inr (.inr (.inl (s, o))) => if N.Live s then N.mkRet hS s o else N
  | .inr (.inr (.inr (.inl (s, o)))) => if N.Live s then N.mkRetX hS s o else N
  | .inr (.inr (.inr (.inr (.inl (s, o))))) => if N.Live s then N.mkRetD hS s o else N
  | .inr (.inr (.inr (.inr (.inr (s, o))))) => if N.Live s then N.mkRetXD hS s o else N

/-- ⭐Every operation keeps strong B's invariants (T off). -/
theorem GoodS.applyOpT {hS : ModalSys.BStrong = true} (hB : ModalSys.B = true)
    (hT : ModalSys.T = false) {N : NetSt σ} (hN : N.GoodS hS) (o : OpS σ) :
    (N.applyOpT hS o).GoodS hS := by
  rcases o with o | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩
  · exact hN.applyOpS hB o
  all_goals
    simp only [NetSt.applyOpT]
    split_ifs with h
    · first
        | exact hN.mkAlias h o
        | exact hN.mkRet hT h o
        | exact hN.mkRetX hT h o
        | exact hN.mkRetD hT h o
        | exact hN.mkRetXD hT h o
    · exact hN

/-- Every operation extends the network. -/
theorem Ext.applyOpT {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS)
    (o : OpS σ) : Ext N (N.applyOpT hS o) := by
  rcases o with o | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩
  · exact Ext.applyOpS hN o
  all_goals
    simp only [NetSt.applyOpT]
    split_ifs with h
    · first
        | exact Ext.mkAlias hN h o
        | exact Ext.mkRet h o
        | exact Ext.mkRetX h o
        | exact Ext.mkRetD h o
        | exact Ext.mkRetXD h o
    · exact Ext.refl N

end NetSt

section ChainS

variable [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-- ⭐The chain of networks from a root theory `M₀`, under strong B. -/
noncomputable def netS (hS : ModalSys.BStrong = true) {l₀ : List VarType}
    (M₀ : Set (WFF σ (ctxOf l₀) 0)) : ℕ → NetSt σ
  | 0 => NetSt.init M₀
  | n + 1 => (netS hS M₀ n).applyOpT hS (schedS n)

/-- ⭐Every network of the strong chain keeps strong B's invariants (T off). -/
theorem goodS_netS (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hT : ModalSys.T = false) {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
    (h : Theory.IsMCS M₀) : ∀ n, (netS hS M₀ n).GoodS hS
  | 0 => NetSt.GoodS.init hS h
  | n + 1 => (goodS_netS hS hB hT h n).applyOpT hB hT (schedS n)

/-- ⭐Along the strong chain, later networks extend earlier ones. -/
theorem ext_netS (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hT : ModalSys.T = false) {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
    (h : Theory.IsMCS M₀) {n m : ℕ} (hnm : n ≤ m) :
    NetSt.Ext (netS hS M₀ n) (netS hS M₀ m) := by
  induction hnm with
  | refl => exact NetSt.Ext.refl _
  | step _ ih => exact ih.trans (NetSt.Ext.applyOpT (goodS_netS hS hB hT h _) _)

/-- A step of the strong chain performs the scheduled operation. -/
theorem netS_succ (hS : ModalSys.BStrong = true) {l₀ : List VarType}
    (M₀ : Set (WFF σ (ctxOf l₀) 0)) (n : ℕ) :
    netS hS M₀ (n + 1) = (netS hS M₀ n).applyOpT hS (schedS n) := rfl

end ChainS

end BArrow

end V12M
