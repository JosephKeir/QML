import QML.QML_v12m_BNetRetC

/-!
# QML v12m — strong B on the network: the returning successors, for either T

The four operations giving a node the child of a returning-possibility obligation, on the generic
children (docs §11.21): the obligation binds the born root `u : □A` itself with all its
companions (`bornShape A`), valued at `unarrT` of the alias `y` — and, for a possible part,
`unarrDT` with its content `z`.  Each child is born with the invariants with companions both ways
(`retChildC_fwd`/`_back`, …), so the operations keep `GoodS` for every value of T.

* `mkRetC` (plain), `mkRetXC` (along a witness `x`), `mkRetDC` (with a possible part, its way home
  in the extent of its own root `e`), `mkRetXDC` (both).
* ⭐`GoodS.mkRetC`, `GoodS.mkRetXC`, `GoodS.mkRetDC`, `GoodS.mkRetXDC`; `Ext.mkRetC`, ….
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

namespace NetSt

/-! ## Plain -/

/-- A returning-possibility obligation at the born shape: over a list of a node's variables, the
    type `A` of what comes back, the alias `y` (of type `(□A).bc`) and the body over the born root
    `u : □A`. -/
abbrev RetOblC (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, ℕ × WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox A)) 1

open Classical in
/-- ⭐Give the node `s` the child of its obligation `◇^{S_A}[u ↦ unarrT y] Ξ`, if it has it — `Ξ`
    over an earlier list of its variables. -/
noncomputable def mkRetC (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RetOblC σ → NetSt σ
  | ⟨l, A, y, Ξ⟩ =>
      if h : l <:+ (N.st s).l then
        if hy : (ctxOf (N.st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc then
          if WFF.retS hS (.nec (bornShape A)) (unarrT (σ := σ) hy).2
              (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) _) Ξ) ∈ (N.st s).M then
            N.newChild s none 0
              (retChildC hS hy (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) _) Ξ))
              Nat.succ [.VTypeBox A] (fun _ => y)
          else N
        else N
      else N

/-- ⭐The child of a returning-possibility obligation keeps the invariants: it is born with them
    (`retChildC_fwd`, `retChildC_back`). -/
theorem GoodS.mkRetC {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) (o : RetOblC σ) : (N.mkRetC hS s o).GoodS hS := by
  obtain ⟨l, A, y, Ξ⟩ := o
  simp only [NetSt.mkRetC]
  split_ifs with h hy hΞ
  · exact hN.newChild hs (retChildC_spec hS hy (hN.mcs s hs) hΞ).2
      ⟨retChildC_fwd hS hy (hN.mcs s hs) hΞ, retChildC_back hS hy (hN.mcs s hs) hΞ⟩
  all_goals exact hN

theorem Ext.mkRetC {hS : ModalSys.BStrong = true} {N : NetSt σ} {s : Node} (hs : N.Live s)
    (o : RetOblC σ) : Ext N (N.mkRetC hS s o) := by
  obtain ⟨l, A, y, Ξ⟩ := o
  simp only [NetSt.mkRetC]
  split_ifs
  · exact Ext.newChild hs _ _ _ _ _ _
  all_goals exact Ext.refl N

/-! ## Along a witness -/

/-- An obligation along a witness `x`: the body over `x`'s view and the born root. -/
abbrev RetOblXC (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, Σ x : VarSymb,
    ℕ × WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox A)) 1

open Classical in
/-- ⭐Give the node `s` the witness child of its obligation `◇_x^{S_A}[u ↦ unarrT y] Ξ`, if it
    has it. -/
noncomputable def mkRetXC (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RetOblXC σ → NetSt σ
  | ⟨l, A, x, y, Ξ⟩ =>
      if h : l <:+ (N.st s).l then
        if hy : (ctxOf (N.st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc then
          match hX : (ctxOf (N.st s).l).ref x with
          | some (.VTypeDia X) =>
              if WFF.retxS hS x ⟨X, hX⟩ (.nec (bornShape A)) (unarrT (σ := σ) hy).2
                  (WFF.mono (((ctxOf_le_of_suffix h).diaIn x).insert (.bnd 0) _) Ξ) ∈
                  (N.st s).M then
                N.newChild s (some (x, X)) ((N.st s).l.length + 1)
                  (retChildXC hS hy hX
                    (WFF.mono (((ctxOf_le_of_suffix h).diaIn x).insert (.bnd 0) _) Ξ))
                  Nat.succ [.VTypeBox A] (fun _ => y)
              else N
          | _ => N
        else N
      else N

/-- ⭐The witness child keeps the invariants (`retChildXC_fwd`, `retChildXC_back`). -/
theorem GoodS.mkRetXC {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS)
    {s : Node} (hs : N.Live s) (o : RetOblXC σ) : (N.mkRetXC hS s o).GoodS hS := by
  obtain ⟨l, A, x, y, Ξ⟩ := o
  simp only [NetSt.mkRetXC]
  split_ifs with h hy
  · split
    · rename_i X hX
      split_ifs with hΞ
      · exact hN.newChild hs (retChildXC_spec hS hy hX (hN.mcs s hs) hΞ).2
          ⟨retChildXC_fwd hS hy hX (hN.mcs s hs) hΞ, retChildXC_back hS hy hX (hN.mcs s hs) hΞ⟩
      · exact hN
    · exact hN
  all_goals exact hN

theorem Ext.mkRetXC {hS : ModalSys.BStrong = true} {N : NetSt σ} {s : Node} (hs : N.Live s)
    (o : RetOblXC σ) : Ext N (N.mkRetXC hS s o) := by
  obtain ⟨l, A, x, y, Ξ⟩ := o
  simp only [NetSt.mkRetXC]
  split_ifs
  · split
    · split_ifs
      · exact Ext.newChild hs _ _ _ _ _ _
      · exact Ext.refl N
    · exact Ext.refl N
  all_goals exact Ext.refl N

/-! ## With a possible part -/

/-- An obligation with a possible part: the alias `y`, a unit root `o` and the content `z`, and
    the body over the born root and the possible part. -/
abbrev RetOblDC (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, Σ X : VarType,
    (ℕ × ℕ × ℕ) × WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (bornShape A) X).ty) 1

open Classical in
/-- ⭐Give the node `s` the back-witness child of its obligation
    `◇^{S_A × ◇X}[⟨u, e⟩ ↦ ⟨unarrT y, z⟩] Ξ`, if it has it.  The two born roots go back to
    distinct roots (`y ≠ o`), so the back arrow's images are injective. -/
noncomputable def mkRetDC (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RetOblDC σ → NetSt σ
  | ⟨l, A, X, (y, o, z), Ξ⟩ =>
      if h : l <:+ (N.st s).l then
        if hy : (ctxOf (N.st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc then
          if (ctxOf (N.st s).l).ref (.root (.free o)) = some .VTypeOne then
            if hz : (ctxOf (N.st s).l).ref (.root (.free z)) = some X then
              if WFF.retS hS (.wit (bornShape A) X) (unarrDT (σ := σ) hy hz).2
                  (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) _) Ξ) ∈
                  (N.st s).M then
                if y ≠ o then
                  N.newChild s none 0
                    (retChildDC hS hy hz
                      (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) _) Ξ))
                    (· + 2) (bclD A X) (backImgD y o) (some (.root (.free 1), X)) z
                else N
              else N
            else N
          else N
        else N
      else N

/-- ⭐The back-witness child keeps the invariants (`retChildDC_fwd`, `retChildDC_back`). -/
theorem GoodS.mkRetDC {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS)
    {s : Node} (hs : N.Live s) (o : RetOblDC σ) : (N.mkRetDC hS s o).GoodS hS := by
  obtain ⟨l, A, X, ⟨y, o, z⟩, Ξ⟩ := o
  simp only [NetSt.mkRetDC]
  split_ifs with h hy ho hz hΞ hyo
  · exact hN.newChild hs (retChildDC_spec hS hy hz (hN.mcs s hs) hΞ).2
      ⟨retChildDC_fwd hS hy hz (hN.mcs s hs) hΞ ho, retChildDC_back hS hy hz (hN.mcs s hs) hΞ ho⟩
  all_goals exact hN

theorem Ext.mkRetDC {hS : ModalSys.BStrong = true} {N : NetSt σ} {s : Node} (hs : N.Live s)
    (o : RetOblDC σ) : Ext N (N.mkRetDC hS s o) := by
  obtain ⟨l, A, X, ⟨y, o, z⟩, Ξ⟩ := o
  simp only [NetSt.mkRetDC]
  split_ifs
  · exact Ext.newChild hs _ _ _ _ _ _ _ _
  all_goals exact Ext.refl N

/-! ## Along a witness, with a possible part -/

/-- An obligation along a witness `x` with a possible part. -/
abbrev RetOblXDC (σ : Signature) :=
  Σ l : List VarType, Σ A : VarType, Σ Xe : VarType, Σ x : VarSymb,
    (ℕ × ℕ × ℕ) × WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (bornShape A) Xe).ty) 1

open Classical in
/-- ⭐Give the node `s` the doubly witnessed child of its obligation
    `◇_x^{S_A × ◇Xe}[⟨u, e⟩ ↦ ⟨unarrT y, z⟩] Ξ`, if it has it; the two born roots go back to
    distinct roots (`y ≠ o`). -/
noncomputable def mkRetXDC (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RetOblXDC σ → NetSt σ
  | ⟨l, A, Xe, x, (y, o, z), Ξ⟩ =>
      if h : l <:+ (N.st s).l then
        if hy : (ctxOf (N.st s).l).ref (.root (.free y)) = some (VarType.VTypeBox A).bc then
          if (ctxOf (N.st s).l).ref (.root (.free o)) = some .VTypeOne then
            if hz : (ctxOf (N.st s).l).ref (.root (.free z)) = some Xe then
              if y ≠ o then
                match hX : (ctxOf (N.st s).l).ref x with
                | some (.VTypeDia X) =>
                    if WFF.retxS hS x ⟨X, hX⟩ (.wit (bornShape A) Xe) (unarrDT (σ := σ) hy hz).2
                        (WFF.mono (((ctxOf_le_of_suffix h).diaIn x).insert (.bnd 0) _) Ξ) ∈
                        (N.st s).M then
                      N.newChild s (some (x, X)) ((N.st s).l.length + 2)
                        (retChildXDC hS hy hz hX
                          (WFF.mono (((ctxOf_le_of_suffix h).diaIn x).insert (.bnd 0) _) Ξ))
                        (· + 2) (bclD A Xe) (backImgD y o) (some (.root (.free 1), Xe)) z
                    else N
                | _ => N
              else N
            else N
          else N
        else N
      else N

/-- ⭐The doubly witnessed child keeps the invariants (`retChildXDC_fwd`, `retChildXDC_back`). -/
theorem GoodS.mkRetXDC {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS)
    {s : Node} (hs : N.Live s) (o : RetOblXDC σ) : (N.mkRetXDC hS s o).GoodS hS := by
  obtain ⟨l, A, Xe, x, ⟨y, o, z⟩, Ξ⟩ := o
  simp only [NetSt.mkRetXDC]
  split_ifs with h hy ho hz hyo
  · split
    · rename_i X hX
      split_ifs with hΞ
      · exact hN.newChild hs (retChildXDC_spec hS hy hz hX (hN.mcs s hs) hΞ).2
          ⟨retChildXDC_fwd hS hy hz hX (hN.mcs s hs) hΞ ho,
            retChildXDC_back hS hy hz hX (hN.mcs s hs) hΞ ho⟩
      · exact hN
    · exact hN
  all_goals exact hN

theorem Ext.mkRetXDC {hS : ModalSys.BStrong = true} {N : NetSt σ} {s : Node} (hs : N.Live s)
    (o : RetOblXDC σ) : Ext N (N.mkRetXDC hS s o) := by
  obtain ⟨l, A, Xe, x, ⟨y, o, z⟩, Ξ⟩ := o
  simp only [NetSt.mkRetXDC]
  split_ifs
  · split
    · split_ifs
      · exact Ext.newChild hs _ _ _ _ _ _ _ _
      · exact Ext.refl N
    · exact Ext.refl N
  all_goals exact Ext.refl N

end NetSt

end BArrow

end V12M
