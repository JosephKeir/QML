import QML.QML_v12m_BNetOps

/-!
# QML v12m — B's arrow model: creating a child in a network

* `newChild`: the node `s` gets a new child `nch s :: s`, with all of `s`'s variables committed
  forward under the same names (`id`), and nothing yet committed back.
* ⭐`Good.mkChild`: for a failing `□φ` (or a true `◇_x φ`) of `s`'s theory, the child from
  `child_consistent` (`childX_consistent`) keeps the invariants.  Its back arrow starts from
  closed transfer, which is **weak B** (`closed_back`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace NetSt

/-- ⭐The network with a new child of `s` in state `t`. -/
def newChild (N : NetSt σ) (s : Node) (kd : Option (VarSymb × VarType)) (cx : ℕ)
    (t : NodeSt σ) : NetSt σ where
  st := Function.update N.st (N.nch s :: s) t
  nch := Function.update (Function.update N.nch s (N.nch s + 1)) (N.nch s :: s) 0
  kind := Function.update N.kind (N.nch s :: s) kd
  cx := Function.update N.cx (N.nch s :: s) cx
  fcl := Function.update N.fcl (N.nch s :: s) (N.st s).l
  fimg := Function.update N.fimg (N.nch s :: s) id
  bcl := Function.update N.bcl (N.nch s :: s) []
  bimg := Function.update N.bimg (N.nch s :: s) id

theorem not_live_new {N : NetSt σ} (s : Node) : ¬ N.Live (N.nch s :: s) :=
  fun h => lt_irrefl _ h.2

theorem not_live_below_new {N : NetSt σ} (s : Node) (d : ℕ) :
    ¬ N.Live (d :: N.nch s :: s) := fun h => not_live_new s h.1

/-- The live nodes after adding a child: the old ones and the new one. -/
theorem live_newChild {N : NetSt σ} {s : Node} (hs : N.Live s) (kd : Option (VarSymb × VarType))
    (cx : ℕ) (t : NodeSt σ) :
    ∀ k, (N.newChild s kd cx t).Live k ↔ N.Live k ∨ k = N.nch s :: s
  | [] => by simp [Live]
  | d :: p => by
      have ih := live_newChild hs kd cx t p
      change (N.newChild s kd cx t).Live p ∧ d < (N.newChild s kd cx t).nch p ↔ _
      by_cases hpk : p = N.nch s :: s
      · subst hpk
        have e : (N.newChild s kd cx t).nch (N.nch s :: s) = 0 := Function.update_self _ _ _
        rw [e]
        simp only [Nat.not_lt_zero, and_false, false_iff, not_or]
        exact ⟨not_live_below_new s d, fun h => by
          have := congrArg List.length h
          simp at this⟩
      · have hnch : (N.newChild s kd cx t).nch p =
            Function.update N.nch s (N.nch s + 1) p := Function.update_of_ne hpk _ _
        rw [hnch, ih]
        simp only [hpk, or_false]
        by_cases hps : p = s
        · subst hps
          simp only [Function.update_self]
          change N.Live p ∧ d < N.nch p + 1 ↔ (N.Live p ∧ d < N.nch p) ∨ d :: p = N.nch p :: p
          simp only [List.cons.injEq, and_true, hs, true_and]
          omega
        · rw [Function.update_of_ne hps]
          change _ ↔ (N.Live p ∧ d < N.nch p) ∨ _
          simp only [List.cons.injEq, hps, and_false, or_false]

/-- ⭐A new child with a good forward arrow and a good back arrow keeps the invariants. -/
theorem Good.newChild [ModalSys.NoTFour] {N : NetSt σ} (hN : N.Good) {s : Node} (hs : N.Live s)
    {kd : Option (VarSymb × VarType)} {cx : ℕ} {t : NodeSt σ} (ht : Theory.IsMCS t.M)
    (hf : FwdData (N.st s) t kd cx (N.st s).l id) (hb : BackData t (N.st s) [] id) :
    (N.newChild s kd cx t).Good := by
  have hks : (N.nch s :: s : Node) ≠ s := ne_parent _ s
  have hold : ∀ k, N.Live k → k ≠ N.nch s :: s := fun k hk h => not_live_new s (h ▸ hk)
  refine ⟨fun k hk => ?_, fun c p hk => ?_, fun c p hk => ?_⟩
  · rcases (live_newChild hs kd cx t k).mp hk with hk | rfl
    · change Theory.IsMCS (Function.update N.st _ t k).M
      rw [Function.update_of_ne (hold k hk)]
      exact hN.mcs k hk
    · change Theory.IsMCS (Function.update N.st _ t _).M
      rw [Function.update_self]
      exact ht
  · rcases (live_newChild hs kd cx t _).mp hk with hk | he
    · have hne := hold _ hk
      have hpne := hold p hk.1
      have := hN.fwd c p hk
      unfold FwdOk at this ⊢
      change FwdData (Function.update N.st _ t p) (Function.update N.st _ t (c :: p))
        (Function.update N.kind _ kd (c :: p)) (Function.update N.cx _ cx (c :: p))
        (Function.update N.fcl _ (N.st s).l (c :: p)) (Function.update N.fimg _ id (c :: p))
      simp only [Function.update_of_ne hne, Function.update_of_ne hpne]
      exact this
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      unfold FwdOk
      change FwdData (Function.update N.st _ t p) (Function.update N.st _ t (N.nch p :: p))
        (Function.update N.kind _ kd _) (Function.update N.cx _ cx _)
        (Function.update N.fcl _ (N.st p).l _) (Function.update N.fimg _ id _)
      simp only [Function.update_self, Function.update_of_ne hks.symm]
      exact hf
  · rcases (live_newChild hs kd cx t _).mp hk with hk | he
    · have hne := hold _ hk
      have hpne := hold p hk.1
      have := hN.back c p hk
      unfold BackOk at this ⊢
      change BackData (Function.update N.st _ t (c :: p)) (Function.update N.st _ t p)
        (Function.update N.bcl _ [] (c :: p)) (Function.update N.bimg _ id (c :: p))
      simp only [Function.update_of_ne hne, Function.update_of_ne hpne]
      exact this
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      unfold BackOk
      change BackData (Function.update N.st _ t (N.nch p :: p)) (Function.update N.st _ t p)
        (Function.update N.bcl _ [] _) (Function.update N.bimg _ id _)
      simp only [Function.update_self, Function.update_of_ne hks.symm]
      exact hb

/-! ## The operation -/

open Classical in
/-- ⭐A new child for a failing `□φ`, or a true `◇_x φ`, of the node `s`'s theory — given as a
    formula over an earlier list of its variables. -/
noncomputable def mkChild [ModalSys.NoTFour] (N : NetSt σ) (s : Node) :
    (Σ l : List VarType, WFF σ (ctxOf l) 0) → NetSt σ
  | ⟨l, φ⟩ =>
      if h : l <:+ (N.st s).l then
        match φ with
        | .box ψ =>
            if WFF.mono (ctxOf_le_of_suffix h) (.box ψ) ∈ (N.st s).M then N else
              N.newChild s none 0 ⟨(N.st s).l.map VarType.bc, complete
                ({(childArrow (N.st s).l (WFF.mono (ctxOf_le_of_suffix h).boxIn ψ)).neg} ∪
                  {χ | ∃ ψ', WFF.mono (Ctx.Le.refl _) (.box ψ') ∈ (N.st s).M ∧
                    χ = childArrow (N.st s).l ψ'})⟩
        | .dia x hx ψ =>
            if WFF.mono (ctxOf_le_of_suffix h) (.dia x hx ψ) ∈ (N.st s).M then
              match hX : (ctxOf (N.st s).l).ref x with
              | some (.VTypeDia X) =>
                  N.newChild s (some (x, X)) (N.st s).l.length
                    ⟨X :: (N.st s).l.map VarType.bc, complete
                      ({childXArrow (N.st s).l hX (WFF.mono ((ctxOf_le_of_suffix h).diaIn x) ψ)} ∪
                        {χ | ∃ ψ', WFF.mono (Ctx.Le.refl _) (WFF.boxx x ⟨X, hX⟩ ψ') ∈ (N.st s).M ∧
                          χ = childXArrow (N.st s).l hX ψ'})⟩
              | _ => N
            else N
        | _ => N
      else N

/-- ⭐Creating a child preserves the invariants — using weak B for the back arrow. -/
theorem Good.mkChild [ModalSys.NoTFour] (hB : ModalSys.B = true) {N : NetSt σ} (hN : N.Good)
    {s : Node} (hs : N.Live s) (o : Σ l : List VarType, WFF σ (ctxOf l) 0) :
    (N.mkChild s o).Good := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.mkChild]
  split_ifs with h
  · have hM := hN.mcs s hs
    match φ with
    | .box ψ =>
        simp only
        split_ifs with hmem
        · exact hN
        · obtain ⟨hS, ht⟩ := complete_spec (child_consistent hM
            (φ := WFF.mono (ctxOf_le_of_suffix h).boxIn ψ) hmem)
          have htr : Transfer (N.st s).M (N.st s).l (ctxOf_le_of_suffix (List.suffix_refl _))
              (complete ({(childArrow (N.st s).l
                (WFF.mono (ctxOf_le_of_suffix h).boxIn ψ)).neg} ∪
                {χ | ∃ ψ', WFF.mono (Ctx.Le.refl _) (.box ψ') ∈ (N.st s).M ∧
                  χ = childArrow (N.st s).l ψ'})) id (childImg _) :=
            fun ψ' hψ' => hS (Or.inr ⟨ψ', hψ', rfl⟩)
          refine hN.newChild (kd := none) (cx := 0) hs ht ⟨List.suffix_refl _, childImg _, htr⟩
            ⟨List.nil_suffix, fun r hr => absurd hr (Nat.not_lt_zero r), ?_⟩
          exact Transfer.of_closed _ (closed_back hB hM ht htr.closed)
    | .dia x hx ψ =>
        simp only
        split_ifs with hmem
        · split
          · rename_i X hX
            obtain ⟨hS, ht⟩ := complete_spec (childX_consistent hM hX
              (φ := WFF.mono ((ctxOf_le_of_suffix h).diaIn x) ψ) hmem)
            have htr : TransferX (N.st s).M (N.st s).l (ctxOf_le_of_suffix (List.suffix_refl _)) hX
                (complete ({childXArrow (N.st s).l hX
                  (WFF.mono ((ctxOf_le_of_suffix h).diaIn x) ψ)} ∪
                  {χ | ∃ ψ', WFF.mono (Ctx.Le.refl _) (WFF.boxx x ⟨X, hX⟩ ψ') ∈ (N.st s).M ∧
                    χ = childXArrow (N.st s).l hX ψ'})) id (childXImg _ X) (N.st s).l.length
                (childX_cx _ X) :=
              fun ψ' hψ' => hS (Or.inr ⟨ψ', hψ', rfl⟩)
            refine hN.newChild (kd := some (x, X)) (cx := (N.st s).l.length) hs ht
              ⟨List.suffix_refl _, childXImg _ X, hX, childX_cx _ X, htr⟩
              ⟨List.nil_suffix, fun r hr => absurd hr (Nat.not_lt_zero r), ?_⟩
            exact Transfer.of_closed _ (closed_back hB hM ht (htr.closed hM))
          · exact hN
        · exact hN
    | .atom _ => exact hN
    | .eq _ _ => exact hN
    | .top => exact hN
    | .bot => exact hN
    | .and _ _ => exact hN
    | .or _ _ => exact hN
    | .imp _ _ => exact hN
    | .all _ _ => exact hN
    | .ex _ _ => exact hN
    | .here _ _ _ => exact hN
  · exact hN

end NetSt

end BArrow

end V12M
