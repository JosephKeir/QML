import QML.QML_v12m_BNetStep

/-!
# QML v12m — B's arrow model: the operations on a network

Four operations, each preserving `Good`:

* `realF`: give the parent's next variable an image in a child (forward);
* `realB`: give a child's next variable an image in its parent (back);
* `henk`: a Henkin witness for an existential, or a counter-instance for a failing universal, of
  one node's theory;
* `mkChild`: a new child for a failing `□φ` or a true `◇_x φ` — ⭐`Good.mkChild` is where weak B
  enters: the new child's back arrow starts from closed transfer (`closed_back`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace NetSt

theorem live_of_nch {N N' : NetSt σ} (h : N'.nch = N.nch) : ∀ k, N'.Live k ↔ N.Live k
  | [] => Iff.rfl
  | c :: p => by
      change N'.Live p ∧ c < N'.nch p ↔ N.Live p ∧ c < N.nch p
      rw [live_of_nch h p, h]

/-- The network with the forward arrow of `k` recommitted. -/
def setFwd (N : NetSt σ) (k : Node) (cl : List VarType) (img : ℕ → ℕ) : NetSt σ :=
  { N with fcl := Function.update N.fcl k cl, fimg := Function.update N.fimg k img }

/-- The network with the back arrow of `k` recommitted. -/
def setBack (N : NetSt σ) (k : Node) (cl : List VarType) (img : ℕ → ℕ) : NetSt σ :=
  { N with bcl := Function.update N.bcl k cl, bimg := Function.update N.bimg k img }

theorem live_setFwd (N : NetSt σ) (k : Node) (cl : List VarType) (img : ℕ → ℕ) (k' : Node) :
    (N.setFwd k cl img).Live k' ↔ N.Live k' :=
  live_of_nch (N := N) (N' := N.setFwd k cl img) rfl k'

theorem live_setBack (N : NetSt σ) (k : Node) (cl : List VarType) (img : ℕ → ℕ) (k' : Node) :
    (N.setBack k cl img).Live k' ↔ N.Live k' :=
  live_of_nch (N := N) (N' := N.setBack k cl img) rfl k'

/-! ## Realising forward -/

/-- The child grown by the image of its parent's next variable. -/
noncomputable def fwdStep [ModalSys.NoTFour] (N : NetSt σ) (k p : Node) : NodeSt σ :=
  match N.kind k with
  | none => realStep (N.st p) (N.st k) (N.fcl k) (N.fimg k)
  | some (x, X) => realXStep (N.st p) (N.st k) x X (N.cx k) (N.fcl k) (N.fimg k)

/-- ⭐Give the parent's next variable an image in the child `k`. -/
noncomputable def realF [ModalSys.NoTFour] (N : NetSt σ) : Node → NetSt σ
  | [] => N
  | c :: p =>
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        (N.setSt (c :: p) (N.fwdStep (c :: p) p)).setFwd (c :: p)
          (nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p))
          (extImg (N.fimg (c :: p)) (N.fcl (c :: p)).length (N.st (c :: p)).l.length)
      else N

theorem fwdStep_ok [ModalSys.NoTFour] {N : NetSt σ} (hN : N.Good) {c : ℕ} {p : Node}
    (hk : N.Live (c :: p)) (hlt : (N.fcl (c :: p)).length < (N.st p).l.length) :
    Theory.IsMCS (N.fwdStep (c :: p) p).M ∧ Grows (N.st (c :: p)) (N.fwdStep (c :: p) p) ∧
      FwdData (N.st p) (N.fwdStep (c :: p) p) (N.kind (c :: p)) (N.cx (c :: p))
        (nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p))
        (extImg (N.fimg (c :: p)) (N.fcl (c :: p)).length (N.st (c :: p)).l.length) := by
  have hf := hN.fwd c p hk
  unfold FwdOk FwdData at hf
  unfold fwdStep FwdData
  cases hkd : N.kind (c :: p) with
  | none =>
      simp only [hkd] at hf ⊢
      obtain ⟨hsuf, himg, htr⟩ := hf
      exact realStep_ok (hN.mcs p hk.1) (hN.mcs _ hk) hsuf himg htr hlt
  | some xX =>
      obtain ⟨x, X⟩ := xX
      simp only [hkd] at hf ⊢
      obtain ⟨hsuf, himg, hx, hcx, htr⟩ := hf
      obtain ⟨h₁, h₂, hsuf', himg', hx', hcx', htr'⟩ :=
        realXStep_ok (hN.mcs p hk.1) (hN.mcs _ hk) hsuf himg hx hcx htr hlt
      exact ⟨h₁, h₂, hsuf', himg', hx', hcx', htr'⟩

/-- ⭐Realising forward preserves the invariants. -/
theorem Good.realF [ModalSys.NoTFour] {N : NetSt σ} (hN : N.Good) {k : Node} (hk : N.Live k) :
    (N.realF k).Good := by
  match k with
  | [] => exact hN
  | c :: p =>
      simp only [NetSt.realF]
      split_ifs with hlt
      · obtain ⟨hmcs, hg, hfd⟩ := fwdStep_ok hN hk hlt
        have hN₁ := hN.setSt hk hg hmcs
        refine ⟨fun s hs => hN₁.mcs s ((live_setFwd _ _ _ _ s).mp hs), fun c' p' hk' => ?_,
          fun c' p' hk' => ?_⟩
        all_goals rw [live_setFwd] at hk'
        · by_cases he : (c' :: p' : Node) = c :: p
          · obtain ⟨rfl, rfl⟩ := List.cons.inj he.symm
            unfold FwdOk
            simp only [setFwd, Function.update_self]
            rw [setSt_ne _ _ (fun h => ne_parent c p h.symm), setSt_self]
            exact hfd
          · have := hN₁.fwd c' p' hk'
            unfold FwdOk at this ⊢
            simp only [setFwd, Function.update_of_ne he]
            exact this
        · exact hN₁.back c' p' hk'
      · exact hN

/-! ## Realising back -/

/-- ⭐Give the child `k`'s next variable an image in its parent. -/
noncomputable def realB [ModalSys.NoTFour] (N : NetSt σ) : Node → NetSt σ
  | [] => N
  | c :: p =>
      if (N.bcl (c :: p)).length < (N.st (c :: p)).l.length then
        (N.setSt p (realStep (N.st (c :: p)) (N.st p) (N.bcl (c :: p)) (N.bimg (c :: p)))).setBack
          (c :: p) (nextTy (N.st (c :: p)).l (N.bcl (c :: p)) :: N.bcl (c :: p))
          (extImg (N.bimg (c :: p)) (N.bcl (c :: p)).length (N.st p).l.length)
      else N

/-- ⭐Realising back preserves the invariants. -/
theorem Good.realB [ModalSys.NoTFour] {N : NetSt σ} (hN : N.Good) {k : Node} (hk : N.Live k) :
    (N.realB k).Good := by
  match k with
  | [] => exact hN
  | c :: p =>
      simp only [NetSt.realB]
      split_ifs with hlt
      · have hb := hN.back c p hk
        unfold BackOk BackData at hb
        obtain ⟨hsuf, himg, htr⟩ := hb
        obtain ⟨hmcs, hg, hsuf', himg', htr'⟩ :=
          realStep_ok (hN.mcs _ hk) (hN.mcs p hk.1) hsuf himg htr hlt
        have hN₁ := hN.setSt hk.1 hg hmcs
        refine ⟨fun s hs => hN₁.mcs s ((live_setBack _ _ _ _ s).mp hs),
          fun c' p' hk' => hN₁.fwd c' p' ((live_setBack _ _ _ _ _).mp hk'), fun c' p' hk' => ?_⟩
        rw [live_setBack] at hk'
        by_cases he : (c' :: p' : Node) = c :: p
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he.symm
          unfold BackOk
          simp only [setBack, Function.update_self]
          rw [setSt_ne _ _ (ne_parent c p), setSt_self]
          exact ⟨hsuf', himg', htr'⟩
        · have := hN₁.back c' p' hk'
          unfold BackOk at this ⊢
          simp only [setBack, Function.update_of_ne he]
          exact this
      · exact hN

/-! ## Henkin witnesses -/

open Classical in
/-- ⭐A Henkin witness for an existential, or a counter-instance for a failing universal, of the
    node `s`'s theory — given as a formula over an earlier list of its variables. -/
noncomputable def henk [ModalSys.NoTFour] (N : NetSt σ) (s : Node) :
    (Σ l : List VarType, WFF σ (ctxOf l) 0) → NetSt σ
  | ⟨l, φ⟩ =>
      if h : l <:+ (N.st s).l then
        match φ with
        | .ex A ψ =>
            if WFF.mono (ctxOf_le_of_suffix h) (.ex A ψ) ∈ (N.st s).M then
              N.setSt s ⟨A :: (N.st s).l, complete
                (WFF.mono (ctxOf_le_append [A] (N.st s).l) '' (N.st s).M ∪
                  {WFF.openFree (N.st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
                    (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ)})⟩
            else N
        | .imp (.all A ψ) .bot =>
            if WFF.mono (ctxOf_le_of_suffix h) (.imp (.all A ψ) .bot) ∈ (N.st s).M then
              N.setSt s ⟨A :: (N.st s).l, complete
                (WFF.mono (ctxOf_le_append [A] (N.st s).l) '' (N.st s).M ∪
                  {WFF.openFree (N.st s).l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
                    (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ).neg})⟩
            else N
        | _ => N
      else N

/-- The Henkin step at a node, as a growth. -/
theorem henk_grow {t : NodeSt σ} {A : VarType} (ht : Theory.IsMCS t.M)
    {χ : WFF σ ((ctxOf t.l).insert (.bnd 0) A) 1} (hex : Theory.Derives t.M (.ex A χ)) :
    Theory.IsMCS (complete (WFF.mono (ctxOf_le_append [A] t.l) '' t.M ∪
        {WFF.openFree t.l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots χ})) ∧
      Grows t ⟨A :: t.l, complete (WFF.mono (ctxOf_le_append [A] t.l) '' t.M ∪
        {WFF.openFree t.l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots χ})⟩ := by
  obtain ⟨hS, hmcs⟩ := complete_spec (henkin_consistent ht.1 hex (ctxOf_fresh (l := t.l) le_rfl))
  exact ⟨hmcs, ⟨[A], rfl⟩, fun φ hφ => hS (Or.inl ⟨φ, hφ, rfl⟩)⟩

/-- ⭐Henkin witnesses preserve the invariants. -/
theorem Good.henk [ModalSys.NoTFour] {N : NetSt σ} (hN : N.Good) {s : Node} (hs : N.Live s)
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).Good := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.henk]
  split_ifs with h
  · have hM := hN.mcs s hs
    match φ with
    | .ex A ψ =>
        simp only
        split_ifs with hmem
        · obtain ⟨h₁, h₂⟩ := henk_grow hM (Theory.Derives.of_mem hmem)
          exact hN.setSt hs h₂ h₁
        · exact hN
    | .imp (.all A ψ) .bot =>
        simp only
        split_ifs with hmem
        · have hex : Theory.Derives (N.st s).M
              (.ex A (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ).neg) :=
            ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hmem,
              ⟨Proof.exNeg_of_negAll _⟩⟩
          obtain ⟨h₁, h₂⟩ := henk_grow hM hex
          exact hN.setSt hs h₂ h₁
        · exact hN
    | .atom _ => exact hN
    | .eq _ _ => exact hN
    | .top => exact hN
    | .bot => exact hN
    | .and _ _ => exact hN
    | .or _ _ => exact hN
    | .imp (.atom _) _ => exact hN
    | .imp (.eq _ _) _ => exact hN
    | .imp .top _ => exact hN
    | .imp .bot _ => exact hN
    | .imp (.and _ _) _ => exact hN
    | .imp (.or _ _) _ => exact hN
    | .imp (.imp _ _) _ => exact hN
    | .imp (.ex _ _) _ => exact hN
    | .imp (.box _) _ => exact hN
    | .imp (.dia _ _ _) _ => exact hN
    | .imp (.here _ _ _ _) _ => exact hN
    | .imp (.all _ _) (.atom _) => exact hN
    | .imp (.all _ _) (.eq _ _) => exact hN
    | .imp (.all _ _) .top => exact hN
    | .imp (.all _ _) (.and _ _) => exact hN
    | .imp (.all _ _) (.or _ _) => exact hN
    | .imp (.all _ _) (.imp _ _) => exact hN
    | .imp (.all _ _) (.all _ _) => exact hN
    | .imp (.all _ _) (.ex _ _) => exact hN
    | .imp (.all _ _) (.box _) => exact hN
    | .imp (.all _ _) (.dia _ _ _) => exact hN
    | .imp (.all _ _) (.here _ _ _ _) => exact hN
    | .all _ _ => exact hN
    | .box _ => exact hN
    | .dia _ _ _ => exact hN
    | .here _ _ _ _ => exact hN
  · exact hN

end NetSt

end BArrow

end V12M
