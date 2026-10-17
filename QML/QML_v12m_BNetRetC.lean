import QML.QML_v12m_BRetBirthC

/-!
# QML v12m — strong B on the network, with companions: the invariants and the operations

Under strong B every child's two arrows carry the returning-possibility invariants with the
tuple's companions (`RetDataB`, docs §11.21): `RetInvB` both ways for a plain child; `RetInvWB`
forward and `RetInvXB` home for a witness child; their mirror for a back-witness child; and
`RetInvWDB` both ways for a doubly witnessed child.  At T off they are the old ones
(`retDataB_false`), and forgetting the companions gives them for every T (`RetDataB.forget`), so
necessity transfer, weak B's `Good` and the old `RetOk` follow (`GoodS.ret`, `GoodS.good`).

* `RetDataB.grow_src`, `RetDataB.grow_tgt`, ⭐`GoodS.setSt`: growing a node keeps the invariants.
* `realFS`, `realBS`: the realisation steps with companions (`retStepB`; `retStepWB` forward and
  `retStepXB` home for a witness child; `retStepWDB` both ways for a doubly witnessed one);
  ⭐`GoodS.realFS`, `GoodS.realBS` by the steps and their reverses.
* `GoodS.henk`, ⭐`GoodS.mkChild`: Henkin steps and children are weak B's; a child is born with
  the invariants (`RetDataB.birth`, by `RetInvB.birth`, `RetInvWB.birth` and the nil lemmas).
* `applyOpS`: weak B's operations under strong B; aliases (`GoodS.mkAlias`).  The returning
  successors are in `QML_v12m_BRetOpsC`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The invariants with companions -/

/-- ⭐The returning-possibility invariants with companions of a child's arrows `p → k` and
    `k → p`, by the child's kind as `RetData`'s; `RetData` at `false`. -/
def RetDataB (hS : ModalSys.BStrong = true) (b : Bool) (hb : ModalSys.T = b) (tp tk : NodeSt σ)
    (kind bkd : Option (VarSymb × VarType)) (cx bcx : ℕ) (fcl : List VarType) (fimg : ℕ → ℕ)
    (bcl : List VarType) (bimg : ℕ → ℕ) : Prop :=
  match kind, bkd with
  | some (x, X), none =>
      RetInvWB hS b hb tp tk fcl fimg bcl bimg x X cx ∧
        RetInvXB hS b hb tk tp bcl bimg fcl fimg x X cx
  | some (x, X), some (e, E) =>
      RetInvWDB hS b hb tp tk fcl fimg bcl bimg x X cx e E bcx ∧
        RetInvWDB hS b hb tk tp bcl bimg fcl fimg e E bcx x X cx
  | none, none =>
      RetInvB hS b hb tp tk fcl fimg bcl bimg ∧ RetInvB hS b hb tk tp bcl bimg fcl fimg
  | none, some (e, X) =>
      RetInvXB hS b hb tp tk fcl fimg bcl bimg e X bcx ∧
        RetInvWB hS b hb tk tp bcl bimg fcl fimg e X bcx

section RetDataB

variable {hS : ModalSys.BStrong = true} {tp tk : NodeSt σ} {kind bkd : Option (VarSymb × VarType)}
  {cx bcx : ℕ} {fcl : List VarType} {fimg : ℕ → ℕ} {bcl : List VarType} {bimg : ℕ → ℕ}

/-- At T off the invariants with companions are the old ones. -/
theorem retDataB_false (hT : ModalSys.T = false) :
    RetDataB hS false hT tp tk kind bkd cx bcx fcl fimg bcl bimg ↔
      RetData hS tp tk kind bkd cx bcx fcl fimg bcl bimg := by
  rcases kind with _ | ⟨x, X⟩ <;> rcases bkd with _ | ⟨e, E⟩ <;> exact Iff.rfl

/-- The flag can be taken to be T itself. -/
theorem retDataB_flag {b : Bool} (hb : ModalSys.T = b) :
    RetDataB hS ModalSys.T rfl tp tk kind bkd cx bcx fcl fimg bcl bimg ↔
      RetDataB hS b hb tp tk kind bkd cx bcx fcl fimg bcl bimg := by
  cases hb
  exact Iff.rfl

/-- The old invariants, at T off, are the invariants with companions. -/
theorem RetDataB.ofK (hT : ModalSys.T = false)
    (h : RetData hS tp tk kind bkd cx bcx fcl fimg bcl bimg) :
    RetDataB hS ModalSys.T rfl tp tk kind bkd cx bcx fcl fimg bcl bimg :=
  (retDataB_flag hT).mpr ((retDataB_false hT).mpr h)

/-- ⭐Forgetting the companions gives the old invariants. -/
theorem RetDataB.forget {b : Bool} {hb : ModalSys.T = b} (hp : Theory.IsMCS tp.M)
    (hk : Theory.IsMCS tk.M) (h : RetDataB hS b hb tp tk kind bkd cx bcx fcl fimg bcl bimg) :
    RetData hS tp tk kind bkd cx bcx fcl fimg bcl bimg := by
  rcases kind with _ | ⟨x, X⟩ <;> rcases bkd with _ | ⟨e, E⟩
  · exact ⟨h.1.forget hk, h.2.forget hp⟩
  · exact ⟨h.1.forget hk, h.2.forget hp⟩
  · exact ⟨h.1.forget hk, h.2.forget hp⟩
  · exact ⟨h.1.forget hk, h.2.forget hp⟩

/-- A growing child keeps the invariants. -/
theorem RetDataB.grow_tgt {b : Bool} {hb : ModalSys.T = b} (hk : Theory.IsMCS tk.M)
    {tk' : NodeSt σ} (hk' : Theory.IsMCS tk'.M)
    (h : RetDataB hS b hb tp tk kind bkd cx bcx fcl fimg bcl bimg) (hg : Grows tk tk') :
    RetDataB hS b hb tp tk' kind bkd cx bcx fcl fimg bcl bimg := by
  rcases kind with _ | ⟨x, X⟩ <;> rcases bkd with _ | ⟨e, E⟩
  · exact ⟨h.1.grow_tgt hg, h.2.grow_src hk hk' hg⟩
  · exact ⟨h.1.grow_tgt hg, h.2.grow_src hk hk' hg⟩
  · exact ⟨h.1.grow_tgt hg, h.2.grow_src hk hk' hg⟩
  · exact ⟨h.1.grow_tgt hg, h.2.grow_src hk hk' hg⟩

/-- A growing parent keeps the invariants. -/
theorem RetDataB.grow_src {b : Bool} {hb : ModalSys.T = b} (hp : Theory.IsMCS tp.M)
    {tp' : NodeSt σ} (hp' : Theory.IsMCS tp'.M)
    (h : RetDataB hS b hb tp tk kind bkd cx bcx fcl fimg bcl bimg) (hg : Grows tp tp') :
    RetDataB hS b hb tp' tk kind bkd cx bcx fcl fimg bcl bimg := by
  rcases kind with _ | ⟨x, X⟩ <;> rcases bkd with _ | ⟨e, E⟩
  · exact ⟨h.1.grow_src hp hp' hg, h.2.grow_tgt hg⟩
  · exact ⟨h.1.grow_src hp hp' hg, h.2.grow_tgt hg⟩
  · exact ⟨h.1.grow_src hp hp' hg, h.2.grow_tgt hg⟩
  · exact ⟨h.1.grow_src hp hp' hg, h.2.grow_tgt hg⟩

end RetDataB

/-- ⭐**Birth**: a new child's arrows, with all the parent's variables committed forward and none
    back, carry the invariants with companions — from the seed's transfer (`RetInvB.birth`,
    `RetInvB.nil`; `RetInvWB.birth`, `RetInvXB.nil`). -/
theorem RetDataB.birth (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) {tp tk : NodeSt σ}
    {kd : Option (VarSymb × VarType)} {cx : ℕ} (hp : Theory.IsMCS tp.M)
    (hk : Theory.IsMCS tk.M) (hf : FwdData tp tk kd cx tp.l id) :
    RetDataB hS ModalSys.T rfl tp tk kd none cx 0 tp.l id [] id := by
  cases kd with
  | none =>
      obtain ⟨hsuf, himg, htr⟩ := hf
      exact ⟨RetInvB.birth hS hB hp hsuf himg htr,
        RetInvB.nil hS hB hk hp hsuf himg htr _ rfl⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      obtain ⟨hsuf, himg, hx, hcx, htr⟩ := hf
      exact ⟨RetInvWB.birth hS hB hp hsuf himg hx hcx htr,
        RetInvXB.nil hS hB hk hp hsuf himg hx hcx htr _ rfl⟩

namespace NetSt

/-- The invariants with companions of the child `k`'s arrows, to and from its parent `p`. -/
def RetOkB (hS : ModalSys.BStrong = true) (N : NetSt σ) (k p : Node) : Prop :=
  RetDataB hS ModalSys.T rfl (N.st p) (N.st k) (N.kind k) (N.bkind k) (N.cx k) (N.bcx k)
    (N.fcl k) (N.fimg k) (N.bcl k) (N.bimg k)

/-- ⭐The invariants of a network under strong B. -/
structure GoodS (hS : ModalSys.BStrong = true) (N : NetSt σ) : Prop where
  mcs : ∀ s, N.Live s → Theory.IsMCS (N.st s).M
  retB : ∀ c p, N.Live (c :: p) → N.RetOkB hS (c :: p) p

/-- Forgetting the companions: the old invariants. -/
theorem GoodS.ret {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) (c : ℕ)
    (p : Node) (hk : N.Live (c :: p)) : N.RetOk hS (c :: p) p :=
  (hN.retB c p hk).forget (hN.mcs p hk.1) (hN.mcs _ hk)

/-- ⭐Strong B's invariants give weak B's. -/
theorem GoodS.good {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) : N.Good :=
  ⟨hN.mcs, fun c p hk => (hN.ret c p hk).fwd (hN.mcs p hk.1) (hN.mcs _ hk),
    fun c p hk => (hN.ret c p hk).back (hN.mcs p hk.1) (hN.mcs _ hk)⟩

/-- ⭐Growing one live node conservatively keeps the invariants. -/
theorem GoodS.setSt {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    {t : NodeSt σ} (hs : N.Live s) (hg : Grows (N.st s) t) (ht : Theory.IsMCS t.M) :
    (N.setSt s t).GoodS hS := by
  refine ⟨(hN.good.setSt hs hg ht).mcs, fun c p hk => ?_⟩
  rw [live_setSt] at hk
  have hr := hN.retB c p hk
  unfold RetOkB at hr ⊢
  change RetDataB hS ModalSys.T rfl ((N.setSt s t).st p) ((N.setSt s t).st (c :: p)) _ _ _ _ _ _ _ _
  by_cases hkp : (c :: p : Node) = s
  · subst hkp
    rw [setSt_ne _ _ (fun h => ne_parent c p h.symm), setSt_self]
    exact hr.grow_tgt (hN.mcs _ hk) ht hg
  · rw [setSt_ne _ _ hkp]
    by_cases hps : p = s
    · subst hps
      rw [setSt_self]
      exact hr.grow_src (hN.mcs p hk.1) ht hg
    · rw [setSt_ne _ _ hps]
      exact hr

/-! ## Realising forward -/

open Classical in
/-- The child grown by the image of its parent's next variable, under strong B: the target gains
    returning possibilities (`retStepB`, or `retStepWB` for a witness child). -/
noncomputable def fwdStepS (hS : ModalSys.BStrong = true) (N : NetSt σ) (k p : Node) :
    NodeSt σ :=
  if h : (N.fcl k).length < (N.st p).l.length ∧ N.fcl k <:+ (N.st p).l ∧
      ImgOk (N.bcl k) (ctxOf (N.st p).l) (N.bimg k) ∧
      ImgOk (N.fcl k) (ctxOf (N.st k).l) (N.fimg k) ∧ N.bcl k <:+ (N.st k).l then
    match N.kind k, N.bkind k with
    | some (x, X), none =>
        if hX : (ctxOf (N.fcl k)).ref x = some (.VTypeDia X) ∧
            (ctxOf (N.st k).l).ref (.root (.free (N.cx k))) = some X then
          retStepWB hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2 hX.1 hX.2
        else N.st k
    | some (x, X), some (e, E) =>
        if hX : (ctxOf (N.fcl k)).ref x = some (.VTypeDia X) ∧
            (ctxOf (N.st k).l).ref (.root (.free (N.cx k))) = some X ∧
            (ctxOf (N.bcl k)).ref e = some (.VTypeDia E) ∧
            (ctxOf (N.st p).l).ref (.root (.free (N.bcx k))) = some E then
          retStepWDB hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2 hX.1 hX.2.1 hX.2.2.1
            hX.2.2.2
        else N.st k
    | none, none => retStepB hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2
    | none, some (e, X) =>
        if hX : (ctxOf (N.bcl k)).ref e = some (.VTypeDia X) ∧
            (ctxOf (N.st p).l).ref (.root (.free (N.bcx k))) = some X then
          retStepXB hS (suffix_next h.2.1 h.1) h.2.2.1 hX.1 hX.2 h.2.2.2.1 h.2.2.2.2
        else N.st k
  else N.st k

/-- ⭐Give the parent's next variable an image in the child `k`, under strong B. -/
noncomputable def realFS (hS : ModalSys.BStrong = true) (N : NetSt σ) : Node → NetSt σ
  | [] => N
  | c :: p =>
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        (N.setSt (c :: p) (N.fwdStepS hS (c :: p) p)).setFwd (c :: p)
          (nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p))
          (extImg (N.fimg (c :: p)) (N.fcl (c :: p)).length (N.st (c :: p)).l.length)
      else N

theorem fwdStepS_ok {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {c : ℕ}
    {p : Node} (hk : N.Live (c :: p)) (hlt : (N.fcl (c :: p)).length < (N.st p).l.length) :
    Theory.IsMCS (N.fwdStepS hS (c :: p) p).M ∧ Grows (N.st (c :: p)) (N.fwdStepS hS (c :: p) p) ∧
      RetDataB hS ModalSys.T rfl (N.st p) (N.fwdStepS hS (c :: p) p) (N.kind (c :: p))
        (N.bkind (c :: p))
        (N.cx (c :: p)) (N.bcx (c :: p))
        (nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p))
        (extImg (N.fimg (c :: p)) (N.fcl (c :: p)).length (N.st (c :: p)).l.length)
        (N.bcl (c :: p)) (N.bimg (c :: p)) := by
  have hr := hN.retB c p hk
  have hp := hN.mcs p hk.1
  have hkM := hN.mcs _ hk
  unfold RetOkB at hr
  unfold fwdStepS
  generalize N.kind (c :: p) = kd at hr ⊢
  generalize N.bkind (c :: p) = bkd at hr ⊢
  cases kd with
  | none =>
      cases bkd with
      | none =>
          obtain ⟨hF, -⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, -⟩ := id hF
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          obtain ⟨h₁, h₂, h₃⟩ := retStepB_ok hS (suffix_next hs hlt) himgt himgs ht hp hkM hF
          exact ⟨h₁, h₂, h₃, retStepB_rev hS (suffix_next hs hlt) himgt himgs ht hp hkM hF⟩
      | some eX =>
          obtain ⟨e, X⟩ := eX
          obtain ⟨hF, -⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, hx, hcx, -⟩ := id hF
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          dsimp only
          rw [dif_pos ⟨hx, hcx⟩]
          obtain ⟨h₁, h₂, h₃⟩ :=
            retStepXB_ok hS (suffix_next hs hlt) himgt hx hcx himgs ht hp hkM hF
          exact ⟨h₁, h₂, h₃,
            retStepXB_rev hS (suffix_next hs hlt) himgt hx hcx himgs ht hp hkM hF⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      cases bkd with
      | none =>
          obtain ⟨hW, -⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, hx, hcx, -⟩ := id hW
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          dsimp only
          rw [dif_pos ⟨hx, hcx⟩]
          obtain ⟨h₁, h₂, h₃⟩ :=
            retStepWB_ok hS (suffix_next hs hlt) himgt himgs ht hx hcx hp hkM hW
          exact ⟨h₁, h₂, h₃,
            retStepWB_rev hS (suffix_next hs hlt) himgt himgs ht hx hcx hp hkM hW⟩
      | some eE =>
          obtain ⟨e, E⟩ := eE
          obtain ⟨hF, -⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, -⟩ := id hF
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          dsimp only
          rw [dif_pos ⟨hx, hcxw, he, hcxv⟩]
          obtain ⟨h₁, h₂, h₃⟩ :=
            retStepWDB_ok hS (suffix_next hs hlt) himgt himgs ht hx hcxw he hcxv hp hkM hF
          exact ⟨h₁, h₂, h₃,
            retStepWDB_rev hS (suffix_next hs hlt) himgt himgs ht hx hcxw he hcxv hp hkM hF⟩

/-- ⭐Realising forward under strong B preserves the invariants. -/
theorem GoodS.realFS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {k : Node}
    (hk : N.Live k) : (N.realFS hS k).GoodS hS := by
  match k with
  | [] => exact hN
  | c :: p =>
      simp only [NetSt.realFS]
      split_ifs with hlt
      · obtain ⟨hmcs, hg, hrd⟩ := fwdStepS_ok hN hk hlt
        have hN₁ := hN.setSt hk hg hmcs
        refine ⟨fun s hs => hN₁.mcs s ((live_setFwd _ _ _ _ s).mp hs), fun c' p' hk' => ?_⟩
        rw [live_setFwd] at hk'
        by_cases he : (c' :: p' : Node) = c :: p
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he.symm
          unfold RetOkB
          simp only [setFwd, Function.update_self]
          rw [setSt_ne _ _ (fun h => ne_parent c p h.symm), setSt_self]
          exact hrd
        · have := hN₁.retB c' p' hk'
          unfold RetOkB at this ⊢
          simp only [setFwd, Function.update_of_ne he]
          exact this
      · exact hN

/-! ## Realising back -/

open Classical in
/-- The parent grown by the image of the child `k`'s next variable, under strong B (`retStepB`, or
    `retStepXB` along the witness for a witness child). -/
noncomputable def backStepS (hS : ModalSys.BStrong = true) (N : NetSt σ) (k p : Node) :
    NodeSt σ :=
  if h : (N.bcl k).length < (N.st k).l.length ∧ N.bcl k <:+ (N.st k).l ∧
      ImgOk (N.fcl k) (ctxOf (N.st k).l) (N.fimg k) ∧
      ImgOk (N.bcl k) (ctxOf (N.st p).l) (N.bimg k) ∧ N.fcl k <:+ (N.st p).l then
    match N.kind k, N.bkind k with
    | some (x, X), none =>
        if hX : (ctxOf (N.fcl k)).ref x = some (.VTypeDia X) ∧
            (ctxOf (N.st k).l).ref (.root (.free (N.cx k))) = some X then
          retStepXB hS (suffix_next h.2.1 h.1) h.2.2.1 hX.1 hX.2 h.2.2.2.1 h.2.2.2.2
        else N.st p
    | some (x, X), some (e, E) =>
        if hX : (ctxOf (N.bcl k)).ref e = some (.VTypeDia E) ∧
            (ctxOf (N.st p).l).ref (.root (.free (N.bcx k))) = some E ∧
            (ctxOf (N.fcl k)).ref x = some (.VTypeDia X) ∧
            (ctxOf (N.st k).l).ref (.root (.free (N.cx k))) = some X then
          retStepWDB hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2 hX.1 hX.2.1 hX.2.2.1
            hX.2.2.2
        else N.st p
    | none, none => retStepB hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2
    | none, some (e, X) =>
        if hX : (ctxOf (N.bcl k)).ref e = some (.VTypeDia X) ∧
            (ctxOf (N.st p).l).ref (.root (.free (N.bcx k))) = some X then
          retStepWB hS (suffix_next h.2.1 h.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2 hX.1 hX.2
        else N.st p
  else N.st p

/-- ⭐Give the child `k`'s next variable an image in its parent, under strong B. -/
noncomputable def realBS (hS : ModalSys.BStrong = true) (N : NetSt σ) : Node → NetSt σ
  | [] => N
  | c :: p =>
      if (N.bcl (c :: p)).length < (N.st (c :: p)).l.length then
        (N.setSt p (N.backStepS hS (c :: p) p)).setBack (c :: p)
          (nextTy (N.st (c :: p)).l (N.bcl (c :: p)) :: N.bcl (c :: p))
          (extImg (N.bimg (c :: p)) (N.bcl (c :: p)).length (N.st p).l.length)
      else N

theorem backStepS_ok {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {c : ℕ}
    {p : Node} (hk : N.Live (c :: p))
    (hlt : (N.bcl (c :: p)).length < (N.st (c :: p)).l.length) :
    Theory.IsMCS (N.backStepS hS (c :: p) p).M ∧ Grows (N.st p) (N.backStepS hS (c :: p) p) ∧
      RetDataB hS ModalSys.T rfl (N.backStepS hS (c :: p) p) (N.st (c :: p)) (N.kind (c :: p))
        (N.bkind (c :: p)) (N.cx (c :: p)) (N.bcx (c :: p))
        (N.fcl (c :: p)) (N.fimg (c :: p))
        (nextTy (N.st (c :: p)).l (N.bcl (c :: p)) :: N.bcl (c :: p))
        (extImg (N.bimg (c :: p)) (N.bcl (c :: p)).length (N.st p).l.length) := by
  have hr := hN.retB c p hk
  have hp := hN.mcs p hk.1
  have hkM := hN.mcs _ hk
  unfold RetOkB at hr
  unfold backStepS
  generalize N.kind (c :: p) = kd at hr ⊢
  generalize N.bkind (c :: p) = bkd at hr ⊢
  cases kd with
  | none =>
      cases bkd with
      | none =>
          obtain ⟨-, hB⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, -⟩ := id hB
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          obtain ⟨h₁, h₂, h₃⟩ := retStepB_ok hS (suffix_next hs hlt) himgt himgs ht hkM hp hB
          exact ⟨h₁, h₂, retStepB_rev hS (suffix_next hs hlt) himgt himgs ht hkM hp hB, h₃⟩
      | some eX =>
          obtain ⟨e, X⟩ := eX
          obtain ⟨-, hW⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, hx, hcx, -⟩ := id hW
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          dsimp only
          rw [dif_pos ⟨hx, hcx⟩]
          obtain ⟨h₁, h₂, h₃⟩ :=
            retStepWB_ok hS (suffix_next hs hlt) himgt himgs ht hx hcx hkM hp hW
          exact ⟨h₁, h₂,
            retStepWB_rev hS (suffix_next hs hlt) himgt himgs ht hx hcx hkM hp hW, h₃⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      cases bkd with
      | none =>
          obtain ⟨-, hX⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, hx, hcx, -⟩ := id hX
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          dsimp only
          rw [dif_pos ⟨hx, hcx⟩]
          obtain ⟨h₁, h₂, h₃⟩ :=
            retStepXB_ok hS (suffix_next hs hlt) himgt hx hcx himgs ht hkM hp hX
          exact ⟨h₁, h₂,
            retStepXB_rev hS (suffix_next hs hlt) himgt hx hcx himgs ht hkM hp hX, h₃⟩
      | some eE =>
          obtain ⟨e, E⟩ := eE
          obtain ⟨-, hB⟩ := hr
          obtain ⟨hs, himgs, ht, himgt, hx, hcxw, he, hcxv, -⟩ := id hB
          rw [dif_pos ⟨hlt, hs, himgt, himgs, ht⟩]
          dsimp only
          rw [dif_pos ⟨hx, hcxw, he, hcxv⟩]
          obtain ⟨h₁, h₂, h₃⟩ :=
            retStepWDB_ok hS (suffix_next hs hlt) himgt himgs ht hx hcxw he hcxv hkM hp hB
          exact ⟨h₁, h₂,
            retStepWDB_rev hS (suffix_next hs hlt) himgt himgs ht hx hcxw he hcxv hkM hp hB, h₃⟩

/-- ⭐Realising back under strong B preserves the invariants. -/
theorem GoodS.realBS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {k : Node}
    (hk : N.Live k) : (N.realBS hS k).GoodS hS := by
  match k with
  | [] => exact hN
  | c :: p =>
      simp only [NetSt.realBS]
      split_ifs with hlt
      · obtain ⟨hmcs, hg, hrd⟩ := backStepS_ok hN hk hlt
        have hN₁ := hN.setSt hk.1 hg hmcs
        refine ⟨fun s hs => hN₁.mcs s ((live_setBack _ _ _ _ s).mp hs), fun c' p' hk' => ?_⟩
        rw [live_setBack] at hk'
        by_cases he : (c' :: p' : Node) = c :: p
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he.symm
          unfold RetOkB
          simp only [setBack, Function.update_self]
          rw [setSt_ne _ _ (ne_parent c p), setSt_self]
          exact hrd
        · have := hN₁.retB c' p' hk'
          unfold RetOkB at this ⊢
          simp only [setBack, Function.update_of_ne he]
          exact this
      · exact hN

/-! ## Henkin witnesses -/

/-- A Henkin step leaves the network or grows the node. -/
theorem henk_cases {N : NetSt σ} {s : Node} (hM : Theory.IsMCS (N.st s).M) (P : NetSt σ → Prop)
    (hP : P N)
    (hset : ∀ t, Grows (N.st s) t → Theory.IsMCS t.M → P (N.setSt s t))
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : P (N.henk s o) := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.henk]
  split_ifs with h
  · split
    · split_ifs with hmem
      · obtain ⟨h₁, h₂⟩ := henk_grow hM (Theory.Derives.of_mem hmem)
        exact hset _ h₂ h₁
      · exact hP
    · rename_i A ψ
      split_ifs with hmem
      · have hex : Theory.Derives (N.st s).M
            (.ex A (WFF.mono ((ctxOf_le_of_suffix h).insert _ A) ψ).neg) :=
          ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hmem,
            ⟨Proof.exNeg_of_negAll _⟩⟩
        obtain ⟨h₁, h₂⟩ := henk_grow hM hex
        exact hset _ h₂ h₁
      · exact hP
    · exact hP
  · exact hP

/-- ⭐Henkin witnesses preserve the invariants under strong B. -/
theorem GoodS.henk {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : (N.henk s o).GoodS hS :=
  henk_cases (hN.mcs s hs) (·.GoodS hS) hN (fun _ hg ht => hN.setSt hs hg ht) o

/-! ## Children -/

/-- A new child whose arrows carry the invariants keeps them. -/
theorem GoodS.newChild {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) {kd : Option (VarSymb × VarType)} {cx : ℕ} {t : NodeSt σ}
    {fimg₀ : ℕ → ℕ} {bcl₀ : List VarType} {bimg₀ : ℕ → ℕ} {bkd₀ : Option (VarSymb × VarType)}
    {bcx₀ : ℕ} (ht : Theory.IsMCS t.M)
    (hr : RetDataB hS ModalSys.T rfl (N.st s) t kd bkd₀ cx bcx₀ (N.st s).l fimg₀ bcl₀ bimg₀) :
    (N.newChild s kd cx t fimg₀ bcl₀ bimg₀ bkd₀ bcx₀).GoodS hS := by
  have hks : (N.nch s :: s : Node) ≠ s := ne_parent _ s
  have hold : ∀ k, N.Live k → k ≠ N.nch s :: s := fun k hk h => not_live_new s (h ▸ hk)
  refine ⟨fun k hk => ?_, fun c p hk => ?_⟩
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
      have := hN.retB c p hk
      unfold RetOkB at this ⊢
      change RetDataB hS ModalSys.T rfl (Function.update N.st _ t p)
        (Function.update N.st _ t (c :: p))
        (Function.update N.kind _ kd (c :: p)) (Function.update N.bkind _ bkd₀ (c :: p))
        (Function.update N.cx _ cx (c :: p)) (Function.update N.bcx _ bcx₀ (c :: p))
        (Function.update N.fcl _ (N.st s).l (c :: p)) (Function.update N.fimg _ fimg₀ (c :: p))
        (Function.update N.bcl _ bcl₀ (c :: p)) (Function.update N.bimg _ bimg₀ (c :: p))
      simp only [Function.update_of_ne hne, Function.update_of_ne hpne]
      exact this
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      unfold RetOkB
      change RetDataB hS ModalSys.T rfl (Function.update N.st _ t p)
        (Function.update N.st _ t (N.nch p :: p))
        (Function.update N.kind _ kd _) (Function.update N.bkind _ bkd₀ _)
        (Function.update N.cx _ cx _) (Function.update N.bcx _ bcx₀ _)
        (Function.update N.fcl _ (N.st p).l _) (Function.update N.fimg _ fimg₀ _)
        (Function.update N.bcl _ bcl₀ _) (Function.update N.bimg _ bimg₀ _)
      simp only [Function.update_self, Function.update_of_ne hks.symm]
      exact hr

/-- Creating a child leaves the network or adds a child with a good seed. -/
theorem mkChild_cases {N : NetSt σ} {s : Node} (hM : Theory.IsMCS (N.st s).M)
    (P : NetSt σ → Prop) (hP : P N)
    (hnew : ∀ kd cx t, Theory.IsMCS t.M → FwdData (N.st s) t kd cx (N.st s).l id →
      P (N.newChild s kd cx t))
    (o : Σ l : List VarType, WFF σ (ctxOf l) 0) : P (N.mkChild s o) := by
  obtain ⟨l, φ⟩ := o
  simp only [NetSt.mkChild]
  split_ifs with h
  · split
    · rename_i ψ
      split_ifs with hmem
      · exact hP
      · obtain ⟨hS, ht⟩ := complete_spec (child_consistent hM
          (φ := WFF.mono (ctxOf_le_of_suffix h).boxIn ψ) hmem)
        exact hnew none 0 _ ht ⟨List.suffix_refl _, childImg _,
          fun ψ' hψ' => hS (Or.inr ⟨ψ', hψ', rfl⟩)⟩
    · rename_i x hx ψ
      split_ifs with hmem
      · split
        · rename_i X hX
          obtain ⟨hS, ht⟩ := complete_spec (childX_consistent hM hX
            (φ := WFF.mono ((ctxOf_le_of_suffix h).diaIn x) ψ) hmem)
          exact hnew (some (x, X)) (N.st s).l.length _ ht
            ⟨List.suffix_refl _, childXImg _ X, hX, childX_cx _ X,
              fun ψ' hψ' => hS (Or.inr ⟨ψ', hψ', rfl⟩)⟩
        · exact hP
      · exact hP
    · exact hP
  · exact hP

/-- ⭐Creating a child preserves the invariants under strong B: its arrows are born with them. -/
theorem GoodS.mkChild {hS : ModalSys.BStrong = true} (hB : ModalSys.B = true) {N : NetSt σ}
    (hN : N.GoodS hS) {s : Node} (hs : N.Live s) (o : Σ l : List VarType, WFF σ (ctxOf l) 0) :
    (N.mkChild s o).GoodS hS :=
  mkChild_cases (hN.mcs s hs) (·.GoodS hS) hN
    (fun _ _ _ ht hf => hN.newChild hs ht (RetDataB.birth hS hB (hN.mcs s hs) ht hf)) o

/-! ## The chain under strong B -/

open Classical in
/-- Perform one operation under strong B, at a live node only. -/
noncomputable def applyOpS (hS : ModalSys.BStrong = true) (N : NetSt σ) : Op σ → NetSt σ
  | .inl (s, o) => if N.Live s then N.henk s o else N
  | .inr (.inl (s, o)) => if N.Live s then N.mkChild s o else N
  | .inr (.inr (.inl k)) => if N.Live k then N.realFS hS k else N
  | .inr (.inr (.inr k)) => if N.Live k then N.realBS hS k else N

theorem GoodS.applyOpS {hS : ModalSys.BStrong = true} (hB : ModalSys.B = true) {N : NetSt σ}
    (hN : N.GoodS hS) (o : Op σ) : (N.applyOpS hS o).GoodS hS := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | k
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact hN.henk h o
    · exact hN
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact hN.mkChild hB h o
    · exact hN
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact hN.realFS h
    · exact hN
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact hN.realBS h
    · exact hN

theorem Ext.realFS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {k : Node}
    (hk : N.Live k) : Ext N (N.realFS hS k) := by
  match k with
  | [] => exact Ext.refl N
  | c :: p =>
      simp only [NetSt.realFS]
      split_ifs with hlt
      · obtain ⟨_, hg, _⟩ := fwdStepS_ok hN hk hlt
        exact (Ext.setSt hg).trans (Ext.setFwd _)
      · exact Ext.refl N

theorem Ext.realBS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {k : Node}
    (hk : N.Live k) : Ext N (N.realBS hS k) := by
  match k with
  | [] => exact Ext.refl N
  | c :: p =>
      simp only [NetSt.realBS]
      split_ifs with hlt
      · obtain ⟨_, hg, _⟩ := backStepS_ok hN hk hlt
        exact (Ext.setSt hg).trans (Ext.setBack _)
      · exact Ext.refl N

theorem Ext.applyOpS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) (o : Op σ) :
    Ext N (N.applyOpS hS o) := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | k
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact Ext.henk hN.good h o
    · exact Ext.refl N
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact Ext.mkChild h o
    · exact Ext.refl N
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact Ext.realFS hN h
    · exact Ext.refl N
  · simp only [NetSt.applyOpS]
    split_ifs with h
    · exact Ext.realBS hN h
    · exact Ext.refl N

theorem GoodS.init (hS : ModalSys.BStrong = true) {l₀ : List VarType}
    {M₀ : Set (WFF σ (ctxOf l₀) 0)} (h : Theory.IsMCS M₀) : (init M₀).GoodS hS :=
  ⟨fun _ _ => h, fun _ _ hk => absurd (init_live hk) (by simp)⟩

/-! ## Aliases -/

/-- ⭐Aliases preserve the invariants under strong B. -/
theorem GoodS.mkAlias {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) (o : AliasObl σ) : (N.mkAlias s o).GoodS hS := by
  obtain ⟨l, A, a, tm⟩ := o
  simp only [NetSt.mkAlias]
  split_ifs with h
  · obtain ⟨h₁, h₂, -⟩ := aliasStep_ok (hN.mcs s hs) (Term.mono (ctxOf_le_of_suffix h) tm)
    exact hN.setSt hs h₂ h₁
  · exact hN

theorem Ext.mkAlias {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS) {s : Node}
    (hs : N.Live s) (o : AliasObl σ) : Ext N (N.mkAlias s o) := by
  obtain ⟨l, A, a, tm⟩ := o
  simp only [NetSt.mkAlias]
  split_ifs with h
  · exact Ext.setSt (aliasStep_ok (hN.mcs s hs) (Term.mono (ctxOf_le_of_suffix h) tm)).2.1
  · exact Ext.refl N

end NetSt

end BArrow

end V12M
