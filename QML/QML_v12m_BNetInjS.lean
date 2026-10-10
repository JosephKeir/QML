import QML.QML_v12m_BNetS
import QML.QML_v12m_BNetInj

/-!
# QML v12m — strong B's networks: injective images

Strong B's operations keep every arrow's images injective (`NetSt.InjOk`): its realisation steps
commit to the target's next variable, aliases only grow a node, and the three returning
successors are born with a shift forward and one or two distinct variables back
(`mkRetD` and `mkRetXD` ask `y ≠ o`).  ⭐`InjOk.applyOpT`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace NetSt

variable [ModalSys.NoFour]

theorem InjOk.realFS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS)
    (h : N.InjOk) (k : Node) (hk : N.Live k) : (N.realFS hS k).InjOk := by
  match k, hk with
  | [], _ => exact h
  | c :: p, hk =>
      simp only [NetSt.realFS]
      split_ifs
      · obtain ⟨_, himg, _⟩ := hN.good.fwd c p hk
        exact (h.setSt _ _).setFwd ((h c p hk).1.ext himg.lt)
      · exact h

theorem InjOk.realBS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS)
    (h : N.InjOk) (k : Node) (hk : N.Live k) : (N.realBS hS k).InjOk := by
  match k, hk with
  | [], _ => exact h
  | c :: p, hk =>
      simp only [NetSt.realBS]
      split_ifs
      · obtain ⟨_, himg, _⟩ := hN.good.back c p hk
        exact (h.setSt _ _).setBack ((h c p hk).2.ext himg.lt)
      · exact h

theorem InjOk.applyOpS {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS)
    (h : N.InjOk) (o : Op σ) : (N.applyOpS hS o).InjOk := by
  rcases o with ⟨s, o⟩ | ⟨s, o⟩ | k | k
  all_goals
    simp only [NetSt.applyOpS]
    split_ifs with hl
    · first
        | exact h.henk s o
        | exact h.mkChild hl o
        | exact h.realFS hN k hl
        | exact h.realBS hN k hl
    · exact h

omit [ModalSys.NoFour] in
theorem InjOk.mkAlias {N : NetSt σ} (h : N.InjOk) (s : Node) (o : AliasObl σ) :
    (N.mkAlias s o).InjOk := by
  obtain ⟨l, A, a, tm⟩ := o
  simp only [NetSt.mkAlias]
  split_ifs
  · exact h.setSt _ _
  · exact h

theorem InjOk.mkRet {hS : ModalSys.BStrong = true} {N : NetSt σ} (h : N.InjOk) {s : Node}
    (hs : N.Live s) (o : RetObl σ) : (N.mkRet hS s o).InjOk := by
  obtain ⟨l, A, y, Φ⟩ := o
  simp only [NetSt.mkRet]
  split_ifs
  · exact h.newChild hs (InjOn.of_injective Nat.succ_injective) (InjOn.single _ _)
  all_goals exact h

theorem InjOk.mkRetX {hS : ModalSys.BStrong = true} {N : NetSt σ} (h : N.InjOk) {s : Node}
    (hs : N.Live s) (o : RetOblX σ) : (N.mkRetX hS s o).InjOk := by
  obtain ⟨l, A, x, y, Φ⟩ := o
  simp only [NetSt.mkRetX]
  split_ifs
  · split
    · split_ifs
      · exact h.newChild hs (InjOn.of_injective Nat.succ_injective) (InjOn.single _ _)
      · exact h
    · exact h
  all_goals exact h

theorem InjOk.mkRetD {hS : ModalSys.BStrong = true} {N : NetSt σ} (h : N.InjOk) {s : Node}
    (hs : N.Live s) (o : RetOblD σ) : (N.mkRetD hS s o).InjOk := by
  obtain ⟨l, A, X, ⟨y, o, z⟩, Φ⟩ := o
  simp only [NetSt.mkRetD]
  split_ifs with _ _ _ _ hyo
  · refine h.newChild hs (InjOn.of_injective fun a b e => by simpa using e) ?_
    intro r r' hr hr' e
    simp only [List.length_cons, List.length_nil] at hr hr'
    unfold backImgD at e
    split_ifs at e <;> omega
  all_goals exact h

theorem InjOk.mkRetXD {hS : ModalSys.BStrong = true} {N : NetSt σ} (h : N.InjOk) {s : Node}
    (hs : N.Live s) (o : RetOblXD σ) : (N.mkRetXD hS s o).InjOk := by
  obtain ⟨l, A, Xe, x, ⟨y, o, z⟩, Φ⟩ := o
  simp only [NetSt.mkRetXD]
  split_ifs with _ _ _ hyo
  · split
    · split_ifs
      · refine h.newChild hs (InjOn.of_injective fun a b e => by simpa using e) ?_
        intro r r' hr hr' e
        simp only [List.length_cons, List.length_nil] at hr hr'
        unfold backImgD at e
        split_ifs at e <;> omega
      · exact h
    · exact h
  all_goals exact h

/-- ⭐Every operation of strong B keeps the images injective (T off). -/
theorem InjOk.applyOpT {hS : ModalSys.BStrong = true} {N : NetSt σ} (hN : N.GoodS hS)
    (h : N.InjOk) (o : OpS σ) : (N.applyOpT hS o).InjOk := by
  rcases o with o | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩ | ⟨s, o⟩
  · exact h.applyOpS hN o
  all_goals
    simp only [NetSt.applyOpT]
    split_ifs with hl
    · first
        | exact h.mkAlias s o
        | exact h.mkRet hl o
        | exact h.mkRetX hl o
        | exact h.mkRetD hl o
        | exact h.mkRetXD hl o
    · exact h

end NetSt

end BArrow

end V12M
