import QML.QML_v12m_BLimitPre
import QML.QML_v12m_BCanonDom

/-!
# QML v12m — B's arrow model: the limit of the network

The canonical model's data (`BData`) from the chain of networks.

* **Worlds** are the nodes ever created.  A node's stages are the rounds from its birth on
  (`nodeWorld`): stage `i` is round `birth + i`.  Henkin witnesses come from `henk_ex`.
* **Accessibility** is the tree's edges, both ways; it is symmetric.
* An **arrow's images** are those committed at some round (`fimgL`, `bimgL`); later rounds keep
  them.  A stage `i` of the source is sent along the arrow at the first stage of the target by
  which its variables are all committed (`stg`, from `fwd_total`, `back_total`).
* ⭐`bdata`: transfer along the arrow is the network's, read through its committed part
  (`Transfer.apply`, …); existence is `child_box` and `child_dia`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour] {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
  (C : FairChain M₀)

/-! ## Worlds -/

/-- The nodes ever created. -/
def Born (k : Node) : Prop := ∃ n, (C.net n).Live k

open Classical in
/-- The round at which a node is created. -/
noncomputable def birth {k : Node} (hk : Born C k) : ℕ := Nat.find hk

open Classical in
theorem live_birth {k : Node} (hk : Born C k) {n : ℕ} (hn : birth C hk ≤ n) :
    (C.net n).Live k :=
  C.live_mono hn (Nat.find_spec hk)

variable {C} in
open Classical in
theorem birth_le {k : Node} (hk : Born C k) {n : ℕ} (hn : (C.net n).Live k) :
    birth C hk ≤ n :=
  Nat.find_min' hk hn

theorem le_birth {k : Node} (hk : Born C k) {n : ℕ} (hn : ¬ (C.net n).Live k) :
    n < birth C hk := by
  by_contra h
  exact hn (live_birth C hk (not_lt.mp h))

/-- ⭐A node as a world: its stages are the rounds from its birth on. -/
noncomputable def nodeWorld (k : Node) (hk : Born C k) : BWorld σ where
  l i := ((C.net (birth C hk + i)).st k).l
  suf {i j} h := C.lang_suffix (by omega) (live_birth C hk (Nat.le_add_right _ i))
  M i := ((C.net (birth C hk + i)).st k).M
  mcs i := (C.good _).mcs k (live_birth C hk (Nat.le_add_right _ i))
  sub {i j} h φ hφ := ((C.ext (by omega : birth C hk + i ≤ birth C hk + j)).grows k
    (live_birth C hk (Nat.le_add_right _ i))).sub φ hφ
  exW {i A ψ} hmem := by
    obtain ⟨m, hnm, hle, c, hc, hm⟩ :=
      C.henk_ex (live_birth C hk (Nat.le_add_right _ i)) hmem
    obtain ⟨j, rfl⟩ : ∃ j, m = birth C hk + j := ⟨m - birth C hk, by omega⟩
    exact ⟨j, by omega, c, hc, hm⟩
  allW {i A ψ} hmem := by
    obtain ⟨m, hnm, hle, a, t, hm⟩ :=
      C.henk_negAll (live_birth C hk (Nat.le_add_right _ i)) hmem
    obtain ⟨j, rfl⟩ : ∃ j, m = birth C hk + j := ⟨m - birth C hk, by omega⟩
    exact ⟨j, by omega, a, t, hm⟩

/-- The worlds of the limit. -/
abbrev LW : Type := {k : Node // Born C k}

/-- Accessibility: the tree's edges, both ways. -/
def LR (s t : LW C) : Prop := (∃ c, t.1 = c :: s.1) ∨ ∃ c, s.1 = c :: t.1

variable {C} in
theorem LR.symm {s t : LW C} (h : LR C s t) : LR C t s := Or.symm h

variable {C} in
/-- The network has no loops: an edge joins a node to its child. -/
theorem LR.irrefl (s : LW C) : ¬ LR C s s := by
  rintro (⟨c, h⟩ | ⟨c, h⟩) <;> exact List.cons_ne_self c s.1 h.symm


variable {C} in
/-- A world's variables at a stage. -/
noncomputable abbrev lat (s : LW C) (i : ℕ) : List VarType :=
  ((C.net (birth C s.2 + i)).st s.1).l

/-! ## Committed images -/

open Classical in
/-- A child's committed image of a parent variable. -/
noncomputable def fimgL (k : Node) (r : ℕ) : ℕ :=
  if h : ∃ m, (C.net m).Live k ∧ r < ((C.net m).fcl k).length then
    (C.net (Nat.find h)).fimg k r
  else 0

open Classical in
/-- A parent's committed image of a child variable. -/
noncomputable def bimgL (k : Node) (r : ℕ) : ℕ :=
  if h : ∃ m, (C.net m).Live k ∧ r < ((C.net m).bcl k).length then
    (C.net (Nat.find h)).bimg k r
  else 0

open Classical in
theorem fimgL_eq {k : Node} {m r : ℕ} (hm : (C.net m).Live k)
    (hr : r < ((C.net m).fcl k).length) : fimgL C k r = (C.net m).fimg k r := by
  have h : ∃ m, (C.net m).Live k ∧ r < ((C.net m).fcl k).length := ⟨m, hm, hr⟩
  rw [fimgL, dif_pos h]
  have hs := Nat.find_spec h
  exact ((C.ext (Nat.find_min' h ⟨hm, hr⟩)).fimg k hs.1 r hs.2).symm

open Classical in
theorem bimgL_eq {k : Node} {m r : ℕ} (hm : (C.net m).Live k)
    (hr : r < ((C.net m).bcl k).length) : bimgL C k r = (C.net m).bimg k r := by
  have h : ∃ m, (C.net m).Live k ∧ r < ((C.net m).bcl k).length := ⟨m, hm, hr⟩
  rw [bimgL, dif_pos h]
  have hs := Nat.find_spec h
  exact ((C.ext (Nat.find_min' h ⟨hm, hr⟩)).bimg k hs.1 r hs.2).symm

open Classical in
/-- The images along an edge: committed forward images into a child, back images into a
    parent. -/
noncomputable def limg (s t : LW C) : ℕ → ℕ :=
  if ∃ c, t.1 = c :: s.1 then fimgL C t.1 else bimgL C s.1

open Classical in
/-- The committed variables along an edge at a round. -/
noncomputable def ccl (s t : LW C) (n : ℕ) : List VarType :=
  if ∃ c, t.1 = c :: s.1 then (C.net n).fcl t.1 else (C.net n).bcl s.1

/-! ## Stages along an edge -/

/-- A stage `j` of the target where stage `i` of the source is committed. -/
def StgP (s t : LW C) (i j : ℕ) : Prop :=
  birth C s.2 + i ≤ birth C t.2 + j ∧ (lat s i).length ≤ (ccl C s t (birth C t.2 + j)).length

theorem fwd_total' {n c : ℕ} {p : Node} (hk : (C.net n).Live (c :: p)) {L : ℕ}
    (hL : L ≤ ((C.net n).st p).l.length) :
    ∃ m, n ≤ m ∧ L ≤ ((C.net m).fcl (c :: p)).length := by
  rcases L with _ | L
  · exact ⟨n, le_rfl, Nat.zero_le _⟩
  · obtain ⟨m, hnm, hm⟩ := C.fwd_total hk (r := L) (by omega)
    exact ⟨m, hnm, hm⟩

theorem back_total' {n c : ℕ} {p : Node} (hk : (C.net n).Live (c :: p)) {L : ℕ}
    (hL : L ≤ ((C.net n).st (c :: p)).l.length) :
    ∃ m, n ≤ m ∧ L ≤ ((C.net m).bcl (c :: p)).length := by
  rcases L with _ | L
  · exact ⟨n, le_rfl, Nat.zero_le _⟩
  · obtain ⟨m, hnm, hm⟩ := C.back_total hk (r := L) (by omega)
    exact ⟨m, hnm, hm⟩

open Classical in
theorem stg_exists {s t : LW C} (h : LR C s t) (i : ℕ) : ∃ j, StgP C s t i j := by
  set n := max (birth C s.2 + i) (birth C t.2)
  have hsn : (C.net n).Live s.1 := live_birth C s.2 (by omega)
  have htn : (C.net n).Live t.1 := live_birth C t.2 (le_max_right _ _)
  have hL : (lat s i).length ≤ ((C.net n).st s.1).l.length :=
    (C.lang_suffix (le_max_left _ _) (live_birth C s.2 (Nat.le_add_right _ i))).length_le
  have key : ∃ m, n ≤ m ∧ (lat s i).length ≤ (ccl C s t m).length := by
    rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [hc] at htn
      obtain ⟨m, hnm, hm⟩ := fwd_total' C htn hL
      refine ⟨m, hnm, ?_⟩
      rw [ccl, if_pos ⟨c, hc⟩, hc]
      exact hm
    · have hnot : ¬ ∃ c, t.1 = c :: s.1 := by
        rintro ⟨c', hc'⟩
        have := congrArg List.length hc
        have := congrArg List.length hc'
        simp only [List.length_cons] at *
        omega
      rw [hc] at hsn hL
      obtain ⟨m, hnm, hm⟩ := back_total' C hsn hL
      refine ⟨m, hnm, ?_⟩
      rw [ccl, if_neg hnot, hc]
      exact hm
  obtain ⟨m, hnm, hm⟩ := key
  refine ⟨m - birth C t.2, ?_, ?_⟩ <;> rw [show birth C t.2 + (m - birth C t.2) = m by omega]
  · omega
  · exact hm

open Classical in
/-- ⭐The stage of the target where stage `i` of the source is committed. -/
noncomputable def lstg (s t : LW C) (i : ℕ) : ℕ :=
  if h : ∃ j, StgP C s t i j then Nat.find h else 0

open Classical in
theorem lstg_spec {s t : LW C} (h : LR C s t) (i : ℕ) : StgP C s t i (lstg C s t i) := by
  have he := stg_exists C h i
  rw [lstg, dif_pos he]
  exact Nat.find_spec he


/-! ## The arrow at a stage -/

variable {C} in
theorem not_fwd_of_back {s t : LW C} {c : ℕ} (hc : s.1 = c :: t.1) : ¬ ∃ c, t.1 = c :: s.1 := by
  rintro ⟨c', hc'⟩
  have h₁ := congrArg List.length hc
  have h₂ := congrArg List.length hc'
  simp only [List.length_cons] at h₁ h₂
  omega

/-- Along a forward edge, stage `i` is committed at the target's stage. -/
theorem fwd_at {s t : LW C} {c : ℕ} (hc : t.1 = c :: s.1) (i : ℕ) :
    lat s i <:+ (C.net (birth C t.2 + lstg C s t i)).fcl t.1 ∧
    (∀ r < (lat s i).length,
      (C.net (birth C t.2 + lstg C s t i)).fimg t.1 r = limg C s t r) ∧
    (C.net (birth C t.2 + lstg C s t i)).FwdOk t.1 s.1 := by
  classical
  obtain ⟨hle, hlen⟩ := lstg_spec C (Or.inl ⟨c, hc⟩) i
  set m := birth C t.2 + lstg C s t i
  rw [ccl, if_pos ⟨c, hc⟩] at hlen
  have htm : (C.net m).Live t.1 := live_birth C t.2 (Nat.le_add_right _ _)
  have hfwd : (C.net m).FwdOk t.1 s.1 := by
    have := (C.good m).fwd c s.1 (hc ▸ htm)
    rwa [← hc] at this
  rcases id hfwd with ⟨hsuf, _, _⟩
  have hls : lat s i <:+ ((C.net m).st s.1).l :=
    C.lang_suffix hle (live_birth C s.2 (Nat.le_add_right _ i))
  refine ⟨List.suffix_of_suffix_length_le hls hsuf hlen, fun r hr => ?_, hfwd⟩
  rw [limg, if_pos ⟨c, hc⟩, fimgL_eq C htm (by omega)]

/-- Along a back edge, stage `i` is committed at the target's stage. -/
theorem back_at {s t : LW C} {c : ℕ} (hc : s.1 = c :: t.1) (i : ℕ) :
    lat s i <:+ (C.net (birth C t.2 + lstg C s t i)).bcl s.1 ∧
    (∀ r < (lat s i).length,
      (C.net (birth C t.2 + lstg C s t i)).bimg s.1 r = limg C s t r) ∧
    (C.net (birth C t.2 + lstg C s t i)).BackOk s.1 t.1 := by
  classical
  obtain ⟨hle, hlen⟩ := lstg_spec C (Or.inr ⟨c, hc⟩) i
  set m := birth C t.2 + lstg C s t i
  rw [ccl, if_neg (not_fwd_of_back hc)] at hlen
  have hsm : (C.net m).Live s.1 := live_birth C s.2 (by omega)
  have hback : (C.net m).BackOk s.1 t.1 := by
    have := (C.good m).back c t.1 (hc ▸ hsm)
    rwa [← hc] at this
  rcases id hback with ⟨hsuf, _, _⟩
  have hls : lat s i <:+ ((C.net m).st s.1).l :=
    C.lang_suffix hle (live_birth C s.2 (Nat.le_add_right _ i))
  refine ⟨List.suffix_of_suffix_length_le hls hsuf hlen, fun r hr => ?_, hback⟩
  rw [limg, if_neg (not_fwd_of_back hc), bimgL_eq C hsm (by omega)]

/-- ⭐**The limit's images are injective** on a stage's variables: at the round where they are
    committed the network's map is, and agrees with the limit's (`NetSt.InjOk`). -/
theorem limg_inj {s t : LW C} (h : LR C s t) (i : ℕ) {r r' : ℕ} (hr : r < (lat s i).length)
    (hr' : r' < (lat s i).length) (e : limg C s t r = limg C s t r') : r = r' := by
  classical
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨hsuf, hag, -⟩ := fwd_at C hc i
    have htm : (C.net (birth C t.2 + lstg C s t i)).Live t.1 :=
      live_birth C t.2 (Nat.le_add_right _ _)
    have hinj := ((C.inj (birth C t.2 + lstg C s t i)) c s.1 (hc ▸ htm)).1
    rw [← hc] at hinj
    refine hinj r r' (lt_of_lt_of_le hr hsuf.length_le) (lt_of_lt_of_le hr' hsuf.length_le) ?_
    rw [hag r hr, hag r' hr', e]
  · obtain ⟨hle, -⟩ := lstg_spec C (Or.inr ⟨c, hc⟩) i
    obtain ⟨hsuf, hag, -⟩ := back_at C hc i
    have hsm : (C.net (birth C t.2 + lstg C s t i)).Live s.1 := live_birth C s.2 (by omega)
    have hinj := ((C.inj (birth C t.2 + lstg C s t i)) c t.1 (hc ▸ hsm)).2
    rw [← hc] at hinj
    refine hinj r r' (lt_of_lt_of_le hr hsuf.length_le) (lt_of_lt_of_le hr' hsuf.length_le) ?_
    rw [hag r hr, hag r' hr', e]

/-- ⭐The images of a stage's variables are declared at the target's stage. -/
theorem limgOk {s t : LW C} (h : LR C s t) (i : ℕ) :
    ImgOk (lat s i) (ctxOf (lat t (lstg C s t i))) (limg C s t) := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨hsuf, hag, hfwd⟩ := fwd_at C hc i
    obtain ⟨_, himg, _⟩ := hfwd
    exact (himg.suffix hsuf).congr hag
  · obtain ⟨hsuf, hag, hback⟩ := back_at C hc i
    obtain ⟨_, himg, _⟩ := hback
    exact (himg.suffix hsuf).congr hag

/-- A stage's theory grows into later rounds. -/
theorem grow_stage (s : LW C) (i : ℕ) {m : ℕ} (hm : birth C s.2 + i ≤ m) :
    Grows ((C.net (birth C s.2 + i)).st s.1) ((C.net m).st s.1) :=
  (C.ext hm).grows s.1 (live_birth C s.2 (Nat.le_add_right _ i))

/-- ⭐Necessity transfer along an edge. -/
theorem ltr {s t : LW C} (h : LR C s t) (i : ℕ) (ψ : WFF σ (ctxOf (lat s i)).boxIn 0)
    (hψ : .box ψ ∈ ((C.net (birth C s.2 + i)).st s.1).M) :
    WFF.subst (arrowIdx (limg C s t)) (arrowS σ _ (limg C s t))
      (ok_arrowS (limgOk C h i)) (coh_arrowS (limgOk C h i))
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
        ((C.net (birth C t.2 + lstg C s t i)).st t.1).M := by
  have hle := (lstg_spec C h i).1
  have hg := grow_stage C s i hle
  have hψ' := hg.sub _ hψ
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨hsuf, hag, hfwd⟩ := fwd_at C hc i
    obtain ⟨hsuf', himg, htr⟩ := hfwd
    have hsm := (C.good _).mcs s.1
      (live_birth C s.2 (hle.trans' (Nat.le_add_right _ i)))
    cases hk : (C.net (birth C t.2 + lstg C s t i)).kind t.1 with
    | none =>
        rw [hk] at htr
        exact Transfer.apply htr hsuf hag (limgOk C (Or.inl ⟨c, hc⟩) i) _ ψ hψ'
    | some xX =>
        obtain ⟨x, X⟩ := xX
        rw [hk] at htr
        obtain ⟨hx, hcx, htrX⟩ := htr
        exact TransferX.applyBox hsm htrX hsuf hag (limgOk C (Or.inl ⟨c, hc⟩) i) _ ψ
          hψ'
  · obtain ⟨hsuf, hag, hback⟩ := back_at C hc i
    obtain ⟨hsuf', himg, htr⟩ := hback
    exact Transfer.apply htr hsuf hag (limgOk C (Or.inr ⟨c, hc⟩) i) _ ψ hψ'


/-! ## Witness edges -/

open Classical in
/-- A forward edge into a witness child records the witness; so does a back-witness child's
    back edge (docs §11.20). -/
noncomputable def lkd (s t : LW C) : Option (VarSymb × VarType) :=
  if ∃ c, t.1 = c :: s.1 then (C.net (birth C t.2)).kind t.1
  else if ∃ c, s.1 = c :: t.1 then (C.net (birth C s.2)).bkind s.1
  else none

open Classical in
/-- The content variable of a witness edge: the witness child's, or a back-witness child's
    parent's. -/
noncomputable def lcx (s t : LW C) : ℕ :=
  if ∃ c, t.1 = c :: s.1 then (C.net (birth C t.2)).cx t.1 else (C.net (birth C s.2)).bcx s.1

variable {C} in
/-- A witness edge is forward into a witness child, or back from a back-witness child. -/
theorem lkd_cases {s t : LW C} {x : VarSymb} {X : VarType} (hk : lkd C s t = some (x, X)) :
    (∃ c, t.1 = c :: s.1) ∨ ((∃ c, s.1 = c :: t.1) ∧
      (C.net (birth C s.2)).bkind s.1 = some (x, X)) := by
  classical
  unfold lkd at hk
  split_ifs at hk with h₁ h₂
  · exact Or.inl h₁
  · exact Or.inr ⟨h₂, hk⟩

variable {C} in
theorem lkdR {s t : LW C} {x : VarSymb} {X : VarType} (hk : lkd C s t = some (x, X)) :
    LR C s t :=
  (lkd_cases hk).elim Or.inl fun h => Or.inr h.1

theorem kind_at (t : LW C) {m : ℕ} (hm : birth C t.2 ≤ m) :
    (C.net m).kind t.1 = (C.net (birth C t.2)).kind t.1 :=
  (C.ext hm).kind t.1 (live_birth C t.2 le_rfl)

theorem cx_at (t : LW C) {m : ℕ} (hm : birth C t.2 ≤ m) :
    (C.net m).cx t.1 = (C.net (birth C t.2)).cx t.1 :=
  (C.ext hm).cx t.1 (live_birth C t.2 le_rfl)

theorem bkind_at (t : LW C) {m : ℕ} (hm : birth C t.2 ≤ m) :
    (C.net m).bkind t.1 = (C.net (birth C t.2)).bkind t.1 :=
  (C.ext hm).bkind t.1 (live_birth C t.2 le_rfl)

theorem bcx_at (t : LW C) {m : ℕ} (hm : birth C t.2 ≤ m) :
    (C.net m).bcx t.1 = (C.net (birth C t.2)).bcx t.1 :=
  (C.ext hm).bcx t.1 (live_birth C t.2 le_rfl)

/-- Along a forward witness edge, the arrow at a stage is a witness arrow. -/
theorem fwdX_at {s t : LW C} {x : VarSymb} {X : VarType} (hc : ∃ c, t.1 = c :: s.1)
    (hk : lkd C s t = some (x, X)) (i : ℕ) :
    lat s i <:+ (C.net (birth C t.2 + lstg C s t i)).fcl t.1 ∧
    (∀ r < (lat s i).length,
      (C.net (birth C t.2 + lstg C s t i)).fimg t.1 r = limg C s t r) ∧
    FwdData ((C.net (birth C t.2 + lstg C s t i)).st s.1)
      ((C.net (birth C t.2 + lstg C s t i)).st t.1) (some (x, X)) (lcx C s t)
      ((C.net (birth C t.2 + lstg C s t i)).fcl t.1)
      ((C.net (birth C t.2 + lstg C s t i)).fimg t.1) := by
  classical
  obtain ⟨c, hc⟩ := hc
  obtain ⟨hsuf, hag, hfwd⟩ := fwd_at C hc i
  have hkd : (C.net (birth C t.2)).kind t.1 = some (x, X) := by
    rw [lkd, if_pos ⟨c, hc⟩] at hk
    exact hk
  refine ⟨hsuf, hag, ?_⟩
  unfold NetSt.FwdOk at hfwd
  rw [kind_at C t (Nat.le_add_right _ _), hkd, cx_at C t (Nat.le_add_right _ _)]
    at hfwd
  rw [lcx, if_pos ⟨c, hc⟩]
  exact hfwd

/-- Along a back-witness edge, the arrow at a stage is a back-witness arrow (`BackXData`). -/
theorem backX_at {s t : LW C} {x : VarSymb} {X : VarType} (hc : ∃ c, s.1 = c :: t.1)
    (hbk : (C.net (birth C s.2)).bkind s.1 = some (x, X)) (i : ℕ) :
    lat s i <:+ (C.net (birth C t.2 + lstg C s t i)).bcl s.1 ∧
    (∀ r < (lat s i).length,
      (C.net (birth C t.2 + lstg C s t i)).bimg s.1 r = limg C s t r) ∧
    BackXData ((C.net (birth C t.2 + lstg C s t i)).st s.1)
      ((C.net (birth C t.2 + lstg C s t i)).st t.1) (some (x, X)) (lcx C s t)
      ((C.net (birth C t.2 + lstg C s t i)).bcl s.1)
      ((C.net (birth C t.2 + lstg C s t i)).bimg s.1) := by
  classical
  obtain ⟨c, hc⟩ := hc
  obtain ⟨hle, -⟩ := lstg_spec C (Or.inr ⟨c, hc⟩) i
  obtain ⟨hsuf, hag, -⟩ := back_at C hc i
  have hbs : birth C s.2 ≤ birth C t.2 + lstg C s t i := by omega
  have hsm : (C.net (birth C t.2 + lstg C s t i)).Live s.1 := live_birth C s.2 hbs
  have hd := C.backX (birth C t.2 + lstg C s t i) c t.1 (hc ▸ hsm)
  rw [← hc, bkind_at C s hbs, hbk, bcx_at C s hbs] at hd
  refine ⟨hsuf, hag, ?_⟩
  rw [lcx, if_neg (not_fwd_of_back hc)]
  exact hd

/-- The content variable is declared at the content type. -/
theorem lhcx {s t : LW C} {x : VarSymb} {X : VarType} (hk : lkd C s t = some (x, X))
    (i : ℕ) : (ctxOf (lat t (lstg C s t i))).ref (.root (.free (lcx C s t))) = some X := by
  rcases lkd_cases hk with hc | ⟨hc, hbk⟩
  · obtain ⟨_, _, _, _, _, hcx, _⟩ := fwdX_at C hc hk i
    exact hcx
  · obtain ⟨_, _, hd⟩ := backX_at C hc hbk i
    obtain ⟨_, _, _, hcx, _⟩ := hd
    exact hcx

/-- The recorded content type is the witness's. -/
theorem lhxX {s t : LW C} {x : VarSymb} {X : VarType} (hk : lkd C s t = some (x, X))
    (i : ℕ) (X' : VarType) (h : (ctxOf (lat s i)).ref x = some (.VTypeDia X')) : X' = X := by
  rcases lkd_cases hk with hc | ⟨hc, hbk⟩
  · obtain ⟨hsuf, _, _, _, hx, _, _⟩ := fwdX_at C hc hk i
    have h1 := (ctxOf_le_of_suffix hsuf).ref h
    rw [hx] at h1
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm
  · obtain ⟨hsuf, _, hd⟩ := backX_at C hc hbk i
    obtain ⟨_, _, hx, _, _⟩ := hd
    have h1 := (ctxOf_le_of_suffix hsuf).ref h
    rw [hx] at h1
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1.symm

/-- ⭐`□_x` transfer along a witness edge, forward or back. -/
theorem ltrX {s t : LW C} {x : VarSymb} {X : VarType} (hk : lkd C s t = some (x, X))
    (i : ℕ) (hx : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (lat s i)).diaIn x) 0)
    (hψ : WFF.boxx x ⟨X, hx⟩ ψ ∈ ((C.net (birth C s.2 + i)).st s.1).M) :
    WFF.subst (arrowXIdx (limg C s t) x (lcx C s t))
      (arrowXS σ _ (limg C s t) x (lcx C s t))
      (ok_arrowXS (limgOk C (lkdR hk) i) hx (lhcx C hk i))
      (coh_arrowXS (limgOk C (lkdR hk) i) hx (lhcx C hk i))
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
        ((C.net (birth C t.2 + lstg C s t i)).st t.1).M := by
  have hψ' := (grow_stage C s i (lstg_spec C (lkdR hk) i).1).sub _ hψ
  rcases lkd_cases hk with hc | ⟨hc, hbk⟩
  · obtain ⟨hsuf, hag, _, _, _, _, htr⟩ := fwdX_at C hc hk i
    exact TransferX.apply htr hsuf hag (limgOk C (lkdR hk) i) hx _ ψ hψ'
  · obtain ⟨hsuf, hag, hd⟩ := backX_at C hc hbk i
    obtain ⟨_, _, _, _, htr⟩ := hd
    exact TransferX.apply htr hsuf hag (limgOk C (lkdR hk) i) hx _ ψ hψ'


/-! ## Existence -/

/-- ⭐A failing necessity has a child where its translation fails. -/
theorem lex (s : LW C) (i : ℕ) (ψ : WFF σ (ctxOf (lat s i)).boxIn 0)
    (hψ : .box ψ ∉ ((C.net (birth C s.2 + i)).st s.1).M) :
    ∃ (t : LW C) (h : LR C s t), (WFF.subst (arrowIdx (limg C s t))
      (arrowS σ _ (limg C s t)) (ok_arrowS (limgOk C h i))
      (coh_arrowS (limgOk C h i)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ).neg ∈
        ((C.net (birth C t.2 + lstg C s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, M', hnot, hlive, hst, _, hfcl, hfimg, hmem⟩ :=
    C.child_box (live_birth C s.2 (Nat.le_add_right _ i)) hψ
  let t : LW C := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (C.net m).nch s.1 :: s.1 := rfl
  have h : LR C s t := Or.inl ⟨_, hc⟩
  refine ⟨t, h, ?_⟩
  have hbt : m < birth C t.2 := le_birth C t.2 hnot
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C t.2 + lstg C s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hm := hg.sub _ hmem
  have hag : ∀ r < (lat s i).length, id r = limg C s t r := fun r hr => by
    have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
      rw [hc, hfcl]
      exact lt_of_lt_of_le hr hsuf.length_le
    rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C hlive hlen, hfimg]
  have e : WFF.mono (ctxOf_le_of_suffix hg.suf) (childArrow ((C.net m).st s.1).l
      (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ)) =
      WFF.subst (arrowIdx (limg C s t)) (arrowS σ _ (limg C s t))
        (ok_arrowS (limgOk C h i)) (coh_arrowS (limgOk C h i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
    rw [WFF.mono_subst, WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots]
    refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
    rw [arrowS_mono]
    exact sim_arrowS hag
  rw [← e]
  exact hm

/-- ⭐A possibility has a witness child where its translation holds. -/
theorem lexX (s : LW C) (i : ℕ) (x : VarSymb) (X : VarType)
    (hx : (ctxOf (lat s i)).ref x = some (.VTypeDia X)) (ψ : WFF σ ((ctxOf (lat s i)).diaIn x) 0)
    (hψ : WFF.dia x ⟨X, hx⟩ ψ ∈ ((C.net (birth C s.2 + i)).st s.1).M) :
    ∃ (t : LW C) (hk : lkd C s t = some (x, X)),
      WFF.subst (arrowXIdx (limg C s t) x (lcx C s t))
        (arrowXS σ _ (limg C s t) x (lcx C s t))
        (ok_arrowXS (limgOk C (lkdR hk) i) hx (lhcx C hk i))
        (coh_arrowXS (limgOk C (lkdR hk) i) hx (lhcx C hk i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
          ((C.net (birth C t.2 + lstg C s t i)).st t.1).M := by
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
  have hbt : m < birth C t.2 := le_birth C t.2 hnot
  have hbt' : birth C t.2 ≤ m + 1 := birth_le t.2 hlive
  have hkd : lkd C s t = some (x, X') := by
    rw [lkd, if_pos ⟨_, hc⟩, ← kind_at C t hbt']
    exact hkind
  have hlcx : lcx C s t = ((C.net m).st s.1).l.length := by
    rw [lcx, if_pos ⟨_, hc⟩]
    exact (cx_at C t hbt').symm.trans hcxe
  refine ⟨t, hkd, ?_⟩
  have hg : Grows ((C.net (m + 1)).st ((C.net m).nch s.1 :: s.1))
      ((C.net (birth C t.2 + lstg C s t i)).st t.1) :=
    (C.ext (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hm := hg.sub _ hmem
  have hag : ∀ r < (lat s i).length, id r = limg C s t r := fun r hr => by
    have hlen : r < ((C.net (m + 1)).fcl t.1).length := by
      rw [hc, hfcl]
      exact lt_of_lt_of_le hr hsuf.length_le
    rw [limg, if_pos ⟨_, hc⟩, fimgL_eq C hlive hlen, hfimg]
  have e : WFF.mono (ctxOf_le_of_suffix hg.suf) (childXArrow ((C.net m).st s.1).l hX
      (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ)) =
      WFF.subst (arrowXIdx (limg C s t) x (lcx C s t))
        (arrowXS σ _ (limg C s t) x (lcx C s t))
        (ok_arrowXS (limgOk C (lkdR hkd) i) hx (lhcx C hkd i))
        (coh_arrowXS (limgOk C (lkdR hkd) i) hx (lhcx C hkd i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
    rw [WFF.mono_subst, WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots]
    refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
    rw [arrowXS_mono, hlcx]
    exact sim_arrowXS hag
  rw [← e]
  exact hm

/-- ⭐Every world with an arrow out has an **unlabelled** arrow out: `□⊥` fails there (`ltr`),
    so `child_box` gives it a child, of kind `none`. -/
theorem lunl {s t : LW C} (h : LR C s t) : ∃ t', LR C s t' ∧ lkd C s t' = none := by
  classical
  have hψ : WFF.box (.bot : WFF σ (ctxOf (lat s 0)).boxIn 0) ∉
      ((C.net (birth C s.2 + 0)).st s.1).M := fun hb =>
    ((nodeWorld C t.1 t.2).mcs _).bot_not_mem (ltr C h 0 .bot hb)
  obtain ⟨m, _, _, _, _, hlive, _, hkind, _⟩ :=
    C.child_box (live_birth C s.2 (Nat.le_add_right _ 0)) hψ
  let t' : LW C := ⟨(C.net m).nch s.1 :: s.1, m + 1, hlive⟩
  refine ⟨t', Or.inl ⟨_, rfl⟩, ?_⟩
  unfold lkd
  rw [if_pos ⟨_, rfl⟩, ← kind_at C t' (birth_le t'.2 hlive)]
  exact hkind

/-! ## The canonical data -/

/-- ⭐**The data of B's canonical model**, from the limit of the network, with strong B off (strong
    B's limit, with its own fields, is `bdataS`). -/
noncomputable def bdata (hW : ModalSys.BStrong = false) : BData σ where
  W := LW C
  actual := ⟨[], 0, trivial⟩
  w s := nodeWorld C s.1 s.2
  R := LR C
  symm := LR.symm
  irrefl := LR.irrefl
  img := limg C
  stg := lstg C
  imgOk h i := limgOk C h i
  tr h i ψ hψ := ltr C h i ψ hψ
  ex s i ψ hψ := lex C s i ψ hψ
  kd := lkd C
  cx := lcx C
  kdR := lkdR
  hcx hk i := lhcx C hk i
  hxX hk i X' h := lhxX C hk i X' h
  trX hk i hx ψ hψ := ltrX C hk i hx ψ hψ
  exX s i x X hx ψ hψ := lexX C s i x X hx ψ hψ
  unl h := lunl C h
  backRel hS := absurd (hW.symm.trans hS) (by decide)
  backRelX hS := absurd (hW.symm.trans hS) (by decide)

end BArrow

end V12M
