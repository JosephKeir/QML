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

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoTFour]
  (hB : ModalSys.B = true) {M₀ : Set (WFF σ (ctxOf []) 0)} (hM₀ : Theory.IsMCS M₀)

/-! ## Worlds -/

variable (M₀) in
/-- The nodes ever created. -/
def Born (k : Node) : Prop := ∃ n, (net M₀ n).Live k

variable (M₀) in
open Classical in
/-- The round at which a node is created. -/
noncomputable def birth {k : Node} (hk : Born M₀ k) : ℕ := Nat.find hk

include hB hM₀

open Classical in
theorem live_birth {k : Node} (hk : Born M₀ k) {n : ℕ} (hn : birth M₀ hk ≤ n) :
    (net M₀ n).Live k :=
  live_mono hB hM₀ hn (Nat.find_spec hk)

omit hB hM₀ in
open Classical in
theorem birth_le {k : Node} (hk : Born M₀ k) {n : ℕ} (hn : (net M₀ n).Live k) :
    birth M₀ hk ≤ n :=
  Nat.find_min' hk hn

theorem le_birth {k : Node} (hk : Born M₀ k) {n : ℕ} (hn : ¬ (net M₀ n).Live k) :
    n < birth M₀ hk := by
  by_contra h
  exact hn (live_birth hB hM₀ hk (not_lt.mp h))

/-- ⭐A node as a world: its stages are the rounds from its birth on. -/
noncomputable def nodeWorld (k : Node) (hk : Born M₀ k) : BWorld σ where
  l i := ((net M₀ (birth M₀ hk + i)).st k).l
  suf {i j} h := lang_suffix hB hM₀ (by omega) (live_birth hB hM₀ hk (Nat.le_add_right _ i))
  M i := ((net M₀ (birth M₀ hk + i)).st k).M
  mcs i := (good_net hB hM₀ _).mcs k (live_birth hB hM₀ hk (Nat.le_add_right _ i))
  sub {i j} h φ hφ := ((ext_net hB hM₀ (by omega : birth M₀ hk + i ≤ birth M₀ hk + j)).grows k
    (live_birth hB hM₀ hk (Nat.le_add_right _ i))).sub φ hφ
  exW {i A ψ} hmem := by
    obtain ⟨m, hnm, hle, a, t, hm⟩ :=
      henk_ex hB hM₀ (live_birth hB hM₀ hk (Nat.le_add_right _ i)) hmem
    obtain ⟨j, rfl⟩ : ∃ j, m = birth M₀ hk + j := ⟨m - birth M₀ hk, by omega⟩
    exact ⟨j, by omega, a, t, hm⟩
  allW {i A ψ} hmem := by
    obtain ⟨m, hnm, hle, a, t, hm⟩ :=
      henk_negAll hB hM₀ (live_birth hB hM₀ hk (Nat.le_add_right _ i)) hmem
    obtain ⟨j, rfl⟩ : ∃ j, m = birth M₀ hk + j := ⟨m - birth M₀ hk, by omega⟩
    exact ⟨j, by omega, a, t, hm⟩

omit hB hM₀

variable (M₀) in
/-- The worlds of the limit. -/
abbrev LW : Type := {k : Node // Born M₀ k}

variable (M₀) in
/-- Accessibility: the tree's edges, both ways. -/
def LR (s t : LW M₀) : Prop := (∃ c, t.1 = c :: s.1) ∨ ∃ c, s.1 = c :: t.1

theorem LR.symm {s t : LW M₀} (h : LR M₀ s t) : LR M₀ t s := Or.symm h


/-- A world's variables at a stage. -/
noncomputable abbrev lat (s : LW M₀) (i : ℕ) : List VarType :=
  ((net M₀ (birth M₀ s.2 + i)).st s.1).l

/-! ## Committed images -/

variable (M₀) in
open Classical in
/-- A child's committed image of a parent variable. -/
noncomputable def fimgL (k : Node) (r : ℕ) : ℕ :=
  if h : ∃ m, (net M₀ m).Live k ∧ r < ((net M₀ m).fcl k).length then
    (net M₀ (Nat.find h)).fimg k r
  else 0

variable (M₀) in
open Classical in
/-- A parent's committed image of a child variable. -/
noncomputable def bimgL (k : Node) (r : ℕ) : ℕ :=
  if h : ∃ m, (net M₀ m).Live k ∧ r < ((net M₀ m).bcl k).length then
    (net M₀ (Nat.find h)).bimg k r
  else 0

include hB hM₀ in
open Classical in
theorem fimgL_eq {k : Node} {m r : ℕ} (hm : (net M₀ m).Live k)
    (hr : r < ((net M₀ m).fcl k).length) : fimgL M₀ k r = (net M₀ m).fimg k r := by
  have h : ∃ m, (net M₀ m).Live k ∧ r < ((net M₀ m).fcl k).length := ⟨m, hm, hr⟩
  rw [fimgL, dif_pos h]
  have hs := Nat.find_spec h
  exact ((ext_net hB hM₀ (Nat.find_min' h ⟨hm, hr⟩)).fimg k hs.1 r hs.2).symm

include hB hM₀ in
open Classical in
theorem bimgL_eq {k : Node} {m r : ℕ} (hm : (net M₀ m).Live k)
    (hr : r < ((net M₀ m).bcl k).length) : bimgL M₀ k r = (net M₀ m).bimg k r := by
  have h : ∃ m, (net M₀ m).Live k ∧ r < ((net M₀ m).bcl k).length := ⟨m, hm, hr⟩
  rw [bimgL, dif_pos h]
  have hs := Nat.find_spec h
  exact ((ext_net hB hM₀ (Nat.find_min' h ⟨hm, hr⟩)).bimg k hs.1 r hs.2).symm

variable (M₀) in
open Classical in
/-- The images along an edge: committed forward images into a child, back images into a
    parent. -/
noncomputable def limg (s t : LW M₀) : ℕ → ℕ :=
  if ∃ c, t.1 = c :: s.1 then fimgL M₀ t.1 else bimgL M₀ s.1

variable (M₀) in
open Classical in
/-- The committed variables along an edge at a round. -/
noncomputable def ccl (s t : LW M₀) (n : ℕ) : List VarType :=
  if ∃ c, t.1 = c :: s.1 then (net M₀ n).fcl t.1 else (net M₀ n).bcl s.1

/-! ## Stages along an edge -/

variable (M₀) in
/-- A stage `j` of the target where stage `i` of the source is committed. -/
def StgP (s t : LW M₀) (i j : ℕ) : Prop :=
  birth M₀ s.2 + i ≤ birth M₀ t.2 + j ∧ (lat s i).length ≤ (ccl M₀ s t (birth M₀ t.2 + j)).length

include hB hM₀ in
theorem fwd_total' {n c : ℕ} {p : Node} (hk : (net M₀ n).Live (c :: p)) {L : ℕ}
    (hL : L ≤ ((net M₀ n).st p).l.length) :
    ∃ m, n ≤ m ∧ L ≤ ((net M₀ m).fcl (c :: p)).length := by
  rcases L with _ | L
  · exact ⟨n, le_rfl, Nat.zero_le _⟩
  · obtain ⟨m, hnm, hm⟩ := fwd_total hB hM₀ hk (r := L) (by omega)
    exact ⟨m, hnm, hm⟩

include hB hM₀ in
theorem back_total' {n c : ℕ} {p : Node} (hk : (net M₀ n).Live (c :: p)) {L : ℕ}
    (hL : L ≤ ((net M₀ n).st (c :: p)).l.length) :
    ∃ m, n ≤ m ∧ L ≤ ((net M₀ m).bcl (c :: p)).length := by
  rcases L with _ | L
  · exact ⟨n, le_rfl, Nat.zero_le _⟩
  · obtain ⟨m, hnm, hm⟩ := back_total hB hM₀ hk (r := L) (by omega)
    exact ⟨m, hnm, hm⟩

include hB hM₀ in
open Classical in
theorem stg_exists {s t : LW M₀} (h : LR M₀ s t) (i : ℕ) : ∃ j, StgP M₀ s t i j := by
  set n := max (birth M₀ s.2 + i) (birth M₀ t.2)
  have hsn : (net M₀ n).Live s.1 := live_birth hB hM₀ s.2 (by omega)
  have htn : (net M₀ n).Live t.1 := live_birth hB hM₀ t.2 (le_max_right _ _)
  have hL : (lat s i).length ≤ ((net M₀ n).st s.1).l.length :=
    (lang_suffix hB hM₀ (le_max_left _ _) (live_birth hB hM₀ s.2 (Nat.le_add_right _ i))).length_le
  have key : ∃ m, n ≤ m ∧ (lat s i).length ≤ (ccl M₀ s t m).length := by
    rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [hc] at htn
      obtain ⟨m, hnm, hm⟩ := fwd_total' hB hM₀ htn hL
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
      obtain ⟨m, hnm, hm⟩ := back_total' hB hM₀ hsn hL
      refine ⟨m, hnm, ?_⟩
      rw [ccl, if_neg hnot, hc]
      exact hm
  obtain ⟨m, hnm, hm⟩ := key
  refine ⟨m - birth M₀ t.2, ?_, ?_⟩ <;> rw [show birth M₀ t.2 + (m - birth M₀ t.2) = m by omega]
  · omega
  · exact hm

variable (M₀) in
open Classical in
/-- ⭐The stage of the target where stage `i` of the source is committed. -/
noncomputable def lstg (s t : LW M₀) (i : ℕ) : ℕ :=
  if h : ∃ j, StgP M₀ s t i j then Nat.find h else 0

include hB hM₀ in
open Classical in
theorem lstg_spec {s t : LW M₀} (h : LR M₀ s t) (i : ℕ) : StgP M₀ s t i (lstg M₀ s t i) := by
  have he := stg_exists hB hM₀ h i
  rw [lstg, dif_pos he]
  exact Nat.find_spec he


/-! ## The arrow at a stage -/

theorem not_fwd_of_back {s t : LW M₀} {c : ℕ} (hc : s.1 = c :: t.1) : ¬ ∃ c, t.1 = c :: s.1 := by
  rintro ⟨c', hc'⟩
  have h₁ := congrArg List.length hc
  have h₂ := congrArg List.length hc'
  simp only [List.length_cons] at h₁ h₂
  omega

include hB hM₀ in
/-- Along a forward edge, stage `i` is committed at the target's stage. -/
theorem fwd_at {s t : LW M₀} {c : ℕ} (hc : t.1 = c :: s.1) (i : ℕ) :
    lat s i <:+ (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).fcl t.1 ∧
    (∀ r < (lat s i).length,
      (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).fimg t.1 r = limg M₀ s t r) ∧
    (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).FwdOk t.1 s.1 := by
  classical
  obtain ⟨hle, hlen⟩ := lstg_spec hB hM₀ (Or.inl ⟨c, hc⟩) i
  set m := birth M₀ t.2 + lstg M₀ s t i
  rw [ccl, if_pos ⟨c, hc⟩] at hlen
  have htm : (net M₀ m).Live t.1 := live_birth hB hM₀ t.2 (Nat.le_add_right _ _)
  have hfwd : (net M₀ m).FwdOk t.1 s.1 := by
    have := (good_net hB hM₀ m).fwd c s.1 (hc ▸ htm)
    rwa [← hc] at this
  rcases id hfwd with ⟨hsuf, _, _⟩
  have hls : lat s i <:+ ((net M₀ m).st s.1).l :=
    lang_suffix hB hM₀ hle (live_birth hB hM₀ s.2 (Nat.le_add_right _ i))
  refine ⟨List.suffix_of_suffix_length_le hls hsuf hlen, fun r hr => ?_, hfwd⟩
  rw [limg, if_pos ⟨c, hc⟩, fimgL_eq hB hM₀ htm (by omega)]

include hB hM₀ in
/-- Along a back edge, stage `i` is committed at the target's stage. -/
theorem back_at {s t : LW M₀} {c : ℕ} (hc : s.1 = c :: t.1) (i : ℕ) :
    lat s i <:+ (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).bcl s.1 ∧
    (∀ r < (lat s i).length,
      (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).bimg s.1 r = limg M₀ s t r) ∧
    (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).BackOk s.1 t.1 := by
  classical
  obtain ⟨hle, hlen⟩ := lstg_spec hB hM₀ (Or.inr ⟨c, hc⟩) i
  set m := birth M₀ t.2 + lstg M₀ s t i
  rw [ccl, if_neg (not_fwd_of_back hc)] at hlen
  have hsm : (net M₀ m).Live s.1 := live_birth hB hM₀ s.2 (by omega)
  have hback : (net M₀ m).BackOk s.1 t.1 := by
    have := (good_net hB hM₀ m).back c t.1 (hc ▸ hsm)
    rwa [← hc] at this
  rcases id hback with ⟨hsuf, _, _⟩
  have hls : lat s i <:+ ((net M₀ m).st s.1).l :=
    lang_suffix hB hM₀ hle (live_birth hB hM₀ s.2 (Nat.le_add_right _ i))
  refine ⟨List.suffix_of_suffix_length_le hls hsuf hlen, fun r hr => ?_, hback⟩
  rw [limg, if_neg (not_fwd_of_back hc), bimgL_eq hB hM₀ hsm (by omega)]

include hB hM₀ in
/-- ⭐The images of a stage's variables are declared at the target's stage. -/
theorem limgOk {s t : LW M₀} (h : LR M₀ s t) (i : ℕ) :
    ImgOk (lat s i) (ctxOf (lat t (lstg M₀ s t i))) (limg M₀ s t) := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨hsuf, hag, hfwd⟩ := fwd_at hB hM₀ hc i
    obtain ⟨_, himg, _⟩ := hfwd
    exact (himg.suffix hsuf).congr hag
  · obtain ⟨hsuf, hag, hback⟩ := back_at hB hM₀ hc i
    obtain ⟨_, himg, _⟩ := hback
    exact (himg.suffix hsuf).congr hag

include hB hM₀ in
/-- A stage's theory grows into later rounds. -/
theorem grow_stage (s : LW M₀) (i : ℕ) {m : ℕ} (hm : birth M₀ s.2 + i ≤ m) :
    Grows ((net M₀ (birth M₀ s.2 + i)).st s.1) ((net M₀ m).st s.1) :=
  (ext_net hB hM₀ hm).grows s.1 (live_birth hB hM₀ s.2 (Nat.le_add_right _ i))

include hB hM₀ in
/-- ⭐Necessity transfer along an edge. -/
theorem ltr {s t : LW M₀} (h : LR M₀ s t) (i : ℕ) (ψ : WFF σ (ctxOf (lat s i)).boxIn 0)
    (hψ : .box ψ ∈ ((net M₀ (birth M₀ s.2 + i)).st s.1).M) :
    WFF.subst (arrowIdx (limg M₀ s t)) (arrowS σ _ (limg M₀ s t))
      (ok_arrowS (limgOk hB hM₀ h i)) (coh_arrowS (limgOk hB hM₀ h i))
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
        ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).st t.1).M := by
  have hle := (lstg_spec hB hM₀ h i).1
  have hg := grow_stage hB hM₀ s i hle
  have hψ' := hg.sub _ hψ
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨hsuf, hag, hfwd⟩ := fwd_at hB hM₀ hc i
    obtain ⟨hsuf', himg, htr⟩ := hfwd
    have hsm := (good_net hB hM₀ _).mcs s.1
      (live_birth hB hM₀ s.2 (hle.trans' (Nat.le_add_right _ i)))
    cases hk : (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).kind t.1 with
    | none =>
        rw [hk] at htr
        exact Transfer.apply htr hsuf hag (limgOk hB hM₀ (Or.inl ⟨c, hc⟩) i) _ ψ hψ'
    | some xX =>
        obtain ⟨x, X⟩ := xX
        rw [hk] at htr
        obtain ⟨hx, hcx, htrX⟩ := htr
        exact TransferX.applyBox hsm htrX hsuf hag (limgOk hB hM₀ (Or.inl ⟨c, hc⟩) i) _ ψ
          hψ'
  · obtain ⟨hsuf, hag, hback⟩ := back_at hB hM₀ hc i
    obtain ⟨hsuf', himg, htr⟩ := hback
    exact Transfer.apply htr hsuf hag (limgOk hB hM₀ (Or.inr ⟨c, hc⟩) i) _ ψ hψ'


/-! ## Witness edges -/

variable (M₀) in
open Classical in
/-- A forward edge into a witness child records the witness. -/
noncomputable def lkd (s t : LW M₀) : Option (VarSymb × VarType) :=
  if ∃ c, t.1 = c :: s.1 then (net M₀ (birth M₀ t.2)).kind t.1 else none

variable (M₀) in
/-- The content variable of a witness child. -/
noncomputable def lcx (_s t : LW M₀) : ℕ := (net M₀ (birth M₀ t.2)).cx t.1

theorem lkd_fwd {s t : LW M₀} {x : VarSymb} {X : VarType} (hk : lkd M₀ s t = some (x, X)) :
    ∃ c, t.1 = c :: s.1 := by
  classical
  by_contra h
  rw [lkd, if_neg h] at hk
  cases hk

theorem lkdR {s t : LW M₀} {x : VarSymb} {X : VarType} (hk : lkd M₀ s t = some (x, X)) :
    LR M₀ s t :=
  Or.inl (lkd_fwd hk)

include hB hM₀ in
theorem kind_at (t : LW M₀) {m : ℕ} (hm : birth M₀ t.2 ≤ m) :
    (net M₀ m).kind t.1 = (net M₀ (birth M₀ t.2)).kind t.1 :=
  (ext_net hB hM₀ hm).kind t.1 (live_birth hB hM₀ t.2 le_rfl)

include hB hM₀ in
theorem cx_at (t : LW M₀) {m : ℕ} (hm : birth M₀ t.2 ≤ m) :
    (net M₀ m).cx t.1 = (net M₀ (birth M₀ t.2)).cx t.1 :=
  (ext_net hB hM₀ hm).cx t.1 (live_birth hB hM₀ t.2 le_rfl)

include hB hM₀ in
/-- Along a witness edge, the arrow at a stage is a witness arrow. -/
theorem fwdX_at {s t : LW M₀} {x : VarSymb} {X : VarType} (hk : lkd M₀ s t = some (x, X))
    (i : ℕ) :
    lat s i <:+ (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).fcl t.1 ∧
    (∀ r < (lat s i).length,
      (net M₀ (birth M₀ t.2 + lstg M₀ s t i)).fimg t.1 r = limg M₀ s t r) ∧
    FwdData ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).st s.1)
      ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).st t.1) (some (x, X)) (lcx M₀ s t)
      ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).fcl t.1)
      ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).fimg t.1) := by
  classical
  obtain ⟨c, hc⟩ := lkd_fwd hk
  obtain ⟨hsuf, hag, hfwd⟩ := fwd_at hB hM₀ hc i
  have hkd : (net M₀ (birth M₀ t.2)).kind t.1 = some (x, X) := by
    rw [lkd, if_pos ⟨c, hc⟩] at hk
    exact hk
  refine ⟨hsuf, hag, ?_⟩
  unfold NetSt.FwdOk at hfwd
  rw [kind_at hB hM₀ t (Nat.le_add_right _ _), hkd, cx_at hB hM₀ t (Nat.le_add_right _ _)]
    at hfwd
  exact hfwd

include hB hM₀ in
/-- The content variable is declared at the content type. -/
theorem lhcx {s t : LW M₀} {x : VarSymb} {X : VarType} (hk : lkd M₀ s t = some (x, X))
    (i : ℕ) : (ctxOf (lat t (lstg M₀ s t i))).ref (.root (.free (lcx M₀ s t))) = some X := by
  obtain ⟨_, _, _, _, _, hcx, _⟩ := fwdX_at hB hM₀ hk i
  exact hcx

include hB hM₀ in
/-- The recorded content type is the witness's. -/
theorem lhxX {s t : LW M₀} {x : VarSymb} {X : VarType} (hk : lkd M₀ s t = some (x, X))
    (i : ℕ) (X' : VarType) (h : (ctxOf (lat s i)).ref x = some (.VTypeDia X')) : X' = X := by
  obtain ⟨hsuf, _, _, _, hx, _, _⟩ := fwdX_at hB hM₀ hk i
  have h1 := (ctxOf_le_of_suffix hsuf).ref h
  rw [hx] at h1
  simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
  exact h1.symm

include hB hM₀ in
/-- ⭐`□_x` transfer along a witness edge. -/
theorem ltrX {s t : LW M₀} {x : VarSymb} {X : VarType} (hk : lkd M₀ s t = some (x, X))
    (i : ℕ) (hx : (ctxOf (lat s i)).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (lat s i)).diaIn x) 0)
    (hψ : WFF.boxx x ⟨X, hx⟩ ψ ∈ ((net M₀ (birth M₀ s.2 + i)).st s.1).M) :
    WFF.subst (arrowXIdx (limg M₀ s t) x (lcx M₀ s t))
      (arrowXS σ _ (limg M₀ s t) x (lcx M₀ s t))
      (ok_arrowXS (limgOk hB hM₀ (lkdR hk) i) hx (lhcx hB hM₀ hk i))
      (coh_arrowXS (limgOk hB hM₀ (lkdR hk) i) hx (lhcx hB hM₀ hk i))
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
        ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).st t.1).M := by
  obtain ⟨hsuf, hag, _, _, _, _, htr⟩ := fwdX_at hB hM₀ hk i
  have hψ' := (grow_stage hB hM₀ s i (lstg_spec hB hM₀ (lkdR hk) i).1).sub _ hψ
  exact TransferX.apply htr hsuf hag (limgOk hB hM₀ (lkdR hk) i) hx _ ψ hψ'


/-! ## Existence -/

include hB hM₀ in
/-- ⭐A failing necessity has a child where its translation fails. -/
theorem lex (s : LW M₀) (i : ℕ) (ψ : WFF σ (ctxOf (lat s i)).boxIn 0)
    (hψ : .box ψ ∉ ((net M₀ (birth M₀ s.2 + i)).st s.1).M) :
    ∃ (t : LW M₀) (h : LR M₀ s t), (WFF.subst (arrowIdx (limg M₀ s t))
      (arrowS σ _ (limg M₀ s t)) (ok_arrowS (limgOk hB hM₀ h i))
      (coh_arrowS (limgOk hB hM₀ h i)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ).neg ∈
        ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, M', hnot, hlive, hst, _, hfcl, hfimg, hmem⟩ :=
    child_box hB hM₀ (live_birth hB hM₀ s.2 (Nat.le_add_right _ i)) hψ
  let t : LW M₀ := ⟨(net M₀ m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (net M₀ m).nch s.1 :: s.1 := rfl
  have h : LR M₀ s t := Or.inl ⟨_, hc⟩
  refine ⟨t, h, ?_⟩
  have hbt : m < birth M₀ t.2 := le_birth hB hM₀ t.2 hnot
  have hg : Grows ((net M₀ (m + 1)).st ((net M₀ m).nch s.1 :: s.1))
      ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).st t.1) :=
    (ext_net hB hM₀ (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hm := hg.sub _ hmem
  have hag : ∀ r < (lat s i).length, id r = limg M₀ s t r := fun r hr => by
    have hlen : r < ((net M₀ (m + 1)).fcl t.1).length := by
      rw [hc, hfcl]
      exact lt_of_lt_of_le hr hsuf.length_le
    rw [limg, if_pos ⟨_, hc⟩, fimgL_eq hB hM₀ hlive hlen, hfimg]
  have e : WFF.mono (ctxOf_le_of_suffix hg.suf) (childArrow ((net M₀ m).st s.1).l
      (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ)) =
      WFF.subst (arrowIdx (limg M₀ s t)) (arrowS σ _ (limg M₀ s t))
        (ok_arrowS (limgOk hB hM₀ h i)) (coh_arrowS (limgOk hB hM₀ h i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
    rw [WFF.mono_subst, WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots]
    refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
    rw [arrowS_mono]
    exact sim_arrowS hag
  rw [← e]
  exact hm

include hB hM₀ in
/-- ⭐A possibility has a witness child where its translation holds. -/
theorem lexX (s : LW M₀) (i : ℕ) (x : VarSymb) (X : VarType)
    (hx : (ctxOf (lat s i)).ref x = some (.VTypeDia X)) (ψ : WFF σ ((ctxOf (lat s i)).diaIn x) 0)
    (hψ : WFF.dia x ⟨X, hx⟩ ψ ∈ ((net M₀ (birth M₀ s.2 + i)).st s.1).M) :
    ∃ (t : LW M₀) (hk : lkd M₀ s t = some (x, X)),
      WFF.subst (arrowXIdx (limg M₀ s t) x (lcx M₀ s t))
        (arrowXS σ _ (limg M₀ s t) x (lcx M₀ s t))
        (ok_arrowXS (limgOk hB hM₀ (lkdR hk) i) hx (lhcx hB hM₀ hk i))
        (coh_arrowXS (limgOk hB hM₀ (lkdR hk) i) hx (lhcx hB hM₀ hk i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
          ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).st t.1).M := by
  classical
  obtain ⟨m, _, hsuf, X', hX, M', hnot, hlive, hst, hkind, hcxe, hfcl, hfimg, hmem⟩ :=
    child_dia hB hM₀ (live_birth hB hM₀ s.2 (Nat.le_add_right _ i)) hψ
  obtain rfl : X' = X := by
    have h1 := (ctxOf_le_of_suffix hsuf).ref hx
    rw [hX] at h1
    simp only [Option.some.injEq, VarType.VTypeDia.injEq] at h1
    exact h1
  let t : LW M₀ := ⟨(net M₀ m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (net M₀ m).nch s.1 :: s.1 := rfl
  have hbt : m < birth M₀ t.2 := le_birth hB hM₀ t.2 hnot
  have hbt' : birth M₀ t.2 ≤ m + 1 := birth_le t.2 hlive
  have hkd : lkd M₀ s t = some (x, X') := by
    rw [lkd, if_pos ⟨_, hc⟩, ← kind_at hB hM₀ t hbt']
    exact hkind
  have hlcx : lcx M₀ s t = ((net M₀ m).st s.1).l.length :=
    (cx_at hB hM₀ t hbt').symm.trans hcxe
  refine ⟨t, hkd, ?_⟩
  have hg : Grows ((net M₀ (m + 1)).st ((net M₀ m).nch s.1 :: s.1))
      ((net M₀ (birth M₀ t.2 + lstg M₀ s t i)).st t.1) :=
    (ext_net hB hM₀ (by omega)).grows t.1 hlive
  rw [hst] at hg
  have hm := hg.sub _ hmem
  have hag : ∀ r < (lat s i).length, id r = limg M₀ s t r := fun r hr => by
    have hlen : r < ((net M₀ (m + 1)).fcl t.1).length := by
      rw [hc, hfcl]
      exact lt_of_lt_of_le hr hsuf.length_le
    rw [limg, if_pos ⟨_, hc⟩, fimgL_eq hB hM₀ hlive hlen, hfimg]
  have e : WFF.mono (ctxOf_le_of_suffix hg.suf) (childXArrow ((net M₀ m).st s.1).l hX
      (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ)) =
      WFF.subst (arrowXIdx (limg M₀ s t) x (lcx M₀ s t))
        (arrowXS σ _ (limg M₀ s t) x (lcx M₀ s t))
        (ok_arrowXS (limgOk hB hM₀ (lkdR hkd) i) hx (lhcx hB hM₀ hkd i))
        (coh_arrowXS (limgOk hB hM₀ (lkdR hkd) i) hx (lhcx hB hM₀ hkd i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ := by
    rw [WFF.mono_subst, WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots]
    refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
    rw [arrowXS_mono, hlcx]
    exact sim_arrowXS hag
  rw [← e]
  exact hm

/-! ## The canonical data -/

include hB hM₀ in
/-- ⭐**The data of B's canonical model**, from the limit of the network. -/
noncomputable def bdata : BData σ where
  W := LW M₀
  actual := ⟨[], 0, trivial⟩
  w s := nodeWorld hB hM₀ s.1 s.2
  R := LR M₀
  symm := LR.symm
  img := limg M₀
  stg := lstg M₀
  imgOk h i := limgOk hB hM₀ h i
  tr h i ψ hψ := ltr hB hM₀ h i ψ hψ
  ex s i ψ hψ := lex hB hM₀ s i ψ hψ
  kd := lkd M₀
  cx := lcx M₀
  kdR := lkdR
  hcx hk i := lhcx hB hM₀ hk i
  hxX hk i X' h := lhxX hB hM₀ hk i X' h
  trX hk i hx ψ hψ := ltrX hB hM₀ hk i hx ψ hψ
  exX s i x X hx ψ hψ := lexX hB hM₀ s i x X hx ψ hψ

end BArrow

end V12M
