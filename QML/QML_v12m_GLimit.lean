import QML.QML_v12m_GChain
import QML.QML_v12m_BStaged
import QML.QML_v12m_BLimitPre

/-!
# QML v12m — the growing tree: the limit

The limit of the chain `gnet hF M₀` (as B's `BLimit`):

* **Worlds** are the nodes ever created (`GW`).  A node's stages are the rounds from its birth
  on (`gnodeWorld`, a `BArrow.BWorld`): stage `i` is round `birth + i`.  Henkin witnesses come
  from `henk_ex`, `henk_negAll`.
* **Edges** join a node to its children (`GCh`).  An edge's **entries** are those committed at
  some round (`fmapL`); later rounds keep them.  A stage `i` of the parent is sent along the edge
  at the first stage of the child by which its variables are committed (`glstg`, from
  `fwd_total`).
* ⭐`gltr`, `gltrX`: transfer along an edge — `□` along any edge, `□_x` along an edge made for
  `◇_x` — read through its committed part.
* ⭐`glex`, `glexX`: existence, from the chain's children.
* ⭐`gllift`: every liftable term of a child is the image of a lifted root's kept item.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  (hF : ModalSys.Four = true) {l₀ : List VarType} (M₀ : Set (WFF σ (ctxOf l₀) 0))

/-! ## Worlds -/

/-- The nodes ever created. -/
def GBorn (k : Node) : Prop := ∃ n, (gnet hF M₀ n).Live k

open Classical in
/-- The round at which a node is created. -/
noncomputable def gbirth {k : Node} (hk : GBorn hF M₀ k) : ℕ := Nat.find hk

variable {M₀}

open Classical in
theorem live_gbirth (hM₀ : Theory.IsMCS M₀) {k : Node} (hk : GBorn hF M₀ k) {n : ℕ}
    (hn : gbirth hF M₀ hk ≤ n) : (gnet hF M₀ n).Live k :=
  gnet_live_mono hF hM₀ hn (Nat.find_spec hk)

open Classical in
theorem gbirth_le {k : Node} (hk : GBorn hF M₀ k) {n : ℕ} (hn : (gnet hF M₀ n).Live k) :
    gbirth hF M₀ hk ≤ n :=
  Nat.find_min' hk hn

theorem le_gbirth (hM₀ : Theory.IsMCS M₀) {k : Node} (hk : GBorn hF M₀ k) {n : ℕ}
    (hn : ¬ (gnet hF M₀ n).Live k) : n < gbirth hF M₀ hk := by
  by_contra h
  exact hn (live_gbirth hF hM₀ hk (not_lt.mp h))

/-- ⭐A node as a world: its stages are the rounds from its birth on. -/
noncomputable def gnodeWorld (hM₀ : Theory.IsMCS M₀) (k : Node) (hk : GBorn hF M₀ k) :
    BWorld σ where
  l i := ((gnet hF M₀ (gbirth hF M₀ hk + i)).st k).l
  suf {i j} h := gnet_lang_suffix hF hM₀ (by omega)
    (live_gbirth hF hM₀ hk (Nat.le_add_right _ i))
  M i := ((gnet hF M₀ (gbirth hF M₀ hk + i)).st k).M
  mcs i := (good_gnet hF hM₀ _).mcs k (live_gbirth hF hM₀ hk (Nat.le_add_right _ i))
  sub {i j} h φ hφ := ((ext_gnet hF hM₀
    (by omega : gbirth hF M₀ hk + i ≤ gbirth hF M₀ hk + j)).grows k
      (live_gbirth hF hM₀ hk (Nat.le_add_right _ i))).sub φ hφ
  exW {i A ψ} hmem := by
    obtain ⟨m, hnm, hle, c, hc, hm⟩ :=
      henk_ex hF hM₀ (live_gbirth hF hM₀ hk (Nat.le_add_right _ i)) hmem
    obtain ⟨j, rfl⟩ : ∃ j, m = gbirth hF M₀ hk + j := ⟨m - gbirth hF M₀ hk, by omega⟩
    exact ⟨j, by omega, c, hc, hm⟩
  allW {i A ψ} hmem := by
    obtain ⟨m, hnm, hle, a, t, hm⟩ :=
      henk_negAll hF hM₀ (live_gbirth hF hM₀ hk (Nat.le_add_right _ i)) hmem
    obtain ⟨j, rfl⟩ : ∃ j, m = gbirth hF M₀ hk + j := ⟨m - gbirth hF M₀ hk, by omega⟩
    exact ⟨j, by omega, a, t, hm⟩

variable (M₀)

/-- The worlds of the limit. -/
abbrev GW : Type := {k : Node // GBorn hF M₀ k}

/-- An edge: from a node to its child. -/
def GCh (s t : GW hF M₀) : Prop := ∃ c, t.1 = c :: s.1

variable {hF M₀}

/-- A world's variables at a stage. -/
noncomputable abbrev glat (s : GW hF M₀) (i : ℕ) : List VarType :=
  ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).l

variable (hF M₀)

/-! ## Committed entries -/

open Classical in
/-- An edge's committed entry for an item. -/
noncomputable def fmapL (k : Node) (v : VarSymb) : LEnt σ :=
  if h : ∃ m, (gnet hF M₀ m).Live k ∧
      ∃ T, (ctxOf ((gnet hF M₀ m).fcl k)).kView ((gnet hF M₀ m).kind k) v = some T then
    (gnet hF M₀ (Nat.find h)).fmap k v
  else .inl v

variable {hF M₀}

open Classical in
theorem fmapL_eq (hM₀ : Theory.IsMCS M₀) {k : Node} {m : ℕ} {v : VarSymb} {T : VarType}
    (hm : (gnet hF M₀ m).Live k)
    (hv : (ctxOf ((gnet hF M₀ m).fcl k)).kView ((gnet hF M₀ m).kind k) v = some T) :
    fmapL hF M₀ k v = (gnet hF M₀ m).fmap k v := by
  have h : ∃ m, (gnet hF M₀ m).Live k ∧
      ∃ T, (ctxOf ((gnet hF M₀ m).fcl k)).kView ((gnet hF M₀ m).kind k) v = some T :=
    ⟨m, hm, T, hv⟩
  rw [fmapL, dif_pos h]
  obtain ⟨hs, T', hs'⟩ := Nat.find_spec h
  exact ((ext_gnet hF hM₀ (Nat.find_min' h ⟨hm, T, hv⟩)).fmap k hs v T' hs').symm

/-- The kind of the edge into a node, fixed at its birth. -/
noncomputable def lkd (t : GW hF M₀) : Option VarSymb :=
  (gnet hF M₀ (gbirth hF M₀ t.2)).kind t.1

theorem kind_at (hM₀ : Theory.IsMCS M₀) (t : GW hF M₀) {m : ℕ} (hm : gbirth hF M₀ t.2 ≤ m) :
    (gnet hF M₀ m).kind t.1 = lkd t :=
  (ext_gnet hF hM₀ hm).kind t.1 (live_gbirth hF hM₀ t.2 le_rfl)

/-! ## Stages along an edge -/

/-- A stage `j` of the child where stage `i` of the parent is committed. -/
def GStgP (s t : GW hF M₀) (i j : ℕ) : Prop :=
  gbirth hF M₀ s.2 + i ≤ gbirth hF M₀ t.2 + j ∧
    (glat s i).length ≤ ((gnet hF M₀ (gbirth hF M₀ t.2 + j)).fcl t.1).length

theorem gstg_exists (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) :
    ∃ j, GStgP s t i j := by
  obtain ⟨c, hc⟩ := h
  set n := max (gbirth hF M₀ s.2 + i) (gbirth hF M₀ t.2)
  have htn : (gnet hF M₀ n).Live t.1 := live_gbirth hF hM₀ t.2 (le_max_right _ _)
  have hL : (glat s i).length ≤ ((gnet hF M₀ n).st s.1).l.length :=
    (gnet_lang_suffix hF hM₀ (le_max_left _ _)
      (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i))).length_le
  rw [hc] at htn
  obtain ⟨m, hnm, hm⟩ : ∃ m, n ≤ m ∧ (glat s i).length ≤ ((gnet hF M₀ m).fcl t.1).length := by
    rcases hlen : (glat s i).length with _ | L
    · exact ⟨n, le_rfl, Nat.zero_le _⟩
    · obtain ⟨m, hnm, hm⟩ := fwd_total hF hM₀ htn (r := L) (by omega)
      rw [← hc] at hm
      exact ⟨m, hnm, hm⟩
  refine ⟨m - gbirth hF M₀ t.2, ?_, ?_⟩ <;>
    rw [show gbirth hF M₀ t.2 + (m - gbirth hF M₀ t.2) = m by omega]
  · omega
  · exact hm

open Classical in
/-- ⭐The stage of the child where stage `i` of the parent is committed. -/
noncomputable def glstg (s t : GW hF M₀) (i : ℕ) : ℕ :=
  if h : ∃ j, GStgP s t i j then Nat.find h else 0

open Classical in
theorem glstg_spec (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) :
    GStgP s t i (glstg s t i) := by
  have he := gstg_exists hM₀ h i
  rw [glstg, dif_pos he]
  exact Nat.find_spec he

open Classical in
theorem glstg_monotone (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t)
    {i i' : ℕ} (hii : i ≤ i') : glstg s t i ≤ glstg s t i' := by
  have hP := glstg_spec hM₀ h i'
  have hP' : GStgP s t i (glstg s t i') :=
    ⟨by have := hP.1; omega, le_trans (gnet_lang_suffix hF hM₀ (by omega)
      (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i))).length_le hP.2⟩
  rw [glstg, dif_pos ⟨_, hP'⟩]
  exact Nat.find_min' _ hP'

/-- The round at which stage `i` of the parent is read along the edge. -/
noncomputable abbrev grnd (s t : GW hF M₀) (i : ℕ) : ℕ := gbirth hF M₀ t.2 + glstg s t i

/-! ## The edge at a stage -/

/-- ⭐Along an edge, stage `i` of the parent is committed at the child's stage, with the limit's
    entries. -/
theorem gfwd_at (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    (i : ℕ) :
    glat s i <:+ (gnet hF M₀ (grnd s t i)).fcl t.1 ∧
    (∀ v T, (ctxOf (glat s i)).kView (lkd t) v = some T →
      (gnet hF M₀ (grnd s t i)).fmap t.1 v = fmapL hF M₀ t.1 v) ∧
    FwdData ((gnet hF M₀ (grnd s t i)).st s.1) ((gnet hF M₀ (grnd s t i)).st t.1) (lkd t)
      ((gnet hF M₀ (grnd s t i)).fcl t.1) ((gnet hF M₀ (grnd s t i)).fmap t.1) := by
  obtain ⟨hle, hlen⟩ := glstg_spec hM₀ ⟨c, hc⟩ i
  set m := grnd s t i
  have htm : (gnet hF M₀ m).Live t.1 := live_gbirth hF hM₀ t.2 (Nat.le_add_right _ _)
  have hkd := kind_at hM₀ t (Nat.le_add_right _ (glstg s t i))
  have hfwd : (gnet hF M₀ m).FwdOk t.1 s.1 := by
    have := (good_gnet hF hM₀ m).fwd c s.1 (hc ▸ htm)
    rwa [← hc] at this
  unfold GNetSt.FwdOk at hfwd
  rw [hkd] at hfwd
  obtain ⟨hsuf, _⟩ := id hfwd
  have hls : glat s i <:+ ((gnet hF M₀ m).st s.1).l :=
    gnet_lang_suffix hF hM₀ hle (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i))
  have hsuf' := List.suffix_of_suffix_length_le hls hsuf hlen
  refine ⟨hsuf', fun v T hv => ?_, hfwd⟩
  refine (fmapL_eq hM₀ htm (T := T) ?_).symm
  rw [hkd]
  exact ((ctxOf_le_of_suffix hsuf').kView _) v T hv

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem EntOk.restrict {Γ Γ' Δ : Ctx} {g : VarSymb → LEnt σ} (hle : Γ'.Le Γ)
    (hg : EntOk Γ Δ g) : EntOk Γ' Δ g := fun v T hl hv => hg v T hl (hle v T hv)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem EntOk.congr {Γ Δ : Ctx} {g g' : VarSymb → LEnt σ}
    (hag : ∀ v T, Γ v = some T → g v = g' v) (hg : EntOk Γ Δ g) : EntOk Γ Δ g' :=
  fun v T hl hv => by rw [← hag v T hv]; exact hg v T hl hv

/-- ⭐An edge's committed entries type a stage's view of its kind. -/
theorem gentOk (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) :
    EntOk ((ctxOf (glat s i)).kView (lkd t)) (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨hsuf, hag, hfwd⟩ := gfwd_at hM₀ hc i
  obtain ⟨_, _, hf, _⟩ := hfwd
  exact (hf.restrict ((ctxOf_le_of_suffix hsuf).kView _)).congr hag

/-- …and its `□` view. -/
theorem gentOk_box (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) :
    EntOk ((ctxOf (glat s i)).kView none) (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1) :=
  (gentOk hM₀ h i).restrict (Ctx.le_boxIn_kView _ _)

/-- A stage's theory grows into later rounds. -/
theorem ggrow_stage (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) {m : ℕ}
    (hm : gbirth hF M₀ s.2 + i ≤ m) :
    Grows ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1) ((gnet hF M₀ m).st s.1) :=
  (ext_gnet hF hM₀ hm).grows s.1 (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i))

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- What is necessary is `□_k`-necessary, for either kind. -/
theorem kBox_of_box {Γ Γ₀ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    (hle : Γ₀.Le Γ) (kd : Option VarSymb) (hk : KDecl Γ₀ kd) (ψ : WFF σ Γ₀.boxIn 0)
    (h : WFF.mono hle (.box ψ) ∈ M) :
    WFF.mono hle (kBox kd hk (WFF.mono (Ctx.le_boxIn_kView _ kd) ψ)) ∈ M := by
  cases kd with
  | none =>
      change WFF.box (WFF.mono hle.boxIn (WFF.mono (Ctx.Le.refl _) ψ)) ∈ M
      rw [WFF.mono_mono]
      exact h
  | some x =>
      obtain ⟨X, hX⟩ := hk x rfl
      refine hM.closed ⟨[WFF.mono hle (.box ψ)], fun y hy => by
        rw [List.mem_singleton.mp hy]; exact h, ?_⟩
      have hp := Proof.box_boxx (Γ := Γ) (x := x) ⟨X, hle.ref hX⟩ (WFF.mono hle.boxIn ψ)
      refine ⟨Proof.conv ?_ hp⟩
      simp only [kBox, WFF.boxx, WFF.neg, WFF.mono, WFF.mono_mono]

/-- ⭐**Necessity transfer along an edge**, of either kind. -/
theorem gltr (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ)
    (ψ : WFF σ ((ctxOf (glat s i)).kView none) 0)
    (hψ : .box ψ ∈ ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M) :
    WFF.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
      (ok_eS_kView (gentOk_box hM₀ h i)) (coh_eS_kView (gentOk_box hM₀ h i))
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ ((gnet hF M₀ (grnd s t i)).st t.1).M := by
  obtain ⟨c, hc⟩ := id h
  have hle := (glstg_spec hM₀ h i).1
  have hψ' := (ggrow_stage hM₀ s i hle).sub _ hψ
  obtain ⟨hsuf, hag, hfwd⟩ := gfwd_at hM₀ hc i
  obtain ⟨hsuf', hk, hf, htr⟩ := hfwd
  have hsm := (good_gnet hF hM₀ (grnd s t i)).mcs s.1
    (live_gbirth hF hM₀ s.2 (hle.trans' (Nat.le_add_right _ i)))
  have hk' := kBox_of_box hsm (ctxOf_le_of_suffix hsuf') (lkd t) hk
    (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ) (by
      convert hψ' using 1
      simp only [WFF.mono, WFF.mono_mono])
  have h₁ := htr _ hk'
  rw [WFF.mono_mono, WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots] at h₁
  rwa [WFF.subst_congr _ _ _ (ok_eS_kView (gentOk_box hM₀ h i)) _
    (coh_eS_kView (gentOk_box hM₀ h i)) _ _
    (sim_eS_congr fun v T _ hv => (hag v T ((Ctx.le_boxIn_kView _ _) v T hv)).symm) ψ] at h₁

/-- ⭐**`□_x` transfer along an edge made for `◇_x`**, at a stage declaring `x`. -/
theorem gltrX (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) {x : VarSymb}
    (hkd : lkd t = some x) (i : ℕ) {X : VarType}
    (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0)
    (hψ : WFF.boxx x ⟨X, hx⟩ ψ ∈ ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M) :
    WFF.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
      (ok_eS_kView (hkd ▸ gentOk hM₀ h i)) (coh_eS_kView (hkd ▸ gentOk hM₀ h i))
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ ((gnet hF M₀ (grnd s t i)).st t.1).M := by
  obtain ⟨c, hc⟩ := id h
  have hle := (glstg_spec hM₀ h i).1
  have hψ' := (ggrow_stage hM₀ s i hle).sub _ hψ
  obtain ⟨hsuf, hag, hfwd⟩ := gfwd_at hM₀ hc i
  rw [hkd] at hag hfwd
  obtain ⟨hsuf', hk, hf, htr⟩ := hfwd
  have hk' : WFF.mono (ctxOf_le_of_suffix hsuf') (kBox (some x) hk
      (WFF.mono ((ctxOf_le_of_suffix hsuf).kView _) ψ)) ∈
      ((gnet hF M₀ (grnd s t i)).st s.1).M := by
    convert hψ' using 1
    simp only [kBox, WFF.boxx, WFF.neg, WFF.mono, WFF.mono_mono]
  have h₁ := htr _ hk'
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots] at h₁
  rwa [WFF.subst_congr _ _ _ (ok_eS_kView (hkd ▸ gentOk hM₀ h i)) _
    (coh_eS_kView (hkd ▸ gentOk hM₀ h i)) _ _
    (sim_eS_congr fun v T _ hv => (hag v T hv).symm) ψ] at h₁

/-! ## Existence -/

/-- A child's entries are its creation map on a stage of its parent's view. -/
theorem glimit_child_ag (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {i m : ℕ} {L : List VarType}
    (hsuf : glat s i <:+ L) {k : Option VarSymb} {t : GW hF M₀}
    (hlive : (gnet hF M₀ (m + 1)).Live t.1)
    (hkind : (gnet hF M₀ (m + 1)).kind t.1 = k) (hfcl : (gnet hF M₀ (m + 1)).fcl t.1 = L)
    (hfmap : (gnet hF M₀ (m + 1)).fmap t.1 = ofRen (gchildMap L k)) :
    ∀ v T, (ctxOf (glat s i)).kView k v = some T → ofRen (gchildMap L k) v = fmapL hF M₀ t.1 v :=
  fun v T hv => by
    rw [fmapL_eq hM₀ hlive (T := T) (by
      rw [hfcl, hkind]
      exact ((ctxOf_le_of_suffix hsuf).kView _) v T hv), hfmap]

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A child's seed formula, grown, is the limit's translation. -/
theorem glimit_child_eq {Γ : Ctx} {Δ Δ' : Ctx} [Δ.NoSlots] [Δ'.NoSlots]
    (h : Δ.Le Δ') {g g' : VarSymb → LEnt σ}
    {l : List VarType} {k : Option VarSymb} (hle : ((ctxOf l).kView k).Le Γ)
    (hg : EntOk Γ Δ g) (hg' : EntOk ((ctxOf l).kView k) Δ' g')
    (hag : ∀ v T, ((ctxOf l).kView k) v = some T → g v = g' v)
    [Γ.NoSlots] (ψ : WFF σ ((ctxOf l).kView k) 0)
    (hokΓ : Subst.Ok Γ (eS σ Δ g)) (hcohΓ : Subst.Coh (eIdx g) Γ (eS σ Δ g)) :
    WFF.mono h (WFF.subst (eIdx g) (eS σ Δ g) hokΓ hcohΓ Ctx.NoSlots.slots Ctx.NoSlots.slots
      (WFF.mono hle ψ)) =
    WFF.subst (eIdx g') (eS σ Δ' g') (ok_eS_kView hg') (coh_eS_kView hg') Ctx.NoSlots.slots
      Ctx.NoSlots.slots ψ := by
  rw [WFF.mono_subst, WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ ?_ ψ
  refine Subst.sim_of fun v T hl hv => ?_
  obtain ⟨u, s, rfl, -, -⟩ := kView_item hv
  change SubE.Sim T (SubE.mono h (eS σ Δ g (.step u s))) (eS σ Δ' g' (.step u s))
  rw [eS_item _ hl, eS_item _ hl, entOf_mono h (hg _ T hl (hle _ T hv)), hag _ T hv]
  exact .refl _

/-- ⭐A failing necessity has a child where its translation fails. -/
theorem glex (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    (ψ : WFF σ ((ctxOf (glat s i)).kView none) 0)
    (hψ : .box ψ ∉ ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M) :
    ∃ (t : GW hF M₀) (h : GCh hF M₀ s t), lkd t = none ∧
      (WFF.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (gentOk_box hM₀ h i)) (coh_eS_kView (gentOk_box hM₀ h i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ).neg ∈ ((gnet hF M₀ (grnd s t i)).st t.1).M := by
  obtain ⟨m, _, hsuf, M', hnot, hlive, hst, hkind, hfcl, hfmap, hmem⟩ :=
    child_box hF hM₀ (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i)) hψ
  let t : GW hF M₀ := ⟨(gnet hF M₀ m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (gnet hF M₀ m).nch s.1 :: s.1 := rfl
  have h : GCh hF M₀ s t := ⟨_, hc⟩
  have hbt' : gbirth hF M₀ t.2 ≤ m + 1 := gbirth_le hF t.2 hlive
  have hlkd : lkd t = none := (kind_at hM₀ t hbt').symm.trans hkind
  refine ⟨t, h, hlkd, ?_⟩
  have hbt : m < gbirth hF M₀ t.2 := le_gbirth hF hM₀ t.2 hnot
  have hg : Grows ((gnet hF M₀ (m + 1)).st t.1) ((gnet hF M₀ (grnd s t i)).st t.1) :=
    (ext_gnet hF hM₀ ((Nat.succ_le_of_lt hbt).trans (Nat.le_add_right _ _))).grows t.1 hlive
  rw [hst] at hg
  have hm := hg.sub _ hmem
  have hag := glimit_child_ag hM₀ hsuf (t := t) hlive hkind hfcl hfmap
  have hE := entOk_ofRen (σ := σ)
    (itemOk_gchild hF ((gnet hF M₀ m).st s.1).l (kContent_none _ .VTypeOne))
  have e := glimit_child_eq (l := glat s i) (k := none) (ctxOf_le_of_suffix hg.suf)
    ((ctxOf_le_of_suffix hsuf).kView none) hE (gentOk_box hM₀ h i) hag ψ.neg
    (ok_eS_kView hE) (coh_eS_kView hE)
  convert hm using 1
  exact e.symm

/-- ⭐A possibility has a child made for it where its translation holds. -/
theorem glexX (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) (x : VarSymb) (X : VarType)
    (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (glat s i)).kView (some x)) 0)
    (hψ : WFF.dia x ⟨X, hx⟩ ψ ∈ ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M) :
    ∃ (t : GW hF M₀) (h : GCh hF M₀ s t) (hkd : lkd t = some x),
      (∃ y, fmapL hF M₀ t.1 (.step x .keep) = .inl y) ∧
      (∃ b, fmapL hF M₀ t.1 (.step x .dia) = .inl b) ∧
      WFF.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (hkd ▸ gentOk hM₀ h i)) (coh_eS_kView (hkd ▸ gentOk hM₀ h i))
        Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ ((gnet hF M₀ (grnd s t i)).st t.1).M := by
  obtain ⟨m, _, hsuf, X', hk, M', hnot, hlive, hst, hkind, hfcl, hfmap, hmem⟩ :=
    child_dia hF hM₀ (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i)) hψ
  let t : GW hF M₀ := ⟨(gnet hF M₀ m).nch s.1 :: s.1, m + 1, hlive⟩
  have hc : t.1 = (gnet hF M₀ m).nch s.1 :: s.1 := rfl
  have h : GCh hF M₀ s t := ⟨_, hc⟩
  have hbt' : gbirth hF M₀ t.2 ≤ m + 1 := gbirth_le hF t.2 hlive
  have hlkd : lkd t = some x := (kind_at hM₀ t hbt').symm.trans hkind
  have hag₀ := glimit_child_ag hM₀ hsuf (t := t) hlive hkind hfcl hfmap
  have hxk : (ctxOf (glat s i)).kView (some x) (.step x .keep) = some (.VTypeDia X) :=
    (Ctx.le_boxIn_diaIn _ x) _ _ ((Ctx.ref_nonproj _ rfl).symm.trans
      (Ctx.ref_keep_of' hF hx VarType.keepable_dia))
  have hxd : (ctxOf (glat s i)).kView (some x) (.step x .dia) = some X :=
    (Ctx.ref_nonproj _ rfl).symm.trans (Ctx.ref_diaIn_of hx)
  refine ⟨t, h, hlkd, ⟨_, (hag₀ _ _ hxk).symm⟩, ⟨_, (hag₀ _ _ hxd).symm⟩, ?_⟩
  have hbt : m < gbirth hF M₀ t.2 := le_gbirth hF hM₀ t.2 hnot
  have hg : Grows ((gnet hF M₀ (m + 1)).st t.1) ((gnet hF M₀ (grnd s t i)).st t.1) :=
    (ext_gnet hF hM₀ ((Nat.succ_le_of_lt hbt).trans (Nat.le_add_right _ _))).grows t.1 hlive
  rw [hst] at hg
  have hm := hg.sub _ hmem
  have hag := glimit_child_ag hM₀ hsuf (t := t) hlive hkind hfcl hfmap
  have hE := entOk_ofRen (σ := σ) (itemOk_gchild hF ((gnet hF M₀ m).st s.1).l hk)
  have e := glimit_child_eq (l := glat s i) (k := some x) (ctxOf_le_of_suffix hg.suf)
    ((ctxOf_le_of_suffix hsuf).kView _) hE (hlkd ▸ gentOk hM₀ h i) hag ψ
    (ok_eS_kView hE) (coh_eS_kView hE)
  convert hm using 1
  exact e.symm

/-! ## Lifts in the limit -/

/-- ⭐**Every admissible liftable term of a child is the image of a lifted root's kept item**
    (a necessary term or a view tuple, `LiftAdm`): some stage of the parent has a root `r` of the
    term's type whose kept item the edge sends to the term. -/
theorem gllift (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (j : ℕ)
    {T : VarType} {a : Ann T} (u : Term σ (ctxOf (glat t j)) T a) (hl : T.liftable = true)
    (hv : LiftAdm hF ⟨glat t j, T, a, u⟩) (hV : ModalSys.Five = false) :
    ∃ (i r : ℕ), r < (glat s i).length ∧ rootTy (glat s i) r = T ∧
      ∃ (L : List VarType) (hL : glat t j <:+ L),
        fmapL hF M₀ t.1 (.step (.root (.free r)) .keep) =
          .inr ⟨L, T, a, Term.mono (ctxOf_le_of_suffix hL) u⟩ ∧
        L <:+ glat t (glstg s t i) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨k, hk⟩ := t
  change k = c :: s.1 at hc
  subst hc
  have hlive := live_gbirth hF hM₀ hk (Nat.le_add_right _ j)
  obtain ⟨m, hnm, -, r, hr, hroot, L, hL, hfm, hLsuf⟩ := lift_total hF hM₀ hlive u hl hv hV
  have hbs : gbirth hF M₀ s.2 ≤ m + 1 :=
    gbirth_le hF s.2 (gnet_live_mono hF hM₀ (by omega) hlive.1)
  have hmi : gbirth hF M₀ s.2 + (m + 1 - gbirth hF M₀ s.2) = m + 1 := by omega
  have hlive' : (gnet hF M₀ (m + 1)).Live (c :: s.1) := gnet_live_mono hF hM₀ (by omega) hlive
  obtain ⟨hsufp, -⟩ := (good_gnet hF hM₀ (m + 1)).fwd c s.1 hlive'
  refine ⟨m + 1 - gbirth hF M₀ s.2, r, ?_, ?_, L, hL, ?_, ?_⟩
  · change r < ((gnet hF M₀ (gbirth hF M₀ s.2 + (m + 1 - gbirth hF M₀ s.2))).st s.1).l.length
    rw [hmi]
    exact lt_of_lt_of_le hr hsufp.length_le
  · change rootTy ((gnet hF M₀ (gbirth hF M₀ s.2 + (m + 1 - gbirth hF M₀ s.2))).st s.1).l r = T
    rw [hmi]
    exact hroot
  · rw [fmapL_eq hM₀ hlive' (T := T), hfm]
    have hR : (ctxOf ((gnet hF M₀ (m + 1)).fcl (c :: s.1))).ref (.root (.free r)) = some T := by
      rw [Ctx.ref_nonproj _ rfl, ctxOf_root_lt hr, rootTy_suffix hsufp hr, hroot]
    exact (Ctx.le_boxIn_kView _ _) _ _
      (Ctx.boxIn_keep_of' hF hR (VarType.keepable_of_liftable hl))
  · have hP := (glstg_spec hM₀ (t := ⟨c :: s.1, hk⟩) ⟨c, rfl⟩ (m + 1 - gbirth hF M₀ s.2)).1
    exact hLsuf.trans (gnet_lang_suffix hF hM₀ (by omega) hlive')

/-- ⭐**Names by origin in the limit** (N1, `docs/v12-modal-extensions.md` §3 5): under 5, with T
    off, every reachable address of a liftable type of a child is named by its edge — the entry of
    a kept item of its parent, at some stage, is the address or its η-term. -/
theorem glorigin (hV : ModalSys.Five = true) (hT : ModalSys.T = false) (hM₀ : Theory.IsMCS M₀)
    {s t : GW hF M₀} (h : GCh hF M₀ s t) (j : ℕ) {z : VarSymb} {T : VarType}
    (hz : (ctxOf (glat t j)).ref z = some T) (hl : T.liftable = true) :
    ∃ (i : ℕ) (v : VarSymb) (U : VarType), (ctxOf (glat s i)).ref v = some U ∧
      U.keepable = true ∧
      (fmapL hF M₀ t.1 (.step v .keep) = .inl z ∨
        ∃ (L : List VarType) (T' : VarType) (hz' : (ctxOf L).ref z = some T'),
          fmapL hF M₀ t.1 (.step v .keep) = .inr ⟨L, T', _, Term.eta z T' hz'⟩) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨k, hk⟩ := t
  change k = c :: s.1 at hc
  subst hc
  have hlive := live_gbirth hF hM₀ hk (Nat.le_add_right _ j)
  obtain ⟨m, hnm, v, U, hv, he⟩ := origin_total hF hM₀ hV hT hlive hz hl
  have hlive' : (gnet hF M₀ (m + 1)).Live (c :: s.1) := gnet_live_mono hF hM₀ (by omega) hlive
  have hbs : gbirth hF M₀ s.2 ≤ m + 1 :=
    gbirth_le hF s.2 (gnet_live_mono hF hM₀ (by omega) hlive.1)
  have hmi : gbirth hF M₀ s.2 + (m + 1 - gbirth hF M₀ s.2) = m + 1 := by omega
  obtain ⟨hsufp, -⟩ := (good_gnet hF hM₀ (m + 1)).fwd c s.1 hlive'
  have hb : (ctxOf ((gnet hF M₀ (m + 1)).fcl (c :: s.1))).boxIn (.step v .keep) = some U := by
    cases hkd : (gnet hF M₀ (m + 1)).kind (c :: s.1) with
    | none => rw [hkd] at hv; exact hv
    | some x => rw [hkd] at hv; exact hv
  obtain ⟨-, hvU, hkp⟩ := Ctx.boxIn_keep hb
  refine ⟨m + 1 - gbirth hF M₀ s.2, v, U, ?_, hkp, ?_⟩
  · change (ctxOf ((gnet hF M₀ (gbirth hF M₀ s.2 + (m + 1 - gbirth hF M₀ s.2))).st s.1).l).ref v =
      some U
    rw [hmi]
    exact (ctxOf_le_of_suffix hsufp).ref hvU
  · rw [fmapL_eq hM₀ hlive' hv]
    exact he

end GArrow

end V12M
