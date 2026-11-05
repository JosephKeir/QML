import QML.QML_v12m_GLoopLimit

/-!
# QML v12m — the world asked about, in the limit

With a hub (`GNetSt.HubOn M₀`; docs, "K45 and KD45 without both lifts: the hub"), the world asked
about is the network's `src`.  Its rounds are its stages (`gsrcWorld`, a `BArrow.BWorld`), with
Henkin witnesses from the root's Henkin operation (`henkSrc_ex`, `henkSrc_negAll`).  Every one of
its variables is eventually committed along the edge into the hub (`hub_total`), so a stage of it
has a stage of the hub where it is (`hstg`, `hub_at`), and the limit's entries type its view and
transfer necessity (`hubOk`, `gltr_hub`).  As `QML_v12m_GLoopLimit` for the root's self-edge.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- The root's Henkin step leaves the world asked about, and the hub flag, alone. -/
theorem GNetSt.henk_src (N : GNetSt σ) (s : Node) (o : Obl σ) :
    (N.henk s o).src = N.src ∧ (N.henk s o).hb = N.hb := by
  obtain ⟨l, φ⟩ := o
  simp only [GNetSt.henk]
  split <;> (try split) <;> (try split) <;> exact ⟨rfl, rfl⟩

/-- The hub flag is fixed along the chain. -/
theorem hb_gnet (hM₀ : Theory.IsMCS M₀) (n : ℕ) : (gnet hF M₀ n).hb = GNetSt.HubOn M₀ :=
  (ext_gnet hF hM₀ (Nat.zero_le n)).hb

/-- The world asked about grows along the chain. -/
theorem src_grows (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {n m : ℕ} (hnm : n ≤ m) :
    Grows (gnet hF M₀ n).src (gnet hF M₀ m).src :=
  (ext_gnet hF hM₀ hnm).src (by rw [hb_gnet hM₀]; exact hh)

theorem src_mcs (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) (n : ℕ) :
    Theory.IsMCS (gnet hF M₀ n).src.M :=
  (good_gnet hF hM₀ n).srcMcs (by rw [hb_gnet hM₀]; exact hh)

/-- The world asked about starts as `M₀`. -/
theorem src_zero : (gnet hF M₀ 0).src = ⟨l₀, M₀⟩ := rfl

/-- A round of the root's Henkin operation is one of the world asked about. -/
theorem src_henk (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {m : ℕ} {o : Obl σ}
    (hs : gsched m = .inl ([], o)) :
    (gnet hF M₀ (m + 1)).src = GNetSt.henkT (gnet hF M₀ m).src o := by
  have h₁ := GNetSt.henk_src (gnet hF M₀ m) [] o
  rw [gnet_succ_of hF hs]
  simp only [GNetSt.applyOp, if_pos (show (gnet hF M₀ m).Live [] from trivial),
    GNetSt.henkSrc, GNetSt.withSrc]
  rw [if_pos ⟨rfl, by rw [h₁.2, hb_gnet hM₀]; exact hh⟩, h₁.1]

/-! ## Henkin witnesses -/

/-- ⭐Every existential of the world asked about eventually has a witness. -/
theorem henkSrc_ex (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {n : ℕ} {A : VarType}
    {ψ : WFF σ ((ctxOf (gnet hF M₀ n).src.l).insert (.bnd 0) A) 1}
    (hmem : WFF.ex A ψ ∈ (gnet hF M₀ n).src.M) :
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf (gnet hF M₀ n).src.l).Le (ctxOf (gnet hF M₀ m).src.l))
      (c : ℕ) (hc : (ctxOf (gnet hF M₀ m).src.l).ref (.root (.free c)) = some A),
      WFF.instantiate Ctx.NoSlots.slots (Term.eta (.root (.free c)) A hc)
        (WFF.mono (hle.insert _ A) ψ) ∈ (gnet hF M₀ m).src.M := by
  obtain ⟨m, hnm, hs'⟩ := gsched_after (σ := σ) (.inl ([], ⟨(gnet hF M₀ n).src.l, .ex A ψ⟩)) n
  have hg := src_grows (hF := hF) hM₀ hh hnm
  have hsuf := hg.suf
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (WFF.ex A ψ) ∈ (gnet hF M₀ m).src.M :=
    hg.sub _ hmem
  have hM := src_mcs (hF := hF) hM₀ hh m
  obtain ⟨hS, -⟩ := complete_spec (henkin_consistent hM.1 (Theory.Derives.of_mem hin)
    (ctxOf_fresh (l := (gnet hF M₀ m).src.l) le_rfl))
  have hst : (gnet hF M₀ (m + 1)).src = ⟨A :: (gnet hF M₀ m).src.l, complete
      (WFF.mono (ctxOf_le_append [A] (gnet hF M₀ m).src.l) '' (gnet hF M₀ m).src.M ∪
        {WFF.openFree (gnet hF M₀ m).src.l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
          (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ)})⟩ := by
    rw [src_henk hM₀ hh hs']
    simp only [GNetSt.henkT, dif_pos hsuf, if_pos hin]
  refine ⟨m + 1, by omega, ?_⟩
  rw [hst]
  refine ⟨(ctxOf_le_of_suffix hsuf).trans (ctxOf_le_append [A] _), _,
    Ctx.ref_insert_root _ _ A, ?_⟩
  refine hS (Or.inr ?_)
  rw [Set.mem_singleton_iff, ← WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots, WFF.mono_mono]

/-- ⭐Every failing universal of the world asked about eventually has a counter-instance. -/
theorem henkSrc_negAll (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {n : ℕ} {A : VarType}
    {ψ : WFF σ ((ctxOf (gnet hF M₀ n).src.l).insert (.bnd 0) A) 1}
    (hmem : (WFF.all A ψ).neg ∈ (gnet hF M₀ n).src.M) :
    ∃ m, n ≤ m ∧ ∃ (hle : (ctxOf (gnet hF M₀ n).src.l).Le (ctxOf (gnet hF M₀ m).src.l))
      (a : Ann A) (t : Term σ (ctxOf (gnet hF M₀ m).src.l) A a),
      (WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (hle.insert _ A) ψ)).neg ∈
        (gnet hF M₀ m).src.M := by
  obtain ⟨m, hnm, hs'⟩ := gsched_after (σ := σ)
    (.inl ([], ⟨(gnet hF M₀ n).src.l, .imp (.all A ψ) .bot⟩)) n
  have hg := src_grows (hF := hF) hM₀ hh hnm
  have hsuf := hg.suf
  have hin : WFF.mono (ctxOf_le_of_suffix hsuf) (.imp (.all A ψ) .bot) ∈
      (gnet hF M₀ m).src.M :=
    hg.sub _ hmem
  have hM := src_mcs (hF := hF) hM₀ hh m
  have hex : Theory.Derives (gnet hF M₀ m).src.M
      (.ex A (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ).neg) :=
    ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hin, ⟨Proof.exNeg_of_negAll _⟩⟩
  obtain ⟨hS, -⟩ := complete_spec (henkin_consistent hM.1 hex
    (ctxOf_fresh (l := (gnet hF M₀ m).src.l) le_rfl))
  have hst : (gnet hF M₀ (m + 1)).src = ⟨A :: (gnet hF M₀ m).src.l, complete
      (WFF.mono (ctxOf_le_append [A] (gnet hF M₀ m).src.l) '' (gnet hF M₀ m).src.M ∪
        {WFF.openFree (gnet hF M₀ m).src.l.length (ctxOf_fresh le_rfl) Ctx.NoSlots.slots
          (WFF.mono ((ctxOf_le_of_suffix hsuf).insert _ A) ψ).neg})⟩ := by
    rw [src_henk hM₀ hh hs']
    simp only [GNetSt.henkT, dif_pos hsuf, if_pos hin]
  refine ⟨m + 1, by omega, ?_⟩
  rw [hst]
  refine ⟨(ctxOf_le_of_suffix hsuf).trans (ctxOf_le_append [A] _), _,
    Term.eta (.root (.free (gnet hF M₀ m).src.l.length)) A (Ctx.ref_insert_root _ _ A), ?_⟩
  refine hS (Or.inr ?_)
  rw [Set.mem_singleton_iff, ← WFF.instantiate_eta_openFree _ (ctxOf_fresh le_rfl)
    Ctx.NoSlots.slots Ctx.NoSlots.slots]
  change _ = (WFF.instantiate _ _ (WFF.mono _ (WFF.mono _ ψ))).neg
  rw [WFF.mono_mono]

variable (hF M₀) in
/-- ⭐The world asked about as a world: its stages are the rounds. -/
noncomputable def gsrcWorld (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) : BWorld σ where
  l i := (gnet hF M₀ i).src.l
  suf h := (src_grows hM₀ hh h).suf
  M i := (gnet hF M₀ i).src.M
  mcs i := src_mcs hM₀ hh i
  sub h φ hφ := (src_grows hM₀ hh h).sub φ hφ
  exW hmem := by
    obtain ⟨m, hnm, _, c, hc, hm⟩ := henkSrc_ex hM₀ hh hmem
    exact ⟨m, hnm, c, hc, hm⟩
  allW hmem := by
    obtain ⟨m, hnm, _, a, t, hm⟩ := henkSrc_negAll hM₀ hh hmem
    exact ⟨m, hnm, a, t, hm⟩

/-! ## The edge into the hub -/

/-- ⭐Every variable of the world asked about is eventually committed into the hub. -/
theorem hub_total (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {n r : ℕ}
    (hr : r < (gnet hF M₀ n).src.l.length) :
    ∃ m, n ≤ m ∧ r < ((gnet hF M₀ m).fcl []).length := by
  have key : ∀ j, ∃ m, n ≤ m ∧ min j (r + 1) ≤ ((gnet hF M₀ m).fcl []).length := by
    intro j
    induction j with
    | zero => exact ⟨n, le_rfl, by simp⟩
    | succ j ih =>
        obtain ⟨m, hnm, hm⟩ := ih
        by_cases hdone : r + 1 ≤ ((gnet hF M₀ m).fcl []).length
        · exact ⟨m, hnm, (min_le_right _ _).trans hdone⟩
        obtain ⟨m', hm'm, hs⟩ := gsched_after (σ := σ) (.inr (.inr (.inl []))) m
        have hmono : ((gnet hF M₀ m).fcl []).length ≤ ((gnet hF M₀ m').fcl []).length :=
          ((ext_gnet hF hM₀ hm'm).fcl [] trivial).length_le
        by_cases hdone' : r + 1 ≤ ((gnet hF M₀ m').fcl []).length
        · exact ⟨m', hnm.trans hm'm, (min_le_right _ _).trans hdone'⟩
        have hlp : (gnet hF M₀ n).src.l.length ≤ (gnet hF M₀ m').src.l.length :=
          (src_grows hM₀ hh (hnm.trans hm'm)).suf.length_le
        have hlt : ((gnet hF M₀ m').fcl []).length < (gnet hF M₀ m').src.l.length := by
          omega
        have hbm : (gnet hF M₀ m').hb := by
          rw [hb_gnet hM₀]
          exact hh
        refine ⟨m' + 1, by omega, ?_⟩
        rw [gnet_succ_of hF hs]
        simp only [GNetSt.applyOp]
        rw [if_pos (show (gnet hF M₀ m').Live [] from trivial), GNetSt.realF_fcl_root,
          if_neg (fun h => (good_gnet hF hM₀ m').excl hbm h.1), if_pos ⟨hbm, hlt⟩,
          List.length_cons]
        omega
  obtain ⟨m, hnm, hm⟩ := key (r + 1)
  exact ⟨m, hnm, by simp at hm; omega⟩

variable (hF M₀) in
/-- A stage `j` of the hub where stage `i` of the world asked about is committed. -/
def HStgP (i j : ℕ) : Prop :=
  i ≤ gbirth hF M₀ (groot hF M₀).2 + j ∧
    (gnet hF M₀ i).src.l.length ≤ ((gnet hF M₀ (gbirth hF M₀ (groot hF M₀).2 + j)).fcl []).length

theorem hstg_exists (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) (i : ℕ) :
    ∃ j, HStgP hF M₀ i j := by
  rcases hlen : (gnet hF M₀ i).src.l.length with _ | L
  · exact ⟨i, by omega, by rw [hlen]; exact Nat.zero_le _⟩
  · obtain ⟨m, hnm, hm⟩ := hub_total hM₀ hh (n := i) (r := L) (by omega)
    refine ⟨m, by omega, ?_⟩
    rw [hlen]
    exact hm.trans_le (((ext_gnet hF hM₀ (Nat.le_add_left m _)).fcl [] trivial).length_le)

variable (hF M₀) in
open Classical in
/-- ⭐The stage of the hub where stage `i` of the world asked about is committed. -/
noncomputable def hstg (i : ℕ) : ℕ :=
  if h : ∃ j, HStgP hF M₀ i j then Nat.find h else 0

variable (hF M₀) in
/-- The round at which stage `i` of the world asked about is read along the edge. -/
noncomputable abbrev hrnd (i : ℕ) : ℕ := gbirth hF M₀ (groot hF M₀).2 + hstg hF M₀ i

open Classical in
theorem hstg_spec (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) (i : ℕ) :
    HStgP hF M₀ i (hstg hF M₀ i) := by
  have he := hstg_exists (hF := hF) hM₀ hh i
  rw [hstg, dif_pos he]
  exact Nat.find_spec he

open Classical in
theorem hstg_monotone (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {i i' : ℕ}
    (hii : i ≤ i') : hstg hF M₀ i ≤ hstg hF M₀ i' := by
  have hP := hstg_spec (hF := hF) hM₀ hh i'
  have hP' : HStgP hF M₀ i (hstg hF M₀ i') :=
    ⟨by have := hP.1; omega, le_trans (src_grows hM₀ hh hii).suf.length_le hP.2⟩
  rw [hstg, dif_pos ⟨_, hP'⟩]
  exact Nat.find_min' _ hP'

/-- ⭐Along the edge into the hub, stage `i` of the world asked about is committed at its stage,
    with the limit's entries. -/
theorem hub_at (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) (i : ℕ) :
    (gnet hF M₀ i).src.l <:+ (gnet hF M₀ (hrnd hF M₀ i)).fcl [] ∧
      (∀ v T, (ctxOf (gnet hF M₀ i).src.l).kView none v = some T →
        (gnet hF M₀ (hrnd hF M₀ i)).fmap [] v = fmapL hF M₀ [] v) ∧
      FwdData (gnet hF M₀ (hrnd hF M₀ i)).src ((gnet hF M₀ (hrnd hF M₀ i)).st []) none
        ((gnet hF M₀ (hrnd hF M₀ i)).fcl []) ((gnet hF M₀ (hrnd hF M₀ i)).fmap []) := by
  obtain ⟨hle, hlen⟩ := hstg_spec (hF := hF) hM₀ hh i
  have hG := good_gnet hF hM₀ (hrnd hF M₀ i)
  have hfd := hG.hub (by rw [hb_gnet hM₀]; exact hh)
  have hls : (gnet hF M₀ i).src.l <:+ (gnet hF M₀ (hrnd hF M₀ i)).src.l :=
    (src_grows hM₀ hh hle).suf
  obtain ⟨hsuf₀, -⟩ := id hfd
  have hsuf' := List.suffix_of_suffix_length_le hls hsuf₀ hlen
  refine ⟨hsuf', fun v T hv => ?_, hfd⟩
  refine (fmapL_eq hM₀ (k := []) trivial (T := T) ?_).symm
  rw [hG.kindRoot]
  exact ((ctxOf_le_of_suffix hsuf').kView _) v T hv

/-- ⭐The limit's entries type a stage's `□` view of the world asked about, at the hub's stage. -/
theorem hubOk (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) (i : ℕ) :
    EntOk ((ctxOf (gnet hF M₀ i).src.l).kView none) (ctxOf (glat (groot hF M₀) (hstg hF M₀ i)))
      (fmapL hF M₀ []) := by
  obtain ⟨hsuf, hag, ⟨_, _, hf, _⟩⟩ := hub_at (hF := hF) hM₀ hh i
  exact (hf.restrict ((ctxOf_le_of_suffix hsuf).kView _)).congr hag

/-- ⭐**Necessity transfer into the hub.** -/
theorem gltr_hub (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) (i : ℕ)
    (ψ : WFF σ ((ctxOf (gnet hF M₀ i).src.l).kView none) 0)
    (hψ : .box ψ ∈ (gnet hF M₀ i).src.M) :
    WFF.subst (eIdx (fmapL hF M₀ [])) (eS σ _ (fmapL hF M₀ []))
      (ok_eS_kView (hubOk hM₀ hh i)) (coh_eS_kView (hubOk hM₀ hh i))
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ ((gnet hF M₀ (hrnd hF M₀ i)).st []).M := by
  have hle := (hstg_spec (hF := hF) hM₀ hh i).1
  have hψ' := (src_grows hM₀ hh hle).sub _ hψ
  obtain ⟨hsuf, hag, ⟨hsuf', hk, hf, htr⟩⟩ := hub_at (hF := hF) hM₀ hh i
  have h₁ := htr (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ) (by
    convert hψ' using 1
    simp only [kBox, WFF.mono, WFF.mono_mono])
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots] at h₁
  change WFF.subst _ (eS σ (ctxOf (glat (groot hF M₀) (hstg hF M₀ i))) _) _ _ _ _ ψ ∈ _ at h₁
  rwa [WFF.subst_congr _ _ _ (ok_eS_kView (hubOk hM₀ hh i)) _
    (coh_eS_kView (hubOk hM₀ hh i)) _ _
    (sim_eS_congr fun v T _ hv => (hag v T hv).symm) ψ] at h₁

/-- ⭐**A `□`-view term of the world asked about, translated into the hub.** -/
noncomputable def hubTm (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) (i : ℕ) {A : VarType}
    {a : Ann A} (b : Term σ ((ctxOf (gnet hF M₀ i).src.l).kView none) A a) :
    Σ c : Ann A, Term σ (ctxOf (glat (groot hF M₀) (hstg hF M₀ i))) A c :=
  ⟨_, Term.subst (eIdx (fmapL hF M₀ [])) (eS σ _ (fmapL hF M₀ []))
    (ok_eS_kView (hubOk hM₀ hh i)) (coh_eS_kView (hubOk hM₀ hh i)) b⟩

/-- Translating a later stage is weakening the translation. -/
theorem hubTm_mono (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {i i' : ℕ} (hii : i ≤ i')
    {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (gnet hF M₀ i).src.l).kView none) A a) :
    (⟨_, Term.mono (gle hM₀ (groot hF M₀) (hstg_monotone hM₀ hh hii)) (hubTm hM₀ hh i b).2⟩ :
      Σ c, Term σ (ctxOf (glat (groot hF M₀) (hstg hF M₀ i'))) A c) =
      hubTm hM₀ hh i'
        (Term.mono ((ctxOf_le_of_suffix (src_grows hM₀ hh hii).suf).kView none) b) := by
  change (⟨_, Term.mono _ (Term.subst _ _ _ _ b)⟩ : Σ c, Term σ _ _ c) =
    ⟨_, Term.subst _ _ _ _ (Term.mono _ b)⟩
  rw [Term.mono_subst, Term.subst_mono]
  exact Term.subst_congr _ _ _ _ _ _ (sim_eS_mono _ (hubOk hM₀ hh i)) b

/-! ## Lifts into the world asked about (docs, "the hub", step 6) -/

namespace GNetSt

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem realF_root_hub (hF : ModalSys.Four = true) (N : GNetSt σ) (hb : N.hb) (hnl : ¬ N.lp)
    (hlt : (N.fcl []).length < N.src.l.length) :
    (N.realF hF []).src = N.src ∧ ((N.realF hF []).fcl []).length = (N.fcl []).length + 1 ∧
      (N.realF hF []).hb = N.hb ∧ (N.realF hF []).lp = N.lp := by
  have e := GNetSt.realF_fcl_root hF N
  rw [if_neg (fun h => hnl h.1), if_pos ⟨hb, hlt⟩] at e
  refine ⟨?_, by rw [e, List.length_cons], ?_, ?_⟩ <;>
  · simp only [GNetSt.realF]
    split_ifs <;> rfl

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem iterate_realF_root (hF : ModalSys.Four = true) :
    ∀ (j : ℕ) (N : GNetSt σ), N.hb → ¬ N.lp → (N.fcl []).length + j ≤ N.src.l.length →
      ((fun N' => N'.realF hF [])^[j] N).src = N.src ∧
        (((fun N' => N'.realF hF [])^[j] N).fcl []).length = (N.fcl []).length + j
  | 0, _, _, _, _ => ⟨rfl, rfl⟩
  | j + 1, N, hb, hnl, h => by
      rw [Function.iterate_succ_apply]
      have hlt : (N.fcl []).length < N.src.l.length := by omega
      obtain ⟨h₁, h₂, h₃, h₄⟩ := realF_root_hub hF N hb hnl hlt
      obtain ⟨ih₁, ih₂⟩ := iterate_realF_root hF j (N.realF hF [])
        (by rw [h₃]; exact hb) (by rw [h₄]; exact hnl) (by rw [h₁, h₂]; omega)
      exact ⟨ih₁.trans h₁, by rw [ih₂, h₂]; omega⟩

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- ⭐After catching up, the world asked about is fully committed along the hub's edge. -/
theorem catchUp_full_hub (hF : ModalSys.Four = true) {N : GNetSt σ} (hN : N.Good) (hb : N.hb) :
    (N.catchUp hF []).fcl [] = (N.catchUp hF []).src.l := by
  obtain ⟨hsuf, -⟩ := hN.hub hb
  have hle := hsuf.length_le
  obtain ⟨h₁, h₂⟩ := iterate_realF_root hF (N.src.l.length - (N.fcl []).length) N hb
    (hN.excl hb) (by omega)
  obtain ⟨hN', -, he⟩ := hN.catchUp hF (k := []) trivial
  have hb' : (N.catchUp hF []).hb := by rw [he.hb]; exact hb
  obtain ⟨hsuf', -⟩ := hN'.hub hb'
  simp only [GNetSt.catchUp, if_pos hb] at hsuf' ⊢
  refine hsuf'.eq_of_length ?_
  rw [h₂, h₁]
  omega

end GNetSt

/-- ⭐**Every hub term of a type lifted by flag is eventually lifted to the world asked about**:
    the world asked about gets a root of the term's type, committed along the hub's edge with
    its kept item sent to the term. -/
theorem hub_lift_total (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {n : ℕ} {T : VarType}
    {a : Ann T} (t : Term σ (ctxOf ((gnet hF M₀ n).st []).l) T a) (hl : T.liftableR = true) :
    ∃ m, n ≤ m ∧ ∃ (r : ℕ) (L : List VarType) (hL : ((gnet hF M₀ n).st []).l <:+ L),
      (gnet hF M₀ (m + 1)).fcl [] = (gnet hF M₀ (m + 1)).src.l ∧
      r < (gnet hF M₀ (m + 1)).src.l.length ∧ rootTy (gnet hF M₀ (m + 1)).src.l r = T ∧
      (gnet hF M₀ (m + 1)).fmap [] (.step (.root (.free r)) .keep) =
        .inr ⟨L, T, a, Term.mono (ctxOf_le_of_suffix hL) t⟩ := by
  obtain ⟨m, hnm, hs⟩ := gsched_after (σ := σ) (.inr (.inr (.inr ([], ⟨_, T, a, t⟩)))) n
  have hN := good_gnet hF hM₀ m
  have hb : (gnet hF M₀ m).hb := by rw [hb_gnet hM₀]; exact hh
  obtain ⟨-, -, he₁⟩ := hN.catchUp hF (k := []) trivial
  have hb' : ((gnet hF M₀ m).catchUp hF []).hb := by rw [he₁.hb]; exact hb
  have hcl := GNetSt.catchUp_full_hub hF hN hb
  have h₁ : ((gnet hF M₀ n).st []).l <:+ (((gnet hF M₀ m).catchUp hF []).st []).l :=
    ((ext_gnet hF hM₀ hnm).grows [] trivial).suf.trans (he₁.grows [] trivial).suf
  have hst : gnet hF M₀ (m + 1) = ((gnet hF M₀ m).catchUp hF []).lift hF [] ⟨_, T, a, t⟩ := by
    rw [gnet_succ_of hF hs]
    simp only [GNetSt.applyOp, if_pos (show (gnet hF M₀ m).Live [] from trivial)]
  refine ⟨m, hnm, ?_⟩
  rw [hst]
  generalize (gnet hF M₀ m).catchUp hF [] = N at hb' hcl h₁
  simp only [GNetSt.lift, if_pos (show N.hb ∧ N.fcl [] = N.src.l from ⟨hb', hcl⟩), dif_pos h₁,
    dif_pos hl]
  refine ⟨N.src.l.length, (N.st []).l, h₁, rfl, ?_, rootTy_new T _, ?_⟩
  · change N.src.l.length < (T :: N.src.l).length
    simp
  · simp only [GNetSt.setFwd, Function.update_self]
    exact gliftG_keep _ _ _ _ _

/-- ⭐**In the limit**: a root of the world asked about at a later stage, of the term's type, whose
    kept item the hub's edge sends to the term. -/
theorem hub_lift_limit (hM₀ : Theory.IsMCS M₀) (hh : GNetSt.HubOn M₀) {n : ℕ} {T : VarType}
    {a : Ann T} (t : Term σ (ctxOf ((gnet hF M₀ n).st []).l) T a) (hl : T.liftableR = true) :
    ∃ j, n < j ∧ ∃ (r : ℕ) (_ : (ctxOf (gnet hF M₀ j).src.l).ref (.root (.free r)) = some T)
      (L : List VarType) (hL : ((gnet hF M₀ n).st []).l <:+ L),
      fmapL hF M₀ [] (.step (.root (.free r)) .keep) =
        .inr ⟨L, T, a, Term.mono (ctxOf_le_of_suffix hL) t⟩ := by
  obtain ⟨m, hnm, r, L, hL, hcl, hr, hty, he⟩ := hub_lift_total hM₀ hh t hl
  have hr' : (ctxOf (gnet hF M₀ (m + 1)).src.l).ref (.root (.free r)) = some T := by
    change ctxOf _ (.root (.free r)) = some T
    rw [ctxOf_root_lt hr, hty]
  refine ⟨m + 1, by omega, r, hr', L, hL, ?_⟩
  rw [fmapL_eq hM₀ (m := m + 1) (k := []) trivial (T := T)]
  · exact he
  · rw [(good_gnet hF hM₀ (m + 1)).kindRoot, hcl]
    exact Ctx.boxIn_keep_of' hF hr' (VarType.keepable_of_liftableR hl)

end GArrow

end V12M
