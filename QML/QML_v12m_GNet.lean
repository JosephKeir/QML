import QML.QML_v12m_GChild
import QML.QML_v12m_GLoopStep

/-!
# QML v12m — the growing tree: networks

The canonical model for strong 4 is the limit of **growing trees**, built round by round: B's
networks (`QML_v12m_BNet.lean`) without back arrows.  A node is a list of child indices, the
newest step first.  Each live node has the types of its variables and a maximal consistent theory
in them (`BArrow.NodeSt`).  Each child has one arrow, from its parent: an edge of kind `kind`
(`none` for `□`, `some x` for a child made for `◇_x`), whose committed part is the parent's
oldest variables `fcl` (a suffix of its list), sent by the item map `fmap`, with `□_k` transfer
(`FwdData`).  `Good` collects the invariants.  The root has no parent, so its slots hold its
self-edge, when it has one (`lp`, KB5 and KDB5): an edge of kind `none` from the root to itself,
fixing kept items (`LoopData`).

The operations, each preserving `Good`:
* `realF`: commit the parent's next variable along an edge (a fresh realisation, `gextF`; on the
  root's self-edge, `gloopF`, kept items fixed);
* `henk`: a Henkin witness, or a counter-instance for a failing universal, at one node;
* `mkChild`: a new child for a failing `□φ` or a true `◇_x φ` (`gchild_consistent`);
* `lift`: ⭐strong 4 — the parent of a fully committed edge gets a fresh root `m` with
  `m.keep ↦ n` for an address `n` of the child (`glift_consistent`), and `m`'s residual a fresh
  variable of the child (`gliftRealise_consistent`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

/-! ## Networks -/

/-- ⭐A growing tree under construction. -/
structure GNetSt (σ : Signature) where
  st : Node → NodeSt σ
  /-- The number of children created so far. -/
  nch : Node → ℕ
  /-- The edge's kind: `none` for a child made for a failing `□φ`, `some x` for one made for
      `◇_x φ`. -/
  kind : Node → Option VarSymb
  /-- The parent's variables with images in the child, and the edge's item map. -/
  fcl : Node → List VarType
  fmap : Node → VarSymb → LEnt σ
  /-- Whether the root has a self-edge. -/
  lp : Prop
  /-- ⭐The world asked about, when the root is a hub (docs, "K45 and KD45 without both lifts: the
      hub"): its theory grows apart from the tree, and its variables are committed into the root
      along the edge `src → []`, whose data are the root's slots. -/
  src : NodeSt σ
  /-- Whether the root is a hub. -/
  hb : Prop

/-- The flags the root's self-edge runs on: 4 and 5, T and strong B off. -/
def LoopFlags : Prop :=
  ModalSys.Four = true ∧ ModalSys.Five = true ∧ ModalSys.BStrong = false ∧ ModalSys.T = false

namespace GNetSt

variable (N : GNetSt σ)

/-- The nodes created so far: the root, and the children created of live nodes. -/
def Live : Node → Prop
  | [] => True
  | c :: p => Live p ∧ c < N.nch p

/-- The edge into the child `k` of `p`. -/
def FwdOk (k p : Node) : Prop := FwdData (N.st p) (N.st k) (N.kind k) (N.fcl k) (N.fmap k)

/-- ⭐The invariants of a growing tree. -/
structure Good : Prop where
  mcs : ∀ s, N.Live s → Theory.IsMCS (N.st s).M
  fwd : ∀ c p, N.Live (c :: p) → N.FwdOk (c :: p) p
  /-- The root's slots are of kind `none`. -/
  kindRoot : N.kind [] = none
  flags : N.lp → LoopFlags
  /-- The root's self-edge. -/
  loop : N.lp → LoopData (N.st []) (N.fcl []) (N.fmap [])
  /-- ⭐Each node holds the rule's closed sentences, where the lifts are derived from them. -/
  ax : ∀ s, N.Live s → ModalSys.axNeed = true → AxOk (N.st s).M
  srcMcs : N.hb → Theory.IsMCS N.src.M
  /-- ⭐The edge from the world asked about into the hub. -/
  hub : N.hb → FwdData N.src (N.st []) none (N.fcl []) (N.fmap [])
  /-- The hub and the self-edge exclude each other. -/
  excl : N.hb → ¬ N.lp

variable {N}

theorem live_of_nch {N N' : GNetSt σ} (h : N'.nch = N.nch) : ∀ k, N'.Live k ↔ N.Live k
  | [] => Iff.rfl
  | c :: p => by
      change N'.Live p ∧ c < N'.nch p ↔ N.Live p ∧ c < N.nch p
      rw [live_of_nch h p, h]

/-! ## Growing one node -/

/-- The network with node `s` in state `t`. -/
def setSt (N : GNetSt σ) (s : Node) (t : NodeSt σ) : GNetSt σ :=
  { N with st := Function.update N.st s t }

theorem setSt_self (N : GNetSt σ) (s : Node) (t : NodeSt σ) : (N.setSt s t).st s = t := by
  unfold setSt
  exact Function.update_self s t N.st

theorem setSt_ne (N : GNetSt σ) {s k : Node} (t : NodeSt σ) (h : k ≠ s) :
    (N.setSt s t).st k = N.st k := by
  unfold setSt
  exact Function.update_of_ne h t N.st

theorem live_setSt (N : GNetSt σ) (s : Node) (t : NodeSt σ) (k : Node) :
    (N.setSt s t).Live k ↔ N.Live k :=
  live_of_nch (N := N) (N' := N.setSt s t) rfl k

/-- ⭐Growing one live node conservatively preserves the invariants. -/
theorem Good.setSt (hN : N.Good) {s : Node} {t : NodeSt σ} (hs : N.Live s)
    (hg : Grows (N.st s) t) (ht : Theory.IsMCS t.M) : (N.setSt s t).Good := by
  refine ⟨fun k hk => ?_, fun c p hk => ?_, hN.kindRoot, hN.flags, fun hl => ?_,
    fun k hk hn => ?_, hN.srcMcs, fun hb => ?_, hN.excl⟩
  · rw [live_setSt] at hk
    by_cases hks : k = s
    · subst hks
      rw [setSt_self]
      exact ht
    · rw [setSt_ne _ _ hks]
      exact hN.mcs k hk
  · rw [live_setSt] at hk
    have hf := hN.fwd c p hk
    unfold FwdOk at hf ⊢
    change FwdData ((N.setSt s t).st p) ((N.setSt s t).st (c :: p)) _ _ _
    by_cases hkp : (c :: p : Node) = s
    · subst hkp
      rw [setSt_ne _ _ (fun h => NetSt.ne_parent c p h.symm), setSt_self]
      exact hf.grow_tgt hg
    · rw [setSt_ne _ _ hkp]
      by_cases hps : p = s
      · subst hps
        rw [setSt_self]
        exact hf.grow_src (hN.mcs p hk.1) ht hg
      · rw [setSt_ne _ _ hps]
        exact hf
  · have h := hN.loop hl
    change LoopData ((N.setSt s t).st []) _ _
    by_cases hs0 : s = []
    · subst hs0
      rw [setSt_self]
      exact ⟨(h.1.grow_tgt hg).grow_src (hN.mcs [] trivial) ht hg, h.2⟩
    · rw [setSt_ne _ _ (Ne.symm hs0)]
      exact h
  · rw [live_setSt] at hk
    by_cases hks : k = s
    · subst hks
      rw [setSt_self]
      exact (hN.ax k hk hn).grow hg
    · rw [setSt_ne _ _ hks]
      exact hN.ax k hk hn
  · have h := hN.hub hb
    change FwdData N.src ((N.setSt s t).st []) none (N.fcl []) (N.fmap [])
    by_cases hs0 : s = []
    · subst hs0
      rw [setSt_self]
      exact h.grow_tgt hg
    · rw [setSt_ne _ _ (Ne.symm hs0)]
      exact h

/-- The network with the edge into `k` recommitted. -/
def setFwd (N : GNetSt σ) (k : Node) (cl : List VarType) (f : VarSymb → LEnt σ) :
    GNetSt σ :=
  { N with fcl := Function.update N.fcl k cl, fmap := Function.update N.fmap k f }

theorem live_setFwd (N : GNetSt σ) (k : Node) (cl : List VarType) (f : VarSymb → LEnt σ)
    (k' : Node) : (N.setFwd k cl f).Live k' ↔ N.Live k' :=
  live_of_nch (N := N) (N' := N.setFwd k cl f) rfl k'

/-- Recommitting one edge with good data preserves the invariants. -/
theorem Good.setFwd (hN : N.Good) {c : ℕ} {p : Node} {cl : List VarType}
    {f : VarSymb → LEnt σ} (hd : FwdData (N.st p) (N.st (c :: p)) (N.kind (c :: p)) cl f) :
    (N.setFwd (c :: p) cl f).Good := by
  refine ⟨fun s hs => hN.mcs s ((live_setFwd _ _ _ _ s).mp hs), fun c' p' hk' => ?_, hN.kindRoot,
    hN.flags, fun hl => ?_, fun s hs hn => hN.ax s ((live_setFwd _ _ _ _ s).mp hs) hn,
    hN.srcMcs, fun hb => ?_, hN.excl⟩
  · rw [live_setFwd] at hk'
    unfold FwdOk
    by_cases he : (c' :: p' : Node) = c :: p
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      simp only [GNetSt.setFwd, Function.update_self]
      exact hd
    · have := hN.fwd c' p' hk'
      unfold FwdOk at this
      simp only [GNetSt.setFwd, Function.update_of_ne he]
      exact this
  · change LoopData (N.st []) (Function.update N.fcl (c :: p) cl [])
      (Function.update N.fmap (c :: p) f [])
    rw [Function.update_of_ne (List.cons_ne_nil c p).symm,
      Function.update_of_ne (List.cons_ne_nil c p).symm]
    exact hN.loop hl
  · change FwdData N.src (N.st []) none (Function.update N.fcl (c :: p) cl [])
      (Function.update N.fmap (c :: p) f [])
    rw [Function.update_of_ne (List.cons_ne_nil c p).symm,
      Function.update_of_ne (List.cons_ne_nil c p).symm]
    exact hN.hub hb

/-- Recommitting the root's self-edge with good data preserves the invariants. -/
theorem Good.setLoop (hN : N.Good) (hl : N.lp) {cl : List VarType} {f : VarSymb → LEnt σ}
    (hd : LoopData (N.st []) cl f) : (N.setFwd [] cl f).Good := by
  refine ⟨fun s hs => hN.mcs s ((live_setFwd _ _ _ _ s).mp hs), fun c p hk => ?_, hN.kindRoot,
    hN.flags, fun _ => ?_, fun s hs hn => hN.ax s ((live_setFwd _ _ _ _ s).mp hs) hn,
    hN.srcMcs, fun hb => absurd hl (hN.excl hb), hN.excl⟩
  · rw [live_setFwd] at hk
    have := hN.fwd c p hk
    unfold FwdOk at this ⊢
    change FwdData (N.st p) (N.st (c :: p)) (N.kind (c :: p))
      (Function.update N.fcl [] cl (c :: p)) (Function.update N.fmap [] f (c :: p))
    rw [Function.update_of_ne (List.cons_ne_nil c p), Function.update_of_ne (List.cons_ne_nil c p)]
    exact this
  · change LoopData (N.st []) (Function.update N.fcl [] cl []) (Function.update N.fmap [] f [])
    rw [Function.update_self, Function.update_self]
    exact hd

/-- Recommitting the edge into the hub with good data preserves the invariants. -/
theorem Good.setHub (hN : N.Good) (hb : N.hb) {cl : List VarType} {f : VarSymb → LEnt σ}
    (hd : FwdData N.src (N.st []) none cl f) : (N.setFwd [] cl f).Good := by
  refine ⟨fun s hs => hN.mcs s ((live_setFwd _ _ _ _ s).mp hs), fun c p hk => ?_, hN.kindRoot,
    hN.flags, fun hl => absurd hl (hN.excl hb),
    fun s hs hn => hN.ax s ((live_setFwd _ _ _ _ s).mp hs) hn, hN.srcMcs, fun _ => ?_, hN.excl⟩
  · rw [live_setFwd] at hk
    have := hN.fwd c p hk
    unfold FwdOk at this ⊢
    change FwdData (N.st p) (N.st (c :: p)) (N.kind (c :: p))
      (Function.update N.fcl [] cl (c :: p)) (Function.update N.fmap [] f (c :: p))
    rw [Function.update_of_ne (List.cons_ne_nil c p), Function.update_of_ne (List.cons_ne_nil c p)]
    exact this
  · change FwdData N.src (N.st []) none (Function.update N.fcl [] cl [])
      (Function.update N.fmap [] f [])
    rw [Function.update_self, Function.update_self]
    exact hd

/-! ## Realising forward -/

/-- What an edge puts into the child when the parent's next variable, of type `A`, is freshly
    realised. -/
noncomputable def grealSet (hF : ModalSys.Four = true) (ts tt : NodeSt σ) (k : Option VarSymb)
    (cl : List VarType) (f : VarSymb → LEnt σ) (A : VarType) :
    Set (WFF σ (ctxOf (A.gc :: tt.l)) 0) :=
  {φ | ∃ (hle : (ctxOf (A :: cl)).Le (ctxOf ts.l)) (hk : KDecl (ctxOf cl) k)
    (hf : EntOk ((ctxOf cl).kView k) (ctxOf tt.l) f)
    (ψ : WFF σ ((ctxOf (A :: cl)).kView k) 0),
    WFF.mono hle (kBox k (kDecl_mono (ctxOf_le_append [A] cl) hk) ψ) ∈ ts.M ∧
      φ = gextArrow hF hk hf ψ}

/-- The child grown by the fresh realisation of the parent's next variable. -/
noncomputable def grealStep (hF : ModalSys.Four = true) (ts tt : NodeSt σ) (k : Option VarSymb)
    (cl : List VarType) (f : VarSymb → LEnt σ) : NodeSt σ :=
  ⟨(nextTy ts.l cl).gc :: tt.l, complete (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).gc] tt.l) ''
    tt.M ∪ grealSet hF ts tt k cl f (nextTy ts.l cl))⟩

/-- ⭐One realisation step along an edge. -/
theorem grealStep_ok (hF : ModalSys.Four = true) {ts tt : NodeSt σ} {k : Option VarSymb}
    {cl : List VarType} {f : VarSymb → LEnt σ} (hs : Theory.IsMCS ts.M)
    (ht : Theory.IsMCS tt.M) (hd : FwdData ts tt k cl f) (hlt : cl.length < ts.l.length) :
    Theory.IsMCS (grealStep hF ts tt k cl f).M ∧ Grows tt (grealStep hF ts tt k cl f) ∧
      FwdData ts (grealStep hF ts tt k cl f) k (nextTy ts.l cl :: cl)
        (gextF f (nextTy ts.l cl) cl.length tt.l.length) := by
  obtain ⟨hsuf, hk, hf, htr⟩ := hd
  have hsuf' := suffix_next hsuf hlt
  have hle := ctxOf_le_of_suffix hsuf'
  have hcons := grealise_consistent hF hs hle ht hk hf htr
  have hsub : WFF.mono (ctxOf_le_append [(nextTy ts.l cl).gc] tt.l) '' tt.M ∪
      grealSet hF ts tt k cl f (nextTy ts.l cl) ⊆
        WFF.mono (ctxOf_le_append [(nextTy ts.l cl).gc] tt.l) '' tt.M ∪
          {φ | ∃ ψ, WFF.mono hle (kBox k (kDecl_mono (ctxOf_le_append [_] cl) hk) ψ) ∈ ts.M ∧
            φ = gextArrow hF hk hf ψ} := by
    rintro φ (h | ⟨_, _, _, ψ, h₁, h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ψ, h₁, h₂⟩
  obtain ⟨hS, hmcs⟩ := complete_spec (hcons.mono hsub)
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hS (Or.inl ⟨φ, hφ, rfl⟩)⟩, hsuf',
    kDecl_mono (ctxOf_le_append [_] cl) hk, itemOk_gextF hF (kOld_of_kDecl hk) hf, ?_⟩
  intro ψ hψ
  rw [mono_kBox] at hψ
  exact hS (Or.inr ⟨hle, hk, hf, ψ, by rw [mono_kBox]; exact hψ, rfl⟩)

open Classical in
/-- ⭐Commit the parent's next variable along the edge into `k`, or the root's along its
    self-edge. -/
noncomputable def realF (hF : ModalSys.Four = true) (N : GNetSt σ) : Node → GNetSt σ
  | [] =>
      if N.lp ∧ (N.fcl []).length < (N.st []).l.length then
        (N.setSt [] (gloopStep (N.st []) (N.fcl []) (N.fmap []))).setFwd []
          (nextTy (N.st []).l (N.fcl []) :: N.fcl [])
          (gloopF (N.fmap []) (N.fcl []).length (N.st []).l.length)
      else if N.hb ∧ (N.fcl []).length < N.src.l.length then
        (N.setSt [] (grealStep hF N.src (N.st []) none (N.fcl []) (N.fmap []))).setFwd []
          (nextTy N.src.l (N.fcl []) :: N.fcl [])
          (gextF (N.fmap []) (nextTy N.src.l (N.fcl [])) (N.fcl []).length (N.st []).l.length)
      else N
  | c :: p =>
      if (N.fcl (c :: p)).length < (N.st p).l.length then
        (N.setSt (c :: p) (grealStep hF (N.st p) (N.st (c :: p)) (N.kind (c :: p))
          (N.fcl (c :: p)) (N.fmap (c :: p)))).setFwd (c :: p)
          (nextTy (N.st p).l (N.fcl (c :: p)) :: N.fcl (c :: p))
          (gextF (N.fmap (c :: p)) (nextTy (N.st p).l (N.fcl (c :: p))) (N.fcl (c :: p)).length
            (N.st (c :: p)).l.length)
      else N

/-- ⭐Realising forward preserves the invariants. -/
theorem Good.realF (hF : ModalSys.Four = true) (hN : N.Good) {k : Node} (hk : N.Live k) :
    (N.realF hF k).Good := by
  match k with
  | [] =>
      simp only [GNetSt.realF]
      split_ifs with h h'
      · obtain ⟨hl, hlt⟩ := h
        obtain ⟨-, hV, hS, hT⟩ := hN.flags hl
        obtain ⟨hmcs, hg, hfd⟩ := gloopStep_ok hF hV hS hT (hN.mcs [] trivial) (hN.loop hl) hlt
        refine (hN.setSt (s := []) trivial hg hmcs).setLoop hl ?_
        rw [setSt_self]
        exact hfd
      · obtain ⟨hb, hlt⟩ := h'
        obtain ⟨hmcs, hg, hfd⟩ :=
          grealStep_ok hF (hN.srcMcs hb) (hN.mcs [] trivial) (hN.hub hb) hlt
        refine (hN.setSt (s := []) trivial hg hmcs).setHub hb ?_
        change FwdData N.src ((N.setSt [] _).st []) none _ _
        rw [setSt_self]
        exact hfd
      · exact hN
  | c :: p =>
      simp only [GNetSt.realF]
      split_ifs with hlt
      · obtain ⟨hmcs, hg, hfd⟩ := grealStep_ok hF (hN.mcs p hk.1) (hN.mcs _ hk) (hN.fwd c p hk) hlt
        have hN₁ := hN.setSt hk hg hmcs
        refine hN₁.setFwd ?_
        change FwdData ((N.setSt _ _).st p) ((N.setSt _ _).st (c :: p)) _ _ _
        rw [setSt_ne _ _ (fun h => NetSt.ne_parent c p h.symm), setSt_self]
        exact hfd
      · exact hN

end GNetSt

end GArrow

end V12M
