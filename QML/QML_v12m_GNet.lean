import QML.QML_v12m_GChild
import QML.QML_v12m_GFwd

/-!
# QML v12m — the growing tree: networks

The canonical model for strong 4 is the limit of **growing trees**, built round by round: B's
networks (`QML_v12m_BNet.lean`) without back arrows.  A node is a list of child indices, the
newest step first.  Each live node has the types of its variables and a maximal consistent theory
in them (`BArrow.NodeSt`).  Each child has one arrow, from its parent: an edge of kind `kind`
(`none` for `□`, `some x` for a child made for `◇_x`), whose committed part is the parent's
oldest variables `fcl` (a suffix of its list), sent by the item map `fmap`, with `□_k` transfer
(`FwdData`).  `Good` collects the invariants.

The operations, each preserving `Good`:
* `realF`: commit the parent's next variable along an edge (a fresh realisation, `gextF`);
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
  refine ⟨fun k hk => ?_, fun c p hk => ?_⟩
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
  refine ⟨fun s hs => hN.mcs s ((live_setFwd _ _ _ _ s).mp hs), fun c' p' hk' => ?_⟩
  rw [live_setFwd] at hk'
  unfold FwdOk
  by_cases he : (c' :: p' : Node) = c :: p
  · obtain ⟨rfl, rfl⟩ := List.cons.inj he
    simp only [GNetSt.setFwd, Function.update_self]
    exact hd
  · have := hN.fwd c' p' hk'
    unfold FwdOk at this
    simp only [GNetSt.setFwd, Function.update_of_ne he]
    exact this

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

/-- ⭐Commit the parent's next variable along the edge into `k`. -/
noncomputable def realF (hF : ModalSys.Four = true) (N : GNetSt σ) : Node → GNetSt σ
  | [] => N
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
  | [] => exact hN
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
