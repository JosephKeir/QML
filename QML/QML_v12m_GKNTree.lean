import QML.QML_v12m_GK

/-!
# QML v12m — the nested calculus `GKN`: trees and the context of a node

`GKN` (N: **nested**) is the first-order version of the prototype `KBNestedProto`: a sequent is
a **tree** of sequents, rules act at any node (docs §12.39, §12.49).  This file is its data.

* A **label** is a node of the tree: a list of child indices, **innermost first** (`k :: τ` is the
  `k`-th child of `τ`), so that recursion on it is structural.
* An **edge** into a node has a kind: `□` (made by `□R` or `serial`) or `◇_x` (made by `◇_xL`,
  `x` an address of the parent).
* A **birth** is a root name and a type introduced at a node (an eigenvariable, or the end
  sequent's declarations at the root).
* ⭐`Tree.ctxAt Γ₀ D τ`, **the context of a node**: computed from the root down, each edge's view
  of the parent's context (`boxIn`, `diaIn x`) plus the node's own births (representation (C),
  §12.49).
* ⭐`Tree.ctxAt_addEdge`, `Tree.ctxAt_addBirth`: growing the tree **weakens every node's
  context**, so a rule's premise is the sequent weakened node-wise (`Seq.mono`).
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace GKN

/-- A node: child indices, innermost first. -/
abbrev Lab := List ℕ

/-- The kind of the edge into a node: a `□` child, or a `◇_x` child. -/
inductive EdgeKind where
  | box
  | dia (x : VarSymb)

/-- A tree: its edges (each into a node, with its kind) and its births, both newest first.
    Finite, so a fresh child index always exists. -/
structure Tree where
  edges : List (Lab × EdgeKind) := []
  births : List (Lab × Root × VarType) := []

/-- `Γ` with a list of declarations added, the head last. -/
def _root_.V12M.Ctx.inserts (Γ : Ctx) : List (Root × VarType) → Ctx
  | [] => Γ
  | b :: L => (Γ.inserts L).insert b.1 b.2

namespace Tree

variable (D : Tree)

/-- The edge into a node, if any: the newest one recorded. -/
def edge (τ : Lab) : Option EdgeKind :=
  (D.edges.find? fun e => decide (e.1 = τ)).map Prod.snd

/-- The view an edge takes of the parent's context. -/
def view (τ : Lab) (Γ : Ctx) : Ctx :=
  match D.edge τ with
  | some (.dia x) => Γ.diaIn x
  | _ => Γ.boxIn

/-- The declarations born at a node. -/
def birthsAt (τ : Lab) : List (Root × VarType) :=
  (D.births.filter fun b => decide (b.1 = τ)).map Prod.snd

/-- ⭐**The context of a node**: the edge's view of the parent's, with the node's births. -/
def ctxAt (Γ₀ : Ctx) : Lab → Ctx
  | [] => Γ₀.inserts (D.birthsAt [])
  | k :: τ => (D.view (k :: τ) (ctxAt Γ₀ τ)).inserts (D.birthsAt (k :: τ))

/-- A new edge into an absent node. -/
def addEdge (c : Lab) (e : EdgeKind) : Tree where
  edges := (c, e) :: D.edges
  births := D.births

/-- A new birth at a node. -/
def addBirth (τ : Lab) (r : Root) (T : VarType) : Tree where
  edges := D.edges
  births := (τ, r, T) :: D.births

theorem edge_addEdge (c : Lab) (e : EdgeKind) (σ : Lab) :
    (D.addEdge c e).edge σ = if σ = c then some e else D.edge σ := by
  unfold edge addEdge
  by_cases h : σ = c
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- A root is **fresh for the tree**: for the end sequent's context and born nowhere. -/
structure Fresh (Γ₀ : Ctx) (r : Root) : Prop where
  ctx : Γ₀.RootFresh r
  births : ∀ b ∈ D.births, b.2.1 ≠ r

end Tree

/-! ## Freshness and weakening along the tree -/

theorem _root_.V12M.Ctx.RootFresh.inserts {Γ : Ctx} {r : Root} (h : Γ.RootFresh r) :
    ∀ L : List (Root × VarType), (∀ b ∈ L, b.1 ≠ r) → (Γ.inserts L).RootFresh r
  | [], _ => h
  | b :: L, hL =>
      (Ctx.RootFresh.inserts h L fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')).insert_ne
        (hL b List.mem_cons_self) b.2

theorem _root_.V12M.Ctx.Le.inserts {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ L : List (Root × VarType), (Γ.inserts L).Le (Γ'.inserts L)
  | [] => h
  | b :: L => (Ctx.Le.inserts h L).insert b.1 b.2

namespace Tree

variable {D : Tree}

theorem view_le {τ : Lab} {Γ Γ' : Ctx} (h : Γ.Le Γ') : (D.view τ Γ).Le (D.view τ Γ') := by
  unfold view
  split
  · exact h.diaIn _
  · exact h.boxIn

theorem birthsAt_fresh {r : Root} (hf : ∀ b ∈ D.births, b.2.1 ≠ r) (τ : Lab) :
    ∀ b ∈ D.birthsAt τ, b.1 ≠ r := by
  intro b hb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
  exact hf b' (List.mem_filter.mp hb').1

/-- ⭐A tree-fresh root is fresh at every node. -/
theorem Fresh.at {Γ₀ : Ctx} {r : Root} (h : D.Fresh Γ₀ r) : ∀ τ, (D.ctxAt Γ₀ τ).RootFresh r
  | [] => h.ctx.inserts _ (birthsAt_fresh h.births [])
  | k :: τ => by
      have ih := Fresh.at h τ
      refine Ctx.RootFresh.inserts ?_ _ (birthsAt_fresh h.births (k :: τ))
      unfold view
      split
      · exact ih.diaIn _
      · exact ih.boxIn

/-- ⭐**A new edge weakens every node's context**: the node had the default `□` view. -/
theorem ctxAt_addEdge {Γ₀ : Ctx} {c : Lab} (hc : D.edge c = none) (e : EdgeKind) :
    ∀ τ, (D.ctxAt Γ₀ τ).Le ((D.addEdge c e).ctxAt Γ₀ τ)
  | [] => Ctx.Le.refl _
  | k :: τ => by
      have ih := ctxAt_addEdge (Γ₀ := Γ₀) hc e τ
      simp only [ctxAt]
      refine Ctx.Le.inserts ((view_le ih).trans ?_) _
      unfold view
      rw [edge_addEdge]
      by_cases hk : k :: τ = c
      · subst hk
        simp only [hc]
        cases e with
        | box => exact Ctx.Le.refl _
        | dia x => exact Ctx.le_boxIn_diaIn _ x
      · simp only [if_neg hk]
        exact Ctx.Le.refl _

theorem birthsAt_addBirth (σ τ : Lab) (r : Root) (T : VarType) :
    (D.addBirth σ r T).birthsAt τ = if τ = σ then (r, T) :: D.birthsAt τ else D.birthsAt τ := by
  unfold birthsAt addBirth
  by_cases h : τ = σ
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- A birth off a node's branch leaves its context alone. -/
theorem ctxAt_addBirth_off {Γ₀ : Ctx} {σ : Lab} {r : Root} {T : VarType} :
    ∀ τ, ¬ σ <:+ τ → (D.addBirth σ r T).ctxAt Γ₀ τ = D.ctxAt Γ₀ τ
  | [], h => by
      simp only [ctxAt]
      rw [birthsAt_addBirth, if_neg (fun he => h (by subst he; exact List.suffix_refl _))]
  | k :: τ, h => by
      simp only [ctxAt]
      rw [ctxAt_addBirth_off τ (fun h' => h (h'.trans (List.suffix_cons k τ))),
        birthsAt_addBirth, if_neg (fun he => h (by subst he; exact List.suffix_refl _))]
      rfl

/-- ⭐**A new birth of a tree-fresh root weakens every node's context.** -/
theorem ctxAt_addBirth {Γ₀ : Ctx} {r : Root} (hf : D.Fresh Γ₀ r) (σ : Lab) (T : VarType) :
    ∀ τ, (D.ctxAt Γ₀ τ).Le ((D.addBirth σ r T).ctxAt Γ₀ τ)
  | [] => by
      simp only [ctxAt]
      rw [birthsAt_addBirth]
      split
      · have h0 := (hf.at []).root
        simp only [ctxAt] at h0
        exact Ctx.le_insert h0 T
      · exact Ctx.Le.refl _
  | k :: τ => by
      simp only [ctxAt]
      have hv : (D.view (k :: τ) (D.ctxAt Γ₀ τ)).Le
          ((D.addBirth σ r T).view (k :: τ) ((D.addBirth σ r T).ctxAt Γ₀ τ)) :=
        view_le (D := D) (ctxAt_addBirth hf σ T τ)
      rw [birthsAt_addBirth]
      split
      · rename_i he
        have hoff : ¬ σ <:+ τ := fun h' => by
          have := h'.length_le
          rw [← he] at this
          simp at this
        refine (Ctx.Le.inserts hv _).trans (Ctx.le_insert ?_ T)
        rw [ctxAt_addBirth_off τ hoff]
        have h0 := (hf.at (k :: τ)).root
        simp only [ctxAt] at h0
        exact h0
      · exact Ctx.Le.inserts hv _

/-- ⭐The node of a new birth: its context is the old one with the birth. -/
theorem insert_le_addBirth {Γ₀ : Ctx} (τ : Lab) (r : Root) (T : VarType) :
    ((D.ctxAt Γ₀ τ).insert r T).Le ((D.addBirth τ r T).ctxAt Γ₀ τ) := by
  cases τ with
  | nil =>
      simp only [ctxAt]
      rw [birthsAt_addBirth, if_pos rfl]
      exact Ctx.Le.refl _
  | cons k τ =>
      have hoff : ¬ (k :: τ) <:+ τ := fun h' => by
        have := h'.length_le
        simp at this
      simp only [ctxAt]
      rw [birthsAt_addBirth, if_pos rfl, ctxAt_addBirth_off τ hoff]
      exact Ctx.Le.refl _

/-- ⭐A new `□`-child with no births: its context is the parent's `□` view. -/
theorem boxIn_le_addEdge {Γ₀ : Ctx} {τ : Lab} {k : ℕ} (hc : D.edge (k :: τ) = none)
    (hb : D.birthsAt (k :: τ) = []) :
    (D.ctxAt Γ₀ τ).boxIn.Le ((D.addEdge (k :: τ) .box).ctxAt Γ₀ (k :: τ)) := by
  simp only [ctxAt]
  have hb' : (D.addEdge (k :: τ) .box).birthsAt (k :: τ) = [] := hb
  rw [hb']
  unfold view
  rw [edge_addEdge, if_pos rfl]
  exact (ctxAt_addEdge hc .box τ).boxIn

/-- ⭐A new `◇_x`-child with no births: its context is the parent's `◇_x` view. -/
theorem diaIn_le_addEdge {Γ₀ : Ctx} {τ : Lab} {k : ℕ} (hc : D.edge (k :: τ) = none)
    (hb : D.birthsAt (k :: τ) = []) (x : VarSymb) :
    ((D.ctxAt Γ₀ τ).diaIn x).Le ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ (k :: τ)) := by
  simp only [ctxAt]
  have hb' : (D.addEdge (k :: τ) (.dia x)).birthsAt (k :: τ) = [] := hb
  rw [hb']
  unfold view
  rw [edge_addEdge, if_pos rfl]
  exact (ctxAt_addEdge hc (.dia x) τ).diaIn x

/-! ## The tree invariant -/

/-- ⭐**The tree invariant**: no birth twice, at most one birth per name, every name fresh for
    the end sequent's context. -/
structure OK (Γ₀ : Ctx) (D : Tree) : Prop where
  nodup : D.births.Nodup
  uniq : ∀ b ∈ D.births, ∀ b' ∈ D.births, b.2.1 = b'.2.1 → b = b'
  fresh : ∀ b ∈ D.births, Γ₀.RootFresh b.2.1
  free : ∀ b ∈ D.births, ∃ u, b.2.1 = .free u

theorem OK.addEdge {Γ₀ : Ctx} (h : D.OK Γ₀) (c : Lab) (e : EdgeKind) : (D.addEdge c e).OK Γ₀ :=
  ⟨h.nodup, h.uniq, h.fresh, h.free⟩

theorem OK.addBirth {Γ₀ : Ctx} (h : D.OK Γ₀) {u : ℕ} (hf : D.Fresh Γ₀ (.free u)) (τ : Lab)
    (T : VarType) : (D.addBirth τ (.free u) T).OK Γ₀ := by
  refine ⟨List.nodup_cons.mpr ⟨fun hm => hf.births _ hm rfl, h.nodup⟩, ?_, ?_, ?_⟩
  · intro b hb b' hb' he
    rcases List.mem_cons.mp hb with rfl | hb <;> rcases List.mem_cons.mp hb' with rfl | hb'
    · rfl
    · exact absurd he.symm (hf.births _ hb')
    · exact absurd he (hf.births _ hb)
    · exact h.uniq b hb b' hb' he
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hf.ctx
    · exact h.fresh b hb
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨u, rfl⟩
    · exact h.free b hb

theorem mem_birthsAt {τ : Lab} {b : Root × VarType} :
    b ∈ D.birthsAt τ ↔ (τ, b.1, b.2) ∈ D.births := by
  unfold birthsAt
  constructor
  · intro hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    obtain ⟨hm, he⟩ := List.mem_filter.mp hb'
    have : b'.1 = τ := by simpa using he
    rw [← this]
    exact hm
  · intro hb
    exact List.mem_map.mpr ⟨(τ, b.1, b.2), List.mem_filter.mpr ⟨hb, by simp⟩, rfl⟩

/-- A root born nowhere on a node's branch, and fresh for `Γ₀`, is fresh there. -/
theorem fresh_branch {Γ₀ : Ctx} {r : Root} (h0 : Γ₀.RootFresh r) :
    ∀ τ, (∀ b ∈ D.births, b.1 <:+ τ → b.2.1 ≠ r) → (D.ctxAt Γ₀ τ).RootFresh r
  | [], hb => by
      simp only [ctxAt]
      exact h0.inserts _ fun b hm => hb _ (mem_birthsAt.mp hm) (List.suffix_refl _)
  | k :: τ, hb => by
      have ih := fresh_branch h0 τ fun b hm hs => hb b hm (hs.trans (List.suffix_cons k τ))
      simp only [ctxAt]
      refine Ctx.RootFresh.inserts ?_ _ fun b hm => hb _ (mem_birthsAt.mp hm) (List.suffix_refl _)
      unfold view
      split
      · exact ih.diaIn _
      · exact ih.boxIn

theorem _root_.V12M.Ctx.le_inserts {Γ : Ctx} :
    ∀ L : List (Root × VarType), L.Pairwise (fun b b' => b.1 ≠ b'.1) →
      (∀ b ∈ L, Γ.RootFresh b.1) → Γ.Le (Γ.inserts L)
  | [], _, _ => Ctx.Le.refl _
  | b :: L, hp, hf => by
      obtain ⟨hb, hp⟩ := List.pairwise_cons.mp hp
      refine (Ctx.le_inserts L hp fun b' hm => hf b' (List.mem_cons_of_mem _ hm)).trans
        (Ctx.le_insert ?_ b.2)
      exact ((hf b List.mem_cons_self).inserts L fun b' hm => (hb b' hm).symm).root

theorem birthsAt_pairwise {Γ₀ : Ctx} (h : D.OK Γ₀) (τ : Lab) :
    (D.birthsAt τ).Pairwise (fun b b' => b.1 ≠ b'.1) := by
  have hp : D.births.Pairwise (fun b b' => b.2.1 ≠ b'.2.1) :=
    (List.Pairwise.imp_of_mem (R := (· ≠ ·)) (fun {b b'} hb hb' hne he =>
      hne (h.uniq b hb b' hb' he)) h.nodup)
  unfold birthsAt
  exact List.pairwise_map.mpr (hp.filter _)

/-- ⭐**A child's context contains its edge's view of the parent's**, under the invariant: the
    child's births are fresh there. -/
theorem view_le_ctxAt {Γ₀ : Ctx} (h : D.OK Γ₀) (k : ℕ) (τ : Lab) :
    (D.view (k :: τ) (D.ctxAt Γ₀ τ)).Le (D.ctxAt Γ₀ (k :: τ)) := by
  simp only [ctxAt]
  refine Ctx.le_inserts _ (birthsAt_pairwise h _) fun b hm => ?_
  have hb := mem_birthsAt.mp hm
  have hfr : (D.ctxAt Γ₀ τ).RootFresh b.1 := by
    refine fresh_branch (h.fresh _ hb) τ fun b' hb' hs he => ?_
    have := h.uniq b' hb' _ hb he
    rw [this] at hs
    have := hs.length_le
    simp at this
  unfold view
  split
  · exact hfr.diaIn _
  · exact hfr.boxIn

theorem boxIn_le_view (τ : Lab) (Γ : Ctx) : Γ.boxIn.Le (D.view τ Γ) := by
  unfold view
  split
  · exact Ctx.le_boxIn_diaIn _ _
  · exact Ctx.Le.refl _

/-- The inclusion `boxL` takes. -/
theorem boxIn_le_child {Γ₀ : Ctx} (h : D.OK Γ₀) (k : ℕ) (τ : Lab) :
    (D.ctxAt Γ₀ τ).boxIn.Le (D.ctxAt Γ₀ (k :: τ)) :=
  (boxIn_le_view _ _).trans (view_le_ctxAt h k τ)

/-- The inclusion `diaR` takes. -/
theorem diaIn_le_child {Γ₀ : Ctx} (h : D.OK Γ₀) {k : ℕ} {τ : Lab} {x : VarSymb}
    (he : D.edge (k :: τ) = some (.dia x)) :
    ((D.ctxAt Γ₀ τ).diaIn x).Le (D.ctxAt Γ₀ (k :: τ)) := by
  have h₁ := view_le_ctxAt h k τ
  unfold view at h₁
  rw [he] at h₁
  exact h₁

/-! ## Slots -/

theorem _root_.V12M.Ctx.SlotsFrom.inserts {Γ : Ctx} (h : Γ.SlotsFrom 0) :
    ∀ L : List (Root × VarType), (∀ b ∈ L, ∃ u, b.1 = .free u) → (Γ.inserts L).SlotsFrom 0
  | [], _ => h
  | b :: L, hL => by
      obtain ⟨u, hu⟩ := hL b List.mem_cons_self
      have ih := Ctx.SlotsFrom.inserts h L fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')
      change ((Γ.inserts L).insert b.1 b.2).SlotsFrom 0
      rw [hu]
      exact ih.insertFree u b.2

/-- Under the invariant every node's context has no slots. -/
theorem ctxAt_slots {Γ₀ : Ctx} (h0 : Γ₀.SlotsFrom 0) (h : D.OK Γ₀) :
    ∀ τ, (D.ctxAt Γ₀ τ).SlotsFrom 0
  | [] => by
      simp only [ctxAt]
      exact h0.inserts _ fun b hb => h.free _ (mem_birthsAt.mp hb)
  | k :: τ => by
      simp only [ctxAt]
      refine Ctx.SlotsFrom.inserts ?_ _ fun b hb => h.free _ (mem_birthsAt.mp hb)
      have ih := ctxAt_slots h0 h τ
      unfold view
      split
      · exact ih.diaIn _
      · exact ih.boxIn

/-! ## Relabelling nodes -/

/-- The root of an inserted declaration holds it, when the roots are distinct. -/
theorem _root_.V12M.Ctx.inserts_root {Γ : Ctx} :
    ∀ {L : List (Root × VarType)}, L.Pairwise (fun b b' => b.1 ≠ b'.1) → ∀ {b}, b ∈ L →
      (Γ.inserts L) (.root b.1) = some b.2
  | b' :: L, hp, b, hb => by
      obtain ⟨hb', hp⟩ := List.pairwise_cons.mp hp
      change ((Γ.inserts L).insert b'.1 b'.2) (.root b.1) = some b.2
      rcases List.mem_cons.mp hb with rfl | hb
      · simp [Ctx.insert]
      · have hne : b'.1 ≠ b.1 := hb' b hb
        simp only [Ctx.insert, VarSymb.atBelow_root]
        rw [if_neg (fun he => hne (VarSymb.root.inj he).symm)]
        exact Ctx.inserts_root hp hb

theorem _root_.V12M.Ctx.insert_le_of {Δ Ξ : Ctx} (h : Δ.Le Ξ) {r : Root} {T : VarType}
    (hr : Ξ (.root r) = some T) : (Δ.insert r T).Le Ξ := by
  refine ⟨fun v U hv => ?_, fun y X hy => h.wit y X hy⟩
  simp only [Ctx.insert] at hv
  split_ifs at hv with h₁ h₂
  · subst h₁
    cases hv
    exact hr
  · exact h v U hv

theorem _root_.V12M.Ctx.inserts_le_of :
    ∀ (L : List (Root × VarType)) {Δ Ξ : Ctx}, Δ.Le Ξ → (∀ b ∈ L, Ξ (.root b.1) = some b.2) →
      (Δ.inserts L).Le Ξ
  | [], _, _, h, _ => h
  | b :: L, _, _, h, hb =>
      Ctx.insert_le_of (Ctx.inserts_le_of L h fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))
        (hb b List.mem_cons_self)

/-- A node's births hold at its context's roots. -/
theorem ctxAt_root {Γ₀ : Ctx} (h : D.OK Γ₀) {τ : Lab} {b : Root × VarType}
    (hb : b ∈ D.birthsAt τ) : (D.ctxAt Γ₀ τ) (.root b.1) = some b.2 := by
  cases τ with
  | nil =>
      simp only [ctxAt]
      exact Ctx.inserts_root (birthsAt_pairwise h _) hb
  | cons k τ =>
      simp only [ctxAt]
      exact Ctx.inserts_root (birthsAt_pairwise h _) hb

end Tree

/-- ⭐**Relabelling by a child-index map**: the root stays, the `j`-th child of `ν` goes to the
    `g ν j`-th child of `ν`'s image.  Structural, so subtrees go to subtrees. -/
def lmap (g : Lab → ℕ → ℕ) : Lab → Lab
  | [] => []
  | j :: ν => g ν j :: lmap g ν

/-- An edge's image may be of a larger view: a `□`-edge goes to any edge, a `◇_x`-edge to a
    `◇_x`-edge. -/
def EdgeKind.Compat : EdgeKind → EdgeKind → Prop
  | .box, _ => True
  | .dia x, .dia y => x = y
  | .dia _, .box => False

namespace Tree

theorem view_box {D : Tree} {σ : Lab} {Γ : Ctx} (h : D.edge σ = none ∨ D.edge σ = some .box) :
    D.view σ Γ = Γ.boxIn := by
  unfold view
  rcases h with h | h <;> rw [h]

theorem view_dia {D : Tree} {σ : Lab} {Γ : Ctx} {x : VarSymb} (h : D.edge σ = some (.dia x)) :
    D.view σ Γ = Γ.diaIn x := by
  unfold view
  rw [h]

theorem view_le_view {D D' : Tree} {σ σ' : Lab} {Γ Γ' : Ctx} (h : Γ.Le Γ')
    (he : ∀ e, D.edge σ = some e → ∃ e', D'.edge σ' = some e' ∧ e.Compat e') :
    (D.view σ Γ).Le (D'.view σ' Γ') := by
  cases hD : D.edge σ with
  | none => rw [view_box (Or.inl hD)]; exact h.boxIn.trans (boxIn_le_view _ _)
  | some e =>
      cases e with
      | box => rw [view_box (Or.inr hD)]; exact h.boxIn.trans (boxIn_le_view _ _)
      | dia x =>
          obtain ⟨e', he', hc⟩ := he _ hD
          cases e' with
          | box => exact hc.elim
          | dia y =>
              change x = y at hc
              subst hc
              rw [view_dia hD, view_dia he']
              exact h.diaIn x

/-- ⭐**A relabelling that keeps edges (with compatible views) and births weakens every node's
    context into its image's**, given the invariant at the target. -/
theorem ctx_le_of_map {Γ₀ : Ctx} {D D' : Tree} (g : Lab → ℕ → ℕ) (hok : D'.OK Γ₀)
    (hedge : ∀ c e, D.edge c = some e → ∃ e', D'.edge (lmap g c) = some e' ∧ e.Compat e')
    (hbirth : ∀ τ b, b ∈ D.birthsAt τ → b ∈ D'.birthsAt (lmap g τ)) :
    ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ (lmap g τ))
  | [] => by
      have hΞ : Γ₀.Le (D'.ctxAt Γ₀ (lmap g [])) := by
        simp only [lmap, ctxAt]
        exact Ctx.le_inserts _ (birthsAt_pairwise hok _)
          fun b hb => hok.fresh _ (mem_birthsAt.mp hb)
      simp only [ctxAt]
      exact Ctx.inserts_le_of _ hΞ fun b hb => ctxAt_root hok (hbirth [] b hb)
  | j :: ν => by
      have ih := ctx_le_of_map g hok hedge hbirth ν
      have hv : (D.view (j :: ν) (D.ctxAt Γ₀ ν)).Le (D'.ctxAt Γ₀ (lmap g (j :: ν))) :=
        (view_le_view ih (hedge (j :: ν))).trans (view_le_ctxAt hok (g ν j) (lmap g ν))
      simp only [ctxAt]
      exact Ctx.inserts_le_of _ hv fun b hb => ctxAt_root hok (hbirth (j :: ν) b hb)

end Tree

end GKN

end V12M
