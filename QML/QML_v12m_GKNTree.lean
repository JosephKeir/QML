import QML.QML_v12m_GK
import QML.QML_v12m_CtxComm

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
* An **opening** is a witness's view opened at a node (`optL`, `Opt`): a kind and a witness.
* ⭐`Tree.ctxAt Γ₀ D τ`, **the context of a node**: computed from the root down, each edge's view
  of the parent's context (`boxIn`, `diaIn x`) plus the node's own births, then its openings
  (representation (C), §12.49; openings (O2), §12.50).  Openings reach the descendants, as
  births do.
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
  opens : List (Lab × WitKind × VarSymb) := []

/-- `Γ` with a list of declarations added, the head last. -/
def _root_.V12M.Ctx.inserts (Γ : Ctx) : List (Root × VarType) → Ctx
  | [] => Γ
  | b :: L => (Γ.inserts L).insert b.1 b.2

/-- `Γ` with a list of witness views opened, the head last. -/
def _root_.V12M.Ctx.optInsK (Γ : Ctx) : List (WitKind × VarSymb) → Ctx
  | [] => Γ
  | o :: L => (Γ.optInsK L).optInK o.1 o.2

/-- A witness's view is **opened** in `Γ`: its content is declared at its kind's step
    (`GK.reopenR`'s condition). -/
abbrev _root_.V12M.Ctx.Opened (Γ : Ctx) (κ : WitKind) (y : VarSymb) : Prop :=
  ∃ X, Γ.witK κ y = some X ∧ Γ (.step y κ.step) = some X

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

/-- The witness views opened at a node. -/
def opensAt (τ : Lab) : List (WitKind × VarSymb) :=
  (D.opens.filter fun o => decide (o.1 = τ)).map Prod.snd

/-- ⭐**The context of a node**: the edge's view of the parent's, with the node's births, then its
    openings. -/
def ctxAt (Γ₀ : Ctx) : Lab → Ctx
  | [] => (Γ₀.inserts (D.birthsAt [])).optInsK (D.opensAt [])
  | k :: τ => ((D.view (k :: τ) (ctxAt Γ₀ τ)).inserts (D.birthsAt (k :: τ))).optInsK
      (D.opensAt (k :: τ))

/-- A node's context before its openings. -/
def preAt (Γ₀ : Ctx) : Lab → Ctx
  | [] => Γ₀.inserts (D.birthsAt [])
  | k :: τ => (D.view (k :: τ) (D.ctxAt Γ₀ τ)).inserts (D.birthsAt (k :: τ))

theorem ctxAt_eq_pre (Γ₀ : Ctx) : ∀ τ, D.ctxAt Γ₀ τ = (D.preAt Γ₀ τ).optInsK (D.opensAt τ)
  | [] => rfl
  | _ :: _ => rfl

/-- A new edge into an absent node. -/
def addEdge (c : Lab) (e : EdgeKind) : Tree where
  edges := (c, e) :: D.edges
  births := D.births
  opens := D.opens

/-- A new birth at a node. -/
def addBirth (τ : Lab) (r : Root) (T : VarType) : Tree where
  edges := D.edges
  births := (τ, r, T) :: D.births
  opens := D.opens

/-- A new opening at a node (`optL`). -/
def addOpen (τ : Lab) (κ : WitKind) (y : VarSymb) : Tree where
  edges := D.edges
  births := D.births
  opens := (τ, κ, y) :: D.opens

@[simp] theorem opensAt_addEdge (c : Lab) (e : EdgeKind) : (D.addEdge c e).opensAt = D.opensAt :=
  rfl

@[simp] theorem opensAt_addBirth (σ : Lab) (r : Root) (T : VarType) :
    (D.addBirth σ r T).opensAt = D.opensAt := rfl

@[simp] theorem birthsAt_addEdge (c : Lab) (e : EdgeKind) :
    (D.addEdge c e).birthsAt = D.birthsAt := rfl

@[simp] theorem birthsAt_addOpen (σ : Lab) (κ : WitKind) (y : VarSymb) :
    (D.addOpen σ κ y).birthsAt = D.birthsAt := rfl

@[simp] theorem edge_addOpen (σ : Lab) (κ : WitKind) (y : VarSymb) :
    (D.addOpen σ κ y).edge = D.edge := rfl

@[simp] theorem edge_addBirth (σ : Lab) (r : Root) (T : VarType) :
    (D.addBirth σ r T).edge = D.edge := rfl

theorem opensAt_addOpen (σ τ : Lab) (κ : WitKind) (y : VarSymb) :
    (D.addOpen σ κ y).opensAt τ = if τ = σ then (κ, y) :: D.opensAt τ else D.opensAt τ := by
  unfold opensAt addOpen
  by_cases h : τ = σ
  · subst h
    simp
  · simp [h, Ne.symm h]

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

/-! ## Openings -/

theorem _root_.V12M.Ctx.RootFresh.optInsK {Γ : Ctx} {r : Root} (h : Γ.RootFresh r) :
    ∀ L : List (WitKind × VarSymb), (Γ.optInsK L).RootFresh r
  | [] => h
  | o :: L => (Ctx.RootFresh.optInsK h L).optInK o.1 o.2

theorem _root_.V12M.Ctx.Le.optInsK {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ L : List (WitKind × VarSymb), (Γ.optInsK L).Le (Γ'.optInsK L)
  | [] => h
  | o :: L => (Ctx.Le.optInsK h L).optInK o.1 o.2

theorem _root_.V12M.Ctx.le_optInsK (Γ : Ctx) : ∀ L : List (WitKind × VarSymb), Γ.Le (Γ.optInsK L)
  | [] => Ctx.Le.refl Γ
  | o :: L => (Ctx.le_optInsK Γ L).trans (Ctx.le_optInK _ o.1 o.2)

theorem _root_.V12M.Ctx.optInsK_wit (Γ : Ctx) :
    ∀ L : List (WitKind × VarSymb), (Γ.optInsK L).wit = Γ.wit
  | [] => rfl
  | o :: L => (Ctx.optInK_wit _ o.1 o.2).trans (Ctx.optInsK_wit Γ L)

theorem _root_.V12M.Ctx.SlotsFrom.optInsK {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) :
    ∀ L : List (WitKind × VarSymb), (Γ.optInsK L).SlotsFrom d
  | [] => h
  | o :: L => (Ctx.SlotsFrom.optInsK h L).optInK o.1 o.2

theorem _root_.V12M.Ctx.none_of_le {Γ Γ' : Ctx} (h : Γ.Le Γ') {v : VarSymb} (hv : Γ' v = none) :
    Γ v = none := by
  cases h' : Γ v with
  | none => rfl
  | some T => rw [h v T h'] at hv; cases hv

theorem _root_.V12M.Ctx.Opened.mono {Γ Γ' : Ctx} (h : Γ.Le Γ') {κ : WitKind} {y : VarSymb} :
    Γ.Opened κ y → Γ'.Opened κ y
  | ⟨X, h₁, h₂⟩ => ⟨X, h.witK h₁, h _ _ h₂⟩

/-- In its own view a witness is opened. -/
theorem _root_.V12M.Ctx.opened_self {Γ : Ctx} {κ : WitKind} {y : VarSymb} {X : VarType}
    (hy : Γ.witK κ y = some X) : (Γ.optInK κ y).Opened κ y :=
  ⟨X, (Ctx.le_optInK Γ κ y).witK hy, Ctx.optInK_content hy⟩

/-- ⭐**A view inside a context where the witness is opened** stays inside it. -/
theorem _root_.V12M.Ctx.optInK_le_of {Γ Ξ : Ctx} (h : Γ.Le Ξ) {κ : WitKind} {y : VarSymb}
    (ho : Ξ.Opened κ y) : (Γ.optInK κ y).Le Ξ := by
  obtain ⟨X, hX, hc⟩ := ho
  refine ⟨fun v U hv => ?_, fun z Z hz => h.wit z Z (by rwa [Ctx.optInK_wit] at hz)⟩
  cases κ with
  | arrow =>
      change Γ.optIn y v = some U at hv
      rw [Ctx.optIn_apply] at hv
      split_ifs at hv with hc'
      · subst hc'
        cases hw : Γ.wit y with
        | none => rw [hw] at hv; exact h _ _ hv
        | some W =>
            rw [hw] at hv
            cases hv
            have hW : Ξ.wit y = some U := h.wit y U hw
            have hX' : Ξ.wit y = some X := hX
            rw [hW] at hX'
            cases hX'
            exact hc
      · exact h _ _ hv
  | ident =>
      change Γ.optInTTy y v = some U at hv
      unfold Ctx.optInTTy at hv
      split_ifs at hv with hc'
      · subst hc'
        cases hw : Γ.witT y with
        | none => rw [hw] at hv; exact h _ _ hv
        | some W =>
            rw [hw] at hv
            cases hv
            have hW : Ξ.witT y = some U := h.witT hw
            have hX' : Ξ.witT y = some X := hX
            rw [hW] at hX'
            cases hX'
            exact hc
      · exact h _ _ hv

/-- A fresh declaration and an opening, in either order: the declaration first is larger. -/
theorem _root_.V12M.Ctx.insert_optInK_le {Γ : Ctx} {u : ℕ} (hu : Γ.RootFresh (.free u))
    (T : VarType) (κ : WitKind) (y : VarSymb) :
    ((Γ.optInK κ y).insert (.free u) T).Le ((Γ.insert (.free u) T).optInK κ y) := by
  cases hw : Γ.witK κ y with
  | some X => rw [Ctx.insert_optInK_comm hu T hw]; exact Ctx.Le.refl _
  | none =>
      cases κ with
      | arrow =>
          change ((Γ.optIn y).insert (.free u) T).Le ((Γ.insert (.free u) T).optIn y)
          rw [Ctx.insert_optIn_comm]
          exact Ctx.Le.refl _
      | ident =>
          change ((Γ.optInT y).insert (.free u) T).Le ((Γ.insert (.free u) T).optInT y)
          rw [Ctx.optInT_of_witT_none (y := y) hw]
          exact Ctx.le_optInT _ y

theorem _root_.V12M.Ctx.insert_optInsK_le {Γ : Ctx} {u : ℕ} (hu : Γ.RootFresh (.free u))
    (T : VarType) : ∀ L : List (WitKind × VarSymb),
    ((Γ.optInsK L).insert (.free u) T).Le ((Γ.insert (.free u) T).optInsK L)
  | [] => Ctx.Le.refl _
  | o :: L => (Ctx.insert_optInK_le (hu.optInsK L) T o.1 o.2).trans
      ((Ctx.insert_optInsK_le hu T L).optInK o.1 o.2)

/-- A declaration of an opened context is the context's, or an opening's content. -/
theorem _root_.V12M.Ctx.optInsK_cases {Γ : Ctx} :
    ∀ {L : List (WitKind × VarSymb)} {v : VarSymb} {U : VarType}, (Γ.optInsK L) v = some U →
      Γ v = some U ∨ ∃ o ∈ L, v = .step o.2 o.1.step
  | [], _, _, h => Or.inl h
  | o :: L, v, U, h => by
      have key : (Γ.optInsK L) v = some U ∨ v = .step o.2 o.1.step := by
        obtain ⟨κ, y⟩ := o
        cases κ with
        | arrow =>
            change (Γ.optInsK L).optIn y v = some U at h
            rw [Ctx.optIn_apply] at h
            split_ifs at h with hc
            · exact Or.inr hc
            · exact Or.inl h
        | ident =>
            change (Γ.optInsK L).optInTTy y v = some U at h
            unfold Ctx.optInTTy at h
            split_ifs at h with hc
            · exact Or.inr hc
            · exact Or.inl h
      rcases key with h' | h'
      · rcases Ctx.optInsK_cases h' with h'' | ⟨o', ho', e⟩
        · exact Or.inl h''
        · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', e⟩
      · exact Or.inr ⟨o, List.mem_cons_self, h'⟩

/-- Every opening of the list **takes effect**: `Opt` is on and its witness is there when it is
    opened. -/
def _root_.V12M.Ctx.OptsEff (Γ : Ctx) : List (WitKind × VarSymb) → Prop
  | [] => True
  | o :: L => Γ.OptsEff L ∧ ModalSys.Opt = true ∧ ∃ X, (Γ.optInsK L).witK o.1 o.2 = some X

theorem _root_.V12M.Ctx.OptsEff.mono {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ {L : List (WitKind × VarSymb)}, Γ.OptsEff L → Γ'.OptsEff L
  | [], _ => trivial
  | _ :: L, ⟨he, hO, X, hX⟩ => ⟨Ctx.OptsEff.mono h he, hO, X, (Ctx.Le.optInsK h L).witK hX⟩

/-- Openings that took effect are opened. -/
theorem _root_.V12M.Ctx.opened_of_eff {Γ : Ctx} :
    ∀ {L : List (WitKind × VarSymb)}, Γ.OptsEff L → ∀ o ∈ L, (Γ.optInsK L).Opened o.1 o.2
  | [], _, _, h => by simp at h
  | o :: L, ⟨he, _, X, hX⟩, o', ho' => by
      rcases List.mem_cons.mp ho' with rfl | ho'
      · exact Ctx.opened_self hX
      · exact (Ctx.opened_of_eff he o' ho').mono (Ctx.le_optInK _ _ _)

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
  | [] => (h.ctx.inserts _ (birthsAt_fresh h.births [])).optInsK _
  | k :: τ => by
      have ih := Fresh.at h τ
      refine (Ctx.RootFresh.inserts ?_ _ (birthsAt_fresh h.births (k :: τ))).optInsK _
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
      refine Ctx.Le.optInsK (Ctx.Le.inserts ((view_le ih).trans ?_) _) _
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
      rw [birthsAt_addBirth, if_neg (fun he => h (by subst he; exact List.suffix_refl _)),
        opensAt_addBirth]
  | k :: τ, h => by
      simp only [ctxAt]
      rw [ctxAt_addBirth_off τ (fun h' => h (h'.trans (List.suffix_cons k τ))),
        birthsAt_addBirth, if_neg (fun he => h (by subst he; exact List.suffix_refl _)),
        opensAt_addBirth]
      rfl

/-- ⭐**A new birth of a tree-fresh root weakens every node's context.** -/
theorem ctxAt_addBirth {Γ₀ : Ctx} {r : Root} (hf : D.Fresh Γ₀ r) (σ : Lab) (T : VarType) :
    ∀ τ, (D.ctxAt Γ₀ τ).Le ((D.addBirth σ r T).ctxAt Γ₀ τ)
  | [] => by
      simp only [ctxAt]
      rw [birthsAt_addBirth, opensAt_addBirth]
      split
      · have h0 := (hf.at []).root
        simp only [ctxAt] at h0
        exact Ctx.Le.optInsK (Ctx.le_insert (Ctx.none_of_le (Ctx.le_optInsK _ _) h0) T) _
      · exact Ctx.Le.refl _
  | k :: τ => by
      simp only [ctxAt]
      have hv : (D.view (k :: τ) (D.ctxAt Γ₀ τ)).Le
          ((D.addBirth σ r T).view (k :: τ) ((D.addBirth σ r T).ctxAt Γ₀ τ)) :=
        view_le (D := D) (ctxAt_addBirth hf σ T τ)
      rw [birthsAt_addBirth, opensAt_addBirth]
      split
      · rename_i he
        have hoff : ¬ σ <:+ τ := fun h' => by
          have := h'.length_le
          rw [← he] at this
          simp at this
        refine Ctx.Le.optInsK ((Ctx.Le.inserts hv _).trans (Ctx.le_insert ?_ T)) _
        rw [ctxAt_addBirth_off τ hoff]
        have h0 := (hf.at (k :: τ)).root
        simp only [ctxAt] at h0
        exact Ctx.none_of_le (Ctx.le_optInsK _ _) h0
      · exact Ctx.Le.optInsK (Ctx.Le.inserts hv _) _

/-- ⭐The node of a new birth: its context is the old one with the birth (the birth commutes with
    the node's openings, `Ctx.insert_optInsK_le`). -/
theorem insert_le_addBirth {Γ₀ : Ctx} {u : ℕ} (hf : D.Fresh Γ₀ (.free u)) (τ : Lab)
    (T : VarType) : ((D.ctxAt Γ₀ τ).insert (.free u) T).Le
      ((D.addBirth τ (.free u) T).ctxAt Γ₀ τ) := by
  have hfr : (D.preAt Γ₀ τ).RootFresh (.free u) :=
    Ctx.RootFresh.of_le (by rw [D.ctxAt_eq_pre Γ₀ τ]; exact Ctx.le_optInsK _ _) (hf.at τ)
  cases τ with
  | nil =>
      simp only [ctxAt]
      rw [birthsAt_addBirth, if_pos rfl, opensAt_addBirth]
      exact Ctx.insert_optInsK_le hfr T _
  | cons k τ =>
      have hoff : ¬ (k :: τ) <:+ τ := fun h' => by
        have := h'.length_le
        simp at this
      simp only [ctxAt]
      rw [birthsAt_addBirth, if_pos rfl, ctxAt_addBirth_off τ hoff, opensAt_addBirth]
      exact Ctx.insert_optInsK_le hfr T _

/-- ⭐A new `□`-child with no births: its context is the parent's `□` view. -/
theorem boxIn_le_addEdge {Γ₀ : Ctx} {τ : Lab} {k : ℕ} (hc : D.edge (k :: τ) = none)
    (hb : D.birthsAt (k :: τ) = []) (ho : D.opensAt (k :: τ) = []) :
    (D.ctxAt Γ₀ τ).boxIn.Le ((D.addEdge (k :: τ) .box).ctxAt Γ₀ (k :: τ)) := by
  simp only [ctxAt]
  have hb' : (D.addEdge (k :: τ) .box).birthsAt (k :: τ) = [] := hb
  have ho' : (D.addEdge (k :: τ) .box).opensAt (k :: τ) = [] := ho
  rw [hb', ho']
  unfold view
  rw [edge_addEdge, if_pos rfl]
  exact (ctxAt_addEdge hc .box τ).boxIn

/-- ⭐A new `◇_x`-child with no births: its context is the parent's `◇_x` view. -/
theorem diaIn_le_addEdge {Γ₀ : Ctx} {τ : Lab} {k : ℕ} (hc : D.edge (k :: τ) = none)
    (hb : D.birthsAt (k :: τ) = []) (ho : D.opensAt (k :: τ) = []) (x : VarSymb) :
    ((D.ctxAt Γ₀ τ).diaIn x).Le ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ (k :: τ)) := by
  simp only [ctxAt]
  have hb' : (D.addEdge (k :: τ) (.dia x)).birthsAt (k :: τ) = [] := hb
  have ho' : (D.addEdge (k :: τ) (.dia x)).opensAt (k :: τ) = [] := ho
  rw [hb', ho']
  unfold view
  rw [edge_addEdge, if_pos rfl]
  exact (ctxAt_addEdge hc (.dia x) τ).diaIn x

/-- An opening off a node's branch leaves its context alone. -/
theorem ctxAt_addOpen_off {Γ₀ : Ctx} {σ : Lab} {κ : WitKind} {y : VarSymb} :
    ∀ τ, ¬ σ <:+ τ → (D.addOpen σ κ y).ctxAt Γ₀ τ = D.ctxAt Γ₀ τ
  | [], h => by
      simp only [ctxAt]
      rw [opensAt_addOpen, if_neg (fun he => h (by subst he; exact List.suffix_refl _))]
      rfl
  | k :: τ, h => by
      simp only [ctxAt]
      rw [ctxAt_addOpen_off τ (fun h' => h (h'.trans (List.suffix_cons k τ))),
        opensAt_addOpen, if_neg (fun he => h (by subst he; exact List.suffix_refl _))]
      rfl

/-- ⭐The node of a new opening: its context is the old one opened. -/
theorem ctxAt_addOpen_self {Γ₀ : Ctx} (τ : Lab) (κ : WitKind) (y : VarSymb) :
    (D.addOpen τ κ y).ctxAt Γ₀ τ = (D.ctxAt Γ₀ τ).optInK κ y := by
  cases τ with
  | nil =>
      simp only [ctxAt]
      rw [opensAt_addOpen, if_pos rfl]
      rfl
  | cons k τ =>
      have hoff : ¬ (k :: τ) <:+ τ := fun h' => by
        have := h'.length_le
        simp at this
      simp only [ctxAt]
      rw [ctxAt_addOpen_off τ hoff, opensAt_addOpen, if_pos rfl]
      rfl

/-- ⭐**A new opening weakens every node's context.** -/
theorem ctxAt_addOpen {Γ₀ : Ctx} (σ : Lab) (κ : WitKind) (y : VarSymb) :
    ∀ τ, (D.ctxAt Γ₀ τ).Le ((D.addOpen σ κ y).ctxAt Γ₀ τ)
  | [] => by
      simp only [ctxAt]
      rw [opensAt_addOpen]
      split
      · exact Ctx.le_optInK _ κ y
      · exact Ctx.Le.refl _
  | k :: τ => by
      have ih := ctxAt_addOpen (Γ₀ := Γ₀) σ κ y τ
      have hv : ((D.view (k :: τ) (D.ctxAt Γ₀ τ)).inserts (D.birthsAt (k :: τ))).Le
          (((D.addOpen σ κ y).view (k :: τ) ((D.addOpen σ κ y).ctxAt Γ₀ τ)).inserts
            ((D.addOpen σ κ y).birthsAt (k :: τ))) :=
        Ctx.Le.inserts (view_le (D := D) ih) _
      simp only [ctxAt]
      rw [opensAt_addOpen]
      split
      · exact (Ctx.Le.optInsK hv _).trans (Ctx.le_optInK _ κ y)
      · exact Ctx.Le.optInsK hv _

theorem view_le_addEdge {c : Lab} (hc : D.edge c = none) (e : EdgeKind) (σ' : Lab) (Γ : Ctx) :
    (D.view σ' Γ).Le ((D.addEdge c e).view σ' Γ) := by
  unfold view
  rw [edge_addEdge]
  by_cases hk : σ' = c
  · subst hk
    simp only [hc]
    cases e with
    | box => exact Ctx.Le.refl _
    | dia x => exact Ctx.le_boxIn_diaIn _ x
  · simp only [if_neg hk]
    exact Ctx.Le.refl _

theorem preAt_addEdge {Γ₀ : Ctx} {c : Lab} (hc : D.edge c = none) (e : EdgeKind) :
    ∀ τ, (D.preAt Γ₀ τ).Le ((D.addEdge c e).preAt Γ₀ τ)
  | [] => Ctx.Le.refl _
  | _ :: τ => Ctx.Le.inserts ((view_le (ctxAt_addEdge hc e τ)).trans (view_le_addEdge hc e _ _)) _

theorem preAt_addBirth {Γ₀ : Ctx} {r : Root} (hf : D.Fresh Γ₀ r) (σ : Lab) (T : VarType) :
    ∀ τ, (D.preAt Γ₀ τ).Le ((D.addBirth σ r T).preAt Γ₀ τ)
  | [] => by
      simp only [preAt]
      rw [birthsAt_addBirth]
      split
      · have h0 := (hf.at []).root
        simp only [ctxAt] at h0
        exact Ctx.le_insert (Ctx.none_of_le (Ctx.le_optInsK _ _) h0) T
      · exact Ctx.Le.refl _
  | k :: τ => by
      simp only [preAt]
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
        exact Ctx.none_of_le (Ctx.le_optInsK _ _) h0
      · exact Ctx.Le.inserts hv _

theorem preAt_addOpen {Γ₀ : Ctx} (σ : Lab) (κ : WitKind) (y : VarSymb) :
    ∀ τ, (D.preAt Γ₀ τ).Le ((D.addOpen σ κ y).preAt Γ₀ τ)
  | [] => Ctx.Le.refl _
  | _ :: τ => Ctx.Le.inserts (view_le (ctxAt_addOpen σ κ y τ)) _

theorem preAt_addOpen_self {Γ₀ : Ctx} (τ : Lab) (κ : WitKind) (y : VarSymb) :
    (D.addOpen τ κ y).preAt Γ₀ τ = D.preAt Γ₀ τ := by
  cases τ with
  | nil => rfl
  | cons k τ =>
      have hoff : ¬ (k :: τ) <:+ τ := fun h' => by
        have := h'.length_le
        simp at this
      simp only [preAt]
      rw [ctxAt_addOpen_off τ hoff]
      rfl

/-! ## The tree invariant -/

/-- ⭐**The tree invariant**: no birth twice, at most one birth per name, every name fresh for
    the end sequent's context; and every opening took effect (`optL` opens a witness). -/
structure OK (Γ₀ : Ctx) (D : Tree) : Prop where
  nodup : D.births.Nodup
  uniq : ∀ b ∈ D.births, ∀ b' ∈ D.births, b.2.1 = b'.2.1 → b = b'
  fresh : ∀ b ∈ D.births, Γ₀.RootFresh b.2.1
  free : ∀ b ∈ D.births, ∃ u, b.2.1 = .free u
  eff : ∀ τ, (D.preAt Γ₀ τ).OptsEff (D.opensAt τ)

/-- Every opening is opened at its node. -/
theorem OK.opened {Γ₀ : Ctx} (h : D.OK Γ₀) (τ : Lab) :
    ∀ o ∈ D.opensAt τ, (D.ctxAt Γ₀ τ).Opened o.1 o.2 := by
  rw [ctxAt_eq_pre]
  exact Ctx.opened_of_eff (h.eff τ)

theorem OK.addEdge {Γ₀ : Ctx} (h : D.OK Γ₀) {c : Lab} (hc : D.edge c = none) (e : EdgeKind) :
    (D.addEdge c e).OK Γ₀ :=
  ⟨h.nodup, h.uniq, h.fresh, h.free, fun τ => (h.eff τ).mono (preAt_addEdge hc e τ)⟩

theorem OK.addOpen {Γ₀ : Ctx} (h : D.OK Γ₀) (hO : ModalSys.Opt = true) {τ : Lab} {κ : WitKind}
    {y : VarSymb} {X : VarType} (hy : (D.ctxAt Γ₀ τ).witK κ y = some X) :
    (D.addOpen τ κ y).OK Γ₀ := by
  refine ⟨h.nodup, h.uniq, h.fresh, h.free, fun σ => ?_⟩
  rw [opensAt_addOpen]
  split_ifs with hσ
  · subst hσ
    rw [preAt_addOpen_self]
    refine ⟨h.eff σ, hO, X, ?_⟩
    rw [← ctxAt_eq_pre]
    exact hy
  · exact (h.eff σ).mono (preAt_addOpen _ κ y σ)

theorem OK.addBirth {Γ₀ : Ctx} (h : D.OK Γ₀) {u : ℕ} (hf : D.Fresh Γ₀ (.free u)) (τ : Lab)
    (T : VarType) : (D.addBirth τ (.free u) T).OK Γ₀ := by
  refine ⟨List.nodup_cons.mpr ⟨fun hm => hf.births _ hm rfl, h.nodup⟩, ?_, ?_, ?_,
    fun σ => (h.eff σ).mono (preAt_addBirth hf τ T σ)⟩
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
      exact (h0.inserts _ fun b hm => hb _ (mem_birthsAt.mp hm) (List.suffix_refl _)).optInsK _
  | k :: τ, hb => by
      have ih := fresh_branch h0 τ fun b hm hs => hb b hm (hs.trans (List.suffix_cons k τ))
      simp only [ctxAt]
      refine (Ctx.RootFresh.inserts ?_ _ fun b hm =>
        hb _ (mem_birthsAt.mp hm) (List.suffix_refl _)).optInsK _
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

/-- A child's context before its openings contains its edge's view of the parent's, under the
    invariant: the child's births are fresh there. -/
theorem view_le_preAt {Γ₀ : Ctx} (h : D.OK Γ₀) (k : ℕ) (τ : Lab) :
    (D.view (k :: τ) (D.ctxAt Γ₀ τ)).Le (D.preAt Γ₀ (k :: τ)) := by
  simp only [preAt]
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

/-- ⭐**A child's context contains its edge's view of the parent's**, under the invariant: the
    child's births are fresh there. -/
theorem view_le_ctxAt {Γ₀ : Ctx} (h : D.OK Γ₀) (k : ℕ) (τ : Lab) :
    (D.view (k :: τ) (D.ctxAt Γ₀ τ)).Le (D.ctxAt Γ₀ (k :: τ)) := by
  simp only [ctxAt]
  refine (Ctx.le_inserts _ (birthsAt_pairwise h _) fun b hm => ?_).trans (Ctx.le_optInsK _ _)
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
      exact (h0.inserts _ fun b hb => h.free _ (mem_birthsAt.mp hb)).optInsK _
  | k :: τ => by
      simp only [ctxAt]
      refine (Ctx.SlotsFrom.inserts ?_ _ fun b hb => h.free _ (mem_birthsAt.mp hb)).optInsK _
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
      exact Ctx.le_optInsK _ _ _ _ (Ctx.inserts_root (birthsAt_pairwise h _) hb)
  | cons k τ =>
      simp only [ctxAt]
      exact Ctx.le_optInsK _ _ _ _ (Ctx.inserts_root (birthsAt_pairwise h _) hb)

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

theorem _root_.V12M.Ctx.inserts_wit (Γ : Ctx) :
    ∀ L : List (Root × VarType), (Γ.inserts L).wit = Γ.wit
  | [] => rfl
  | _ :: L => Ctx.inserts_wit Γ L

/-- A node's witnesses are its edge's view's: births and openings keep them. -/
theorem ctxAt_wit {Γ₀ : Ctx} (D : Tree) (k : ℕ) (τ : Lab) :
    (D.ctxAt Γ₀ (k :: τ)).wit = (D.view (k :: τ) (D.ctxAt Γ₀ τ)).wit := by
  simp only [ctxAt]
  rw [Ctx.optInsK_wit, Ctx.inserts_wit]

theorem _root_.V12M.Ctx.optInsK_le_of {Ξ : Ctx} :
    ∀ (L : List (WitKind × VarSymb)) {Γ : Ctx}, Γ.Le Ξ → (∀ o ∈ L, Ξ.Opened o.1 o.2) →
      (Γ.optInsK L).Le Ξ
  | [], _, h, _ => h
  | o :: L, _, h, ho => Ctx.optInK_le_of
      (Ctx.optInsK_le_of L h fun o' h' => ho o' (List.mem_cons_of_mem _ h'))
      (ho o List.mem_cons_self)

/-- An edge's image **fits**: of a compatible kind, or (a `◇_x`-edge) onto a node where `x` is
    opened, whose context holds the `◇_x` view (`Ctx.le_diaIn_boxIn_optIn`; docs §12.50). -/
def _root_.V12M.GKN.EdgeKind.Fits (Ξ : Ctx) (e e' : EdgeKind) : Prop :=
  e.Compat e' ∨ ∃ x, e = .dia x ∧ Ξ.Opened .arrow x

theorem _root_.V12M.GKN.EdgeKind.Fits.of_compat {Ξ : Ctx} {e e' : EdgeKind} (h : e.Compat e') :
    e.Fits Ξ e' :=
  Or.inl h

theorem _root_.V12M.GKN.EdgeKind.Fits.mono {Ξ Ξ' : Ctx} (h : Ξ.Le Ξ') {e e' : EdgeKind} :
    e.Fits Ξ e' → e.Fits Ξ' e'
  | .inl hc => .inl hc
  | .inr ⟨x, hx, ho⟩ => .inr ⟨x, hx, ho.mono h⟩

/-- ⭐A view inside the image node's context, the edges fitting there. -/
theorem view_le_of {D D' : Tree} {σ σ' : Lab} {Γ Γ' Ξ : Ctx} (h : Γ.Le Γ')
    (hΞ : (D'.view σ' Γ').Le Ξ) (hw : Ξ.wit = (D'.view σ' Γ').wit)
    (he : ∀ e, D.edge σ = some e → ∃ e', D'.edge σ' = some e' ∧ e.Fits Ξ e') :
    (D.view σ Γ).Le Ξ := by
  cases hD : D.edge σ with
  | none => rw [view_box (Or.inl hD)]; exact h.boxIn.trans ((boxIn_le_view _ _).trans hΞ)
  | some e =>
      obtain ⟨e', he', hc⟩ := he _ hD
      rcases hc with hc | ⟨x, rfl, ho⟩
      · exact (view_le_view h fun e₀ h₀ => by
          rw [hD] at h₀
          cases h₀
          exact ⟨e', he', hc⟩).trans hΞ
      · obtain ⟨X, hX, -⟩ := id ho
        have hX' : (D'.view σ' Γ').wit x = some X := by rw [← hw]; exact hX
        have hb : Γ'.boxIn.wit x = some X := by
          unfold view at hX'
          split at hX' <;> exact hX'
        obtain ⟨hO, hr⟩ := Ctx.boxIn_wit.mp hb
        rw [view_dia hD]
        exact (h.diaIn x).trans ((Ctx.le_diaIn_boxIn_optIn hO hr).trans
          (Ctx.optInK_le_of (κ := .arrow) ((boxIn_le_view _ _).trans hΞ) ho))

/-- ⭐**A relabelling that keeps edges (fitting) and births, and whose images open what the
    nodes open, weakens every node's context into its image's**, given the invariant at the
    target. -/
theorem ctx_le_of_map {Γ₀ : Ctx} {D D' : Tree} (g : Lab → ℕ → ℕ) (hok : D'.OK Γ₀)
    (hedge : ∀ c e, D.edge c = some e →
      ∃ e', D'.edge (lmap g c) = some e' ∧ e.Fits (D'.ctxAt Γ₀ (lmap g c)) e')
    (hbirth : ∀ τ b, b ∈ D.birthsAt τ → b ∈ D'.birthsAt (lmap g τ))
    (hopen : ∀ τ, ∀ o ∈ D.opensAt τ, (D'.ctxAt Γ₀ (lmap g τ)).Opened o.1 o.2) :
    ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ (lmap g τ))
  | [] => by
      have hΞ : Γ₀.Le (D'.ctxAt Γ₀ (lmap g [])) := by
        simp only [lmap, ctxAt]
        exact (Ctx.le_inserts _ (birthsAt_pairwise hok _)
          fun b hb => hok.fresh _ (mem_birthsAt.mp hb)).trans (Ctx.le_optInsK _ _)
      simp only [ctxAt]
      exact Ctx.optInsK_le_of _
        (Ctx.inserts_le_of _ hΞ fun b hb => ctxAt_root hok (hbirth [] b hb)) (hopen [])
  | j :: ν => by
      have ih := ctx_le_of_map g hok hedge hbirth hopen ν
      have hv : (D.view (j :: ν) (D.ctxAt Γ₀ ν)).Le (D'.ctxAt Γ₀ (lmap g (j :: ν))) :=
        view_le_of ih (view_le_ctxAt hok (g ν j) (lmap g ν)) (ctxAt_wit D' (g ν j) (lmap g ν))
          (hedge (j :: ν))
      simp only [ctxAt]
      exact Ctx.optInsK_le_of _
        (Ctx.inserts_le_of _ hv fun b hb => ctxAt_root hok (hbirth (j :: ν) b hb))
        (hopen (j :: ν))

/-- ⭐The inclusion `diaR` takes, at a child the `◇_x` view fits. -/
theorem diaIn_le_fit {Γ₀ : Ctx} {D : Tree} (h : D.OK Γ₀) {k : ℕ} {τ : Lab} {x : VarSymb}
    {e : EdgeKind} (he : D.edge (k :: τ) = some e)
    (hf : (EdgeKind.dia x).Fits (D.ctxAt Γ₀ (k :: τ)) e) :
    ((D.ctxAt Γ₀ τ).diaIn x).Le (D.ctxAt Γ₀ (k :: τ)) := by
  have hv : (Tree.view {edges := [((k :: τ), .dia x)]} (k :: τ) (D.ctxAt Γ₀ τ)) =
      (D.ctxAt Γ₀ τ).diaIn x := by
    unfold view edge
    simp
  rw [← hv]
  refine view_le_of (Ctx.Le.refl _) (view_le_ctxAt h k τ) (ctxAt_wit D k τ) fun e₀ h₀ => ?_
  have : e₀ = .dia x := by
    unfold edge at h₀
    simpa using h₀.symm
  subst this
  exact ⟨e, he, hf⟩

end Tree

end GKN

end V12M
