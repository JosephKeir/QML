import QML.QML_v12m_GKN

/-!
# QML v12m — `GKN`: relabelling and weakening

The first-order form of the prototype's `Der.subst` (docs §12.49): derivations are closed under
**relabelling** the tree by a child-index map (`lmap g`) that keeps edges (with views as large:
`EdgeKind.Fits`, a `◇_x`-edge possibly onto a node where `x` is opened), births and openings (an
image opens what its node opens, `Ctx.Opened`: a semantic condition), onto a target tree
satisfying the invariant, and under **weakening** of both sides.
Each new child of the derivation gets a fresh index in the target (`exists_vacant`), so the map
is updated there.

* `GKN.TMap g D D'`: the conditions, and `TMap.le`, the node-wise inclusion they give
  (`Tree.ctx_le_of_map`).
* ⭐`GKN.relabel`: relabelling and weakening at once.
* ⭐`GKN.weaken`: weakening (the identity relabelling).
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace GKN

variable {σ : Signature}

/-! ## Formulas at nodes -/

theorem LF.mono_eq {Γ₀ : Ctx} {D : Tree} {A : Ctx} (φ : WFF σ A 0) {τ τ' : Lab} (e : τ = τ')
    (h : A.Le (D.ctxAt Γ₀ τ)) (h' : A.Le (D.ctxAt Γ₀ τ')) :
    (⟨τ, WFF.mono h φ⟩ : LF σ Γ₀ D) = ⟨τ', WFF.mono h' φ⟩ := by
  subst e
  rfl

theorem LF.mono_mono_eq {Γ₀ : Ctx} {D : Tree} {A B C : Ctx} (φ : WFF σ A 0) {τ τ' : Lab}
    (e : τ = τ') (b : A.Le B) (a : B.Le (D.ctxAt Γ₀ τ)) (d : A.Le C) (c : C.Le (D.ctxAt Γ₀ τ')) :
    (⟨τ, WFF.mono a (WFF.mono b φ)⟩ : LF σ Γ₀ D) = ⟨τ', WFF.mono c (WFF.mono d φ)⟩ := by
  rw [WFF.mono_mono, WFF.mono_mono]
  exact LF.mono_eq φ e _ _

theorem cons_sub {α : Type*} {a a' : α} {L L' : List α} (e : a = a') (h : L ⊆ L') :
    a :: L ⊆ a' :: L' := by
  subst e
  exact List.cons_subset_cons _ h

theorem isAtom_mono {Γ Γ' : Ctx} {d : ℕ} {h : Γ.Le Γ'} {P : WFF σ Γ d} (hP : P.IsAtom) :
    (WFF.mono h P).IsAtom := by
  cases P <;> trivial

/-! ## Relabelling a side -/

/-- A side relabelled. -/
def Seq.relabel {Γ₀ : Ctx} {D D' : Tree} (g : Lab → ℕ → ℕ)
    (h : ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ (lmap g τ))) (L : Seq σ Γ₀ D) : Seq σ Γ₀ D' :=
  L.map fun p => ⟨lmap g p.1, WFF.mono (h p.1) p.2⟩

theorem mem_relabel {Γ₀ : Ctx} {D D' : Tree} {g : Lab → ℕ → ℕ}
    {h : ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ (lmap g τ))} {L : Seq σ Γ₀ D} {p : LF σ Γ₀ D}
    (hp : p ∈ L) : (⟨lmap g p.1, WFF.mono (h p.1) p.2⟩ : LF σ Γ₀ D') ∈ Seq.relabel g h L :=
  List.mem_map_of_mem hp

/-- ⭐Relabelling a weakened side, when the map agrees on its nodes. -/
theorem relabel_mono_sub {Γ₀ : Ctx} {D D₁ D' D'₁ : Tree} {g g₁ : Lab → ℕ → ℕ}
    {h : ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ (lmap g τ))}
    {h₁ : ∀ τ, (D₁.ctxAt Γ₀ τ).Le (D'₁.ctxAt Γ₀ (lmap g₁ τ))}
    {k : ∀ τ, (D.ctxAt Γ₀ τ).Le (D₁.ctxAt Γ₀ τ)} {k' : ∀ τ, (D'.ctxAt Γ₀ τ).Le (D'₁.ctxAt Γ₀ τ)}
    {L : Seq σ Γ₀ D} {L' : Seq σ Γ₀ D'} (hL : Seq.relabel g h L ⊆ L')
    (hl : ∀ p ∈ L, lmap g₁ p.1 = lmap g p.1) :
    Seq.relabel g₁ h₁ (Seq.mono k L) ⊆ Seq.mono k' L' := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hm : (⟨lmap g p.1, WFF.mono (h p.1) p.2⟩ : LF σ Γ₀ D') ∈ L' := hL (mem_relabel hp)
  have := List.mem_map_of_mem (f := fun p : LF σ Γ₀ D' => (⟨p.1, WFF.mono (k' p.1) p.2⟩ :
    LF σ Γ₀ D'₁)) hm
  refine (congrArg (· ∈ Seq.mono k' L') ?_).mpr this
  exact LF.mono_mono_eq p.2 (hl p hp) _ _ _ _

/-! ## Fresh child indices -/

/-- Every node has a vacant child. -/
theorem exists_vacant {Γ₀ : Ctx} (τ : Lab) (D : Tree) (Δ Θ : Seq σ Γ₀ D) :
    ∃ k, Vacant D (k :: τ) Δ Θ := by
  set labels : List Lab := D.edges.map Prod.fst ++ D.births.map Prod.fst ++ Δ.map Sigma.fst ++
    Θ.map Sigma.fst ++ D.opens.map Prod.fst
  set N := (labels.map List.sum).sum
  have key : ∀ ℓ ∈ labels, ¬ ((N + 1) :: τ) <:+ ℓ := by
    intro ℓ hℓ hs
    have h₁ : N + 1 ∈ ℓ := hs.subset List.mem_cons_self
    have h₂ : N + 1 ≤ ℓ.sum := List.le_sum_of_mem h₁
    have h₃ : ℓ.sum ≤ N := List.le_sum_of_mem (List.mem_map_of_mem hℓ)
    omega
  refine ⟨N + 1, ⟨fun τ' hs => ?_, fun b hb hs => ?_, fun o ho hs => ?_, fun p hp hs => ?_,
    fun p hp hs => ?_⟩⟩
  · cases he : D.edge τ' with
    | none => rfl
    | some e =>
        exfalso
        unfold Tree.edge at he
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp he
        have hxm := List.mem_of_find?_eq_some hx
        have hx1 : x.1 = τ' := by
          have := List.find?_some hx
          simpa using this
        exact key x.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map_of_mem hxm))))) (hx1 ▸ hs)
  · exact key b.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map_of_mem hb))))) hs
  · exact key o.1 (List.mem_append_right _ (List.mem_map_of_mem ho)) hs
  · exact key p.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem hp)))) hs
  · exact key p.1 (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hp))) hs

/-! ## The relabelling conditions -/

/-- `g` sends the child `k` of `τ` to `k'`, elsewhere as before. -/
def setIdx (g : Lab → ℕ → ℕ) (τ : Lab) (k k' : ℕ) : Lab → ℕ → ℕ :=
  fun ν j => if ν = τ ∧ j = k then k' else g ν j

theorem lmap_setIdx_off (g : Lab → ℕ → ℕ) {τ : Lab} {k k' : ℕ} :
    ∀ σ, ¬ (k :: τ) <:+ σ → lmap (setIdx g τ k k') σ = lmap g σ
  | [], _ => rfl
  | j :: ν, h => by
      have hν : ¬ (k :: τ) <:+ ν := fun h' => h (h'.trans (List.suffix_cons j ν))
      have hne : ¬ (ν = τ ∧ j = k) := fun ⟨h₁, h₂⟩ => h (by subst h₁ h₂; exact List.suffix_refl _)
      change setIdx g τ k k' ν j :: lmap (setIdx g τ k k') ν = g ν j :: lmap g ν
      rw [lmap_setIdx_off g ν hν]
      unfold setIdx
      rw [if_neg hne]

theorem lmap_setIdx_new (g : Lab → ℕ → ℕ) (τ : Lab) (k k' : ℕ) :
    lmap (setIdx g τ k k') (k :: τ) = k' :: lmap g τ := by
  change setIdx g τ k k' τ k :: lmap (setIdx g τ k k') τ = _
  rw [lmap_setIdx_off g τ (fun h' => by have := h'.length_le; simp at this)]
  unfold setIdx
  rw [if_pos ⟨rfl, rfl⟩]

/-- ⭐**The relabelling conditions**: the target satisfies the invariant, edges go to edges with
    views as large (`EdgeKind.Fits`), births to births, an image opens what its node opens, and
    the target's names are the source's. -/
structure TMap (Γ₀ : Ctx) (g : Lab → ℕ → ℕ) (D D' : Tree) : Prop where
  ok : D'.OK Γ₀
  edge : ∀ c e, D.edge c = some e →
    ∃ e', D'.edge (lmap g c) = some e' ∧ e.Fits (D'.ctxAt Γ₀ (lmap g c)) e'
  birth : ∀ τ b, b ∈ D.birthsAt τ → b ∈ D'.birthsAt (lmap g τ)
  opens : ∀ τ, ∀ o ∈ D.opensAt τ, (D'.ctxAt Γ₀ (lmap g τ)).Opened o.1 o.2
  names : ∀ b ∈ D'.births, ∃ b₀ ∈ D.births, b₀.2.1 = b.2.1

theorem TMap.le {Γ₀ : Ctx} {g : Lab → ℕ → ℕ} {D D' : Tree} (hm : TMap Γ₀ g D D') :
    ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ (lmap g τ)) :=
  Tree.ctx_le_of_map g hm.ok hm.edge hm.birth hm.opens

theorem TMap.fresh {Γ₀ : Ctx} {g : Lab → ℕ → ℕ} {D D' : Tree} (hm : TMap Γ₀ g D D') {r : Root}
    (hr : D.Fresh Γ₀ r) : D'.Fresh Γ₀ r :=
  ⟨hr.ctx, fun b hb he => by
    obtain ⟨b₀, hb₀, he₀⟩ := hm.names b hb
    exact hr.births b₀ hb₀ (he₀.trans he)⟩

/-- A birth on both sides. -/
theorem TMap.addBirth {Γ₀ : Ctx} {g : Lab → ℕ → ℕ} {D D' : Tree} (hm : TMap Γ₀ g D D')
    {u : ℕ} (hu : D.Fresh Γ₀ (.free u)) (τ : Lab) (T : VarType) :
    TMap Γ₀ g (D.addBirth τ (.free u) T) (D'.addBirth (lmap g τ) (.free u) T) := by
  have hk := Tree.ctxAt_addBirth (Γ₀ := Γ₀) (hm.fresh hu) (lmap g τ) T
  refine ⟨hm.ok.addBirth (hm.fresh hu) _ T, fun c e he => ?_, fun σ b hb => ?_,
    fun σ o ho => (hm.opens σ o ho).mono (hk _), fun b hb => ?_⟩
  · obtain ⟨e', he', hf⟩ := hm.edge c e he
    exact ⟨e', he', hf.mono (hk _)⟩
  · rw [Tree.birthsAt_addBirth] at hb ⊢
    split_ifs at hb with hσ
    · subst hσ
      rw [if_pos rfl]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hm.birth _ b hb)
    · have := hm.birth σ b hb
      split_ifs
      · exact List.mem_cons_of_mem _ this
      · exact this
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨(τ, .free u, T), List.mem_cons_self, rfl⟩
    · obtain ⟨b₀, hb₀, he⟩ := hm.names b hb
      exact ⟨b₀, List.mem_cons_of_mem _ hb₀, he⟩

/-- A new child on both sides: the source's vacant, the target's fresh. -/
theorem TMap.addEdge {Γ₀ : Ctx} {g : Lab → ℕ → ℕ} {D D' : Tree} (hm : TMap Γ₀ g D D')
    {τ : Lab} {k k' : ℕ} {Δ Θ : Seq σ Γ₀ D} {Δ' Θ' : Seq σ Γ₀ D'} (hv : Vacant D (k :: τ) Δ Θ)
    (hv' : Vacant D' (k' :: lmap g τ) Δ' Θ') (e : EdgeKind) :
    TMap Γ₀ (setIdx g τ k k') (D.addEdge (k :: τ) e) (D'.addEdge (k' :: lmap g τ) e) := by
  have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) (hv'.edge _ (List.suffix_refl _)) e
  refine ⟨hm.ok.addEdge (hv'.edge _ (List.suffix_refl _)) _, fun c e₁ hc => ?_,
    fun σ b hb => ?_, fun σ o ho => ?_, hm.names⟩
  · rw [Tree.edge_addEdge] at hc
    split_ifs at hc with hck
    · cases hc
      subst hck
      refine ⟨e, ?_, ?_⟩
      · rw [lmap_setIdx_new, Tree.edge_addEdge, if_pos rfl]
      · exact .of_compat (by cases e <;> simp [EdgeKind.Compat])
    · have hoff : ¬ (k :: τ) <:+ c := fun hs => by
        rw [hv.edge c hs] at hc
        cases hc
      obtain ⟨e', he', hc'⟩ := hm.edge c e₁ hc
      refine ⟨e', ?_, ?_⟩
      · rw [lmap_setIdx_off g c hoff, Tree.edge_addEdge, if_neg]
        · exact he'
        · intro heq
          rw [heq, hv'.edge _ (List.suffix_refl _)] at he'
          cases he'
      · rw [lmap_setIdx_off g c hoff]
        exact hc'.mono (hk _)
  · have hb' := Tree.mem_birthsAt.mp hb
    have hoff : ¬ (k :: τ) <:+ σ := hv.births _ hb'
    rw [lmap_setIdx_off g σ hoff]
    exact hm.birth σ b hb
  · rw [lmap_setIdx_off g σ (hv.not_opensAt ho)]
    exact (hm.opens σ o ho).mono (hk _)

/-- ⭐**A new opening on both sides**: the source's at a witness, so the image's is too. -/
theorem TMap.addOpen {Γ₀ : Ctx} {g : Lab → ℕ → ℕ} {D D' : Tree} (hm : TMap Γ₀ g D D')
    (hO : ModalSys.Opt = true) {τ : Lab} {κ : WitKind} {y : VarSymb} {X : VarType}
    (hy : (D.ctxAt Γ₀ τ).witK κ y = some X) :
    TMap Γ₀ g (D.addOpen τ κ y) (D'.addOpen (lmap g τ) κ y) := by
  have hk := Tree.ctxAt_addOpen (D := D') (Γ₀ := Γ₀) (lmap g τ) κ y
  refine ⟨hm.ok.addOpen hO ((hm.le τ).witK hy), fun c e he => ?_, hm.birth, fun σ o ho => ?_,
    hm.names⟩
  · obtain ⟨e', he', hf⟩ := hm.edge c e he
    exact ⟨e', he', hf.mono (hk _)⟩
  · rw [Tree.opensAt_addOpen] at ho
    split_ifs at ho with hσ
    · subst hσ
      rcases List.mem_cons.mp ho with rfl | ho
      · rw [Tree.ctxAt_addOpen_self]
        exact Ctx.opened_self ((hm.le _).witK hy)
      · exact (hm.opens _ o ho).mono (hk _)
    · exact (hm.opens σ o ho).mono (hk _)

end GKN

open GKN

/-! ## Relabelling -/

/-- ⭐**Relabelling and weakening**: a derivation over a tree gives one over any tree it maps to
    (`TMap`), with both sides relabelled and enlarged. -/
theorem GKN.relabel {n : ℕ} {Γ₀ : Ctx} (hs0 : Γ₀.SlotsFrom 0) {D : Tree} {Δ Θ : Seq σ Γ₀ D}
    (p : GKN σ Γ₀ n D Δ Θ) :
    ∀ (g : Lab → ℕ → ℕ) (D' : Tree) (hm : TMap Γ₀ g D D') (Δ' Θ' : Seq σ Γ₀ D'),
      Seq.relabel g hm.le Δ ⊆ Δ' → Seq.relabel g hm.le Θ ⊆ Θ' → GKN σ Γ₀ n D' Δ' Θ' := by
  induction p with
  | ax τ P hP h₁ h₂ =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .ax (lmap g τ) _ (isAtom_mono hP) (hΔ (mem_relabel h₁)) (hΘ (mem_relabel h₂))
  | botL τ h =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .botL (lmap g τ) (hΔ (mem_relabel h))
  | topR τ h =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .topR (lmap g τ) (hΘ (mem_relabel h))
  | andL τ h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .andL (lmap g τ) (hΔ (mem_relabel h))
        (ih g D' hm _ _ (List.cons_subset_cons _ (List.cons_subset_cons _ hΔ)) hΘ)
  | andR τ h _ _ ih₁ ih₂ =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .andR (lmap g τ) (hΘ (mem_relabel h))
        (ih₁ g D' hm _ _ hΔ (List.cons_subset_cons _ hΘ))
        (ih₂ g D' hm _ _ hΔ (List.cons_subset_cons _ hΘ))
  | orL τ h _ _ ih₁ ih₂ =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .orL (lmap g τ) (hΔ (mem_relabel h))
        (ih₁ g D' hm _ _ (List.cons_subset_cons _ hΔ) hΘ)
        (ih₂ g D' hm _ _ (List.cons_subset_cons _ hΔ) hΘ)
  | orR τ h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .orR (lmap g τ) (hΘ (mem_relabel h))
        (ih g D' hm _ _ hΔ (List.cons_subset_cons _ (List.cons_subset_cons _ hΘ)))
  | impL τ h _ _ ih₁ ih₂ =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .impL (lmap g τ) (hΔ (mem_relabel h))
        (ih₁ g D' hm _ _ hΔ (List.cons_subset_cons _ hΘ))
        (ih₂ g D' hm _ _ (List.cons_subset_cons _ hΔ) hΘ)
  | impR τ h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .impR (lmap g τ) (hΘ (mem_relabel h))
        (ih g D' hm _ _ (List.cons_subset_cons _ hΔ) (List.cons_subset_cons _ hΘ))
  | allL τ hs T t h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots hs0 hm.ok (lmap g τ)
      refine .allL (lmap g τ) hs' T (Term.mono (hm.le τ) t) (hΔ (mem_relabel h))
        (ih g D' hm _ _ (cons_sub ?_ hΔ) hΘ)
      exact congrArg (Sigma.mk _) (WFF.mono_instantiate (hm.le τ) hs hs' t _)
  | exR τ hs T t h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots hs0 hm.ok (lmap g τ)
      refine .exR (lmap g τ) hs' T (Term.mono (hm.le τ) t) (hΘ (mem_relabel h))
        (ih g D' hm _ _ hΔ (cons_sub ?_ hΘ))
      exact congrArg (Sigma.mk _) (WFF.mono_instantiate (hm.le τ) hs hs' t _)
  | @allR n D Δ Θ τ hs u T hu φ hle h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots hs0 hm.ok (lmap g τ)
      have hu' := hm.fresh hu
      have hm₁ := hm.addBirth hu τ T
      have hp : (⟨lmap g τ, .all T (WFF.bindFree u (hu'.at (lmap g τ)) hs' T
          (WFF.mono ((hm.le τ).insert (.free u) T) φ))⟩ : LF σ Γ₀ D') ∈ Θ' := by
        rw [← WFF.mono_bindFree (hm.le τ) (hu.at τ) (hu'.at _) hs hs' T φ]
        exact hΘ (mem_relabel h)
      refine .allR (lmap g τ) hs' u T hu' (Tree.insert_le_addBirth hu' _ _) hp
        (ih g _ hm₁ _ _ (relabel_mono_sub hΔ fun _ _ => rfl)
          (cons_sub (LF.mono_mono_eq _ rfl _ _ _ _)
            (relabel_mono_sub (h₁ := hm₁.le) hΘ fun _ _ => rfl)))
  | @exL n D Δ Θ τ hs u T hu φ hle h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots hs0 hm.ok (lmap g τ)
      have hu' := hm.fresh hu
      have hm₁ := hm.addBirth hu τ T
      have hp : (⟨lmap g τ, .ex T (WFF.bindFree u (hu'.at (lmap g τ)) hs' T
          (WFF.mono ((hm.le τ).insert (.free u) T) φ))⟩ : LF σ Γ₀ D') ∈ Δ' := by
        rw [← WFF.mono_bindFree (hm.le τ) (hu.at τ) (hu'.at _) hs hs' T φ]
        exact hΔ (mem_relabel h)
      refine .exL (lmap g τ) hs' u T hu' (Tree.insert_le_addBirth hu' _ _) hp
        (ih g _ hm₁ _ _
          (cons_sub (LF.mono_mono_eq _ rfl _ _ _ _)
            (relabel_mono_sub (h₁ := hm₁.le) hΔ fun _ _ => rfl))
          (relabel_mono_sub hΘ fun _ _ => rfl))
  | ref τ t _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      exact .ref (lmap g τ) (Term.mono (hm.le τ) t)
        (ih g D' hm _ _ (List.cons_subset_cons _ hΔ) hΘ)
  | @repl n D Δ Θ τ hs P hP t s h₁ h₂ _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      have hs' := Tree.ctxAt_slots hs0 hm.ok (lmap g τ)
      have hp₂ := hΔ (mem_relabel h₂)
      rw [show (⟨lmap g τ, WFF.mono (hm.le τ) (WFF.instantiate hs t _)⟩ : LF σ Γ₀ D') =
          ⟨lmap g τ, WFF.instantiate hs' (Term.mono (hm.le τ) t)
            (WFF.mono ((hm.le τ).insert (.bnd 0) .Var) _)⟩ from
        congrArg (Sigma.mk _) (WFF.mono_instantiate (hm.le τ) hs hs' t _)] at hp₂
      refine .repl (lmap g τ) hs' (isAtom_mono (h := (hm.le τ).insert (.bnd 0) .Var) hP)
        (Term.mono (hm.le τ) t)
        (Term.mono (hm.le τ) s) (hΔ (mem_relabel h₁)) hp₂ (ih g D' hm _ _ (cons_sub ?_ hΔ) hΘ)
      exact congrArg (Sigma.mk _) (WFF.mono_instantiate (hm.le τ) hs hs' s _)
  | boxR τ k hv hle h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      obtain ⟨k', hv'⟩ := exists_vacant (lmap g τ) D' Δ' Θ'
      have hm₁ := hm.addEdge hv hv' .box
      refine .boxR (lmap g τ) k' hv'
        (Tree.boxIn_le_addEdge (hv'.edge _ (List.suffix_refl _)) hv'.birthsAt hv'.opensAt)
        (hΘ (mem_relabel h)) (ih _ _ hm₁ _ _ ?_ ?_)
      · exact relabel_mono_sub hΔ fun p hp => lmap_setIdx_off g p.1 (hv.left p hp)
      · exact cons_sub (LF.mono_mono_eq _ (lmap_setIdx_new g τ k k') _ _ _ _)
          (relabel_mono_sub (h₁ := hm₁.le) hΘ fun p hp => lmap_setIdx_off g p.1 (hv.right p hp))
  | diaL τ k x hx hv hle h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      obtain ⟨k', hv'⟩ := exists_vacant (lmap g τ) D' Δ' Θ'
      have hm₁ := hm.addEdge hv hv' (.dia x)
      refine .diaL (lmap g τ) k' x _ hv'
        (Tree.diaIn_le_addEdge (hv'.edge _ (List.suffix_refl _)) hv'.birthsAt hv'.opensAt x)
        (hΔ (mem_relabel h)) (ih _ _ hm₁ _ _ ?_ ?_)
      · exact cons_sub (LF.mono_mono_eq _ (lmap_setIdx_new g τ k k') _ _ _ _)
          (relabel_mono_sub (h₁ := hm₁.le) hΔ fun p hp => lmap_setIdx_off g p.1 (hv.left p hp))
      · exact relabel_mono_sub hΘ fun p hp => lmap_setIdx_off g p.1 (hv.right p hp)
  | boxL τ k e he hle h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      obtain ⟨e', he', -⟩ := hm.edge _ e he
      exact .boxL (lmap g τ) (g τ k) e' he' (Tree.boxIn_le_child hm.ok _ _)
        (hΔ (mem_relabel h))
        (ih g D' hm _ _ (cons_sub (LF.mono_mono_eq _ rfl _ _ _ _) hΔ) hΘ)
  | diaR τ k e x hx he hf hle h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      obtain ⟨e', he', hc⟩ := hm.edge _ _ he
      have hf' : (EdgeKind.dia x).Fits (D'.ctxAt Γ₀ (lmap g (k :: τ))) e' := by
        rcases hf with hf | ⟨x', hx', ho⟩
        · cases e with
          | box => exact hf.elim
          | dia z =>
              change x = z at hf
              subst hf
              exact hc
        · cases hx'
          exact .inr ⟨x, rfl, ho.mono (hm.le _)⟩
      exact .diaR (lmap g τ) (g τ k) e' x _ he' hf' (Tree.diaIn_le_fit hm.ok he' hf')
        (hΘ (mem_relabel h))
        (ih g D' hm _ _ hΔ (cons_sub (LF.mono_mono_eq _ rfl _ _ _ _) hΘ))
  | optL hO τ κ y hy hle h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      obtain ⟨X, hX⟩ := id hy
      have hm₁ := hm.addOpen hO hX
      have hy' : ∃ X, (D'.ctxAt Γ₀ (lmap g τ)).witK κ y = some X := ⟨X, (hm.le τ).witK hX⟩
      have hp : (⟨lmap g τ, .optx hO κ y hy' (WFF.mono ((hm.le τ).optInK κ y) _)⟩ :
          LF σ Γ₀ D') ∈ Δ' := hΔ (mem_relabel h)
      refine .optL hO (lmap g τ) κ y hy' (by rw [Tree.ctxAt_addOpen_self]; exact Ctx.Le.refl _)
        hp (ih g _ hm₁ _ _ (cons_sub (LF.mono_mono_eq _ rfl _ _ _ _)
          (relabel_mono_sub (h₁ := hm₁.le) hΔ fun _ _ => rfl))
          (relabel_mono_sub hΘ fun _ _ => rfl))
  | reopenR hO τ κ y hy h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      have hy' := hy.mono (hm.le τ)
      refine .reopenR hO (lmap g τ) κ y hy' ?_ (ih g D' hm _ _ hΔ (List.cons_subset_cons _ hΘ))
      have := hΘ (mem_relabel h)
      refine (congrArg (· ∈ Θ') (congrArg (Sigma.mk _) ?_)).mp this
      change WFF.optx hO κ y _ (WFF.mono ((hm.le τ).optInK κ y) (WFF.mono _ _)) = _
      rw [WFF.mono_mono, WFF.mono_mono]
  | foldR hO τ k e x hx he hle h _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      obtain ⟨e', he', -⟩ := hm.edge _ e he
      refine .foldR hO (lmap g τ) (g τ k) e' x _ he' (Tree.boxIn_le_child hm.ok _ _)
        (hΘ (mem_relabel h)) (ih g D' hm _ _ hΔ (cons_sub ?_ hΘ))
      dsimp only
      rw [WFF.fold_mono hO (hm.le τ) x hx]
      exact LF.mono_mono_eq _ rfl _ _ _ _
  | serial hD τ k hv _ ih =>
      intro g D' hm Δ' Θ' hΔ hΘ
      obtain ⟨k', hv'⟩ := exists_vacant (lmap g τ) D' Δ' Θ'
      have hm₁ := hm.addEdge hv hv' .box
      exact .serial hD (lmap g τ) k' hv'
        (ih _ _ hm₁ _ _ (relabel_mono_sub hΔ fun p hp => lmap_setIdx_off g p.1 (hv.left p hp))
          (relabel_mono_sub hΘ fun p hp => lmap_setIdx_off g p.1 (hv.right p hp)))

/-! ## Weakening -/

namespace GKN

/-- The identity child-index map. -/
def idIdx : Lab → ℕ → ℕ := fun _ j => j

theorem lmap_idIdx : ∀ σ, lmap idIdx σ = σ
  | [] => rfl
  | j :: ν => congrArg (j :: ·) (lmap_idIdx ν)

theorem TMap.id {Γ₀ : Ctx} {D : Tree} (h : D.OK Γ₀) : TMap Γ₀ idIdx D D := by
  refine ⟨h, fun c e he => ⟨e, by rw [lmap_idIdx]; exact he, ?_⟩, fun τ b hb => by
    rw [lmap_idIdx]; exact hb, fun τ o hm => by rw [lmap_idIdx]; exact h.opened τ o hm,
    fun b hb => ⟨b, hb, rfl⟩⟩
  exact .of_compat (by cases e <;> simp [EdgeKind.Compat])

theorem relabel_id_sub {Γ₀ : Ctx} {D : Tree} (h : D.OK Γ₀) {L L' : Seq σ Γ₀ D} (hL : L ⊆ L') :
    Seq.relabel idIdx (TMap.id h).le L ⊆ L' := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have e : (⟨lmap idIdx p.1, WFF.mono ((TMap.id h).le p.1) p.2⟩ : LF σ Γ₀ D) = p := by
    rw [LF.mono_eq p.2 (lmap_idIdx p.1) _ (Ctx.Le.refl _), WFF.mono_refl]
  rw [e]
  exact hL hp

end GKN

open GKN

/-- ⭐**Weakening**: both sides can be enlarged. -/
theorem GKN.weaken {n : ℕ} {Γ₀ : Ctx} (hs0 : Γ₀.SlotsFrom 0) {D : Tree} (h : D.OK Γ₀)
    {Δ Θ Δ' Θ' : Seq σ Γ₀ D} (p : GKN σ Γ₀ n D Δ Θ) (hΔ : Δ ⊆ Δ') (hΘ : Θ ⊆ Θ') :
    GKN σ Γ₀ n D Δ' Θ' :=
  GKN.relabel hs0 p idIdx D (TMap.id h) Δ' Θ' (relabel_id_sub h hΔ) (relabel_id_sub h hΘ)

/-! ## Retargeting a vacant child -/

namespace GKN

/-- ⭐**Retargeting**: a vacant child `k :: τ`, made by a rule, sent onto an existing child
    `k₀ :: τ` of a larger tree whose view fits; everything else stays. -/
theorem TMap.retargetTo {Γ₀ : Ctx} {D D' : Tree} (hm : TMap Γ₀ idIdx D D') {τ : Lab}
    {k k₀ : ℕ} {Δ Θ : Seq σ Γ₀ D} (hv : Vacant D (k :: τ) Δ Θ) {e e' : EdgeKind}
    (hq : D'.edge (k₀ :: τ) = some e') (hc : e.Fits (D'.ctxAt Γ₀ (k₀ :: τ)) e') :
    TMap Γ₀ (setIdx idIdx τ k k₀) (D.addEdge (k :: τ) e) D' := by
  refine ⟨hm.ok, fun c e₁ he₁ => ?_, fun σ b hb => ?_, fun σ o ho => ?_, hm.names⟩
  · rw [Tree.edge_addEdge] at he₁
    split_ifs at he₁ with hck
    · cases he₁
      subst hck
      rw [lmap_setIdx_new, lmap_idIdx]
      exact ⟨e', hq, hc⟩
    · have hoff : ¬ (k :: τ) <:+ c := fun hs => by
        rw [hv.edge c hs] at he₁
        cases he₁
      rw [lmap_setIdx_off idIdx c hoff]
      exact hm.edge c e₁ he₁
  · rw [lmap_setIdx_off idIdx σ (hv.births _ (Tree.mem_birthsAt.mp hb))]
    exact hm.birth σ b hb
  · rw [lmap_setIdx_off idIdx σ (hv.not_opensAt ho)]
    exact hm.opens σ o ho

/-- Retargeting within the tree. -/
theorem TMap.retarget {Γ₀ : Ctx} {D : Tree} (h : D.OK Γ₀) {τ : Lab} {k k₀ : ℕ}
    {Δ Θ : Seq σ Γ₀ D} (hv : Vacant D (k :: τ) Δ Θ) {e e' : EdgeKind}
    (hq : D.edge (k₀ :: τ) = some e') (hc : e.Fits (D.ctxAt Γ₀ (k₀ :: τ)) e') :
    TMap Γ₀ (setIdx idIdx τ k k₀) (D.addEdge (k :: τ) e) D :=
  (TMap.id h).retargetTo hv hq hc

/-- Retargeting leaves a weakened side that avoided the vacant child where it was. -/
theorem retarget_mono_sub {Γ₀ : Ctx} {D : Tree} (h : D.OK Γ₀) {τ : Lab} {k k₀ : ℕ}
    {Δ Θ : Seq σ Γ₀ D} (hv : Vacant D (k :: τ) Δ Θ) {e e' : EdgeKind}
    (hq : D.edge (k₀ :: τ) = some e') (hc : e.Fits (D.ctxAt Γ₀ (k₀ :: τ)) e')
    {kk : ∀ σ, (D.ctxAt Γ₀ σ).Le ((D.addEdge (k :: τ) e).ctxAt Γ₀ σ)} {L : Seq σ Γ₀ D}
    (hL : ∀ p ∈ L, ¬ (k :: τ) <:+ p.1) :
    Seq.relabel (setIdx idIdx τ k k₀) (TMap.retarget h hv hq hc).le (Seq.mono kk L) ⊆ L := by
  intro x hx
  obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq'
  have hl : lmap (setIdx idIdx τ k k₀) p.1 = p.1 := by
    rw [lmap_setIdx_off idIdx p.1 (hL p hp), lmap_idIdx]
  have e₁ : (⟨lmap (setIdx idIdx τ k k₀) p.1, WFF.mono ((TMap.retarget h hv hq hc).le p.1)
      (WFF.mono (kk p.1) p.2)⟩ : LF σ Γ₀ D) = p := by
    rw [WFF.mono_mono, LF.mono_eq p.2 hl _ (Ctx.Le.refl _), WFF.mono_refl]
  rw [e₁]
  exact hp

end GKN

open GKN

/-- ⭐**Retargeting `boxR`'s or `serial`'s child**: a derivation over the tree with the vacant
    child `k :: τ` and a formula there on the right gives one with the formula at the existing
    child `k₀ :: τ`. -/
theorem GKN.retargetR {n : ℕ} {Γ₀ : Ctx} (hs0 : Γ₀.SlotsFrom 0) {D : Tree} (h : D.OK Γ₀)
    {τ : Lab} {k k₀ : ℕ} {Δ Θ : Seq σ Γ₀ D} (hv : Vacant D (k :: τ) Δ Θ) {e e' : EdgeKind}
    (hq : D.edge (k₀ :: τ) = some e') (hc : e.Fits (D.ctxAt Γ₀ (k₀ :: τ)) e') {A : Ctx}
    {φ : WFF σ A 0}
    (h₁ : A.Le ((D.addEdge (k :: τ) e).ctxAt Γ₀ (k :: τ))) (h₂ : A.Le (D.ctxAt Γ₀ (k₀ :: τ)))
    (p : GKN σ Γ₀ n (D.addEdge (k :: τ) e)
      (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) e) Δ)
      (⟨k :: τ, WFF.mono h₁ φ⟩ ::
        Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) e) Θ)) :
    GKN σ Γ₀ n D Δ (⟨k₀ :: τ, WFF.mono h₂ φ⟩ :: Θ) := by
  refine GKN.relabel hs0 p _ D (TMap.retarget h hv hq hc) _ _
    (retarget_mono_sub h hv hq hc hv.left) (cons_sub ?_ (retarget_mono_sub h hv hq hc hv.right))
  dsimp only
  rw [WFF.mono_mono]
  exact LF.mono_eq φ (by rw [lmap_setIdx_new, lmap_idIdx]) _ _

/-- ⭐**Retargeting `diaL`'s child**: the same with the formula on the left. -/
theorem GKN.retargetL {n : ℕ} {Γ₀ : Ctx} (hs0 : Γ₀.SlotsFrom 0) {D : Tree} (h : D.OK Γ₀)
    {τ : Lab} {k k₀ : ℕ} {Δ Θ : Seq σ Γ₀ D} (hv : Vacant D (k :: τ) Δ Θ) {e e' : EdgeKind}
    (hq : D.edge (k₀ :: τ) = some e') (hc : e.Fits (D.ctxAt Γ₀ (k₀ :: τ)) e') {A : Ctx}
    {φ : WFF σ A 0}
    (h₁ : A.Le ((D.addEdge (k :: τ) e).ctxAt Γ₀ (k :: τ))) (h₂ : A.Le (D.ctxAt Γ₀ (k₀ :: τ)))
    (p : GKN σ Γ₀ n (D.addEdge (k :: τ) e)
      (⟨k :: τ, WFF.mono h₁ φ⟩ ::
        Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) e) Δ)
      (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) e) Θ)) :
    GKN σ Γ₀ n D (⟨k₀ :: τ, WFF.mono h₂ φ⟩ :: Δ) Θ := by
  refine GKN.relabel hs0 p _ D (TMap.retarget h hv hq hc) _ _
    (cons_sub ?_ (retarget_mono_sub h hv hq hc hv.left)) (retarget_mono_sub h hv hq hc hv.right)
  dsimp only
  rw [WFF.mono_mono]
  exact LF.mono_eq φ (by rw [lmap_setIdx_new, lmap_idIdx]) _ _

end V12M
