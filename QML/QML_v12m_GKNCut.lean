import QML.QML_v12m_GKNCollapse
import QML.QML_v12m_GKCut

/-!
# QML v12m — cut is admissible in `GKN`

⭐`GKN.cut`: from `Δ ⇒ ⟨τ, A⟩, Θ` and `⟨τ, A⟩, Δ ⇒ Θ` over a tree, `Δ ⇒ Θ` over the same tree
(docs §12.49).  Kleene's proof for G3 with principal formulas kept, as `GK.cut`: induction on the
weight of `A`, then on the sum of the heights (`GKN.CutIH`).
* The cut moves up the left derivation (`permLeft`) until `A` is principal there
  (`RightPrin`), then up the right one (`permRight`) until it is principal there too
  (`LeftPrin`).  A premise over a grown tree takes the other derivation weakened into it: by an
  edge (`GKN.weakenEdge`, relabelling), or by a birth (`GKN.weakenBirth`, tree substitution, the
  node carrying the rule's principal formula).
* Both principal: the cut against each premise first (same formula, smaller height), then on the
  components.  `□`/`◇_x`: the vacant child made by `boxR` (`diaL`) is retargeted onto the child
  `boxL` (`diaR`) used (`GKN.retargetR`/`L`); quantifiers: the eigenvariable unbound by the term
  (`GKN.instance_allR`/`exL`).
* T (docs §12.50 item (v)): `boxR` against `TL` and `diaT` against `diaL` cut the formula out of
  the premise over the grown tree, collapse the new child onto its parent (`GKN.collapse`; for
  `◇_x`, onto `x`'s identity view, opened by `optL`), then cut the lighter formula, at any
  heights.

K, KD, KT and KDT, `Opt` on where T is (`ModalSys.TOpt`); the trees carry `Tree.OK` and
`Tree.WitOK`, over a presented context.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

namespace GKN

variable {σ : Signature} {Γ₀ : Ctx}

/-! ## Weakening -/

theorem EdgeKind.compat_refl : ∀ e : EdgeKind, e.Compat e
  | .box => trivial
  | .dia _ => rfl

/-- A tree maps into itself with a new edge into an absent node. -/
theorem TMap.ofAddEdge {D : Tree} (h : D.OK Γ₀) {c : Lab} (hc : D.edge c = none)
    (e : EdgeKind) : TMap Γ₀ idIdx D (D.addEdge c e) where
  ok := h.addEdge hc e
  edge c' e' he' := by
    refine ⟨e', ?_, .of_compat (EdgeKind.compat_refl e')⟩
    rw [lmap_idIdx, Tree.edge_addEdge, if_neg (fun h => by rw [h, hc] at he'; cases he')]
    exact he'
  birth τ b hb := by rw [lmap_idIdx]; exact hb
  opens τ o ho := by
    rw [lmap_idIdx]
    exact (h.opened τ o ho).mono (Tree.ctxAt_addEdge hc e τ)
  names b hb := ⟨b, hb, rfl⟩

theorem relabel_id_eq {D D' : Tree} {hm : TMap Γ₀ idIdx D D'}
    (hk : ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ τ)) (L : Seq σ Γ₀ D) :
    Seq.relabel idIdx hm.le L = Seq.mono hk L :=
  List.map_congr_left fun p _ => LF.mono_eq p.2 (lmap_idIdx p.1) _ _

/-- ⭐**Weakening by a new edge** into an absent node, height kept. -/
theorem weakenEdge {n : ℕ} (hs0 : Γ₀.SlotsFrom 0) {D : Tree} (hok : D.OK Γ₀)
    {Δ Θ : Seq σ Γ₀ D} (p : GKN σ Γ₀ n D Δ Θ) {c : Lab} (hc : D.edge c = none) (e : EdgeKind) :
    GKN σ Γ₀ n (D.addEdge c e) (Seq.mono (Tree.ctxAt_addEdge hc e) Δ)
      (Seq.mono (Tree.ctxAt_addEdge hc e) Θ) :=
  GKN.relabel hs0 p idIdx _ (TMap.ofAddEdge hok hc e) _ _
    (by
      rw [relabel_id_eq (hm := TMap.ofAddEdge hok hc e) (Tree.ctxAt_addEdge hc e)]
      exact List.Subset.refl _)
    (by
      rw [relabel_id_eq (hm := TMap.ofAddEdge hok hc e) (Tree.ctxAt_addEdge hc e)]
      exact List.Subset.refl _)

/-- A tree maps into itself with a new opening that takes effect. -/
theorem TMap.ofAddOpen {D : Tree} (h : D.OK Γ₀) (hO : ModalSys.Opt = true) {τ : Lab}
    {κ : WitKind} {y : VarSymb} {X : VarType} (hy : (D.ctxAt Γ₀ τ).witK κ y = some X) :
    TMap Γ₀ idIdx D (D.addOpen τ κ y) where
  ok := h.addOpen hO hy
  edge c' e' he' := ⟨e', by rw [lmap_idIdx]; exact he', .of_compat (EdgeKind.compat_refl e')⟩
  birth τ' b hb := by rw [lmap_idIdx]; exact hb
  opens τ' o ho := by
    rw [lmap_idIdx]
    exact (h.opened τ' o ho).mono (Tree.ctxAt_addOpen τ κ y τ')
  names b hb := ⟨b, hb, rfl⟩

/-- ⭐**Weakening by a new opening** that takes effect, height kept. -/
theorem weakenOpen {n : ℕ} (hs0 : Γ₀.SlotsFrom 0) {D : Tree} (hok : D.OK Γ₀)
    {Δ Θ : Seq σ Γ₀ D} (p : GKN σ Γ₀ n D Δ Θ) (hO : ModalSys.Opt = true) {τ : Lab}
    {κ : WitKind} {y : VarSymb} {X : VarType} (hy : (D.ctxAt Γ₀ τ).witK κ y = some X) :
    GKN σ Γ₀ n (D.addOpen τ κ y) (Seq.mono (Tree.ctxAt_addOpen τ κ y) Δ)
      (Seq.mono (Tree.ctxAt_addOpen τ κ y) Θ) :=
  GKN.relabel hs0 p idIdx _ (TMap.ofAddOpen hok hO hy) _ _
    (by
      rw [relabel_id_eq (hm := TMap.ofAddOpen hok hO hy) (Tree.ctxAt_addOpen τ κ y)]
      exact List.Subset.refl _)
    (by
      rw [relabel_id_eq (hm := TMap.ofAddOpen hok hO hy) (Tree.ctxAt_addOpen τ κ y)]
      exact List.Subset.refl _)

/-- A **redundant opening** (the witness opened already) maps back into the tree. -/
theorem TMap.ofOpened {D : Tree} (h : D.OK Γ₀) {τ : Lab} {κ : WitKind} {y : VarSymb}
    (ho : (D.ctxAt Γ₀ τ).Opened κ y) : TMap Γ₀ idIdx (D.addOpen τ κ y) D where
  ok := h
  edge c' e' he' := ⟨e', by rw [lmap_idIdx]; exact he', .of_compat (EdgeKind.compat_refl e')⟩
  birth τ' b hb := by rw [lmap_idIdx]; exact hb
  opens τ' o hm := by
    rw [lmap_idIdx]
    rw [Tree.opensAt_addOpen] at hm
    split_ifs at hm with hτ
    · subst hτ
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ho
      · exact h.opened _ o hm
    · exact h.opened τ' o hm
  names b hb := ⟨b, hb, rfl⟩

theorem _root_.V12M.GKN.Tree.WitOK.addOpen {D : Tree} (h : D.WitOK Γ₀) (τ : Lab) (κ : WitKind)
    (y : VarSymb) : (D.addOpen τ κ y).WitOK Γ₀ := fun k ρ x he =>
  (h k ρ x he).imp fun _ hX => (Tree.ctxAt_addOpen τ κ y ρ).ref hX

theorem Vacant.sub {D : Tree} {c : Lab} {Δ Θ Δ' Θ' : Seq σ Γ₀ D} (hv : Vacant D c Δ Θ)
    (hΔ : Δ' ⊆ Δ) (hΘ : Θ' ⊆ Θ) : Vacant D c Δ' Θ' :=
  ⟨hv.edge, hv.births, hv.opens, fun p hp => hv.left p (hΔ hp), fun p hp => hv.right p (hΘ hp)⟩

theorem both {a b : ℕ} {D : Tree} {Δ₁ Θ₁ Δ₂ Θ₂ : Seq σ Γ₀ D} (p : GKN σ Γ₀ a D Δ₁ Θ₁)
    (q : GKN σ Γ₀ b D Δ₂ Θ₂) : GKN σ Γ₀ (max a b) D Δ₁ Θ₁ ∧ GKN σ Γ₀ (max a b) D Δ₂ Θ₂ :=
  ⟨p.mono_height (le_max_left _ _), q.mono_height (le_max_right _ _)⟩

/-- Rearranging, copying and dropping formulas between sides. -/
macro "wk" : tactic =>
  `(tactic| (intro a ha; simp only [List.mem_cons, Seq.mono, List.map_cons] at ha ⊢; tauto))

/-! ## The induction -/

/-- The induction hypothesis: cut on a lighter formula at any heights, or on one as heavy with a
    smaller sum of heights; over any tree with the invariants. -/
def CutIH (σ : Signature) (Γ₀ : Ctx) (w s : ℕ) : Prop :=
  ∀ {D : Tree}, D.OK Γ₀ → D.WitOK Γ₀ → ∀ (τ : Lab) (A : WFF σ (D.ctxAt Γ₀ τ) 0) {n m : ℕ}
    {Δ Θ : Seq σ Γ₀ D}, (A.weight < w ∨ A.weight = w ∧ n + m < s) →
    GKN σ Γ₀ n D Δ (⟨τ, A⟩ :: Θ) → GKN σ Γ₀ m D (⟨τ, A⟩ :: Δ) Θ → ∃ k, GKN σ Γ₀ k D Δ Θ

/-- ⭐**The cut formula principal on the right of the left derivation**, with that rule's
    premises.  Indexed by the formula, so a case analysis keeps only the matching rules. -/
inductive RightPrin (σ : Signature) (Γ₀ : Ctx) (D : Tree) (τ : Lab) :
    WFF σ (D.ctxAt Γ₀ τ) 0 → ℕ → Seq σ Γ₀ D → Seq σ Γ₀ D → Prop where
  | top {n : ℕ} {Δ Θ : Seq σ Γ₀ D} : RightPrin σ Γ₀ D τ .top n Δ Θ
  | and {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} {n n' : ℕ} {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D Δ (⟨τ, φ⟩ :: ⟨τ, φ.and ψ⟩ :: Θ) →
      GKN σ Γ₀ n' D Δ (⟨τ, ψ⟩ :: ⟨τ, φ.and ψ⟩ :: Θ) → RightPrin σ Γ₀ D τ (φ.and ψ) n Δ Θ
  | or {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} {n n' : ℕ} {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D Δ (⟨τ, φ⟩ :: ⟨τ, ψ⟩ :: ⟨τ, φ.or ψ⟩ :: Θ) → RightPrin σ Γ₀ D τ (φ.or ψ) n Δ Θ
  | imp {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} {n n' : ℕ} {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D (⟨τ, φ⟩ :: Δ) (⟨τ, ψ⟩ :: ⟨τ, φ.imp ψ⟩ :: Θ) →
      RightPrin σ Γ₀ D τ (φ.imp ψ) n Δ Θ
  | all (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0) (u : ℕ) (T : VarType) (hu : D.Fresh Γ₀ (.free u))
      {φ : WFF σ ((D.ctxAt Γ₀ τ).insert (.free u) T) 0}
      (hle : ((D.ctxAt Γ₀ τ).insert (.free u) T).Le ((D.addBirth τ (.free u) T).ctxAt Γ₀ τ))
      {n n' : ℕ} {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' (D.addBirth τ (.free u) T) (Seq.mono (Tree.ctxAt_addBirth hu τ T) Δ)
        (⟨τ, WFF.mono hle φ⟩ :: Seq.mono (Tree.ctxAt_addBirth hu τ T)
          (⟨τ, .all T (WFF.bindFree u (hu.at τ) hs T φ)⟩ :: Θ)) →
      RightPrin σ Γ₀ D τ (.all T (WFF.bindFree u (hu.at τ) hs T φ)) n Δ Θ
  | ex (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0) (T : VarType)
      {φ : WFF σ ((D.ctxAt Γ₀ τ).insert (.bnd 0) T) 1} {a : Ann T}
      (t : Term σ (D.ctxAt Γ₀ τ) T a) {n n' : ℕ} {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D Δ (⟨τ, WFF.instantiate hs t φ⟩ :: ⟨τ, .ex T φ⟩ :: Θ) →
      RightPrin σ Γ₀ D τ (.ex T φ) n Δ Θ
  | box (k : ℕ) {φ : WFF σ (D.ctxAt Γ₀ τ).boxIn 0} {n n' : ℕ} {Δ Θ : Seq σ Γ₀ D}
      (hv : Vacant D (k :: τ) Δ (⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ :: Θ))
      (hle : (D.ctxAt Γ₀ τ).boxIn.Le ((D.addEdge (k :: τ) .box).ctxAt Γ₀ (k :: τ))) : n' < n →
      GKN σ Γ₀ n' (D.addEdge (k :: τ) .box)
        (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) .box) Δ)
        (⟨k :: τ, WFF.mono hle φ⟩ ::
          Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) .box)
            (⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ :: Θ)) →
      RightPrin σ Γ₀ D τ (WFF.box φ) n Δ Θ
  | dia (k : ℕ) (e : EdgeKind) (x : VarSymb) (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X))
      {θ : WFF σ ((D.ctxAt Γ₀ τ).diaIn x) 0} (he : D.edge (k :: τ) = some e)
      (hf : (EdgeKind.dia x).Fits (D.ctxAt Γ₀ (k :: τ)) e)
      (hle : ((D.ctxAt Γ₀ τ).diaIn x).Le (D.ctxAt Γ₀ (k :: τ))) {n n' : ℕ}
      {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D Δ (⟨k :: τ, WFF.mono hle θ⟩ :: ⟨τ, .dia x hx θ⟩ :: Θ) →
      RightPrin σ Γ₀ D τ (.dia x hx θ) n Δ Θ
  | reopen (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
      (hy : (D.ctxAt Γ₀ τ).Opened κ y) {χ : WFF σ (D.ctxAt Γ₀ τ) 0} {n n' : ℕ}
      {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D Δ (⟨τ, χ⟩ :: ⟨τ, .optx hO κ y (hy.imp fun _ h => h.1)
        (WFF.mono (Ctx.le_optInK _ κ y) χ)⟩ :: Θ) →
      RightPrin σ Γ₀ D τ (.optx hO κ y (hy.imp fun _ h => h.1) (WFF.mono (Ctx.le_optInK _ κ y) χ))
        n Δ Θ
  | fold (hO : ModalSys.Opt = true) (k : ℕ) (e : EdgeKind) (x : VarSymb)
      (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X))
      {θ : WFF σ ((D.ctxAt Γ₀ τ).diaIn x) 0} (he : D.edge (k :: τ) = some e)
      (hle : (D.ctxAt Γ₀ τ).boxIn.Le (D.ctxAt Γ₀ (k :: τ))) {n n' : ℕ}
      {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D Δ (⟨k :: τ, WFF.mono hle (WFF.fold hO x hx θ)⟩ :: ⟨τ, .dia x hx θ⟩ :: Θ) →
      RightPrin σ Γ₀ D τ (.dia x hx θ) n Δ Θ
  | diaT (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0)
      (x : VarSymb) (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X))
      {φ : WFF σ ((D.ctxAt Γ₀ τ).diaIn x) 0} {n n' : ℕ} {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D Δ (⟨τ, WFF.optx hO .ident x (hx.imp fun _ h => Ctx.witT_of hT hO h)
        (WFF.collapse (hx.elim fun _ h => Ctx.collapses_diaIn_optInT hT hO _ h) (hs.diaIn x) φ)⟩
          :: ⟨τ, .dia x hx φ⟩ :: Θ) →
      RightPrin σ Γ₀ D τ (.dia x hx φ) n Δ Θ

/-- ⭐**The cut formula principal on the left of the right derivation**, with that rule's
    premises. -/
inductive LeftPrin (σ : Signature) (Γ₀ : Ctx) (D : Tree) (τ : Lab) :
    WFF σ (D.ctxAt Γ₀ τ) 0 → ℕ → Seq σ Γ₀ D → Seq σ Γ₀ D → Prop where
  | bot {m : ℕ} {Δ Θ : Seq σ Γ₀ D} : LeftPrin σ Γ₀ D τ .bot m Δ Θ
  | and {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} {m m' : ℕ} {Δ Θ : Seq σ Γ₀ D} : m' < m →
      GKN σ Γ₀ m' D (⟨τ, φ⟩ :: ⟨τ, ψ⟩ :: ⟨τ, φ.and ψ⟩ :: Δ) Θ →
      LeftPrin σ Γ₀ D τ (φ.and ψ) m Δ Θ
  | or {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} {m m' : ℕ} {Δ Θ : Seq σ Γ₀ D} : m' < m →
      GKN σ Γ₀ m' D (⟨τ, φ⟩ :: ⟨τ, φ.or ψ⟩ :: Δ) Θ →
      GKN σ Γ₀ m' D (⟨τ, ψ⟩ :: ⟨τ, φ.or ψ⟩ :: Δ) Θ → LeftPrin σ Γ₀ D τ (φ.or ψ) m Δ Θ
  | imp {φ ψ : WFF σ (D.ctxAt Γ₀ τ) 0} {m m' : ℕ} {Δ Θ : Seq σ Γ₀ D} : m' < m →
      GKN σ Γ₀ m' D (⟨τ, φ.imp ψ⟩ :: Δ) (⟨τ, φ⟩ :: Θ) →
      GKN σ Γ₀ m' D (⟨τ, ψ⟩ :: ⟨τ, φ.imp ψ⟩ :: Δ) Θ → LeftPrin σ Γ₀ D τ (φ.imp ψ) m Δ Θ
  | all (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0) (T : VarType)
      {φ : WFF σ ((D.ctxAt Γ₀ τ).insert (.bnd 0) T) 1} {a : Ann T}
      (t : Term σ (D.ctxAt Γ₀ τ) T a) {m m' : ℕ} {Δ Θ : Seq σ Γ₀ D} : m' < m →
      GKN σ Γ₀ m' D (⟨τ, WFF.instantiate hs t φ⟩ :: ⟨τ, .all T φ⟩ :: Δ) Θ →
      LeftPrin σ Γ₀ D τ (.all T φ) m Δ Θ
  | ex (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0) (u : ℕ) (T : VarType) (hu : D.Fresh Γ₀ (.free u))
      {φ : WFF σ ((D.ctxAt Γ₀ τ).insert (.free u) T) 0}
      (hle : ((D.ctxAt Γ₀ τ).insert (.free u) T).Le ((D.addBirth τ (.free u) T).ctxAt Γ₀ τ))
      {m m' : ℕ} {Δ Θ : Seq σ Γ₀ D} : m' < m →
      GKN σ Γ₀ m' (D.addBirth τ (.free u) T)
        (⟨τ, WFF.mono hle φ⟩ :: Seq.mono (Tree.ctxAt_addBirth hu τ T)
          (⟨τ, .ex T (WFF.bindFree u (hu.at τ) hs T φ)⟩ :: Δ))
        (Seq.mono (Tree.ctxAt_addBirth hu τ T) Θ) →
      LeftPrin σ Γ₀ D τ (.ex T (WFF.bindFree u (hu.at τ) hs T φ)) m Δ Θ
  | box (k : ℕ) (e : EdgeKind) {χ : WFF σ (D.ctxAt Γ₀ τ).boxIn 0}
      (he : D.edge (k :: τ) = some e) (hle : (D.ctxAt Γ₀ τ).boxIn.Le (D.ctxAt Γ₀ (k :: τ)))
      {m m' : ℕ} {Δ Θ : Seq σ Γ₀ D} : m' < m →
      GKN σ Γ₀ m' D (⟨k :: τ, WFF.mono hle χ⟩ :: ⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) χ⟩ :: Δ) Θ →
      LeftPrin σ Γ₀ D τ (WFF.box χ) m Δ Θ
  | dia (k : ℕ) (x : VarSymb) (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X))
      {ψ : WFF σ ((D.ctxAt Γ₀ τ).diaIn x) 0} {m m' : ℕ} {Δ Θ : Seq σ Γ₀ D}
      (hv : Vacant D (k :: τ) (⟨τ, .dia x hx ψ⟩ :: Δ) Θ)
      (hle : ((D.ctxAt Γ₀ τ).diaIn x).Le ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ (k :: τ))) :
      m' < m →
      GKN σ Γ₀ m' (D.addEdge (k :: τ) (.dia x))
        (⟨k :: τ, WFF.mono hle ψ⟩ ::
          Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) (.dia x))
            (⟨τ, .dia x hx ψ⟩ :: Δ))
        (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) (.dia x)) Θ) →
      LeftPrin σ Γ₀ D τ (.dia x hx ψ) m Δ Θ
  | opt (hO : ModalSys.Opt = true) (κ : WitKind) (y : VarSymb)
      (hy : ∃ X, (D.ctxAt Γ₀ τ).witK κ y = some X) {ψ : WFF σ ((D.ctxAt Γ₀ τ).optInK κ y) 0}
      (hle : ((D.ctxAt Γ₀ τ).optInK κ y).Le ((D.addOpen τ κ y).ctxAt Γ₀ τ)) {m m' : ℕ}
      {Δ Θ : Seq σ Γ₀ D} : m' < m →
      GKN σ Γ₀ m' (D.addOpen τ κ y)
        (⟨τ, WFF.mono hle ψ⟩ :: Seq.mono (Tree.ctxAt_addOpen τ κ y) (⟨τ, .optx hO κ y hy ψ⟩ :: Δ))
        (Seq.mono (Tree.ctxAt_addOpen τ κ y) Θ) →
      LeftPrin σ Γ₀ D τ (.optx hO κ y hy ψ) m Δ Θ
  | T (hT : ModalSys.T = true) (hs : (D.ctxAt Γ₀ τ).SlotsFrom 0)
      {φ : WFF σ (D.ctxAt Γ₀ τ).boxIn 0} {m m' : ℕ} {Δ Θ : Seq σ Γ₀ D} : m' < m →
      GKN σ Γ₀ m' D (⟨τ, WFF.collapse (Ctx.collapses_boxIn_self hT _) hs.boxIn φ⟩ ::
        ⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ :: Δ) Θ →
      LeftPrin σ Γ₀ D τ (WFF.box φ) m Δ Θ

variable [ModalSys.TOpt] [Γ₀.Presented]

theorem wkn {n : ℕ} {D : Tree} (hok : D.OK Γ₀) {Δ Θ Δ' Θ' : Seq σ Γ₀ D}
    (p : GKN σ Γ₀ n D Δ Θ) (hΔ : Δ ⊆ Δ') (hΘ : Θ ⊆ Θ') : GKN σ Γ₀ n D Δ' Θ' :=
  GKN.weaken Ctx.NoSlots.slots hok p hΔ hΘ

/-- The cut moves into a left premise over the same tree. -/
theorem upL {w s : ℕ} (ih : CutIH σ Γ₀ w s) {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {τ : Lab} {A : WFF σ (D.ctxAt Γ₀ τ) 0} (hw : A.weight = w) {n' m : ℕ} (hlt : n' + m < s)
    {Δ Θ Δ' Θ' Θ₁ : Seq σ Γ₀ D} (q : GKN σ Γ₀ m D (⟨τ, A⟩ :: Δ) Θ) (hΔ : Δ ⊆ Δ')
    (hΘ : Θ ⊆ Θ') (p' : GKN σ Γ₀ n' D Δ' Θ₁) (h₁ : Θ₁ ⊆ ⟨τ, A⟩ :: Θ') :
    ∃ k, GKN σ Γ₀ k D Δ' Θ' :=
  ih hok hW τ A (.inr ⟨hw, hlt⟩) (wkn hok p' (List.Subset.refl _) h₁)
    (wkn hok q (List.cons_subset_cons _ hΔ) hΘ)

/-- The cut moves into a right premise over the same tree. -/
theorem upR {w s : ℕ} (ih : CutIH σ Γ₀ w s) {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {τ : Lab} {A : WFF σ (D.ctxAt Γ₀ τ) 0} (hw : A.weight = w) {n m' : ℕ} (hlt : n + m' < s)
    {Δ Θ Δ' Θ' Δ₁ : Seq σ Γ₀ D} (p : GKN σ Γ₀ n D Δ (⟨τ, A⟩ :: Θ)) (hΔ : Δ ⊆ Δ')
    (hΘ : Θ ⊆ Θ') (q' : GKN σ Γ₀ m' D Δ₁ Θ') (h₁ : Δ₁ ⊆ ⟨τ, A⟩ :: Δ') :
    ∃ k, GKN σ Γ₀ k D Δ' Θ' :=
  ih hok hW τ A (.inr ⟨hw, hlt⟩) (wkn hok p hΔ (List.cons_subset_cons _ hΘ))
    (wkn hok q' h₁ (List.Subset.refl _))

theorem sub_cons {α : Type*} (a : α) (L : List α) : L ⊆ a :: L := List.subset_cons_self _ _

theorem Seq.relabel_cons {D D' : Tree} (g : Lab → ℕ → ℕ)
    (h : ∀ τ, (D.ctxAt Γ₀ τ).Le (D'.ctxAt Γ₀ (lmap g τ))) (p : LF σ Γ₀ D) (L : Seq σ Γ₀ D) :
    Seq.relabel g h (p :: L) = ⟨lmap g p.1, WFF.mono (h p.1) p.2⟩ :: Seq.relabel g h L := rfl

/-- Weakening into a larger tree and relabelling back is nothing. -/
theorem relabel_back {D D' : Tree} {hm : TMap Γ₀ idIdx D' D}
    (hk : ∀ σ', (D.ctxAt Γ₀ σ').Le (D'.ctxAt Γ₀ σ')) (L : Seq σ Γ₀ D) :
    Seq.relabel idIdx hm.le (Seq.mono hk L) = L := by
  unfold Seq.relabel Seq.mono
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  refine List.map_congr_left fun p _ => ?_
  obtain ⟨ρ, ψ⟩ := p
  change (⟨lmap idIdx ρ, WFF.mono _ (WFF.mono _ ψ)⟩ : LF σ Γ₀ D) = ⟨ρ, ψ⟩
  rw [WFF.mono_mono, LF.mono_eq ψ (lmap_idIdx ρ) _ (Ctx.Le.refl _), WFF.mono_refl]

/-- Retargeting into a larger tree leaves a weakened side that avoided the vacant child. -/
theorem retargetTo_mono_sub {D D' : Tree} (hm : TMap Γ₀ idIdx D D') {τ : Lab} {k k₀ : ℕ}
    {Δ Θ : Seq σ Γ₀ D} (hv : Vacant D (k :: τ) Δ Θ) {e e' : EdgeKind}
    (hq : D'.edge (k₀ :: τ) = some e') (hc : e.Fits (D'.ctxAt Γ₀ (k₀ :: τ)) e')
    {kk : ∀ σ', (D.ctxAt Γ₀ σ').Le ((D.addEdge (k :: τ) e).ctxAt Γ₀ σ')}
    (kk' : ∀ σ', (D.ctxAt Γ₀ σ').Le (D'.ctxAt Γ₀ σ')) {L : Seq σ Γ₀ D}
    (hL : ∀ p ∈ L, ¬ (k :: τ) <:+ p.1) :
    Seq.relabel (setIdx idIdx τ k k₀) (hm.retargetTo hv hq hc).le (Seq.mono kk L) ⊆
      Seq.mono kk' L := by
  intro x hx
  obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq'
  have hl : lmap (setIdx idIdx τ k k₀) p.1 = p.1 := by
    rw [lmap_setIdx_off idIdx p.1 (hL p hp), lmap_idIdx]
  have e₁ : (⟨lmap (setIdx idIdx τ k k₀) p.1, WFF.mono ((hm.retargetTo hv hq hc).le p.1)
      (WFF.mono (kk p.1) p.2)⟩ : LF σ Γ₀ D') = ⟨p.1, WFF.mono (kk' p.1) p.2⟩ := by
    rw [WFF.mono_mono]
    exact LF.mono_eq p.2 hl _ _
  rw [e₁]
  exact List.mem_map_of_mem hp

/-! ## The cut moves up the left derivation -/

set_option maxHeartbeats 2000000 in
-- One case per rule of `GKN`, each weakening and rearranging sides (`wk`'s `tauto`): long, not
-- stuck.
/-- ⭐**The cut moves up the left derivation** until the cut formula is principal there. -/
theorem permLeft {w s : ℕ} (ih : CutIH σ Γ₀ w s) {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    (τ : Lab) (A : WFF σ (D.ctxAt Γ₀ τ) 0) {n m : ℕ} {Δ Θ : Seq σ Γ₀ D}
    (hw : A.weight = w) (hs : n + m = s)
    (p : GKN σ Γ₀ n D Δ (⟨τ, A⟩ :: Θ)) (q : GKN σ Γ₀ m D (⟨τ, A⟩ :: Δ) Θ) :
    (∃ k, GKN σ Γ₀ k D Δ Θ) ∨ RightPrin σ Γ₀ D τ A n Δ Θ := by
  have hs0 : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
  cases p with
  | ax τ' P hP h₁ h₂ =>
      rcases List.mem_cons.mp h₂ with he | h₂
      · refine .inl ⟨_, wkn hok q (fun x hx => ?_) (List.Subset.refl _)⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [← he]; exact h₁
        · exact hx
      · exact .inl ⟨0, .ax τ' P hP h₁ h₂⟩
  | botL τ' h => exact .inl ⟨0, .botL τ' h⟩
  | topR τ' h =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr .top
      · exact .inl ⟨0, .topR τ' h⟩
  | @andL n' _ _ _ τ' φ ψ h p₁ =>
      obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (by wk) (List.Subset.refl _) p₁
        (List.Subset.refl _)
      exact .inl ⟨k + 1, .andL τ' h d⟩
  | @andR n' _ _ _ τ' φ ψ h p₁ p₂ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.and (Nat.lt_succ_self _) p₁ p₂)
      · obtain ⟨k₁, d₁⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (sub_cons ⟨τ', φ⟩ Θ) p₁ (by wk)
        obtain ⟨k₂, d₂⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (sub_cons ⟨τ', ψ⟩ Θ) p₂ (by wk)
        exact .inl ⟨_, .andR τ' h (both d₁ d₂).1 (both d₁ d₂).2⟩
  | @orL n' _ _ _ τ' φ ψ h p₁ p₂ =>
      obtain ⟨k₁, d₁⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (List.Subset.refl _) p₁
        (List.Subset.refl _)
      obtain ⟨k₂, d₂⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (List.Subset.refl _) p₂
        (List.Subset.refl _)
      exact .inl ⟨_, .orL τ' h (both d₁ d₂).1 (both d₁ d₂).2⟩
  | @orR n' _ _ _ τ' φ ψ h p₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.or (Nat.lt_succ_self _) p₁)
      · obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (Θ' := ⟨τ', φ⟩ :: ⟨τ', ψ⟩ :: Θ) (by wk) p₁ (by wk)
        exact .inl ⟨k + 1, .orR τ' h d⟩
  | @impL n' _ _ _ τ' φ ψ h p₁ p₂ =>
      obtain ⟨k₁, d₁⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
        (sub_cons ⟨τ', φ⟩ Θ) p₁ (by wk)
      obtain ⟨k₂, d₂⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (List.Subset.refl _) p₂
        (List.Subset.refl _)
      exact .inl ⟨_, .impL τ' h (both d₁ d₂).1 (both d₁ d₂).2⟩
  | @impR n' _ _ _ τ' φ ψ h p₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.imp (Nat.lt_succ_self _) p₁)
      · obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (sub_cons ⟨τ', ψ⟩ Θ) p₁
          (by wk)
        exact .inl ⟨k + 1, .impR τ' h d⟩
  | @allL n' _ _ _ τ' hs' T' φ a' t' h p₁ =>
      obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (List.Subset.refl _) p₁
        (List.Subset.refl _)
      exact .inl ⟨k + 1, .allL τ' hs' T' t' h d⟩
  | @exR n' _ _ _ τ' hs' T' φ a' t' h p₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.ex hs' T' t' (Nat.lt_succ_self _) p₁)
      · obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (sub_cons ⟨τ', WFF.instantiate hs' t' φ⟩ Θ) p₁ (by wk)
        exact .inl ⟨k + 1, .exR τ' hs' T' t' h d⟩
  | @ref n' _ _ _ τ' t' p₁ =>
      obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (List.Subset.refl _) p₁
        (List.Subset.refl _)
      exact .inl ⟨k + 1, .ref τ' t' d⟩
  | @repl n' _ _ _ τ' hs' P hP t₁ t₂ h₁ h₂ p₁ =>
      obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (List.Subset.refl _) p₁
        (List.Subset.refl _)
      exact .inl ⟨k + 1, .repl τ' hs' hP t₁ t₂ h₁ h₂ d⟩
  | @allR n' _ _ _ τ' hs' v T' hv φ hle h p₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.all hs' v T' hv hle (Nat.lt_succ_self _) p₁)
      · have hk := Tree.ctxAt_addBirth hv τ' T'
        have hok' := hok.addBirth hv τ' T'
        have q' := weakenBirth hok hW q hv τ' T' (.inr ⟨_, h, rfl⟩)
        haveI : ((D.addBirth τ' (.free v) T').ctxAt Γ₀ τ).NoSlots :=
          ⟨Tree.ctxAt_slots hs0 hok' τ⟩
        obtain ⟨k, d⟩ := ih hok' (hW.addBirth hv τ' T') τ (WFF.mono (hk τ) A)
          (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
          (Δ := Seq.mono hk Δ) (Θ := ⟨τ', WFF.mono hle φ⟩ :: Seq.mono hk Θ)
          (wkn hok' p₁ (List.Subset.refl _) (by wk)) (wkn hok' q' (List.Subset.refl _) (by wk))
        exact .inl ⟨k + 1, .allR τ' hs' v T' hv hle h d⟩
  | @exL n' _ _ _ τ' hs' v T' hv φ hle h p₁ =>
      have hk := Tree.ctxAt_addBirth hv τ' T'
      have hok' := hok.addBirth hv τ' T'
      have q' := weakenBirth hok hW q hv τ' T' (.inl ⟨_, List.mem_cons_of_mem _ h, rfl⟩)
      haveI : ((D.addBirth τ' (.free v) T').ctxAt Γ₀ τ).NoSlots :=
        ⟨Tree.ctxAt_slots hs0 hok' τ⟩
      obtain ⟨k, d⟩ := ih hok' (hW.addBirth hv τ' T') τ (WFF.mono (hk τ) A)
        (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
        (Δ := ⟨τ', WFF.mono hle φ⟩ :: Seq.mono hk Δ) (Θ := Seq.mono hk Θ)
        (wkn hok' p₁ (List.Subset.refl _) (by wk)) (wkn hok' q' (by wk) (List.Subset.refl _))
      exact .inl ⟨k + 1, .exL τ' hs' v T' hv hle h d⟩
  | @boxL n' _ _ _ τ' k e χ he hle h p₁ =>
      obtain ⟨k', d⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (List.Subset.refl _) p₁
        (List.Subset.refl _)
      exact .inl ⟨k' + 1, .boxL τ' k e he hle h d⟩
  | @diaR n' _ _ _ τ' k e x hx θ he hf hle h p₁ =>
      rcases List.mem_cons.mp h with he' | h
      · cases he'
        exact .inr (.dia k e x hx he hf hle (Nat.lt_succ_self _) p₁)
      · obtain ⟨k', d⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (sub_cons ⟨k :: τ', WFF.mono hle θ⟩ Θ) p₁ (by wk)
        exact .inl ⟨k' + 1, .diaR τ' k e x hx he hf hle h d⟩
  | @TL n' _ _ _ hT τ' hs' φ h p₁ =>
      obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (sub_cons _ _) (List.Subset.refl _) p₁
        (List.Subset.refl _)
      exact .inl ⟨k + 1, .TL hT τ' hs' h d⟩
  | @diaT n' _ _ _ hT hO τ' hs' x hx φ h p₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.diaT hT hO hs' x hx (Nat.lt_succ_self _) p₁)
      · obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (sub_cons ⟨τ', WFF.optx hO .ident x (hx.imp fun _ h => Ctx.witT_of hT hO h)
            (WFF.collapse (hx.elim fun _ h => Ctx.collapses_diaIn_optInT hT hO _ h)
              (hs'.diaIn x) φ)⟩ Θ) p₁ (by wk)
        exact .inl ⟨k + 1, .diaT hT hO τ' hs' x hx h d⟩
  | @optL n' _ _ _ hO τ' κ y hy ψ hle h p₁ =>
      obtain ⟨X, hX⟩ := id hy
      have hk := Tree.ctxAt_addOpen (D := D) (Γ₀ := Γ₀) τ' κ y
      have hok' := hok.addOpen hO hX
      have q' := weakenOpen hs0 hok q hO hX
      haveI : ((D.addOpen τ' κ y).ctxAt Γ₀ τ).NoSlots := ⟨Tree.ctxAt_slots hs0 hok' τ⟩
      obtain ⟨k, d⟩ := ih hok' (hW.addOpen τ' κ y) τ (WFF.mono (hk τ) A)
        (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
        (Δ := ⟨τ', WFF.mono hle ψ⟩ :: Seq.mono hk Δ) (Θ := Seq.mono hk Θ)
        (wkn hok' p₁ (List.Subset.refl _) (by wk)) (wkn hok' q' (by wk) (List.Subset.refl _))
      exact .inl ⟨k + 1, .optL hO τ' κ y hy hle h d⟩
  | @reopenR n' _ _ _ hO τ' κ y hy χ h p₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.reopen hO κ y hy (Nat.lt_succ_self _) p₁)
      · obtain ⟨k, d⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (sub_cons ⟨τ', χ⟩ Θ) p₁ (by wk)
        exact .inl ⟨k + 1, .reopenR hO τ' κ y hy h d⟩
  | @foldR n' _ _ _ hO τ' k e x hx θ he hle h p₁ =>
      rcases List.mem_cons.mp h with he' | h
      · cases he'
        exact .inr (.fold hO k e x hx he hle (Nat.lt_succ_self _) p₁)
      · obtain ⟨k', d⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (sub_cons ⟨k :: τ', WFF.mono hle (WFF.fold hO x hx θ)⟩ Θ) p₁ (by wk)
        exact .inl ⟨k' + 1, .foldR hO τ' k e x hx he hle h d⟩
  | @boxR n' _ _ _ τ' k φ hv hle h p₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.box k hv hle (Nat.lt_succ_self _) p₁)
      · have hc := hv.edge _ (List.suffix_refl _)
        have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc EdgeKind.box
        have hok' := hok.addEdge hc EdgeKind.box
        have q' := weakenEdge hs0 hok q hc .box
        haveI : ((D.addEdge (k :: τ') .box).ctxAt Γ₀ τ).NoSlots :=
          ⟨Tree.ctxAt_slots hs0 hok' τ⟩
        obtain ⟨k', d⟩ := ih hok' (hW.addEdge hc .box (fun _ _ _ _ he => by cases he)) τ
          (WFF.mono (hk τ) A) (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
          (Δ := Seq.mono hk Δ) (Θ := ⟨k :: τ', WFF.mono hle φ⟩ :: Seq.mono hk Θ)
          (wkn hok' p₁ (List.Subset.refl _) (by wk)) (wkn hok' q' (List.Subset.refl _) (by wk))
        exact .inl ⟨k' + 1, .boxR τ' k (hv.sub (List.Subset.refl _) (sub_cons _ _)) hle h d⟩
  | @serial n' _ _ _ hD τ' k hv p₁ =>
      have hc := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc EdgeKind.box
      have hok' := hok.addEdge hc EdgeKind.box
      have q' := weakenEdge hs0 hok q hc .box
      haveI : ((D.addEdge (k :: τ') .box).ctxAt Γ₀ τ).NoSlots :=
        ⟨Tree.ctxAt_slots hs0 hok' τ⟩
      obtain ⟨k', d⟩ := ih hok' (hW.addEdge hc .box (fun _ _ _ _ he => by cases he)) τ
        (WFF.mono (hk τ) A) (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
        (Δ := Seq.mono hk Δ) (Θ := Seq.mono hk Θ) p₁ q'
      exact .inl ⟨k' + 1, .serial hD τ' k (hv.sub (List.Subset.refl _) (sub_cons _ _)) d⟩
  | @diaL n' _ _ _ τ' k x hx ψ hv hle h p₁ =>
      have hc := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc (EdgeKind.dia x)
      have hok' := hok.addEdge hc (EdgeKind.dia x)
      have q' := weakenEdge hs0 hok q hc (.dia x)
      haveI : ((D.addEdge (k :: τ') (.dia x)).ctxAt Γ₀ τ).NoSlots :=
        ⟨Tree.ctxAt_slots hs0 hok' τ⟩
      obtain ⟨k', d⟩ := ih hok' (hW.addEdge hc (.dia x) (fun j ρ y hj he => by
          cases hj
          cases he
          exact hx)) τ
        (WFF.mono (hk τ) A) (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
        (Δ := ⟨k :: τ', WFF.mono hle ψ⟩ :: Seq.mono hk Δ) (Θ := Seq.mono hk Θ) p₁
        (wkn hok' q' (by wk) (List.Subset.refl _))
      exact .inl ⟨k' + 1, .diaL τ' k x hx (hv.sub (List.Subset.refl _) (sub_cons _ _)) hle h d⟩

/-! ## The cut moves up the right derivation -/

set_option maxHeartbeats 2000000 in
-- One case per rule of `GKN`, each weakening and rearranging sides (`wk`'s `tauto`): long, not
-- stuck.
/-- ⭐**The cut moves up the right derivation** until the cut formula is principal there.  The
    cut formula is not an atom (those are settled at the left derivation's axioms). -/
theorem permRight {w s : ℕ} (ih : CutIH σ Γ₀ w s) {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    (τ : Lab) (A : WFF σ (D.ctxAt Γ₀ τ) 0) {n m : ℕ} {Δ Θ : Seq σ Γ₀ D}
    (hw : A.weight = w) (hs : n + m = s) (hA : ¬ A.IsAtom)
    (p : GKN σ Γ₀ n D Δ (⟨τ, A⟩ :: Θ)) (q : GKN σ Γ₀ m D (⟨τ, A⟩ :: Δ) Θ) :
    (∃ k, GKN σ Γ₀ k D Δ Θ) ∨ LeftPrin σ Γ₀ D τ A m Δ Θ := by
  have hs0 : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
  cases q with
  | ax τ' P hP h₁ h₂ =>
      rcases List.mem_cons.mp h₁ with he | h₁
      · cases he
        exact absurd hP hA
      · exact .inl ⟨0, .ax τ' P hP h₁ h₂⟩
  | botL τ' h =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr .bot
      · exact .inl ⟨0, .botL τ' h⟩
  | topR τ' h => exact .inl ⟨0, .topR τ' h⟩
  | @andL m' _ _ _ τ' φ ψ h q₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.and (Nat.lt_succ_self _) q₁)
      · obtain ⟨k, d⟩ := upR ih hok hW hw (by omega) p (Δ' := ⟨τ', φ⟩ :: ⟨τ', ψ⟩ :: Δ) (by wk)
          (List.Subset.refl _) q₁ (by wk)
        exact .inl ⟨k + 1, .andL τ' h d⟩
  | @andR m' _ _ _ τ' φ ψ h q₁ q₂ =>
      obtain ⟨k₁, d₁⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₁
        (List.Subset.refl _)
      obtain ⟨k₂, d₂⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₂
        (List.Subset.refl _)
      exact .inl ⟨_, .andR τ' h (both d₁ d₂).1 (both d₁ d₂).2⟩
  | @orL m' _ _ _ τ' φ ψ h q₁ q₂ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.or (Nat.lt_succ_self _) q₁ q₂)
      · obtain ⟨k₁, d₁⟩ := upR ih hok hW hw (by omega) p (Δ' := ⟨τ', φ⟩ :: Δ) (sub_cons _ _)
          (List.Subset.refl _) q₁ (by wk)
        obtain ⟨k₂, d₂⟩ := upR ih hok hW hw (by omega) p (Δ' := ⟨τ', ψ⟩ :: Δ) (sub_cons _ _)
          (List.Subset.refl _) q₂ (by wk)
        exact .inl ⟨_, .orL τ' h (both d₁ d₂).1 (both d₁ d₂).2⟩
  | @orR m' _ _ _ τ' φ ψ h q₁ =>
      obtain ⟨k, d⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (by wk) q₁
        (List.Subset.refl _)
      exact .inl ⟨k + 1, .orR τ' h d⟩
  | @impL m' _ _ _ τ' φ ψ h q₁ q₂ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.imp (Nat.lt_succ_self _) q₁ q₂)
      · obtain ⟨k₁, d₁⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₁
          (List.Subset.refl _)
        obtain ⟨k₂, d₂⟩ := upR ih hok hW hw (by omega) p (Δ' := ⟨τ', ψ⟩ :: Δ) (sub_cons _ _)
          (List.Subset.refl _) q₂ (by wk)
        exact .inl ⟨_, .impL τ' h (both d₁ d₂).1 (both d₁ d₂).2⟩
  | @impR m' _ _ _ τ' φ ψ h q₁ =>
      obtain ⟨k, d⟩ := upR ih hok hW hw (by omega) p (Δ' := ⟨τ', φ⟩ :: Δ) (sub_cons _ _)
        (sub_cons _ _) q₁ (by wk)
      exact .inl ⟨k + 1, .impR τ' h d⟩
  | @allL m' _ _ _ τ' hs' T' φ a' t' h q₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.all hs' T' t' (Nat.lt_succ_self _) q₁)
      · obtain ⟨k, d⟩ := upR ih hok hW hw (by omega) p
          (Δ' := ⟨τ', WFF.instantiate hs' t' φ⟩ :: Δ) (sub_cons _ _) (List.Subset.refl _) q₁
          (by wk)
        exact .inl ⟨k + 1, .allL τ' hs' T' t' h d⟩
  | @exR m' _ _ _ τ' hs' T' φ a' t' h q₁ =>
      obtain ⟨k, d⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₁
        (List.Subset.refl _)
      exact .inl ⟨k + 1, .exR τ' hs' T' t' h d⟩
  | @ref m' _ _ _ τ' t' q₁ =>
      obtain ⟨k, d⟩ := upR ih hok hW hw (by omega) p (Δ' := ⟨τ', .eq t' t'⟩ :: Δ)
        (sub_cons _ _) (List.Subset.refl _) q₁ (by wk)
      exact .inl ⟨k + 1, .ref τ' t' d⟩
  | @repl m' _ _ _ τ' hs' P hP t₁ t₂ h₁ h₂ q₁ =>
      rcases List.mem_cons.mp h₁ with he | h₁
      · cases he
        exact absurd trivial hA
      rcases List.mem_cons.mp h₂ with he | h₂
      · cases he
        exact absurd hP.instantiate hA
      obtain ⟨k, d⟩ := upR ih hok hW hw (by omega) p
        (Δ' := ⟨τ', WFF.instantiate hs' t₂ P⟩ :: Δ) (sub_cons _ _) (List.Subset.refl _) q₁
        (by wk)
      exact .inl ⟨k + 1, .repl τ' hs' hP t₁ t₂ h₁ h₂ d⟩
  | @boxL m' _ _ _ τ' k e χ he hle h q₁ =>
      rcases List.mem_cons.mp h with he' | h
      · cases he'
        exact .inr (.box k e he hle (Nat.lt_succ_self _) q₁)
      · obtain ⟨k', d⟩ := upR ih hok hW hw (by omega) p
          (Δ' := ⟨k :: τ', WFF.mono hle χ⟩ :: Δ) (sub_cons _ _) (List.Subset.refl _) q₁ (by wk)
        exact .inl ⟨k' + 1, .boxL τ' k e he hle h d⟩
  | @diaR m' _ _ _ τ' k e x hx θ he hf hle h q₁ =>
      obtain ⟨k', d⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₁
        (List.Subset.refl _)
      exact .inl ⟨k' + 1, .diaR τ' k e x hx he hf hle h d⟩
  | @TL m' _ _ _ hT τ' hs' φ h q₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.T hT hs' (Nat.lt_succ_self _) q₁)
      · obtain ⟨k', d⟩ := upR ih hok hW hw (by omega) p
          (Δ' := ⟨τ', WFF.collapse (Ctx.collapses_boxIn_self hT _) hs'.boxIn φ⟩ :: Δ)
          (sub_cons _ _) (List.Subset.refl _) q₁ (by wk)
        exact .inl ⟨k' + 1, .TL hT τ' hs' h d⟩
  | @diaT m' _ _ _ hT hO τ' hs' x hx φ h q₁ =>
      obtain ⟨k', d⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₁
        (List.Subset.refl _)
      exact .inl ⟨k' + 1, .diaT hT hO τ' hs' x hx h d⟩
  | @reopenR m' _ _ _ hO τ' κ y hy χ h q₁ =>
      obtain ⟨k', d⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₁
        (List.Subset.refl _)
      exact .inl ⟨k' + 1, .reopenR hO τ' κ y hy h d⟩
  | @foldR m' _ _ _ hO τ' k e x hx θ he hle h q₁ =>
      obtain ⟨k', d⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₁
        (List.Subset.refl _)
      exact .inl ⟨k' + 1, .foldR hO τ' k e x hx he hle h d⟩
  | @optL m' _ _ _ hO τ' κ y hy ψ hle h q₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.opt hO κ y hy hle (Nat.lt_succ_self _) q₁)
      · obtain ⟨X, hX⟩ := id hy
        have hk := Tree.ctxAt_addOpen (D := D) (Γ₀ := Γ₀) τ' κ y
        have hok' := hok.addOpen hO hX
        have p' := weakenOpen hs0 hok p hO hX
        haveI : ((D.addOpen τ' κ y).ctxAt Γ₀ τ).NoSlots := ⟨Tree.ctxAt_slots hs0 hok' τ⟩
        obtain ⟨k, d⟩ := ih hok' (hW.addOpen τ' κ y) τ (WFF.mono (hk τ) A)
          (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
          (Δ := ⟨τ', WFF.mono hle ψ⟩ :: Seq.mono hk Δ) (Θ := Seq.mono hk Θ)
          (wkn hok' p' (by wk) (List.Subset.refl _)) (wkn hok' q₁ (by wk) (List.Subset.refl _))
        exact .inl ⟨k + 1, .optL hO τ' κ y hy hle h d⟩
  | @allR m' _ _ _ τ' hs' v T' hv φ hle h q₁ =>
      have hk := Tree.ctxAt_addBirth hv τ' T'
      have hok' := hok.addBirth hv τ' T'
      have p' := weakenBirth hok hW p hv τ' T' (.inr ⟨_, List.mem_cons_of_mem _ h, rfl⟩)
      haveI : ((D.addBirth τ' (.free v) T').ctxAt Γ₀ τ).NoSlots :=
        ⟨Tree.ctxAt_slots hs0 hok' τ⟩
      obtain ⟨k, d⟩ := ih hok' (hW.addBirth hv τ' T') τ (WFF.mono (hk τ) A)
        (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
        (Δ := Seq.mono hk Δ) (Θ := ⟨τ', WFF.mono hle φ⟩ :: Seq.mono hk Θ)
        (wkn hok' p' (List.Subset.refl _) (by wk)) q₁
      exact .inl ⟨k + 1, .allR τ' hs' v T' hv hle h d⟩
  | @exL m' _ _ _ τ' hs' v T' hv φ hle h q₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.ex hs' v T' hv hle (Nat.lt_succ_self _) q₁)
      · have hk := Tree.ctxAt_addBirth hv τ' T'
        have hok' := hok.addBirth hv τ' T'
        have p' := weakenBirth hok hW p hv τ' T' (.inl ⟨_, h, rfl⟩)
        haveI : ((D.addBirth τ' (.free v) T').ctxAt Γ₀ τ).NoSlots :=
          ⟨Tree.ctxAt_slots hs0 hok' τ⟩
        obtain ⟨k, d⟩ := ih hok' (hW.addBirth hv τ' T') τ (WFF.mono (hk τ) A)
          (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
          (Δ := ⟨τ', WFF.mono hle φ⟩ :: Seq.mono hk Δ) (Θ := Seq.mono hk Θ)
          (wkn hok' p' (by wk) (List.Subset.refl _)) (wkn hok' q₁ (by wk) (List.Subset.refl _))
        exact .inl ⟨k + 1, .exL τ' hs' v T' hv hle h d⟩
  | @boxR m' _ _ _ τ' k φ hv hle h q₁ =>
      have hc := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc EdgeKind.box
      have hok' := hok.addEdge hc EdgeKind.box
      have p' := weakenEdge hs0 hok p hc .box
      haveI : ((D.addEdge (k :: τ') .box).ctxAt Γ₀ τ).NoSlots :=
        ⟨Tree.ctxAt_slots hs0 hok' τ⟩
      obtain ⟨k', d⟩ := ih hok' (hW.addEdge hc .box (fun _ _ _ _ he => by cases he)) τ
        (WFF.mono (hk τ) A) (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
        (Δ := Seq.mono hk Δ) (Θ := ⟨k :: τ', WFF.mono hle φ⟩ :: Seq.mono hk Θ)
        (wkn hok' p' (List.Subset.refl _) (by wk)) q₁
      exact .inl ⟨k' + 1, .boxR τ' k (hv.sub (sub_cons _ _) (List.Subset.refl _)) hle h d⟩
  | @serial m' _ _ _ hD τ' k hv q₁ =>
      have hc := hv.edge _ (List.suffix_refl _)
      have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc EdgeKind.box
      have hok' := hok.addEdge hc EdgeKind.box
      have p' := weakenEdge hs0 hok p hc .box
      haveI : ((D.addEdge (k :: τ') .box).ctxAt Γ₀ τ).NoSlots :=
        ⟨Tree.ctxAt_slots hs0 hok' τ⟩
      obtain ⟨k', d⟩ := ih hok' (hW.addEdge hc .box (fun _ _ _ _ he => by cases he)) τ
        (WFF.mono (hk τ) A) (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
        (Δ := Seq.mono hk Δ) (Θ := Seq.mono hk Θ) p' q₁
      exact .inl ⟨k' + 1, .serial hD τ' k (hv.sub (sub_cons _ _) (List.Subset.refl _)) d⟩
  | @diaL m' _ _ _ τ' k x hx ψ hv hle h q₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.dia k x hx hv hle (Nat.lt_succ_self _) q₁)
      · have hc := hv.edge _ (List.suffix_refl _)
        have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc (EdgeKind.dia x)
        have hok' := hok.addEdge hc (EdgeKind.dia x)
        have p' := weakenEdge hs0 hok p hc (.dia x)
        haveI : ((D.addEdge (k :: τ') (.dia x)).ctxAt Γ₀ τ).NoSlots :=
          ⟨Tree.ctxAt_slots hs0 hok' τ⟩
        obtain ⟨k', d⟩ := ih hok' (hW.addEdge hc (.dia x) (fun j ρ y hj he => by
            cases hj
            cases he
            exact hx)) τ
          (WFF.mono (hk τ) A) (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
          (Δ := ⟨k :: τ', WFF.mono hle ψ⟩ :: Seq.mono hk Δ) (Θ := Seq.mono hk Θ)
          (wkn hok' p' (by wk) (List.Subset.refl _)) (wkn hok' q₁ (by wk) (List.Subset.refl _))
        exact .inl ⟨k' + 1, .diaL τ' k x hx (hv.sub (sub_cons _ _) (List.Subset.refl _)) hle h d⟩

/-! ## Both principal -/

theorem RightPrin.not_atom {D : Tree} {τ : Lab} {A : WFF σ (D.ctxAt Γ₀ τ) 0} {n : ℕ}
    {Δ Θ : Seq σ Γ₀ D} (P : RightPrin σ Γ₀ D τ A n Δ Θ) : ¬ A.IsAtom := by
  cases P <;> exact id

set_option maxHeartbeats 2000000 in
-- Several cuts with rearranged sides (`wk`'s `tauto`): long, not stuck.
/-- ⭐**`boxR` against `TL`** (T, docs §12.50 item (v)): cut `□φ` out of `boxR`'s premise over
    the grown tree, collapse the new child onto `τ` (`GKN.collapse`), cut `□φ` out of `TL`'s
    premise, then cut the lighter collapsed formula. -/
theorem boxTPrin {w s : ℕ} (ih : CutIH σ Γ₀ w s) {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {τ : Lab} {k : ℕ} {φ : WFF σ (D.ctxAt Γ₀ τ).boxIn 0} {n n' m m' : ℕ} {Δ Θ : Seq σ Γ₀ D}
    (hw : (WFF.box (Γ := D.ctxAt Γ₀ τ) φ).weight = w) (hs : n + m = s) (hn : n' < n)
    (hm : m' < m) (p : GKN σ Γ₀ n D Δ (⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ :: Θ))
    (q : GKN σ Γ₀ m D (⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ :: Δ) Θ)
    (hv : Vacant D (k :: τ) Δ (⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ :: Θ))
    (hle : (D.ctxAt Γ₀ τ).boxIn.Le ((D.addEdge (k :: τ) .box).ctxAt Γ₀ (k :: τ)))
    (p₁ : GKN σ Γ₀ n' (D.addEdge (k :: τ) .box)
      (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) .box) Δ)
      (⟨k :: τ, WFF.mono hle φ⟩ ::
        Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) .box)
          (⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ :: Θ)))
    (hT : ModalSys.T = true) (hsτ : (D.ctxAt Γ₀ τ).SlotsFrom 0)
    (q₁ : GKN σ Γ₀ m' D (⟨τ, WFF.collapse (Ctx.collapses_boxIn_self hT _) hsτ.boxIn φ⟩ ::
      ⟨τ, WFF.box (Γ := D.ctxAt Γ₀ τ) φ⟩ :: Δ) Θ) :
    ∃ k, GKN σ Γ₀ k D Δ Θ := by
  have hs0 : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
  have hO := ModalSys.TOpt.tOpt hT
  haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨hsτ⟩
  have hc := hv.edge _ (List.suffix_refl _)
  have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc EdgeKind.box
  have hok' := hok.addEdge hc EdgeKind.box
  have hW' := hW.addEdge hc .box (fun _ _ _ _ he => by cases he)
  have q' := weakenEdge hs0 hok q hc .box
  haveI : ((D.addEdge (k :: τ) .box).ctxAt Γ₀ τ).NoSlots :=
    ⟨Tree.ctxAt_slots hs0 hok' τ⟩
  -- cut `□φ` out of `boxR`'s premise
  obtain ⟨_, P₀⟩ := ih hok' hW' τ (WFF.mono (hk τ) (WFF.box φ))
    (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
    (Δ := Seq.mono hk Δ) (Θ := ⟨k :: τ, WFF.mono hle φ⟩ :: Seq.mono hk Θ)
    (wkn hok' p₁ (List.Subset.refl _) (by wk)) (wkn hok' q' (List.Subset.refl _) (by wk))
  -- the new child collapsed onto `τ`
  have cs₀ : CSetup Γ₀ τ k idIdx (D.addEdge (k :: τ) .box) D :=
    CSetup.ofEdge hok hT hO hv .box hok (fun _ => Ctx.Le.refl _) (fun _ => rfl)
      (fun _ _ hb => hb) (fun _ hb => hb) (fun _ he => by cases he)
  have e₁ : cs₀.lf hs0 hok' hW' ⟨k :: τ, WFF.mono hle φ⟩ =
      ⟨τ, WFF.collapse (Ctx.collapses_boxIn_self hT _) hsτ.boxIn φ⟩ := by
    rw [cs₀.lf_mk, cs₀.F_under hs0 hok' hW' (List.suffix_refl _)]
    have := LF.col_eq (cmap_idIdx_c τ k) (cdepth_c τ k)
      ((cs₀.ctx hok' hW' (k :: τ)).2 (List.suffix_refl _)) (Tree.ctxAt_slots hs0 hok' _) hle
      (Ctx.collapses_boxIn_self hT _) hsτ.boxIn (Ctx.Le.refl (D.ctxAt Γ₀ τ)) φ
    rwa [WFF.mono_refl] at this
  have hsub : ∀ {L : Seq σ Γ₀ D}, (∀ p ∈ L, ¬ (k :: τ) <:+ p.1) →
      (Seq.mono hk L).map (cs₀.lf hs0 hok' hW') ⊆ L := fun hL => by
    have := cs₀.map_mono_off hs0 hok' hW' hk (fun _ => Ctx.Le.refl _) hL
    rwa [Seq.mono_self] at this
  obtain ⟨_, P⟩ := GKN.collapse hs0 P₀ hok' hW' cs₀ Δ
    (⟨τ, WFF.collapse (Ctx.collapses_boxIn_self hT _) hsτ.boxIn φ⟩ :: Θ) (hsub hv.left)
    (cons_sub e₁ (hsub fun p hp => hv.right p (List.mem_cons_of_mem _ hp)))
  -- cut `□φ` out of `TL`'s premise
  obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
    (Δ := ⟨τ, WFF.collapse (Ctx.collapses_boxIn_self hT _) hsτ.boxIn φ⟩ :: Δ)
    (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok q₁ (by wk) (List.Subset.refl _))
  exact ih hok hW τ _
    (.inl (by rw [← hw]; simp only [WFF.weight, WFF.weight_collapse]; omega)) P E

set_option maxHeartbeats 2000000 in
-- Several cuts with rearranged sides (`wk`'s `tauto`): long, not stuck.
/-- ⭐**`diaT` against `diaL`** (T, docs §12.50 item (v)): cut `◇_x φ` out of `diaL`'s premise over
    the grown tree, collapse the new child onto `x`'s identity view at `τ` (`GKN.collapse`, `x`
    opened there) and open it by `optL`; cut `◇_x φ` out of `diaT`'s premise, then cut the
    lighter identity reading. -/
theorem diaTPrin {w s : ℕ} (ih : CutIH σ Γ₀ w s) {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    {τ : Lab} {k : ℕ} {n n' m m' : ℕ} {Δ Θ : Seq σ Γ₀ D} (hT : ModalSys.T = true)
    (hO : ModalSys.Opt = true) (hsτ : (D.ctxAt Γ₀ τ).SlotsFrom 0) (x : VarSymb)
    (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X)) {φ : WFF σ ((D.ctxAt Γ₀ τ).diaIn x) 0}
    (hw : (WFF.dia x hx φ).weight = w) (hs : n + m = s) (hn : n' < n) (hm : m' < m)
    (p : GKN σ Γ₀ n D Δ (⟨τ, .dia x hx φ⟩ :: Θ)) (q : GKN σ Γ₀ m D (⟨τ, .dia x hx φ⟩ :: Δ) Θ)
    (p₁ : GKN σ Γ₀ n' D Δ (⟨τ, WFF.optx hO .ident x (hx.imp fun _ h => Ctx.witT_of hT hO h)
      (WFF.collapse (hx.elim fun _ h => Ctx.collapses_diaIn_optInT hT hO _ h) (hsτ.diaIn x) φ)⟩
        :: ⟨τ, .dia x hx φ⟩ :: Θ))
    (hv : Vacant D (k :: τ) (⟨τ, .dia x hx φ⟩ :: Δ) Θ)
    (hle : ((D.ctxAt Γ₀ τ).diaIn x).Le ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ (k :: τ)))
    (q₁ : GKN σ Γ₀ m' (D.addEdge (k :: τ) (.dia x))
      (⟨k :: τ, WFF.mono hle φ⟩ ::
        Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) (.dia x))
          (⟨τ, .dia x hx φ⟩ :: Δ))
      (Seq.mono (Tree.ctxAt_addEdge (hv.edge _ (List.suffix_refl _)) (.dia x)) Θ)) :
    ∃ k, GKN σ Γ₀ k D Δ Θ := by
  have hs0 : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
  haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨hsτ⟩
  have hc := hv.edge _ (List.suffix_refl _)
  have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc (EdgeKind.dia x)
  have hok' := hok.addEdge hc (EdgeKind.dia x)
  have hW' := hW.addEdge hc (.dia x) (fun j ρ y hj he => by
    cases hj
    cases he
    exact hx)
  have p' := weakenEdge hs0 hok p hc (.dia x)
  haveI : ((D.addEdge (k :: τ) (.dia x)).ctxAt Γ₀ τ).NoSlots :=
    ⟨Tree.ctxAt_slots hs0 hok' τ⟩
  -- cut `◇_x φ` out of `diaL`'s premise
  obtain ⟨_, Q₀⟩ := ih hok' hW' τ (WFF.mono (hk τ) (.dia x hx φ))
    (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
    (Δ := ⟨k :: τ, WFF.mono hle φ⟩ :: Seq.mono hk Δ) (Θ := Seq.mono hk Θ)
    (wkn hok' p' (by wk) (List.Subset.refl _)) (wkn hok' q₁ (by wk) (List.Subset.refl _))
  -- the new child collapsed onto `x`'s identity view at `τ`, opened there
  obtain ⟨X, hX⟩ := id hx
  have hXT : (D.ctxAt Γ₀ τ).witT x = some X := Ctx.witT_of hT hO hX
  have hkO := Tree.ctxAt_addOpen (D := D) (Γ₀ := Γ₀) τ .ident x
  have hokO := hok.addOpen (κ := .ident) hO hXT
  have hleO : ((D.ctxAt Γ₀ τ).optInK .ident x).Le ((D.addOpen τ .ident x).ctxAt Γ₀ τ) := by
    rw [Tree.ctxAt_addOpen_self]
    exact Ctx.Le.refl _
  have hop : ((D.addOpen τ .ident x).ctxAt Γ₀ τ).Opened .ident x := by
    rw [Tree.ctxAt_addOpen_self]
    exact Ctx.opened_self (κ := .ident) hXT
  have cs₀ : CSetup Γ₀ τ k idIdx (D.addEdge (k :: τ) (.dia x)) (D.addOpen τ .ident x) :=
    CSetup.ofEdge hok hT hO hv (.dia x) hokO hkO (fun _ => rfl) (fun _ _ hb => hb)
      (fun _ hb => hb) (fun y he => by cases he; exact hop)
  have h₀ := Ctx.collapses_diaIn_optInT hT hO (D.ctxAt Γ₀ τ) hX
  have e₁ : cs₀.lf hs0 hok' hW' ⟨k :: τ, WFF.mono hle φ⟩ =
      ⟨τ, WFF.mono hleO (WFF.collapse h₀ (hsτ.diaIn x) φ)⟩ := by
    rw [cs₀.lf_mk, cs₀.F_under hs0 hok' hW' (List.suffix_refl _)]
    exact LF.col_eq (cmap_idIdx_c τ k) (cdepth_c τ k) _ _ hle h₀ (hsτ.diaIn x) hleO φ
  obtain ⟨_, Q⟩ := GKN.collapse hs0 Q₀ hok' hW' cs₀
    (⟨τ, WFF.mono hleO (WFF.collapse h₀ (hsτ.diaIn x) φ)⟩ ::
      Seq.mono hkO (⟨τ, WFF.optx hO .ident x (hx.imp fun _ h => Ctx.witT_of hT hO h)
        (WFF.collapse (hx.elim fun _ h => Ctx.collapses_diaIn_optInT hT hO _ h)
          (hsτ.diaIn x) φ)⟩ :: Δ)) (Seq.mono hkO Θ)
    (cons_sub e₁ (List.subset_cons_of_subset _ (cs₀.map_mono_off hs0 hok' hW' hk hkO
      fun p hp => hv.left p (List.mem_cons_of_mem _ hp))))
    (cs₀.map_mono_off hs0 hok' hW' hk hkO hv.right)
  have E : GKN σ Γ₀ _ D (⟨τ, WFF.optx hO .ident x (hx.imp fun _ h => Ctx.witT_of hT hO h)
      (WFF.collapse (hx.elim fun _ h => Ctx.collapses_diaIn_optInT hT hO _ h)
        (hsτ.diaIn x) φ)⟩ :: Δ) Θ :=
    .optL hO τ .ident x ⟨X, hXT⟩ hleO List.mem_cons_self Q
  -- cut `◇_x φ` out of `diaT`'s premise
  obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
    (Θ := ⟨τ, WFF.optx hO .ident x (hx.imp fun _ h => Ctx.witT_of hT hO h)
      (WFF.collapse (hx.elim fun _ h => Ctx.collapses_diaIn_optInT hT hO _ h)
        (hsτ.diaIn x) φ)⟩ :: Θ)
    (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
  exact ih hok hW τ _
    (.inl (by rw [← hw]; simp only [WFF.weight, WFF.weight_collapse]; omega)) D₁ E

set_option maxHeartbeats 4000000 in
-- Each connective's reduction is several cuts with rearranged sides (`wk`'s `tauto`): long, not
-- stuck.
/-- ⭐**One step of cut elimination.** -/
theorem cut_step {w s : ℕ} (ih : CutIH σ Γ₀ w s) {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀)
    (τ : Lab) (A : WFF σ (D.ctxAt Γ₀ τ) 0) {n m : ℕ} {Δ Θ : Seq σ Γ₀ D}
    (hw : A.weight = w) (hs : n + m = s)
    (p : GKN σ Γ₀ n D Δ (⟨τ, A⟩ :: Θ)) (q : GKN σ Γ₀ m D (⟨τ, A⟩ :: Δ) Θ) :
    ∃ k, GKN σ Γ₀ k D Δ Θ := by
  have hs0 : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
  rcases permLeft ih hok hW τ A hw hs p q with done | P₁
  · exact done
  rcases permRight ih hok hW τ A hw hs P₁.not_atom p q with done | P₂
  · exact done
  cases P₁ with
  | top => cases P₂
  | @and φ ψ _ n' _ _ hn p₁ p₂ =>
      cases P₂ with
      | @and _ _ _ m' _ _ hm q₁ =>
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Θ := ⟨τ, φ⟩ :: Θ)
        (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, D₂⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Θ := ⟨τ, ψ⟩ :: Θ)
        (wkn hok p₂ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Δ := ⟨τ, φ⟩ :: ⟨τ, ψ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok q₁ (by wk) (List.Subset.refl _))
      obtain ⟨_, F⟩ := ih hok hW τ ψ (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
        (Δ := ⟨τ, φ⟩ :: Δ) (wkn hok D₂ (by wk) (List.Subset.refl _))
        (wkn hok E (by wk) (List.Subset.refl _))
      exact ih hok hW τ φ (.inl (by rw [← hw]; simp only [WFF.weight]; omega)) D₁ F
  | @or φ ψ _ n' _ _ hn p₁ =>
      cases P₂ with
      | @or _ _ _ m' _ _ hm q₁ q₂ =>
      obtain ⟨_, Pab⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Θ := ⟨τ, φ⟩ :: ⟨τ, ψ⟩ :: Θ)
        (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, Ea⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Δ := ⟨τ, φ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok q₁ (by wk) (List.Subset.refl _))
      obtain ⟨_, Eb⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Δ := ⟨τ, ψ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok q₂ (by wk) (List.Subset.refl _))
      obtain ⟨_, F⟩ := ih hok hW τ φ (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
        (Θ := ⟨τ, ψ⟩ :: Θ) Pab (wkn hok Ea (List.Subset.refl _) (by wk))
      exact ih hok hW τ ψ (.inl (by rw [← hw]; simp only [WFF.weight]; omega)) F Eb
  | @imp φ ψ _ n' _ _ hn p₁ =>
      cases P₂ with
      | @imp _ _ _ m' _ _ hm q₁ q₂ =>
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Δ := ⟨τ, φ⟩ :: Δ)
        (Θ := ⟨τ, ψ⟩ :: Θ)
        (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (by wk) (by wk))
      obtain ⟨_, D₂⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Θ := ⟨τ, φ⟩ :: Θ)
        (wkn hok p (List.Subset.refl _) (by wk)) q₁
      obtain ⟨_, D₃⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Δ := ⟨τ, ψ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok q₂ (by wk) (List.Subset.refl _))
      obtain ⟨_, F⟩ := ih hok hW τ ψ (.inl (by rw [← hw]; simp only [WFF.weight]; omega))
        (Δ := ⟨τ, φ⟩ :: Δ) D₁ (wkn hok D₃ (by wk) (List.Subset.refl _))
      exact ih hok hW τ φ (.inl (by rw [← hw]; simp only [WFF.weight]; omega)) D₂ F
  | @all hsτ u T hu φ hle _ n' _ _ hn p₁ =>
      cases P₂ with
      | @all hs' _ _ a t _ m' _ _ hm q₁ =>
      have I₁ := instance_allR hok hW (Θ := ⟨τ, _⟩ :: Θ) τ hsτ T hu hle p₁ t
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Θ := ⟨τ, WFF.instantiate hsτ t (WFF.bindFree u (hu.at τ) hsτ T φ)⟩ :: Θ)
        (wkn hok I₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Δ := ⟨τ, WFF.instantiate hs' t (WFF.bindFree u (hu.at τ) hsτ T φ)⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok q₁ (by wk) (List.Subset.refl _))
      exact ih hok hW τ _
        (.inl (by rw [← hw, WFF.weight_instantiate]; simp only [WFF.weight]; omega)) D₁ E
  | @ex hsτ T φ a t _ n' _ _ hn p₁ =>
      cases P₂ with
      | @ex hs' u _ hu φ' hle _ m' _ _ hm q₁ =>
      have I₂ := instance_exL hok hW (Δ := ⟨τ, _⟩ :: Δ) τ hs' T hu hle q₁ t
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Θ := ⟨τ, WFF.instantiate hsτ t (WFF.bindFree u (hu.at τ) hs' T φ')⟩ :: Θ)
        (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Δ := ⟨τ, WFF.instantiate hs' t (WFF.bindFree u (hu.at τ) hs' T φ')⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok I₂ (by wk) (List.Subset.refl _))
      exact ih hok hW τ _
        (.inl (by rw [← hw, WFF.weight_instantiate]; simp only [WFF.weight]; omega)) D₁ E
  | @box k φ _ n' _ _ hv hle hn p₁ =>
      cases P₂ with
      | @box k' e _ he hle' _ m' _ _ hm q₁ =>
      haveI : (D.ctxAt Γ₀ (k' :: τ)).NoSlots := ⟨Tree.ctxAt_slots hs0 hok _⟩
      have R := GKN.retargetR hs0 hok hv he (e := .box) (.of_compat trivial) hle hle' p₁
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Θ := ⟨k' :: τ, WFF.mono hle' φ⟩ :: Θ)
        (wkn hok R (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Δ := ⟨k' :: τ, WFF.mono hle' φ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok q₁ (by wk) (List.Subset.refl _))
      exact ih hok hW (k' :: τ) (WFF.mono hle' φ)
        (.inl (by rw [WFF.weight_mono, ← hw]; simp only [WFF.weight]; omega)) D₁ E
      | @T hT hsτ _ _ m' _ _ hm q₁ =>
      exact boxTPrin ih hok hW hw hs hn hm p q hv hle p₁ hT hsτ q₁
  | @dia k' e' x hx θ he hf hle _ n' _ _ hn p₁ =>
      cases P₂ with
      | @dia k _ _ _ _ m' _ _ hv hle' hm q₁ =>
      haveI : (D.ctxAt Γ₀ (k' :: τ)).NoSlots := ⟨Tree.ctxAt_slots hs0 hok _⟩
      have R := GKN.retargetL hs0 hok hv he (e := .dia x) hf hle' hle q₁
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Θ := ⟨k' :: τ, WFF.mono hle θ⟩ :: Θ)
        (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Δ := ⟨k' :: τ, WFF.mono hle θ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok R (by wk) (List.Subset.refl _))
      exact ih hok hW (k' :: τ) (WFF.mono hle θ)
        (.inl (by rw [WFF.weight_mono, ← hw]; simp only [WFF.weight]; omega)) D₁ E
  | @reopen hO κ y hy χ _ n' _ _ hn p₁ =>
      cases P₂ with
      | @opt _ _ _ _ _ hle _ m' _ _ hm q₁ =>
      haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨Tree.ctxAt_slots hs0 hok τ⟩
      have hk := Tree.ctxAt_addOpen (D := D) (Γ₀ := Γ₀) τ κ y
      have hm₀ := TMap.ofOpened hok hy
      -- the redundant opening removed
      have R₀ := GKN.relabel hs0 q₁ idIdx D hm₀ _ _ (List.Subset.refl _) (List.Subset.refl _)
      rw [Seq.relabel_cons, relabel_back (hm := hm₀) hk, relabel_back (hm := hm₀) hk] at R₀
      have e₁ : (⟨lmap idIdx τ, WFF.mono (hm₀.le τ) (WFF.mono hle (WFF.mono
          (Ctx.le_optInK _ κ y) χ))⟩ : LF σ Γ₀ D) = ⟨τ, χ⟩ := by
        rw [WFF.mono_mono, WFF.mono_mono, LF.mono_eq χ (lmap_idIdx τ) _ (Ctx.Le.refl _),
          WFF.mono_refl]
      have R := wkn hok R₀ (cons_sub e₁ (List.Subset.refl _)) (List.Subset.refl _)
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Θ := ⟨τ, χ⟩ :: Θ)
        (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩) (Δ := ⟨τ, χ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok R (by wk) (List.Subset.refl _))
      exact ih hok hW τ χ
        (.inl (by rw [← hw]; simp only [WFF.weight, WFF.weight_mono]; omega)) D₁ E
  | @fold hO k e x hx θ he hle _ n' _ _ hn p₁ =>
      cases P₂ with
      | @dia k' _ _ _ _ m' _ _ hv hle' hm q₁ =>
      haveI : (D.ctxAt Γ₀ τ).NoSlots := ⟨Tree.ctxAt_slots hs0 hok τ⟩
      haveI : (D.ctxAt Γ₀ (k :: τ)).NoSlots := ⟨Tree.ctxAt_slots hs0 hok _⟩
      obtain ⟨X, hX⟩ := id hx
      have hwc : (D.ctxAt Γ₀ (k :: τ)).wit x = some X := by
        rw [Tree.ctxAt_wit]
        unfold Tree.view
        split <;> exact Ctx.boxIn_wit.mpr ⟨hO, hX⟩
      have hkO := Tree.ctxAt_addOpen (D := D) (Γ₀ := Γ₀) (k :: τ) .arrow x
      have hokO := hok.addOpen (κ := .arrow) hO hwc
      have hmO := TMap.ofAddOpen hok hO (κ := .arrow) hwc
      have hq : (D.addOpen (k :: τ) .arrow x).edge (k :: τ) = some e := he
      have hc : (EdgeKind.dia x).Fits ((D.addOpen (k :: τ) .arrow x).ctxAt Γ₀ (k :: τ)) e := by
        refine .inr ⟨x, rfl, ?_⟩
        rw [Tree.ctxAt_addOpen_self]
        exact Ctx.opened_self (κ := .arrow) hwc
      -- the `◇_x` child onto the fold's child, `x` opened there
      have R₀ := GKN.relabel hs0 q₁ _ _ (hmO.retargetTo hv hq hc) _ _ (List.Subset.refl _)
        (List.Subset.refl _)
      rw [Seq.relabel_cons] at R₀
      have R := wkn hokO R₀
        (List.cons_subset_cons _ (retargetTo_mono_sub hmO hv hq hc hkO hv.left))
        (retargetTo_mono_sub hmO hv hq hc hkO hv.right)
      -- cut `◇_x θ` out over the opened tree
      have p' := weakenOpen hs0 hok p hO (κ := .arrow) hwc
      haveI : ((D.addOpen (k :: τ) .arrow x).ctxAt Γ₀ τ).NoSlots := ⟨Tree.ctxAt_slots hs0 hokO τ⟩
      obtain ⟨_, E₁⟩ := ih hokO (hW.addOpen _ _ _) τ (WFF.mono (hkO τ) (.dia x hx θ))
        (.inr ⟨by rw [WFF.weight_mono]; exact hw, by omega⟩)
        (Δ := ⟨lmap (setIdx idIdx τ k' k) (k' :: τ),
          WFF.mono ((hmO.retargetTo hv hq hc).le (k' :: τ)) (WFF.mono hle' θ)⟩ :: Seq.mono hkO Δ)
        (Θ := Seq.mono hkO Θ)
        (wkn hokO p' (sub_cons _ _) (by wk)) (wkn hokO R (by wk) (List.Subset.refl _))
      -- `optL` at the fold's child
      have hleO : ((D.ctxAt Γ₀ (k :: τ)).optInK .arrow x).Le
          ((D.addOpen (k :: τ) .arrow x).ctxAt Γ₀ (k :: τ)) := by
        rw [Tree.ctxAt_addOpen_self]
        exact Ctx.Le.refl _
      have eH : (⟨lmap (setIdx idIdx τ k' k) (k' :: τ),
          WFF.mono ((hmO.retargetTo hv hq hc).le (k' :: τ)) (WFF.mono hle' θ)⟩ :
            LF σ Γ₀ (D.addOpen (k :: τ) .arrow x)) =
          ⟨k :: τ, WFF.mono hleO (WFF.mono (hle.optInK .arrow x)
            (WFF.mono (hx.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h) θ))⟩ := by
        rw [WFF.mono_mono, WFF.mono_mono, WFF.mono_mono]
        exact LF.mono_eq θ (by rw [lmap_setIdx_new, lmap_idIdx]) _ _
      have E₂ : GKN σ Γ₀ _ D (⟨k :: τ, WFF.mono hle (WFF.fold hO x hx θ)⟩ :: Δ) Θ :=
        .optL hO (k :: τ) .arrow x ⟨X, hwc⟩ hleO List.mem_cons_self
          (wkn hokO E₁ (cons_sub eH (by wk)) (List.Subset.refl _))
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Θ := ⟨k :: τ, WFF.mono hle (WFF.fold hO x hx θ)⟩ :: Θ)
        (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      exact ih hok hW (k :: τ) _
        (.inl (by rw [← hw, WFF.weight_mono]; simp only [WFF.fold, WFF.weight, WFF.weight_mono]
                  omega)) D₁ E₂
  | @diaT hT hO hsτ x hx φ _ n' _ _ hn p₁ =>
      cases P₂ with
      | @dia k _ _ _ _ m' _ _ hv hle hm q₁ =>
      exact diaTPrin ih hok hW hT hO hsτ x hx hw hs hn hm p q p₁ hv hle q₁

theorem cutIH_all : ∀ w s, CutIH σ Γ₀ w s := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ihw =>
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ihs =>
      intro D hok hW τ A n m Δ Θ hlt p q
      rcases hlt with hlt | ⟨heq, hlt⟩
      · exact cut_step (ihw _ hlt (n + m)) hok hW τ A rfl rfl p q
      · exact cut_step (ihs _ hlt) hok hW τ A heq rfl p q

/-- ⭐**Cut is admissible in `GKN`** (K, KD, KT and KDT), at any node of any tree with the
    invariants, over a presented context. -/
theorem cut {n m : ℕ} {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) {Δ Θ : Seq σ Γ₀ D}
    (τ : Lab) (A : WFF σ (D.ctxAt Γ₀ τ) 0) (p : GKN σ Γ₀ n D Δ (⟨τ, A⟩ :: Θ))
    (q : GKN σ Γ₀ m D (⟨τ, A⟩ :: Δ) Θ) : ∃ k, GKN σ Γ₀ k D Δ Θ :=
  cutIH_all (A.weight + 1) 0 hok hW τ A (.inl (Nat.lt_succ_self _)) p q

end GKN

end V12M
