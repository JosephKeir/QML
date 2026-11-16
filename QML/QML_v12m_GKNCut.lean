import QML.QML_v12m_GKNSubst
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

K and KD, `Opt` off; the trees carry `Tree.OK` and `Tree.WitOK`, over a presented context.
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
  ok := h.addEdge c e
  edge c' e' he' := by
    refine ⟨e', ?_, EdgeKind.compat_refl e'⟩
    rw [lmap_idIdx, Tree.edge_addEdge, if_neg (fun h => by rw [h, hc] at he'; cases he')]
    exact he'
  birth τ b hb := by rw [lmap_idIdx]; exact hb
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

theorem Vacant.sub {D : Tree} {c : Lab} {Δ Θ Δ' Θ' : Seq σ Γ₀ D} (hv : Vacant D c Δ Θ)
    (hΔ : Δ' ⊆ Δ) (hΘ : Θ' ⊆ Θ) : Vacant D c Δ' Θ' :=
  ⟨hv.edge, hv.births, fun p hp => hv.left p (hΔ hp), fun p hp => hv.right p (hΘ hp)⟩

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
  | dia (k : ℕ) (x : VarSymb) (hx : ∃ X, (D.ctxAt Γ₀ τ).ref x = some (.VTypeDia X))
      {θ : WFF σ ((D.ctxAt Γ₀ τ).diaIn x) 0} (he : D.edge (k :: τ) = some (.dia x))
      (hle : ((D.ctxAt Γ₀ τ).diaIn x).Le (D.ctxAt Γ₀ (k :: τ))) {n n' : ℕ}
      {Δ Θ : Seq σ Γ₀ D} : n' < n →
      GKN σ Γ₀ n' D Δ (⟨k :: τ, WFF.mono hle θ⟩ :: ⟨τ, .dia x hx θ⟩ :: Θ) →
      RightPrin σ Γ₀ D τ (.dia x hx θ) n Δ Θ

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

variable [ModalSys.NoOpt] [Γ₀.Presented]

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
  | @diaR n' _ _ _ τ' k x hx θ he hle h p₁ =>
      rcases List.mem_cons.mp h with he' | h
      · cases he'
        exact .inr (.dia k x hx he hle (Nat.lt_succ_self _) p₁)
      · obtain ⟨k', d⟩ := upL ih hok hW hw (by omega) q (List.Subset.refl _)
          (sub_cons ⟨k :: τ', WFF.mono hle θ⟩ Θ) p₁ (by wk)
        exact .inl ⟨k' + 1, .diaR τ' k x hx he hle h d⟩
  | @boxR n' _ _ _ τ' k φ hv hle h p₁ =>
      rcases List.mem_cons.mp h with he | h
      · cases he
        exact .inr (.box k hv hle (Nat.lt_succ_self _) p₁)
      · have hc := hv.edge _ (List.suffix_refl _)
        have hk := Tree.ctxAt_addEdge (Γ₀ := Γ₀) hc EdgeKind.box
        have hok' := hok.addEdge (k :: τ') EdgeKind.box
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
      have hok' := hok.addEdge (k :: τ') EdgeKind.box
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
      have hok' := hok.addEdge (k :: τ') (EdgeKind.dia x)
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
  | @diaR m' _ _ _ τ' k x hx θ he hle h q₁ =>
      obtain ⟨k', d⟩ := upR ih hok hW hw (by omega) p (List.Subset.refl _) (sub_cons _ _) q₁
        (List.Subset.refl _)
      exact .inl ⟨k' + 1, .diaR τ' k x hx he hle h d⟩
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
      have hok' := hok.addEdge (k :: τ') EdgeKind.box
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
      have hok' := hok.addEdge (k :: τ') EdgeKind.box
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
        have hok' := hok.addEdge (k :: τ') (EdgeKind.dia x)
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
      have R := GKN.retargetR hs0 hok hv he (e := .box) trivial hle hle' p₁
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Θ := ⟨k' :: τ, WFF.mono hle' φ⟩ :: Θ)
        (wkn hok R (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Δ := ⟨k' :: τ, WFF.mono hle' φ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok q₁ (by wk) (List.Subset.refl _))
      exact ih hok hW (k' :: τ) (WFF.mono hle' φ)
        (.inl (by rw [WFF.weight_mono, ← hw]; simp only [WFF.weight]; omega)) D₁ E
  | @dia k' x hx θ he hle _ n' _ _ hn p₁ =>
      cases P₂ with
      | @dia k _ _ _ _ m' _ _ hv hle' hm q₁ =>
      haveI : (D.ctxAt Γ₀ (k' :: τ)).NoSlots := ⟨Tree.ctxAt_slots hs0 hok _⟩
      have R := GKN.retargetL hs0 hok hv he (e := .dia x) rfl hle' hle q₁
      obtain ⟨_, D₁⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Θ := ⟨k' :: τ, WFF.mono hle θ⟩ :: Θ)
        (wkn hok p₁ (List.Subset.refl _) (by wk)) (wkn hok q (List.Subset.refl _) (by wk))
      obtain ⟨_, E⟩ := ih hok hW τ _ (.inr ⟨hw, by omega⟩)
        (Δ := ⟨k' :: τ, WFF.mono hle θ⟩ :: Δ)
        (wkn hok p (by wk) (List.Subset.refl _)) (wkn hok R (by wk) (List.Subset.refl _))
      exact ih hok hW (k' :: τ) (WFF.mono hle θ)
        (.inl (by rw [WFF.weight_mono, ← hw]; simp only [WFF.weight]; omega)) D₁ E

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

/-- ⭐**Cut is admissible in `GKN`** (K and KD), at any node of any tree with the invariants,
    over a presented context. -/
theorem cut {n m : ℕ} {D : Tree} (hok : D.OK Γ₀) (hW : D.WitOK Γ₀) {Δ Θ : Seq σ Γ₀ D}
    (τ : Lab) (A : WFF σ (D.ctxAt Γ₀ τ) 0) (p : GKN σ Γ₀ n D Δ (⟨τ, A⟩ :: Θ))
    (q : GKN σ Γ₀ m D (⟨τ, A⟩ :: Δ) Θ) : ∃ k, GKN σ Γ₀ k D Δ Θ :=
  cutIH_all (A.weight + 1) 0 hok hW τ A (.inl (Nat.lt_succ_self _)) p q

end GKN

end V12M
