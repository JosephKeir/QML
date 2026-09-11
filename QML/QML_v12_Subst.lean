import QML.QML_v12_Mono

/-!
# QML v12 — substitution (entries and their algebra)

A substitution `θ : Root → SubE σ Δ` sends each root of the source context to an ENTRY over the
target `Δ`: a name (`ren`), a term (`tm`), a split `node`, or nothing (`hide`).  Renaming, pair
grafting (`u₁ ↦ z.1`) and instantiation are all instances.

Entries are tree-shaped because source contexts under modal nodes are split trees; they are
projected along name paths (`SubE.atPath`) and viewed through `□` (`SubE.unbox`).
-/

namespace V12

/-- The subtree at a node path (none if the path enters a leaf). -/
def Entry.subtree : Entry → List PStep → Option Entry
  | e, [] => some e
  -- ⚠️split on the list first: with mixed patterns the matcher also splits on the step, and
  -- `(leaf o).subtree (st :: q)` would not reduce for a variable `st`
  | e, st :: q => match e, st with
    | .node a _, .fst => a.subtree q
    | .node _ b, .snd => b.subtree q
    | .leaf _, _ => none
-- ⚠️recurse on the LIST, so that `e.subtree []` reduces for a variable `e`
termination_by structural _ q => q

theorem Ctx.Sim.of_eq {Γ Γ' : Ctx} (h : Γ = Γ') : Γ.Sim Γ' := by
  subst h
  exact Ctx.Sim.refl _

inductive SubE (σ : Signature) (Δ : Ctx) : Type where
  | hide
  | ren (w : VarSymb)
  | tm {T : VarType} {a : Ann T} (s : Term σ Δ T a)
  | node (l r : SubE σ Δ)

namespace SubE

variable {σ : Signature} {Δ : Ctx}

/-- One projection of a term entry: terms are η-long, so a product term is a pair. -/
def projTm : {T : VarType} → {a : Ann T} → Term σ Δ T a → PStep → SubE σ Δ
  | _, _, .pair s _, .fst => .tm s
  | _, _, .pair _ t, .snd => .tm t
  | _, _, _, _ => .hide

def proj : SubE σ Δ → PStep → SubE σ Δ
  | .hide, _ => .hide
  | .ren w, st => .ren (.comp w st)
  | .tm s, st => projTm s st
  | .node l _, .fst => l
  | .node _ r, .snd => r

/-- The entry at a name path. -/
def atPath : SubE σ Δ → List PStep → SubE σ Δ
  | e, [] => e
  | e, st :: p => (e.proj st).atPath p

/-- A term entry seen through `□`: its box bodies (moved onto `Δ.boxIn`), through pairs. -/
def unboxTm : {T : VarType} → {a : Ann T} → Term σ Δ T a → SubE σ Δ.boxIn
  | _, _, .boxtm t hΔ _hb => .tm (Term.transport (Ctx.Sim.of_eq hΔ) t)
  | _, _, .pair s t => .node (unboxTm s) (unboxTm t)
  | _, _, _ => .hide

def unbox : SubE σ Δ → SubE σ Δ.boxIn
  | .hide => .hide
  | .ren w => .ren w
  | .tm s => unboxTm s
  | .node l r => .node l.unbox r.unbox

/-- Where an index of the source root lands. -/
def idx : SubE σ Δ → List Step → Idx
  | .ren w, p => ⟨w.root, w.path.map PStep.toStep ++ p⟩
  | .tm (a := a) _, p => a.idxAt p
  | .node l _, .fst :: p => l.idx p
  | .node _ r, .snd :: p => r.idx p
  | _, _ => ⟨.free 0, []⟩

/-- The entry fits a present source leaf of type `T`. -/
def OkLeaf : SubE σ Δ → VarType → Prop
  | .ren w, T => (Δ.tree w.root).subtree w.path = some (.leaf (some T))
  | .tm (T := U) _, T => U = T
  | _, _ => False

/-- The entry fits a source root's tree: at every present leaf. -/
def Ok (e : SubE σ Δ) (E : Entry) : Prop :=
  ∀ p T, E.subtree p = some (.leaf (some T)) → (e.atPath p).OkLeaf T

@[simp] theorem atPath_nil (e : SubE σ Δ) : e.atPath [] = e := rfl
@[simp] theorem atPath_cons (e : SubE σ Δ) (st : PStep) (p : List PStep) :
    e.atPath (st :: p) = (e.proj st).atPath p := rfl

theorem atPath_append (e : SubE σ Δ) (p q : List PStep) :
    e.atPath (p ++ q) = (e.atPath p).atPath q := by
  induction p generalizing e with
  | nil => rfl
  | cons st p ih => exact ih _

theorem ren_atPath (w : VarSymb) (p : List PStep) :
    (SubE.ren w : SubE σ Δ).atPath p = .ren (p.foldl VarSymb.comp w) := by
  induction p generalizing w with
  | nil => rfl
  | cons st p ih => exact ih _

end SubE

theorem VarSymb.root_foldl_comp (w : VarSymb) (p : List PStep) :
    (p.foldl VarSymb.comp w).root = w.root := by
  induction p generalizing w with
  | nil => rfl
  | cons st p ih => exact ih _

theorem VarSymb.path_foldl_comp (w : VarSymb) (p : List PStep) :
    (p.foldl VarSymb.comp w).path = w.path ++ p := by
  induction p generalizing w with
  | nil => simp
  | cons st p ih => rw [List.foldl_cons, ih]; simp [VarSymb.path]

/-- A substitution from `Γ` into `Δ`. -/
abbrev Subst (σ : Signature) (Δ : Ctx) := Root → SubE σ Δ

def Subst.Ok {σ : Signature} {Δ : Ctx} (θ : Subst σ Δ) (Γ : Ctx) : Prop :=
  ∀ r, (θ r).Ok (Γ.tree r)

def Subst.idx {σ : Signature} {Δ : Ctx} (θ : Subst σ Δ) (i : Idx) : Idx := (θ i.root).idx i.path

def Subst.unbox {σ : Signature} {Δ : Ctx} (θ : Subst σ Δ) : Subst σ Δ.boxIn :=
  fun r => (θ r).unbox

/-! ## Subtrees and lookups -/

theorem Entry.subtree_append : ∀ (e : Entry) (p q : List PStep),
    e.subtree (p ++ q) = (e.subtree p).bind (fun e' => e'.subtree q)
  | e, [], q => by rw [List.nil_append]; rfl
  | .node a _, .fst :: p, q => Entry.subtree_append a p q
  | .node _ b, .snd :: p, q => Entry.subtree_append b p q
  | .leaf _, _ :: _, _ => rfl

/-- A lookup goes through split nodes to a present leaf, then into the leaf's type. -/
theorem Entry.lookup_split : ∀ (e : Entry) (p : List PStep) (T : VarType),
    e.lookup p = some T →
      ∃ p₁ p₂ U, p = p₁ ++ p₂ ∧ e.subtree p₁ = some (.leaf (some U)) ∧ U.follow p₂ = some T
  | .leaf none, _, _, h => by cases h
  | .leaf (some U), p, _, h => ⟨[], p, U, rfl, rfl, h⟩
  | .node _ _, [], _, h => by cases h
  | .node a _, .fst :: p, T, h => by
      obtain ⟨p₁, p₂, U, rfl, h1, h2⟩ := Entry.lookup_split a p T h
      exact ⟨.fst :: p₁, p₂, U, rfl, h1, h2⟩
  | .node _ b, .snd :: p, T, h => by
      obtain ⟨p₁, p₂, U, rfl, h1, h2⟩ := Entry.lookup_split b p T h
      exact ⟨.snd :: p₁, p₂, U, rfl, h1, h2⟩

theorem Entry.lookup_of_subtree : ∀ (e : Entry) (q p : List PStep) (U T : VarType),
    e.subtree q = some (.leaf (some U)) → U.follow p = some T → e.lookup (q ++ p) = some T
  | .leaf _, [], _, _, _, h, hf => by cases h; exact hf
  | .leaf _, _ :: _, _, _, _, h, _ => by cases h
  | .node _ _, [], _, _, _, h, _ => by cases h
  | .node a _, .fst :: q, p, U, T, h, hf => Entry.lookup_of_subtree a q p U T h hf
  | .node _ b, .snd :: q, p, U, T, h, hf => Entry.lookup_of_subtree b q p U T h hf

namespace SubE

variable {σ : Signature} {Δ : Ctx}

/-- The entry has plain type `T` in the target (a name may point inside an unsplit leaf). -/
def OkRef : SubE σ Δ → VarType → Prop
  | .ren w, T => Δ.refType w = some T
  | .tm (T := U) _, T => U = T
  | _, _ => False

theorem okRef_tm_atPath (p : List PStep) : ∀ {U T : VarType} {a : Ann U} (s : Term σ Δ U a),
    U.follow p = some T → ((SubE.tm s).atPath p).OkRef T := by
  induction p with
  | nil => intro U T a s h; cases U <;> cases h <;> rfl
  | cons st p ih => intro U T a s h; cases st <;> cases s <;> first | exact ih _ h | cases h

/-- A base-typed entry, as a term. -/
def toVar : (e : SubE σ Δ) → e.OkRef .Var → Term σ Δ .Var .var
  | .ren w, h => .var w h
  | .tm (.var v hv), _ => .var v hv
  | .tm (.func f), _ => .func f
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _t _hΔ _hb), h => nomatch h
  | .tm (.diatm _x _X _hx _t _hΔ _hb), h => nomatch h
  | .hide, h => False.elim h
  | .node _ _, h => False.elim h

end SubE

/-- ⭐An `Ok` substitution fits every lookup of the source. -/
theorem Subst.okRef {σ : Signature} {Δ : Ctx} {θ : Subst σ Δ} {Γ : Ctx} (hθ : θ.Ok Γ)
    {v : VarSymb} {T : VarType} (hv : Γ.refType v = some T) :
    ((θ v.root).atPath v.path).OkRef T := by
  obtain ⟨p₁, p₂, U, hp, h1, h2⟩ := Entry.lookup_split _ _ _ hv
  have hleaf := hθ v.root p₁ U h1
  rw [hp, SubE.atPath_append]
  generalize (θ v.root).atPath p₁ = e at hleaf ⊢
  cases e with
  | hide => exact False.elim hleaf
  | ren w =>
      rw [SubE.ren_atPath]
      change Δ.refType _ = some T
      simp only [Ctx.refType, VarSymb.root_foldl_comp, VarSymb.path_foldl_comp]
      exact Entry.lookup_of_subtree _ _ _ _ _ hleaf h2
  | tm s =>
      have hU : _ = U := hleaf
      subst hU
      exact SubE.okRef_tm_atPath p₂ s h2
  | node _ _ => exact False.elim hleaf

/-! ## Present leaves -/

def Entry.NoPresent (E : Entry) : Prop := ∀ p T, E.subtree p ≠ some (.leaf (some T))

theorem Entry.noPresent_of_leaf_none : ∀ {q : List PStep} {V : Entry},
    (Entry.leaf none).subtree q = some V → V.NoPresent
  | [], _, h => by
      cases h
      intro p T hp
      cases p with
      | nil => cases hp
      | cons _ _ => cases hp
  | _ :: _, _, h => by cases h

theorem Entry.noPresent_leaf_none : (Entry.leaf none).NoPresent :=
  Entry.noPresent_of_leaf_none (q := []) rfl

theorem Entry.NoPresent.node {E₁ E₂ : Entry} (h : (Entry.node E₁ E₂).NoPresent) :
    E₁.NoPresent ∧ E₂.NoPresent :=
  ⟨fun p T hp => h (.fst :: p) T hp, fun p T hp => h (.snd :: p) T hp⟩

theorem Entry.noPresent_node {E₁ E₂ : Entry} (h₁ : E₁.NoPresent) (h₂ : E₂.NoPresent) :
    (Entry.node E₁ E₂).NoPresent := by
  intro p T hp
  rcases p with _ | ⟨_ | _, p⟩
  · cases hp
  · exact h₁ p T hp
  · exact h₂ p T hp

theorem Entry.noPresent_mkNode {E₁ E₂ : Entry} (h₁ : E₁.NoPresent) (h₂ : E₂.NoPresent) :
    (Entry.mkNode E₁ E₂).NoPresent := by
  by_cases hc : E₁ = .leaf none ∧ E₂ = .leaf none
  · obtain ⟨rfl, rfl⟩ := hc
    exact Entry.noPresent_leaf_none
  · rw [Entry.mkNode_of_ne hc]
    exact Entry.noPresent_node h₁ h₂

theorem Entry.noPresent_boxView : ∀ (E : Entry), E.NoPresent →
    ((E.refine E.forced).unbox).NoPresent
  | .leaf none, _ => Entry.noPresent_leaf_none
  | .leaf (some T), h => (h [] T rfl).elim
  | .node E₁ E₂, h => Entry.noPresent_mkNode (Entry.noPresent_boxView E₁ h.node.1)
      (Entry.noPresent_boxView E₂ h.node.2)

/-- The subtree of a `□` view is the view of the subtree, unless the view hides it entirely. -/
theorem Entry.subtree_boxView : ∀ (q : List PStep) (e E : Entry), e.subtree q = some E →
    ((e.refine e.forced).unbox).subtree q = some ((E.refine E.forced).unbox) ∨
      ((E.refine E.forced).unbox).NoPresent
  | [], _, _, h => by cases h; exact Or.inl rfl
  | _ :: _, .leaf _, _, h => by cases h
  | .fst :: q, .node a b, E, h => by
      rcases Entry.subtree_boxView q a E h with h' | h'
      · by_cases hc : (a.refine a.forced).unbox = .leaf none ∧
            (b.refine b.forced).unbox = .leaf none
        · right
          rw [hc.1] at h'
          exact Entry.noPresent_of_leaf_none h'
        · left
          change (Entry.mkNode _ _).subtree (.fst :: q) = _
          rw [Entry.mkNode_of_ne hc]
          exact h'
      · exact Or.inr h'
  | .snd :: q, .node a b, E, h => by
      rcases Entry.subtree_boxView q b E h with h' | h'
      · by_cases hc : (a.refine a.forced).unbox = .leaf none ∧
            (b.refine b.forced).unbox = .leaf none
        · right
          rw [hc.2] at h'
          exact Entry.noPresent_of_leaf_none h'
        · left
          change (Entry.mkNode _ _).subtree (.snd :: q) = _
          rw [Entry.mkNode_of_ne hc]
          exact h'
      · exact Or.inr h'

/-! ## The `Ok` condition, structurally -/

namespace SubE

variable {σ : Signature} {Δ : Ctx}

theorem ok_of_noPresent {e : SubE σ Δ} {E : Entry} (hE : E.NoPresent) : e.Ok E :=
  fun p T hp => absurd hp (hE p T)

theorem ok_node {e : SubE σ Δ} {E₁ E₂ : Entry} :
    e.Ok (.node E₁ E₂) ↔ (e.proj .fst).Ok E₁ ∧ (e.proj .snd).Ok E₂ := by
  constructor
  · intro h
    exact ⟨fun p T hp => h (.fst :: p) T hp, fun p T hp => h (.snd :: p) T hp⟩
  · rintro ⟨h₁, h₂⟩ p T hp
    rcases p with _ | ⟨_ | _, p⟩
    · cases hp
    · exact h₁ p T hp
    · exact h₂ p T hp

theorem ok_leaf {e : SubE σ Δ} {U : VarType} : e.Ok (.leaf (some U)) ↔ e.OkLeaf U := by
  constructor
  · intro h
    exact h [] U rfl
  · intro h p T hp
    rcases p with _ | ⟨_, p⟩
    · cases hp
      exact h
    · cases hp

theorem ok_mkNode {e : SubE σ Δ} {E₁ E₂ : Entry} (h₁ : (e.proj .fst).Ok E₁)
    (h₂ : (e.proj .snd).Ok E₂) : e.Ok (Entry.mkNode E₁ E₂) := by
  by_cases hc : E₁ = .leaf none ∧ E₂ = .leaf none
  · obtain ⟨rfl, rfl⟩ := hc
    exact ok_of_noPresent Entry.noPresent_leaf_none
  · rw [Entry.mkNode_of_ne hc]
    exact ok_node.mpr ⟨h₁, h₂⟩

theorem ok_ren {w : VarSymb} {E : Entry} (h : (Δ.tree w.root).subtree w.path = some E) :
    (SubE.ren w : SubE σ Δ).Ok E := by
  intro p T hp
  rw [ren_atPath]
  change (Δ.tree (p.foldl VarSymb.comp w).root).subtree (p.foldl VarSymb.comp w).path = _
  rw [VarSymb.root_foldl_comp, VarSymb.path_foldl_comp, Entry.subtree_append, h]
  exact hp

theorem hide_atPath : ∀ (p : List PStep), (SubE.hide : SubE σ Δ).atPath p = .hide
  | [] => rfl
  | _ :: p => hide_atPath p

theorem noPresent_of_ok_hide {E : Entry} (h : (SubE.hide : SubE σ Δ).Ok E) : E.NoPresent := by
  intro p T hp
  have h' := h p T hp
  rw [hide_atPath] at h'
  exact h'

theorem ok_unboxTm (U : VarType) : ∀ {a : Ann U} (s : Term σ Δ U a),
    (SubE.unboxTm s).Ok (((Entry.leaf (some U)).refine (Entry.forcedTy U)).unbox) := by
  induction U with
  | Var => intro a s; exact ok_of_noPresent Entry.noPresent_leaf_none
  | VTypeOne => intro a s; exact ok_of_noPresent Entry.noPresent_leaf_none
  | VTypeDia X _ => intro a s; exact ok_of_noPresent Entry.noPresent_leaf_none
  | VTypeBox A _ =>
      intro a s
      cases s
      exact ok_leaf.mpr rfl
  | VTypeProd A B ihA ihB =>
      intro a s
      cases s with
      | pair s₁ s₂ =>
          by_cases hb : (VarType.VTypeProd A B).boxy = true
          · simp only [Entry.forcedTy, hb, if_true, Entry.refine, Entry.unbox]
            exact ok_mkNode (ihA s₁) (ihB s₂)
          · rw [Entry.forcedTy_of_not_boxy (Bool.eq_false_iff.mpr hb)]
            exact ok_of_noPresent Entry.noPresent_leaf_none

/-- ⭐Seen through `□`, an entry that fits a source tree fits its view. -/
theorem ok_unbox : ∀ (E : Entry) (e : SubE σ Δ), e.Ok E → e.unbox.Ok ((E.refine E.forced).unbox)
  | .leaf none, _, _ => ok_of_noPresent Entry.noPresent_leaf_none
  | .leaf (some U), e, h => by
      have hl := ok_leaf.mp h
      cases e with
      | hide => exact False.elim hl
      | node _ _ => exact False.elim hl
      | ren w =>
          rcases Entry.subtree_boxView w.path (Δ.tree w.root) _ hl with h' | h'
          · exact ok_ren h'
          · exact ok_of_noPresent h'
      | tm s =>
          have hU : _ = U := hl
          subst hU
          exact ok_unboxTm _ s
  | .node E₁ E₂, e, h => by
      obtain ⟨h₁, h₂⟩ := ok_node.mp h
      cases e with
      | hide =>
          exact ok_of_noPresent (Entry.noPresent_boxView _ (noPresent_of_ok_hide h))
      | ren w => exact ok_mkNode (ok_unbox E₁ _ h₁) (ok_unbox E₂ _ h₂)
      | node l r => exact ok_mkNode (ok_unbox E₁ l h₁) (ok_unbox E₂ r h₂)
      | tm s =>
          cases s with
          | pair s₁ s₂ => exact ok_mkNode (ok_unbox E₁ _ h₁) (ok_unbox E₂ _ h₂)
          | _ =>
              exact ok_of_noPresent (Entry.noPresent_boxView _
                (Entry.noPresent_node (noPresent_of_ok_hide h₁) (noPresent_of_ok_hide h₂)))

end SubE

theorem Subst.ok_unbox {σ : Signature} {Δ : Ctx} {θ : Subst σ Δ} {Γ : Ctx} (hθ : θ.Ok Γ) :
    θ.unbox.Ok Γ.boxIn :=
  fun r => SubE.ok_unbox (Γ.tree r) (θ r) (hθ r)

end V12
