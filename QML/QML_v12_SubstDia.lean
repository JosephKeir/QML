import QML.QML_v12_Subst

/-!
# QML v12 — substitution under `◇_x`

The `◇` case needs the entries of the other roots moved from the target's `□` view into its `◇`
view.  The `□` view is below the `◇` view (`Ctx.le_boxIn_diaIn`), so entries move along it by
monotonicity (`SubE.mono`), keeping their fit and their indices.
-/

namespace V12

/-! ## Present leaves survive revealing -/

theorem Entry.Le.subtree_leaf {e e' : Entry} (h : e.Le e') :
    ∀ {q : List PStep} {T : VarType},
      e.subtree q = some (.leaf (some T)) → e'.subtree q = some (.leaf (some T)) := by
  induction h with
  | hide e => intro q T hq; exact absurd hq (Entry.noPresent_leaf_none q T)
  | refl e => intro q T hq; exact hq
  | node _ _ iha ihb =>
      intro q T hq
      rcases q with _ | ⟨_ | _, q⟩
      · cases hq
      · exact iha hq
      · exact ihb hq

theorem Entry.Le.mkNode_node {x x' y y' : Entry} (hx : x.Le x') (hy : y.Le y') :
    (Entry.mkNode x y).Le (.node x' y') := by
  by_cases hc : x = .leaf none ∧ y = .leaf none
  · obtain ⟨rfl, rfl⟩ := hc
    exact Entry.Le.hide _
  · rw [Entry.mkNode_of_ne hc]
    exact Entry.Le.node hx hy

/-! ## The `□` view is below the `◇` view -/

theorem Entry.le_box_dia : ∀ (q : List PStep) (e : Entry) (X : VarType),
    e.lookup q = some (.VTypeDia X) →
      ((e.refine e.forced).unbox).Le ((e.refine (e.forced.join (Pat.path q))).unboxExcept q X)
  | [], .leaf none, _, h => by cases h
  | [], .node _ _, _, h => by cases h
  | [], .leaf (some T), _, h => by
      cases T <;> cases h
      exact Entry.Le.hide _
  | _ :: _, .leaf none, _, h => by cases h
  | .fst :: q, .node a _, X, h => by
      simp only [Entry.forced, Pat.path, Pat.join, Pat.join_stop, Entry.refine, Entry.unbox,
        Entry.unboxExcept]
      exact Entry.Le.mkNode_node (Entry.le_box_dia q a X h) (Entry.Le.refl _)
  | .snd :: q, .node _ b, X, h => by
      simp only [Entry.forced, Pat.path, Pat.join, Pat.join_stop, Entry.refine, Entry.unbox,
        Entry.unboxExcept]
      exact Entry.Le.mkNode_node (Entry.Le.refl _) (Entry.le_box_dia q b X h)
  | st :: q, .leaf (some T), X, h => by
      cases T with
      | VTypeProd A B =>
          by_cases hb : (VarType.VTypeProd A B).boxy = true
          · cases st with
            | fst =>
                have h' : (Entry.leaf (some A)).lookup q = some (.VTypeDia X) := h
                simp only [Entry.forced, Entry.forcedTy, hb, if_true, Pat.path, Pat.join,
                  Pat.join_stop, Entry.refine, Entry.unbox, Entry.unboxExcept]
                exact Entry.Le.mkNode_node (Entry.le_box_dia q _ X h') (Entry.Le.refl _)
            | snd =>
                have h' : (Entry.leaf (some B)).lookup q = some (.VTypeDia X) := h
                simp only [Entry.forced, Entry.forcedTy, hb, if_true, Pat.path, Pat.join,
                  Pat.join_stop, Entry.refine, Entry.unbox, Entry.unboxExcept]
                exact Entry.Le.mkNode_node (Entry.Le.refl _) (Entry.le_box_dia q _ X h')
          · have hs : Entry.forcedTy (.VTypeProd A B) = .stop :=
              Entry.forcedTy_of_not_boxy (Bool.eq_false_iff.mpr hb)
            change (((Entry.leaf (some (.VTypeProd A B))).refine
              (Entry.forcedTy (.VTypeProd A B))).unbox).Le _
            rw [hs]
            exact Entry.Le.hide _
      | _ => cases st <;> cases h

theorem Ctx.le_boxIn_diaIn {Γ : Ctx} {x : VarSymb} {X : VarType}
    (hx : Γ.refType x = some (.VTypeDia X)) : Γ.boxIn.Le (Γ.diaIn x X) := by
  refine ⟨rfl, fun r => ?_⟩
  by_cases hr : r = x.root
  · subst hr
    have ht : (Γ.diaIn x X).tree x.root =
        ((Γ.tree x.root).refine ((Γ.tree x.root).forced.join (Pat.path x.path))).unboxExcept
          x.path X := by
      simp only [Ctx.diaIn, Ctx.dia, Ctx.refine, Ctx.forcedX, Ctx.forced, Ctx.pathPat, if_true]
    rw [ht]
    exact Entry.le_box_dia x.path _ X hx
  · have ht : (Γ.diaIn x X).tree r = ((Γ.tree r).refine (Γ.tree r).forced).unbox := by
      simp only [Ctx.diaIn, Ctx.dia, Ctx.refine, Ctx.forcedX, Ctx.forced, Ctx.pathPat, hr,
        if_false, Pat.join_stop]
    rw [ht]
    exact Entry.Le.refl _

/-! ## Monotonicity of entries -/

namespace SubE

variable {σ : Signature} {Δ₁ Δ₂ : Ctx}

def mono (h : Δ₁.Le Δ₂) : SubE σ Δ₁ → SubE σ Δ₂
  | .hide => .hide
  | .ren w => .ren w
  | .tm s => .tm (Term.mono h s)
  | .node l r => .node (mono h l) (mono h r)

theorem mono_proj (h : Δ₁.Le Δ₂) (e : SubE σ Δ₁) (st : PStep) :
    (e.mono h).proj st = (e.proj st).mono h := by
  cases e with
  | tm s => cases s <;> cases st <;> rfl
  | node l r => cases st <;> rfl
  | hide => rfl
  | ren w => rfl

theorem mono_atPath (h : Δ₁.Le Δ₂) : ∀ (e : SubE σ Δ₁) (p : List PStep),
    (e.mono h).atPath p = (e.atPath p).mono h
  | _, [] => rfl
  | e, st :: p => by
      rw [atPath_cons, atPath_cons, mono_proj]
      exact mono_atPath h _ p

theorem okLeaf_mono (h : Δ₁.Le Δ₂) {e : SubE σ Δ₁} {T : VarType} (he : e.OkLeaf T) :
    (e.mono h).OkLeaf T := by
  cases e with
  | ren w => exact (h.tree w.root).subtree_leaf he
  | tm s => exact he
  | hide => exact False.elim he
  | node _ _ => exact False.elim he

theorem ok_mono (h : Δ₁.Le Δ₂) {e : SubE σ Δ₁} {E : Entry} (he : e.Ok E) : (e.mono h).Ok E :=
  fun p T hp => by
    rw [mono_atPath]
    exact okLeaf_mono h (he p T hp)

theorem idx_mono (h : Δ₁.Le Δ₂) : ∀ (e : SubE σ Δ₁) (p : List Step), (e.mono h).idx p = e.idx p
  | .hide, _ => rfl
  | .ren _, _ => rfl
  | .tm _, _ => rfl
  | .node l _, .fst :: p => idx_mono h l p
  | .node _ r, .snd :: p => idx_mono h r p
  | .node _ _, [] => rfl
  | .node _ _, .box :: _ => rfl
  | .node _ _, .dia :: _ => rfl

end SubE

end V12
