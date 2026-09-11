import QML.QML_v12_Terms

/-!
# QML v12 — scoping of annotations

Every index in a term's annotation points at a `◇`-node of a PRESENT leaf of its context
(`Term.scoped`).  Substitution needs this: its index maps commute with the modal out-maps only on
indices in scope.
-/

namespace V12

/-- The path reaches a `◇`-node: through split nodes, then through a present leaf's type. -/
def Entry.DiaAt : Entry → List Step → Prop
  | .node a _, .fst :: p => a.DiaAt p
  | .node _ b, .snd :: p => b.DiaAt p
  | .node _ _, _ => False
  | .leaf (some T), p => T.DiaAt p
  | .leaf none, _ => False

theorem VarType.diaAt_of_follow : ∀ (q : List PStep) (T X : VarType),
    T.follow q = some (.VTypeDia X) → T.DiaAt (q.map PStep.toStep)
  | [], T, X, h => by
      simp only [VarType.follow, Option.some.injEq] at h
      subst h
      trivial
  | s :: q, T, X, h => by
      cases T <;> cases s <;> first | exact VarType.diaAt_of_follow q _ X h | cases h

theorem Entry.diaAt_of_lookup : ∀ (q : List PStep) (e : Entry) (X : VarType),
    e.lookup q = some (.VTypeDia X) → e.DiaAt (q.map PStep.toStep)
  | _, .leaf none, _, h => by cases h
  | q, .leaf (some T), X, h => VarType.diaAt_of_follow q T X h
  | [], .node _ _, _, h => by cases h
  | .fst :: q, .node a _, X, h => Entry.diaAt_of_lookup q a X h
  | .snd :: q, .node _ b, X, h => Entry.diaAt_of_lookup q b X h

theorem Entry.mkNode_of_diaAt {a b : Entry} {p : List Step} (h : (Entry.mkNode a b).DiaAt p) :
    Entry.mkNode a b = .node a b := by
  rcases a with ⟨_ | _⟩ | ⟨_, _⟩ <;> rcases b with ⟨_ | _⟩ | ⟨_, _⟩ <;>
    first | rfl | exact False.elim h

/-! ## The `□` view -/

theorem Entry.diaAt_boxView_leaf : ∀ (T : VarType) (s : List PStep → Step), (∀ q, s q = .box) →
    ∀ p, ((Entry.leaf (some T)).refine (Entry.forcedTy T)).unbox.DiaAt p →
      (Entry.leaf (some T)).DiaAt
        (((Entry.leaf (some T)).refine (Entry.forcedTy T)).unbox.outPath s p) := by
  intro T
  induction T with
  | Var => intro s _ p h; exact False.elim h
  | VTypeOne => intro s _ p h; exact False.elim h
  | VTypeDia X _ => intro s _ p h; exact False.elim h
  | VTypeBox X _ =>
      intro s hs p h
      change VarType.DiaAt (.VTypeBox X) (s [] :: p)
      rw [hs]
      exact h
  | VTypeProd A B ihA ihB =>
      intro s hs p h
      by_cases hb : (VarType.VTypeProd A B).boxy = true
      · simp only [Entry.forcedTy, hb, if_true, Entry.refine, Entry.unbox] at h ⊢
        have hn := Entry.mkNode_of_diaAt h
        rw [hn] at h ⊢
        rcases p with _ | ⟨_ | _ | _ | _, p⟩
        · exact False.elim h
        · exact ihA _ (fun _ => hs _) p h
        · exact ihB _ (fun _ => hs _) p h
        · exact False.elim h
        · exact False.elim h
      · rw [Entry.forcedTy_of_not_boxy (Bool.eq_false_iff.mpr hb)] at h
        exact False.elim h

/-- ⭐Out of a `□`, an index in scope inside stays in scope. -/
theorem Entry.diaAt_boxView : ∀ (e : Entry) (s : List PStep → Step), (∀ q, s q = .box) →
    ∀ p, (e.refine e.forced).unbox.DiaAt p → e.DiaAt ((e.refine e.forced).unbox.outPath s p)
  | .leaf none, _, _, _, h => False.elim h
  | .leaf (some T), s, hs, p, h => Entry.diaAt_boxView_leaf T s hs p h
  | .node a b, s, hs, p, h => by
      change (Entry.mkNode (a.refine a.forced).unbox (b.refine b.forced).unbox).DiaAt p at h
      change (Entry.node a b).DiaAt
        ((Entry.mkNode (a.refine a.forced).unbox (b.refine b.forced).unbox).outPath s p)
      have hn := Entry.mkNode_of_diaAt h
      rw [hn] at h ⊢
      rcases p with _ | ⟨_ | _ | _ | _, p⟩
      · exact False.elim h
      · exact Entry.diaAt_boxView a _ (fun _ => hs _) p h
      · exact Entry.diaAt_boxView b _ (fun _ => hs _) p h
      · exact False.elim h
      · exact False.elim h

/-! ## The `◇_x` view, at the witness root -/

/-- ⭐Out of a `◇_x`, an index in scope inside stays in scope: a `◇`-step into the witness leaf, a
    `□`-step into every other leaf. -/
theorem Entry.diaAt_diaView : ∀ (q : List PStep) (e : Entry) (X : VarType)
    (s : List PStep → Step), s q = .dia → (∀ q', q' ≠ q → s q' = .box) →
    e.lookup q = some (.VTypeDia X) →
    ∀ p, ((e.refine (e.forced.join (Pat.path q))).unboxExcept q X).DiaAt p →
      e.DiaAt (((e.refine (e.forced.join (Pat.path q))).unboxExcept q X).outPath s p)
  | [], .leaf none, _, _, _, _, hl => by cases hl
  | [], .node _ _, _, _, _, _, hl => by cases hl
  | [], .leaf (some T), X, s, hs0, _, hl => by
      cases T <;> cases hl
      intro p h
      change VarType.DiaAt (.VTypeDia _) (s [] :: p)
      rw [hs0]
      exact h
  | _ :: _, .leaf none, _, _, _, _, hl => by cases hl
  | .fst :: q, .node a b, X, s, hs0, hsb, hl => by
      intro p h
      simp only [Entry.forced, Pat.path, Pat.join, Pat.join_stop, Entry.refine,
        Entry.unboxExcept] at h ⊢
      rcases p with _ | ⟨_ | _ | _ | _, p⟩
      · exact False.elim h
      · exact Entry.diaAt_diaView q a X (fun q' => s (.fst :: q')) hs0
          (fun q' hq' => hsb _ (fun he => hq' (List.cons.inj he).2)) hl p h
      · exact Entry.diaAt_boxView b (fun q' => s (.snd :: q'))
          (fun q' => hsb _ (fun he => by cases he)) p h
      · exact False.elim h
      · exact False.elim h
  | .snd :: q, .node a b, X, s, hs0, hsb, hl => by
      intro p h
      simp only [Entry.forced, Pat.path, Pat.join, Pat.join_stop, Entry.refine,
        Entry.unboxExcept] at h ⊢
      rcases p with _ | ⟨_ | _ | _ | _, p⟩
      · exact False.elim h
      · exact Entry.diaAt_boxView a (fun q' => s (.fst :: q'))
          (fun q' => hsb _ (fun he => by cases he)) p h
      · exact Entry.diaAt_diaView q b X (fun q' => s (.snd :: q')) hs0
          (fun q' hq' => hsb _ (fun he => hq' (List.cons.inj he).2)) hl p h
      · exact False.elim h
      · exact False.elim h
  | st :: q, .leaf (some T), X, s, hs0, hsb, hl => by
      intro p h
      cases T with
      | VTypeProd A B =>
          by_cases hb : (VarType.VTypeProd A B).boxy = true
          · cases st with
            | fst =>
                have hsnd : ∀ q', s (.snd :: q') = .box := fun q' => hsb _ (fun he => by cases he)
                have hl' : (Entry.leaf (some A)).lookup q = some (.VTypeDia X) := hl
                simp only [Entry.forced, Entry.forcedTy, hb, if_true, Pat.path, Pat.join,
                  Pat.join_stop, Entry.refine, Entry.unboxExcept] at h ⊢
                rcases p with _ | ⟨_ | _ | _ | _, p⟩
                · exact False.elim h
                · exact Entry.diaAt_diaView q (.leaf (some A)) X (fun q' => s (.fst :: q')) hs0
                    (fun q' hq' => hsb _ (fun he => hq' (List.cons.inj he).2)) hl' p h
                · exact Entry.diaAt_boxView_leaf B _ hsnd p h
                · exact False.elim h
                · exact False.elim h
            | snd =>
                have hfst : ∀ q', s (.fst :: q') = .box := fun q' => hsb _ (fun he => by cases he)
                have hl' : (Entry.leaf (some B)).lookup q = some (.VTypeDia X) := hl
                simp only [Entry.forced, Entry.forcedTy, hb, if_true, Pat.path, Pat.join,
                  Pat.join_stop, Entry.refine, Entry.unboxExcept] at h ⊢
                rcases p with _ | ⟨_ | _ | _ | _, p⟩
                · exact False.elim h
                · exact Entry.diaAt_boxView_leaf A _ hfst p h
                · exact Entry.diaAt_diaView q (.leaf (some B)) X (fun q' => s (.snd :: q')) hs0
                    (fun q' hq' => hsb _ (fun he => hq' (List.cons.inj he).2)) hl' p h
                · exact False.elim h
                · exact False.elim h
          · have hb' := Bool.eq_false_iff.mpr hb
            have hAB : A.boxy = false ∧ B.boxy = false := by
              simpa only [VarType.boxy, Bool.or_eq_false_iff] using hb'
            have hfA := Entry.forcedTy_of_not_boxy hAB.1
            have hfB := Entry.forcedTy_of_not_boxy hAB.2
            cases st with
            | fst =>
                have hsnd : ∀ q', s (.snd :: q') = .box := fun q' => hsb _ (fun he => by cases he)
                have hl' : (Entry.leaf (some A)).lookup q = some (.VTypeDia X) := hl
                simp only [Entry.forced, Entry.forcedTy_of_not_boxy hb', Pat.path, Pat.join,
                  Entry.refine, Entry.unboxExcept] at h ⊢
                rcases p with _ | ⟨_ | _ | _ | _, p⟩
                · exact False.elim h
                · have key := Entry.diaAt_diaView q (.leaf (some A)) X (fun q' => s (.fst :: q'))
                    hs0 (fun q' hq' => hsb _ (fun he => hq' (List.cons.inj he).2)) hl' p
                    (by simp only [Entry.forced, hfA, Pat.join]; exact h)
                  simp only [Entry.forced, hfA, Pat.join] at key
                  exact key
                · have key := Entry.diaAt_boxView_leaf B _ hsnd p (by rw [hfB]; exact h)
                  rw [hfB] at key
                  exact key
                · exact False.elim h
                · exact False.elim h
            | snd =>
                have hfst : ∀ q', s (.fst :: q') = .box := fun q' => hsb _ (fun he => by cases he)
                have hl' : (Entry.leaf (some B)).lookup q = some (.VTypeDia X) := hl
                simp only [Entry.forced, Entry.forcedTy_of_not_boxy hb', Pat.path, Pat.join,
                  Entry.refine, Entry.unboxExcept] at h ⊢
                rcases p with _ | ⟨_ | _ | _ | _, p⟩
                · exact False.elim h
                · have key := Entry.diaAt_boxView_leaf A _ hfst p (by rw [hfA]; exact h)
                  rw [hfA] at key
                  exact key
                · have key := Entry.diaAt_diaView q (.leaf (some B)) X (fun q' => s (.snd :: q'))
                    hs0 (fun q' hq' => hsb _ (fun he => hq' (List.cons.inj he).2)) hl' p
                    (by simp only [Entry.forced, hfB, Pat.join]; exact h)
                  simp only [Entry.forced, hfB, Pat.join] at key
                  exact key
                · exact False.elim h
                · exact False.elim h
      | _ => cases st <;> cases hl

/-! ## Contexts and terms -/

theorem Ctx.diaAt_boxOut {Γ : Ctx} {i : Idx} (h : (Γ.boxIn.tree i.root).DiaAt i.path) :
    (Γ.tree (Γ.boxIn.boxOut i).root).DiaAt (Γ.boxIn.boxOut i).path :=
  Entry.diaAt_boxView (Γ.tree i.root) _ (fun _ => rfl) i.path h

theorem Ctx.diaAt_diaOut {Γ : Ctx} {x : VarSymb} {X : VarType}
    (hx : Γ.refType x = some (.VTypeDia X)) {i : Idx}
    (h : ((Γ.diaIn x X).tree i.root).DiaAt i.path) :
    (Γ.tree ((Γ.diaIn x X).diaOut x i).root).DiaAt ((Γ.diaIn x X).diaOut x i).path := by
  obtain ⟨r, p⟩ := i
  change ((Γ.diaIn x X).tree r).DiaAt p at h
  change (Γ.tree r).DiaAt (((Γ.diaIn x X).tree r).outPath
    (fun q => if r = x.root ∧ q = x.path then .dia else .box) p)
  by_cases hr : r = x.root
  · subst hr
    have ht : (Γ.diaIn x X).tree x.root =
        ((Γ.tree x.root).refine ((Γ.tree x.root).forced.join (Pat.path x.path))).unboxExcept
          x.path X := by
      simp only [Ctx.diaIn, Ctx.dia, Ctx.refine, Ctx.forcedX, Ctx.forced, Ctx.pathPat, if_true]
    rw [ht] at h ⊢
    exact Entry.diaAt_diaView x.path _ X _ (if_pos ⟨rfl, rfl⟩)
      (fun q hq => if_neg (fun hc => hq hc.2)) hx p h
  · have ht : (Γ.diaIn x X).tree r = ((Γ.tree r).refine (Γ.tree r).forced).unbox := by
      simp only [Ctx.diaIn, Ctx.dia, Ctx.refine, Ctx.forcedX, Ctx.forced, Ctx.pathPat, hr,
        if_false, Pat.join_stop]
    rw [ht] at h ⊢
    exact Entry.diaAt_boxView _ _ (fun q => if_neg (fun hc => hr hc.1)) p h

/-- ⭐**Scoping**: every index in a term's annotation reaches a `◇`-node of a present leaf. -/
theorem Term.scoped {σ : Signature} {Γ : Ctx} {T : VarType} {a : Ann T} (t : Term σ Γ T a) :
    ∀ i ∈ a.idxs, (Γ.tree i.root).DiaAt i.path := by
  refine Term.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun Γ _ a _ => ∀ i ∈ a.idxs, (Γ.tree i.root).DiaAt i.path)
    ?F ?eval ?var ?func ?unit ?pair ?boxtm ?diatm t
  case F => intros; trivial
  case eval => intros; trivial
  case var => intro Γ v hv i hi; simp [Ann.idxs] at hi
  case func => intro Γ f _ i hi; simp [Ann.idxs] at hi
  case unit => intro Γ i hi; simp [Ann.idxs] at hi
  case pair =>
    intro Γ A B a b s t ih₁ ih₂ i hi
    rcases List.mem_append.mp hi with h | h
    · exact ih₁ i h
    · exact ih₂ i h
  case boxtm =>
    intro Γ Δ A a b t hΔ hb ih i hi
    subst hΔ hb
    have hi' : i ∈ (a.mapIdx Γ.boxIn.boxOut).idxs := hi
    obtain ⟨j, hj, rfl⟩ := Ann.mem_idxs_mapIdx hi'
    exact Ctx.diaAt_boxOut (ih j hj)
  case diatm =>
    intro Γ Δ A a b x X hx t hΔ hb ih i hi
    subst hΔ hb
    have hi' : i ∈ x.toIdx :: (a.mapIdx ((Γ.diaIn x X).diaOut x)).idxs := hi
    rcases List.mem_cons.mp hi' with rfl | hi''
    · exact Entry.diaAt_of_lookup x.path _ X hx
    · obtain ⟨j, hj, rfl⟩ := Ann.mem_idxs_mapIdx hi''
      exact Ctx.diaAt_diaOut hx (ih j hj)

end V12
