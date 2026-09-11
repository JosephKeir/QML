import QML.QML_v12_Scope
import QML.QML_v12_WFF

/-!
# QML v12 — monotonicity and weakening

`Entry.Le e e'`: `e'` is `e` with some hidden leaves revealed.  The relation survives the modal
views, preserves lookups, and — on indices in scope — the out-maps.  So terms and formulas move
along it with their annotations UNCHANGED (`Term.mono`, `WFF.mono`).  Weakening by a fresh root is
the instance `Ctx.le_insertRoot`.
-/

namespace V12

inductive Entry.Le : Entry → Entry → Prop where
  | hide (e : Entry) : Entry.Le (.leaf none) e
  | refl (e : Entry) : Entry.Le e e
  | node {a a' b b' : Entry} : Entry.Le a a' → Entry.Le b b' → Entry.Le (.node a b) (.node a' b')

theorem Entry.Le.lookup {e e' : Entry} (h : e.Le e') :
    ∀ {q : List PStep} {T : VarType}, e.lookup q = some T → e'.lookup q = some T := by
  induction h with
  | hide e => intro q T hl; cases hl
  | refl e => intro q T hl; exact hl
  | node _ _ iha ihb =>
      intro q T hl
      rcases q with _ | ⟨_ | _, q⟩
      · cases hl
      · exact iha hl
      · exact ihb hl

theorem Entry.Le.outPath {e e' : Entry} (h : e.Le e') :
    ∀ {s : List PStep → Step} {p : List Step}, e.DiaAt p → e.outPath s p = e'.outPath s p := by
  induction h with
  | hide e => intro s p hp; exact False.elim hp
  | refl e => intro s p _; rfl
  | node _ _ iha ihb =>
      intro s p hp
      rcases p with _ | ⟨_ | _ | _ | _, p⟩
      · exact False.elim hp
      · exact congrArg (List.cons _) (iha hp)
      · exact congrArg (List.cons _) (ihb hp)
      · exact False.elim hp
      · exact False.elim hp

theorem Entry.Le.eq_none {e : Entry} (h : e.Le (.leaf none)) : e = .leaf none := by
  cases h <;> rfl

theorem Entry.mkNode_of_ne {a b : Entry} (h : ¬(a = .leaf none ∧ b = .leaf none)) :
    Entry.mkNode a b = .node a b := by
  rcases a with ⟨_ | _⟩ | ⟨_, _⟩ <;> rcases b with ⟨_ | _⟩ | ⟨_, _⟩ <;>
    first | rfl | exact absurd ⟨rfl, rfl⟩ h

theorem Entry.Le.mkNode {a a' b b' : Entry} (ha : a.Le a') (hb : b.Le b') :
    (Entry.mkNode a b).Le (Entry.mkNode a' b') := by
  by_cases h : a = .leaf none ∧ b = .leaf none
  · obtain ⟨rfl, rfl⟩ := h
    exact Entry.Le.hide _
  · rw [Entry.mkNode_of_ne h]
    by_cases h' : a' = .leaf none ∧ b' = .leaf none
    · obtain ⟨rfl, rfl⟩ := h'
      exact absurd ⟨ha.eq_none, hb.eq_none⟩ h
    · rw [Entry.mkNode_of_ne h']
      exact Entry.Le.node ha hb

theorem Entry.Le.boxView {e e' : Entry} (h : e.Le e') :
    ((e.refine e.forced).unbox).Le ((e'.refine e'.forced).unbox) := by
  induction h with
  | hide e => exact Entry.Le.hide _
  | refl e => exact Entry.Le.refl _
  | node _ _ iha ihb => exact Entry.Le.mkNode iha ihb

theorem Entry.Le.diaView {e e' : Entry} (h : e.Le e') :
    ∀ {q : List PStep} {X : VarType}, e.lookup q = some (.VTypeDia X) →
      ((e.refine (e.forced.join (Pat.path q))).unboxExcept q X).Le
        ((e'.refine (e'.forced.join (Pat.path q))).unboxExcept q X) := by
  induction h with
  | hide e => intro q X hl; cases hl
  | refl e => intro q X _; exact Entry.Le.refl _
  | @node a a' b b' ha hb iha ihb =>
      intro q X hl
      rcases q with _ | ⟨_ | _, q⟩
      · cases hl
      · simp only [Entry.forced, Pat.path, Pat.join, Pat.join_stop, Entry.refine,
          Entry.unboxExcept]
        exact Entry.Le.node (iha hl) hb.boxView
      · simp only [Entry.forced, Pat.path, Pat.join, Pat.join_stop, Entry.refine,
          Entry.unboxExcept]
        exact Entry.Le.node ha.boxView (ihb hl)

/-! ## Contexts -/

structure Ctx.Le (Γ Γ' : Ctx) : Prop where
  depth : Γ'.depth = Γ.depth
  tree : ∀ r, (Γ.tree r).Le (Γ'.tree r)

theorem Ctx.Le.refl (Γ : Ctx) : Γ.Le Γ := ⟨rfl, fun _ => Entry.Le.refl _⟩

theorem Ctx.Le.refType {Γ Γ' : Ctx} (h : Γ.Le Γ') {v : VarSymb} {T : VarType}
    (hv : Γ.refType v = some T) : Γ'.refType v = some T :=
  (h.tree v.root).lookup hv

theorem Ctx.Le.boxIn {Γ Γ' : Ctx} (h : Γ.Le Γ') : Γ.boxIn.Le Γ'.boxIn :=
  ⟨h.depth, fun r => (h.tree r).boxView⟩

theorem Ctx.Le.diaIn {Γ Γ' : Ctx} (h : Γ.Le Γ') {x : VarSymb} {X : VarType}
    (hx : Γ.refType x = some (.VTypeDia X)) : (Γ.diaIn x X).Le (Γ'.diaIn x X) := by
  refine ⟨h.depth, fun r => ?_⟩
  by_cases hr : r = x.root
  · subst hr
    have ht : ∀ Δ : Ctx, (Δ.diaIn x X).tree x.root =
        ((Δ.tree x.root).refine ((Δ.tree x.root).forced.join (Pat.path x.path))).unboxExcept
          x.path X := fun Δ => by
      simp only [Ctx.diaIn, Ctx.dia, Ctx.refine, Ctx.forcedX, Ctx.forced, Ctx.pathPat, if_true]
    rw [ht Γ, ht Γ']
    exact (h.tree x.root).diaView hx
  · have ht : ∀ Δ : Ctx, (Δ.diaIn x X).tree r = ((Δ.tree r).refine (Δ.tree r).forced).unbox :=
      fun Δ => by
        simp only [Ctx.diaIn, Ctx.dia, Ctx.refine, Ctx.forcedX, Ctx.forced, Ctx.pathPat, hr,
          if_false, Pat.join_stop]
    rw [ht Γ, ht Γ']
    exact (h.tree r).boxView

theorem Ctx.Le.outIdx {Δ Δ' : Ctx} (h : Δ.Le Δ') {s : Root → List PStep → Step} {i : Idx}
    (hi : (Δ.tree i.root).DiaAt i.path) : Δ.outIdx s i = Δ'.outIdx s i := by
  simp only [Ctx.outIdx, (h.tree i.root).outPath hi]

theorem Ctx.Le.insertBnd {Γ Γ' : Ctx} (h : Γ.Le Γ') (T : VarType) :
    (Γ.insertBnd T).Le (Γ'.insertBnd T) := by
  refine ⟨by simp [Ctx.insertBnd, h.depth], fun r => ?_⟩
  simp only [Ctx.insertBnd, h.depth, Function.update_apply]
  split_ifs
  · exact Entry.Le.refl _
  · exact h.tree r

/-- Weakening by a fresh root. -/
theorem Ctx.le_insertRoot {Γ : Ctx} {r : Root} (hr : Γ.FreshRoot r) (T : VarType) :
    Γ.Le (Γ.insertRoot r T) := by
  refine ⟨rfl, fun r' => ?_⟩
  simp only [Ctx.insertRoot, Function.update_apply]
  split_ifs with h
  · subst h
    rw [hr]
    exact Entry.Le.hide _
  · exact Entry.Le.refl _

/-! ## Terms and formulas -/

mutual
  def Func.mono {σ : Signature} : {Γ Γ' : Ctx} → Γ.Le Γ' → {n : ℕ} → Func σ Γ n → Func σ Γ' n
    | _, _, _, _, .F f => .F f
    | _, _, h, _, .eval g t => .eval (Func.mono h g) (Term.mono h t)

  /-- ⭐Enters modal bodies; the annotation is unchanged because the out-maps agree on the
      indices in scope (`Term.scoped`). -/
  def Term.mono {σ : Signature} : {Γ Γ' : Ctx} → Γ.Le Γ' → {T : VarType} → {a : Ann T} →
      Term σ Γ T a → Term σ Γ' T a
    | _, _, h, _, _, .var v hv => .var v (h.refType hv)
    | _, _, h, _, _, .func f => .func (Func.mono h f)
    | _, _, _, _, _, .unit => .unit
    | _, _, h, _, _, .pair s t => .pair (Term.mono h s) (Term.mono h t)
    | _, Γ', h, _, _, .boxtm (Δ := Δ) (a := a) t hΔ hb =>
        have hle : Δ.Le Γ'.boxIn := hΔ ▸ h.boxIn
        .boxtm (Term.mono hle t) rfl
          (hb.trans (congrArg Ann.box
            (Ann.mapIdx_congr a (fun i hi => hle.outIdx (Term.scoped t i hi)))))
    | _, Γ', h, _, _, .diatm (Δ := Δ) (a := a) x X hx t hΔ hb =>
        have hle : Δ.Le (Γ'.diaIn x X) := hΔ ▸ h.diaIn hx
        .diatm x X (h.refType hx) (Term.mono hle t) rfl
          (hb.trans (congrArg (Ann.dia x.toIdx)
            (Ann.mapIdx_congr a (fun i hi => hle.outIdx (Term.scoped t i hi)))))
end

def Rel.mono {σ : Signature} {Γ Γ' : Ctx} (h : Γ.Le Γ') : {n : ℕ} → Rel σ Γ n → Rel σ Γ' n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.mono h ρ) (Term.mono h t)

def WFF.mono {σ : Signature} : {Γ Γ' : Ctx} → Γ.Le Γ' → WFF σ Γ → WFF σ Γ'
  | _, _, h, .atom ρ => .atom (Rel.mono h ρ)
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, h, .and φ ψ => .and (WFF.mono h φ) (WFF.mono h ψ)
  | _, _, h, .or φ ψ => .or (WFF.mono h φ) (WFF.mono h ψ)
  | _, _, h, .imp φ ψ => .imp (WFF.mono h φ) (WFF.mono h ψ)
  | _, _, h, .all T φ => .all T (WFF.mono (h.insertBnd T) φ)
  | _, _, h, .ex T φ => .ex T (WFF.mono (h.insertBnd T) φ)
  | _, _, h, .eq t s => .eq (Term.mono h t) (Term.mono h s)
  | _, Γ', h, .box (Δ := Δ) φ hΔ =>
      .box (WFF.mono (hΔ ▸ h.boxIn : Δ.Le Γ'.boxIn) φ) rfl
  | _, Γ', h, .dia (Δ := Δ) x X hx φ hΔ =>
      .dia x X (h.refType hx) (WFF.mono (hΔ ▸ h.diaIn hx : Δ.Le (Γ'.diaIn x X)) φ) rfl

/-! ## Weakening -/

def Term.weaken {σ : Signature} {Γ : Ctx} (u : FreeSymb) (T : VarType)
    (hu : Γ.FreshRoot (.free u.idx)) {S : VarType} {a : Ann S} (t : Term σ Γ S a) :
    Term σ (Γ.insertFree u T) S a :=
  Term.mono (Ctx.le_insertRoot hu T) t

def WFF.weaken {σ : Signature} {Γ : Ctx} (u : FreeSymb) (T : VarType)
    (hu : Γ.FreshRoot (.free u.idx)) (φ : WFF σ Γ) : WFF σ (Γ.insertFree u T) :=
  WFF.mono (Ctx.le_insertRoot hu T) φ

end V12
