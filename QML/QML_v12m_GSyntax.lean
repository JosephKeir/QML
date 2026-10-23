import QML.QML_v12m_BSyntax

/-!
# QML v12m — the growing tree: arrows as item maps

The canonical model for strong 4 (`docs/v12-modal-extensions.md` §3 4, "The growing tree, on
paper") is B's network without back arrows: worlds of their own variables (`BArrow.ctxOf`), linked
by arrows.  B's arrows are index maps on roots (`BArrow.arrowS`): every item of a root lands in one
variable of the target.  The growing tree's cannot be: a lift sends `m.keep` to an **existing**
address `n` of the target, and two roots may share an image.  So here an arrow is an **item map**:
each item of the source's view — an address ending in a level step, `u.box` and `u.keep` (and for
a witness arrow `x.dia`) — goes to an address of the target (`itemS`).

Annotation indices follow by splitting an address at its first level step (`splitLevel`): the
item before it goes where the map sends it, the rest is kept (`itemIdx`).  An item's own address
is a projection path followed by its level step (`view_item`, from `BArrow.reach_ppath`), so the
split recovers it (`splitLevel_item`), and the arrow is coherent (`coh_itemS`).

B's arrows are the instance sending `u.box` to `BArrow.itemImg img u`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

/-! ## Splitting an address at its first level step -/

/-- The first level step of a path, with the projections before it and the steps after. -/
def splitLevel : List Step → Option (List Step × Step × List Step)
  | [] => none
  | s :: p =>
      if s.isProj then (splitLevel p).map fun t => (s :: t.1, t.2.1, t.2.2)
      else some ([], s, p)

omit [ModalSys] in
/-- ⭐A projection path followed by a level step splits there. -/
theorem splitLevel_ppath : ∀ {q : List Step}, PPath q → ∀ {s : Step}, s.isProj = false →
    ∀ k : List Step, splitLevel (q ++ s :: k) = some (q, s, k)
  | [], _, s, hs, k => by
      change (if s.isProj then _ else _) = _
      rw [if_neg (by simp [hs])]
  | a :: q, h, s, hs, k => by
      change (if a.isProj then _ else _) = _
      rw [if_pos (h a (by simp))]
      change Option.map _ (splitLevel (q ++ s :: k)) = _
      rw [splitLevel_ppath (fun s' hs' => h s' (by simp [hs'])) hs k]
      rfl

/-! ## The renaming of an arrow -/

/-- ⭐The renaming of an arrow given by an item map `f`: an item (an address ending in a level
    step) goes to its image. -/
def itemS (σ : Signature) (Δ : Ctx) (f : VarSymb → VarSymb) : Subst σ Δ := fun v =>
  match v with
  | .step u s => if s.isProj then .hide else .ren (f (.step u s))
  | .root _ => .hide

/-- Where an item map sends annotation indices: the item before the first level step to its
    image, the rest kept. -/
def itemIdx (f : VarSymb → VarSymb) (a : VarSymb) : VarSymb :=
  match splitLevel a.path with
  | some (q, s, k) => (f (.step ((VarSymb.root a.rt).ext q) s)).ext k
  | none => a

/-- The images are declared at the items' types. -/
def ItemOk (Γ Δ : Ctx) (f : VarSymb → VarSymb) : Prop :=
  ∀ v T, v.lastProj = false → Γ v = some T → Δ.ref (f v) = some T

theorem ok_itemS {σ : Signature} {Γ Δ : Ctx} {f : VarSymb → VarSymb} (hf : ItemOk Γ Δ f)
    (hit : ∀ v T, v.lastProj = false → Γ v = some T → ∃ u s, v = .step u s) :
    Subst.Ok Γ (itemS σ Δ f) := by
  intro v T hv hT
  obtain ⟨u, s, rfl⟩ := hit v T hv hT
  have hs : s.isProj = false := hv
  change (if s.isProj then SubE.hide else .ren (f (.step u s))).OkRef T
  rw [if_neg (by simp [hs])]
  exact hf _ T hv hT

omit [ModalSys] in
/-- The index map of an item map at an item `u.s`, followed by `p`, for `u` a projection path. -/
theorem itemIdx_item (f : VarSymb → VarSymb) {u : VarSymb} (hu : PPath u.path) {s : Step}
    (hs : s.isProj = false) (p : List Step) :
    itemIdx f ((VarSymb.step u s).ext p) = (f (.step u s)).ext p := by
  unfold itemIdx
  rw [VarSymb.ext_path, VarSymb.ext_rt]
  rw [show (VarSymb.step u s).path ++ p = u.path ++ s :: p by
    change (u.path ++ [s]) ++ p = _
    simp, splitLevel_ppath hu hs p]
  change (f (.step ((VarSymb.root u.rt).ext u.path) s)).ext p = _
  rw [← VarSymb.eq_root_ext u]

/-- ⭐An item map is coherent with its index map, given the items are projection paths followed
    by a level step. -/
theorem coh_itemS {σ : Signature} {Γ Δ : Ctx} {f : VarSymb → VarSymb} (hf : ItemOk Γ Δ f)
    (hit : ∀ v T, v.lastProj = false → Γ v = some T → ∃ u s, v = .step u s ∧ PPath u.path) :
    Subst.Coh (itemIdx f) Γ (itemS σ Δ f) := by
  refine Subst.coh_of (ok_itemS hf fun v T hv hT => ?_) ?_
  · obtain ⟨u, s, rfl, _⟩ := hit v T hv hT
    exact ⟨u, s, rfl⟩
  intro v T hv hT p
  obtain ⟨u, s, rfl, hu⟩ := hit v T hv hT
  have hs : s.isProj = false := hv
  change (if s.isProj then SubE.hide else .ren (f (.step u s))).idxAlong p = _
  rw [if_neg (by simp [hs]), itemIdx_item f hu hs p]
  rfl

/-! ## The items of a world's views -/

/-- ⭐An item of the `□` view of a world is a reachable address followed by a level step. -/
theorem boxIn_item {l : List VarType} {v : VarSymb} {T : VarType}
    (h : (ctxOf l).boxIn v = some T) :
    ∃ u s, v = .step u s ∧ PPath u.path ∧ ∃ U, (ctxOf l).ref u = some U := by
  match v with
  | .step u .box =>
      have hu := (Ctx.boxIn_box h).2
      exact ⟨u, .box, rfl, (reach_ppath hu).1, _, hu⟩
  | .step u .keep =>
      have hu := (Ctx.boxIn_keep h).2.1
      exact ⟨u, .keep, rfl, (reach_ppath hu).1, _, hu⟩
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

/-- An item of a `◇_x` view: one of the `□` view, or `x.dia`. -/
theorem diaIn_item {l : List VarType} {x v : VarSymb} {T : VarType}
    (h : ((ctxOf l).diaIn x) v = some T) :
    ∃ u s, v = .step u s ∧ PPath u.path ∧ ∃ U, (ctxOf l).ref u = some U := by
  match v with
  | .step u .dia =>
      change (if u = x then (match (ctxOf l).ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at h
      split_ifs at h with hux
      subst hux
      cases hx : (ctxOf l).ref u with
      | none => rw [hx] at h; cases h
      | some U => exact ⟨u, .dia, rfl, (reach_ppath hx).1, U, hx⟩
  | .step u .box => exact boxIn_item (l := l) h
  | .step u .keep => exact boxIn_item (l := l) h
  | .root r => exact boxIn_item (l := l) h
  | .step u .fst => exact boxIn_item (l := l) h
  | .step u .snd => exact boxIn_item (l := l) h
  | .step u .here => exact boxIn_item (l := l) h

theorem coh_itemS_boxIn {σ : Signature} {l : List VarType} {Δ : Ctx} {f : VarSymb → VarSymb}
    (hf : ItemOk (ctxOf l).boxIn Δ f) :
    Subst.Coh (itemIdx f) (ctxOf l).boxIn (itemS σ Δ f) :=
  coh_itemS hf fun _ _ _ hT => by
    obtain ⟨u, s, e, hu, _⟩ := boxIn_item hT
    exact ⟨u, s, e, hu⟩

theorem coh_itemS_diaIn {σ : Signature} {l : List VarType} {x : VarSymb} {Δ : Ctx}
    {f : VarSymb → VarSymb} (hf : ItemOk ((ctxOf l).diaIn x) Δ f) :
    Subst.Coh (itemIdx f) ((ctxOf l).diaIn x) (itemS σ Δ f) :=
  coh_itemS hf fun _ _ _ hT => by
    obtain ⟨u, s, e, hu, _⟩ := diaIn_item hT
    exact ⟨u, s, e, hu⟩

end GArrow

end V12M
