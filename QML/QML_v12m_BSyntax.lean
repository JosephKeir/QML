import QML.QML_v12m_ProofSubst

/-!
# QML v12m — B's arrow model: syntax

The canonical model for B (`docs/v12-arrow-canonical.md`) is built from worlds whose contexts
consist of **their own variables only**: the `n`-th variable declared is `free n`, and the types
are a list, newest first (`ctxOf`).  Nothing of another world appears in a world's context; worlds
are linked by **arrows**, which translate the source's `□` view into the target's variables.

An item of the `□` view is `u.box` for a reachable `u : □A`.  In a context of own variables a
reachable address is a root followed by projections (`reach_ppath`), so the items of one root `r`
are the `□`-components of its type.  An arrow sends them all to **one** variable `z` of the
target, of the type `r`'s type has with each `□A` component replaced by its box contents and every
other leaf by `𝟙` (`VarType.bc`), and the item `r.q.box` to the address `itemAt z r.q` in it
(`arrowS`, well typed by `ref_item`).  So an arrow is an index map on roots.  A `◇_x` arrow,
towards a world in the extent of `x`, also sends `x.dia` to a variable holding `x`'s content
(`arrowXS`).

Without T, `itemAt z r.q` is `z.q`.  Under T the projection `here` makes `r.here.q.box` an item
too, so a `□A` component's box contents are `A × bc A` and `itemAt` encodes the path
(`encPath`, `itemTail`; `docs/v12-arrow-canonical.md` §9.2).  The construction needs 4 off
(`ModalSys.NoFour`): views then show exactly the `box` items (and `x.dia`).
-/


namespace V12M

/-- The flag the arrow construction needs (`docs/v12-arrow-canonical.md` §9): 4 off, so a view
    shows `u.box` (and `x.dia`) and never `keep`.  Under T a reachable address may also pass
    through the projection `here`, which `VarType.bc` and the arrows account for. -/
class ModalSys.NoFour [ModalSys] : Prop where
  noFour : ModalSys.Four = false

/-- The flags the network's canonical `Model` and B's completeness are stated for: 4 off, and
    strong T off whenever T is on — strong T's term query in the network is still to come
    (`docs/v12-roadmap.md`, milestone 1 step 6). -/
class ModalSys.NoFourNoTS [ModalSys] : Prop extends ModalSys.NoFour where
  noTS : ModalSys.T = true → ModalSys.TStrong = false

variable [ModalSys]

theorem ModalSys.NoFour.keepOnly [ModalSys.NoFour] : ModalSys.keepOnly = false := by
  simp [ModalSys.keepOnly, ModalSys.NoFour.noFour]

/-! ## Addresses as paths -/

namespace VarSymb

omit [ModalSys]

theorem ext_append : ∀ (v : VarSymb) (p q : List Step), v.ext (p ++ q) = (v.ext p).ext q
  | _, [], _ => rfl
  | v, s :: p, q => ext_append (.step v s) p q

theorem ext_nil (v : VarSymb) : v.ext [] = v := rfl

theorem ext_step (v : VarSymb) (p : List Step) (s : Step) :
    v.ext (p ++ [s]) = .step (v.ext p) s :=
  ext_append v p [s]

/-- An address is its root followed by its path. -/
theorem eq_root_ext : ∀ v : VarSymb, v = (VarSymb.root v.rt).ext v.path
  | .root _ => rfl
  | .step v s => by
      change VarSymb.step v s = (VarSymb.root v.rt).ext (v.path ++ [s])
      rw [ext_step, ← eq_root_ext v]

theorem reroot_eq : ∀ (u : VarSymb) (r : Root), u.reroot r = (VarSymb.root r).ext u.path
  | .root _, _ => rfl
  | .step u s, r => by
      change VarSymb.step (u.reroot r) s = (VarSymb.root r).ext (u.path ++ [s])
      rw [ext_step, reroot_eq u r]

theorem reroot_rt : ∀ (u : VarSymb) (r : Root), (u.reroot r).rt = r
  | .root _, _ => rfl
  | .step u _, r => reroot_rt u r

theorem reroot_path : ∀ (u : VarSymb) (r : Root), (u.reroot r).path = u.path
  | .root _, _ => rfl
  | .step u s, r => by
      change (u.reroot r).path ++ [s] = u.path ++ [s]
      rw [reroot_path u r]

end VarSymb

/-- A path of projections: `fst`, `snd`, and under T `here`. -/
def PPath (p : List Step) : Prop := ∀ s ∈ p, s.isProj = true

omit [ModalSys] in
theorem PPath.box_not_mem {p : List Step} (h : PPath p) : Step.box ∉ p := fun hm =>
  absurd (h _ hm) (by decide)

omit [ModalSys] in
theorem PPath.dia_not_mem {p : List Step} (h : PPath p) : Step.dia ∉ p := fun hm =>
  absurd (h _ hm) (by decide)

omit [ModalSys] in
theorem PPath.append {p q : List Step} (hp : PPath p) (hq : PPath q) : PPath (p ++ q) :=
  fun s hs => (List.mem_append.mp hs).elim (hp s) (hq s)

namespace BArrow

/-! ## Contexts of own variables -/

/-- The declarations of variables of types `l`, newest first: the `n`-th declared is `free n`. -/
def decls : List VarType → List (ℕ × VarType)
  | [] => []
  | A :: l => (l.length, A) :: decls l

/-- ⭐The context of a world whose own variables have the types `l`, newest first. -/
abbrev ctxOf (l : List VarType) : Ctx := Ctx.ofDecls (decls l)

omit [ModalSys] in
theorem ctxOf_cons (A : VarType) (l : List VarType) :
    ctxOf (A :: l) = (ctxOf l).insert (.free l.length) A := rfl

omit [ModalSys] in
theorem ctxOf_nil : ctxOf [] = Ctx.empty := rfl

omit [ModalSys] in
/-- Only roots are declared, and only free ones. -/
theorem ctxOf_decl : ∀ {l : List VarType} {v : VarSymb} {T : VarType}, ctxOf l v = some T →
    ∃ r, v = .root (.free r)
  | [], _, _, h => nomatch h
  | A :: l, v, T, h => by
      rw [ctxOf_cons] at h
      simp only [Ctx.insert] at h
      split_ifs at h with hv
      · exact ⟨_, hv⟩
      · exact ctxOf_decl h

omit [ModalSys] in
theorem ctxOf_root : ∀ (l : List VarType) (r : ℕ), ctxOf l (.root (.free r)) = l.reverse[r]?
  | [], _ => rfl
  | A :: l, r => by
      rw [ctxOf_cons]
      simp only [Ctx.insert, VarSymb.root.injEq, Root.free.injEq, List.reverse_cons]
      split_ifs with hr
      · subst hr
        simp
      · rw [ctxOf_root l r]
        by_cases hlt : r < l.length
        · rw [List.getElem?_append_left (by simpa using hlt)]
        · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt),
            List.getElem?_append_right (by simpa using Nat.le_of_not_lt hlt)]
          simp only [List.length_reverse, List.getElem?_singleton]
          rw [if_neg (by omega)]

omit [ModalSys] in
theorem ctxOf_fresh {l : List VarType} {n : ℕ} (h : l.length ≤ n) :
    (ctxOf l).RootFresh (.free n) := by
  intro v hv
  cases hc : ctxOf l v with
  | none => rfl
  | some T =>
      obtain ⟨r, rfl⟩ := ctxOf_decl hc
      cases hv
      rw [ctxOf_root, List.getElem?_eq_none (by simpa using h)] at hc
      cases hc

/-- The context of a world language is presented: each own variable is declared with a name the
    ones before it do not use (`ctxOf_fresh`). -/
instance presented_ctxOf : ∀ l : List VarType, (ctxOf l).Presented
  | [] => inferInstanceAs Ctx.empty.Presented
  | A :: l => (presented_ctxOf l).insertFree l.length (ctxOf_fresh le_rfl) A

omit [ModalSys] in
/-- Declaring more variables, newer ones in front. -/
theorem ctxOf_le_append : ∀ (l' l : List VarType), (ctxOf l).Le (ctxOf (l' ++ l))
  | [], l => Ctx.Le.refl _
  | A :: l', l => by
      refine (ctxOf_le_append l' l).trans ?_
      change (ctxOf (l' ++ l)).Le (ctxOf (A :: (l' ++ l)))
      rw [ctxOf_cons]
      exact Ctx.le_insert (ctxOf_fresh le_rfl).root A

/-- The type of the `r`-th variable. -/
def rootTy (l : List VarType) (r : ℕ) : VarType := l.reverse.getD r .VTypeOne

omit [ModalSys] in
theorem ctxOf_root_lt {l : List VarType} {r : ℕ} (h : r < l.length) :
    ctxOf l (.root (.free r)) = some (rootTy l r) := by
  rw [ctxOf_root, rootTy, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using h)]
  rfl

/-! ## Reachable addresses are projection paths -/

/-- In a context of own variables a reachable address is a declared root followed by projections
    (under T possibly `here`). -/
theorem reach_ppath {l : List VarType} :
    ∀ {v : VarSymb} {T : VarType}, (ctxOf l).ref v = some T →
      PPath v.path ∧ ∃ r, v.rt = .free r
  | .root r, T, h => by
      obtain ⟨r', hr'⟩ := ctxOf_decl h
      cases hr'
      exact ⟨(fun _ hs => nomatch hs), _, rfl⟩
  | .step v s, T, h => by
      simp only [Ctx.ref] at h
      split_ifs at h with hs
      · cases hU : (ctxOf l).ref v with
        | none => rw [hU] at h; cases h
        | some U =>
            obtain ⟨hp, hr⟩ := reach_ppath hU
            refine ⟨?_, hr⟩
            change PPath (v.path ++ [s])
            refine hp.append fun s' hs' => ?_
            rw [List.mem_singleton.mp hs']
            exact hs
      · obtain ⟨r, hr⟩ := ctxOf_decl h
        cases hr

/-! ## Box contents -/

/-- The box-contents type, for a given value `b` of the T flag (`VarType.bc` takes `ModalSys.T`).
    Taking the flag as an argument lets terms of this type be built by matching on it, with no
    casts (`tupB`). -/
def _root_.V12M.VarType.bcB (b : Bool) : VarType → VarType
  | .Var => .VTypeOne
  | .VTypeOne => .VTypeOne
  | .VTypeProd A B => .VTypeProd (VarType.bcB b A) (VarType.bcB b B)
  | .VTypeBox A => cond b (.VTypeProd A (VarType.bcB b A)) A
  | .VTypeDia _ => .VTypeOne

/-- ⭐The type of what an arrow gives a variable of type `T` at the target: each `□A` component
    becomes `A`, every other leaf `𝟙`.  Under T a `□A` component also reaches its value here
    (`u.here : A`), whose own items an arrow must carry too, so it becomes `A × bc A`: the box
    contents first, the `here` value's items second (`docs/v12-arrow-canonical.md` §9.2). -/
abbrev _root_.V12M.VarType.bc (T : VarType) : VarType := VarType.bcB ModalSys.T T

/-! ## Where an item lands -/

/-- A projection step, read in the `bc` type: under T, `here` is the second component of a `□`
    component's box contents. -/
def encStep (s : Step) : Step :=
  if ModalSys.T then (match s with | .here => .snd | s => s) else s

/-- A projection path, read in the `bc` type. -/
def encPath (p : List Step) : List Step := p.map encStep

/-- The last step to an item's image: under T the box contents are the first component. -/
def itemTail : List Step := if ModalSys.T then [.fst] else []

/-- ⭐Where an address of the `□` view lands, relative to its root's image: the projections up to
    the first `box` encoded, the `box` replaced by `itemTail`, the rest kept. -/
def itemPath : List Step → List Step
  | [] => []
  | .box :: p => itemTail ++ p
  | s :: p => encStep s :: itemPath p

theorem encStep_noT (hT : ModalSys.T = false) (s : Step) : encStep s = s := by
  simp [encStep, hT]

theorem encPath_noT (hT : ModalSys.T = false) (p : List Step) : encPath p = p := by
  rw [encPath, show encStep = id from funext (encStep_noT hT), List.map_id]

theorem itemTail_noT (hT : ModalSys.T = false) : itemTail = [] := by
  simp [itemTail, hT]

theorem itemPath_cons {s : Step} (hs : s ≠ .box) (p : List Step) :
    itemPath (s :: p) = encStep s :: itemPath p := by
  cases s <;> first | rfl | exact absurd rfl hs

theorem itemPath_append_ppath : ∀ {q : List Step}, PPath q → ∀ r : List Step,
    itemPath (q ++ r) = encPath q ++ itemPath r
  | [], _, _ => rfl
  | s :: q, h, r => by
      have hs : s ≠ .box := fun e => absurd (h s (by simp)) (by rw [e]; decide)
      rw [List.cons_append, itemPath_cons hs,
        itemPath_append_ppath (fun s' hs' => h s' (by simp [hs'])) r]
      rfl

/-- ⭐The image path of an item `u.box`, followed by `p`. -/
theorem itemPath_item {u : VarSymb} (hu : PPath u.path) (p : List Step) :
    itemPath ((VarSymb.step u .box).ext p).path = encPath u.path ++ itemTail ++ p := by
  rw [VarSymb.ext_path]
  change itemPath ((u.path ++ [Step.box]) ++ p) = _
  rw [List.append_assoc, itemPath_append_ppath hu, List.append_assoc]
  rfl

theorem encStep_proj {s : Step} (hs : s.isProj = true) : (encStep s).isProj = true := by
  unfold encStep
  split_ifs <;> cases s <;> first | rfl | exact absurd hs (by decide)

/-- One projection step, read in the `bc` type. -/
theorem bc_encStep {T U : VarType} {s : Step} (hs : s.isProj = true) (h : T.step s = some U) :
    T.bc.step (encStep s) = some U.bc := by
  cases s with
  | fst =>
      cases T with
      | VTypeProd A B => cases h; simp [encStep, VarType.bcB, VarType.step]
      | _ => cases h
  | snd =>
      cases T with
      | VTypeProd A B => cases h; simp [encStep, VarType.bcB, VarType.step]
      | _ => cases h
  | here =>
      cases T with
      | VTypeBox A =>
          obtain ⟨hT, rfl⟩ := VarType.step_here h
          simp [encStep, VarType.bc, VarType.bcB, VarType.step, hT]
      | _ => cases h
  | _ => exact absurd hs (by decide)

/-- ⭐A reachable address's projections, encoded and read from a variable of its root's `bc` type,
    reach the `bc` type of the address. -/
theorem ref_enc_bc {l : List VarType} {Δ : Ctx} {z : Root} {R : VarType} :
    ∀ {u : VarSymb} {T : VarType}, (ctxOf l).ref u = some T → (ctxOf l).ref (.root u.rt) = some R →
      Δ.ref (.root z) = some R.bc → Δ.ref ((VarSymb.root z).ext (encPath u.path)) = some T.bc
  | .root r, T, h, hR, hz => by
      change (ctxOf l).ref (.root r) = some R at hR
      rw [hR] at h
      cases h
      exact hz
  | .step u s, T, h, hR, hz => by
      have hproj : s.isProj = true := (reach_ppath h).1 s (by simp [VarSymb.path])
      simp only [Ctx.ref, if_pos hproj] at h
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at h; cases h
      | some U =>
          rw [hU] at h
          have ih := ref_enc_bc hU hR hz
          change Δ.ref ((VarSymb.root z).ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step]
          simp only [Ctx.ref, if_pos (encStep_proj hproj), ih, Option.bind_some]
          exact bc_encStep hproj h

/-- ⭐The image of an item `u.box` read from a root `z` holding `u`'s root's box contents: `u`'s
    projections encoded, then `itemTail`.  Arrows take `z` to be the root's image (`itemImg`),
    abstraction the slot.  Without T this is `u` rerooted at `z` (`itemAt_noT`). -/
def itemAt (z : Root) (u : VarSymb) : VarSymb :=
  (VarSymb.root z).ext (encPath u.path ++ itemTail)

theorem itemAt_noT (hT : ModalSys.T = false) (z : Root) (u : VarSymb) :
    itemAt z u = u.reroot z := by
  rw [itemAt, encPath_noT hT, itemTail_noT hT, List.append_nil, VarSymb.reroot_eq]

theorem itemAt_rt (z : Root) (u : VarSymb) : (itemAt z u).rt = z := VarSymb.ext_rt _ _

theorem itemAt_path (z : Root) (u : VarSymb) : (itemAt z u).path = encPath u.path ++ itemTail := by
  rw [itemAt, VarSymb.ext_path]
  rfl

theorem PPath.encPath {p : List Step} (h : PPath p) : PPath (encPath p) := fun s hs => by
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  exact encStep_proj (h s' hs')

theorem PPath.itemTail : PPath itemTail := fun s hs => by
  unfold V12M.BArrow.itemTail at hs
  split_ifs at hs
  · rw [List.mem_singleton.mp hs]
    rfl
  · cases hs

/-- The image path of an item is a projection path. -/
theorem itemAt_ppath {u : VarSymb} (hu : PPath u.path) (z : Root) : PPath (itemAt z u).path := by
  rw [itemAt_path]
  exact (PPath.encPath hu).append PPath.itemTail

/-- ⭐An item `u.box`, for `u : □T`, lands at type `T`. -/
theorem ref_item {l : List VarType} {Δ : Ctx} {z : Root} {R : VarType} {u : VarSymb}
    {T : VarType} (hu : (ctxOf l).ref u = some (.VTypeBox T))
    (hR : (ctxOf l).ref (.root u.rt) = some R) (hz : Δ.ref (.root z) = some R.bc) :
    Δ.ref (itemAt z u) = some T := by
  have h := ref_enc_bc hu hR hz
  rw [itemAt, VarSymb.ext_append]
  unfold itemTail
  by_cases hT : ModalSys.T = true
  · rw [if_pos hT]
    change Δ.ref (.step ((VarSymb.root z).ext (encPath u.path)) .fst) = _
    simp only [Ctx.ref, Step.isProj, if_true, h, Option.bind_some, VarType.bc, hT, VarType.bcB]
    rfl
  · rw [if_neg hT]
    simpa [VarType.bc, VarType.bcB, hT] using h

/-! ## The renaming of an arrow -/

/-- The image of a root under an index map on variables. -/
def imgRoot (img : ℕ → ℕ) : Root → Root
  | .free r => .free (img r)
  | .bnd n => .bnd n

/-- The image of an item `u.box`: from its root's image, `u`'s projections encoded, then
    `itemTail`.  Without T this is `u` rerooted (`itemAt_noT`). -/
abbrev itemImg (img : ℕ → ℕ) (u : VarSymb) : VarSymb := itemAt (imgRoot img u.rt) u

/-- ⭐The renaming of an arrow: the item `u.box` goes to its image (`itemImg`). -/
def arrowS (σ : Signature) (Δ : Ctx) (img : ℕ → ℕ) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => .ren (itemImg img u)
  | _ => .hide

/-- Where an arrow sends annotation indices: the root renamed, the path as `itemPath` sends it. -/
def arrowIdx (img : ℕ → ℕ) (a : VarSymb) : VarSymb :=
  (VarSymb.root (imgRoot img a.rt)).ext (itemPath a.path)

/-- The images of the variables are declared at the `bc` types. -/
def ImgOk (l : List VarType) (Δ : Ctx) (img : ℕ → ℕ) : Prop :=
  ∀ r, r < l.length → Δ.ref (.root (.free (img r))) = some (rootTy l r).bc

theorem boxIn_item [ModalSys.NoFour] {l : List VarType} {v : VarSymb} {T : VarType}
    (h : (ctxOf l).boxIn v = some T) :
    ∃ u, v = .step u .box ∧ (ctxOf l).ref u = some (.VTypeBox T) := by
  match v with
  | .step u .box => exact ⟨u, rfl, (Ctx.boxIn_box h).2⟩
  | .step u .keep =>
      obtain ⟨hF, _⟩ := Ctx.boxIn_keep h
      rw [ModalSys.NoFour.noFour] at hF
      cases hF
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

/-- The root of a reachable address is declared at its own type. -/
theorem ref_rt {l : List VarType} {u : VarSymb} {T : VarType}
    (h : (ctxOf l).ref u = some T) :
    ∃ r, u.rt = .free r ∧ r < l.length ∧ (ctxOf l).ref (.root u.rt) = some (rootTy l r) := by
  obtain ⟨_, r, hr⟩ := reach_ppath h
  have hdecl : (ctxOf l).ref (.root u.rt) ≠ none := by
    intro hn
    have hfr : ∀ v : VarSymb, v.rt = u.rt → (ctxOf l).ref v = none :=
      Ctx.ref_none_of_rootFresh (fun v hv => by
        cases hc : ctxOf l v with
        | none => rfl
        | some U =>
            obtain ⟨r', rfl⟩ := ctxOf_decl hc
            change VarSymb.rt (.root (.free r')) = u.rt at hv
            rw [← hv] at hn
            change ctxOf l (.root (.free r')) = none at hn
            rw [hc] at hn
            cases hn)
    rw [hfr u rfl] at h
    cases h
  have hlt : r < l.length := by
    by_contra hge
    apply hdecl
    rw [hr]
    exact (ctxOf_fresh (Nat.le_of_not_lt hge)) _ rfl
  refine ⟨r, hr, hlt, ?_⟩
  rw [hr]
  exact ctxOf_root_lt hlt

theorem ok_arrowS [ModalSys.NoFour] {σ : Signature} {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) : Subst.Ok (ctxOf l).boxIn (arrowS σ Δ img) := by
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
  change Δ.ref (itemImg img u) = some T
  have hz : Δ.ref (.root (imgRoot img u.rt)) = some (rootTy l r).bc := by
    rw [hr]
    exact himg r hlt
  exact ref_item hu hR hz

omit [ModalSys] in
/-- Two projection paths, each followed by a level step, agree only if the paths and the steps
    do. -/
theorem ppath_level : ∀ {p q : List Step} {s t : Step} {k m : List Step}, PPath p → PPath q →
    s.isProj = false → t.isProj = false → p ++ s :: k = q ++ t :: m →
      p = q ∧ s = t ∧ k = m
  | [], [], _, _, _, _, _, _, _, _, h => by
      simp only [List.nil_append, List.cons.injEq] at h
      exact ⟨rfl, h⟩
  | [], b :: q, _, _, _, _, _, hq, hs, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hq b (by simp)) (by rw [hs]; decide)
  | a :: p, [], _, _, _, _, hp, _, _, ht, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hp a (by simp)) (by rw [ht]; decide)
  | a :: p, b :: q, _, _, _, _, hp, hq, hs, ht, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hab, h'⟩ := h
      obtain ⟨e₁, e₂, e₃⟩ := ppath_level (fun s' hs' => hp s' (by simp [hs']))
        (fun s' hs' => hq s' (by simp [hs'])) hs ht h'
      exact ⟨by rw [hab, e₁], e₂, e₃⟩

/-- The index map of an arrow at an item is the item's image. -/
theorem arrowIdx_item {img : ℕ → ℕ} {u : VarSymb} (hu : PPath u.path) :
    arrowIdx img (.step u .box) = itemAt (imgRoot img u.rt) u := by
  have h := itemPath_item hu []
  rw [List.append_nil] at h
  unfold arrowIdx
  change (VarSymb.root (imgRoot img u.rt)).ext (itemPath ((VarSymb.step u .box).ext []).path) = _
  rw [h]
  rfl

theorem coh_arrowS [ModalSys.NoFour] {σ : Signature} {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) : Subst.Coh (arrowIdx img) (ctxOf l).boxIn (arrowS σ Δ img) := by
  refine Subst.coh_of (ok_arrowS himg) ?_
  intro v T _ hv p
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  change (itemImg img u).ext p = (VarSymb.root (imgRoot img _)).ext _
  rw [itemPath_item (reach_ppath hu).1 p, VarSymb.ext_rt,
    VarSymb.ext_append (VarSymb.root _) (encPath u.path ++ itemTail) p]
  rfl

/-! ## The renaming of a witness arrow -/

/-- ⭐The renaming of an arrow into the extent of `x`: items as for `□`, and `x.dia` to the
    variable `cx` holding `x`'s content. -/
def arrowXS (σ : Signature) (Δ : Ctx) (img : ℕ → ℕ) (x : VarSymb) (cx : ℕ) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => .ren (itemImg img u)
  | .step u .dia => if u = x then .ren (.root (.free cx)) else .hide
  | _ => .hide

open Classical in
/-- Where a witness arrow sends annotation indices: below `x.dia` to below `cx`. -/
noncomputable def arrowXIdx (img : ℕ → ℕ) (x : VarSymb) (cx : ℕ) (a : VarSymb) : VarSymb :=
  if a.rt = x.rt ∧ (x.path ++ [Step.dia]) <+: a.path then
    (VarSymb.root (.free cx)).ext (a.path.drop (x.path.length + 1))
  else arrowIdx img a

theorem diaIn_item [ModalSys.NoFour] {l : List VarType} {x v : VarSymb} {T : VarType}
    (h : ((ctxOf l).diaIn x) v = some T) :
    (∃ u, v = .step u .box ∧ (ctxOf l).ref u = some (.VTypeBox T)) ∨
      (v = .step x .dia ∧ (ctxOf l).ref x = some (.VTypeDia T)) := by
  match v with
  | .step u .dia =>
      change (if u = x then (match (ctxOf l).ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at h
      split_ifs at h with hux
      · subst hux
        refine Or.inr ⟨rfl, ?_⟩
        cases hx : (ctxOf l).ref u with
        | none => rw [hx] at h; cases h
        | some U =>
            rw [hx] at h
            cases U <;> cases h
            rfl
  | .step u .box => exact Or.inl (boxIn_item (l := l) h)
  | .step u .keep => exact Or.inl (boxIn_item (l := l) h)
  | .root r => exact Or.inl (boxIn_item (l := l) h)
  | .step u .fst => exact Or.inl (boxIn_item (l := l) h)
  | .step u .snd => exact Or.inl (boxIn_item (l := l) h)
  | .step u .here => exact Or.inl (boxIn_item (l := l) h)

theorem ok_arrowXS [ModalSys.NoFour] {σ : Signature} {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) :
    Subst.Ok ((ctxOf l).diaIn x) (arrowXS σ Δ img x cx) := by
  intro v T _ hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, hxT⟩
  · exact ok_arrowS (σ := σ) himg (.step u .box) T rfl
      (by rw [Ctx.boxIn_box_of ModalSys.NoFour.keepOnly hu])
  · rw [hx] at hxT
    cases hxT
    change (if x = x then SubE.ren (.root (.free cx)) else .hide).OkRef X
    rw [if_pos rfl]
    exact hcx

theorem coh_arrowXS [ModalSys.NoFour] {σ : Signature} {l : List VarType} {Δ : Ctx}
    {img : ℕ → ℕ} (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType}
    (hx : (ctxOf l).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : Δ.ref (.root (.free cx)) = some X) :
    Subst.Coh (arrowXIdx img x cx) ((ctxOf l).diaIn x) (arrowXS σ Δ img x cx) := by
  have hxp := (reach_ppath hx).1
  refine Subst.coh_of (ok_arrowXS himg hx hcx) ?_
  intro v T _ hv p
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
  · have hup := (reach_ppath hu).1
    have hnot : ¬ (((VarSymb.step u .box).ext p).rt = x.rt ∧
        (x.path ++ [Step.dia]) <+: ((VarSymb.step u .box).ext p).path) := by
      rintro ⟨_, k, hk⟩
      rw [VarSymb.ext_path] at hk
      change x.path ++ [Step.dia] ++ k = u.path ++ [Step.box] ++ p at hk
      simp only [List.append_assoc, List.singleton_append] at hk
      -- The first level step of `u.box.p` is the `box` after `u`; of `x.dia.k`, the `dia`.
      exact absurd (ppath_level hxp hup rfl rfl hk).2.1 (by simp)
    change (itemImg img u).ext p = arrowXIdx img x cx _
    rw [arrowXIdx, if_neg hnot, arrowIdx, itemPath_item hup p, VarSymb.ext_rt,
      VarSymb.ext_append (VarSymb.root _) (encPath u.path ++ itemTail) p]
    rfl
  · change (if x = x then SubE.ren (.root (.free cx)) else .hide).idxAlong p = _
    rw [if_pos rfl]
    have hpre : ((VarSymb.step x .dia).ext p).rt = x.rt ∧
        (x.path ++ [Step.dia]) <+: ((VarSymb.step x .dia).ext p).path :=
      ⟨VarSymb.ext_rt _ _, ⟨p, by rw [VarSymb.ext_path]; rfl⟩⟩
    change (VarSymb.root (.free cx)).ext p = arrowXIdx img x cx _
    rw [arrowXIdx, if_pos hpre, VarSymb.ext_path]
    change _ = (VarSymb.root (.free cx)).ext ((x.path ++ [Step.dia] ++ p).drop (x.path.length + 1))
    have hl : x.path.length + 1 = (x.path ++ [Step.dia]).length := by simp
    rw [hl, List.drop_left]

end BArrow

end V12M
