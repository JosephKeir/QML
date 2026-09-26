import QML.QML_v12m_ProofSubst

/-!
# QML v12m — B's arrow model: syntax

The canonical model for B (`docs/v12-arrow-canonical.md`) is built from worlds whose contexts
consist of **their own variables only**: the `n`-th variable declared is `free n`, and the types
are a list, newest first (`ctxOf`).  Nothing of another world appears in a world's context; worlds
are linked by **arrows**, which translate the source's `□` view into the target's variables.

An item of the `□` view is `u.box` for a reachable `u : □A`.  In a context of own variables a
reachable address is a root followed by projections (`reach_ppath`), so the items of one root `r`
are the `□`-components of its type.  An arrow sends them all to **one** variable of the target, of
the type `r`'s type has with each `□A` component replaced by `A` and every other leaf by `𝟙`
(`VarType.bc`): the item `r.q.box` goes to `z.q` (`arrowS`, well typed by `ref_reroot_bc`).  So an
arrow is an index map on roots.  A `◇_x` arrow, towards a world in the extent of `x`, also sends
`x.dia` to a variable holding `x`'s content (`arrowXS`).

The construction assumes neither T nor 4 (`ModalSys.NoTFour`): views then show exactly the `box`
items (and `x.dia`).
-/

namespace V12M

/-- The flags of the arrow construction for B: neither T nor 4, so a view shows only `u.box` (and
    `x.dia`), and a reachable address of a context of variables is a projection path. -/
class ModalSys.NoTFour [ModalSys] : Prop where
  noT : ModalSys.T = false
  noFour : ModalSys.Four = false

variable [ModalSys]

theorem ModalSys.NoTFour.keepOnly [ModalSys.NoTFour] : ModalSys.keepOnly = false := by
  simp [ModalSys.keepOnly, ModalSys.NoTFour.noT]

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

/-- A path of projections `fst`/`snd` only. -/
def PPath (p : List Step) : Prop := ∀ s ∈ p, s = .fst ∨ s = .snd

omit [ModalSys] in
theorem PPath.box_not_mem {p : List Step} (h : PPath p) : Step.box ∉ p := fun hm => by
  rcases h _ hm with h' | h' <;> cases h'

omit [ModalSys] in
theorem PPath.dia_not_mem {p : List Step} (h : PPath p) : Step.dia ∉ p := fun hm => by
  rcases h _ hm with h' | h' <;> cases h'

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

/-- In a context of own variables, without T, a reachable address is a declared root followed by
    projections. -/
theorem reach_ppath [ModalSys.NoTFour] {l : List VarType} :
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
            rw [hU] at h
            cases s with
            | fst => exact Or.inl rfl
            | snd => exact Or.inr rfl
            | here =>
                cases U <;> simp [VarType.step, ModalSys.NoTFour.noT] at h
            | box => cases hs
            | dia => cases hs
            | keep => cases hs
      · obtain ⟨r, hr⟩ := ctxOf_decl h
        cases hr

/-! ## Box contents -/

/-- ⭐The type of what an arrow gives a variable of type `T` at the target: each `□A` component
    becomes `A`, every other leaf `𝟙`. -/
def _root_.V12M.VarType.bc : VarType → VarType
  | .Var => .VTypeOne
  | .VTypeOne => .VTypeOne
  | .VTypeProd A B => .VTypeProd A.bc B.bc
  | .VTypeBox A => A
  | .VTypeDia _ => .VTypeOne

theorem bc_step {T U : VarType} {s : Step} (hs : s = .fst ∨ s = .snd) (h : T.step s = some U) :
    T.bc.step s = some U.bc := by
  rcases hs with rfl | rfl <;> cases T <;> cases h <;> rfl

/-- ⭐Rerooting a reachable address at a variable of the `bc` type of its root gives the `bc` type
    of the address. -/
theorem ref_reroot_bc [ModalSys.NoTFour] {l : List VarType} {Δ : Ctx} {z : Root} {R : VarType} :
    ∀ {u : VarSymb} {T : VarType}, (ctxOf l).ref u = some T → (ctxOf l).ref (.root u.rt) = some R →
      Δ.ref (.root z) = some R.bc → Δ.ref (u.reroot z) = some T.bc
  | .root r, T, h, hR, hz => by
      change (ctxOf l).ref (.root r) = some R at hR
      rw [hR] at h
      cases h
      exact hz
  | .step u s, T, h, hR, hz => by
      have hp := (reach_ppath h).1
      have hs : s = .fst ∨ s = .snd := hp s (by simp [VarSymb.path])
      have hproj : s.isProj = true := by rcases hs with rfl | rfl <;> rfl
      simp only [Ctx.ref, if_pos hproj] at h
      cases hU : (ctxOf l).ref u with
      | none => rw [hU] at h; cases h
      | some U =>
          rw [hU] at h
          have ih := ref_reroot_bc hU hR hz
          change Δ.ref (.step (u.reroot z) s) = _
          simp only [Ctx.ref, if_pos hproj, ih, Option.bind_some]
          exact bc_step hs h

/-! ## The renaming of an arrow -/

/-- The image of a root under an index map on variables. -/
def imgRoot (img : ℕ → ℕ) : Root → Root
  | .free r => .free (img r)
  | .bnd n => .bnd n

/-- ⭐The renaming of an arrow: the item `u.box` goes to `u` rerooted at its root's image. -/
def arrowS (σ : Signature) (Δ : Ctx) (img : ℕ → ℕ) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => .ren (u.reroot (imgRoot img u.rt))
  | _ => .hide

/-- Where an arrow sends annotation indices: the first `box` is dropped and the root renamed. -/
def arrowIdx (img : ℕ → ℕ) (a : VarSymb) : VarSymb :=
  (VarSymb.root (imgRoot img a.rt)).ext (a.path.erase .box)

/-- The images of the variables are declared at the `bc` types. -/
def ImgOk (l : List VarType) (Δ : Ctx) (img : ℕ → ℕ) : Prop :=
  ∀ r, r < l.length → Δ.ref (.root (.free (img r))) = some (rootTy l r).bc

theorem boxIn_item [ModalSys.NoTFour] {l : List VarType} {v : VarSymb} {T : VarType}
    (h : (ctxOf l).boxIn v = some T) :
    ∃ u, v = .step u .box ∧ (ctxOf l).ref u = some (.VTypeBox T) := by
  match v with
  | .step u .box => exact ⟨u, rfl, (Ctx.boxIn_box h).2⟩
  | .step u .keep =>
      obtain ⟨hF, _⟩ := Ctx.boxIn_keep h
      rw [ModalSys.NoTFour.noFour] at hF
      cases hF
  | .root _ => cases h
  | .step _ .fst => cases h
  | .step _ .snd => cases h
  | .step _ .dia => cases h
  | .step _ .here => cases h

/-- The root of a reachable address is declared at its own type. -/
theorem ref_rt [ModalSys.NoTFour] {l : List VarType} {u : VarSymb} {T : VarType}
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

theorem ok_arrowS [ModalSys.NoTFour] {σ : Signature} {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) : Subst.Ok (ctxOf l).boxIn (arrowS σ Δ img) := by
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨r, hr, hlt, hR⟩ := ref_rt hu
  change Δ.ref (u.reroot (imgRoot img u.rt)) = some T
  have hz : Δ.ref (.root (imgRoot img u.rt)) = some (rootTy l r).bc := by
    rw [hr]
    exact himg r hlt
  exact ref_reroot_bc hu hR hz

omit [ModalSys] in
/-- Two projection paths, each followed by a level step, agree only if the paths and the steps
    do. -/
theorem ppath_level : ∀ {p q : List Step} {s t : Step} {k m : List Step}, PPath p → PPath q →
    ¬ (s = .fst ∨ s = .snd) → ¬ (t = .fst ∨ t = .snd) → p ++ s :: k = q ++ t :: m →
      p = q ∧ s = t ∧ k = m
  | [], [], _, _, _, _, _, _, _, _, h => by
      simp only [List.nil_append, List.cons.injEq] at h
      exact ⟨rfl, h⟩
  | [], b :: q, _, _, _, _, _, hq, hs, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hq b (by simp)) hs
  | a :: p, [], _, _, _, _, hp, _, _, ht, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hp a (by simp)) ht
  | a :: p, b :: q, _, _, _, _, hp, hq, hs, ht, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hab, h'⟩ := h
      obtain ⟨e₁, e₂, e₃⟩ := ppath_level (fun s' hs' => hp s' (by simp [hs']))
        (fun s' hs' => hq s' (by simp [hs'])) hs ht h'
      exact ⟨by rw [hab, e₁], e₂, e₃⟩

omit [ModalSys] in
theorem erase_box_item {u : VarSymb} (hu : PPath u.path) (p : List Step) :
    ((VarSymb.step u .box).ext p).path.erase .box = u.path ++ p := by
  rw [VarSymb.ext_path]
  change (u.path ++ [Step.box] ++ p).erase .box = u.path ++ p
  rw [List.append_assoc, List.erase_append_right _ hu.box_not_mem]
  simp

theorem coh_arrowS [ModalSys.NoTFour] {σ : Signature} {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) : Subst.Coh (arrowIdx img) (ctxOf l).boxIn (arrowS σ Δ img) := by
  refine Subst.coh_of (ok_arrowS himg) ?_
  intro v T _ hv p
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  change (u.reroot (imgRoot img u.rt)).ext p = (VarSymb.root (imgRoot img _)).ext _
  rw [erase_box_item (reach_ppath hu).1 p, VarSymb.ext_rt, VarSymb.ext_append,
    VarSymb.reroot_eq]
  rfl

/-! ## The renaming of a witness arrow -/

/-- ⭐The renaming of an arrow into the extent of `x`: items as for `□`, and `x.dia` to the
    variable `cx` holding `x`'s content. -/
def arrowXS (σ : Signature) (Δ : Ctx) (img : ℕ → ℕ) (x : VarSymb) (cx : ℕ) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => .ren (u.reroot (imgRoot img u.rt))
  | .step u .dia => if u = x then .ren (.root (.free cx)) else .hide
  | _ => .hide

open Classical in
/-- Where a witness arrow sends annotation indices: below `x.dia` to below `cx`. -/
noncomputable def arrowXIdx (img : ℕ → ℕ) (x : VarSymb) (cx : ℕ) (a : VarSymb) : VarSymb :=
  if a.rt = x.rt ∧ (x.path ++ [Step.dia]) <+: a.path then
    (VarSymb.root (.free cx)).ext (a.path.drop (x.path.length + 1))
  else arrowIdx img a

theorem diaIn_item [ModalSys.NoTFour] {l : List VarType} {x v : VarSymb} {T : VarType}
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

theorem ok_arrowXS [ModalSys.NoTFour] {σ : Signature} {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X))
    {cx : ℕ} (hcx : Δ.ref (.root (.free cx)) = some X) :
    Subst.Ok ((ctxOf l).diaIn x) (arrowXS σ Δ img x cx) := by
  intro v T _ hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, hxT⟩
  · exact ok_arrowS (σ := σ) himg (.step u .box) T rfl
      (by rw [Ctx.boxIn_box_of ModalSys.NoTFour.keepOnly hu])
  · rw [hx] at hxT
    cases hxT
    change (if x = x then SubE.ren (.root (.free cx)) else .hide).OkRef X
    rw [if_pos rfl]
    exact hcx

theorem coh_arrowXS [ModalSys.NoTFour] {σ : Signature} {l : List VarType} {Δ : Ctx}
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
      exact absurd (ppath_level hxp hup (by simp) (by simp) hk).2.1 (by simp)
    change (u.reroot (imgRoot img u.rt)).ext p = arrowXIdx img x cx _
    rw [arrowXIdx, if_neg hnot, arrowIdx, erase_box_item hup p, VarSymb.ext_rt,
      VarSymb.ext_append, VarSymb.reroot_eq]
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
