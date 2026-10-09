import QML.QML_v12m_BSyntax

/-!
# QML v12m — B's arrow model: abstracting a variable's items

Realising a new variable `c : A` of the source along an arrow needs two identities between
formulas of the source's `□` view (with `c` the newest variable, `l.length`):

* ⭐`instantiate_tup_abs`: a formula `ψ` is its **abstraction** (`absS`: `c`'s items become the
  components of the slot `bnd 0 : A.bc`, every other item stays) instantiated at the **tuple** of
  `c`'s items (`tup`).  So `□ψ` gives `□∃y. ψ̃(y)`, a formula about the older variables only.
* ⭐`subst_arrow_abs`: the arrow extended by `c ↦ z` sends `ψ` to the abstraction sent by the old
  arrow and opened at `z` — the Henkin instance the target realises.

Under T a `□` component's items include those of its value here (`VarType.bc`), so the tuple
carries them too (`tupB`), and an item lands where `itemAt` says (`docs/v12-arrow-canonical.md`
§9.2).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The tuple of a variable's items -/

/-- The annotation of `tupB`. -/
def tupAnnB : VarSymb → (R : VarType) → (b : Bool) → Ann (R.bcB b)
  | _, .Var, _ => .one
  | _, .VTypeOne, _ => .one
  | u, .VTypeProd A B, b => .prod (tupAnnB (.step u .fst) A b) (tupAnnB (.step u .snd) B b)
  | u, .VTypeBox A, true => .prod (Ann.eta (.step u .box) A) (tupAnnB (.step u .here) A true)
  | u, .VTypeBox A, false => Ann.eta (.step u .box) A
  | _, .VTypeDia _, _ => .one

/-- The items of `u : R` as one term of the `□` view, for a value `b` of the T flag: under T a
    `□A` component contributes its box contents and, second, the items of its value here.  The
    flag is an argument so that the type `R.bcB b` reduces by matching on it. -/
def tupB [ModalSys.NoFour] {Γ : Ctx} : (u : VarSymb) → (R : VarType) → (b : Bool) →
    ModalSys.T = b → Γ.ref u = some R → Term σ Γ.boxIn (R.bcB b) (tupAnnB u R b)
  | _, .Var, _, _, _ => .unit
  | _, .VTypeOne, _, _, _ => .unit
  | u, .VTypeProd A B, b, hb, h =>
      .pair (tupB (.step u .fst) A b hb (Ctx.ref_fst_of h))
        (tupB (.step u .snd) B b hb (Ctx.ref_snd_of h))
  | u, .VTypeBox A, true, hb, h =>
      .pair (Term.eta (.step u .box) A (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly h))
        (tupB (.step u .here) A true hb (Ctx.ref_here_of hb h))
  | u, .VTypeBox A, false, _, h =>
      Term.eta (.step u .box) A (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly h)
  | _, .VTypeDia _, _, _, _ => .unit

/-- The annotation of `tup`. -/
abbrev tupAnn (u : VarSymb) (R : VarType) : Ann R.bc := tupAnnB u R ModalSys.T

/-- ⭐The items of `u : R`, as one term of the `□` view of type `R.bc`. -/
abbrev tup [ModalSys.NoFour] {Γ : Ctx} (u : VarSymb) (R : VarType) (h : Γ.ref u = some R) :
    Term σ Γ.boxIn R.bc (tupAnn u R) :=
  tupB u R ModalSys.T rfl h

/-! ## Abstraction -/

/-- Abstracting the variable `c`: its items go to the components of `bnd 0`, the others stay. -/
def absS (σ : Signature) (Δ : Ctx) (c : ℕ) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => if u.rt = .free c then .ren (itemAt (.bnd 0) u) else .ren (.step u .box)
  | _ => .hide

open Classical in
/-- Where abstraction sends annotation indices. -/
noncomputable def absIdx (c : ℕ) (a : VarSymb) : VarSymb :=
  if a.rt = .free c then (VarSymb.root (.bnd 0)).ext (itemPath a.path) else a

/-- The context of the abstracted formula: the older variables' view and the slot. -/
abbrev absCtx (A : VarType) (l : List VarType) : Ctx := (ctxOf l).boxIn.insert (.bnd 0) A.bc

theorem absCtx_slots (A : VarType) (l : List VarType) : (absCtx A l).SlotsFrom 1 :=
  (Ctx.NoSlots.slots (Γ := (ctxOf l).boxIn)).insert A.bc

/-- The newest variable is declared at its type. -/
theorem ctxOf_ref_new (A : VarType) (l : List VarType) :
    (ctxOf (A :: l)).ref (.root (.free l.length)) = some A :=
  Ctx.ref_insert_root _ _ A

/-- An older variable's addresses are reached as before. -/
theorem ctxOf_ref_old {A : VarType} {l : List VarType} {u : VarSymb}
    (h : u.rt ≠ .free l.length) : (ctxOf (A :: l)).ref u = (ctxOf l).ref u :=
  Ctx.ref_insert_ne A h

theorem ok_absS [ModalSys.NoFour] (A : VarType) (l : List VarType) :
    Subst.Ok (ctxOf (A :: l)).boxIn (absS σ (absCtx A l) l.length) := by
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  change (if u.rt = .free l.length then SubE.ren (itemAt (.bnd 0) u)
    else .ren (.step u .box)).OkRef T
  split_ifs with hrt
  · change (absCtx A l).ref (itemAt (.bnd 0) u) = some T
    exact ref_item hu (by rw [hrt]; exact ctxOf_ref_new A l) (Ctx.ref_insert_root _ _ _)
  · change (absCtx A l).ref (.step u .box) = some T
    obtain ⟨r, hr⟩ := (reach_ppath hu).2
    rw [Ctx.ref_insert_ne _ (fun h => by
      change u.rt = _ at h
      rw [hr] at h
      cases h)]
    rw [ctxOf_ref_old hrt] at hu
    exact Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hu

theorem coh_absS [ModalSys.NoFour] (A : VarType) (l : List VarType) :
    Subst.Coh (absIdx l.length) (ctxOf (A :: l)).boxIn (absS σ (absCtx A l) l.length) := by
  refine Subst.coh_of (ok_absS A l) ?_
  intro v T _ hv p
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  change (if u.rt = .free l.length then SubE.ren (itemAt (.bnd 0) u)
    else .ren (.step u .box)).idxAlong p = absIdx l.length _
  have hrt' : ((VarSymb.step u .box).ext p).rt = u.rt := VarSymb.ext_rt _ _
  split_ifs with hrt
  · change (itemAt (.bnd 0) u).ext p = _
    rw [absIdx, if_pos (hrt'.trans hrt), itemPath_item (reach_ppath hu).1 p,
      VarSymb.ext_append (VarSymb.root (.bnd 0)) (encPath u.path ++ itemTail) p]
    rfl
  · change (VarSymb.step u .box).ext p = _
    rw [absIdx, if_neg (fun h => hrt (hrt'.symm.trans h))]

/-- Weakening the abstracted context into the new variable's context. -/
theorem absCtx_le (A : VarType) (l : List VarType) :
    (absCtx A l).Le ((ctxOf (A :: l)).boxIn.insert (.bnd 0) A.bc) :=
  ((ctxOf_le_append [A] l).boxIn).insert (.bnd 0) A.bc

/-- ⭐The abstraction of a formula of the new `□` view. -/
noncomputable def abs [ModalSys.NoFour] (A : VarType) (l : List VarType)
    (ψ : WFF σ (ctxOf (A :: l)).boxIn 0) : WFF σ (absCtx A l) 1 :=
  WFF.subst (absIdx l.length) (absS σ (absCtx A l) l.length) (ok_absS A l) (coh_absS A l)
    Ctx.NoSlots.slots (absCtx_slots A l) ψ

/-! ## Instantiating the abstraction at the tuple -/

theorem encStep_fst : encStep .fst = .fst := by unfold encStep; split <;> rfl

theorem encStep_snd : encStep .snd = .snd := by unfold encStep; split <;> rfl

theorem encStep_here (hT : ModalSys.T = true) : encStep .here = .snd := by
  simp [encStep, hT]

/-- ⭐Projecting a tuple along an encoded projection step gives the tuple of the projected
    address: a product's tuple is a pair, and under T a `□` component's tuple has its value
    here's tuple second. -/
theorem proj_tupB [ModalSys.NoFour] {Γ : Ctx} {u : VarSymb} {U U' : VarType} {b : Bool}
    (hb : ModalSys.T = b) (hu : Γ.ref u = some U) {s : Step} (hs : s.isProj = true)
    (h' : U.step s = some U') (hu' : Γ.ref (.step u s) = some U') :
    (SubE.tm (tupB (σ := σ) u U b hb hu) : SubE σ Γ.boxIn).proj (encStep s) =
      .tm (tupB (.step u s) U' b hb hu') := by
  cases s with
  | fst =>
      rw [encStep_fst]
      cases U with
      | VTypeProd X Y => cases h'; rfl
      | _ => cases h'
  | snd =>
      rw [encStep_snd]
      cases U with
      | VTypeProd X Y => cases h'; rfl
      | _ => cases h'
  | here =>
      cases U with
      | VTypeBox X =>
          obtain ⟨hT, rfl⟩ := VarType.step_here h'
          obtain rfl : b = true := hb.symm.trans hT
          rw [encStep_here hT]
          rfl
      | _ => cases h'
  | _ => exact absurd hs (by decide)

/-- ⭐A substitution whose entry at an encoded address is the tuple of `u : □T` reads, at `u`'s
    item's image, the item itself. -/
theorem at_item_of_tupB [ModalSys.NoFour] {Γ : Ctx} (θ : Subst σ Γ.boxIn) (z : Root)
    {u : VarSymb} {T : VarType} (hu : Γ.ref u = some (.VTypeBox T)) (b : Bool)
    (hb : ModalSys.T = b)
    (h : θ.at ((VarSymb.root z).ext (encPath u.path)) = .tm (tupB u (.VTypeBox T) b hb hu)) :
    θ.at (itemAt z u) =
      .tm (Term.eta (.step u .box) T (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hu)) := by
  rw [itemAt, VarSymb.ext_append]
  cases b with
  | true =>
      rw [show itemTail = [Step.fst] by simp [itemTail, hb]]
      change θ.at (.step ((VarSymb.root z).ext (encPath u.path)) .fst) = _
      rw [Subst.at_proj _ _ rfl, h]
      rfl
  | false =>
      rw [show itemTail = [] by simp [itemTail, hb]]
      exact h

/-- `proj_tupB` for a tuple weakened into a larger context. -/
theorem proj_tupB_mono [ModalSys.NoFour] {Γ Δ : Ctx} (hle : Γ.boxIn.Le Δ) {u : VarSymb}
    {U U' : VarType} {b : Bool} (hb : ModalSys.T = b) (hu : Γ.ref u = some U) {s : Step}
    (hs : s.isProj = true) (h' : U.step s = some U') (hu' : Γ.ref (.step u s) = some U') :
    (SubE.tm (Term.mono hle (tupB (σ := σ) u U b hb hu)) : SubE σ Δ).proj (encStep s) =
      .tm (Term.mono hle (tupB (.step u s) U' b hb hu')) := by
  cases s with
  | fst =>
      rw [encStep_fst]
      cases U with
      | VTypeProd X Y => cases h'; rfl
      | _ => cases h'
  | snd =>
      rw [encStep_snd]
      cases U with
      | VTypeProd X Y => cases h'; rfl
      | _ => cases h'
  | here =>
      cases U with
      | VTypeBox X =>
          obtain ⟨hT, rfl⟩ := VarType.step_here h'
          obtain rfl : b = true := hb.symm.trans hT
          rw [encStep_here hT]
          rfl
      | _ => cases h'
  | _ => exact absurd hs (by decide)

/-- `at_item_of_tupB` for a tuple weakened into a larger context. -/
theorem at_item_of_tupB_mono [ModalSys.NoFour] {Γ Δ : Ctx} (hle : Γ.boxIn.Le Δ)
    (θ : Subst σ Δ) (z : Root) {u : VarSymb} {T : VarType} (hu : Γ.ref u = some (.VTypeBox T))
    (b : Bool) (hb : ModalSys.T = b)
    (h : θ.at ((VarSymb.root z).ext (encPath u.path)) =
      .tm (Term.mono hle (tupB u (.VTypeBox T) b hb hu))) :
    θ.at (itemAt z u) = .tm (Term.mono hle
      (Term.eta (.step u .box) T (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hu))) := by
  rw [itemAt, VarSymb.ext_append]
  cases b with
  | true =>
      rw [show itemTail = [Step.fst] by simp [itemTail, hb]]
      change θ.at (.step ((VarSymb.root z).ext (encPath u.path)) .fst) = _
      rw [Subst.at_proj _ _ rfl, h]
      rfl
  | false =>
      rw [show itemTail = [] by simp [itemTail, hb]]
      exact h

/-- Projecting the tuple entry along an encoded path from the slot reaches the tuple of the
    component. -/
theorem at_single_tupB [ModalSys.NoFour] (b : Bool) (hb : ModalSys.T = b) {A : VarType}
    {l : List VarType} :
    ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf (A :: l)).ref u = some U),
      u.rt = .free l.length →
      (Subst.single (σ := σ) (Δ := (ctxOf (A :: l)).boxIn) (.bnd 0)
        (.tm (tupB (.root (.free l.length)) A b hb (ctxOf_ref_new A l)))).at
          ((VarSymb.root (.bnd 0)).ext (encPath u.path)) = .tm (tupB u U b hb hu)
  | .root r, U, hu, hrt => by
      change VarSymb.rt (.root r) = _ at hrt
      subst hrt
      rw [ctxOf_ref_new] at hu
      cases hu
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
  | .step u s, U, hu, hrt => by
      have hproj : s.isProj = true := (reach_ppath hu).1 s (by simp [VarSymb.path])
      have hu' := hu
      simp only [Ctx.ref, if_pos hproj] at hu'
      cases hU : (ctxOf (A :: l)).ref u with
      | none => rw [hU] at hu'; cases hu'
      | some U' =>
          rw [hU] at hu'
          have ih := at_single_tupB b hb hU hrt
          change (Subst.single (.bnd 0) _).at
            ((VarSymb.root (.bnd 0)).ext (encPath (u.path ++ [s]))) = _
          rw [show encPath (u.path ++ [s]) = encPath u.path ++ [encStep s] from
            List.map_append, VarSymb.ext_step, Subst.at_proj _ _ (encStep_proj hproj), ih]
          cases s with
          | fst =>
              rw [encStep_fst]
              cases U' with
              | VTypeProd X Y => cases hu'; rfl
              | _ => cases hu'
          | snd =>
              rw [encStep_snd]
              cases U' with
              | VTypeProd X Y => cases hu'; rfl
              | _ => cases hu'
          | here =>
              cases U' with
              | VTypeBox X =>
                  obtain ⟨hT, rfl⟩ := VarType.step_here hu'
                  obtain rfl : b = true := hb.symm.trans hT
                  rw [encStep_here hT]
                  rfl
              | _ => cases hu'
          | _ => exact absurd hproj (by decide)

/-- The tuple entry read at an item's image is the item. -/
theorem at_single_item [ModalSys.NoFour] (b : Bool) (hb : ModalSys.T = b) {A : VarType}
    {l : List VarType} {u : VarSymb} {T : VarType}
    (hu : (ctxOf (A :: l)).ref u = some (.VTypeBox T)) (hrt : u.rt = .free l.length) :
    (Subst.single (σ := σ) (Δ := (ctxOf (A :: l)).boxIn) (.bnd 0)
      (.tm (tupB (.root (.free l.length)) A b hb (ctxOf_ref_new A l)))).at (itemAt (.bnd 0) u) =
      .tm (Term.eta (.step u .box) T (Ctx.ref_boxIn_of ModalSys.NoFour.keepOnly hu)) := by
  have ih := at_single_tupB (σ := σ) b hb hu hrt
  rw [itemAt, VarSymb.ext_append]
  cases b with
  | true =>
      rw [show itemTail = [Step.fst] by simp [itemTail, hb]]
      change (Subst.single _ _).at (.step ((VarSymb.root (.bnd 0)).ext (encPath u.path)) .fst) = _
      rw [Subst.at_proj _ _ rfl, ih]
      rfl
  | false =>
      rw [show itemTail = [] by simp [itemTail, hb]]
      exact ih

/-- ⭐A formula of the new `□` view is its abstraction instantiated at the tuple of the new
    variable's items. -/
theorem instantiate_tup_abs [ModalSys.NoFour] (A : VarType) (l : List VarType)
    (ψ : WFF σ (ctxOf (A :: l)).boxIn 0) :
    WFF.instantiate Ctx.NoSlots.slots (tup (.root (.free l.length)) A (ctxOf_ref_new A l))
      (WFF.mono (absCtx_le A l) (abs A l ψ)) = ψ := by
  have hs : ((ctxOf (A :: l)).boxIn.insert (.bnd 0) A.bc).SlotsFrom 1 :=
    (Ctx.NoSlots.slots (Γ := (ctxOf (A :: l)).boxIn)).insert A.bc
  unfold WFF.instantiate WFF.substRoot abs
  rw [WFF.subst_mono (absCtx_le A l) _ _ _ (absCtx_slots A l) hs]
  refine (WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ Subst.ok_idS Subst.coh_idS _ _ _ ?_ ψ).trans
    (WFF.subst_id _ _ _ ψ)
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  change SubE.Sim T (.ren (.step u .box)) ((absS σ (absCtx A l) l.length (.step u .box)).comp _ _ _)
  change SubE.Sim T _ ((if u.rt = .free l.length then SubE.ren (itemAt (.bnd 0) u)
    else .ren (.step u .box)).comp _ _ _)
  split_ifs with hrt
  · change SubE.Sim T _ ((Subst.single (.bnd 0) _).at (itemAt (.bnd 0) u))
    rw [at_single_item ModalSys.T rfl hu hrt]
    exact .ren_eta _ _
  · change SubE.Sim T _ ((Subst.single (.bnd 0) _).at (.step u .box))
    rw [Subst.single_at_ne (by
      change u.rt ≠ _
      obtain ⟨r, hr⟩ := (reach_ppath hu).2
      rw [hr]
      exact fun h => by cases h)]
    exact .refl _

/-! ## The extended arrow is the old one opened at the new variable -/

/-- An index map extended by `c ↦ z`. -/
def extImg (img : ℕ → ℕ) (c z : ℕ) : ℕ → ℕ := fun r => if r = c then z else img r

omit [ModalSys] in
theorem rootTy_new (A : VarType) (l : List VarType) : rootTy (A :: l) l.length = A := by
  simp [rootTy, List.getD_eq_getElem?_getD]

omit [ModalSys] in
theorem rootTy_old {A : VarType} {l : List VarType} {r : ℕ} (h : r < l.length) :
    rootTy (A :: l) r = rootTy l r := by
  simp only [rootTy, List.reverse_cons, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using h)]

theorem imgOk_ext {A : VarType} {ls lt : List VarType} {img : ℕ → ℕ}
    (himg : ImgOk ls (ctxOf lt) img) :
    ImgOk (A :: ls) (ctxOf (A.bc :: lt)) (extImg img ls.length lt.length) := by
  intro r hr
  by_cases hrc : r = ls.length
  · subst hrc
    rw [rootTy_new]
    change (ctxOf (A.bc :: lt)).ref (.root (.free (if ls.length = ls.length then _ else _))) = _
    rw [if_pos rfl]
    exact ctxOf_ref_new A.bc lt
  · have hlt : r < ls.length := by
      change r < ls.length + 1 at hr
      omega
    rw [rootTy_old hlt]
    change (ctxOf (A.bc :: lt)).ref (.root (.free (if r = ls.length then _ else _))) = _
    rw [if_neg hrc]
    exact (ctxOf_le_append [A.bc] lt).ref (himg r hlt)

/-- A renaming entry at the slot, projected along a path, renames the projected address. -/
theorem at_toFree_reroot {Δ : Ctx} (θ : Subst σ Δ) (z : ℕ) (T : VarType)
    (h : Δ (.root (.free z)) = none) :
    ∀ u : VarSymb, PPath u.path →
      (θ.toFree 0 z T h).at (u.reroot (.bnd 0)) = .ren (u.reroot (.free z))
  | .root _, _ => by
      change θ.toFree 0 z T h (.root (.bnd 0)) = .ren (.root (.free z))
      exact if_pos rfl
  | .step u s, hp => by
      have hproj : s.isProj = true := hp s (by simp [VarSymb.path])
      change (θ.toFree 0 z T h).at (.step (u.reroot (.bnd 0)) s) = .ren (.step (u.reroot _) s)
      rw [Subst.at_proj _ _ hproj,
        at_toFree_reroot θ z T h u (fun s' hs' => hp s' (by simp [VarSymb.path, hs']))]
      rfl

theorem itemAt_reroot (z z' : Root) (u : VarSymb) : (itemAt z u).reroot z' = itemAt z' u := by
  rw [VarSymb.reroot_eq, itemAt_path]
  rfl

/-- ⭐The arrow extended by the new variable's image is the old arrow applied to the abstraction,
    with the slot sent to the image. -/
theorem subst_arrow_abs [ModalSys.NoFour] {A : VarType} {ls lt : List VarType} {img : ℕ → ℕ}
    (himg : ImgOk ls (ctxOf lt) img) (ψ : WFF σ (ctxOf (A :: ls)).boxIn 0) :
    WFF.subst (arrowIdx (extImg img ls.length lt.length))
        (arrowS σ (ctxOf (A.bc :: lt)) (extImg img ls.length lt.length))
        (ok_arrowS (imgOk_ext himg)) (coh_arrowS (imgOk_ext himg)) Ctx.NoSlots.slots
        Ctx.NoSlots.slots ψ =
      WFF.subst (VarSymb.slotToFree (arrowIdx img) 0 lt.length)
        ((arrowS σ (ctxOf lt) img).toFree 0 lt.length A.bc (ctxOf_fresh le_rfl).root)
        (Subst.ok_toFree (ok_arrowS himg) A.bc _)
        (Subst.coh_toFree (ok_arrowS himg) (coh_arrowS himg) Ctx.NoSlots.slots A.bc _)
        (absCtx_slots A ls) Ctx.NoSlots.slots (abs A ls ψ) := by
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ ψ).symm
  refine Subst.sim_of ?_
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  obtain ⟨hup, r, hr⟩ := reach_ppath hu
  change SubE.Sim T (.ren (itemAt (imgRoot _ u.rt) u))
    ((if u.rt = .free ls.length then SubE.ren (itemAt (.bnd 0) u)
      else .ren (.step u .box)).comp _ _ _)
  split_ifs with hrt
  · change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.bc _).at (itemAt (.bnd 0) u))
    have hat := at_toFree_reroot (arrowS σ (ctxOf lt) img) lt.length A.bc
      (ctxOf_fresh le_rfl).root (itemAt (.bnd 0) u) (itemAt_ppath hup _)
    rw [itemAt_reroot, itemAt_reroot] at hat
    rw [hat, hrt]
    change SubE.Sim T (.ren (itemAt (.free (if ls.length = ls.length then _ else _)) u)) _
    rw [if_pos rfl]
    exact .refl _
  · change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.bc _).at (.step u .box))
    rw [Subst.at_nonproj _ (rfl : (VarSymb.step u .box).lastProj = false)]
    change SubE.Sim T _ (if VarSymb.step u .box = .root (.bnd 0) then _ else _)
    rw [if_neg (fun h => by cases h)]
    change SubE.Sim T _ (.ren (itemAt (imgRoot img u.rt) u))
    rw [hr]
    have hrc : r ≠ ls.length := fun h => hrt (by rw [hr, h])
    change SubE.Sim T (.ren (itemAt (.free (if r = ls.length then _ else _)) u)) _
    rw [if_neg hrc]
    exact .refl _

end BArrow

end V12M
