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
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The tuple of a variable's items -/

/-- The annotation of `tup`. -/
def tupAnn : VarSymb → (R : VarType) → Ann R.bc
  | _, .Var => .one
  | _, .VTypeOne => .one
  | u, .VTypeProd A B => .prod (tupAnn (.step u .fst) A) (tupAnn (.step u .snd) B)
  | u, .VTypeBox A => Ann.eta (.step u .box) A
  | _, .VTypeDia _ => .one

/-- ⭐The items of `u : R`, as one term of the `□` view of type `R.bc`. -/
def tup [ModalSys.NoTFour] {Γ : Ctx} : (u : VarSymb) → (R : VarType) → Γ.ref u = some R →
    Term σ Γ.boxIn R.bc (tupAnn u R)
  | _, .Var, _ => .unit
  | _, .VTypeOne, _ => .unit
  | u, .VTypeProd A B, h =>
      .pair (tup (.step u .fst) A (Ctx.ref_fst_of h)) (tup (.step u .snd) B (Ctx.ref_snd_of h))
  | u, .VTypeBox A, h => Term.eta (.step u .box) A (Ctx.ref_boxIn_of ModalSys.NoTFour.keepOnly h)
  | _, .VTypeDia _, _ => .unit

/-! ## Abstraction -/

/-- Abstracting the variable `c`: its items go to the components of `bnd 0`, the others stay. -/
def absS (σ : Signature) (Δ : Ctx) (c : ℕ) : Subst σ Δ := fun v =>
  match v with
  | .step u .box => if u.rt = .free c then .ren (u.reroot (.bnd 0)) else .ren (.step u .box)
  | _ => .hide

open Classical in
/-- Where abstraction sends annotation indices. -/
noncomputable def absIdx (c : ℕ) (a : VarSymb) : VarSymb :=
  if a.rt = .free c then (VarSymb.root (.bnd 0)).ext (a.path.erase .box) else a

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

theorem ok_absS [ModalSys.NoTFour] (A : VarType) (l : List VarType) :
    Subst.Ok (ctxOf (A :: l)).boxIn (absS σ (absCtx A l) l.length) := by
  intro v T _ hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  change (if u.rt = .free l.length then SubE.ren (u.reroot (.bnd 0))
    else .ren (.step u .box)).OkRef T
  split_ifs with hrt
  · change (absCtx A l).ref (u.reroot (.bnd 0)) = some T
    exact ref_reroot_bc (T := .VTypeBox T) hu (by rw [hrt]; exact ctxOf_ref_new A l)
      (Ctx.ref_insert_root _ _ _)
  · change (absCtx A l).ref (.step u .box) = some T
    obtain ⟨r, hr⟩ := (reach_ppath hu).2
    rw [Ctx.ref_insert_ne _ (fun h => by
      change u.rt = _ at h
      rw [hr] at h
      cases h)]
    rw [ctxOf_ref_old hrt] at hu
    exact Ctx.ref_boxIn_of ModalSys.NoTFour.keepOnly hu

theorem coh_absS [ModalSys.NoTFour] (A : VarType) (l : List VarType) :
    Subst.Coh (absIdx l.length) (ctxOf (A :: l)).boxIn (absS σ (absCtx A l) l.length) := by
  refine Subst.coh_of (ok_absS A l) ?_
  intro v T _ hv p
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  change (if u.rt = .free l.length then SubE.ren (u.reroot (.bnd 0))
    else .ren (.step u .box)).idxAlong p = absIdx l.length _
  have hrt' : ((VarSymb.step u .box).ext p).rt = u.rt := VarSymb.ext_rt _ _
  split_ifs with hrt
  · change (u.reroot (.bnd 0)).ext p = _
    rw [absIdx, if_pos (hrt'.trans hrt), erase_box_item (reach_ppath hu).1 p,
      VarSymb.ext_append, VarSymb.reroot_eq]
  · change (VarSymb.step u .box).ext p = _
    rw [absIdx, if_neg (fun h => hrt (hrt'.symm.trans h))]

/-- Weakening the abstracted context into the new variable's context. -/
theorem absCtx_le (A : VarType) (l : List VarType) :
    (absCtx A l).Le ((ctxOf (A :: l)).boxIn.insert (.bnd 0) A.bc) :=
  ((ctxOf_le_append [A] l).boxIn).insert (.bnd 0) A.bc

/-- ⭐The abstraction of a formula of the new `□` view. -/
noncomputable def abs [ModalSys.NoTFour] (A : VarType) (l : List VarType)
    (ψ : WFF σ (ctxOf (A :: l)).boxIn 0) : WFF σ (absCtx A l) 1 :=
  WFF.subst (absIdx l.length) (absS σ (absCtx A l) l.length) (ok_absS A l) (coh_absS A l)
    Ctx.NoSlots.slots (absCtx_slots A l) ψ

/-! ## Instantiating the abstraction at the tuple -/

/-- Projecting the tuple entry along a path from the slot reaches the tuple of the component. -/
theorem at_single_tup [ModalSys.NoTFour] {A : VarType} {l : List VarType} :
    ∀ {u : VarSymb} {U : VarType} (hu : (ctxOf (A :: l)).ref u = some U),
      u.rt = .free l.length →
      (Subst.single (σ := σ) (Δ := (ctxOf (A :: l)).boxIn) (.bnd 0)
        (.tm (tup (.root (.free l.length)) A (ctxOf_ref_new A l)))).at (u.reroot (.bnd 0)) =
        .tm (tup u U hu)
  | .root r, U, hu, hrt => by
      change VarSymb.rt (.root r) = _ at hrt
      subst hrt
      rw [ctxOf_ref_new] at hu
      cases hu
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
  | .step u s, U, hu, hrt => by
      have hp := (reach_ppath hu).1
      have hs : s = .fst ∨ s = .snd := hp s (by simp [VarSymb.path])
      have hproj : s.isProj = true := by rcases hs with rfl | rfl <;> rfl
      have hu' := hu
      simp only [Ctx.ref, if_pos hproj] at hu'
      cases hU : (ctxOf (A :: l)).ref u with
      | none => rw [hU] at hu'; cases hu'
      | some U' =>
          rw [hU] at hu'
          have ih := at_single_tup hU hrt
          change (Subst.single (.bnd 0) _).at (.step (u.reroot (.bnd 0)) s) = _
          rw [show ∀ (θ : Subst σ (ctxOf (A :: l)).boxIn) (v : VarSymb),
              θ.at (.step v s) = (θ.at v).proj s from fun θ v => if_pos hproj, ih]
          rcases hs with rfl | rfl
          · cases U' with
            | VTypeProd X Y =>
                cases hu'
                rfl
            | _ => cases hu'
          · cases U' with
            | VTypeProd X Y =>
                cases hu'
                rfl
            | _ => cases hu'

/-- ⭐A formula of the new `□` view is its abstraction instantiated at the tuple of the new
    variable's items. -/
theorem instantiate_tup_abs [ModalSys.NoTFour] (A : VarType) (l : List VarType)
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
  change SubE.Sim T _ ((if u.rt = .free l.length then SubE.ren (u.reroot (.bnd 0))
    else .ren (.step u .box)).comp _ _ _)
  split_ifs with hrt
  · change SubE.Sim T _ ((Subst.single (.bnd 0) _).at (u.reroot (.bnd 0)))
    rw [at_single_tup hu hrt]
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
theorem at_toFree_reroot [ModalSys.NoTFour] {Δ : Ctx} (θ : Subst σ Δ) (z : ℕ) (T : VarType)
    (h : Δ (.root (.free z)) = none) :
    ∀ u : VarSymb, PPath u.path →
      (θ.toFree 0 z T h).at (u.reroot (.bnd 0)) = .ren (u.reroot (.free z))
  | .root _, _ => by
      change θ.toFree 0 z T h (.root (.bnd 0)) = .ren (.root (.free z))
      exact if_pos rfl
  | .step u s, hp => by
      have hs : s = .fst ∨ s = .snd := hp s (by simp [VarSymb.path])
      have hproj : s.isProj = true := by rcases hs with rfl | rfl <;> rfl
      change (θ.toFree 0 z T h).at (.step (u.reroot (.bnd 0)) s) = .ren (.step (u.reroot _) s)
      rw [show ∀ (θ' : Subst σ (Δ.insert (.free z) T)) (v : VarSymb),
          θ'.at (.step v s) = (θ'.at v).proj s from fun θ' v => if_pos hproj,
        at_toFree_reroot θ z T h u (fun s' hs' => hp s' (by simp [VarSymb.path, hs']))]
      rfl

/-- ⭐The arrow extended by the new variable's image is the old arrow applied to the abstraction,
    with the slot sent to the image. -/
theorem subst_arrow_abs [ModalSys.NoTFour] {A : VarType} {ls lt : List VarType} {img : ℕ → ℕ}
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
  change SubE.Sim T (.ren (u.reroot (imgRoot _ u.rt)))
    ((if u.rt = .free ls.length then SubE.ren (u.reroot (.bnd 0))
      else .ren (.step u .box)).comp _ _ _)
  split_ifs with hrt
  · change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.bc _).at (u.reroot (.bnd 0)))
    rw [at_toFree_reroot _ _ _ _ u hup, hrt]
    change SubE.Sim T (.ren (u.reroot (.free (if ls.length = ls.length then _ else _)))) _
    rw [if_pos rfl]
    exact .refl _
  · change SubE.Sim T _ ((Subst.toFree _ 0 lt.length A.bc _).at (.step u .box))
    rw [Subst.at_nonproj _ (rfl : (VarSymb.step u .box).lastProj = false)]
    change SubE.Sim T _ (if VarSymb.step u .box = .root (.bnd 0) then _ else _)
    rw [if_neg (fun h => by cases h)]
    change SubE.Sim T _ (.ren (u.reroot (imgRoot img u.rt)))
    rw [hr]
    have hrc : r ≠ ls.length := fun h => hrt (by rw [hr, h])
    change SubE.Sim T (.ren (u.reroot (.free (if r = ls.length then _ else _)))) _
    rw [if_neg hrc]
    exact .refl _

end BArrow

end V12M
