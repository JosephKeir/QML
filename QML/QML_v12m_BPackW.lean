import QML.QML_v12m_BPack

/-!
# QML v12m — packing a world's roots and a slot into one hole

`QML_v12m_BPack` packs the *items* of a world's roots (its `□` view) into a hole.  Here the roots
themselves are packed, together with a formula's slot: a slot formula `χ(v)` over `ctxOf l`
becomes a hole formula `packRoots l χ` over `A × tyT l`, and reading it at `⟨s, tupW l⟩` gives back
`χ(s)` (⭐`holeAt_pair_tupW_packRoots`).

A hole formula mentions no variable of the context, so it can be placed at any term, slots
included (`WFF.holeAt`).  That is what lets a formula over a *later* stage of a world be said of
two objects at once, uniformly in all the roots born since (docs §11.20: the persistence of
aliases and of `Back` atoms, `∀z (H(⟨v, z⟩) ↔ H(⟨t, z⟩))`).

* `tyT l`, `tupW l`: the tuple of `l`'s roots, oldest innermost (as `bcT`, `tupT`);
* `packRootsS`, `packRootsIdx`, `packRoots`: the slot to the first component, root `r` to its
  place in the second;
* ⭐`holeAt_pair_tupW_packRoots`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The tuple of the roots -/

/-- The type of the tuple of a list's roots, oldest innermost. -/
def tyT : List VarType → VarType
  | [] => .VTypeOne
  | A :: l => .VTypeProd (tyT l) A

theorem ref_tupPathW {Δ : Ctx} : ∀ (l : List VarType) {r : ℕ}, r < l.length → ∀ {b : VarSymb},
    Δ.ref b = some (tyT l) → Δ.ref (b.ext (tupPath l r)) = some (rootTy l r)
  | [], r, h, _, _ => absurd h (Nat.not_lt_zero r)
  | A :: l, r, h, b, hb => by
      unfold tupPath
      split_ifs with hr
      · subst hr
        rw [rootTy_new]
        change Δ.ref (.step b .snd) = _
        simp only [Ctx.ref, Step.isProj, if_true, hb, Option.bind_some]
        rfl
      · have hr' : r < l.length := by
          have : r < l.length + 1 := h
          omega
        rw [rootTy_old hr']
        change Δ.ref ((VarSymb.step b .fst).ext (tupPath l r)) = _
        exact ref_tupPathW l hr' (by
          simp only [Ctx.ref, Step.isProj, if_true, hb, Option.bind_some]
          rfl)

/-- ⭐`l`'s roots, as one term. -/
def tupW : (l : List VarType) → Σ a : Ann (tyT l), Term σ (ctxOf l) (tyT l) a
  | [] => ⟨_, .unit⟩
  | A :: l => ⟨_, .pair (Term.mono (ctxOf_le_append [A] l) (tupW l).2)
      (Term.eta (.root (.free l.length)) A (ctxOf_ref_new A l))⟩

/-- The tuple's entry for root `r`, reached along its path: the η-expansion of `r`. -/
theorem at_tupPath_tupW {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ (l : List VarType) (hle : (ctxOf l).Le Δ) {b : VarSymb},
      θ.at b = .tm (Term.mono hle (tupW l).2) → ∀ {r : ℕ}, r < l.length →
        ∃ (R : VarType) (hR : Δ.ref (.root (.free r)) = some R),
          θ.at (b.ext (tupPath l r)) = .tm (Term.eta (.root (.free r)) R hR)
  | [], _, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | A :: l, hle, b, hb, r, hr => by
      unfold tupPath
      split_ifs with hrn
      · subst hrn
        refine ⟨A, hle.ref (ctxOf_ref_new A l), ?_⟩
        change θ.at (.step b .snd) = _
        rw [Subst.at_proj _ _ rfl, hb]
        change SubE.tm (Term.mono hle (Term.eta _ A _)) = _
        rw [Term.mono_eta]
      · have hr' : r < l.length := by
          have : r < l.length + 1 := hr
          omega
        have hb' : θ.at (.step b .fst) =
            .tm (Term.mono ((ctxOf_le_append [A] l).trans hle) (tupW l).2) := by
          rw [Subst.at_proj _ _ rfl, hb]
          exact congrArg SubE.tm (Term.mono_mono (ctxOf_le_append [A] l) hle (tupW l).2)
        exact at_tupPath_tupW θ l _ hb' hr'

/-! ## Packing -/

/-- The packed hole's context. -/
abbrev packRootsCtx (A : VarType) (l : List VarType) : Ctx :=
  Ctx.empty.insert (.bnd 0) (.VTypeProd A (tyT l))

/-- ⭐Packing a slot formula: the slot goes to the hole's first component, root `r` to its place
    in the second. -/
def packRootsS (σ : Signature) (A : VarType) (l : List VarType) : Subst σ (packRootsCtx A l) :=
  fun v =>
    match v with
    | .root (.bnd _) => .ren (.step (.root (.bnd 0)) .fst)
    | .root (.free r) => .ren ((VarSymb.step (.root (.bnd 0)) .snd).ext (tupPath l r))
    | _ => .hide

/-- Where packing sends annotation indices. -/
def packRootsIdx (l : List VarType) (i : VarSymb) : VarSymb :=
  match i.rt with
  | .bnd _ => (VarSymb.step (.root (.bnd 0)) .fst).ext i.path
  | .free r => ((VarSymb.step (.root (.bnd 0)) .snd).ext (tupPath l r)).ext i.path

theorem ref_packRoots_hole (A : VarType) (l : List VarType) :
    (packRootsCtx A l).ref (.root (.bnd 0)) = some (.VTypeProd A (tyT l)) :=
  Ctx.ref_insert_root _ _ _

theorem ref_packRoots_slot (A : VarType) (l : List VarType) :
    (packRootsCtx A l).ref (.step (.root (.bnd 0)) .fst) = some A := by
  simp only [Ctx.ref, Step.isProj, if_true]
  rfl

theorem ref_packRoots_root (A : VarType) {l : List VarType} {r : ℕ} (hr : r < l.length) :
    (packRootsCtx A l).ref ((VarSymb.step (.root (.bnd 0)) .snd).ext (tupPath l r)) =
      some (rootTy l r) :=
  ref_tupPathW l hr (by
    simp only [Ctx.ref, Step.isProj, if_true]
    rfl)

omit [ModalSys] in
/-- The visible addresses of a slot formula's context: the slot and the roots. -/
theorem vis_slotCtx {A : VarType} {l : List VarType} {v : VarSymb} {T : VarType}
    (hv : ((ctxOf l).insert (.bnd 0) A) v = some T) :
    (v = .root (.bnd 0) ∧ T = A) ∨ ∃ r, v = .root (.free r) ∧ r < l.length ∧ T = rootTy l r := by
  by_cases h0 : v = .root (.bnd 0)
  · subst h0
    left
    exact ⟨rfl, by simpa [Ctx.insert] using hv.symm⟩
  · right
    have hv' : ctxOf l v = some T := by simpa [Ctx.insert, h0] using hv
    obtain ⟨r, rfl⟩ := ctxOf_decl hv'
    have hlt : r < l.length := by
      rw [ctxOf_root] at hv'
      by_contra hn
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hn)] at hv'
      cases hv'
    refine ⟨r, rfl, hlt, ?_⟩
    rw [ctxOf_root_lt hlt] at hv'
    exact (Option.some.inj hv').symm

theorem ok_packRootsS (A : VarType) (l : List VarType) :
    Subst.Ok ((ctxOf l).insert (.bnd 0) A) (packRootsS σ A l) := by
  intro v T _ hv
  rcases vis_slotCtx hv with ⟨rfl, rfl⟩ | ⟨r, rfl, hr, rfl⟩
  · exact ref_packRoots_slot T l
  · exact ref_packRoots_root A hr

theorem coh_packRootsS (A : VarType) (l : List VarType) :
    Subst.Coh (packRootsIdx l) ((ctxOf l).insert (.bnd 0) A) (packRootsS σ A l) := by
  refine Subst.coh_of (ok_packRootsS A l) ?_
  intro v T _ hv p
  rcases vis_slotCtx hv with ⟨rfl, rfl⟩ | ⟨r, rfl, hr, rfl⟩
  · change (VarSymb.step (.root (.bnd 0)) .fst).ext p =
      packRootsIdx l ((VarSymb.root (.bnd 0)).ext p)
    simp only [packRootsIdx, VarSymb.ext_rt, VarSymb.ext_path, VarSymb.rt, VarSymb.path,
      List.nil_append]
  · change ((VarSymb.step (.root (.bnd 0)) .snd).ext (tupPath l r)).ext p =
      packRootsIdx l ((VarSymb.root (.free r)).ext p)
    simp only [packRootsIdx, VarSymb.ext_rt, VarSymb.ext_path, VarSymb.rt, VarSymb.path,
      List.nil_append]

/-- ⭐A slot formula over `ctxOf l`, packed into a hole over `A × tyT l`. -/
def packRoots {A : VarType} (l : List VarType) (χ : WFF σ ((ctxOf l).insert (.bnd 0) A) 1) :
    WFF σ (packRootsCtx A l) 1 :=
  WFF.subst (packRootsIdx l) (packRootsS σ A l) (ok_packRootsS A l) (coh_packRootsS A l)
    ((Ctx.NoSlots.slots (Γ := ctxOf l)).insert A) (Ctx.slotsFrom_empty.insert _) χ

/-- ⭐**Packing is undone at the tuple of the roots**: read at `⟨s, tupW l⟩`, the packed formula
    is the slot formula at `s`. -/
theorem holeAt_pair_tupW_packRoots {A : VarType} {a : Ann A} (l : List VarType)
    (s : Term σ (ctxOf l) A a) (χ : WFF σ ((ctxOf l).insert (.bnd 0) A) 1) :
    WFF.holeAt Ctx.NoSlots.slots (Term.pair s (tupW l).2) (packRoots l χ) =
      WFF.instantiate Ctx.NoSlots.slots s χ := by
  unfold WFF.holeAt WFF.instantiate WFF.substRoot packRoots
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ χ
  refine Subst.sim_of ?_
  intro v T _ hv
  rcases vis_slotCtx hv with ⟨rfl, rfl⟩ | ⟨r, rfl, hr, rfl⟩
  · change SubE.Sim T (Subst.single (.bnd 0) (.tm s) (.root (.bnd 0)))
      ((Subst.single (.bnd 0) (.tm (Term.pair s (tupW l).2))).at
        (.step (.root (.bnd 0)) .fst))
    rw [Subst.at_proj _ _ rfl]
    simp only [Subst.at, Subst.single, if_true]
    exact .refl _
  · change SubE.Sim _ (Subst.single (.bnd 0) (.tm s) (.root (.free r)))
      ((Subst.single (.bnd 0) (.tm (Term.pair s (tupW l).2))).at
        ((VarSymb.step (.root (.bnd 0)) .snd).ext (tupPath l r)))
    have hsnd : (Subst.single (σ := σ) (Δ := ctxOf l) (.bnd 0)
        (.tm (Term.pair s (tupW l).2))).at (.step (.root (.bnd 0)) .snd) =
        .tm (Term.mono (Ctx.Le.refl _) (tupW l).2) := by
      rw [Subst.at_proj _ _ rfl, Term.mono_refl]
      simp only [Subst.at, Subst.single, if_true]
      rfl
    obtain ⟨R, hR, h⟩ := at_tupPath_tupW _ l _ hsnd hr
    rw [h]
    obtain rfl : R = rootTy l r := Option.some.inj (hR.symm.trans (ctxOf_root_lt hr))
    simp only [Subst.single, VarSymb.root.injEq, reduceCtorEq, if_false]
    exact .ren_eta _ _

end BArrow

end V12M
