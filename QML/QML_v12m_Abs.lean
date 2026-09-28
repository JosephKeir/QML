import QML.QML_v12m_DiaAbs
import QML.QML_v12m_Realise

/-!
# QML v12m — abstracting a `◇` view at an **arbitrary** address (strong T)

`Subst.diaAbs` abstracts the content of `◇_c` into a hole, for a *root* `c`.  The canonical model
needs it at an arbitrary declared `◇`-typed address `x`, because `WFF.here`'s subject is any
`◇`-term and every one is `Term.diatm x hx s` — already at depth 0, where a context variable
`p : (◇A) × B` makes `p.fst : ◇A` (§2d, §9).  A substitution cannot do it in general: `Subst.Coh`
would have to send the one address `x.dia` to two images as soon as `x` is itself a view entry,
which happens for `.step u .box` without 4 and for `u.keep.here` with it.

This file builds the **address map** that the recursion needs.  Inside `◇_x` where `x` is a view
entry, `Ctx.diaIn x` *shadows*: `x.dia` there is the inner content, while the outer content's
readings survive one level in, as `Γ.boxIn` entries `.step (x.dia) .box`.  So below `x.dia` the two
readings separate by whether the remaining path crosses a **level** step — projections stay inner, a
level step reads it outside — and the map has to count the `◇_x` views entered:

* ⭐`VarSymb.absAddr x k`: below `x.dia` with at least `k` levels to go, reroot at the slot;
  otherwise keep.
* ⭐`absAddr_root_zero`: at a root it is exactly `Subst.diaAbsIdx`, at every level — a root is never
  a view entry, so `k` stays `0` and the test always holds.
-/

namespace V12M

variable [ModalSys]

namespace VarSymb

/-- ⭐The address map of abstraction, at `k` nested `◇_x` views: an address below `x.dia` whose
    remaining path still crosses `k` levels is the outer content's, and reroots at the slot;
    everything else — including the inner content of a shadowing `◇_x` — stays. -/
def absAddr (x : VarSymb) (k : ℕ) (v : VarSymb) : VarSymb :=
  match belowDia x v with
  | some p => if k ≤ Step.levels p then (VarSymb.root (.bnd 0)).ext p else v
  | none => v

omit [ModalSys] in
theorem absAddr_of_none {x v : VarSymb} (k : ℕ) (h : belowDia x v = none) :
    absAddr x k v = v := by
  simp only [absAddr, h]

omit [ModalSys] in
/-- Below the content, with the levels to spare: the slot. -/
theorem absAddr_of_some {x v : VarSymb} {k : ℕ} {p : List Step} (h : belowDia x v = some p)
    (hk : k ≤ Step.levels p) : absAddr x k v = (VarSymb.root (.bnd 0)).ext p := by
  simp only [absAddr, h, if_pos hk]

omit [ModalSys] in
/-- Below the content, but the shadow has not been left: unchanged. -/
theorem absAddr_of_shadowed {x v : VarSymb} {k : ℕ} {p : List Step} (h : belowDia x v = some p)
    (hk : ¬ k ≤ Step.levels p) : absAddr x k v = v := by
  simp only [absAddr, h, if_neg hk]

omit [ModalSys] in
theorem absAddr_dia (x : VarSymb) (k : ℕ) (p : List Step) (hk : k ≤ Step.levels p) :
    absAddr x k ((VarSymb.step x .dia).ext p) = (VarSymb.root (.bnd 0)).ext p :=
  absAddr_of_some (belowDia_dia_ext x p) hk

end VarSymb

omit [ModalSys] in
theorem Step.levels_append : ∀ (p q : List Step),
    Step.levels (p ++ q) = Step.levels p + Step.levels q
  | [], q => by simp [Step.levels]
  | s :: p, q => by
      change (if s.isProj then 0 else 1) + Step.levels (p ++ q) =
        ((if s.isProj then 0 else 1) + Step.levels p) + Step.levels q
      rw [Step.levels_append p q]
      omega

namespace VarSymb

omit [ModalSys] in
/-- Abstraction passes through projections: they do not cross a level, so the test is unchanged. -/
theorem absAddr_proj {x : VarSymb} {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = true) :
    absAddr x k (.step v s) = .step (absAddr x k v) s := by
  have hsd : s ≠ .dia := by
    intro he
    rw [he] at hs
    cases hs
  have hne : (VarSymb.step v s) ≠ .step x .dia := by
    intro he
    injection he with _ hs'
    exact hsd hs'
  have hb : belowDia x (.step v s) = (belowDia x v).map (fun p => p ++ [s]) := by
    have he : belowDia x (.step v s) = (if (VarSymb.step v s) = .step x .dia
      then some ([] : List Step) else (belowDia x v).map (fun p => p ++ [s])) := rfl
    rw [he, if_neg hne]
  cases hq : belowDia x v with
  | none => rw [absAddr_of_none k hq, absAddr_of_none k (by rw [hb, hq]; rfl)]
  | some q =>
      have hlev : Step.levels (q ++ [s]) = Step.levels q := by
        rw [Step.levels_append]
        simp [Step.levels, hs]
      by_cases hk : k ≤ Step.levels q
      · rw [absAddr_of_some hq hk,
          absAddr_of_some (by rw [hb, hq]; rfl) (by rw [hlev]; exact hk), ext_snoc]
      · rw [absAddr_of_shadowed hq hk,
          absAddr_of_shadowed (by rw [hb, hq]; rfl) (by rw [hlev]; exact hk)]

omit [ModalSys] in
/-- ⭐Abstraction passes through a **level** step, at a level that may drop by one: crossing a level
    is what escapes a shadow, and that is what makes `Ctx.Abstracts` a *downward-closed family* of
    levels rather than one level. -/
theorem absAddr_level {x : VarSymb} {u : VarSymb} {s : Step} (hs : s.isProj = false)
    (hne : (VarSymb.step u s) ≠ .step x .dia) (k : ℕ) :
    ∃ j ≤ k, absAddr x k (.step u s) = .step (absAddr x j u) s := by
  have hb : belowDia x (.step u s) = (belowDia x u).map (fun p => p ++ [s]) := by
    have he : belowDia x (.step u s) = (if (VarSymb.step u s) = .step x .dia
      then some ([] : List Step) else (belowDia x u).map (fun p => p ++ [s])) := rfl
    rw [he, if_neg hne]
  cases hq : belowDia x u with
  | none =>
      refine ⟨k, le_rfl, ?_⟩
      rw [absAddr_of_none k hq, absAddr_of_none k (by rw [hb, hq]; rfl)]
  | some q =>
      have hlev : Step.levels (q ++ [s]) = Step.levels q + 1 := by
        rw [Step.levels_append]
        simp [Step.levels, hs]
      by_cases hk : k ≤ Step.levels q
      · refine ⟨k, le_rfl, ?_⟩
        rw [absAddr_of_some hq hk,
          absAddr_of_some (by rw [hb, hq]; rfl) (by rw [hlev]; omega), ext_snoc]
      · by_cases hk' : k ≤ Step.levels q + 1
        · refine ⟨Step.levels q, by omega, ?_⟩
          rw [absAddr_of_some hq le_rfl,
            absAddr_of_some (by rw [hb, hq]; rfl) (by rw [hlev]; exact hk'), ext_snoc]
        · refine ⟨k, le_rfl, ?_⟩
          rw [absAddr_of_shadowed hq hk,
            absAddr_of_shadowed (by rw [hb, hq]; rfl) (by rw [hlev]; omega)]

end VarSymb

/-- ⭐Abstracting an annotation: the witness indices move by `absAddr`, and entering a **shadowing**
    `◇_x` — an inner witness that is the abstracted address itself — is what raises the level. -/
def Ann.abs (x : VarSymb) : ℕ → {T : VarType} → Ann T → Ann T
  | _, _, .var => .var
  | _, _, .one => .one
  | k, _, .prod a b => .prod (Ann.abs x k a) (Ann.abs x k b)
  | k, _, .box a => .box (Ann.abs x k a)
  | k, _, .dia i a =>
      .dia (VarSymb.absAddr x k i) (Ann.abs x (if i = x then k + 1 else k) a)

/-- ⭐`Γ₁` abstracts onto `Γ₂` at level `k`: a **downward-closed family**, because crossing a level
    step escapes a shadow and so reads an address one level lower (`VarSymb.absAddr_level`). -/
def Ctx.Abstracts (x : VarSymb) (k : ℕ) (Γ₁ Γ₂ : Ctx) : Prop :=
  ∀ (j : ℕ), j ≤ k → ∀ v T, Γ₁.ref v = some T → Γ₂.ref (VarSymb.absAddr x j v) = some T

theorem Ctx.Abstracts.mono {x : VarSymb} {k k' : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Abstracts x k Γ₁ Γ₂)
    (hk : k' ≤ k) : Ctx.Abstracts x k' Γ₁ Γ₂ :=
  fun j hj => h j (hj.trans hk)

/-- It suffices to check the visible non-projection addresses. -/
theorem Ctx.Abstracts.of_raw {x : VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : ∀ (j : ℕ), j ≤ k → ∀ v T, v.lastProj = false → Γ₁ v = some T →
      Γ₂.ref (VarSymb.absAddr x j v) = some T) :
    Ctx.Abstracts x k Γ₁ Γ₂ := by
  intro j hj v
  induction v with
  | root r => intro T hv; exact h j hj _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · rw [VarSymb.absAddr_proj hs]
        have hv' : (Γ₁.ref v).bind (·.step s) = some T := by
          rw [Ctx.ref] at hv
          rwa [if_pos hs] at hv
        cases hU : Γ₁.ref v with
        | none => rw [hU] at hv'; cases hv'
        | some U =>
            rw [hU] at hv'
            rw [Ctx.ref, if_pos hs, ih U hU]
            exact hv'
      · have hlp : (VarSymb.step v s).lastProj = false := by
          cases s <;> first | rfl | exact absurd rfl hs
        rw [Ctx.ref, if_neg hs] at hv
        exact h j hj _ _ hlp hv

/-- ⭐Abstraction descends into the `□` view — at the **same** level, the extra level being part of
    the address, and using the family's lower members (`VarSymb.absAddr_level`). -/
theorem Ctx.Abstracts.boxIn {x : VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Abstracts x k Γ₁ Γ₂) :
    Ctx.Abstracts x k Γ₁.boxIn Γ₂.boxIn := by
  refine Ctx.Abstracts.of_raw ?_
  intro j hj v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hkb, hu⟩ := Ctx.boxIn_box hv
      obtain ⟨j', hj', he⟩ := VarSymb.absAddr_level (x := x) (u := u) (s := .box) rfl
        (by intro he; injection he with _ hs'; cases hs') j
      rw [he, Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_box_of hkb (h j' (hj'.trans hj) u _ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      obtain ⟨j', hj', he⟩ := VarSymb.absAddr_level (x := x) (u := u) (s := .keep) rfl
        (by intro he; injection he with _ hs'; cases hs') j
      rw [he, Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_keep_of hF (h j' (hj'.trans hj) u _ hu)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv


/-- ⭐**Nothing below the content is `◇`-typed.**  Automatic when the content type is `◇`-free, as
    `WFF.here` demands (§2d): every address below `x.dia` reads a part of the content, and a
    `◇`-free type has no `◇` anywhere inside it.  This is what makes abstraction leave every
    **witness** address alone, so the level bookkeeping never reaches the annotations. -/
def Ctx.DiaFreeBelow (x : VarSymb) (Γ : Ctx) : Prop :=
  ∀ (v : VarSymb) (X : VarType), VarSymb.belowDia x v ≠ none → Γ.ref v ≠ some (.VTypeDia X)

/-- ⭐So a witness's address is untouched, at every level. -/
theorem Ctx.DiaFreeBelow.absAddr_eq {x : VarSymb} {Γ : Ctx} (h : Ctx.DiaFreeBelow x Γ)
    {y : VarSymb} {X : VarType} (hy : Γ.ref y = some (.VTypeDia X)) (j : ℕ) :
    VarSymb.absAddr x j y = y := by
  cases hb : VarSymb.belowDia x y with
  | none => exact VarSymb.absAddr_of_none j hb
  | some p => exact absurd hy (h y X (by rw [hb]; exact fun hcon => by cases hcon))

/-- ⭐Abstraction descends into the view of a **different** witness, at the same level.  The witness
    address itself is untouched (`DiaFreeBelow.absAddr_eq`), which is what lets the target context
    be stated with one level. -/
theorem Ctx.Abstracts.diaIn {x : VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Abstracts x k Γ₁ Γ₂)
    (hdf : Ctx.DiaFreeBelow x Γ₁) {y : VarSymb} {X : VarType}
    (hy : Γ₁.ref y = some (.VTypeDia X)) (hne : y ≠ x) :
    Ctx.Abstracts x k (Γ₁.diaIn y) (Γ₂.diaIn y) := by
  refine Ctx.Abstracts.of_raw ?_
  intro j hj v T _ hv
  match v with
  | .step u .dia =>
      change (if u = y then
        (match Γ₁.ref y with | some (.VTypeDia Z) => some Z | _ => none) else none) = some T
        at hv
      split_ifs at hv with huy
      subst huy
      cases hz : Γ₁.ref u with
      | none => rw [hz] at hv; cases hv
      | some U =>
          rw [hz] at hv
          obtain ⟨j', hj', he⟩ := VarSymb.absAddr_level (x := x) (u := u) (s := .dia) rfl
            (by intro he; injection he with hu' _; exact hne hu') j
          rw [he, hdf.absAddr_eq hy j', Ctx.ref_nonproj _ rfl]
          change (if u = u then
            (match Γ₂.ref u with | some (.VTypeDia Z) => some Z | _ => none) else none) = some T
          have hgt : Γ₂.ref u = some U := by
            have hju := h j hj u _ hz
            rwa [hdf.absAddr_eq hy j] at hju
          rw [if_pos rfl, hgt]
          exact hv
  | .step u .box =>
      obtain ⟨hkb, hu⟩ := Ctx.boxIn_box hv
      obtain ⟨j', hj', he⟩ := VarSymb.absAddr_level (x := x) (u := u) (s := .box) rfl
        (by intro he; injection he with _ hs'; cases hs') j
      rw [he, Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_box_of (Γ := Γ₂) hkb (h j' (hj'.trans hj) u _ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      obtain ⟨j', hj', he⟩ := VarSymb.absAddr_level (x := x) (u := u) (s := .keep) rfl
        (by intro he; injection he with _ hs'; cases hs') j
      rw [he, Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_keep_of hF (h j' (hj'.trans hj) u _ hu)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv
namespace Subst

omit [ModalSys] in
/-- An address that does not pass through `c.dia` is left alone by the root-keyed map. -/
theorem diaAbsIdx_of_belowDia_none {c : ℕ} : ∀ {v : VarSymb},
    VarSymb.belowDia (.root (.free c)) v = none → diaAbsIdx c v = v
  | .root _, _ => rfl
  | .step u s, h => by
    have hne : (VarSymb.step u s) ≠ .step (.root (.free c)) .dia := by
      intro he
      rw [he] at h
      rw [VarSymb.belowDia_dia] at h
      cases h
    have hu : VarSymb.belowDia (.root (.free c)) u = none := by
      have h' : (if (VarSymb.step u s) = .step (.root (.free c)) .dia then some ([] : List Step)
        else (VarSymb.belowDia (.root (.free c)) u).map (fun p => p ++ [s])) = none := h
      rw [if_neg hne] at h'
      cases hb : VarSymb.belowDia (.root (.free c)) u with
      | none => rfl
      | some q => rw [hb] at h'; cases h'
    have hcon : ¬ (u = .root (.free c) ∧ s = Step.dia) := by
      intro ⟨hu', hs'⟩
      exact hne (by rw [hu', hs'])
    change (if u = .root (.free c) ∧ s = Step.dia then _ else
      VarSymb.step (diaAbsIdx c u) s) = _
    rw [if_neg hcon, diaAbsIdx_of_belowDia_none hu]

omit [ModalSys] in
/-- An address below `c.dia` is rerooted at the slot by the root-keyed map. -/
theorem diaAbsIdx_of_belowDia_some {c : ℕ} : ∀ {v : VarSymb} {p : List Step},
    VarSymb.belowDia (.root (.free c)) v = some p →
      diaAbsIdx c v = (VarSymb.root (.bnd 0)).ext p
  | .root _, _, h => by cases h
  | .step u s, p, h => by
    have h' : (if (VarSymb.step u s) = .step (.root (.free c)) .dia then some ([] : List Step)
      else (VarSymb.belowDia (.root (.free c)) u).map (fun q => q ++ [s])) = some p := h
    by_cases hne : (VarSymb.step u s) = .step (.root (.free c)) .dia
    · rw [if_pos hne] at h'
      obtain rfl : p = [] := (Option.some.inj h').symm
      injection hne with hu' hs'
      subst hu'
      subst hs'
      change (if (VarSymb.root (.free c)) = .root (.free c) ∧ Step.dia = Step.dia then _
        else VarSymb.step (diaAbsIdx c (.root (.free c))) Step.dia) = _
      rw [if_pos ⟨rfl, rfl⟩]
      rfl
    · rw [if_neg hne] at h'
      cases hb : VarSymb.belowDia (.root (.free c)) u with
      | none => rw [hb] at h'; cases h'
      | some q =>
          rw [hb] at h'
          obtain rfl : p = q ++ [s] := (Option.some.inj h').symm
          have hcon : ¬ (u = .root (.free c) ∧ s = Step.dia) := by
            intro ⟨hu', hs'⟩
            exact hne (by rw [hu', hs'])
          change (if u = .root (.free c) ∧ s = Step.dia then _ else
            VarSymb.step (diaAbsIdx c u) s) = _
          rw [if_neg hcon, diaAbsIdx_of_belowDia_some hb, VarSymb.ext_snoc]

omit [ModalSys] in
/-- ⭐**The generalisation is one**: at level `0` the level-aware map is exactly the root-keyed map.
    And at a root, level `0` is the only level the recursion ever reaches — a view context declares
    no roots (`Ctx.diaIn` falls through to `Ctx.boxIn`, which is `none` at a root), so no `◇_x` view
    can shadow a root and the increment never fires. -/
theorem absAddr_root_zero (c : ℕ) (v : VarSymb) :
    VarSymb.absAddr (.root (.free c)) 0 v = diaAbsIdx c v := by
  cases h : VarSymb.belowDia (.root (.free c)) v with
  | none => rw [VarSymb.absAddr_of_none 0 h, diaAbsIdx_of_belowDia_none h]
  | some p =>
      rw [diaAbsIdx_of_belowDia_some h, VarSymb.absAddr_of_some h (Nat.zero_le _)]

end Subst

end V12M
