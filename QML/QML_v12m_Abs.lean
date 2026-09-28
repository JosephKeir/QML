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
