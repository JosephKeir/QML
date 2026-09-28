import QML.QML_v12m_DiaAbs
import QML.QML_v12m_Realise
import QML.QML_v12m_ViewFresh

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

/-! ## Abstracting a `◇` view at an arbitrary declared address -/

namespace VarSymb

omit [ModalSys] in
/-- Being below the content is being an extension of it. -/
theorem belowDia_eq {x : VarSymb} : ∀ {v : VarSymb} {p : List Step},
    belowDia x v = some p → v = (VarSymb.step x .dia).ext p
  | .root _, _, h => by cases h
  | .step u s, p, h => by
      by_cases he : (VarSymb.step u s) = .step x .dia
      · have hp : p = [] := by
          have h' : (if (VarSymb.step u s) = .step x .dia then some ([] : List Step)
            else (belowDia x u).map (fun q => q ++ [s])) = some p := h
          rw [if_pos he] at h'
          exact (Option.some.inj h').symm
        rw [hp, he]
        rfl
      · have h' : (if (VarSymb.step u s) = .step x .dia then some ([] : List Step)
          else (belowDia x u).map (fun q => q ++ [s])) = some p := h
        rw [if_neg he] at h'
        cases hu : belowDia x u with
        | none => rw [hu] at h'; cases h'
        | some q =>
            rw [hu] at h'
            obtain rfl : p = q ++ [s] := (Option.some.inj h').symm
            rw [VarSymb.ext_snoc, ← belowDia_eq hu]

omit [ModalSys] in
/-- ⭐An extension reaches the content only by **passing through** it: if `v` is not below `x.dia`
    but some extension of it is, then an extension of `v` *is* `x.dia`. -/
theorem belowDia_ext_of_none {x v : VarSymb} : ∀ (p : List Step) {q : List Step},
    belowDia x v = none → belowDia x (v.ext p) = some q →
      ∃ p' : List Step, v.ext p' = VarSymb.step x .dia
  | [], _, hv, hq => by rw [show VarSymb.ext v [] = v from rfl, hv] at hq; cases hq
  | s :: p, q, hv, hq => by
      cases hs : belowDia x (.step v s) with
      | some r =>
          refine ⟨[s], ?_⟩
          have h' : (if (VarSymb.step v s) = .step x .dia then some ([] : List Step)
            else (belowDia x v).map (fun t => t ++ [s])) = some r := hs
          rw [hv] at h'
          by_cases he : (VarSymb.step v s) = .step x .dia
          · exact he
          · rw [if_neg he] at h'
            cases h'
      | none =>
          obtain ⟨r, hr⟩ := belowDia_ext_of_none (x := x) (v := .step v s) p hs hq
          exact ⟨s :: r, hr⟩

end VarSymb


namespace Subst

/-- ⭐The abstraction of a `◇_x` view at an **arbitrary** address: the content goes to the hole, the
    `□`-view entries stay.  `Subst.diaAbs` is the case of a root. -/
def diaAbsA (σ : Signature) (Δ : Ctx) (x : VarSymb) : Subst σ Δ := fun v =>
  match v with
  | .step u .dia => if u = x then .ren (.root (.bnd 0)) else .hide
  | .step u .box => .ren (.step u .box)
  | .step u .keep => .ren (.step u .keep)
  | _ => .hide

variable {Γ : Ctx} {x : VarSymb} {A : VarType}

/-- ⭐The view's entries at an arbitrary witness: the content, or a `□`-view entry not below it.
    What was the root's freshness `hfr` is now `Ctx.Presented.not_below` — the naming discipline
    (§2d, §9). -/
theorem diaIn_casesA (hxA : Γ.ref x = some (.VTypeDia A))
    (hnb : ∀ p : List Step, Γ.ref ((VarSymb.step x .dia).ext p) = none) :
    ∀ {v : VarSymb} {T : VarType}, (Γ.diaIn x) v = some T →
      (v = .step x .dia ∧ T = A) ∨
        (VarSymb.belowDia x v = none ∧ Γ.boxIn v = some T ∧
          (∀ Δ : Ctx, diaAbsA σ Δ x v = .ren v) ∧ ∀ r : Root, v ≠ .root r) := by
  intro v T hv
  match v with
  | .step u .dia =>
      have hu : u = x := by
        change (if u = x then
          (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        split_ifs at hv with hcon
        exact hcon
      subst hu
      refine Or.inl ⟨rfl, ?_⟩
      change (if u = u then
        (match Γ.ref u with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      rw [if_pos rfl, hxA] at hv
      exact (Option.some.inj hv).symm
  | .step u .box =>
      refine Or.inr ⟨?_, hv, fun _ => rfl, fun _ h => by cases h⟩
      cases hb : VarSymb.belowDia x (.step u .box) with
      | none => rfl
      | some p =>
          exfalso
          obtain ⟨_, hu⟩ := Ctx.boxIn_box (Γ := Γ) hv
          have hne : (VarSymb.step u .box) ≠ .step x .dia := fun hcon => by cases hcon
          have hbu : (VarSymb.belowDia x u).map (fun q => q ++ [Step.box]) = some p := by
            have h' : (if (VarSymb.step u .box) = .step x .dia then some ([] : List Step)
              else (VarSymb.belowDia x u).map (fun q => q ++ [Step.box])) = some p := hb
            rwa [if_neg hne] at h'
          cases hq : VarSymb.belowDia x u with
          | none => rw [hq] at hbu; cases hbu
          | some q =>
              rw [VarSymb.belowDia_eq hq, hnb q] at hu
              cases hu
  | .step u .keep =>
      refine Or.inr ⟨?_, hv, fun _ => rfl, fun _ h => by cases h⟩
      cases hb : VarSymb.belowDia x (.step u .keep) with
      | none => rfl
      | some p =>
          exfalso
          obtain ⟨_, hu, _, rfl⟩ := Ctx.boxIn_keep (Γ := Γ) hv
          have hne : (VarSymb.step u .keep) ≠ .step x .dia := fun hcon => by cases hcon
          have hbu : (VarSymb.belowDia x u).map (fun q => q ++ [Step.keep]) = some p := by
            have h' : (if (VarSymb.step u .keep) = .step x .dia then some ([] : List Step)
              else (VarSymb.belowDia x u).map (fun q => q ++ [Step.keep])) = some p := hb
            rwa [if_neg hne] at h'
          cases hq : VarSymb.belowDia x u with
          | none => rw [hq] at hbu; cases hbu
          | some q =>
              rw [VarSymb.belowDia_eq hq, hnb q] at hu
              cases hu
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- ⭐Well-typedness of the generalised abstraction. -/
theorem ok_diaAbsA (hxA : Γ.ref x = some (.VTypeDia A))
    (hnb : ∀ p : List Step, Γ.ref ((VarSymb.step x .dia).ext p) = none)
    (h₀ : Γ.boxIn (.root (.bnd 0)) = none) :
    Ok (Γ.diaIn x) (diaAbsA σ (Γ.boxIn.insert (.bnd 0) A) x) := by
  intro v T hlp hv
  rcases diaIn_casesA (σ := σ) hxA hnb hv with ⟨rfl, rfl⟩ | ⟨_, hb, hen, _⟩
  · change (if x = x then SubE.ren (.root (.bnd 0)) else .hide).OkRef T
    rw [if_pos rfl]
    exact Ctx.ref_insert_root _ (.bnd 0) T
  · rw [hen (Γ.boxIn.insert (.bnd 0) A)]
    change (Γ.boxIn.insert (.bnd 0) A).ref v = some T
    exact (Ctx.ref_nonproj _ hlp).trans (Ctx.le_insert h₀ A v T hb)

/-- ⭐**Coherence at an arbitrary address.**  The one path that would need two images — from `x` by
    `.dia` — is unavailable: an extension of a view entry reaches the content only by passing
    through it (`VarSymb.belowDia_ext_of_none`), and `Ctx.ViewFresh` keeps `x` and its prefixes out
    of the view.  That is the whole of what the naming discipline buys here. -/
theorem coh_diaAbsA (hxA : Γ.ref x = some (.VTypeDia A))
    (hnb : ∀ p : List Step, Γ.ref ((VarSymb.step x .dia).ext p) = none)
    (hvf : Γ.ViewFresh) (h₀ : Γ.boxIn (.root (.bnd 0)) = none) :
    Coh (VarSymb.absAddr x 0) (Γ.diaIn x) (diaAbsA σ (Γ.boxIn.insert (.bnd 0) A) x) := by
  refine coh_of (ok_diaAbsA hxA hnb h₀) ?_
  intro v T hlp hv p
  rcases diaIn_casesA (σ := σ) hxA hnb hv with ⟨rfl, rfl⟩ | ⟨hbl, hb, hen, _⟩
  · change (if x = x then SubE.ren (.root (.bnd 0)) else .hide).idxAlong p = _
    rw [if_pos rfl, VarSymb.absAddr_dia x 0 p (Nat.zero_le _)]
    rfl
  · have hnone : VarSymb.belowDia x (v.ext p) = none := by
      cases hq : VarSymb.belowDia x (v.ext p) with
      | none => rfl
      | some q =>
          exfalso
          obtain ⟨p', hp'⟩ := VarSymb.belowDia_ext_of_none p hbl hq
          rcases List.eq_nil_or_concat p' with rfl | ⟨p'', s, rfl⟩
          · rw [show VarSymb.ext v [] = v from rfl] at hp'
            rw [hp'] at hb
            cases hb
          · rw [List.concat_eq_append, VarSymb.ext_snoc] at hp'
            injection hp' with hvx _
            have hbv : Γ.boxIn.ref v ≠ none := by
              rw [Ctx.ref_nonproj _ hlp, hb]
              exact fun hcon => by cases hcon
            have hx := hvf v p'' hbv
            rw [hvx, hxA] at hx
            cases hx
    rw [hen (Γ.boxIn.insert (.bnd 0) A), VarSymb.absAddr_of_none 0 hnone]
    rfl

end Subst


/-! ## The abstraction on terms and formulas, and the round trip -/

/-- ⭐A hole formula read inside `◇_x`, at **any** context declaring `x` at a `◇`-type.  The root
    case is `WFF.viewReadAt`. -/
def WFF.viewReadAtA {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (x : VarSymb) {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A))
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) : WFF σ (Γ.diaIn x) 0 :=
  WFF.renameRoot (.bnd 0) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0))
    (Ctx.le_boxIn_diaIn Γ x) (.step x .dia)
    (Ctx.ref_diaIn_of hxA) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) Ctx.NoSlots.slots ψ

/-- ⭐The hole formula a formula of the `◇_x` view is read from, at an arbitrary declared address.
    The only hypothesis is that `x` is declared at `◇A`: what the root version needed as freshness
    comes from the presentation (`Ctx.Presented.not_below`, `Ctx.Presented.viewFresh`). -/
def WFF.diaAbsA {σ : Signature} {Γ : Ctx} [hp : Γ.Presented] (x : VarSymb) {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A)) (χ : WFF σ (Γ.diaIn x) 0) :
    WFF σ (Γ.boxIn.insert (.bnd 0) A) 1 :=
  WFF.subst (VarSymb.absAddr x 0) (Subst.diaAbsA σ (Γ.boxIn.insert (.bnd 0) A) x)
    (Subst.ok_diaAbsA hxA (hp.not_below hxA rfl) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root))
    (Subst.coh_diaAbsA hxA (hp.not_below hxA rfl) hp.viewFresh
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root))
    Ctx.NoSlots.slots ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) χ

/-- ⭐The same abstraction on a term of the view. -/
def Term.diaAbsA {σ : Signature} {Γ : Ctx} [hp : Γ.Presented] (x : VarSymb) {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A)) {T : VarType} {b : Ann T}
    (t : Term σ (Γ.diaIn x) T b) :
    Term σ (Γ.boxIn.insert (.bnd 0) A) T (b.mapIdx (VarSymb.absAddr x 0)) :=
  Term.subst (VarSymb.absAddr x 0) (Subst.diaAbsA σ (Γ.boxIn.insert (.bnd 0) A) x)
    (Subst.ok_diaAbsA hxA (hp.not_below hxA rfl) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root))
    (Subst.coh_diaAbsA hxA (hp.not_below hxA rfl) hp.viewFresh
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).root)) t

/-- Abstracting and then reading back is the identity substitution, at an arbitrary address. -/
theorem Subst.sim_diaAbsA_viewRead {σ : Signature} {Γ : Ctx} {x : VarSymb} {A : VarType}
    (hxA : Γ.ref x = some (.VTypeDia A))
    (hnb : ∀ p : List Step, Γ.ref ((VarSymb.step x .dia).ext p) = none)
    {ι₂ : VarSymb → VarSymb}
    (hθ₂ : Subst.Ok (Γ.boxIn.insert (.bnd 0) A)
      (Subst.single (σ := σ) (Δ := Γ.diaIn x) (.bnd 0) (.ren (.step x .dia))))
    (hc₂ : Subst.Coh ι₂ (Γ.boxIn.insert (.bnd 0) A)
      (Subst.single (σ := σ) (Δ := Γ.diaIn x) (.bnd 0) (.ren (.step x .dia)))) :
    Subst.Sim (Γ.diaIn x) (Subst.idS σ (Γ.diaIn x))
      ((Subst.diaAbsA σ (Γ.boxIn.insert (.bnd 0) A) x).comp
        (Subst.single (.bnd 0) (.ren (.step x .dia))) hθ₂ hc₂) := by
  refine Subst.sim_of ?_
  intro v T hlp hv
  rcases Subst.diaIn_casesA (σ := σ) hxA hnb hv with ⟨rfl, _⟩ | ⟨_, _, hen, hroot⟩
  · change SubE.Sim T (.ren (.step x .dia))
      ((if x = x then SubE.ren (.root (.bnd 0)) else .hide).comp _ hθ₂ hc₂)
    rw [if_pos rfl]
    change SubE.Sim T (.ren (.step x .dia))
      (if (VarSymb.root (Root.bnd 0)) = .root (.bnd 0) then
        SubE.ren (.step x .dia) else .ren (.root (.bnd 0)))
    rw [if_pos rfl]
    exact .refl _
  · change SubE.Sim T (.ren v) ((Subst.diaAbsA σ (Γ.boxIn.insert (.bnd 0) A) x v).comp _ hθ₂ hc₂)
    rw [hen (Γ.boxIn.insert (.bnd 0) A)]
    change SubE.Sim T (.ren v)
      ((Subst.single (.bnd 0) (.ren (.step x .dia))).at v)
    rw [Subst.at_nonproj _ hlp,
      show (Subst.single (σ := σ) (Δ := Γ.diaIn x) (.bnd 0)
        (.ren (.step x .dia))) v = .ren v from if_neg (hroot (.bnd 0))]
    exact .refl _

/-- ⭐**The round trip at an arbitrary address**: every formula of the `◇_x` view is read from its
    abstraction.  This is what the pinned realisation rules need in order to present a view formula
    as a hole formula. -/
theorem WFF.viewReadAtA_diaAbsA {σ : Signature} {Γ : Ctx} [hp : Γ.Presented] (x : VarSymb)
    {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A)) (χ : WFF σ (Γ.diaIn x) 0) :
    WFF.viewReadAtA x hxA (WFF.diaAbsA x hxA χ) = χ := by
  have h₀ : Γ.boxIn (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root
  refine (WFF.subst_comp _ _ (Subst.idS σ _)
    (Subst.ok_diaAbsA hxA (hp.not_below hxA rfl) h₀)
    (Subst.coh_diaAbsA hxA (hp.not_below hxA rfl) hp.viewFresh h₀) _ _
    Subst.ok_idS Subst.coh_idS Ctx.NoSlots.slots ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
    Ctx.NoSlots.slots (Subst.sim_diaAbsA_viewRead hxA (hp.not_below hxA rfl) _ _) χ).trans ?_
  exact WFF.subst_id Subst.ok_idS Subst.coh_idS Ctx.NoSlots.slots χ

/-- ⭐The realisation of a view **term** at an arbitrary declared address. -/
def Term.realiseAtA {σ : Signature} {Γ : Ctx} [Γ.Presented] (hT : ModalSys.T = true) (x : VarSymb)
    {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A)) {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    {T : VarType} {b : Ann T} (t : Term σ (Γ.diaIn x) T b) :
    Term σ Γ T
      (((b.mapIdx (VarSymb.absAddr x 0)).collapse 0).mapIdx
        (Subst.singleIdx (.bnd 0) (.tm t₀))) :=
  Term.hereRead hT t₀ (Term.diaAbsA x hxA t)

/-- ⭐The realisation of a view **formula** at an arbitrary declared address. -/
def WFF.realiseAtA {σ : Signature} {Γ : Ctx} [Γ.Presented] (hT : ModalSys.T = true) (x : VarSymb)
    {A : VarType} (hxA : Γ.ref x = some (.VTypeDia A)) {a₀ : Ann A} (t₀ : Term σ Γ A a₀)
    (χ : WFF σ (Γ.diaIn x) 0) : WFF σ Γ 0 :=
  WFF.hereRead hT t₀ (WFF.diaAbsA x hxA χ)

end V12M
