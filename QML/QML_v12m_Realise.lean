import QML.QML_v12m_Subst

/-!
# QML v12m — realising a `◇` view at the current world (strong T)

Strong T's canonical model needs the *content* of a possible object at the world where it is
realised, not merely that world's membership in the extent.

At a **proper** successor that content is read off the successor's own language, because the
successor's base *is* the `◇_x` view (`DiaView`), so `x.dia` is a genuine address there.  At the
world itself there is no such vocabulary — `w` is not a `◇` view of `w` — so the content has to be
computed from a term `t₀ : A` naming the realisation of `x : ◇A`.  The `◇_x` view then collapses
onto the current level by

* `x.dia ↦ t₀` — the witness content is the realising term;
* `u.box ↦ u.here` — a necessary entry's value at the current world (weak T's projection);
* `u.keep ↦ u` — the kept component is the entry itself (under 4).

`Subst.realise` is that substitution and `Subst.ok_realise` says it is well-typed.  Note this adds
nothing to the proof system: it is an operation of the canonical model only, so there is no `ret`
term former, no equation and no congruence axiom, and nothing for substitution to commute with.

**A substitution is the wrong vehicle, and this file is kept only for the typing facts.**
`Term.subst` needs `Subst.Coh ι`, and `coh_of` would force `ι ((.step u .box).ext p) =
(.step u .here).ext p` — an index map that acts on *the level step this view introduced*.  That is
not a function of the address: `(.step u .box).ext [.box]` and `(.step (.step u .box) .box).ext []`
are the same address with different intended images.  Every existing combinator dodges this —
`coh_box` and `coh_dia` keep the *same* `ι`, while `setIdx`/`singleIdx` discriminate on the
**root**, which is unambiguous.

The fix is the one weak T already uses: `Term.collapse` is not a substitution but a dedicated
recursion carrying an explicit level `k` (`h.boxIn`/`h.diaIn` preserve it, annotations move by
`a.collapse k`), so the level is *threaded* rather than recovered.  Realisation should be a
`Term.realise` in the same shape — a `Ctx.Realises` relation, an `Ann.realise`, and a `var` case
branching to `t₀` at the realised address instead of to an address.  With `k` threaded that test is
well defined.  `Subst.ok_realise` below still records the typing of the three entries, which that
recursion needs.
-/

namespace V12M

namespace Subst

variable [ModalSys] {σ : Signature} {Γ : Ctx}

/-- The `◇_x` view realised at the current world by `t₀`. -/
def realise (x : VarSymb) {A : VarType} {a : Ann A} (t₀ : Term σ Γ A a) : Subst σ Γ := fun v =>
  match v with
  | .step u .dia => if u = x then .tm t₀ else .hide
  | .step u .box => .ren (.step u .here)
  | .step u .keep => .ren u
  | _ => .hide

/-- Realising is well-typed: the witness content takes the realising term, a necessary entry its
    value here, and a kept entry itself. -/
theorem ok_realise (hT : ModalSys.T = true) {x : VarSymb} {A : VarType} {a : Ann A}
    (hx : Γ.ref x = some (.VTypeDia A)) (t₀ : Term σ Γ A a) :
    Subst.Ok (Γ.diaIn x) (realise x t₀) := by
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      rw [hx] at hv
      cases hv
      change (if u = u then (SubE.tm t₀ : SubE σ Γ) else .hide).OkRef A
      rw [if_pos rfl]
      rfl
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      change ((SubE.ren (.step u .here) : SubE σ Γ)).OkRef T
      change Γ.ref (.step u .here) = some T
      rw [Ctx.ref_step_proj Γ u (rfl : Step.here.isProj = true), hu]
      change (if ModalSys.T then some T else none) = some T
      rw [if_pos hT]
  | .step u .keep =>
      obtain ⟨_, hu, _⟩ := Ctx.boxIn_keep hv
      exact hu
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

end Subst

/-! ## The realised content's address

`Term.realise` has to decide, of each address it meets, whether it passes through the realised
content `x.dia`.  Unlike "the level step this view introduced" — which is *not* a function of the
address, and is what blocked the substitution route — this test is against the concrete address
`x.dia`, fixed in advance, so it is unambiguous and the remainder path is determined. -/

namespace VarSymb

/-- Strip the inner prefix `x.dia`, returning the steps below it; `none` if the address does not
    pass through the realised content. -/
def belowDia (x : VarSymb) : VarSymb → Option (List Step)
  | .root _ => none
  | .step v s =>
      if (VarSymb.step v s) = .step x .dia then some []
      else (belowDia x v).map (fun p => p ++ [s])

theorem belowDia_dia (x : VarSymb) : belowDia x (.step x .dia) = some [] := if_pos rfl

/-- Passing through `x.dia` costs at least one step, so an address is never below its own
    dia-child. -/
theorem belowDia_length {x v : VarSymb} {q : List Step} (h : belowDia x v = some q) :
    x.path.length < v.path.length := by
  induction v generalizing q with
  | root r => cases h
  | step v s ih =>
      have h' : (if (VarSymb.step v s) = .step x .dia then some ([] : List Step)
        else (belowDia x v).map (fun p => p ++ [s])) = some q := h
      split_ifs at h' with hv
      · injection hv with hv' _
        subst hv'
        simp [VarSymb.path]
      · cases hq : belowDia x v with
        | none => rw [hq] at h'; cases h'
        | some q' =>
            have hlt := ih hq
            simp only [VarSymb.path, List.length_append]
            omega

theorem belowDia_self (x : VarSymb) : belowDia x x = none := by
  cases hb : belowDia x x with
  | none => rfl
  | some _ => exact absurd (belowDia_length hb) (lt_irrefl _)

theorem belowDia_step {x v : VarSymb} {q : List Step} (h : belowDia x v = some q) (s : Step) :
    belowDia x (.step v s) = some (q ++ [s]) := by
  have hv : (VarSymb.step v s) ≠ .step x .dia := by
    intro he
    injection he with hv' _
    subst hv'
    rw [belowDia_self] at h
    cases h
  have : belowDia x (.step v s) = (if (VarSymb.step v s) = .step x .dia then some ([] : List Step)
    else (belowDia x v).map (fun p => p ++ [s])) := rfl
  rw [this, if_neg hv, h]
  rfl

theorem belowDia_ext {x : VarSymb} : ∀ (p : List Step) {v : VarSymb} {q : List Step},
    belowDia x v = some q → belowDia x (v.ext p) = some (q ++ p) := by
  intro p
  induction p with
  | nil => intro v q h; simpa [VarSymb.ext] using h
  | cons s p ih =>
      intro v q h
      have hstep := ih (belowDia_step h s)
      have hext : VarSymb.ext v (s :: p) = VarSymb.ext (.step v s) p := rfl
      rw [hext]
      simpa using hstep

/-- ⭐The realised content's own addresses: `x.dia` extended by `p` is below `x.dia`, with
    remainder exactly `p`. -/
theorem belowDia_dia_ext (x : VarSymb) (p : List Step) :
    belowDia x ((VarSymb.step x .dia).ext p) = some p := by
  simpa using belowDia_ext p (belowDia_dia x)

theorem ext_snoc (v : VarSymb) (p : List Step) (s : Step) :
    v.ext (p ++ [s]) = .step (v.ext p) s := by
  induction p generalizing v with
  | nil => rfl
  | cons t p ih => exact ih (.step v t)

/-- ⭐The address map of realisation: below the realised content reroot at `d`, the constant naming
    it; everywhere else collapse.

    Naming the content by a constant is what keeps this a pure *address* map, so `Term.realise` can
    mirror `Term.collapse` instead of threading entries.  It is a device of the canonical model, not
    of the proof system — the Henkin construction already names `∃`-witnesses this way — so the
    `y.ret` objection, which was about substituting a compound term leaving no address, does not
    arise. -/
def realiseAddr (x d : VarSymb) (k : ℕ) (v : VarSymb) : VarSymb :=
  match belowDia x v with
  | some p => d.ext p
  | none => v.collapse k

/-- Realisation passes through projections. -/
theorem realiseAddr_proj {x d : VarSymb} {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = true) :
    realiseAddr x d k (.step v s) = .step (realiseAddr x d k v) s := by
  have hsd : s ≠ .dia := by
    intro he
    rw [he] at hs
    cases hs
  have hne : (VarSymb.step v s) ≠ .step x .dia := by
    intro he
    injection he with _ hs'
    exact hsd hs'
  have hb : belowDia x (.step v s) = (belowDia x v).map (fun p => p ++ [s]) := by
    have : belowDia x (.step v s) = (if (VarSymb.step v s) = .step x .dia then some ([] : List Step)
      else (belowDia x v).map (fun p => p ++ [s])) := rfl
    rw [this, if_neg hne]
  simp only [realiseAddr, hb]
  cases belowDia x v with
  | none => simp only [Option.map_none, VarSymb.collapse_proj hs]
  | some p => simp only [Option.map_some, ext_snoc]

end VarSymb

/-- Realising an annotation, mirroring `Ann.collapse`: the level `k` is threaded, rising by one on
    each descent into a view. -/
def Ann.realise (x d : VarSymb) : ℕ → {T : VarType} → Ann T → Ann T
  | _, _, .var => .var
  | _, _, .one => .one
  | k, _, .prod a b => .prod (Ann.realise x d k a) (Ann.realise x d k b)
  | k, _, .box a => .box (Ann.realise x d (k + 1) a)
  | k, _, .dia i a => .dia (VarSymb.realiseAddr x d k i) (Ann.realise x d (k + 1) a)

/-- `Γ₁` realises onto `Γ₂` at level `k`, with the content of `x.dia` named by `d`.  Exactly the
    shape of `Ctx.Collapses`, with `VarSymb.collapse k` replaced by `VarSymb.realiseAddr x d k`. -/
def Ctx.Realises [ModalSys] (k : ℕ) (x d : VarSymb) (Γ₁ Γ₂ : Ctx) : Prop :=
  ∀ v T, Γ₁.ref v = some T → Γ₂.ref (VarSymb.realiseAddr x d k v) = some T

/-- Realisation passes through a level step other than the realised `dia`, dropping the level by
    one — the analogue of `VarSymb.collapse_level_succ`. -/
theorem VarSymb.realiseAddr_level {x d : VarSymb} {k : ℕ} {v : VarSymb} {s : Step}
    (hs : s.isProj = false) (hsd : s ≠ .dia) :
    VarSymb.realiseAddr x d (k + 1) (.step v s) = .step (VarSymb.realiseAddr x d k v) s := by
  have hne : (VarSymb.step v s) ≠ .step x .dia := by
    intro he
    injection he with _ hs'
    exact hsd hs'
  have hb : VarSymb.belowDia x (.step v s) =
      (VarSymb.belowDia x v).map (fun p => p ++ [s]) := by
    have he : VarSymb.belowDia x (.step v s) =
      (if (VarSymb.step v s) = .step x .dia then some ([] : List Step)
        else (VarSymb.belowDia x v).map (fun p => p ++ [s])) := rfl
    rw [he, if_neg hne]
  simp only [VarSymb.realiseAddr, hb]
  cases VarSymb.belowDia x v with
  | none => simp only [Option.map_none, VarSymb.collapse_level_succ hs]
  | some p => simp only [Option.map_some, VarSymb.ext_snoc]

/-- It suffices to check the visible non-projection addresses. -/
theorem Ctx.Realises.of_raw [ModalSys] {k : ℕ} {x d : VarSymb} {Γ₁ Γ₂ : Ctx}
    (h : ∀ v T, v.lastProj = false → Γ₁ v = some T →
      Γ₂.ref (VarSymb.realiseAddr x d k v) = some T) :
    Ctx.Realises k x d Γ₁ Γ₂ := by
  intro v
  induction v with
  | root r => intro T hv; exact h _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        rw [VarSymb.realiseAddr_proj hs, Ctx.ref_step_proj _ _ hs]
        cases hU : Γ₁.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [hU] at hv; rw [ih U hU]; exact hv
      · exact h _ _ (show s.isProj = false from Bool.eq_false_iff.mpr hs)
          (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

/-! ## The `diaIn` side condition: a root is invisible in a view

`Ctx.Realises.diaIn` will read `Realises (k+1) x d (Γ₁.diaIn y) (Γ₂.diaIn (realiseAddr x d k y))`,
which is false when `y = x`: there the entry `.step x .dia` maps to `d`, a constant of `Γ₂` rather
than an address of the view.  Worse, it would be *unsound* rather than merely unprovable — an inner
witness that happened to be spelled `x` would have its content `.step x .dia` collide, under
`belowDia`, with the outer realised content.

The collision is not impossible for an arbitrary `x`: if `x` is a level-step address `u.box`, then
`(Γ.diaIn x).ref x` is `Γ.boxIn x`, which is `◇`-typed whenever `Γ.ref u = some (□◇_)`.  Ruling that
out in general needs a regress argument.  But it is ruled out cheaply by the condition that actually
holds in the canonical model, where witnesses are Henkin *constants*: **`x` is a root**.  Roots are
never entries of a view, so `Γ₁.ref x = none` at every depth and `y ≠ x` is immediate. -/

theorem Ctx.ref_root_boxIn [ModalSys] (Γ : Ctx) (r : Root) :
    Γ.boxIn.ref (.root r) = none := rfl

theorem Ctx.ref_root_diaIn [ModalSys] (Γ : Ctx) (y : VarSymb) (r : Root) :
    (Γ.diaIn y).ref (.root r) = none := rfl

/-- So a `◇`-typed address of a `□` view is never the realised root. -/
theorem Ctx.ne_root_of_ref_boxIn [ModalSys] {Γ : Ctx} {y : VarSymb} {r : Root} {X : VarType}
    (hy : Γ.boxIn.ref y = some (.VTypeDia X)) : y ≠ .root r := by
  intro he
  rw [he, Ctx.ref_root_boxIn] at hy
  cases hy

/-- And likewise of a `◇_y` view. -/
theorem Ctx.ne_root_of_ref_diaIn [ModalSys] {Γ : Ctx} {y z : VarSymb} {r : Root} {X : VarType}
    (hz : (Γ.diaIn y).ref z = some (.VTypeDia X)) : z ≠ .root r := by
  intro he
  rw [he, Ctx.ref_root_diaIn] at hz
  cases hz

/-- Realisation descends into the `□` view, exactly as `Ctx.Collapses.boxIn` does. -/
theorem Ctx.Realises.boxIn [ModalSys] {k : ℕ} {x d : VarSymb} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.Realises k x d Γ₁ Γ₂) : Ctx.Realises (k + 1) x d Γ₁.boxIn Γ₂.boxIn := by
  refine Ctx.Realises.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
      rw [VarSymb.realiseAddr_level rfl (by decide), Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_box_of hk (h u _ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      rw [VarSymb.realiseAddr_level rfl (by decide), Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_keep_of' hF (h u _ hu) hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-- Realisation passes through a `dia` step on a *different* witness.  The hypothesis `u ≠ x` is
    what the root condition supplies: see `Ctx.ne_root_of_ref_boxIn`. -/
theorem VarSymb.realiseAddr_dia_ne {x d : VarSymb} {k : ℕ} {u : VarSymb} (hu : u ≠ x) :
    VarSymb.realiseAddr x d (k + 1) (.step u .dia) =
      .step (VarSymb.realiseAddr x d k u) .dia := by
  have hne : (VarSymb.step u .dia) ≠ .step x .dia := by
    intro he
    injection he with hu' _
    exact hu hu'
  have hb : VarSymb.belowDia x (.step u .dia) =
      (VarSymb.belowDia x u).map (fun p => p ++ [Step.dia]) := by
    have he : VarSymb.belowDia x (.step u .dia) =
      (if (VarSymb.step u .dia) = .step x .dia then some ([] : List Step)
        else (VarSymb.belowDia x u).map (fun p => p ++ [Step.dia])) := rfl
    rw [he, if_neg hne]
  simp only [VarSymb.realiseAddr, hb]
  cases VarSymb.belowDia x u with
  | none => simp only [Option.map_none, VarSymb.collapse_level_succ (s := Step.dia) rfl]
  | some p => simp only [Option.map_some, VarSymb.ext_snoc]

/-- Realisation descends into a `◇_y` view, provided `y` is not the realised witness. -/
theorem Ctx.Realises.diaIn [ModalSys] {k : ℕ} {x d : VarSymb} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.Realises k x d Γ₁ Γ₂) {y : VarSymb} (hy : y ≠ x) :
    Ctx.Realises (k + 1) x d (Γ₁.diaIn y) (Γ₂.diaIn (VarSymb.realiseAddr x d k y)) := by
  refine Ctx.Realises.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = y then (match Γ₁.ref y with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with huy
      subst huy
      cases hx : Γ₁.ref u with
      | none => rw [hx] at hv; cases hv
      | some U =>
          rw [hx] at hv
          rw [VarSymb.realiseAddr_dia_ne hy, Ctx.ref_nonproj _ rfl]
          change (if VarSymb.realiseAddr x d k u = VarSymb.realiseAddr x d k u then
            (match Γ₂.ref (VarSymb.realiseAddr x d k u) with
              | some (.VTypeDia X) => some X | _ => none)
            else none) = some T
          rw [if_pos rfl, h u _ hx]
          exact hv
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ₁) hv
      rw [VarSymb.realiseAddr_level rfl (by decide), Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_box_of (Γ := Γ₂) hk (h u _ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ₁) hv
      rw [VarSymb.realiseAddr_level rfl (by decide), Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_keep_of' hF (h u _ hu) hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-! ## ⭐Realising a term

The `◇_{root r}` view read at the current world, with the realised content named by `d`.  A near
copy of `Term.collapse`: the level `k` is threaded, `var` goes by `VarSymb.realiseAddr`, and the
freshness hypothesis `Γ₁.ref (.root r) = none` — preserved at every descent by
`Ctx.ref_root_boxIn` / `Ctx.ref_root_diaIn` — is what rules out an inner witness colliding with the
realised one. -/

mutual
  def Func.realise {σ : Signature} [ModalSys] {r : Root} {d : VarSymb} {k : ℕ} :
      {Γ₁ Γ₂ : Ctx} → Ctx.Realises k (.root r) d Γ₁ Γ₂ → Γ₁.ref (.root r) = none →
      {n : ℕ} → Func σ Γ₁ n → Func σ Γ₂ n
    | _, _, _, _, _, .F f => .F f
    | _, _, h, hfr, _, .eval g t => .eval (Func.realise h hfr g) (Term.realise h hfr t)

  def Term.realise {σ : Signature} [ModalSys] {r : Root} {d : VarSymb} {k : ℕ} :
      {Γ₁ Γ₂ : Ctx} → Ctx.Realises k (.root r) d Γ₁ Γ₂ → Γ₁.ref (.root r) = none →
      {T : VarType} → {a : Ann T} → Term σ Γ₁ T a →
      Term σ Γ₂ T (Ann.realise (.root r) d k a)
    | _, _, h, _, _, _, .var v hv => .var _ (h v _ hv)
    | _, _, h, hfr, _, _, .func f => .func (Func.realise h hfr f)
    | _, _, _, _, _, _, .unit => .unit
    | _, _, h, hfr, _, _, .pair s t => .pair (Term.realise h hfr s) (Term.realise h hfr t)
    | _, _, h, _, _, _, .boxtm t =>
        .boxtm (Term.realise h.boxIn (Ctx.ref_root_boxIn _ r) t)
    | _, _, h, hfr, _, _, .diatm y hy t =>
        have hne : y ≠ .root r := fun he => by
          obtain ⟨X, hX⟩ := hy
          rw [he, hfr] at hX
          cases hX
        .diatm (VarSymb.realiseAddr (.root r) d k y) (hy.imp fun _ hX => h y _ hX)
          (Term.realise (h.diaIn hne) (Ctx.ref_root_diaIn _ y r) t)
end

end V12M
