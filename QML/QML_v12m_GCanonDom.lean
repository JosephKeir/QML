import QML.QML_v12m_GCanonPath

/-!
# QML v12m — the growing tree's canonical model: raw objects and denotations

As B's `BCanonDom`, with paths for arrows.

* An **arrow** out of `s` is a strict descendant with its (unique) path (`GAcc`, `pathOf`).
* **Raw objects** (`GRDom`): a necessary object has a value along each arrow, a possible object
  an extent (a set of arrows) and a value along each of its arrows (`GRPos`).
* ⭐`grden`: the denotation of a term.  A necessary term `□b` denotes, along an arrow, the
  denotation at its end of `b` translated along the path (`pTr`); a possible term `◇_x b` has
  the arrows of `x`'s extent (`InExt`), and along each the denotation of `b` translated by the
  witness's translation (`pTrX`).  A recursion on the type.
* It commutes with weakening (`grden_mono`) and does not depend on the stage (`grden_congr`).
* `GDefinable`: the raw objects denoted by terms.

This file is for 4 without T: no world has its own arrow, and no object carries a shape.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Arrows -/

variable (hF M₀) in
/-- The arrows out of a world: its strict descendants. -/
abbrev GAcc (s : GW hF M₀) : Type := Σ t : GW hF M₀, PLift (GR s t)

/-- A raw possible object: an extent, and a raw object along each of its arrows. -/
structure GRPos (s : GW hF M₀) (C : GAcc hF M₀ s → Type) where
  E : Set (GAcc hF M₀ s)
  c : (a : E) → C a.1

theorem GRPos.congr_cont {s : GW hF M₀} {C : GAcc hF M₀ s → Type} {E : Set (GAcc hF M₀ s)}
    {c c' : (a : E) → C a.1} (hc : c = c') : (⟨E, c⟩ : GRPos s C) = ⟨E, c'⟩ := by
  subst hc
  rfl

/-! ## Raw objects and denotations -/

variable (hM₀ : Theory.IsMCS M₀)

/-- A world as a staged theory. -/
noncomputable abbrev gw (s : GW hF M₀) : BWorld σ := gnodeWorld hF hM₀ s.1 s.2

/-- Raw objects of a type at a world. -/
def GRDom : VarType → GW hF M₀ → Type
  | .Var, s => (gw hM₀ s).D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A C, s => GRDom A s × GRDom C s
  | .VTypeBox A, s => (a : GAcc hF M₀ s) → GRDom A a.1
  | .VTypeDia A, s => GRPos s fun a => GRDom A a.1

/-- ⭐The denotation of a term at a world, computed at a stage containing its context. -/
noncomputable def grden : {A : VarType} → {a : Ann A} → {Γ : Ctx} → (s : GW hF M₀) → (i : ℕ) →
    Γ.Le (ctxOf (glat s i)) → Term σ Γ A a → GRDom hM₀ A s
  | _, _, _, s, i, e, .var v hv => (gw hM₀ s).cls i (.var v (e.ref hv))
  | _, _, _, s, i, e, .func f => (gw hM₀ s).cls i (Term.mono e (.func f))
  | _, _, _, _, _, _, .unit => PUnit.unit
  | _, _, _, s, i, e, .pair t u => (grden s i e t, grden s i e u)
  | _, _, _, s, i, e, .boxtm b => fun a =>
      grden a.1 (pstg s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) i) (Ctx.Le.refl _)
        (pTr hM₀ s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (pathOf_ok a.2.down) i
          (Term.mono e.boxIn b)).2
  | _, _, _, s, i, e, .diatm x hx t =>
      ⟨{a | InExt s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) x}, fun a =>
        grden a.1.1 (pstg s a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) i) (Ctx.Le.refl _)
          (pTrX hM₀ s a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) i x
            (hx.imp fun _ h => e.ref h) a.2 (Term.mono (e.diaIn x) t)).2⟩
  termination_by structural A => A

variable {hM₀}

theorem grden_sigma {A : VarType} {Γ : Ctx} {s : GW hF M₀} {i : ℕ} (e : Γ.Le (ctxOf (glat s i)))
    {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) : grden hM₀ s i e p.2 = grden hM₀ s i e q.2 := by
  subst h
  rfl

/-- The denotation commutes with weakening. -/
theorem grden_mono : ∀ {A : VarType} {a : Ann A} {Γ Γ' : Ctx} (h : Γ.Le Γ')
    (t : Term σ Γ A a) (s : GW hF M₀) (i : ℕ) (e : Γ'.Le (ctxOf (glat s i))),
    grden hM₀ s i e (Term.mono h t) = grden hM₀ s i (h.trans e) t
  | _, _, _, _, _, .var _ _, _, _, _ => rfl
  | _, _, _, _, h, .func f, s, i, e => by
      change (gw hM₀ s).cls i (Term.mono e (Term.mono h (.func f))) =
        (gw hM₀ s).cls i (Term.mono (h.trans e) (.func f))
      rw [Term.mono_mono]
  | _, _, _, _, _, .unit, _, _, _ => rfl
  | _, _, _, _, h, .pair t u, s, i, e => Prod.ext (grden_mono h t s i e) (grden_mono h u s i e)
  | _, _, _, _, h, .boxtm t, s, i, e => funext fun a => by
      change grden hM₀ s i e (.boxtm (Term.mono h.boxIn t)) a =
        grden hM₀ s i (h.trans e) (.boxtm t) a
      simp only [grden]
      rw [Term.mono_mono]
  | _, _, _, _, h, .diatm x hx t, s, i, e => by
      change grden hM₀ s i e (.diatm x _ (Term.mono (h.diaIn x) t)) = _
      simp only [grden]
      exact GRPos.congr_cont (funext fun a => by rw [Term.mono_mono])
  termination_by structural A => A

/-- ⭐The denotation does not depend on the stage it is computed at. -/
theorem grden_congr : ∀ {A : VarType} {a : Ann A} {Γ : Ctx} (t : Term σ Γ A a) (s : GW hF M₀)
    (i j : ℕ) (e : Γ.Le (ctxOf (glat s i))) (e' : Γ.Le (ctxOf (glat s j))),
    grden hM₀ s i e t = grden hM₀ s j e' t
  | _, _, _, .var _ _, s, i, j, _, _ =>
      Quotient.sound (BWorld.TEq_of_lift_eq (w := gw hM₀ s) (le_max_left i j)
        (le_max_right i j) rfl)
  | _, _, _, .func _, s, i, j, _, _ =>
      Quotient.sound (BWorld.TEq_of_lift_eq (w := gw hM₀ s) (le_max_left i j)
        (le_max_right i j) ((Term.mono_mono _ _ _).trans (Term.mono_mono _ _ _).symm))
  | _, _, _, .unit, _, _, _, _, _ => rfl
  | _, _, _, .pair t u, s, i, j, e, e' =>
      Prod.ext (grden_congr t s i j e e') (grden_congr u s i j e e')
  | _, _, Γ, .boxtm t, s, i, j, e, e' => funext fun a => by
      simp only [grden]
      set P := pathOf a.2.down
      have hP := pathOf_eq a.2.down
      have hne := pathOf_ok a.2.down
      set K := max i j
      have side : ∀ (k : ℕ) (hk : k ≤ K) (ek : Γ.Le (ctxOf (glat s k))),
          grden hM₀ a.1 (pstg s a.1 P hP k) (Ctx.Le.refl _)
              (pTr hM₀ s a.1 P hP hne k (Term.mono ek.boxIn t)).2 =
            grden hM₀ a.1 (pstg s a.1 P hP K) (Ctx.Le.refl _)
              (pTr hM₀ s a.1 P hP hne K (Term.mono (ek.trans (gle hM₀ s hk)).boxIn t)).2 := by
        intro k hk ek
        refine (grden_congr _ a.1 _ (pstg s a.1 P hP K) (Ctx.Le.refl _)
          (gle hM₀ a.1 (pstg_monotone hM₀ s a.1 P hP hk))).trans ?_
        refine ((grden_mono (gle hM₀ a.1 (pstg_monotone hM₀ s a.1 P hP hk)) _ a.1 _
          (Ctx.Le.refl _)).symm).trans ?_
        refine grden_sigma _ ((pTr_mono hM₀ s a.1 P hP hne hk _).trans ?_)
        rw [Term.mono_mono]
      exact (side i (le_max_left _ _) e).trans (side j (le_max_right _ _) e').symm
  | _, _, Γ, .diatm x hx t, s, i, j, e, e' =>
      GRPos.congr_cont (funext fun a => by
        set P := pathOf a.1.2.down
        have hP := pathOf_eq a.1.2.down
        set K := max i j
        have side : ∀ (k : ℕ) (hk : k ≤ K) (ek : Γ.Le (ctxOf (glat s k))),
            grden hM₀ a.1.1 (pstg s a.1.1 P hP k) (Ctx.Le.refl _)
                (pTrX hM₀ s a.1.1 P hP k x (hx.imp fun _ h => ek.ref h)
                  a.2 (Term.mono (ek.diaIn x) t)).2 =
              grden hM₀ a.1.1 (pstg s a.1.1 P hP K) (Ctx.Le.refl _)
                (pTrX hM₀ s a.1.1 P hP K x (hx.imp fun _ h => (ek.trans (gle hM₀ s hk)).ref h)
                  a.2 (Term.mono ((ek.trans (gle hM₀ s hk)).diaIn x) t)).2 := by
          intro k hk ek
          refine (grden_congr _ a.1.1 _ (pstg s a.1.1 P hP K) (Ctx.Le.refl _)
            (gle hM₀ a.1.1 (pstg_monotone hM₀ s a.1.1 P hP hk))).trans ?_
          refine ((grden_mono (gle hM₀ a.1.1 (pstg_monotone hM₀ s a.1.1 P hP hk)) _ a.1.1 _
            (Ctx.Le.refl _)).symm).trans ?_
          refine grden_sigma _ ((pTrX_mono hM₀ s a.1.1 P hP hk x _ a.2 _).trans ?_)
          refine pTrX_sigma hM₀ _ _ _ _ _ _ _ _ ?_
          rw [Term.mono_mono]
        exact (side i (le_max_left _ _) e).trans (side j (le_max_right _ _) e').symm)
  termination_by structural A => A

/-! ## Definable objects -/

variable (hM₀) in
/-- ⭐The raw objects denoted by terms. -/
def GDefinable (A : VarType) (s : GW hF M₀) (o : GRDom hM₀ A s) : Prop :=
  ∃ (i : ℕ) (a : Ann A) (t : Term σ (ctxOf (glat s i)) A a), grden hM₀ s i (Ctx.Le.refl _) t = o

theorem gdefinable_rden {A : VarType} {a : Ann A} {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) (t : Term σ Γ A a) :
    GDefinable hM₀ A s (grden hM₀ s i e t) :=
  ⟨i, a, Term.mono e t, by rw [grden_mono]⟩

theorem grden_var_cls {s : GW hF M₀} {i : ℕ} :
    ∀ (t : Term σ (ctxOf (glat s i)) .Var .var),
      grden hM₀ s i (Ctx.Le.refl _) t = (gw hM₀ s).cls i t
  | .var _ _ => rfl
  | .func f => by
      change (gw hM₀ s).cls i (Term.mono (Ctx.Le.refl _) (.func f)) = _
      rw [Term.mono_refl]

theorem gdefinable_var {s : GW hF M₀} (d : (gw hM₀ s).D) : GDefinable hM₀ .Var s d :=
  Quotient.inductionOn d fun p => ⟨p.1, .var, p.2, grden_var_cls p.2⟩

theorem gdefinable_unit {s : GW hF M₀} (o : GRDom hM₀ .VTypeOne s) :
    GDefinable hM₀ .VTypeOne s o :=
  ⟨0, .one, .unit, rfl⟩

theorem gdefinable_fst {A C : VarType} {s : GW hF M₀} {o : GRDom hM₀ (.VTypeProd A C) s}
    (h : GDefinable hM₀ (.VTypeProd A C) s o) : GDefinable hM₀ A s o.1 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair u _ => exact ⟨i, _, u, rfl⟩

theorem gdefinable_snd {A C : VarType} {s : GW hF M₀} {o : GRDom hM₀ (.VTypeProd A C) s}
    (h : GDefinable hM₀ (.VTypeProd A C) s o) : GDefinable hM₀ C s o.2 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair _ u => exact ⟨i, _, u, rfl⟩

theorem gdefinable_pair {A C : VarType} {s : GW hF M₀} {o₁ : GRDom hM₀ A s}
    {o₂ : GRDom hM₀ C s} (h₁ : GDefinable hM₀ A s o₁) (h₂ : GDefinable hM₀ C s o₂) :
    GDefinable hM₀ (.VTypeProd A C) s ((o₁, o₂) : GRDom hM₀ (.VTypeProd A C) s) := by
  obtain ⟨i₁, a₁, t₁, rfl⟩ := h₁
  obtain ⟨i₂, a₂, t₂, rfl⟩ := h₂
  refine ⟨max i₁ i₂, _, .pair ((gw hM₀ s).liftT (le_max_left _ _) t₁)
    ((gw hM₀ s).liftT (le_max_right _ _) t₂), Prod.ext ?_ ?_⟩
  · change grden hM₀ s _ _ (Term.mono _ t₁) = _
    rw [grden_mono]
    exact grden_congr _ _ _ _ _ _
  · change grden hM₀ s _ _ (Term.mono _ t₂) = _
    rw [grden_mono]
    exact grden_congr _ _ _ _ _ _

theorem gdefinable_box_apply {A : VarType} {s : GW hF M₀} {o : GRDom hM₀ (.VTypeBox A) s}
    (h : GDefinable hM₀ (.VTypeBox A) s o) (a : GAcc hF M₀ s) : GDefinable hM₀ A a.1 (o a) := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | boxtm b => exact gdefinable_rden _ _

theorem gdefinable_dia_apply {A : VarType} {s : GW hF M₀} {o : GRDom hM₀ (.VTypeDia A) s}
    (h : GDefinable hM₀ (.VTypeDia A) s o) (a : o.E) : GDefinable hM₀ A a.1.1 (o.c a) := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | diatm x hx b => exact gdefinable_rden _ _

end GArrow

end V12M
