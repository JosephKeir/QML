import QML.QML_v12m_BCanonWorld

/-!
# QML v12m — B's canonical model: arrows, raw objects and denotations

`BData` is what the canonical model for B needs from the construction, abstracted from the
networks: worlds (`BWorld`), a symmetric accessibility `R`, and for each accessible pair an
**arrow**: an index map on variables (`img`), with, for each stage of the source, a stage of the
target where every source variable has its image (`stg`, `imgOk`); necessity transfer along it
(`tr`) and existence of arrows for failing necessities (`ex`).  Some arrows lead into the extent
of a witness `x` (`kd`), with content variable `cx`, `□_x` transfer (`trX`) and existence for true
`◇_x` formulas (`exX`).

* **Raw objects** (`RDom`) are as in the staged model: a necessary object has a value along each
  arrow, a possible object has an extent (a set of arrows) and a value along each.
* ⭐`rden`: the denotation of a term.  A necessary term `□t` denotes, along an arrow, the
  denotation at the target of `t` **translated** along the arrow (`arrowS`); a possible term
  `◇_x t` has the extent of `x`, and along each of its arrows the denotation of `t` translated by
  the witness arrow (`arrowXS`).  This is a recursion on the type.
* It does not depend on the stage (`rden_congr`) and commutes with weakening (`rden_mono`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-- ⭐The data of the canonical model for B. -/
structure BData [ModalSys.NoTFour] (σ : Signature) where
  W : Type
  actual : W
  w : W → BWorld σ
  R : W → W → Prop
  symm : ∀ {s t}, R s t → R t s
  img : W → W → ℕ → ℕ
  stg : W → W → ℕ → ℕ
  imgOk : ∀ {s t}, R s t → ∀ i, ImgOk ((w s).l i) ((w t).ctx (stg s t i)) (img s t)
  tr : ∀ {s t} (h : R s t) (i : ℕ) (ψ : WFF σ ((w s).ctx i).boxIn 0), .box ψ ∈ (w s).M i →
    WFF.subst (arrowIdx (img s t)) (arrowS σ _ (img s t)) (ok_arrowS (imgOk h i))
      (coh_arrowS (imgOk h i)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ (w t).M (stg s t i)
  ex : ∀ (s : W) (i : ℕ) (ψ : WFF σ ((w s).ctx i).boxIn 0), .box ψ ∉ (w s).M i →
    ∃ (t : W) (h : R s t), (WFF.subst (arrowIdx (img s t)) (arrowS σ _ (img s t))
      (ok_arrowS (imgOk h i)) (coh_arrowS (imgOk h i)) Ctx.NoSlots.slots Ctx.NoSlots.slots
        ψ).neg ∈ (w t).M (stg s t i)
  kd : W → W → Option (VarSymb × VarType)
  cx : W → W → ℕ
  kdR : ∀ {s t x X}, kd s t = some (x, X) → R s t
  hcx : ∀ {s t x X}, kd s t = some (x, X) → ∀ i,
    ((w t).ctx (stg s t i)).ref (.root (.free (cx s t))) = some X
  hxX : ∀ {s t x X}, kd s t = some (x, X) → ∀ i X',
    ((w s).ctx i).ref x = some (.VTypeDia X') → X' = X
  trX : ∀ {s t x X} (hk : kd s t = some (x, X)) (i : ℕ)
    (hx : ((w s).ctx i).ref x = some (.VTypeDia X)) (ψ : WFF σ (((w s).ctx i).diaIn x) 0),
    WFF.boxx x ⟨X, hx⟩ ψ ∈ (w s).M i →
    WFF.subst (arrowXIdx (img s t) x (cx s t)) (arrowXS σ _ (img s t) x (cx s t))
      (ok_arrowXS (imgOk (kdR hk) i) hx (hcx hk i))
      (coh_arrowXS (imgOk (kdR hk) i) hx (hcx hk i)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
        (w t).M (stg s t i)
  exX : ∀ (s : W) (i : ℕ) (x : VarSymb) (X : VarType)
    (hx : ((w s).ctx i).ref x = some (.VTypeDia X)) (ψ : WFF σ (((w s).ctx i).diaIn x) 0),
    WFF.dia x ⟨X, hx⟩ ψ ∈ (w s).M i →
    ∃ (t : W) (hk : kd s t = some (x, X)),
      WFF.subst (arrowXIdx (img s t) x (cx s t)) (arrowXS σ _ (img s t) x (cx s t))
        (ok_arrowXS (imgOk (kdR hk) i) hx (hcx hk i))
        (coh_arrowXS (imgOk (kdR hk) i) hx (hcx hk i)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
          (w t).M (stg s t i)

namespace BData

variable [ModalSys.NoTFour] (B : BData σ)

/-- The arrows out of a world. -/
abbrev Acc (s : B.W) : Type := Σ t : B.W, PLift (B.R s t)

/-- ⭐The extent of the witness `x` at `s`: the arrows into its extent. -/
def extent (s : B.W) (x : VarSymb) : Set (B.Acc s) := {a | ∃ X, B.kd s a.1 = some (x, X)}

/-- The arrow's renaming is well typed at a stage. -/
theorem arOk {s t : B.W} (h : B.R s t) (i : ℕ) :
    Subst.Ok ((B.w s).ctx i).boxIn (arrowS σ ((B.w t).ctx (B.stg s t i)) (B.img s t)) :=
  ok_arrowS (B.imgOk h i)

theorem arCoh {s t : B.W} (h : B.R s t) (i : ℕ) :
    Subst.Coh (arrowIdx (B.img s t)) ((B.w s).ctx i).boxIn
      (arrowS σ ((B.w t).ctx (B.stg s t i)) (B.img s t)) :=
  coh_arrowS (B.imgOk h i)

/-- A witness arrow's renaming is well typed at a stage where the witness is visible. -/
theorem arXOk {s t : B.W} {x : VarSymb} (hm : ∃ X, B.kd s t = some (x, X)) (i : ℕ)
    (hx : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X)) :
    Subst.Ok (((B.w s).ctx i).diaIn x)
      (arrowXS σ ((B.w t).ctx (B.stg s t i)) (B.img s t) x (B.cx s t)) := by
  obtain ⟨X, hk⟩ := hm
  obtain ⟨X', hX'⟩ := hx
  have e := B.hxX hk i X' hX'
  subst e
  exact ok_arrowXS (B.imgOk (B.kdR hk) i) hX' (B.hcx hk i)

theorem arXCoh {s t : B.W} {x : VarSymb} (hm : ∃ X, B.kd s t = some (x, X)) (i : ℕ)
    (hx : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X)) :
    Subst.Coh (arrowXIdx (B.img s t) x (B.cx s t)) (((B.w s).ctx i).diaIn x)
      (arrowXS σ ((B.w t).ctx (B.stg s t i)) (B.img s t) x (B.cx s t)) := by
  obtain ⟨X, hk⟩ := hm
  obtain ⟨X', hX'⟩ := hx
  have e := B.hxX hk i X' hX'
  subst e
  exact coh_arrowXS (B.imgOk (B.kdR hk) i) hX' (B.hcx hk i)

/-! ## Raw objects and denotations -/

/-- Raw objects of a type at a world. -/
def RDom : VarType → B.W → Type
  | .Var, s => (B.w s).D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A C, s => RDom A s × RDom C s
  | .VTypeBox A, s => (a : B.Acc s) → RDom A a.1
  | .VTypeDia A, s => Σ E : Set (B.Acc s), (a : E) → RDom A a.1.1

/-- ⭐The denotation of a term at a world, computed at a stage containing its context. -/
noncomputable def rden : {A : VarType} → {a : Ann A} → {Γ : Ctx} → (s : B.W) → (i : ℕ) →
    Γ.Le ((B.w s).ctx i) → Term σ Γ A a → B.RDom A s
  | _, _, _, s, i, e, .var v hv => (B.w s).cls i (.var v (e.ref hv))
  | _, _, _, s, i, e, .func f => (B.w s).cls i (Term.mono e (.func f))
  | _, _, _, _, _, _, .unit => PUnit.unit
  | _, _, _, s, i, e, .pair t u => (rden s i e t, rden s i e u)
  | _, _, _, s, i, e, .boxtm t => fun a =>
      rden a.1 (B.stg s a.1 i) (Ctx.Le.refl _)
        (Term.subst (arrowIdx (B.img s a.1)) (arrowS σ _ (B.img s a.1))
          ((B.arOk a.2.down i).restrict e.boxIn) ((B.arCoh a.2.down i).restrict e.boxIn) t)
  | _, _, _, s, i, e, .diatm x hx t =>
      ⟨B.extent s x, fun a => rden a.1.1 (B.stg s a.1.1 i) (Ctx.Le.refl _)
        (Term.subst (arrowXIdx (B.img s a.1.1) x (B.cx s a.1.1))
          (arrowXS σ _ (B.img s a.1.1) x (B.cx s a.1.1))
          ((B.arXOk a.2 i (hx.imp fun _ h => e.ref h)).restrict (e.diaIn x))
          ((B.arXCoh a.2 i (hx.imp fun _ h => e.ref h)).restrict (e.diaIn x)) t)⟩
  termination_by structural A => A

variable {B}

theorem rden_sigma {A : VarType} {Γ : Ctx} {s : B.W} {i : ℕ} (e : Γ.Le ((B.w s).ctx i))
    {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) : B.rden s i e p.2 = B.rden s i e q.2 := by
  subst h
  rfl

/-- The denotation commutes with weakening. -/
theorem rden_mono : ∀ {A : VarType} {a : Ann A} {Γ Γ' : Ctx} (h : Γ.Le Γ') (t : Term σ Γ A a)
    (s : B.W) (i : ℕ) (e : Γ'.Le ((B.w s).ctx i)),
    B.rden s i e (Term.mono h t) = B.rden s i (h.trans e) t
  | _, _, _, _, _, .var _ _, _, _, _ => rfl
  | _, _, _, _, h, .func f, s, i, e => by
      change (B.w s).cls i (Term.mono e (Term.mono h (.func f))) =
        (B.w s).cls i (Term.mono (h.trans e) (.func f))
      rw [Term.mono_mono]
  | _, _, _, _, _, .unit, _, _, _ => rfl
  | _, _, _, _, h, .pair t u, s, i, e => Prod.ext (rden_mono h t s i e) (rden_mono h u s i e)
  | _, _, _, _, h, .boxtm t, s, i, e => funext fun a => by
      change B.rden a.1 _ _ (Term.subst _ _ _ _ (Term.mono h.boxIn t)) = _
      rw [Term.subst_mono]
      rfl
  | _, _, _, _, h, .diatm x hx t, s, i, e => by
      change (⟨B.extent s x, fun a => B.rden a.1.1 _ _
        (Term.subst _ _ _ _ (Term.mono (h.diaIn x) t))⟩ : B.RDom (.VTypeDia _) s) = _
      simp only [Term.subst_mono]
      rfl
  termination_by structural A => A

/-- Substituting along an arrow into a later stage of the target is weakening. -/
theorem subst_arrow_mono {s t : B.W} {Γ : Ctx} (i : ℕ) (j : ℕ) (hij : B.stg s t i ≤ j)
    (e : Γ.Le ((B.w s).ctx i).boxIn) (hθ : Subst.Ok Γ (arrowS σ ((B.w t).ctx j) (B.img s t)))
    (hc : Subst.Coh (arrowIdx (B.img s t)) Γ (arrowS σ ((B.w t).ctx j) (B.img s t)))
    (h : B.R s t) {A : VarType} {a : Ann A} (u : Term σ Γ A a) :
    Term.mono ((B.w t).le hij) (Term.subst (arrowIdx (B.img s t)) (arrowS σ _ (B.img s t))
        ((B.arOk h i).restrict e) ((B.arCoh h i).restrict e) u) =
      Term.subst (arrowIdx (B.img s t)) (arrowS σ ((B.w t).ctx j) (B.img s t)) hθ hc u := by
  rw [Term.mono_subst]
  exact eq_of_heq (Sigma.mk.inj (Term.subst_congr _ _ _ _ _ _ (fun v T hv => by
    rw [arrowS_mono]; exact .refl _) u)).2

/-- Substituting along a witness arrow into a later stage of the target is weakening. -/
theorem subst_arrowX_mono {s t : B.W} {Γ : Ctx} {x : VarSymb} (i : ℕ) (j : ℕ)
    (hij : B.stg s t i ≤ j) (e : Γ.Le (((B.w s).ctx i).diaIn x))
    (hθ : Subst.Ok Γ (arrowXS σ ((B.w t).ctx j) (B.img s t) x (B.cx s t)))
    (hc : Subst.Coh (arrowXIdx (B.img s t) x (B.cx s t)) Γ
      (arrowXS σ ((B.w t).ctx j) (B.img s t) x (B.cx s t)))
    (hm : ∃ X, B.kd s t = some (x, X)) (hx : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (u : Term σ Γ A a) :
    Term.mono ((B.w t).le hij) (Term.subst (arrowXIdx (B.img s t) x (B.cx s t))
        (arrowXS σ _ (B.img s t) x (B.cx s t))
        ((B.arXOk hm i hx).restrict e) ((B.arXCoh hm i hx).restrict e) u) =
      Term.subst (arrowXIdx (B.img s t) x (B.cx s t))
        (arrowXS σ ((B.w t).ctx j) (B.img s t) x (B.cx s t)) hθ hc u := by
  rw [Term.mono_subst]
  exact eq_of_heq (Sigma.mk.inj (Term.subst_congr _ _ _ _ _ _ (fun v T hv => by
    rw [arrowXS_mono]; exact .refl _) u)).2

/-- The denotation does not depend on the stage it is computed at. -/
theorem rden_congr : ∀ {A : VarType} {a : Ann A} {Γ : Ctx} (t : Term σ Γ A a) (s : B.W)
    (i j : ℕ) (e : Γ.Le ((B.w s).ctx i)) (e' : Γ.Le ((B.w s).ctx j)),
    B.rden s i e t = B.rden s j e' t
  | _, _, _, .var _ _, s, i, j, _, _ =>
      Quotient.sound (BWorld.TEq_of_lift_eq (w := B.w s) (le_max_left i j)
        (le_max_right i j) rfl)
  | _, _, _, .func _, s, i, j, _, _ =>
      Quotient.sound (BWorld.TEq_of_lift_eq (w := B.w s) (le_max_left i j)
        (le_max_right i j) ((Term.mono_mono _ _ _).trans (Term.mono_mono _ _ _).symm))
  | _, _, _, .unit, _, _, _, _, _ => rfl
  | _, _, _, .pair t u, s, i, j, e, e' =>
      Prod.ext (rden_congr t s i j e e') (rden_congr u s i j e e')
  | _, _, _, .boxtm t, s, i, j, e, e' => funext fun a => by
      change B.rden a.1 (B.stg s a.1 i) _ _ = B.rden a.1 (B.stg s a.1 j) _ _
      set K := max (B.stg s a.1 i) (B.stg s a.1 j)
      have hθ : Subst.Ok _ (arrowS σ ((B.w a.1).ctx K) (B.img s a.1)) :=
        (ok_arrowS ((B.imgOk a.2.down i).mono ((B.w a.1).le (le_max_left _ _)))).restrict
          e.boxIn
      have hc : Subst.Coh (arrowIdx (B.img s a.1)) _
          (arrowS σ ((B.w a.1).ctx K) (B.img s a.1)) :=
        (coh_arrowS ((B.imgOk a.2.down i).mono ((B.w a.1).le (le_max_left _ _)))).restrict
          e.boxIn
      have h₁ := (rden_congr _ a.1 (B.stg s a.1 i) K (Ctx.Le.refl _)
        ((B.w a.1).le (le_max_left _ _))).trans
        ((rden_mono ((B.w a.1).le (le_max_left _ _)) _ a.1 K (Ctx.Le.refl _)).symm.trans
          (congrArg (B.rden a.1 K (Ctx.Le.refl _))
            (subst_arrow_mono i K (le_max_left _ _) e.boxIn hθ hc a.2.down t)))
      have h₂ := (rden_congr _ a.1 (B.stg s a.1 j) K (Ctx.Le.refl _)
        ((B.w a.1).le (le_max_right _ _))).trans
        ((rden_mono ((B.w a.1).le (le_max_right _ _)) _ a.1 K (Ctx.Le.refl _)).symm.trans
          (congrArg (B.rden a.1 K (Ctx.Le.refl _))
            (subst_arrow_mono j K (le_max_right _ _) e'.boxIn hθ hc a.2.down t)))
      exact h₁.trans h₂.symm
  | _, _, Γ, .diatm x hx t, s, i, j, e, e' =>
      congrArg (Sigma.mk _) (funext fun a => by
        set K := max (B.stg s a.1.1 i) (B.stg s a.1.1 j)
        have hxi : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X) := hx.imp fun _ h => e.ref h
        have hθ : Subst.Ok (Γ.diaIn x)
            (arrowXS σ ((B.w a.1.1).ctx K) (B.img s a.1.1) x (B.cx s a.1.1)) := by
          obtain ⟨X, hk⟩ := a.2
          obtain ⟨X', hX'⟩ := hxi
          have ee := B.hxX hk i X' hX'
          subst ee
          exact (ok_arrowXS ((B.imgOk (B.kdR hk) i).mono ((B.w a.1.1).le (le_max_left _ _))) hX'
            (((B.w a.1.1).le (le_max_left _ _)).ref (B.hcx hk i))).restrict (e.diaIn x)
        have hc : Subst.Coh (arrowXIdx (B.img s a.1.1) x (B.cx s a.1.1)) (Γ.diaIn x)
            (arrowXS σ ((B.w a.1.1).ctx K) (B.img s a.1.1) x (B.cx s a.1.1)) := by
          obtain ⟨X, hk⟩ := a.2
          obtain ⟨X', hX'⟩ := hxi
          have ee := B.hxX hk i X' hX'
          subst ee
          exact (coh_arrowXS ((B.imgOk (B.kdR hk) i).mono ((B.w a.1.1).le (le_max_left _ _)))
            hX' (((B.w a.1.1).le (le_max_left _ _)).ref (B.hcx hk i))).restrict (e.diaIn x)
        have h₁ := (rden_congr _ a.1.1 (B.stg s a.1.1 i) K (Ctx.Le.refl _)
          ((B.w a.1.1).le (le_max_left _ _))).trans
          ((rden_mono ((B.w a.1.1).le (le_max_left _ _)) _ a.1.1 K (Ctx.Le.refl _)).symm.trans
            (congrArg (B.rden a.1.1 K (Ctx.Le.refl _))
              (subst_arrowX_mono i K (le_max_left _ _) (e.diaIn x) hθ hc a.2 hxi t)))
        have h₂ := (rden_congr _ a.1.1 (B.stg s a.1.1 j) K (Ctx.Le.refl _)
          ((B.w a.1.1).le (le_max_right _ _))).trans
          ((rden_mono ((B.w a.1.1).le (le_max_right _ _)) _ a.1.1 K (Ctx.Le.refl _)).symm.trans
            (congrArg (B.rden a.1.1 K (Ctx.Le.refl _))
              (subst_arrowX_mono j K (le_max_right _ _) (e'.diaIn x) hθ hc a.2
                (hx.imp fun _ h => e'.ref h) t)))
        exact h₁.trans h₂.symm)
  termination_by structural A => A

/-! ## Definable objects -/

/-- ⭐The raw objects denoted by terms. -/
def Definable (A : VarType) (s : B.W) (o : B.RDom A s) : Prop :=
  ∃ (i : ℕ) (a : Ann A) (t : Term σ ((B.w s).ctx i) A a), B.rden s i (Ctx.Le.refl _) t = o

theorem definable_rden {A : VarType} {a : Ann A} {Γ : Ctx} {s : B.W} {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) (t : Term σ Γ A a) : Definable A s (B.rden s i e t) :=
  ⟨i, a, Term.mono e t, by rw [rden_mono]⟩

theorem rden_var_cls {s : B.W} {i : ℕ} :
    ∀ (t : Term σ ((B.w s).ctx i) .Var .var), B.rden s i (Ctx.Le.refl _) t = (B.w s).cls i t
  | .var _ _ => rfl
  | .func f => by
      change (B.w s).cls i (Term.mono (Ctx.Le.refl _) (.func f)) = _
      rw [Term.mono_refl]

theorem definable_var {s : B.W} (d : (B.w s).D) : Definable .Var s d :=
  Quotient.inductionOn d fun p => ⟨p.1, .var, p.2, rden_var_cls p.2⟩

theorem definable_unit {s : B.W} (o : B.RDom .VTypeOne s) : Definable .VTypeOne s o :=
  ⟨0, .one, .unit, rfl⟩

theorem definable_fst {A C : VarType} {s : B.W} {o : B.RDom (.VTypeProd A C) s}
    (h : Definable (.VTypeProd A C) s o) : Definable A s o.1 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair u _ => exact ⟨i, _, u, rfl⟩

theorem definable_snd {A C : VarType} {s : B.W} {o : B.RDom (.VTypeProd A C) s}
    (h : Definable (.VTypeProd A C) s o) : Definable C s o.2 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair _ u => exact ⟨i, _, u, rfl⟩

theorem definable_pair {A C : VarType} {s : B.W} {o₁ : B.RDom A s} {o₂ : B.RDom C s}
    (h₁ : Definable A s o₁) (h₂ : Definable C s o₂) :
    Definable (.VTypeProd A C) s ((o₁, o₂) : B.RDom (.VTypeProd A C) s) := by
  obtain ⟨i₁, a₁, t₁, rfl⟩ := h₁
  obtain ⟨i₂, a₂, t₂, rfl⟩ := h₂
  refine ⟨max i₁ i₂, _, .pair ((B.w s).liftT (le_max_left _ _) t₁)
    ((B.w s).liftT (le_max_right _ _) t₂), Prod.ext ?_ ?_⟩
  · change B.rden s _ _ (Term.mono _ t₁) = _
    rw [rden_mono]
    exact rden_congr _ _ _ _ _ _
  · change B.rden s _ _ (Term.mono _ t₂) = _
    rw [rden_mono]
    exact rden_congr _ _ _ _ _ _

theorem definable_box_apply {A : VarType} {s : B.W} {o : B.RDom (.VTypeBox A) s}
    (h : Definable (.VTypeBox A) s o) (a : B.Acc s) : Definable A a.1 (o a) := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | boxtm b => exact definable_rden _ _

theorem definable_dia_apply {A : VarType} {s : B.W} {o : B.RDom (.VTypeDia A) s}
    (h : Definable (.VTypeDia A) s o) (a : o.1) : Definable A a.1.1 (o.2 a) := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | diatm x hx b => exact definable_rden _ _

end BData

end BArrow

end V12M
