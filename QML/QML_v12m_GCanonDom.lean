import QML.QML_v12m_GLaws

/-!
# QML v12m — the growing tree's canonical model: raw objects and denotations

As B's `BCanonDom`, with paths for arrows.

* An **arrow** out of `s` is a descendant with its (unique) path (`GAcc`, `pathOf`); under T
  the empty path is the world's own arrow.
* **Raw objects** (`GRDom`): a necessary object has a value along each arrow, a possible object
  an extent (a set of arrows), a value along each of its arrows and, under T, its shape
  (`GRPos`, as B's `RPos`); `grawShape` arranges the stored shapes as the type does.
* ⭐`grden`: the denotation of a term.  A necessary term `□b` denotes, along an arrow, the
  denotation at its end of `b` translated along the path (`pTr`).  A possible term `◇_x b` has
  the arrows whose end realises the witness kept along them (`kw`) — under T — or, without T,
  the arrows of `x`'s extent (`InExt`).  Along a realising arrow its content is `b` translated
  with the witness kept (`pTrXK`) and realised by the end's datum (`grealT`); along the others
  `b` translated by the witness's translation (`pTrX`).  Its tag is its canonical shape.  A
  recursion on the type.
* It commutes with weakening (`grden_mono`) and does not depend on the stage (`grden_congr`).
* `GDefinable`: the raw objects denoted by terms.
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

/-- A raw possible object: an extent, a raw object along each of its arrows, and, under T, its
    shape, which the canonical model stores rather than computes (as B's `RPos`; the tree's
    `Canon.RPos` likewise asks for T, the only shaped flag without B). -/
structure GRPos (s : GW hF M₀) (A : VarType) (C : GAcc hF M₀ s → Type) where
  E : Set (GAcc hF M₀ s)
  c : (a : E) → C a.1
  tag : ModalSys.T = true → GShape hF M₀ s (.VTypeDia A)

theorem GRPos.congr_cont {s : GW hF M₀} {A : VarType} {C : GAcc hF M₀ s → Type}
    {E : Set (GAcc hF M₀ s)} {c c' : (a : E) → C a.1}
    {τ τ' : ModalSys.T = true → GShape hF M₀ s (.VTypeDia A)} (hc : c = c')
    (hτ : ∀ hT, τ hT = τ' hT) : (⟨E, c, τ⟩ : GRPos s A C) = ⟨E, c', τ'⟩ := by
  subst hc
  obtain rfl : τ = τ' := funext hτ
  rfl

/-! ## Raw objects and denotations -/

variable (hM₀ : Theory.IsMCS M₀)

/-- A world as a staged theory. -/
noncomputable abbrev gw (s : GW hF M₀) : BWorld σ := gnodeWorld hF hM₀ s.1 s.2

/-- ⭐**A path in a witness's canonical extent**: under T, its end realises the witness kept
    along it (`kw`); without T, its last edge is made for that witness (`InExt`).  Both recurse
    on the path as the translations do, so along `c :: c' :: P` this is the first edge's kept
    witness's membership along the rest, by definition. -/
abbrev GMem (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (x : VarSymb) : Prop :=
  (gw hM₀ t).Realised (kw s t P h x) ∨ (ModalSys.T = false ∧ InExt s t P h x)

/-- Raw objects of a type at a world. -/
def GRDom : VarType → GW hF M₀ → Type
  | .Var, s => (gw hM₀ s).D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A C, s => GRDom A s × GRDom C s
  | .VTypeBox A, s => (a : GAcc hF M₀ s) → GRDom A a.1
  | .VTypeDia A, s => GRPos s A fun a => GRDom A a.1

variable {hM₀} in
/-- ⭐Under T, the shape of a raw object: the stored shapes of its possible objects, arranged as
    its type arranges them — `Frame.domShape` for raw objects (B's `rawShape`). -/
def grawShape (hT : ModalSys.T = true) :
    {A : VarType} → {s : GW hF M₀} → GRDom hM₀ A s → GShape hF M₀ s A
  | .Var, _, _ => .var
  | .VTypeOne, _, _ => .one
  | .VTypeProd _ _, _, o => .prod (grawShape hT o.1) (grawShape hT o.2)
  | .VTypeBox _, _, o =>
      .box (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb) fun a =>
        grawShape hT (o a))
  | .VTypeDia _, _, o => o.3 hT

variable {hM₀} in
/-- Under a realised witness, the content of the possible object `⟨y; b⟩`: the body realised by
    the datum's content, at a stage above both (`Term.realiseAtA`) — B's `realTerm`. -/
noncomputable def grealT {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {Γ : Ctx}
    {i : ℕ} (e : Γ.Le (ctxOf (glat t i))) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y))
    {A : VarType} {a : Ann A} (b : Term σ (Γ.diaIn y) A a) :
    Σ c : Ann A, Term σ (ctxOf (glat t (max i hr.data.i₀))) A c :=
  ⟨_, Term.realiseAtA hr.data.hT y
    (hr.data.hdeclOf _ (hy.imp fun _ h => (gle hM₀ t (le_max_left _ _)).ref (e.ref h)))
    (Term.mono (gle hM₀ t (le_max_right _ _)) hr.data.t₀)
    (Term.mono ((e.trans (gle hM₀ t (le_max_left _ _))).diaIn y) b)⟩

variable {hM₀} in
/-- Realising at a later stage is weakening. -/
theorem grealT_mono {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {i j : ℕ}
    (hij : i ≤ j) (hy : ∃ Y, (ctxOf (glat t i)).ref y = some (.VTypeDia Y))
    (hy' : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y)) {A : VarType} {a a' : Ann A}
    (b : Term σ ((ctxOf (glat t i)).diaIn y) A a) (b' : Term σ ((ctxOf (glat t j)).diaIn y) A a')
    (hb : (⟨_, Term.mono ((gle hM₀ t hij).diaIn y) b⟩ : Σ c, Term σ _ A c) = ⟨_, b'⟩) :
    (⟨_, Term.mono (gle hM₀ t (max_le_max hij (le_refl _))) (grealT hr (Ctx.Le.refl _) hy b).2⟩ :
        Σ c : Ann A, Term σ (ctxOf (glat t (max j hr.data.i₀))) A c) =
      grealT hr (Ctx.Le.refl _) hy' b' := by
  cases hb
  simp only [grealT]
  rw [Term.mono_realiseAtA hr.data.hT _
      (hcA' := hr.data.hdeclOf _ (hy'.imp fun _ h => (gle hM₀ t (le_max_left _ _)).ref h)),
    Term.mono_mono, Term.mono_mono, Term.mono_mono]
  rfl

variable {hM₀} in
theorem grealT_sigma {t : GW hF M₀} {y : VarSymb} (hr : (gw hM₀ t).Realised y) {Γ : Ctx} {i : ℕ}
    (e : Γ.Le (ctxOf (glat t i))) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {A : VarType}
    {p q : Σ b : Ann A, Term σ (Γ.diaIn y) A b} (h : p = q) :
    grealT hr e hy p.2 = grealT hr e hy q.2 := by
  subst h
  rfl

open Classical in
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
  | _, _, Γ, s, i, e, .diatm x hx t =>
      ⟨{a | GMem hM₀ s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) x}, fun a =>
        if hr : (gw hM₀ a.1.1).Realised (kw s a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) x)
        then
          grden a.1.1 _ (Ctx.Le.refl _)
            (grealT hr (Ctx.Le.refl _)
              (kw_decl hM₀ s a.1.1 _ (pathOf_eq a.1.2.down) i (hx.imp fun _ h => e.ref h))
              (pTrXK hM₀ s a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) i x
                (hx.imp fun _ h => e.ref h) (Term.mono (e.diaIn x) t)).2).2
        else
          grden a.1.1 (pstg s a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) i) (Ctx.Le.refl _)
            (pTrX hM₀ s a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) i x
              (hx.imp fun _ h => e.ref h) (Or.resolve_left a.2 hr).2 (Term.mono (e.diaIn x) t)).2,
        fun _ => Model.termShp (famEnv cEnv Γ s) 0 (.diatm x hx t)⟩
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
  | _, _, Γ, Γ', h, .diatm x hx t, s, i, e => by
      change grden hM₀ s i e (.diatm x _ (Term.mono (h.diaIn x) t)) = _
      simp only [grden]
      refine GRPos.congr_cont (funext fun a => ?_) fun _ =>
        Model.termShp_mono (h := h) (ρ := famEnv cEnv Γ s) (ρ' := famEnv cEnv Γ' s)
          (fun _ _ _ => rfl) 0 (.diatm x hx t)
      by_cases hr :
          (gw hM₀ a.1.1).Realised (kw s a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) x)
      · simp only [dif_pos hr]
        rw [Term.mono_mono]
      · simp only [dif_neg hr]
        rw [Term.mono_mono]
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
        by_cases hr :
            (gw hM₀ a.1.1).Realised (kw s a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) x)
        · simp only [dif_pos hr]
          set P := pathOf a.1.2.down
          have hP := pathOf_eq a.1.2.down
          set K := max i j
          have side : ∀ (k : ℕ) (hk : k ≤ K) (ek : Γ.Le (ctxOf (glat s k))),
              grden hM₀ a.1.1 (max (pstg s a.1.1 P hP k) hr.data.i₀) (Ctx.Le.refl _)
                  (grealT hr (Ctx.Le.refl _) (kw_decl hM₀ s a.1.1 P hP k
                      (hx.imp fun _ h => ek.ref h))
                    (pTrXK hM₀ s a.1.1 P hP k x (hx.imp fun _ h => ek.ref h)
                      (Term.mono (ek.diaIn x) t)).2).2 =
                grden hM₀ a.1.1 (max (pstg s a.1.1 P hP K) hr.data.i₀) (Ctx.Le.refl _)
                  (grealT hr (Ctx.Le.refl _) (kw_decl hM₀ s a.1.1 P hP K
                      (hx.imp fun _ h => (ek.trans (gle hM₀ s hk)).ref h))
                    (pTrXK hM₀ s a.1.1 P hP K x
                      (hx.imp fun _ h => (ek.trans (gle hM₀ s hk)).ref h)
                      (Term.mono ((ek.trans (gle hM₀ s hk)).diaIn x) t)).2).2 := by
            intro k hk ek
            have hm := pstg_monotone hM₀ s a.1.1 P hP hk
            have hm' : max (pstg s a.1.1 P hP k) hr.data.i₀ ≤
                max (pstg s a.1.1 P hP K) hr.data.i₀ := max_le_max hm (le_refl _)
            refine (grden_congr _ a.1.1 _ _ (Ctx.Le.refl _) (gle hM₀ a.1.1 hm')).trans ?_
            refine ((grden_mono (gle hM₀ a.1.1 hm') _ a.1.1 _ (Ctx.Le.refl _)).symm).trans ?_
            refine grden_sigma _ (grealT_mono hr hm _ _ _ _ ?_)
            refine (pTrXK_mono hM₀ s a.1.1 P hP hk x _ _).trans ?_
            refine pTrXK_sigma hM₀ _ _ _ _ _ _ _ ?_
            rw [Term.mono_mono]
          exact (side i (le_max_left _ _) e).trans (side j (le_max_right _ _) e').symm
        simp only [dif_neg hr]
        set P := pathOf a.1.2.down
        have hP := pathOf_eq a.1.2.down
        set K := max i j
        have hm := (Or.resolve_left a.2 hr).2
        have side : ∀ (k : ℕ) (hk : k ≤ K) (ek : Γ.Le (ctxOf (glat s k))),
            grden hM₀ a.1.1 (pstg s a.1.1 P hP k) (Ctx.Le.refl _)
                (pTrX hM₀ s a.1.1 P hP k x (hx.imp fun _ h => ek.ref h)
                  hm (Term.mono (ek.diaIn x) t)).2 =
              grden hM₀ a.1.1 (pstg s a.1.1 P hP K) (Ctx.Le.refl _)
                (pTrX hM₀ s a.1.1 P hP K x (hx.imp fun _ h => (ek.trans (gle hM₀ s hk)).ref h)
                  hm (Term.mono ((ek.trans (gle hM₀ s hk)).diaIn x) t)).2 := by
          intro k hk ek
          refine (grden_congr _ a.1.1 _ (pstg s a.1.1 P hP K) (Ctx.Le.refl _)
            (gle hM₀ a.1.1 (pstg_monotone hM₀ s a.1.1 P hP hk))).trans ?_
          refine ((grden_mono (gle hM₀ a.1.1 (pstg_monotone hM₀ s a.1.1 P hP hk)) _ a.1.1 _
            (Ctx.Le.refl _)).symm).trans ?_
          refine grden_sigma _ ((pTrX_mono hM₀ s a.1.1 P hP hk x _ hm _).trans ?_)
          refine pTrX_sigma hM₀ _ _ _ _ _ _ _ _ ?_
          rw [Term.mono_mono]
        exact (side i (le_max_left _ _) e).trans (side j (le_max_right _ _) e').symm)
        fun _ => rfl
  termination_by structural A => A

/-- ⭐**Under T, a denotation's shape is its term's canonical shape** — the tags arranged as the
    type arranges them; along each arrow by `termShp_boxPush` (B's `rawShape_rden`). -/
theorem grawShape_grden (hT : ModalSys.T = true) : ∀ {A : VarType} {a : Ann A} {Γ : Ctx}
    (s : GW hF M₀) (i : ℕ) (e : Γ.Le (ctxOf (glat s i))) (t : Term σ Γ A a),
    grawShape hT (grden hM₀ s i e t) = Model.termShp (famEnv cEnv Γ s) 0 t
  | _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, .unit => rfl
  | _, _, _, s, i, e, .pair u v => by
      change Shp.prod (grawShape hT (grden hM₀ s i e u)) (grawShape hT (grden hM₀ s i e v)) = _
      rw [grawShape_grden hT s i e u, grawShape_grden hT s i e v]
      rfl
  | _, _, Γ, s, i, e, .boxtm t => by
      change Shp.box (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb)
          fun a => grawShape hT (grden hM₀ s i e (.boxtm t) a)) =
        Shp.box (Model.termShp ((famEnv cEnv Γ s).boxPush 0) 1 t)
      rw [← Model.termShp_mono (h := e.boxIn) (ρ := (famEnv cEnv Γ s).boxPush 0)
        (ρ' := (famEnv cEnv (ctxOf (glat s i)) s).boxPush 0)
        (Model.ShEnv.boxPush_agree (h := e) (ρ := famEnv cEnv Γ s)
          (ρ' := famEnv cEnv (ctxOf (glat s i)) s) (fun _ _ _ => rfl) 0) 1 t,
        termShp_boxPush hT hM₀ s i]
      exact congrArg Shp.box (congrArg _ (funext fun a => grawShape_grden hT a.1 _ _ _))
  | _, _, _, _, _, _, .diatm _ _ _ => rfl
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
  | diatm x hx b =>
      simp only [grden]
      split
      · exact gdefinable_rden _ _
      · exact gdefinable_rden _ _

end GArrow

end V12M
