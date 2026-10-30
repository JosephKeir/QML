import QML.QML_v12m_GCluLabel

/-!
# QML v12m — 5 on the growing tree: the cluster model's raw objects and denotations

The K45 cluster model (`docs/v12-modal-extensions.md` §3 5, "The K45 cluster model: design pass
against the code").  Without T every non-root world is a strict descendant of the root `ρ`
(`groot`), so every world's arrows are the root's (`CAcc := GAcc ρ`), and modal raw objects do
not depend on the world.

* `CluFlags`: 5 and both lifts on, T and B off.
* `rpath`, `rstg`, `rorig`: a world's path from the root, the root stage of its stage, and its
  origins at the root (`GCluOrig`).
* **Raw objects** (`CRDom`): a necessary object has a value along each arrow of the root, a
  possible object an extent of such arrows with a value along each.
* `preTB`, `preTD`: a world's `□`-view and `◇_x`-view terms read at the root (one renaming).
* ⭐`cden`: the denotation, **one structural recursion on the type**.  At a modal type a world's
  term denotes the root's denotation of its preimage, inlined: `□b` along `a` is the denotation at
  `a`'s end of the preimage of `b` translated along `a`'s path (`pTr`); `◇_x b` has the arrows of
  the extent of `x`'s origin (`InExt`), with contents translated by `pTrX`.
* `cden_mono`: it commutes with weakening; ⭐`cden_congr`: it does not depend on the stage.
* `cden_root_box`, `cden_root_dia`: at the root, as on the growing tree; ⭐`cden_box_eq`,
  ⭐`cden_dia_eq`: a world's modal term denotes the root's denotation of its preimage.
* `CDefinable` and its closure lemmas.
* ⭐`cdefinable_box_iff`, ⭐`cdefinable_dia_iff` (R4): at modal types a world defines exactly what
  the root defines — one way by preimages, the other by naming the root term at the world
  (`cden_named_box`, `cden_named_dia`), whose preimage is the root term renamed by the round trip, a
  weakening.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- The flags of the K45 cluster model: 5 and both lifts on, T and B off. -/
structure CluFlags : Prop where
  five : ModalSys.Five = true
  noT : ModalSys.T = false
  fourS : ModalSys.FourStrong = true
  fourSW : ModalSys.FourStrongW = true
  noB : ModalSys.B = false
  noBStrong : ModalSys.BStrong = false

theorem CluFlags.keepOnly (hX : CluFlags) : ModalSys.keepOnly = false := by
  simp [ModalSys.keepOnly, hX.noT]

theorem rpre (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) :
    PPreOk (rpath s) (groot hF M₀) s (rpath_eq s) i :=
  pPreOk hX.five hX.fourS hX.fourSW hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i

/-! ## Raw objects -/

variable (hF M₀) in
/-- The arrows of every world: the root's. -/
abbrev CAcc : Type := GAcc hF M₀ (groot hF M₀)

/-- A raw possible object: an extent and a raw object along each of its arrows. -/
structure CRPos (C : CAcc hF M₀ → Type) where
  E : Set (CAcc hF M₀)
  c : (a : E) → C a.1

variable (hM₀ : Theory.IsMCS M₀)

/-- Raw objects of a type at a world; at modal types they do not depend on the world. -/
def CRDom : VarType → GW hF M₀ → Type
  | .Var, s => (gw hM₀ s).D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A C, s => CRDom A s × CRDom C s
  | .VTypeBox A, _ => (a : CAcc hF M₀) → CRDom A a.1
  | .VTypeDia A, _ => CRPos fun a => CRDom A a.1

/-! ## Preimages of terms at the root -/

variable {hM₀}

/-- A world's `□`-view term, read at the root. -/
noncomputable def preTB (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat s i)).boxIn A a) :
    Σ c : Ann A, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView none) A c :=
  ⟨_, Term.subst (eIdx (ofRen (preI (rorig s))))
    (eS σ (ctxOf (glat (groot hF M₀) (rstg s i))).boxIn (ofRen (preI (rorig s))))
    (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI (rpre hX hM₀ s i))))
    (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI (rpre hX hM₀ s i)))) b⟩

theorem itemOk_rpreX (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) :
    ItemOk ((ctxOf (glat s i)).diaIn x) ((ctxOf (glat (groot hF M₀) (rstg s i))).diaIn (rorig s x))
      (preIX (rorig s) x) := by
  obtain ⟨X, hX'⟩ := hx
  exact itemOk_preIX hX' (rpre hX hM₀ s i)

/-- A world's `◇_x`-view term, read at the root in the view of `x`'s origin. -/
noncomputable def preTD (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat s i)).diaIn x) A a) :
    Σ c : Ann A, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView (some (rorig s x))) A c :=
  ⟨_, Term.subst (eIdx (ofRen (preIX (rorig s) x)))
    (eS σ ((ctxOf (glat (groot hF M₀) (rstg s i))).diaIn (rorig s x)) (ofRen (preIX (rorig s) x)))
    (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_rpreX hX hM₀ s i hx)))
    (coh_eS_kView (k := some x) (entOk_ofRen (itemOk_rpreX hX hM₀ s i hx))) b⟩

theorem rorig_ref (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) :
    ∃ X, (ctxOf (glat (groot hF M₀) (rstg s i))).ref (rorig s x) = some (.VTypeDia X) :=
  hx.imp fun _ h => rpre hX hM₀ s i x _ h rfl

/-! ## Denotations -/

variable (hM₀) in
/-- ⭐**The denotation of a term at a world**, computed at a stage containing its context.  At
    a modal type it is the root's denotation of the term's preimage, inlined, so the recursion is
    on the type alone. -/
noncomputable def cden (hX : CluFlags) : {A : VarType} → {a : Ann A} → {Γ : Ctx} →
    (s : GW hF M₀) → (i : ℕ) → Γ.Le (ctxOf (glat s i)) → Term σ Γ A a → CRDom hM₀ A s
  | _, _, _, s, i, e, .var v hv => (gw hM₀ s).cls i (.var v (e.ref hv))
  | _, _, _, s, i, e, .func f => (gw hM₀ s).cls i (Term.mono e (.func f))
  | _, _, _, _, _, _, .unit => PUnit.unit
  | _, _, _, s, i, e, .pair t u => (cden hX s i e t, cden hX s i e u)
  | _, _, _, s, i, e, .boxtm b => fun a =>
      cden hX a.1 (pstg (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rstg s i))
        (Ctx.Le.refl _)
        (pTr hM₀ (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (pathOf_ok a.2.down)
          (rstg s i) (preTB hX hM₀ s i (Term.mono e.boxIn b)).2).2
  | _, _, _, s, i, e, .diatm x hx t =>
      ⟨{a | InExt (groot hF M₀) a.1 (pathOf a.2.down) (pathOf_eq a.2.down) (rorig s x)}, fun a =>
        cden hX a.1.1
          (pstg (groot hF M₀) a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) (rstg s i))
          (Ctx.Le.refl _)
          (pTrX hM₀ (groot hF M₀) a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) (rstg s i)
            (rorig s x) (rorig_ref hX hM₀ s i (hx.imp fun _ h => e.ref h)) a.2
            (preTD hX hM₀ s i (hx.imp fun _ h => e.ref h) (Term.mono (e.diaIn x) t)).2).2⟩
  termination_by structural A => A

theorem cden_sigma (hX : CluFlags) {A : VarType} {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) :
    cden hM₀ hX s i e p.2 = cden hM₀ hX s i e q.2 := by
  subst h
  rfl

/-- The denotation commutes with weakening. -/
theorem cden_mono (hX : CluFlags) : ∀ {A : VarType} {a : Ann A} {Γ Γ' : Ctx} (h : Γ.Le Γ')
    (t : Term σ Γ A a) (s : GW hF M₀) (i : ℕ) (e : Γ'.Le (ctxOf (glat s i))),
    cden hM₀ hX s i e (Term.mono h t) = cden hM₀ hX s i (h.trans e) t
  | _, _, _, _, _, .var _ _, _, _, _ => rfl
  | _, _, _, _, h, .func f, s, i, e => by
      change (gw hM₀ s).cls i (Term.mono e (Term.mono h (.func f))) =
        (gw hM₀ s).cls i (Term.mono (h.trans e) (.func f))
      rw [Term.mono_mono]
  | _, _, _, _, _, .unit, _, _, _ => rfl
  | _, _, _, _, h, .pair t u, s, i, e => Prod.ext (cden_mono hX h t s i e) (cden_mono hX h u s i e)
  | _, _, _, _, h, .boxtm t, s, i, e => funext fun a => by
      change cden hM₀ hX s i e (.boxtm (Term.mono h.boxIn t)) a =
        cden hM₀ hX s i (h.trans e) (.boxtm t) a
      simp only [cden]
      rw [Term.mono_mono]
  | _, _, _, _, h, .diatm x hx t, s, i, e => by
      change cden hM₀ hX s i e (.diatm x _ (Term.mono (h.diaIn x) t)) = _
      simp only [cden]
      congr 1
      funext a
      rw [Term.mono_mono]
  termination_by structural A => A

/-- The root stage `R` reads a world's stage-`i` preimages, when it is no earlier. -/
theorem rpre_le (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) {i R : ℕ}
    (hR : rstg s i ≤ R) :
    ∀ z T, (ctxOf (glat s i)).ref z = some T → T.keepable = true →
      (ctxOf (glat (groot hF M₀) R)).ref (rorig s z) = some T :=
  fun z T hz hkp => (gle hM₀ (groot hF M₀) hR).ref (rpre hX hM₀ s i z T hz hkp)

theorem itemOk_rpreX_le (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) {i R : ℕ}
    (hR : rstg s i ≤ R) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) :
    ItemOk ((ctxOf (glat s i)).diaIn x) ((ctxOf (glat (groot hF M₀) R)).diaIn (rorig s x))
      (preIX (rorig s) x) := by
  obtain ⟨X, hX'⟩ := hx
  exact itemOk_preIX hX' (rpre_le hX hM₀ s hR)

/-- ⭐**The denotation does not depend on the stage it is computed at.**  The root stages of two
    stages need not be ordered; both preimages are read at the later one, where the renaming is
    the same (`porig` is stage-free). -/
theorem cden_congr (hX : CluFlags) : ∀ {A : VarType} {a : Ann A} {Γ : Ctx} (t : Term σ Γ A a)
    (s : GW hF M₀) (i j : ℕ) (e : Γ.Le (ctxOf (glat s i))) (e' : Γ.Le (ctxOf (glat s j))),
    cden hM₀ hX s i e t = cden hM₀ hX s j e' t
  | _, _, _, .var _ _, s, i, j, _, _ =>
      Quotient.sound (BWorld.TEq_of_lift_eq (w := gw hM₀ s) (le_max_left i j)
        (le_max_right i j) rfl)
  | _, _, _, .func _, s, i, j, _, _ =>
      Quotient.sound (BWorld.TEq_of_lift_eq (w := gw hM₀ s) (le_max_left i j)
        (le_max_right i j) ((Term.mono_mono _ _ _).trans (Term.mono_mono _ _ _).symm))
  | _, _, _, .unit, _, _, _, _, _ => rfl
  | _, _, _, .pair t u, s, i, j, e, e' =>
      Prod.ext (cden_congr hX t s i j e e') (cden_congr hX u s i j e e')
  | _, _, Γ, .boxtm b, s, i, j, e, e' => funext fun a => by
      simp only [cden]
      set P := pathOf a.2.down
      have hP := pathOf_eq a.2.down
      have hne := pathOf_ok a.2.down
      set R := max (rstg s i) (rstg s j)
      have side : ∀ (k : ℕ) (hk : rstg s k ≤ R) (ek : Γ.Le (ctxOf (glat s k))),
          cden hM₀ hX a.1 (pstg (groot hF M₀) a.1 P hP (rstg s k)) (Ctx.Le.refl _)
              (pTr hM₀ (groot hF M₀) a.1 P hP hne (rstg s k)
                (preTB hX hM₀ s k (Term.mono ek.boxIn b)).2).2 =
            cden hM₀ hX a.1 (pstg (groot hF M₀) a.1 P hP R) (Ctx.Le.refl _)
              (pTr hM₀ (groot hF M₀) a.1 P hP hne R
                (Term.subst (eIdx (ofRen (preI (rorig s))))
                  (eS σ (ctxOf (glat (groot hF M₀) R)).boxIn (ofRen (preI (rorig s))))
                  ((ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI
                    (rpre_le hX hM₀ s (le_max_left _ _))))).restrict e.boxIn)
                  ((coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI
                    (rpre_le hX hM₀ s (le_max_left _ _))))).restrict e.boxIn) b)).2 := by
        intro k hk ek
        have hm := pstg_monotone hM₀ (groot hF M₀) a.1 P hP hk
        refine (cden_congr hX _ a.1 _ (pstg (groot hF M₀) a.1 P hP R) (Ctx.Le.refl _)
          (gle hM₀ a.1 hm)).trans ?_
        refine ((cden_mono hX (gle hM₀ a.1 hm) _ a.1 _ (Ctx.Le.refl _)).symm).trans ?_
        refine cden_sigma hX _ ((pTr_mono hM₀ (groot hF M₀) a.1 P hP hne hk _).trans ?_)
        refine pTr_sigma hM₀ _ _ _ _ _ _ ?_
        change (⟨_, Term.mono _ (Term.subst _ _ _ _ (Term.mono ek.boxIn b))⟩ :
          Σ c, Term σ _ _ c) = _
        rw [Term.mono_subst]
        refine (Term.subst_congr (ι' := eIdx (ofRen (preI (rorig s)))) _ _ _
          (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI (rpre_le hX hM₀ s hk))))
          _ (coh_eS_kView (k := none)
            (entOk_ofRen (itemOk_preI (rpre_le hX hM₀ s hk))))
          (sim_eS_mono (l := glat s k) (k := none) _
            (entOk_ofRen (itemOk_preI (rpre hX hM₀ s k)))) _).trans ?_
        rw [Term.subst_mono]
      exact (side i (le_max_left _ _) e).trans (side j (le_max_right _ _) e').symm
  | _, _, Γ, .diatm x hx b, s, i, j, e, e' => by
      simp only [cden]
      congr 1
      funext a
      set P := pathOf a.1.2.down
      have hP := pathOf_eq a.1.2.down
      set R := max (rstg s i) (rstg s j)
      have side : ∀ (k : ℕ) (hk : rstg s k ≤ R) (ek : Γ.Le (ctxOf (glat s k))),
          cden hM₀ hX a.1.1 (pstg (groot hF M₀) a.1.1 P hP (rstg s k)) (Ctx.Le.refl _)
              (pTrX hM₀ (groot hF M₀) a.1.1 P hP (rstg s k) (rorig s x)
                (rorig_ref hX hM₀ s k (hx.imp fun _ h => ek.ref h)) a.2
                (preTD hX hM₀ s k (hx.imp fun _ h => ek.ref h) (Term.mono (ek.diaIn x) b)).2).2 =
            cden hM₀ hX a.1.1 (pstg (groot hF M₀) a.1.1 P hP R) (Ctx.Le.refl _)
              (pTrX hM₀ (groot hF M₀) a.1.1 P hP R (rorig s x)
                ((rorig_ref hX hM₀ s i (hx.imp fun _ h => e.ref h)).imp fun _ h =>
                  (gle hM₀ (groot hF M₀) (le_max_left _ _)).ref h) a.2
                (Term.subst (eIdx (ofRen (preIX (rorig s) x)))
                  (eS σ ((ctxOf (glat (groot hF M₀) R)).diaIn (rorig s x))
                    (ofRen (preIX (rorig s) x)))
                  ((ok_eS_kView (k := some x) (entOk_ofRen (itemOk_rpreX_le hX hM₀ s
                    (le_max_left _ _) (hx.imp fun _ h => e.ref h)))).restrict (e.diaIn x))
                  ((coh_eS_kView (k := some x) (entOk_ofRen (itemOk_rpreX_le hX hM₀ s
                    (le_max_left _ _) (hx.imp fun _ h => e.ref h)))).restrict (e.diaIn x))
                  b)).2 := by
        intro k hk ek
        have hm := pstg_monotone hM₀ (groot hF M₀) a.1.1 P hP hk
        refine (cden_congr hX _ a.1.1 _ (pstg (groot hF M₀) a.1.1 P hP R) (Ctx.Le.refl _)
          (gle hM₀ a.1.1 hm)).trans ?_
        refine ((cden_mono hX (gle hM₀ a.1.1 hm) _ a.1.1 _ (Ctx.Le.refl _)).symm).trans ?_
        refine cden_sigma hX _ ((pTrX_mono hM₀ (groot hF M₀) a.1.1 P hP hk _ _ a.2 _).trans ?_)
        refine pTrX_sigma hM₀ _ _ _ _ _ _ _ _ ?_
        change (⟨_, Term.mono _ (Term.subst _ _ _ _ (Term.mono (ek.diaIn x) b))⟩ :
          Σ c, Term σ _ _ c) = _
        rw [Term.mono_subst]
        refine (Term.subst_congr (ι' := eIdx (ofRen (preIX (rorig s) x))) _ _ _
          (ok_eS_kView (k := some x) (entOk_ofRen
            (itemOk_rpreX_le hX hM₀ s hk (hx.imp fun _ h => ek.ref h))))
          _ (coh_eS_kView (k := some x) (entOk_ofRen
            (itemOk_rpreX_le hX hM₀ s hk (hx.imp fun _ h => ek.ref h))))
          (sim_eS_mono (l := glat s k) (k := some x) _
            (entOk_ofRen (itemOk_rpreX hX hM₀ s k (hx.imp fun _ h => ek.ref h)))) _).trans ?_
        rw [Term.subst_mono]
      exact (side i (le_max_left _ _) e).trans (side j (le_max_right _ _) e').symm
  termination_by structural A => A

/-! ## At the root, and a world's denotation through the root -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- The identity renaming of a `□`-view term is the term. -/
theorem subst_preI_id {l : List VarType} {A : VarType} {a : Ann A}
    (b : Term σ (ctxOf l).boxIn A a)
    (hθ : Subst.Ok (ctxOf l).boxIn (eS σ (ctxOf l).boxIn (ofRen (preI id))))
    (hc : Subst.Coh (eIdx (ofRen (σ := σ) (preI id))) (ctxOf l).boxIn
      (eS σ (ctxOf l).boxIn (ofRen (preI id)))) :
    (⟨_, Term.subst (eIdx (ofRen (σ := σ) (preI id))) (eS σ (ctxOf l).boxIn (ofRen (preI id)))
        hθ hc b⟩ : Σ c, Term σ (ctxOf l).boxIn A c) = ⟨a, b⟩ := by
  refine (Term.subst_congr _ (Subst.idS σ _) hθ (Subst.ok_idS_le (Ctx.Le.refl _)) hc
    (Subst.coh_idS_le (Ctx.Le.refl _)) (Subst.sim_of fun v T hl hv => ?_) b).trans ?_
  · match v, hl with
    | .root _, _ => cases hv
    | .step u st, hl =>
        rw [eS_item _ hl]
        change SubE.Sim T (.ren (preI id (.step u st))) (.ren (.step u st))
        rw [show preI id (.step u st) = .step u st by cases st <;> rfl]
        exact .refl _
  · rw [Term.subst_idS_mono (Ctx.Le.refl _) _ _ b, Term.mono_refl]

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- The identity renaming of a `◇_x`-view term is the term. -/
theorem subst_preIX_id {l : List VarType} {x : VarSymb} {A : VarType} {a : Ann A}
    (b : Term σ ((ctxOf l).diaIn x) A a)
    (hθ : Subst.Ok ((ctxOf l).diaIn x) (eS σ ((ctxOf l).diaIn x) (ofRen (preIX id x))))
    (hc : Subst.Coh (eIdx (ofRen (σ := σ) (preIX id x))) ((ctxOf l).diaIn x)
      (eS σ ((ctxOf l).diaIn x) (ofRen (preIX id x)))) :
    (⟨_, Term.subst (eIdx (ofRen (σ := σ) (preIX id x)))
        (eS σ ((ctxOf l).diaIn x) (ofRen (preIX id x))) hθ hc b⟩ :
        Σ c, Term σ ((ctxOf l).diaIn x) A c) = ⟨a, b⟩ := by
  refine (Term.subst_congr _ (Subst.idS σ _) hθ (Subst.ok_idS_le (Ctx.Le.refl _)) hc
    (Subst.coh_idS_le (Ctx.Le.refl _)) (Subst.sim_of fun v T hl hv => ?_) b).trans ?_
  · match v, hl with
    | .root _, _ => cases hv
    | .step u st, hl =>
        rw [eS_item _ hl]
        change SubE.Sim T (.ren (preIX id x (.step u st))) (.ren (.step u st))
        rw [show preIX id x (.step u st) = .step u st by
          unfold preIX
          split_ifs with h
          · exact h.symm
          · cases st <;> rfl]
        exact .refl _
  · rw [Term.subst_idS_mono (Ctx.Le.refl _) _ _ b, Term.mono_refl]

/-- At the root, a necessary term denotes as on the growing tree: along each arrow, the term
    translated along its path. -/
theorem cden_root_box (hX : CluFlags) {A : VarType} {a : Ann A} {Γ : Ctx} (i : ℕ)
    (e : Γ.Le (ctxOf (glat (groot hF M₀) i))) (b : Term σ Γ.boxIn A a) (a' : CAcc hF M₀) :
    cden hM₀ hX (groot hF M₀) i e (.boxtm b) a' =
      cden hM₀ hX a'.1 (pstg (groot hF M₀) a'.1 (pathOf a'.2.down) (pathOf_eq a'.2.down) i)
        (Ctx.Le.refl _)
        (pTr hM₀ (groot hF M₀) a'.1 (pathOf a'.2.down) (pathOf_eq a'.2.down) (pathOf_ok a'.2.down)
          i (Term.mono e.boxIn b)).2 :=
  cden_sigma hX _ (pTr_sigma hM₀ _ _ _ _ _ _ (subst_preI_id _ _ _))

/-- At the root, a possible term denotes as on the growing tree, without T. -/
theorem cden_root_dia (hX : CluFlags) {A : VarType} {a : Ann A} {Γ : Ctx} (i : ℕ)
    (e : Γ.Le (ctxOf (glat (groot hF M₀) i))) (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (b : Term σ (Γ.diaIn x) A a) :
    cden hM₀ hX (groot hF M₀) i e (.diatm x hx b) =
      ⟨{a' | InExt (groot hF M₀) a'.1 (pathOf a'.2.down) (pathOf_eq a'.2.down) x}, fun a' =>
        cden hM₀ hX a'.1.1
          (pstg (groot hF M₀) a'.1.1 (pathOf a'.1.2.down) (pathOf_eq a'.1.2.down) i)
          (Ctx.Le.refl _)
          (pTrX hM₀ (groot hF M₀) a'.1.1 (pathOf a'.1.2.down) (pathOf_eq a'.1.2.down) i x
            (hx.imp fun _ h => e.ref h) a'.2 (Term.mono (e.diaIn x) b)).2⟩ := by
  simp only [cden]
  congr 1
  funext a'
  exact cden_sigma hX _ (pTrX_sigma hM₀ _ _ _ _ _ _ _ _ (subst_preIX_id _ _ _))

/-- ⭐**A world's necessary term denotes the root's denotation of its preimage.** -/
theorem cden_box_eq (hX : CluFlags) {A : VarType} {a : Ann A} {Γ : Ctx} (s : GW hF M₀)
    (i : ℕ) (e : Γ.Le (ctxOf (glat s i))) (b : Term σ Γ.boxIn A a) :
    cden hM₀ hX s i e (.boxtm b) =
      cden hM₀ hX (groot hF M₀) (rstg s i) (Ctx.Le.refl _)
        (.boxtm (preTB hX hM₀ s i (Term.mono e.boxIn b)).2) := by
  funext a'
  rw [cden_root_box, Term.mono_refl]
  rfl

/-- ⭐**A world's possible term denotes the root's denotation of its preimage.** -/
theorem cden_dia_eq (hX : CluFlags) {A : VarType} {a : Ann A} {Γ : Ctx} (s : GW hF M₀)
    (i : ℕ) (e : Γ.Le (ctxOf (glat s i))) (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (b : Term σ (Γ.diaIn x) A a) :
    cden hM₀ hX s i e (.diatm x hx b) =
      cden hM₀ hX (groot hF M₀) (rstg s i) (Ctx.Le.refl _)
        (.diatm (rorig s x) (rorig_ref hX hM₀ s i (hx.imp fun _ h => e.ref h))
          (preTD hX hM₀ s i (hx.imp fun _ h => e.ref h) (Term.mono (e.diaIn x) b)).2) := by
  rw [cden_root_dia, Term.mono_refl]
  rfl

/-! ## Definable objects -/

variable (hM₀) in
/-- ⭐The raw objects denoted by terms. -/
def CDefinable (hX : CluFlags) (A : VarType) (s : GW hF M₀) (o : CRDom hM₀ A s) : Prop :=
  ∃ (i : ℕ) (a : Ann A) (t : Term σ (ctxOf (glat s i)) A a),
    cden hM₀ hX s i (Ctx.Le.refl _) t = o

theorem cdefinable_den (hX : CluFlags) {A : VarType} {a : Ann A} {Γ : Ctx} {s : GW hF M₀}
    {i : ℕ} (e : Γ.Le (ctxOf (glat s i))) (t : Term σ Γ A a) :
    CDefinable hM₀ hX A s (cden hM₀ hX s i e t) :=
  ⟨i, a, Term.mono e t, by rw [cden_mono]⟩

theorem cden_var_cls (hX : CluFlags) {s : GW hF M₀} {i : ℕ} :
    ∀ (t : Term σ (ctxOf (glat s i)) .Var .var),
      cden hM₀ hX s i (Ctx.Le.refl _) t = (gw hM₀ s).cls i t
  | .var _ _ => rfl
  | .func f => by
      change (gw hM₀ s).cls i (Term.mono (Ctx.Le.refl _) (.func f)) = _
      rw [Term.mono_refl]

theorem cdefinable_var (hX : CluFlags) {s : GW hF M₀} (d : (gw hM₀ s).D) :
    CDefinable hM₀ hX .Var s d :=
  Quotient.inductionOn d fun p => ⟨p.1, .var, p.2, cden_var_cls hX p.2⟩

theorem cdefinable_unit (hX : CluFlags) {s : GW hF M₀} (o : CRDom hM₀ .VTypeOne s) :
    CDefinable hM₀ hX .VTypeOne s o :=
  ⟨0, .one, .unit, rfl⟩

theorem cdefinable_fst (hX : CluFlags) {A C : VarType} {s : GW hF M₀}
    {o : CRDom hM₀ (.VTypeProd A C) s} (h : CDefinable hM₀ hX (.VTypeProd A C) s o) :
    CDefinable hM₀ hX A s o.1 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair u _ => exact ⟨i, _, u, rfl⟩

theorem cdefinable_snd (hX : CluFlags) {A C : VarType} {s : GW hF M₀}
    {o : CRDom hM₀ (.VTypeProd A C) s} (h : CDefinable hM₀ hX (.VTypeProd A C) s o) :
    CDefinable hM₀ hX C s o.2 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair _ u => exact ⟨i, _, u, rfl⟩

theorem cdefinable_pair (hX : CluFlags) {A C : VarType} {s : GW hF M₀} {o₁ : CRDom hM₀ A s}
    {o₂ : CRDom hM₀ C s} (h₁ : CDefinable hM₀ hX A s o₁) (h₂ : CDefinable hM₀ hX C s o₂) :
    CDefinable hM₀ hX (.VTypeProd A C) s ((o₁, o₂) : CRDom hM₀ (.VTypeProd A C) s) := by
  obtain ⟨i₁, a₁, t₁, rfl⟩ := h₁
  obtain ⟨i₂, a₂, t₂, rfl⟩ := h₂
  refine ⟨max i₁ i₂, _, .pair ((gw hM₀ s).liftT (le_max_left _ _) t₁)
    ((gw hM₀ s).liftT (le_max_right _ _) t₂), Prod.ext ?_ ?_⟩
  · change cden hM₀ hX s _ _ (Term.mono _ t₁) = _
    rw [cden_mono]
    exact cden_congr hX _ _ _ _ _ _
  · change cden hM₀ hX s _ _ (Term.mono _ t₂) = _
    rw [cden_mono]
    exact cden_congr hX _ _ _ _ _ _

theorem cdefinable_box_apply (hX : CluFlags) {A : VarType} {s : GW hF M₀}
    {o : CRDom hM₀ (.VTypeBox A) s} (h : CDefinable hM₀ hX (.VTypeBox A) s o)
    (a : CAcc hF M₀) : CDefinable hM₀ hX A a.1 (o a) := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | boxtm b => exact cdefinable_den hX _ _

theorem cdefinable_dia_apply (hX : CluFlags) {A : VarType} {s : GW hF M₀}
    {o : CRDom hM₀ (.VTypeDia A) s} (h : CDefinable hM₀ hX (.VTypeDia A) s o) (a : o.E) :
    CDefinable hM₀ hX A a.1.1 (o.c a) := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | diatm x hx b => exact cdefinable_den hX _ _

/-! ## Definable at a world = definable at the root (R4), at `□` types -/

/-- ⭐**What a world defines at a `□` type, the root defines**: its preimage. -/
theorem cdefinable_box_root (hX : CluFlags) {A : VarType} (s : GW hF M₀)
    (o : CRDom hM₀ (.VTypeBox A) s) (h : CDefinable hM₀ hX (.VTypeBox A) s o) :
    CDefinable hM₀ hX (.VTypeBox A) (groot hF M₀) o := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | boxtm b =>
      exact ⟨rstg s i, _, .boxtm (preTB hX hM₀ s i (Term.mono (Ctx.Le.refl _).boxIn b)).2,
        (cden_box_eq hX s i _ b).symm⟩

/-- ⭐**A root `□`-term named at a world denotes what the root term does** (R4), at any stage
    of the world where the names are declared: the named term's preimage is the root term
    renamed by the round trip (`Term.subst_comp_sig`, `sim_eS_ren_comp`), a weakening
    (`round_trip`). -/
theorem cden_named_box (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i J : ℕ)
    (hJ : ∀ z T, (ctxOf (glat (groot hF M₀) i)).ref z = some T → T.keepable = true →
      (ctxOf (glat s J)).ref (pnm (rpath s) (groot hF M₀) s (rpath_eq s) z) = some T)
    {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat (groot hF M₀) i)).boxIn A a) :
    cden hM₀ hX s J (Ctx.Le.refl _)
        (.boxtm (Term.subst (eIdx (ofRen (preI (pnm (rpath s) (groot hF M₀) s (rpath_eq s)))))
          (eS σ (ctxOf (glat s J)).boxIn
            (ofRen (preI (pnm (rpath s) (groot hF M₀) s (rpath_eq s)))))
          (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hJ)))
          (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hJ))) b)) =
      cden hM₀ hX (groot hF M₀) i (Ctx.Le.refl _) (.boxtm b) := by
  rw [cden_box_eq]
  set r := rstg s J
  set K := max i r
  have hrtr : ∀ z T, (ctxOf (glat (groot hF M₀) i)).ref z = some T → T.keepable = true →
      (ctxOf (glat (groot hF M₀) r)).ref
        ((rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) z) = some T :=
    fun z T hz hkp => rpre hX hM₀ s J _ T (hJ z T hz hkp) hkp
  have hrtK : ∀ z T, (ctxOf (glat (groot hF M₀) i)).ref z = some T → T.keepable = true →
      (ctxOf (glat (groot hF M₀) K)).ref
        ((rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) z) = some T :=
    fun z T hz hkp => (gle hM₀ _ (le_max_right i r)).ref (hrtr z T hz hkp)
  refine (cden_congr hX _ _ _ K _ (gle hM₀ _ (le_max_right i r))).trans ?_
  refine (cden_mono hX (gle hM₀ _ (le_max_right i r)) _ _ _ (Ctx.Le.refl _)).symm.trans ?_
  refine Eq.trans ?_ ((cden_mono hX (gle hM₀ _ (le_max_left i r)) _ _ _
    (Ctx.Le.refl _)).trans (cden_congr hX _ _ _ _ _ _))
  refine cden_sigma hX _ (sig_boxtm ?_)
  have e0 : (⟨_, (preTB hX hM₀ s J (Term.mono (Ctx.Le.refl _).boxIn
        (Term.subst (eIdx (ofRen (preI (pnm (rpath s) (groot hF M₀) s (rpath_eq s)))))
          (eS σ (ctxOf (glat s J)).boxIn
            (ofRen (preI (pnm (rpath s) (groot hF M₀) s (rpath_eq s)))))
          (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hJ)))
          (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hJ))) b))).2⟩ :
        Σ c, Term σ (ctxOf (glat (groot hF M₀) r)).boxIn A c) =
      ⟨_, Term.subst (eIdx (ofRen (preI (rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)))))
        (eS σ (ctxOf (glat (groot hF M₀) r)).boxIn
          (ofRen (preI (rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)))))
        (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hrtr)))
        (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hrtr))) b⟩ := by
    simp only [preTB, Term.mono_refl]
    refine Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
      fun u st _ hst _ => ?_) b
    obtain ⟨u', e⟩ := preI_step (pnm (rpath s) (groot hF M₀) s (rpath_eq s)) u st
    exact ⟨u', st, e, hst, by rw [← e, preI_comp]⟩
  have e1 := congrArg (fun p : Σ c, Term σ (ctxOf (glat (groot hF M₀) r)).boxIn A c =>
    (⟨p.1, Term.mono (gle hM₀ _ (le_max_right i r)).boxIn p.2⟩ :
      Σ c, Term σ (ctxOf (glat (groot hF M₀) K)).boxIn A c)) e0
  refine e1.trans ?_
  dsimp only
  rw [Term.mono_subst]
  have hKo := itemOk_preI hrtK
  refine (Term.subst_congr
    (ι' := eIdx (ofRen (preI (rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s))))) _ _ _
    (ok_eS_kView (k := none) (entOk_ofRen hKo)) _ (coh_eS_kView (k := none) (entOk_ofRen hKo))
    (sim_eS_mono (l := glat (groot hF M₀) i) (k := none) _
      (entOk_ofRen (itemOk_preI hrtr))) b).trans ?_
  exact round_trip hX.five hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i hrtK
    (le_max_left i r) b

/-- ⭐**What the root defines at a `□` type, every world defines** (R4): the root term named at
    the world (`cden_named_box`). -/
theorem cdefinable_box_of_root (hX : CluFlags) {A : VarType} (s : GW hF M₀)
    (o : CRDom hM₀ (.VTypeBox A) (groot hF M₀))
    (h : CDefinable hM₀ hX (.VTypeBox A) (groot hF M₀) o) :
    CDefinable hM₀ hX (.VTypeBox A) s o := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | boxtm b =>
      exact ⟨_, _, _, cden_named_box hX hM₀ s i _
        (pnm_ref hX.five hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i) b⟩

/-- ⭐**At a `□` type a world defines exactly what the root defines.** -/
theorem cdefinable_box_iff (hX : CluFlags) {A : VarType} (s : GW hF M₀)
    (o : CRDom hM₀ (.VTypeBox A) s) :
    CDefinable hM₀ hX (.VTypeBox A) s o ↔ CDefinable hM₀ hX (.VTypeBox A) (groot hF M₀) o :=
  ⟨cdefinable_box_root hX s o, cdefinable_box_of_root hX s o⟩

/-! ## Definable at a world = definable at the root (R4), at `◇` types -/

/-- ⭐**What a world defines at a `◇` type, the root defines**: its preimage. -/
theorem cdefinable_dia_root (hX : CluFlags) {A : VarType} (s : GW hF M₀)
    (o : CRDom hM₀ (.VTypeDia A) s) (h : CDefinable hM₀ hX (.VTypeDia A) s o) :
    CDefinable hM₀ hX (.VTypeDia A) (groot hF M₀) o := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | diatm x hx b =>
      exact ⟨rstg s i, _, _, (cden_dia_eq hX s i _ x hx b).symm⟩

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A renaming of a `◇_x` view fixing `x` and every η-faithful item is weakening.  The witness's
    image is a variable `y` with `y = x`, so that the target view can be rewritten. -/
theorem ren_dia_fix {l l' : List VarType} (hle : (ctxOf l).Le (ctxOf l')) (f : VarSymb → VarSymb)
    {x : VarSymb}
    (hfix : ∀ u st T, st.isProj = false → (ctxOf l).boxIn (.step u st) = some T →
      T.etaInj = true → preI f (.step u st) = .step u st) :
    ∀ (y : VarSymb) (_hy : f x = y) (_hyx : y = x)
      (hθ : Subst.Ok ((ctxOf l).diaIn x) (eS σ ((ctxOf l').diaIn y) (ofRen (preIX f x))))
      (hc : Subst.Coh (eIdx (ofRen (σ := σ) (preIX f x))) ((ctxOf l).diaIn x)
        (eS σ ((ctxOf l').diaIn y) (ofRen (preIX f x))))
      {A : VarType} {a : Ann A} (b : Term σ ((ctxOf l).diaIn x) A a),
      HEq (⟨_, Term.subst (eIdx (ofRen (σ := σ) (preIX f x)))
          (eS σ ((ctxOf l').diaIn y) (ofRen (preIX f x))) hθ hc b⟩ :
          Σ c, Term σ ((ctxOf l').diaIn y) A c)
        (⟨a, Term.mono (hle.diaIn x) b⟩ : Σ c, Term σ ((ctxOf l').diaIn x) A c) := by
  intro y hy hyx hθ hc A a b
  subst hyx
  refine heq_of_eq ((Term.subst_congrF _ (Subst.idS σ _) hθ (Subst.ok_idS_le (hle.diaIn y)) hc
    (Subst.coh_idS_le (hle.diaIn y)) (Subst.simF_of fun v T hl hv hT => ?_) b).trans
    (Term.subst_idS_mono (hle.diaIn y) _ _ b))
  match v, hl with
  | .root _, _ => cases hv
  | .step u st, hl =>
      rw [eS_item _ hl]
      change SubE.Sim T (.ren (preIX f y (.step u st))) (.ren (.step u st))
      by_cases hvx : VarSymb.step u st = .step y .dia
      · rw [show preIX f y (.step u st) = .step u st by
          unfold preIX
          rw [if_pos hvx, hy, hvx]]
        exact .refl _
      · rw [show preIX f y (.step u st) = .step u st by
          unfold preIX
          rw [if_neg hvx]
          exact hfix u st T hl (diaIn_boxIn_of_ne' hv hvx) hT]
        exact .refl _

/-- Two root denotations of possible terms agree when their witnesses do and their bodies do
    at a common stage; the witnesses are equal only propositionally, so one is a variable. -/
theorem cden_root_dia_wit (hX : CluFlags) {A : VarType} {a a' : Ann A} {r i K : ℕ}
    (hrK : r ≤ K) (hiK : i ≤ K) {y : VarSymb}
    (hy : ∃ Y, (ctxOf (glat (groot hF M₀) i)).ref y = some (.VTypeDia Y))
    (b : Term σ ((ctxOf (glat (groot hF M₀) i)).diaIn y) A a) :
    ∀ (y' : VarSymb) (_hyy : y' = y)
      (hy' : ∃ Y, (ctxOf (glat (groot hF M₀) r)).ref y' = some (.VTypeDia Y))
      (u : Term σ ((ctxOf (glat (groot hF M₀) r)).diaIn y') A a'),
      HEq (⟨_, Term.mono ((gle hM₀ (groot hF M₀) hrK).diaIn y') u⟩ :
          Σ c, Term σ ((ctxOf (glat (groot hF M₀) K)).diaIn y') A c)
        (⟨_, Term.mono ((gle hM₀ (groot hF M₀) hiK).diaIn y) b⟩ :
          Σ c, Term σ ((ctxOf (glat (groot hF M₀) K)).diaIn y) A c) →
      cden hM₀ hX (groot hF M₀) r (Ctx.Le.refl _) (.diatm y' hy' u) =
        cden hM₀ hX (groot hF M₀) i (Ctx.Le.refl _) (.diatm y hy b) := by
  intro y' hyy hy' u H
  subst hyy
  have H' := eq_of_heq H
  refine (cden_congr hX _ _ _ K _ (gle hM₀ _ hrK)).trans ?_
  refine (cden_mono hX (gle hM₀ _ hrK) _ _ _ (Ctx.Le.refl _)).symm.trans ?_
  refine Eq.trans ?_ ((cden_mono hX (gle hM₀ _ hiK) _ _ _ (Ctx.Le.refl _)).trans
    (cden_congr hX _ _ _ _ _ _))
  exact cden_sigma hX _ (sig_diatm H')

/-- The round trip fixes every η-faithful item of a root's `□` view. -/
theorem rt_fix (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) :
    ∀ u st T, st.isProj = false → (ctxOf (glat (groot hF M₀) i)).boxIn (.step u st) = some T →
      T.etaInj = true →
      preI (rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) (.step u st) = .step u st
  | u, .box, T, _, hb, hT => by
      have hu := Ctx.boxIn_step_box hb
      change VarSymb.step (porig (rpath s) (groot hF M₀) s (rpath_eq s)
        (pnm (rpath s) (groot hF M₀) s (rpath_eq s) u)) .box = _
      rw [porig_pnm hX.five hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i u _ hu rfl hT]
  | u, .keep, T, _, hb, hT => by
      obtain ⟨-, hu, hkp⟩ := Ctx.boxIn_keep hb
      change VarSymb.step (porig (rpath s) (groot hF M₀) s (rpath_eq s)
        (pnm (rpath s) (groot hF M₀) s (rpath_eq s) u)) .keep = _
      rw [porig_pnm hX.five hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i u _ hu hkp hT]
  | _, .fst, _, _, hb, _ => by cases hb
  | _, .snd, _, _, hb, _ => by cases hb
  | _, .dia, _, _, hb, _ => by cases hb
  | _, .here, _, _, hb, _ => by cases hb

/-- ⭐**A root possible term named at a world denotes what the root term does** (R4), at any
    stage of the world where the names are declared: its preimage is at the witness's round
    trip, which is the witness (`porig_pnm`), with the body renamed by the round trip, a
    weakening (`ren_dia_fix`, `cden_root_dia_wit`). -/
theorem cden_named_dia (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i J : ℕ)
    {y : VarSymb} {Y : VarType} (hY : (ctxOf (glat (groot hF M₀) i)).ref y = some (.VTypeDia Y))
    (hJ : ∀ z T, (ctxOf (glat (groot hF M₀) i)).ref z = some T → T.keepable = true →
      (ctxOf (glat s J)).ref (pnm (rpath s) (groot hF M₀) s (rpath_eq s) z) = some T)
    {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat (groot hF M₀) i)).diaIn y) A a) :
    cden hM₀ hX s J (Ctx.Le.refl _)
        (.diatm (pnm (rpath s) (groot hF M₀) s (rpath_eq s) y) ⟨Y, hJ y _ hY rfl⟩
          (Term.subst (eIdx (ofRen (preIX (pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)))
            (eS σ ((ctxOf (glat s J)).diaIn (pnm (rpath s) (groot hF M₀) s (rpath_eq s) y))
              (ofRen (preIX (pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)))
            (ok_eS_kView (k := some y) (entOk_ofRen (itemOk_preIX hY hJ)))
            (coh_eS_kView (k := some y) (entOk_ofRen (itemOk_preIX hY hJ))) b)) =
      cden hM₀ hX (groot hF M₀) i (Ctx.Le.refl _) (.diatm y ⟨Y, hY⟩ b) := by
  rw [cden_dia_eq]
  set r := rstg s J
  set K := max i r
  have hrtr : ∀ z T, (ctxOf (glat (groot hF M₀) i)).ref z = some T → T.keepable = true →
      (ctxOf (glat (groot hF M₀) r)).ref
        ((rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) z) = some T :=
    fun z T hz hkp => rpre hX hM₀ s J _ T (hJ z T hz hkp) hkp
  have hrtK : ∀ z T, (ctxOf (glat (groot hF M₀) i)).ref z = some T → T.keepable = true →
      (ctxOf (glat (groot hF M₀) K)).ref
        ((rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) z) = some T :=
    fun z T hz hkp => (gle hM₀ _ (le_max_right i r)).ref (hrtr z T hz hkp)
  have hyy := porig_pnm hX.five hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i y _ hY
    rfl rfl
  have hKo := itemOk_preIX hY hrtK
  refine cden_root_dia_wit hX (le_max_right i r) (le_max_left i r) ⟨Y, hY⟩ b _ hyy _ _ ?_
  refine heq_of_eq_of_heq ?_ (ren_dia_fix (gle hM₀ (groot hF M₀) (le_max_left i r))
    (rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) (rt_fix hX hM₀ s i) _ rfl hyy
    (ok_eS_kView (k := some y) (entOk_ofRen hKo)) (coh_eS_kView (k := some y)
      (entOk_ofRen hKo)) b)
  have e0 : (⟨_, (preTD hX hM₀ s J ⟨Y, hJ y _ hY rfl⟩ (Term.mono (Ctx.Le.refl _)
        (Term.subst (eIdx (ofRen (preIX (pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)))
          (eS σ ((ctxOf (glat s J)).diaIn (pnm (rpath s) (groot hF M₀) s (rpath_eq s) y))
            (ofRen (preIX (pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)))
          (ok_eS_kView (k := some y) (entOk_ofRen (itemOk_preIX hY hJ)))
          (coh_eS_kView (k := some y) (entOk_ofRen (itemOk_preIX hY hJ))) b))).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) r)).diaIn
          ((rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)) A c) =
      ⟨_, Term.subst
        (eIdx (ofRen (preIX (rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)))
        (eS σ ((ctxOf (glat (groot hF M₀) r)).diaIn
            ((rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y))
          (ofRen (preIX (rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)))
        (ok_eS_kView (k := some y) (entOk_ofRen (itemOk_preIX hY hrtr)))
        (coh_eS_kView (k := some y) (entOk_ofRen (itemOk_preIX hY hrtr))) b⟩ := by
    simp only [preTD, Term.mono_refl]
    refine Term.subst_comp_sig _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
      fun u st _ hst hv => ?_) b
    have hc := preIX_comp (rorig s) (pnm (rpath s) (groot hF M₀) s (rpath_eq s))
      (v := .step u st) hst hv
    by_cases hvx : VarSymb.step u st = .step y .dia
    · have e : preIX (pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y (.step u st) =
          .step (pnm (rpath s) (groot hF M₀) s (rpath_eq s) y) .dia := by
        unfold preIX
        rw [if_pos hvx]
      exact ⟨_, .dia, e, rfl, by rw [← e, hc]⟩
    · obtain ⟨u', e'⟩ := preI_step (pnm (rpath s) (groot hF M₀) s (rpath_eq s)) u st
      have e : preIX (pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y (.step u st) =
          .step u' st := by
        unfold preIX
        rw [if_neg hvx, e']
      exact ⟨u', st, e, hst, by rw [← e, hc]⟩
  have e1 := congrArg (fun p : Σ c, Term σ ((ctxOf (glat (groot hF M₀) r)).diaIn
      ((rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)) A c =>
    (⟨p.1, Term.mono ((gle hM₀ _ (le_max_right i r)).diaIn _) p.2⟩ :
      Σ c, Term σ ((ctxOf (glat (groot hF M₀) K)).diaIn
        ((rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)) A c)) e0
  refine e1.trans ?_
  dsimp only
  rw [Term.mono_subst]
  exact Term.subst_congr
    (ι' := eIdx (ofRen (preIX (rorig s ∘ pnm (rpath s) (groot hF M₀) s (rpath_eq s)) y)))
    _ _ _ (ok_eS_kView (k := some y) (entOk_ofRen hKo)) _
    (coh_eS_kView (k := some y) (entOk_ofRen hKo))
    (sim_eS_mono (l := glat (groot hF M₀) i) (k := some y) _
      (entOk_ofRen (itemOk_preIX hY hrtr))) b

/-- ⭐**What the root defines at a `◇` type, every world defines** (R4): the root term named at
    the world (`cden_named_dia`). -/
theorem cdefinable_dia_of_root (hX : CluFlags) {A : VarType} (s : GW hF M₀)
    (o : CRDom hM₀ (.VTypeDia A) (groot hF M₀))
    (h : CDefinable hM₀ hX (.VTypeDia A) (groot hF M₀) o) :
    CDefinable hM₀ hX (.VTypeDia A) s o := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | diatm y hy b =>
      obtain ⟨Y, hY⟩ := hy
      exact ⟨_, _, _, cden_named_dia hX hM₀ s i _ hY
        (pnm_ref hX.five hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i) b⟩

/-- ⭐**At a `◇` type a world defines exactly what the root defines.** -/
theorem cdefinable_dia_iff (hX : CluFlags) {A : VarType} (s : GW hF M₀)
    (o : CRDom hM₀ (.VTypeDia A) s) :
    CDefinable hM₀ hX (.VTypeDia A) s o ↔ CDefinable hM₀ hX (.VTypeDia A) (groot hF M₀) o :=
  ⟨cdefinable_dia_root hX s o, cdefinable_dia_of_root hX s o⟩

end GArrow

end V12M
