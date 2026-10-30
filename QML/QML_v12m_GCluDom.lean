import QML.QML_v12m_GCluOrig

/-!
# QML v12m — 5 on the growing tree: the cluster model's raw objects and denotations

The K45 cluster model (`docs/v12-modal-extensions.md` §3 5, "The K45 cluster model: design pass
against the code").  Without T every non-root world is a strict descendant of the root `ρ`
(`groot`), so every world's arrows are the root's (`CAcc := GAcc ρ`), and modal raw objects do
not depend on the world.

* `CluFlags`: 5 and both lifts on, T off.
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
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- The flags of the K45 cluster model: 5 and both lifts on, T off. -/
structure CluFlags : Prop where
  five : ModalSys.Five = true
  noT : ModalSys.T = false
  fourS : ModalSys.FourStrong = true
  fourSW : ModalSys.FourStrongW = true

theorem CluFlags.keepOnly (hX : CluFlags) : ModalSys.keepOnly = false := by
  simp [ModalSys.keepOnly, hX.noT]

/-! ## Paths from the root -/

/-- A world's path from the root. -/
def rpath (s : GW hF M₀) : List ℕ := s.1.reverse

theorem rpath_eq (s : GW hF M₀) : s.1 = nodeOf (groot hF M₀).1 (rpath s) := by
  rw [nodeOf_eq]
  simp [rpath, groot]

/-- The root's stage at which a world's stage has its preimage. -/
noncomputable abbrev rstg (s : GW hF M₀) (i : ℕ) : ℕ :=
  pstgO (rpath s) (groot hF M₀) s (rpath_eq s) i

/-- A world's origins at the root. -/
noncomputable abbrev rorig (s : GW hF M₀) : VarSymb → VarSymb :=
  porig (rpath s) (groot hF M₀) s (rpath_eq s)

theorem rpre (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ) :
    PPreOk (rpath s) (groot hF M₀) s (rpath_eq s) i :=
  pPreOk hX.five hX.noT hX.fourS hX.fourSW hM₀ (rpath s) (groot hF M₀) s (rpath_eq s) i

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
    (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly (rpre hX hM₀ s i))))
    (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly (rpre hX hM₀ s i)))) b⟩

theorem itemOk_rpreX (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) :
    ItemOk ((ctxOf (glat s i)).diaIn x) ((ctxOf (glat (groot hF M₀) (rstg s i))).diaIn (rorig s x))
      (preIX (rorig s) x) := by
  obtain ⟨X, hX'⟩ := hx
  exact itemOk_preIX hX.keepOnly hX' (rpre hX hM₀ s i)

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
  exact itemOk_preIX hX.keepOnly hX' (rpre_le hX hM₀ s hR)

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
                  ((ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly
                    (rpre_le hX hM₀ s (le_max_left _ _))))).restrict e.boxIn)
                  ((coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly
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
          (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hX.keepOnly (rpre_le hX hM₀ s hk))))
          _ (coh_eS_kView (k := none)
            (entOk_ofRen (itemOk_preI hX.keepOnly (rpre_le hX hM₀ s hk))))
          (sim_eS_mono (l := glat s k) (k := none) _
            (entOk_ofRen (itemOk_preI hX.keepOnly (rpre hX hM₀ s k)))) _).trans ?_
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

end GArrow

end V12M
