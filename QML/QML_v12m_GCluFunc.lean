import QML.QML_v12m_GCluRaw

/-!
# QML v12m — 5 on the growing tree: the cluster model's function algebra

As `GCanonFunc`'s for the growing tree, with every world's arrows the root's.

* `crawEval`: the function algebra on raw objects; `dup` and `dkeep` leave an object unchanged
  along every arrow (4's keep is the identity), `extract` is vacuous (T off).
* `shiftCorr_preI`, `shiftCorr_preIX`: a world's preimage renamings commute with 4's shift.
* `preTB_shift`, `preTB_keepDia`: so the preimage of a kept term is the kept preimage.
* ⭐`cden_applyG`: denoting an applied map is applying it to the denotation; so
  ⭐`cdefinable_rawEval`: definable objects are closed under the function algebra.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

variable (hM₀ : Theory.IsMCS M₀)

/-- ⭐**The function algebra on raw objects.**  `dup` and `dkeep` read an object along every
    arrow as itself: every world's arrows are the root's, and 4's keep is the identity. -/
noncomputable def crawEval (hX : CluFlags) :
    {A C : VarType} → GFunc σ A C → (s : GW hF M₀) → CRDom hM₀ A s → CRDom hM₀ C s
  | _, _, .id _, _, o => o
  | _, _, .comp g f, s, o => crawEval hX g s (crawEval hX f s o)
  | _, _, .fst, _, o => o.1
  | _, _, .snd, _, o => o.2
  | _, _, .pair f g, s, o => (crawEval hX f s o, crawEval hX g s o)
  | _, _, .unit _, _, _ => PUnit.unit
  | _, _, .func f args, s, o => (gw hM₀ s).canonFunc f (fun k => crawEval hX (args k) s o)
  | _, _, .boxMap f, _, o => fun a => crawEval hX f a.1 (o a)
  | _, _, .boxPair _ _, _, o => fun a => (o.1 a, o.2 a)
  | _, _, .boxUnit, _, _ => fun _ => PUnit.unit
  | _, _, .diaMap f, _, o =>
      ⟨o.E, fun a => crawEval hX f a.1.1 (o.c a),
        fun hT => .dia (o.tag hT).label (GFunc.shp f 1 (o.tag hT).body)⟩
  | _, _, .strength _ _, _, o =>
      ⟨o.2.E, fun a => (o.1 a.1, o.2.c a),
        fun hT => .dia (o.2.tag hT).label
          (.prod (Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb)
            fun a => crawShape hT (o.1 a)) (o.2.tag hT).body)⟩
  | _, _, .extract hT, s, o => o ⟨s, ⟨(carrows hF M₀).refl hT s⟩⟩
  | _, _, .dup _, _, o => fun _ => o
  | _, _, .dkeep _, _, o => fun _ => o

variable {hM₀}

/-! ## A world's preimage commutes with 4's shift -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A renaming of `□`-view items commutes with 4's shift. -/
theorem shiftCorr_preI {l L : List VarType}
    (f : VarSymb → VarSymb)
    (hθ : Subst.Ok (ctxOf l).boxIn (eS σ (ctxOf L).boxIn (ofRen (preI f)))) :
    Subst.ShiftCorr (ctxOf l).boxIn (Ctx.shifts_boxIn_boxIn hF (ctxOf L))
      (eS σ (ctxOf L).boxIn (ofRen (preI f))) (eS σ (ctxOf L).boxIn (ofRen (preI f))).box := by
  refine Subst.shiftCorr_of hθ fun v T hl hv => ?_
  match v, hl, hv with
  | .step u .box, _, hv =>
      obtain ⟨hk, -⟩ := Ctx.boxIn_box hv
      rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
      change SubE.Sim T (((eS σ (ctxOf L).boxIn (ofRen (preI f))).at (.step u .keep)).unbox)
        ((eS σ (ctxOf L).boxIn (ofRen (preI f)) (.step u .box)).shift _)
      rw [Subst.at_nonproj _ rfl, eS_item _ rfl, eS_item _ rfl]
      change SubE.Sim T (.ren (VarSymb.step (f u) .keep).inner)
        (.ren ((VarSymb.step (f u) .box).shift 0))
      rw [VarSymb.inner_box hk, VarSymb.shift_level_zero rfl]
      exact .refl _
  | .step u .keep, _, _ =>
      rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
      change SubE.Sim T (.ren (.step (.step (f u) .keep) .keep))
        (.ren ((VarSymb.step (f u) .keep).shift 0))
      rw [VarSymb.shift_level_zero rfl]
      exact .refl _
  | .root _, _, hv => cases hv
  | .step _ .fst, _, hv => cases hv
  | .step _ .snd, _, hv => cases hv
  | .step _ .dia, _, hv => cases hv
  | .step _ .here, _, hv => cases hv

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A renaming of `◇_x`-view items commutes with `four_dia`'s shift. -/
theorem shiftCorr_preIX {l L : List VarType}
    (f : VarSymb → VarSymb) {x : VarSymb}
    (hθ : Subst.Ok ((ctxOf l).diaIn x) (eS σ ((ctxOf L).diaIn (f x)) (ofRen (preIX f x)))) :
    Subst.ShiftCorr ((ctxOf l).diaIn x) (Ctx.shifts_diaIn_keep hF (ctxOf L) (f x))
      (eS σ ((ctxOf L).diaIn (f x)) (ofRen (preIX f x)))
      ((eS σ (ctxOf L).boxIn (ofRen (preI f))).dia (.step x .keep) (.step (f x) .keep)) := by
  refine Subst.shiftCorr_of hθ fun v T hl hv => ?_
  obtain ⟨u, st, rfl, -, -⟩ := kView_item (k := some x) hv
  rw [eS_item _ hl, VarSymb.shift_level_zero hl,
    Subst.at_nonproj _ (v := VarSymb.step (VarSymb.step u .keep) st) hl]
  by_cases hvx : VarSymb.step u st = .step x .dia
  · obtain ⟨rfl, rfl⟩ := VarSymb.step.inj hvx
    change SubE.Sim T (if VarSymb.step u .keep = .step u .keep then
        ((eS σ (ctxOf L).boxIn (ofRen (preI f))).at (.step u .keep)).diaBody
          (.step (f u) .keep) else .hide)
      ((SubE.ren (preIX f u (.step u .dia))).shift _)
    rw [if_pos rfl, Subst.at_nonproj _ rfl, eS_item _ rfl,
      show preIX f u (.step u .dia) = .step (f u) .dia from if_pos rfl]
    change SubE.Sim T (.ren (.step (.step (f u) .keep) .dia))
      (.ren ((VarSymb.step (f u) .dia).shift 0))
    rw [VarSymb.shift_level_zero rfl]
    exact .refl _
  · have e : preIX f x (.step u st) = preI f (.step u st) := if_neg hvx
    have hb := diaIn_boxIn_of_ne' hv hvx
    match st, hb, e with
    | .box, hb, e =>
        obtain ⟨hk, -⟩ := Ctx.boxIn_box hb
        change SubE.Sim T
          ((((eS σ (ctxOf L).boxIn (ofRen (preI f))).at (.step u .keep)).unbox).mono
            (Ctx.le_boxIn_diaIn (ctxOf L).boxIn (.step (f x) .keep)))
          ((SubE.ren (preIX f x (.step u .box))).shift _)
        rw [e, Subst.at_nonproj _ rfl, eS_item _ rfl]
        change SubE.Sim T (.ren (VarSymb.step (f u) .keep).inner)
          (.ren ((VarSymb.step (f u) .box).shift 0))
        rw [VarSymb.inner_box hk, VarSymb.shift_level_zero rfl]
        exact .refl _
    | .keep, _, e =>
        change SubE.Sim T
          ((((eS σ (ctxOf L).boxIn (ofRen (preI f))).at (.step u .keep)).keepE).mono
            (Ctx.le_boxIn_diaIn (ctxOf L).boxIn (.step (f x) .keep)))
          ((SubE.ren (preIX f x (.step u .keep))).shift _)
        rw [e, Subst.at_nonproj _ rfl, eS_item _ rfl]
        change SubE.Sim T (.ren (.step (.step (f u) .keep) .keep))
          (.ren ((VarSymb.step (f u) .keep).shift 0))
        rw [VarSymb.shift_level_zero rfl]
        exact .refl _
    | .fst, hb, _ => cases hb
    | .snd, hb, _ => cases hb
    | .dia, hb, _ => cases hb
    | .here, hb, _ => cases hb

/-- The preimage of a kept `□`-view term is the kept preimage. -/
theorem preTB_shift (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat s i)).boxIn A a) :
    (⟨_, (preTB hX hM₀ s i (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView none) (.VTypeBox A) c) =
      ⟨_, .boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (preTB hX hM₀ s i b).2)⟩ :=
  sig_boxtm (Term.shift_subst (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF _) _ _ _
    _ _ _ (shiftCorr_preI (hF := hF) _ (ok_eS_kView (k := none)
      (entOk_ofRen (itemOk_preI (rpre hX hM₀ s i))))) b).symm

/-- The preimage of a kept possible term is the kept preimage, at the kept witness's origin. -/
theorem preTB_keepDia (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {x : VarSymb} {X : VarType} (hx : (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (b : Term σ ((ctxOf (glat s i)).diaIn x) A a) :
    (⟨_, (preTB hX hM₀ s i (.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hx⟩)
        (Term.shift (Ctx.shifts_diaIn_keep hF _ x) b))).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView none) (.VTypeDia A) c) =
      ⟨_, .diatm (.step (rorig s x) .keep)
        (Ctx.exists_keep_dia hF (rorig_ref hX hM₀ s i ⟨X, hx⟩))
        (Term.shift (Ctx.shifts_diaIn_keep hF _ (rorig s x)) (preTD hX hM₀ s i ⟨X, hx⟩ b).2)⟩ := by
  have hθ := ok_eS_kView (k := none)
    (entOk_ofRen (σ := σ) (itemOk_preI (rpre hX hM₀ s i)))
  have hc := coh_eS_kView (k := none)
    (entOk_ofRen (σ := σ) (itemOk_preI (rpre hX hM₀ s i)))
  have hy : eIdx (ofRen (σ := σ) (preI (rorig s))) (.step x .keep) = .step (rorig s x) .keep := by
    rw [show (VarSymb.step x .keep) = (VarSymb.step x .keep).ext [] from rfl,
      eIdx_item _ (reach_ppath hx).1 rfl []]
    rfl
  have hw : ((eS σ (ctxOf (glat (groot hF M₀) (rstg s i))).boxIn
      (ofRen (preI (rorig s)))).at (.step x .keep)).idxAlong [] = .step (rorig s x) .keep := by
    rw [Subst.at_nonproj _ rfl, eS_item _ rfl]
    rfl
  have hxk := Ctx.exists_keep_dia hF ⟨X, hx⟩
  refine (sig_subst_diatm _ hθ hc hxk _ _ hy
    (Ctx.exists_keep_dia hF (rorig_ref hX hM₀ s i ⟨X, hx⟩)) (Subst.ok_dia hθ hxk hw)
    (hy ▸ Subst.coh_dia hθ hc hxk)).trans (sig_diatm ?_)
  exact (Term.shift_subst (Ctx.shifts_diaIn_keep hF _ x) (Ctx.shifts_diaIn_keep hF _ (rorig s x))
    _ _ _ _ _ _ (shiftCorr_preIX (hF := hF) _ (ok_eS_kView (k := some x)
      (entOk_ofRen (itemOk_rpreX hX hM₀ s i ⟨X, hx⟩)))) b).symm

/-! ## Denoting an applied map -/

theorem preTB_sigma (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {A : VarType} {a a' : Ann A} {x : Term σ (ctxOf (glat s i)).boxIn A a}
    {y : Term σ (ctxOf (glat s i)).boxIn A a'}
    (h : (⟨a, x⟩ : Σ c, Term σ (ctxOf (glat s i)).boxIn A c) = ⟨a', y⟩) :
    (⟨_, (preTB hX hM₀ s i x).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView none) A c) =
      ⟨_, (preTB hX hM₀ s i y).2⟩ := by
  cases h
  rfl

theorem cden_varTerm (hX : CluFlags) {Γ : Ctx} (s : GW hF M₀) (i : ℕ)
    (e : Γ.Le (ctxOf (glat s i))) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b),
      cden hM₀ hX s i e (Canon.varTerm p) = cden hM₀ hX s i e p.2
  | ⟨.var, _⟩ => rfl

theorem cden_var_mono (hX : CluFlags) {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) :
    ∀ u : Term σ Γ .Var .var, cden hM₀ hX s i e u = (gw hM₀ s).cls i (Term.mono e u)
  | .var _ _ => rfl
  | .func _ => rfl

/-- A world's preimage commutes with applying a map, at a `□` view. -/
theorem preTB_applyG (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {A C : VarType}
    (g : GFunc σ A C) {Γ : Ctx} {s : GW hF M₀} {i : ℕ} (e : Γ.Le (ctxOf (glat s i)))
    {a : Ann A} (b : Term σ Γ.boxIn A a) :
    (⟨_, (preTB hX hM₀ s i (Term.mono e.boxIn (Canon.applyG g b).2)).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView none) C c) =
      Canon.applyG g (preTB hX hM₀ s i (Term.mono e.boxIn b)).2 := by
  refine Eq.symm ?_
  simp only [preTB]
  rw [Canon.applyG_subst, Canon.applyG_mono]

/-- A world's preimage commutes with applying a map, at a `◇_x` view. -/
theorem preTD_applyG (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {A C : VarType}
    (g : GFunc σ A C) {Γ : Ctx} {s : GW hF M₀} {i : ℕ} (e : Γ.Le (ctxOf (glat s i)))
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {a : Ann A} (b : Term σ (Γ.diaIn x) A a) :
    (⟨_, (preTD hX hM₀ s i hx (Term.mono (e.diaIn x) (Canon.applyG g b).2)).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView (some (rorig s x))) C c) =
      Canon.applyG g (preTD hX hM₀ s i hx (Term.mono (e.diaIn x) b)).2 := by
  refine Eq.symm ?_
  simp only [preTD]
  rw [Canon.applyG_subst, Canon.applyG_mono]

/-- A world's preimage of a necessary term weakened into a `◇_x` view is its `□`-view preimage,
    weakened. -/
theorem preTD_box (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) {Γ : Ctx} {s : GW hF M₀} {i : ℕ}
    (e : Γ.Le (ctxOf (glat s i))) {x : VarSymb}
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (b : Term σ Γ.boxIn A a) :
    (⟨_, (preTD hX hM₀ s i hx (Term.mono (e.diaIn x) (Term.mono (Ctx.le_boxIn_diaIn Γ x) b))).2⟩ :
        Σ c, Term σ ((ctxOf (glat (groot hF M₀) (rstg s i))).kView (some (rorig s x))) A c) =
      ⟨_, Term.mono (Ctx.le_boxIn_diaIn _ (rorig s x))
        (preTB hX hM₀ s i (Term.mono e.boxIn b)).2⟩ := by
  simp only [preTD, preTB]
  rw [Term.mono_mono, Term.mono_subst, Term.subst_mono, Term.subst_mono]
  refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v T hl hv => ?_) b
  match v, hl with
  | .root _, _ => exact .refl _
  | .step u st, hl =>
      change SubE.Sim T (eS σ _ (ofRen (preIX (rorig s) x)) (.step u st))
        (SubE.mono _ (eS σ _ (ofRen (preI (rorig s))) (.step u st)))
      rw [eS_item _ hl, eS_item _ hl]
      change SubE.Sim T (.ren (preIX (rorig s) x (.step u st))) (.ren (preI (rorig s) (.step u st)))
      have hst : st ≠ .dia := by
        rintro rfl
        cases hv
      rw [show preIX (rorig s) x (.step u st) = preI (rorig s) (.step u st) from
        if_neg fun h => hst (VarSymb.step.inj h).2]
      exact .refl _

/-- ⭐The realised content of a term of the `□` view is what the term denotes here: realisation
    collapses it (`grden_grealT_mono_boxIn`). -/
theorem cden_grealT_mono_boxIn (hX : CluFlags) {t : GW hF M₀} {y : VarSymb}
    (hr : (gw hM₀ t).Realised y) {j : ℕ}
    (hy : ∃ Y, (ctxOf (glat t j)).ref y = some (.VTypeDia Y)) {A : VarType} {a : Ann A}
    (b : Term σ (ctxOf (glat t j)).boxIn A a) :
    cden hM₀ hX t _ (Ctx.Le.refl _)
        (grealT hr (Ctx.Le.refl _) hy (Term.mono (Ctx.le_boxIn_diaIn _ y) b)).2 =
      cden hM₀ hX t j (Ctx.Le.refl _) (Term.collapse (Ctx.collapses_boxIn_self hr.T _) b) := by
  have hle : (ctxOf (glat t j)).boxIn.Le (ctxOf (glat t (max j hr.data.i₀))).boxIn :=
    (gle hM₀ t (le_max_left _ _)).boxIn
  have hcomb : Term.mono (((Ctx.Le.refl _).trans (gle hM₀ t (le_max_left _ _))).diaIn y)
      (Term.mono (Ctx.le_boxIn_diaIn _ y) b) =
      Term.mono (Ctx.le_boxIn_diaIn (ctxOf (glat t (max j hr.data.i₀))) y) (Term.mono hle b) := by
    rw [Term.mono_mono, Term.mono_mono]
  simp only [grealT]
  rw [hcomb, cden_sigma hX _ (Term.realiseAtA_mono_boxIn hr.data.hT y _ _ (Term.mono hle b)),
    Term.collapse_mono (Ctx.collapses_boxIn_self hr.T _)
      (Ctx.collapses_boxIn_self hr.data.hT _) hle (gle hM₀ t (le_max_left _ _)) b,
    cden_mono]
  exact cden_congr hX _ _ _ _ _ _

/-- ⭐**Denoting a map applied to a term is applying the map to the denotation.**  As
    `grden_applyG`, a world's preimage commuting with each operation; `dup` and `dkeep` are the
    path translation's round trip (`cden_tr`, `cden_trX`). -/
theorem cden_applyG (hX : CluFlags) :
    ∀ {A C : VarType} (g : GFunc σ A C) {Γ : Ctx} {a : Ann A} (t : Term σ Γ A a)
      (s : GW hF M₀) (i : ℕ) (e : Γ.Le (ctxOf (glat s i))),
    cden hM₀ hX s i e (Canon.applyG g t).2 = crawEval hM₀ hX g s (cden hM₀ hX s i e t)
  | _, _, .id _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, t, s, i, e =>
      (cden_applyG hX g _ s i e).trans
        (congrArg (crawEval hM₀ hX g s) (cden_applyG hX f t s i e))
  | _, _, .fst, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .snd, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .pair f g, _, _, t, s, i, e =>
      Prod.ext (cden_applyG hX f t s i e) (cden_applyG hX g t s i e)
  | _, _, .unit _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, t, s, i, e => by
      change cden hM₀ hX s i e (.func _) =
        (gw hM₀ s).canonFunc f (fun k => crawEval hM₀ hX (args k) s (cden hM₀ hX s i e t))
      have hk : (fun k => crawEval hM₀ hX (args k) s (cden hM₀ hX s i e t)) =
          fun k => (gw hM₀ s).cls i (Term.mono e (Canon.varTerm (Canon.applyG (args k) t))) := by
        funext k
        rw [← cden_applyG hX (args k) t s i e, ← cden_varTerm, cden_var_mono]
      rw [hk, BWorld.canonFunc_cls, cden_var_mono, Term.mono_fill, Spine.mono_ofFn]
      rfl
  | _, _, .boxMap f, _, _, .boxtm b, s, i, e => funext fun a => by
      change cden hM₀ hX s i e (.boxtm (Canon.applyG f b).2) a =
        crawEval hM₀ hX f a.1 (cden hM₀ hX s i e (.boxtm b) a)
      simp only [cden]
      refine (cden_sigma hX _ ((pTr_sigma hM₀ _ _ _ _ _ _ (preTB_applyG hX hM₀ f e b)).trans
        (pTr_applyG f _ _ _ _ _ _ _))).trans ?_
      exact cden_applyG hX f _ a.1 _ (Ctx.Le.refl _)
  | _, _, .boxPair _ _, _, _, .pair (.boxtm b) (.boxtm c), s, i, e => funext fun a => by
      change cden hM₀ hX s i e (.boxtm (.pair b c)) a =
        (cden hM₀ hX s i e (.boxtm b) a, cden hM₀ hX s i e (.boxtm c) a)
      simp only [cden]
      exact cden_sigma hX _ (pTr_pair _ _ _ _ _ _ _ _)
  | _, _, .boxUnit, _, _, .unit, _, _, _ => funext fun _ => rfl
  | _, _, .diaMap f, _, _, .diatm x hx c, s, i, e => by
      change cden hM₀ hX s i e (.diatm x hx (Canon.applyG f c).2) =
        crawEval hM₀ hX (.diaMap f) s (cden hM₀ hX s i e (.diatm x hx c))
      simp only [cden, crawEval]
      refine CRPos.congr_cont (funext fun a => ?_) fun hT => ?_
      · by_cases hr : (gw hM₀ a.1.1).Realised
            (kw (groot hF M₀) a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) (rorig s x))
        · simp only [dif_pos hr]
          refine (cden_sigma hX _ ((grealT_sigma hr _ _ ((pTrXK_sigma hM₀ _ _ _ _ _ _ _
            (preTD_applyG hX hM₀ f e _ c)).trans (pTrXK_applyG f _ _ _ _ _ _ _ _))).trans
            (grealT_applyG f hr _ _ _))).trans ?_
          exact cden_applyG hX f _ a.1.1 _ (Ctx.Le.refl _)
        · simp only [dif_neg hr]
          refine (cden_sigma hX _ ((pTrX_sigma hM₀ _ _ _ _ _ _ _ _
            (preTD_applyG hX hM₀ f e _ c)).trans (pTrX_applyG f _ _ _ _ _ _ _ _ _))).trans ?_
          exact cden_applyG hX f _ a.1.1 _ (Ctx.Le.refl _)
      · have e₁ := congrArg Sigma.fst (preTD_applyG hX hM₀ f e (hx.imp fun _ h => e.ref h) c)
        exact (congrArg (fun c' => annC (groot hF M₀) (Ann.dia (rorig s x) c')) e₁).trans
          (annC_applyG hX.five hX.fourS hX.fourSW hM₀ hT (.diaMap f)
            (.diatm (rorig s x) (rorig_ref hX hM₀ s i (hx.imp fun _ h => e.ref h))
              (preTD hX hM₀ s i (hx.imp fun _ h => e.ref h) (Term.mono (e.diaIn x) c)).2))
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c), s, i, e => by
      change cden hM₀ hX s i e (.diatm x hx (.pair (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) c)) =
        crawEval hM₀ hX (.strength _ _) s (cden hM₀ hX s i e (.pair (.boxtm b) (.diatm x hx c)))
      simp only [cden, crawEval]
      refine CRPos.congr_cont (funext fun a => ?_) fun hT => ?_
      · by_cases hr : (gw hM₀ a.1.1).Realised
            (kw (groot hF M₀) a.1.1 (pathOf a.1.2.down) (pathOf_eq a.1.2.down) (rorig s x))
        · simp only [dif_pos hr]
          refine (cden_sigma hX _ (grealT_sigma hr _ _ (pTrXK_pair _ _ _ _ _ _ _ _ _))).trans
            (Prod.ext ?_ rfl)
          have hk := kw_decl hM₀ (groot hF M₀) a.1.1 _ (pathOf_eq a.1.2.down) (rstg s i)
            (rorig_ref hX hM₀ s i (hx.imp fun _ h => e.ref h))
          refine (cden_sigma hX (Ctx.Le.refl _) (grealT_sigma hr (Ctx.Le.refl _) hk
            ((pTrXK_sigma hM₀ _ _ _ _ _ _ _
              (preTD_box hX hM₀ e (hx.imp fun _ h => e.ref h) b)).trans
            (pTrXK_box _ _ _ _ _ _ _ _)))).trans ?_
          refine (cden_grealT_mono_boxIn hX hr hk _).trans ?_
          exact cden_sigma hX _ (collapse_pTrK hr.T _ _ _ _ (pathOf_ok a.1.2.down) _ _)
        · simp only [dif_neg hr]
          refine (cden_sigma hX _ (pTrX_pair _ _ _ _ _ _ _ _ _ _)).trans (Prod.ext ?_ rfl)
          exact cden_sigma hX _ ((pTrX_sigma hM₀ _ _ _ _ _ _ _ _
            (preTD_box hX hM₀ e (hx.imp fun _ h => e.ref h) b)).trans
              (pTrX_box _ _ _ _ (pathOf_ok a.1.2.down) _ _ _ _ _))
      · have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
        obtain ⟨X, hr⟩ := id hx
        have key := crawShape_box_transpose hX hM₀ hT s (groot hF M₀) i e b
        have e₂ := mapIdx_eIdx_preIX hko s e hr (Term.mono (Ctx.le_boxIn_diaIn Γ x) b)
        exact (congrArg (fun z => (Shp.dia (cLab (rorig s x) (groot hF M₀))
          (Shp.prod (annC (groot hF M₀) z) (annC (groot hF M₀)
            (preTD hX hM₀ s i (hx.imp fun _ h => e.ref h) (Term.mono (e.diaIn x) c)).1)) :
            CShape hF M₀ (groot hF M₀) _)) e₂).trans
          (congrArg (fun z => (Shp.dia (cLab (rorig s x) (groot hF M₀)) (Shp.prod z (annC
            (groot hF M₀)
            (preTD hX hM₀ s i (hx.imp fun _ h => e.ref h) (Term.mono (e.diaIn x) c)).1)) :
            CShape hF M₀ (groot hF M₀) _)) key.symm)
  | _, _, .extract hT, Γ, _, .boxtm b, s, i, e => by
      change cden hM₀ hX s i e (Term.collapse (Ctx.collapses_boxIn_self hT Γ) b) =
        cden hM₀ hX s i e (.boxtm b) ⟨s, ⟨(carrows hF M₀).refl hT s⟩⟩
      simp only [cden]
      rw [cden_collapse hX hM₀ hT s i, Term.collapse_mono (Ctx.collapses_boxIn_self hT Γ)
        (Ctx.collapses_boxIn_self hT _) e.boxIn e, cden_mono]
  | _, _, .dup _, Γ, _, .boxtm b, s, i, e => funext fun v => funext fun u => by
      have hm : (⟨_, Term.mono e.boxIn (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))⟩ :
          Σ c, Term σ (ctxOf (glat s i)).boxIn _ c) =
          ⟨_, Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) (Term.mono e.boxIn b))⟩ := by
        change (⟨_, Term.boxtm (Term.mono e.boxIn.boxIn
          (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))⟩ : Σ c, Term σ _ _ c) = _
        rw [← Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.shifts_boxIn_boxIn hF _)
          e.boxIn e.boxIn.boxIn b]
      have key : cden hM₀ hX s i e
          (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) v =
          cden hM₀ hX (groot hF M₀) (rstg s i) (Ctx.Le.refl _)
            (.boxtm (preTB hX hM₀ s i (Term.mono e.boxIn b)).2) :=
        (cden_sigma hX _ (pTr_sigma hM₀ _ _ _ _ _ _ ((preTB_sigma hX hM₀ s i hm).trans
          (preTB_shift hX hM₀ s i _)))).trans (cden_tr hX hM₀ v.1 _ _ _ _ _)
      change cden hM₀ hX s i e (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)))
        v u = cden hM₀ hX s i e (.boxtm b) u
      rw [key, cden_box_eq hX s i e b]
  | _, _, .dkeep _, Γ, _, .diatm x hx c, s, i, e => funext fun v => by
      obtain ⟨X, hX'⟩ := hx
      have hxs := e.ref hX'
      have hm : (⟨_, Term.mono e.boxIn (Term.diatm (.step x .keep)
          (Ctx.exists_keep_dia hF ⟨X, hX'⟩) (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) c))⟩ :
          Σ e', Term σ (ctxOf (glat s i)).boxIn _ e') =
          ⟨_, Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF ⟨X, hxs⟩)
            (Term.shift (Ctx.shifts_diaIn_keep hF _ x) (Term.mono (e.diaIn x) c))⟩ := by
        change (⟨_, Term.diatm (.step x .keep) _ (Term.mono (e.boxIn.diaIn (.step x .keep))
          (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) c))⟩ : Σ e', Term σ _ _ e') = _
        rw [← Term.shift_mono (Ctx.shifts_diaIn_keep hF Γ x) (Ctx.shifts_diaIn_keep hF _ x)
          (e.diaIn x) (e.boxIn.diaIn (.step x .keep)) c]
      have key : cden hM₀ hX s i e (.boxtm (.diatm (.step x .keep)
          (Ctx.exists_keep_dia hF ⟨X, hX'⟩) (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) c))) v =
          cden hM₀ hX (groot hF M₀) (rstg s i) (Ctx.Le.refl _)
            (.diatm (rorig s x) ⟨X, rpre hX hM₀ s i x _ hxs rfl⟩
              (preTD hX hM₀ s i ⟨X, hxs⟩ (Term.mono (e.diaIn x) c)).2) :=
        (cden_sigma hX _ (pTr_sigma hM₀ _ _ _ _ _ _ ((preTB_sigma hX hM₀ s i hm).trans
          (preTB_keepDia hX hM₀ s i hxs _)))).trans
          (cden_trX hX hM₀ v.1 _ _ _ _ (rpre hX hM₀ s i x _ hxs rfl) _)
      change cden hM₀ hX s i e (.boxtm (.diatm (.step x .keep)
          (Ctx.exists_keep_dia hF ⟨X, hX'⟩) (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) c))) v =
        cden hM₀ hX s i e (.diatm x ⟨X, hX'⟩ c)
      rw [key, cden_dia_eq hX s i e x ⟨X, hX'⟩ c]

/-- ⭐**Definable objects are closed under the function algebra.** -/
theorem cdefinable_rawEval (hX : CluFlags) {A C : VarType} (g : GFunc σ A C) {s : GW hF M₀}
    {o : CRDom hM₀ A s} (h : CDefinable hM₀ hX A s o) :
    CDefinable hM₀ hX C s (crawEval hM₀ hX g s o) := by
  obtain ⟨i, a, t, rfl⟩ := h
  exact ⟨i, _, (Canon.applyG g t).2, cden_applyG hX g t s i _⟩

end GArrow

end V12M
