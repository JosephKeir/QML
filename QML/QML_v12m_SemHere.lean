import QML.QML_v12m_SemStrongT

/-!
# QML v12m — the realisation predicate, and the soundness of its rules

`WFF.here hT s t` says that the possible object denoted by the `◇`-term `s` is realised at this
world, with value `t` (`Model.Realised`).  Its rules (`Proof.here_elim`, `Proof.here_intro`) state
it in the **pinned** form `WFF.hereAt hT x hx t`, whose subject is the η-expansion of an address.
So soundness needs two things:

* ⭐`Model.interp_eta`: the **η-law** — an address's η-expansion denotes the address.  Every case is
  a coherence already in the model: projections by `Model.stepObj`, `□` by `nec_inj` and
  `Env.ref_inner`, `◇` by `pos_inj` and `Model.dia_beta`.
* ⭐`Model.sat_hereAt`: so `WFF.hereAt` says exactly what the probe called `HereData` — the identity
  arrow lies in the address's extent, and its content there is `t`.

The rules themselves are then `Model.sat_realiseAt` read in the two directions:

* ⭐`Model.sat_here_elim`: `Here x t, □_x χ ⊢ χ(t)`;
* ⭐`Model.sat_here_intro`: `Here x t, χ(t) ⊢ ◇_x χ`.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-! ## Environments read projections -/

theorem Env.ref_fst {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {u : VarSymb} {A B : VarType}
    (hu : Γ.ref u = some (.VTypeProd A B)) (h : Γ.ref (.step u .fst) = some A) :
    env.ref (.step u .fst) h = (env.ref u hu).1 := by
  have hhs : Step.fst.isProj = true := rfl
  rw [Env.ref, dif_pos hhs]
  split
  · rename_i U hU
    have hUU : U = .VTypeProd A B := Option.some.inj (hU.symm.trans hu)
    subst hUU
    rfl
  · rename_i hU
    exact absurd (hU.symm.trans hu) (by simp)

theorem Env.ref_snd {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {u : VarSymb} {A B : VarType}
    (hu : Γ.ref u = some (.VTypeProd A B)) (h : Γ.ref (.step u .snd) = some B) :
    env.ref (.step u .snd) h = (env.ref u hu).2 := by
  have hhs : Step.snd.isProj = true := rfl
  rw [Env.ref, dif_pos hhs]
  split
  · rename_i U hU
    have hUU : U = .VTypeProd A B := Option.some.inj (hU.symm.trans hu)
    subst hUU
    rfl
  · rename_i hU
    exact absurd (hU.symm.trans hu) (by simp)

/-- Pushed into `◇_x`, the content address of `x` holds `x`'s content at the world pushed to. -/
theorem Env.ref_dia {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x hx)).1)
    (h : (Γ.diaIn x).ref (.step x .dia) = some X) :
    (env.diaPush x hx w').ref (.step x .dia) h = (M.posEval (env.ref x hx)).2 w' := by
  rw [Env.ref, dif_neg (by decide : ¬ Step.dia.isProj = true)]
  rfl

/-! ## The η-law for shapes -/

/-- Reading a necessary address's contents one view in gives the contents of its shape.  Under T+4
    the contents are `u.keep.here`, a shift followed by a collapse one level further in, and this
    is the second counit (`Frame.Leaf.collapse_shift_succ`). -/
theorem ShEnv.ref_inner {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (j : ℕ) {u : VarSymb}
    {A : VarType} (h : Γ.ref u = some (.VTypeBox A)) :
    (ρ.boxPush j).ref (j + 1) u.inner (Ctx.ref_inner h) = (ρ.ref j u h).inner := by
  by_cases hk : ModalSys.keepOnly = true
  · obtain ⟨hT, hF⟩ := ModalSys.keepOnly_flags hk
    have hkr : Γ.boxIn.ref (.step u .keep) = some (.VTypeBox A) := Ctx.ref_keep_of hF h
    have hh : Γ.boxIn.ref (.step (.step u .keep) .here) = some A := by
      rw [← VarSymb.inner_keepOnly hk]
      exact Ctx.ref_inner h
    rw [ShEnv.ref_congr _ _ (VarSymb.inner_keepOnly hk) _ hh,
      ShEnv.ref_proj _ _ (rfl : Step.here.isProj = true) hkr,
      ShEnv.ref_nonproj _ _ (by decide : ¬ Step.keep.isProj = true)]
    change ((ρ.ref j u h).inner.map (Frame.Leaf.shift hF j)).map
      (Frame.Leaf.collapse hT (j + 1)) = _
    rw [Shp.map_map]
    exact (Shp.map_congr (g := Frame.Leaf.collapse hT (j + 1) ∘ Frame.Leaf.shift hF j)
      (g' := id) (fun ℓ => Frame.Leaf.collapse_shift_succ hT hF j ℓ) _).trans (Shp.map_id _)
  · have hk' : ModalSys.keepOnly = false := by simpa using hk
    rw [ShEnv.ref_congr _ _ (VarSymb.inner_box hk') _ (Ctx.ref_boxIn_of hk' h),
      ShEnv.ref_nonproj _ _ (by decide : ¬ Step.box.isProj = true)]
    rfl

/-- ⭐**η for shapes**: an address's η-expansion has the address's shape. -/
theorem termShp_eta :
    ∀ {Γ : Ctx} {w : M.frame.W} (ρ : M.ShEnv Γ w) (j : ℕ) {T : VarType} (x : VarSymb)
      (h : Γ.ref x = some T), termShp ρ j (Term.eta (σ := σ) x T h) = ρ.ref j x h
  | _, _, _, _, .Var, _, _ => shp_var_eq _ _
  | _, _, _, _, .VTypeOne, _, _ => Shp.one_eq _ _
  | _, _, ρ, j, .VTypeProd A B, x, h => by
      change Shp.prod (termShp ρ j (Term.eta (.step x .fst) A (Ctx.ref_fst_of h)))
        (termShp ρ j (Term.eta (.step x .snd) B (Ctx.ref_snd_of h))) = _
      rw [termShp_eta ρ j (.step x .fst), termShp_eta ρ j (.step x .snd),
        ShEnv.ref_proj ρ j rfl h, ShEnv.ref_proj ρ j rfl h]
      exact (Shp.prod_eta _).symm
  | _, _, ρ, j, .VTypeBox A, x, h => by
      change Shp.box (termShp (ρ.boxPush j) (j + 1) (Term.eta x.inner A (Ctx.ref_inner h))) = _
      rw [termShp_eta (ρ.boxPush j) (j + 1) x.inner, ShEnv.ref_inner ρ j h]
      exact (Shp.box_eta _).symm
  | _, _, ρ, j, .VTypeDia A, x, h => by
      change termShp ρ j (Term.diatm x ⟨A, h⟩ (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of h))) = _
      rw [termShp_diatm ρ j h, termShp_eta (ρ.diaPush j x h) (j + 1) (.step x .dia),
        ShEnv.ref_nonproj _ _ (by decide : ¬ Step.dia.isProj = true)]
      exact (Shp.dia_eta _).symm

/-! ## The η-law -/

/-- ⭐**η for environments**: an address's η-expansion denotes the address.  At `𝟙` the domain is a
    single point; at a product the components are the projections; at `□` and `◇` the carriers are
    extensional, so it suffices that the sections agree, which is what `Env.ref_inner` and
    `Env.ref_dia` say. -/
theorem interp_eta {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    ∀ {T : VarType} (x : VarSymb) (h : Γ.ref x = some T),
      interp env (Term.eta x T h) = env.ref x h
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A B, x, h => by
      change (interp env (Term.eta (.step x .fst) A (Ctx.ref_fst_of h)),
        interp env (Term.eta (.step x .snd) B (Ctx.ref_snd_of h))) = _
      rw [interp_eta env (.step x .fst) (Ctx.ref_fst_of h),
        interp_eta env (.step x .snd) (Ctx.ref_snd_of h),
        Env.ref_fst env h (Ctx.ref_fst_of h), Env.ref_snd env h (Ctx.ref_snd_of h)]
      rfl
  | .VTypeBox A, x, h => by
      change interp env (Term.boxtm (Term.eta x.inner A (Ctx.ref_inner h))) = _
      refine M.nec_inj (funext fun w' => ?_)
      rw [box_beta env (Term.eta x.inner A (Ctx.ref_inner h)) w',
        interp_eta (env.boxPush w') x.inner (Ctx.ref_inner h), Env.ref_inner env w' h]
  | .VTypeDia A, x, h => by
      change interp env (Term.diatm x ⟨A, h⟩ (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of h))) = _
      refine M.pos_inj ?_ fun hT => ?_
      swap
      · change domSh hT (interp env (Term.eta x (.VTypeDia A) h)) = domSh hT (env.ref x h)
        rw [domSh_interp, ← ref_envShape]
        exact termShp_eta _ 0 x h
      rw [dia_beta env ⟨A, h⟩ h (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of h))]
      refine Sigma.ext rfl (heq_of_eq (funext fun w' => ?_))
      dsimp only
      rw [interp_eta (env.diaPush x h w') (.step x .dia) (Ctx.ref_diaIn_of h),
        Env.ref_dia env h w' (Ctx.ref_diaIn_of h)]

/-! ## What the pinned form says -/

section

variable (hT : ModalSys.T = true) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
  (hnp : Γ.NoProjLast) {x : VarSymb} {X : VarType}

omit [Γ.NoSlots] in
/-- ⭐The pinned form says that the identity arrow lies in the address's extent, and that the
    content there is `t`. -/
theorem sat_hereAt {A : VarType} (hx : Γ.ref x = some (.VTypeDia A))
    {a : Ann A}
    (t : Term σ Γ A a) :
    M.sat env (WFF.hereAt hT x hx t : WFF σ Γ 0) ↔
      ∃ hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hx)).1,
        (M.posEval (env.ref x hx)).2 ⟨M.frame.reflAcc hT w, hm⟩ = interp env t := by
  change Realised hT (interp env (Term.eta x (.VTypeDia A) hx)) (interp env t) ↔ _
  rw [interp_eta env x hx]
  exact Iff.rfl

omit [Γ.NoSlots] in
/-- ⭐What the general form says: the identity arrow lies in the witness's extent, and the body's
    value there is `t`.  By `Model.dia_beta`, a `◇`-term has its witness's extent. -/
theorem sat_here_diatm (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    (h : Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a)
    {a₁ : Ann A} (bd : Term σ (Γ.diaIn x) A a₁) :
    M.sat env (WFF.here hT (Term.diatm x hx bd) t : WFF σ Γ 0) ↔
      ∃ hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x h)).1,
        interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hm⟩) bd = interp env t := by
  change Realised hT (interp env (Term.diatm x hx bd)) (interp env t) ↔ _
  unfold Realised
  rw [dia_beta env hx h bd]

omit [Γ.NoSlots] in
/-- ⭐**Functionality** is sound at **every content type**: a possible object has one realisation
    here, because `Realised` reads its content at one arrow.  The two values carry unrelated
    annotations, so the conclusion is the annotation-free `eqRec` of §2d — which is what let the
    predicate stop being base-typed. -/
theorem sat_here_fun {A : VarType} {b : Ann (.VTypeDia A)}
    (s : Term σ Γ (.VTypeDia A) b)
    {a : Ann A} (t t' : Term σ Γ A a)
    (h : M.sat env (WFF.here hT s t : WFF σ Γ 0))
    (h' : M.sat env (WFF.here hT s t' : WFF σ Γ 0)) :
    M.sat env (eqRec A t t' : WFF σ Γ 0) := by
  obtain ⟨_, hc⟩ := h
  obtain ⟨_, hc'⟩ := h'
  exact (sat_eqRec env A t t').mpr (hc.symm.trans hc')

/-- ⭐**A realised witness has a content, semantically**: a `Pos`-object's content function is total
    on its extent, so once the reflexive arrow lies there — which is what the `𝟙`-atom says,
    `Dom 𝟙 w` being a single point — the object's content at that arrow is an element of the
    domain, and that element is the existential's witness.  No condition on the type: this is the
    totality half of the pair whose other half, surjectivity, is `Model.posRet_exists` and
    `Proof.T_dia` (§10.15). -/
theorem sat_here_name (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    (h : Γ.ref x = some (.VTypeDia X)) {B : VarType} {β : Ann B} (bd : Term σ (Γ.diaIn x) B β)
    (hunit : M.sat env (WFF.here hT (Term.diatm x hx Term.unit) Term.unit : WFF σ Γ 0)) :
    M.sat env (WFF.hereEx hT (Term.diatm x hx bd)) := by
  obtain ⟨hm, -⟩ := (sat_here_diatm hT env hx h Term.unit Term.unit).mp hunit
  have hm' : M.frame.reflAcc hT w ∈ (M.posEval (interp env (Term.diatm x hx bd))).1 := by
    rw [dia_beta env hx h bd]
    exact hm
  have hr : Γ.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)
  refine ⟨(M.posEval (interp env (Term.diatm x hx bd))).2 ⟨M.frame.reflAcc hT w, hm'⟩, ?_⟩
  have hag : Env.Agree (Ctx.le_insert hr.root B) env
      (env.extend (.bnd 0) ((M.posEval (interp env (Term.diatm x hx bd))).2
        ⟨M.frame.reflAcc hT w, hm'⟩)) := by
    intro v U hv
    have hne : v ≠ .root (.bnd 0) := fun hvr => by rw [hvr, hr.root] at hv; cases hv
    simp only [Env.extend, dif_neg hne]
  have hslot : (env.extend (.bnd 0)
        ((M.posEval (interp env (Term.diatm x hx bd))).2 ⟨M.frame.reflAcc hT w, hm'⟩)).ref
        (.root (.bnd 0)) (Ctx.ref_insert_root Γ (.bnd 0) B) =
      (M.posEval (interp env (Term.diatm x hx bd))).2 ⟨M.frame.reflAcc hT w, hm'⟩ :=
    Env.extend_root env (.bnd 0) _ (Ctx.ref_insert_root Γ (.bnd 0) B)
  change Realised hT (interp _ (Term.mono _ (Term.diatm x hx bd))) (interp _ (Term.eta _ _ _))
  rw [interp_mono hag (Term.diatm x hx bd),
    interp_eta _ (.root (.bnd 0)) (Ctx.ref_insert_root Γ (.bnd 0) B), hslot]
  exact ⟨hm', rfl⟩

include hnp in
/-- ⭐**Functionality, substitutionally, is sound at every content type**: `Realised` reads a
    possible object's content at one arrow, so two candidates for it are the same object, and
    substituting one for the other in any formula preserves truth (`Model.sat_instantiate` twice).
    This is what makes `Proof.here_subst` sound where no equation is available — the annotations
    need not agree, since the two instances are simply two formulas (§10.11). -/
theorem sat_here_subst {A : VarType} {b : Ann (.VTypeDia A)} (s : Term σ Γ (.VTypeDia A) b)
    {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
    (φ : WFF σ (Γ.insert (.bnd 0) A) 1)
    (h : M.sat env (WFF.here hT s t : WFF σ Γ 0))
    (h' : M.sat env (WFF.here hT s t' : WFF σ Γ 0))
    (hφ : M.sat env (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    M.sat env (WFF.instantiate Ctx.NoSlots.slots t' φ) := by
  obtain ⟨_, hc⟩ := h
  obtain ⟨_, hc'⟩ := h'
  refine (sat_instantiate env hnp Ctx.NoSlots.slots t' φ).mpr ?_
  rw [← hc.symm.trans hc']
  exact (sat_instantiate env hnp Ctx.NoSlots.slots t φ).mp hφ

omit [Γ.NoSlots] in
/-- ⭐**Leibniz for the content is sound**: the defined equality holds exactly when the two contents
    denote one object (`sat_eqRec`), and `Realised` reads the content as an object. -/
theorem sat_here_eq {A : VarType} {b : Ann (.VTypeDia A)} (s : Term σ Γ (.VTypeDia A) b)
    {a : Ann A} (t t' : Term σ Γ A a)
    (h : M.sat env (WFF.here hT s t : WFF σ Γ 0))
    (he : M.sat env (eqRec A t t' : WFF σ Γ 0)) :
    M.sat env (WFF.here hT s t' : WFF σ Γ 0) := by
  change Realised hT (interp env s) (interp env t')
  rw [← (sat_eqRec env A t t').mp he]
  exact h

/-! ## The two readings of a hole formula, at the identity arrow -/

omit [Γ.NoSlots] in
/-- Pushed into `◇_x`, an environment is the one pushed into `□` along the same arrow on the whole
    `□` part of the view: the two are given by the same clauses there. -/
theorem Env.diaPush_boxIn (h : Γ.ref x = some (.VTypeDia X))
    (w' : (M.posEval (env.ref x h)).1) :
    Env.Agree (Ctx.le_boxIn_diaIn Γ x) (env.boxPush w'.1) (env.diaPush x h w') := by
  intro v T hv
  match v with
  | .step _ .box => rfl
  | .step _ .keep => rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

include hnp in
/-- ⭐**The realisation bridge**: at the identity arrow, a hole formula read inside `◇_x` with the
    body `bd` in its hole holds exactly when it holds here with `bd`'s value there in its hole.  The
    `□` part of the view is read at the identity arrow either way — `Env.diaPush_boxIn` and
    `Env.collapseAgree_self` — and the hole gets the same object by `hval`. -/
theorem sat_viewReadTm (h : Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {b : Ann A} (bd : Term σ (Γ.diaIn x) A b)
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1)
    (hmem : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x h)).1)
    (hval : interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) bd = interp env t) :
    M.sat (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) (WFF.viewReadTm bd ψ) ↔
      M.sat env (WFF.hereRead hT t ψ) := by
  refine (sat_instantiate (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩)
    (Ctx.noProjLast_diaIn Γ x) (Ctx.NoSlots.slots (Γ := Γ.diaIn x)) bd _).trans ?_
  rw [hval]
  refine (sat_mono (Env.extend_agree (Env.diaPush_boxIn env h ⟨M.frame.reflAcc hT w, hmem⟩)
    (.bnd 0) (interp env t)) ψ).trans ?_
  refine Iff.symm ((sat_instantiate env hnp Ctx.NoSlots.slots t _).trans ?_)
  exact sat_collapse ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
    ((Env.collapseAgree_self hT env).extend
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (interp env t)) ψ


include hnp in
/-- ⭐The same bridge for **terms**: at the identity arrow, a hole term read inside `◇_x` with the
    body in its hole denotes what it denotes here with the body's value there in its hole. -/
theorem interp_viewReadTm (h : Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {a' : Ann A} (bd : Term σ (Γ.diaIn x) A a')
    {B : VarType} {b : Ann B} (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b)
    (hmem : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x h)).1)
    (hval : interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) bd = interp env t) :
    interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) (Term.viewReadTm bd s) =
      interp env (Term.hereRead hT t s) := by
  have hdp := env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩
  simp only [Term.viewReadTm, Term.hereRead]
  rw [interp_subst _ _ _ ((Ctx.noProjLast_diaIn Γ x).insert (.bnd 0) A) _,
    substEnv_single_tm _ (Ctx.noProjLast_diaIn Γ x) (.bnd 0) bd, hval,
    interp_mono (Env.extend_agree (Env.diaPush_boxIn env h ⟨M.frame.reflAcc hT w, hmem⟩)
      (.bnd 0) (interp env t)) s,
    interp_subst _ _ _ (hnp.insert (.bnd 0) A) env, substEnv_single_tm env hnp (.bnd 0) t,
    interp_collapse ((Env.collapseAgree_self hT env).extend
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (interp env t))]
/-! ## The rules are sound -/


include hnp in
/-- ⭐**β** is sound: the realisation of a body read through a hole term is the realisation of the
    body read here through the same hole (`interp_viewReadTm`), at the one arrow `Here` speaks
    of. -/
theorem sat_here_beta (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    (h : Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {a₁ : Ann A} (bd : Term σ (Γ.diaIn x) A a₁)
    {B : VarType} {b : Ann B}
    (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b)
    (hhere : M.sat env (WFF.here hT (Term.diatm x hx bd) t : WFF σ Γ 0)) :
    M.sat env
      (WFF.here hT (Term.diatm x hx (Term.viewReadTm bd s)) (Term.hereRead hT t s) :
        WFF σ Γ 0) := by
  obtain ⟨hmem, hval⟩ := (sat_here_diatm hT env hx h t bd).mp hhere
  exact (sat_here_diatm hT env hx h (Term.hereRead hT t s) (Term.viewReadTm bd s)).mpr
    ⟨hmem, interp_viewReadTm hT env hnp h t bd s hmem hval⟩
include hnp in
/-- ⭐**Elimination** is sound: what is necessary over the witness's extent holds of the realisation
    here.  This is weak T relativised to the witness. -/
theorem sat_here_elim (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) {a₁ : Ann A}
    (bd : Term σ (Γ.diaIn x) A a₁) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1)
    (hhere : M.sat env (WFF.here hT (Term.diatm x hx bd) t : WFF σ Γ 0))
    (hbox : M.sat env (WFF.boxx x hx (WFF.viewReadTm bd ψ))) :
    M.sat env (WFF.hereRead hT t ψ) := by
  obtain ⟨Y, h⟩ := hx
  obtain ⟨hmem, hval⟩ := (sat_here_diatm hT env ⟨Y, h⟩ h t bd).mp hhere
  by_contra hno
  exact hbox ⟨Y, h, ⟨M.frame.reflAcc hT w, hmem⟩, fun hχ =>
    hno ((sat_viewReadTm hT env hnp h t bd ψ hmem hval).mp hχ)⟩

include hnp in
/-- ⭐**Introduction** is sound: what holds of the realisation here is possible for the witness,
    this very world witnessing it. -/
theorem sat_here_intro (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) {a₁ : Ann A}
    (bd : Term σ (Γ.diaIn x) A a₁) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1)
    (hhere : M.sat env (WFF.here hT (Term.diatm x hx bd) t : WFF σ Γ 0))
    (hφ : M.sat env (WFF.hereRead hT t ψ)) :
    M.sat env (WFF.dia x hx (WFF.viewReadTm bd ψ)) := by
  obtain ⟨Y, h⟩ := hx
  obtain ⟨hmem, hval⟩ := (sat_here_diatm hT env ⟨Y, h⟩ h t bd).mp hhere
  exact ⟨Y, h, ⟨M.frame.reflAcc hT w, hmem⟩,
    (sat_viewReadTm hT env hnp h t bd ψ hmem hval).mpr hφ⟩

/-! ## What has to introduce a `Here` -/

omit [Γ.NoSlots] in
/-- ⭐**Strong T inwards: the existential is valid at every content type.**
    `Model.posRet_exists` is literally this: every object has a possible object whose extent
    contains the reflexive arrow and whose content there is that object.  So `∃x:◇A. Here x t`
    holds in *every* model, at every content type, now that `WFF.here` is general.

    That settles what must put a `Here` into the canonical model's theory.  No rule introduces
    one: `here_elim`, `here_intro`, `here_beta`, `here_fun` and the pinned forms each consume a
    `Here` premise, and the outward rule `T_dia` hands the continuation the realisation *schema*
    (`WFF.retHyp`, which is `here_intro`'s conclusion for each hole formula) rather than the atom
    — and no finite set of schema instances yields the atom.  Since the model's own datum makes
    the atom true, a theory lacking it would be maximal consistent while the model satisfied it,
    so the truth lemma's `here` case would fail.  The chain must therefore witness this
    existential, which is what "`real` driven by `Here`" means; the present `retHyp` hypotheses
    are then derivable from the atom by `here_intro`, so that replaces `T_dia`'s hypotheses
    rather than adding a rule. -/
theorem sat_hereAt_extend {A : VarType} (r : Root)
    (hr : Γ.RootFresh r) (p : M.frame.Dom (.VTypeDia A) w) {a : Ann A} (t : Term σ Γ A a) :
    M.sat (env.extend r p) (WFF.hereAt hT (.root r)
        (Ctx.ref_insert_root Γ r (.VTypeDia A))
        (Term.weaken hr.root (.VTypeDia A) t) : WFF σ (Γ.insert r (.VTypeDia A)) 0) ↔
      Realised hT p (interp env t) := by
  have hag : Env.Agree (Ctx.le_insert hr.root (.VTypeDia A)) env (env.extend r p) := by
    intro v U hv
    have hne : v ≠ .root r := fun hvr => by rw [hvr, hr.root] at hv; cases hv
    simp only [Env.extend, dif_neg hne]
  have hslot : (env.extend r p).ref (.root r) (Ctx.ref_insert_root Γ r (.VTypeDia A)) = p :=
    Env.extend_root env r p (Ctx.ref_insert_root Γ r (.VTypeDia A))
  change Realised hT (interp (env.extend r p) (Term.eta _ _ _))
    (interp (env.extend r p) (Term.mono _ t)) ↔ _
  rw [interp_eta (env.extend r p) (.root r) (Ctx.ref_insert_root Γ r (.VTypeDia A)), hslot,
    interp_mono hag t]

omit [Γ.NoSlots] in
/-- The existential, as `WFF.ex` binds it. -/
theorem sat_here_ex (hS : ModalSys.TStrong = true) {A : VarType} (hA : A.diaFree = true)
    {a : Ann A} (t : Term σ Γ A a) (hr : Γ.RootFresh (.bnd 0)) :
    M.sat env (WFF.ex (.VTypeDia A)
      (WFF.hereAt hT (.root (.bnd 0)) (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A))
        (Term.weaken hr.root (.VTypeDia A) t)) : WFF σ Γ 0) := by
  obtain ⟨p, hm, hcon⟩ := M.posRet_exists hT hS hA (interp env t)
  exact ⟨p, (sat_hereAt_extend hT env (.bnd 0) hr p t).mpr ⟨hm, hcon⟩⟩

end
end Model

end V12M
