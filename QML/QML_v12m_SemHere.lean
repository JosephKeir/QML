import QML.QML_v12m_SemStrongT
import QML.QML_v12m_CtxFin

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

end Model

namespace Model

variable {σ : Signature} {F : Arrows.{u, v} σ} {Root : F.W → Type u}

/-! ## The η-law for shapes -/

/-- Reading a necessary address's contents one view in gives the contents of its shape.  Under T+4
    the contents are `u.keep.here`, a shift followed by a collapse one level further in, and this
    is the second counit (`Arrows.Leaf.collapse_shift_succ`). -/
theorem ShEnv.ref_inner {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (j : ℕ)
    {u : VarSymb}
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
    change ((ρ.ref j u h).inner.map (Arrows.Leaf.shift hF j)).map
      (Arrows.Leaf.collapse hT (j + 1)) = _
    rw [Shp.map_map]
    exact (Shp.map_congr (g := Arrows.Leaf.collapse hT (j + 1) ∘ Arrows.Leaf.shift hF j)
      (g' := id) (fun ℓ => Arrows.Leaf.collapse_shift_succ hT hF j ℓ) _).trans (Shp.map_id _)
  · have hk' : ModalSys.keepOnly = false := by simpa using hk
    rw [ShEnv.ref_congr _ _ (VarSymb.inner_box hk') _ (Ctx.ref_boxIn_of hk' h),
      ShEnv.ref_nonproj _ _ (by decide : ¬ Step.box.isProj = true)]
    rfl

/-- ⭐**η for shapes**: an address's η-expansion has the address's shape. -/
theorem termShp_eta :
    ∀ {Γ : Ctx} {w : F.W} (ρ : ShEnv F Root Γ w) (j : ℕ) {T : VarType}
    (x : VarSymb)
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

end Model

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

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
      refine M.pos_inj ?_ fun hSh => ?_
      swap
      · change domSh hSh (interp env (Term.eta x (.VTypeDia A) h)) = domSh hSh (env.ref x h)
        rw [domSh_interp, ← ref_envShape]
        exact termShp_eta _ 0 x h
      rw [dia_beta env ⟨A, h⟩ h (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of h))]
      refine Sigma.ext rfl (heq_of_eq (funext fun w' => ?_))
      dsimp only
      rw [interp_eta (env.diaPush x h w') (.step x .dia) (Ctx.ref_diaIn_of h),
        Env.ref_dia env h w' (Ctx.ref_diaIn_of h)]

/-! ## Indistinguishability -/

/-- The environment of the empty context. -/
def Env.empty (w : M.frame.W) : M.Env Ctx.empty w := fun _ _ h => nomatch h

/-- A hole term's value at an object: a term closed apart from its hole, evaluated with the object
    in the hole. -/
def holeVal {A B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    {v : M.frame.W} (o : M.frame.Dom A v) : M.frame.Dom B v :=
  interp ((Env.empty v).extend (.bnd 0) o) s

variable (M) in
/-- ⭐**"Comes back as" is a congruence** (strong B, docs §11.20): a hole term maps the values
    and what they come back as (`back_beta`); two carriers over one leg pair (`back_pair`) — two
    carriers' data, as `back_pair` pairs (a `◇`-free component need not be any carrier's, and then
    no atom stands behind it).  Part of a model proper (`IndInvariant.ret`), since it mentions hole
    terms. -/
structure RetCongr : Prop where
  map : ∀ {A B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    {w : M.frame.W} {S : Set (M.frame.Acc w)}
    {val : (a : S) → (c : M.frame.Acc a.1.1) → M.frame.Dom A c.1} {o : M.frame.Dom A w},
    M.Ret S val o → M.Ret S (fun a c => M.holeVal s (val a c)) (M.holeVal s o)
  pair : ∀ {A B : VarType} {w : M.frame.W} {S : Set (M.frame.Acc w)}
    {val : (a : S) → (c : M.frame.Acc a.1.1) → M.frame.Dom A c.1}
    {val' : (a : S) → (c : M.frame.Acc a.1.1) → M.frame.Dom B c.1}
    {o : M.frame.Dom A w} {o' : M.frame.Dom B w},
    M.IsCarrierData S val → M.IsCarrierData S val' → M.Ret S val o → M.Ret S val' o' →
      M.Ret (A := .VTypeProd A B) S
        (fun a c => ((val a c, val' a c) : M.frame.Dom (.VTypeProd A B) c.1))
        ((o, o') : M.frame.Dom (.VTypeProd A B) w)

variable (M) in
/-- ⭐**A model proper.**  `Ind` is **indistinguishability**: related objects satisfy the same
    formulas, whatever the rest of the environment (`inv`).  This is the semantic content of
    `Proof.here_subst` — co-named objects are interchangeable — and it is a condition on models
    rather than a field because it mentions satisfaction, which is defined from the model (docs
    §10.33).  Stated, as `here_subst` is, for a formula with one slot over a context of a proof: one
    without slots, tame (`Ctx.Tame`: finite, one view depth per address — every presented context
    is) and without projections declared.  That is what lets the canonical model name an
    environment at one stage, coherently (§10.38, §10.40).

    And `Ind` is a **congruence** for what strong B builds values with (§11.15): it is preserved by
    a hole term (`map`, `back_beta`/`ret_beta`) and by pairing (`pair`, `back_pair`/`ret_ext`).  At
    a `◇`-free type, `Ind` to a named object is equality (`Model.eq_of_ind`) and these are free;
    at a `◇`-typed content they are what returning a value *up to `Ind`* needs.

    Under strong B, "comes back as" (`Model.Ret`) is a congruence for the same two operations
    (`ret`: `back_beta`, `back_pair`); its invariance under `Ind` is part of `inv`. -/
structure IndInvariant : Prop where
  inv : ∀ {Γ : Ctx} [Γ.NoSlots], Γ.Tame → Γ.NoProjLast → ∀ {w : M.frame.W} (env : M.Env Γ w)
    {A : VarType} (φ : WFF σ (Γ.insert (.bnd 0) A) 1) (o o' : M.frame.Dom A w),
    M.Ind o o' → (M.sat (env.extend (.bnd 0) o) φ ↔ M.sat (env.extend (.bnd 0) o') φ)
  map : ∀ {A B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    {w : M.frame.W} {o o' : M.frame.Dom A w}, M.Ind o o' → M.Ind (M.holeVal s o) (M.holeVal s o')
  pair : ∀ {A B : VarType} {w : M.frame.W} {a a' : M.frame.Dom A w} {b b' : M.frame.Dom B w},
    M.Ind a a' → M.Ind b b' → M.Ind (A := .VTypeProd A B) (w := w) (a, b) (a', b')
  ret : ModalSys.BStrong = true → M.RetCongr

/-- A model whose `Ind` is equality is a model proper, given that "comes back as" is a
    congruence. -/
theorem indInvariant_of_eq
    (h : ∀ {A : VarType} {w : M.frame.W} (o o' : M.frame.Dom A w), M.Ind o o' → o = o')
    (hR : ModalSys.BStrong = true → M.RetCongr) :
    M.IndInvariant where
  inv := by
    intro Γ _ _ _ w env A φ o o' hi
    rw [h o o' hi]
  map := by
    intro _ _ _ s _ _ _ hi
    rw [h _ _ hi]
    exact M.Ind_refl _
  pair := by
    intro _ _ _ _ _ _ _ ha hb
    rw [h _ _ ha, h _ _ hb]
    exact M.Ind_refl _
  ret := hR

/-! ## What the pinned form says -/

section

variable (hT : ModalSys.T = true) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
  (hnp : Γ.NoProjLast) (hfin : Γ.Tame) {x : VarSymb} {X : VarType}

omit [Γ.NoSlots] in
/-- ⭐The pinned form says that the identity arrow lies in the address's extent, and that the
    content there is indistinguishable from `t`. -/
theorem sat_hereAt {A : VarType} (hx : Γ.ref x = some (.VTypeDia A))
    {a : Ann A}
    (t : Term σ Γ A a) :
    M.sat env (WFF.hereAt hT x hx t : WFF σ Γ 0) ↔
      ∃ hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hx)).1,
        M.Ind ((M.posEval (env.ref x hx)).2 ⟨M.frame.reflAcc hT w, hm⟩) (interp env t) := by
  change Realised hT (interp env (Term.eta x (.VTypeDia A) hx)) (interp env t) ↔ _
  rw [interp_eta env x hx]
  exact Iff.rfl

omit [Γ.NoSlots] in
/-- ⭐What the general form says: the identity arrow lies in the witness's extent, and the body's
    value there is indistinguishable from `t`.  By `Model.dia_beta`, a `◇`-term has its witness's
    extent. -/
theorem sat_here_diatm (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    (h : Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a)
    {a₁ : Ann A} (bd : Term σ (Γ.diaIn x) A a₁) :
    M.sat env (WFF.here hT (Term.diatm x hx bd) t : WFF σ Γ 0) ↔
      ∃ hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x h)).1,
        M.Ind (interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hm⟩) bd) (interp env t) := by
  change Realised hT (interp env (Term.diatm x hx bd)) (interp env t) ↔ _
  unfold Realised
  rw [dia_beta env hx h bd]

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
  exact ⟨hm', M.Ind_refl _⟩

include hnp hfin in
/-- ⭐**Functionality, substitutionally, is sound at every content type**: both candidates are
    indistinguishable from the one content, so substituting one for the other in any formula
    preserves truth (`Model.sat_instantiate`, then `IndInvariant` twice).  This is what makes
    `Proof.here_subst` sound where no equation is available — the annotations need not agree, since
    the two instances are simply two formulas (§10.11). -/
theorem sat_here_subst (hM : M.IndInvariant) {A : VarType} {b : Ann (.VTypeDia A)}
    (s : Term σ Γ (.VTypeDia A) b)
    {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
    (φ : WFF σ (Γ.insert (.bnd 0) A) 1)
    (h : M.sat env (WFF.here hT s t : WFF σ Γ 0))
    (h' : M.sat env (WFF.here hT s t' : WFF σ Γ 0))
    (hφ : M.sat env (WFF.instantiate Ctx.NoSlots.slots t φ)) :
    M.sat env (WFF.instantiate Ctx.NoSlots.slots t' φ) := by
  obtain ⟨_, hc⟩ := h
  obtain ⟨_, hc'⟩ := h'
  refine (sat_instantiate env hnp Ctx.NoSlots.slots t' φ).mpr ?_
  refine (hM.inv hfin hnp env φ _ _ hc').mp ?_
  exact (hM.inv hfin hnp env φ _ _ hc).mpr ((sat_instantiate env hnp Ctx.NoSlots.slots t φ).mp hφ)

omit [Γ.NoSlots] in
/-- ⭐**Leibniz for the content is sound**: the defined equality holds exactly when the two contents
    denote one object (`sat_eqRec`), and `Realised` receives the same object. -/
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

include hnp hfin in
/-- ⭐**The realisation bridge**: at the identity arrow, a hole formula read inside `◇_x` with the
    body `bd` in its hole holds exactly when it holds here with `t` in its hole, `t` being
    indistinguishable from `bd`'s value there.  The `□` part of the view is read at the identity
    arrow either way — `Env.diaPush_boxIn` and `Env.collapseAgree_self` — and `IndInvariant` moves
    the hole from `bd`'s value to `t`'s. -/
theorem sat_viewReadTm (hM : M.IndInvariant) (h : Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) {b : Ann A} (bd : Term σ (Γ.diaIn x) A b)
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1)
    (hmem : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x h)).1)
    (hval : M.Ind (interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) bd) (interp env t)) :
    M.sat (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) (WFF.viewReadTm bd ψ) ↔
      M.sat env (WFF.hereRead hT t ψ) := by
  refine (sat_instantiate (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩)
    (Ctx.noProjLast_diaIn Γ x) (Ctx.NoSlots.slots (Γ := Γ.diaIn x)) bd _).trans ?_
  refine (sat_mono (Env.extend_agree (Env.diaPush_boxIn env h ⟨M.frame.reflAcc hT w, hmem⟩)
    (.bnd 0) (interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) bd)) ψ).trans ?_
  refine (sat_collapse ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
    ((Env.collapseAgree_self hT env).extend
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0))
      (interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) bd)) ψ).symm.trans ?_
  refine (hM.inv hfin hnp env _ _ _ hval).trans ?_
  exact (sat_instantiate env hnp Ctx.NoSlots.slots t _).symm

/-- The value of a hole term read inside `◇_x` with the body in its hole, at the identity arrow:
    the hole term's value in the `□` view there, with the body's value in the hole. -/
theorem interp_viewReadTm (h : Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a' : Ann A} (bd : Term σ (Γ.diaIn x) A a')
    {B : VarType} {b : Ann B} (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b)
    (hmem : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x h)).1) :
    interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) (Term.viewReadTm bd s) =
      interp ((env.boxPush (M.frame.reflAcc hT w)).extend (.bnd 0)
        (interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) bd)) s := by
  simp only [Term.viewReadTm]
  rw [interp_subst _ _ _ ((Ctx.noProjLast_diaIn Γ x).insert (.bnd 0) A) _,
    substEnv_single_tm _ (Ctx.noProjLast_diaIn Γ x) (.bnd 0) bd,
    interp_mono (Env.extend_agree (Env.diaPush_boxIn env h ⟨M.frame.reflAcc hT w, hmem⟩)
      (.bnd 0) _) s]

include hnp in
/-- The value of a hole term read here with `t` in its hole: the hole term's value in the `□`
    view at the identity arrow, with `t`'s value in the hole. -/
theorem interp_hereRead {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {B : VarType} {b : Ann B} (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b) :
    interp env (Term.hereRead hT t s) =
      interp ((env.boxPush (M.frame.reflAcc hT w)).extend (.bnd 0) (interp env t)) s := by
  simp only [Term.hereRead]
  rw [interp_subst _ _ _ (hnp.insert (.bnd 0) A) env, substEnv_single_tm env hnp (.bnd 0) t,
    interp_collapse ((Env.collapseAgree_self hT env).extend
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) (interp env t))]

/-! ## The rules are sound -/

include hnp hfin in
/-- ⭐**β** is sound.  The new subject `⟨x; viewReadTm bd s⟩` is realised here, its content being
    the hole term `s` read with `bd`'s value `c` in the hole (`interp_viewReadTm`); the claimed
    content is `s` read with `t`'s value in the hole (`interp_hereRead`).  So the atom "`Here`(new
    subject, `s` read with the hole)" holds with `c` in the hole, by reflexivity, and `IndInvariant`
    carries it to `t`'s value, `c` and `t` being indistinguishable. -/
theorem sat_here_beta (hM : M.IndInvariant) (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    (h : Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {a₁ : Ann A} (bd : Term σ (Γ.diaIn x) A a₁)
    {B : VarType} {b : Ann B}
    (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b)
    (hhere : M.sat env (WFF.here hT (Term.diatm x hx bd) t : WFF σ Γ 0)) :
    M.sat env
      (WFF.here hT (Term.diatm x hx (Term.viewReadTm bd s)) (Term.hereRead hT t s) :
        WFF σ Γ 0) := by
  obtain ⟨hmem, hval⟩ := (sat_here_diatm hT env hx h t bd).mp hhere
  refine (sat_here_diatm hT env hx h (Term.hereRead hT t s) (Term.viewReadTm bd s)).mpr
    ⟨hmem, ?_⟩
  rw [interp_viewReadTm hT env h bd s hmem, interp_hereRead hT env hnp t s]
  -- The atom `Here(new subject, s read with the hole)`, with the hole filled by `o`.
  have hr : Γ.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)
  let S := Term.mono (Ctx.le_insert hr.root A) (Term.diatm x hx (Term.viewReadTm bd s))
  let Φ : WFF σ (Γ.insert (.bnd 0) A) 1 :=
    WFF.here hT S (Term.collapse ((Ctx.collapses_boxIn_self hT Γ).insert
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) A) s)
  have key : ∀ o : M.frame.Dom A w, M.sat (env.extend (.bnd 0) o) Φ ↔
      M.Ind (interp ((env.boxPush (M.frame.reflAcc hT w)).extend (.bnd 0)
          (interp (env.diaPush x h ⟨M.frame.reflAcc hT w, hmem⟩) bd)) s)
        (interp ((env.boxPush (M.frame.reflAcc hT w)).extend (.bnd 0) o) s) := by
    intro o
    have hag : Env.Agree (Ctx.le_insert hr.root A) env (env.extend (.bnd 0) o) := by
      intro v U hv
      have hne : v ≠ .root (.bnd 0) := fun hvr => by rw [hvr, hr.root] at hv; cases hv
      simp only [Env.extend, dif_neg hne]
    change Realised hT (interp (env.extend (.bnd 0) o) S)
      (interp (env.extend (.bnd 0) o) (Term.collapse _ s)) ↔ _
    rw [interp_mono hag, interp_collapse ((Env.collapseAgree_self hT env).extend
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) o)]
    unfold Realised
    rw [dia_beta env hx h (Term.viewReadTm bd s)]
    constructor
    · rintro ⟨_, hi⟩
      dsimp only at hi
      rwa [interp_viewReadTm hT env h bd s hmem] at hi
    · intro hi
      refine ⟨hmem, ?_⟩
      dsimp only
      rwa [interp_viewReadTm hT env h bd s hmem]
  exact (key _).mp ((hM.inv hfin hnp env Φ _ _ hval).mp ((key _).mpr (M.Ind_refl _)))

include hnp hfin in
/-- ⭐**Elimination** is sound: what is necessary over the witness's extent holds of the realisation
    here.  This is weak T relativised to the witness. -/
theorem sat_here_elim (hM : M.IndInvariant) (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) {a₁ : Ann A}
    (bd : Term σ (Γ.diaIn x) A a₁) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1)
    (hhere : M.sat env (WFF.here hT (Term.diatm x hx bd) t : WFF σ Γ 0))
    (hbox : M.sat env (WFF.boxx x hx (WFF.viewReadTm bd ψ))) :
    M.sat env (WFF.hereRead hT t ψ) := by
  obtain ⟨Y, h⟩ := hx
  obtain ⟨hmem, hval⟩ := (sat_here_diatm hT env ⟨Y, h⟩ h t bd).mp hhere
  by_contra hno
  exact hbox ⟨Y, h, ⟨M.frame.reflAcc hT w, hmem⟩, fun hχ =>
    hno ((sat_viewReadTm hT env hnp hfin hM h t bd ψ hmem hval).mp hχ)⟩

include hnp hfin in
/-- ⭐**Introduction** is sound: what holds of the realisation here is possible for the witness,
    this very world witnessing it. -/
theorem sat_here_intro (hM : M.IndInvariant) (hx : ∃ Y, Γ.ref x = some (.VTypeDia Y))
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) {a₁ : Ann A}
    (bd : Term σ (Γ.diaIn x) A a₁) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1)
    (hhere : M.sat env (WFF.here hT (Term.diatm x hx bd) t : WFF σ Γ 0))
    (hφ : M.sat env (WFF.hereRead hT t ψ)) :
    M.sat env (WFF.dia x hx (WFF.viewReadTm bd ψ)) := by
  obtain ⟨Y, h⟩ := hx
  obtain ⟨hmem, hval⟩ := (sat_here_diatm hT env ⟨Y, h⟩ h t bd).mp hhere
  exact ⟨Y, h, ⟨M.frame.reflAcc hT w, hmem⟩,
    (sat_viewReadTm hT env hnp hfin hM h t bd ψ hmem hval).mpr hφ⟩

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
theorem sat_here_ex (hS : ModalSys.TStrong = true) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (hr : Γ.RootFresh (.bnd 0)) :
    M.sat env (WFF.ex (.VTypeDia A)
      (WFF.hereAt hT (.root (.bnd 0)) (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A))
        (Term.weaken hr.root (.VTypeDia A) t)) : WFF σ Γ 0) := by
  obtain ⟨p, hm, hcon⟩ := M.posRet_exists hT hS (interp env t)
  exact ⟨p, (sat_hereAt_extend hT env (.bnd 0) hr p t).mpr ⟨hm, hcon⟩⟩

end
end Model

end V12M
