import QML.QML_v12m_GCluTr

/-!
# QML v12m — 5 on the growing tree: the shapes of denotations

Under T (`docs/v12-modal-extensions.md` §3 5, "Design for the rest"): the shape of a term's
denotation at a world is its annotation's, each index read at the root (`preIx`).

* `KForm`, `KInv`: in a world's `□` view and the views below it every address is keep-first.
* `VForm`, `VInv`: in a `◇_x` view the first level step is a `keep`, or a `dia` at `x`; so a
  preimage maps a term's indices by `preIx` (`mapIdx_eIdx_preIX`).
* `gI`, ⭐`ann_collapse_ren`, ⭐`pTr_ann`: a path translation's annotation.
* ⭐`transpose_annC`: the family of a `□`-term's values' shapes is the term's annotation's shape,
  each member being a keep-first label's by definition (`cLab_keep_of`).
* ⭐⭐`crawShape_cden`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

omit [ModalSys] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem Ann.mapIdx_mapIdx (f g : VarSymb → VarSymb) :
    ∀ {T : VarType} (a : Ann T), (a.mapIdx f).mapIdx g = a.mapIdx (g ∘ f)
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by
      simp only [Ann.mapIdx]
      rw [Ann.mapIdx_mapIdx f g a, Ann.mapIdx_mapIdx f g b]
  | _, .box a => by
      simp only [Ann.mapIdx]
      rw [Ann.mapIdx_mapIdx f g a]
  | _, .dia i a => by
      simp only [Ann.mapIdx]
      rw [Ann.mapIdx_mapIdx f g a]
      rfl

/-! ## Keep-first addresses -/

/-- `y` is a keep-first position of a declared address of `s`, `k` levels below its kept item. -/
def KForm (s : GW hF M₀) (k : ℕ) (y : VarSymb) (T : VarType) : Prop :=
  ∃ (z : VarSymb) (U : VarType) (r : List Step), DeclAt s z U ∧ PPath z.path ∧
    U.keepable = true ∧ y = (VarSymb.step z .keep).ext r ∧ Step.walkTy U r = some T ∧
    Step.levels r = k

theorem KForm.proj {s : GW hF M₀} {k : ℕ} {y : VarSymb} {U T : VarType} (h : KForm s k y U)
    {st : Step} (hs : st.isProj = true) (hst : U.step st = some T) :
    KForm s k (.step y st) T := by
  obtain ⟨z, U₀, r, hd, hv, hk, rfl, hw, hn⟩ := h
  refine ⟨z, U₀, r ++ [st], hd, hv, hk, (VarSymb.ext_append_single _ r st).symm, ?_, ?_⟩
  · rw [Step.walkTy_append, hw, Option.bind_some]
    cases st with
    | fst => exact Option.bind_eq_some_iff.mpr ⟨T, hst, rfl⟩
    | snd => exact Option.bind_eq_some_iff.mpr ⟨T, hst, rfl⟩
    | here => exact Option.bind_eq_some_iff.mpr ⟨T, hst, rfl⟩
    | box => cases hs
    | dia => cases hs
    | keep => cases hs
  · rw [Step.levels_append, hn]
    simp [Step.levels, hs]

theorem KForm.keep {s : GW hF M₀} {k : ℕ} {y : VarSymb} {U : VarType} (h : KForm s k y U)
    (hkU : U.keepable = true) : KForm s (k + 1) (.step y .keep) U := by
  obtain ⟨z, U₀, r, hd, hv, hk, rfl, hw, hn⟩ := h
  refine ⟨z, U₀, r ++ [.keep], hd, hv, hk, (VarSymb.ext_append_single _ r _).symm, ?_, ?_⟩
  · rw [Step.walkTy_append, hw, Option.bind_some, walkTy_keep hkU]
    rfl
  · rw [Step.levels_append, hn]
    simp [Step.levels, Step.isProj]

theorem KForm.dia {s : GW hF M₀} {k : ℕ} {y : VarSymb} {X : VarType}
    (h : KForm s k y (.VTypeDia X)) : KForm s (k + 1) (.step y .dia) X := by
  obtain ⟨z, U₀, r, hd, hv, hk, rfl, hw, hn⟩ := h
  refine ⟨z, U₀, r ++ [.dia], hd, hv, hk, (VarSymb.ext_append_single _ r _).symm, ?_, ?_⟩
  · rw [Step.walkTy_append, hw, Option.bind_some]
    rfl
  · rw [Step.levels_append, hn]
    simp [Step.levels, Step.isProj]

/-- Every reachable address of `Δ` is keep-first. -/
def KInv (s : GW hF M₀) (Δ : Ctx) (k : ℕ) : Prop :=
  ∀ (y : VarSymb) {T : VarType}, Δ.ref y = some T → KForm s k y T

/-- What holds of a context's declared addresses holds of its reachable ones. -/
theorem kInv_of_items {s : GW hF M₀} {Δ : Ctx} {k : ℕ}
    (hitem : ∀ (v : VarSymb) (T : VarType), Δ v = some T → KForm s k v T) : KInv s Δ k
  | .root r, T, h => hitem _ T (by rwa [Ctx.ref_nonproj _ rfl] at h)
  | .step v st, T, h => by
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Δ.ref v = some U := by
          rw [Ctx.ref_step_proj _ v hs] at h
          cases hU : Δ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        have hst : U.step st = some T := by
          rw [Ctx.ref_step_proj _ v hs, hU] at h
          exact h
        exact (kInv_of_items hitem v hU).proj hs hst
      · exact hitem _ T (by rwa [Ctx.ref_step_nonproj _ v hs] at h)

theorem kInv_box_item {s : GW hF M₀} {Δ : Ctx} {k : ℕ} (hko : ModalSys.keepOnly = true)
    (hI : KInv s Δ k) (v : VarSymb) (T : VarType) (h : Δ.boxIn v = some T) :
    KForm s (k + 1) v T := by
  match v, h with
  | .step u .keep, h =>
      obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep h
      exact (hI u hu).keep hk
  | .step u .box, h =>
      have := (Ctx.boxIn_box h).1
      rw [hko] at this
      cases this
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .dia, h => cases h
  | .step _ .here, h => cases h

theorem KInv.box {s : GW hF M₀} {Δ : Ctx} {k : ℕ} (hko : ModalSys.keepOnly = true)
    (hI : KInv s Δ k) : KInv s Δ.boxIn (k + 1) :=
  kInv_of_items (kInv_box_item hko hI)

theorem KInv.dia {s : GW hF M₀} {Δ : Ctx} {k : ℕ} (hko : ModalSys.keepOnly = true)
    (hI : KInv s Δ k) {x : VarSymb} {X : VarType} (hx : Δ.ref x = some (.VTypeDia X)) :
    KInv s (Δ.diaIn x) (k + 1) := by
  refine kInv_of_items fun v T h => ?_
  by_cases hvx : v = .step x .dia
  · subst hvx
    obtain rfl := Ctx.diaIn_step_dia hx h
    exact (hI x hx).dia
  · exact kInv_box_item hko hI v T (diaIn_boxIn_of_ne' h hvx)

/-- A world's `□` view is keep-first. -/
theorem kInv_base {s : GW hF M₀} {i : ℕ} {Γ : Ctx} (hko : ModalSys.keepOnly = true)
    (e : Γ.Le (ctxOf (glat s i))) : KInv s Γ.boxIn 0 := by
  refine kInv_of_items fun v T h => ?_
  match v, h with
  | .step u .keep, h =>
      obtain ⟨-, hu, hk⟩ := Ctx.boxIn_keep h
      exact ⟨u, T, [], ⟨i, e.ref hu⟩, (reach_ppath (e.ref hu)).1, hk, rfl, rfl, rfl⟩
  | .step u .box, h =>
      have := (Ctx.boxIn_box h).1
      rw [hko] at this
      cases this
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .dia, h => cases h
  | .step _ .here, h => cases h

/-! ## What a preimage does to indices -/

/-- In a `◇_x` view: the first level step is a `keep`, or a `dia` at `x`. -/
def VForm (x y : VarSymb) : Prop :=
  ∃ (z : VarSymb) (st : Step) (r : List Step), y = (VarSymb.step z st).ext r ∧ PPath z.path ∧
    (st = .keep ∨ (st = .dia ∧ z = x))

omit [ModalSys] in
theorem VForm.step {x y : VarSymb} (h : VForm x y) (st : Step) : VForm x (.step y st) := by
  obtain ⟨z, st', r, rfl, hz, hst⟩ := h
  exact ⟨z, st', r ++ [st], (VarSymb.ext_append_single _ r st).symm, hz, hst⟩

/-- Every reachable address of `Δ` has its first level step at `x`'s view. -/
def VInv (x : VarSymb) (Δ : Ctx) : Prop :=
  ∀ (y : VarSymb) {T : VarType}, Δ.ref y = some T → VForm x y

theorem vInv_of_items {x : VarSymb} {Δ : Ctx}
    (hitem : ∀ (v : VarSymb) (T : VarType), Δ v = some T → VForm x v) : VInv x Δ
  | .root r, T, h => hitem _ T (by rwa [Ctx.ref_nonproj _ rfl] at h)
  | .step v st, T, h => by
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Δ.ref v = some U := by
          rw [Ctx.ref_step_proj _ v hs] at h
          cases hU : Δ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        exact (vInv_of_items hitem v hU).step st
      · exact hitem _ T (by rwa [Ctx.ref_step_nonproj _ v hs] at h)

theorem vInv_box_item {x : VarSymb} {Δ : Ctx} (hko : ModalSys.keepOnly = true) (hI : VInv x Δ)
    (v : VarSymb) (T : VarType) (h : Δ.boxIn v = some T) : VForm x v := by
  match v, h with
  | .step u .keep, h => exact (hI u (Ctx.boxIn_keep h).2.1).step .keep
  | .step u .box, h =>
      have := (Ctx.boxIn_box h).1
      rw [hko] at this
      cases this
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .dia, h => cases h
  | .step _ .here, h => cases h

theorem VInv.box {x : VarSymb} {Δ : Ctx} (hko : ModalSys.keepOnly = true) (hI : VInv x Δ) :
    VInv x Δ.boxIn :=
  vInv_of_items (vInv_box_item hko hI)

theorem VInv.dia {x : VarSymb} {Δ : Ctx} (hko : ModalSys.keepOnly = true) (hI : VInv x Δ)
    {y : VarSymb} {Y : VarType} (hy : Δ.ref y = some (.VTypeDia Y)) : VInv x (Δ.diaIn y) := by
  refine vInv_of_items fun v T h => ?_
  by_cases hvy : v = .step y .dia
  · subst hvy
    exact (hI y hy).step .dia
  · exact vInv_box_item hko hI v T (diaIn_boxIn_of_ne' h hvy)

/-- A `◇_x` view of a world's stage has its first level steps at `x`. -/
theorem vInv_base {s : GW hF M₀} {i : ℕ} {Γ : Ctx} (hko : ModalSys.keepOnly = true)
    (e : Γ.Le (ctxOf (glat s i))) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) : VInv x (Γ.diaIn x) := by
  refine vInv_of_items fun v T h => ?_
  by_cases hvx : v = .step x .dia
  · subst hvx
    exact ⟨x, .dia, [], rfl, (reach_ppath (e.ref hx)).1, .inr ⟨rfl, rfl⟩⟩
  · match v, diaIn_boxIn_of_ne' h hvx with
    | .step u .keep, hb =>
        exact ⟨u, .keep, [], rfl, (reach_ppath (e.ref (Ctx.boxIn_keep hb).2.1)).1, .inl rfl⟩
    | .step u .box, hb =>
        have := (Ctx.boxIn_box hb).1
        rw [hko] at this
        cases this
    | .root _, hb => cases hb
    | .step _ .fst, hb => cases hb
    | .step _ .snd, hb => cases hb
    | .step _ .dia, hb => cases hb
    | .step _ .here, hb => cases hb

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A term's indices, mapped by two maps agreeing on `x`'s view. -/
theorem mapIdx_of_vInv {x : VarSymb} {ι ι' : VarSymb → VarSymb}
    (hko : ModalSys.keepOnly = true) (hag : ∀ y, VForm x y → ι y = ι' y) :
    ∀ {Δ : Ctx}, VInv x Δ → ∀ {A : VarType} {a : Ann A} (_t : Term σ Δ A a),
      a.mapIdx ι = a.mapIdx ι'
  | _, _, _, _, .var _ _ => rfl
  | _, _, _, _, .func _ => rfl
  | _, _, _, _, .unit => rfl
  | _, hI, _, _, .pair t u => by
      simp only [Ann.mapIdx]
      rw [mapIdx_of_vInv hko hag hI t, mapIdx_of_vInv hko hag hI u]
  | _, hI, _, _, .boxtm u => by
      simp only [Ann.mapIdx]
      rw [mapIdx_of_vInv hko hag (hI.box hko) u]
  | _, hI, _, _, .diatm y hy u => by
      obtain ⟨Y, hr⟩ := id hy
      simp only [Ann.mapIdx]
      rw [mapIdx_of_vInv hko hag (hI.dia hko hr) u, hag _ (hI y hr)]

/-- A preimage's index map is `preIx` on a `◇_x` view. -/
theorem eIdx_preIX_form (s : GW hF M₀) {x y : VarSymb} (h : VForm x y) :
    eIdx (ofRen (σ := σ) (preIX (rorig s) x)) y = preIx s y := by
  obtain ⟨z, st, r, rfl, hz, hst⟩ := h
  have hs : st.isProj = false := by
    rcases hst with rfl | ⟨rfl, -⟩ <;> rfl
  rw [eIdx_item _ hz hs, preIx_lvl _ hz hs]
  change ((preIX (rorig s) x) (.step z st)).ext r = _
  rcases hst with rfl | ⟨rfl, rfl⟩
  · rw [show preIX (rorig s) x (.step z .keep) = .step (rorig s z) .keep from if_neg (by simp)]
  · rw [show preIX (rorig s) z (.step z .dia) = .step (rorig s z) .dia from if_pos rfl]

/-- ⭐**A `◇_x`-view preimage's annotation is the annotation read at the root.** -/
theorem mapIdx_eIdx_preIX (hko : ModalSys.keepOnly = true) (s : GW hF M₀) {i : ℕ} {Γ : Ctx}
    (e : Γ.Le (ctxOf (glat s i))) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    a.mapIdx (eIdx (ofRen (σ := σ) (preIX (rorig s) x))) = a.mapIdx (preIx s) :=
  mapIdx_of_vInv hko (fun _ h => eIdx_preIX_form s h) (vInv_base hko e hx) t

/-! ## A path translation's annotation -/

/-- The kept item of an index renamed by `f`, its `keep` dropped: what collapsing reads. -/
noncomputable def gI (f : VarSymb → VarSymb) (y : VarSymb) : VarSymb :=
  match splitLevel y.path with
  | some (q, .keep, r) => (f ((VarSymb.root y.rt).ext q)).ext r
  | _ => y

omit [ModalSys] in
theorem gI_kept (f : VarSymb → VarSymb) {z : VarSymb} (hz : PPath z.path) (r : List Step) :
    gI f ((VarSymb.step z .keep).ext r) = (f z).ext r := by
  unfold gI
  rw [show ((VarSymb.step z .keep).ext r).path = z.path ++ .keep :: r by
      rw [VarSymb.ext_path]
      change (z.path ++ [.keep]) ++ r = _
      simp,
    splitLevel_ppath hz (by decide)]
  simp only [VarSymb.ext_rt]
  rw [show (VarSymb.step z .keep).rt = z.rt from rfl, VarSymb.root_ext_path]

/-- Renaming a term of a keep-first view twice and collapsing is `gI`. -/
theorem ann_collapse_ren {s : GW hF M₀} (hko : ModalSys.keepOnly = true) (f g : VarSymb → VarSymb)
    (hp : ∀ z U, DeclAt s z U → U.keepable = true → PPath (f z).path) :
    ∀ {Δ : Ctx} {k : ℕ}, KInv s Δ k → ∀ {A : VarType} {a : Ann A} (_t : Term σ Δ A a),
      ((a.mapIdx (eIdx (ofRen (σ := σ) (preI f)))).mapIdx
        (eIdx (ofRen (σ := σ) (preI g)))).collapse k = a.mapIdx (gI (g ∘ f))
  | _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, .unit => rfl
  | _, _, hI, _, _, .pair t u => by
      simp only [Ann.mapIdx, Ann.collapse]
      rw [ann_collapse_ren hko f g hp hI t, ann_collapse_ren hko f g hp hI u]
  | _, _, hI, _, _, .boxtm u => by
      simp only [Ann.mapIdx, Ann.collapse]
      rw [ann_collapse_ren hko f g hp (hI.box hko) u]
  | _, k, hI, _, _, .diatm x hx u => by
      obtain ⟨X, hr⟩ := id hx
      simp only [Ann.mapIdx, Ann.collapse]
      rw [ann_collapse_ren hko f g hp (hI.dia hko hr) u]
      obtain ⟨z, U, r, hd, hz, hk, rfl, -, rfl⟩ := hI x hr
      rw [show eIdx (ofRen (σ := σ) (preI f)) ((VarSymb.step z .keep).ext r) =
          (VarSymb.step (f z) .keep).ext r from eIdx_item _ hz rfl r,
        show eIdx (ofRen (σ := σ) (preI g)) ((VarSymb.step (f z) .keep).ext r) =
          (VarSymb.step (g (f z)) .keep).ext r from eIdx_item _ (hp z U hd hk) rfl r,
        show gI (g ∘ f) ((VarSymb.step z .keep).ext r) = (g (f z)).ext r from gI_kept _ hz r,
        collapse_kept]

section Shape

variable (hX : CluFlags) (hM₀ : Theory.IsMCS M₀) (hT : ModalSys.T = true)

include hX hT in
/-- ⭐**A path translation's annotation.** -/
theorem pTr_ann {P : List ℕ} {t s : GW hF M₀} (h : t.1 = nodeOf (groot hF M₀).1 P)
    (hP : PathOk P) (i : ℕ) {A : VarType} {a : Ann A}
    (b : Term σ (ctxOf (glat s i)).boxIn A a) :
    (pTr hM₀ (groot hF M₀) t P h hP (rstg s i) (preTB hX hM₀ s i b).2).1 =
      a.mapIdx (gI (pnm P (groot hF M₀) t h ∘ rorig s)) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  have e₁ := congrArg Sigma.fst (collapse_pTrK (hM₀ := hM₀) hT (groot hF M₀) t P h hP
    (rstg s i) (preTB hX hM₀ s i b).2)
  have e₂ := congrArg Sigma.fst (tr_pathK hX hM₀ P (groot hF M₀) t h (rstg s i)
    (preTB hX hM₀ s i b).2)
  refine e₁.symm.trans ?_
  change Ann.collapse 0 _ = _
  rw [e₂]
  exact ann_collapse_ren hko _ _ (fun z U hd hk => by
    obtain ⟨j, hj⟩ := declAt_rorig hX.five hX.fourS hX.fourSW hM₀ s hd hk
    exact (reach_ppath hj).1) (kInv_base hko (Ctx.Le.refl _)) b

omit hX hM₀ hT in
theorem pnm_path_congr {P P' : List ℕ} {s t : GW hF M₀} (e : P = P')
    (h : t.1 = nodeOf s.1 P) (h' : t.1 = nodeOf s.1 P') : pnm P s t h = pnm P' s t h' := by
  subst e
  rfl

/-- An index read along an arrow, through the root. -/
noncomputable abbrev chiI (s b : GW hF M₀) (y : VarSymb) : VarSymb :=
  preIx b (gI (rnm b ∘ rorig s) y)

include hX hM₀ hT in
/-- ⭐**The family of an annotation's readings along the arrows is its shape**: a keep-first
    label is the family of what it reads (`cLab_keep_of`). -/
theorem transpose_annC (s g : GW hF M₀) : ∀ {Δ : Ctx} {k : ℕ}, KInv s Δ k → ∀ {A : VarType}
    {a : Ann A} (_t : Term σ Δ A a),
    Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb) (w := g)
        (fun b => annC b.1 (a.mapIdx (chiI s b.1))) = annC g (a.mapIdx (preIx s))
  | _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, .unit => rfl
  | _, _, hI, _, _, .pair t u => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [← transpose_annC s g hI t, ← transpose_annC s g hI u]
      rfl
  | _, _, hI, _, _, .boxtm u => by
      have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      change Shp.box _ = Shp.box _
      rw [← transpose_annC s g (hI.box hko) u]
      rfl
  | _, _, hI, _, _, .diatm x hx u => by
      have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      obtain ⟨X, hr⟩ := id hx
      obtain ⟨z, U, r, hd, hz, hk, e, hw, -⟩ := hI x hr
      have hdo := declAt_rorig hX.five hX.fourS hX.fourSW hM₀ s hd hk
      obtain ⟨j, hj⟩ := id hdo
      refine congrArg₂ Shp.dia ?_ (transpose_annC s g (hI.dia hko hr) u)
      change Arrows.Leaf.fam (fun b => cLab (chiI s b.1 x) b.1) = cLab (preIx s x) g
      rw [e, preIx_lvl _ hz rfl,
        cLab_keep_of hX.five hX.fourS hX.fourSW hM₀ hT hdo (reach_ppath hj).1 hk hw g]
      refine congrArg _ (funext fun b => ?_)
      change cLab (preIx b.1 (gI (rnm b.1 ∘ rorig s) ((VarSymb.step z .keep).ext r))) b.1 = _
      rw [gI_kept _ hz]
      rfl

omit hX hM₀ hT in
/-- A leaf moved to an anchor is its label there. -/
theorem annC_map_rean (s : GW hF M₀) : ∀ {T : VarType} (a : Ann T),
    (annC (groot hF M₀) a).map (CLeaf.rean s) = annC s a
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod a b => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [annC_map_rean s a, annC_map_rean s b]
  | _, .box a => by
      change Shp.box _ = Shp.box _
      rw [annC_map_rean s a]
  | _, .dia i a => by
      change Shp.dia _ _ = Shp.dia _ _
      rw [annC_map_rean s a]
      congr 1
      exact cLab_rean i _ s

include hX hM₀ hT in
/-- ⭐⭐**A denotation's shape is its term's annotation's, each index read at the root.** -/
theorem crawShape_cden : ∀ {A : VarType} {a : Ann A} {Γ : Ctx} (s : GW hF M₀) (i : ℕ)
    (e : Γ.Le (ctxOf (glat s i))) (t : Term σ Γ A a),
    crawShape hT (cden hM₀ hX s i e t) = annC s (a.mapIdx (preIx s))
  | _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, .unit => rfl
  | _, _, _, s, i, e, .pair u v => by
      change Shp.prod (crawShape hT (cden hM₀ hX s i e u)) (crawShape hT (cden hM₀ hX s i e v)) = _
      rw [crawShape_cden s i e u, crawShape_cden s i e v]
      rfl
  | _, _, Γ, s, i, e, .boxtm b => by
      have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      change Shp.box (Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb)
        fun a => crawShape hT (cden hM₀ hX s i e (.boxtm b) a)) = Shp.box _
      refine congrArg Shp.box ?_
      rw [← transpose_annC hX hM₀ hT s s (kInv_base hko e) b]
      refine congrArg _ (funext fun a' => ?_)
      simp only [cden]
      rw [crawShape_cden]
      refine congrArg (annC a'.1) ?_
      rw [pTr_ann hX hM₀ hT (pathOf_eq a'.2.down) (pathOf_ok a'.2.down) i (Term.mono e.boxIn b)]
      rw [pnm_path_congr (nodeOf_inj ((pathOf_eq a'.2.down).symm.trans (rpath_eq a'.1)))
        (pathOf_eq a'.2.down) (rpath_eq a'.1), Ann.mapIdx_mapIdx]
      rfl
  | _, _, Γ, s, i, e, .diatm x hx c => by
      have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      obtain ⟨X, hr⟩ := id hx
      change (annC (groot hF M₀) (.dia (rorig s x) (preTD hX hM₀ s i (hx.imp fun _ h => e.ref h)
        (Term.mono (e.diaIn x) c)).1)).map (CLeaf.rean s) = _
      rw [annC_map_rean]
      change annC s (.dia (rorig s x) (Ann.mapIdx _ _)) = annC s (.dia (preIx s x) _)
      rw [preIx_ppath _ (reach_ppath (e.ref hr)).1, mapIdx_eIdx_preIX hko s e hr c]
  termination_by structural A => A

include hX hM₀ hT in
/-- A `□`-term's value along an arrow has the annotation read along it. -/
theorem crawShape_box_at {A : VarType} {a : Ann A} {Γ : Ctx} (s : GW hF M₀) (i : ℕ)
    (e : Γ.Le (ctxOf (glat s i))) (b : Term σ Γ.boxIn A a) (a' : CAcc hF M₀) :
    crawShape hT (cden hM₀ hX s i e (.boxtm b) a') = annC a'.1 (a.mapIdx (chiI s a'.1)) := by
  simp only [cden]
  rw [crawShape_cden hX hM₀ hT]
  refine congrArg (annC a'.1) ?_
  rw [pTr_ann hX hM₀ hT (pathOf_eq a'.2.down) (pathOf_ok a'.2.down) i (Term.mono e.boxIn b),
    pnm_path_congr (nodeOf_inj ((pathOf_eq a'.2.down).symm.trans (rpath_eq a'.1)))
      (pathOf_eq a'.2.down) (rpath_eq a'.1), Ann.mapIdx_mapIdx]
  rfl

include hX hM₀ hT in
/-- ⭐**The family of a `□`-term's values' shapes is its annotation's shape**, at any anchor. -/
theorem crawShape_box_transpose {A : VarType} {a : Ann A} {Γ : Ctx} (s g : GW hF M₀) (i : ℕ)
    (e : Γ.Le (ctxOf (glat s i))) (b : Term σ Γ.boxIn A a) :
    Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb) (w := g)
        (fun a' => crawShape hT (cden hM₀ hX s i e (.boxtm b) a')) =
      annC g (a.mapIdx (preIx s)) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  rw [← transpose_annC hX hM₀ hT s g (kInv_base hko e) b]
  exact congrArg _ (funext fun a' => crawShape_box_at hX hM₀ hT s i e b a')

end Shape

end GArrow

end V12M
