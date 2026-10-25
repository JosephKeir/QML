import QML.QML_v12m_GTruth

/-!
# QML v12m — the growing tree's canonical model is a model proper

As B's (`QML_v12m_BInd`).  Under T the canonical `Ind` relates objects with related
representatives (`gInd`); without T it is equality.  Invariance is proved from the truth lemma:

* over a tame context every environment is the canonical environment at one stage, read through a
  substitution sending each declared address to a representative of its value (`grepSubst`,
  ⭐`substEnv_grepSubst`);
* ⭐⭐`gmodel_indInvariant`: so a slot formula with an object in its slot is true exactly when the
  substituted slot formula, instantiated at a representative, is in the theory; related objects
  have representatives interchangeable in every slot formula (`DTerm.Rel`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
  [ModalSys.NoSym] (hM₀ : Theory.IsMCS M₀)

/-! ## Representatives -/

/-- A representative of an object: a term denoting it, at some stage. -/
noncomputable def grep {A : VarType} {s : GW hF M₀} (o : (gframe hF hM₀).Dom A s) :
    Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A :=
  ⟨(gdefinable_fromDom hM₀ A s o).choose, (gdefinable_fromDom hM₀ A s o).choose_spec.choose,
    (gdefinable_fromDom hM₀ A s o).choose_spec.choose_spec.choose⟩

theorem grep_spec {A : VarType} {s : GW hF M₀} (o : (gframe hF hM₀).Dom A s) :
    grden hM₀ s (grep hM₀ o).i (Ctx.Le.refl _) (grep hM₀ o).t = gfromDom hM₀ A s o :=
  (gdefinable_fromDom hM₀ A s o).choose_spec.choose_spec.choose_spec

section Represent

variable {Γ : Ctx} {s : GW hF M₀} (env : (gmodel hF hM₀).Env Γ s)

/-- The stage of a declared address's representative. -/
noncomputable def grepStage (v : VarSymb) : ℕ :=
  match h : Γ v with
  | some T => (grep hM₀ (env v T h)).i
  | none => 0

theorem grepStage_eq {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    grepStage hM₀ env v = (grep hM₀ (env v T h)).i := by
  unfold grepStage
  split
  · rename_i T' h'
    obtain rfl : T' = T := Option.some.inj (h'.symm.trans h)
    rfl
  · rename_i h'
    rw [h'] at h
    cases h

variable (hfin : Γ.Fin)

/-- ⭐One stage above every representative: a finite context has finitely many. -/
noncomputable def grepSup : ℕ := hfin.toFinset.sup (grepStage hM₀ env)

theorem le_grepSup {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    (grep hM₀ (env v T h)).i ≤ grepSup hM₀ env hfin := by
  rw [← grepStage_eq hM₀ env h]
  exact Finset.le_sup (hfin.mem_toFinset.mpr (by change (Γ v).isSome = true; rw [h]; rfl))

/-- ⭐The substitution sending each declared address to its representative, at `grepSup`. -/
noncomputable def grepSubst : Subst σ (ctxOf (glat s (grepSup hM₀ env hfin))) := fun v =>
  match h : Γ v with
  | some T => .tm (Term.mono (gle hM₀ s (le_grepSup hM₀ env hfin h)) (grep hM₀ (env v T h)).t)
  | none => .hide

theorem grepSubst_eq {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    grepSubst hM₀ env hfin v =
      .tm (Term.mono (gle hM₀ s (le_grepSup hM₀ env hfin h)) (grep hM₀ (env v T h)).t) := by
  unfold grepSubst
  split
  · rename_i T' h'
    obtain rfl : T' = T := Option.some.inj (h'.symm.trans h)
    rfl
  · rename_i h'
    rw [h'] at h
    cases h

theorem grepSubst_ok : Subst.Ok Γ (grepSubst hM₀ env hfin) := fun _ _ _ h => by
  rw [grepSubst_eq hM₀ env hfin h]
  rfl

open Classical in
/-- The witness index of an address below a declared one: the representative's. -/
noncomputable def grepIdx (y : VarSymb) : VarSymb :=
  if h : ∃ q : VarSymb × List Step,
      q.1.lastProj = false ∧ (Γ q.1).isSome = true ∧ y = q.1.ext q.2 then
    (grepSubst hM₀ env hfin h.choose.1).idxAlong h.choose.2
  else y

/-- ⭐The representing substitution is coherent, at one view depth per address. -/
theorem grepSubst_coh {d : Root → ℕ} (hd : Γ.LevelDepth d) :
    Subst.Coh (grepIdx hM₀ env hfin) Γ (grepSubst hM₀ env hfin) := by
  refine Subst.coh_of (grepSubst_ok hM₀ env hfin) fun v T hl hv p => ?_
  have hex : ∃ q : VarSymb × List Step,
      q.1.lastProj = false ∧ (Γ q.1).isSome = true ∧ v.ext p = q.1.ext q.2 :=
    ⟨(v, p), hl, by rw [hv]; rfl, rfl⟩
  unfold grepIdx
  rw [dif_pos hex]
  obtain ⟨hl', hs', he'⟩ := hex.choose_spec
  obtain ⟨T', hv'⟩ := Option.isSome_iff_exists.mp hs'
  obtain ⟨e₁, e₂⟩ := Ctx.decomp_unique hd hv hv' hl hl' he'
  rw [← e₁, ← e₂]

/-- ⭐**Every environment over a tame context is the canonical one read through a substitution.** -/
theorem substEnv_grepSubst (hnp : Γ.NoProjLast) :
    Model.substEnv (grepSubst hM₀ env hfin) (grepSubst_ok hM₀ env hfin) hnp
      (gcanonEnv hM₀ s (grepSup hM₀ env hfin)) = env := by
  funext v T hv
  change Model.entryVal _ (grepSubst hM₀ env hfin v) _ = env v T hv
  rw [Model.entryVal_congr _ (grepSubst_eq hM₀ env hfin hv) _ rfl]
  change Model.interp (gcanonEnv hM₀ s (grepSup hM₀ env hfin))
    (Term.mono (gle hM₀ s (le_grepSup hM₀ env hfin hv)) (grep hM₀ (env v T hv)).t) = env v T hv
  rw [interp_gcanon _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
  refine Eq.trans ?_ (gtoDom_fromDom hM₀ T s (env v T hv))
  exact gtoDom_congr ((grden_lift (le_grepSup hM₀ env hfin hv) _).trans (grep_spec hM₀ _)) _ _

end Represent

/-- Invariance under T, as B's (`BData.indInvariant_inv`).  Over a tame context an environment is
    the canonical one at a stage, read through a substitution (`substEnv_grepSubst`); so a slot
    formula with an object in its slot is true exactly when the substituted slot formula,
    instantiated at a representative of the object, is in the theory (`sat_subst`,
    `sat_instantiate`, `gtruth`).  Related objects have representatives interchangeable in every
    slot formula (`DTerm.Rel`), so the two memberships agree. -/
theorem gindInvariant_inv : ∀ {Γ : Ctx} [Γ.NoSlots], Γ.Tame → Γ.NoProjLast →
    ∀ {s : GW hF M₀} (env : (gmodel hF hM₀).Env Γ s) {A : VarType}
      (φ : WFF σ (Γ.insert (.bnd 0) A) 1) (o o' : (gframe hF hM₀).Dom A s), gInd hM₀ o o' →
      ((gmodel hF hM₀).sat (env.extend (.bnd 0) o) φ ↔
        (gmodel hF hM₀).sat (env.extend (.bnd 0) o') φ) := by
  intro Γ _ htame hnp s env A φ o o' hInd
  obtain ⟨hfin, d, hd⟩ := htame
  have hθ := grepSubst_ok hM₀ env hfin
  have hc := grepSubst_coh hM₀ env hfin hd
  have h0 : (ctxOf (glat s (grepSup hM₀ env hfin))) (.root (.bnd 0)) = none :=
    (Ctx.NoSlots.slots (Γ := ctxOf (glat s (grepSup hM₀ env hfin)))).root
  let φ' : WFF σ ((ctxOf (glat s (grepSup hM₀ env hfin))).insert (.bnd 0) A) 1 :=
    WFF.subst (VarSymb.shiftSlot (grepIdx hM₀ env hfin) 0 0)
      ((grepSubst hM₀ env hfin).under 0 0 A h0) (Subst.ok_under hθ A h0)
      (Subst.coh_under hθ hc Ctx.NoSlots.slots A h0)
      (Ctx.NoSlots.slots.insert A) ((Ctx.NoSlots.slots).insert A) φ
  have key : ∀ (o₁ : (gframe hF hM₀).Dom A s) (u : Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A),
      grden hM₀ s u.i (Ctx.Le.refl _) u.t = gfromDom hM₀ A s o₁ →
      ∀ (K' : ℕ) (hK : grepSup hM₀ env hfin ≤ K') (hu : u.i ≤ K'),
        ((gmodel hF hM₀).sat (env.extend (.bnd 0) o₁) φ ↔
          WFF.instantiate Ctx.NoSlots.slots (u.lift K' hu)
            (WFF.mono ((gle hM₀ s hK).insert (.bnd 0) A) φ') ∈ (gw hM₀ s).M K') := by
    intro o₁ u hu₁ K' hK hu
    have hval : Model.interp (gcanonEnv hM₀ s K') (u.lift K' hu) = o₁ := by
      rw [interp_gcanon _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
      refine Eq.trans ?_ (gtoDom_fromDom hM₀ A s o₁)
      exact gtoDom_congr ((grden_lift hu u.t).trans hu₁) _ _
    calc (gmodel hF hM₀).sat (env.extend (.bnd 0) o₁) φ
        ↔ (gmodel hF hM₀).sat ((Model.substEnv (grepSubst hM₀ env hfin) hθ hnp
            (gcanonEnv hM₀ s (grepSup hM₀ env hfin))).extend (.bnd 0) o₁) φ := by
          rw [substEnv_grepSubst hM₀ env hfin hnp]
      _ ↔ (gmodel hF hM₀).sat (Model.substEnv ((grepSubst hM₀ env hfin).under 0 0 A h0)
            (Subst.ok_under hθ A h0) (hnp.insert (.bnd 0) A)
            ((gcanonEnv hM₀ s (grepSup hM₀ env hfin)).extend (.bnd 0) o₁)) φ := by
          rw [Model.substEnv_under]
      _ ↔ (gmodel hF hM₀).sat ((gcanonEnv hM₀ s (grepSup hM₀ env hfin)).extend (.bnd 0) o₁)
            φ' :=
          (Model.sat_subst _ _ _ _ _ _ _ φ).symm
      _ ↔ (gmodel hF hM₀).sat ((gcanonEnv hM₀ s K').extend (.bnd 0) o₁)
            (WFF.mono ((gle hM₀ s hK).insert (.bnd 0) A) φ') :=
          (Model.sat_mono (Model.Env.extend_agree (gcanonEnv_le s hK) (.bnd 0) o₁) φ').symm
      _ ↔ (gmodel hF hM₀).sat (gcanonEnv hM₀ s K') (WFF.instantiate Ctx.NoSlots.slots
            (u.lift K' hu) (WFF.mono ((gle hM₀ s hK).insert (.bnd 0) A) φ')) := by
          rw [Model.sat_instantiate (gcanonEnv hM₀ s K') (Ctx.Presented.noProjLast _), hval]
      _ ↔ _ := gtruth s K' _
  obtain ⟨u, u', hu, hu', hrel⟩ := hInd
  have hK : grepSup hM₀ env hfin ≤ max (grepSup hM₀ env hfin) (max u.i u'.i) := le_max_left _ _
  have h₁ : u.i ≤ max (grepSup hM₀ env hfin) (max u.i u'.i) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : u'.i ≤ max (grepSup hM₀ env hfin) (max u.i u'.i) :=
    (le_max_right _ _).trans (le_max_right _ _)
  rw [key o u hu _ hK h₁, key o' u' hu' _ hK h₂]
  exact hrel _ h₁ h₂ _

/-- A representative of an object is one of the value under a hole term, filled. -/
theorem grden_holeAt {s : GW hF M₀} {A : VarType} {o : (gframe hF hM₀).Dom A s}
    (u : Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A)
    (hu : grden hM₀ s u.i (Ctx.Le.refl _) u.t = gfromDom hM₀ A s o)
    {C : VarType} {c : Ann C} (hh : Term σ (Ctx.empty.insert (.bnd 0) A) C c) :
    grden hM₀ s u.i (Ctx.Le.refl _) (Term.holeAt u.t hh) =
      gfromDom hM₀ C s ((gmodel hF hM₀).holeVal hh o) := by
  have e1 := interp_gcanon (hM₀ := hM₀) (Term.holeAt u.t hh) (env := gcanonEnv hM₀ s u.i)
    (e := Ctx.Le.refl _) (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)
  have e2 : Model.interp (gcanonEnv hM₀ s u.i) u.t = o := by
    rw [interp_gcanon u.t (env := gcanonEnv hM₀ s u.i) (e := Ctx.Le.refl _)
      (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
    exact (gtoDom_congr hu _ _).trans (gtoDom_fromDom hM₀ A s o)
  rw [Model.interp_holeAt, e2] at e1
  rw [e1, gfromDom_toDom]

/-- ⭐⭐**The growing tree's canonical model is a model proper**: invariance (`gindInvariant_inv`
    under T, equality without) and the congruence laws: related representatives stay related
    under hole terms and pairing (`DTerm.Rel.holeAt`, `DTerm.Rel.pair`). -/
theorem gmodel_indInvariant : (gmodel hF hM₀).IndInvariant where
  inv := by
    intro Γ _ htame hnp s env A φ o o' hInd
    by_cases hT : ModalSys.T = true
    · exact gindInvariant_inv hM₀ htame hnp env φ o o' (hInd.1 hT)
    · rw [hInd.2 (Bool.eq_false_iff.mpr hT)]
  map := by
    intro A C c hh s o o' hi
    refine ⟨fun hT => ?_, fun hT => by rw [hi.2 hT]⟩
    obtain ⟨u, u', hu, hu', hrel⟩ := hi.1 hT
    exact ⟨⟨u.i, _, Term.holeAt u.t hh⟩, ⟨u'.i, _, Term.holeAt u'.t hh⟩,
      grden_holeAt hM₀ u hu hh, grden_holeAt hM₀ u' hu' hh, hrel.holeAt hh⟩
  pair := by
    intro A C s a a' b b' ha hb
    refine ⟨fun hT => ?_, fun hT => by rw [ha.2 hT, hb.2 hT]⟩
    obtain ⟨u₁, u₁', h₁, h₁', r₁⟩ := ha.1 hT
    obtain ⟨u₂, u₂', h₂, h₂', r₂⟩ := hb.1 hT
    refine ⟨⟨max u₁.i u₂.i, _, Term.pair (u₁.lift _ (le_max_left _ _))
        (u₂.lift _ (le_max_right _ _))⟩,
      ⟨max u₁'.i u₂'.i, _, Term.pair (u₁'.lift _ (le_max_left _ _))
        (u₂'.lift _ (le_max_right _ _))⟩, ?_, ?_, Canon.DTerm.Rel.pair r₁ r₂ _ _ _ _ _ _⟩
    · exact Prod.ext ((grden_lift (le_max_left u₁.i u₂.i) u₁.t).trans h₁)
        ((grden_lift (le_max_right u₁.i u₂.i) u₂.t).trans h₂)
    · exact Prod.ext ((grden_lift (le_max_left u₁'.i u₂'.i) u₁'.t).trans h₁')
        ((grden_lift (le_max_right u₁'.i u₂'.i) u₂'.t).trans h₂')
  ret := fun hS => (absBS hS).elim

end GArrow

end V12M
