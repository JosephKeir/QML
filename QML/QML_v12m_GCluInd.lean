import QML.QML_v12m_GCluTruth

/-!
# QML v12m — 5 on the growing tree: the cluster model is a model proper

As the growing tree's (`QML_v12m_GInd`).  Under T the canonical `Ind` relates objects with related
representatives (`cInd`); without T it is equality.  Invariance is proved from the truth lemma:

* over a tame context every environment is the canonical environment at one stage, read through a
  substitution sending each declared address to a representative of its value (`crepSubst`,
  ⭐`substEnv_crepSubst`);
* ⭐⭐`cmodel_indInvariant`: so a slot formula with an object in its slot is true exactly when the
  substituted slot formula, instantiated at a representative, is in the theory; related objects
  have representatives interchangeable in every slot formula (`DTerm.Rel`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}
  (hM₀ : Theory.IsMCS M₀) (hX : CluFlags)

/-! ## Representatives -/

/-- A representative of an object: a term denoting it, at some stage. -/
noncomputable def crep {A : VarType} {s : GW hF M₀} (o : (cframe hF hM₀ hX).Dom A s) :
    Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A :=
  ⟨(cdefinable_fromDom hM₀ hX A s o).choose, (cdefinable_fromDom hM₀ hX A s o).choose_spec.choose,
    (cdefinable_fromDom hM₀ hX A s o).choose_spec.choose_spec.choose⟩

theorem crep_spec {A : VarType} {s : GW hF M₀} (o : (cframe hF hM₀ hX).Dom A s) :
    cden hM₀ hX s (crep hM₀ hX o).i (Ctx.Le.refl _) (crep hM₀ hX o).t = cfromDom hM₀ hX A s o :=
  (cdefinable_fromDom hM₀ hX A s o).choose_spec.choose_spec.choose_spec

section Represent

variable {Γ : Ctx} {s : GW hF M₀} (env : (cmodel hF hM₀ hX).Env Γ s)

/-- The stage of a declared address's representative. -/
noncomputable def crepStage (v : VarSymb) : ℕ :=
  match h : Γ v with
  | some T => (crep hM₀ hX (env v T h)).i
  | none => 0

theorem crepStage_eq {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    crepStage hM₀ hX env v = (crep hM₀ hX (env v T h)).i := by
  unfold crepStage
  split
  · rename_i T' h'
    obtain rfl : T' = T := Option.some.inj (h'.symm.trans h)
    rfl
  · rename_i h'
    rw [h'] at h
    cases h

variable (hfin : Γ.Fin)

/-- ⭐One stage above every representative: a finite context has finitely many. -/
noncomputable def crepSup : ℕ := hfin.toFinset.sup (crepStage hM₀ hX env)

theorem le_crepSup {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    (crep hM₀ hX (env v T h)).i ≤ crepSup hM₀ hX env hfin := by
  rw [← crepStage_eq hM₀ hX env h]
  exact Finset.le_sup (hfin.mem_toFinset.mpr (by change (Γ v).isSome = true; rw [h]; rfl))

/-- ⭐The substitution sending each declared address to its representative, at `crepSup`. -/
noncomputable def crepSubst : Subst σ (ctxOf (glat s (crepSup hM₀ hX env hfin))) := fun v =>
  match h : Γ v with
  | some T => .tm (Term.mono (gle hM₀ s (le_crepSup hM₀ hX env hfin h)) (crep hM₀ hX (env v T h)).t)
  | none => .hide

theorem crepSubst_eq {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    crepSubst hM₀ hX env hfin v =
      .tm (Term.mono (gle hM₀ s (le_crepSup hM₀ hX env hfin h)) (crep hM₀ hX (env v T h)).t) := by
  unfold crepSubst
  split
  · rename_i T' h'
    obtain rfl : T' = T := Option.some.inj (h'.symm.trans h)
    rfl
  · rename_i h'
    rw [h'] at h
    cases h

theorem crepSubst_ok : Subst.Ok Γ (crepSubst hM₀ hX env hfin) := fun _ _ _ h => by
  rw [crepSubst_eq hM₀ hX env hfin h]
  rfl

open Classical in
/-- The witness index of an address below a declared one: the representative's. -/
noncomputable def crepIdx (y : VarSymb) : VarSymb :=
  if h : ∃ q : VarSymb × List Step,
      q.1.lastProj = false ∧ (Γ q.1).isSome = true ∧ y = q.1.ext q.2 then
    (crepSubst hM₀ hX env hfin h.choose.1).idxAlong h.choose.2
  else y

/-- ⭐The representing substitution is coherent, at one view depth per address. -/
theorem crepSubst_coh {d : Root → ℕ} (hd : Γ.LevelDepth d) :
    Subst.Coh (crepIdx hM₀ hX env hfin) Γ (crepSubst hM₀ hX env hfin) := by
  refine Subst.coh_of (crepSubst_ok hM₀ hX env hfin) fun v T hl hv p => ?_
  have hex : ∃ q : VarSymb × List Step,
      q.1.lastProj = false ∧ (Γ q.1).isSome = true ∧ v.ext p = q.1.ext q.2 :=
    ⟨(v, p), hl, by rw [hv]; rfl, rfl⟩
  unfold crepIdx
  rw [dif_pos hex]
  obtain ⟨hl', hs', he'⟩ := hex.choose_spec
  obtain ⟨T', hv'⟩ := Option.isSome_iff_exists.mp hs'
  obtain ⟨e₁, e₂⟩ := Ctx.decomp_unique hd hv hv' hl hl' he'
  rw [← e₁, ← e₂]

/-- ⭐**Every environment over a tame context is the canonical one read through a substitution.** -/
theorem substEnv_crepSubst (hnp : Γ.NoProjLast) :
    Model.substEnv (crepSubst hM₀ hX env hfin) (crepSubst_ok hM₀ hX env hfin) hnp
      (ccanonEnv hM₀ hX s (crepSup hM₀ hX env hfin)) = env := by
  funext v T hv
  change Model.entryVal _ (crepSubst hM₀ hX env hfin v) _ = env v T hv
  rw [Model.entryVal_congr _ (crepSubst_eq hM₀ hX env hfin hv) _ rfl]
  change Model.interp (ccanonEnv hM₀ hX s (crepSup hM₀ hX env hfin))
    (Term.mono (gle hM₀ s (le_crepSup hM₀ hX env hfin hv)) (crep hM₀ hX (env v T hv)).t) =
      env v T hv
  rw [interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
  refine Eq.trans ?_ (ctoDom_fromDom hM₀ hX T s (env v T hv))
  exact ctoDom_congr hX ((cden_lift hX (le_crepSup hM₀ hX env hfin hv) _).trans
    (crep_spec hM₀ hX _)) _ _

end Represent

/-- Invariance under T, as the tree's (`gindInvariant_inv`).  Over a tame context an environment is
    the canonical one at a stage, read through a substitution (`substEnv_crepSubst`); so a slot
    formula with an object in its slot is true exactly when the substituted slot formula,
    instantiated at a representative of the object, is in the theory (`sat_subst`,
    `sat_instantiate`, `ctruth`).  Related objects have representatives interchangeable in every
    slot formula (`DTerm.Rel`), so the two memberships agree. -/
theorem cindInvariant_inv (hNS : ModalSys.BStrong = false) :
    ∀ {Γ : Ctx} [Γ.NoSlots], Γ.Tame → Γ.NoProjLast →
    ∀ {s : GW hF M₀} (env : (cmodel hF hM₀ hX).Env Γ s) {A : VarType}
      (φ : WFF σ (Γ.insert (.bnd 0) A) 1) (o o' : (cframe hF hM₀ hX).Dom A s), cInd hM₀ hX o o' →
      ((cmodel hF hM₀ hX).sat (env.extend (.bnd 0) o) φ ↔
        (cmodel hF hM₀ hX).sat (env.extend (.bnd 0) o') φ) := by
  intro Γ _ htame hnp s env A φ o o' hInd
  obtain ⟨hfin, d, hd⟩ := htame
  have hθ := crepSubst_ok hM₀ hX env hfin
  have hc := crepSubst_coh hM₀ hX env hfin hd
  have h0 : (ctxOf (glat s (crepSup hM₀ hX env hfin))) (.root (.bnd 0)) = none :=
    (Ctx.NoSlots.slots (Γ := ctxOf (glat s (crepSup hM₀ hX env hfin)))).root
  let φ' : WFF σ ((ctxOf (glat s (crepSup hM₀ hX env hfin))).insert (.bnd 0) A) 1 :=
    WFF.subst (VarSymb.shiftSlot (crepIdx hM₀ hX env hfin) 0 0)
      ((crepSubst hM₀ hX env hfin).under 0 0 A h0) (Subst.ok_under hθ A h0)
      (Subst.coh_under hθ hc Ctx.NoSlots.slots A h0)
      (Ctx.NoSlots.slots.insert A) ((Ctx.NoSlots.slots).insert A) φ
  have key : ∀ (o₁ : (cframe hF hM₀ hX).Dom A s) (u : Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A),
      cden hM₀ hX s u.i (Ctx.Le.refl _) u.t = cfromDom hM₀ hX A s o₁ →
      ∀ (K' : ℕ) (hK : crepSup hM₀ hX env hfin ≤ K') (hu : u.i ≤ K'),
        ((cmodel hF hM₀ hX).sat (env.extend (.bnd 0) o₁) φ ↔
          WFF.instantiate Ctx.NoSlots.slots (u.lift K' hu)
            (WFF.mono ((gle hM₀ s hK).insert (.bnd 0) A) φ') ∈ (gw hM₀ s).M K') := by
    intro o₁ u hu₁ K' hK hu
    have hval : Model.interp (ccanonEnv hM₀ hX s K') (u.lift K' hu) = o₁ := by
      rw [interp_ccanon hX _ (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
      refine Eq.trans ?_ (ctoDom_fromDom hM₀ hX A s o₁)
      exact ctoDom_congr hX ((cden_lift hX hu u.t).trans hu₁) _ _
    calc (cmodel hF hM₀ hX).sat (env.extend (.bnd 0) o₁) φ
        ↔ (cmodel hF hM₀ hX).sat ((Model.substEnv (crepSubst hM₀ hX env hfin) hθ hnp
            (ccanonEnv hM₀ hX s (crepSup hM₀ hX env hfin))).extend (.bnd 0) o₁) φ := by
          rw [substEnv_crepSubst hM₀ hX env hfin hnp]
      _ ↔ (cmodel hF hM₀ hX).sat (Model.substEnv ((crepSubst hM₀ hX env hfin).under 0 0 A h0)
            (Subst.ok_under hθ A h0) (hnp.insert (.bnd 0) A)
            ((ccanonEnv hM₀ hX s (crepSup hM₀ hX env hfin)).extend (.bnd 0) o₁)) φ := by
          rw [Model.substEnv_under]
      _ ↔ (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s (crepSup hM₀ hX env hfin)).extend (.bnd 0) o₁)
            φ' :=
          (Model.sat_subst _ _ _ _ _ _ _ φ).symm
      _ ↔ (cmodel hF hM₀ hX).sat ((ccanonEnv hM₀ hX s K').extend (.bnd 0) o₁)
            (WFF.mono ((gle hM₀ s hK).insert (.bnd 0) A) φ') :=
          (Model.sat_mono (Model.Env.extend_agree (ccanonEnv_le hX s hK) (.bnd 0) o₁) φ').symm
      _ ↔ (cmodel hF hM₀ hX).sat (ccanonEnv hM₀ hX s K') (WFF.instantiate Ctx.NoSlots.slots
            (u.lift K' hu) (WFF.mono ((gle hM₀ s hK).insert (.bnd 0) A) φ')) := by
          rw [Model.sat_instantiate (ccanonEnv hM₀ hX s K') (Ctx.Presented.noProjLast _), hval]
      _ ↔ _ := ctruth hX hNS s K' _
  obtain ⟨u, u', hu, hu', hrel⟩ := hInd
  have hK : crepSup hM₀ hX env hfin ≤ max (crepSup hM₀ hX env hfin) (max u.i u'.i) :=
    le_max_left _ _
  have h₁ : u.i ≤ max (crepSup hM₀ hX env hfin) (max u.i u'.i) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : u'.i ≤ max (crepSup hM₀ hX env hfin) (max u.i u'.i) :=
    (le_max_right _ _).trans (le_max_right _ _)
  rw [key o u hu _ hK h₁, key o' u' hu' _ hK h₂]
  exact hrel _ h₁ h₂ _

/-- A representative of an object is one of the value under a hole term, filled. -/
theorem cden_holeAt {s : GW hF M₀} {A : VarType} {o : (cframe hF hM₀ hX).Dom A s}
    (u : Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A)
    (hu : cden hM₀ hX s u.i (Ctx.Le.refl _) u.t = cfromDom hM₀ hX A s o)
    {C : VarType} {c : Ann C} (hh : Term σ (Ctx.empty.insert (.bnd 0) A) C c) :
    cden hM₀ hX s u.i (Ctx.Le.refl _) (Term.holeAt u.t hh) =
      cfromDom hM₀ hX C s ((cmodel hF hM₀ hX).holeVal hh o) := by
  have e1 := interp_ccanon hX (hM₀ := hM₀) (Term.holeAt u.t hh) (env := ccanonEnv hM₀ hX s u.i)
    (e := Ctx.Le.refl _) (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)
  have e2 : Model.interp (ccanonEnv hM₀ hX s u.i) u.t = o := by
    rw [interp_ccanon hX u.t (env := ccanonEnv hM₀ hX s u.i) (e := Ctx.Le.refl _)
      (Model.Env.Agree.refl' _) (Ctx.Presented.noProjLast _)]
    exact (ctoDom_congr hX hu _ _).trans (ctoDom_fromDom hM₀ hX A s o)
  rw [Model.interp_holeAt, e2] at e1
  rw [e1, cfromDom_toDom]

/-- ⭐⭐**The cluster model is a model proper**: invariance (`cindInvariant_inv`
    under T, equality without) and the congruence laws: related representatives stay related
    under hole terms and pairing (`DTerm.Rel.holeAt`, `DTerm.Rel.pair`). -/
theorem cmodel_indInvariant (hF : ModalSys.Four = true) (hNS : ModalSys.BStrong = false) :
    (cmodel hF hM₀ hX).IndInvariant where
  inv := by
    intro Γ _ htame hnp s env A φ o o' hInd
    by_cases hT : ModalSys.T = true
    · exact cindInvariant_inv hM₀ hX hNS htame hnp env φ o o' (hInd.1 hT)
    · rw [hInd.2 (Bool.eq_false_iff.mpr hT)]
  map := by
    intro A C c hh s o o' hi
    refine ⟨fun hT => ?_, fun hT => by rw [hi.2 hT]⟩
    obtain ⟨u, u', hu, hu', hrel⟩ := hi.1 hT
    exact ⟨⟨u.i, _, Term.holeAt u.t hh⟩, ⟨u'.i, _, Term.holeAt u'.t hh⟩,
      cden_holeAt hM₀ hX u hu hh, cden_holeAt hM₀ hX u' hu' hh, hrel.holeAt hh⟩
  pair := by
    intro A C s a a' b b' ha hb
    refine ⟨fun hT => ?_, fun hT => by rw [ha.2 hT, hb.2 hT]⟩
    obtain ⟨u₁, u₁', h₁, h₁', r₁⟩ := ha.1 hT
    obtain ⟨u₂, u₂', h₂, h₂', r₂⟩ := hb.1 hT
    refine ⟨⟨max u₁.i u₂.i, _, Term.pair (u₁.lift _ (le_max_left _ _))
        (u₂.lift _ (le_max_right _ _))⟩,
      ⟨max u₁'.i u₂'.i, _, Term.pair (u₁'.lift _ (le_max_left _ _))
        (u₂'.lift _ (le_max_right _ _))⟩, ?_, ?_, Canon.DTerm.Rel.pair r₁ r₂ _ _ _ _ _ _⟩
    · exact Prod.ext ((cden_lift hX (le_max_left u₁.i u₂.i) u₁.t).trans h₁)
        ((cden_lift hX (le_max_right u₁.i u₂.i) u₂.t).trans h₂)
    · exact Prod.ext ((cden_lift hX (le_max_left u₁'.i u₂'.i) u₁'.t).trans h₁')
        ((cden_lift hX (le_max_right u₁'.i u₂'.i) u₂'.t).trans h₂')
  ret := fun hS => absurd (hNS.symm.trans hS) (by decide)

end GArrow

end V12M
