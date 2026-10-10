import QML.QML_v12m_BTruth

/-!
# QML v12m — B's canonical model is a model proper

The network's `Ind` is attested (`BData.Att`, docs §11.16), and attested objects have related
representatives (`Ind.rel`), so invariance is proved as in the tree (`QML_v12m_CanonInd`,
`Canon.indInvariant`), and the congruence laws hold by construction:

* over a tame context every environment is the canonical environment at one stage, read through a
  substitution sending each declared address to a representative of its value (`repSubst`,
  ⭐`substEnv_repSubst`);
* ⭐⭐`indInvariant`: so a slot formula with an object in its slot is true exactly when the
  substituted slot formula, instantiated at a representative, is in the theory; related objects
  have representatives interchangeable in every slot formula (`DTerm.Rel`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFour] {B : BData σ}

/-! ## Representatives -/

theorem exists_rep {A : VarType} {s : B.W} (o : B.frame.Dom A s) :
    ∃ (i : ℕ) (a : Ann A) (t : Term σ ((B.w s).ctx i) A a),
      B.rden s i (Ctx.Le.refl _) t = B.fromDom A s o :=
  B.definable_fromDom A s o

/-- A representative of an object: a term denoting it, at some stage. -/
noncomputable def rep {A : VarType} {s : B.W} (o : B.frame.Dom A s) :
    Canon.DTerm (B.w s).sys (B.w s).T A :=
  ⟨(exists_rep o).choose, (exists_rep o).choose_spec.choose,
    (exists_rep o).choose_spec.choose_spec.choose⟩

theorem rep_spec {A : VarType} {s : B.W} (o : B.frame.Dom A s) :
    B.rden s (rep o).i (Ctx.Le.refl _) (rep o).t = B.fromDom A s o :=
  (exists_rep o).choose_spec.choose_spec.choose_spec

section Represent

variable {Γ : Ctx} {s : B.W} (env : B.model.Env Γ s)

/-- The stage of a declared address's representative. -/
noncomputable def repStage (v : VarSymb) : ℕ :=
  match h : Γ v with
  | some T => (rep (env v T h)).i
  | none => 0

theorem repStage_eq {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    repStage env v = (rep (env v T h)).i := by
  unfold repStage
  split
  · rename_i T' h'
    obtain rfl : T' = T := Option.some.inj (h'.symm.trans h)
    rfl
  · rename_i h'
    rw [h'] at h
    cases h

variable (hfin : Γ.Fin)

/-- ⭐One stage above every representative: a finite context has finitely many. -/
noncomputable def repSup : ℕ := hfin.toFinset.sup (repStage env)

theorem le_repSup {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    (rep (env v T h)).i ≤ repSup env hfin := by
  rw [← repStage_eq env h]
  exact Finset.le_sup (hfin.mem_toFinset.mpr (by change (Γ v).isSome = true; rw [h]; rfl))

/-- ⭐The substitution sending each declared address to its representative, at `repSup`. -/
noncomputable def repSubst : Subst σ ((B.w s).ctx (repSup env hfin)) := fun v =>
  match h : Γ v with
  | some T => .tm (Term.mono ((B.w s).le (le_repSup env hfin h)) (rep (env v T h)).t)
  | none => .hide

theorem repSubst_eq {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    repSubst env hfin v =
      .tm (Term.mono ((B.w s).le (le_repSup env hfin h)) (rep (env v T h)).t) := by
  unfold repSubst
  split
  · rename_i T' h'
    obtain rfl : T' = T := Option.some.inj (h'.symm.trans h)
    rfl
  · rename_i h'
    rw [h'] at h
    cases h

theorem repSubst_ok : Subst.Ok Γ (repSubst env hfin) := fun _ _ _ h => by
  rw [repSubst_eq env hfin h]
  rfl

open Classical in
/-- The witness index of an address below a declared one: the representative's. -/
noncomputable def repIdx (y : VarSymb) : VarSymb :=
  if h : ∃ q : VarSymb × List Step,
      q.1.lastProj = false ∧ (Γ q.1).isSome = true ∧ y = q.1.ext q.2 then
    (repSubst env hfin h.choose.1).idxAlong h.choose.2
  else y

/-- ⭐The representing substitution is coherent, at one view depth per address. -/
theorem repSubst_coh {d : Root → ℕ} (hd : Γ.LevelDepth d) :
    Subst.Coh (repIdx env hfin) Γ (repSubst env hfin) := by
  refine Subst.coh_of (repSubst_ok env hfin) fun v T hl hv p => ?_
  have hex : ∃ q : VarSymb × List Step,
      q.1.lastProj = false ∧ (Γ q.1).isSome = true ∧ v.ext p = q.1.ext q.2 :=
    ⟨(v, p), hl, by rw [hv]; rfl, rfl⟩
  unfold repIdx
  rw [dif_pos hex]
  obtain ⟨hl', hs', he'⟩ := hex.choose_spec
  obtain ⟨T', hv'⟩ := Option.isSome_iff_exists.mp hs'
  obtain ⟨e₁, e₂⟩ := Ctx.decomp_unique hd hv hv' hl hl' he'
  rw [← e₁, ← e₂]

/-- ⭐**Every environment over a tame context is the canonical one read through a substitution.** -/
theorem substEnv_repSubst (hnp : Γ.NoProjLast) :
    Model.substEnv (repSubst env hfin) (repSubst_ok env hfin) hnp
      (B.canonEnv s (repSup env hfin)) = env := by
  funext v T hv
  change Model.entryVal _ (repSubst env hfin v) _ = env v T hv
  rw [Model.entryVal_congr _ (repSubst_eq env hfin hv) _ rfl]
  change Model.interp (B.canonEnv s (repSup env hfin))
    (Term.mono ((B.w s).le (le_repSup env hfin hv)) (rep (env v T hv)).t) = env v T hv
  rw [interp_canon _ (fun _ _ _ => rfl)]
  refine Eq.trans ?_ (B.toDom_fromDom T s (env v T hv))
  exact toDom_congr ((rden_lift (le_repSup env hfin hv) _).trans (rep_spec _)) _ _

end Represent

/-- Invariance for B's canonical model, as the tree's (`Canon.indInvariant_inv`).  Over a
    tame context an environment is the canonical one at a stage, read through a substitution
    (`substEnv_repSubst`); so a slot formula with an object in its slot is true exactly when the
    substituted slot formula, instantiated at a representative of the object, is in the theory
    (`sat_subst`, `sat_instantiate`, the truth lemma).  Attested objects have representatives
    interchangeable in every slot formula (`Ind.rel`, `DTerm.Rel`), so the two memberships agree. -/
theorem indInvariant_inv : ∀ {Γ : Ctx} [Γ.NoSlots], Γ.Tame → Γ.NoProjLast →
    ∀ {s : B.model.frame.W} (env : B.model.Env Γ s) {A : VarType}
      (φ : WFF σ (Γ.insert (.bnd 0) A) 1) (o o' : B.model.frame.Dom A s), B.model.Ind o o' →
      (B.model.sat (env.extend (.bnd 0) o) φ ↔ B.model.sat (env.extend (.bnd 0) o') φ) := by
  intro Γ _ htame hnp s env A φ o o' hInd
  obtain ⟨hfin, d, hd⟩ := htame
  have hθ := repSubst_ok env hfin
  have hc := repSubst_coh env hfin hd
  have h0 : ((B.w s).ctx (repSup env hfin)) (.root (.bnd 0)) = none :=
    (Ctx.NoSlots.slots (Γ := (B.w s).ctx (repSup env hfin))).root
  let φ' : WFF σ (((B.w s).ctx (repSup env hfin)).insert (.bnd 0) A) 1 :=
    WFF.subst (VarSymb.shiftSlot (repIdx env hfin) 0 0)
      ((repSubst env hfin).under 0 0 A h0) (Subst.ok_under hθ A h0)
      (Subst.coh_under hθ hc Ctx.NoSlots.slots A h0)
      (Ctx.NoSlots.slots.insert A) ((Ctx.NoSlots.slots).insert A) φ
  have key : ∀ (o₁ : B.model.frame.Dom A s) (u : Canon.DTerm (B.w s).sys (B.w s).T A),
      B.rden s u.i (Ctx.Le.refl _) u.t = B.fromDom A s o₁ →
      ∀ (K' : ℕ) (hK : repSup env hfin ≤ K') (hu : u.i ≤ K'),
        (B.model.sat (env.extend (.bnd 0) o₁) φ ↔
          WFF.instantiate Ctx.NoSlots.slots (u.lift K' hu)
            (WFF.mono (((B.w s).le hK).insert (.bnd 0) A) φ') ∈ (B.w s).M K') := by
    intro o₁ u hu₁ K' hK hu
    have hval : Model.interp (B.canonEnv s K') (u.lift K' hu) = o₁ := by
      rw [interp_canon _ (fun _ _ _ => rfl)]
      refine Eq.trans ?_ (B.toDom_fromDom A s o₁)
      exact toDom_congr ((rden_lift hu u.t).trans hu₁) _ _
    calc B.model.sat (env.extend (.bnd 0) o₁) φ
        ↔ B.model.sat ((Model.substEnv (repSubst env hfin) hθ hnp
            (B.canonEnv s (repSup env hfin))).extend (.bnd 0) o₁) φ := by
          rw [substEnv_repSubst env hfin hnp]
      _ ↔ B.model.sat (Model.substEnv ((repSubst env hfin).under 0 0 A h0)
            (Subst.ok_under hθ A h0) (hnp.insert (.bnd 0) A)
            ((B.canonEnv s (repSup env hfin)).extend (.bnd 0) o₁)) φ := by
          rw [Model.substEnv_under]
      _ ↔ B.model.sat ((B.canonEnv s (repSup env hfin)).extend (.bnd 0) o₁) φ' :=
          (Model.sat_subst _ _ _ _ _ _ _ φ).symm
      _ ↔ B.model.sat ((B.canonEnv s K').extend (.bnd 0) o₁)
            (WFF.mono (((B.w s).le hK).insert (.bnd 0) A) φ') :=
          (Model.sat_mono (Model.Env.extend_agree (canonEnv_le s hK) (.bnd 0) o₁) φ').symm
      _ ↔ B.model.sat (B.canonEnv s K') (WFF.instantiate Ctx.NoSlots.slots (u.lift K' hu)
            (WFF.mono (((B.w s).le hK).insert (.bnd 0) A) φ')) := by
          rw [Model.sat_instantiate (B.canonEnv s K') (noProjLast s K'), hval]
      _ ↔ _ := truth s K' _
  obtain ⟨u, u', hu, hu', hrel⟩ := hInd.rel
  have hK : repSup env hfin ≤ max (repSup env hfin) (max u.i u'.i) := le_max_left _ _
  have h₁ : u.i ≤ max (repSup env hfin) (max u.i u'.i) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : u'.i ≤ max (repSup env hfin) (max u.i u'.i) :=
    (le_max_right _ _).trans (le_max_right _ _)
  rw [key o u hu _ hK h₁, key o' u' hu' _ hK h₂]
  exact hrel _ h₁ h₂ _

/-- A representative of an object is one of the value under a hole term, filled. -/
theorem rden_holeAt {s : B.W} {A : VarType} {o : B.model.frame.Dom A s}
    (u : Canon.DTerm (B.w s).sys (B.w s).T A)
    (hu : B.rden s u.i (Ctx.Le.refl _) u.t = B.fromDom A s o)
    {C : VarType} {c : Ann C} (hh : Term σ (Ctx.empty.insert (.bnd 0) A) C c) :
    B.rden s u.i (Ctx.Le.refl _) (Term.holeAt u.t hh) = B.fromDom C s (B.model.holeVal hh o) := by
  have e1 := interp_canon (Term.holeAt u.t hh) (env := B.canonEnv s u.i)
    (e := Ctx.Le.refl _) (fun _ _ _ => rfl)
  have e2 : Model.interp (B.canonEnv s u.i) u.t = o := by
    rw [interp_canon u.t (env := B.canonEnv s u.i) (e := Ctx.Le.refl _) (fun _ _ _ => rfl)]
    exact (B.toDom_congr hu _ _).trans (B.toDom_fromDom A s o)
  rw [Model.interp_holeAt, e2] at e1
  rw [e1, B.fromDom_toDom]

/-- ⭐⭐**B's canonical model is a model proper**: invariance (`indInvariant_inv`) and the
    congruence laws (§11.15), which hold by construction: attestation is closed under hole terms
    and pairing (`Att.holeAt`, `Att.pair`). -/
theorem indInvariant : B.model.IndInvariant where
  inv := indInvariant_inv
  map := by
    intro A C c hh s o o' ⟨u, u', hu, hu', hatt⟩
    exact ⟨⟨u.i, _, Term.holeAt u.t hh⟩, ⟨u'.i, _, Term.holeAt u'.t hh⟩, rden_holeAt u hu hh,
      rden_holeAt u' hu' hh, hatt.holeAt hh⟩
  pair := by
    intro A C s a a' b b' ⟨u₁, u₁', h₁, h₁', r₁⟩ ⟨u₂, u₂', h₂, h₂', r₂⟩
    refine ⟨_, _, ?_, ?_, Att.pair r₁ r₂⟩
    · exact Prod.ext ((rden_lift (le_max_left u₁.i u₂.i) u₁.t).trans h₁)
        ((rden_lift (le_max_right u₁.i u₂.i) u₂.t).trans h₂)
    · exact Prod.ext ((rden_lift (le_max_left u₁'.i u₂'.i) u₁'.t).trans h₁')
        ((rden_lift (le_max_right u₁'.i u₂'.i) u₂'.t).trans h₂')
  ret hS := (ModalSys.NoFour.absurdStrong hS).elim

end BData

end BArrow

end V12M
