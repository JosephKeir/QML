import QML.QML_v12m_CanonHere

/-!
# QML v12m — the canonical model: environments are substitutions of the canonical one

Canonical `IndInvariant` (docs §10.38, item 7) speaks about an *arbitrary* environment.  Over a tame
context (`Ctx.Tame`: finite, one view depth per address) every environment is the canonical
environment at one stage, read through a substitution:

* every value has a representative term (`rep`, by definability);
* finitely many declared addresses, so one stage lies above all their representatives
  (`repSup`);
* the substitution sends each declared address to its representative there (`repSubst`); its
  witness indices are coherent because, at one view depth per address, an address extends at most
  one declared address (`decomp_unique`);
* ⭐`substEnv_repSubst`: reading the canonical environment through it gives the environment back.
-/

namespace V12M

variable [ModalSys]

/-! ## An address extends at most one declared address -/

omit [ModalSys] in
theorem VarSymb.eq_of_rt_path {v v' : VarSymb} (hr : v.rt = v'.rt) (hp : v.path = v'.path) :
    v = v' := by
  rw [VarSymb.eq_root_ext_path v, VarSymb.eq_root_ext_path v', hr, hp]

omit [ModalSys] in
/-- An address whose path ends in a nonempty run of projections ends in a projection. -/
theorem VarSymb.lastProj_of_path {v : VarSymb} {pre a : List Step} (h : v.path = pre ++ a)
    (ha : a ≠ []) (hl : Step.levels a = 0) : v.lastProj = true := by
  obtain ⟨a', s', rfl⟩ := (List.eq_nil_or_concat a).resolve_left ha
  rw [List.concat_eq_append] at h hl
  cases v with
  | root r =>
      change [] = pre ++ (a' ++ [s']) at h
      simp at h
  | step u s =>
      change u.path ++ [s] = pre ++ (a' ++ [s']) at h
      rw [← List.append_assoc] at h
      obtain ⟨-, hs⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at hs
      subst hs
      rw [Step.levels_append, Step.levels_single] at hl
      change s.isProj = true
      by_contra hp
      rw [if_neg hp] at hl
      omega

/-- ⭐**At one view depth per address, an address extends at most one declared address**: a
    declared address extended by projections only ends in a projection, so is not declared. -/
theorem Ctx.decomp_unique {Γ : Ctx} {d : Root → ℕ} (hd : Γ.LevelDepth d) {v v' : VarSymb}
    {T T' : VarType} (hv : Γ v = some T) (hv' : Γ v' = some T') (hl : v.lastProj = false)
    (hl' : v'.lastProj = false) {p p' : List Step} (h : v.ext p = v'.ext p') :
    v = v' ∧ p = p' := by
  have hrt : v.rt = v'.rt := by rw [← VarSymb.ext_rt v p, h, VarSymb.ext_rt]
  have hpath : v.path ++ p = v'.path ++ p' := by rw [← VarSymb.ext_path, h, VarSymb.ext_path]
  have lv := hd v T ((Ctx.ref_nonproj Γ hl).trans hv)
  have lv' := hd v' T' ((Ctx.ref_nonproj Γ hl').trans hv')
  rcases List.append_eq_append_iff.mp hpath with ⟨a, h₁, h₂⟩ | ⟨c, h₁, h₂⟩
  · have ha0 : Step.levels a = 0 := by
      rw [h₁, Step.levels_append, lv, hrt] at lv'
      omega
    by_cases ha : a = []
    · subst ha
      simp only [List.append_nil, List.nil_append] at h₁ h₂
      exact ⟨VarSymb.eq_of_rt_path hrt h₁.symm, h₂⟩
    · exact absurd (VarSymb.lastProj_of_path h₁ ha ha0) (by simp [hl'])
  · have hc0 : Step.levels c = 0 := by
      rw [h₁, Step.levels_append, lv', ← hrt] at lv
      omega
    by_cases hc : c = []
    · subst hc
      simp only [List.append_nil, List.nil_append] at h₁ h₂
      exact ⟨VarSymb.eq_of_rt_path hrt h₁, h₂.symm⟩
    · exact absurd (VarSymb.lastProj_of_path h₁ hc hc0) (by simp [hl])

namespace Canon

variable {σ : Signature} {N₀ : ℕ} (w₀ : World σ N₀) [Countable σ.FuncSyms]
  [Countable σ.RelSyms] [ModalSys.NoB]

/-! ## Representatives -/

/-- A representative of an object: a term denoting it, at some stage. -/
noncomputable def rep {A : VarType} {w : World σ N₀} (o : (frame w₀).Dom A w) :
    DTerm w.L.sys w.T A :=
  ⟨(definable_fromDom w₀ A w o).choose, (definable_fromDom w₀ A w o).choose_spec.choose,
    (definable_fromDom w₀ A w o).choose_spec.choose_spec.choose⟩

theorem rep_spec {A : VarType} {w : World σ N₀} (o : (frame w₀).Dom A w) :
    rden w (rep w₀ o).i (Ctx.Le.refl _) (rep w₀ o).t = fromDom w₀ A w o :=
  (definable_fromDom w₀ A w o).choose_spec.choose_spec.choose_spec

section Represent

variable {Γ : Ctx} {w : World σ N₀} (env : (model w₀).Env Γ w)

/-- The stage of a declared address's representative. -/
noncomputable def repStage (v : VarSymb) : ℕ × ℕ :=
  match h : Γ v with
  | some T => (rep w₀ (env v T h)).i
  | none => (0, 0)

theorem repStage_eq {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    repStage w₀ env v = (rep w₀ (env v T h)).i := by
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
noncomputable def repSup : ℕ × ℕ := hfin.toFinset.sup (repStage w₀ env)

theorem le_repSup {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    (rep w₀ (env v T h)).i ≤ repSup w₀ env hfin := by
  rw [← repStage_eq w₀ env h]
  exact Finset.le_sup (hfin.mem_toFinset.mpr (by change (Γ v).isSome = true; rw [h]; rfl))

/-- ⭐The substitution sending each declared address to its representative, at `repSup`. -/
noncomputable def repSubst : Subst σ (w.L.ctx (repSup w₀ env hfin)) := fun v =>
  match h : Γ v with
  | some T => .tm (Term.mono (w.L.ctx_le (le_repSup w₀ env hfin h)) (rep w₀ (env v T h)).t)
  | none => .hide

theorem repSubst_eq {v : VarSymb} {T : VarType} (h : Γ v = some T) :
    repSubst w₀ env hfin v =
      .tm (Term.mono (w.L.ctx_le (le_repSup w₀ env hfin h)) (rep w₀ (env v T h)).t) := by
  unfold repSubst
  split
  · rename_i T' h'
    obtain rfl : T' = T := Option.some.inj (h'.symm.trans h)
    rfl
  · rename_i h'
    rw [h'] at h
    cases h

theorem repSubst_ok : Subst.Ok Γ (repSubst w₀ env hfin) := fun _ _ _ h => by
  rw [repSubst_eq w₀ env hfin h]
  rfl

open Classical in
/-- The witness index of an address below a declared one: the representative's. -/
noncomputable def repIdx (y : VarSymb) : VarSymb :=
  if h : ∃ q : VarSymb × List Step,
      q.1.lastProj = false ∧ (Γ q.1).isSome = true ∧ y = q.1.ext q.2 then
    (repSubst w₀ env hfin h.choose.1).idxAlong h.choose.2
  else y

/-- ⭐The representing substitution is coherent, at one view depth per address. -/
theorem repSubst_coh {d : Root → ℕ} (hd : Γ.LevelDepth d) :
    Subst.Coh (repIdx w₀ env hfin) Γ (repSubst w₀ env hfin) := by
  refine Subst.coh_of (repSubst_ok w₀ env hfin) fun v T hl hv p => ?_
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
    Model.substEnv (repSubst w₀ env hfin) (repSubst_ok w₀ env hfin) hnp
      (canonEnv w₀ w (repSup w₀ env hfin)) = env := by
  funext v T hv
  change Model.entryVal _ (repSubst w₀ env hfin v) _ = env v T hv
  rw [Model.entryVal_congr _ (repSubst_eq w₀ env hfin hv) _ rfl]
  change Model.interp (canonEnv w₀ w (repSup w₀ env hfin))
    (Term.mono (w.L.ctx_le (le_repSup w₀ env hfin hv)) (rep w₀ (env v T hv)).t) = env v T hv
  rw [interp_canon w₀ _ (fun _ _ _ => rfl)]
  refine Eq.trans ?_ (toDom_fromDom w₀ T w (env v T hv))
  exact toDom_congr w₀ ((rden_lift (le_repSup w₀ env hfin hv) _).trans (rep_spec w₀ _)) _ _

end Represent

end Canon

end V12M
