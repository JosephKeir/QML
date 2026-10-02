import QML.QML_v12m_BCanonModel
import QML.QML_v12m_CanonTerm

/-!
# QML v12m — B's canonical model: the truth lemma for terms

* `canonEnv s i`: every visible address of stage `i` denotes its η-expansion.
* ⭐`boxPush_canon`: pushing the canonical environment into `□` along an arrow **is** the target's
  canonical environment seen through the arrow's renaming (`substEnv`); `diaPush_canon` likewise
  along a witness arrow.  So substitution (`Model.interp_subst`) replaces the staged model's
  inclusions of views.
* ⭐`interp_canon`: in an environment agreeing with the canonical one, a term's value is its
  denotation — by induction on the type, then the size.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-- The size of a type. -/
def tsz : VarType → ℕ
  | .Var => 0
  | .VTypeOne => 0
  | .VTypeProd A C => tsz A + tsz C + 1
  | .VTypeBox A => tsz A + 1
  | .VTypeDia A => tsz A + 1

namespace BData

variable [ModalSys.NoTFour] {B : BData σ}

theorem noProjLast (s : B.W) (i : ℕ) : ((B.w s).ctx i).NoProjLast :=
  Ctx.Presented.noProjLast _

variable (B)

/-- Without T a possible object is its section: the stored shape is vacuous. -/
theorem posEval_injective {A : VarType} {s : B.W} :
    Function.Injective (B.posEval (A := A) (s := s)) := fun _ _ h =>
  B.posFull_injective (Prod.ext h (funext fun hT => (noT hT).elim))

/-- ⭐The canonical environment: every visible address denotes its η-expansion. -/
noncomputable def canonEnv (s : B.W) (i : ℕ) : B.model.Env ((B.w s).ctx i) s :=
  fun v T hv => B.toDom T s
    (B.rden s i (Ctx.Le.refl _) (Term.eta v T ((Ctx.ref_nonproj _ (noProjLast s i v T hv)).trans
      hv))) (definable_rden _ _)

variable {B}

/-- Every reachable address reads as its η-expansion. -/
theorem canonEnv_ref (s : B.W) (i : ℕ) :
    ∀ (v : VarSymb) {T : VarType} (h : ((B.w s).ctx i).ref v = some T),
      (B.canonEnv s i).ref v h =
        B.toDom T s (B.rden s i (Ctx.Le.refl _) (Term.eta v T h)) (definable_rden _ _)
  | .root _, _, _ => rfl
  | .step v st, T, h => by
      by_cases hs : st.isProj = true
      · rw [Model.Env.ref, dif_pos hs]
        split
        · rename_i U hU
          rw [canonEnv_ref s i v hU]
          have hT : U.step st = some T := by
            rw [Ctx.ref_step_proj _ _ hs, hU] at h
            exact h
          cases st with
          | fst =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              rfl
          | snd =>
              cases U <;> simp only [VarType.step, reduceCtorEq, Option.some.injEq] at hT
              subst hT
              rfl
          | here =>
              cases U <;> simp only [VarType.step, reduceCtorEq] at hT
              exact (noT (VarType.step_here hT).1).elim
          | box => cases hs
          | dia => cases hs
          | keep => cases hs
        · rename_i hU
          rw [Ctx.ref_step_proj _ _ hs, hU] at h
          cases h
      · rw [Model.Env.ref, dif_neg hs]
        rfl

theorem canonEnv_extent (s : B.W) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : ((B.w s).ctx i).ref x = some (.VTypeDia X)) :
    (B.model.posEval ((B.canonEnv s i).ref x hr)).1 = B.extent s x := by
  rw [canonEnv_ref]
  rfl

/-- The canonical environment at a later stage agrees with the one at an earlier stage. -/
theorem canonEnv_le (s : B.W) {i j : ℕ} (hij : i ≤ j) :
    Model.Env.Agree ((B.w s).le hij) (B.canonEnv s i) (B.canonEnv s j) :=
  fun v T hv => toDom_congr (by
    rw [show Term.eta (σ := σ) v T _ = Term.mono ((B.w s).le hij) (Term.eta v T _) from
      (Term.mono_eta _ v T _).symm, rden_mono]
    exact rden_congr _ _ _ _ _ _) _ _

/-! ## Pushing into views along arrows -/

omit [ModalSys.NoTFour] in
/-- A coherent entry that is an address is the address the index map gives. -/
theorem ren_of_coh {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {θ : Subst σ Δ} (hc : Subst.Coh ι Γ θ)
    {v : VarSymb} {U : VarType} (hlp : v.lastProj = false) (hv : Γ v = some U) {w : VarSymb}
    (hw : θ v = .ren w) : θ v = .ren (ι v) := by
  have := hc v U ((Ctx.ref_nonproj Γ hlp).trans hv) []
  rw [Subst.at_nonproj θ hlp, hw] at this
  rw [hw]
  exact congrArg SubE.ren this

/-- An arrow is a renaming. -/
theorem isRen_arrowS {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ} (himg : ImgOk l Δ img) :
    Subst.IsRen (arrowIdx img) (ctxOf l).boxIn (arrowS σ Δ img) :=
  Subst.isRen_of (coh_arrowS himg) fun v U hlp hv => by
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    exact ren_of_coh (coh_arrowS himg) hlp hv rfl

/-- A witness arrow is a renaming. -/
theorem isRen_arrowXS {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ} (himg : ImgOk l Δ img)
    {x : VarSymb} {X : VarType} (hx : (ctxOf l).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : Δ.ref (.root (.free cx)) = some X) :
    Subst.IsRen (arrowXIdx img x cx) ((ctxOf l).diaIn x) (arrowXS σ Δ img x cx) :=
  Subst.isRen_of (coh_arrowXS himg hx hcx) fun v U hlp hv => by
    rcases diaIn_item hv with ⟨u, rfl, _⟩ | ⟨rfl, _⟩
    · exact ren_of_coh (coh_arrowXS himg hx hcx) hlp hv rfl
    · exact ren_of_coh (coh_arrowXS himg hx hcx) hlp hv (if_pos rfl)

/-- ⭐Pushing the canonical environment into `□` along an arrow is the target's canonical
    environment read through the arrow. -/
theorem boxPush_canon (s : B.W) (i : ℕ) (a : B.Acc s) :
    (B.canonEnv s i).boxPush a = Model.substEnv (arrowS σ _ (B.img s a.1))
      (B.arOk (R_of_RT a.2.down) i) (Ctx.noProjLast_boxIn _)
      (B.canonEnv a.1 (B.stg s a.1 i)) := by
  funext v T hv
  obtain ⟨u, rfl, hu⟩ := boxIn_item hv
  have hk := ModalSys.NoTFour.keepOnly
  have hw : ((B.w a.1).ctx (B.stg s a.1 i)).ref (itemAt (imgRoot (B.img s a.1) u.rt) u) =
      some T := B.arOk (R_of_RT a.2.down) i (.step u .box) T rfl hv
  change B.model.necEval ((B.canonEnv s i).ref u (Ctx.boxIn_step_box hv)) a =
    (B.canonEnv a.1 (B.stg s a.1 i)).ref (itemAt (imgRoot (B.img s a.1) u.rt) u) hw
  rw [canonEnv_ref, canonEnv_ref]
  refine toDom_congr ?_ _ _
  change B.rden s i _ (.boxtm (Term.eta u.inner T _)) a = _
  rw [rden_boxtm_net _ _ _ (R_of_RT a.2.down)]
  have hren := isRen_arrowS (σ := σ) (B.imgOk (R_of_RT a.2.down) i)
  have hw' : ((B.w a.1).ctx (B.stg s a.1 i)).ref (arrowIdx (B.img s a.1) (.step u .box)) =
      some T := by
    rw [arrowIdx_item (reach_ppath hu).1]
    exact hw
  exact rden_sigma _ (((Term.subst_sigma (Term.eta_congr (VarSymb.inner_box hk) T _
    (Ctx.ref_boxIn_of hk hu))).trans (Term.subst_eta_ren _ _ _
      (fun v U hv => hren v U ((Ctx.Le.refl _).ref hv)) T _ (Ctx.ref_boxIn_of hk hu) hw')).trans
    (Term.eta_congr (arrowIdx_item (reach_ppath hu).1) T _ _))

/-- ⭐Pushing the canonical environment into `◇_x` along a witness arrow is the target's canonical
    environment read through the witness arrow. -/
theorem diaPush_canon (s : B.W) (i : ℕ) {x : VarSymb} {X : VarType}
    (hr : ((B.w s).ctx i).ref x = some (.VTypeDia X))
    (a : (B.model.posEval ((B.canonEnv s i).ref x hr)).1) :
    (B.canonEnv s i).diaPush x hr a = Model.substEnv (arrowXS σ _ (B.img s a.1.1) x (B.cx s a.1.1))
      (B.arXOk (kd_of_extent (show a.1 ∈ B.extent s x by rw [← canonEnv_extent s i hr]; exact a.2))
        i ⟨X, hr⟩)
      (Ctx.noProjLast_diaIn _ x)
      (B.canonEnv a.1.1 (B.stg s a.1.1 i)) := by
  have ha : a.1 ∈ B.extent s x := by rw [← canonEnv_extent s i hr]; exact a.2
  obtain ⟨X', hk⟩ := kd_of_extent ha
  have hXX := B.hxX hk i X hr
  subst hXX
  have hcx := B.hcx hk i
  funext v T hv
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, hxT⟩
  · have hv' : ((B.w s).ctx i).boxIn (.step u .box) = some T := hv
    exact congrFun (congrFun (congrFun (boxPush_canon s i a.1) (.step u .box)) T) hv'
  · have hTX : T = X := by
      rw [hr] at hxT
      cases hxT
      rfl
    subst hTX
    have he : arrowXS σ ((B.w a.1.1).ctx (B.stg s a.1.1 i)) (B.img s a.1.1) x (B.cx s a.1.1)
        (.step x .dia) = .ren (.root (.free (B.cx s a.1.1))) := by
      change (if x = x then SubE.ren (.root (.free (B.cx s a.1.1))) else .hide) = _
      rw [if_pos rfl]
    refine Eq.trans ?_ (Model.entryVal_congr _ he.symm (T := T) hcx _)
    change (B.model.posEval ((B.canonEnv s i).ref x hr)).2 a =
      (B.canonEnv a.1.1 (B.stg s a.1.1 i)).ref (.root (.free (B.cx s a.1.1))) hcx
    have hpq := canonEnv_ref s i x hr
    rw [Model.posEval_snd_congr hpq a (hpq ▸ a.2)]
    refine toDom_congr ?_ _ _
    change (B.rden s i _ (Term.diatm x _ (Term.eta (.step x .dia) T _))).2 _ = _
    rw [rden_diatm_net _ _ _ _ ⟨_, hk⟩]
    have hren := isRen_arrowXS (σ := σ) (B.imgOk (B.kdR hk) i) hr hcx
    have hix : arrowXIdx (B.img s a.1.1) x (B.cx s a.1.1) (.step x .dia) =
        .root (.free (B.cx s a.1.1)) := by
      have := coh_arrowXS (σ := σ) (B.imgOk (B.kdR hk) i) hr hcx (.step x .dia) T
        (Ctx.ref_diaIn_of hr) []
      rw [Subst.at_nonproj _ rfl] at this
      change (if x = x then SubE.ren (.root (.free (B.cx s a.1.1))) else .hide).idxAlong [] = _
        at this
      rw [if_pos rfl] at this
      exact this.symm
    have hw' : ((B.w a.1.1).ctx (B.stg s a.1.1 i)).ref
        (arrowXIdx (B.img s a.1.1) x (B.cx s a.1.1) (.step x .dia)) = some T := by
      rw [hix]
      exact hcx
    exact rden_sigma _ ((Term.subst_eta_ren _ _ _
      (fun v U hv => hren v U ((Ctx.Le.refl _).ref hv)) T _ (Ctx.ref_diaIn_of hr) hw').trans
      (Term.eta_congr hix T _ _))


/-! ## The truth lemma for terms -/

mutual
  theorem interpFunc_canon : ∀ {Γ : Ctx} {n : ℕ} (g : Func σ Γ n) {s : B.W} {i : ℕ}
      {e : Γ.Le ((B.w s).ctx i)} {env : B.model.Env Γ s},
      Model.Env.Agree e env (B.canonEnv s i) →
      ∀ (args : Fin n → (B.w s).D) (ts : Fin n → Term σ Γ .Var .var),
        (∀ k, args k = (B.w s).cls i (Term.mono e (ts k))) →
        Model.interpFunc env g args =
          (B.w s).cls i (Term.mono e (.func ((Spine.ofFn ts).fill g)))
    | _, _, .F ⟨f, rfl⟩, s, i, e, env, _, args, ts, hts => by
        change (B.w s).canonFunc f (fun k => args (Fin.cast rfl k)) = _
        rw [Term.mono_fill, Spine.mono_ofFn,
          show (fun k => args (Fin.cast rfl k)) = fun k => (B.w s).cls i (Term.mono e (ts k)) from
            funext fun k => hts k,
          BWorld.canonFunc_cls]
        rfl
    | _, _, .eval g t, s, i, e, env, hag, args, ts, hts => by
        change Model.interpFunc env g (Fin.cons (Model.interp env t) args) = _
        have h0 : Model.interp env t = (B.w s).cls i (Term.mono e t) :=
          (interp_canon t hag).trans (rden_var_mono e t)
        rw [interpFunc_canon g hag (Fin.cons (Model.interp env t) args) (Fin.cons t ts)
          (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
        rfl
    termination_by _ _ g => (tsz .Var, g.size)
    decreasing_by
      all_goals simp only [Prod.lex_def, Func.size, tsz, true_and]
      all_goals omega

  /-- ⭐In an environment agreeing with the canonical one, a term's value is its denotation. -/
  theorem interp_canon : ∀ {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
      {s : B.W} {i : ℕ} {e : Γ.Le ((B.w s).ctx i)} {env : B.model.Env Γ s},
      Model.Env.Agree e env (B.canonEnv s i) →
      Model.interp env t = B.toDom A s (B.rden s i e t) (definable_rden e t)
    | _, _, _, .var v hv, s, i, e, env, hag => by
        change env.ref v hv = _
        rw [Model.Env.ref_agree hag v hv, canonEnv_ref]
        rfl
    | _, _, _, .func f, _, _, _, env, hag => by
        change Model.interpFunc env f Fin.elim0 = _
        exact interpFunc_canon f hag Fin.elim0 Fin.elim0 (fun k => k.elim0)
    | _, _, _, .unit, _, _, _, _, _ => rfl
    | _, _, _, .pair t u, _, _, _, _, hag => Prod.ext (interp_canon t hag) (interp_canon u hag)
    | _, _, _, .boxtm t, s, i, e, env, hag => by
        apply B.model.nec_inj
        funext a
        rw [Model.box_beta]
        change Model.interp (env.boxPush a) t = B.toDom _ a.1 (B.rden s i e (.boxtm t) a) _
        rw [toDom_congr (rden_boxtm_net e t a (R_of_RT a.2.down)) _ (definable_rden _ _)]
        have hag' := Model.Env.boxPush_agree hag a
        rw [boxPush_canon] at hag'
        rw [← Model.interp_mono hag' t, ← Model.interp_subst _ _ (B.arCoh (R_of_RT a.2.down) i),
          Term.subst_mono]
        exact interp_canon _ (fun _ _ _ => rfl)
    | _, _, _, .diatm x hx t, s, i, e, env, hag => by
        obtain ⟨X, hr⟩ := hx
        refine B.posEval_injective (?_ : B.model.posEval _ = B.model.posEval _)
        rw [Model.dia_beta env ⟨X, hr⟩ hr t]
        have hpq₀ : env.ref x hr = (B.canonEnv s i).ref x (e.ref hr) :=
          Model.Env.ref_agree hag x hr
        have hpq := hpq₀.trans (canonEnv_ref s i x (e.ref hr))
        refine Model.posSec_ext hpq _ _ fun a => ?_
        have hm : a.1 ∈ (B.model.posEval ((B.canonEnv s i).ref x (e.ref hr))).1 := hpq₀ ▸ a.2
        have hag' := Model.Env.diaPush_agree hag hr a hm
        rw [diaPush_canon] at hag'
        rw [← Model.interp_mono hag' t]
        have hmx : a.1 ∈ B.extent s x := canonEnv_extent s i (e.ref hr) ▸ hm
        rw [← Model.interp_subst _ _ (B.arXCoh (kd_of_extent hmx) i ⟨X, e.ref hr⟩), Term.subst_mono]
        refine (interp_canon _ (fun _ _ _ => rfl)).trans (toDom_congr ?_ _ _)
        exact (rden_diatm_net e ⟨X, hr⟩ t ⟨a.1, hmx⟩ (kd_of_extent hmx)).symm
    termination_by _ A _ t => (tsz A, t.size)
    decreasing_by
      all_goals simp only [Prod.lex_def, Term.size, tsz, true_and]
      all_goals omega
end

end BData

end BArrow

end V12M
