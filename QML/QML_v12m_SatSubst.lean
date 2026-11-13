import QML.QML_v12m_SemSubst

/-!
# QML v12m — semantics of substitution (formulas)

⭐`sat_subst`: a substituted formula holds in an environment exactly when the formula holds in the
substituted environment.  The binder case uses `substEnv_under` (the substituted environment of
`θ.under` is the substituted environment of `θ`, extended); the modal cases use `substEnv_box`
and `substEnv_dia`.
-/

namespace V12M

variable [ModalSys]

omit [ModalSys] in
theorem Ctx.NoProjLast.insert {Γ : Ctx} (h : Γ.NoProjLast) (r : Root) (T : VarType) :
    (Γ.insert r T).NoProjLast := by
  intro v U hv
  by_cases hvr : v = .root r
  · subst hvr
    rfl
  · exact h v U (Ctx.insert_ne_some hv hvr)

omit [ModalSys] in
theorem Ctx.NoProjLast.optIn {Γ : Ctx} (h : Γ.NoProjLast) (y : VarSymb) :
    (Γ.optIn y).NoProjLast := by
  intro v T hv
  by_cases hc : v = .step y .dia
  · subst hc
    rfl
  · rw [Ctx.optIn_ne hc] at hv
    exact h v T hv

theorem Ctx.NoProjLast.optInT {Γ : Ctx} (h : Γ.NoProjLast) (y : VarSymb) :
    (Γ.optInT y).NoProjLast := by
  intro v T hv
  by_cases hc : v = .step y .at
  · subst hc
    rfl
  · rw [Ctx.optInT_ne hc] at hv
    exact h v T hv

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

omit [ModalSys] in
theorem part_get_eq {α : Type*} {p q : Part α} (h : p = q) (hp : p.Dom) :
    p.get hp = q.get (h ▸ hp) := by
  subst h
  rfl

/-! ## Environments respecting their opened witnesses -/

/-! ## Into the view of a witness -/

/-- The content of a witness entry, read in the view of its image, is the entry's value. -/
theorem entryVal_optBody {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {z : VarSymb}
    {Z : VarType} (hz : Δ.wit z = some Z) (hd : (env.wit z Z hz).Dom) :
    ∀ {e : WitE σ Δ} {X : VarType} (he : e.OkW X) (hw : e.idxAlong [] = z)
      (hd' : (witVal env e he).Dom),
      entryVal (env.optPush z hz hd) (e.optBody z)
          (WitE.okRef_optBody he hw) = (witVal env e he).get hd'
  | .ren w', X, he, hw, hd' => by
      have hw' : w' = z := hw
      subst hw'
      have hXZ : X = Z := Option.some.inj (he.symm.trans hz)
      subst hXZ
      change Env.ref (env.optPush w' hz hd) (.step w' .dia)
        (WitE.okRef_optBody (X := X) (e := WitE.ren w') he rfl) = (env.wit w' X he).get hd'
      rw [Env.ref, dif_neg (by decide : ¬ Step.dia.isStruct = true)]
      change (if hv : VarSymb.step w' .dia = .step w' .dia then _ else _) = _
      rw [dif_pos rfl]
  | .tm w' b, X, he, hw, hd' => by
      have hw' : w' = z := hw
      subst hw'
      obtain ⟨⟨Z', hZ'⟩, rfl⟩ := he
      rw [part_get_eq (witVal_tm env hz b _) hd']
      rw [entryVal_congr _ (show (WitE.tm w' b : WitE σ Δ).optBody w' =
        SubE.tm (Term.mono (Ctx.Le.refl _) b) from dif_pos rfl) _ rfl]
      change interp _ (Term.mono (Ctx.Le.refl _) b) = interp _ b
      rw [Term.mono_refl]
  | .hide, _, he, _, _ => False.elim he

theorem witVal_dom {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {z : VarSymb} {Z : VarType}
    (hz : Δ.wit z = some Z) :
    ∀ {e : WitE σ Δ} {X : VarType} (he : e.OkW X) (_hw : e.idxAlong [] = z),
      (witVal env e he).Dom ↔ (env.wit z Z hz).Dom
  | .ren w', X, he, hw => by
      have hw' : w' = z := hw
      subst hw'
      have hXZ : X = Z := Option.some.inj (he.symm.trans hz)
      subst hXZ
      exact Iff.rfl
  | .tm w' b, X, he, hw => by
      have hw' : w' = z := hw
      subst hw'
      obtain ⟨_, rfl⟩ := he
      rw [witVal_tm env hz b]
      exact Iff.rfl
  | .hide, _, he, _ => False.elim he

/-- ⭐**A substituted witness is its entry's value**, under coherence: an opened witness is read
    off its content (`Model.substEnv`), and its entry goes to an opened witness
    (`Subst.Coh.openedTo`) whose content the entry's content is (`Subst.Coh.opened`). -/
theorem substEnv_wit {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hnp : Γ.NoProjLast) (env : M.Env Δ w)
    (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X)
    (h : (θ.wit y).OkW X) : (substEnv θ hθ hnp env).wit y X hy = witVal env (θ.wit y) h := by
  by_cases ho : Γ (.step y .dia) = some X
  · obtain ⟨Z, hZ, hZd⟩ := hc.openedTo hO y X _ hy ho rfl
    obtain ⟨hdz, -⟩ := env.opened _ Z hZ hZd
    have hdom := (witVal_dom env hZ h rfl).mpr hdz
    rw [(substEnv θ hθ hnp env).wit_opened hy ho]
    refine (Part.eq_some_iff.mpr ⟨hdom, ?_⟩).symm
    rw [← entryVal_optBody env hZ hdz h rfl hdom,
      ← entryVal_congr _ (hc.opened hO y X _ hy ho rfl) (SubE.okRef_mono _ (hθ _ X rfl ho)) _]
    exact entryVal_mono (Env.agree_optPush env hZ hdz) _ _
  · exact substEnv_wit_of_not θ hθ hnp env hy ho h

/-- ⭐**Into the view of a witness**: the substituted environment of `θ.optIn` is the substituted
    environment's view of the witness. -/
theorem substEnv_optIn {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) (hO : ModalSys.Opt = true)
    {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X) {z : VarSymb} {Z : VarType}
    (hw : (θ.wit y).idxAlong [] = z) (hz : Δ.wit z = some Z) (hd : (env.wit z Z hz).Dom)
    (hd' : ((substEnv θ hθ hnp env).wit y X hy).Dom) :
    substEnv (θ.optIn y z) (Subst.ok_optIn hθ hO hy hw) (hnp.optIn y)
        (env.optPush z hz hd) =
      (substEnv θ hθ hnp env).optPush y hy hd' := by
  refine Env.ext_val (fun v T hv => ?_) (fun y' X' hy' hn => ?_)
  swap
  · have hne : y' ≠ y := fun he => by
      subst he
      exact hn (Ctx.optIn_content (Option.some.inj (hy.symm.trans hy') ▸ hy))
    have hdne : VarSymb.step y' .dia ≠ .step y .dia := fun he => hne (by cases he; rfl)
    have hn' : Γ (.step y' .dia) ≠ some X' := by rwa [Ctx.optIn_ne hdne] at hn
    rw [substEnv_wit_substWit _ _ _ _ hy' hn]
    change _ = (substEnv θ hθ hnp env).wit y' X' hy'
    rw [substEnv_wit_substWit θ hθ hnp env hy' hn']
    exact substWit_mono (Env.agree_optPush env hz hd) (fun _ _ _ => rfl) (fun _ => rfl) _ _
  by_cases hcv : v = .step y .dia
  · subst hcv
    have hXT : X = T := by
      rw [Ctx.optIn_content hy] at hv
      exact Option.some.inj hv
    subst hXT
    change entryVal _ (if VarSymb.step y .dia = .step y .dia then (θ.wit y).optBody z
      else (θ (.step y .dia)).mono (Ctx.le_optIn Δ z)) _ =
      (if hv' : VarSymb.step y .dia = .step y .dia then _ else _)
    rw [dif_pos rfl]
    rw [entryVal_congr _ (if_pos rfl) _ (WitE.okRef_optBody (hθ.wit hO y X hy) hw)]
    have hsw := substEnv_wit θ hθ hc hnp env hO hy (hθ.wit hO y X hy)
    have hd'' : (witVal env (θ.wit y) (hθ.wit hO y X hy)).Dom := hsw ▸ hd'
    rw [entryVal_optBody env hz hd (hθ.wit hO y X hy) hw hd'']
    change _ = ((substEnv θ hθ hnp env).wit y X hy).get hd'
    exact part_get_eq (p := witVal env (θ.wit y) (hθ.wit hO y X hy)) hsw.symm hd''
  · have hv' : Γ v = some T := by rwa [Ctx.optIn_ne hcv] at hv
    change entryVal _ (if v = .step y .dia then (θ.wit y).optBody z
      else (θ v).mono (Ctx.le_optIn Δ z)) _ = (if hv'' : v = .step y .dia then _ else _)
    rw [dif_neg hcv]
    rw [entryVal_congr _ (if_neg hcv) _ (SubE.okRef_mono _ (hθ v T (hnp v T hv') hv'))]
    exact entryVal_mono (Env.agree_optPush env hz hd) _ _

theorem substEnv_under {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) {d d' : ℕ} (T : VarType)
    (h : Δ (.root (.bnd d')) = none) (o : M.frame.Dom T w) :
    substEnv (θ.under d d' T h) (Subst.ok_under hθ T h) (hnp.insert (.bnd d) T)
        (env.extend (.bnd d') o) =
      (substEnv θ hθ hnp env).extend (.bnd d) o := by
  refine Env.ext_val (fun v U hv => ?_) (fun y X hy hn => ?_)
  swap
  · have hn' : Γ (.step y .dia) ≠ some X := by
      rwa [Ctx.insert_ne (fun he => by cases he)] at hn
    rw [substEnv_wit_substWit _ _ _ _ hy hn]
    change _ = (substEnv θ hθ hnp env).wit y X hy
    rw [substEnv_wit_substWit θ hθ hnp env hy hn']
    exact substWit_mono (Env.agree_extend env h o) (fun _ _ _ => rfl) (fun _ => rfl) _ _
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [Env.extend_root (substEnv θ hθ hnp env) _ o hv]
    exact (entryVal_congr _
      (show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl) _
      (Ctx.ref_insert_root Δ _ T)).trans (Env.extend_root env _ o (Ctx.ref_insert_root Δ _ T))
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
    rw [Env.extend_ne (substEnv θ hθ hnp env) _ o hv hvr hv']
    exact (entryVal_congr _
      (show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr) _
      (SubE.okRef_mono _ (hθ v U (hnp v U hv') hv'))).trans
      (entryVal_mono (Env.agree_extend env h o) _ _)

/-! ## Into the identity view (M2, docs §12.30) -/

/-- `Opt` and T are not both on, or the environment respects its identity contents.  (While
    M2 step 3 is in progress it falls back on `ModalSys.optStage`.) -/
macro "witT_off" : tactic => `(tactic| first
  | exact fun _ hO => absurd hO (by rw [show ModalSys.Opt = false by opt_off]; decide)
  | exact fun hT hO => (by have := ModalSys.optStage hO; simp [hT] at this))

/-- A possible object's entry is present at the identity arrow where its image is. -/
theorem posPart_entryVal_dom (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) {Δ : Ctx}
    {w : M.frame.W} (env : M.Env Δ w) {z : VarSymb} {Z : VarType} (hz : Δ.witT z = some Z) :
    ∀ {e : SubE σ Δ} {X : VarType} (he : e.OkRef (.VTypeDia X)) (_hw : e.idxAlong [] = z),
      (posPart (entryVal env e he) (M.frame.reflAcc hT w)).Dom ↔ (env.witT z hz).Dom
  | .ren w', X, he, hw => by
      have hw' : w' = z := hw
      subst hw'
      have hXZ : X = Z := Option.some.inj ((Ctx.witT_of hT hO he).symm.trans hz)
      subst hXZ
      exact Iff.rfl
  | .tm s, X, he, hw => by
      cases s with
      | diatm x hx b =>
          have hxz : x = z := hw
          subst hxz
          cases he
          obtain ⟨Y, hr⟩ := id hx
          have hYZ : Y = Z := Option.some.inj ((Ctx.witT_of hT hO hr).symm.trans hz)
          subst hYZ
          change _ ∈ (M.posEval (interp env (Term.diatm x hx b))).1 ↔
            _ ∈ (M.posEval (env.ref x hr)).1
          rw [dia_beta env hx hr b]
      | _ => cases he
  | .hide, _, he, _ => False.elim he

/-- ⭐**The content at the identity arrow of a substituted possible object** is the entry's value
    there: a renaming's identity content, or a possible term's body read at the current world
    (`dia_beta`, collapsed onto the identity view). -/
theorem entryVal_atBody (hT : ModalSys.T = true) (hO : ModalSys.Opt = true) {Δ : Ctx}
    {w : M.frame.W} (env : M.Env Δ w) (hop : env.OpenedT) {z : VarSymb} {Z : VarType}
    (hz : Δ.witT z = some Z) (hd : (env.witT z hz).Dom) :
    ∀ {e : SubE σ Δ} {X : VarType} (he : e.OkRef (.VTypeDia X)) (hw : e.idxAlong [] = z)
      (hd' : (posPart (entryVal env e he) (M.frame.reflAcc hT w)).Dom),
      entryVal (env.optPushT z hz hd) (e.atBody z) (SubE.okRef_atBody hT hO he hw) =
        (posPart (entryVal env e he) (M.frame.reflAcc hT w)).get hd'
  | .ren w', X, he, hw, hd' => by
      have hw' : w' = z := hw
      subst hw'
      have hXZ : X = Z := Option.some.inj ((Ctx.witT_of hT hO he).symm.trans hz)
      subst hXZ
      change Env.ref (env.optPushT w' hz hd) (.step w' .at)
        ((Ctx.ref_nonproj _ rfl).trans (Ctx.optInT_content hz)) = _
      rw [Env.ref, dif_neg (by decide : ¬ Step.at.isStruct = true)]
      change (if hv : VarSymb.step w' .at = .step w' .at then _ else _) = _
      rw [dif_pos rfl]
      rfl
  | .tm s, X, he, hw, hd' => by
      cases s with
      | diatm x hx b =>
          have hxz : x = z := hw
          subst hxz
          cases he
          obtain ⟨Y, hr⟩ := id hx
          have hYZ : Y = Z := Option.some.inj ((Ctx.witT_of hT hO hr).symm.trans hz)
          subst hYZ
          have hdb := dia_beta env hx hr b
          have hm : M.frame.reflAcc hT w ∈ (M.posEval (env.ref x hr)).1 := by
            have h₀ : M.frame.reflAcc hT w ∈ (M.posEval (interp env (Term.diatm x hx b))).1 := hd'
            rw [hdb] at h₀
            exact h₀
          rw [entryVal_congr _ (show (SubE.tm (Term.diatm x hx b) : SubE σ Δ).atBody x =
            SubE.tm (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) b)
            from dif_pos ⟨hT, hO, rfl⟩) _ rfl]
          change interp (env.optPushT x hz hd) (Term.collapse _ b) =
            (M.posEval (interp env (Term.diatm x hx b))).2 ⟨_, hd'⟩
          rw [interp_collapse (Env.collapseAgree_diaIn_optInT hT hO env hop hr hm hd) b]
          exact (sec_apply hdb ⟨_, hd'⟩ hm).symm
      | _ => cases he
  | .hide, _, he, _, _ => False.elim he

/-- ⭐**Into the identity view**: the substituted environment of `θ.optInT` is the substituted
    environment's identity view. -/
theorem substEnv_optInT {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hnp : Γ.NoProjLast) (env : M.Env Δ w) (hop : env.OpenedT)
    {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X) (hw : (θ.at y).idxAlong [] = ι y)
    {Z : VarType} (hz : Δ.witT (ι y) = some Z) (hd : (env.witT (ι y) hz).Dom)
    (hd' : ((substEnv θ hθ hnp env).witT y hy).Dom) :
    substEnv (θ.optInT y (ι y)) (Subst.ok_optInT hθ hy hw) (hnp.optInT y)
        (env.optPushT (ι y) hz hd) =
      (substEnv θ hθ hnp env).optPushT y hy hd' := by
  obtain ⟨hT, hO, hr⟩ := Ctx.witT_spec hy
  refine Env.ext_val (fun v T hv => ?_) (fun y' X' hy' hn => ?_)
  swap
  · have hdne : VarSymb.step y' .dia ≠ .step y .at := fun he => by cases he
    have hn' : Γ (.step y' .dia) ≠ some X' := by rwa [Ctx.optInT_ne hdne] at hn
    rw [substEnv_wit_substWit _ _ _ _ hy' hn]
    change _ = (substEnv θ hθ hnp env).wit y' X' hy'
    rw [substEnv_wit_substWit θ hθ hnp env hy' hn']
    exact substWit_mono (Env.agree_optPushT env hop hz hd) (fun _ _ _ => rfl) (fun _ => rfl) _ _
  by_cases hcv : v = .step y .at
  · subst hcv
    have hXT : X = T := by
      rw [Ctx.optInT_content hy] at hv
      exact Option.some.inj hv
    subst hXT
    change entryVal _ (if VarSymb.step y .at = .step y .at then (θ.at y).atBody (ι y)
      else (θ (.step y .at)).mono (Ctx.le_optInT Δ (ι y))) _ =
      (if hv' : VarSymb.step y .at = .step y .at then _ else _)
    rw [dif_pos rfl]
    rw [entryVal_congr _ (if_pos rfl) _ (SubE.okRef_atBody hT hO (Subst.okRef_at hθ hr) hw)]
    have hW : (substEnv θ hθ hnp env).witT y hy =
        posPart (entryVal env (θ.at y) (Subst.okRef_at hθ hr)) (M.frame.reflAcc hT w) := by
      unfold Env.witT
      rw [substEnv_ref θ hθ hnp env y]
    have hd'' : (posPart (entryVal env (θ.at y) (Subst.okRef_at hθ hr))
        (M.frame.reflAcc hT w)).Dom := hW ▸ hd'
    rw [entryVal_atBody hT hO env hop hz hd (Subst.okRef_at hθ hr) hw hd'']
    exact part_get_eq hW.symm hd''
  · have hv' : Γ v = some T := by rwa [Ctx.optInT_ne hcv] at hv
    change entryVal _ (if v = .step y .at then (θ.at y).atBody (ι y)
      else (θ v).mono (Ctx.le_optInT Δ (ι y))) _ = (if hv'' : v = .step y .at then _ else _)
    rw [dif_neg hcv]
    rw [entryVal_congr _ (if_neg hcv) _ (SubE.okRef_mono _ (hθ v T (hnp v T hv') hv'))]
    exact entryVal_mono (Env.agree_optPushT env hop hz hd) _ _

theorem relSat_subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hnp : Γ.NoProjLast) {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {n : ℕ} (ρ : Rel σ Γ n) (args : Fin n → M.frame.D w),
      relSat env (Rel.subst ι θ hθ hc ρ) args ↔ relSat (substEnv θ hθ hnp env) ρ args
  | _, .R _, _ => Iff.rfl
  | _, .eval ρ t, args => by
      change relSat env (Rel.subst ι θ hθ hc ρ)
          (Fin.cons (interp env (Term.subst ι θ hθ hc t)) args) ↔
        relSat (substEnv θ hθ hnp env) ρ (Fin.cons (interp (substEnv θ hθ hnp env) t) args)
      rw [interp_subst θ hθ hc hnp env t]
      exact relSat_subst θ hθ hc hnp env ρ _

/-- ⭐**Substitution lemma** for formulas. -/
theorem sat_subst : ∀ {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hnp : Γ.NoProjLast) {w : M.frame.W} (env : M.Env Δ w) (φ : WFF σ Γ d)
    (_hop : ModalSys.T = true → ModalSys.Opt = true → env.OpenedT := by witT_off),
    M.sat env (WFF.subst ι θ hθ hc hΓ hΔ φ) ↔ M.sat (substEnv θ hθ hnp env) φ
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .atom ρ, _ =>
      relSat_subst θ hθ hc hnp env ρ Fin.elim0
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .eq t s, _ => by
      change interp env (Term.subst _ θ hθ hc t) = interp env (Term.subst _ θ hθ hc s) ↔ _
      rw [interp_subst θ hθ hc hnp env t, interp_subst θ hθ hc hnp env s]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .top, _ => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .bot, _ => Iff.rfl
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .and φ ψ, hop =>
      and_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ hop) (sat_subst θ hθ hc hΓ hΔ hnp env ψ hop)
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .or φ ψ, hop =>
      or_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ hop) (sat_subst θ hθ hc hΓ hΔ hnp env ψ hop)
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .imp φ ψ, hop =>
      imp_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ hop) (sat_subst θ hθ hc hΓ hΔ hnp env ψ hop)
  | _, _, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .all T φ, hop =>
      forall_congr' fun o =>
        (sat_subst (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
          (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T)
          (hnp.insert (.bnd d) T) (env.extend (.bnd d') o) φ
          fun hT hO => (hop hT hO).extend hΔ.root o).trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_under θ hθ hnp env T hΔ.root o)))
  | _, _, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .ex T φ, hop =>
      exists_congr fun o =>
        (sat_subst (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
          (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T)
          (hnp.insert (.bnd d) T) (env.extend (.bnd d') o) φ
          fun hT hO => (hop hT hO).extend hΔ.root o).trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_under θ hθ hnp env T hΔ.root o)))
  | _, Γ, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .box φ, hop =>
      forall_congr' fun w' =>
        (sat_subst θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn
          (Ctx.noProjLast_boxIn Γ) (env.boxPush w') φ fun _ _ => env.openedT_boxPush w').trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_box θ hθ hnp env w')))
  | ι, Γ, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .dia x hx φ, hop => by
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      constructor
      · rintro ⟨Y, hr₁, w', hsat⟩
        obtain ⟨X, hr⟩ := hx
        have hE : (M.posEval (env.ref (ι x) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref x hr)).1 := by
          rw [substEnv_ref θ hθ hnp env x hr, entryVal_dia_ext env _ hw hr₁]
        refine ⟨X, hr, ⟨w'.1, hE ▸ w'.2⟩, ?_⟩
        rw [← substEnv_dia θ hθ hnp env ⟨X, hr⟩ hr hr₁ hw w' _]
        exact (sat_subst (θ.dia x (ι x)) (Subst.ok_dia hθ ⟨X, hr⟩ hw)
          (Subst.coh_dia hθ hc ⟨X, hr⟩) (hΓ.diaIn x) (hΔ.diaIn (ι x))
          (Ctx.noProjLast_diaIn Γ x) (env.diaPush (ι x) hr₁ w') φ
          fun _ _ => env.openedT_diaPush _ _ _).mp hsat
      · rintro ⟨X, hr, w₂, hsat⟩
        obtain ⟨Y, hr₁⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hw
        have hE : (M.posEval (env.ref (ι x) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref x hr)).1 := by
          rw [substEnv_ref θ hθ hnp env x hr, entryVal_dia_ext env _ hw hr₁]
        refine ⟨Y, hr₁, ⟨w₂.1, hE.symm ▸ w₂.2⟩, ?_⟩
        refine (sat_subst (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hΓ.diaIn x) (hΔ.diaIn (ι x)) (Ctx.noProjLast_diaIn Γ x)
          (env.diaPush (ι x) hr₁ ⟨w₂.1, hE.symm ▸ w₂.2⟩) φ
          fun _ _ => env.openedT_diaPush _ _ _).mpr ?_
        rw [substEnv_dia θ hθ hnp env hx hr hr₁ hw ⟨w₂.1, hE.symm ▸ w₂.2⟩ w₂.2]
        exact hsat
  | ι, Γ, Δ, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .optx hO .arrow y hy φ, hop => by
      obtain ⟨X, hX⟩ := hy
      have hw : (θ.wit y).idxAlong [] = ι y := hc.wit hO y X hX []
      obtain ⟨Z, hZ⟩ := WitE.wit_of (hθ.wit hO y X hX) hw
      have hdom : ((substEnv θ hθ hnp env).wit y X hX).Dom ↔ (env.wit (ι y) Z hZ).Dom := by
        rw [substEnv_wit θ hθ hc hnp env hO hX (hθ.wit hO y X hX)]
        exact witVal_dom env hZ (hθ.wit hO y X hX) hw
      constructor
      · rintro ⟨Z', hZ', hd, hsat⟩
        have hZZ : Z = Z' := Option.some.inj (hZ.symm.trans hZ')
        subst hZZ
        refine ⟨X, hX, hdom.mpr hd, ?_⟩
        rw [← substEnv_optIn θ hθ hc hnp env hO hX hw hZ hd (hdom.mpr hd)]
        exact (sat_subst (θ.optIn y (ι y)) (Subst.ok_optIn hθ hO hX hw)
          (Subst.coh_optIn hθ hc hO hX) (hΓ.optIn y) (hΔ.optIn (ι y)) (hnp.optIn y)
          (env.optPush (ι y) hZ hd) φ fun hT hO' => (hop hT hO').optPush hZ hd).mp hsat
      · rintro ⟨X', hX', hd', hsat⟩
        have hXX : X = X' := Option.some.inj (hX.symm.trans hX')
        subst hXX
        refine ⟨Z, hZ, hdom.mp hd', ?_⟩
        refine (sat_subst (θ.optIn y (ι y)) (Subst.ok_optIn hθ hO hX hw)
          (Subst.coh_optIn hθ hc hO hX) (hΓ.optIn y) (hΔ.optIn (ι y)) (hnp.optIn y)
          (env.optPush (ι y) hZ (hdom.mp hd')) φ
          fun hT hO' => (hop hT hO').optPush hZ _).mpr ?_
        rw [substEnv_optIn θ hθ hc hnp env hO hX hw hZ (hdom.mp hd') hd']
        exact hsat
  | ι, Γ, Δ, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .optx hO .ident y hy φ, hop => by
      obtain ⟨X, hX⟩ := hy
      obtain ⟨hT, -, hr⟩ := Ctx.witT_spec hX
      have hw : (θ.at y).idxAlong [] = ι y := hc y _ hr []
      obtain ⟨Z, hZ₀⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hw
      have hZ : Δ.witT (ι y) = some Z := Ctx.witT_of hT hO hZ₀
      have hop' := hop hT hO
      have hW : (substEnv θ hθ hnp env).witT y hX =
          posPart (entryVal env (θ.at y) (Subst.okRef_at hθ hr)) (M.frame.reflAcc hT _) := by
        unfold Env.witT
        rw [substEnv_ref θ hθ hnp env y]
      have hdom : ((substEnv θ hθ hnp env).witT y hX).Dom ↔ (env.witT (ι y) hZ).Dom := by
        rw [hW]
        exact posPart_entryVal_dom hT hO env hZ (Subst.okRef_at hθ hr) hw
      constructor
      · rintro ⟨Z', hZ', hd, hsat⟩
        obtain rfl : Z = Z' := Option.some.inj (hZ.symm.trans hZ')
        refine ⟨X, hX, hdom.mpr hd, ?_⟩
        rw [← substEnv_optInT θ hθ hnp env hop' hX hw hZ hd (hdom.mpr hd)]
        exact (sat_subst (θ.optInT y (ι y)) (Subst.ok_optInT hθ hX hw)
          (Subst.coh_optInT hθ hc hX) (hΓ.optInT y) (hΔ.optInT (ι y)) (hnp.optInT y)
          (env.optPushT (ι y) hZ hd) φ fun _ _ => hop'.optPushT hZ hd).mp hsat
      · rintro ⟨X', hX', hd', hsat⟩
        obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
        refine ⟨Z, hZ, hdom.mp hd', ?_⟩
        refine (sat_subst (θ.optInT y (ι y)) (Subst.ok_optInT hθ hX hw)
          (Subst.coh_optInT hθ hc hX) (hΓ.optInT y) (hΔ.optInT (ι y)) (hnp.optInT y)
          (env.optPushT (ι y) hZ (hdom.mp hd')) φ fun _ _ => hop'.optPushT hZ _).mpr ?_
        rw [substEnv_optInT θ hθ hnp env hop' hX hw hZ (hdom.mp hd') hd']
        exact hsat
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .here hT s t, _ => by
      change Model.Realised hT (interp env (Term.subst _ θ hθ hc s))
        (interp env (Term.subst _ θ hθ hc t)) ↔ _
      rw [interp_subst θ hθ hc hnp env s, interp_subst θ hθ hc hnp env t]
      exact Iff.rfl
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .back hB L s t, _ => by
      change Model.Backs L (interp env (Term.subst _ θ hθ hc s))
        (interp env (Term.subst _ θ hθ hc t)) ↔ _
      rw [interp_subst θ hθ hc hnp env s, interp_subst θ hθ hc hnp env t]
      exact Iff.rfl
  | _, Γ, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .retS hB S t Φ, _ =>
      exists_congr fun a => exists_congr fun e =>
        and_congr
          ((sat_subst (θ.box.under d d' _ hΔ.boxIn.root)
              (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
              (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
              (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) ((Ctx.noProjLast_boxIn Γ).insert (.bnd d) _)
              ((env.boxPush a).extend (.bnd d') e) Φ).trans
            (iff_of_eq (congrArg (fun en => M.sat en Φ)
              ((substEnv_under θ.box (Subst.ok_box hθ) (Ctx.noProjLast_boxIn Γ) (env.boxPush a)
                  _ hΔ.boxIn.root e).trans
                (congrArg (fun en => Env.extend en (.bnd d) e) (substEnv_box θ hθ hnp env a))))))
          (by rw [interp_subst θ hθ hc hnp env t])
  | ι, Γ, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .retxS hB y hy S t Φ, _ => by
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      have hr₀ := (hΔ.diaIn (ι y)).root
      constructor
      · rintro ⟨Y, hr₁, a, e, hsat, hr⟩
        obtain ⟨X, hrX⟩ := hy
        have hE : (M.posEval (env.ref (ι y) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref y hrX)).1 := by
          rw [substEnv_ref θ hθ hnp env y hrX, entryVal_dia_ext env _ hw hr₁]
        refine ⟨X, hrX, ⟨a.1, hE ▸ a.2⟩, e, ?_, ?_⟩
        · rw [← substEnv_dia θ hθ hnp env ⟨X, hrX⟩ hrX hr₁ hw a _,
            ← substEnv_under (θ.dia y (ι y)) (Subst.ok_dia hθ ⟨X, hrX⟩ hw)
              (Ctx.noProjLast_diaIn Γ y) (env.diaPush (ι y) hr₁ a) _ hr₀ e]
          exact (sat_subst ((θ.dia y (ι y)).under d d' _ hr₀)
            (Subst.ok_under (Subst.ok_dia hθ ⟨X, hrX⟩ hw) _ hr₀)
            (Subst.coh_under (Subst.ok_dia hθ ⟨X, hrX⟩ hw) (Subst.coh_dia hθ hc ⟨X, hrX⟩)
              (hΓ.diaIn y) _ hr₀)
            ((hΓ.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _)
            ((Ctx.noProjLast_diaIn Γ y).insert (.bnd d) _)
            ((env.diaPush (ι y) hr₁ a).extend (.bnd d') e) Φ).mp hsat
        · rw [interp_subst θ hθ hc hnp env t] at hr
          exact hr
      · rintro ⟨X, hrX, a, e, hsat, hr⟩
        obtain ⟨Y, hr₁⟩ := SubE.ref_witness (Subst.okRef_at hθ hrX) hw
        have hE : (M.posEval (env.ref (ι y) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref y hrX)).1 := by
          rw [substEnv_ref θ hθ hnp env y hrX, entryVal_dia_ext env _ hw hr₁]
        refine ⟨Y, hr₁, ⟨a.1, hE.symm ▸ a.2⟩, e, ?_, ?_⟩
        · refine (sat_subst ((θ.dia y (ι y)).under d d' _ hr₀)
            (Subst.ok_under (Subst.ok_dia hθ hy hw) _ hr₀)
            (Subst.coh_under (Subst.ok_dia hθ hy hw) (Subst.coh_dia hθ hc hy) (hΓ.diaIn y) _ hr₀)
            ((hΓ.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _)
            ((Ctx.noProjLast_diaIn Γ y).insert (.bnd d) _)
            ((env.diaPush (ι y) hr₁ ⟨a.1, hE.symm ▸ a.2⟩).extend (.bnd d') e) Φ).mpr ?_
          rw [substEnv_under (θ.dia y (ι y)) (Subst.ok_dia hθ hy hw) (Ctx.noProjLast_diaIn Γ y)
              (env.diaPush (ι y) hr₁ ⟨a.1, hE.symm ▸ a.2⟩) _ hr₀ e,
            substEnv_dia θ hθ hnp env hy hrX hr₁ hw ⟨a.1, hE.symm ▸ a.2⟩ a.2]
          exact hsat
        · rw [interp_subst θ hθ hc hnp env t]
          exact hr
  | _, Γ, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .link hV hF t Φ, _ =>
      forall_congr' fun a => by
        rw [interp_subst θ hθ hc hnp env t]
        exact (sat_subst (θ.box.under d d' _ hΔ.boxIn.root)
            (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
            (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
            (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) ((Ctx.noProjLast_boxIn Γ).insert (.bnd d) _)
            ((env.boxPush a).extend (.bnd d') _) Φ).trans
          (iff_of_eq (congrArg (fun en => M.sat en Φ)
            ((substEnv_under θ.box (Subst.ok_box hθ) (Ctx.noProjLast_boxIn Γ) (env.boxPush a)
                _ hΔ.boxIn.root _).trans
              (congrArg (fun en => Env.extend en (.bnd d) _) (substEnv_box θ hθ hnp env a)))))
  | ι, Γ, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .linkx hV hF y hy t Φ, _ => by
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      have hr₀ := (hΔ.diaIn (ι y)).root
      constructor
      · rintro ⟨Y, hr₁, a, hsat⟩
        obtain ⟨X, hrX⟩ := hy
        have hE : (M.posEval (env.ref (ι y) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref y hrX)).1 := by
          rw [substEnv_ref θ hθ hnp env y hrX, entryVal_dia_ext env _ hw hr₁]
        refine ⟨X, hrX, ⟨a.1, hE ▸ a.2⟩, ?_⟩
        rw [interp_subst θ hθ hc hnp env t] at hsat
        have h₁ := (sat_subst ((θ.dia y (ι y)).under d d' _ hr₀)
          (Subst.ok_under (Subst.ok_dia hθ ⟨X, hrX⟩ hw) _ hr₀)
          (Subst.coh_under (Subst.ok_dia hθ ⟨X, hrX⟩ hw) (Subst.coh_dia hθ hc ⟨X, hrX⟩)
            (hΓ.diaIn y) _ hr₀)
          ((hΓ.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _)
          ((Ctx.noProjLast_diaIn Γ y).insert (.bnd d) _)
          ((env.diaPush (ι y) hr₁ a).extend (.bnd d') _) Φ).mp hsat
        rw [substEnv_under (θ.dia y (ι y)) (Subst.ok_dia hθ ⟨X, hrX⟩ hw)
            (Ctx.noProjLast_diaIn Γ y) (env.diaPush (ι y) hr₁ a) _ hr₀ _,
          substEnv_dia θ hθ hnp env ⟨X, hrX⟩ hrX hr₁ hw a _] at h₁
        exact h₁
      · rintro ⟨X, hrX, a, hsat⟩
        obtain ⟨Y, hr₁⟩ := SubE.ref_witness (Subst.okRef_at hθ hrX) hw
        have hE : (M.posEval (env.ref (ι y) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref y hrX)).1 := by
          rw [substEnv_ref θ hθ hnp env y hrX, entryVal_dia_ext env _ hw hr₁]
        refine ⟨Y, hr₁, ⟨a.1, hE.symm ▸ a.2⟩, ?_⟩
        rw [interp_subst θ hθ hc hnp env t]
        refine (sat_subst ((θ.dia y (ι y)).under d d' _ hr₀)
          (Subst.ok_under (Subst.ok_dia hθ hy hw) _ hr₀)
          (Subst.coh_under (Subst.ok_dia hθ hy hw) (Subst.coh_dia hθ hc hy) (hΓ.diaIn y) _ hr₀)
          ((hΓ.diaIn y).insert _) ((hΔ.diaIn (ι y)).insert _)
          ((Ctx.noProjLast_diaIn Γ y).insert (.bnd d) _)
          ((env.diaPush (ι y) hr₁ ⟨a.1, hE.symm ▸ a.2⟩).extend (.bnd d') _) Φ).mpr ?_
        rw [substEnv_under (θ.dia y (ι y)) (Subst.ok_dia hθ hy hw) (Ctx.noProjLast_diaIn Γ y)
            (env.diaPush (ι y) hr₁ ⟨a.1, hE.symm ▸ a.2⟩) _ hr₀ _,
          substEnv_dia θ hθ hnp env hy hrX hr₁ hw ⟨a.1, hE.symm ▸ a.2⟩ a.2]
        exact hsat

end Model

end V12M
