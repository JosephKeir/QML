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
  · exact h v U (by simpa [Ctx.insert, hvr] using hv)

omit [ModalSys] in
theorem Ctx.NoProjLast.optIn {Γ : Ctx} (h : Γ.NoProjLast) (y : VarSymb) :
    (Γ.optIn y).NoProjLast := by
  intro v T hv
  by_cases hc : v = .step y .dia
  · subst hc
    rfl
  · rw [Ctx.optIn_ne hc] at hv
    exact h v T hv

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

omit [ModalSys] in
theorem part_get_eq {α : Type*} {p q : Part α} (h : p = q) (hp : p.Dom) :
    p.get hp = q.get (h ▸ hp) := by
  subst h
  rfl

/-! ## Environments respecting their opened witnesses -/

/-- ⭐An environment **respects its opened witnesses**: where a witness's content is in view, it is
    present and its value is the witness's content.  Every environment the semantics builds does
    (`opened_boxPush`, `opened_diaPush`, `opened_optPush`, `opened_extend`). -/
def Env.Opened {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) : Prop :=
  ∀ z Z (hz : Δ.wit z = some Z) (hv : Δ (.step z .dia) = some Z),
    ∃ hd : (env.wit z Z hz).Dom, env (.step z .dia) Z hv = (env.wit z Z hz).get hd

theorem Env.opened_boxPush {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) (w' : M.frame.Acc w) :
    (env.boxPush w').Opened := fun _ _ _ hv => by cases hv

theorem Env.opened_extend {Δ : Ctx} {w : M.frame.W} {env : M.Env Δ w} (h : env.Opened)
    (r : Root) {T : VarType} (o : M.frame.Dom T w) : (env.extend r o).Opened := by
  intro z Z hz hv
  have hne : VarSymb.step z .dia ≠ .root r := fun he => by cases he
  have hv' : Δ (.step z .dia) = some Z := by rwa [Ctx.insert_ne hne] at hv
  obtain ⟨hd, he⟩ := h z Z hz hv'
  refine ⟨hd, ?_⟩
  rw [Env.extend_ne env r o hv hne hv']
  exact he

theorem Env.opened_diaPush {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {x : VarSymb}
    {X : VarType} (hx : Δ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x hx)).1) :
    (env.diaPush x hx w').Opened := by
  intro z Z hz hv
  have hzx : z = x := by
    change (if z = x then (match Δ.ref x with | some (.VTypeDia X) => some X | _ => none)
      else none) = some Z at hv
    split_ifs at hv with h
    exact h
  subst hzx
  have hXZ := Ctx.diaIn_step_dia hx hv
  subst hXZ
  exact ⟨w'.2, rfl⟩

theorem Env.opened_optPush {Δ : Ctx} {w : M.frame.W} {env : M.Env Δ w} (h : env.Opened)
    {y : VarSymb} {Y : VarType} (hy : Δ.wit y = some Y) (hd : (env.wit y Y hy).Dom) :
    (env.optPush y hy ((env.wit y Y hy).get hd)).Opened := by
  intro z Z hz hv
  by_cases hzy : z = y
  · subst hzy
    have hYZ : Y = Z := Option.some.inj (hy.symm.trans hz)
    subst hYZ
    refine ⟨hd, ?_⟩
    change (if hv' : VarSymb.step z .dia = .step z .dia then _ else _) = _
    rw [dif_pos rfl]
    rfl
  · have hne : VarSymb.step z .dia ≠ .step y .dia := fun he => hzy (by cases he; rfl)
    have hv' : Δ (.step z .dia) = some Z := by rwa [Ctx.optIn_ne hne] at hv
    obtain ⟨hd', he⟩ := h z Z hz hv'
    refine ⟨hd', ?_⟩
    change (if hv'' : VarSymb.step z .dia = .step y .dia then _ else _) = _
    rw [dif_neg hne]
    exact he

/-- Into the view of a witness, an environment respecting it agrees with itself. -/
theorem Env.agree_optPush {Δ : Ctx} {w : M.frame.W} {env : M.Env Δ w} (h : env.Opened)
    {z : VarSymb} {Z : VarType} (hz : Δ.wit z = some Z) (hd : (env.wit z Z hz).Dom) :
    Env.Agree (Ctx.le_optIn Δ z) env (env.optPush z hz ((env.wit z Z hz).get hd)) := by
  intro v T hv
  by_cases hvz : v = .step z .dia
  · subst hvz
    have hTZ : T = Z := by
      rcases Δ.wit_dia z Z hz with h' | h'
      · rw [h'] at hv
        cases hv
      · rw [h'] at hv
        exact (Option.some.inj hv).symm
    subst hTZ
    obtain ⟨hd', he⟩ := h z T hz hv
    rw [he]
    change _ = (if hv' : VarSymb.step z .dia = .step z .dia then _ else _)
    rw [dif_pos rfl]
  · change _ = (if hv' : v = .step z .dia then _ else _)
    rw [dif_neg hvz]

/-! ## Into the view of a witness -/

/-- The content of a witness entry, read in the view of its image, is the entry's value. -/
theorem entryVal_optBody {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {z : VarSymb}
    {Z : VarType} (hz : Δ.wit z = some Z) (hd : (env.wit z Z hz).Dom) :
    ∀ {e : WitE σ Δ} {X : VarType} (he : e.OkW X) (hw : e.idxAlong [] = z)
      (hd' : (witVal env e he).Dom),
      entryVal (env.optPush z hz ((env.wit z Z hz).get hd)) (e.optBody z)
          (WitE.okRef_optBody he hw) = (witVal env e he).get hd'
  | .ren w', X, he, hw, hd' => by
      have hw' : w' = z := hw
      subst hw'
      have hXZ : X = Z := Option.some.inj (he.symm.trans hz)
      subst hXZ
      change Env.ref (env.optPush w' hz ((env.wit w' X hz).get hd)) (.step w' .dia)
        (WitE.okRef_optBody (X := X) (e := WitE.ren w') he rfl) = (env.wit w' X he).get hd'
      rw [Env.ref, dif_neg (by decide : ¬ Step.dia.isProj = true)]
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

/-- ⭐**Into the view of a witness**: the substituted environment of `θ.optIn` is the substituted
    environment's view of the witness, when the environment respects its opened witnesses. -/
theorem substEnv_optIn {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) (hop : env.Opened) (hO : ModalSys.Opt = true)
    {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X) {z : VarSymb} {Z : VarType}
    (hw : (θ.wit y).idxAlong [] = z) (hz : Δ.wit z = some Z) (hd : (env.wit z Z hz).Dom)
    (hd' : ((substEnv θ hθ hnp env).wit y X hy).Dom) :
    substEnv (θ.optIn y z) (Subst.ok_optIn hθ hO hy hw) (hnp.optIn y)
        (env.optPush z hz ((env.wit z Z hz).get hd)) =
      (substEnv θ hθ hnp env).optPush y hy (((substEnv θ hθ hnp env).wit y X hy).get hd') := by
  refine Env.ext' (fun v T hv => ?_) (fun y' X' hy' => ?_)
  swap
  · exact substWit_mono (Env.agree_optPush hop hz hd) (fun _ _ _ => rfl) (fun _ => rfl) _ _
  by_cases hc : v = .step y .dia
  · subst hc
    have hXT : X = T := by
      rw [Ctx.optIn_content hy] at hv
      exact Option.some.inj hv
    subst hXT
    change entryVal _ (if VarSymb.step y .dia = .step y .dia then (θ.wit y).optBody z
      else (θ (.step y .dia)).mono (Ctx.le_optIn Δ z)) _ =
      (if hv' : VarSymb.step y .dia = .step y .dia then _ else _)
    rw [dif_pos rfl]
    rw [entryVal_congr _ (if_pos rfl) _ (WitE.okRef_optBody (hθ.wit hO y X hy) hw)]
    have hsw := substEnv_wit θ hθ hnp env hy (hθ.wit hO y X hy)
    have hd'' : (witVal env (θ.wit y) (hθ.wit hO y X hy)).Dom := hsw ▸ hd'
    rw [entryVal_optBody env hz hd (hθ.wit hO y X hy) hw hd'']
    change _ = ((substEnv θ hθ hnp env).wit y X hy).get hd'
    exact part_get_eq (p := witVal env (θ.wit y) (hθ.wit hO y X hy)) hsw.symm hd''
  · have hv' : Γ v = some T := by rwa [Ctx.optIn_ne hc] at hv
    change entryVal _ (if v = .step y .dia then (θ.wit y).optBody z
      else (θ v).mono (Ctx.le_optIn Δ z)) _ = (if hv'' : v = .step y .dia then _ else _)
    rw [dif_neg hc]
    rw [entryVal_congr _ (if_neg hc) _ (SubE.okRef_mono _ (hθ v T (hnp v T hv') hv'))]
    exact entryVal_mono (Env.agree_optPush hop hz hd) _ _

/-- ⭐What substituting into a formula of `Γ` needs of the environment: `Γ` has no witness to open,
    or the environment respects its opened witnesses. -/
def Env.OpenedFor (Γ : Ctx) {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) : Prop :=
  (∀ y X, Γ.wit y = some X → False) ∨ env.Opened

/-- The default for the environment condition: `Opt` off, an assumption, a context without
    witnesses, or a push of an environment that respects its witnesses. -/
macro "opened_tac" : tactic => `(tactic| first
  | assumption
  | exact fun h => absurd h (by rw [show ModalSys.Opt = false by opt_off]; decide)
  | exact fun _ => Or.inr (Model.Env.opened_boxPush _ _)
  | exact fun _ => Or.inr (Model.Env.opened_diaPush _ _ _)
  | exact fun _ => Or.inr (Model.Env.opened_extend (Model.Env.opened_boxPush _ _) _ _)
  | exact fun _ => Or.inr (Model.Env.opened_extend (Model.Env.opened_diaPush _ _ _) _ _)
  | exact fun hO => Or.inr (‹ModalSys.Opt = true → Model.Env.Opened _› hO)
  | exact fun hO => Or.inr (Model.Env.opened_extend (‹ModalSys.Opt = true → Model.Env.Opened _› hO)
      _ _)
  | exact fun hO => (‹ModalSys.Opt = true → _› hO).imp id
      (fun h => Model.Env.opened_extend h _ _)
  | exact fun _ => Or.inl (fun _ _ h => nomatch h))

theorem Env.agree_extend {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) {r : Root}
    (h : Δ (.root r) = none) {T : VarType} (o : M.frame.Dom T w) :
    Env.Agree (Ctx.le_insert h T) env (env.extend r o) := fun v U hv =>
  (Env.extend_ne env r o _ (fun he => by subst he; rw [h] at hv; cases hv) hv).symm

theorem substEnv_under {Γ Δ : Ctx} {w : M.frame.W} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hnp : Γ.NoProjLast) (env : M.Env Δ w) {d d' : ℕ} (T : VarType)
    (h : Δ (.root (.bnd d')) = none) (o : M.frame.Dom T w) :
    substEnv (θ.under d d' T h) (Subst.ok_under hθ T h) (hnp.insert (.bnd d) T)
        (env.extend (.bnd d') o) =
      (substEnv θ hθ hnp env).extend (.bnd d) o := by
  refine Env.ext' (fun v U hv => ?_) (fun y X hy => ?_)
  swap
  · exact substWit_mono (Env.agree_extend env h o) (fun _ _ _ => rfl) (fun _ => rfl) _ _
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [Env.extend_root (substEnv θ hθ hnp env) _ o hv]
    exact (entryVal_congr _
      (show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl) _
      (Ctx.ref_insert_root Δ _ T)).trans (Env.extend_root env _ o (Ctx.ref_insert_root Δ _ T))
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [Env.extend_ne (substEnv θ hθ hnp env) _ o hv hvr hv']
    exact (entryVal_congr _
      (show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr) _
      (SubE.okRef_mono _ (hθ v U (hnp v U hv') hv'))).trans
      (entryVal_mono (Env.agree_extend env h o) _ _)

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
    (_henv : ModalSys.Opt = true → Env.OpenedFor Γ env := by opened_tac),
    M.sat env (WFF.subst ι θ hθ hc hΓ hΔ φ) ↔ M.sat (substEnv θ hθ hnp env) φ
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .atom ρ, henv =>
      relSat_subst θ hθ hc hnp env ρ Fin.elim0
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .eq t s, henv => by
      change interp env (Term.subst _ θ hθ hc t) = interp env (Term.subst _ θ hθ hc s) ↔ _
      rw [interp_subst θ hθ hc hnp env t, interp_subst θ hθ hc hnp env s]
      exact Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .top, _ => Iff.rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .bot, _ => Iff.rfl
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .and φ ψ, henv =>
      and_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ) (sat_subst θ hθ hc hΓ hΔ hnp env ψ)
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .or φ ψ, henv =>
      or_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ) (sat_subst θ hθ hc hΓ hΔ hnp env ψ)
  | _, _, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .imp φ ψ, henv =>
      imp_congr (sat_subst θ hθ hc hΓ hΔ hnp env φ) (sat_subst θ hθ hc hΓ hΔ hnp env ψ)
  | _, _, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .all T φ, henv =>
      forall_congr' fun o =>
        (sat_subst (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
          (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T)
          (hnp.insert (.bnd d) T) (env.extend (.bnd d') o) φ).trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_under θ hθ hnp env T hΔ.root o)))
  | _, _, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .ex T φ, henv =>
      exists_congr fun o =>
        (sat_subst (θ.under d d' T hΔ.root) (Subst.ok_under hθ T hΔ.root)
          (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T)
          (hnp.insert (.bnd d) T) (env.extend (.bnd d') o) φ).trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_under θ hθ hnp env T hΔ.root o)))
  | _, Γ, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .box φ, henv =>
      forall_congr' fun w' =>
        (sat_subst θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn
          (Ctx.noProjLast_boxIn Γ) (env.boxPush w') φ).trans
        (iff_of_eq (congrArg (fun e => M.sat e φ) (substEnv_box θ hθ hnp env w')))
  | ι, Γ, _, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .dia x hx φ, henv => by
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
          (Ctx.noProjLast_diaIn Γ x) (env.diaPush (ι x) hr₁ w') φ).mp hsat
      · rintro ⟨X, hr, w₂, hsat⟩
        obtain ⟨Y, hr₁⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hw
        have hE : (M.posEval (env.ref (ι x) hr₁)).1 =
            (M.posEval ((substEnv θ hθ hnp env).ref x hr)).1 := by
          rw [substEnv_ref θ hθ hnp env x hr, entryVal_dia_ext env _ hw hr₁]
        refine ⟨Y, hr₁, ⟨w₂.1, hE.symm ▸ w₂.2⟩, ?_⟩
        refine (sat_subst (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hΓ.diaIn x) (hΔ.diaIn (ι x)) (Ctx.noProjLast_diaIn Γ x)
          (env.diaPush (ι x) hr₁ ⟨w₂.1, hE.symm ▸ w₂.2⟩) φ).mpr ?_
        rw [substEnv_dia θ hθ hnp env hx hr hr₁ hw ⟨w₂.1, hE.symm ▸ w₂.2⟩ w₂.2]
        exact hsat
  | ι, Γ, Δ, _, _, θ, hθ, hc, hΓ, hΔ, hnp, _, env, .optx hO y hy φ, henv => by
      obtain ⟨X, hX⟩ := hy
      have hop : env.Opened := (henv hO).resolve_left fun h => h y X hX
      have hw : (θ.wit y).idxAlong [] = ι y := hc.wit hO y X hX []
      obtain ⟨Z, hZ⟩ := WitE.wit_of (hθ.wit hO y X hX) hw
      have hdom : ((substEnv θ hθ hnp env).wit y X hX).Dom ↔ (env.wit (ι y) Z hZ).Dom := by
        rw [substEnv_wit θ hθ hnp env hX (hθ.wit hO y X hX)]
        exact witVal_dom env hZ (hθ.wit hO y X hX) hw
      constructor
      · rintro ⟨Z', hZ', hd, hsat⟩
        have hZZ : Z = Z' := Option.some.inj (hZ.symm.trans hZ')
        subst hZZ
        refine ⟨X, hX, hdom.mpr hd, ?_⟩
        rw [← substEnv_optIn θ hθ hnp env hop hO hX hw hZ hd (hdom.mpr hd)]
        exact (sat_subst (θ.optIn y (ι y)) (Subst.ok_optIn hθ hO hX hw)
          (Subst.coh_optIn hθ hc hO hX) (hΓ.optIn y) (hΔ.optIn (ι y)) (hnp.optIn y)
          (env.optPush (ι y) hZ ((env.wit (ι y) Z hZ).get hd)) φ
          (fun _ => Or.inr (Env.opened_optPush hop hZ hd))).mp hsat
      · rintro ⟨X', hX', hd', hsat⟩
        have hXX : X = X' := Option.some.inj (hX.symm.trans hX')
        subst hXX
        refine ⟨Z, hZ, hdom.mp hd', ?_⟩
        refine (sat_subst (θ.optIn y (ι y)) (Subst.ok_optIn hθ hO hX hw)
          (Subst.coh_optIn hθ hc hO hX) (hΓ.optIn y) (hΔ.optIn (ι y)) (hnp.optIn y)
          (env.optPush (ι y) hZ ((env.wit (ι y) Z hZ).get (hdom.mp hd'))) φ
          (fun _ => Or.inr (Env.opened_optPush hop hZ (hdom.mp hd')))).mpr ?_
        rw [substEnv_optIn θ hθ hnp env hop hO hX hw hZ (hdom.mp hd') hd']
        exact hsat
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .here hT s t, henv => by
      change Model.Realised hT (interp env (Term.subst _ θ hθ hc s))
        (interp env (Term.subst _ θ hθ hc t)) ↔ _
      rw [interp_subst θ hθ hc hnp env s, interp_subst θ hθ hc hnp env t]
      exact Iff.rfl
  | _, _, _, _, _, θ, hθ, hc, _, _, hnp, _, env, .back hB L s t, henv => by
      change Model.Backs L (interp env (Term.subst _ θ hθ hc s))
        (interp env (Term.subst _ θ hθ hc t)) ↔ _
      rw [interp_subst θ hθ hc hnp env s, interp_subst θ hθ hc hnp env t]
      exact Iff.rfl
  | _, Γ, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .retS hB S t Φ, henv =>
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
  | ι, Γ, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .retxS hB y hy S t Φ, henv => by
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
  | _, Γ, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .link hV hF t Φ, henv =>
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
  | ι, Γ, _, d, d', θ, hθ, hc, hΓ, hΔ, hnp, _, env, .linkx hV hF y hy t Φ, henv => by
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
