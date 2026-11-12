import QML.QML_v12m_Cone
import QML.QML_v12m_SatSubst
import QML.QML_v12m_CanonFunc

/-!
# QML v12m — the cone: the apex read one view further in

At the apex of a cone (`ConeData.cone`) a modal formula means what its shift means in `N`, at `ρ`,
in an environment `V` of the apex's `□` view whose kept addresses hold the apex's objects
(`ConeData.Keyed`): `□ψ` at the apex is `□(shift ψ)` under `V` (⭐`sat_apex_box`), `◇_x ψ` is
`◇_{x.keep}(shift ψ)` (⭐`sat_apex_dia`), and a modal term's object is that of its kept form
(`interp_apex_box`, `interp_apex_dia`).  So `ρ` reads the apex as if the apex were its parent
(docs, "K45 and KD45 without both lifts: the hub", step 5).

Generic, for closing the apex's objects under the operations: in any unshaped model the value of a
map applied to a term is the map applied to the value (⭐`Model.interp_applyG`).
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature}

section Apply

variable {M : Model.{u, v} σ}

theorem interp_varTerm {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b), interp env (Canon.varTerm p) = interp env p.2
  | ⟨.var, _⟩ => rfl

/-- ⭐**The value of a map applied to a term is the map applied to the value** (unshaped: the
    `interp` form of `cden_applyG`). -/
theorem interp_applyG (hSh : ModalSys.shaped = false) :
    ∀ {A B : VarType} (g : GFunc σ A B) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w)
      {a : Ann A} (t : Term σ Γ A a),
      interp env (Canon.applyG g t).2 = GFunc.eval M.ops g w (interp env t)
  | _, _, .id _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, w, env, _, t =>
      (interp_applyG hSh g env _).trans
        (congrArg (GFunc.eval M.ops g w) (interp_applyG hSh f env t))
  | _, _, .fst, _, _, _, _, .pair _ _ => rfl
  | _, _, .snd, _, _, _, _, .pair _ _ => rfl
  | _, _, .pair f g, _, _, env, _, t =>
      Prod.ext (interp_applyG hSh f env t) (interp_applyG hSh g env t)
  | _, _, .unit _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, w, env, _, t => by
      change interpFunc env ((Spine.ofFn fun k => Canon.varTerm (Canon.applyG (args k) t)).fill
          (.F ⟨f, rfl⟩)) Fin.elim0 =
        M.frame.funcInterp f w (fun k => GFunc.eval M.ops (args k) w (interp env t))
      rw [interpFunc_fill]
      change M.frame.funcInterp f w (fun k => interp env (Canon.varTerm (Canon.applyG (args k) t)))
        = _
      congr 1
      funext k
      rw [interp_varTerm, interp_applyG hSh (args k) env t]
  | _, _, .boxMap f, _, _, env, _, .boxtm b => M.nec_inj (funext fun a => by
      change M.necEval (interp env (Term.boxtm (Canon.applyG f b).2)) a =
        M.necEval (M.ops.necMap f (interp env (Term.boxtm b))) a
      rw [box_beta, M.necMap_eval, box_beta]
      exact interp_applyG hSh f (env.boxPush a) b)
  | _, _, .boxPair _ _, _, _, env, _, .pair (.boxtm b) (.boxtm c) => M.nec_inj (funext fun a => by
      change M.necEval (interp env (Term.boxtm (.pair b c))) a =
        M.necEval (M.ops.necPair (interp env (Term.boxtm b)) (interp env (Term.boxtm c))) a
      rw [box_beta, M.necPair_eval, box_beta, box_beta]
      rfl)
  | _, _, .boxUnit, _, _, _, _, .unit => M.nec_inj (funext fun _ => rfl)
  | _, _, .diaMap f, _, _, env, _, .diatm x hx c => by
      obtain ⟨X, hr⟩ := id hx
      refine M.pos_inj ?_ fun h => flagElim hSh h
      obtain ⟨hE1, hf1⟩ := posSec_of_eq (dia_beta env hx hr (Canon.applyG f c).2)
      obtain ⟨hE2, hf2⟩ := posSec_of_eq (M.posMap_eval f (interp env (Term.diatm x hx c)))
      obtain ⟨hE3, hf3⟩ := posSec_of_eq (dia_beta env hx hr c)
      refine posSec_ext' (hE1.trans (hE2.trans hE3).symm) fun a h h' => ?_
      have hm : a ∈ (M.posEval (env.ref x hr)).1 := hE1 ▸ h
      have h'' : a ∈ (M.posEval (interp env (Term.diatm x hx c))).1 := hE2 ▸ h'
      refine (hf1 a h hm).trans ((interp_applyG hSh f _ c).trans ?_)
      refine Eq.trans ?_ (hf2 a h' h'').symm
      exact congrArg (GFunc.eval M.ops f a.1) (hf3 a h'' hm).symm
  | _, _, .strength _ _, Γ, _, env, _, .pair (.boxtm b) (.diatm x hx c) => by
      obtain ⟨X, hr⟩ := id hx
      refine M.pos_inj ?_ fun h => flagElim hSh h
      obtain ⟨hE1, hf1⟩ := posSec_of_eq (dia_beta env hx hr
        (.pair (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) c))
      obtain ⟨hE2, hf2⟩ := posSec_of_eq (M.posStrength_eval (interp env (Term.boxtm b))
        (interp env (Term.diatm x hx c)))
      obtain ⟨hE3, hf3⟩ := posSec_of_eq (dia_beta env hx hr c)
      refine posSec_ext' (hE1.trans (hE2.trans hE3).symm) fun a h h' => ?_
      have hm : a ∈ (M.posEval (env.ref x hr)).1 := hE1 ▸ h
      have h'' : a ∈ (M.posEval (interp env (Term.diatm x hx c))).1 := hE2 ▸ h'
      refine (hf1 a h hm).trans (Eq.trans ?_ (hf2 a h' h'').symm)
      change (interp _ (Term.mono _ b), interp _ c) =
        ((M.necEval (interp env (Term.boxtm b)) a, _) : M.frame.Dom (.VTypeProd _ _) a.1)
      rw [interp_mono (Env.box_dia_agree env hr ⟨a, hm⟩) b, box_beta, hf3 a h'' hm]
  | _, _, .extract hT, _, _, _, _, .boxtm _ => flagElim hSh (ModalSys.shaped_of_T hT)
  | _, _, .dup hF, Γ, _, env, _, .boxtm b => M.nec_inj (funext fun v => by
      change M.necEval (interp env (Term.boxtm (Term.boxtm
          (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)))) v =
        M.necEval (M.ops.necDup hF (interp env (Term.boxtm b))) v
      rw [box_beta]
      apply M.nec_inj
      funext s
      rw [box_beta, M.necDup_eval, box_beta]
      exact interp_shift (Env.shiftAgree_twoBox hF env v s) b)
  | _, _, .dkeep hF, Γ, _, env, _, .diatm x hx c => M.nec_inj (funext fun v => by
      have h := entryVal_keepE_dia env v hF (e := SubE.tm (Term.diatm x hx c)) rfl
      rw [entryVal_congr _ (SubE.keepE_dia x hx c hF) _ rfl] at h
      change M.necEval (interp env (Term.boxtm (Term.diatm (.step x .keep)
          (Ctx.exists_keep_dia hF hx) (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) c)))) v =
        M.necEval (M.ops.posKeep hF (interp env (Term.diatm x hx c))) v
      rw [box_beta]
      exact h)

/-- In a relational unshaped model a possible object moved across is the object kept (docs §3 5,
    "with 4, `x.side` is `x.keep`"). -/
theorem posSide_eq_posKeep {M : Model.{u, 0} σ} (hSh : ModalSys.shaped = false)
    (hInd : ∀ {A : VarType} {w : M.frame.W} (o o' : M.frame.Dom A w), M.Ind o o' → o = o')
    (hF : ModalSys.Four = true) (hV : ModalSys.Five = true) {A : VarType} {w : M.frame.W}
    (p : M.frame.Pos A w) : M.ops.posSide hV p = M.ops.posKeep hF p := by
  apply M.nec_inj
  funext a
  refine M.pos_inj ?_ fun h => flagElim hSh h
  obtain ⟨hE, hf⟩ := posSec_of_eq (congrArg Prod.fst (M.posKeep_full hF p a))
  have hmem : ∀ b : M.frame.Acc a.1, b ∈ (M.posEval (M.necEval (M.ops.posSide hV p) a)).1 ↔
      (⟨b.1, ⟨M.frame.trans hF a.2.down b.2.down⟩⟩ : M.frame.Acc w) ∈ (M.posEval p).1 := by
    intro b
    change b ∈ (M.posFull _).1.1 ↔ _
    rw [M.posSide_ext hV p a]
    constructor
    · rintro ⟨⟨t, ⟨r⟩⟩, hb', e⟩
      obtain rfl : t = b.1 := congrArg Sigma.fst e
      exact hb'
    · intro h
      exact ⟨_, h, rfl⟩
  refine posSec_ext' (Set.ext fun b => (hmem b).trans (Set.ext_iff.mp hE b).symm) ?_
  intro b h h'
  have hb := (hmem b).mp h
  exact (hInd _ _ (M.posSide_content hV p a ⟨b.1, ⟨M.frame.trans hF a.2.down b.2.down⟩⟩ hb h)).trans
    (hf b h' hb).symm

end Apply

namespace ConeData

variable {N : Model.{0, 0} σ} {c : N.ConeData} {hT : ModalSys.T = false}
  {hB : ModalSys.B = false} {hS : ModalSys.BStrong = false}
  {hInd : ∀ {A : VarType} {w : N.frame.W} (o o' : N.frame.Dom A w), N.Ind o o' → o = o'}

/-- The object of `N` under a necessary object of the apex. -/
abbrev nb {A : VarType} (n : (c.cone hT hB hS hInd).frame.Dom (.VTypeBox A) none) :
    N.frame.Nec A c.ρ :=
  (n : {n : N.frame.Nec A c.ρ // c.DefN A n}).1

/-- The object of `N` under a possible object of the apex. -/
abbrev pb {A : VarType} (p : (c.cone hT hB hS hInd).frame.Dom (.VTypeDia A) none) :
    N.frame.Pos A c.ρ :=
  (p : {p : N.frame.Pos A c.ρ // c.DefP A p}).1

/-! ## From the apex into a modality, read in `N` -/

/-- The apex's `□` view at an arrow of `ρ`, read in `N`. -/
def downBox {Γ : Ctx} (E : (c.cone hT hB hS hInd).Env Γ none) (s : N.frame.Acc c.ρ) :
    N.Env Γ.boxIn s.1 :=
  fun v T h => c.ofC hT hB T s.1 (E.boxPush (c.up hT hB (w := none) s) v T h)

theorem envRel_downBox {Γ : Ctx} (E : (c.cone hT hB hS hInd).Env Γ none)
    (s : N.frame.Acc c.ρ) :
    c.EnvRel hT hB hS hInd (t := s.1) (E.boxPush (c.up hT hB (w := none) s)) (downBox E s) :=
  fun _ T _ => (c.toC_ofC hT hB T s.1 _).symm

/-- The apex's `◇_x` view at an arrow of `x`'s extent, read in `N`. -/
def downDia {Γ : Ctx} (E : (c.cone hT hB hS hInd).Env Γ none) {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) (s : N.frame.Acc c.ρ)
    (h : c.up hT hB (w := none) s ∈ ((c.cone hT hB hS hInd).posEval (E.ref x hx)).1) :
    N.Env (Γ.diaIn x) s.1 :=
  fun v T hv => c.ofC hT hB T s.1 (E.diaPush x hx ⟨_, h⟩ v T hv)

theorem envRel_downDia {Γ : Ctx} (E : (c.cone hT hB hS hInd).Env Γ none) {x : VarSymb}
    {X : VarType} (hx : Γ.ref x = some (.VTypeDia X)) (s : N.frame.Acc c.ρ)
    (h : c.up hT hB (w := none) s ∈ ((c.cone hT hB hS hInd).posEval (E.ref x hx)).1) :
    c.EnvRel hT hB hS hInd (t := s.1) (E.diaPush x hx ⟨_, h⟩) (downDia E hx s h) :=
  fun _ T _ => (c.toC_ofC hT hB T s.1 _).symm

/-! ## The keys -/

variable (hF : ModalSys.Four = true)

/-- ⭐`V`, an environment of the apex's `□` view at `ρ`, holds at each kept address the apex's
    object at the address. -/
def Keyed {Γ : Ctx} (E : (c.cone hT hB hS hInd).Env Γ none) (V : N.Env Γ.boxIn c.ρ) : Prop :=
  (∀ u A (hu : Γ.ref u = some (.VTypeBox A)),
    nb (E.ref u hu) = V.ref (.step u .keep) (Ctx.ref_keep_of hF hu)) ∧
  (∀ u A (hu : Γ.ref u = some (.VTypeDia A)),
    pb (E.ref u hu) = V.ref (.step u .keep) (Ctx.ref_keep_of' hF hu VarType.keepable_dia))

variable {hF}

/-- ⭐Into a `□` from the apex is, across the shift, into a `□` from `V`. -/
theorem shiftAgree_downBox {Γ : Ctx} {E : (c.cone hT hB hS hInd).Env Γ none}
    {V : N.Env Γ.boxIn c.ρ} (hK : Keyed hF E V) (s : N.frame.Acc c.ρ) :
    Env.ShiftAgree (Ctx.shifts_boxIn_boxIn hF Γ) (downBox E s) (V.boxPush s) := by
  refine Env.ShiftAgree.of_raw ?_
  intro x T _ hx
  match x with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := Ctx.boxIn_box hx
      rw [Env.ref_congr _ (VarSymb.shift_level_zero (s := .box) rfl) _
        (Ctx.ref_boxIn_of hk (Ctx.ref_keep_of hF hu)), Env.ref,
        dif_neg (by decide : ¬ Step.box.isStruct = true)]
      change c.ofC hT hB T s.1 (c.toC hT hB T s.1 (N.necEval (nb (E.ref u hu)) s)) =
        N.necEval (V.ref (.step u .keep) (Ctx.ref_keep_of hF hu)) s
      rw [c.ofC_toC, hK.1 u T hu]
  | .step u .keep =>
      obtain ⟨_, hu, hk⟩ := Ctx.boxIn_keep hx
      cases T with
      | VTypeDia A =>
          rw [Env.ref_congr _ (VarSymb.shift_level_zero (s := .keep) rfl) _
            (Ctx.ref_keep_of' hF (Ctx.ref_keep_of' hF hu hk) hk), Env.ref,
            dif_neg (by decide : ¬ Step.keep.isStruct = true)]
          change c.ofC hT hB _ s.1 (c.toC hT hB _ s.1
              (N.necEval (N.ops.posKeep hF (pb (E.ref u hu))) s)) =
            N.necEval (N.ops.posKeep hF (V.ref (.step u .keep) (Ctx.ref_keep_of' hF hu hk))) s
          rw [c.ofC_toC, hK.2 u A hu]
      | VTypeBox A =>
          rw [Env.ref_congr _ (VarSymb.shift_level_zero (s := .keep) rfl) _
            (Ctx.ref_keep_of hF (Ctx.ref_keep_of hF hu)), Env.ref,
            dif_neg (by decide : ¬ Step.keep.isStruct = true)]
          change c.ofC hT hB _ s.1 (c.toC hT hB _ s.1
              (N.necEval (N.ops.necDup hF (nb (E.ref u hu))) s)) =
            N.necEval (N.ops.necDup hF (V.ref (.step u .keep) (Ctx.ref_keep_of hF hu))) s
          rw [c.ofC_toC, hK.1 u A hu]
      | Var => simp [VarType.keepable] at hk
      | VTypeOne => simp [VarType.keepable] at hk
      | VTypeProd _ _ => simp [VarType.keepable] at hk
  | .root _ => cases hx
  | .step _ .fst => cases hx
  | .step _ .snd => cases hx
  | .step _ .dia => cases hx
  | .step _ .here => cases hx

/-- ⭐Into a `◇_x` from the apex is, across the shift, into a `◇_{x.keep}` from `V`. -/
theorem shiftAgree_downDia {Γ : Ctx} {E : (c.cone hT hB hS hInd).Env Γ none}
    {V : N.Env Γ.boxIn c.ρ} (hK : Keyed hF E V) {x : VarSymb} {X : VarType}
    (hr : Γ.ref x = some (.VTypeDia X)) (s : N.frame.Acc c.ρ)
    (h : c.up hT hB (w := none) s ∈ ((c.cone hT hB hS hInd).posEval (E.ref x hr)).1)
    (hxk : Γ.boxIn.ref (.step x .keep) = some (.VTypeDia X))
    (h' : s ∈ (N.posEval (V.ref (.step x .keep) hxk)).1) :
    Env.ShiftAgree (Ctx.shifts_diaIn_keep hF Γ x) (downDia E hr s h)
      (V.diaPush (.step x .keep) hxk ⟨s, h'⟩) := by
  refine Env.ShiftAgree.of_raw ?_
  intro v T hlp hv
  match v with
  | .step u .dia =>
      have hu : u = x := by
        change (if u = x then _ else none) = some T at hv
        split_ifs at hv with h
        exact h
      subst hu
      have hXT := Ctx.diaIn_step_dia hr hv
      subst hXT
      rw [Env.ref_congr _ (VarSymb.shift_level_zero (s := .dia) rfl) _ (Ctx.ref_diaIn_of hxk),
        Env.ref, dif_neg (by decide : ¬ Step.dia.isStruct = true)]
      refine (c.ofC_toC hT hB _ s.1 ((N.posEval (pb (E.ref u hr))).2 ⟨s, h⟩)).trans ?_
      exact posEval_snd_congr (hK.2 u _ hr) ⟨s, h⟩ h'
  | .step u .box =>
      exact shiftAgree_downBox hK s (.step u .box) T ((Ctx.ref_nonproj _ hlp).trans hv)
  | .step u .keep =>
      exact shiftAgree_downBox hK s (.step u .keep) T ((Ctx.ref_nonproj _ hlp).trans hv)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-! ## Truth and values at the apex -/

/-- ⭐⭐**`□` at the apex is `□(shift ψ)` under `V`.** -/
theorem sat_apex_box {Γ : Ctx} [Γ.NoSlots] {E : (c.cone hT hB hS hInd).Env Γ none}
    {V : N.Env Γ.boxIn c.ρ} (hK : Keyed hF E V) (ψ : WFF σ Γ.boxIn 0) :
    (c.cone hT hB hS hInd).sat E (.box ψ) ↔
      N.sat V (.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots ψ)) := by
  haveI : ModalSys.NoOpt := ⟨by opt_off⟩
  change (∀ a, (c.cone hT hB hS hInd).sat (E.boxPush a) ψ) ↔
    ∀ s, N.sat (V.boxPush s) (WFF.shift (Ctx.shifts_boxIn_boxIn hF Γ) Ctx.NoSlots.slots ψ)
  constructor
  · intro H s
    exact (sat_shift Ctx.NoSlots.slots (shiftAgree_downBox hK s) ψ).mpr
      ((sat_cone (fun _ => hF) (envRel_downBox E s) ψ).mp (H _))
  · intro H a
    obtain ⟨_ | t, ⟨r⟩⟩ := a
    · exact False.elim r
    exact (sat_cone (fun _ => hF) (envRel_downBox E ⟨t, ⟨r⟩⟩) ψ).mpr
      ((sat_shift Ctx.NoSlots.slots (shiftAgree_downBox hK ⟨t, ⟨r⟩⟩) ψ).mp (H _))

/-- ⭐⭐**`◇_x` at the apex is `◇_{x.keep}(shift ψ)` under `V`.** -/
theorem sat_apex_dia {Γ : Ctx} [Γ.NoSlots] {E : (c.cone hT hB hS hInd).Env Γ none}
    {V : N.Env Γ.boxIn c.ρ} (hK : Keyed hF E V) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (ψ : WFF σ (Γ.diaIn x) 0) :
    (c.cone hT hB hS hInd).sat E (.dia x hx ψ) ↔
      N.sat V (.dia (.step x .keep) (Ctx.exists_keep_dia hF hx)
        (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots ψ)) := by
  haveI : ModalSys.NoOpt := ⟨by opt_off⟩
  constructor
  · rintro ⟨X, hr, ⟨⟨_ | s, ⟨r⟩⟩, h⟩, H⟩
    · exact False.elim r
    have hxk := Ctx.ref_keep_of' hF hr VarType.keepable_dia
    have h' : (⟨s, ⟨r⟩⟩ : N.frame.Acc c.ρ) ∈ (N.posEval (V.ref (.step x .keep) hxk)).1 := by
      rw [← hK.2 x X hr]
      exact h
    exact ⟨X, hxk, ⟨_, h'⟩, (sat_shift Ctx.NoSlots.slots
      (shiftAgree_downDia hK hr ⟨s, ⟨r⟩⟩ h hxk h') ψ).mpr
      ((sat_cone (fun _ => hF) (envRel_downDia E hr ⟨s, ⟨r⟩⟩ h) ψ).mp H)⟩
  · rintro ⟨X, hxk, ⟨s, h'⟩, H⟩
    obtain ⟨X', hr⟩ := hx
    obtain rfl : X' = X := by
      have := (Ctx.ref_keep_of' hF hr VarType.keepable_dia).symm.trans hxk
      simpa using this
    have h : c.up hT hB (w := none) s ∈ ((c.cone hT hB hS hInd).posEval (E.ref x hr)).1 := by
      change s ∈ (N.posEval (pb (E.ref x hr))).1
      rw [hK.2 x X' hr]
      exact h'
    exact ⟨X', hr, ⟨_, h⟩, (sat_cone (fun _ => hF) (envRel_downDia E hr s h) ψ).mpr
      ((sat_shift Ctx.NoSlots.slots (shiftAgree_downDia hK hr s h hxk h') ψ).mp H)⟩

/-- ⭐A necessary term's object at the apex is its kept form's under `V`. -/
theorem interp_apex_box {Γ : Ctx} {E : (c.cone hT hB hS hInd).Env Γ none}
    {V : N.Env Γ.boxIn c.ρ} (hK : Keyed hF E V) {A : VarType} {a : Ann A}
    (b : Term σ Γ.boxIn A a) :
    nb (interp E (Term.boxtm b)) =
      interp V (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)) := by
  apply N.nec_inj
  funext s
  rw [box_beta, interp_shift (shiftAgree_downBox hK s) b]
  have h1 := box_beta E b (c.up hT hB (w := none) s)
  rw [interp_cone (envRel_downBox E s) b] at h1
  exact c.toC_injective hT hB (h1 : c.toC hT hB A s.1 (N.necEval (nb (interp E (Term.boxtm b))) s)
    = _)

/-- ⭐A possible term's object at the apex is its kept form's under `V`. -/
theorem interp_apex_dia {Γ : Ctx} {E : (c.cone hT hB hS hInd).Env Γ none}
    {V : N.Env Γ.boxIn c.ρ} (hK : Keyed hF E V) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (t : Term σ (Γ.diaIn x) A a) :
    pb (interp E (Term.diatm x hx t)) =
      interp V (Term.diatm (.step x .keep) (Ctx.exists_keep_dia hF hx)
        (Term.shift (Ctx.shifts_diaIn_keep hF Γ x) t)) := by
  obtain ⟨X, hr⟩ := id hx
  have hxk := Ctx.ref_keep_of' hF hr VarType.keepable_dia
  refine N.pos_inj ?_ fun h => flagElim (shaped_false_of hT hS) h
  obtain ⟨hE, hf⟩ := posSec_of_eq (dia_beta E hx hr t)
  rw [dia_beta V (Ctx.exists_keep_dia hF hx) hxk]
  refine posSec_ext' ?_ ?_
  · ext s
    dsimp only
    rw [← hK.2 x X hr]
    exact Set.ext_iff.mp hE (c.up hT hB (w := none) s)
  · intro s h h'
    have hm : c.up hT hB (w := none) s ∈ ((c.cone hT hB hS hInd).posEval (E.ref x hr)).1 := by
      change s ∈ (N.posEval (pb (E.ref x hr))).1
      rw [hK.2 x X hr]
      exact h'
    have hc := hf (c.up hT hB (w := none) s) h hm
    dsimp only at hc
    rw [interp_cone (envRel_downDia E hr s hm) t] at hc
    dsimp only
    rw [interp_shift (shiftAgree_downDia hK hr s hm hxk h') t]
    exact c.toC_injective hT hB (hc : c.toC hT hB A s.1 ((N.posEval (pb (interp E
      (Term.diatm x hx t)))).2 ⟨s, h⟩) = _)

/-! ## An environment at the apex -/

section ApexEnv

variable (c hT hB hS hInd hF) {Γ : Ctx}

/-- ⭐**The apex's object at an address**: a base address `bv`'s, a pair by its components, and a
    necessary or possible address `V`'s object at the kept address. -/
def apexVal (bv : ∀ v, Γ.ref v = some .Var → c.D) (V : N.Env Γ.boxIn c.ρ)
    (hN : ∀ v A (h : Γ.ref v = some (.VTypeBox A)),
      c.DefN A (V.ref (.step v .keep) (Ctx.ref_keep_of hF h)))
    (hP : ∀ v A (h : Γ.ref v = some (.VTypeDia A)),
      c.DefP A (V.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))) :
    ∀ (T : VarType) (v : VarSymb), Γ.ref v = some T → (c.cone hT hB hS hInd).frame.Dom T none
  | .Var, v, h => bv v h
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A B, v, h =>
      (apexVal bv V hN hP A (.step v .fst) (Ctx.ref_fst_of h),
        apexVal bv V hN hP B (.step v .snd) (Ctx.ref_snd_of h))
  | .VTypeBox A, v, h =>
      (⟨V.ref (.step v .keep) (Ctx.ref_keep_of hF h), hN v A h⟩ :
        {n : N.frame.Nec A c.ρ // c.DefN A n})
  | .VTypeDia A, v, h =>
      (⟨V.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia), hP v A h⟩ :
        {p : N.frame.Pos A c.ρ // c.DefP A p})

/-- The apex's environment of `apexVal`. -/
def apexEnv (hnp : Γ.NoProjLast) (bv : ∀ v, Γ.ref v = some .Var → c.D)
    (V : N.Env Γ.boxIn c.ρ)
    (hN : ∀ v A (h : Γ.ref v = some (.VTypeBox A)),
      c.DefN A (V.ref (.step v .keep) (Ctx.ref_keep_of hF h)))
    (hP : ∀ v A (h : Γ.ref v = some (.VTypeDia A)),
      c.DefP A (V.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))) :
    (c.cone hT hB hS hInd).Env Γ none :=
  fun v T h => apexVal c hT hB hS hInd hF bv V hN hP T v ((Ctx.ref_nonproj Γ (hnp v T h)).trans h)

variable {c hT hB hS hInd hF}

theorem stepObj_apexVal {bv : ∀ v, Γ.ref v = some .Var → c.D} {V : N.Env Γ.boxIn c.ρ}
    {hN : ∀ v A (h : Γ.ref v = some (.VTypeBox A)),
      c.DefN A (V.ref (.step v .keep) (Ctx.ref_keep_of hF h))}
    {hP : ∀ v A (h : Γ.ref v = some (.VTypeDia A)),
      c.DefP A (V.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))}
    {U T : VarType} {s : Step} (hs : s.isStruct = true) (hst : U.step s = some T) (v : VarSymb)
    (hU : Γ.ref v = some U) (hv : Γ.ref (.step v s) = some T) :
    (c.cone hT hB hS hInd).stepObj hs hst (apexVal c hT hB hS hInd hF bv V hN hP U v hU) =
      apexVal c hT hB hS hInd hF bv V hN hP T (.step v s) hv := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases hst) <;> try rfl
  exact flagElim hT (VarType.step_here hst).1

/-- ⭐Reading the apex's environment at any reachable address gives `apexVal`. -/
theorem apexEnv_ref {hnp : Γ.NoProjLast} {bv : ∀ v, Γ.ref v = some .Var → c.D}
    {V : N.Env Γ.boxIn c.ρ}
    {hN : ∀ v A (h : Γ.ref v = some (.VTypeBox A)),
      c.DefN A (V.ref (.step v .keep) (Ctx.ref_keep_of hF h))}
    {hP : ∀ v A (h : Γ.ref v = some (.VTypeDia A)),
      c.DefP A (V.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))} :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (apexEnv c hT hB hS hInd hF hnp bv V hN hP).ref v h =
        apexVal c hT hB hS hInd hF bv V hN hP T v h
  | .root _, _, _ => rfl
  | .step v s, T, hv => by
      by_cases hs : s.isStruct = true
      · rw [Env.ref, dif_pos hs]
        split
        · rename_i U hU
          rw [apexEnv_ref v hU]
          exact stepObj_apexVal hs _ v hU hv
        · rename_i hU
          exfalso
          rw [Ctx.ref_step_proj Γ v hs, hU] at hv
          cases hv
      · rw [Env.ref, dif_neg hs]
        rfl

/-- ⭐The apex's environment is keyed to `V`. -/
theorem apexEnv_keyed {hnp : Γ.NoProjLast} {bv : ∀ v, Γ.ref v = some .Var → c.D}
    {V : N.Env Γ.boxIn c.ρ}
    {hN : ∀ v A (h : Γ.ref v = some (.VTypeBox A)),
      c.DefN A (V.ref (.step v .keep) (Ctx.ref_keep_of hF h))}
    {hP : ∀ v A (h : Γ.ref v = some (.VTypeDia A)),
      c.DefP A (V.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))} :
    Keyed hF (apexEnv c hT hB hS hInd hF hnp bv V hN hP) V :=
  ⟨fun u _ hu => by rw [apexEnv_ref u hu]; rfl, fun u _ hu => by rw [apexEnv_ref u hu]; rfl⟩

/-- The apex's objects at a larger context agree with those at a smaller one, when the base
    objects and `V` do. -/
theorem apexVal_mono {Γ' : Ctx} (hle : Γ.Le Γ') {bv : ∀ v, Γ.ref v = some .Var → c.D}
    {bv' : ∀ v, Γ'.ref v = some .Var → c.D} {V : N.Env Γ.boxIn c.ρ} {V' : N.Env Γ'.boxIn c.ρ}
    {hN : ∀ v A (h : Γ.ref v = some (.VTypeBox A)),
      c.DefN A (V.ref (.step v .keep) (Ctx.ref_keep_of hF h))}
    {hP : ∀ v A (h : Γ.ref v = some (.VTypeDia A)),
      c.DefP A (V.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))}
    {hN' : ∀ v A (h : Γ'.ref v = some (.VTypeBox A)),
      c.DefN A (V'.ref (.step v .keep) (Ctx.ref_keep_of hF h))}
    {hP' : ∀ v A (h : Γ'.ref v = some (.VTypeDia A)),
      c.DefP A (V'.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))}
    (hb : ∀ v (h : Γ.ref v = some .Var), bv' v (hle.ref h) = bv v h)
    (hV : ∀ v T (h : Γ.boxIn.ref v = some T), V'.ref v (hle.boxIn.ref h) = V.ref v h) :
    ∀ (T : VarType) (v : VarSymb) (h : Γ.ref v = some T),
      apexVal c hT hB hS hInd hF bv' V' hN' hP' T v (hle.ref h) =
        apexVal c hT hB hS hInd hF bv V hN hP T v h
  | .Var, v, h => hb v h
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A B, v, h =>
      Prod.ext (apexVal_mono hle hb hV A (.step v .fst) (Ctx.ref_fst_of h))
        (apexVal_mono hle hb hV B (.step v .snd) (Ctx.ref_snd_of h))
  | .VTypeBox _, v, h => Subtype.ext (hV (.step v .keep) _ (Ctx.ref_keep_of hF h))
  | .VTypeDia _, v, h => Subtype.ext (hV (.step v .keep) _ (Ctx.ref_keep_of' hF h
      VarType.keepable_dia))

/-- ⭐The apex's environments at two contexts agree, when the base objects and `V` do. -/
theorem apexEnv_agree {Γ' : Ctx} (hle : Γ.Le Γ') {hnp : Γ.NoProjLast} {hnp' : Γ'.NoProjLast}
    {bv : ∀ v, Γ.ref v = some .Var → c.D}
    {bv' : ∀ v, Γ'.ref v = some .Var → c.D} {V : N.Env Γ.boxIn c.ρ} {V' : N.Env Γ'.boxIn c.ρ}
    {hN : ∀ v A (h : Γ.ref v = some (.VTypeBox A)),
      c.DefN A (V.ref (.step v .keep) (Ctx.ref_keep_of hF h))}
    {hP : ∀ v A (h : Γ.ref v = some (.VTypeDia A)),
      c.DefP A (V.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))}
    {hN' : ∀ v A (h : Γ'.ref v = some (.VTypeBox A)),
      c.DefN A (V'.ref (.step v .keep) (Ctx.ref_keep_of hF h))}
    {hP' : ∀ v A (h : Γ'.ref v = some (.VTypeDia A)),
      c.DefP A (V'.ref (.step v .keep) (Ctx.ref_keep_of' hF h VarType.keepable_dia))}
    (hb : ∀ v (h : Γ.ref v = some .Var), bv' v (hle.ref h) = bv v h)
    (hV : ∀ v T (h : Γ.boxIn.ref v = some T), V'.ref v (hle.boxIn.ref h) = V.ref v h) :
    Env.Agree hle (apexEnv c hT hB hS hInd hF hnp bv V hN hP)
      (apexEnv c hT hB hS hInd hF hnp' bv' V' hN' hP') :=
  fun v T _ => (apexVal_mono hle hb hV T v _).symm

end ApexEnv

end ConeData

end Model

end V12M
