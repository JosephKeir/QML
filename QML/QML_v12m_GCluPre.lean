import QML.QML_v12m_GLimit
import QML.QML_v12m_GViewSubst
import QML.QML_v12m_CtxFin

/-!
# QML v12m — 5 on the growing tree: preimages along an edge

Names by origin (`docs/v12-modal-extensions.md` §3 5): under 5, with T off, every reachable
address of a liftable type of a child is named by its edge (`glorigin`): some kept parent item
`v.keep` has the entry `z`, or `z`'s η-term.  So a formula of the child's `□` view is the edge's
translation of a formula of the parent's `□` view read through the shift — `five_box`'s form.

* `Names`: the edge names `z` by `v`;
* `preI`: the preimage item map, from an address map `pre` (`z.box ↦ pre z .box`,
  `z.keep ↦ pre z .keep`), with `itemOk_preI`;
* ⭐`subst_shift_pre` (to come): the edge's translation of `shift (pre ψ)` is `ψ`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- The edge into `t` **names** `z` by the parent's address `v`: the entry of `v.keep` is `z`, or
    `z`'s η-term (`glorigin`). -/
def Names (t : GW hF M₀) (v z : VarSymb) : Prop :=
  fmapL hF M₀ t.1 (.step v .keep) = .inl z ∨
    ∃ (L : List VarType) (T : VarType) (hz : (ctxOf L).ref z = some T),
      fmapL hF M₀ t.1 (.step v .keep) = .inr ⟨L, T, _, Term.eta z T hz⟩

/-- The preimage item map of an address map: an item of `z` to the same item of `pre z`. -/
def preI (pre : VarSymb → VarSymb) : VarSymb → VarSymb
  | .step z .box => .step (pre z) .box
  | .step z .keep => .step (pre z) .keep
  | v => v

/-- An item of a `□` view has one level step. -/
theorem levels_boxIn_item {l : List VarType} {v : VarSymb} {T : VarType}
    (hl : v.lastProj = false) (h : (ctxOf l).boxIn v = some T) : Step.levels v.path = 1 := by
  obtain ⟨u, s, rfl, hu, -⟩ := boxIn_item h
  have hs : s.isProj = false := hl
  change Step.levels (u.path ++ [s]) = 1
  rw [Step.levels_append, levels_ppath hu, Step.levels_cons, if_neg (by simp [hs])]
  rfl

/-- ⭐**The preimage item map is well typed**, when `pre` keeps the type of every reachable
    keepable address. -/
theorem itemOk_preI {ls lt : List VarType} {pre : VarSymb → VarSymb}
    (hk : ModalSys.keepOnly = false)
    (hpre : ∀ z T, (ctxOf lt).ref z = some T → T.keepable = true →
      (ctxOf ls).ref (pre z) = some T) :
    ItemOk ((ctxOf lt).boxIn) ((ctxOf ls).boxIn) (preI pre) := by
  intro v T _ hv
  match v with
  | .step z .box =>
      obtain ⟨-, hz⟩ := Ctx.boxIn_box hv
      rw [Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_box_of hk (hpre z _ hz rfl)
  | .step z .keep =>
      obtain ⟨hF', hz, hkp⟩ := Ctx.boxIn_keep hv
      rw [Ctx.ref_nonproj _ rfl]
      exact Ctx.boxIn_keep_of' hF' (hpre z _ hz hkp) hkp
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

/-! ## The edge read through the shift, after the preimage -/

/-- The edge's `□`-view substitution into `t`, at the stage of `t` where stage `i` of `s` is
    committed. -/
noncomputable abbrev edgeBox (s t : GW hF M₀) (i : ℕ) :
    Subst σ (ctxOf (glat t (glstg s t i))).boxIn :=
  (eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)).box

theorem ok_edgeBox (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) :
    Subst.Ok (ctxOf (glat s i)).boxIn.boxIn (edgeBox s t i) :=
  Subst.ok_box (ok_eS_kView (gentOk_box hM₀ h i))

theorem coh_edgeBox (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) :
    Subst.Coh (eIdx (fmapL hF M₀ t.1)) (ctxOf (glat s i)).boxIn.boxIn (edgeBox s t i) :=
  Subst.coh_box (ok_eS_kView (gentOk_box hM₀ h i)) (coh_eS_kView (gentOk_box hM₀ h i))

theorem levels_boxIn (l : List VarType) :
    ∀ v T, v.lastProj = false → (ctxOf l).boxIn v = some T → Step.levels v.path = 1 :=
  fun _ _ hl h => levels_boxIn_item hl h

/-- The entry of a named address's kept item, when it is a term: the address's η-term. -/
theorem entOf_names_tm (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ)
    {v z : VarSymb}
    {U : VarType} (hv : (ctxOf (glat s i)).ref v = some U) (hkp : U.keepable = true)
    {L : List VarType} {T : VarType} (hz : (ctxOf L).ref z = some T)
    (he : fmapL hF M₀ t.1 (.step v .keep) = .inr ⟨L, T, _, Term.eta z T hz⟩) :
    ∃ (_ : T = U) (hz' : (ctxOf (glat t (glstg s t i))).ref z = some T),
      entOf (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1 (.step v .keep)) =
        .tm (Term.eta z T hz') := by
  have hok := gentOk_box hM₀ h i (.step v .keep) U rfl (Ctx.boxIn_keep_of' hF hv hkp)
  rw [he] at hok ⊢
  have hL : (ctxOf L).Le (ctxOf (glat t (glstg s t i))) := by
    by_contra hn
    rw [show entOf (ctxOf (glat t (glstg s t i))) (.inr ⟨L, T, _, Term.eta z T hz⟩) = .hide
      from dif_neg hn] at hok
    exact hok
  rw [show entOf (ctxOf (glat t (glstg s t i))) (.inr ⟨L, T, _, Term.eta z T hz⟩) =
    .tm (Term.mono hL (Term.eta z T hz)) from dif_pos hL, Term.mono_eta] at hok ⊢
  exact ⟨hok, _, rfl⟩

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A kept η-term is the η-term of the kept address, up to η. -/
theorem keepE_eta_sim {Δ : Ctx} (hk : ModalSys.keepOnly = false) (hF' : ModalSys.Four = true)
    {u : VarSymb} {T : VarType} (hu : Δ.ref u = some T) (hkp : T.keepable = true) :
    SubE.Sim T (SubE.keepE (.tm (Term.eta (σ := σ) u T hu))) (.ren (.step u .keep)) := by
  cases T with
  | VTypeBox A =>
      change SubE.Sim _ (SubE.keepE (.tm (.boxtm (Term.eta u.inner A (Ctx.ref_inner hu))))) _
      rw [SubE.keepE_tm _ hF']
      have e1 : (VarSymb.inner u).shift 0 = (VarSymb.step u .keep).inner := by
        rw [VarSymb.inner_box hk, VarSymb.inner_box hk, VarSymb.shift_level_zero rfl]
      have hr : Δ.boxIn.ref (.step u .keep) = some (.VTypeBox A) := Ctx.ref_keep_of hF' hu
      have H := (Term.shift_eta (σ := σ) (Ctx.shifts_boxIn_boxIn hF' Δ) u.inner A
        (Ctx.ref_inner hu)).trans (Term.eta_congr e1 A _ (Ctx.ref_inner hr))
      rw [show (SubE.tm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF' Δ)
          (Term.eta u.inner A (Ctx.ref_inner hu)))) : SubE σ Δ.boxIn) =
        SubE.tm (Term.boxtm (Term.eta (VarSymb.step u .keep).inner A (Ctx.ref_inner hr))) from
        congrArg (fun p : Σ b, Term σ Δ.boxIn.boxIn A b => SubE.tm (Term.boxtm p.2)) H]
      exact SubE.Sim.eta_ren (T := .VTypeBox A) (.step u .keep) hr
  | VTypeDia A =>
      change SubE.Sim _ (SubE.keepE (.tm (.diatm u ⟨A, hu⟩
        (Term.eta (.step u .dia) A (Ctx.ref_diaIn_of hu))))) _
      rw [SubE.keepE_dia _ _ _ hF']
      have hr : Δ.boxIn.ref (.step u .keep) = some (.VTypeDia A) :=
        Ctx.ref_keep_of' hF' hu VarType.keepable_dia
      have e1 : (VarSymb.step u .dia).shift 0 = .step (.step u .keep) .dia :=
        VarSymb.shift_level_zero rfl
      have H := (Term.shift_eta (σ := σ) (Ctx.shifts_diaIn_keep hF' Δ u) (.step u .dia) A
        (Ctx.ref_diaIn_of hu)).trans (Term.eta_congr e1 A _ (Ctx.ref_diaIn_of hr))
      rw [show (SubE.tm (Term.diatm (.step u .keep) (Ctx.exists_keep_dia hF' ⟨A, hu⟩)
          (Term.shift (Ctx.shifts_diaIn_keep hF' Δ u)
            (Term.eta (.step u .dia) A (Ctx.ref_diaIn_of hu)))) : SubE σ Δ.boxIn) =
        SubE.tm (Term.diatm (.step u .keep) ⟨A, hr⟩
          (Term.eta (.step (.step u .keep) .dia) A (Ctx.ref_diaIn_of hr))) from
        congrArg (fun p : Σ b, Term σ (Δ.boxIn.diaIn (.step u .keep)) A b =>
          SubE.tm (Term.diatm (.step u .keep) ⟨A, hr⟩ p.2)) H]
      exact SubE.Sim.eta_ren (T := .VTypeDia A) (.step u .keep) hr
  | Var => cases hkp
  | VTypeOne => cases hkp
  | VTypeProd _ _ => cases hkp

/-- An address map that **is a preimage along the edge** at stage `i` of the parent: it keeps the
    type of every reachable keepable address of `lt`, and the edge names the address by it. -/
def PreOk (s t : GW hF M₀) (i : ℕ) (lt : List VarType) (pre : VarSymb → VarSymb) : Prop :=
  ∀ z T, (ctxOf lt).ref z = some T → T.keepable = true →
    (ctxOf (glat s i)).ref (pre z) = some T ∧ Names t (pre z) z

/-- ⭐**The preimage, then the edge read through the shift, is the identity** on the child's `□`
    view, up to η (`docs/v12-modal-extensions.md` §3 5, names by origin). -/
theorem sim_pre_edge (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false)
    {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) {lt : List VarType}
    {pre : VarSymb → VarSymb} (hpre : PreOk s t i lt pre) :
    Subst.Sim ((ctxOf lt).boxIn)
      ((eS σ (ctxOf (glat s i)).boxIn (ofRen (preI pre))).comp
        (Subst.atShift (edgeBox s t i))
        (Subst.ok_atShift (Ctx.shifts_boxIn_boxIn hF _) (ok_edgeBox hM₀ h i))
        (Subst.coh_atShift (Ctx.shifts_boxIn_boxIn hF _) (ok_edgeBox hM₀ h i)
          (coh_edgeBox hM₀ h i) (levels_boxIn _)))
      (Subst.idS σ (ctxOf (glat t (glstg s t i))).boxIn) := by
  refine Subst.sim_of fun v T hl hv => ?_
  change SubE.Sim T ((eS σ (ctxOf (glat s i)).boxIn (ofRen (preI pre)) v).comp _ _ _) (.ren v)
  obtain ⟨u, st, rfl, -, -⟩ := boxIn_item hv
  rw [eS_item _ hl]
  change SubE.Sim T ((Subst.atShift (edgeBox s t i)).at (preI pre (.step u st))) (.ren _)
  rw [Subst.at_atShift]
  match st, hv with
  | .box, hv =>
      obtain ⟨-, hz⟩ := Ctx.boxIn_box hv
      obtain ⟨hpz, hn⟩ := hpre u _ hz rfl
      change SubE.Sim T ((edgeBox s t i).at (VarSymb.shift 0 (.step (pre u) .box))) _
      rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
      change SubE.Sim T (((eS σ _ (fmapL hF M₀ t.1)).at (.step (pre u) .keep)).unbox) _
      rw [Subst.at_nonproj _ rfl, eS_item _ rfl]
      rcases hn with he | ⟨L, U, hz', he⟩
      · rw [he]
        change SubE.Sim T (.ren u.inner) _
        rw [VarSymb.inner_box hk]
        exact .refl _
      · obtain ⟨rfl, hz'', e⟩ := entOf_names_tm hM₀ h i hpz rfl hz' he
        rw [e]
        change SubE.Sim T (.tm (Term.eta u.inner T (Ctx.ref_inner hz''))) _
        generalize Ctx.ref_inner hz'' = hp
        revert hp
        rw [VarSymb.inner_box hk]
        exact fun hp => .eta_ren _ hp
  | .keep, hv =>
      obtain ⟨hF', hz, hkp⟩ := Ctx.boxIn_keep hv
      obtain ⟨hpz, hn⟩ := hpre u _ hz hkp
      change SubE.Sim T ((edgeBox s t i).at (VarSymb.shift 0 (.step (pre u) .keep))) _
      rw [VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
      change SubE.Sim T (((eS σ _ (fmapL hF M₀ t.1)).at (.step (pre u) .keep)).keepE) _
      rw [Subst.at_nonproj _ rfl, eS_item _ rfl]
      rcases hn with he | ⟨L, U, hz', he⟩
      · rw [he]
        exact .refl _
      · obtain ⟨rfl, hz'', e⟩ := entOf_names_tm hM₀ h i hpz hkp hz' he
        rw [e]
        exact keepE_eta_sim hk hF' hz'' hkp
  | .fst, hv => cases hv
  | .snd, hv => cases hv
  | .dia, hv => cases hv
  | .here, hv => cases hv

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem simE_symm {Δ : Ctx} {T : VarType} {e e' : SubE σ Δ} (h : SubE.Sim T e e') :
    SubE.Sim T e' e := by
  cases h with
  | refl => exact .refl _
  | eta_ren w h => exact .ren_eta w h
  | ren_eta w h => exact .eta_ren w h

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem simS_symm {Γ Δ : Ctx} {θ θ' : Subst σ Δ} (h : Subst.Sim Γ θ θ') : Subst.Sim Γ θ' θ :=
  fun v T hv => simE_symm (h v T hv)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Substituting every address for itself into a larger context is weakening. -/
theorem subst_idS_le {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots] (hle : Γ.Le Δ) (ψ : WFF σ Γ 0) :
    WFF.subst id (Subst.idS σ Δ) (Subst.ok_idS_le hle) (Subst.coh_idS_le hle)
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ = WFF.mono hle ψ := by
  have h := WFF.subst_mono_eq (Ctx.Le.refl Γ) hle (Subst.idS σ Γ) Subst.ok_idS Subst.coh_idS
    (Subst.idS σ Δ) (Subst.ok_idS_le hle) (Subst.coh_idS_le hle) Ctx.NoSlots.slots
    Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots
    (fun v T _ => by rw [Subst.at_idS, Subst.at_mono, Subst.at_idS]; exact .refl _) ψ
  rwa [WFF.mono_refl, WFF.subst_id] at h

/-- The preimage of a formula of the child's `□` view, in the parent's `□` view. -/
noncomputable def preW (hk : ModalSys.keepOnly = false) {s t : GW hF M₀} {i : ℕ}
    {lt : List VarType} {pre : VarSymb → VarSymb} (hpre : PreOk s t i lt pre)
    (ψ : WFF σ (ctxOf lt).boxIn 0) : WFF σ (ctxOf (glat s i)).boxIn 0 :=
  WFF.subst (eIdx (ofRen (preI pre))) (eS σ (ctxOf (glat s i)).boxIn (ofRen (preI pre)))
    (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hk fun z T hz hkp => (hpre z T hz hkp).1)))
    (coh_eS_kView (k := none)
      (entOk_ofRen (itemOk_preI hk fun z T hz hkp => (hpre z T hz hkp).1)))
    Ctx.NoSlots.slots Ctx.NoSlots.slots ψ

/-- ⭐**A formula of the child's `□` view is the edge's translation of its preimage, read
    through the shift** (`docs/v12-modal-extensions.md` §3 5): `five_box`'s and `four_box`'s
    form, so `□ψ` at the child and `□ (preW ψ)` at the parent stand or fall together. -/
theorem subst_shift_pre (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false)
    {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) {lt : List VarType}
    (hle : (ctxOf lt).Le (ctxOf (glat t (glstg s t i)))) {pre : VarSymb → VarSymb}
    (hpre : PreOk s t i lt pre) (ψ : WFF σ (ctxOf lt).boxIn 0) :
    WFF.subst (eIdx (fmapL hF M₀ t.1)) (edgeBox s t i) (ok_edgeBox hM₀ h i)
        (coh_edgeBox hM₀ h i) Ctx.NoSlots.slots Ctx.NoSlots.slots
        (WFF.shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots (preW hk hpre ψ)) =
      WFF.mono hle.boxIn ψ := by
  unfold preW
  rw [WFF.subst_shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots Ctx.NoSlots.slots _
      (ok_edgeBox hM₀ h i) (coh_edgeBox hM₀ h i) (Subst.atShift (edgeBox s t i))
      (Subst.ok_atShift (Ctx.shifts_boxIn_boxIn hF _) (ok_edgeBox hM₀ h i))
      (Subst.coh_atShift (Ctx.shifts_boxIn_boxIn hF _) (ok_edgeBox hM₀ h i)
        (coh_edgeBox hM₀ h i) (levels_boxIn _))
      Ctx.NoSlots.slots (Subst.preShift_atShift _ _),
    WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le hle.boxIn)
      (Subst.coh_idS_le hle.boxIn) Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots
      (simS_symm (sim_pre_edge hM₀ hk h i hpre)) ψ]
  exact subst_idS_le hle.boxIn ψ

/-- ⭐**Cluster uniformity along an edge** (`docs/v12-modal-extensions.md` §3 5): under 4 and 5, a
    child's `□`-formula holds exactly when its preimage's does at the parent — by `four_box` and
    the edge's transfer one way, the transfer's contrapositive and `five_box` the other. -/
theorem box_pre_iff (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false)
    (hV : ModalSys.Five = true) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ)
    {lt : List VarType} (hle : (ctxOf lt).Le (ctxOf (glat t (glstg s t i))))
    {pre : VarSymb → VarSymb} (hpre : PreOk s t i lt pre) (ψ : WFF σ (ctxOf lt).boxIn 0) :
    WFF.box (preW hk hpre ψ) ∈ ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M ↔
      WFF.box (WFF.mono hle.boxIn ψ) ∈ ((gnet hF M₀ (grnd s t i)).st t.1).M := by
  have hsm : Theory.IsMCS ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M :=
    (good_gnet hF hM₀ _).mcs s.1 (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i))
  have htm : Theory.IsMCS ((gnet hF M₀ (grnd s t i)).st t.1).M :=
    (good_gnet hF hM₀ _).mcs t.1 (live_gbirth hF hM₀ t.2 (Nat.le_add_right _ _))
  have key := subst_shift_pre hM₀ hk h i hle hpre ψ
  constructor
  · intro hb
    have h4 : WFF.box (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF _) Ctx.NoSlots.slots
        (preW hk hpre ψ))) ∈ ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M :=
      hsm.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact hb,
        ⟨Proof.four_box hF (Proof.lookup List.mem_cons_self)⟩⟩
    rw [← key]
    exact gltr hM₀ h i _ h4
  · intro hb
    rw [← key] at hb
    by_contra hn
    have h5 : WFF.box (WFF.neg (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF _)
        Ctx.NoSlots.slots (preW hk hpre ψ)))) ∈
        ((gnet hF M₀ (gbirth hF M₀ s.2 + i)).st s.1).M := by
      by_contra hn'
      exact hn (hsm.closed ⟨[_], fun x hx => by
        rw [List.mem_singleton.mp hx]; exact hsm.neg_mem_iff.mpr hn',
        ⟨Proof.five_box hF hV (Proof.lookup List.mem_cons_self)⟩⟩)
    exact htm.neg_mem_iff.mp (gltr hM₀ h i _ h5) hb

/-! ## Preimages exist -/

omit [ModalSys] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A root-only language declares finitely many addresses. -/
theorem ctxOf_fin : ∀ l : List VarType, (ctxOf l).Fin
  | [] => by
      change {v | (Ctx.ofDecls (decls []) v).isSome}.Finite
      convert Set.finite_empty
      ext v
      simp [Ctx.ofDecls, decls, Ctx.empty]
  | A :: l => by
      rw [ctxOf_cons]
      exact (ctxOf_fin l).insert _ A

/-- A world's language grows with its stages. -/
theorem glat_suffix (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) {i i' : ℕ} (h : i ≤ i') :
    glat s i <:+ glat s i' :=
  gnet_lang_suffix hF hM₀ (by omega) (live_gbirth hF hM₀ s.2 (Nat.le_add_right _ i))

/-- Two stages' languages agree on what both declare. -/
theorem glat_ref_agree (hM₀ : Theory.IsMCS M₀) (t : GW hF M₀) {j j' : ℕ} {z : VarSymb}
    {T T' : VarType} (h : (ctxOf (glat t j)).ref z = some T)
    (h' : (ctxOf (glat t j')).ref z = some T') : T = T' := by
  rcases le_total j j' with hjj | hjj
  · exact Option.some.inj (((ctxOf_le_of_suffix (glat_suffix hM₀ t hjj)).ref h).symm.trans h')
  · exact Option.some.inj (h.symm.trans ((ctxOf_le_of_suffix (glat_suffix hM₀ t hjj)).ref h'))

/-- The parent's address that names a child's address has its type. -/
theorem names_type (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) {i j : ℕ}
    {v z : VarSymb} {U T : VarType} (hv : (ctxOf (glat s i)).ref v = some U)
    (hkp : U.keepable = true) (hn : Names t v z) (hz : (ctxOf (glat t j)).ref z = some T) :
    U = T := by
  rcases hn with he | ⟨L, T', hz', he⟩
  · have hok := gentOk_box hM₀ h i (.step v .keep) U rfl (Ctx.boxIn_keep_of' hF hv hkp)
    rw [he] at hok
    exact glat_ref_agree hM₀ t hok hz
  · obtain ⟨rfl, hz'', -⟩ := entOf_names_tm hM₀ h i hv hkp hz' he
    exact glat_ref_agree hM₀ t hz'' hz

/-- ⭐**Every stage of a child has a preimage along its edge**, at a stage of the parent committed
    no earlier than it (names by origin, `glorigin`; both lifts on, so every keepable address is
    liftable). -/
theorem exists_pre (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (j : ℕ) :
    ∃ (i : ℕ) (pre : VarSymb → VarSymb), j ≤ glstg s t i ∧ PreOk s t i (glat t j) pre := by
  classical
  have hor : ∀ z T, (ctxOf (glat t j)).ref z = some T → T.keepable = true →
      ∃ (i : ℕ) (v : VarSymb), (ctxOf (glat s i)).ref v = some T ∧ Names t v z := by
    intro z T hz hkp
    have hl : T.liftable = true := by
      cases T <;> simp_all [VarType.liftable, VarType.keepable]
    obtain ⟨i, v, U, hv, hkU, hn⟩ := glorigin hV hT hM₀ h j hz hl
    obtain rfl := names_type hM₀ h hv hkU hn hz
    exact ⟨i, v, hv, hn⟩
  let P : VarSymb → Prop := fun z =>
    ∃ T, (ctxOf (glat t j)).ref z = some T ∧ T.keepable = true
  let iz : VarSymb → ℕ := fun z =>
    if hz : P z then (hor z _ hz.choose_spec.1 hz.choose_spec.2).choose else 0
  let pre : VarSymb → VarSymb := fun z =>
    if hz : P z then (hor z _ hz.choose_spec.1 hz.choose_spec.2).choose_spec.choose else z
  obtain ⟨N, hN⟩ := ((Ctx.Fin.reach (ctxOf_fin (glat t j))).image iz).bddAbove
  refine ⟨max N (gbirth hF M₀ t.2 + j), pre, ?_, ?_⟩
  · have := (glstg_spec hM₀ h (max N (gbirth hF M₀ t.2 + j))).1
    omega
  · intro z T hz hkp
    have hP : P z := ⟨T, hz, hkp⟩
    have hc := (hor z _ hP.choose_spec.1 hP.choose_spec.2).choose_spec.choose_spec
    have hTT : hP.choose = T := Option.some.inj (hP.choose_spec.1.symm.trans hz)
    have hiz : iz z ≤ max N (gbirth hF M₀ t.2 + j) :=
      (hN ⟨z, by simp [hz], rfl⟩).trans (le_max_left _ _)
    simp only [iz, dif_pos hP] at hiz
    simp only [pre, dif_pos hP]
    refine ⟨?_, hc.2⟩
    rw [← hTT]
    exact (ctxOf_le_of_suffix (glat_suffix hM₀ s hiz)).ref hc.1

end GArrow

end V12M
