import QML.QML_v12m_GCluPre
import QML.QML_v12m_GCluNames

/-!
# QML v12m — 5 on the growing tree: preimages of `◇_x` views

The `◇` counterpart of `QML_v12m_GCluPre.lean` (`docs/v12-modal-extensions.md` §3 5, the cluster
model's R2): a formula of a child's `◇_x` view is the edge's translation, inside
`◇_{(pre x).keep}`, of a formula of the parent's `◇_{pre x}` view read through `four_dia`'s shift.

* `preIX`, `itemOk_preIX`, `preWX`: the preimage of a `◇_x` view (`x.dia ↦ (pre x).dia`);
* `edgeDia`: the edge's substitution inside `◇_{z.keep}`, at the witness `x`;
* ⭐`sim_preX_edge`, ⭐`subst_shift_preX`, `subst_dia_preX`;
* ⭐`dia_pre_iff`, ⭐`dia_path_iff`: `◇`-uniformity along an edge and along a path.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- The preimage item map of a `◇_x` view: `x.dia` to `(pre x).dia`, the rest as `preI`. -/
def preIX (pre : VarSymb → VarSymb) (x : VarSymb) (v : VarSymb) : VarSymb :=
  if v = .step x .dia then .step (pre x) .dia else preI pre v

/-- The preimage item map of a `◇_x` view is well typed. -/
theorem itemOk_preIX {ls lt : List VarType} {pre : VarSymb → VarSymb}
    (hk : ModalSys.keepOnly = false) {x : VarSymb} {X : VarType}
    (hx : (ctxOf lt).ref x = some (.VTypeDia X))
    (hpre : ∀ z T, (ctxOf lt).ref z = some T → T.keepable = true →
      (ctxOf ls).ref (pre z) = some T) :
    ItemOk ((ctxOf lt).diaIn x) ((ctxOf ls).diaIn (pre x)) (preIX pre x) := by
  intro v T hl hv
  by_cases hvx : v = .step x .dia
  · subst hvx
    unfold preIX
    rw [if_pos rfl]
    have hT : T = X := Option.some.inj (hv.symm.trans
      ((Ctx.ref_nonproj _ (v := .step x .dia) rfl).symm.trans (Ctx.ref_diaIn_of hx)))
    subst hT
    exact Ctx.ref_diaIn_of (hpre x _ hx rfl)
  · unfold preIX
    rw [if_neg hvx]
    exact (Ctx.le_boxIn_diaIn _ _).ref
      (itemOk_preI hk hpre v T hl (diaIn_boxIn_of_ne' hv hvx))

/-- The preimage of a formula of a child's `◇_x` view, in the parent's `◇_{pre x}` view. -/
noncomputable def preWX (hk : ModalSys.keepOnly = false) {s t : GW hF M₀} {i : ℕ}
    {lt : List VarType} {pre : VarSymb → VarSymb} (hpre : PreOk s t i lt pre) {x : VarSymb}
    {X : VarType} (hx : (ctxOf lt).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf lt).diaIn x) 0) : WFF σ ((ctxOf (glat s i)).diaIn (pre x)) 0 :=
  WFF.subst (eIdx (ofRen (preIX pre x)))
    (eS σ ((ctxOf (glat s i)).diaIn (pre x)) (ofRen (preIX pre x)))
    (ok_eS_kView (k := some x)
      (entOk_ofRen (itemOk_preIX hk hx fun z T hz hkp => (hpre z T hz hkp).1)))
    (coh_eS_kView (k := some x)
      (entOk_ofRen (itemOk_preIX hk hx fun z T hz hkp => (hpre z T hz hkp).1)))
    Ctx.NoSlots.slots Ctx.NoSlots.slots ψ

/-- The edge's substitution of the parent's `□` view into the child. -/
noncomputable abbrev edgeS (s t : GW hF M₀) (i : ℕ) :
    Subst σ (ctxOf (glat t (glstg s t i))) :=
  eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1)

/-- A named possible address's kept item has the address as its index. -/
theorem idx_names (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ)
    {z x : VarSymb} {X : VarType} (hz : (ctxOf (glat s i)).ref z = some (.VTypeDia X))
    (hn : Names t z x) : eIdx (fmapL hF M₀ t.1) (.step z .keep) = x := by
  rw [show (VarSymb.step z .keep) = (VarSymb.step z .keep).ext [] from rfl,
    eIdx_item _ (reach_ppath hz).1 rfl []]
  rcases hn with he | ⟨L, T, hx, he⟩
  · rw [he]
    rfl
  · obtain ⟨rfl, -, -⟩ := entOf_names_tm hM₀ h i hz rfl hx he
    rw [he]
    rfl

/-- The edge's substitution inside `◇_{z.keep}`, at the witness `x` its kept item names. -/
noncomputable abbrev edgeDia (s t : GW hF M₀) (i : ℕ) (z x : VarSymb) :
    Subst σ ((ctxOf (glat t (glstg s t i))).diaIn x) :=
  (edgeS s t i).dia (.step z .keep) x

theorem ok_edgeDia (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ)
    {z x : VarSymb} {X : VarType} (hz : (ctxOf (glat s i)).ref z = some (.VTypeDia X))
    (hn : Names t z x) :
    Subst.Ok ((ctxOf (glat s i)).boxIn.diaIn (.step z .keep)) (edgeDia s t i z x) :=
  Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ h i)) (Ctx.exists_keep_dia hF ⟨X, hz⟩)
    ((coh_eS_kView (gentOk_box hM₀ h i) _ _ (Ctx.exists_keep_dia hF ⟨X, hz⟩).choose_spec
      []).trans (idx_names hM₀ h i hz hn))

theorem coh_edgeDia (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ)
    {z x : VarSymb} {X : VarType} (hz : (ctxOf (glat s i)).ref z = some (.VTypeDia X))
    (hn : Names t z x) :
    Subst.Coh (eIdx (fmapL hF M₀ t.1)) ((ctxOf (glat s i)).boxIn.diaIn (.step z .keep))
      (edgeDia s t i z x) :=
  idx_names hM₀ h i hz hn ▸ Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ h i))
    (coh_eS_kView (gentOk_box hM₀ h i)) (Ctx.exists_keep_dia hF ⟨X, hz⟩)

theorem levels_diaIn (l : List VarType) (z : VarSymb) :
    ∀ v T, v.lastProj = false → (ctxOf l).diaIn z v = some T → Step.levels v.path = 1 := by
  intro v T hl hv
  by_cases hvz : v = .step z .dia
  · subst hvz
    have hz : ∃ Z, (ctxOf l).ref z = some (.VTypeDia Z) := by
      change (if z = z then (match (ctxOf l).ref z with
        | some (.VTypeDia X) => some X | _ => none) else none) = some T at hv
      rw [if_pos rfl] at hv
      split at hv
      · exact ⟨_, by assumption⟩
      · cases hv
    obtain ⟨Z, hZ⟩ := hz
    change Step.levels (z.path ++ [.dia]) = 1
    rw [Step.levels_append, levels_ppath (reach_ppath hZ).1]
    rfl
  · exact levels_boxIn_item hl (diaIn_boxIn_of_ne' hv hvz)

/-- ⭐**The preimage of a `◇_x` view, then the edge read through `four_dia`'s shift, is the
    identity**, up to η. -/
theorem sim_preX_edge (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false)
    {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) {lt : List VarType}
    {pre : VarSymb → VarSymb} (hpre : PreOk s t i lt pre) {x : VarSymb} {X : VarType}
    (hx : (ctxOf lt).ref x = some (.VTypeDia X)) :
    Subst.Sim ((ctxOf lt).diaIn x)
      ((eS σ ((ctxOf (glat s i)).diaIn (pre x)) (ofRen (preIX pre x))).comp
        (Subst.atShift (edgeDia s t i (pre x) x))
        (Subst.ok_atShift (Ctx.shifts_diaIn_keep hF _ (pre x))
          (ok_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2))
        (Subst.coh_atShift (Ctx.shifts_diaIn_keep hF _ (pre x))
          (ok_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2)
          (coh_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2) (levels_diaIn _ _)))
      (Subst.idS σ ((ctxOf (glat t (glstg s t i))).diaIn x)) := by
  obtain ⟨hz, hn⟩ := hpre x _ hx rfl
  refine Subst.sim_of fun v T hl hv => ?_
  change SubE.Sim T ((eS σ ((ctxOf (glat s i)).diaIn (pre x)) (ofRen (preIX pre x)) v).comp
    _ _ _) (.ren v)
  obtain ⟨u, st, rfl, -, -⟩ := kView_item (k := some x) hv
  rw [eS_item _ hl]
  generalize hvs : VarSymb.step u st = v at *
  change SubE.Sim T ((Subst.atShift (edgeDia s t i (pre x) x)).at (preIX pre x v)) (.ren v)
  rw [Subst.at_atShift]
  by_cases hvx : v = .step x .dia
  · subst hvx
    have hT : T = X := Option.some.inj (hv.symm.trans
      ((Ctx.ref_nonproj _ (v := .step x .dia) rfl).symm.trans (Ctx.ref_diaIn_of hx)))
    subst hT
    rw [show preIX pre x (.step x .dia) = .step (pre x) .dia from if_pos rfl,
      VarSymb.shift_level_zero rfl, Subst.at_nonproj _ rfl]
    change SubE.Sim T (if VarSymb.step (pre x) .keep = .step (pre x) .keep then
      ((edgeS s t i).at (.step (pre x) .keep)).diaBody x else .hide) _
    rw [if_pos rfl, Subst.at_nonproj _ rfl, edgeS, eS_item _ rfl]
    rcases hn with he | ⟨L, U, hz', he⟩
    · rw [he]
      exact .refl _
    · obtain ⟨rfl, hz'', e⟩ := entOf_names_tm hM₀ h i hz rfl hz' he
      rw [e]
      unfold Term.eta
      rw [SubE.diaBody_diatm]
      exact .eta_ren _ _
  · rw [show preIX pre x v = preI pre v from if_neg hvx]
    have hb := diaIn_boxIn_of_ne' hv hvx
    have hpv := itemOk_preI hk (fun z T hz hkp => (hpre z T hz hkp).1) v T hl hb
    rw [Subst.dia_eq_box_mono (edgeS s t i) (.step (pre x) .keep) x _ T
      (Ctx.shifts_boxIn_boxIn hF _ _ T hpv)]
    have H := sim_pre_edge hM₀ hk h i hpre v T ((Ctx.ref_nonproj _ hl).trans hb)
    rw [Subst.at_nonproj _ hl, Subst.at_idS] at H
    change SubE.Sim T (((eS σ _ (ofRen (preI pre))) v).comp _ _ _) _ at H
    subst hvs
    rw [eS_item _ hl] at H
    change SubE.Sim T ((Subst.atShift (edgeBox s t i)).at (preI pre _)) _ at H
    rw [Subst.at_atShift] at H
    exact H.mono _

/-- ⭐**A formula of a child's `◇_x` view is the edge's translation of its preimage, read through
    `four_dia`'s shift**: `five_dia`'s and `four_dia`'s form. -/
theorem subst_shift_preX (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false)
    {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) {lt : List VarType}
    (hle : (ctxOf lt).Le (ctxOf (glat t (glstg s t i)))) {pre : VarSymb → VarSymb}
    (hpre : PreOk s t i lt pre) {x : VarSymb} {X : VarType}
    (hx : (ctxOf lt).ref x = some (.VTypeDia X)) (ψ : WFF σ ((ctxOf lt).diaIn x) 0) :
    WFF.subst (eIdx (fmapL hF M₀ t.1)) (edgeDia s t i (pre x) x)
        (ok_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2)
        (coh_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2)
        Ctx.NoSlots.slots Ctx.NoSlots.slots
        (WFF.shift (Ctx.shifts_diaIn_keep hF _ (pre x)) Ctx.NoSlots.slots
          (preWX hk hpre hx ψ)) =
      WFF.mono (hle.diaIn x) ψ := by
  unfold preWX
  rw [WFF.subst_shift (Ctx.shifts_diaIn_keep hF _ (pre x)) Ctx.NoSlots.slots Ctx.NoSlots.slots
      _ (ok_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2)
      (coh_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2)
      (Subst.atShift (edgeDia s t i (pre x) x))
      (Subst.ok_atShift (Ctx.shifts_diaIn_keep hF _ (pre x))
        (ok_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2))
      (Subst.coh_atShift (Ctx.shifts_diaIn_keep hF _ (pre x))
        (ok_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2)
        (coh_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2) (levels_diaIn _ _))
      Ctx.NoSlots.slots (Subst.preShift_atShift _ _),
    WFF.subst_comp _ _ (Subst.idS σ _) _ _ _ _ (Subst.ok_idS_le (hle.diaIn x))
      (Subst.coh_idS_le (hle.diaIn x)) Ctx.NoSlots.slots Ctx.NoSlots.slots Ctx.NoSlots.slots
      (simS_symm (sim_preX_edge hM₀ hk h i hpre hx)) ψ]
  exact subst_idS_le (hle.diaIn x) ψ

/-- The edge translates `◇_{(pre x).keep}` of a preimage, read through `four_dia`'s shift, into
    `◇_x` of the formula. -/
theorem subst_dia_preX (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false)
    {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ) {lt : List VarType}
    (hle : (ctxOf lt).Le (ctxOf (glat t (glstg s t i)))) {pre : VarSymb → VarSymb}
    (hpre : PreOk s t i lt pre) {x : VarSymb} {X : VarType}
    (hx : (ctxOf lt).ref x = some (.VTypeDia X)) (ψ : WFF σ ((ctxOf lt).diaIn x) 0) :
    WFF.subst (eIdx (fmapL hF M₀ t.1)) (edgeS s t i) (ok_eS_kView (gentOk_box hM₀ h i))
        (coh_eS_kView (gentOk_box hM₀ h i)) Ctx.NoSlots.slots Ctx.NoSlots.slots
        (WFF.dia (.step (pre x) .keep) (Ctx.exists_keep_dia hF ⟨X, (hpre x _ hx rfl).1⟩)
          (WFF.shift (Ctx.shifts_diaIn_keep hF _ (pre x)) Ctx.NoSlots.slots
            (preWX hk hpre hx ψ))) =
      WFF.mono hle (WFF.dia x ⟨X, hx⟩ ψ) := by
  rw [WFF.subst_dia _ _ _ _ _ _ x (idx_names hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2)
    ⟨X, hle.ref hx⟩ (ok_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2)
    (coh_edgeDia hM₀ h i (hpre x _ hx rfl).1 (hpre x _ hx rfl).2) Ctx.NoSlots.slots]
  exact congrArg (WFF.dia x ⟨X, hle.ref hx⟩) (subst_shift_preX hM₀ hk h i hle hpre hx ψ)

/-- ⭐**`◇`-uniformity along an edge** (`docs/v12-modal-extensions.md` §3 5, R2): under 4 and 5,
    a child's `◇_x ψ` holds exactly when `◇_{pre x}` of its preimage does at the parent — by
    `five_dia` and the edge's transfer one way, `four_dia` and the transfer's contrapositive the
    other. -/
theorem dia_pre_iff (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false)
    (hV : ModalSys.Five = true) {s t : GW hF M₀} (h : GCh hF M₀ s t) (i : ℕ)
    {lt : List VarType} (hle : (ctxOf lt).Le (ctxOf (glat t (glstg s t i))))
    {pre : VarSymb → VarSymb} (hpre : PreOk s t i lt pre) {x : VarSymb} {X : VarType}
    (hx : (ctxOf lt).ref x = some (.VTypeDia X)) (ψ : WFF σ ((ctxOf lt).diaIn x) 0) :
    WFF.dia (pre x) ⟨X, (hpre x _ hx rfl).1⟩ (preWX hk hpre hx ψ) ∈ gMs s i ↔
      WFF.mono hle (WFF.dia x ⟨X, hx⟩ ψ) ∈ ((gnet hF M₀ (grnd s t i)).st t.1).M := by
  have hsm := gMs_mcs hM₀ s i
  have htm : Theory.IsMCS ((gnet hF M₀ (grnd s t i)).st t.1).M :=
    (good_gnet hF hM₀ _).mcs t.1 (live_gbirth hF hM₀ t.2 (Nat.le_add_right _ _))
  have hz : ∃ Z, (ctxOf (glat s i)).ref (pre x) = some (.VTypeDia Z) :=
    ⟨X, (hpre x _ hx rfl).1⟩
  constructor
  · intro hd
    have h5 : WFF.box (WFF.dia (.step (pre x) .keep) (Ctx.exists_keep_dia hF hz)
        (WFF.shift (Ctx.shifts_diaIn_keep hF _ (pre x)) Ctx.NoSlots.slots
          (preWX hk hpre hx ψ))) ∈ gMs s i :=
      hsm.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hd,
        ⟨Proof.five_dia hF hV hz (Proof.lookup List.mem_cons_self)⟩⟩
    rw [← subst_dia_preX hM₀ hk h i hle hpre hx ψ]
    exact gltr hM₀ h i _ h5
  · intro hb
    by_contra hn
    have hbx : WFF.boxx (pre x) hz (preWX hk hpre hx ψ).neg ∈ gMs s i :=
      hsm.closed ⟨[_], fun y hy => by
        rw [List.mem_singleton.mp hy]; exact hsm.neg_mem_iff.mpr hn,
        ⟨Proof.boxx_neg_of_not_dia (pre x) hz _⟩⟩
    have h4 : WFF.box (WFF.boxx (.step (pre x) .keep) (Ctx.exists_keep_dia hF hz)
        (WFF.shift (Ctx.shifts_diaIn_keep hF _ (pre x)) Ctx.NoSlots.slots
          (preWX hk hpre hx ψ).neg)) ∈ gMs s i :=
      hsm.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact hbx,
        ⟨Proof.four_dia hF hz (Proof.lookup List.mem_cons_self)⟩⟩
    have hnn : (WFF.mono hle (WFF.dia x ⟨X, hx⟩ ψ.neg.neg)).neg ∈
        ((gnet hF M₀ (grnd s t i)).st t.1).M := by
      rw [← subst_dia_preX hM₀ hk h i hle hpre hx ψ.neg.neg]
      exact gltr hM₀ h i _ h4
    refine htm.neg_mem_iff.mp hnn (htm.closed ⟨[_], fun y hy => by
      rw [List.mem_singleton.mp hy]; exact hb, ⟨Proof.ofSubset (fun y hy => by simpa using hy)
        (Proof.K_dia (Δ₁ := []) (Δ₂ := []) x _ ?_)⟩⟩)
    exact .imp_intro (.imp_elim (Proof.lookup List.mem_cons_self)
      (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- ⭐**`◇`-uniformity along a path** (`docs/v12-modal-extensions.md` §3 5, R2): a `◇_x`-formula
    at a descendant's stage holds, at some later stage of it, exactly when a `◇`-formula holds at
    the ancestor — at the witness's preimage, of the body's preimage, edge by edge. -/
theorem dia_path_iff (hV : ModalSys.Five = true)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false) :
    ∀ (P : List ℕ) (s t : GW hF M₀), t.1 = nodeOf s.1 P → ∀ (j : ℕ) (x : VarSymb) (X : VarType)
      (hx : (ctxOf (glat t j)).ref x = some (.VTypeDia X))
      (ψ : WFF σ ((ctxOf (glat t j)).diaIn x) 0),
      ∃ (i j' : ℕ) (hjj : j ≤ j') (x' : VarSymb)
        (hx' : (ctxOf (glat s i)).ref x' = some (.VTypeDia X))
        (ψ' : WFF σ ((ctxOf (glat s i)).diaIn x') 0),
        WFF.dia x' ⟨X, hx'⟩ ψ' ∈ gMs s i ↔
          WFF.mono (ctxOf_le_of_suffix (glat_suffix hM₀ t hjj)) (WFF.dia x ⟨X, hx⟩ ψ) ∈ gMs t j'
  | [], s, t, hP, j, x, X, hx, ψ => by
      obtain rfl : t = s := gw_eq hP
      exact ⟨j, j, le_rfl, x, hx, ψ, by rw [WFF.mono_refl]⟩
  | c :: P, s, t, hP, j, x, X, hx, ψ => by
      have hb := born_step hP
      obtain ⟨i', j', hjj, x', hx', ψ', hiff⟩ :=
        dia_path_iff hV hS hW hM₀ hk P (stepW s c hb) t hP j x X hx ψ
      have hch : GCh hF M₀ s (stepW s c hb) := ⟨c, rfl⟩
      obtain ⟨i, pre, hi', hpre⟩ := exists_pre hV hS hW hM₀ hch i'
      have hle := ctxOf_le_of_suffix (glat_suffix hM₀ (stepW s c hb) hi')
      refine ⟨i, j', hjj, pre x', (hpre x' _ hx' rfl).1, preWX hk hpre hx' ψ', ?_⟩
      rw [dia_pre_iff hM₀ hk hV hch i hle hpre hx' ψ', ← hiff]
      exact (gMs_mono_iff hM₀ (stepW s c hb) hi' _).symm

end GArrow

end V12M
