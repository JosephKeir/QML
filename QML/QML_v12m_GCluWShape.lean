import QML.QML_v12m_GCluModel

/-!
# QML v12m — 5 on the growing tree: shapes in a world's environment

Under T the truth lemma for terms compares a term's shape in an environment with the shape of its
denotation, which is its annotation's, read at the root (`crawShape_cden`).  An environment at a
world is pushed into views as at the root (`CPushed`), with its addresses read at the root:

* `preIx_step`: reading at the root commutes with a level step, and with any step below one.
* `CInvW w τ j`: `τ` reads every reachable address `y` at the shape of its root reading
  `preIx w y`, anchored at `w`.  At the first level this is asked of the keepable addresses only:
  they are the ones a view reads, and the others have no root reading.
* ⭐`CInvW.box`, `CInvW.dia`, ⭐`termShp_annW`: pushing keeps the invariant, so a term's shape in
  such an environment is its annotation's, read at the root.
* `postIx_preIx`, ⭐`ann_eq_of_termShpW`: positions of `◇` type are read at the root faithfully,
  so in such an environment shapes determine annotations.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-- Reading at the root commutes with a level step, and with any step below one. -/
theorem preIx_step (s : GW hF M₀) (z : VarSymb) {st : Step}
    (hl : 0 < Step.levels z.path ∨ st.isProj = false) :
    preIx s (.step z st) = .step (preIx s z) st := by
  by_cases h0 : Step.levels z.path = 0
  · have hz := ppath_of_levels0 h0
    have hst : st.isProj = false := hl.resolve_left (by omega)
    rw [preIx_ppath s hz]
    exact preIx_lvl s hz hst []
  · obtain ⟨q, st', r, hq, hq₀, hst'⟩ := split_first z.path (by omega)
    have e : z = (VarSymb.step ((VarSymb.root z.rt).ext q) st').ext r := by
      conv_lhs => rw [VarSymb.eq_root_ext z, hq, VarSymb.ext_append]
      rfl
    have hp : PPath ((VarSymb.root z.rt).ext q).path := by
      rw [VarSymb.ext_path]
      simpa [VarSymb.path] using hq₀
    rw [e, ← VarSymb.ext_append_single, preIx_lvl _ hp hst', preIx_lvl _ hp hst',
      VarSymb.ext_append_single]

/-- ⭐**A world's environment, pushed**: every reachable address (at the first level, every
    keepable one) reads as the shape of its root reading. -/
def CInvW (w : GW hF M₀) {Δ : Ctx}
    (τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ w) (j : ℕ) : Prop :=
  ∀ (y : VarSymb) {T : VarType} (h : Δ.ref y = some T), Step.levels y.path = j ∧
    CFormAt w j y T ∧ (0 < j ∨ T.keepable = true →
      CForm (hF := hF) (M₀ := M₀) j (preIx w y) T ∧
        τ.ref j y h = annC w (Ann.eta (preIx w y) T))

section Pushed

variable (hV : ModalSys.Five = true) (hS : ModalSys.fourL = true)
  (hW : ModalSys.fourLW = true) (hM₀ : Theory.IsMCS M₀) (hT : ModalSys.T = true)

include hV hS hW hM₀ hT in
/-- What holds of a view's declared addresses holds of its reachable ones. -/
theorem cInvW_of_items {w : GW hF M₀} {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ w} {j : ℕ} (hj : 0 < j)
    (hitem : ∀ (v : VarSymb) (T : VarType) (h : Δ v = some T), Step.levels v.path = j ∧
      CFormAt w j v T ∧ CForm (hF := hF) (M₀ := M₀) j (preIx w v) T ∧
        τ v T h = annC w (Ann.eta (preIx w v) T)) :
    CInvW w τ j
  | .root r, T, h => by
      have h' : Δ (.root r) = some T := by rwa [Ctx.ref_nonproj _ rfl] at h
      obtain ⟨hl, hw', hf, he⟩ := hitem _ T h'
      exact ⟨hl, hw', fun _ => ⟨hf, he⟩⟩
  | .step v st, T, h => by
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Δ.ref v = some U := by
          rw [Ctx.ref_step_proj _ v hs] at h
          cases hU : Δ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        have hst : U.step st = some T := by
          rw [Ctx.ref_step_proj _ v hs, hU] at h
          exact h
        obtain ⟨hl, hw', hv⟩ := cInvW_of_items hj hitem v hU
        obtain ⟨hf, he⟩ := hv (.inl hj)
        have e := preIx_step w v (st := st) (.inl (by omega))
        refine ⟨?_, hw'.proj hs hst, fun _ => ⟨?_, ?_⟩⟩
        · change Step.levels (v.path ++ [st]) = j
          rw [Step.levels_append, hl]
          simp [Step.levels, hs]
        · rw [e]
          exact hf.proj hs hst
        · rw [e, Model.ShEnv.ref_proj _ j hs hU h, he]
          exact proj_annC hV hS hW hM₀ hT (fun h0 => by omega) hf hs _
      · have h' : Δ (.step v st) = some T := by rwa [Ctx.ref_step_nonproj _ v hs] at h
        obtain ⟨hl, hw', hf, he⟩ := hitem _ T h'
        refine ⟨hl, hw', fun _ => ⟨hf, ?_⟩⟩
        rw [Model.ShEnv.ref_nonproj _ j hs h]
        exact he

include hV hS hW hM₀ hT in
/-- Pushing into `□` keeps the invariant at its items. -/
theorem cInvW_box_item {w : GW hF M₀} {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ w} {j : ℕ}
    (hI : CInvW w τ j) (v : VarSymb) (T : VarType) (h : Δ.boxIn v = some T) :
    Step.levels v.path = j + 1 ∧ CFormAt w (j + 1) v T ∧
      CForm (hF := hF) (M₀ := M₀) (j + 1) (preIx w v) T ∧
      τ.boxPush j v T h = annC w (Ann.eta (preIx w v) T) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  match v, h with
  | .step u .keep, h =>
      obtain ⟨hF', hu, hk⟩ := Ctx.boxIn_keep h
      obtain ⟨hl, hw', hv⟩ := hI u hu
      obtain ⟨hf, he⟩ := hv (.inr hk)
      have e := preIx_step w u (st := .keep) (.inr rfl)
      refine ⟨?_, hw'.keep hk, ?_, ?_⟩
      · change Step.levels (u.path ++ [.keep]) = j + 1
        rw [Step.levels_append, hl]
        simp [Step.levels, Step.isProj]
      · rw [e]
        exact hf.keep hk
      · change (GFunc.shp (GFunc.keep hF' hk) j (τ.ref j u hu)).inner = _
        rw [he, e]
        exact keep_annC hV hS hW hM₀ hT hf hF' hk
  | .step u .box, h =>
      have := (Ctx.boxIn_box h).1
      rw [hko] at this
      cases this
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .dia, h => cases h
  | .step _ .here, h => cases h

include hV hS hW hM₀ hT in
/-- ⭐Pushing into `□` keeps the invariant. -/
theorem CInvW.box {w : GW hF M₀} {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ w} {j : ℕ}
    (hI : CInvW w τ j) : CInvW w (τ.boxPush j) (j + 1) :=
  cInvW_of_items hV hS hW hM₀ hT (Nat.succ_pos j) fun v T h =>
    cInvW_box_item hV hS hW hM₀ hT hI v T h

include hV hS hW hM₀ hT in
/-- ⭐Pushing into `◇_x` keeps the invariant. -/
theorem CInvW.dia {w : GW hF M₀} {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ w} {j : ℕ}
    (hI : CInvW w τ j) {x : VarSymb} {X : VarType} (hx : Δ.ref x = some (.VTypeDia X)) :
    CInvW w (τ.diaPush j x hx) (j + 1) := by
  refine cInvW_of_items hV hS hW hM₀ hT (Nat.succ_pos j) fun v T h => ?_
  by_cases hvx : v = .step x .dia
  · subst hvx
    obtain rfl := Ctx.diaIn_step_dia hx h
    obtain ⟨hl, hw', hv⟩ := hI x hx
    obtain ⟨hf, he⟩ := hv (.inr rfl)
    have e := preIx_step w x (st := .dia) (.inr rfl)
    refine ⟨?_, hw'.dia, ?_, ?_⟩
    · change Step.levels (x.path ++ [.dia]) = j + 1
      rw [Step.levels_append, hl]
      simp [Step.levels, Step.isProj]
    · rw [e]
      exact hf.dia
    · change (τ.ref j x hx).body = _
      rw [he, e]
      rfl
  · match v, h, hvx with
    | .step u .keep, h, _ =>
        have h' : Δ.boxIn (.step u .keep) = some T := h
        exact cInvW_box_item hV hS hW hM₀ hT hI _ T h'
    | .step u .box, h, _ =>
        have h' : Δ.boxIn (.step u .box) = some T := h
        exact cInvW_box_item hV hS hW hM₀ hT hI _ T h'
    | .step u .dia, h, hvx =>
        change (if u = x then _ else none) = some T at h
        split_ifs at h with hux
        exact absurd (by rw [hux]) hvx
    | .root _, h, _ => cases h
    | .step _ .fst, h, _ => cases h
    | .step _ .snd, h, _ => cases h
    | .step _ .here, h, _ => cases h

include hV hS hW hM₀ hT in
/-- ⭐**In a pushed world environment a term's shape is its annotation's, read at the root.** -/
theorem termShp_annW {w : GW hF M₀} : ∀ {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ w} {j : ℕ},
    CInvW w τ j → ∀ {A : VarType} {a : Ann A} (t : Term σ Δ A a),
      Model.termShp τ j t = annC w (a.mapIdx (preIx w))
  | _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, .unit => rfl
  | _, _, _, hI, _, _, .pair t₁ t₂ => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [termShp_annW hI t₁, termShp_annW hI t₂]
  | _, _, _, hI, _, _, .boxtm u => by
      change Shp.box _ = Shp.box _
      rw [termShp_annW (hI.box hV hS hW hM₀ hT) u]
  | Δ, τ, j, hI, _, _, .diatm x hx u => by
      obtain ⟨X, hr⟩ := id hx
      rw [Model.termShp_diatm τ j hr hx u, termShp_annW (hI.dia hV hS hW hM₀ hT hr) u,
        ((hI x hr).2.2 (.inr rfl)).2]
      rfl

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Below a level step the type before it is keepable (keep-only views). -/
theorem keepable_of_level (hko : ModalSys.keepOnly = true) {U X : VarType} {st : Step}
    {r : List Step} (hs : st.isProj = false)
    (h : Step.walkTy U (st :: r) = some (.VTypeDia X)) : U.keepable = true := by
  obtain ⟨W, hW, -⟩ := Option.bind_eq_some_iff.mp h
  cases st with
  | fst => cases hs
  | snd => cases hs
  | here => cases hs
  | box =>
      change (if ModalSys.keepOnly = true then none else U.step .box) = some W at hW
      rw [if_pos hko] at hW
      cases hW
  | dia =>
      cases U <;> first | rfl | cases hW
  | keep =>
      change (if U.keepable = true then some U else none) = some W at hW
      by_contra hk
      rw [if_neg hk] at hW
      cases hW

include hV hS hW hM₀ hT in
/-- ⭐**A position of `◇` type at a world is read at the root faithfully**: `postIx` undoes
    `preIx` (`rnm_rorig`). -/
theorem postIx_preIx (w : GW hF M₀) {j : ℕ} {y : VarSymb} {X : VarType}
    (hf : CFormAt w j y (.VTypeDia X)) : postIx w (preIx w y) = y := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨v, U, π, hd, hv, rfl, hw, hn⟩ := hf
  by_cases h0 : j = 0
  · subst h0
    have hπ := ppath_of_levels0 hn
    have hp := ppath_ext hv hπ
    have hdp := declAt_ext hd hπ hw
    obtain ⟨i, hi⟩ := declAt_rorig hV hS hW hM₀ w hdp rfl
    rw [preIx_ppath w hp, postIx_ppath w (reach_ppath hi).1]
    exact rnm_rorig hV hS hW hM₀ w hdp rfl rfl
  · obtain ⟨q, st, r, rfl, hq, hst⟩ := split_first π (by omega)
    have hp := ppath_ext hv hq
    rw [Step.walkTy_append] at hw
    cases hU : Step.walkTy U q with
    | none =>
        rw [hU] at hw
        cases hw
    | some U' =>
        rw [hU, Option.bind_some] at hw
        have hdp := declAt_ext hd hq hU
        have hk := keepable_of_level hko hst hw
        obtain ⟨i, hi⟩ := declAt_rorig hV hS hW hM₀ w hdp hk
        rw [VarSymb.ext_append,
          show (v.ext q).ext (st :: r) = (VarSymb.step (v.ext q) st).ext r from rfl,
          preIx_lvl w hp hst r, postIx_lvl w (reach_ppath hi).1 hst r,
          rnm_rorig hV hS hW hM₀ w hdp hk (etaInj_of_walkTy _ hw)]

include hV hS hW hM₀ hT in
/-- ⭐⭐**Shapes determine annotations** in a pushed world environment. -/
theorem ann_eq_of_termShpW {w : GW hF M₀} : ∀ {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ w} {j : ℕ},
    CInvW w τ j → ∀ {A : VarType} {a a' : Ann A} (t : Term σ Δ A a)
      (t' : Term σ Δ A a'), Model.termShp τ j t = Model.termShp τ j t' → a = a'
  | _, _, _, _, _, _, _, .var _ _, .var _ _, _ => rfl
  | _, _, _, _, _, _, _, .var _ _, .func _, _ => rfl
  | _, _, _, _, _, _, _, .func _, .var _ _, _ => rfl
  | _, _, _, _, _, _, _, .func _, .func _, _ => rfl
  | _, _, _, _, _, _, _, .unit, .unit, _ => rfl
  | _, _, _, hI, _, _, _, .pair t₁ t₂, .pair t₁' t₂', h => by
      change Shp.prod _ _ = Shp.prod _ _ at h
      injection h with _ _ h₁ h₂
      rw [ann_eq_of_termShpW hI t₁ t₁' h₁, ann_eq_of_termShpW hI t₂ t₂' h₂]
  | _, _, _, hI, _, _, _, .boxtm u, .boxtm u', h => by
      change Shp.box _ = Shp.box _ at h
      injection h with _ h₁
      rw [ann_eq_of_termShpW (hI.box hV hS hW hM₀ hT) u u' h₁]
  | Δ, τ, j, hI, _, _, _, .diatm x hx u, .diatm x' hx' u', h => by
      obtain ⟨X, hr⟩ := id hx
      obtain ⟨X', hr'⟩ := id hx'
      rw [Model.termShp_diatm τ j hr hx u, Model.termShp_diatm τ j hr' hx' u'] at h
      injection h with _ hl hb
      obtain ⟨-, hw₁, hv₁⟩ := hI x hr
      obtain ⟨-, hw₂, hv₂⟩ := hI x' hr'
      obtain ⟨hf, he⟩ := hv₁ (.inr rfl)
      obtain ⟨hf', he'⟩ := hv₂ (.inr rfl)
      rw [he, he'] at hl
      have e := cLab_inj hV hS hW hM₀ hT j hf hf' _ hl
      obtain rfl : x = x' := by
        rw [← postIx_preIx hV hS hW hM₀ hT w hw₁, ← postIx_preIx hV hS hW hM₀ hT w hw₂, e]
      obtain rfl : X = X' := by
        rw [hr] at hr'
        injection hr' with e'
        injection e'
      rw [ann_eq_of_termShpW (hI.dia hV hS hW hM₀ hT hr) u u' hb]

end Pushed

end GArrow

end V12M
