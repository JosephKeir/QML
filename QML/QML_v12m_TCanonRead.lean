import QML.QML_v12m_TCanonName
import QML.QML_v12m_ReadNamesSubst

/-!
# QML v12m — the KT tree: reading an identity view at a name

The `◇⁰ᵀ_x χ` case of the truth lemma (docs §12.36): `χ` lives in `x`'s identity view, which no
stage declares.  Read at a fresh root `c` (`x.at ↦ c`, `TCanon.nameAt`), it becomes a formula of
the stage with `c` added, and `bindFree` makes that a slot formula `Φ`.  ⭐`TCanon.roundTrip`: `Φ`
filled with `x.at` in the view is `χ` again — through the legal substitution `c ↦ x.at`
(`WFF.subst_readNames`), since the source declares no opened identity content.  Leibniz along `≡`
then gives `◇⁰ᵀ_x (x.at ≡ t) ⊢ ◇⁰ᵀ_x χ ↔ Φ(t)`.

* `VarSymb.NoAt`, `Ctx.NoAt`: no `at` step; stage contexts declare none.
* `TCanon.nameAt x c`, `TCanon.readsName`: the naming and its typing.
-/

namespace V12M

variable [ModalSys]

/-- No step is an identity reading. -/
def VarSymb.NoAt : VarSymb → Prop
  | .root _ => True
  | .step v s => s ≠ .at ∧ v.NoAt

omit [ModalSys] in
/-- An address with no identity reading is not renamed. -/
theorem VarSymb.readNames_noAt {ν : VarSymb → Option VarSymb} :
    ∀ {k : ℕ} {v : VarSymb}, v.NoAt → v.readNames ν k = v
  | _, .root _, _ => rfl
  | k, .step v s, ⟨hs, hv⟩ => by
      by_cases hp : s.isProj = true
      · rw [VarSymb.readNames_proj hp (fun h => hs h.2), VarSymb.readNames_noAt hv]
      · cases k with
        | zero => exact VarSymb.readNames_level_zero (Bool.eq_false_iff.mpr hp)
        | succ k =>
            rw [VarSymb.readNames_level_succ (Bool.eq_false_iff.mpr hp),
              VarSymb.readNames_noAt hv]

/-- A context declaring no identity reading (the stages of a world). -/
def Ctx.NoAt (Γ : Ctx) : Prop := ∀ v T, Γ v = some T → v.NoAt

namespace TCanon

variable {σ : Signature} (hT : ModalSys.T = true) (hO : ModalSys.Opt = true)

/-- ⭐Naming `x`'s identity content by the root `free c`. -/
def nameAt (x : VarSymb) (c : ℕ) : VarSymb → Option VarSymb :=
  fun y => if y = x then some (.root (.free c)) else none

omit [ModalSys] in
theorem nameAt_self (x : VarSymb) (c : ℕ) : nameAt x c x = some (.root (.free c)) := if_pos rfl

omit [ModalSys] in
theorem nameAt_eq {x y n : VarSymb} {c : ℕ} (h : nameAt x c y = some n) :
    y = x ∧ n = .root (.free c) := by
  unfold nameAt at h
  split_ifs at h with hyx
  exact ⟨hyx, (Option.some.inj h).symm⟩

omit [ModalSys] in
theorem nameAt_rt {x : VarSymb} {c : ℕ} :
    ∀ y n, nameAt x c y = some n → ∀ e, n.rt ≠ .bnd e := by
  intro y n h e he
  obtain ⟨-, rfl⟩ := nameAt_eq h
  cases he

theorem nameAt_dom {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {X : VarType}
    (hx : Γ.ref x = some (.VTypeDia X)) {c : ℕ} :
    ∀ y n, nameAt x c y = some n → ∀ e, y.rt ≠ .bnd e := by
  intro y n h e he
  obtain ⟨rfl, -⟩ := nameAt_eq h
  rw [Ctx.ref_none_of_rootFresh ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (Nat.zero_le e)) y he]
    at hx
  cases hx

include hT hO in
/-- ⭐Reading `x`'s identity view at a fresh root is well typed. -/
theorem readsName {Γ : Ctx} (hfree : Γ.NoAt) {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) {c : ℕ} (hc : Γ.RootFresh (.free c)) :
    Ctx.ReadsNames (nameAt x c) 0 (Γ.optInT x) (Γ.insert (.free c) A) := by
  have hxT := Ctx.witT_of hT hO hx
  refine Ctx.ReadsNames.of_raw (fun v T hlp hv => ?_) (fun y X hy => hy) (fun _ y n hyn => ?_)
  · by_cases hvx : v = .step x .at
    · subst hvx
      rw [Ctx.optInT_content hxT] at hv
      cases hv
      rw [VarSymb.readNames_at_named (nameAt_self x c)]
      exact Ctx.ref_insert_root Γ _ A
    · rw [Ctx.optInT_ne hvx] at hv
      rw [VarSymb.readNames_noAt (hfree v T hv)]
      have hrt : v.rt ≠ .free c := fun he => by rw [hc v he] at hv; cases hv
      rw [Ctx.ref_insert_ne A hrt, Ctx.ref_nonproj Γ hlp]
      exact hv
  · obtain ⟨rfl, rfl⟩ := nameAt_eq hyn
    exact ⟨A, (Ctx.le_optInT Γ y).ref hx, Ctx.ref_insert_root Γ _ A⟩

/-- ⭐**The round trip**: `x`'s identity view read at a fresh root, bound to the slot, and filled
    with `x.at` in the view, is the formula again. -/
theorem roundTrip {Γ : Ctx} [Γ.Presented] (hfree : Γ.NoAt) {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) {c : ℕ} (hc : Γ.RootFresh (.free c))
    (χ : WFF σ (Γ.optInT x) 0) :
    WFF.instantiate Ctx.NoSlots.slots
        (Term.eta (.step x .at) A (Ctx.ref_optInT_content (Ctx.witT_of hT hO hx)))
        (WFF.mono ((Ctx.le_optInT Γ x).insert (.bnd 0) A)
          (WFF.bindFree c hc Ctx.NoSlots.slots A
            (WFF.readNames nameAt_rt (readsName hT hO hfree hx hc) Ctx.NoSlots.slots χ))) =
      χ := by
  have hxT := Ctx.witT_of hT hO hx
  have hΓx : (Γ.optInT x).SlotsFrom 0 := Ctx.NoSlots.slots
  rw [WFF.instantiate_bindFree (Ctx.le_optInT Γ x) c hc]
  have hp : Subst.PreRead (nameAt x c) 0 (Γ.optInT x)
      (Subst.single (.free c) (.tm (Term.eta (σ := σ) (.step x .at) A
        (Ctx.ref_optInT_content hxT))))
      (Subst.idRen (Γ.optInT x)) := by
    refine Subst.preRead_of (fun v T _ hv => ?_) (fun _ y X _ => .refl _)
      (fun _ y n X hyn hy => ?_)
    · by_cases hvx : v = .step x .at
      · subst hvx
        rw [Ctx.optInT_content hxT] at hv
        cases hv
        rw [VarSymb.readNames_at_named (nameAt_self x c), Subst.at_single_root]
        exact .eta_ren _ _
      · rw [Ctx.optInT_ne hvx] at hv
        rw [VarSymb.readNames_noAt (hfree v T hv),
          Subst.single_at_ne (fun he => by rw [hc v he] at hv; cases hv)]
        exact .refl _
    · obtain ⟨rfl, rfl⟩ := nameAt_eq hyn
      rw [Subst.at_single_root, Subst.at_idRen]
      change SubE.Sim X (SubE.tm (Term.mono _ (Term.eta (.step y .at) A _)))
        (SubE.ren (.step y .at))
      rw [(Ctx.le_optInT Γ y).ref hx] at hy
      cases hy
      rw [Term.mono_eta]
      exact .eta_ren _ _
  refine (WFF.subst_readNames nameAt_rt (nameAt_dom hx) (readsName hT hO hfree hx hc) hΓx
    ((Ctx.NoSlots.slots (Γ := Γ)).insertFree c A) _ _ _ (Subst.idRen _) Subst.ok_idRen
    Subst.coh_idRen hΓx hp χ).trans ?_
  exact (WFF.subst_ren (Ctx.Le.refl _) _ _ _ hΓx _ (fun v _ _ => Subst.at_idRen v) χ
    (fun _ _ _ _ => rfl)).trans (WFF.mono_refl _ χ)

/-- ⭐`x`'s identity view read at a fresh root and bound to the slot: a formula of `Γ` with a hole
    of the content type. -/
abbrev readSlot {Γ : Ctx} [Γ.NoSlots] (hfree : Γ.NoAt) {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) {c : ℕ} (hc : Γ.RootFresh (.free c))
    (χ : WFF σ (Γ.optInT x) 0) : WFF σ (Γ.insert (.bnd 0) A) 1 :=
  WFF.bindFree c hc Ctx.NoSlots.slots A
    (WFF.readNames nameAt_rt (readsName hT hO hfree hx hc) Ctx.NoSlots.slots χ)

/-- `◇⁰ᵀ_x (x.at ≡ t)`: `x` is realised here, its content `≡` to `t`. -/
abbrev nameSent {Γ : Ctx} {x : VarSymb} {A : VarType} (hx : Γ.ref x = some (.VTypeDia A))
    {a : Ann A} (t : Term σ Γ A a) : WFF σ Γ 0 :=
  .optx hO .ident x ⟨A, Ctx.witT_of hT hO hx⟩
    (eqH hO A (Term.eta (.step x .at) A (Ctx.ref_optInT_content (Ctx.witT_of hT hO hx)))
      (Term.mono (Ctx.le_optInT Γ x) t))

omit hT in
/-- ⭐`optNameT` filled with a term, in a larger context, is `◇⁰ᵀ_y (y.at ≡ t)`. -/
theorem instantiate_optNameT {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ') {y : VarSymb}
    {X : VarType} (hy : Γ.witT y = some X) {a : Ann X} (t : Term σ Γ' X a) :
    WFF.instantiate Ctx.NoSlots.slots t (WFF.mono (h.insert (.bnd 0) X) (WFF.optNameT hO hy)) =
      .optx hO .ident y ⟨X, h.witT hy⟩
        (eqH hO X (Term.eta (.step y .at) X (Ctx.ref_optInT_content (h.witT hy)))
          (Term.mono (Ctx.le_optInT Γ' y) t)) := by
  have hyT : Γ'.witT y = some X := h.witT hy
  have hne : y.rt ≠ .bnd 0 := Ctx.NoSlots.ref_bnd0 (Ctx.witT_spec hyT).2.2
  rw [WFF.instantiate, WFF.substRoot,
    WFF.subst_mono (hΓ := (Ctx.NoSlots.slots (Γ := Γ)).insert X)]
  have hz : Subst.singleIdx (.bnd 0) (.tm t) y = y := if_neg hne
  have hθ := (Subst.ok_single (Ctx.Le.refl Γ') (Γ := Γ') (r := .bnd 0) (T := X) (e := .tm t)
    rfl).restrict (h.insert (.bnd 0) X)
  have hc := (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ')).rootFresh le_rfl)
    (Ctx.Le.refl Γ') (T := X) (e := .tm t) rfl).restrict (h.insert (.bnd 0) X)
  have hyI : (Γ.insert (.bnd 0) X).witT y = some X :=
    (Ctx.le_insert Ctx.NoSlots.slots.root X).witT hy
  have hat₀ : (Subst.single (.bnd 0) (.tm t)).at y = .ren y := Subst.single_at_ne hne
  have hθz := Subst.ok_optInT hθ (y := y) (z := y) hyI (by rw [hat₀]; rfl)
  have hcz : Subst.Coh (Subst.singleIdx (.bnd 0) (.tm t)) ((Γ.insert (.bnd 0) X).optInT y)
      ((Subst.single (.bnd 0) (.tm t)).optInT y y) := by
    have := Subst.coh_optInT hθ hc (y := y) hyI
    rwa [hz] at this
  have hat : ((Subst.single (.bnd 0) (.tm t)).optInT y y).at (.step y .at) =
      .ren (.step y .at) := by
    rw [Subst.at_nonproj _ rfl, Subst.optInT_content, hat₀]
    rfl
  have hat₂ : ((Subst.single (.bnd 0) (.tm t)).optInT y y).at (.root (.bnd 0)) =
      .tm (Term.mono (Ctx.le_optInT _ y) t) := by
    change ((Subst.single (.bnd 0) (.tm t)).optInT y y) (.root (.bnd 0)) = _
    rw [Subst.optInT_ne _ _ (fun h => by cases h), Subst.single_root]
    rfl
  rw [WFF.subst_optxT_eq (Γ := Γ.insert (.bnd 0) X) (Δ := Γ') _ _ _ _ _ hO y ⟨X, hyI⟩
      _ hz ⟨X, hyT⟩ hθz hcz, WFF.subst_eqH,
    eqH_congr hO (Term.subst_eta_renAt _ _ _ X _ _ _
        (Ctx.ref_optInT_content (Γ := Γ') hyT) hat)
      (Term.subst_eta_tm _ _ _ X _ _ _ hat₂)]

/-- ⭐**Reading an identity view at a name**, one way: `◇⁰ᵀ_x (x.at ≡ t), ◇⁰ᵀ_x χ ⊢ Φ(t)`.
    Inside the view (one content, `opt_fun`), Leibniz along `≡` from the round trip; then out of
    the view (`opt_out`). -/
def optT_named {Γ : Ctx} [Γ.Presented] (hfree : Γ.NoAt) {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) {c : ℕ} (hc : Γ.RootFresh (.free c))
    (χ : WFF σ (Γ.optInT x) 0) {a : Ann A} (t : Term σ Γ A a) :
    Proof σ Γ [nameSent hT hO hx t, .optx hO .ident x ⟨A, Ctx.witT_of hT hO hx⟩ χ]
      (WFF.instantiate Ctx.NoSlots.slots t (readSlot hT hO hfree hx hc χ)) := by
  have hy : ∃ X, Γ.witK .ident x = some X := ⟨A, Ctx.witT_of hT hO hx⟩
  have inner : Proof σ (Γ.optInT x)
      [(eqH hO A (Term.eta (.step x .at) A (Ctx.ref_optInT_content (Ctx.witT_of hT hO hx)))
        (Term.mono (Ctx.le_optInT Γ x) t)).and χ]
      (WFF.mono (Ctx.le_optInT Γ x)
        (WFF.instantiate Ctx.NoSlots.slots t (readSlot hT hO hfree hx hc χ))) :=
    Proof.conv (WFF.mono_instantiate (Ctx.le_optInT Γ x) _ Ctx.NoSlots.slots t _).symm
      (Proof.leibnizH hO A (.and_elim_l (Proof.lookup List.mem_cons_self))
        (Proof.conv (roundTrip hT hO hfree hx hc χ).symm
          (.and_elim_r (Proof.lookup List.mem_cons_self))))
  have k := Proof.K_opt hO .ident x hy (Δ₁ := []) (Δ₂ := []) inner
  have f := Proof.opt_fun hO .ident x hy
    (eqH hO A (Term.eta (.step x .at) A (Ctx.ref_optInT_content (Ctx.witT_of hT hO hx)))
      (Term.mono (Ctx.le_optInT Γ x) t)) χ
  exact Proof.opt_out hO .ident x hy
    (.imp_elim (Proof.ofSubset (fun _ h => by simp at h) (.imp_intro k)) f)

/-- ⭐**Reading an identity view at a name**, the other way: `◇⁰ᵀ_x (x.at ≡ t), Φ(t) ⊢ ◇⁰ᵀ_x χ`. -/
def named_optT {Γ : Ctx} [Γ.Presented] (hfree : Γ.NoAt) {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) {c : ℕ} (hc : Γ.RootFresh (.free c))
    (χ : WFF σ (Γ.optInT x) 0) {a : Ann A} (t : Term σ Γ A a) :
    Proof σ Γ [nameSent hT hO hx t,
        WFF.instantiate Ctx.NoSlots.slots t (readSlot hT hO hfree hx hc χ)]
      (.optx hO .ident x ⟨A, Ctx.witT_of hT hO hx⟩ χ) := by
  have hy : ∃ X, Γ.witK .ident x = some X := ⟨A, Ctx.witT_of hT hO hx⟩
  refine Proof.K_opt hO .ident x hy (Δ₂ := [])
    (Δ₁ := [WFF.instantiate Ctx.NoSlots.slots t (readSlot hT hO hfree hx hc χ)]) ?_
  refine Proof.conv (roundTrip hT hO hfree hx hc χ)
    (Proof.leibnizH hO A (Proof.eqH_symm hO A (Proof.lookup List.mem_cons_self))
      (Proof.conv (WFF.mono_instantiate (Ctx.le_optInT Γ x) _ Ctx.NoSlots.slots t _)
        (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))

open Canon

variable {N₀ : ℕ} {hT hO}

/-- ⭐**An identity name's sentence is `nameSent`** at its stage: `x` realised here, its content
    `≡` to the name. -/
theorem IdName.nameSent_mem {w : World σ N₀} {x : VarSymb} (d : IdName hT hO w x) :
    (⟨d.i₀, nameSent hT hO ((w.L.ctx_le d.hi).ref d.hx)
      (Term.eta (.root (.free d.c)) d.A d.hc)⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  have h := d.hname
  rw [instantiate_optNameT hO (w.L.ctx_le d.hi) (Ctx.witT_of hT hO d.hx)] at h
  exact h

variable (hT hO) in
include hT hO in
/-- ⭐Reading `x`'s identity view at a name **already declared** in the context (a Henkin root of a
    later stage than `x`'s, as in the canonical model): the target is the context itself. -/
theorem readsNameIn {Γ : Ctx} (hfree : Γ.NoAt) {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) {c : ℕ} (hc : Γ.ref (.root (.free c)) = some A) :
    Ctx.ReadsNames (nameAt x c) 0 (Γ.optInT x) Γ := by
  have hxT := Ctx.witT_of hT hO hx
  refine Ctx.ReadsNames.of_raw (fun v T hlp hv => ?_) (fun y X hy => hy) (fun _ y n hyn => ?_)
  · by_cases hvx : v = .step x .at
    · subst hvx
      rw [Ctx.optInT_content hxT] at hv
      cases hv
      rw [VarSymb.readNames_at_named (nameAt_self x c)]
      exact hc
    · rw [Ctx.optInT_ne hvx] at hv
      rw [VarSymb.readNames_noAt (hfree v T hv), Ctx.ref_nonproj Γ hlp]
      exact hv
  · obtain ⟨rfl, rfl⟩ := nameAt_eq hyn
    exact ⟨A, (Ctx.le_optInT Γ y).ref hx, hc⟩

end TCanon

/-! ## Reading at names commutes with weakening -/

mutual
  theorem Func.readNames_mono {σ : Signature} {ν : VarSymb → Option VarSymb} {k : ℕ}
      {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} (h : Ctx.ReadsNames ν k Γ₁ Γ₂) (h' : Ctx.ReadsNames ν k Γ₁' Γ₂')
      (l₁ : Γ₁.Le Γ₁') (l₂ : Γ₂.Le Γ₂') :
      {n : ℕ} → (f : Func σ Γ₁ n) →
      Func.readNames h' (Func.mono l₁ f) = Func.mono l₂ (Func.readNames h f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.readNames h' (Func.mono l₁ g))
          (Term.readNames h' (Term.mono l₁ t)) = _
        rw [Func.readNames_mono h h' l₁ l₂ g, Term.readNames_mono h h' l₁ l₂ t]
        rfl
    termination_by structural _ f => f

  /-- ⭐Reading at names commutes with weakening, as `Term.collapse_mono`. -/
  theorem Term.readNames_mono {σ : Signature} {ν : VarSymb → Option VarSymb} {k : ℕ}
      {Γ₁ Γ₂ Γ₁' Γ₂' : Ctx} (h : Ctx.ReadsNames ν k Γ₁ Γ₂) (h' : Ctx.ReadsNames ν k Γ₁' Γ₂')
      (l₁ : Γ₁.Le Γ₁') (l₂ : Γ₂.Le Γ₂') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      Term.readNames h' (Term.mono l₁ t) = Term.mono l₂ (Term.readNames h t)
    | _, _, .var _ _ => rfl
    | _, _, .func f => by
        change Term.func (Func.readNames h' (Func.mono l₁ f)) = _
        rw [Func.readNames_mono h h' l₁ l₂ f]
        rfl
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        change Term.pair (Term.readNames h' (Term.mono l₁ s))
          (Term.readNames h' (Term.mono l₁ t)) = _
        rw [Term.readNames_mono h h' l₁ l₂ s, Term.readNames_mono h h' l₁ l₂ t]
        rfl
    | _, _, .boxtm t => by
        change Term.boxtm (Term.readNames h'.boxIn (Term.mono l₁.boxIn t)) = _
        rw [Term.readNames_mono h.boxIn h'.boxIn l₁.boxIn l₂.boxIn t]
        rfl
    | _, _, .diatm x _ t => by
        change Term.diatm _ _ (Term.readNames (h'.diaIn x) (Term.mono (l₁.diaIn x) t)) = _
        rw [Term.readNames_mono (h.diaIn x) (h'.diaIn x) (l₁.diaIn x) (l₂.diaIn _) t]
        rfl
    termination_by structural _ _ t => t
end

end V12M
