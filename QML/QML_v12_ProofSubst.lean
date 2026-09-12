import QML.QML_v12_Open

/-!
# QML v12 — substitution in proofs

⭐`Proof.subst`: a substitution sending the context `Γ` of a proof into a presented context `Γ'`
sends the proof to a proof of the substituted hypotheses and conclusion.  Renaming and weakening
are the instances whose entries are addresses; ⭐`Proof.mono` is weakening along `Ctx.Le`.

By induction on the proof.  Eigenvariables are renamed to a name fresh for `Γ'`, read off its
presentation, so nothing is assumed of the target beyond being presented.  Pair elimination needs
no rule: its components go to the projections of the pair's entry.

The rules' formula operations commute with substitution: `WFF.subst_mono_eq` (weakening),
`WFF.subst_instantiate`, `WFF.subst_bindFree`, `WFF.subst_bindPair`, `WFF.subst_diaIn_mono`.
-/

namespace V12

/-! ## Small facts -/

theorem SubE.mono_refl {σ : Signature} {Δ : Ctx} (h : Δ.Le Δ) : ∀ e : SubE σ Δ, e.mono h = e
  | .hide => rfl
  | .ren _ => rfl
  | .tm s => congrArg SubE.tm (Term.mono_refl h s)

theorem SubE.comp_ren {σ : Signature} {ι₂ : VarSymb → VarSymb} {Δ₁ Δ₂ : Ctx} (θ₂ : Subst σ Δ₂)
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) (w : VarSymb) :
    (SubE.ren w : SubE σ Δ₁).comp θ₂ hθ₂ hc₂ = θ₂.at w :=
  rfl

theorem Ctx.SlotsFrom.of_le {Γ Γ₁ : Ctx} {d : ℕ} (h : Γ.Le Γ₁) (hs : Γ₁.SlotsFrom d) :
    Γ.SlotsFrom d := by
  intro v n hv hn
  cases hΓ : Γ v with
  | none => rfl
  | some T =>
      have h₁ := h v T hΓ
      rw [hs v n hv hn] at h₁
      cases h₁

/-- Rename the root `free u` to `free u'`. -/
def VarSymb.renameIdx (ι : VarSymb → VarSymb) (u u' : ℕ) : VarSymb → VarSymb :=
  fun i => if i.rt = .free u then (VarSymb.root (.free u')).ext i.path else ι i

def Proof.castHyps {σ : Signature} {Γ : Ctx} {Δ Δ' : List (WFF σ Γ 0)} {φ : WFF σ Γ 0}
    (h : Δ = Δ') (p : Proof σ Γ Δ φ) : Proof σ Γ Δ' φ :=
  h ▸ p

namespace Subst

variable {σ : Signature} {Δ : Ctx}

theorem comp_apply {ι₂ : VarSymb → VarSymb} {Δ₁ : Ctx} (θ₁ : Subst σ Δ₁) (θ₂ : Subst σ Δ)
    (hθ₂ : Ok Δ₁ θ₂) (hc₂ : Coh ι₂ Δ₁ θ₂) (v : VarSymb) :
    θ₁.comp θ₂ hθ₂ hc₂ v = (θ₁ v).comp θ₂ hθ₂ hc₂ :=
  rfl

theorem single_root (r : Root) (e : SubE σ Δ) : single r e (.root r) = e := if_pos rfl

theorem single_ne {r : Root} (e : SubE σ Δ) {v : VarSymb} (h : v ≠ .root r) :
    single r e v = .ren v :=
  if_neg h

/-! ## Changing one root's entry -/

/-- `r ↦ e`, every other address as in `θ`. -/
def set (θ : Subst σ Δ) (r : Root) (e : SubE σ Δ) : Subst σ Δ :=
  fun v => if v = .root r then e else θ v

def setIdx (ι : VarSymb → VarSymb) (r : Root) (e : SubE σ Δ) : VarSymb → VarSymb :=
  fun i => if i.rt = r then e.idxAlong i.path else ι i

theorem set_root (θ : Subst σ Δ) (r : Root) (e : SubE σ Δ) : θ.set r e (.root r) = e :=
  if_pos rfl

theorem set_ne (θ : Subst σ Δ) {r : Root} (e : SubE σ Δ) {v : VarSymb} (h : v ≠ .root r) :
    θ.set r e v = θ v :=
  if_neg h

theorem ok_set {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {r : Root} {T : VarType}
    {e : SubE σ Δ} (he : e.OkRef T) : Ok (Γ.insert r T) (θ.set r e) := by
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [set_root]
    exact he
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [set_ne _ _ hvr]
    exact hθ v U hlp hv'

theorem coh_set {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {r : Root} {T : VarType} {e : SubE σ Δ} (hr : Γ.RootFresh r)
    (he : e.OkRef T) : Coh (setIdx ι r e) (Γ.insert r T) (θ.set r e) := by
  refine coh_of (ok_set hθ he) ?_
  intro v U hlp hv p
  by_cases hvr : v = .root r
  · subst hvr
    rw [set_root]
    change e.idxAlong p = if ((VarSymb.root r).ext p).rt = r then
      e.idxAlong ((VarSymb.root r).ext p).path else _
    simp only [VarSymb.ext_rt, VarSymb.ext_path, VarSymb.rt, VarSymb.path, List.nil_append,
      if_true]
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ r := fun he' => by
      rw [hr v he'] at hv'
      cases hv'
    rw [set_ne _ _ hvr, ← at_nonprod θ hlp, hc v U ((Ctx.ref_nonprod Γ hlp).trans hv') p]
    change ι (v.ext p) = if (v.ext p).rt = r then _ else ι (v.ext p)
    rw [VarSymb.ext_rt, if_neg hrt]

/-! ## Renaming an eigenvariable -/

/-- The eigenvariable `u` renamed to `u'`, fresh for the target; everything else weakened past
    it. -/
def rename (θ : Subst σ Δ) (u u' : ℕ) (T : VarType) (h : Δ (.root (.free u')) = none) :
    Subst σ (Δ.insert (.free u') T) :=
  (θ.mono (Ctx.le_insert h T)).set (.free u) (.ren (.root (.free u')))

theorem rename_root (θ : Subst σ Δ) (u u' : ℕ) (T : VarType) (h : Δ (.root (.free u')) = none) :
    θ.rename u u' T h (.root (.free u)) = .ren (.root (.free u')) :=
  if_pos rfl

theorem rename_ne (θ : Subst σ Δ) {u : ℕ} (u' : ℕ) (T : VarType)
    (h : Δ (.root (.free u')) = none) {v : VarSymb} (hv : v ≠ .root (.free u)) :
    θ.rename u u' T h v = (θ v).mono (Ctx.le_insert h T) :=
  if_neg hv

theorem ok_rename {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {u u' : ℕ} (T : VarType)
    (h : Δ (.root (.free u')) = none) : Ok (Γ.insert (.free u) T) (θ.rename u u' T h) :=
  ok_set (ok_mono hθ _) (e := .ren (.root (.free u'))) (Ctx.ref_insert_root Δ _ T)

theorem coh_rename {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (T : VarType)
    (h : Δ (.root (.free u')) = none) :
    Coh (VarSymb.renameIdx ι u u') (Γ.insert (.free u) T) (θ.rename u u' T h) :=
  coh_set (ok_mono hθ _) (coh_mono hc _) (e := .ren (.root (.free u'))) hu
    (Ctx.ref_insert_root Δ _ T)

theorem sim_rename_mono {Γ : Ctx} {θ : Subst σ Δ} {u u' : ℕ} (hu : Γ.RootFresh (.free u))
    (T : VarType) (h : Δ (.root (.free u')) = none) :
    Sim Γ (θ.rename u u' T h) (θ.mono (Ctx.le_insert h T)) :=
  sim_of fun v _ _ hv => by
    have hvr : v ≠ .root (.free u) := fun he => by
      subst he
      rw [hu.root] at hv
      cases hv
    rw [rename_ne _ _ _ _ hvr]
    exact .refl _

/-! ## Splitting a pair's entry -/

/-- The components `u₁`, `u₂` go to the projections of the entry of `z`. -/
def pairSplit (θ : Subst σ Δ) (u₁ u₂ z : ℕ) : Subst σ Δ :=
  (θ.set (.free u₁) ((θ (.root (.free z))).proj .fst)).set (.free u₂)
    ((θ (.root (.free z))).proj .snd)

def pairSplitIdx (ι : VarSymb → VarSymb) (θ : Subst σ Δ) (u₁ u₂ z : ℕ) : VarSymb → VarSymb :=
  setIdx (setIdx ι (.free u₁) ((θ (.root (.free z))).proj .fst)) (.free u₂)
    ((θ (.root (.free z))).proj .snd)

theorem okRef_pairEntry {Γ : Ctx} {θ : Subst σ Δ} {z : ℕ} {A B : VarType}
    (hθ : Ok (Γ.insert (.free z) (.VTypeProd A B)) θ) :
    (θ (.root (.free z))).OkRef (.VTypeProd A B) :=
  hθ _ _ rfl (by simp [Ctx.insert])

theorem ok_pairSplit {Γ : Ctx} {θ : Subst σ Δ} {u₁ u₂ z : ℕ} {A B : VarType}
    (hzf : Γ.RootFresh (.free z)) (hθ : Ok (Γ.insert (.free z) (.VTypeProd A B)) θ) :
    Ok ((Γ.insert (.free u₁) A).insert (.free u₂) B) (θ.pairSplit u₁ u₂ z) := by
  have he₁ : ((θ (.root (.free z))).proj .fst).OkRef A :=
    SubE.okRef_proj (okRef_pairEntry hθ) rfl rfl
  have he₂ : ((θ (.root (.free z))).proj .snd).OkRef B :=
    SubE.okRef_proj (okRef_pairEntry hθ) rfl rfl
  exact ok_set ((ok_set hθ he₁).restrict ((Ctx.le_insert hzf.root _).insert _ A)) he₂

theorem coh_pairSplit {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} {u₁ u₂ z : ℕ}
    {A B : VarType} (hu : u₁ ≠ u₂) (hz₁ : z ≠ u₁) (hu₁ : Γ.RootFresh (.free u₁))
    (hu₂ : Γ.RootFresh (.free u₂)) (hzf : Γ.RootFresh (.free z))
    (hθ : Ok (Γ.insert (.free z) (.VTypeProd A B)) θ)
    (hc : Coh ι (Γ.insert (.free z) (.VTypeProd A B)) θ) :
    Coh (pairSplitIdx ι θ u₁ u₂ z) ((Γ.insert (.free u₁) A).insert (.free u₂) B)
      (θ.pairSplit u₁ u₂ z) := by
  have hne₁₂ : Root.free u₁ ≠ Root.free u₂ := fun h => hu (Root.free.inj h)
  have hne_z₁ : Root.free z ≠ Root.free u₁ := fun h => hz₁ (Root.free.inj h)
  have he₁ : ((θ (.root (.free z))).proj .fst).OkRef A :=
    SubE.okRef_proj (okRef_pairEntry hθ) rfl rfl
  have he₂ : ((θ (.root (.free z))).proj .snd).OkRef B :=
    SubE.okRef_proj (okRef_pairEntry hθ) rfl rfl
  have hle := (Ctx.le_insert hzf.root (.VTypeProd A B)).insert (.free u₁) A
  exact coh_set ((ok_set hθ he₁).restrict hle)
    ((coh_set hθ hc (hu₁.insert_ne hne_z₁ _) he₁).restrict hle) (hu₂.insert_ne hne₁₂ A) he₂

end Subst

/-! ## The formula operations commute with substitution -/

section Commute

variable {σ : Signature}

/-- Weakening, then substituting, is substituting, then weakening. -/
theorem WFF.subst_mono_eq {ι ι₁ : VarSymb → VarSymb} {Γ Γ₁ Δ Δ₁ : Ctx} {d d' : ℕ}
    (hle : Γ.Le Γ₁) (hle' : Δ.Le Δ₁) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (θ₁ : Subst σ Δ₁) (hθ₁ : Subst.Ok Γ₁ θ₁) (hc₁ : Subst.Coh ι₁ Γ₁ θ₁)
    (hΓ : Γ.SlotsFrom d) (hΓ₁ : Γ₁.SlotsFrom d) (hΔ : Δ.SlotsFrom d') (hΔ₁ : Δ₁.SlotsFrom d')
    (hs : Subst.Sim Γ θ₁ (θ.mono hle')) (φ : WFF σ Γ d) :
    WFF.subst ι₁ θ₁ hθ₁ hc₁ hΓ₁ hΔ₁ (WFF.mono hle φ) =
      WFF.mono hle' (WFF.subst ι θ hθ hc hΓ hΔ φ) :=
  (WFF.subst_mono hle θ₁ hθ₁ hc₁ hΓ hΓ₁ hΔ₁ φ).trans
    ((WFF.subst_congr θ₁ (θ.mono hle') (hθ₁.restrict hle) (Subst.ok_mono hθ hle')
      (hc₁.restrict hle) (Subst.coh_mono hc hle') hΓ hΔ₁ hs φ).trans
      (WFF.mono_subst hle' θ hθ hc hΓ hΔ hΔ₁ φ).symm)

/-- Substituting into an instantiation. -/
theorem WFF.subst_instantiate {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {T : VarType} {a : Ann T} (t : Term σ Γ T a) (φ : WFF σ (Γ.insert (.bnd 0) T) 1) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.instantiate hΓ t φ) =
      WFF.instantiate hΔ (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 T hΔ.root)
          (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T)
          (hΔ.insert T) φ) := by
  have hr : Γ.RootFresh (.bnd 0) := hΓ.rootFresh le_rfl
  have hrΔ : Δ.RootFresh (.bnd 0) := hΔ.rootFresh le_rfl
  have he : (SubE.tm (Term.subst ι θ hθ hc t) : SubE σ Δ).OkRef T := rfl
  have hθ₃ := Subst.ok_set (r := .bnd 0) hθ he
  have hc₃ := Subst.coh_set hθ hc hr he
  refine (WFF.subst_comp (Subst.single (.bnd 0) (.tm t)) θ _
    (Subst.ok_single (Ctx.Le.refl Γ) rfl) (Subst.coh_single hr (Ctx.Le.refl Γ) rfl) hθ hc
    hθ₃ hc₃ (hΓ.insert T) hΓ hΔ ?_ φ).trans
    (WFF.subst_comp (θ.under 0 0 T hΔ.root) (Subst.single (.bnd 0) (.tm (Term.subst ι θ hθ hc t)))
      _ (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
      (Subst.ok_single (Ctx.Le.refl Δ) rfl) (Subst.coh_single hrΔ (Ctx.Le.refl Δ) rfl) hθ₃ hc₃
      (hΓ.insert T) (hΔ.insert T) hΔ ?_ φ).symm
  · refine Subst.sim_of ?_
    intro v U hlp hv
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.set_root, Subst.single_root]
      exact .refl _
    · rw [Subst.set_ne _ _ hvr, Subst.single_ne _ hvr, SubE.comp_ren, Subst.at_nonprod θ hlp]
      exact .refl _
  · refine Subst.sim_of ?_
    intro v U hlp hv
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.set_root, show θ.under 0 0 T hΔ.root (.root (.bnd 0)) = .ren (.root (.bnd 0))
        from if_pos rfl, SubE.comp_ren]
      change SubE.Sim U _ (Subst.single (.bnd 0) (.tm (Term.subst ι θ hθ hc t)) (.root (.bnd 0)))
      rw [Subst.single_root]
      exact .refl _
    · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
      rw [Subst.set_ne _ _ hvr,
        show θ.under 0 0 T hΔ.root v = (θ v).mono (Ctx.le_insert hΔ.root T) from if_neg hvr,
        SubE.comp_mono (Subst.idRen Δ) Subst.ok_idRen Subst.coh_idRen (Ctx.le_insert hΔ.root T)
          (Ctx.Le.refl Δ) _ _ _
          (fun w _ hw' => by
            rw [Subst.single_at_ne (Ctx.ref_rt_ne hrΔ hw'), Subst.at_idRen]
            rfl)
          (hθ v U hlp hv'),
        SubE.comp_idRen, SubE.mono_refl]
      exact .refl _

/-- Substituting into a bound eigenvariable: rename it to a fresh one. -/
theorem WFF.subst_bindFree {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u')) (T : VarType)
    (φ : WFF σ (Γ.insert (.free u) T) 0) :
    WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 T hΔ.root) (Subst.ok_under hθ T hΔ.root)
        (Subst.coh_under hθ hc hΓ T hΔ.root) (hΓ.insert T) (hΔ.insert T)
        (WFF.bindFree u hu hΓ T φ) =
      WFF.bindFree u' hu' hΔ T
        (WFF.subst (VarSymb.renameIdx ι u u') (θ.rename u u' T hu'.root)
          (Subst.ok_rename hθ T hu'.root) (Subst.coh_rename hθ hc hu T hu'.root)
          (hΓ.insertFree u T) (hΔ.insertFree u' T) φ) := by
  have hle : Δ.Le (Δ.insert (.bnd 0) T) := Ctx.le_insert hΔ.root T
  have hw : (Δ.insert (.bnd 0) T).ref (.root (.bnd 0)) = some T := Ctx.ref_insert_root Δ _ T
  have hwΓ : (Γ.insert (.bnd 0) T).ref (.root (.bnd 0)) = some T := Ctx.ref_insert_root Γ _ T
  have hθ₃ : Subst.Ok (Γ.insert (.free u) T) ((θ.mono hle).set (.free u) (.ren (.root (.bnd 0)))) :=
    Subst.ok_set (Subst.ok_mono hθ hle) (e := .ren (.root (.bnd 0))) hw
  have hc₃ := Subst.coh_set (Subst.ok_mono hθ hle) (Subst.coh_mono hc hle)
    (e := .ren (.root (.bnd 0))) hu hw
  refine (WFF.subst_comp (Subst.single (.free u) (.ren (.root (.bnd 0)))) (θ.under 0 0 T hΔ.root)
    _ (Subst.ok_single (Ctx.le_insert hΓ.root T) hwΓ)
    (Subst.coh_single hu (Ctx.le_insert hΓ.root T) hwΓ)
    (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root) hθ₃ hc₃
    (hΓ.insertFree u T) (hΓ.insert T) (hΔ.insert T) ?_ φ).trans
    (WFF.subst_comp (θ.rename u u' T hu'.root) (Subst.single (.free u') (.ren (.root (.bnd 0))))
      _ (Subst.ok_rename hθ T hu'.root) (Subst.coh_rename hθ hc hu T hu'.root)
      (Subst.ok_single hle hw) (Subst.coh_single hu' hle hw) hθ₃ hc₃
      (hΓ.insertFree u T) (hΔ.insertFree u' T) (hΔ.insert T) ?_ φ).symm
  · refine Subst.sim_of ?_
    intro v U hlp hv
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.free u)
    · subst hvr
      rw [Subst.set_root, Subst.single_root, SubE.comp_ren]
      change SubE.Sim U _ (θ.under 0 0 T hΔ.root (.root (.bnd 0)))
      rw [show θ.under 0 0 T hΔ.root (.root (.bnd 0)) = .ren (.root (.bnd 0)) from if_pos rfl]
      exact .refl _
    · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
      rw [Subst.set_ne _ _ hvr, Subst.single_ne _ hvr, SubE.comp_ren,
        Subst.under_eq_mono θ hΓ T hΔ.root v U ((Ctx.ref_nonprod Γ hlp).trans hv'),
        Subst.at_nonprod θ hlp]
      exact .refl _
  · refine Subst.sim_of ?_
    intro v U hlp hv
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.free u)
    · subst hvr
      rw [Subst.set_root, Subst.rename_root, SubE.comp_ren]
      change SubE.Sim U _ (Subst.single (.free u') (.ren (.root (.bnd 0))) (.root (.free u')))
      rw [Subst.single_root]
      exact .refl _
    · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
      rw [Subst.set_ne _ _ hvr, Subst.rename_ne _ _ _ _ hvr,
        SubE.comp_mono (Subst.idRen Δ) Subst.ok_idRen Subst.coh_idRen
          (Ctx.le_insert hu'.root T) hle _ _ _
          (fun w _ hw' => by
            rw [Subst.single_at_ne (Ctx.ref_rt_ne hu' hw'), Subst.at_idRen]
            rfl)
          (hθ v U hlp hv'),
        SubE.comp_idRen]
      exact .refl _

/-- Weakening past an eigenvariable commutes with renaming it. -/
theorem WFF.subst_weaken_rename {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u')) (T : VarType)
    (ψ : WFF σ Γ 0) :
    WFF.subst (VarSymb.renameIdx ι u u') (θ.rename u u' T hu'.root)
        (Subst.ok_rename hθ T hu'.root) (Subst.coh_rename hθ hc hu T hu'.root)
        (hΓ.insertFree u T) (hΔ.insertFree u' T) (WFF.weaken hu.root T ψ) =
      WFF.weaken hu'.root T (WFF.subst ι θ hθ hc hΓ hΔ ψ) :=
  WFF.subst_mono_eq _ _ θ hθ hc _ _ _ hΓ _ hΔ _ (Subst.sim_rename_mono hu T hu'.root) ψ

/-- Substituting into a `□`-hypothesis moved into a `◇_x` view. -/
theorem WFF.subst_diaIn_mono {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = ι x)
    (hΓ : Γ.SlotsFrom 0) (hΔb : Δ.boxIn.SlotsFrom 0) (hΔd : (Δ.diaIn (ι x)).SlotsFrom 0)
    (χ : WFF σ Γ.boxIn 0) :
    WFF.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) (hΓ.diaIn x) hΔd
        (WFF.mono (Ctx.le_boxIn_diaIn Γ x) χ) =
      WFF.mono (Ctx.le_boxIn_diaIn Δ (ι x))
        (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔb χ) :=
  WFF.subst_mono_eq _ _ θ.box _ _ (θ.dia x (ι x)) _ _ hΓ.boxIn (hΓ.diaIn x) hΔb hΔd
    (fun v T hv => by
      rw [Subst.dia_eq_box_mono θ x (ι x) v T hv, Subst.at_mono]
      exact .refl _) χ

/-- Substituting into pair elimination's formula: the components go to the projections. -/
theorem WFF.subst_bindPair {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (u₁ u₂ z : ℕ) (hu : u₁ ≠ u₂)
    (hz₁ : z ≠ u₁) (hu₁ : Γ.RootFresh (.free u₁)) (hu₂ : Γ.RootFresh (.free u₂))
    (hzf : Γ.RootFresh (.free z)) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) (A B : VarType)
    (θ : Subst σ Δ) (hθ : Subst.Ok (Γ.insert (.free z) (.VTypeProd A B)) θ)
    (hc : Subst.Coh ι (Γ.insert (.free z) (.VTypeProd A B)) θ)
    (φ : WFF σ ((Γ.insert (.free u₁) A).insert (.free u₂) B) 0) :
    WFF.subst ι θ hθ hc (hΓ.insertFree z _) hΔ
        (WFF.bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf hΓ A B φ) =
      WFF.subst (Subst.pairSplitIdx ι θ u₁ u₂ z) (θ.pairSplit u₁ u₂ z)
        (Subst.ok_pairSplit hzf hθ) (Subst.coh_pairSplit hu hz₁ hu₁ hu₂ hzf hθ hc)
        ((hΓ.insertFree u₁ A).insertFree u₂ B) hΔ φ := by
  have hne₁₂ : Root.free u₁ ≠ Root.free u₂ := fun h => hu (Root.free.inj h)
  have hne_z₁ : Root.free z ≠ Root.free u₁ := fun h => hz₁ (Root.free.inj h)
  have he₁ : ((θ (.root (.free z))).proj .fst).OkRef A :=
    SubE.okRef_proj (Subst.okRef_pairEntry hθ) rfl rfl
  have hr₁ : (Γ.insert (.free z) (.VTypeProd A B)).RootFresh (.free u₁) :=
    hu₁.insert_ne hne_z₁ _
  have hθ₅ := Subst.ok_set (r := .free u₁) hθ he₁
  have hc₅ := Subst.coh_set (r := .free u₁) hθ hc hr₁ he₁
  have hsw : ((Γ.insert (.free u₁) A).insert (.free z) (.VTypeProd A B)).Le
      ((Γ.insert (.free z) (.VTypeProd A B)).insert (.free u₁) A) :=
    Ctx.insert_swap_le hne_z₁.symm _ _
  let φ₁ : WFF σ ((Γ.insert (.free u₁) A).insert (.free z) (.VTypeProd A B)) 0 :=
    WFF.renameRoot (.free u₂) (hu₂.insert_ne hne₁₂ A)
      (Ctx.le_insert (hzf.insert_ne hne_z₁.symm A).root _) (.step (.root (.free z)) .snd)
      (Ctx.ref_insert_snd _ _ A B) ((hΓ.insertFree u₁ A).insertFree u₂ B)
      ((hΓ.insertFree u₁ A).insertFree z _) φ
  -- `u₁ ↦ z.fst`, then `θ`
  refine (WFF.subst_comp (Subst.single (.free u₁) (.ren (.step (.root (.free z)) .fst))) θ _
    (Subst.ok_single (Ctx.Le.refl _) (Ctx.ref_insert_fst _ _ A B))
    (Subst.coh_single hr₁ (Ctx.Le.refl _) (Ctx.ref_insert_fst _ _ A B)) hθ hc hθ₅ hc₅
    ((hΓ.insertFree z _).insertFree u₁ A) (hΓ.insertFree z _) hΔ ?_ (WFF.mono hsw φ₁)).trans ?_
  · refine Subst.sim_of ?_
    intro v U hlp hv
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.free u₁)
    · subst hvr
      rw [Subst.set_root, Subst.single_root]
      exact .refl _
    · rw [Subst.set_ne _ _ hvr, Subst.single_ne _ hvr, SubE.comp_ren, Subst.at_nonprod θ hlp]
      exact .refl _
  -- undo the reordering, then `u₂ ↦ z.snd`, then `θ₅`
  refine (WFF.subst_mono hsw _ hθ₅ hc₅ ((hΓ.insertFree u₁ A).insertFree z _)
    ((hΓ.insertFree z _).insertFree u₁ A) hΔ φ₁).trans ?_
  refine WFF.subst_comp (Subst.single (.free u₂) (.ren (.step (.root (.free z)) .snd)))
    (θ.set (.free u₁) ((θ (.root (.free z))).proj .fst)) _
    (Subst.ok_single (Ctx.le_insert (hzf.insert_ne hne_z₁.symm A).root _)
      (Ctx.ref_insert_snd _ _ A B))
    (Subst.coh_single (hu₂.insert_ne hne₁₂ A) (Ctx.le_insert (hzf.insert_ne hne_z₁.symm A).root _)
      (Ctx.ref_insert_snd _ _ A B))
    (hθ₅.restrict hsw) (hc₅.restrict hsw) _ _ ((hΓ.insertFree u₁ A).insertFree u₂ B)
    ((hΓ.insertFree u₁ A).insertFree z _) hΔ ?_ φ
  refine Subst.sim_of ?_
  intro v U hlp hv
  rw [Subst.comp_apply]
  by_cases hvr : v = .root (.free u₂)
  · subst hvr
    rw [Subst.pairSplit, Subst.set_root, Subst.single_root, SubE.comp_ren]
    change SubE.Sim U _ (((θ.set (.free u₁) ((θ (.root (.free z))).proj .fst))
      (.root (.free z))).proj .snd)
    rw [Subst.set_ne _ _ (fun h => hne_z₁ (VarSymb.root.inj h))]
    exact .refl _
  · rw [Subst.pairSplit, Subst.set_ne _ _ hvr, Subst.single_ne _ hvr, SubE.comp_ren,
      Subst.at_nonprod _ hlp]
    exact .refl _

end Commute

/-! ## Substitution in proofs -/

/-- ⭐**Substitution in proofs**: a substitution from the context of a proof into a presented
    context sends the proof to a proof of the substituted sequent. -/
def Proof.subst {σ : Signature} : {Γ : Ctx} → {Δs : List (WFF σ Γ 0)} → {φ : WFF σ Γ 0} →
    Proof σ Γ Δs φ → {Γ' : Ctx} → [Γ'.Presented] → {ι : VarSymb → VarSymb} →
    (θ : Subst σ Γ') → (hθ : Subst.Ok Γ θ) → (hc : Subst.Coh ι Γ θ) → (hΓ : Γ.SlotsFrom 0) →
    Proof σ Γ' (Δs.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots))
      (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots φ)
  | _, _, _, .ax _, _, _, _, _, _, _, _ => .ax _
  | _, _, _, .weak _ p, _, _, _, θ, hθ, hc, hΓ => .weak _ (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .contr p, _, _, _, θ, hθ, hc, hΓ => .contr (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .exch Δ₁ Δ₂ p, _, _, ι, θ, hθ, hc, hΓ =>
      Proof.castHyps List.map_append.symm
        (.exch (Δ₁.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots))
          (Δ₂.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots))
          (Proof.castHyps List.map_append (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, .weak_ctx u T hu p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hle := Ctx.le_insert hu.root T
      have hΓ₀ := hΓ.of_le hle
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.castHyps
        (by
          rw [List.map_map]
          exact List.map_congr_left fun ψ _ =>
            (WFF.subst_mono hle θ hθ hc hΓ₀ hΓ hΓ' ψ).symm)
        (Proof.conv (WFF.subst_mono hle θ hθ hc hΓ₀ hΓ hΓ' _).symm
          (Proof.subst p θ (hθ.restrict hle) (hc.restrict hle) hΓ₀))
  | _, _, _, .and_intro p q, _, _, _, θ, hθ, hc, hΓ =>
      .and_intro (Proof.subst p θ hθ hc hΓ) (Proof.subst q θ hθ hc hΓ)
  | _, _, _, .and_elim_l p, _, _, _, θ, hθ, hc, hΓ => .and_elim_l (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .and_elim_r p, _, _, _, θ, hθ, hc, hΓ => .and_elim_r (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .or_intro_l _ p, _, _, _, θ, hθ, hc, hΓ => .or_intro_l _ (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .or_intro_r _ p, _, _, _, θ, hθ, hc, hΓ => .or_intro_r _ (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .or_elim p q r, _, _, _, θ, hθ, hc, hΓ =>
      .or_elim (Proof.subst p θ hθ hc hΓ) (Proof.subst q θ hθ hc hΓ) (Proof.subst r θ hθ hc hΓ)
  | _, _, _, .imp_intro p, _, _, _, θ, hθ, hc, hΓ => .imp_intro (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .imp_elim p q, _, _, _, θ, hθ, hc, hΓ =>
      .imp_elim (Proof.subst p θ hθ hc hΓ) (Proof.subst q θ hθ hc hΓ)
  | _, _, _, .top_intro, _, _, _, _, _, _, _ => .top_intro
  | _, _, _, .bot_elim _ p, _, _, _, θ, hθ, hc, hΓ => .bot_elim _ (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .lem _, _, _, _, _, _, _, _ => .lem _
  | _, _, _, @Proof.all_intro _ _ _ Δs u T hu φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) := Ctx.Presented.fresh _ le_rfl
      have ih := Proof.subst p (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) T)
        (θ.rename u _ T hu'.root) (Subst.ok_rename hθ T hu'.root)
        (Subst.coh_rename hθ hc hu T hu'.root) (hΓ.insertFree u T)
      Proof.conv (congrArg (WFF.all T) (WFF.subst_bindFree θ hθ hc hΓ hΓ' hu hu' T φ).symm)
        (Proof.all_intro _ T hu'
          (Proof.castHyps
            (by
              rw [List.map_map, List.map_map]
              exact List.map_congr_left fun ψ _ =>
                WFF.subst_weaken_rename θ hθ hc hΓ hΓ' hu hu' T ψ)
            ih))
  | _, _, _, @Proof.all_elim _ _ _ _ T φ _ t p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ).symm
        (Proof.all_elim T (Term.subst ι θ hθ hc t) (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.ex_intro _ _ _ _ T φ _ t p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.ex_intro T (Term.subst ι θ hθ hc t)
        (Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ) (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.ex_elim _ _ _ Δs u T hu φ ψ p q, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) := Ctx.Presented.fresh _ le_rfl
      have ihq := Proof.subst q (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) T)
        (θ.rename u _ T hu'.root) (Subst.ok_rename hθ T hu'.root)
        (Subst.coh_rename hθ hc hu T hu'.root) (hΓ.insertFree u T)
      Proof.ex_elim _ T hu'
        (φ := WFF.subst (VarSymb.renameIdx ι u _) (θ.rename u _ T hu'.root)
          (Subst.ok_rename hθ T hu'.root) (Subst.coh_rename hθ hc hu T hu'.root)
          (hΓ.insertFree u T) (hΓ'.insertFree _ T) φ)
        (Proof.conv (congrArg (WFF.ex T) (WFF.subst_bindFree θ hθ hc hΓ hΓ' hu hu' T φ))
          (Proof.subst p θ hθ hc hΓ))
        (Proof.conv (WFF.subst_weaken_rename θ hθ hc hΓ hΓ' hu hu' T ψ)
          (Proof.castHyps
            (by
              rw [List.map_cons, List.map_map, List.map_map]
              exact congrArg _ (List.map_congr_left fun χ _ =>
                WFF.subst_weaken_rename θ hθ hc hΓ hΓ' hu hu' T χ))
            ihq))
  | _, _, _, .eq_intro _, _, _, _, _, _, _, _ => .eq_intro _
  | _, _, _, @Proof.eq_elim _ _ _ _ φ t s p q, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' s φ).symm
        (Proof.eq_elim
          (φ := WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 .Var hΓ'.root)
            (Subst.ok_under hθ .Var hΓ'.root) (Subst.coh_under hθ hc hΓ .Var hΓ'.root)
            (hΓ.insert .Var) (hΓ'.insert .Var) φ)
          (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s) (Proof.subst p θ hθ hc hΓ)
          (Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ) (Proof.subst q θ hθ hc hΓ)))
  | _, _, _, @Proof.pair_elim _ Γ₀ _ A B u₁ u₂ z hu hz₁ hu₁ hu₂ hzf _ φ p, Γ', _, ι, θ, hθ,
      hc, hΓ =>
      have hΓ₀ : Γ₀.SlotsFrom 0 := Ctx.NoSlots.slots
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.castHyps
        (by
          rw [List.map_map]
          exact List.map_congr_left fun χ _ =>
            (WFF.subst_bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf hΓ₀ hΓ' A B θ hθ hc χ).symm)
        (Proof.conv (WFF.subst_bindPair u₁ u₂ z hu hz₁ hu₁ hu₂ hzf hΓ₀ hΓ' A B θ hθ hc φ).symm
          (Proof.subst p (θ.pairSplit u₁ u₂ z) (Subst.ok_pairSplit hzf hθ)
            (Subst.coh_pairSplit hu hz₁ hu₁ hu₂ hzf hθ hc) ((hΓ₀.insertFree u₁ A).insertFree u₂ B)))
  | _, _, _, .K_box p, Γ', _, ι, θ, hθ, hc, hΓ =>
      Proof.castHyps
        (by
          rw [List.map_map, List.map_map]
          rfl)
        (Proof.K_box (Γ := Γ')
          (Proof.subst p θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn))
  | _, _, _, @Proof.K_dia _ _ x hx Δ₁ Δ₂ φ ψ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hwx : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      have ih := Proof.subst p (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
        (hΓ.diaIn x)
      Proof.castHyps
        (by
          simp only [List.map_cons, List.map_append, List.map_map]
          rfl)
        (Proof.K_dia (Γ := Γ') (ι x) hwx
          (Δ₁ := Δ₁.map (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
            Ctx.NoSlots.slots))
          (Δ₂ := Δ₂.map (WFF.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw)
            (Subst.coh_dia hθ hc hx) (hΓ.diaIn x) Ctx.NoSlots.slots))
          (Proof.castHyps
            (by
              simp only [List.map_cons, List.map_append, List.map_map]
              congr 2
              exact List.map_congr_left fun χ _ =>
                WFF.subst_diaIn_mono θ hθ hc hx hw hΓ Ctx.NoSlots.slots Ctx.NoSlots.slots χ)
            ih))
  | _, _, _, .dia_bot x hx p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hwx : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      .dia_bot (ι x) hwx (Proof.subst p θ hθ hc hΓ)

/-- ⭐**Weakening** along any inclusion of contexts, into a presented context. -/
def Proof.mono {σ : Signature} {Γ Γ' : Ctx} [Γ'.Presented] {Δs : List (WFF σ Γ 0)}
    {φ : WFF σ Γ 0} (h : Γ.Le Γ') (p : Proof σ Γ Δs φ) :
    Proof σ Γ' (Δs.map (WFF.mono h)) (WFF.mono h φ) :=
  have hΓ : Γ.SlotsFrom 0 := (Ctx.NoSlots.slots (Γ := Γ')).of_le h
  have hid : ∀ v T, Γ.ref v = some T → (Subst.idRen (σ := σ) Γ').at v = .ren v :=
    fun v _ _ => Subst.at_idRen v
  have key : ∀ ψ : WFF σ Γ 0, WFF.subst id (Subst.idRen Γ') (Subst.ok_idRen.restrict h)
      (Subst.coh_idRen.restrict h) hΓ Ctx.NoSlots.slots ψ = WFF.mono h ψ :=
    fun ψ => WFF.subst_ren h (Subst.idRen Γ') _ _ hΓ Ctx.NoSlots.slots hid ψ
  Proof.castHyps (List.map_congr_left fun ψ _ => key ψ)
    (Proof.conv (key φ)
      (Proof.subst p (Subst.idRen Γ') (Subst.ok_idRen.restrict h) (Subst.coh_idRen.restrict h) hΓ))

theorem Provable.monoCtx {σ : Signature} {Γ Γ' : Ctx} [Γ'.Presented] {Δs : List (WFF σ Γ 0)}
    {φ : WFF σ Γ 0} (h : Γ.Le Γ') (p : Provable Δs φ) :
    Provable (Δs.map (WFF.mono h)) (WFF.mono h φ) :=
  p.map (Proof.mono h)

end V12
