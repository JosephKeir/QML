import QML.QML_v12m_Open
import QML.QML_v12m_SubstId

/-!
# QML v12m — substitution in proofs

⭐`Proof.subst`: a substitution sending the context `Γ` of a proof into a presented context `Γ'`
sends the proof to a proof of the substituted hypotheses and conclusion.  Renaming and weakening
are the instances whose entries are addresses; ⭐`Proof.mono` is weakening along `Ctx.Le`.

By induction on the proof.  Eigenvariables are renamed to a name fresh for `Γ'`, read off its
presentation, so nothing is assumed of the target beyond being presented.  Pair elimination needs
no rule: its components go to the projections of the pair's entry.

The rules' formula operations commute with substitution: `WFF.subst_mono_eq` (weakening),
`WFF.subst_instantiate`, `WFF.subst_bindFree`, `WFF.subst_bindPair`, `WFF.subst_diaIn_mono`.
-/

namespace V12M

variable [ModalSys]

/-! ## Small facts -/

theorem SubE.mono_refl {σ : Signature} {Δ : Ctx} (h : Δ.Le Δ) : ∀ e : SubE σ Δ, e.mono h = e
  | .hide => rfl
  | .ren _ => rfl
  | .tm s => congrArg SubE.tm (Term.mono_refl h s)

theorem SubE.comp_ren {σ : Signature} {ι₂ : VarSymb → VarSymb} {Δ₁ Δ₂ : Ctx} (θ₂ : Subst σ Δ₂)
    (hθ₂ : Subst.Ok Δ₁ θ₂) (hc₂ : Subst.Coh ι₂ Δ₁ θ₂) (w : VarSymb) :
    (SubE.ren w : SubE σ Δ₁).comp θ₂ hθ₂ hc₂ = θ₂.at w :=
  rfl

omit [ModalSys] in
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
    rw [set_ne _ _ hvr, ← at_nonproj θ hlp, hc v U ((Ctx.ref_nonproj Γ hlp).trans hv') p]
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

/-- ⭐The eigenvariable `u` sent to the **η-expansion** of a fresh `u'`, everything else weakened
    past it.  `Subst.rename` sends it to `u'` as an address, which behaves like a renaming only
    where the whole substitution does (`Subst.IsRen` is global); a term entry is read pointwise
    (`Term.subst_eta_tm`), which is what a hypothesis mentioning the eigenvariable as a *term* — the
    `Here` atom of `Proof.T_dia` — needs. -/
def renameTm (θ : Subst σ Δ) (u u' : ℕ) (T : VarType) (h : Δ (.root (.free u')) = none) :
    Subst σ (Δ.insert (.free u') T) :=
  (θ.mono (Ctx.le_insert h T)).set (.free u)
    (.tm (Term.eta (.root (.free u')) T (Ctx.ref_insert_root Δ (.free u') T)))

/-- The index map `renameTm` coheres with. -/
def renameTmIdx (σ : Signature) (ι : VarSymb → VarSymb) {Δ : Ctx} (u u' : ℕ) (T : VarType)
    (_h : Δ (.root (.free u')) = none) : VarSymb → VarSymb :=
  setIdx ι (.free u)
    (.tm (Term.eta (σ := σ) (.root (.free u')) T (Ctx.ref_insert_root Δ (.free u') T)))

theorem renameTm_ne (θ : Subst σ Δ) {u : ℕ} (u' : ℕ) (T : VarType)
    (h : Δ (.root (.free u')) = none) {v : VarSymb} (hv : v ≠ .root (.free u)) :
    θ.renameTm u u' T h v = (θ v).mono (Ctx.le_insert h T) :=
  if_neg hv

theorem ok_renameTm {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {u u' : ℕ} (T : VarType)
    (h : Δ (.root (.free u')) = none) : Ok (Γ.insert (.free u) T) (θ.renameTm u u' T h) :=
  ok_set (ok_mono hθ _) (e := .tm (Term.eta _ T (Ctx.ref_insert_root Δ (.free u') T))) rfl

theorem coh_renameTm {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (T : VarType)
    (h : Δ (.root (.free u')) = none) :
    Coh (renameTmIdx σ ι u u' T h) (Γ.insert (.free u) T) (θ.renameTm u u' T h) :=
  coh_set (ok_mono hθ _) (coh_mono hc _)
    (e := .tm (Term.eta _ T (Ctx.ref_insert_root Δ (.free u') T))) hu rfl

theorem sim_renameTm_mono {Γ : Ctx} {θ : Subst σ Δ} {u u' : ℕ} (hu : Γ.RootFresh (.free u))
    (T : VarType) (h : Δ (.root (.free u')) = none) :
    Sim Γ (θ.renameTm u u' T h) (θ.mono (Ctx.le_insert h T)) :=
  sim_of fun v _ _ hv => by
    have hvr : v ≠ .root (.free u) := fun he => by
      subst he
      rw [hu.root] at hv
      cases hv
    rw [renameTm_ne _ _ _ _ hvr]
    exact .refl _

/-- At the eigenvariable itself the entry is that η-expansion, which is what reads it off. -/
theorem at_renameTm_root (θ : Subst σ Δ) (u u' : ℕ) (T : VarType)
    (h : Δ (.root (.free u')) = none) :
    (θ.renameTm u u' T h).at (.root (.free u)) =
      .tm (Term.eta (.root (.free u')) T (Ctx.ref_insert_root Δ (.free u') T)) := by
  rw [at_nonproj (θ.renameTm u u' T h)
    (show (VarSymb.root (Root.free u)).lastProj = false from rfl)]
  exact set_root _ _ _

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

theorem Ctx.ref_empty (v : VarSymb) : Ctx.empty.ref v = none :=
  Ctx.ref_none_of_rootFresh (fun _ _ => rfl) v rfl

/-- ⭐Substitution fixes closed formulas: a formula of the empty context, weakened into the source,
    comes out as the same formula weakened into the target. -/
theorem WFF.subst_mono_empty {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d : ℕ}
    (h : Ctx.empty.Le Γ) (h' : Ctx.empty.Le Δ) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d)
    (φ : WFF σ Ctx.empty d) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.mono h φ) = WFF.mono h' φ := by
  have hE : Ctx.empty.SlotsFrom d := fun _ _ _ _ => rfl
  have e := WFF.subst_mono_eq h h' (Subst.idS σ Ctx.empty) Subst.ok_idS Subst.coh_idS θ hθ hc
    hE hΓ hE hΔ (fun v _ hv => by rw [Ctx.ref_empty] at hv; cases hv) φ
  rw [WFF.subst_id] at e
  exact e

/-- `◇□` of a closed formula is closed. -/
theorem WFF.diaBox_closed (Γ : Ctx) (ψ : WFF σ Ctx.empty 0) :
    WFF.diaBox (ψ.closed Γ.boxIn.boxIn) =
      WFF.closed Γ (WFF.diaBox (Γ := Ctx.empty) (ψ.closed _)) := by
  simp only [WFF.closed, WFF.diaBox, WFF.neg, WFF.mono, WFF.mono_mono]

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
    · rw [Subst.set_ne _ _ hvr, Subst.single_ne _ hvr, SubE.comp_ren, Subst.at_nonproj θ hlp]
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


/-- ⭐The term counterpart of `WFF.subst_instantiate`, at **every** type: substituting after filling
    the slot with `t` is filling it with `t` substituted.  Annotations move under substitution, so
    at a compound value type the two sides agree as `Sigma`s; `Term.subst_single_tm` is the base
    case, where the annotation is forced.  The two `Subst.Sim` obligations are as in `WFF`'s — at
    the slot both sides are the entry, elsewhere the composite is the entry itself. -/
theorem Term.subst_single_tm_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {T : VarType} {a : Ann T} (t : Term σ Γ T a)
    {B : VarType} {b : Ann B} (u : Term σ (Γ.insert (.bnd 0) T) B b) :
    (⟨_, Term.subst ι θ hθ hc
        (Term.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
          (Subst.ok_single (Ctx.Le.refl Γ) rfl)
          (Subst.coh_single (hΓ.rootFresh le_rfl) (Ctx.Le.refl Γ) rfl) u)⟩ :
        Σ c, Term σ Δ B c) =
      ⟨_, Term.subst (Subst.singleIdx (.bnd 0) (.tm (Term.subst ι θ hθ hc t)))
        (Subst.single (.bnd 0) (.tm (Term.subst ι θ hθ hc t)))
        (Subst.ok_single (Ctx.Le.refl Δ) rfl)
        (Subst.coh_single (hΔ.rootFresh le_rfl) (Ctx.Le.refl Δ) rfl)
        (Term.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 T hΔ.root)
          (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root) u)⟩ := by
  have hr : Γ.RootFresh (.bnd 0) := hΓ.rootFresh le_rfl
  have hrΔ : Δ.RootFresh (.bnd 0) := hΔ.rootFresh le_rfl
  have he : (SubE.tm (Term.subst ι θ hθ hc t) : SubE σ Δ).OkRef T := rfl
  have hθ₃ := Subst.ok_set (r := .bnd 0) hθ he
  have hc₃ := Subst.coh_set hθ hc hr he
  refine (Term.subst_comp_sig (Subst.single (.bnd 0) (.tm t)) θ _
    (Subst.ok_single (Ctx.Le.refl Γ) rfl) (Subst.coh_single hr (Ctx.Le.refl Γ) rfl) hθ hc
    hθ₃ hc₃ ?_ u).trans
    (Term.subst_comp_sig (θ.under 0 0 T hΔ.root)
      (Subst.single (.bnd 0) (.tm (Term.subst ι θ hθ hc t)))
      _ (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
      (Subst.ok_single (Ctx.Le.refl Δ) rfl) (Subst.coh_single hrΔ (Ctx.Le.refl Δ) rfl) hθ₃ hc₃
      ?_ u).symm
  · refine Subst.sim_of ?_
    intro v U hlp hv
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.set_root, Subst.single_root]
      exact .refl _
    · rw [Subst.set_ne _ _ hvr, Subst.single_ne _ hvr, SubE.comp_ren, Subst.at_nonproj θ hlp]
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

/-- `Term.subst_single_tm_sig` at base value type, where the annotation is forced. -/
theorem Term.subst_single_tm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {T : VarType} {a : Ann T} (t : Term σ Γ T a)
    (u : Term σ (Γ.insert (.bnd 0) T) .Var .var) :
    Term.subst ι θ hθ hc
        (Term.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
          (Subst.ok_single (Ctx.Le.refl Γ) rfl)
          (Subst.coh_single (hΓ.rootFresh le_rfl) (Ctx.Le.refl Γ) rfl) u) =
      Term.subst (Subst.singleIdx (.bnd 0) (.tm (Term.subst ι θ hθ hc t)))
        (Subst.single (.bnd 0) (.tm (Term.subst ι θ hθ hc t)))
        (Subst.ok_single (Ctx.Le.refl Δ) rfl)
        (Subst.coh_single (hΔ.rootFresh le_rfl) (Ctx.Le.refl Δ) rfl)
        (Term.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 T hΔ.root)
          (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root) u) :=
  eq_of_heq (Sigma.mk.inj (Term.subst_single_tm_sig θ hθ hc hΓ hΔ t u)).2

/-- ⭐The term counterpart of `WFF.subst_hereRead`, at **every** value type: the hole term's own
    annotation moves under substitution, so the two sides agree as `Sigma`s.  Filling the slot
    commutes by `Term.subst_single_tm_sig`, and the `□`-collapse by `Term.collapse_subst`. -/
theorem Term.subst_hereRead_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (hT : ModalSys.T = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {B : VarType} {b : Ann B} (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b) :
    (⟨_, Term.subst ι θ hθ hc (Term.hereRead hT t s)⟩ : Σ c, Term σ Δ B c) =
      ⟨_, Term.hereRead hT (Term.subst ι θ hθ hc t)
        (Term.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
          s)⟩ := by
  refine (Term.subst_single_tm_sig θ hθ hc hΓ hΔ t _).trans ?_
  simp only [Term.hereRead]
  exact sig_subst _ _ _ (Term.collapse_subst
    ((Ctx.collapses_boxIn_self hT Γ).insert (hΓ.boxIn.rootFresh le_rfl) A)
    ((Ctx.collapses_boxIn_self hT Δ).insert (hΔ.boxIn.rootFresh le_rfl) A)
    (θ.box.under 0 0 A hΔ.boxIn.root) (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
    (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
    (θ.under 0 0 A hΔ.root) (Subst.ok_under hθ A hΔ.root)
    (Subst.coh_under hθ hc hΓ A hΔ.root)
    (Subst.corr_under (Subst.ok_box hθ) (Subst.corr_box_self hT hθ) hΓ.boxIn A
      hΔ.boxIn.root hΔ.root (hΔ.boxIn.rootFresh le_rfl)) s).symm

/-- `Term.subst_hereRead_sig` at base value type, where the annotation is forced. -/
theorem Term.subst_hereRead {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (hT : ModalSys.T = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (s : Term σ (Γ.boxIn.insert (.bnd 0) A) .Var .var) :
    Term.subst ι θ hθ hc (Term.hereRead hT t s) =
      Term.hereRead hT (Term.subst ι θ hθ hc t)
        (Term.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
          s) :=
  eq_of_heq (Sigma.mk.inj (Term.subst_hereRead_sig hT θ hθ hc hΓ hΔ t s)).2

/-- ⭐The term counterpart of `WFF.subst_viewReadTm`, at **every** value type: as `Sigma`s, the hole
    term's annotation moving under substitution. -/
theorem Term.subst_viewReadTm_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {x : VarSymb} (y : VarSymb)
    (hθy : Subst.Ok (Γ.diaIn x) (θ.dia x y)) (hcy : Subst.Coh ι (Γ.diaIn x) (θ.dia x y))
    (hsy : (Δ.diaIn y).SlotsFrom 0) {A : VarType} {a : Ann A} (bd : Term σ (Γ.diaIn x) A a)
    {B : VarType} {b : Ann B} (s : Term σ (Γ.boxIn.insert (.bnd 0) A) B b) :
    (⟨_, Term.subst ι (θ.dia x y) hθy hcy (Term.viewReadTm bd s)⟩ :
        Σ c, Term σ (Δ.diaIn y) B c) =
      ⟨_, Term.viewReadTm (Term.subst ι (θ.dia x y) hθy hcy bd)
        (Term.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
          s)⟩ := by
  have hmono : Δ.boxIn.Le (Δ.diaIn y) := Ctx.le_boxIn_diaIn Δ y
  have hma : ∀ {Δ₁ Δ₂ : Ctx} (θ' : Subst σ Δ₁) (hle : Δ₁.Le Δ₂) (v : VarSymb),
      θ'.mono hle v = (θ' v).mono hle := fun _ _ _ => rfl
  refine (Term.subst_single_tm_sig (θ.dia x y) hθy hcy (hΓ.diaIn x) hsy bd _).trans ?_
  refine sig_subst _ _ _ ?_
  rw [Term.subst_mono ((Ctx.le_boxIn_diaIn Γ x).insert (.bnd 0) A) _ _ _ s,
    Term.mono_subst (hmono.insert (.bnd 0) A) (θ.box.under 0 0 A hΔ.boxIn.root)
      (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
      (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root) s]
  refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of ?_) s
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [show (θ.dia x y).under 0 0 A hsy.root (.root (.bnd 0)) = .ren (.root (.bnd 0)) from
        if_pos rfl,
      hma _ _ _,
      show θ.box.under 0 0 A hΔ.boxIn.root (.root (.bnd 0)) = .ren (.root (.bnd 0)) from
        if_pos rfl]
    exact .refl _
  · have hv' : Γ.boxIn v = some U := by simpa [Ctx.insert, hvr] using hv
    have hvr' : Γ.boxIn.ref v = some U := (Ctx.ref_nonproj Γ.boxIn hlp).trans hv'
    rw [show (θ.dia x y).under 0 0 A hsy.root v = ((θ.dia x y) v).mono
          (Ctx.le_insert hsy.root A) from if_neg hvr,
      hma _ _ _,
      show θ.box.under 0 0 A hΔ.boxIn.root v = (θ.box v).mono
          (Ctx.le_insert hΔ.boxIn.root A) from if_neg hvr,
      SubE.mono_mono, ← Subst.at_nonproj (θ.dia x y) hlp, ← Subst.at_nonproj θ.box hlp,
      Subst.dia_eq_box_mono θ x y v U hvr', SubE.mono_mono]
    exact .refl _

/-- `Term.subst_viewReadTm_sig` at base value type, where the annotation is forced. -/
theorem Term.subst_viewReadTm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {x : VarSymb} (y : VarSymb)
    (hθy : Subst.Ok (Γ.diaIn x) (θ.dia x y)) (hcy : Subst.Coh ι (Γ.diaIn x) (θ.dia x y))
    (hsy : (Δ.diaIn y).SlotsFrom 0) {A : VarType} {a : Ann A} (bd : Term σ (Γ.diaIn x) A a)
    (s : Term σ (Γ.boxIn.insert (.bnd 0) A) .Var .var) :
    Term.subst ι (θ.dia x y) hθy hcy (Term.viewReadTm bd s) =
      Term.viewReadTm (Term.subst ι (θ.dia x y) hθy hcy bd)
        (Term.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
          s) :=
  eq_of_heq (Sigma.mk.inj
    (Term.subst_viewReadTm_sig θ hθ hc hΓ hΔ y hθy hcy hsy bd s)).2

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
        Subst.under_eq_mono θ hΓ T hΔ.root v U ((Ctx.ref_nonproj Γ hlp).trans hv'),
        Subst.at_nonproj θ hlp]
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

/-- The same for `Subst.renameTm`: away from the eigenvariable it is the weakened substitution, so a
    hypothesis that does not mention the eigenvariable travels exactly as before. -/
theorem WFF.subst_weaken_renameTm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u')) (T : VarType)
    (ψ : WFF σ Γ 0) :
    WFF.subst (Subst.renameTmIdx σ ι u u' T hu'.root) (θ.renameTm u u' T hu'.root)
        (Subst.ok_renameTm hθ T hu'.root) (Subst.coh_renameTm hθ hc hu T hu'.root)
        (hΓ.insertFree u T) (hΔ.insertFree u' T) (WFF.weaken hu.root T ψ) =
      WFF.weaken hu'.root T (WFF.subst ι θ hθ hc hΓ hΔ ψ) :=
  WFF.subst_mono_eq _ _ θ hθ hc _ _ _ hΓ _ hΔ _ (Subst.sim_renameTm_mono hu T hu'.root) ψ

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
    · rw [Subst.set_ne _ _ hvr, Subst.single_ne _ hvr, SubE.comp_ren, Subst.at_nonproj θ hlp]
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
      Subst.at_nonproj _ hlp]
    exact .refl _

end Commute

/-! ## Substitution in proofs -/

/-- Substituting into the `here` reading of a `□`-view formula with a hole: the term substitutes,
    and the hole formula substitutes one view in, under the slot. -/
theorem WFF.subst_hereRead {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (hT : ModalSys.T = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.hereRead hT t ψ) =
      WFF.hereRead hT (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
          (hΓ.boxIn.insert A) (hΔ.boxIn.insert A) ψ) := by
  refine (WFF.subst_instantiate θ hθ hc hΓ hΔ t _).trans ?_
  exact congrArg (WFF.instantiate hΔ (Term.subst ι θ hθ hc t))
    (WFF.collapse_subst
      ((Ctx.collapses_boxIn_self hT Γ).insert (hΓ.boxIn.rootFresh le_rfl) A)
      ((Ctx.collapses_boxIn_self hT Δ).insert (hΔ.boxIn.rootFresh le_rfl) A)
      (θ.box.under 0 0 A hΔ.boxIn.root) (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
      (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
      (θ.under 0 0 A hΔ.root) (Subst.ok_under hθ A hΔ.root)
      (Subst.coh_under hθ hc hΓ A hΔ.root)
      (hΓ.boxIn.insert A) (hΓ.insert A) (hΔ.boxIn.insert A) (hΔ.insert A)
      (Subst.corr_under (Subst.ok_box hθ) (Subst.corr_box_self hT hθ) hΓ.boxIn A
        hΔ.boxIn.root hΔ.root (hΔ.boxIn.rootFresh le_rfl))
      ψ).symm

/-- The `.dia` arm of `WFF.subst`, stated with the target witness address as a *variable*.

    `WFF.subst` builds the node at `ι x`, and callers usually want it at some `y` with `ι x = y`
    only propositionally.  Rewriting that in place is not possible: the address occurs in the type
    of the body, and the `Subst.ok_dia` / `Subst.coh_dia` arguments the arm generates mention `ι x`
    inside their own types, so it cannot be abstracted uniformly — `rw` fails the motive check and
    `generalize` fails outright.  Taking `y` as a variable and the right-hand side's side conditions
    as hypotheses fixes both problems: `subst hxy` rewrites uniformly, and `Ok`, `Coh` and
    `SlotsFrom` are `Prop`s, so what is left is proof irrelevance. -/
theorem WFF.subst_dia {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (y : VarSymb) (hxy : ι x = y)
    (hy : ∃ X, Δ.ref y = some (.VTypeDia X))
    (hθy : Subst.Ok (Γ.diaIn x) (θ.dia x y)) (hcy : Subst.Coh ι (Γ.diaIn x) (θ.dia x y))
    (hsy : (Δ.diaIn y).SlotsFrom d') (φ : WFF σ (Γ.diaIn x) d) :
    WFF.subst ι θ hθ hc hΓ hΔ (.dia x hx φ) =
      .dia y hy (WFF.subst ι (θ.dia x y) hθy hcy (hΓ.diaIn x) hsy φ) := by
  subst hxy
  rfl


/-- ⭐Substituting into the reading of a hole formula inside `◇_x`, with the view term in its hole.
    The witness index is handled by the caller (`WFF.subst_dia`); here the body and the hole formula
    each get their own substitution, and the two `□`-view substitutions are reconciled by
    `Subst.dia_eq_box_mono`: away from the slot, the `◇_y` view of `θ` is the `□` view of `θ`
    weakened into that view. -/
theorem WFF.subst_viewReadTm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {x : VarSymb} (y : VarSymb)
    (hθy : Subst.Ok (Γ.diaIn x) (θ.dia x y)) (hcy : Subst.Coh ι (Γ.diaIn x) (θ.dia x y))
    (hsy : (Δ.diaIn y).SlotsFrom 0) {A : VarType} {a : Ann A} (bd : Term σ (Γ.diaIn x) A a)
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.subst ι (θ.dia x y) hθy hcy (hΓ.diaIn x) hsy (WFF.viewReadTm bd ψ) =
      WFF.viewReadTm (Term.subst ι (θ.dia x y) hθy hcy bd)
        (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
          (hΓ.boxIn.insert A) (hΔ.boxIn.insert A) ψ) := by
  have hmono : Δ.boxIn.Le (Δ.diaIn y) := Ctx.le_boxIn_diaIn Δ y
  have hma : ∀ {Δ₁ Δ₂ : Ctx} (θ' : Subst σ Δ₁) (hle : Δ₁.Le Δ₂) (v : VarSymb),
      θ'.mono hle v = (θ' v).mono hle := fun _ _ _ => rfl
  refine (WFF.subst_instantiate (θ.dia x y) hθy hcy (hΓ.diaIn x) hsy bd _).trans ?_
  refine congrArg (WFF.instantiate hsy (Term.subst ι (θ.dia x y) hθy hcy bd)) ?_
  rw [WFF.subst_mono ((Ctx.le_boxIn_diaIn Γ x).insert (.bnd 0) A) _ _ _
      (hΓ.boxIn.insert A) ((hΓ.diaIn x).insert A) (hsy.insert A) ψ,
    WFF.mono_subst (hmono.insert (.bnd 0) A) (θ.box.under 0 0 A hΔ.boxIn.root)
      (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
      (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
      (hΓ.boxIn.insert A) (hΔ.boxIn.insert A) (hsy.insert A) ψ]
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of ?_) ψ
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    rw [show (θ.dia x y).under 0 0 A hsy.root (.root (.bnd 0)) = .ren (.root (.bnd 0)) from
        if_pos rfl,
      hma _ _ _,
      show θ.box.under 0 0 A hΔ.boxIn.root (.root (.bnd 0)) = .ren (.root (.bnd 0)) from if_pos rfl]
    exact .refl _
  · have hv' : Γ.boxIn v = some U := by simpa [Ctx.insert, hvr] using hv
    have hvr' : Γ.boxIn.ref v = some U := (Ctx.ref_nonproj Γ.boxIn hlp).trans hv'
    rw [show (θ.dia x y).under 0 0 A hsy.root v = ((θ.dia x y) v).mono
          (Ctx.le_insert hsy.root A) from if_neg hvr,
      hma _ _ _,
      show θ.box.under 0 0 A hΔ.boxIn.root v = (θ.box v).mono (Ctx.le_insert hΔ.boxIn.root A) from
        if_neg hvr,
      SubE.mono_mono, ← Subst.at_nonproj (θ.dia x y) hlp, ← Subst.at_nonproj θ.box hlp,
      Subst.dia_eq_box_mono θ x y v U hvr', SubE.mono_mono]
    exact .refl _
/-- Substituting into the `◇_c` reading, with the eigenvariable `c` renamed to `c'`.

    The witness index is dealt with by `WFF.subst_dia` above: the `.dia` arm builds the node at
    `ι x`, which here is `VarSymb.renameIdx ι c c' (.root (.free c))`, only propositionally equal to
    `.root (.free c')` — it reduces to an `if` on `Root.free c = Root.free c`, and `Nat.decEq c c`
    does not reduce for a variable `c`.

    The body is the `◇` counterpart of `WFF.subst_bindFree`: both sides are a `WFF.renameRoot`, so
    each is composed by `WFF.subst_comp` against the common substitution
    `(θ.box.mono _).set (.bnd 0) (.ren (.step (.root (.free c')) .dia))`, which sends the slot to
    `c'.dia` and each `□` entry to its weakening into the `◇_{c'}` view.  Of the two `Subst.Sim`
    obligations, the first goes through `Subst.dia_eq_box_mono` away from the slot — with
    `θ.rename`'s entries related to `θ`'s by `Subst.at_eq_mono_of` and freshness of `c` in `Γ`,
    then `SubE.unbox_mono` / `SubE.keepE_mono` — and through `SubE.diaBody` on a `.ren` at the
    slot; the second is `Subst.under_eq_mono` with the `SubE.comp_mono` / `idRen` step, exactly as
    in `WFF.subst_bindFree`. -/
theorem WFF.subst_diaViewRead {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {c c' : ℕ} (hcf : Γ.RootFresh (.free c)) (hcf' : Δ.RootFresh (.free c'))
    (A : VarType) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.subst (VarSymb.renameIdx ι c c') (θ.rename c c' (.VTypeDia A) hcf'.root)
        (Subst.ok_rename hθ (.VTypeDia A) hcf'.root)
        (Subst.coh_rename hθ hc hcf (.VTypeDia A) hcf'.root)
        (hΓ.insertFree c (.VTypeDia A)) (hΔ.insertFree c' (.VTypeDia A))
        (WFF.dia (.root (.free c)) ⟨A, Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)⟩
          (WFF.viewRead c hcf A ψ)) =
      WFF.dia (.root (.free c')) ⟨A, Ctx.ref_insert_root Δ (.free c') (.VTypeDia A)⟩
        (WFF.viewRead c' hcf' A
          (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 A hΔ.boxIn.root)
            (Subst.ok_under (Subst.ok_box hθ) A hΔ.boxIn.root)
            (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn A hΔ.boxIn.root)
            (hΓ.boxIn.insert A) (hΔ.boxIn.insert A) ψ)) := by
  have hrefΓ : (Γ.insert (.free c) (.VTypeDia A)).ref (.root (.free c)) = some (.VTypeDia A) :=
    Ctx.ref_insert_root Γ (.free c) (.VTypeDia A)
  have hx : ∃ X, (Γ.insert (.free c) (.VTypeDia A)).ref (.root (.free c)) = some (.VTypeDia X) :=
    ⟨A, hrefΓ⟩
  have hy : ∃ X, (Δ.insert (.free c') (.VTypeDia A)).ref (.root (.free c')) = some (.VTypeDia X) :=
    ⟨A, Ctx.ref_insert_root Δ (.free c') (.VTypeDia A)⟩
  have hidx : VarSymb.renameIdx ι c c' (.root (.free c)) = .root (.free c') := if_pos rfl
  have hθr := Subst.ok_rename (u := c) hθ (.VTypeDia A) hcf'.root
  have hcr := Subst.coh_rename hθ hc hcf (.VTypeDia A) hcf'.root
  have hw : ((θ.rename c c' (.VTypeDia A) hcf'.root).at (.root (.free c))).idxAlong [] =
      .root (.free c') := (hcr (.root (.free c)) _ hrefΓ []).trans hidx
  refine (WFF.subst_dia _ hθr hcr (hΓ.insertFree c (.VTypeDia A))
    (hΔ.insertFree c' (.VTypeDia A)) hx (.root (.free c')) hidx hy
    (Subst.ok_dia hθr hx hw) (hidx ▸ Subst.coh_dia hθr hcr hx)
    ((hΔ.insertFree c' (.VTypeDia A)).diaIn _) _).trans ?_
  refine congrArg (WFF.dia (.root (.free c')) hy) ?_
  -- Both sides are a `renameRoot`, i.e. a `subst` by `single (.bnd 0) (.ren _)`; compose each
  -- against the common substitution `θ₃`, which sends the slot to `c'.dia` and everything else
  -- to its `□` entry weakened into the `◇_{c'}` view.
  have hmono : Δ.boxIn.Le ((Δ.insert (.free c') (.VTypeDia A)).diaIn (.root (.free c'))) :=
    (Ctx.le_insert hcf'.root (.VTypeDia A)).boxIn.trans
      (Ctx.le_boxIn_diaIn _ (.root (.free c')))
  have hedge : ((Δ.insert (.free c') (.VTypeDia A)).diaIn (.root (.free c'))).ref
      (.step (.root (.free c')) .dia) = some A :=
    Ctx.ref_diaIn_of (Ctx.ref_insert_root Δ (.free c') (.VTypeDia A))
  have hθ₃ : Subst.Ok (Γ.boxIn.insert (.bnd 0) A)
      ((θ.box.mono hmono).set (.bnd 0) (.ren (.step (.root (.free c')) .dia))) :=
    Subst.ok_set (Subst.ok_mono (Subst.ok_box hθ) hmono)
      (e := .ren (.step (.root (.free c')) .dia)) hedge
  have hc₃ : Subst.Coh (Subst.setIdx ι (.bnd 0) (.ren (.step (.root (.free c')) .dia)))
      (Γ.boxIn.insert (.bnd 0) A)
      ((θ.box.mono hmono).set (.bnd 0) (.ren (.step (.root (.free c')) .dia))) :=
    Subst.coh_set (Subst.ok_mono (Subst.ok_box hθ) hmono)
      (Subst.coh_mono (Subst.coh_box hθ hc) hmono) (hΓ.boxIn.rootFresh le_rfl)
      (e := .ren (.step (.root (.free c')) .dia)) hedge
  refine (WFF.subst_comp _ _ _ _ _ _ _ hθ₃ hc₃ _ _ _ ?_ ψ).trans
    (WFF.subst_comp _ _ _ _ _ _ _ hθ₃ hc₃ _ _ _ ?_ ψ).symm
  · -- `single (.bnd 0) (.ren c.dia)` then the `◇_{c'}` view of the renamed substitution.
    have hat : ∀ w T, Γ.ref w = some T →
        (θ.rename c c' (.VTypeDia A) hcf'.root).at w =
          (θ.at w).mono (Ctx.le_insert hcf'.root (.VTypeDia A)) :=
      Subst.at_eq_mono_of _ (fun w T _ hw =>
        Subst.rename_ne θ c' (.VTypeDia A) hcf'.root (fun he => by
          subst he
          rw [hcf.root] at hw
          cases hw))
    have hbox : ∀ w T, Γ.boxIn.ref w = some T →
        (θ.rename c c' (.VTypeDia A) hcf'.root).box.at w =
          (θ.box.at w).mono ((Ctx.le_insert hcf'.root (.VTypeDia A)).boxIn) :=
      Subst.at_eq_mono_of _ (fun w T _ hw => by
        match w with
        | .step u .box =>
            change ((θ.rename c c' (.VTypeDia A) hcf'.root).at u).unbox = _
            rw [hat u _ (Ctx.boxIn_step_box hw), SubE.unbox_mono]
            rfl
        | .step u .keep =>
            obtain ⟨hF, hu, B, rfl⟩ := Ctx.boxIn_keep hw
            change ((θ.rename c c' (.VTypeDia A) hcf'.root).at u).keepE = _
            rw [hat u _ hu, SubE.keepE_mono]
            rfl
        | .root _ => cases hw
        | .step _ .fst => cases hw
        | .step _ .snd => cases hw
        | .step _ .dia => cases hw
        | .step _ .here => cases hw)
    refine Subst.sim_of ?_
    intro v U hlp hv
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.set_root, Subst.single_root, SubE.comp_ren,
        Subst.at_nonproj _ (rfl : (VarSymb.step (.root (.free c)) .dia).lastProj = false)]
      change SubE.Sim U (SubE.ren (.step (.root (.free c')) .dia))
        (if (VarSymb.root (.free c)) = (VarSymb.root (.free c)) then
          ((θ.rename c c' (.VTypeDia A) hcf'.root).at (.root (.free c))).diaBody
            (.root (.free c'))
          else SubE.hide)
      rw [if_pos rfl, show (θ.rename c c' (.VTypeDia A) hcf'.root).at (.root (.free c)) =
        SubE.ren (.root (.free c')) from Subst.rename_root θ c c' (.VTypeDia A) hcf'.root]
      exact .refl _
    · have hv' : Γ.boxIn v = some U := by simpa [Ctx.insert, hvr] using hv
      have hvr' : Γ.boxIn.ref v = some U := (Ctx.ref_nonproj Γ.boxIn hlp).trans hv'
      rw [Subst.set_ne _ _ hvr, Subst.single_ne _ hvr, SubE.comp_ren,
        Subst.dia_eq_box_mono _ _ _ v U
          (((Ctx.le_insert hcf.root (.VTypeDia A)).boxIn).ref hvr'),
        hbox v U hvr', SubE.mono_mono, Subst.at_nonproj θ.box hlp]
      exact .refl _
  · -- The `□` view under the slot, then `single (.bnd 0) (.ren c'.dia)`.
    refine Subst.sim_of ?_
    intro v U hlp hv
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.set_root,
        show θ.box.under 0 0 A hΔ.boxIn.root (.root (.bnd 0)) = .ren (.root (.bnd 0)) from
          if_pos rfl, SubE.comp_ren, Subst.at_nonproj _ hlp, Subst.single_root]
      exact .refl _
    · have hv' : Γ.boxIn v = some U := by simpa [Ctx.insert, hvr] using hv
      rw [Subst.set_ne _ _ hvr,
        show θ.box.under 0 0 A hΔ.boxIn.root v = (θ.box v).mono
          (Ctx.le_insert hΔ.boxIn.root A) from if_neg hvr,
        SubE.comp_mono (Subst.idRen _) Subst.ok_idRen Subst.coh_idRen
          (Ctx.le_insert hΔ.boxIn.root A) hmono _ _ _
          (fun w _ hw' => by
            rw [Subst.single_at_ne (Ctx.ref_rt_ne (hΔ.boxIn.rootFresh le_rfl) hw'),
              Subst.at_idRen]
            rfl)
          (Subst.ok_box hθ v U hlp hv'),
        SubE.comp_idRen]
      exact .refl _


/-! ## The pinned form of the realisation rules

`WFF.viewReadTm` at the η-expansion of the witness content is the reading `WFF.viewReadAt`, so the
rules specialise to the form one expects, `Here x t, □_x χ ⊢ χ(t)` and `Here x t, χ(t) ⊢ ◇_x χ`,
with `χ(t) = WFF.realiseAt`.
-/

/-- ⭐The general reading at the witness content is the pinned one: the two substitutions send the
    slot to `x.dia` as a term and as a renaming, which is exactly `SubE.Sim.eta_ren`. -/
theorem WFF.viewReadTm_eta {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {A : VarType}
    (hx : Γ.ref x = some (.VTypeDia A)) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.viewReadTm (Term.eta (.step x .dia) A (Ctx.ref_diaIn_of hx)) ψ =
      WFF.renameRoot (.bnd 0) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0))
        (Ctx.le_boxIn_diaIn Γ x) (.step x .dia) (Ctx.ref_diaIn_of hx)
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) (Ctx.NoSlots.slots (Γ := Γ.diaIn x)) ψ := by
  refine (WFF.subst_mono ((Ctx.le_boxIn_diaIn Γ x).insert (.bnd 0) A) _ _ _
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) _ _ ψ).trans ?_
  refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of ?_) ψ
  intro v U _ hv
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    have hUA : U = A := by simpa [Ctx.insert] using hv.symm
    subst hUA
    rw [Subst.single_root, Subst.single_root]
    exact .eta_ren _ (Ctx.ref_diaIn_of hx)
  · rw [Subst.single_ne _ hvr, Subst.single_ne _ hvr]
    exact .refl _

/-- ⭐**Elimination, pinned at an address**: `Here x t, □_x χ ⊢ χ(t)`, the rule strong T's canonical
    model states as `RealDatum.spec`.  Every view formula is its abstraction read back
    (`WFF.viewReadAt_diaAbs`), so the hole formula is `WFF.diaAbs`. -/
def Proof.here_elimAt {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
    (c : ℕ) {A : VarType} (hA : A.diaFree = true)
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a : Ann A} (t : Term σ Γ A a) (χ : WFF σ (Γ.diaIn (.root (.free c))) 0)
    (ph : Proof σ Γ Δ (WFF.hereAt hT (.root (.free c)) hA hcA t))
    (pb : Proof σ Γ Δ (WFF.boxx (.root (.free c)) ⟨A, hcA⟩ χ)) :
    Proof σ Γ Δ (WFF.realiseAt hT c hcA hfr t χ) :=
  Proof.here_elim hT (.root (.free c)) ⟨A, hcA⟩ hA t
    (Term.eta (.step (.root (.free c)) .dia) A (Ctx.ref_diaIn_of hcA))
    (WFF.diaAbs c hcA hfr χ) ph
    (Proof.conv (congrArg (WFF.boxx (.root (.free c)) ⟨A, hcA⟩)
      (((WFF.viewReadAt_diaAbs c hcA hfr χ).symm.trans
        (WFF.viewReadTm_eta hcA (WFF.diaAbs c hcA hfr χ)).symm))) pb)

/-- ⭐**Introduction, pinned at an address**: `Here x t, χ(t) ⊢ ◇_x χ`. -/
def Proof.here_introAt {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
    (c : ℕ) {A : VarType} (hA : A.diaFree = true)
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a : Ann A} (t : Term σ Γ A a) (χ : WFF σ (Γ.diaIn (.root (.free c))) 0)
    (ph : Proof σ Γ Δ (WFF.hereAt hT (.root (.free c)) hA hcA t))
    (pr : Proof σ Γ Δ (WFF.realiseAt hT c hcA hfr t χ)) :
    Proof σ Γ Δ (WFF.dia (.root (.free c)) ⟨A, hcA⟩ χ) :=
  Proof.conv (congrArg (WFF.dia (.root (.free c)) ⟨A, hcA⟩)
      ((WFF.viewReadTm_eta hcA (WFF.diaAbs c hcA hfr χ)).trans
        (WFF.viewReadAt_diaAbs c hcA hfr χ)))
    (Proof.here_intro hT (.root (.free c)) ⟨A, hcA⟩ hA t
      (Term.eta (.step (.root (.free c)) .dia) A (Ctx.ref_diaIn_of hcA))
      (WFF.diaAbs c hcA hfr χ) ph pr)

/-! ## `Here` at a pair content, componentwise -/

/-- ⭐**The `×` clause of compound `Here`, forwards**: if a pair content is realised here by a pair,
    each component is realised here by its component.  An instance of `here_beta` at the hole term
    built from the **slot's own `.fst` address** — a hole term of *compound* value type, and so the
    reason `here_beta` had to be general there (§2d).  The substitution machinery does the work: the
    entry is a term, and `SubE.proj` takes the pair apart
    (`Subst.at_single_fst`, `Term.viewReadTm_eta_fst`, `Term.hereRead_eta_fst`).

    There is no converse.  Nothing introduces a `Here` except the outward rule `T_dia`, so two
    component facts cannot be assembled into one about the pair — and nothing needs them to be: the
    chain hands over a compound `Here` directly at the witness's full content type. -/
def Proof.here_fst {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
    (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A B : VarType} (hA : A.diaFree = true)
    (hB : B.diaFree = true) {a : Ann A} {b : Ann B}
    (t₁ : Term σ Γ A a) (t₂ : Term σ Γ B b) {a' : Ann A} {b' : Ann B}
    (bd₁ : Term σ (Γ.diaIn x) A a') (bd₂ : Term σ (Γ.diaIn x) B b')
    (p : Proof σ Γ Δ (WFF.here hT (VarType.diaFree_prod hA hB)
      (Term.diatm x hx (Term.pair bd₁ bd₂)) (Term.pair t₁ t₂))) :
    Proof σ Γ Δ (WFF.here hT hA (Term.diatm x hx bd₁) t₁) :=
  Proof.conv
    (WFF.here_congr hT hA (sig_diatm (Term.viewReadTm_eta_fst bd₁ bd₂))
      (Term.hereRead_eta_fst hT t₁ t₂))
    (Proof.here_beta hT x hx (VarType.diaFree_prod hA hB) (Term.pair t₁ t₂) (Term.pair bd₁ bd₂) hA
      (Term.eta (.step (.root (.bnd 0)) .fst) A (Ctx.ref_insert_fst Γ.boxIn (.bnd 0) A B)) p)

/-- The second component, by the slot's `.snd` address. -/
def Proof.here_snd {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
    (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A B : VarType} (hA : A.diaFree = true)
    (hB : B.diaFree = true) {a : Ann A} {b : Ann B}
    (t₁ : Term σ Γ A a) (t₂ : Term σ Γ B b) {a' : Ann A} {b' : Ann B}
    (bd₁ : Term σ (Γ.diaIn x) A a') (bd₂ : Term σ (Γ.diaIn x) B b')
    (p : Proof σ Γ Δ (WFF.here hT (VarType.diaFree_prod hA hB)
      (Term.diatm x hx (Term.pair bd₁ bd₂)) (Term.pair t₁ t₂))) :
    Proof σ Γ Δ (WFF.here hT hB (Term.diatm x hx bd₂) t₂) :=
  Proof.conv
    (WFF.here_congr hT hB (sig_diatm (Term.viewReadTm_eta_snd bd₁ bd₂))
      (Term.hereRead_eta_snd hT t₁ t₂))
    (Proof.here_beta hT x hx (VarType.diaFree_prod hA hB) (Term.pair t₁ t₂) (Term.pair bd₁ bd₂) hB
      (Term.eta (.step (.root (.bnd 0)) .snd) B (Ctx.ref_insert_snd Γ.boxIn (.bnd 0) A B)) p)

/-- Substituting into a term weakened past a renamed eigenvariable is weakening the substituted
    term.  Stated for dependent pairs: the annotations are built from `renameIdx ι u u'` and `ι`,
    which agree on the term's indices only propositionally. -/
theorem Term.subst_mono_rename_sigma {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {u u' : ℕ} (hu : Γ.RootFresh (.free u))
    (hu' : Δ.RootFresh (.free u')) (T : VarType) {A : VarType} {a : Ann A} (t : Term σ Γ A a) :
    (⟨_, Term.subst (VarSymb.renameIdx ι u u') (θ.rename u u' T hu'.root)
        (Subst.ok_rename hθ T hu'.root) (Subst.coh_rename hθ hc hu T hu'.root)
        (Term.mono (Ctx.le_insert hu.root T) t)⟩ : Σ b, Term σ (Δ.insert (.free u') T) A b) =
      ⟨_, Term.mono (Ctx.le_insert hu'.root T) (Term.subst ι θ hθ hc t)⟩ := by
  rw [Term.subst_mono, Term.mono_subst]
  exact Term.subst_congr _ _ _ _ _ _ (Subst.sim_rename_mono hu T hu'.root) t

/-- The same for `Subst.renameTm`. -/
theorem Term.subst_mono_renameTm_sigma {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {u u' : ℕ} (hu : Γ.RootFresh (.free u))
    (hu' : Δ.RootFresh (.free u')) (T : VarType) {A : VarType} {a : Ann A} (t : Term σ Γ A a) :
    (⟨_, Term.subst (Subst.renameTmIdx σ ι u u' T hu'.root) (θ.renameTm u u' T hu'.root)
        (Subst.ok_renameTm hθ T hu'.root) (Subst.coh_renameTm hθ hc hu T hu'.root)
        (Term.mono (Ctx.le_insert hu.root T) t)⟩ : Σ b, Term σ (Δ.insert (.free u') T) A b) =
      ⟨_, Term.mono (Ctx.le_insert hu'.root T) (Term.subst ι θ hθ hc t)⟩ := by
  rw [Term.subst_mono, Term.mono_subst]
  exact Term.subst_congr _ _ _ _ _ _ (Subst.sim_renameTm_mono hu T hu'.root) t

/-- ⭐**Substituting the `Here` atom of `Proof.T_dia`.**  The eigenvariable occurs as a *term*, its
    η-expansion, and `Subst.renameTm` sends it to the new eigenvariable's η-expansion — read off
    pointwise by `Term.subst_eta_tm`, which is why the entry is a term and not a renaming.  The
    value travels by `Term.subst_mono_renameTm_sigma`, and `WFF.here_congr` takes both sides as
    `Sigma`s because substitution moves the annotations. -/
theorem WFF.subst_hereAt_renameTm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (hT : ModalSys.T = true)
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u'))
    {A : VarType} (hA : A.diaFree = true) {a : Ann A} (t : Term σ Γ A a) :
    WFF.subst (Subst.renameTmIdx σ ι u u' (.VTypeDia A) hu'.root)
        (θ.renameTm u u' (.VTypeDia A) hu'.root)
        (Subst.ok_renameTm hθ (.VTypeDia A) hu'.root)
        (Subst.coh_renameTm hθ hc hu (.VTypeDia A) hu'.root)
        (hΓ.insertFree u (.VTypeDia A)) (hΔ.insertFree u' (.VTypeDia A))
        (WFF.hereAt hT (.root (.free u)) hA (Ctx.ref_insert_root Γ (.free u) (.VTypeDia A))
          (Term.weaken hu.root (.VTypeDia A) t) : WFF σ (Γ.insert (.free u) (.VTypeDia A)) 0) =
      WFF.hereAt hT (.root (.free u')) hA (Ctx.ref_insert_root Δ (.free u') (.VTypeDia A))
        (Term.weaken hu'.root (.VTypeDia A) (Term.subst ι θ hθ hc t)) :=
  WFF.here_congr hT hA
    (Term.subst_eta_tm _ _ _ (.VTypeDia A) (.root (.free u))
      (Ctx.ref_insert_root Γ (.free u) (.VTypeDia A)) _
      (Subst.at_renameTm_root θ u u' (.VTypeDia A) hu'.root))
    (Term.subst_mono_renameTm_sigma θ hθ hc hu hu' (.VTypeDia A) t)

/-- The `here` reading depends on its term only as a dependent pair. -/
theorem WFF.hereRead_congr {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true) {A : VarType}
    {a₁ a₂ : Ann A} {t₁ : Term σ Γ A a₁} {t₂ : Term σ Γ A a₂}
    (h : (⟨a₁, t₁⟩ : Σ b, Term σ Γ A b) = ⟨a₂, t₂⟩) (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.hereRead hT t₁ ψ = WFF.hereRead hT t₂ ψ := by
  cases h
  rfl

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
  | _, _, _, @Proof.all_intro _ _ _ _ Δs u T hu φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) := Ctx.Presented.fresh_bound _ le_rfl
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
  | _, _, _, @Proof.all_elim _ _ _ _ _ T φ _ t p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ).symm
        (Proof.all_elim T (Term.subst ι θ hθ hc t) (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.ex_intro _ _ _ _ _ T φ _ t p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.ex_intro T (Term.subst ι θ hθ hc t)
        (Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ) (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.ex_elim _ _ _ _ Δs u T hu φ ψ p q, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) := Ctx.Presented.fresh_bound _ le_rfl
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
  | _, _, _, @Proof.eq_elim _ _ _ _ _ φ t s p q, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' s φ).symm
        (Proof.eq_elim
          (φ := WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 .Var hΓ'.root)
            (Subst.ok_under hθ .Var hΓ'.root) (Subst.coh_under hθ hc hΓ .Var hΓ'.root)
            (hΓ.insert .Var) (hΓ'.insert .Var) φ)
          (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s) (Proof.subst p θ hθ hc hΓ)
          (Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ) (Proof.subst q θ hθ hc hΓ)))
  | _, _, _, @Proof.pair_elim _ _ Γ₀ _ A B u₁ u₂ z hu hz₁ hu₁ hu₂ hzf _ φ p, Γ', _, ι, θ, hθ,
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
  | _, _, _, @Proof.K_dia _ _ _ x hx Δ₁ Δ₂ φ ψ p, Γ', _, ι, θ, hθ, hc, hΓ =>
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
  | _, _, _, .D_box hD p, _, _, _, θ, hθ, hc, hΓ => .D_box hD (Proof.subst p θ hθ hc hΓ)
  | _, _, _, .D_ex hDS, _, _, _, _, _, _, _ => .D_ex hDS
  | _, _, _, .B_dia hB ψ p, _, _, _, θ, hθ, hc, hΓ =>
      Proof.conv
        (WFF.subst_mono_empty (Ctx.empty_le _) (Ctx.empty_le _) θ hθ hc hΓ Ctx.NoSlots.slots
          ψ).symm
        (.B_dia hB ψ (Proof.conv
          ((congrArg (WFF.subst _ θ hθ hc hΓ Ctx.NoSlots.slots) (WFF.diaBox_closed _ ψ)).trans
            ((WFF.subst_mono_empty _ _ θ hθ hc hΓ Ctx.NoSlots.slots _).trans
              (WFF.diaBox_closed _ ψ).symm))
          (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.T_box _ _ _ _ hT _ φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      Proof.conv
        (WFF.collapse_subst (Ctx.collapses_boxIn_self hT _) (Ctx.collapses_boxIn_self hT Γ')
          θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ hc hΓ.boxIn hΓ Ctx.NoSlots.slots
          Ctx.NoSlots.slots (Subst.corr_box_self hT hθ) φ)
        (Proof.T_box hT (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.four_box _ _ _ _ hF _ φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      Proof.conv
        (congrArg (fun χ => WFF.box (WFF.box χ))
          (WFF.shift_subst (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF Γ')
            θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ.box.box
            (Subst.ok_box (Subst.ok_box hθ)) (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc))
            hΓ.boxIn hΓ.boxIn.boxIn Ctx.NoSlots.slots Ctx.NoSlots.slots
            (Subst.shiftCorr_box_box hF hθ) φ))
        (Proof.four_box hF (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.T_dia _ _ _ _ hT hS A hA _ t c hcf _ _ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hcf' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.subst p (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) (.VTypeDia A))
        (θ.renameTm c _ (.VTypeDia A) hcf'.root) (Subst.ok_renameTm hθ (.VTypeDia A) hcf'.root)
        (Subst.coh_renameTm hθ hc hcf (.VTypeDia A) hcf'.root) (hΓ.insertFree c (.VTypeDia A))
      Proof.T_dia hT hS A hA (Term.subst ι θ hθ hc t) (Ctx.Presented.bound Γ') hcf'
        (Proof.castHyps
          (by
            simp only [List.map_cons, List.map_map, Function.comp_def]
            exact congrArg₂ List.cons
              (WFF.subst_hereAt_renameTm hT θ hθ hc hΓ hΓ' hcf hcf' hA t)
              (List.map_congr_left fun χ _ =>
                WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' (.VTypeDia A) χ))
          (Proof.conv (WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' (.VTypeDia A) _) ih))
  | _, _, _, @Proof.here_elim _ _ Γ _ _ hT x hx A hA a t a₁ bd ψ ph pb, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (WFF.subst_hereRead hT θ hθ hc hΓ hΓ' t ψ).symm
        (Proof.here_elim hT (ι x) hy hA (Term.subst ι θ hθ hc t)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) _
          (Proof.subst ph θ hθ hc hΓ)
          (Proof.conv (congrArg (WFF.boxx (ι x) hy)
            (WFF.subst_viewReadTm θ hθ hc hΓ hΓ' (ι x) (Subst.ok_dia hθ hx hw)
              (Subst.coh_dia hθ hc hx) (hΓ'.diaIn (ι x)) bd ψ))
            (Proof.subst pb θ hθ hc hΓ)))
  | _, _, _, @Proof.here_intro _ _ Γ _ _ hT x hx A hA a t a₁ bd ψ ph pr, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (congrArg (WFF.dia (ι x) hy)
          (WFF.subst_viewReadTm θ hθ hc hΓ hΓ' (ι x) (Subst.ok_dia hθ hx hw)
            (Subst.coh_dia hθ hc hx) (hΓ'.diaIn (ι x)) bd ψ).symm)
        (Proof.here_intro hT (ι x) hy hA (Term.subst ι θ hθ hc t)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) _
          (Proof.subst ph θ hθ hc hΓ)
          (Proof.conv (WFF.subst_hereRead hT θ hθ hc hΓ hΓ' t ψ) (Proof.subst pr θ hθ hc hΓ)))
  | _, _, _, @Proof.here_beta _ _ Γ _ _ hT x hx A hA a t a₁ bd B hB b s ph, Γ', _, ι, θ, hθ,
      hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv
        (WFF.here_congr hT hB
          (sig_diatm
            (Term.subst_viewReadTm_sig θ hθ hc hΓ hΓ' (ι x) (Subst.ok_dia hθ hx hw)
              (Subst.coh_dia hθ hc hx) (hΓ'.diaIn (ι x)) bd s).symm)
          (Term.subst_hereRead_sig hT θ hθ hc hΓ hΓ' t s).symm)
        (Proof.here_beta hT (ι x) hy hA (Term.subst ι θ hθ hc t)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) hB _
          (Proof.subst ph θ hθ hc hΓ))
  | _, _, _, @Proof.here_fun _ _ Γ _ hT A hA b s a t t' ph ph', Γ', _, ι, θ, hθ, hc, hΓ =>
      Proof.conv (WFF.subst_eqRec θ hθ hc hΓ Ctx.NoSlots.slots A hA t t').symm
        (Proof.here_fun hT hA (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
          (Term.subst ι θ hθ hc t') (Proof.subst ph θ hθ hc hΓ) (Proof.subst ph' θ hθ hc hΓ))

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

end V12M
