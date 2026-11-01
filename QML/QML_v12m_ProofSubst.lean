import QML.QML_v12m_Eq
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

/-- A reachable address is not rooted at a fresh name. -/
theorem Ctx.RootFresh.rt_ne {Δ : Ctx} {r : Root} (hfr : Δ.RootFresh r) :
    ∀ {w : VarSymb} {T : VarType}, Δ.ref w = some T → w.rt ≠ r
  | .root r', T, h, he => by
      change Δ (.root r') = some T at h
      have hrr : r' = r := he
      subst hrr
      rw [hfr.root] at h
      cases h
  | .step w s, T, h, he => by
      simp only [Ctx.ref] at h
      split_ifs at h with hs
      · cases hU : Δ.ref w with
        | none => rw [hU] at h; cases h
        | some U => exact Ctx.RootFresh.rt_ne hfr hU he
      · rw [hfr _ he] at h
        cases h

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


/-- ⭐Substituting **under a slot**, on a term weakened from below it, is the weakening of the
    substituted term: on everything `Γ` declares — and `Γ` declares no slot — `Subst.under` is `θ`
    weakened past the slot (`Subst.sim_of`), and weakening then commutes with substitution
    (`Term.mono_subst`).  `Sigma`-valued, since substitution moves the annotation.  This is what an
    existential whose body mentions a `Γ`-term needs, `Proof.here_name`'s being the one. -/
theorem Term.subst_under_mono {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    (B : VarType) {T : VarType} {a : Ann T} (t : Term σ Γ T a) :
    (⟨_, Term.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 B hΔ.root)
        (Subst.ok_under hθ B hΔ.root) (Subst.coh_under hθ hc hΓ B hΔ.root)
        (Term.mono (Ctx.le_insert hΓ.root B) t)⟩ :
      Σ b, Term σ (Δ.insert (.bnd 0) B) T b) =
      ⟨_, Term.mono (Ctx.le_insert hΔ.root B) (Term.subst ι θ hθ hc t)⟩ := by
  have hsim : Subst.Sim Γ (θ.under 0 0 B hΔ.root) (θ.mono (Ctx.le_insert hΔ.root B)) := by
    refine Subst.sim_of fun v U _ hv => ?_
    have hne : v ≠ .root (.bnd 0) := fun hvr => by
      rw [hvr, hΓ.root] at hv
      cases hv
    rw [show θ.under 0 0 B hΔ.root v = (θ v).mono (Ctx.le_insert hΔ.root B) from if_neg hne]
    exact .refl _
  rw [Term.subst_mono]
  refine (Term.subst_congr (θ.under 0 0 B hΔ.root) (θ.mono (Ctx.le_insert hΔ.root B))
    ((Subst.ok_under hθ B hΔ.root).restrict (Ctx.le_insert hΓ.root B))
    (Subst.ok_mono hθ (Ctx.le_insert hΔ.root B))
    ((Subst.coh_under hθ hc hΓ B hΔ.root).restrict (Ctx.le_insert hΓ.root B))
    (Subst.coh_mono hc (Ctx.le_insert hΔ.root B)) hsim t).trans ?_
  exact congrArg (Sigma.mk _) (Term.mono_subst (Ctx.le_insert hΔ.root B) θ hθ hc t).symm

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

/-- ⭐**Substitution commutes with equality at every type.**  At `◇` the equality is
    `□_x (eqRec A t s)`, and substitution sends both the `□_x` and the two terms to the witness's
    image `ι x`, with the bodies under `θ.dia x (ι x)` — the same arm on both sides, so the case is
    the inductive hypothesis there.  (`WFF.subst_eqRec` is the `◇`-free special case.) -/
theorem WFF.subst_eqRec_gen {ι : VarSymb → VarSymb} :
    {Γ Δ : Ctx} → {d d' : ℕ} → (θ : Subst σ Δ) → (hθ : Subst.Ok Γ θ) → (hc : Subst.Coh ι Γ θ) →
    (hΓ : Γ.SlotsFrom d) → (hΔ : Δ.SlotsFrom d') → (T : VarType) → {a : Ann T} →
    (t : Term σ Γ T a) → (s : Term σ Γ T a) →
    WFF.subst ι θ hθ hc hΓ hΔ (eqRec T t s : WFF σ Γ d) =
      eqRec T (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s)
  | _, _, _, _, _, _, _, _, _, .Var, .var, t, s => by
      have e : ∀ {Γ' : Ctx} {e' : ℕ} (u v : Term σ Γ' .Var .var),
          (eqRec .Var u v : WFF σ Γ' e') = .eq u v := by
        intro _ _ u v
        cases u <;> cases v <;> rfl
      rw [e t s, e _ _]
      rfl
  | _, _, _, _, _, _, _, _, _, .VTypeOne, .one, .unit, .unit => rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change WFF.and (WFF.subst ι θ hθ hc hΓ hΔ (eqRec A t₁ s₁))
        (WFF.subst ι θ hθ hc hΓ hΔ (eqRec B t₂ s₂)) = _
      rw [WFF.subst_eqRec_gen θ hθ hc hΓ hΔ A t₁ s₁, WFF.subst_eqRec_gen θ hθ hc hΓ hΔ B t₂ s₂]
      rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeBox A, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        hΓ.boxIn hΔ.boxIn (eqRec A t s)) = _
      rw [WFF.subst_eqRec_gen θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn A t s]
      rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s => by
      obtain ⟨X, hr⟩ := id hx
      have hw : (θ.at x).idxAlong [] = ι x := hc x _ hr []
      exact congrArg (WFF.boxx (ι x) (SubE.ref_witness (Subst.okRef_at hθ hr) hw))
        (WFF.subst_eqRec_gen (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hΓ.diaIn x) (hΔ.diaIn (ι x)) A t s)

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
            obtain ⟨hF, hu, _⟩ := Ctx.boxIn_keep hw
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
    (c : ℕ) {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a : Ann A} (t : Term σ Γ A a) (χ : WFF σ (Γ.diaIn (.root (.free c))) 0)
    (ph : Proof σ Γ Δ (WFF.hereAt hT (.root (.free c)) hcA t))
    (pb : Proof σ Γ Δ (WFF.boxx (.root (.free c)) ⟨A, hcA⟩ χ)) :
    Proof σ Γ Δ (WFF.realiseAt hT c hcA hfr t χ) :=
  Proof.here_elim hT (.root (.free c)) ⟨A, hcA⟩ t
    (Term.eta (.step (.root (.free c)) .dia) A (Ctx.ref_diaIn_of hcA))
    (WFF.diaAbs c hcA hfr χ) ph
    (Proof.conv (congrArg (WFF.boxx (.root (.free c)) ⟨A, hcA⟩)
      (((WFF.viewReadAt_diaAbs c hcA hfr χ).symm.trans
        (WFF.viewReadTm_eta hcA (WFF.diaAbs c hcA hfr χ)).symm))) pb)

/-- ⭐**Introduction, pinned at an address**: `Here x t, χ(t) ⊢ ◇_x χ`. -/
def Proof.here_introAt {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
    (c : ℕ) {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a : Ann A} (t : Term σ Γ A a) (χ : WFF σ (Γ.diaIn (.root (.free c))) 0)
    (ph : Proof σ Γ Δ (WFF.hereAt hT (.root (.free c)) hcA t))
    (pr : Proof σ Γ Δ (WFF.realiseAt hT c hcA hfr t χ)) :
    Proof σ Γ Δ (WFF.dia (.root (.free c)) ⟨A, hcA⟩ χ) :=
  Proof.conv (congrArg (WFF.dia (.root (.free c)) ⟨A, hcA⟩)
      ((WFF.viewReadTm_eta hcA (WFF.diaAbs c hcA hfr χ)).trans
        (WFF.viewReadAt_diaAbs c hcA hfr χ)))
    (Proof.here_intro hT (.root (.free c)) ⟨A, hcA⟩ t
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
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A B : VarType} {a : Ann A} {b : Ann B}
    (t₁ : Term σ Γ A a) (t₂ : Term σ Γ B b) {a' : Ann A} {b' : Ann B}
    (bd₁ : Term σ (Γ.diaIn x) A a') (bd₂ : Term σ (Γ.diaIn x) B b')
    (p : Proof σ Γ Δ (WFF.here hT
      (Term.diatm x hx (Term.pair bd₁ bd₂)) (Term.pair t₁ t₂))) :
    Proof σ Γ Δ (WFF.here hT (Term.diatm x hx bd₁) t₁) :=
  Proof.conv
    (WFF.here_congr hT (sig_diatm (Term.viewReadTm_eta_fst bd₁ bd₂))
      (Term.hereRead_eta_fst hT t₁ t₂))
    (Proof.here_beta hT x hx (Term.pair t₁ t₂) (Term.pair bd₁ bd₂)
      (Term.eta (.step (.root (.bnd 0)) .fst) A (Ctx.ref_insert_fst Γ.boxIn (.bnd 0) A B)) p)

/-- The second component, by the slot's `.snd` address. -/
def Proof.here_snd {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)} (hT : ModalSys.T = true)
    (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A B : VarType} {a : Ann A} {b : Ann B}
    (t₁ : Term σ Γ A a) (t₂ : Term σ Γ B b) {a' : Ann A} {b' : Ann B}
    (bd₁ : Term σ (Γ.diaIn x) A a') (bd₂ : Term σ (Γ.diaIn x) B b')
    (p : Proof σ Γ Δ (WFF.here hT
      (Term.diatm x hx (Term.pair bd₁ bd₂)) (Term.pair t₁ t₂))) :
    Proof σ Γ Δ (WFF.here hT (Term.diatm x hx bd₂) t₂) :=
  Proof.conv
    (WFF.here_congr hT (sig_diatm (Term.viewReadTm_eta_snd bd₁ bd₂))
      (Term.hereRead_eta_snd hT t₁ t₂))
    (Proof.here_beta hT x hx (Term.pair t₁ t₂) (Term.pair bd₁ bd₂)
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
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) :
    WFF.subst (Subst.renameTmIdx σ ι u u' (.VTypeDia A) hu'.root)
        (θ.renameTm u u' (.VTypeDia A) hu'.root)
        (Subst.ok_renameTm hθ (.VTypeDia A) hu'.root)
        (Subst.coh_renameTm hθ hc hu (.VTypeDia A) hu'.root)
        (hΓ.insertFree u (.VTypeDia A)) (hΔ.insertFree u' (.VTypeDia A))
        (WFF.hereAt hT (.root (.free u)) (Ctx.ref_insert_root Γ (.free u) (.VTypeDia A))
          (Term.weaken hu.root (.VTypeDia A) t) : WFF σ (Γ.insert (.free u) (.VTypeDia A)) 0) =
      WFF.hereAt hT (.root (.free u')) (Ctx.ref_insert_root Δ (.free u') (.VTypeDia A))
        (Term.weaken hu'.root (.VTypeDia A) (Term.subst ι θ hθ hc t)) :=
  WFF.here_congr hT
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

/-- ⭐Substituting the naming existential: the subject travels and the slot stays.  Both halves are
    known — the subject is weakened past the slot (`Term.subst_under_mono`), and the content is the
    slot's η-expansion, whose entry under `Subst.under` is a renaming (`Term.subst_eta_renAt`).
    This is what makes `Proof.here_name`'s conclusion survive substitution, and so why the rule is
    stated at an arbitrary body (§10.11). -/
theorem WFF.subst_hereEx {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (hT : ModalSys.T = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) {B : VarType} {b : Ann (.VTypeDia B)}
    (s : Term σ Γ (.VTypeDia B) b) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.hereEx hT s) = WFF.hereEx hT (Term.subst ι θ hθ hc s) := by
  refine congrArg (WFF.ex B) (WFF.here_congr hT (Term.subst_under_mono θ hθ hc hΓ hΔ B s) ?_)
  exact Term.subst_eta_renAt (θ.under 0 0 B hΔ.root) (Subst.ok_under hθ B hΔ.root)
    (Subst.coh_under hθ hc hΓ B hΔ.root) B (.root (.bnd 0)) (.root (.bnd 0))
    (Ctx.ref_insert_root Γ (.bnd 0) B) (Ctx.ref_insert_root Δ (.bnd 0) B)
    (by
      have hslot : (θ.under 0 0 B hΔ.root) (.root (.bnd 0)) = .ren (.root (.bnd 0)) := if_pos rfl
      exact hslot)

/-! ### Strong B: substituting what the `Back` rules read -/

/-- On the hole's context `Subst.under` renames every address to itself: the slot is all there
    is. -/
theorem Subst.under_hole_ren {Δ : Ctx} (θ : Subst σ Δ) {A : VarType}
    (h : Δ (.root (.bnd 0)) = none) :
    ∀ v T, (Ctx.empty.insert (.bnd 0) A).ref v = some T → (θ.under 0 0 A h).at v = .ren v :=
  Subst.at_ren_of fun v U _ hv => by
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      exact if_pos rfl
    · simp [Ctx.insert, hvr, Ctx.empty] at hv

/-- ⭐Substituting into a hole formula's reading substitutes into the term in its hole: the
    formula itself is closed apart from the hole, which `Subst.under` keeps. -/
theorem WFF.subst_holeRead {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.holeRead t ψ) = WFF.holeRead (Term.subst ι θ hθ hc t) ψ := by
  unfold WFF.holeRead
  rw [WFF.subst_instantiate θ hθ hc hΓ hΔ t,
    WFF.subst_mono (hΓ := (show Ctx.empty.SlotsFrom 0 from fun _ _ _ _ => rfl).insert A),
    WFF.subst_ren ((Ctx.empty_le Δ).insert (.bnd 0) A) _ _ _ _ _
      (Subst.under_hole_ren θ hΔ.root) ψ]

/-- ⭐The same for a hole term, as dependent pairs. -/
theorem Term.subst_holeRead_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.subst ι θ hθ hc (Term.holeRead t s)⟩ : Σ c, Term σ Δ B c) =
      ⟨_, Term.holeRead (Term.subst ι θ hθ hc t) s⟩ := by
  refine (Term.subst_single_tm_sig θ hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots t _).trans ?_
  refine sig_subst _ _ _ ?_
  rw [Term.subst_mono]
  exact Term.subst_ren ((Ctx.empty_le Δ).insert (.bnd 0) A) _ _ _
    (Subst.under_hole_ren θ (Ctx.NoSlots.slots (Γ := Δ)).root) s

theorem WFF.instantiate_congr_sig {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {T : VarType}
    {a a' : Ann T} {t : Term σ Γ T a} {t' : Term σ Γ T a'}
    (h : (⟨a, t⟩ : Σ b, Term σ Γ T b) = ⟨a', t'⟩) (φ : WFF σ (Γ.insert (.bnd d) T) (d + 1)) :
    WFF.instantiate hs t φ = WFF.instantiate hs t' φ := by
  cases h
  rfl

/-- A term of the doubled `□` view, read in a leg's `□` view, substitutes as itself. -/
theorem OutLeg.subst_mono_view {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
    (O : OutLeg Γ) → {A : VarType} → {a : Ann A} → (s : Term σ Γ.boxIn.boxIn A a) →
    (⟨_, Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
        (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) (Term.mono O.le_view.boxIn s)⟩ :
        Σ c, Term σ (O.subst θ hθ hc).view.boxIn A c) =
      ⟨_, Term.mono (O.subst θ hθ hc).le_view.boxIn
        (Term.subst ι θ.box.box (Subst.ok_box (Subst.ok_box hθ))
          (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc)) s)⟩
  | .nec, _, _, s => by
      change (⟨_, Term.subst ι θ.box.box _ _ (Term.mono (Ctx.Le.refl _).boxIn s)⟩ :
        Σ c, Term σ Δ.boxIn.boxIn _ c) = ⟨_, Term.mono (Ctx.Le.refl _).boxIn _⟩
      rw [Term.mono_refl, Term.mono_refl]
  | .pos y hy, _, _, s => by
      have hle := Ctx.le_boxIn_diaIn Δ (ι y)
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      have hs₁ : Subst.Sim Γ.boxIn (θ.dia y (ι y)) (θ.box.mono hle) := fun v T hv => by
        rw [Subst.dia_eq_box_mono θ y (ι y) v T hv, ← Subst.at_mono]
        exact .refl _
      refine (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ s)).trans ?_
      refine Eq.trans ?_ (congrArg (Sigma.mk _) (Term.mono_subst _ _ _ _ _)).symm
      refine (Term.subst_congr _ _ _ (Subst.ok_box (Subst.ok_mono (Subst.ok_box hθ) hle)) _
        (Subst.coh_box (Subst.ok_mono (Subst.ok_box hθ) hle)
          (Subst.coh_mono (Subst.coh_box hθ hc) hle)) (Subst.sim_box hs₁) s).trans ?_
      exact (Term.subst_congr _ _ _ _ _ _ (Subst.sim_box_mono θ.box hle) s).symm

/-- Substituting `back_here`'s conclusion: instantiation commutes with substitution, and so do the
    two collapses (`Term.collapse_subst`, twice). -/
theorem WFF.subst_backHere {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (hT : ModalSys.T = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) {A : VarType} {a₀ : Ann A}
    (bd : Term σ Γ.boxIn.boxIn A a₀) (φ : WFF σ (Γ.insert (.bnd 0) A) 1) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.instantiate Ctx.NoSlots.slots (Term.collapse
        (Ctx.collapses_boxIn_self hT Γ) (Term.collapse (Ctx.collapses_boxIn_self hT Γ.boxIn) bd))
        φ) =
      WFF.instantiate Ctx.NoSlots.slots (Term.collapse (Ctx.collapses_boxIn_self hT Δ)
        (Term.collapse (Ctx.collapses_boxIn_self hT Δ.boxIn)
          (Term.subst ι θ.box.box (Subst.ok_box (Subst.ok_box hθ))
            (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc)) bd)))
        (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 A hΔ.root) (Subst.ok_under hθ A hΔ.root)
          (Subst.coh_under hθ hc hΓ A hΔ.root) (hΓ.insert A) (hΔ.insert A) φ) := by
  rw [WFF.subst_instantiate θ hθ hc hΓ hΔ]
  refine WFF.instantiate_congr_sig _ ?_ _
  have hcol : ∀ {k : ℕ} {Δ₁ Δ₂ : Ctx} (D : Ctx.Collapses k Δ₁ Δ₂) {B : VarType} {b b' : Ann B}
      {u : Term σ Δ₁ B b} {u' : Term σ Δ₁ B b'},
      (⟨b, u⟩ : Σ c, Term σ Δ₁ B c) = ⟨b', u'⟩ →
        (⟨_, Term.collapse D u⟩ : Σ c, Term σ Δ₂ B c) = ⟨_, Term.collapse D u'⟩ := by
    intro k Δ₁ Δ₂ D B b b' u u' h
    cases h
    rfl
  refine (Term.collapse_subst (Ctx.collapses_boxIn_self hT Γ) (Ctx.collapses_boxIn_self hT Δ)
    θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ hc (Subst.corr_box_self hT hθ) _).symm.trans
    ?_
  exact hcol _ (Term.collapse_subst (Ctx.collapses_boxIn_self hT Γ.boxIn)
    (Ctx.collapses_boxIn_self hT Δ.boxIn) θ.box.box (Subst.ok_box (Subst.ok_box hθ))
    (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc)) θ.box (Subst.ok_box hθ)
    (Subst.coh_box hθ hc) (Subst.corr_box_self hT (Subst.ok_box hθ)) bd).symm

/-- A term of the `□` view's `□` view, weakened past the slot, substituted through `under` and
    `box`: the weakening of the term substituted through `box`.  Both sides are compared with
    `θ.mono`'s box, `Subst.Sim` not being transitive. -/
theorem Term.subst_box_under_mono {ι : VarSymb → VarSymb} {V W : Ctx} (θ : Subst σ W)
    (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) (hV : V.SlotsFrom 0) (hW : W.SlotsFrom 0)
    (T : VarType) {C : VarType} {c : Ann C} (bd : Term σ V.boxIn C c) :
    (⟨_, Term.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 T hW.root).box
        (Subst.ok_box (Subst.ok_under hθ T hW.root))
        (Subst.coh_box (Subst.ok_under hθ T hW.root) (Subst.coh_under hθ hc hV T hW.root))
        (Term.mono (Ctx.le_insert hV.root T).boxIn bd)⟩ :
        Σ b, Term σ (W.insert (.bnd 0) T).boxIn C b) =
      ⟨_, Term.mono (Ctx.le_insert hW.root T).boxIn
        (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) bd)⟩ := by
  have hsim : Subst.Sim V (θ.under 0 0 T hW.root) (θ.mono (Ctx.le_insert hW.root T)) := by
    refine Subst.sim_of fun v U _ hv => ?_
    have hne : v ≠ .root (.bnd 0) := fun hvr => by rw [hvr, hV.root] at hv; cases hv
    rw [show θ.under 0 0 T hW.root v = (θ v).mono (Ctx.le_insert hW.root T) from if_neg hne]
    exact .refl _
  rw [Term.subst_mono, Term.mono_subst]
  refine (Term.subst_congr _ ((θ.mono (Ctx.le_insert hW.root T)).box) _
    (Subst.ok_box (Subst.ok_mono hθ (Ctx.le_insert hW.root T))) _
    (Subst.coh_box (Subst.ok_mono hθ (Ctx.le_insert hW.root T))
      (Subst.coh_mono hc (Ctx.le_insert hW.root T))) (Subst.sim_box hsim) bd).trans ?_
  exact (Term.subst_congr _ _ _ _ _ _ (Subst.sim_box_mono θ (Ctx.le_insert hW.root T)) bd).symm

/-- Substituting the `Back` atom of `Proof.B_strong`: the eigenvariable's η-expansion goes to the
    new eigenvariable's, as in `WFF.subst_hereAt_renameTm`. -/
theorem WFF.subst_backEta_renameTm {ι : VarSymb → VarSymb} {Γ Δ : Ctx}
    (hS : ModalSys.BStrong = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) {u u' : ℕ} (hu : Γ.RootFresh (.free u))
    (hu' : Δ.RootFresh (.free u')) {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) :
    WFF.subst (Subst.renameTmIdx σ ι u u' (.VTypeBox (.VTypeBox A)) hu'.root)
        (θ.renameTm u u' (.VTypeBox (.VTypeBox A)) hu'.root)
        (Subst.ok_renameTm hθ (.VTypeBox (.VTypeBox A)) hu'.root)
        (Subst.coh_renameTm hθ hc hu (.VTypeBox (.VTypeBox A)) hu'.root)
        (hΓ.insertFree u (.VTypeBox (.VTypeBox A))) (hΔ.insertFree u' (.VTypeBox (.VTypeBox A)))
        (WFF.back hS .nec (Term.eta (.root (.free u)) _
            (Ctx.ref_insert_root Γ (.free u) (.VTypeBox (.VTypeBox A))))
          (Term.weaken hu.root _ t) : WFF σ (Γ.insert (.free u) (.VTypeBox (.VTypeBox A))) 0) =
      WFF.back hS .nec (Term.eta (.root (.free u')) _
          (Ctx.ref_insert_root Δ (.free u') (.VTypeBox (.VTypeBox A))))
        (Term.weaken hu'.root _ (Term.subst ι θ hθ hc t)) :=
  WFF.back_congr hS .nec
    (Term.subst_eta_tm _ _ _ (.VTypeBox (.VTypeBox A)) (.root (.free u))
      (Ctx.ref_insert_root Γ (.free u) (.VTypeBox (.VTypeBox A))) _
      (Subst.at_renameTm_root θ u u' (.VTypeBox (.VTypeBox A)) hu'.root))
    (Term.subst_mono_renameTm_sigma θ hθ hc hu hu' (.VTypeBox (.VTypeBox A)) t)

/-! ### Strong B: substituting what the returning possibility's rules read -/

/-- A renamed address's contents are renamed with it. -/
theorem Subst.box_at_inner_ren {Δ : Ctx} (θ : Subst σ Δ) {v w : VarSymb}
    (hs : θ.at v = .ren w) : θ.box.at v.inner = .ren w.inner := by
  by_cases hk : ModalSys.keepOnly = true
  · rw [VarSymb.inner_keepOnly hk, VarSymb.inner_keepOnly hk]
    change ((θ.at v).keepE).proj .here = _
    rw [hs]
    rfl
  · rw [VarSymb.inner_box (Bool.eq_false_iff.mpr hk)]
    change (θ.at v).unbox = _
    rw [hs]
    rfl

/-- The box components of a renamed necessary pair are renamed with it. -/
theorem Term.subst_boxFst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {v w : VarSymb} {A B : VarType}
    (hv : Γ.ref v = some (.VTypeBox (.VTypeProd A B)))
    (hw : Δ.ref w = some (.VTypeBox (.VTypeProd A B))) (hs : θ.at v = .ren w) :
    (⟨_, Term.subst ι θ hθ hc (Term.boxFst hv)⟩ : Σ b, Term σ Δ (.VTypeBox A) b) =
      ⟨_, Term.boxFst hw⟩ :=
  sig_boxtm (Term.subst_eta_renAt θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) A
    (.step v.inner .fst) (.step w.inner .fst) _ _ (by
      change (θ.box.at v.inner).proj .fst = _
      rw [Subst.box_at_inner_ren θ hs]
      rfl))

theorem Term.subst_boxSnd {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {v w : VarSymb} {A B : VarType}
    (hv : Γ.ref v = some (.VTypeBox (.VTypeProd A B)))
    (hw : Δ.ref w = some (.VTypeBox (.VTypeProd A B))) (hs : θ.at v = .ren w) :
    (⟨_, Term.subst ι θ hθ hc (Term.boxSnd hv)⟩ : Σ b, Term σ Δ (.VTypeBox B) b) =
      ⟨_, Term.boxSnd hw⟩ :=
  sig_boxtm (Term.subst_eta_renAt θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) B
    (.step v.inner .snd) (.step w.inner .snd) _ _ (by
      change (θ.box.at v.inner).proj .snd = _
      rw [Subst.box_at_inner_ren θ hs]
      rfl))

/-- A substitution read at a projection is its entry projected. -/
theorem Subst.at_proj {Δ : Ctx} (θ : Subst σ Δ) (v : VarSymb) {s : Step}
    (hs : s.isProj = true) : θ.at (.step v s) = (θ.at v).proj s := by
  change (if s.isProj then (θ.at v).proj s else θ (.step v s)) = _
  rw [if_pos hs]

/-- Weakening a hole term's reading is reading the weakened term. -/
theorem Term.mono_holeAt_sig {Γ Γ' : Ctx} (h : Γ.Le Γ') {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.mono h (Term.holeAt t s)⟩ : Σ c, Term σ Γ' B c) =
      ⟨_, Term.holeAt (Term.mono h t) s⟩ := by
  unfold Term.holeAt
  rw [Term.mono_subst]
  refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun v U _ hv => ?_) s
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    change SubE.Sim U (SubE.mono h (if (VarSymb.root (.bnd 0)) = .root (.bnd 0) then _ else _))
      (if (VarSymb.root (.bnd 0)) = .root (.bnd 0) then _ else _)
    rw [if_pos rfl, if_pos rfl]
    exact .refl _
  · simp [Ctx.insert, hvr, Ctx.empty] at hv

/-- Substituting under the slot leaves a closed hole term alone. -/
theorem Term.subst_under_closed {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {B T : VarType} {a : Ann T} (s : Term σ (Ctx.empty.insert (.bnd 0) B) T a) :
    (⟨_, Term.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 B hΔ.root)
        (Subst.ok_under hθ B hΔ.root) (Subst.coh_under hθ hc hΓ B hΔ.root)
        (Term.mono ((Ctx.empty_le Γ).insert (.bnd 0) B) s)⟩ :
      Σ b, Term σ (Δ.insert (.bnd 0) B) T b) =
      ⟨_, Term.mono ((Ctx.empty_le Δ).insert (.bnd 0) B) s⟩ := by
  rw [Term.subst_mono]
  refine Term.subst_ren _ _ _ _ (Subst.at_ren_of fun v U _ hv => ?_) s
  have hvr : v = .root (.bnd 0) := by
    by_contra hne
    simp [Ctx.insert, hne, Ctx.empty] at hv
  subst hvr
  exact if_pos rfl

theorem Subst.under_at_root {Δ : Ctx} (θ : Subst σ Δ) (T : VarType)
    (h : Δ (.root (.bnd 0)) = none) :
    (θ.under 0 0 T h).at (.root (.bnd 0)) = .ren (.root (.bnd 0)) := by
  change (θ.under 0 0 T h) (.root (.bnd 0)) = _
  exact if_pos rfl

/-- The same at any slot. -/
theorem Subst.under_at_slot {Δ : Ctx} (θ : Subst σ Δ) (d d' : ℕ) (T : VarType)
    (h : Δ (.root (.bnd d')) = none) :
    (θ.under d d' T h).at (.root (.bnd d)) = .ren (.root (.bnd d')) := by
  change (θ.under d d' T h) (.root (.bnd d)) = _
  exact if_pos rfl

/-- ⭐A hole formula read at any depth: substituting into the reading substitutes into the term in
    its hole.  One composition of substitutions. -/
theorem WFF.subst_holeAt {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.holeAt hΓ t ψ) = WFF.holeAt hΔ (Term.subst ι θ hθ hc t) ψ :=
  WFF.subst_comp (Subst.single (.bnd 0) (.tm t)) θ
    (Subst.single (.bnd 0) (.tm (Term.subst ι θ hθ hc t)))
    (Subst.ok_single (Ctx.empty_le Γ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl) hθ hc
    (Subst.ok_single (Ctx.empty_le Δ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Δ) rfl)
    (Ctx.slotsFrom_empty.insert A) hΓ hΔ
    (Subst.sim_of fun v U _ hv => by
      by_cases hvr : v = .root (.bnd 0)
      · subst hvr
        rw [Subst.comp_apply, Subst.single_root, Subst.single_root]
        exact .refl _
      · simp [Ctx.insert, hvr, Ctx.empty] at hv) ψ

/-- The same for a hole term, as dependent pairs. -/
theorem Term.subst_holeAt_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.subst ι θ hθ hc (Term.holeAt t s)⟩ : Σ c, Term σ Δ B c) =
      ⟨_, Term.holeAt (Term.subst ι θ hθ hc t) s⟩ :=
  Term.subst_comp_sig (Subst.single (.bnd 0) (.tm t)) θ
    (Subst.single (.bnd 0) (.tm (Term.subst ι θ hθ hc t)))
    (Subst.ok_single (Ctx.empty_le Γ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Γ) rfl) hθ hc
    (Subst.ok_single (Ctx.empty_le Δ) rfl)
    (Subst.coh_single (Ctx.RootFresh.empty _) (Ctx.empty_le Δ) rfl)
    (Subst.sim_of fun v U _ hv => by
      by_cases hvr : v = .root (.bnd 0)
      · subst hvr
        rw [Subst.comp_apply, Subst.single_root, Subst.single_root]
        exact .refl _
      · simp [Ctx.insert, hvr, Ctx.empty] at hv) s

theorem WFF.holeAt_congr {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {A : VarType} {a₁ a₂ : Ann A}
    {t₁ : Term σ Γ A a₁} {t₂ : Term σ Γ A a₂} (h : (⟨a₁, t₁⟩ : Σ b, Term σ Γ A b) = ⟨a₂, t₂⟩)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) : WFF.holeAt hs t₁ ψ = WFF.holeAt hs t₂ ψ := by
  cases h
  rfl

theorem VarSymb.inner_rt (u : VarSymb) : u.inner.rt = u.rt := by
  unfold VarSymb.inner
  split <;> rfl

/-- Substituting `ret_unit`'s new conjunct: its value is weakened past the outer slot
    (`Term.subst_under_mono`), and both components of its hole are slots' η-expansions, which the
    substitution renames to themselves (`Term.subst_eta_renAt`). -/
theorem WFF.subst_unitBody {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) (hS : ModalSys.BStrong = true) {C A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 (.VTypeBox C) hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
        (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) (WFF.unitBody hS sb ψ) =
      WFF.unitBody hS (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) ψ := by
  unfold WFF.unitBody
  refine WFF.ret_congr hS ?_ ?_
  · exact Term.subst_under_mono θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
      hΔ.boxIn _ sb
  · refine (WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ)
    refine sig_pair (Term.subst_eta_renAt _ _ _ C _ _ _ _ ?_)
      (Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_)
    · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.box_at_inner_ren _ (Subst.under_at_root _ _ _)]
      rfl
    · exact Subst.under_at_slot _ (0 + 1) (0 + 1) _ _

omit [ModalSys] in
/-- A slot's own address is fixed by shifting slots in place. -/
theorem VarSymb.shiftSlot_snd (ι : VarSymb → VarSymb) :
    VarSymb.shiftSlot ι 0 0 (.step (.root (.bnd 0)) .snd) = .step (.root (.bnd 0)) .snd :=
  if_pos rfl

/-- Substituting `◇_x φ` when the witness's image is known. -/
theorem WFF.subst_dia_at {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (φ : WFF σ (Γ.diaIn x) d)
    (z : VarSymb) (hz : ι x = z) (P : ∃ Y, Δ.ref z = some (.VTypeDia Y))
    (hz' : (Δ.diaIn z).SlotsFrom d') (p : Subst.Ok (Γ.diaIn x) (θ.dia x z))
    (q : Subst.Coh ι (Γ.diaIn x) (θ.dia x z)) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.dia x hx φ) =
      WFF.dia z P (WFF.subst ι (θ.dia x z) p q (hΓ.diaIn x) hz' φ) := by
  subst hz
  rfl

/-- In a witness view, an item's entry is the `□` view's, weakened. -/
theorem Subst.dia_at_inner_ren {Γ Δ : Ctx} (θ : Subst σ Δ) (x y : VarSymb) {v : VarSymb}
    {T : VarType} (hv : Γ.boxIn.ref v.inner = some T) (hs : θ.at v = .ren v) :
    (θ.dia x y).at v.inner = .ren v.inner := by
  rw [Subst.dia_eq_box_mono (Δ₁ := Γ) θ x y _ _ hv, Subst.box_at_inner_ren _ hs]
  rfl

/-- Substituting the counit's body of a possible part leaves it alone: both its holes are the
    slot's own addresses. -/
theorem WFF.subst_counitBodyD {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {C X : VarType}
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C X)) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        (θ.box.under 0 0 (RShape.wit (.box C) X).ty hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
        (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) (WFF.counitBodyD (Γ := Γ) ψ) =
      WFF.counitBodyD (Γ := Δ) ψ := by
  have hu := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ' := Subst.ok_under (d := 0) (Subst.ok_box hθ) (RShape.wit (.box C) X).ty
    hΔ.boxIn.root
  have hc' := Subst.coh_under (d := 0) (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
    (RShape.wit (.box C) X).ty hΔ.boxIn.root
  have hw : ((θ.box.under 0 0 _ hΔ.boxIn.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] =
      .step (.root (.bnd 0)) .snd := (hc' _ _ hsnd []).trans (VarSymb.shiftSlot_snd ι)
  unfold WFF.counitBodyD WFF.boxx
  change WFF.imp (WFF.subst _ _ _ _ _ _ (WFF.dia _ _ _)) WFF.bot = _
  rw [WFF.subst_dia_at _ _ _ _ _ _ _ _ _ (VarSymb.shiftSlot_snd ι) ⟨X, Ctx.ref_snd_of
      (Ctx.ref_insert_root Δ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty)⟩
    ((hΔ.boxIn.insert _).diaIn _) (Subst.ok_dia hθ' ⟨X, hsnd⟩ hw)
    (VarSymb.shiftSlot_snd ι ▸ Subst.coh_dia hθ' hc' ⟨X, hsnd⟩)]
  refine congrArg (fun φ => WFF.imp (WFF.dia _ _ (WFF.imp φ WFF.bot)) WFF.bot) ?_
  refine (WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ)
  refine sig_pair (Term.subst_eta_renAt _ _ _ C _ _ _ _ ?_)
    (Term.subst_eta_renAt _ _ _ X _ _ _ _ ?_)
  · exact Subst.dia_at_inner_ren _ _ _ (Ctx.ref_inner (Ctx.ref_fst_of hu))
      (by rw [Subst.at_proj _ _ rfl, Subst.under_at_root]; rfl)
  · rw [Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, Subst.under_at_root]
    rfl

theorem sig_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') {T : VarType} {a a' : Ann T} {t : Term σ Γ T a}
    {t' : Term σ Γ T a'} (e : (⟨a, t⟩ : Σ b, Term σ Γ T b) = ⟨a', t'⟩) :
    (⟨_, Term.mono h t⟩ : Σ b, Term σ Γ' T b) = ⟨_, Term.mono h t'⟩ := by
  cases e
  rfl

theorem sig_collapse {k : ℕ} {Γ₁ Γ₂ : Ctx} (hk : Ctx.Collapses k Γ₁ Γ₂) {A : VarType}
    {a a' : Ann A} {t : Term σ Γ₁ A a} {t' : Term σ Γ₁ A a'}
    (h : (⟨a, t⟩ : Σ b, Term σ Γ₁ A b) = ⟨a', t'⟩) :
    (⟨_, Term.collapse hk t⟩ : Σ b, Term σ Γ₂ A b) = ⟨_, Term.collapse hk t'⟩ := by
  cases h
  rfl

/-- Substituting the contents of a necessary term is taking the contents of its substitute. -/
theorem Term.subst_unboxtm_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {A : VarType} {a : Ann (.VTypeBox A)}
    (x : Term σ Γ (.VTypeBox A) a) :
    (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) (Term.unboxtm x).2⟩ :
        Σ b, Term σ Δ.boxIn A b) = ⟨_, (Term.unboxtm (Term.subst ι θ hθ hc x)).2⟩ := by
  cases x with
  | boxtm t => rfl

theorem sig_unboxtm {Γ : Ctx} {A : VarType} {a a' : Ann (.VTypeBox A)}
    {x : Term σ Γ (.VTypeBox A) a} {x' : Term σ Γ (.VTypeBox A) a'}
    (h : (⟨a, x⟩ : Σ b, Term σ Γ (.VTypeBox A) b) = ⟨a', x'⟩) :
    (⟨_, (Term.unboxtm x).2⟩ : Σ b, Term σ Γ.boxIn A b) = ⟨_, (Term.unboxtm x').2⟩ := by
  cases h
  rfl

/-- Substituting a companion's contents is taking the substitute's. -/
theorem subst_compVal_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (p : List Step) {ps : List (List Step)}
    (h : A.CompOk (p :: ps)) :
    (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) (compVal sb p h).2⟩ :
        Σ b, Term σ Δ.boxIn ((A.compAt p).getD .VTypeOne) b) =
      ⟨_, (compVal (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) p h).2⟩ :=
  (Term.subst_unboxtm_sig θ hθ hc _).trans
    (sig_unboxtm (Term.subst_holeAt_sig θ hθ hc (Term.boxtm sb) _))

/-- Substituting the values of `□sb` and its companions is taking the substitute's. -/
theorem subst_compsVal_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) : (cs : List (List Step)) → (h : A.CompOk cs) →
    (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) (compsVal sb cs h).2⟩ :
        Σ b, Term σ Δ.boxIn (A.compsFlat cs) b) =
      ⟨_, (compsVal (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) cs h).2⟩
  | [], _ => rfl
  | p :: ps, h => sig_pair (subst_compsVal_sig θ hθ hc sb ps h.tail)
      (subst_compVal_sig θ hθ hc sb p h)

omit [ModalSys] in
/-- A companion path is made of projections. -/
theorem VarType.compAt_isProj : ∀ (A : VarType) (p : List Step), (A.compAt p).isSome = true →
    ∀ s ∈ p, s.isProj = true
  | _, [], _, _, hs => absurd hs List.not_mem_nil
  | A, t :: p, h, s, hs => by
      cases A <;> cases t <;> simp only [VarType.compAt, Option.isSome_none,
        Bool.false_eq_true] at h
      all_goals
        rcases List.mem_cons.mp hs with rfl | hs
        · rfl
        · exact VarType.compAt_isProj _ p h s hs

/-- A substitution renaming an address renames its extensions by projections alike. -/
theorem Subst.at_ext_ren {Δ : Ctx} (θ : Subst σ Δ) : ∀ (q : List Step) {u u' : VarSymb},
    θ.at u = .ren u' → (∀ s ∈ q, s.isProj = true) → θ.at (u.ext q) = .ren (u'.ext q)
  | [], _, _, h, _ => h
  | s :: q, u, u', h, hq => Subst.at_ext_ren θ q
      (by rw [Subst.at_proj θ u (hq s List.mem_cons_self), h]; rfl)
      (fun s' hs' => hq s' (List.mem_cons_of_mem _ hs'))

/-- Substituting a value with companions read at a slot that the substitution fixes. -/
theorem Term.subst_compsSlot {ι : VarSymb → VarSymb} {Δ₀ Δ₀' Δ₁ Δ₂ : Ctx} {u₁ u₂ : VarSymb}
    {C : VarType} (hu₁ : Δ₀.ref u₁ = some (.VTypeBox C)) (hle₁ : Δ₀.boxIn.Le Δ₁)
    (hu₂ : Δ₀'.ref u₂ = some (.VTypeBox C)) (hle₂ : Δ₀'.boxIn.Le Δ₂) (θ : Subst σ Δ₂)
    (hθ : Subst.Ok Δ₁ θ) (hc : Subst.Coh ι Δ₁ θ)
    (hat : ∀ (q : List Step) (C' : VarType), (∀ s ∈ q, s.isProj = true) →
      Δ₀.ref (u₁.ext q) = some (.VTypeBox C') → θ.at (u₁.ext q).inner = .ren (u₂.ext q).inner) :
    ∀ (cs : List (List Step)) (h : C.CompOk cs),
      (⟨_, Term.subst ι θ hθ hc (compsSlot hu₁ hle₁ cs h).2⟩ :
        Σ a, Term σ Δ₂ (C.compsFlat cs) a) = compsSlot hu₂ hle₂ cs h
  | [], _ => Term.subst_eta_renAt _ _ _ C _ _ _ _
      (hat [] C (fun _ hs => absurd hs List.not_mem_nil) hu₁)
  | p :: ps, h => by
      have hp := (h.resolve_left (List.cons_ne_nil _ _)).2.1 p List.mem_cons_self
      exact sig_pair (Term.subst_compsSlot hu₁ hle₁ hu₂ hle₂ θ hθ hc hat ps h.tail)
        (Term.subst_eta_renAt _ _ _ _ _ _ _ _ (hat (.here :: p) _ (by
          intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · rfl
          · exact VarType.compAt_isProj C p hp s hs) (h.ref_head hu₁)))

/-- Substituting `ret_unit`'s conjunct with companions (`subst_unitBody` at `cs`). -/
theorem WFF.subst_unitBodyC {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) (hS : ModalSys.BStrong = true) {C A : VarType}
    (co : List (List Step)) (ho : C.CompOk co) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (h : A.CompOk cs)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (C.compsFlat co) (.VTypeBox A))) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 (.VTypeBox C) hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
        (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) (WFF.unitBodyC hS co ho sb cs h ψ) =
      WFF.unitBodyC hS co ho (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) cs h
        ψ := by
  unfold WFF.unitBodyC
  refine WFF.retS_congr hS _ ?_ ?_
  · exact (Term.subst_under_mono θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
      hΔ.boxIn _ _).trans (sig_mono _ (subst_compsVal_sig θ hθ hc sb cs h))
  · refine (WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ)
    refine sig_pair (Term.subst_compsSlot _ _ _ _ _ _ _ (fun q _ hq _ => ?_) co ho)
      (Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_)
    · rw [Subst.at_under_ne _ _ _ (by
          rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
        Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q (Subst.under_at_root _ _ _) hq)]
      rfl
    · exact Subst.under_at_slot _ (0 + 1) (0 + 1) _ _

/-- Substituting a `□`-view term moved into a witness view: the witness view sends the `□` view's
    addresses as the `□` view does (`Subst.dia_eq_box_mono`). -/
theorem Term.subst_diaIn_mono {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (x z : VarSymb)
    (hθd : Subst.Ok (Γ.diaIn x) (θ.dia x z)) (hcd : Subst.Coh ι (Γ.diaIn x) (θ.dia x z))
    {A : VarType} {a : Ann A} (sb : Term σ Γ.boxIn A a) :
    (⟨_, Term.subst ι (θ.dia x z) hθd hcd (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb)⟩ :
        Σ b, Term σ (Δ.diaIn z) A b) =
      ⟨_, Term.mono (Ctx.le_boxIn_diaIn Δ z)
        (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb)⟩ := by
  rw [Term.subst_mono, Term.mono_subst]
  exact Term.subst_congr _ _ _ _ _ _ (fun v T hv => by
    rw [Subst.dia_eq_box_mono θ x z v T hv, Subst.at_mono]
    exact .refl _) sb

/-- ⭐**A kept possible object substitutes as itself**: the kept witness goes to the image's
    (`Subst.coh_keep_dia`), and the shifted body across the shift (`Subst.shiftCorr_dia_keep`). -/
theorem Term.subst_keptDia {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (hF : ModalSys.Four = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = ι x)
    (hy : ∃ X, Δ.ref (ι x) = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (bd : Term σ (Γ.diaIn x) A a) :
    (⟨_, Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) (Term.keptDia hF hx bd).2⟩ :
        Σ b, Term σ Δ.boxIn (.VTypeDia A) b) =
      Term.keptDia hF hy
        (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) := by
  have hk₂ : ι (.step x .keep) = .step (ι x) .keep :=
    hx.elim fun _ hX => Subst.coh_keep_dia hθ hc hX
  have hwk : (θ.box.at (.step x .keep)).idxAlong [] = .step (ι x) .keep :=
    hx.elim fun _ hX => Subst.idx_box_keep_dia hF hθ hc hX
  have hθk := Subst.ok_dia (Subst.ok_box hθ) (Ctx.exists_keep_dia hF hx) hwk
  have hck := hk₂ ▸ Subst.coh_dia (Subst.ok_box hθ) (Subst.coh_box hθ hc)
    (Ctx.exists_keep_dia hF hx)
  refine (Term.subst_diatm_sig θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
    (Ctx.exists_keep_dia hF hx) _ hk₂ hwk hθk hck (Ctx.exists_keep_dia hF hy)).trans ?_
  exact sig_diatm (Term.shift_subst (Ctx.shifts_diaIn_keep hF Γ x)
    (Ctx.shifts_diaIn_keep hF Δ (ι x)) (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw)
    (Subst.coh_dia hθ hc hx) _ hθk hck (Subst.shiftCorr_dia_keep hF hθ hx hw) bd).symm

/-- ⭐**Substituting `here_keep`'s formula** gives its instance at the witness's image and the
    substituted body: the subject goes as the `□` view does (`Term.subst_diaIn_mono`), the kept
    witness to the image's (`Subst.coh_keep_dia`), and the shifted body across the shift
    (`Subst.shiftCorr_dia_keep`), as for `four_dia`. -/
theorem WFF.subst_hereKeep {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (hT : ModalSys.T = true) (hF : ModalSys.Four = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = ι x)
    (hy : ∃ X, Δ.ref (ι x) = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (bd : Term σ (Γ.diaIn x) A a) :
    WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots (WFF.hereKeep hT hF x hx bd) =
      WFF.hereKeep hT hF (ι x) hy
        (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) := by
  refine congrArg WFF.neg ((WFF.subst_dia θ hθ hc hΓ Ctx.NoSlots.slots hx (ι x) rfl hy
    (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) Ctx.NoSlots.slots _).trans ?_)
  refine congrArg (fun χ => WFF.dia (ι x) hy (WFF.neg χ)) (WFF.here_congr hT ?_ rfl)
  refine (Term.subst_diaIn_mono θ hθ hc x (ι x) _ _ _).trans (sig_mono _ ?_)
  exact Term.subst_keptDia hF θ hθ hc hx hw hy bd

/-- Substituting the witnessed unit's body: the necessary object goes as the `□` view does, the
    witness's content as the witness view does, and the hole reads slots only. -/
theorem WFF.subst_unitBodyW {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hS : ModalSys.BStrong = true) {x z : VarSymb} (hθd : Subst.Ok (Γ.diaIn x) (θ.dia x z))
    (hcd : Subst.Coh ι (Γ.diaIn x) (θ.dia x z)) (hsz : (Δ.diaIn z).SlotsFrom 0)
    {C A X : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty)) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0) ((θ.dia x z).under 0 0 (.VTypeBox C) hsz.root)
        (Subst.ok_under hθd _ hsz.root) (Subst.coh_under hθd hcd (hΓ.diaIn x) _ hsz.root)
        ((hΓ.diaIn x).insert _) (hsz.insert _) (WFF.unitBodyW hS sb u ψ) =
      WFF.unitBodyW (x := z) hS (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb)
        (Term.subst ι (θ.dia x z) hθd hcd u) ψ := by
  unfold WFF.unitBodyW
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
  · rw [← Term.mono_mono (Ctx.le_boxIn_diaIn Γ x) (Ctx.le_insert (hΓ.diaIn x).root _),
      ← Term.mono_mono (Ctx.le_boxIn_diaIn Δ z) (Ctx.le_insert hsz.root _)]
    refine (Term.subst_under_mono (θ.dia x z) hθd hcd (hΓ.diaIn x) hsz _ _).trans ?_
    exact sig_mono _ (Term.subst_diaIn_mono θ hθ hc x z hθd hcd sb)
  · exact Term.subst_under_mono (θ.dia x z) hθd hcd (hΓ.diaIn x) hsz _ u
  · refine (WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ)
    refine sig_pair (Term.subst_eta_renAt _ _ _ C _ _ _ _ ?_)
      (Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_)
    · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.box_at_inner_ren _ (Subst.under_at_root _ _ _)]
      rfl
    · exact Subst.under_at_slot _ (0 + 1) (0 + 1) _ _

/-- Substituting the witnessed unit's body: the necessary object goes as the `□` view does, the
    witness's content as the witness view does, and the hole reads slots only. -/
theorem WFF.subst_unitBodyWC {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hS : ModalSys.BStrong = true) {x z : VarSymb} (hθd : Subst.Ok (Γ.diaIn x) (θ.dia x z))
    (hcd : Subst.Coh ι (Γ.diaIn x) (θ.dia x z)) (hsz : (Δ.diaIn z).SlotsFrom 0)
    {C A X : VarType} (co : List (List Step)) (ho : C.CompOk co) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (cs : List (List Step)) (h : A.CompOk cs)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty)) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0) ((θ.dia x z).under 0 0 (.VTypeBox C) hsz.root)
        (Subst.ok_under hθd _ hsz.root) (Subst.coh_under hθd hcd (hΓ.diaIn x) _ hsz.root)
        ((hΓ.diaIn x).insert _) (hsz.insert _) (WFF.unitBodyWC hS co ho sb u cs h ψ) =
      WFF.unitBodyWC (x := z) hS co ho
        (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb)
        (Term.subst ι (θ.dia x z) hθd hcd u) cs h ψ := by
  unfold WFF.unitBodyWC
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
  · rw [← Term.mono_mono (Ctx.le_boxIn_diaIn Γ x) (Ctx.le_insert (hΓ.diaIn x).root _),
      ← Term.mono_mono (Ctx.le_boxIn_diaIn Δ z) (Ctx.le_insert hsz.root _)]
    refine (Term.subst_under_mono (θ.dia x z) hθd hcd (hΓ.diaIn x) hsz _ _).trans ?_
    exact (sig_mono _ (Term.subst_diaIn_mono θ hθ hc x z hθd hcd _)).trans
      (sig_mono _ (sig_mono _ (subst_compsVal_sig θ hθ hc sb cs h)))
  · exact Term.subst_under_mono (θ.dia x z) hθd hcd (hΓ.diaIn x) hsz _ u
  · refine (WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ)
    refine sig_pair (Term.subst_compsSlot _ _ _ _ _ _ _ (fun q _ hq _ => ?_) co ho)
      (Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_)
    · rw [Subst.at_under_ne _ _ _ (by
          rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
        Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q (Subst.under_at_root _ _ _) hq)]
      rfl
    · exact Subst.under_at_slot _ (0 + 1) (0 + 1) _ _

/-- Substituting a returning possibility along a witness whose image is known. -/
theorem WFF.subst_retxS_at {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hB : ModalSys.BStrong = true) (y : VarSymb) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y))
    (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Φ : WFF σ ((Γ.diaIn y).insert (.bnd d) S.ty) (d + 1))
    (z : VarSymb) (hz : ι y = z) (P : ∃ Y, Δ.ref z = some (.VTypeDia Y))
    (hz' : (Δ.diaIn z).SlotsFrom d') (p : Subst.Ok (Γ.diaIn y) (θ.dia y z))
    (q : Subst.Coh ι (Γ.diaIn y) (θ.dia y z)) :
    WFF.subst ι θ hθ hc hΓ hΔ (WFF.retxS hB y hy S t Φ) =
      WFF.retxS hB z P S (Term.subst ι θ hθ hc t)
        (WFF.subst (VarSymb.shiftSlot ι d d') ((θ.dia y z).under d d' _ hz'.root)
          (Subst.ok_under p _ hz'.root) (Subst.coh_under p q (hΓ.diaIn y) _ hz'.root)
          ((hΓ.diaIn y).insert _) (hz'.insert _) Φ) := by
  subst hz
  rfl

/-- Substituting the unit's body along a returned possible part: the returning possibility is
    along the slot's own possible part, which substitution fixes. -/
theorem WFF.subst_unitBodyD {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) (hS : ModalSys.BStrong = true) {C X A : VarType} {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd C X) (.VTypeBox A))) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        (θ.box.under 0 0 (RShape.wit (.box C) X).ty hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
        (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) (WFF.unitBodyD hS sb ψ) =
      WFF.unitBodyD hS (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) ψ := by
  have hu := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ' := Subst.ok_under (d := 0) (Subst.ok_box hθ) (RShape.wit (.box C) X).ty
    hΔ.boxIn.root
  have hc' := Subst.coh_under (d := 0) (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
    (RShape.wit (.box C) X).ty hΔ.boxIn.root
  have hw : ((θ.box.under 0 0 _ hΔ.boxIn.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] =
      .step (.root (.bnd 0)) .snd := (hc' _ _ hsnd []).trans (VarSymb.shiftSlot_snd ι)
  unfold WFF.unitBodyD
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ _ (VarSymb.shiftSlot_snd ι) ⟨X, Ctx.ref_snd_of
      (Ctx.ref_insert_root Δ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty)⟩
    ((hΔ.boxIn.insert _).diaIn _) (Subst.ok_dia hθ' ⟨X, hsnd⟩ hw)
    (VarSymb.shiftSlot_snd ι ▸ Subst.coh_dia hθ' hc' ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _
    (Term.subst_under_mono θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn _ sb)
    ((WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ))
  refine sig_pair (sig_pair (Term.subst_eta_renAt _ _ _ C _ _ _ _ ?_)
    (Term.subst_eta_renAt _ _ _ X _ _ _ _ ?_)) (Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_)
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.dia_at_inner_ren _ _ _ (Ctx.ref_inner (Ctx.ref_fst_of hu))
        (by rw [Subst.at_proj _ _ rfl, Subst.under_at_root]; rfl)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, Subst.under_at_root]
    rfl
  · exact Subst.under_at_slot _ (0 + 1) (0 + 1) _ _

/-- Substituting the unit's body along a returned possible part: the returning possibility is
    along the slot's own possible part, which substitution fixes. -/
theorem WFF.subst_unitBodyDC {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) (hS : ModalSys.BStrong = true) {C X A : VarType}
    (co : List (List Step)) (ho : C.CompOk co) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (h : A.CompOk cs)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A))) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        (θ.box.under 0 0 (RShape.wit (.box C) X).ty hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
        (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) (WFF.unitBodyDC hS co ho sb cs h ψ) =
      WFF.unitBodyDC hS co ho (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) cs h
        ψ := by
  have hu := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ' := Subst.ok_under (d := 0) (Subst.ok_box hθ) (RShape.wit (.box C) X).ty
    hΔ.boxIn.root
  have hc' := Subst.coh_under (d := 0) (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
    (RShape.wit (.box C) X).ty hΔ.boxIn.root
  have hw : ((θ.box.under 0 0 _ hΔ.boxIn.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] =
      .step (.root (.bnd 0)) .snd := (hc' _ _ hsnd []).trans (VarSymb.shiftSlot_snd ι)
  unfold WFF.unitBodyDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ _ (VarSymb.shiftSlot_snd ι) ⟨X, Ctx.ref_snd_of
      (Ctx.ref_insert_root Δ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty)⟩
    ((hΔ.boxIn.insert _).diaIn _) (Subst.ok_dia hθ' ⟨X, hsnd⟩ hw)
    (VarSymb.shiftSlot_snd ι ▸ Subst.coh_dia hθ' hc' ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _
    ((Term.subst_under_mono θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn
      _ _).trans
      (sig_mono _ (subst_compsVal_sig θ hθ hc sb cs h)))
    ((WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ))
  refine sig_pair (sig_pair
    (Term.subst_compsSlot _ _ _ _ _ _ _ (fun q _ hq hr => ?_) co ho)
    (Term.subst_eta_renAt _ _ _ X _ _ _ _ ?_)) (Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_)
  · rw [Subst.at_under_ne _ _ _ (by
        rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
      Subst.dia_at_inner_ren _ _ _ (Ctx.ref_inner hr)
        (Subst.at_ext_ren _ q (by rw [Subst.at_proj _ _ rfl, Subst.under_at_root]; rfl) hq)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, Subst.under_at_root]
    rfl
  · exact Subst.under_at_slot _ (0 + 1) (0 + 1) _ _

/-- Substituting the doubly witnessed unit's body: along the slot's own possible part, which
    substitution fixes; the value as in the witnessed unit's. -/
theorem WFF.subst_unitBodyWD {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hS : ModalSys.BStrong = true) {x z : VarSymb} (hθd : Subst.Ok (Γ.diaIn x) (θ.dia x z))
    (hcd : Subst.Coh ι (Γ.diaIn x) (θ.dia x z)) (hsz : (Δ.diaIn z).SlotsFrom 0)
    {C Xe A X : VarType} {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty)) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        ((θ.dia x z).under 0 0 (RShape.wit (.box C) Xe).ty hsz.root)
        (Subst.ok_under hθd _ hsz.root) (Subst.coh_under hθd hcd (hΓ.diaIn x) _ hsz.root)
        ((hΓ.diaIn x).insert _) (hsz.insert _) (WFF.unitBodyWD hS sb u ψ) =
      WFF.unitBodyWD (x := z) hS (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb)
        (Term.subst ι (θ.dia x z) hθd hcd u) ψ := by
  have hu := Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) (RShape.wit (.box C) Xe).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ' := Subst.ok_under (d := 0) hθd (RShape.wit (.box C) Xe).ty hsz.root
  have hc' := Subst.coh_under (d := 0) hθd hcd (hΓ.diaIn x) (RShape.wit (.box C) Xe).ty
    hsz.root
  have hw : (((θ.dia x z).under 0 0 _ hsz.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] =
      .step (.root (.bnd 0)) .snd := (hc' _ _ hsnd []).trans (VarSymb.shiftSlot_snd ι)
  unfold WFF.unitBodyWD
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ _ (VarSymb.shiftSlot_snd ι) ⟨Xe, Ctx.ref_snd_of
      (Ctx.ref_insert_root (Δ.diaIn z) (.bnd 0) (RShape.wit (.box C) Xe).ty)⟩
    ((hsz.insert _).diaIn _) (Subst.ok_dia hθ' ⟨Xe, hsnd⟩ hw)
    (VarSymb.shiftSlot_snd ι ▸ Subst.coh_dia hθ' hc' ⟨Xe, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ ?_)
    ((WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ))
  · rw [← Term.mono_mono (Ctx.le_boxIn_diaIn Γ x) (Ctx.le_insert (hΓ.diaIn x).root _),
      ← Term.mono_mono (Ctx.le_boxIn_diaIn Δ z) (Ctx.le_insert hsz.root _)]
    refine (Term.subst_under_mono (θ.dia x z) hθd hcd (hΓ.diaIn x) hsz _ _).trans ?_
    exact sig_mono _ (Term.subst_diaIn_mono θ hθ hc x z hθd hcd sb)
  · exact Term.subst_under_mono (θ.dia x z) hθd hcd (hΓ.diaIn x) hsz _ u
  refine sig_pair (sig_pair (Term.subst_eta_renAt _ _ _ C _ _ _ _ ?_)
    (Term.subst_eta_renAt _ _ _ Xe _ _ _ _ ?_)) (Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_)
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.dia_at_inner_ren _ _ _ (Ctx.ref_inner (Ctx.ref_fst_of hu))
        (by rw [Subst.at_proj _ _ rfl, Subst.under_at_root]; rfl)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, Subst.under_at_root]
    rfl
  · exact Subst.under_at_slot _ (0 + 1) (0 + 1) _ _

/-- Substituting the doubly witnessed unit's body: along the slot's own possible part, which
    substitution fixes; the value as in the witnessed unit's. -/
theorem WFF.subst_unitBodyWDC {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hS : ModalSys.BStrong = true) {x z : VarSymb} (hθd : Subst.Ok (Γ.diaIn x) (θ.dia x z))
    (hcd : Subst.Coh ι (Γ.diaIn x) (θ.dia x z)) (hsz : (Δ.diaIn z).SlotsFrom 0)
    {C Xe A X : VarType} (co : List (List Step)) (ho : C.CompOk co) {a₀ : Ann A}
    (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (cs : List (List Step)) (h : A.CompOk cs)
    (ψ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) Xe) (RShape.wit (.box A) X).ty)) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        ((θ.dia x z).under 0 0 (RShape.wit (.box C) Xe).ty hsz.root)
        (Subst.ok_under hθd _ hsz.root) (Subst.coh_under hθd hcd (hΓ.diaIn x) _ hsz.root)
        ((hΓ.diaIn x).insert _) (hsz.insert _) (WFF.unitBodyWDC hS co ho sb u cs h ψ) =
      WFF.unitBodyWDC (x := z) hS co ho
        (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb)
        (Term.subst ι (θ.dia x z) hθd hcd u) cs h ψ := by
  have hu := Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) (RShape.wit (.box C) Xe).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ' := Subst.ok_under (d := 0) hθd (RShape.wit (.box C) Xe).ty hsz.root
  have hc' := Subst.coh_under (d := 0) hθd hcd (hΓ.diaIn x) (RShape.wit (.box C) Xe).ty
    hsz.root
  have hw : (((θ.dia x z).under 0 0 _ hsz.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] =
      .step (.root (.bnd 0)) .snd := (hc' _ _ hsnd []).trans (VarSymb.shiftSlot_snd ι)
  unfold WFF.unitBodyWDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ _ (VarSymb.shiftSlot_snd ι) ⟨Xe, Ctx.ref_snd_of
      (Ctx.ref_insert_root (Δ.diaIn z) (.bnd 0) (RShape.wit (.box C) Xe).ty)⟩
    ((hsz.insert _).diaIn _) (Subst.ok_dia hθ' ⟨Xe, hsnd⟩ hw)
    (VarSymb.shiftSlot_snd ι ▸ Subst.coh_dia hθ' hc' ⟨Xe, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ ?_)
    ((WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ))
  · rw [← Term.mono_mono (Ctx.le_boxIn_diaIn Γ x) (Ctx.le_insert (hΓ.diaIn x).root _),
      ← Term.mono_mono (Ctx.le_boxIn_diaIn Δ z) (Ctx.le_insert hsz.root _)]
    refine (Term.subst_under_mono (θ.dia x z) hθd hcd (hΓ.diaIn x) hsz _ _).trans ?_
    exact (sig_mono _ (Term.subst_diaIn_mono θ hθ hc x z hθd hcd _)).trans
      (sig_mono _ (sig_mono _ (subst_compsVal_sig θ hθ hc sb cs h)))
  · exact Term.subst_under_mono (θ.dia x z) hθd hcd (hΓ.diaIn x) hsz _ u
  refine sig_pair (sig_pair
    (Term.subst_compsSlot _ _ _ _ _ _ _ (fun q _ hq hr => ?_) co ho)
    (Term.subst_eta_renAt _ _ _ Xe _ _ _ _ ?_)) (Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_)
  · rw [Subst.at_under_ne _ _ _ (by
        rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
      Subst.dia_at_inner_ren _ _ _ (Ctx.ref_inner hr)
        (Subst.at_ext_ren _ q (by rw [Subst.at_proj _ _ rfl, Subst.under_at_root]; rfl) hq)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, Subst.under_at_root]
    rfl
  · exact Subst.under_at_slot _ (0 + 1) (0 + 1) _ _

theorem Term.holeRead_congr_sig {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a a' : Ann A}
    {x : Term σ Γ A a} {y : Term σ Γ A a'} (h : (⟨a, x⟩ : Σ b, Term σ Γ A b) = ⟨a', y⟩)
    {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.holeRead x s⟩ : Σ c, Term σ Γ B c) = ⟨_, Term.holeRead y s⟩ := by
  cases h
  rfl

/-- Substituting the companion step's value substitutes its parts. -/
theorem RShape.subst_extTm_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (S : RShape) {B : VarType}
    {a : Ann S.flat} (t : Term σ Γ S.flat a) {b : Ann B} (u : Term σ Γ B b) {a' : Ann S.flat}
    {t' : Term σ Δ S.flat a'} {b' : Ann B} {u' : Term σ Δ B b'}
    (ht : (⟨_, Term.subst ι θ hθ hc t⟩ : Σ c, Term σ Δ S.flat c) = ⟨a', t'⟩)
    (hu : (⟨_, Term.subst ι θ hθ hc u⟩ : Σ c, Term σ Δ B c) = ⟨b', u'⟩) :
    (⟨_, Term.subst ι θ hθ hc (S.extTm t u).2⟩ : Σ c, Term σ Δ (S.ext B).flat c) =
      ⟨_, (S.extTm t' u').2⟩ := by
  cases S with
  | nec N => exact sig_pair ht hu
  | wit N X =>
      exact (Term.subst_holeRead_sig θ hθ hc _ _).trans
        (Term.holeRead_congr_sig (sig_pair ht hu) _)

/-- Substituting under the slot leaves the companion step's object term alone. -/
theorem RShape.subst_extL {ι : VarSymb → VarSymb} {V W : Ctx} [V.NoSlots] [W.NoSlots]
    (θ : Subst σ W) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) (S : RShape) (B : VarType) :
    (⟨_, Term.subst (VarSymb.shiftSlot ι 0 0)
        (θ.under 0 0 (S.ext B).ty (Ctx.NoSlots.slots (Γ := W)).root)
        (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _) (S.extL V B).2⟩ :
        Σ a, Term σ (W.insert (.bnd 0) (S.ext B).ty) S.ty a) = ⟨_, (S.extL W B).2⟩ := by
  cases S with
  | nec N =>
      exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by
        rw [Subst.at_proj _ _ rfl, Subst.under_at_root]
        rfl)
  | wit N X =>
      exact sig_pair
        (Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by
          rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, Subst.under_at_root]
          rfl))
        (Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by
          rw [Subst.at_proj _ _ rfl, Subst.under_at_root]
          rfl))

/-- Substituting under the slot leaves `ret_realise`'s reading of the necessary part alone. -/
theorem RShape.subst_realL {ι : VarSymb → VarSymb} {V W : Ctx} [V.NoSlots] [W.NoSlots]
    (θ : Subst σ W) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) (N : NShape) (X : VarType) :
    (⟨_, Term.subst (VarSymb.shiftSlot ι 0 0)
        (θ.under 0 0 (RShape.wit N X).ty (Ctx.NoSlots.slots (Γ := W)).root)
        (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _)
        (RShape.realL V N X).2⟩ :
        Σ a, Term σ (W.insert (.bnd 0) (RShape.wit N X).ty) N.ty a) =
      ⟨_, (RShape.realL W N X).2⟩ :=
  Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by
    rw [Subst.at_proj _ _ rfl, Subst.under_at_root]
    rfl)

/-- A term of the `□` view, read in a leg's view, substitutes as itself. -/
theorem OutLeg.subst_mono_le_view {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
    (O : OutLeg Γ) → {A : VarType} → {a : Ann A} → (s : Term σ Γ.boxIn A a) →
    (⟨_, Term.subst ι (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)
        (Term.mono O.le_view s)⟩ : Σ c, Term σ (O.subst θ hθ hc).view A c) =
      ⟨_, Term.mono (O.subst θ hθ hc).le_view
        (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) s)⟩
  | .nec, _, _, s => by
      change (⟨_, Term.subst ι θ.box _ _ (Term.mono (Ctx.Le.refl _) s)⟩ :
        Σ c, Term σ Δ.boxIn _ c) = ⟨_, Term.mono (Ctx.Le.refl _) _⟩
      rw [Term.mono_refl, Term.mono_refl]
  | .pos y _, _, _, s => Term.subst_diaIn_mono θ hθ hc y (ι y) _ _ s

/-- Substituting under the slot sends `ret_keep`'s reading of the slot to the instance at the
    substituted content. -/
theorem RShape.subst_keepL {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (hF : ModalSys.Four = true) (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (O : OutLeg Γ) (N : NShape) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (hw : (θ.at x).idxAlong [] = ι x) (hy : ∃ X, Δ.ref (ι x) = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (bd : Term σ (Γ.diaIn x) A a) :
    (⟨_, Term.subst (VarSymb.shiftSlot ι 0 0)
        ((O.viewSubst θ hθ hc).under 0 0 N.ty
          (Ctx.NoSlots.slots (Γ := (O.subst θ hθ hc).view)).root)
        (Subst.ok_under (O.viewOk θ hθ hc) _ _)
        (Subst.coh_under (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc) Ctx.NoSlots.slots _ _)
        (RShape.keepL hF O N hx bd).2⟩ :
        Σ b, Term σ ((O.subst θ hθ hc).view.insert (.bnd 0) N.ty) (RShape.wit N A).ty b) =
      RShape.keepL hF (O.subst θ hθ hc) N hy
        (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) := by
  refine sig_pair (Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_root _ _ _)) ?_
  refine (Term.subst_under_mono (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)
    Ctx.NoSlots.slots Ctx.NoSlots.slots N.ty _).trans (sig_mono _ ?_)
  exact (OutLeg.subst_mono_le_view θ hθ hc O _).trans
    (sig_mono _ (Term.subst_keptDia hF θ hθ hc hx hw hy bd))

/-- Substituting under the slot leaves the companion step's companion term alone. -/
theorem RShape.subst_extR {ι : VarSymb → VarSymb} {V W : Ctx} [V.NoSlots] [W.NoSlots]
    (θ : Subst σ W) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) (S : RShape) (B : VarType) :
    (⟨_, Term.subst (VarSymb.shiftSlot ι 0 0)
        (θ.under 0 0 (S.ext B).ty (Ctx.NoSlots.slots (Γ := W)).root)
        (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _) (S.extR V B).2⟩ :
        Σ a, Term σ (W.insert (.bnd 0) (S.ext B).ty) (.VTypeBox B) a) = ⟨_, (S.extR W B).2⟩ := by
  cases S with
  | nec N =>
      dsimp only [RShape.extR]
      exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by
        rw [Subst.at_proj _ _ rfl, Subst.under_at_root]
        rfl)
  | wit N X =>
      dsimp only [RShape.extR]
      exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by
        rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, Subst.under_at_root]
        rfl)

/-- Substituting the companion-naming step's value substitutes its parts. -/
theorem RShape.subst_compTm_sig {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (A : VarType)
    (cs : List (List Step)) (h : A.CompOk cs) (p : List Step) (h' : A.CompOk (p :: cs))
    (S : RShape) {a : Ann (S.withNec (.boxC A cs h)).flat}
    (t : Term σ Γ (S.withNec (.boxC A cs h)).flat a) {b : Ann ((A.compAt p).getD .VTypeOne)}
    (u : Term σ Γ ((A.compAt p).getD .VTypeOne) b) {a' : Ann (S.withNec (.boxC A cs h)).flat}
    {t' : Term σ Δ (S.withNec (.boxC A cs h)).flat a'} {b' : Ann ((A.compAt p).getD .VTypeOne)}
    {u' : Term σ Δ ((A.compAt p).getD .VTypeOne) b'}
    (ht : (⟨_, Term.subst ι θ hθ hc t⟩ : Σ c, Term σ Δ (S.withNec (.boxC A cs h)).flat c) =
      ⟨a', t'⟩)
    (hu : (⟨_, Term.subst ι θ hθ hc u⟩ : Σ c, Term σ Δ ((A.compAt p).getD .VTypeOne) c) =
      ⟨b', u'⟩) :
    (⟨_, Term.subst ι θ hθ hc (RShape.compTm A cs h p h' S t u).2⟩ :
        Σ c, Term σ Δ (S.withNec (.boxC A (p :: cs) h')).flat c) =
      ⟨_, (RShape.compTm A cs h p h' S t' u').2⟩ := by
  cases S with
  | nec N => exact sig_pair ht hu
  | wit N X =>
      exact (Term.subst_holeRead_sig θ hθ hc _ _).trans
        (Term.holeRead_congr_sig (sig_pair ht hu) _)

/-- Substituting under the slot leaves the companion-naming step's object term alone. -/
theorem RShape.subst_compL {ι : VarSymb → VarSymb} {V W : Ctx} [V.NoSlots] [W.NoSlots]
    (θ : Subst σ W) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) (A : VarType)
    (cs : List (List Step)) (h : A.CompOk cs) (p : List Step) (h' : A.CompOk (p :: cs))
    (S : RShape) :
    (⟨_, Term.subst (VarSymb.shiftSlot ι 0 0)
        (θ.under 0 0 (S.withNec (.boxC A (p :: cs) h')).ty (Ctx.NoSlots.slots (Γ := W)).root)
        (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _)
        (RShape.compL V A cs h p h' S).2⟩ :
        Σ a, Term σ (W.insert (.bnd 0) (S.withNec (.boxC A (p :: cs) h')).ty)
          (S.withNec (.boxC A cs h)).ty a) = ⟨_, (RShape.compL W A cs h p h' S).2⟩ := by
  cases S with
  | nec N =>
      exact Term.subst_eta_renAt _ _ _ _ _ _ (Ctx.ref_insert_root V (.bnd 0) _)
        (Ctx.ref_insert_root W (.bnd 0) _) (by rw [Subst.under_at_root])
  | wit N X =>
      exact Term.subst_eta_renAt _ _ _ _ _ _ (Ctx.ref_insert_root V (.bnd 0) _)
        (Ctx.ref_insert_root W (.bnd 0) _) (by rw [Subst.under_at_root])

/-- Substituting a lifted body is lifting the substituted body: the leg's view sends the `□`
    view's addresses as the `□` view does (`Subst.dia_eq_box_mono`). -/
theorem OutLeg.subst_lift {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) :
    (O : OutLeg Γ) → {T : VarType} → (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) →
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        ((O.viewSubst θ hθ hc).under 0 0 T (OutLeg.slotsFrom hΔ (O.subst θ hθ hc)).root)
        (Subst.ok_under (O.viewOk θ hθ hc) _ (OutLeg.slotsFrom hΔ (O.subst θ hθ hc)).root)
        (Subst.coh_under (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc) (OutLeg.slotsFrom hΓ O) _
          (OutLeg.slotsFrom hΔ (O.subst θ hθ hc)).root)
        ((OutLeg.slotsFrom hΓ O).insert _) ((OutLeg.slotsFrom hΔ (O.subst θ hθ hc)).insert _)
        (O.lift φ) =
      (O.subst θ hθ hc).lift (WFF.subst (VarSymb.shiftSlot ι 0 0)
        (θ.box.under 0 0 T hΔ.boxIn.root) (Subst.ok_under (Subst.ok_box hθ) T hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn T hΔ.boxIn.root)
        (hΓ.boxIn.insert T) (hΔ.boxIn.insert T) φ)
  | .nec, _, _ => rfl
  | .pos y hy, T, φ => by
      have hsy := hΔ.diaIn (ι y)
      have hma : ∀ {Δ₁ Δ₂ : Ctx} (θ' : Subst σ Δ₁) (hle : Δ₁.Le Δ₂) (v : VarSymb),
          θ'.mono hle v = (θ' v).mono hle := fun _ _ _ => rfl
      dsimp only [OutLeg.lift, OutLeg.viewSubst, OutLeg.subst]
      rw [WFF.subst_mono ((Ctx.le_boxIn_diaIn Γ y).insert (.bnd 0) T) _ _ _
          (hΓ.boxIn.insert T) _ _ φ,
        WFF.mono_subst ((Ctx.le_boxIn_diaIn Δ (ι y)).insert (.bnd 0) T) _ _ _ _ _
          (hsy.insert T) φ]
      refine WFF.subst_congr _ _ _ _ _ _ _ _ (Subst.sim_of ?_) φ
      intro v U hlp hv
      by_cases hvr : v = .root (.bnd 0)
      · subst hvr
        rw [show (θ.dia y (ι y)).under 0 0 T hsy.root (.root (.bnd 0)) = .ren (.root (.bnd 0))
            from if_pos rfl, hma _ _ _,
          show θ.box.under 0 0 T hΔ.boxIn.root (.root (.bnd 0)) = .ren (.root (.bnd 0))
            from if_pos rfl]
        exact .refl _
      · have hv' : Γ.boxIn v = some U := by simpa [Ctx.insert, hvr] using hv
        have hvr' : Γ.boxIn.ref v = some U := (Ctx.ref_nonproj Γ.boxIn hlp).trans hv'
        rw [show (θ.dia y (ι y)).under 0 0 T hsy.root v = ((θ.dia y (ι y)) v).mono
              (Ctx.le_insert hsy.root T) from if_neg hvr,
          hma _ _ _,
          show θ.box.under 0 0 T hΔ.boxIn.root v = (θ.box v).mono
              (Ctx.le_insert hΔ.boxIn.root T) from if_neg hvr,
          SubE.mono_mono, ← Subst.at_nonproj (θ.dia y (ι y)) hlp, ← Subst.at_nonproj θ.box hlp,
          Subst.dia_eq_box_mono θ y (ι y) v U hvr', SubE.mono_mono]
        exact .refl _

theorem WFF.bodyRepl_congr {V : Ctx} [V.NoSlots] {A B : VarType} {b₁ b₂ : Ann B}
    {X₁ : Term σ (V.insert (.bnd 0) A) B b₁}
    {X₂ : Term σ (V.insert (.bnd 0) A) B b₂}
    (h : (⟨b₁, X₁⟩ : Σ b, Term σ _ _ b) = ⟨b₂, X₂⟩)
    (Φ : WFF σ (V.insert (.bnd 0) B) 1) :
    WFF.bodyRepl X₁ Φ = WFF.bodyRepl X₂ Φ := by
  cases h
  rfl

theorem WFF.bodySplit_congr {V : Ctx} [V.NoSlots] {A B C : VarType} {b₀ b₀' : Ann A}
    {b₁ b₁' : Ann B} {X₀ : Term σ (V.insert (.bnd 0) C) A b₀}
    {X₀' : Term σ (V.insert (.bnd 0) C) A b₀'}
    {X₁ : Term σ (V.insert (.bnd 0) C) B b₁}
    {X₁' : Term σ (V.insert (.bnd 0) C) B b₁'}
    (h₀ : (⟨b₀, X₀⟩ : Σ b, Term σ _ _ b) = ⟨b₀', X₀'⟩)
    (h₁ : (⟨b₁, X₁⟩ : Σ b, Term σ _ _ b) = ⟨b₁', X₁'⟩)
    (Φ : WFF σ ((V.insert (.bnd 0) A).insert (.bnd 1) B) 2) :
    WFF.bodySplit X₀ X₁ Φ = WFF.bodySplit X₀' X₁' Φ := by
  cases h₀
  cases h₁
  rfl

/-- On the view's addresses the replacing substitution is the identity, weakened. -/
theorem Subst.set_idS_at {V : Ctx} [V.NoSlots] (T : VarType) (e : SubE σ (V.insert (.bnd 0) T)) :
    ∀ w U, V.ref w = some U → ((Subst.idS σ (V.insert (.bnd 0) T)).set (.bnd 0) e).at w =
      (((Subst.idRen (σ := σ) V).at w).mono
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := V)).root T)) := by
  intro w U hw
  rw [Subst.at_idRen]
  refine Subst.at_ren_of (Γ := V) (fun v U' _ hv => ?_) w U hw
  have hne : v ≠ .root (.bnd 0) := fun he => by
    subst he
    rw [(Ctx.NoSlots.slots (Γ := V)).root] at hv
    cases hv
  exact Subst.set_ne _ _ hne

/-- ⭐**Replacing the bound item commutes with substitution**: both sides are one substitution — the
    view's addresses go as `θ` sends them, the item to the substituted term. -/
theorem WFF.subst_bodyRepl {ι : VarSymb → VarSymb} {V W : Ctx} [V.NoSlots] [W.NoSlots]
    (θ : Subst σ W) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) {A B : VarType}
    {b : Ann B} (X : Term σ (V.insert (.bnd 0) A) B b)
    (Φ : WFF σ (V.insert (.bnd 0) B) 1) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        (θ.under 0 0 A (Ctx.NoSlots.slots (Γ := W)).root)
        (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _)
        ((Ctx.NoSlots.slots (Γ := V)).insert _) ((Ctx.NoSlots.slots (Γ := W)).insert _)
        (WFF.bodyRepl X Φ) =
      WFF.bodyRepl (Term.subst (VarSymb.shiftSlot ι 0 0)
          (θ.under 0 0 A (Ctx.NoSlots.slots (Γ := W)).root)
          (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _) X)
        (WFF.subst (VarSymb.shiftSlot ι 0 0)
          (θ.under 0 0 B (Ctx.NoSlots.slots (Γ := W)).root)
          (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _)
          ((Ctx.NoSlots.slots (Γ := V)).insert _) ((Ctx.NoSlots.slots (Γ := W)).insert _) Φ) := by
  have hW := (Ctx.NoSlots.slots (Γ := W)).root
  have hrV : V.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)
  have hθA := Subst.ok_under (d := 0) hθ A hW
  have hcA := Subst.coh_under hθ hc Ctx.NoSlots.slots A hW
  set X' := Term.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 A hW) hθA hcA X
  have hθ₅ := Subst.ok_set (r := .bnd 0) (T := B) (e := .tm X')
    (hθA.restrict (body_le (V := V) A)) rfl
  have hc₅ := Subst.coh_set (r := .bnd 0) (T := B) (e := .tm X')
    (hθA.restrict (body_le (V := V) A)) (hcA.restrict (body_le (V := V) _)) hrV rfl
  unfold WFF.bodyRepl
  refine (WFF.subst_comp _ _ _ _ _ _ _ hθ₅ hc₅ _ _ _ ?_ Φ).trans
    (WFF.subst_comp _ _ _ _ _ _ _ hθ₅ hc₅ _ _ _ ?_ Φ).symm
  · refine Subst.sim_of fun v U hlp hv => ?_
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.set_root, Subst.set_root]
      exact .refl _
    · rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr,
        show (Subst.idS σ (V.insert (.bnd 0) A) v) = .ren v from rfl, SubE.comp_ren,
        Subst.at_nonproj _ hlp]
      exact .refl _
  · refine Subst.sim_of fun v U hlp hv => ?_
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.set_root, show θ.under 0 0 B hW (.root (.bnd 0)) = .ren (.root (.bnd 0))
        from if_pos rfl, SubE.comp_ren]
      change SubE.Sim _ _ ((Subst.idS σ _).set (.bnd 0) (.tm X') (.root (.bnd 0)))
      rw [Subst.set_root]
      exact .refl _
    · have hv' : V v = some U := by simpa [Ctx.insert, hvr] using hv
      rw [Subst.set_ne _ _ hvr,
        show θ.under 0 0 A hW v = (θ v).mono (Ctx.le_insert hW A)
          from if_neg hvr,
        show θ.under 0 0 B hW v = (θ v).mono (Ctx.le_insert hW B)
          from if_neg hvr,
        SubE.comp_mono (Subst.idRen W) Subst.ok_idRen Subst.coh_idRen
          (Ctx.le_insert hW B) (Ctx.le_insert hW A) _ _ _
          (Subst.set_idS_at (V := W) A (.tm X')) (hθ v U hlp hv'),
        SubE.comp_idRen]
      exact .refl _

/-- ⭐**Splitting a paired item commutes with substitution**, likewise. -/
theorem WFF.subst_bodySplit {ι : VarSymb → VarSymb} {V W : Ctx} [V.NoSlots] [W.NoSlots]
    (θ : Subst σ W) (hθ : Subst.Ok V θ) (hc : Subst.Coh ι V θ) {A B C : VarType}
    {b₀ : Ann A} {b₁ : Ann B}
    (X₀ : Term σ (V.insert (.bnd 0) C) A b₀)
    (X₁ : Term σ (V.insert (.bnd 0) C) B b₁)
    (Φ : WFF σ ((V.insert (.bnd 0) A).insert (.bnd 1) B) 2) :
    WFF.subst (VarSymb.shiftSlot ι 0 0)
        (θ.under 0 0 C (Ctx.NoSlots.slots (Γ := W)).root)
        (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _)
        ((Ctx.NoSlots.slots (Γ := V)).insert _) ((Ctx.NoSlots.slots (Γ := W)).insert _)
        (WFF.bodySplit X₀ X₁ Φ) =
      WFF.bodySplit
        (Term.subst (VarSymb.shiftSlot ι 0 0)
          (θ.under 0 0 C (Ctx.NoSlots.slots (Γ := W)).root)
          (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _) X₀)
        (Term.subst (VarSymb.shiftSlot ι 0 0)
          (θ.under 0 0 C (Ctx.NoSlots.slots (Γ := W)).root)
          (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _) X₁)
        (WFF.subst (VarSymb.shiftSlot (VarSymb.shiftSlot ι 0 0) 1 1)
          ((θ.under 0 0 A (Ctx.NoSlots.slots (Γ := W)).root).under 1 1 B
            ((Ctx.NoSlots.slots (Γ := W)).insert _).root)
          (Subst.ok_under (Subst.ok_under hθ _ _) _ _)
          (Subst.coh_under (Subst.ok_under hθ _ _) (Subst.coh_under hθ hc Ctx.NoSlots.slots _ _)
            ((Ctx.NoSlots.slots (Γ := V)).insert _) _ _)
          (((Ctx.NoSlots.slots (Γ := V)).insert _).insert _)
          (((Ctx.NoSlots.slots (Γ := W)).insert _).insert _) Φ) := by
  have hW := (Ctx.NoSlots.slots (Γ := W)).root
  have hW1 := ((Ctx.NoSlots.slots (Γ := W)).insert A).root
  have hrV : V.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)
  have hrV1 : (V.insert (.bnd 0) A).RootFresh (.bnd 1) :=
    ((Ctx.NoSlots.slots (Γ := V)).insert _).rootFresh (le_refl 1)
  have hθC := Subst.ok_under (d := 0) hθ C hW
  have hcC := Subst.coh_under hθ hc Ctx.NoSlots.slots C hW
  set X₀' := Term.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 C hW) hθC hcC X₀
  set X₁' := Term.subst (VarSymb.shiftSlot ι 0 0) (θ.under 0 0 C hW) hθC hcC X₁
  have h₀ := Subst.ok_set (r := .bnd 0) (T := A) (e := .tm X₀')
    (hθC.restrict (body_le (V := V) C)) rfl
  have c₀ := Subst.coh_set (r := .bnd 0) (T := A) (e := .tm X₀')
    (hθC.restrict (body_le (V := V) C)) (hcC.restrict (body_le (V := V) _)) hrV rfl
  have hθ₅ := Subst.ok_set (r := .bnd 1) (T := B) (e := .tm X₁') h₀ rfl
  have hc₅ := Subst.coh_set (r := .bnd 1) (T := B) (e := .tm X₁') h₀ c₀ hrV1 rfl
  have h10 : (VarSymb.root (.bnd 1)) ≠ .root (.bnd 0) := by simp
  unfold WFF.bodySplit
  refine (WFF.subst_comp _ _ _ _ _ _ _ hθ₅ hc₅ _ _ _ ?_ Φ).trans
    (WFF.subst_comp _ _ _ _ _ _ _ hθ₅ hc₅ _ _ _ ?_ Φ).symm
  · refine Subst.sim_of fun v U hlp hv => ?_
    rw [Subst.comp_apply]
    by_cases hv1 : v = .root (.bnd 1)
    · subst hv1
      rw [Subst.set_root, Subst.set_root]
      exact .refl _
    · by_cases hv0 : v = .root (.bnd 0)
      · subst hv0
        rw [Subst.set_ne _ _ hv1, Subst.set_ne _ _ hv1, Subst.set_root, Subst.set_root]
        exact .refl _
      · rw [Subst.set_ne _ _ hv1, Subst.set_ne _ _ hv1, Subst.set_ne _ _ hv0,
          Subst.set_ne _ _ hv0,
          show (Subst.idS σ (V.insert (.bnd 0) C) v) = .ren v from rfl, SubE.comp_ren,
          Subst.at_nonproj _ hlp]
        exact .refl _
  · refine Subst.sim_of fun v U hlp hv => ?_
    rw [Subst.comp_apply]
    by_cases hv1 : v = .root (.bnd 1)
    · subst hv1
      rw [Subst.set_root, show (θ.under 0 0 A hW).under 1 1 B hW1
          (.root (.bnd 1)) = .ren (.root (.bnd 1)) from if_pos rfl, SubE.comp_ren]
      change SubE.Sim _ _ ((((Subst.idS σ _).set (.bnd 0) (.tm X₀')).set (.bnd 1) (.tm X₁'))
        (.root (.bnd 1)))
      rw [Subst.set_root]
      exact .refl _
    · by_cases hv0 : v = .root (.bnd 0)
      · subst hv0
        rw [Subst.set_ne _ _ hv1, Subst.set_root,
          show (θ.under 0 0 A hW).under 1 1 B hW1 (.root (.bnd 0)) =
            ((θ.under 0 0 A hW) (.root (.bnd 0))).mono
              (Ctx.le_insert hW1 B) from if_neg hv1,
          show θ.under 0 0 A hW (.root (.bnd 0)) = .ren (.root (.bnd 0)) from
            if_pos rfl]
        change SubE.Sim _ _ ((((Subst.idS σ _).set (.bnd 0) (.tm X₀')).set (.bnd 1) (.tm X₁')).at
          (.root (.bnd 0)))
        change SubE.Sim _ _ ((((Subst.idS σ _).set (.bnd 0) (.tm X₀')).set (.bnd 1) (.tm X₁'))
          (.root (.bnd 0)))
        rw [Subst.set_ne _ _ (Ne.symm h10), Subst.set_root]
        exact .refl _
      · have hv' : V v = some U := by simpa [Ctx.insert, hv0, hv1] using hv
        rw [Subst.set_ne _ _ hv1, Subst.set_ne _ _ hv0,
          show θ.under 0 0 C hW v = (θ v).mono (Ctx.le_insert hW C)
            from if_neg hv0,
          show (θ.under 0 0 A hW).under 1 1 B hW1 v =
            ((θ.under 0 0 A hW) v).mono (Ctx.le_insert hW1 B)
            from if_neg hv1,
          show θ.under 0 0 A hW v = (θ v).mono (Ctx.le_insert hW A)
            from if_neg hv0, SubE.mono_mono,
          SubE.comp_mono (Subst.idRen W) Subst.ok_idRen Subst.coh_idRen
            ((Ctx.le_insert hW A).trans (Ctx.le_insert hW1 B))
            (Ctx.le_insert hW C) _ _ _ ?_ (hθ v U hlp hv'),
          SubE.comp_idRen]
        · exact .refl _
        · intro w T hw
          rw [Subst.at_idRen]
          refine Subst.at_ren_of (Γ := W) (fun x U' _ hx => ?_) w T hw
          have hne0 : x ≠ .root (.bnd 0) := fun he => by
            subst he
            rw [hW] at hx
            cases hx
          have hne1 : x ≠ .root (.bnd 1) := fun he => by
            subst he
            rw [(Ctx.NoSlots.slots (Γ := W)).rootFresh (n := 1) (Nat.zero_le 1) (.root (.bnd 1))
              rfl] at hx
            cases hx
          exact (Subst.set_ne _ _ hne1).trans (Subst.set_ne _ _ hne0)

/-- ⭐**A body weakened past a fresh eigenvariable**, substituted with the eigenvariable renamed:
    the weakening of the substituted body.  Read off `WFF.subst_weaken_renameTm` at `□∃d. Φ`. -/
theorem WFF.subst_body_renameTm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u')) (T : VarType)
    {C : VarType} (Ψ : WFF σ (Γ.boxIn.insert (.bnd 0) C) 1) :
    WFF.subst (VarSymb.shiftSlot (Subst.renameTmIdx σ ι u u' T hu'.root) 0 0)
        ((θ.renameTm u u' T hu'.root).box.under 0 0 C
          (hΔ.insertFree u' T).boxIn.root)
        (Subst.ok_under (Subst.ok_box (Subst.ok_renameTm hθ T hu'.root)) _ _)
        (Subst.coh_under (Subst.ok_box (Subst.ok_renameTm hθ T hu'.root))
          (Subst.coh_box (Subst.ok_renameTm hθ T hu'.root)
            (Subst.coh_renameTm hθ hc hu T hu'.root)) (hΓ.insertFree u T).boxIn _ _)
        ((hΓ.insertFree u T).boxIn.insert _) ((hΔ.insertFree u' T).boxIn.insert _)
        (WFF.mono ((Ctx.le_insert hu.root T).boxIn.insert (.bnd 0) _) Ψ) =
      WFF.mono ((Ctx.le_insert hu'.root T).boxIn.insert (.bnd 0) _)
        (WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 C hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) _ _)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ _)
          (hΓ.boxIn.insert _) (hΔ.boxIn.insert _) Ψ) := by
  have h := WFF.subst_weaken_renameTm θ hθ hc hΓ hΔ hu hu' T (WFF.box (WFF.ex C Ψ))
  injection h with _ _ h₁
  simp only [WFF.mono, WFF.subst] at h₁
  injection h₁ with _ _ _ h₂

/-- How a substitution acts on a returning possibility's body: through the `□` view, under the
    slot. -/
abbrev WFF.bodySubst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) {T : VarType}
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) : WFF σ (Δ.boxIn.insert (.bnd 0) T) 1 :=
  WFF.subst (VarSymb.shiftSlot ι 0 0) (θ.box.under 0 0 T hΔ.boxIn.root)
    (Subst.ok_under (Subst.ok_box hθ) T hΔ.boxIn.root)
    (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn T hΔ.boxIn.root)
    (hΓ.boxIn.insert T) (hΔ.boxIn.insert T) Φ

/-- How a substitution acts on a returning possibility's body along a leg: through the leg's
    view, under the slot. -/
abbrev OutLeg.bodySubst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0) (O : OutLeg Γ)
    {T : VarType} (Φ : WFF σ (O.view.insert (.bnd 0) T) 1) :
    WFF σ ((O.subst θ hθ hc).view.insert (.bnd 0) T) 1 :=
  WFF.subst (VarSymb.shiftSlot ι 0 0)
    ((O.viewSubst θ hθ hc).under 0 0 T (OutLeg.slotsFrom hΔ (O.subst θ hθ hc)).root)
    (Subst.ok_under (O.viewOk θ hθ hc) T (OutLeg.slotsFrom hΔ (O.subst θ hθ hc)).root)
    (Subst.coh_under (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc) (OutLeg.slotsFrom hΓ O) T
      (OutLeg.slotsFrom hΔ (O.subst θ hθ hc)).root)
    ((OutLeg.slotsFrom hΓ O).insert T) ((OutLeg.slotsFrom hΔ (O.subst θ hθ hc)).insert T) Φ

/-- Substituting a body along `◇_x` given by a hole formula: the content's view term goes as
    `x`'s view sends it, the hole formula as the `□` view does. -/
theorem WFF.subst_viewBody {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (hy : ∃ X, Δ.ref (ι x) = some (.VTypeDia X)) {X T : VarType} {a : Ann X}
    (bd : Term σ (Γ.diaIn x) X a) (χ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeProd X T)) 1) :
    OutLeg.bodySubst θ hθ hc hΓ hΔ (.pos x hx) (WFF.viewBody hx bd χ) =
      WFF.viewBody hy (Term.subst ι (θ.dia x (ι x))
          (Subst.ok_dia hθ hx (hx.elim fun _ hX => hc x _ hX [])) (Subst.coh_dia hθ hc hx) bd)
        (WFF.bodySubst θ hθ hc hΓ hΔ χ) := by
  have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
  refine (WFF.subst_bodyRepl (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
    _ _).trans ?_
  refine (WFF.bodyRepl_congr (sig_pair (Term.subst_under_mono (θ.dia x (ι x))
      (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) (hΓ.diaIn x) (hΔ.diaIn (ι x)) T bd)
    (Term.subst_eta_renAt _ _ _ _ _ _ (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) _)
      (Ctx.ref_insert_root (Δ.diaIn (ι x)) (.bnd 0) _) (by rw [Subst.under_at_root]))) _).trans ?_
  exact congrArg _ (OutLeg.subst_lift θ hθ hc hΓ hΔ (.pos x hx) χ)

/-- ⭐Substituting the returning possibility that a fresh-value rule hands its subproof: the leg
    and the body are weakened past the fresh root, so they go as the old substitution sends them;
    only the value is new.  Along a witness the witness goes to `ι y` (the fresh root is not its
    root). -/
theorem OutLeg.subst_retS_renameTm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u')) (T : VarType)
    (hS : ModalSys.BStrong = true) (O : OutLeg Γ) (S : RShape)
    (Φ : WFF σ (O.view.insert (.bnd 0) S.ty) 1) {a a' : Ann S.flat}
    (s : Term σ (Γ.insert (.free u) T) S.flat a)
    (s' : Term σ (Δ.insert (.free u') T) S.flat a')
    (hs : (⟨_, Term.subst (Subst.renameTmIdx σ ι u u' T hu'.root) (θ.renameTm u u' T hu'.root)
        (Subst.ok_renameTm hθ T hu'.root) (Subst.coh_renameTm hθ hc hu T hu'.root) s⟩ :
        Σ b, Term σ (Δ.insert (.free u') T) S.flat b) = ⟨_, s'⟩) :
    WFF.subst (Subst.renameTmIdx σ ι u u' T hu'.root) (θ.renameTm u u' T hu'.root)
        (Subst.ok_renameTm hθ T hu'.root) (Subst.coh_renameTm hθ hc hu T hu'.root)
        (hΓ.insertFree u T) (hΔ.insertFree u' T)
        ((O.mono (Ctx.le_insert hu.root T)).retS hS S s
          (WFF.mono ((O.le_view_mono (Ctx.le_insert hu.root T)).insert (.bnd 0) _) Φ)) =
      ((O.subst θ hθ hc).mono (Ctx.le_insert hu'.root T)).retS hS S s'
        (WFF.mono (((O.subst θ hθ hc).le_view_mono (Ctx.le_insert hu'.root T)).insert (.bnd 0) _)
          (OutLeg.bodySubst θ hθ hc hΓ hΔ O Φ)) := by
  cases O with
  | nec => exact WFF.retS_congr hS S hs (WFF.subst_body_renameTm θ hθ hc hΓ hΔ hu hu' T Φ)
  | pos y hy =>
      have hle := Ctx.le_insert hu.root T
      have hle' := Ctx.le_insert hu'.root T
      have hΔ' := hΔ.insertFree u' T
      have okr := Subst.ok_renameTm (u := u) hθ T hu'.root
      have cohr := Subst.coh_renameTm hθ hc hu T hu'.root
      have hyΓ : ∃ Y, (Γ.insert (.free u) T).ref y = some (.VTypeDia Y) :=
        hy.imp fun _ h => hle.ref h
      have hιr : Subst.renameTmIdx σ ι u u' T hu'.root y = ι y := by
        obtain ⟨Y, h⟩ := hy
        exact if_neg (Ctx.RootFresh.rt_ne hu h)
      have hwr : ((θ.renameTm u u' T hu'.root).at y).idxAlong [] = ι y :=
        hyΓ.elim fun _ h => (cohr y _ h []).trans hιr
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ h => hc y _ h []
      have hwm : ((θ.mono hle').at y).idxAlong [] = ι y :=
        hy.elim fun _ h => Subst.coh_mono hc hle' y _ h []
      have hr0 := (hΔ.diaIn (ι y)).root
      have hr1 := (hΔ'.diaIn (ι y)).root
      have key : ∀ (z : VarSymb) (_hz : Subst.renameTmIdx σ ι u u' T hu'.root y = z)
          (P : ∃ Y, (Δ.insert (.free u') T).ref z = some (.VTypeDia Y))
          (hz' : ((Δ.insert (.free u') T).diaIn z).SlotsFrom 0)
          (p : Subst.Ok (((Γ.insert (.free u) T).diaIn y).insert (.bnd 0) S.ty)
            (((θ.renameTm u u' T hu'.root).dia y z).under 0 0 _ hz'.root))
          (q : Subst.Coh (VarSymb.shiftSlot (Subst.renameTmIdx σ ι u u' T hu'.root) 0 0)
            (((Γ.insert (.free u) T).diaIn y).insert (.bnd 0) S.ty)
            (((θ.renameTm u u' T hu'.root).dia y z).under 0 0 _ hz'.root)),
          WFF.subst (Subst.renameTmIdx σ ι u u' T hu'.root) (θ.renameTm u u' T hu'.root) okr cohr
              (hΓ.insertFree u T) hΔ'
              (WFF.retxS hS y hyΓ S s (WFF.mono ((hle.diaIn y).insert (.bnd 0) _) Φ)) =
            WFF.retxS hS z P S (Term.subst _ _ okr cohr s)
              (WFF.subst (VarSymb.shiftSlot (Subst.renameTmIdx σ ι u u' T hu'.root) 0 0)
                (((θ.renameTm u u' T hu'.root).dia y z).under 0 0 _ hz'.root) p q
                (((hΓ.insertFree u T).diaIn y).insert _) (hz'.insert _)
                (WFF.mono ((hle.diaIn y).insert (.bnd 0) _) Φ)) := by
        intro z hz P hz' p q
        subst hz
        rfl
      have okd := Subst.ok_dia okr hyΓ hwr
      have cohd : Subst.Coh (Subst.renameTmIdx σ ι u u' T hu'.root) ((Γ.insert (.free u) T).diaIn y)
          ((θ.renameTm u u' T hu'.root).dia y (ι y)) := hιr ▸ Subst.coh_dia okr cohr hyΓ
      refine (key (ι y) hιr _ (hΔ'.diaIn (ι y)) (Subst.ok_under okd _ hr1)
        (Subst.coh_under okd cohd ((hΓ.insertFree u T).diaIn y) _ hr1)).trans
        (WFF.retxS_congr hS _ _ S hs ?_)
      have okm := Subst.ok_dia (Subst.ok_mono hθ hle') hy hwm
      have cohm := Subst.coh_dia (Subst.ok_mono hθ hle') (Subst.coh_mono hc hle') hy
      have ok0 := Subst.ok_dia hθ hy hw
      have coh0 := Subst.coh_dia hθ hc hy
      have ok3 := Subst.ok_mono ok0 (hle'.diaIn (ι y))
      have coh3 := Subst.coh_mono coh0 (hle'.diaIn (ι y))
      rw [WFF.subst_mono ((hle.diaIn y).insert (.bnd 0) _) _ _ _ ((hΓ.diaIn y).insert _) _ _ Φ]
      refine (WFF.subst_congr _ (((θ.mono hle').dia y (ι y)).under 0 0 _ hr1) _
        (Subst.ok_under okm _ hr1) _ (Subst.coh_under okm cohm (hΓ.diaIn y) _ hr1) _ _
        (Subst.sim_under (Subst.sim_dia (Subst.sim_renameTm_mono hu T hu'.root) hwr) _ hr1)
        Φ).trans ?_
      refine (WFF.subst_congr (((θ.dia y (ι y)).mono (hle'.diaIn (ι y))).under 0 0 _ hr1) _
        (Subst.ok_under ok3 _ hr1) _ (Subst.coh_under ok3 coh3 (hΓ.diaIn y) _ hr1) _ _ _
        (Subst.sim_under (Subst.sim_dia_mono θ hle' y (ι y)) _ hr1) Φ).symm.trans ?_
      refine (WFF.subst_congr (((θ.dia y (ι y)).under 0 0 _ hr0).mono
          ((hle'.diaIn (ι y)).insert _ _)) _
        (Subst.ok_mono (Subst.ok_under ok0 _ hr0) _) _
        (Subst.coh_mono (Subst.coh_under ok0 coh0 (hΓ.diaIn y) _ hr0) _) _ _ _
        (Subst.sim_under_mono (θ.dia y (ι y)) (hle'.diaIn (ι y)) _ hr0 hr1) Φ).symm.trans ?_
      exact (WFF.mono_subst ((hle'.diaIn (ι y)).insert _ _) _ (Subst.ok_under ok0 _ hr0)
        (Subst.coh_under ok0 coh0 (hΓ.diaIn y) _ hr0) ((hΓ.diaIn y).insert _)
        ((hΔ.diaIn (ι y)).insert _) ((hΔ'.diaIn (ι y)).insert _) Φ).symm

/-- A body weakened past a fresh variable, substituted with the variable renamed: the weakening
    of the substituted body (`WFF.subst_body_renameTm` for `Subst.rename`). -/
theorem WFF.subst_body_rename {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u')) (T : VarType)
    {C : VarType} (Ψ : WFF σ (Γ.boxIn.insert (.bnd 0) C) 1) :
    WFF.subst (VarSymb.shiftSlot (VarSymb.renameIdx ι u u') 0 0)
        ((θ.rename u u' T hu'.root).box.under 0 0 C
          (hΔ.insertFree u' T).boxIn.root)
        (Subst.ok_under (Subst.ok_box (Subst.ok_rename hθ T hu'.root)) _ _)
        (Subst.coh_under (Subst.ok_box (Subst.ok_rename hθ T hu'.root))
          (Subst.coh_box (Subst.ok_rename hθ T hu'.root)
            (Subst.coh_rename hθ hc hu T hu'.root)) (hΓ.insertFree u T).boxIn _ _)
        ((hΓ.insertFree u T).boxIn.insert _) ((hΔ.insertFree u' T).boxIn.insert _)
        (WFF.mono ((Ctx.le_insert hu.root T).boxIn.insert (.bnd 0) _) Ψ) =
      WFF.mono ((Ctx.le_insert hu'.root T).boxIn.insert (.bnd 0) _)
        (WFF.bodySubst θ hθ hc hΓ hΔ Ψ) := by
  have h := WFF.subst_weaken_rename θ hθ hc hΓ hΔ hu hu' T (WFF.box (WFF.ex C Ψ))
  injection h with _ _ h₁
  simp only [WFF.mono, WFF.subst] at h₁
  injection h₁ with _ _ _ h₂

/-- The renamed fresh variable, kept, goes to the new one kept. -/
theorem Subst.rename_box_keep (θ : Subst σ Δ) (u u' : ℕ) (T : VarType)
    (h : Δ (.root (.free u')) = none) :
    (θ.rename u u' T h).box.at (.step (.root (.free u)) .keep) =
      .ren (.step (.root (.free u')) .keep) := by
  rw [Subst.at_nonproj _ rfl]
  change (θ.rename u u' T h (.root (.free u))).keepE = _
  rw [Subst.rename_root]
  rfl

/-- ⭐**Substituting `keep_lift`'s hypothesis**: the leg and the body go as the old substitution
    sends them, and the fresh variable kept goes to the new one kept.  Along a witness the witness
    goes to `ι y`, as in `OutLeg.subst_retS_renameTm`. -/
theorem WFF.subst_liftRead_rename {ι : VarSymb → VarSymb} {Γ Δ : Ctx} [Γ.NoSlots] [Δ.NoSlots]
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u'))
    (hF : ModalSys.Four = true) {T : VarType} (hl : T.liftable = true) (O : OutLeg Γ)
    (φ : WFF σ (O.view.insert (.bnd 0) T) 1) :
    WFF.subst (VarSymb.renameIdx ι u u') (θ.rename u u' T hu'.root) (Subst.ok_rename hθ T hu'.root)
        (Subst.coh_rename hθ hc hu T hu'.root) (hΓ.insertFree u T) (hΔ.insertFree u' T)
        (WFF.liftRead hF hl O hu φ) =
      WFF.liftRead hF hl (O.subst θ hθ hc) hu' (OutLeg.bodySubst θ hθ hc hΓ hΔ O φ) := by
  have hle := Ctx.le_insert hu.root T
  have hle' := Ctx.le_insert hu'.root T
  have hΔ' := hΔ.insertFree u' T
  have okr := Subst.ok_rename (u := u) hθ T hu'.root
  have cohr := Subst.coh_rename hθ hc hu T hu'.root
  cases O with
  | nec =>
      refine congrArg (fun χ : WFF σ (Δ.insert (.free u') T).boxIn 0 => (WFF.box χ.neg).neg) ?_
      refine (WFF.subst_instantiate _ (Subst.ok_box okr) (Subst.coh_box okr cohr)
        (hΓ.insertFree u T).boxIn hΔ'.boxIn _ _).trans ?_
      refine (WFF.instantiate_congr_sig _ (Term.subst_eta_renAt _ _ _ T _ _ _
        (Ctx.ref_keep_of' hF (Ctx.ref_insert_root Δ (.free u') T) (VarType.keepable_of_liftable hl))
        (Subst.rename_box_keep θ u u' T hu'.root)) _).trans ?_
      exact congrArg _ (WFF.subst_body_rename θ hθ hc hΓ hΔ hu hu' T φ)
  | pos y hy =>
      have hyΓ : ∃ Y, (Γ.insert (.free u) T).ref y = some (.VTypeDia Y) :=
        hy.imp fun _ h => hle.ref h
      have hιr : VarSymb.renameIdx ι u u' y = ι y := by
        obtain ⟨Y, h⟩ := hy
        exact if_neg (Ctx.RootFresh.rt_ne hu h)
      have hwr : ((θ.rename u u' T hu'.root).at y).idxAlong [] = ι y :=
        hyΓ.elim fun _ h => (cohr y _ h []).trans hιr
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ h => hc y _ h []
      have hwm : ((θ.mono hle').at y).idxAlong [] = ι y :=
        hy.elim fun _ h => Subst.coh_mono hc hle' y _ h []
      have hr0 := (hΔ.diaIn (ι y)).root
      have hr1 := (hΔ'.diaIn (ι y)).root
      have key : ∀ (z : VarSymb) (_hz : VarSymb.renameIdx ι u u' y = z)
          (P : ∃ Y, (Δ.insert (.free u') T).ref z = some (.VTypeDia Y))
          (hz' : ((Δ.insert (.free u') T).diaIn z).SlotsFrom 0)
          (p : Subst.Ok ((Γ.insert (.free u) T).diaIn y) ((θ.rename u u' T hu'.root).dia y z))
          (q : Subst.Coh (VarSymb.renameIdx ι u u') ((Γ.insert (.free u) T).diaIn y)
            ((θ.rename u u' T hu'.root).dia y z))
          (ψ : WFF σ ((Γ.insert (.free u) T).diaIn y) 0),
          WFF.subst (VarSymb.renameIdx ι u u') (θ.rename u u' T hu'.root) okr cohr
              (hΓ.insertFree u T) hΔ' (WFF.dia y hyΓ ψ) =
            WFF.dia z P (WFF.subst (VarSymb.renameIdx ι u u') ((θ.rename u u' T hu'.root).dia y z)
              p q ((hΓ.insertFree u T).diaIn y) hz' ψ) := by
        intro z hz P hz' p q ψ
        subst hz
        rfl
      have okd := Subst.ok_dia okr hyΓ hwr
      have cohd : Subst.Coh (VarSymb.renameIdx ι u u') ((Γ.insert (.free u) T).diaIn y)
          ((θ.rename u u' T hu'.root).dia y (ι y)) := hιr ▸ Subst.coh_dia okr cohr hyΓ
      refine (key (ι y) hιr _ (hΔ'.diaIn (ι y)) okd cohd _).trans (congrArg (WFF.dia _ _) ?_)
      refine (WFF.subst_instantiate _ okd cohd ((hΓ.insertFree u T).diaIn y)
        (hΔ'.diaIn (ι y)) _ _).trans ?_
      have hat : ((θ.rename u u' T hu'.root).dia y (ι y)).at (.step (.root (.free u)) .keep) =
          .ren (.step (.root (.free u')) .keep) := by
        rw [Subst.dia_eq_box_mono _ y (ι y) _ T (Ctx.ref_keep_of' hF
          (Ctx.ref_insert_root Γ (.free u) T) (VarType.keepable_of_liftable hl)),
          Subst.rename_box_keep]
        rfl
      refine (WFF.instantiate_congr_sig _ (Term.subst_eta_renAt _ _ _ T _ _ _
        ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_keep_of' hF (Ctx.ref_insert_root Δ (.free u') T)
          (VarType.keepable_of_liftable hl))) hat) _).trans
        (congrArg _ ?_)
      have okm := Subst.ok_dia (Subst.ok_mono hθ hle') hy hwm
      have cohm := Subst.coh_dia (Subst.ok_mono hθ hle') (Subst.coh_mono hc hle') hy
      have ok0 := Subst.ok_dia hθ hy hw
      have coh0 := Subst.coh_dia hθ hc hy
      have ok3 := Subst.ok_mono ok0 (hle'.diaIn (ι y))
      have coh3 := Subst.coh_mono coh0 (hle'.diaIn (ι y))
      rw [WFF.subst_mono ((hle.diaIn y).insert (.bnd 0) _) _ _ _ ((hΓ.diaIn y).insert _) _ _ φ]
      refine (WFF.subst_congr _ (((θ.mono hle').dia y (ι y)).under 0 0 _ hr1) _
        (Subst.ok_under okm _ hr1) _ (Subst.coh_under okm cohm (hΓ.diaIn y) _ hr1) _ _
        (Subst.sim_under (Subst.sim_dia (Subst.sim_rename_mono hu T hu'.root) hwr) _ hr1)
        φ).trans ?_
      refine (WFF.subst_congr (((θ.dia y (ι y)).mono (hle'.diaIn (ι y))).under 0 0 _ hr1) _
        (Subst.ok_under ok3 _ hr1) _ (Subst.coh_under ok3 coh3 (hΓ.diaIn y) _ hr1) _ _ _
        (Subst.sim_under (Subst.sim_dia_mono θ hle' y (ι y)) _ hr1) φ).symm.trans ?_
      refine (WFF.subst_congr (((θ.dia y (ι y)).under 0 0 _ hr0).mono
          ((hle'.diaIn (ι y)).insert _ _)) _
        (Subst.ok_mono (Subst.ok_under ok0 _ hr0) _) _
        (Subst.coh_mono (Subst.coh_under ok0 coh0 (hΓ.diaIn y) _ hr0) _) _ _ _
        (Subst.sim_under_mono (θ.dia y (ι y)) (hle'.diaIn (ι y)) _ hr0 hr1) φ).symm.trans ?_
      exact (WFF.mono_subst ((hle'.diaIn (ι y)).insert _ _) _ (Subst.ok_under ok0 _ hr0)
        (Subst.coh_under ok0 coh0 (hΓ.diaIn y) _ hr0) ((hΓ.diaIn y).insert _)
        ((hΔ.diaIn (ι y)).insert _) ((hΔ'.diaIn (ι y)).insert _) φ).symm

/-- ⭐Substituting the returning possibility that a fresh-value rule hands its subproof: the leg
    and the body are weakened past the fresh root, so they go as the old substitution sends them;
    only the value is new.  Along a witness the witness goes to `ι y` (the fresh root is not its
    root). -/
theorem OutLeg.subst_ret_renameTm {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u')) (T : VarType)
    (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) {a a' : Ann A}
    (s : Term σ (Γ.insert (.free u) T) A a) (s' : Term σ (Δ.insert (.free u') T) A a')
    (hs : (⟨_, Term.subst (Subst.renameTmIdx σ ι u u' T hu'.root) (θ.renameTm u u' T hu'.root)
        (Subst.ok_renameTm hθ T hu'.root) (Subst.coh_renameTm hθ hc hu T hu'.root) s⟩ :
        Σ b, Term σ (Δ.insert (.free u') T) A b) = ⟨_, s'⟩) :
    WFF.subst (Subst.renameTmIdx σ ι u u' T hu'.root) (θ.renameTm u u' T hu'.root)
        (Subst.ok_renameTm hθ T hu'.root) (Subst.coh_renameTm hθ hc hu T hu'.root)
        (hΓ.insertFree u T) (hΔ.insertFree u' T)
        ((O.mono (Ctx.le_insert hu.root T)).ret hS s
          (WFF.mono ((O.le_view_mono (Ctx.le_insert hu.root T)).insert (.bnd 0) _) Φ)) =
      ((O.subst θ hθ hc).mono (Ctx.le_insert hu'.root T)).ret hS s'
        (WFF.mono (((O.subst θ hθ hc).le_view_mono (Ctx.le_insert hu'.root T)).insert (.bnd 0) _)
          (OutLeg.bodySubst θ hθ hc hΓ hΔ O Φ)) :=
  OutLeg.subst_retS_renameTm θ hθ hc hΓ hΔ hu hu' T hS O (.box A) Φ s s' hs

theorem Term.holeAt_congr_sig {Γ : Ctx} {A : VarType} {a₁ a₂ : Ann A} {t₁ : Term σ Γ A a₁}
    {t₂ : Term σ Γ A a₂} (h : (⟨a₁, t₁⟩ : Σ b, Term σ Γ A b) = ⟨a₂, t₂⟩) {B : VarType}
    {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    (⟨_, Term.holeAt t₁ s⟩ : Σ c, Term σ Γ B c) = ⟨_, Term.holeAt t₂ s⟩ := by
  cases h
  rfl

/-- Substituting `back_ret`'s body: the slot is fixed and the carrier's term goes as the leg's `□`
    view does. -/
theorem OutLeg.subst_backRetBody {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) (O : OutLeg Γ) {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A}
    (bd : Term σ O.view.boxIn A a₀) :
    OutLeg.bodySubst θ hθ hc hΓ hΔ O (WFF.backRetBody (OutLeg.slotsFrom hΓ O) hA bd) =
      WFF.backRetBody (OutLeg.slotsFrom hΔ (O.subst θ hθ hc)) hA
        (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
          (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd) := by
  unfold OutLeg.bodySubst WFF.backRetBody
  rw [WFF.subst_eqRec_gen]
  refine eqRec_congr ?_ ?_
  · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ 0 0 _ _)
  · refine (sig_subst _ _ _ (Term.sigma_castAnn (A := .VTypeBox A) hA _).symm).trans ?_
    refine (Term.subst_under_mono (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)
      (OutLeg.slotsFrom hΓ O) (OutLeg.slotsFrom hΔ _) _ (Term.boxtm bd)).trans ?_
    exact Term.sigma_castAnn (A := .VTypeBox A) hA _

/-- Substituting `back_ret`'s conclusion, the fresh value equal to `t`. -/
theorem WFF.subst_backRet_eq {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hΔ : Δ.SlotsFrom 0) {u u' : ℕ} (hu : Γ.RootFresh (.free u)) (hu' : Δ.RootFresh (.free u'))
    {A : VarType} (hA : A.diaFree = true) {a : Ann A} (t : Term σ Γ A a) :
    WFF.subst (Subst.renameTmIdx σ ι u u' A hu'.root) (θ.renameTm u u' A hu'.root)
        (Subst.ok_renameTm hθ A hu'.root) (Subst.coh_renameTm hθ hc hu A hu'.root)
        (hΓ.insertFree u A) (hΔ.insertFree u' A)
        (eqRec A (Term.eta (.root (.free u)) A (Ctx.ref_insert_root Γ (.free u) A))
          (Term.castAnn hA (Term.weaken hu.root A t))) =
      eqRec A (Term.eta (.root (.free u')) A (Ctx.ref_insert_root Δ (.free u') A))
        (Term.castAnn hA (Term.weaken hu'.root A (Term.subst ι θ hθ hc t))) := by
  rw [WFF.subst_eqRec_gen]
  refine eqRec_congr (Term.subst_eta_tm _ _ _ A (.root (.free u))
    (Ctx.ref_insert_root Γ (.free u) A) _ (Subst.at_renameTm_root θ u u' A hu'.root)) ?_
  refine (sig_subst _ _ _ (Term.sigma_castAnn hA _).symm).trans ?_
  exact (Term.subst_mono_renameTm_sigma θ hθ hc hu hu' A t).trans (Term.sigma_castAnn hA _)

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
  | _, _, _, @Proof.four_dia _ _ Γ _ hF _ x hx φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      have hk₂ : ι (.step x .keep) = .step (ι x) .keep :=
        hx.elim fun _ hX => Subst.coh_keep_dia hθ hc hX
      have hwk : (θ.box.at (.step x .keep)).idxAlong [] = .step (ι x) .keep :=
        hx.elim fun _ hX => Subst.idx_box_keep_dia hF hθ hc hX
      Proof.conv
        (congrArg (fun χ => WFF.box (WFF.neg χ))
          ((WFF.subst_dia θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
            Ctx.NoSlots.slots (Ctx.exists_keep_dia hF hx) _ hk₂ (Ctx.exists_keep_dia hF hy)
            (Subst.ok_dia (Subst.ok_box hθ) (Ctx.exists_keep_dia hF hx) hwk)
            (hk₂ ▸ Subst.coh_dia (Subst.ok_box hθ) (Subst.coh_box hθ hc)
              (Ctx.exists_keep_dia hF hx))
            Ctx.NoSlots.slots
            (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots φ).neg).trans
            (congrArg (fun χ => WFF.dia _ _ (WFF.neg χ))
              (WFF.shift_subst (Ctx.shifts_diaIn_keep hF Γ x)
                (Ctx.shifts_diaIn_keep hF Γ' (ι x)) (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw)
                (Subst.coh_dia hθ hc hx) _ _ _ (hΓ.diaIn x) Ctx.NoSlots.slots
                Ctx.NoSlots.slots Ctx.NoSlots.slots
                (Subst.shiftCorr_dia_keep hF hθ hx hw) φ)).symm).symm)
        (Proof.four_dia hF hy (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.five_box _ _ _ _ hF hV _ φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      Proof.five_box hF hV (Proof.conv
        (congrArg (fun χ => WFF.neg (WFF.box (WFF.neg (WFF.box χ))))
          (WFF.shift_subst (Ctx.shifts_boxIn_boxIn hF _) (Ctx.shifts_boxIn_boxIn hF Γ')
            θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ.box.box
            (Subst.ok_box (Subst.ok_box hθ)) (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc))
            hΓ.boxIn hΓ.boxIn.boxIn Ctx.NoSlots.slots Ctx.NoSlots.slots
            (Subst.shiftCorr_box_box hF hθ) φ).symm)
        (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.five_dia _ _ Γ _ hF hV _ x hx φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      have hk₂ : ι (.step x .keep) = .step (ι x) .keep :=
        hx.elim fun _ hX => Subst.coh_keep_dia hθ hc hX
      have hwk : (θ.box.at (.step x .keep)).idxAlong [] = .step (ι x) .keep :=
        hx.elim fun _ hX => Subst.idx_box_keep_dia hF hθ hc hX
      Proof.conv
        (congrArg WFF.box
          ((WFF.subst_dia θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn
            Ctx.NoSlots.slots (Ctx.exists_keep_dia hF hx) _ hk₂ (Ctx.exists_keep_dia hF hy)
            (Subst.ok_dia (Subst.ok_box hθ) (Ctx.exists_keep_dia hF hx) hwk)
            (hk₂ ▸ Subst.coh_dia (Subst.ok_box hθ) (Subst.coh_box hθ hc)
              (Ctx.exists_keep_dia hF hx))
            Ctx.NoSlots.slots
            (WFF.shift (Ctx.shifts_diaIn_keep hF Γ x) Ctx.NoSlots.slots φ)).trans
            (congrArg (fun χ => WFF.dia _ _ χ)
              (WFF.shift_subst (Ctx.shifts_diaIn_keep hF Γ x)
                (Ctx.shifts_diaIn_keep hF Γ' (ι x)) (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw)
                (Subst.coh_dia hθ hc hx) _ _ _ (hΓ.diaIn x) Ctx.NoSlots.slots
                Ctx.NoSlots.slots Ctx.NoSlots.slots
                (Subst.shiftCorr_dia_keep hF hθ hx hw) φ)).symm).symm)
        (Proof.five_dia hF hV hy (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.here_keep _ _ Γ _ Δ hT hF x hx A a bd, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (WFF.subst_hereKeep hT hF θ hθ hc hΓ hx hw hy bd).symm
        (Proof.here_keep hT hF (ι x) hy _)
  | _, _, _, @Proof.keep_lift _ _ Γ _ Δ hF T hl O φ c cfr ψ p q, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hu' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ihq := Proof.subst q (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) T)
        (θ.rename c _ T hu'.root) (Subst.ok_rename hθ T hu'.root)
        (Subst.coh_rename hθ hc cfr T hu'.root) (hΓ.insertFree c T)
      Proof.keep_lift hF hl (O.subst θ hθ hc) (OutLeg.bodySubst θ hθ hc hΓ hΓ' O φ) _ hu'
        (Proof.conv (OutLeg.subst_dia θ hθ hc hΓ hΓ' O (WFF.ex T φ))
          (Proof.subst p θ hθ hc hΓ))
        (Proof.conv (WFF.subst_weaken_rename θ hθ hc hΓ hΓ' cfr hu' T ψ)
          (Proof.castHyps
            (by
              rw [List.map_cons, List.map_map, List.map_map]
              exact congrArg₂ List.cons
                (WFF.subst_liftRead_rename θ hθ hc hΓ hΓ' cfr hu' hF
                  (VarType.liftable_of_R hl) O φ)
                (List.map_congr_left fun χ _ =>
                  WFF.subst_weaken_rename θ hθ hc hΓ hΓ' cfr hu' T χ))
            ihq))
  | _, _, _, @Proof.T_dia _ _ _ _ hT hS A _ t c hcf _ _ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hcf' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.subst p (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) (.VTypeDia A))
        (θ.renameTm c _ (.VTypeDia A) hcf'.root) (Subst.ok_renameTm hθ (.VTypeDia A) hcf'.root)
        (Subst.coh_renameTm hθ hc hcf (.VTypeDia A) hcf'.root) (hΓ.insertFree c (.VTypeDia A))
      Proof.T_dia hT hS A (Term.subst ι θ hθ hc t) (Ctx.Presented.bound Γ') hcf'
        (Proof.castHyps
          (by
            simp only [List.map_cons, List.map_map, Function.comp_def]
            exact congrArg₂ List.cons
              (WFF.subst_hereAt_renameTm hT θ hθ hc hΓ hΓ' hcf hcf' t)
              (List.map_congr_left fun χ _ =>
                WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' (.VTypeDia A) χ))
          (Proof.conv (WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' (.VTypeDia A) _) ih))
  | _, _, _, @Proof.here_elim _ _ Γ _ _ hT x hx A a t a₁ bd ψ ph pb, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (WFF.subst_hereRead hT θ hθ hc hΓ hΓ' t ψ).symm
        (Proof.here_elim hT (ι x) hy (Term.subst ι θ hθ hc t)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) _
          (Proof.subst ph θ hθ hc hΓ)
          (Proof.conv (congrArg (WFF.boxx (ι x) hy)
            (WFF.subst_viewReadTm θ hθ hc hΓ hΓ' (ι x) (Subst.ok_dia hθ hx hw)
              (Subst.coh_dia hθ hc hx) (hΓ'.diaIn (ι x)) bd ψ))
            (Proof.subst pb θ hθ hc hΓ)))
  | _, _, _, @Proof.here_intro _ _ Γ _ _ hT x hx A a t a₁ bd ψ ph pr, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (congrArg (WFF.dia (ι x) hy)
          (WFF.subst_viewReadTm θ hθ hc hΓ hΓ' (ι x) (Subst.ok_dia hθ hx hw)
            (Subst.coh_dia hθ hc hx) (hΓ'.diaIn (ι x)) bd ψ).symm)
        (Proof.here_intro hT (ι x) hy (Term.subst ι θ hθ hc t)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) _
          (Proof.subst ph θ hθ hc hΓ)
          (Proof.conv (WFF.subst_hereRead hT θ hθ hc hΓ hΓ' t ψ) (Proof.subst pr θ hθ hc hΓ)))
  | _, _, _, @Proof.here_beta _ _ Γ _ _ hT x hx A a t a₁ bd B b s ph, Γ', _, ι, θ, hθ,
      hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv
        (WFF.here_congr hT
          (sig_diatm
            (Term.subst_viewReadTm_sig θ hθ hc hΓ hΓ' (ι x) (Subst.ok_dia hθ hx hw)
              (Subst.coh_dia hθ hc hx) (hΓ'.diaIn (ι x)) bd s).symm)
          (Term.subst_hereRead_sig hT θ hθ hc hΓ hΓ' t s).symm)
        (Proof.here_beta hT (ι x) hy (Term.subst ι θ hθ hc t)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd) _
          (Proof.subst ph θ hθ hc hΓ))
  | _, _, _, @Proof.here_name _ _ Γ _ _ hT x hx B β bd p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (WFF.subst_hereEx hT θ hθ hc hΓ hΓ' (Term.diatm x hx bd)).symm
        (Proof.here_name hT (ι x) hy
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd)
          (Proof.subst p θ hθ hc hΓ))
  | _, _, _, @Proof.here_subst _ _ Γ _ _ hT A b s a a' t t' φ ph ph' pf, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t' φ).symm
        (Proof.here_subst hT (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
          (Term.subst ι θ hθ hc t') _ (Proof.subst ph θ hθ hc hΓ) (Proof.subst ph' θ hθ hc hΓ)
          (Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ) (Proof.subst pf θ hθ hc hΓ)))
  | _, _, _, @Proof.here_eq _ _ Γ _ _ hT A b s a t t' ph pe, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.here_eq hT (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
        (Term.subst ι θ hθ hc t') (Proof.subst ph θ hθ hc hΓ)
        (Proof.conv (WFF.subst_eqRec_gen θ hθ hc hΓ hΓ' A t t') (Proof.subst pe θ hθ hc hΓ))
  | _, _, _, @Proof.back_counit _ _ Γ _ _ hS O A a₀ bd a t ψ pb pd, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ' t ψ).symm
        (Proof.back_counit hS (O.subst θ hθ hc)
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t) ψ
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t) (Proof.subst pb θ hθ hc hΓ))
          (Proof.conv ((OutLeg.subst_dia θ hθ hc hΓ hΓ' O (WFF.box (WFF.holeRead bd ψ))).trans
              (congrArg (fun φ => (O.subst θ hθ hc).dia (WFF.box φ))
                (WFF.subst_holeRead (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
                  (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) _ _ bd ψ)))
            (Proof.subst pd θ hθ hc hΓ)))
  | _, _, _, @Proof.back_unit _ _ Γ _ _ hS O A a₀ bd a t ψ pb pr, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv ((OutLeg.subst_box θ hθ hc hΓ hΓ' O
            ((WFF.box (WFF.holeRead bd ψ).neg).neg)).trans
          (congrArg (fun φ : WFF σ (O.subst θ hθ hc).view.boxIn 0 =>
              (O.subst θ hθ hc).box (WFF.box φ.neg).neg)
                (WFF.subst_holeRead (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
                  (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) _ _ bd ψ))).symm
        (Proof.back_unit hS (O.subst θ hθ hc)
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t) ψ
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t) (Proof.subst pb θ hθ hc hΓ))
          (Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ' t ψ) (Proof.subst pr θ hθ hc hΓ)))
  | _, _, _, @Proof.back_ne _ _ Γ _ _ hS O A a₀ bd a t pb, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (OutLeg.subst_dia θ hθ hc hΓ hΓ' O .top).symm
        (Proof.back_ne hS (O.subst θ hθ hc)
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t)
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t) (Proof.subst pb θ hθ hc hΓ)))
  | _, _, _, @Proof.back_beta _ _ Γ _ _ hS O A a₀ bd a t B b s pb, Γ', _, ι, θ, hθ, hc,
      hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv ((OutLeg.subst_back θ hθ hc hΓ hΓ' hS O (Term.holeRead bd s)
            (Term.holeRead t s)).trans
          (OutLeg.back_congr hS _ (Term.subst_holeRead_sig _ _ _ bd s)
            (Term.subst_holeRead_sig θ hθ hc t s))).symm
        (Proof.back_beta hS (O.subst θ hθ hc)
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t) s
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t) (Proof.subst pb θ hθ hc hΓ)))
  | _, _, _, @Proof.back_pair _ _ Γ _ _ hS O A a₀ bd a t B b₀ bd' b t' pb pb', Γ', _, ι, θ,
      hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O
          (Term.pair bd bd')
          (Term.pair t t')).symm
        (Proof.back_pair hS (O.subst θ hθ hc)
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t)
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd')
          (Term.subst ι θ hθ hc t')
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t) (Proof.subst pb θ hθ hc hΓ))
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd' t')
            (Proof.subst pb' θ hθ hc hΓ)))
  | _, _, _, @Proof.back_eq _ _ Γ _ _ hS L A b s a t t' pb pe, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.back_eq hS L (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
        (Term.subst ι θ hθ hc t') (Proof.subst pb θ hθ hc hΓ)
        (Proof.conv (WFF.subst_eqRec_gen θ hθ hc hΓ hΓ' A t t') (Proof.subst pe θ hθ hc hΓ))
  | _, _, _, @Proof.back_eqC _ _ Γ _ _ hS L A b s s' a t pb pe, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.back_eqC hS L (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc s')
        (Term.subst ι θ hθ hc t) (Proof.subst pb θ hθ hc hΓ)
        (Proof.conv (WFF.subst_eqRec_gen θ hθ hc hΓ hΓ' (L.carrier A) s s')
          (Proof.subst pe θ hθ hc hΓ))
  | _, _, _, @Proof.back_here _ _ Γ _ _ hS hT A a₀ bd a t φ pb pφ, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_backHere hT θ hθ hc hΓ hΓ' bd φ).symm
        (Proof.back_here hS hT
          (Term.subst ι θ.box.box (Subst.ok_box (Subst.ok_box hθ))
            (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc)) bd)
          (Term.subst ι θ hθ hc t) _
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS .nec bd t)
            (Proof.subst pb θ hθ hc hΓ))
          (Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ) (Proof.subst pφ θ hθ hc hΓ)))
  | _, _, _, @Proof.back_keep _ _ Γ _ _ hS hT hF O A a b pne, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hb := Subst.ok_box hθ
      have hcb := Subst.coh_box hθ hc
      have hmono : ∀ {B : VarType} {Δ₁ Δ₂ : Ctx} (e : Δ₁.Le Δ₂) {u u' : Σ c, Term σ Δ₁ B c},
          u = u' → (⟨_, Term.mono e u.2⟩ : Σ c, Term σ Δ₂ B c) = ⟨_, Term.mono e u'.2⟩ := by
        intro B Δ₁ Δ₂ e u u' h
        cases h
        rfl
      Proof.conv
        ((OutLeg.back_congr hS (O.subst θ hθ hc)
          ((OutLeg.subst_mono_view θ hθ hc O (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b)).trans
            (hmono _ (Term.shift_subst (Ctx.shifts_boxIn_boxIn hF Γ)
              (Ctx.shifts_boxIn_boxIn hF Γ') θ.box hb hcb θ.box.box (Subst.ok_box hb)
              (Subst.coh_box hb hcb) (Subst.shiftCorr_box_box hF hθ) b).symm)).symm
          (Term.collapse_subst (Ctx.collapses_boxIn_self hT Γ)
            (Ctx.collapses_boxIn_self hT Γ') θ.box hb hcb θ hθ hc
            (Subst.corr_box_self hT hθ) b)).trans
          (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O _ _).symm)
        (Proof.back_keep hS hT hF (O.subst θ hθ hc) (Term.subst ι θ.box hb hcb b)
          (Proof.conv (OutLeg.subst_dia θ hθ hc hΓ hΓ' O .top) (Proof.subst pne θ hθ hc hΓ)))
  | _, _, _, @Proof.back_ret _ _ Γ _ hS hB O A hA a₀ bd a t c hcf _ pne p, Γ', _, ι, θ, hθ,
      hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hcf' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.subst p (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) A)
        (θ.renameTm c _ A hcf'.root) (Subst.ok_renameTm hθ A hcf'.root)
        (Subst.coh_renameTm hθ hc hcf A hcf'.root) (hΓ.insertFree c A)
      Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t).symm
        (Proof.back_ret hS hB (O.subst θ hθ hc) hA
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t) (Ctx.Presented.bound Γ') hcf'
          (Proof.conv (OutLeg.subst_dia θ hθ hc hΓ hΓ' O .top) (Proof.subst pne θ hθ hc hΓ))
          (Proof.castHyps
            (by
              simp only [List.map_cons, List.map_map, Function.comp_def]
              exact congrArg₂ List.cons
                ((OutLeg.subst_ret_renameTm θ hθ hc hΓ hΓ' hcf hcf' A hS O _ _ _
                  (Term.subst_eta_tm _ _ _ A (.root (.free c))
                    (Ctx.ref_insert_root Γ (.free c) A) _
                    (Subst.at_renameTm_root θ c _ A hcf'.root))).trans
                  (by rw [OutLeg.subst_backRetBody]))
                (List.map_congr_left fun χ _ =>
                  WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' A χ))
            (Proof.conv (WFF.subst_backRet_eq θ hθ hc hΓ hΓ' hcf hcf' hA t) ih)))
  | _, _, _, @Proof.B_strong _ _ _ _ hS A _ t c hcf _ _ pne p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hcf' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.subst p
        (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) (.VTypeBox (.VTypeBox A)))
        (θ.renameTm c _ (.VTypeBox (.VTypeBox A)) hcf'.root)
        (Subst.ok_renameTm hθ (.VTypeBox (.VTypeBox A)) hcf'.root)
        (Subst.coh_renameTm hθ hc hcf (.VTypeBox (.VTypeBox A)) hcf'.root)
        (hΓ.insertFree c (.VTypeBox (.VTypeBox A)))
      Proof.B_strong hS (Term.subst ι θ hθ hc t) (Ctx.Presented.bound Γ') hcf'
        (Proof.conv (OutLeg.subst_dia θ hθ hc hΓ hΓ' .nec .top) (Proof.subst pne θ hθ hc hΓ))
        (Proof.castHyps
          (by
            simp only [List.map_cons, List.map_map, Function.comp_def]
            exact congrArg₂ List.cons
              (WFF.subst_backEta_renameTm hS θ hθ hc hΓ hΓ' hcf hcf' t)
              (List.map_congr_left fun χ _ =>
                WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' (.VTypeBox (.VTypeBox A)) χ))
          (Proof.conv
            (WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' (.VTypeBox (.VTypeBox A)) _) ih))
  | _, _, _, @Proof.ret_new _ _ Γ _ hS hB O A Φ c hcf _ _ pd p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hcf' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.subst p (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) A)
        (θ.renameTm c _ A hcf'.root) (Subst.ok_renameTm hθ A hcf'.root)
        (Subst.coh_renameTm hθ hc hcf A hcf'.root) (hΓ.insertFree c A)
      Proof.ret_new hS hB (O.subst θ hθ hc) (OutLeg.bodySubst θ hθ hc hΓ hΓ' O Φ)
        (Ctx.Presented.bound Γ') hcf'
        (Proof.conv (OutLeg.subst_dia θ hθ hc hΓ hΓ' O _) (Proof.subst pd θ hθ hc hΓ))
        (Proof.castHyps
          (by
            simp only [List.map_cons, List.map_map, Function.comp_def]
            exact congrArg₂ List.cons
              (OutLeg.subst_ret_renameTm θ hθ hc hΓ hΓ' hcf hcf' A hS O Φ _ _
                (Term.subst_eta_tm _ _ _ A (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) A) _
                  (Subst.at_renameTm_root θ c _ A hcf'.root)))
              (List.map_congr_left fun χ _ =>
                WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' A χ))
          (Proof.conv (WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' A _) ih))
  | _, _, _, @Proof.ret_extS _ _ Γ _ hS O S B a t Φ c hcf _ _ pr p, Γ', _, ι, θ, hθ, hc,
      hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hcf' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.subst p (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) B)
        (θ.renameTm c _ B hcf'.root) (Subst.ok_renameTm hθ B hcf'.root)
        (Subst.coh_renameTm hθ hc hcf B hcf'.root) (hΓ.insertFree c B)
      Proof.ret_extS hS (O.subst θ hθ hc) (Term.subst ι θ hθ hc t) _ (Ctx.Presented.bound Γ')
        hcf' (Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O S t _) (Proof.subst pr θ hθ hc hΓ))
        (Proof.castHyps
          (by
            simp only [List.map_cons, List.map_map, Function.comp_def]
            exact congrArg₂ List.cons
              ((OutLeg.subst_retS_renameTm θ hθ hc hΓ hΓ' hcf hcf' B hS O (S.ext B) _
                (S.extTm (Term.weaken hcf.root B t)
                  (Term.eta (.root (.free c)) B (Ctx.ref_insert_root Γ (.free c) B))).2 _
                (RShape.subst_extTm_sig _ _ _ S _ _
                  (Term.subst_mono_renameTm_sigma θ hθ hc hcf hcf' B t)
                  (Term.subst_eta_tm _ _ _ B (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) B)
                    _ (Subst.at_renameTm_root θ c _ B hcf'.root)))).trans
                (OutLeg.retS_congr' hS _ _ rfl (congrArg (WFF.mono _)
                  ((WFF.subst_bodySplit (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
                      (O.viewCoh θ hθ hc) _ _ Φ).trans
                    (WFF.bodySplit_congr
                      (RShape.subst_extL (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
                        (O.viewCoh θ hθ hc) S B)
                      (RShape.subst_extR (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
                        (O.viewCoh θ hθ hc) S B) _)))))
              (List.map_congr_left fun χ _ =>
                WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' B χ))
          (Proof.conv (WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' B _) ih))
  | _, _, _, @Proof.ret_compS _ _ Γ _ hS O S A cs h p h' a t Φ c hcf _ _ pr pf, Γ', _, ι, θ,
      hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hcf' : Γ'.RootFresh (.free (Ctx.Presented.bound Γ')) :=
        Ctx.Presented.fresh_bound _ le_rfl
      have ih := Proof.subst pf
        (Γ' := Γ'.insert (.free (Ctx.Presented.bound Γ')) ((A.compAt p).getD .VTypeOne))
        (θ.renameTm c _ _ hcf'.root) (Subst.ok_renameTm hθ _ hcf'.root)
        (Subst.coh_renameTm hθ hc hcf _ hcf'.root) (hΓ.insertFree c _)
      Proof.ret_compS hS (O.subst θ hθ hc) S p h' (Term.subst ι θ hθ hc t) _
        (Ctx.Presented.bound Γ') hcf'
        (Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O _ t _) (Proof.subst pr θ hθ hc hΓ))
        (Proof.castHyps
          (by
            simp only [List.map_cons, List.map_map, Function.comp_def]
            exact congrArg₂ List.cons
              ((OutLeg.subst_retS_renameTm θ hθ hc hΓ hΓ' hcf hcf' _ hS O
                (S.withNec (.boxC A (p :: cs) h')) _
                (RShape.compTm A cs h p h' S (Term.weaken hcf.root _ t)
                  (Term.eta (.root (.free c)) _ (Ctx.ref_insert_root Γ (.free c) _))).2 _
                (RShape.subst_compTm_sig _ _ _ A cs h p h' S _ _
                  (Term.subst_mono_renameTm_sigma θ hθ hc hcf hcf' _ t)
                  (Term.subst_eta_tm _ _ _ _ (.root (.free c)) (Ctx.ref_insert_root Γ (.free c) _)
                    _ (Subst.at_renameTm_root θ c _ _ hcf'.root)))).trans
                (OutLeg.retS_congr' hS _ _ rfl (congrArg (WFF.mono _)
                  ((WFF.subst_bodyRepl (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
                      (O.viewCoh θ hθ hc) _ Φ).trans
                    (WFF.bodyRepl_congr
                      (RShape.subst_compL (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
                        (O.viewCoh θ hθ hc) A cs h p h' S) _)))))
              (List.map_congr_left fun χ _ =>
                WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' _ χ))
          (Proof.conv (WFF.subst_weaken_renameTm θ hθ hc hΓ hΓ' hcf hcf' _ _) ih))
  | _, _, _, @Proof.ret_map _ _ Γ _ _ hS O S T F a y Φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv ((OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (S.withNec T) _ Φ).trans
          (OutLeg.retS_congr hS _ (S.withNec T)
            (Term.subst_holeRead_sig θ hθ hc y (ShapeMap.liftVal S F).2) rfl)).symm
        (Proof.ret_map hS (O.subst θ hθ hc) F (Term.subst ι θ hθ hc y) _
          (Proof.conv ((OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O S y _).trans
            (OutLeg.retS_congr' hS _ S rfl
              ((WFF.subst_bodyRepl (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)
                  _ Φ).trans
                (WFF.bodyRepl_congr (Term.subst_under_closed (O.viewSubst θ hθ hc)
                  (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc) (OutLeg.slotsFrom hΓ O)
                  (OutLeg.slotsFrom hΓ' _) (ShapeMap.liftObj S F).2) _))))
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_mapD _ _ Γ _ _ hS O C X Z cs hcs b h a y Φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv ((OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.wit (.boxC C cs hcs) Z) _ Φ).trans
          (OutLeg.retS_congr hS _ (.wit (.boxC C cs hcs) Z)
            (Term.subst_holeRead_sig θ hθ hc y (ShapeMap.possValC h cs hcs).2) rfl)).symm
        (Proof.ret_mapD hS (O.subst θ hθ hc) h (Term.subst ι θ hθ hc y) _
          (Proof.conv ((OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.wit (.boxC C cs hcs) X) y _).trans
            (OutLeg.retS_congr' hS _ (.wit (.boxC C cs hcs) X) rfl
              ((WFF.subst_bodyRepl (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)
                  _ Φ).trans
                (WFF.bodyRepl_congr (Term.subst_under_closed (O.viewSubst θ hθ hc)
                  (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc) (OutLeg.slotsFrom hΓ O)
                  (OutLeg.slotsFrom hΓ' _) (ShapeMap.possObj h).2) _))))
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_realise _ _ Γ _ _ hS hW O N X a y c₀ c Φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv ((OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.wit N X) _ _).trans
          (OutLeg.retS_congr' hS _ (.wit N X) rfl
            ((WFF.subst_bodyRepl (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)
                _ Φ).trans
              (WFF.bodyRepl_congr (RShape.subst_realL (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
                (O.viewCoh θ hθ hc) N X) _)))).symm
        (Proof.ret_realise hS hW (O.subst θ hθ hc) N (Term.subst ι θ hθ hc y)
          (Term.subst ι θ hθ hc c) _
          (Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.nec N) y Φ)
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_keep _ _ Γ _ _ hS hT hF O N x hx A b₀ bd c₀ c a y Φ ph p, Γ', _, ι, θ, hθ,
      hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.wit N A) _ Φ).symm
        (Proof.ret_keep hS hT hF (O.subst θ hθ hc) N (ι x) hy
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd)
          (Term.subst ι θ hθ hc c) (Term.subst ι θ hθ hc y) _
          (Proof.subst ph θ hθ hc hΓ)
          (Proof.conv ((OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.nec N) y _).trans
              (OutLeg.retS_congr' hS _ (.nec N) rfl
                ((WFF.subst_bodyRepl (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)
                    _ Φ).trans
                  (WFF.bodyRepl_congr (RShape.subst_keepL hF θ hθ hc O N hx hw hy bd) _))))
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_counit _ _ Γ _ _ hS O A a t ψ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ' t ψ).symm
        (Proof.ret_counit hS (O.subst θ hθ hc) (Term.subst ι θ hθ hc t) ψ
          (Proof.conv (by
              refine (OutLeg.subst_ret θ hθ hc hΓ hΓ' hS O t _).trans
                (congrArg ((O.subst θ hθ hc).ret hS (Term.subst ι θ hθ hc t))
                  ((OutLeg.subst_lift θ hθ hc hΓ hΓ' O _).trans
                    (congrArg (O.subst θ hθ hc).lift ?_)))
              exact congrArg WFF.box ((WFF.subst_holeAt _ _ _ _ _ _ ψ).trans
                (WFF.holeAt_congr _ (Term.subst_eta_renAt _ _ _ A _ _ _ _
                  (Subst.box_at_inner_ren _ (Subst.under_at_root _ _ _))) ψ)))
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_counitC _ _ Γ _ _ hS O A C a y c₀ bd c t ψ pr pb, Γ', _, ι, θ, hθ, hc,
      hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ' (Term.pair y t) ψ).symm
        (Proof.ret_counitC hS (O.subst θ hθ hc) (Term.subst ι θ hθ hc y)
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t) ψ
          (Proof.conv (by
              refine (OutLeg.subst_ret θ hθ hc hΓ hΓ' hS O y _).trans
                (congrArg ((O.subst θ hθ hc).ret hS (Term.subst ι θ hθ hc y))
                  (congrArg WFF.box ?_))
              refine (WFF.subst_holeAt _ _ _ _ _ _ ψ).trans (WFF.holeAt_congr _ ?_ ψ)
              exact sig_pair
                (Term.subst_eta_renAt _ _ _ A _ _ _ _
                  (Subst.box_at_inner_ren _ (Subst.under_at_root _ _ _)))
                (Term.subst_box_under_mono (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
                  (O.viewCoh θ hθ hc) (OutLeg.slotsFrom hΓ O)
                  (OutLeg.slotsFrom hΓ' (O.subst θ hθ hc)) _ bd))
            (Proof.subst pr θ hθ hc hΓ))
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t)
            (Proof.subst pb θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_unitC _ _ Γ _ _ hS O C A co ho c y Ψ a₀ sb cs h ψ p q, Γ', _, ι, θ, hθ,
      hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (by
          refine ((OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.nec (.boxC C co ho)) y _).trans
            (congrArg ((O.subst θ hθ hc).retS hS (.nec (.boxC C co ho)) (Term.subst ι θ hθ hc y))
              ?_)).symm
          exact congrArg (WFF.and _) ((OutLeg.subst_lift θ hθ hc hΓ hΓ' O _).trans
            (congrArg (O.subst θ hθ hc).lift
              (WFF.subst_unitBodyC θ hθ hc hΓ hΓ' hS co ho sb cs h ψ))))
        (Proof.ret_unitC hS (O.subst θ hθ hc) co ho (Term.subst ι θ hθ hc y) _
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) cs h ψ
          (Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.nec (.boxC C co ho)) y Ψ)
            (Proof.subst p θ hθ hc hΓ))
          (Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ' (Term.pair y (Term.boxtm sb)) ψ)
            (Proof.subst q θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_unitWC _ _ Γ _ _ hS x hx C A X co ho c y Ψ a₀ sb b₀ u cs h ψ p q, Γ', _,
      ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (WFF.retxS_congr' hS (ι x) hy (.nec (.boxC C co ho)) rfl (congrArg (WFF.and _)
          (WFF.subst_unitBodyWC θ hθ hc hΓ hS (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
            (hΓ'.diaIn (ι x)) co ho sb u cs h ψ))).symm
        (Proof.ret_unitWC hS hy co ho (Term.subst ι θ hθ hc y) _
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) u) cs h
          ψ
          (Proof.subst p θ hθ hc hΓ)
          (Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ'
              (Term.pair y (Term.pair (Term.boxtm sb) (Term.diatm x hx u))) ψ)
            (Proof.subst q θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_unitDC _ _ Γ _ _ hS O C X A co ho c y Ψ a₀ sb cs h ψ p q, Γ', _, ι, θ,
      hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (by
          refine ((OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.wit (.boxC C co ho) X) y _).trans
            (congrArg ((O.subst θ hθ hc).retS hS (.wit (.boxC C co ho) X)
              (Term.subst ι θ hθ hc y)) ?_)).symm
          exact congrArg (WFF.and _) ((OutLeg.subst_lift θ hθ hc hΓ hΓ' O _).trans
            (congrArg (O.subst θ hθ hc).lift
              (WFF.subst_unitBodyDC θ hθ hc hΓ hΓ' hS co ho sb cs h ψ))))
        (Proof.ret_unitDC hS (O.subst θ hθ hc) co ho (Term.subst ι θ hθ hc y) _
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) cs h ψ
          (Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O (.wit (.boxC C co ho) X) y Ψ)
            (Proof.subst p θ hθ hc hΓ))
          (Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ' (Term.pair y (Term.boxtm sb)) ψ)
            (Proof.subst q θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_unitWDC _ _ Γ _ _ hS x hx C Xe A X co ho c y Ψ a₀ sb b₀ u cs h ψ p q,
      Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (WFF.retxS_congr' hS (ι x) hy (.wit (.boxC C co ho) Xe) rfl
          (congrArg (WFF.and _)
          (WFF.subst_unitBodyWDC θ hθ hc hΓ hS (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
            (hΓ'.diaIn (ι x)) co ho sb u cs h ψ))).symm
        (Proof.ret_unitWDC hS hy co ho (Term.subst ι θ hθ hc y) _
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) u) cs h
          ψ
          (Proof.subst p θ hθ hc hΓ)
          (Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ'
              (Term.pair y (Term.pair (Term.boxtm sb) (Term.diatm x hx u))) ψ)
            (Proof.subst q θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_counitD _ _ Γ _ _ hS C X c y ψ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.subst_holeRead θ hθ hc hΓ hΓ' y ψ).symm
        (Proof.ret_counitD hS (Term.subst ι θ hθ hc y) ψ
          (Proof.conv (WFF.retS_congr' hS _ rfl (WFF.subst_counitBodyD θ hθ hc hΓ hΓ' ψ))
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_monoS _ _ Γ _ _ hS O S a t Φ Φ' p q, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O S t Φ').symm
        (Proof.ret_monoS hS (O.subst θ hθ hc) (Term.subst ι θ hθ hc t) _ _
          (Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O S t Φ) (Proof.subst p θ hθ hc hΓ))
          (Proof.conv (OutLeg.subst_box θ hθ hc hΓ hΓ' O _) (Proof.subst q θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_diaS _ _ Γ _ _ hS O S a t Φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (OutLeg.subst_dia θ hθ hc hΓ hΓ' O _).symm
        (Proof.ret_diaS hS (O.subst θ hθ hc) (Term.subst ι θ hθ hc t) _
          (Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O S t Φ) (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_eqS _ _ Γ _ _ hS O S a t t' Φ p q, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O S t' Φ).symm
        (Proof.ret_eqS hS (O.subst θ hθ hc) (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc t') _
          (Proof.conv (OutLeg.subst_retS θ hθ hc hΓ hΓ' hS O S t Φ) (Proof.subst p θ hθ hc hΓ))
          (Proof.conv (WFF.subst_eqRec_gen θ hθ hc hΓ hΓ' S.flat t t')
            (Proof.subst q θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_hereC _ _ Γ _ _ hS hT A a₀ sb cs h Φ p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.retS_congr hS _ ((sig_collapse (Ctx.collapses_boxIn_self hT Γ')
          (subst_compsVal_sig θ hθ hc sb cs h).symm).trans
          (Term.collapse_subst (Ctx.collapses_boxIn_self hT Γ)
          (Ctx.collapses_boxIn_self hT Γ') θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ hc
          (Subst.corr_box_self hT hθ) (compsVal sb cs h).2)) rfl)
        (Proof.ret_hereC hS hT (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) cs h
          (WFF.bodySubst θ hθ hc hΓ hΓ' Φ)
          (Proof.conv (WFF.subst_hereRead hT θ hθ hc hΓ hΓ' (Term.boxtm sb) Φ)
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_hereWC _ _ Γ _ _ hS hT A Y a₀ sb cs h b pt c u Φ ph p, Γ', _, ι, θ, hθ,
      hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (WFF.retS_congr hS _ (sig_pair ((sig_collapse (Ctx.collapses_boxIn_self hT Γ')
          (subst_compsVal_sig θ hθ hc sb cs h).symm).trans
          (Term.collapse_subst (Ctx.collapses_boxIn_self hT Γ)
          (Ctx.collapses_boxIn_self hT Γ') θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ hc
          (Subst.corr_box_self hT hθ) (compsVal sb cs h).2)) rfl) rfl)
        (Proof.ret_hereWC hS hT (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb)
          cs h (Term.subst ι θ hθ hc pt) (Term.subst ι θ hθ hc u)
          (WFF.bodySubst θ hθ hc hΓ hΓ' Φ) (Proof.subst ph θ hθ hc hΓ)
          (Proof.conv (WFF.subst_hereRead hT θ hθ hc hΓ hΓ' (Term.pair (Term.boxtm sb) pt) Φ)
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_hereXC _ _ Γ _ _ hS hT x hx X A a₁ bd a' t₀ a₀ sb cs h χ ph p, Γ', _, ι,
      θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (WFF.retxS_congr hS (ι x) hy _ ((sig_collapse (Ctx.collapses_boxIn_self hT Γ')
          (subst_compsVal_sig θ hθ hc sb cs h).symm).trans
          (Term.collapse_subst (Ctx.collapses_boxIn_self hT Γ)
          (Ctx.collapses_boxIn_self hT Γ') θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ hc
          (Subst.corr_box_self hT hθ) (compsVal sb cs h).2))
          (WFF.subst_viewBody θ hθ hc hΓ hΓ' hx hy bd χ).symm)
        (Proof.ret_hereXC hS hT (ι x) hy
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd)
          (Term.subst ι θ hθ hc t₀)
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) cs h
          (WFF.bodySubst θ hθ hc hΓ hΓ' χ) (Proof.subst ph θ hθ hc hΓ)
          (Proof.conv (WFF.subst_hereRead hT θ hθ hc hΓ hΓ' (Term.pair t₀ (Term.boxtm sb)) χ)
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_hereXWC _ _ Γ _ _ hS hT x hx X A Y a₁ bd a' t₀ a₀ sb cs h b pt c u χ
      ph php p, Γ', _, ι, θ, hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hy : ∃ X, Γ'.ref (ι x) = some (.VTypeDia X) :=
        hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw
      Proof.conv (WFF.retxS_congr hS (ι x) hy _
          (sig_pair ((sig_collapse (Ctx.collapses_boxIn_self hT Γ')
            (subst_compsVal_sig θ hθ hc sb cs h).symm).trans
            (Term.collapse_subst (Ctx.collapses_boxIn_self hT Γ)
            (Ctx.collapses_boxIn_self hT Γ') θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ
            hc (Subst.corr_box_self hT hθ) (compsVal sb cs h).2)) rfl)
          (WFF.subst_viewBody θ hθ hc hΓ hΓ' hx hy bd χ).symm)
        (Proof.ret_hereXWC hS hT (ι x) hy
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) bd)
          (Term.subst ι θ hθ hc t₀)
          (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) sb) cs h
          (Term.subst ι θ hθ hc pt) (Term.subst ι θ hθ hc u)
          (WFF.bodySubst θ hθ hc hΓ hΓ' χ) (Proof.subst ph θ hθ hc hΓ)
          (Proof.subst php θ hθ hc hΓ)
          (Proof.conv (WFF.subst_hereRead hT θ hθ hc hΓ hΓ'
              (Term.pair t₀ (Term.pair (Term.boxtm sb) pt)) χ)
            (Proof.subst p θ hθ hc hΓ)))
  | _, _, _, @Proof.back_hereX _ _ Γ _ _ hS hT y hy A a₀ bd a t a' t₀ φ pb ph pφ, Γ', _, ι, θ,
      hθ, hc, hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      let O : OutLeg Γ := .pos y hy
      Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t₀ φ).symm
        (Proof.back_hereX hS hT (ι y) _
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc t₀) _
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t) (Proof.subst pb θ hθ hc hΓ))
          (Proof.conv (WFF.here_congr hT (sig_diatm
              (Term.collapse_subst (Ctx.collapses_boxIn_self hT (Γ.diaIn y))
                (Ctx.collapses_boxIn_self hT (Γ'.diaIn (ι y))) (O.viewSubst θ hθ hc).box
                (Subst.ok_box (O.viewOk θ hθ hc)) (Subst.coh_box (O.viewOk θ hθ hc)
                  (O.viewCoh θ hθ hc))
                (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)
                (Subst.corr_box_self hT (O.viewOk θ hθ hc)) bd).symm) rfl)
            (Proof.subst ph θ hθ hc hΓ))
          (Proof.conv (WFF.subst_instantiate θ hθ hc hΓ hΓ' t φ) (Proof.subst pφ θ hθ hc hΓ)))
  | _, _, _, @Proof.ret_bridge _ _ Γ _ _ hS O A a₀ bd a t Φ pb pd, Γ', _, ι, θ, hθ, hc,
      hΓ =>
      have hΓ' : Γ'.SlotsFrom 0 := Ctx.NoSlots.slots
      Proof.conv (OutLeg.subst_ret θ hθ hc hΓ hΓ' hS O t Φ).symm
        (Proof.ret_bridge hS (O.subst θ hθ hc)
          (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
            (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
          (Term.subst ι θ hθ hc t) (OutLeg.bodySubst θ hθ hc hΓ hΓ' O Φ)
          (Proof.conv (OutLeg.subst_back θ hθ hc hΓ hΓ' hS O bd t) (Proof.subst pb θ hθ hc hΓ))
          (Proof.conv ((OutLeg.subst_dia θ hθ hc hΓ hΓ' O _).trans
              (congrArg (O.subst θ hθ hc).dia
                (WFF.subst_instantiate (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
                  (O.viewCoh θ hθ hc) (OutLeg.slotsFrom hΓ O) (OutLeg.slotsFrom hΓ' _)
                  (Term.boxtm bd) Φ)))
            (Proof.subst pd θ hθ hc hΓ)))

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


/-! ## Naming an object by an address -/

/-- ⭐Filling the slot of a naming equation: the slot's η-expansion becomes the term, and the value,
    weakened past the slot, comes back unchanged.  `◇`-free, which is where `WFF.subst_eqRec` lives
    and where naming is wanted (§2d). -/
theorem WFF.instantiate_eqRec_slot {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType}
    (hA : A.diaFree = true) {b : Ann A} (u : Term σ Γ A b)
    (t : Term σ Γ A (Ann.eta (.root (.bnd 0)) A)) :
    WFF.instantiate (d := 0) Ctx.NoSlots.slots u
        (eqRec A (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root Γ (.bnd 0) A))
          (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root A) t)) =
      eqRec A u (Term.castAnn hA t) := by
  rw [WFF.instantiate, WFF.substRoot, WFF.subst_eqRec _ _ _ _ _ A hA]
  refine eqRec_congr (Term.subst_eta_tm _ _ _ A (.root (.bnd 0)) _ u
    (Subst.at_single_root _ _)) ?_
  refine (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ t)).trans ?_
  refine ((Term.subst_ren (Ctx.Le.refl Γ) _ _ _ ?_ t).trans
    (congrArg (Sigma.mk _) (Term.mono_refl _ t))).trans (Term.sigma_castAnn hA t)
  intro v T hv
  exact Subst.single_at_ne
    (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)

/-- ⭐**Every object has a name**: the equation `η b = t` for a fresh `b` is provable's existential,
    so a witnessed theory contains an instance of it.  (The canonical model no longer needs naming:
    strong T reads `Ind` there, §10.41.) -/
def Proof.exists_eqRec_eta {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    {A : VarType} (hA : A.diaFree = true) (t : Term σ Γ A (Ann.eta (.root (.bnd 0)) A)) :
    Proof σ Γ Δ (.ex A (eqRec A (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root Γ (.bnd 0) A))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root A) t))) :=
  Proof.ex_intro A t
    (Proof.conv (WFF.instantiate_eqRec_slot hA t t).symm (Proof.eqRec_refl A t))

/-- ⭐Filling the slot of `Proof.here_name`'s existential: the subject, weakened past the slot, comes
    back unchanged, and the slot's η-expansion becomes the term.  So a witnessed theory containing
    `WFF.hereEx hT s` contains the atom `Here s (η b₀)` at a declared root — which is what
    `Canon.RealDatum` is made of (§10.13). -/
theorem WFF.instantiate_here_slot {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true)
    {B : VarType} {b : Ann (.VTypeDia B)} (s : Term σ Γ (.VTypeDia B) b) {β : Ann B}
    (u : Term σ Γ B β) :
    WFF.instantiate (d := 0) Ctx.NoSlots.slots u
        (WFF.here hT (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root B) s)
          (Term.eta (.root (.bnd 0)) B (Ctx.ref_insert_root Γ (.bnd 0) B))) =
      WFF.here hT s u := by
  rw [WFF.instantiate, WFF.substRoot]
  refine WFF.here_congr hT ?_ ?_
  · refine (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ s)).trans ?_
    refine ((Term.subst_ren (Ctx.Le.refl Γ) _ _ _ ?_ s).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ s)))
    intro v T hv
    exact Subst.single_at_ne
      (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)
  · exact Term.subst_eta_tm _ _ _ B (.root (.bnd 0)) _ u (Subst.at_single_root _ _)

/-! ## A hole formula read inside `◇` at the slot

The test formula that turns interchangeability of two `◇`-terms into their `◇`-facts.  A `◇`-typed
term occurs in a formula only inside a `Here` atom, but a `◇`-typed **slot** may also be a witness —
and substituting a `◇`-term for a witness is `Subst.dia`/`SubE.diaBody`: the new witness is the
term's, and the body takes the content address's place.  So instantiating the slot of
`◇_{bnd 0} (ψ read in the slot's view)` with `diatm y bd` gives `◇_y (ψ read with bd in its hole)`,
which is `WFF.viewReadTm`.  The term-level version of this computes by `rfl` (§10.14). -/

/-- ⭐The hole formula `ψ` read inside `◇` **at the slot** `bnd 0`, the slot's content in its hole:
    `WFF.viewRead` at the slot rather than at a free root.  Instantiating the slot with a `◇`-term
    `diatm y bd` reads `ψ` inside `◇_y` with `bd` in its hole (`WFF.instantiate_diaSlot`), so an
    interchangeability instance at this formula is a transfer of `◇`-facts between two names. -/
def WFF.diaSlot {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType}
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) : WFF σ (Γ.insert (.bnd 0) (.VTypeDia A)) 1 :=
  WFF.dia (.root (.bnd 0)) ⟨A, Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)⟩
    (WFF.renameRoot (.bnd 0) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0))
      ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root (.VTypeDia A)).boxIn.trans
        (Ctx.le_boxIn_diaIn _ (.root (.bnd 0))))
      (.step (.root (.bnd 0)) .dia)
      (Ctx.ref_diaIn_of (Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)))
      ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A)
      (((Ctx.NoSlots.slots (Γ := Γ)).insert (.VTypeDia A)).diaIn (.root (.bnd 0))) ψ)

/-- ⭐**Instantiating a `◇`-typed slot used as a witness**: filling the slot of `WFF.diaSlot ψ` with
    the possible object `diatm y bd` gives `◇_y` of `ψ` read with `bd` in its hole.

    The witness of the `◇` node is the instantiating term's (`WFF.subst_dia`, the index reducing
    because the slot is the numeral `bnd 0`).  For the body, the slot's renaming to its own content
    address and then the `◇_y` view of the instantiation compose — `WFF.subst_comp` — to the single
    substitution of `bd` for the slot that `WFF.viewReadTm` is (`WFF.subst_mono` on that side).  The
    one `Subst.Sim` obligation: at the slot both sides give `bd`, through `SubE.diaBody` on the
    instantiating `diatm`; on the box part the instantiation is the identity, which
    `Subst.dia_eq_box_mono` and `Subst.single_at_ne` show entry by entry. -/
theorem WFF.instantiate_diaSlot {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType}
    (ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) {y : VarSymb}
    (hy : ∃ X, Γ.ref y = some (.VTypeDia X)) {a : Ann A} (bd : Term σ (Γ.diaIn y) A a) :
    WFF.instantiate Ctx.NoSlots.slots (Term.diatm y hy bd) (WFF.diaSlot ψ) =
      WFF.dia y hy (WFF.viewReadTm bd ψ) := by
  have hΓ : Γ.SlotsFrom 0 := Ctx.NoSlots.slots
  have hr : Γ.RootFresh (.bnd 0) := hΓ.rootFresh le_rfl
  have hrb : Γ.boxIn.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh le_rfl
  have hslot : (Γ.insert (.bnd 0) (.VTypeDia A)).ref (.root (.bnd 0)) = some (.VTypeDia A) :=
    Ctx.ref_insert_root Γ (.bnd 0) (.VTypeDia A)
  have hθ := Subst.ok_single (σ := σ) (r := .bnd 0) (Ctx.Le.refl Γ)
    (e := .tm (Term.diatm y hy bd)) (T := .VTypeDia A) rfl
  have hc := Subst.coh_single (σ := σ) hr (Ctx.Le.refl Γ)
    (e := .tm (Term.diatm y hy bd)) (T := .VTypeDia A) rfl
  have hidx : Subst.singleIdx (σ := σ) (.bnd 0) (.tm (Term.diatm y hy bd)) (.root (.bnd 0)) = y :=
    rfl
  have hw : ((Subst.single (σ := σ) (.bnd 0) (.tm (Term.diatm y hy bd))).at
      (.root (.bnd 0))).idxAlong [] = y := rfl
  unfold WFF.instantiate WFF.substRoot WFF.diaSlot
  refine (WFF.subst_dia _ hθ hc (hΓ.insert _) hΓ ⟨A, hslot⟩ y hidx hy
    (Subst.ok_dia hθ ⟨A, hslot⟩ hw) (Subst.coh_dia hθ hc ⟨A, hslot⟩)
    (hΓ.diaIn y) _).trans ?_
  refine congrArg (WFF.dia y hy) ?_
  -- the body: compose the slot's renaming with the `◇_y` view of the instantiation
  have hθ₃ := Subst.ok_single (σ := σ) (r := .bnd 0) (Ctx.le_boxIn_diaIn Γ y)
    (e := .tm bd) (T := A) rfl
  have hc₃ := Subst.coh_single (σ := σ) hrb (Ctx.le_boxIn_diaIn Γ y) (e := .tm bd) (T := A) rfl
  unfold WFF.renameRoot
  refine (WFF.subst_comp _ _ _ _ _ _ _ hθ₃ hc₃ _ _ _ ?_ ψ).trans ?_
  · refine Subst.sim_of fun v U hlp hv => ?_
    rw [Subst.comp_apply]
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      rw [Subst.single_root, Subst.single_root, SubE.comp_ren,
        Subst.at_nonproj _ (show (VarSymb.step (.root (.bnd 0)) .dia).lastProj = false from rfl)]
      change SubE.Sim _ (.tm bd)
        (if (VarSymb.root (.bnd 0)) = .root (.bnd 0) then
          ((Subst.single (σ := σ) (.bnd 0) (.tm (Term.diatm y hy bd))).at
            (.root (.bnd 0))).diaBody y
        else .hide)
      rw [if_pos rfl]
      change SubE.Sim _ (.tm bd) (if h : y = y then .tm (Term.mono _ bd) else .hide)
      rw [dif_pos rfl, Term.mono_refl]
      exact .refl _
    · have hv' : Γ.boxIn v = some U := by simpa [Ctx.insert, hvr] using hv
      have hvr' : Γ.boxIn.ref v = some U := (Ctx.ref_nonproj Γ.boxIn hlp).trans hv'
      rw [Subst.single_ne _ hvr, Subst.single_ne _ hvr, SubE.comp_ren,
        Subst.dia_eq_box_mono _ _ y v U hvr', Subst.at_nonproj _ hlp]
      match v, hv' with
      | .step u .box, hv' =>
          obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv'
          change SubE.Sim _ (.ren (.step u .box))
            ((((Subst.single (σ := σ) (.bnd 0) (.tm (Term.diatm y hy bd))).at u).unbox).mono _)
          rw [Subst.single_at_ne (Ctx.ref_rt_ne hr hu)]
          change SubE.Sim _ (.ren (.step u .box)) (.ren u.inner)
          rw [VarSymb.inner_box hk]
          exact .refl _
      | .step u .keep, hv' =>
          obtain ⟨_, hu, _⟩ := Ctx.boxIn_keep hv'
          change SubE.Sim _ (.ren (.step u .keep))
            ((((Subst.single (σ := σ) (.bnd 0) (.tm (Term.diatm y hy bd))).at u).keepE).mono _)
          rw [Subst.single_at_ne (Ctx.ref_rt_ne hr hu)]
          exact .refl _
  · rw [WFF.viewReadTm, WFF.instantiate, WFF.substRoot,
      WFF.subst_mono ((Ctx.le_boxIn_diaIn Γ y).insert (.bnd 0) A) _ _ _
        ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert A) _ _ ψ]

/-! ## Functionality as an equation, where one is available -/

/-- ⭐**Functionality**: a possible object has one realisation here.  No longer primitive — it is
    `Proof.here_subst` at the hole formula `eqRec A (η slot) t`, whose `t`-instance is
    reflexivity and
    whose `t'`-instance is the equation, read back by `WFF.instantiate_eqRec_slot` and turned
    round by
    `Proof.eqRec_symm` (§10.11).

    It stays `◇`-free, and that is not a restriction but the shape of the statement: `WFF.eqRec`
    compares two terms at **one** annotation, which at a `◇`-free type is automatic
    (`Ann.eq_of_diaFree`) and at a `◇`-typed one would mean one witness.  Where the annotations may
    differ, functionality is `here_subst` itself. -/
def Proof.here_fun {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hT : ModalSys.T = true) {A : VarType} (hA : A.diaFree = true) {b : Ann (.VTypeDia A)}
    (s : Term σ Γ (.VTypeDia A) b) {a : Ann A} (t t' : Term σ Γ A a)
    (p : Proof σ Γ Δ (WFF.here hT s t)) (p' : Proof σ Γ Δ (WFF.here hT s t')) :
    Proof σ Γ Δ (eqRec A t t') := by
  obtain rfl := Ann.eq_of_diaFree hA a (Ann.eta (.root (.bnd 0)) A)
  refine Proof.eqRec_symm A (Proof.conv (WFF.instantiate_eqRec_slot hA t' t) ?_)
  exact Proof.here_subst hT s t t' _ p p'
    (Proof.conv (WFF.instantiate_eqRec_slot hA t t).symm (Proof.eqRec_refl A t))


/-- A term weakened past the slot, the slot then filled, is the term. -/
theorem Term.subst_single_mono_sig {σ : Signature} {Γ : Ctx} [Γ.NoSlots]
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) {B : VarType} {b : Ann B} (u : Term σ Γ B b) :
    (⟨_, Term.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
        (Subst.ok_single (Ctx.Le.refl Γ) rfl)
        (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) (Ctx.Le.refl Γ) rfl)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ)).root A) u)⟩ :
        Σ c, Term σ Γ B c) = ⟨b, u⟩ :=
  (congrArg (Sigma.mk _) (Term.subst_mono _ _ _ _ u)).trans
    ((Term.subst_ren (Ctx.Le.refl Γ) _ _ _ (fun _ _ hv => Subst.single_at_ne
      (Ctx.ref_rt_ne ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) hv)) u).trans
      (congrArg (Sigma.mk _) (Term.mono_refl _ u)))

/-- A closed hole term weakened into a context and filled there is the hole term filled. -/
theorem Term.holeRead_eq_holeAt {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType}
    {a : Ann A} (t : Term σ Γ A a) {B : VarType} {b : Ann B}
    (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) : Term.holeRead t s = Term.holeAt t s :=
  Term.subst_mono _ _ _ _ s

end V12M
