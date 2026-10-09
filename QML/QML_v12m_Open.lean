import QML.QML_v12m_LeibnizQuant
import QML.QML_v12m_Stages

/-!
# QML v12m — opening a quantifier body at a fresh variable

For Henkin witnesses: the body `ψ` of `∃x ψ` is opened at a fresh free variable `u`
(`WFF.openFree`).  Binding `u` back gives `ψ` (`bindFree_openFree`), so `∃`-elimination applies to
`∃x ψ` itself; and the opened body is the instantiation at the η-expanded variable
(`instantiate_eta_openFree`).

* `WFF.subst_ren`: a substitution renaming every visible address to itself acts as weakening.
-/

namespace V12M

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx}

theorem ren_under {Γ : Ctx} {θ : Subst σ Δ} (hid : ∀ v T, Γ.ref v = some T → θ.at v = .ren v)
    {d : ℕ} (T : VarType) (h : Δ (.root (.bnd d)) = none) :
    ∀ v U, (Γ.insert (.bnd d) T).ref v = some U → (θ.under d d T h).at v = .ren v :=
  at_ren_of fun v U hlp hv => by
    by_cases hvr : v = .root (.bnd d)
    · subst hvr
      exact if_pos rfl
    · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
      rw [show θ.under d d T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
        ← Subst.at_nonproj θ hlp, hid v U ((Ctx.ref_nonproj Γ hlp).trans hv')]
      rfl

end Subst

theorem Rel.subst_ren {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (hle : Γ.Le Δ)
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (hid : ∀ v T, Γ.ref v = some T → θ.at v = .ren v) :
    ∀ {n : ℕ} (ρ : Rel σ Γ n), Rel.subst ι θ hθ hc ρ = Rel.mono hle ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.subst ι θ hθ hc ρ) (Term.subst ι θ hθ hc t) =
        Rel.eval (Rel.mono hle ρ) (Term.mono hle t)
      rw [Rel.subst_ren hle θ hθ hc hid ρ,
        eq_of_heq (Sigma.mk.inj (Term.subst_ren hle θ hθ hc hid t)).2]

/-- ⭐A substitution renaming every visible address to itself acts on formulas as weakening. -/
theorem WFF.subst_ren {σ : Signature} : {ι : VarSymb → VarSymb} → {Γ Δ : Ctx} → {d : ℕ} →
    (hle : Γ.Le Δ) → (θ : Subst σ Δ) → (hθ : Subst.Ok Γ θ) → (hc : Subst.Coh ι Γ θ) →
    (hΓ : Γ.SlotsFrom d) → (hΔ : Δ.SlotsFrom d) →
    (∀ v T, Γ.ref v = some T → θ.at v = .ren v) → (φ : WFF σ Γ d) →
    WFF.subst ι θ hθ hc hΓ hΔ φ = WFF.mono hle φ
  | _, _, _, _, hle, θ, hθ, hc, _, _, hid, .atom ρ =>
      congrArg WFF.atom (Rel.subst_ren hle θ hθ hc hid ρ)
  | _, _, _, _, hle, θ, hθ, hc, _, _, hid, .eq t s =>
      congrArg₂ WFF.eq (eq_of_heq (Sigma.mk.inj (Term.subst_ren hle θ hθ hc hid t)).2)
        (eq_of_heq (Sigma.mk.inj (Term.subst_ren hle θ hθ hc hid s)).2)
  | _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, hle, θ, hθ, hc, hΓ, hΔ, hid, .and φ ψ =>
      congrArg₂ WFF.and (WFF.subst_ren hle θ hθ hc hΓ hΔ hid φ)
        (WFF.subst_ren hle θ hθ hc hΓ hΔ hid ψ)
  | _, _, _, _, hle, θ, hθ, hc, hΓ, hΔ, hid, .or φ ψ =>
      congrArg₂ WFF.or (WFF.subst_ren hle θ hθ hc hΓ hΔ hid φ)
        (WFF.subst_ren hle θ hθ hc hΓ hΔ hid ψ)
  | _, _, _, _, hle, θ, hθ, hc, hΓ, hΔ, hid, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.subst_ren hle θ hθ hc hΓ hΔ hid φ)
        (WFF.subst_ren hle θ hθ hc hΓ hΔ hid ψ)
  | _, _, _, _, hle, θ, hθ, hc, hΓ, hΔ, hid, .all T φ =>
      congrArg (WFF.all T) (WFF.subst_ren (hle.insert _ T) _ _ _ _ _
        (Subst.ren_under hid T hΔ.root) φ)
  | _, _, _, _, hle, θ, hθ, hc, hΓ, hΔ, hid, .ex T φ =>
      congrArg (WFF.ex T) (WFF.subst_ren (hle.insert _ T) _ _ _ _ _
        (Subst.ren_under hid T hΔ.root) φ)
  | _, _, _, _, hle, θ, hθ, hc, hΓ, hΔ, hid, .box φ =>
      congrArg WFF.box (WFF.subst_ren hle.boxIn θ.box _ _ _ _ (Subst.ren_box hid) φ)
  | ι, Γ, Δ, d, hle, θ, hθ, hc, hΓ, hΔ, hid, .dia x hx φ => by
      have key : ∀ (y : VarSymb) (_hy : x = y) (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
          (p : Subst.Ok (Γ.diaIn x) (θ.dia x y)) (q : Subst.Coh ι (Γ.diaIn x) (θ.dia x y))
          (hΔ' : (Δ.diaIn y).SlotsFrom d),
          WFF.dia y P (WFF.subst ι (θ.dia x y) p q (hΓ.diaIn x) hΔ' φ) =
            WFF.mono hle (WFF.dia x hx φ) := by
        intro y hy P p q hΔ'
        subst hy
        exact congrArg (WFF.dia x _)
          (WFF.subst_ren (hle.diaIn x) (θ.dia x x) p q _ _ (Subst.ren_dia hid x) φ)
      exact key (ι x) (Subst.idx_ren hc hid hx).symm _ _ _ _
  | _, _, _, _, hle, θ, hθ, hc, _, _, hid, .here hT s t =>
      WFF.here_congr hT (Term.subst_ren hle θ hθ hc hid s)
        (Term.subst_ren hle θ hθ hc hid t)
  | _, _, _, _, hle, θ, hθ, hc, _, _, hid, .back hB L s t =>
      WFF.back_congr hB L (Term.subst_ren hle θ hθ hc hid s)
        (Term.subst_ren hle θ hθ hc hid t)
  | _, _, _, _, hle, θ, hθ, hc, hΓ, hΔ, hid, .ret hB t Φ =>
      WFF.ret_congr hB (Term.subst_ren hle θ hθ hc hid t)
        (WFF.subst_ren (hle.boxIn.insert _ _) _ _ _ _ _
          (Subst.ren_under (Subst.ren_box hid) _ hΔ.boxIn.root) Φ)
  | ι, Γ, Δ, d, hle, θ, hθ, hc, hΓ, hΔ, hid, .retx (A := A) hB y hy t Φ => by
      have key : ∀ (z : VarSymb) (_hz : y = z) (P : ∃ Y, Δ.ref z = some (.VTypeDia Y))
          (hΔz : (Δ.diaIn z).SlotsFrom d)
          (p : Subst.Ok ((Γ.diaIn y).insert (.bnd d) (.VTypeBox A))
            ((θ.dia y z).under d d _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot ι d d) ((Γ.diaIn y).insert (.bnd d) (.VTypeBox A))
            ((θ.dia y z).under d d _ hΔz.root)),
          WFF.retx hB z P (Term.subst ι θ hθ hc t)
              (WFF.subst (VarSymb.shiftSlot ι d d) ((θ.dia y z).under d d _ hΔz.root) p q
                ((hΓ.diaIn y).insert _) (hΔz.insert _) Φ) =
            WFF.mono hle (WFF.retx hB y hy t Φ) := by
        intro z hz P hΔz p q
        subst hz
        exact WFF.retx_congr hB y _ (Term.subst_ren hle θ hθ hc hid t)
          (WFF.subst_ren ((hle.diaIn y).insert _ _) _ p q _ _
            (Subst.ren_under (Subst.ren_dia hid y) _ hΔz.root) Φ)
      exact key (ι y) (Subst.idx_ren hc hid hy).symm _ (hΔ.diaIn _) _ _

section Open

variable {σ : Signature} {Γ : Ctx} {T : VarType}

/-- The body of a quantifier opened at a fresh free variable. -/
def WFF.openFree (u : ℕ) (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom 0)
    (ψ : WFF σ (Γ.insert (.bnd 0) T) 1) : WFF σ (Γ.insert (.free u) T) 0 :=
  WFF.subst (VarSymb.slotToFree id 0 u) ((Subst.idRen Γ).toFree 0 u T hu.root)
    (Subst.ok_toFree Subst.ok_idRen T hu.root)
    (Subst.coh_toFree Subst.ok_idRen Subst.coh_idRen hs T hu.root) (hs.insert T)
    (hs.insertFree u T) ψ

theorem idRen_under_ren (hs : Γ.SlotsFrom 0) :
    ∀ v U, (Γ.insert (.bnd 0) T).ref v = some U →
      ((Subst.idRen (σ := σ) Γ).under 0 0 T hs.root).at v = .ren v :=
  Subst.ren_under (fun v _ _ => Subst.at_idRen v) T hs.root

/-- ⭐Binding the variable back gives the body. -/
theorem WFF.bindFree_openFree (u : ℕ) (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom 0)
    (ψ : WFF σ (Γ.insert (.bnd 0) T) 1) :
    WFF.bindFree u hu hs T (WFF.openFree u hu hs ψ) = ψ :=
  (WFF.bindFree_toFree (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen hs hs u hu T ψ).trans
    ((WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (idRen_under_ren hs) ψ).trans
      (WFF.mono_refl _ ψ))

/-- ⭐The opened body is the instantiation at the η-expanded variable. -/
theorem WFF.instantiate_eta_openFree (u : ℕ) (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom 0)
    (hs' : (Γ.insert (.free u) T).SlotsFrom 0) (ψ : WFF σ (Γ.insert (.bnd 0) T) 1) :
    WFF.instantiate hs' (Term.eta (.root (.free u)) T (Ctx.ref_insert_root Γ _ T))
        (WFF.mono ((Ctx.le_insert hu.root T).insert (.bnd 0) T) ψ) =
      WFF.openFree u hu hs ψ := by
  have h := WFF.instantiate_toFree (Subst.idRen Γ) Subst.ok_idRen Subst.coh_idRen hs hs u hu T hs' ψ
  rw [WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (idRen_under_ren hs) ψ, WFF.mono_mono] at h
  exact h

/-- Opening commutes with negation. -/
theorem WFF.openFree_neg (u : ℕ) (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom 0)
    (ψ : WFF σ (Γ.insert (.bnd 0) T) 1) :
    WFF.openFree u hu hs ψ.neg = (WFF.openFree u hu hs ψ).neg :=
  rfl

end Open

end V12M
