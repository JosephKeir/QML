import QML.QML_v12m_BFair

/-!
# QML v12m — B's arrow model: arrows read through their committed part

In the limit of the network an arrow's images are those committed at some round, and a stage of
the source is sent along the part of the arrow committed by a later round.  So an arrow is used
through a **suffix** of the variables it covers (`ImgOk.suffix`) and with **another image map
agreeing on them** (`sim_arrowS`, `sim_arrowXS`).  ⭐`Transfer.apply`, `TransferX.apply`,
`TransferX.applyBox`: a transfer serves every such restriction; along a witness arrow, necessities
transfer too (by `□ψ ⊢ □_x ψ`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

omit [ModalSys] in
theorem rootTy_suffix {l l' : List VarType} (h : l <:+ l') {r : ℕ} (hr : r < l.length) :
    rootTy l r = rootTy l' r := by
  obtain ⟨e, rfl⟩ := h
  simp only [rootTy, List.reverse_append, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hr)]

theorem ImgOk.suffix {l l' : List VarType} {Δ : Ctx} {img : ℕ → ℕ} (h : l <:+ l')
    (himg : ImgOk l' Δ img) : ImgOk l Δ img := fun r hr => by
  rw [rootTy_suffix h hr]
  exact himg r (lt_of_lt_of_le hr h.length_le)

theorem ImgOk.congr {l : List VarType} {Δ : Ctx} {img img' : ℕ → ℕ}
    (h : ∀ r < l.length, img r = img' r) (himg : ImgOk l Δ img) : ImgOk l Δ img' :=
  fun r hr => by
    rw [← h r hr]
    exact himg r hr

variable [ModalSys.NoFour]

/-- Arrows with images agreeing on a world's variables agree on its `□` view. -/
theorem sim_arrowS {l : List VarType} {Δ : Ctx} {img img' : ℕ → ℕ}
    (h : ∀ r < l.length, img r = img' r) :
    Subst.Sim (ctxOf l).boxIn (arrowS σ Δ img) (arrowS σ Δ img') :=
  Subst.sim_of fun v T _ hv => by
    obtain ⟨u, rfl, hu⟩ := boxIn_item hv
    obtain ⟨r, hr, hlt, _⟩ := ref_rt hu
    change SubE.Sim T (.ren (itemAt (imgRoot img u.rt) u)) (.ren (itemAt (imgRoot img' u.rt) u))
    rw [hr, imgRoot, imgRoot, h r hlt]
    exact .refl _

/-- Witness arrows with images agreeing on a world's variables agree on its `◇_x` view. -/
theorem sim_arrowXS {l : List VarType} {Δ : Ctx} {img img' : ℕ → ℕ} {x : VarSymb} {cx : ℕ}
    (h : ∀ r < l.length, img r = img' r) :
    Subst.Sim ((ctxOf l).diaIn x) (arrowXS σ Δ img x cx) (arrowXS σ Δ img' x cx) :=
  Subst.sim_of fun v T _ hv => by
    rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
    · obtain ⟨r, hr, hlt, _⟩ := ref_rt hu
      change SubE.Sim T (.ren (itemAt (imgRoot img u.rt) u))
        (.ren (itemAt (imgRoot img' u.rt) u))
      rw [hr, imgRoot, imgRoot, h r hlt]
      exact .refl _
    · exact .refl _

/-- ⭐A transfer serves any suffix of its variables, with any images agreeing on them. -/
theorem Transfer.apply {Γ : Ctx} {M : Set (WFF σ Γ 0)} {ls : List VarType}
    {hle : (ctxOf ls).Le Γ} {Δ : Ctx} [Δ.NoSlots] {N : Set (WFF σ Δ 0)} {img : ℕ → ℕ}
    {himg : ImgOk ls Δ img} (htr : Transfer M ls hle N img himg) {l : List VarType}
    (hsuf : l <:+ ls) {img' : ℕ → ℕ} (hag : ∀ r < l.length, img r = img' r)
    (himg' : ImgOk l Δ img') (hle' : (ctxOf l).Le Γ) (ψ : WFF σ (ctxOf l).boxIn 0)
    (hψ : WFF.mono hle' (.box ψ) ∈ M) :
    WFF.subst (arrowIdx img') (arrowS σ Δ img') (ok_arrowS himg') (coh_arrowS himg')
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ N := by
  have h := htr (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ) (by
    change WFF.box (WFF.mono hle.boxIn (WFF.mono (ctxOf_le_of_suffix hsuf).boxIn ψ)) ∈ M
    rw [WFF.mono_mono]
    exact hψ)
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots] at h
  rwa [WFF.subst_congr _ _ _ (ok_arrowS himg') _ (coh_arrowS himg') _ _ (sim_arrowS hag) ψ] at h

/-- ⭐A witness transfer serves any suffix of its variables, with any images agreeing on them. -/
theorem TransferX.apply {Γ : Ctx} {M : Set (WFF σ Γ 0)} {ls : List VarType}
    {hle : (ctxOf ls).Le Γ} {x : VarSymb} {X : VarType} {hx : (ctxOf ls).ref x = some (.VTypeDia X)}
    {Δ : Ctx} [Δ.NoSlots] {N : Set (WFF σ Δ 0)} {img : ℕ → ℕ} {himg : ImgOk ls Δ img} {cx : ℕ}
    {hcx : Δ.ref (.root (.free cx)) = some X} (htr : TransferX M ls hle hx N img himg cx hcx)
    {l : List VarType} (hsuf : l <:+ ls) {img' : ℕ → ℕ} (hag : ∀ r < l.length, img r = img' r)
    (himg' : ImgOk l Δ img') (hx' : (ctxOf l).ref x = some (.VTypeDia X))
    (hle' : (ctxOf l).Le Γ) (ψ : WFF σ ((ctxOf l).diaIn x) 0)
    (hψ : WFF.mono hle' (WFF.boxx x ⟨X, hx'⟩ ψ) ∈ M) :
    WFF.subst (arrowXIdx img' x cx) (arrowXS σ Δ img' x cx) (ok_arrowXS himg' hx' hcx)
      (coh_arrowXS himg' hx' hcx) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ N := by
  have h := htr (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ) (by
    have e : WFF.mono hle (WFF.boxx x ⟨X, hx⟩ (WFF.mono ((ctxOf_le_of_suffix hsuf).diaIn x) ψ)) =
        WFF.mono hle' (WFF.boxx x ⟨X, hx'⟩ ψ) := by
      simp only [WFF.mono, WFF.mono_mono]
    rw [e]
    exact hψ)
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots] at h
  rwa [WFF.subst_congr _ _ _ (ok_arrowXS himg' hx' hcx) _ (coh_arrowXS himg' hx' hcx) _ _
    (sim_arrowXS hag) ψ] at h

/-- ⭐Along a witness arrow, necessities transfer too. -/
theorem TransferX.applyBox {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {ls : List VarType} {hle : (ctxOf ls).Le Γ} {x : VarSymb} {X : VarType}
    {hx : (ctxOf ls).ref x = some (.VTypeDia X)} {Δ : Ctx} [Δ.NoSlots] {N : Set (WFF σ Δ 0)}
    {img : ℕ → ℕ} {himg : ImgOk ls Δ img} {cx : ℕ} {hcx : Δ.ref (.root (.free cx)) = some X}
    (htr : TransferX M ls hle hx N img himg cx hcx) {l : List VarType} (hsuf : l <:+ ls)
    {img' : ℕ → ℕ} (hag : ∀ r < l.length, img r = img' r) (himg' : ImgOk l Δ img')
    (hle' : (ctxOf l).Le Γ) (ψ : WFF σ (ctxOf l).boxIn 0) (hψ : WFF.mono hle' (.box ψ) ∈ M) :
    WFF.subst (arrowIdx img') (arrowS σ Δ img') (ok_arrowS himg') (coh_arrowS himg')
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ N := by
  have hb : WFF.mono hle (WFF.boxx x ⟨X, hx⟩
      (WFF.mono ((ctxOf_le_of_suffix hsuf).boxIn.trans (Ctx.le_boxIn_diaIn _ x)) ψ)) ∈ M := by
    refine hM.closed ⟨[WFF.mono hle' (.box ψ)], fun y hy => by
      rw [List.mem_singleton.mp hy]; exact hψ, ?_⟩
    have h := Proof.box_boxx (Γ := Γ) (x := x) ⟨X, hle.ref hx⟩ (WFF.mono hle'.boxIn ψ)
    refine ⟨Proof.conv ?_ (Proof.castHyps (by simp only [WFF.mono]) h)⟩
    simp only [WFF.boxx, WFF.neg, WFF.mono, WFF.mono_mono]
  have h := htr _ hb
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots] at h
  rwa [WFF.subst_congr _ _ _ (ok_arrowS himg') _ (coh_arrowS himg') _ _
    (sim_arrowXS_arrowS hag) ψ] at h

end BArrow

end V12M
