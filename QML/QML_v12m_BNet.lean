import QML.QML_v12m_BDia

/-!
# QML v12m — B's arrow model: networks

The canonical model for B is the limit of **networks**, built round by round.  A network is a
finite tree of worlds.  A node is a list of child indices, the newest step first (`c :: p` is the
`c`-th child of `p`).  Each live node has the types of its variables and a maximal consistent
theory in them (`NodeSt`).  Each child has two arrows, both renamings of variables:

* **forward**, from its parent: the parent's oldest variables `fcl` (a suffix of its list) have
  images (`fimg`), with necessity transfer (`Transfer`), or `□_x` transfer (`TransferX`) when the
  child was made for `◇_x` (`kind`), `x.dia` going to the child's variable `cx`;
* **back**, to its parent: the child's oldest variables `bcl` have images (`bimg`), with necessity
  transfer.

`Good` collects the invariants.  The transfers survive growth at either end
(`Transfer.mono_tgt`, `Transfer.mono_src`): a target that grows keeps what it had, and a source
that grows conservatively necessitates nothing new about its old variables.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## Completing a theory -/

open Classical in
/-- A maximal consistent extension, when there is one. -/
noncomputable def complete {Γ : Ctx} (S : Set (WFF σ Γ 0)) : Set (WFF σ Γ 0) :=
  if h : Theory.Consistent S then Classical.choose (Theory.lindenbaum h) else S

theorem complete_spec {Γ : Ctx} {S : Set (WFF σ Γ 0)} (h : Theory.Consistent S) :
    S ⊆ complete S ∧ Theory.IsMCS (complete S) := by
  unfold complete
  rw [dif_pos h]
  exact Classical.choose_spec (Theory.lindenbaum h)

/-- A theory extended conservatively decides its old formulas as before. -/
theorem mem_of_mono_mem {Γ Γ' : Ctx} (h : Γ.Le Γ') {M : Set (WFF σ Γ 0)} (hM : Theory.IsMCS M)
    {M' : Set (WFF σ Γ' 0)} (hM' : Theory.IsMCS M') (hsub : ∀ φ ∈ M, WFF.mono h φ ∈ M')
    {φ : WFF σ Γ 0} (hφ : WFF.mono h φ ∈ M') : φ ∈ M := by
  by_contra hn
  exact hM'.neg_mem_iff.mp (hsub _ (hM.neg_mem_iff.mpr hn)) hφ

/-! ## Suffixes -/

omit [ModalSys] in
theorem ctxOf_le_of_suffix {l l' : List VarType} (h : l <:+ l') : (ctxOf l).Le (ctxOf l') := by
  obtain ⟨e, rfl⟩ := h
  exact ctxOf_le_append e l

/-! ## Substitution along equal renamings -/

theorem WFF.subst_eq_of_eq {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ} {θ θ' : Subst σ Δ}
    (e : θ = θ') (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
    (hc' : Subst.Coh ι Γ θ') (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d') (φ : WFF σ Γ d) :
    WFF.subst ι θ hθ hc hΓ hΔ φ = WFF.subst ι θ' hθ' hc' hΓ hΔ φ := by
  subst e
  rfl

theorem arrowS_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') (img : ℕ → ℕ) :
    (arrowS σ Δ img).mono h = arrowS σ Δ' img := by
  funext v
  match v with
  | .step u .box => rfl
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .dia => rfl
  | .step _ .here => rfl
  | .step _ .keep => rfl

theorem arrowXS_mono {Δ Δ' : Ctx} (h : Δ.Le Δ') (img : ℕ → ℕ) (x : VarSymb) (cx : ℕ) :
    (arrowXS σ Δ img x cx).mono h = arrowXS σ Δ' img x cx := by
  funext v
  match v with
  | .step u .box => rfl
  | .step u .dia =>
      change SubE.mono h (if u = x then SubE.ren (.root (.free cx)) else .hide) =
        (if u = x then SubE.ren (.root (.free cx)) else .hide)
      split_ifs <;> rfl
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .here => rfl
  | .step _ .keep => rfl

/-! ## Transfers survive growth -/

theorem ImgOk.mono {l : List VarType} {Δ Δ' : Ctx} (h : Δ.Le Δ') {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) : ImgOk l Δ' img := fun r hr => h.ref (himg r hr)

/-- A growing target keeps the transfer. -/
theorem Transfer.mono_tgt [ModalSys.NoFour] {Γ : Ctx} {M : Set (WFF σ Γ 0)} {ls : List VarType}
    {hle : (ctxOf ls).Le Γ} {Δ Δ' : Ctx} [Δ.NoSlots] [Δ'.NoSlots] (h : Δ.Le Δ')
    {N : Set (WFF σ Δ 0)} {N' : Set (WFF σ Δ' 0)} (hN : ∀ φ ∈ N, WFF.mono h φ ∈ N')
    {img : ℕ → ℕ} {himg : ImgOk ls Δ img} (htr : Transfer M ls hle N img himg) :
    Transfer M ls hle N' img (himg.mono h) := by
  intro ψ hψ
  have h' := hN _ (htr ψ hψ)
  rw [WFF.mono_subst] at h'
  rwa [WFF.subst_eq_of_eq (arrowS_mono h img) _ (ok_arrowS (himg.mono h)) _
    (coh_arrowS (himg.mono h))] at h'

/-- A source growing conservatively keeps the transfer. -/
theorem Transfer.mono_src [ModalSys.NoFour] {Γ Γ' : Ctx} (h : Γ.Le Γ') {M : Set (WFF σ Γ 0)}
    (hM : Theory.IsMCS M) {M' : Set (WFF σ Γ' 0)} (hM' : Theory.IsMCS M')
    (hsub : ∀ φ ∈ M, WFF.mono h φ ∈ M') {ls : List VarType} {hle : (ctxOf ls).Le Γ} {Δ : Ctx}
    [Δ.NoSlots] {N : Set (WFF σ Δ 0)} {img : ℕ → ℕ} {himg : ImgOk ls Δ img}
    (htr : Transfer M ls hle N img himg) : Transfer M' ls (hle.trans h) N img himg := by
  intro ψ hψ
  refine htr ψ (mem_of_mono_mem h hM hM' hsub ?_)
  rwa [WFF.mono_mono]

/-- A growing target keeps a witness transfer. -/
theorem TransferX.mono_tgt [ModalSys.NoFour] {Γ : Ctx} {M : Set (WFF σ Γ 0)} {ls : List VarType}
    {hle : (ctxOf ls).Le Γ} {x : VarSymb} {X : VarType} {hx : (ctxOf ls).ref x = some (.VTypeDia X)}
    {Δ Δ' : Ctx} [Δ.NoSlots] [Δ'.NoSlots] (h : Δ.Le Δ')
    {N : Set (WFF σ Δ 0)} {N' : Set (WFF σ Δ' 0)} (hN : ∀ φ ∈ N, WFF.mono h φ ∈ N')
    {img : ℕ → ℕ} {himg : ImgOk ls Δ img} {cx : ℕ} {hcx : Δ.ref (.root (.free cx)) = some X}
    (htr : TransferX M ls hle hx N img himg cx hcx) :
    TransferX M ls hle hx N' img (himg.mono h) cx (h.ref hcx) := by
  intro ψ hψ
  have h' := hN _ (htr ψ hψ)
  rw [WFF.mono_subst] at h'
  rwa [WFF.subst_eq_of_eq (arrowXS_mono h img x cx) _ (ok_arrowXS (himg.mono h) hx (h.ref hcx))
    _ (coh_arrowXS (himg.mono h) hx (h.ref hcx))] at h'

/-- A source growing conservatively keeps a witness transfer. -/
theorem TransferX.mono_src [ModalSys.NoFour] {Γ Γ' : Ctx} (h : Γ.Le Γ') {M : Set (WFF σ Γ 0)}
    (hM : Theory.IsMCS M) {M' : Set (WFF σ Γ' 0)} (hM' : Theory.IsMCS M')
    (hsub : ∀ φ ∈ M, WFF.mono h φ ∈ M') {ls : List VarType} {hle : (ctxOf ls).Le Γ}
    {x : VarSymb} {X : VarType} {hx : (ctxOf ls).ref x = some (.VTypeDia X)} {Δ : Ctx}
    [Δ.NoSlots] {N : Set (WFF σ Δ 0)} {img : ℕ → ℕ} {himg : ImgOk ls Δ img} {cx : ℕ}
    {hcx : Δ.ref (.root (.free cx)) = some X} (htr : TransferX M ls hle hx N img himg cx hcx) :
    TransferX M' ls (hle.trans h) hx N img himg cx hcx := by
  intro ψ hψ
  refine htr ψ (mem_of_mono_mem h hM hM' hsub ?_)
  rwa [WFF.mono_mono]

/-! ## Networks -/

/-- A node: child indices from the node up to the root. -/
abbrev Node := List ℕ

/-- A world under construction: the types of its variables and its theory. -/
structure NodeSt (σ : Signature) where
  l : List VarType
  M : Set (WFF σ (ctxOf l) 0)

/-- ⭐A network under construction. -/
structure NetSt (σ : Signature) where
  st : Node → NodeSt σ
  /-- The number of children created so far. -/
  nch : Node → ℕ
  /-- A child made for `◇_x` records `x` and its content type. -/
  kind : Node → Option (VarSymb × VarType)
  /-- The child's variable holding the witness's content, for a child made for `◇_x`. -/
  cx : Node → ℕ
  /-- A **back-witness child**, made for a returning possibility with a possible part
      `e ⇝ z`, records `e` (a variable of the child) and its content type: its way home lies in
      `e`'s extent, with content `bcx` at the parent. -/
  bkind : Node → Option (VarSymb × VarType)
  /-- The parent's variable holding the back witness's content, for a back-witness child. -/
  bcx : Node → ℕ
  /-- The parent's variables with images in the child, and the images. -/
  fcl : Node → List VarType
  fimg : Node → ℕ → ℕ
  /-- The child's variables with images in the parent, and the images. -/
  bcl : Node → List VarType
  bimg : Node → ℕ → ℕ

/-! ## Arrows between two worlds -/

/-- ⭐A forward arrow from `tp` to `tk`: `tp`'s variables `fcl` have images `fimg` in `tk`, with
    necessity transfer, or `□_x` transfer for a child made for `◇_x` (`kind`). -/
def FwdData [ModalSys.NoFour] (tp tk : NodeSt σ) (kind : Option (VarSymb × VarType)) (cx : ℕ)
    (fcl : List VarType) (fimg : ℕ → ℕ) : Prop :=
  ∃ (hsuf : fcl <:+ tp.l) (himg : ImgOk fcl (ctxOf tk.l) fimg),
    match kind with
    | none => Transfer tp.M fcl (ctxOf_le_of_suffix hsuf) tk.M fimg himg
    | some (x, X) => ∃ (hx : (ctxOf fcl).ref x = some (.VTypeDia X))
        (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X),
        TransferX tp.M fcl (ctxOf_le_of_suffix hsuf) hx tk.M fimg himg cx hcx

/-- ⭐A back arrow from `tk` to `tp`: `tk`'s variables `bcl` have images `bimg` in `tp`, with
    necessity transfer. -/
def BackData [ModalSys.NoFour] (tk tp : NodeSt σ) (bcl : List VarType) (bimg : ℕ → ℕ) : Prop :=
  ∃ (hsuf : bcl <:+ tk.l) (himg : ImgOk bcl (ctxOf tp.l) bimg),
    Transfer tk.M bcl (ctxOf_le_of_suffix hsuf) tp.M bimg himg

namespace NetSt

variable (N : NetSt σ)

/-- The nodes created so far: the root, and the children created of live nodes. -/
def Live : Node → Prop
  | [] => True
  | c :: p => Live p ∧ c < N.nch p

/-- The forward arrow into the child `k` of `p`. -/
def FwdOk [ModalSys.NoFour] (k p : Node) : Prop :=
  FwdData (N.st p) (N.st k) (N.kind k) (N.cx k) (N.fcl k) (N.fimg k)

/-- The back arrow from the child `k` to its parent `p`. -/
def BackOk [ModalSys.NoFour] (k p : Node) : Prop :=
  BackData (N.st k) (N.st p) (N.bcl k) (N.bimg k)

/-- ⭐The invariants of a network. -/
structure Good [ModalSys.NoFour] : Prop where
  mcs : ∀ s, N.Live s → Theory.IsMCS (N.st s).M
  fwd : ∀ c p, N.Live (c :: p) → N.FwdOk (c :: p) p
  back : ∀ c p, N.Live (c :: p) → N.BackOk (c :: p) p

end NetSt

end BArrow

end V12M
