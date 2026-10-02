import QML.QML_v12m_BNet

/-!
# QML v12m — B's arrow model: growing one node

Every step of the construction grows one node conservatively (`Grows`: more variables, and the old
theory lifted into the new).  An arrow survives growth at either end (`FwdData.grow_tgt`,
`FwdData.grow_src`, and likewise for `BackData`), so ⭐`Good.setSt`: growing one live node
preserves the invariants.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-- `t'` extends `t`: its variables continue `t`'s, and its theory contains `t`'s. -/
structure Grows (t t' : NodeSt σ) : Prop where
  suf : t.l <:+ t'.l
  sub : ∀ φ ∈ t.M, WFF.mono (ctxOf_le_of_suffix suf) φ ∈ t'.M

theorem Grows.refl (t : NodeSt σ) : Grows t t :=
  ⟨List.suffix_refl _, fun φ h => by rwa [WFF.mono_refl]⟩

theorem Grows.trans {t t' t'' : NodeSt σ} (h₁ : Grows t t') (h₂ : Grows t' t'') : Grows t t'' :=
  ⟨h₁.suf.trans h₂.suf, fun φ h => by
    have := h₂.sub _ (h₁.sub φ h)
    rwa [WFF.mono_mono] at this⟩

/-! ## Arrows survive growth -/

theorem FwdData.grow_tgt [ModalSys.NoFour] {tp tk tk' : NodeSt σ}
    {kind : Option (VarSymb × VarType)} {cx : ℕ} {fcl : List VarType} {fimg : ℕ → ℕ}
    (h : FwdData tp tk kind cx fcl fimg) (hg : Grows tk tk') : FwdData tp tk' kind cx fcl fimg := by
  have hle := ctxOf_le_of_suffix hg.suf
  cases kind with
  | none =>
      obtain ⟨hsuf, himg, htr⟩ := h
      exact ⟨hsuf, himg.mono hle, Transfer.mono_tgt hle hg.sub htr⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      obtain ⟨hsuf, himg, hx, hcx, htr⟩ := h
      exact ⟨hsuf, himg.mono hle, hx, hle.ref hcx, TransferX.mono_tgt hle hg.sub htr⟩

theorem FwdData.grow_src [ModalSys.NoFour] {tp tp' tk : NodeSt σ}
    {kind : Option (VarSymb × VarType)} {cx : ℕ} {fcl : List VarType} {fimg : ℕ → ℕ}
    (hp : Theory.IsMCS tp.M) (hp' : Theory.IsMCS tp'.M)
    (h : FwdData tp tk kind cx fcl fimg) (hg : Grows tp tp') :
    FwdData tp' tk kind cx fcl fimg := by
  have hle := ctxOf_le_of_suffix hg.suf
  cases kind with
  | none =>
      obtain ⟨hsuf, himg, htr⟩ := h
      exact ⟨hsuf.trans hg.suf, himg, Transfer.mono_src hle hp hp' hg.sub htr⟩
  | some xX =>
      obtain ⟨x, X⟩ := xX
      obtain ⟨hsuf, himg, hx, hcx, htr⟩ := h
      exact ⟨hsuf.trans hg.suf, himg, hx, hcx, TransferX.mono_src hle hp hp' hg.sub htr⟩

theorem BackData.grow_src [ModalSys.NoFour] {tk tk' tp : NodeSt σ} {bcl : List VarType}
    {bimg : ℕ → ℕ} (hk : Theory.IsMCS tk.M) (hk' : Theory.IsMCS tk'.M)
    (h : BackData tk tp bcl bimg) (hg : Grows tk tk') : BackData tk' tp bcl bimg := by
  obtain ⟨hsuf, himg, htr⟩ := h
  exact ⟨hsuf.trans hg.suf, himg,
    Transfer.mono_src (ctxOf_le_of_suffix hg.suf) hk hk' hg.sub htr⟩

theorem BackData.grow_tgt [ModalSys.NoFour] {tk tp tp' : NodeSt σ} {bcl : List VarType}
    {bimg : ℕ → ℕ} (h : BackData tk tp bcl bimg) (hg : Grows tp tp') :
    BackData tk tp' bcl bimg := by
  obtain ⟨hsuf, himg, htr⟩ := h
  have hle := ctxOf_le_of_suffix hg.suf
  exact ⟨hsuf, himg.mono hle, Transfer.mono_tgt hle hg.sub htr⟩

namespace NetSt

/-- The network with node `s` in state `t`. -/
def setSt (N : NetSt σ) (s : Node) (t : NodeSt σ) : NetSt σ :=
  { N with st := Function.update N.st s t }

theorem live_setSt (N : NetSt σ) (s : Node) (t : NodeSt σ) :
    ∀ k, (N.setSt s t).Live k ↔ N.Live k
  | [] => Iff.rfl
  | c :: p => by
      change (N.setSt s t).Live p ∧ c < N.nch p ↔ N.Live p ∧ c < N.nch p
      rw [live_setSt N s t p]

theorem setSt_self (N : NetSt σ) (s : Node) (t : NodeSt σ) : (N.setSt s t).st s = t := by
  unfold setSt
  exact Function.update_self s t N.st

theorem setSt_ne (N : NetSt σ) {s k : Node} (t : NodeSt σ) (h : k ≠ s) :
    (N.setSt s t).st k = N.st k := by
  unfold setSt
  exact Function.update_of_ne h t N.st

omit [ModalSys] in
theorem ne_parent (c : ℕ) (p : Node) : (c :: p : Node) ≠ p := by
  intro h
  have := congrArg List.length h
  simp at this

/-- ⭐Growing one live node conservatively preserves the invariants. -/
theorem Good.setSt [ModalSys.NoFour] {N : NetSt σ} (hN : N.Good) {s : Node} {t : NodeSt σ}
    (hs : N.Live s) (hg : Grows (N.st s) t) (ht : Theory.IsMCS t.M) : (N.setSt s t).Good := by
  refine ⟨fun k hk => ?_, fun c p hk => ?_, fun c p hk => ?_⟩
  · rw [live_setSt] at hk
    by_cases hks : k = s
    · subst hks
      rw [setSt_self]
      exact ht
    · rw [setSt_ne _ _ hks]
      exact hN.mcs k hk
  · rw [live_setSt] at hk
    have hf := hN.fwd c p hk
    unfold FwdOk at hf ⊢
    change FwdData ((N.setSt s t).st p) ((N.setSt s t).st (c :: p)) _ _ _ _
    by_cases hkp : (c :: p : Node) = s
    · subst hkp
      rw [setSt_ne _ _ (fun h => ne_parent c p h.symm), setSt_self]
      exact hf.grow_tgt hg
    · rw [setSt_ne _ _ hkp]
      by_cases hps : p = s
      · subst hps
        rw [setSt_self]
        exact hf.grow_src (hN.mcs p hk.1) ht hg
      · rw [setSt_ne _ _ hps]
        exact hf
  · rw [live_setSt] at hk
    have hb := hN.back c p hk
    unfold BackOk at hb ⊢
    change BackData ((N.setSt s t).st (c :: p)) ((N.setSt s t).st p) _ _
    by_cases hkp : (c :: p : Node) = s
    · subst hkp
      rw [setSt_ne _ _ (fun h => ne_parent c p h.symm), setSt_self]
      exact hb.grow_src (hN.mcs _ hk) ht hg
    · rw [setSt_ne _ _ hkp]
      by_cases hps : p = s
      · subst hps
        rw [setSt_self]
        exact hb.grow_tgt hg
      · rw [setSt_ne _ _ hps]
        exact hb

end NetSt

end BArrow

end V12M
