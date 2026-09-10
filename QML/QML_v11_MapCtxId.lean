import QML.QML_v11_MapCtxCompWFF

/-!
# QML v11 — `mapCtx` depends only on the underlying function

Toward LEMMA A1 (`ctx_extU` commutes with `mapCtx`).  After weakening by `u`, a box's interior is
imaged along a bijection whose function is `m.f` updated at `u` — which agrees with `m.f` on the
interior (it cannot mention `u`) but lands in an image context that is only PROPOSITIONALLY equal to
`m.imageCtx`.  So A1 needs `mapCtx_congr`: two bijections with the same function give the same
result up to a cast.

⭐Neither lemma here needs a new induction.  Both follow from the round trip and composition:

* `mapCtx_idOfEq` — along an identity bijection between equal contexts, `mapCtx` is the cast.  At
  `A = A`, the round trip gives `I ∘ I = id` and composition gives `I ∘ I = I`, so `I = id`.
* `mapCtx_congr` — compose `m` with the identity bijection onto `m'`'s target; composition says the
  result is `mapCtx m'`, and `mapCtx_idOfEq` turns the identity step into a cast.
-/

/-- The identity bijection between two equal contexts. -/
def CtxBij.idOfEq {A B : VarCtx} (h : A = B) : CtxBij A B where
  f := id
  inj := fun _ _ _ _ hab => hab
  maps := by intro p hp; subst h; exact hp
  onto := by intro p hp; subst h; exact ⟨p, hp, rfl⟩

@[simp] theorem CtxBij.idOfEq_f {A B : VarCtx} (h : A = B) :
    (CtxBij.idOfEq h).toCtxMap.f = id := rfl

theorem Term.mapCtx_idOfEq {σ : Signature} {A B : VarCtx} (h : A = B) {S : VarType}
    (t : Term σ A S) : Term.mapCtx (CtxBij.idOfEq h) t = h ▸ t := by
  subst h
  have hr := Term.mapCtx_roundtrip A A A (CtxBij.idOfEq rfl) (CtxBij.idOfEq rfl) rfl
    (fun _ _ => rfl) S t
  have hc := Term.mapCtx_comp A A A A (CtxBij.idOfEq rfl) (CtxBij.idOfEq rfl)
    (CtxBij.idOfEq rfl) rfl (fun _ _ => rfl) S t
  exact hc.symm.trans hr

theorem Rel.mapCtx_idOfEq {σ : Signature} {A B : VarCtx} (h : A = B) {n : ℕ}
    (R : Rel σ A n) : Rel.mapCtx (CtxBij.idOfEq h) R = h ▸ R := by
  subst h
  have hr := Rel.mapCtx_roundtrip (CtxBij.idOfEq (rfl : A = A)) (CtxBij.idOfEq rfl) rfl
    (fun _ _ => rfl) R
  have hc := Rel.mapCtx_comp (CtxBij.idOfEq (rfl : A = A)) (CtxBij.idOfEq rfl)
    (CtxBij.idOfEq rfl) rfl (fun _ _ => rfl) R
  exact hc.symm.trans hr

theorem WFF.mapCtx_idOfEq {σ : Signature} {A B : VarCtx} (h : A = B) (φ : WFF σ A) :
    WFF.mapCtx (CtxBij.idOfEq h) φ = h ▸ φ := by
  subst h
  have hr := WFF.mapCtx_roundtrip A A A (CtxBij.idOfEq rfl) (CtxBij.idOfEq rfl) rfl
    (fun _ _ => rfl) φ
  have hc := WFF.mapCtx_comp A A A A (CtxBij.idOfEq rfl) (CtxBij.idOfEq rfl)
    (CtxBij.idOfEq rfl) rfl (fun _ _ => rfl) φ
  exact hc.symm.trans hr

/-- ⭐`mapCtx` depends only on the underlying function on the source's symbols. -/
theorem Term.mapCtx_congr {σ : Signature} {V V₁ V₂ : VarCtx} (m : CtxBij V V₁)
    (m' : CtxBij V V₂) (h : V₁ = V₂)
    (hf : ∀ v ∈ VarCtx_to_VarSymbs V, m.toCtxMap.f v = m'.toCtxMap.f v) {S : VarType}
    (t : Term σ V S) : h ▸ Term.mapCtx m t = Term.mapCtx m' t := by
  have hc := Term.mapCtx_comp V V₁ V₂ V₂ m (CtxBij.idOfEq h) m' rfl hf S t
  rw [Term.mapCtx_idOfEq] at hc
  exact hc

theorem Rel.mapCtx_congr {σ : Signature} {V V₁ V₂ : VarCtx} (m : CtxBij V V₁)
    (m' : CtxBij V V₂) (h : V₁ = V₂)
    (hf : ∀ v ∈ VarCtx_to_VarSymbs V, m.toCtxMap.f v = m'.toCtxMap.f v) {n : ℕ}
    (R : Rel σ V n) : h ▸ Rel.mapCtx m R = Rel.mapCtx m' R := by
  have hc := Rel.mapCtx_comp m (CtxBij.idOfEq h) m' rfl hf R
  rw [Rel.mapCtx_idOfEq] at hc
  exact hc

theorem WFF.mapCtx_congr {σ : Signature} {V V₁ V₂ : VarCtx} (m : CtxBij V V₁)
    (m' : CtxBij V V₂) (h : V₁ = V₂)
    (hf : ∀ v ∈ VarCtx_to_VarSymbs V, m.toCtxMap.f v = m'.toCtxMap.f v)
    (φ : WFF σ V) : h ▸ WFF.mapCtx m φ = WFF.mapCtx m' φ := by
  have hc := WFF.mapCtx_comp V V₁ V₂ V₂ m (CtxBij.idOfEq h) m' rfl hf φ
  rw [WFF.mapCtx_idOfEq] at hc
  exact hc
