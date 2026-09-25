import QML.QML_v12m_SemStrongT

/-!
# QML v12m — the realisation predicate, semantic probe

A probe for the design recorded in `docs/v12-modal-extensions.md` §3 T ("strong T inwards, via a
realisation predicate").  It adds nothing to the syntax: it states `Here x t` **semantically** —
the identity arrow lies in `x`'s extent and `x`'s content there is `t` — and checks that the two
rules it is meant to license are sound **by reuse**.

* `Model.HereData`: the semantic content of `Here x t`.
* ⭐`Model.sat_here_elim`: `Here x t, □_x χ ⊢ χ(t)`.
* ⭐`Model.sat_here_intro`: `Here x t, χ(t) ⊢ ◇_x χ`.

Both are immediate from `Model.sat_realiseAt`, whose hypotheses `hmem` and `hcont` *are* the two
fields of `HereData`, and whose biconditional is the two rules at once.  `χ(t)` is
`WFF.realiseAt`, which already exists: abstract the witness out of the view formula (`diaAbs`),
then read it at the actual world with `t` in the hole (`hereRead`).

So the semantics needs nothing new, and what a `WFF` constructor would add is only the ability to
*say* `Here x t` inside the object language — which is what the canonical model would need.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-- ⭐The semantic content of `Here x t`: the identity arrow lies in the witness's extent, and the
    witness's content there is `t`. -/
structure HereData (hT : ModalSys.T = true) {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {c : ℕ}
    {A : VarType} (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A)) {a₀ : Ann A}
    (t₀ : Term σ Γ A a₀) : Prop where
  /-- The witness is realised here. -/
  mem : M.frame.reflAcc hT w ∈ (M.posEval (env.ref (.root (.free c)) hcA)).1
  /-- And its content here is `t₀`. -/
  cont : (M.posEval (env.ref (.root (.free c)) hcA)).2 ⟨M.frame.reflAcc hT w, mem⟩ =
    interp env t₀

variable (hT : ModalSys.T = true) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
  (hnp : Γ.NoProjLast) {c : ℕ} {A : VarType}
  (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
  (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none) {a₀ : Ann A}
  (t₀ : Term σ Γ A a₀) (χ : WFF σ (Γ.diaIn (.root (.free c))) 0)

include hnp in
/-- ⭐**Elimination**: what is necessary over the witness's extent holds of its realisation here.
    This is weak T relativised to the witness. -/
theorem sat_here_elim (h : HereData hT env hcA t₀)
    (hbox : M.sat env (WFF.boxx (.root (.free c)) ⟨A, hcA⟩ χ)) :
    M.sat env (WFF.realiseAt hT c hcA hfr t₀ χ) := by
  by_contra hno
  exact hbox ⟨A, hcA, ⟨M.frame.reflAcc hT w, h.mem⟩, fun hχ =>
    hno ((sat_realiseAt hT env hnp hcA hfr t₀ h.mem h.cont χ).mpr hχ)⟩

include hnp in
/-- ⭐**Introduction**: what holds of the realisation here is possible for the witness, the actual
    world witnessing it. -/
theorem sat_here_intro (h : HereData hT env hcA t₀)
    (hφ : M.sat env (WFF.realiseAt hT c hcA hfr t₀ χ)) :
    M.sat env (WFF.dia (.root (.free c)) ⟨A, hcA⟩ χ) :=
  ⟨A, hcA, ⟨M.frame.reflAcc hT w, h.mem⟩,
    (sat_realiseAt hT env hnp hcA hfr t₀ h.mem h.cont χ).mp hφ⟩

omit [Γ.NoSlots] in
/-- The realisation is unique, so the relation is functional — the model-level counterpart of
    `Here x a, Here x b ⊢ a = b`. -/
theorem HereData.interp_eq {a₁ : Ann A} {t₁ : Term σ Γ A a₁}
    (h : HereData hT env hcA t₀) (h₁ : HereData hT env hcA t₁) :
    interp env t₀ = interp env t₁ := by
  rw [← h.cont, ← h₁.cont]

end Model

end V12M
