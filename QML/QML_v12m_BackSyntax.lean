import QML.QML_v12m_SubstEta

/-!
# QML v12m — strong B: the syntax its rules are stated in

Roadmap milestone 2, step 4 (`docs/v12-modal-extensions.md` §11.2, §11.14).

* **Hole formulas and terms**, closed apart from one hole (§11.2): `WFF.holeRead`, `Term.holeRead`
  read them in a context with a term in the hole.  A round trip carries no addresses, so the two
  ends of a `Back` meet only through the hole.
* ⭐`OutLeg`: the out leg of a round trip — every arrow (`nec`, row 1) or a witness's extent
  (`pos y`, row 2) — with its view, its `◇` and `□`, and the `Back` atom of a carrier given by its
  body (`OutLeg.back`).  The rules are stated once over it; substitution sends a leg to a leg
  (`OutLeg.subst`) and acts on its pieces definitionally (`OutLeg.subst_dia`, `subst_box`,
  `subst_back`).
-/

namespace V12M

variable [ModalSys]

/-- A **hole formula** — closed apart from its hole — read in `Γ` with `t` in the hole. -/
def WFF.holeRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) (ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) : WFF σ Γ 0 :=
  WFF.instantiate Ctx.NoSlots.slots t (WFF.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) ψ)

/-- A **hole term** — closed apart from its hole — read in `Γ` with `t` in the hole: what `Back`'s
    β-rule maps a carrier and its value by. -/
def Term.holeRead {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A}
    (t : Term σ Γ A a) {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) :
    Term σ Γ B (b.mapIdx (Subst.singleIdx (.bnd 0) (.tm t))) :=
  Term.subst (Subst.singleIdx (.bnd 0) (.tm t)) (Subst.single (.bnd 0) (.tm t))
    (Subst.ok_single (Ctx.Le.refl Γ) rfl)
    (Subst.coh_single ((Ctx.NoSlots.slots (Γ := Γ)).rootFresh (le_refl 0)) (Ctx.Le.refl Γ) rfl)
    (Term.mono ((Ctx.empty_le Γ).insert (.bnd 0) A) s)

/-- ⭐The **out leg** of a round trip (§11.1): every arrow out of the world (`nec`, row 1, carrier
    `□□A`) or the extent of a witness `y` (`pos`, row 2, carrier `◇□A`). -/
inductive OutLeg (Γ : Ctx) where
  | nec
  | pos (y : VarSymb) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y))

namespace OutLeg

variable {σ : Signature} {Γ : Ctx}

/-- The leg of the `Back` atom. -/
def leg : OutLeg Γ → BLeg
  | .nec => .nec
  | .pos _ _ => .pos

/-- The view at the far end of the out leg. -/
def view : OutLeg Γ → Ctx
  | .nec => Γ.boxIn
  | .pos y _ => Γ.diaIn y

instance instNoSlots [Γ.NoSlots] {O : OutLeg Γ} : O.view.NoSlots := by
  cases O <;> (dsimp only [view]; infer_instance)

theorem slotsFrom {d : ℕ} (h : Γ.SlotsFrom d) : (O : OutLeg Γ) → O.view.SlotsFrom d
  | .nec => h.boxIn
  | .pos y _ => h.diaIn y

/-- Some arrow of the leg: `◇` or `◇_y`. -/
def dia {d : ℕ} : (O : OutLeg Γ) → WFF σ O.view d → WFF σ Γ d
  | .nec, φ => (WFF.box φ.neg).neg
  | .pos y hy, φ => WFF.dia y hy φ

/-- Every arrow of the leg: `□` or `□_y`. -/
def box {d : ℕ} : (O : OutLeg Γ) → WFF σ O.view d → WFF σ Γ d
  | .nec, φ => WFF.box φ
  | .pos y hy, φ => WFF.boxx y hy φ

/-- ⭐The `Back` atom of the carrier with body `bd` — `boxtm (boxtm bd)` or `diatm y (boxtm bd)`:
    every term of type `□□A` or `◇□A` has this shape, so the rules are stated at the body and
    survive substitution (§10.11). -/
def back {d : ℕ} (hS : ModalSys.BStrong = true) : (O : OutLeg Γ) → {A : VarType} →
    A.diaFree = true → {a₀ : Ann A} → Term σ O.view.boxIn A a₀ → {a : Ann A} → Term σ Γ A a →
    WFF σ Γ d
  | .nec, _, hA, _, bd, _, t => WFF.back hS .nec hA (Term.boxtm (Term.boxtm bd)) t
  | .pos y hy, _, hA, _, bd, _, t => WFF.back hS .pos hA (Term.diatm y hy (Term.boxtm bd)) t

/-- The atom depends on its terms only as dependent pairs. -/
theorem back_congr {d : ℕ} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₁ a₂ : Ann A} {bd₁ : Term σ O.view.boxIn A a₁}
    {bd₂ : Term σ O.view.boxIn A a₂}
    (hbd : (⟨a₁, bd₁⟩ : Σ b, Term σ O.view.boxIn A b) = ⟨a₂, bd₂⟩) {c₁ c₂ : Ann A}
    {t₁ : Term σ Γ A c₁} {t₂ : Term σ Γ A c₂} (ht : (⟨c₁, t₁⟩ : Σ b, Term σ Γ A b) = ⟨c₂, t₂⟩) :
    (O.back hS hA bd₁ t₁ : WFF σ Γ d) = O.back hS hA bd₂ t₂ := by
  cases hbd
  cases ht
  rfl

/-! ### Substitution -/

section Subst

variable {ι : VarSymb → VarSymb} {Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
  (hc : Subst.Coh ι Γ θ)

/-- The leg a substitution sends a leg to: the witness goes where `ι` sends it. -/
def subst : OutLeg Γ → OutLeg Δ
  | .nec => .nec
  | .pos y hy =>
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      .pos (ι y) (hy.elim fun _ hY => SubE.ref_witness (Subst.okRef_at hθ hY) hw)

/-- The substitution on the leg's view. -/
def viewSubst : (O : OutLeg Γ) → Subst σ (O.subst θ hθ hc).view
  | .nec => θ.box
  | .pos y _ => θ.dia y (ι y)

theorem viewOk : (O : OutLeg Γ) → Subst.Ok O.view (O.viewSubst θ hθ hc)
  | .nec => Subst.ok_box hθ
  | .pos y hy => Subst.ok_dia hθ hy (hy.elim fun _ hY => hc y _ hY [])

theorem viewCoh : (O : OutLeg Γ) → Subst.Coh ι O.view (O.viewSubst θ hθ hc)
  | .nec => Subst.coh_box hθ hc
  | .pos _ hy => Subst.coh_dia hθ hc hy

theorem subst_dia {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d') :
    (O : OutLeg Γ) → (φ : WFF σ O.view d) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.dia φ) =
      (O.subst θ hθ hc).dia (WFF.subst ι (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
        (O.viewCoh θ hθ hc) (slotsFrom hΓ O) (slotsFrom hΔ _) φ)
  | .nec, _ => rfl
  | .pos _ _, _ => rfl

theorem subst_box {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d') :
    (O : OutLeg Γ) → (φ : WFF σ O.view d) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.box φ) =
      (O.subst θ hθ hc).box (WFF.subst ι (O.viewSubst θ hθ hc) (O.viewOk θ hθ hc)
        (O.viewCoh θ hθ hc) (slotsFrom hΓ O) (slotsFrom hΔ _) φ)
  | .nec, _ => rfl
  | .pos _ _, _ => rfl

theorem subst_back {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (hΔ : Δ.SlotsFrom d')
    (hS : ModalSys.BStrong = true) :
    (O : OutLeg Γ) → {A : VarType} → (hA : A.diaFree = true) → {a₀ : Ann A} →
    (bd : Term σ O.view.boxIn A a₀) → {a : Ann A} → (t : Term σ Γ A a) →
    WFF.subst ι θ hθ hc hΓ hΔ (O.back hS hA bd t : WFF σ Γ d) =
      ((O.subst θ hθ hc).back hS hA
        (Term.subst ι (O.viewSubst θ hθ hc).box (Subst.ok_box (O.viewOk θ hθ hc))
          (Subst.coh_box (O.viewOk θ hθ hc) (O.viewCoh θ hθ hc)) bd)
        (Term.subst ι θ hθ hc t) : WFF σ Δ d')
  | .nec, _, _, _, _, _, _ => rfl
  | .pos _ _, _, _, _, _, _, _ => rfl

end Subst

end OutLeg

end V12M
