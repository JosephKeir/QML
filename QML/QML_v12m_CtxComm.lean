import QML.QML_v12m_Symbols

/-!
# QML v12m — contexts: extensionality, and a declaration commuting with an opening

* `Ctx.ext'`: contexts with the same declarations and witnesses are equal.
* ⭐`Ctx.insert_optInT_comm` (identity kind, moved from `QML_v12m_TCanonOpenT`),
  `Ctx.insert_optIn_comm` (arrow kind), together `Ctx.insert_optInK_comm`: a fresh declaration
  commutes with an opening, so a context built in any order of births and openings is the one
  with the births first (the nested calculus `GKN`'s nodes, docs §12.50).
* `Ctx.optIn_optInT_comm`: an arrow opening commutes with an identity opening.
-/

namespace V12M

set_option linter.unusedSectionVars false

variable [ModalSys]

/-- Contexts with the same declarations and witnesses are equal. -/
theorem Ctx.ext' {Γ Δ : Ctx} (h₁ : Γ.ty = Δ.ty) (h₂ : Γ.wit = Δ.wit) : Γ = Δ := by
  cases Γ
  cases Δ
  cases h₁
  cases h₂
  rfl

/-- Opening the identity view of an address that is not a possibility here changes nothing. -/
theorem Ctx.optInT_of_witT_none {Γ : Ctx} {y : VarSymb} (h : Γ.witT y = none) :
    Γ.optInT y = Γ := by
  refine Ctx.ext' (funext fun v => ?_) rfl
  change Γ.optInTTy y v = Γ v
  unfold Ctx.optInTTy
  by_cases hv : v = .step y .at
  · rw [if_pos hv, h]
  · rw [if_neg hv]

/-- ⭐A fresh declaration commutes with an identity opening that takes effect. -/
theorem Ctx.insert_optInT_comm {Γ : Ctx} {u : ℕ} (hu : Γ.RootFresh (.free u)) {y : VarSymb}
    {X : VarType} (hy : Γ.witT y = some X) (T : VarType) :
    (Γ.optInT y).insert (.free u) T = (Γ.insert (.free u) T).optInT y := by
  have hyI : (Γ.insert (.free u) T).witT y = some X := (Ctx.le_insert (hu _ rfl) T).witT hy
  have hrt : y.rt ≠ .free u := fun he => by
    have h₁ := Ctx.ref_none_of_rootFresh hu y he
    rw [(Ctx.witT_spec hy).2.2] at h₁
    cases h₁
  refine Ctx.ext' (funext fun v => ?_) rfl
  change (if v = .root (.free u) then some T
      else if v.atBelow (.free u) then none else Γ.optInTTy y v) =
    (Γ.insert (.free u) T).optInTTy y v
  unfold Ctx.optInTTy
  by_cases hv : v = .step y .at
  · subst hv
    have hab : (VarSymb.step y .at).atBelow (.free u) = false := by
      simp [VarSymb.atBelow, VarSymb.rt, hrt]
    rw [if_neg (fun h => by cases h), if_pos rfl, if_pos rfl, hyI, hy, hab]
    rfl
  · rw [if_neg hv, if_neg hv]
    rfl

/-- ⭐An arrow opening commutes with an identity opening that takes effect. -/
theorem Ctx.optIn_optInT_comm {Γ : Ctx} {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X)
    (z : VarSymb) : (Γ.optInT y).optIn z = (Γ.optIn z).optInT y := by
  have hyI : (Γ.optIn z).witT y = some X := (Ctx.le_optIn Γ z).witT hy
  refine Ctx.ext' (funext fun v => ?_) rfl
  change (if v = .step z .dia then (match Γ.wit z with
      | some X' => some X' | none => Γ.optInTTy y v) else Γ.optInTTy y v) =
    (Γ.optIn z).optInTTy y v
  unfold Ctx.optInTTy
  by_cases hv : v = .step y .at
  · subst hv
    rw [if_neg (fun h => by cases h), if_pos rfl, if_pos rfl, hy, hyI]
  · rw [if_neg hv, if_neg hv]
    rfl

/-- ⭐**A declaration commutes with an arrow opening**: the opening writes only at `y.dia`, which
    no declaration's `atBelow` reaches, and both keep the witnesses. -/
theorem Ctx.insert_optIn_comm (Γ : Ctx) (r : Root) (T : VarType) (y : VarSymb) :
    (Γ.optIn y).insert r T = (Γ.insert r T).optIn y := by
  refine Ctx.ext' (funext fun v => ?_) rfl
  change (if v = .root r then some T else if v.atBelow r then none else Γ.optIn y v) =
    (Γ.insert r T).optIn y v
  rw [Ctx.optIn_apply, Ctx.optIn_apply]
  by_cases hv : v = .step y .dia
  · subst hv
    have hab : (VarSymb.step y .dia).atBelow r = false := rfl
    rw [if_neg (fun h => by cases h), hab, if_pos rfl, if_pos rfl]
    change _ = (match Γ.wit y with | some X => some X | none => (Γ.insert r T) (.step y .dia))
    cases Γ.wit y with
    | some X => rfl
    | none =>
        change Γ (.step y .dia) = (if VarSymb.step y .dia = .root r then some T
          else if (VarSymb.step y .dia).atBelow r then none else Γ (.step y .dia))
        rw [if_neg (fun h => by cases h), hab]
        rfl
  · rw [if_neg hv, if_neg hv]
    rfl

/-- ⭐**A fresh declaration commutes with an opening of either kind** that takes effect. -/
theorem Ctx.insert_optInK_comm {Γ : Ctx} {u : ℕ} (hu : Γ.RootFresh (.free u)) (T : VarType) :
    ∀ {κ : WitKind} {y : VarSymb} {X : VarType}, Γ.witK κ y = some X →
      (Γ.optInK κ y).insert (.free u) T = (Γ.insert (.free u) T).optInK κ y
  | .arrow, y, _, _ => Ctx.insert_optIn_comm Γ _ T y
  | .ident, _, _, hy => Ctx.insert_optInT_comm hu hy T

end V12M
