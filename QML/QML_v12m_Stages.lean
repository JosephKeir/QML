import QML.QML_v12m_Theory
import QML.QML_v12m_SubstComp

/-!
# QML v12m — weakening twice; declaring variables in stages

* `WFF.mono_mono`, `WFF.mono_refl`: weakening a formula twice is weakening once; weakening along
  `Γ ≤ Γ` changes nothing.
* `Ctx.stage B τ ρ k`: the context `B` with the variables `ρ 0 : τ 0, …, ρ (k - 1) : τ (k - 1)`
  declared; names fresh for `B` and distinct stay fresh at every earlier stage
  (`Ctx.stage_fresh`).  World languages (`QML_v12m_WorldLang`) are built from these stages.
-/

namespace V12M

variable [ModalSys]

/-! ## Weakening twice -/

theorem Rel.mono_mono {σ : Signature} {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : Γ₁.Le Γ₂) (h₂ : Γ₂.Le Γ₃) :
    ∀ {n : ℕ} (ρ : Rel σ Γ₁ n), Rel.mono h₂ (Rel.mono h₁ ρ) = Rel.mono (h₁.trans h₂) ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.mono h₂ (Rel.mono h₁ ρ)) (Term.mono h₂ (Term.mono h₁ t)) = _
      rw [Rel.mono_mono h₁ h₂ ρ, Term.mono_mono h₁ h₂ t]
      rfl

theorem WFF.mono_mono {σ : Signature} : ∀ {Γ₁ Γ₂ Γ₃ : Ctx} {d : ℕ} (h₁ : Γ₁.Le Γ₂)
    (h₂ : Γ₂.Le Γ₃) (φ : WFF σ Γ₁ d), WFF.mono h₂ (WFF.mono h₁ φ) = WFF.mono (h₁.trans h₂) φ
  | _, _, _, _, h₁, h₂, .atom ρ => congrArg WFF.atom (Rel.mono_mono h₁ h₂ ρ)
  | _, _, _, _, h₁, h₂, .eq t s =>
      congrArg₂ WFF.eq (Term.mono_mono h₁ h₂ t) (Term.mono_mono h₁ h₂ s)
  | _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, h₁, h₂, .and φ ψ =>
      congrArg₂ WFF.and (WFF.mono_mono h₁ h₂ φ) (WFF.mono_mono h₁ h₂ ψ)
  | _, _, _, _, h₁, h₂, .or φ ψ =>
      congrArg₂ WFF.or (WFF.mono_mono h₁ h₂ φ) (WFF.mono_mono h₁ h₂ ψ)
  | _, _, _, _, h₁, h₂, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.mono_mono h₁ h₂ φ) (WFF.mono_mono h₁ h₂ ψ)
  | _, _, _, _, h₁, h₂, .all T φ =>
      congrArg (WFF.all T) (WFF.mono_mono (h₁.insert _ T) (h₂.insert _ T) φ)
  | _, _, _, _, h₁, h₂, .ex T φ =>
      congrArg (WFF.ex T) (WFF.mono_mono (h₁.insert _ T) (h₂.insert _ T) φ)
  | _, _, _, _, h₁, h₂, .box φ => congrArg WFF.box (WFF.mono_mono h₁.boxIn h₂.boxIn φ)
  | _, _, _, _, h₁, h₂, .dia x _ φ =>
      congrArg (WFF.dia x _) (WFF.mono_mono (h₁.diaIn x) (h₂.diaIn x) φ)
  | _, _, _, _, h₁, h₂, .here hT s t =>
      WFF.here_congr' hT (Term.mono_mono h₁ h₂ s) (Term.mono_mono h₁ h₂ t)
  | _, _, _, _, h₁, h₂, .back hB L s t =>
      WFF.back_congr' hB L (Term.mono_mono h₁ h₂ s) (Term.mono_mono h₁ h₂ t)
  | _, _, _, _, h₁, h₂, .ret hB t Φ =>
      WFF.ret_congr' hB (Term.mono_mono h₁ h₂ t)
        (WFF.mono_mono (h₁.boxIn.insert _ _) (h₂.boxIn.insert _ _) Φ)

theorem Rel.mono_refl {σ : Signature} {Γ : Ctx} (h : Γ.Le Γ) :
    ∀ {n : ℕ} (ρ : Rel σ Γ n), Rel.mono h ρ = ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.mono h ρ) (Term.mono h t) = _
      rw [Rel.mono_refl h ρ, Term.mono_refl h t]

theorem WFF.mono_refl {σ : Signature} : ∀ {Γ : Ctx} {d : ℕ} (h : Γ.Le Γ) (φ : WFF σ Γ d),
    WFF.mono h φ = φ
  | _, _, h, .atom ρ => congrArg WFF.atom (Rel.mono_refl h ρ)
  | _, _, h, .eq t s => congrArg₂ WFF.eq (Term.mono_refl h t) (Term.mono_refl h s)
  | _, _, _, .top => rfl
  | _, _, _, .bot => rfl
  | _, _, h, .and φ ψ => congrArg₂ WFF.and (WFF.mono_refl h φ) (WFF.mono_refl h ψ)
  | _, _, h, .or φ ψ => congrArg₂ WFF.or (WFF.mono_refl h φ) (WFF.mono_refl h ψ)
  | _, _, h, .imp φ ψ => congrArg₂ WFF.imp (WFF.mono_refl h φ) (WFF.mono_refl h ψ)
  | _, _, h, .all T φ => congrArg (WFF.all T) (WFF.mono_refl (h.insert _ T) φ)
  | _, _, h, .ex T φ => congrArg (WFF.ex T) (WFF.mono_refl (h.insert _ T) φ)
  | _, _, h, .box φ => congrArg WFF.box (WFF.mono_refl h.boxIn φ)
  | _, _, h, .dia x hx φ => congrArg (WFF.dia x hx) (WFF.mono_refl (h.diaIn x) φ)
  | _, _, h, .here hT s t => WFF.here_congr' hT (Term.mono_refl h s) (Term.mono_refl h t)
  | _, _, h, .back hB L s t =>
      WFF.back_congr' hB L (Term.mono_refl h s) (Term.mono_refl h t)
  | _, _, h, .ret hB t Φ =>
      WFF.ret_congr' hB (Term.mono_refl h t) (WFF.mono_refl (h.boxIn.insert _ _) Φ)

/-! ## Stages -/

/-- Stage `k + 1` declares the variable `ρ k` at type `τ k`. -/
def Ctx.stage (B : Ctx) (τ : ℕ → VarType) (ρ : ℕ → ℕ) : ℕ → Ctx
  | 0 => B
  | k + 1 => (Ctx.stage B τ ρ k).insert (.free (ρ k)) (τ k)

omit [ModalSys] in
theorem Ctx.stage_fresh {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} (hρ : Function.Injective ρ)
    (hB : ∀ n, B.RootFresh (.free (ρ n))) :
    ∀ {k n : ℕ}, k ≤ n → (B.stage τ ρ k).RootFresh (.free (ρ n))
  | 0, n, _ => hB n
  | k + 1, n, h =>
      (Ctx.stage_fresh hρ hB (Nat.le_of_succ_le h)).insert_ne
        (fun he => by
          have hkn := hρ (Root.free.inj he)
          omega) _

/-- A variable declared at an earlier stage is reachable at its own type. -/
theorem Ctx.stage_ref_root {B : Ctx} {τ : ℕ → VarType} (ρ : ℕ → ℕ) (hρ : Function.Injective ρ)
    (hB : ∀ n, B.RootFresh (.free (ρ n))) {k : ℕ} :
    ∀ {j : ℕ}, k < j → (B.stage τ ρ j).ref (.root (.free (ρ k))) = some (τ k)
  | j + 1, h => by
      change (if (VarSymb.root (.free (ρ k))) = .root (.free (ρ j)) then some (τ j)
        else (B.stage τ ρ j) (.root (.free (ρ k)))) = _
      by_cases hkj : k = j
      · subst hkj
        rw [if_pos rfl]
      · rw [if_neg (fun he => hkj (hρ (Root.free.inj (VarSymb.root.inj he))))]
        exact Ctx.stage_ref_root ρ hρ hB (by omega)

omit [ModalSys] in
/-- Declaring a variable writes only at its root: nothing else rooted there is reachable. -/
theorem Ctx.stage_only_root {B : Ctx} {τ : ℕ → VarType} (ρ : ℕ → ℕ) (hρ : Function.Injective ρ)
    (hB : ∀ n, B.RootFresh (.free (ρ n))) {k : ℕ} :
    ∀ (j : ℕ) (v : VarSymb), v.rt = .free (ρ k) → v ≠ .root (.free (ρ k)) →
      (B.stage τ ρ j) v = none
  | 0, v, hv, _ => hB k v hv
  | j + 1, v, hv, hne => by
      change (if v = .root (.free (ρ j)) then some (τ j) else (B.stage τ ρ j) v) = none
      rw [if_neg ?_]
      · exact Ctx.stage_only_root ρ hρ hB j v hv hne
      · intro he
        subst he
        exact hne (congrArg (fun r => VarSymb.root (Root.free r)) (Root.free.inj hv))

omit [ModalSys] in
theorem Ctx.stage_slots {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} (hB : B.SlotsFrom 0) :
    ∀ k, (B.stage τ ρ k).SlotsFrom 0
  | 0 => hB
  | k + 1 => (Ctx.stage_slots hB k).insertFree (ρ k) (τ k)

end V12M
