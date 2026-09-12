import QML.QML_v12_Theory
import QML.QML_v12_SubstComp

/-!
# QML v12 — staged languages

A world's language grows in stages: a **base** context (the empty context, or a modal view of
another world's language), and at stage `k + 1` the free variable `ρ k` is declared at the type
`τ k`.  The names `ρ k` are distinct (`ρ` injective) and fresh for the base — a modal view still
exposes addresses rooted at the outer language's variables (`u.box`), so a world's own variables
must avoid those names.  Every name `ρ n` with `n ≥ k` is fresh at stage `k`, so witnesses are
always available, and moving a proof to a later stage is the rule `weak_ctx`.

* `Lang`, `Lang.ctx k`, `Lang.le`, `Lang.lift`;
* `WFF.mono_mono`, `WFF.mono_refl`;
* ⭐`Lang.Provable.lift`: provability survives lifting to a later stage.
-/

namespace V12

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

/-! ## Stages -/

/-- Stage `k + 1` declares the variable `ρ k` at type `τ k`. -/
def Ctx.stage (B : Ctx) (τ : ℕ → VarType) (ρ : ℕ → ℕ) : ℕ → Ctx
  | 0 => B
  | k + 1 => (Ctx.stage B τ ρ k).insert (.free (ρ k)) (τ k)

theorem Ctx.stage_fresh {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} (hρ : Function.Injective ρ)
    (hB : ∀ n, B.RootFresh (.free (ρ n))) :
    ∀ {k n : ℕ}, k ≤ n → (B.stage τ ρ k).RootFresh (.free (ρ n))
  | 0, n, _ => hB n
  | k + 1, n, h =>
      (Ctx.stage_fresh hρ hB (Nat.le_of_succ_le h)).insert_ne
        (fun he => by
          have hkn := hρ (Root.free.inj he)
          omega) _

theorem Ctx.stage_slots {B : Ctx} {τ : ℕ → VarType} {ρ : ℕ → ℕ} (hB : B.SlotsFrom 0) :
    ∀ k, (B.stage τ ρ k).SlotsFrom 0
  | 0 => hB
  | k + 1 => (Ctx.stage_slots hB k).insertFree (ρ k) (τ k)

/-- A staged language: a base without slots, the distinct fresh names of its own variables, and
    their types. -/
structure Lang where
  base : Ctx
  τ : ℕ → VarType
  ρ : ℕ → ℕ
  ρ_inj : Function.Injective ρ
  fresh_base : ∀ n, base.RootFresh (.free (ρ n))
  slots : base.SlotsFrom 0

namespace Lang

variable (L : Lang)

/-- The context at stage `k`. -/
def ctx (k : ℕ) : Ctx := L.base.stage L.τ L.ρ k

instance (k : ℕ) : (L.ctx k).NoSlots := ⟨Ctx.stage_slots L.slots k⟩

theorem fresh {k n : ℕ} (h : k ≤ n) : (L.ctx k).RootFresh (.free (L.ρ n)) :=
  Ctx.stage_fresh L.ρ_inj L.fresh_base h

theorem le_succ (k : ℕ) : (L.ctx k).Le (L.ctx (k + 1)) := Ctx.le_insert (L.fresh le_rfl).root _

theorem le {k m : ℕ} (h : k ≤ m) : (L.ctx k).Le (L.ctx m) := by
  induction h with
  | refl => exact Ctx.Le.refl _
  | step _ ih => exact ih.trans (L.le_succ _)

variable {L} {σ : Signature}

/-- A formula moved to a later stage. -/
def lift {k m : ℕ} (h : k ≤ m) (φ : WFF σ (L.ctx k) 0) : WFF σ (L.ctx m) 0 := WFF.mono (L.le h) φ

theorem lift_lift {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) (φ : WFF σ (L.ctx k) 0) :
    lift h₂ (lift h₁ φ) = lift (h₁.trans h₂) φ :=
  WFF.mono_mono _ _ φ

theorem lift_refl {k : ℕ} (h : k ≤ k) (φ : WFF σ (L.ctx k) 0) : lift h φ = φ :=
  WFF.mono_refl _ φ

theorem lift_neg {k m : ℕ} (h : k ≤ m) (φ : WFF σ (L.ctx k) 0) :
    lift h φ.neg = (lift h φ).neg :=
  rfl

theorem lift_bot {k m : ℕ} (h : k ≤ m) : lift h (.bot : WFF σ (L.ctx k) 0) = .bot := rfl

/-- ⭐Provability survives lifting to a later stage. -/
theorem Provable.lift {k m : ℕ} (h : k ≤ m) {Δ : List (WFF σ (L.ctx k) 0)}
    {φ : WFF σ (L.ctx k) 0} (p : Provable Δ φ) :
    Provable (Δ.map (Lang.lift h)) (Lang.lift h φ) := by
  induction h with
  | refl =>
      have hΔ : Δ.map (Lang.lift (Nat.le_refl k)) = Δ := by
        conv_rhs => rw [← List.map_id Δ]
        exact List.map_congr_left fun ψ _ => lift_refl _ ψ
      rw [hΔ, lift_refl]
      exact p
  | @step m hkm ih =>
      have p' := ih.map (Proof.weak_ctx (L.ρ m) (L.τ m) (L.fresh le_rfl))
      have hΔ : (Δ.map (Lang.lift hkm)).map (WFF.weaken (L.fresh (le_refl m)).root (L.τ m)) =
          Δ.map (Lang.lift (Nat.le.step hkm)) := by
        rw [List.map_map]
        exact List.map_congr_left fun ψ _ => lift_lift hkm (Nat.le_succ m) ψ
      have hφ : WFF.weaken (L.fresh (le_refl m)).root (L.τ m) (Lang.lift hkm φ) =
          Lang.lift (Nat.le.step hkm) φ :=
        lift_lift hkm (Nat.le_succ m) φ
      rw [hΔ, hφ] at p'
      exact p'

end Lang

end V12
