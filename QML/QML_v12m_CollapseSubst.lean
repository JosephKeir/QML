import QML.QML_v12m_SubstCompose

/-!
# QML v12m — collapsing commutes with substitution

Two facts about moving syntax down a collapsed level (weak T):

* **Collapses at two levels commute** (`Term.collapse_collapse`), matching
  `VarSymb.collapse_collapse` on addresses.
* **Collapsing a substituted term is substituting into the collapsed term**
  (`Term.collapse_subst`, `WFF.collapse_subst`), whenever the second substitution sends each
  collapsed address to the collapsed entry of the first, up to η (`Subst.Corr`).

The first gives the `here` projection of a collapsed entry (`SubE.proj_collapse`); the second is
what substituting twice and the renaming of proofs need at a `here` step and at the T rule.
-/

namespace V12M

theorem VarSymb.collapse_ext : ∀ (w : VarSymb) (p : List Step) (k : ℕ),
    (w.ext p).collapse (k + Step.levels p) = (w.collapse k).ext p
  | _, [], _ => rfl
  | w, s :: p, k => by
      change ((VarSymb.step w s).ext p).collapse _ = (VarSymb.step (w.collapse k) s).ext p
      by_cases hs : s.isProj = true
      · rw [Step.levels_cons, if_pos hs, Nat.zero_add, VarSymb.collapse_ext (.step w s) p k,
          VarSymb.collapse_proj hs]
      · rw [Step.levels_cons, if_neg hs, show k + (1 + Step.levels p) = (k + 1) + Step.levels p
          by omega, VarSymb.collapse_ext (.step w s) p (k + 1),
          VarSymb.collapse_level_succ (Bool.eq_false_iff.mpr hs)]

variable [ModalSys]

theorem sig_var {σ : Signature} {Γ : Ctx} {v v' : VarSymb} (e : v = v')
    (h : Γ.ref v = some .Var) (h' : Γ.ref v' = some .Var) :
    (⟨_, Term.var (σ := σ) v h⟩ : Σ b, Term σ Γ .Var b) = ⟨_, Term.var v' h'⟩ := by
  subst e
  rfl

/-! ## Collapses at two levels commute -/

mutual
  theorem Func.collapse_collapse {σ : Signature} {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
      (h₁₂ : Ctx.Collapses (k + 1 + m) Γ₁ Γ₂) (h₂₃ : Ctx.Collapses m Γ₂ Γ₃)
      (h₁₄ : Ctx.Collapses m Γ₁ Γ₄) (h₄₃ : Ctx.Collapses (k + m) Γ₄ Γ₃) :
      {n : ℕ} → (f : Func σ Γ₁ n) →
      Func.collapse h₂₃ (Func.collapse h₁₂ f) = Func.collapse h₄₃ (Func.collapse h₁₄ f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.collapse h₂₃ (Func.collapse h₁₂ g))
            (Term.collapse h₂₃ (Term.collapse h₁₂ t)) =
          Func.eval (Func.collapse h₄₃ (Func.collapse h₁₄ g))
            (Term.collapse h₄₃ (Term.collapse h₁₄ t))
        rw [Func.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ g,
          eq_of_heq (Sigma.mk.inj (Term.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ t)).2]
    termination_by structural _ f => f

  /-- ⭐Collapsing at level `k + 1 + m` then `m` is collapsing at `m` then `k + m`. -/
  theorem Term.collapse_collapse {σ : Signature} {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
      (h₁₂ : Ctx.Collapses (k + 1 + m) Γ₁ Γ₂) (h₂₃ : Ctx.Collapses m Γ₂ Γ₃)
      (h₁₄ : Ctx.Collapses m Γ₁ Γ₄) (h₄₃ : Ctx.Collapses (k + m) Γ₄ Γ₃) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      (⟨_, Term.collapse h₂₃ (Term.collapse h₁₂ t)⟩ : Σ b, Term σ Γ₃ T b) =
        ⟨_, Term.collapse h₄₃ (Term.collapse h₁₄ t)⟩
    | _, _, .var v _ => sig_var (VarSymb.collapse_collapse v k m) _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.collapse h₂₃ (Func.collapse h₁₂ f))⟩ :
            Σ b, Term σ Γ₃ .Var b) = ⟨_, Term.func (Func.collapse h₄₃ (Func.collapse h₁₄ f))⟩
        rw [Func.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ s)
          (Term.collapse_collapse h₁₂ h₂₃ h₁₄ h₄₃ t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.collapse_collapse (m := m + 1) h₁₂.boxIn h₂₃.boxIn h₁₄.boxIn h₄₃.boxIn t)
    | _, _, .diatm x hx t => by
        have key : ∀ (y : VarSymb) (_hy : y = (x.collapse (k + 1 + m)).collapse m)
            (P : ∃ X, Γ₃.ref y = some (.VTypeDia X))
            (h' : Ctx.Collapses (k + m + 1) (Γ₄.diaIn (x.collapse m)) (Γ₃.diaIn y)),
            (⟨_, Term.collapse h₂₃ (Term.collapse h₁₂ (Term.diatm x hx t))⟩ :
              Σ b, Term σ Γ₃ _ b) =
              ⟨_, Term.diatm y P (Term.collapse h' (Term.collapse (h₁₄.diaIn x) t))⟩ := by
          intro y hy P h'
          subst hy
          exact sig_diatm (Term.collapse_collapse (m := m + 1) (h₁₂.diaIn x) (h₂₃.diaIn _)
            (h₁₄.diaIn x) h' t)
        exact key _ (VarSymb.collapse_collapse x k m).symm _ _
    termination_by structural _ _ t => t
end

/-! ## Collapsing and shifting commute -/

mutual
  theorem Func.collapse_shift {σ : Signature} {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
      (h₁₂ : Ctx.Shifts m Γ₁ Γ₂) (h₂₃ : Ctx.Collapses (k + 2 + m) Γ₂ Γ₃)
      (h₁₄ : Ctx.Collapses (k + 1 + m) Γ₁ Γ₄) (h₄₃ : Ctx.Shifts m Γ₄ Γ₃) :
      {n : ℕ} → (f : Func σ Γ₁ n) →
      Func.collapse h₂₃ (Func.shift h₁₂ f) = Func.shift h₄₃ (Func.collapse h₁₄ f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.collapse h₂₃ (Func.shift h₁₂ g))
            (Term.collapse h₂₃ (Term.shift h₁₂ t)) =
          Func.eval (Func.shift h₄₃ (Func.collapse h₁₄ g))
            (Term.shift h₄₃ (Term.collapse h₁₄ t))
        rw [Func.collapse_shift h₁₂ h₂₃ h₁₄ h₄₃ g,
          eq_of_heq (Sigma.mk.inj (Term.collapse_shift h₁₂ h₂₃ h₁₄ h₄₃ t)).2]
    termination_by structural _ f => f

  /-- A collapse outside a shift commutes with it. -/
  theorem Term.collapse_shift {σ : Signature} {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
      (h₁₂ : Ctx.Shifts m Γ₁ Γ₂) (h₂₃ : Ctx.Collapses (k + 2 + m) Γ₂ Γ₃)
      (h₁₄ : Ctx.Collapses (k + 1 + m) Γ₁ Γ₄) (h₄₃ : Ctx.Shifts m Γ₄ Γ₃) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      (⟨_, Term.collapse h₂₃ (Term.shift h₁₂ t)⟩ : Σ b, Term σ Γ₃ T b) =
        ⟨_, Term.shift h₄₃ (Term.collapse h₁₄ t)⟩
    | _, _, .var v _ => sig_var (VarSymb.collapse_shift v k m).symm _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.collapse h₂₃ (Func.shift h₁₂ f))⟩ :
            Σ b, Term σ Γ₃ .Var b) = ⟨_, Term.func (Func.shift h₄₃ (Func.collapse h₁₄ f))⟩
        rw [Func.collapse_shift h₁₂ h₂₃ h₁₄ h₄₃ f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.collapse_shift h₁₂ h₂₃ h₁₄ h₄₃ s) (Term.collapse_shift h₁₂ h₂₃ h₁₄ h₄₃ t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.collapse_shift (m := m + 1) h₁₂.boxIn h₂₃.boxIn h₁₄.boxIn h₄₃.boxIn t)
    | _, _, .diatm x hx t => by
        have key : ∀ (y : VarSymb) (_hy : y = (x.shift m).collapse (k + 2 + m))
            (P : ∃ X, Γ₃.ref y = some (.VTypeDia X))
            (h' : Ctx.Shifts (m + 1) (Γ₄.diaIn (x.collapse (k + 1 + m))) (Γ₃.diaIn y)),
            (⟨_, Term.collapse h₂₃ (Term.shift h₁₂ (Term.diatm x hx t))⟩ :
              Σ b, Term σ Γ₃ _ b) =
              ⟨_, Term.diatm y P (Term.shift h' (Term.collapse (h₁₄.diaIn x) t))⟩ := by
          intro y hy P h'
          subst hy
          exact sig_diatm (Term.collapse_shift (m := m + 1) (h₁₂.diaIn x) (h₂₃.diaIn _)
            (h₁₄.diaIn x) h' t)
        exact key _ (VarSymb.collapse_shift x k m) _ _
    termination_by structural _ _ t => t
end

mutual
  theorem Func.collapse_shift_self {σ : Signature} {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
      (hs : Ctx.Shifts m Γ₁ Γ₂) (hc : Ctx.Collapses (m + 1) Γ₂ Γ₃) (hle : Γ₁.Le Γ₃) :
      {n : ℕ} → (f : Func σ Γ₁ n) → Func.collapse hc (Func.shift hs f) = Func.mono hle f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.collapse hc (Func.shift hs g))
            (Term.collapse hc (Term.shift hs t)) = Func.eval (Func.mono hle g) (Term.mono hle t)
        rw [Func.collapse_shift_self hs hc hle g,
          eq_of_heq (Sigma.mk.inj (Term.collapse_shift_self hs hc hle t)).2]
    termination_by structural _ f => f

  /-- Collapsing just outside a shift undoes it. -/
  theorem Term.collapse_shift_self {σ : Signature} {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
      (hs : Ctx.Shifts m Γ₁ Γ₂) (hc : Ctx.Collapses (m + 1) Γ₂ Γ₃) (hle : Γ₁.Le Γ₃) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      (⟨_, Term.collapse hc (Term.shift hs t)⟩ : Σ b, Term σ Γ₃ T b) = ⟨_, Term.mono hle t⟩
    | _, _, .var v _ => sig_var (VarSymb.collapse_shift_self v m) _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.collapse hc (Func.shift hs f))⟩ : Σ b, Term σ Γ₃ .Var b) =
          ⟨_, Term.func (Func.mono hle f)⟩
        rw [Func.collapse_shift_self hs hc hle f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.collapse_shift_self hs hc hle s) (Term.collapse_shift_self hs hc hle t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.collapse_shift_self (m := m + 1) hs.boxIn hc.boxIn hle.boxIn t)
    | _, _, .diatm x hx t => by
        have key : ∀ (y : VarSymb) (_hy : y = (x.shift m).collapse (m + 1))
            (P : ∃ X, Γ₃.ref y = some (.VTypeDia X)) (hle' : (Γ₁.diaIn x).Le (Γ₃.diaIn y)),
            (⟨_, Term.collapse hc (Term.shift hs (Term.diatm x hx t))⟩ : Σ b, Term σ Γ₃ _ b) =
              ⟨_, Term.diatm y P (Term.mono hle' t)⟩ := by
          intro y hy P hle'
          subst hy
          exact sig_diatm (Term.collapse_shift_self (m := m + 1) (hs.diaIn x) (hc.diaIn _) hle' t)
        exact key x (VarSymb.collapse_shift_self x m).symm _ _
    termination_by structural _ _ t => t
end

/-! ## Collapsing entries -/

namespace SubE

variable {σ : Signature}

/-- Move an entry down a collapsed level. -/
def collapse {k : ℕ} {Δ Δ' : Ctx} (D : Ctx.Collapses k Δ Δ') : SubE σ Δ → SubE σ Δ'
  | .hide => .hide
  | .ren w => .ren (w.collapse k)
  | .tm s => .tm (Term.collapse D s)

theorem diaBody_diatm {Δ : Ctx} {A : VarType} {a : Ann A} (y : VarSymb)
    (hy : ∃ X, Δ.ref y = some (.VTypeDia X)) (u : Term σ (Δ.diaIn y) A a) :
    (SubE.tm (Term.diatm y hy u) : SubE σ Δ).diaBody y = SubE.tm u := by
  rw [show (SubE.tm (Term.diatm y hy u) : SubE σ Δ).diaBody y =
    SubE.tm (Term.mono (Ctx.Le.refl _) u) from dif_pos rfl, Term.mono_refl]

theorem collapse_mono {k : ℕ} {Δ₁ Δ₂ Δ₁' Δ₂' : Ctx} (D₁ : Ctx.Collapses k Δ₁ Δ₁')
    (D₂ : Ctx.Collapses k Δ₂ Δ₂') (l : Δ₁.Le Δ₂) (l' : Δ₁'.Le Δ₂') :
    ∀ (e : SubE σ Δ₁), (e.mono l).collapse D₂ = (e.collapse D₁).mono l'
  | .hide => rfl
  | .ren _ => rfl
  | .tm s => congrArg SubE.tm (Term.collapse_mono D₁ D₂ l l' s)

variable {k : ℕ} {Δ Δ' : Ctx} (D : Ctx.Collapses k Δ Δ')

theorem okRef_collapse : ∀ {e : SubE σ Δ} {T : VarType}, e.OkRef T → (e.collapse D).OkRef T
  | .ren w, _, he => D w _ he
  | .tm _, _, he => he
  | .hide, _, he => he.elim

theorem idxAlong_collapse : ∀ (e : SubE σ Δ) (p : List Step),
    (e.collapse D).idxAlong p = (e.idxAlong p).collapse (k + Step.levels p)
  | .ren w, p => (VarSymb.collapse_ext w p k).symm
  | .tm (a := a) _, p => Ann.idxAt_collapse a k p
  | .hide, _ => rfl

theorem toVar_collapse : ∀ (e : SubE σ Δ) (he : e.OkRef .Var),
    Term.collapse D (e.toVar he) = (e.collapse D).toVar (okRef_collapse D he)
  | .ren _, _ => rfl
  | .tm (.var _ _), _ => rfl
  | .tm (.func _), _ => rfl
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _), h => nomatch h
  | .tm (.diatm _ _ _), h => nomatch h
  | .hide, h => False.elim h

theorem unbox_collapse : ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) →
    e.unbox.collapse D.boxIn = (e.collapse D).unbox
  | .ren w, _, _ => by
      change SubE.ren (w.inner.collapse (k + 1)) = SubE.ren (w.collapse k).inner
      rw [VarSymb.inner_collapse_succ]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem keepE_collapse : ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) →
    e.keepE.collapse D.boxIn = (e.collapse D).keepE
  | .ren w, _, _ => by
      change SubE.ren ((VarSymb.step w .keep).collapse (k + 1)) =
        SubE.ren (.step (w.collapse k) .keep)
      rw [VarSymb.collapse_level_succ rfl]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          change (SubE.tm (Term.boxtm t)).keepE.collapse D.boxIn =
            (SubE.tm (Term.boxtm (Term.collapse D.boxIn t))).keepE
          by_cases hF : ModalSys.Four = true
          · rw [keepE_tm _ hF, keepE_tm _ hF]
            exact tm_eq_of_sig (sig_boxtm (Term.collapse_shift (k := k) (m := 0)
              (Ctx.shifts_boxIn_boxIn hF Δ) D.boxIn.boxIn D.boxIn
              (Ctx.shifts_boxIn_boxIn hF Δ') t))
          · rw [show (SubE.tm (Term.boxtm t) : SubE σ Δ).keepE = .hide from dif_neg hF,
              show (SubE.tm (Term.boxtm (Term.collapse D.boxIn t)) : SubE σ Δ').keepE = .hide
                from dif_neg hF]
            rfl

/-- The `here` projection of a collapsed entry. -/
theorem proj_collapse : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step}, e.OkRef U →
    s.isProj = true → U.step s = some T → (e.proj s).collapse D = (e.collapse D).proj s
  | .ren w, _, _, s, _, hs, _ => by
      change SubE.ren ((VarSymb.step w s).collapse k) = SubE.ren (.step (w.collapse k) s)
      rw [VarSymb.collapse_proj hs]
  | .hide, _, _, _, he, _, _ => False.elim he
  | .tm (T := U') s₀, U, T, s, he, hs, hst => by
      have hU : U' = U := he
      subst hU
      cases s with
      | fst =>
          cases s₀ <;> cases hst
          rfl
      | snd =>
          cases s₀ <;> cases hst
          rfl
      | box => cases hs
      | dia => cases hs
      | keep => cases hs
      | here =>
          cases s₀ with
          | boxtm t =>
              obtain ⟨hT, hAT⟩ := VarType.step_here hst
              subst hAT
              change ((SubE.tm (Term.boxtm t)).proj .here).collapse D =
                (SubE.tm (Term.boxtm (Term.collapse D.boxIn t))).proj .here
              rw [proj_boxtm_here _ hT, proj_boxtm_here _ hT]
              exact tm_eq_of_sig (Term.collapse_collapse (m := 0) D.boxIn
                (Ctx.collapses_boxIn_self hT Δ') (Ctx.collapses_boxIn_self hT Δ) D t).symm
          | _ => cases hst

theorem diaBody_collapse {ιx : VarSymb} : ∀ {e : SubE σ Δ} {X : VarType},
    e.OkRef (.VTypeDia X) → e.idxAlong [] = ιx →
    (e.diaBody ιx).collapse (D.diaIn ιx) = (e.collapse D).diaBody (ιx.collapse k)
  | .ren w, _, _, hw => by
      have hw' : w = ιx := hw
      subst hw'
      change SubE.ren ((VarSymb.step w .dia).collapse (k + 1)) =
        SubE.ren (.step (w.collapse k) .dia)
      rw [VarSymb.collapse_level_succ rfl]
  | .tm (.diatm y hy u), _, _, hw => by
      have hyx : y = ιx := hw
      subst hyx
      rw [diaBody_diatm]
      change SubE.tm (Term.collapse (D.diaIn y) u) =
        (SubE.tm (Term.diatm (y.collapse k) _ (Term.collapse (D.diaIn y) u))).diaBody (y.collapse k)
      rw [diaBody_diatm]
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

theorem Sim.collapse {T : VarType} {e e' : SubE σ Δ} (h : Sim T e e') :
    Sim T (e.collapse D) (e'.collapse D) := by
  cases h with
  | refl => exact .refl _
  | eta_ren w hw =>
      change Sim T (SubE.tm (Term.collapse D (Term.eta w T hw))) (.ren (w.collapse k))
      rw [tm_eq_of_sig (Term.collapse_eta D w T hw)]
      exact .eta_ren _ _
  | ren_eta w hw =>
      change Sim T (.ren (w.collapse k)) (SubE.tm (Term.collapse D (Term.eta w T hw)))
      rw [tm_eq_of_sig (Term.collapse_eta D w T hw)]
      exact .ren_eta _ _

end SubE

/-! ## Substitutions corresponding across a collapse -/

namespace Subst

variable {σ : Signature}

theorem at_under_ne {Δ : Ctx} (θ : Subst σ Δ) {d d' : ℕ} (T : VarType)
    (h : Δ (.root (.bnd d')) = none) :
    ∀ {v : VarSymb}, v.rt ≠ .bnd d → (θ.under d d' T h).at v = (θ.at v).mono (Ctx.le_insert h T)
  | .root r, hv => by
      change (if VarSymb.root r = .root (.bnd d) then _ else _) = _
      rw [if_neg (fun he => hv (by cases he; rfl))]
      rfl
  | .step v s, hv => by
      simp only [Subst.at]
      split_ifs
      · rw [at_under_ne θ T h (v := v) hv, SubE.proj_mono]
      · change (if VarSymb.step v s = .root (.bnd d) then _ else _) = _
        rw [if_neg (fun he => by cases he)]

/-- `θ'` substitutes each collapsed address as `θ` substitutes the address, collapsed. -/
def Corr {k : ℕ} (Γ : Ctx) {Δ Δ' : Ctx} (D : Ctx.Collapses k Δ Δ') (θ : Subst σ Δ)
    (θ' : Subst σ Δ') : Prop :=
  ∀ v T, Γ.ref v = some T → SubE.Sim T (θ'.at (v.collapse k)) ((θ.at v).collapse D)

variable {k : ℕ} {Γ Δ Δ' : Ctx} {D : Ctx.Collapses k Δ Δ'} {θ : Subst σ Δ} {θ' : Subst σ Δ'}

theorem corr_of (hθ : Ok Γ θ)
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T →
      SubE.Sim T (θ'.at (v.collapse k)) ((θ v).collapse D)) :
    Corr Γ D θ θ' := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            rw [VarSymb.collapse_proj hs]
            change SubE.Sim T (if s.isProj then (θ'.at (v.collapse k)).proj s else θ' _)
              ((if s.isProj then (θ.at v).proj s else θ _).collapse D)
            rw [if_pos hs, if_pos hs, SubE.proj_collapse D (okRef_at hθ hU) hs hv]
            exact (ih U hU).proj_step hs hv
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [at_nonproj θ hlp]
        exact hvis _ _ hlp (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

theorem corr_box (hθ : Ok Γ θ) (hcr : Corr Γ D θ θ') :
    Corr Γ.boxIn D.boxIn θ.box θ'.box := by
  refine corr_of (ok_box hθ) ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      change SubE.Sim T (θ'.at (u.collapse k)).unbox ((θ.at u).unbox.collapse D.boxIn)
      rw [SubE.unbox_collapse D (okRef_at hθ hu)]
      exact (hcr u _ hu).unbox
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      change SubE.Sim (.VTypeBox A) (θ'.at (u.collapse k)).keepE
        ((θ.at u).keepE.collapse D.boxIn)
      rw [SubE.keepE_collapse D (okRef_at hθ hu)]
      exact (hcr u _ hu).keepE hF
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem corr_dia (hθ : Ok Γ θ) (hcr : Corr Γ D θ θ') {x ιx : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = ιx)
    (hw' : (θ'.at (x.collapse k)).idxAlong [] = ιx.collapse k) :
    Corr (Γ.diaIn x) (D.diaIn ιx) (θ.dia x ιx) (θ'.dia (x.collapse k) (ιx.collapse k)) := by
  refine corr_of (ok_dia hθ hx hw) ?_
  obtain ⟨X, hX⟩ := hx
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      rw [hX] at hv
      cases hv
      change SubE.Sim X
        (if u.collapse k = u.collapse k then (θ'.at (u.collapse k)).diaBody (ιx.collapse k)
          else SubE.hide)
        ((if u = u then (θ.at u).diaBody ιx else SubE.hide).collapse (D.diaIn ιx))
      rw [if_pos rfl, if_pos rfl, SubE.diaBody_collapse D (okRef_at hθ hX) hw]
      exact (hcr u _ hX).diaBody hw'
  | .step u .box =>
      have hu := Ctx.boxIn_step_box (Γ := Γ) hv
      change SubE.Sim T ((θ'.at (u.collapse k)).unbox.mono (Ctx.le_boxIn_diaIn Δ' (ιx.collapse k)))
        ((((θ.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ ιx)).collapse (D.diaIn ιx))
      rw [SubE.collapse_mono D.boxIn (D.diaIn ιx) (Ctx.le_boxIn_diaIn Δ ιx)
          (Ctx.le_boxIn_diaIn Δ' (ιx.collapse k)), SubE.unbox_collapse D (okRef_at hθ hu)]
      exact ((hcr u _ hu).unbox).mono _
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      change SubE.Sim (.VTypeBox A)
        ((θ'.at (u.collapse k)).keepE.mono (Ctx.le_boxIn_diaIn Δ' (ιx.collapse k)))
        ((((θ.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ ιx)).collapse (D.diaIn ιx))
      rw [SubE.collapse_mono D.boxIn (D.diaIn ιx) (Ctx.le_boxIn_diaIn Δ ιx)
          (Ctx.le_boxIn_diaIn Δ' (ιx.collapse k)), SubE.keepE_collapse D (okRef_at hθ hu)]
      exact ((hcr u _ hu).keepE hF).mono _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem corr_under (hθ : Ok Γ θ) (hcr : Corr Γ D θ θ') {d d' : ℕ} (hΓ : Γ.SlotsFrom d)
    (T : VarType) (h : Δ (.root (.bnd d')) = none) (h' : Δ' (.root (.bnd d')) = none)
    (hr : Δ.RootFresh (.bnd d')) :
    Corr (Γ.insert (.bnd d) T) (D.insert hr T) (θ.under d d' T h) (θ'.under d d' T h') := by
  refine corr_of (ok_under hθ T h) ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    change SubE.Sim U ((θ'.under d d' T h') (.root (.bnd d)))
      ((θ.under d d' T h (.root (.bnd d))).collapse (D.insert hr T))
    rw [show θ'.under d d' T h' (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl,
      show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ .bnd d := fun he => by
      rw [hΓ v d he le_rfl] at hv'
      cases hv'
    rw [at_under_ne θ' T h' (by rwa [VarSymb.collapse_rt]),
      show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      SubE.collapse_mono D (D.insert hr T) (Ctx.le_insert h T) (Ctx.le_insert h' T)]
    have h₁ := hcr v U ((Ctx.ref_nonproj Γ hlp).trans hv')
    rw [at_nonproj θ hlp] at h₁
    exact h₁.mono _

end Subst

/-! ## Collapsing a substituted term -/

section CollapseSubst

variable {σ : Signature}

mutual
  theorem Func.collapse_subst {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ Δ' : Ctx}
      (C : Ctx.Collapses k Γ Γ') (D : Ctx.Collapses k Δ Δ')
      (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
      (θ' : Subst σ Δ') (hθ' : Subst.Ok Γ' θ') (hc' : Subst.Coh ι' Γ' θ')
      (hcr : Subst.Corr Γ D θ θ') :
      {n : ℕ} → (f : Func σ Γ n) →
      Func.collapse D (Func.subst ι θ hθ hc f) = Func.subst ι' θ' hθ' hc' (Func.collapse C f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.collapse D (Func.subst ι θ hθ hc g))
            (Term.collapse D (Term.subst ι θ hθ hc t)) =
          Func.eval (Func.subst ι' θ' hθ' hc' (Func.collapse C g))
            (Term.subst ι' θ' hθ' hc' (Term.collapse C t))
        rw [Func.collapse_subst C D θ hθ hc θ' hθ' hc' hcr g,
          eq_of_heq (Sigma.mk.inj (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)).2]
    termination_by structural _ f => f

  /-- ⭐Collapsing a substituted term is substituting the corresponding entries into the
      collapsed term. -/
  theorem Term.collapse_subst {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ Δ' : Ctx}
      (C : Ctx.Collapses k Γ Γ') (D : Ctx.Collapses k Δ Δ')
      (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
      (θ' : Subst σ Δ') (hθ' : Subst.Ok Γ' θ') (hc' : Subst.Coh ι' Γ' θ')
      (hcr : Subst.Corr Γ D θ θ') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.collapse D (Term.subst ι θ hθ hc t)⟩ : Σ b, Term σ Δ' T b) =
        ⟨_, Term.subst ι' θ' hθ' hc' (Term.collapse C t)⟩
    | _, _, .var v hv =>
        congrArg (Sigma.mk _) ((SubE.toVar_collapse D _ _).trans ((hcr v _ hv).toVar _ _).symm)
    | _, _, .func f => by
        change (⟨_, Term.func (Func.collapse D (Func.subst ι θ hθ hc f))⟩ :
            Σ b, Term σ Δ' .Var b) = ⟨_, Term.func (Func.subst ι' θ' hθ' hc' (Func.collapse C f))⟩
        rw [Func.collapse_subst C D θ hθ hc θ' hθ' hc' hcr f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr s)
          (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.collapse_subst C.boxIn D.boxIn θ.box (Subst.ok_box hθ)
          (Subst.coh_box hθ hc) θ'.box (Subst.ok_box hθ') (Subst.coh_box hθ' hc')
          (Subst.corr_box hθ hcr) t)
    | _, _, .diatm x hx t => by
        have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
        have hwι : ι' (x.collapse k) = (ι x).collapse k := hx.elim fun _ hX => by
          have h₁ := hc' (x.collapse k) _ (C x _ hX) []
          have h₂ := (hcr x _ hX).idx
          rw [SubE.idxAlong_collapse, hw] at h₂
          exact h₁.symm.trans h₂
        have hw' : (θ'.at (x.collapse k)).idxAlong [] = (ι x).collapse k :=
          hx.elim fun _ hX => (hc' _ _ (C x _ hX) []).trans hwι
        have key : ∀ (y : VarSymb) (_hy : y = (ι x).collapse k)
            (P : ∃ Y, Δ'.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ'.diaIn (x.collapse k)) (θ'.dia (x.collapse k) y))
            (q : Subst.Coh ι' (Γ'.diaIn (x.collapse k)) (θ'.dia (x.collapse k) y)),
            (⟨_, Term.collapse D (Term.subst ι θ hθ hc (Term.diatm x hx t))⟩ :
              Σ b, Term σ Δ' _ b) =
              ⟨_, Term.diatm y P
                (Term.subst ι' (θ'.dia (x.collapse k) y) p q (Term.collapse (C.diaIn x) t))⟩ := by
          intro y hy P p q
          subst hy
          exact sig_diatm (Term.collapse_subst (C.diaIn x) (D.diaIn (ι x)) (θ.dia x (ι x))
            (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
            (θ'.dia (x.collapse k) ((ι x).collapse k)) p q
            (Subst.corr_dia hθ hcr hx hw hw') t)
        exact key _ hwι _ _ _
    termination_by structural _ _ t => t
end

theorem Term.collapse_subst_var {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ Δ' : Ctx}
    (C : Ctx.Collapses k Γ Γ') (D : Ctx.Collapses k Δ Δ')
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (θ' : Subst σ Δ') (hθ' : Subst.Ok Γ' θ') (hc' : Subst.Coh ι' Γ' θ')
    (hcr : Subst.Corr Γ D θ θ') (t : Term σ Γ .Var .var) :
    Term.collapse D (Term.subst ι θ hθ hc t) = Term.subst ι' θ' hθ' hc' (Term.collapse C t) :=
  eq_of_heq (Sigma.mk.inj (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)).2

theorem Rel.collapse_subst {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ Δ' : Ctx}
    (C : Ctx.Collapses k Γ Γ') (D : Ctx.Collapses k Δ Δ')
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (θ' : Subst σ Δ') (hθ' : Subst.Ok Γ' θ') (hc' : Subst.Coh ι' Γ' θ')
    (hcr : Subst.Corr Γ D θ θ') :
    {n : ℕ} → (ρ : Rel σ Γ n) →
    Rel.collapse D (Rel.subst ι θ hθ hc ρ) = Rel.subst ι' θ' hθ' hc' (Rel.collapse C ρ)
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.collapse D (Rel.subst ι θ hθ hc ρ))
          (Term.collapse D (Term.subst ι θ hθ hc t)) =
        Rel.eval (Rel.subst ι' θ' hθ' hc' (Rel.collapse C ρ))
          (Term.subst ι' θ' hθ' hc' (Term.collapse C t))
      rw [Rel.collapse_subst C D θ hθ hc θ' hθ' hc' hcr ρ,
        Term.collapse_subst_var C D θ hθ hc θ' hθ' hc' hcr t]

/-- ⭐Collapsing a substituted formula is substituting into the collapsed formula. -/
theorem WFF.collapse_subst : {k : ℕ} → {ι ι' : VarSymb → VarSymb} → {Γ Γ' Δ Δ' : Ctx} →
    {d d' : ℕ} → (C : Ctx.Collapses k Γ Γ') → (D : Ctx.Collapses k Δ Δ') →
    (θ : Subst σ Δ) → (hθ : Subst.Ok Γ θ) → (hc : Subst.Coh ι Γ θ) →
    (θ' : Subst σ Δ') → (hθ' : Subst.Ok Γ' θ') → (hc' : Subst.Coh ι' Γ' θ') →
    (hΓ : Γ.SlotsFrom d) → (hΓ' : Γ'.SlotsFrom d) → (hΔ : Δ.SlotsFrom d') →
    (hΔ' : Δ'.SlotsFrom d') → Subst.Corr Γ D θ θ' → (φ : WFF σ Γ d) →
    WFF.collapse D hΔ (WFF.subst ι θ hθ hc hΓ hΔ φ) =
      WFF.subst ι' θ' hθ' hc' hΓ' hΔ' (WFF.collapse C hΓ φ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr, .atom ρ =>
      congrArg WFF.atom (Rel.collapse_subst C D θ hθ hc θ' hθ' hc' hcr ρ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr, .eq t s =>
      congrArg₂ WFF.eq (Term.collapse_subst_var C D θ hθ hc θ' hθ' hc' hcr t)
        (Term.collapse_subst_var C D θ hθ hc θ' hθ' hc' hcr s)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .and φ ψ =>
      congrArg₂ WFF.and (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ)
        (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .or φ ψ =>
      congrArg₂ WFF.or (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ)
        (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ)
        (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ)
  | _, _, _, _, _, _, _, d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .all T φ =>
      congrArg (WFF.all T) (WFF.collapse_subst (C.insert (hΓ.rootFresh le_rfl) T)
        (D.insert (hΔ.rootFresh le_rfl) T) (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (θ'.under d d' T hΔ'.root) (Subst.ok_under hθ' T hΔ'.root)
        (Subst.coh_under hθ' hc' hΓ' T hΔ'.root) (hΓ.insert T) (hΓ'.insert T) (hΔ.insert T)
        (hΔ'.insert T)
        (Subst.corr_under hθ hcr hΓ T hΔ.root hΔ'.root (hΔ.rootFresh le_rfl)) φ)
  | _, _, _, _, _, _, _, d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .ex T φ =>
      congrArg (WFF.ex T) (WFF.collapse_subst (C.insert (hΓ.rootFresh le_rfl) T)
        (D.insert (hΔ.rootFresh le_rfl) T) (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (θ'.under d d' T hΔ'.root) (Subst.ok_under hθ' T hΔ'.root)
        (Subst.coh_under hθ' hc' hΓ' T hΔ'.root) (hΓ.insert T) (hΓ'.insert T) (hΔ.insert T)
        (hΔ'.insert T)
        (Subst.corr_under hθ hcr hΓ T hΔ.root hΔ'.root (hΔ.rootFresh le_rfl)) φ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .box φ =>
      congrArg WFF.box (WFF.collapse_subst C.boxIn D.boxIn θ.box (Subst.ok_box hθ)
        (Subst.coh_box hθ hc) θ'.box (Subst.ok_box hθ') (Subst.coh_box hθ' hc') hΓ.boxIn
        hΓ'.boxIn hΔ.boxIn hΔ'.boxIn (Subst.corr_box hθ hcr) φ)
  | k, ι, ι', Γ, Γ', Δ, Δ', _, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .dia x hx φ => by
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hwι : ι' (x.collapse k) = (ι x).collapse k := hx.elim fun _ hX => by
        have h₁ := hc' (x.collapse k) _ (C x _ hX) []
        have h₂ := (hcr x _ hX).idx
        rw [SubE.idxAlong_collapse, hw] at h₂
        exact h₁.symm.trans h₂
      have hw' : (θ'.at (x.collapse k)).idxAlong [] = (ι x).collapse k :=
        hx.elim fun _ hX => (hc' _ _ (C x _ hX) []).trans hwι
      have key : ∀ (y : VarSymb) (_hy : y = (ι x).collapse k)
          (P : ∃ Y, Δ'.ref y = some (.VTypeDia Y))
          (p : Subst.Ok (Γ'.diaIn (x.collapse k)) (θ'.dia (x.collapse k) y))
          (q : Subst.Coh ι' (Γ'.diaIn (x.collapse k)) (θ'.dia (x.collapse k) y))
          (hΔy : (Δ'.diaIn y).SlotsFrom d'),
          WFF.collapse D hΔ (WFF.subst ι θ hθ hc hΓ hΔ (.dia x hx φ)) =
            .dia y P (WFF.subst ι' (θ'.dia (x.collapse k) y) p q (hΓ'.diaIn (x.collapse k)) hΔy
              (WFF.collapse (C.diaIn x) (hΓ.diaIn x) φ)) := by
        intro y hy P p q hΔy
        subst hy
        exact congrArg (WFF.dia ((ι x).collapse k) _) (WFF.collapse_subst (C.diaIn x)
          (D.diaIn (ι x)) (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (θ'.dia (x.collapse k) ((ι x).collapse k)) p q (hΓ.diaIn x) (hΓ'.diaIn (x.collapse k))
          (hΔ.diaIn (ι x)) hΔy (Subst.corr_dia hθ hcr hx hw hw') φ)
      exact key _ hwι _ _ _ _
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr, .here hT hA s t =>
      WFF.here_congr hT hA (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr s)
        (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)

end CollapseSubst

end V12M
