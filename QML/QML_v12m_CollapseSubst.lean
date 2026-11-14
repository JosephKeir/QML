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

theorem VarSymb.collapse_ext [ModalSys] : ∀ (w : VarSymb) (p : List Step) (k : ℕ),
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

/-- `keepE_collapse` at any keepable type: a kept possible entry `◇_y t` collapses along
    `y.keep`, its shifted body collapsed one level further in (`Term.collapse_shift`). -/
theorem keepE_collapse' : ∀ {e : SubE σ Δ} {T : VarType}, T.keepable = true → e.OkRef T →
    e.keepE.collapse D.boxIn = (e.collapse D).keepE
  | .ren w, _, _, _ => by
      change SubE.ren ((VarSymb.step w .keep).collapse (k + 1)) =
        SubE.ren (.step (w.collapse k) .keep)
      rw [VarSymb.collapse_level_succ rfl]
  | .hide, _, _, he => False.elim he
  | .tm (T := U) s, T, hk, he => by
      have hU : U = T := he
      subst hU
      cases U with
      | VTypeBox A => exact keepE_collapse D (e := .tm s) rfl
      | VTypeDia A =>
          cases s with
          | diatm y hy t =>
              change (SubE.tm (Term.diatm y hy t)).keepE.collapse D.boxIn =
                (SubE.tm (Term.diatm (y.collapse k) _ (Term.collapse (D.diaIn y) t))).keepE
              by_cases hK : ModalSys.Four = true
              · have hF := hK
                rw [keepE_dia _ _ _ hF, keepE_dia _ _ _ hF]
                exact tm_eq_of_sig (sig_diatm (Term.collapse_shift (k := k) (m := 0)
                  (Ctx.shifts_diaIn_keep hF Δ y) (D.boxIn.diaIn (.step y .keep)) (D.diaIn y)
                  (Ctx.shifts_diaIn_keep hF Δ' (y.collapse k)) t))
              · rw [keepE_dia_off _ _ _ hK, keepE_dia_off _ _ _ hK]
                rfl
      | _ => cases hk

/-- The `here` projection of a collapsed entry. -/
theorem proj_collapse : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step}, e.OkRef U →
    s.isStruct = true → U.step s = some T → (e.proj s).collapse D = (e.collapse D).proj s
  | .ren w, _, _, s, _, hs, _ => by
      change SubE.ren ((VarSymb.step w s).collapse k) = SubE.ren (.step (w.collapse k) s)
      rw [VarSymb.collapse_proj (Step.isProj_of_isStruct hs)]
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
      | «at» => cases hs
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

/-- A witness entry's content, read one view in and collapsed further in, is the collapsed
    entry's (M2). -/
theorem toWit_optBody_collapse (hO : ModalSys.Opt = true) {z : VarSymb} {Z : VarType}
    (hz : Δ.boxIn.wit z = some Z) :
    ∀ {e : SubE σ Δ} {X : VarType}, e.OkRef (.VTypeDia X) → e.idxAlong [] = z →
      (e.toWit.optBody z).collapse (D.boxIn.optIn_succ hz) =
        (e.collapse D).toWit.optBody (z.collapse k)
  | .ren w, _, _, hw => by
      have hw' : w = z := hw
      subst hw'
      change SubE.ren ((VarSymb.step w .dia).collapse (k + 1)) =
        SubE.ren (.step (w.collapse k) .dia)
      rw [VarSymb.collapse_level_succ rfl]
  | .tm (.diatm x hx b), _, _, hw => by
      have hxz : x = z := hw
      subst hxz
      obtain ⟨Y, hY⟩ := id hx
      have hY' : Δ'.ref (x.collapse k) = some (.VTypeDia Y) := D x _ hY
      rw [show (SubE.tm (Term.diatm x hx b) : SubE σ Δ).toWit =
          WitE.tm x (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) b) from dif_pos hO,
        show (WitE.tm x (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) b) :
            WitE σ Δ.boxIn).optBody x =
          SubE.tm (Term.mono (Ctx.Le.refl _) (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY) b))
          from dif_pos rfl]
      change SubE.tm (Term.collapse _ _) =
        (SubE.tm (Term.diatm (x.collapse k) ⟨Y, hY'⟩ (Term.collapse (D.diaIn x) b))).toWit.optBody
          (x.collapse k)
      rw [show (SubE.tm (Term.diatm (x.collapse k) ⟨Y, hY'⟩ (Term.collapse (D.diaIn x) b)) :
            SubE σ Δ').toWit = WitE.tm (x.collapse k)
            (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY') (Term.collapse (D.diaIn x) b))
          from dif_pos hO,
        show (WitE.tm (x.collapse k)
            (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY') (Term.collapse (D.diaIn x) b)) :
            WitE σ Δ'.boxIn).optBody (x.collapse k) =
          SubE.tm (Term.mono (Ctx.Le.refl _)
            (Term.mono (Ctx.le_diaIn_boxIn_optIn hO hY') (Term.collapse (D.diaIn x) b)))
          from dif_pos rfl,
        Term.mono_refl, Term.mono_refl]
      exact congrArg SubE.tm (Term.collapse_mono (D.diaIn x) _ _ _ b)
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

/-- A possible object's identity content, collapsed further in, is the collapsed entry's (M2). -/
theorem atBody_collapse {z : VarSymb} {Z : VarType} (hz : Δ.witT z = some Z) :
    ∀ {e : SubE σ Δ} {X : VarType}, e.OkRef (.VTypeDia X) → e.idxAlong [] = z →
      (e.atBody z).collapse (D.optInT hz) = (e.collapse D).atBody (z.collapse k)
  | .ren w, _, _, hw => by
      have hw' : w = z := hw
      subst hw'
      change SubE.ren ((VarSymb.step w .at).collapse k) = SubE.ren (.step (w.collapse k) .at)
      rw [VarSymb.collapse_proj rfl]
  | .tm (.diatm x hx b), _, _, hw => by
      have hxz : x = z := hw
      subst hxz
      obtain ⟨hT, hO, -⟩ := Ctx.witT_spec hz
      obtain ⟨Y, hY⟩ := id hx
      have hY' : Δ'.ref (x.collapse k) = some (.VTypeDia Y) := D x _ hY
      rw [show (SubE.tm (Term.diatm x hx b) : SubE σ Δ).atBody x =
          SubE.tm (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ hx) b)
          from dif_pos ⟨hT, hO, rfl⟩]
      change SubE.tm (Term.collapse _ _) =
        (SubE.tm (Term.diatm (x.collapse k) ⟨Y, hY'⟩ (Term.collapse (D.diaIn x) b))).atBody
          (x.collapse k)
      rw [show (SubE.tm (Term.diatm (x.collapse k) ⟨Y, hY'⟩ (Term.collapse (D.diaIn x) b)) :
            SubE σ Δ').atBody (x.collapse k) =
          SubE.tm (Term.collapse (Ctx.collapses_diaIn_optInT' ⟨hT, hO, rfl⟩ ⟨Y, hY'⟩)
            (Term.collapse (D.diaIn x) b)) from dif_pos ⟨hT, hO, rfl⟩]
      exact SubE.tm_eq_of_sig (Term.collapse_collapse (k := k) (m := 0) (D.diaIn x) _ _
        (D.optInT hz) b).symm
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

theorem Sim.okRef_left {T : VarType} {e e' : SubE σ Δ} (h : Sim T e e') (he : e'.OkRef T) :
    e.OkRef T := by
  cases h with
  | refl => exact he
  | eta_ren w h => rfl
  | ren_eta w h => exact h

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
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            rw [VarSymb.collapse_proj (Step.isProj_of_isStruct hs)]
            change SubE.Sim T (if s.isStruct then (θ'.at (v.collapse k)).proj s else θ' _)
              ((if s.isStruct then (θ.at v).proj s else θ _).collapse D)
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
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      change SubE.Sim T (θ'.at (u.collapse k)).keepE
        ((θ.at u).keepE.collapse D.boxIn)
      rw [SubE.keepE_collapse' D hk (okRef_at hθ hu)]
      exact (hcr u _ hu).keepE' hF hk
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
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      change SubE.Sim T
        ((θ'.at (u.collapse k)).keepE.mono (Ctx.le_boxIn_diaIn Δ' (ιx.collapse k)))
        ((((θ.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ ιx)).collapse (D.diaIn ιx))
      rw [SubE.collapse_mono D.boxIn (D.diaIn ιx) (Ctx.le_boxIn_diaIn Δ ιx)
          (Ctx.le_boxIn_diaIn Δ' (ιx.collapse k)), SubE.keepE_collapse' D hk (okRef_at hθ hu)]
      exact ((hcr u _ hu).keepE' hF hk).mono _
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
  · have hv' : Γ v = some U := Ctx.insert_ne_some hv hvr
    have hrt : v.rt ≠ .bnd d := fun he => by
      rw [hΓ v d he le_rfl] at hv'
      cases hv'
    rw [at_under_ne θ' T h' (by rwa [VarSymb.collapse_rt]),
      show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      SubE.collapse_mono D (D.insert hr T) (Ctx.le_insert h T) (Ctx.le_insert h' T)]
    have h₁ := hcr v U ((Ctx.ref_nonproj Γ hlp).trans hv')
    rw [at_nonproj θ hlp] at h₁
    exact h₁.mono _

/-! ### Witnesses (M2, docs §12.30) -/

/-- ⭐**The witnesses of a correspondence** (M2): along the collapsed arrow, the image of a
    possible object read at the identity arrow is the witness's content collapsed; further in,
    the collapsed witness's content is the witness's content collapsed. -/
def CorrW : {k : ℕ} → Ctx → {Δ Δ' : Ctx} → Ctx.Collapses k Δ Δ' → Subst σ Δ → Subst σ Δ' →
    Prop
  | 0, Γ, Δ, _, D, θ, θ' => ∀ y X, Γ.wit y = some X → ∀ (hO : ModalSys.Opt = true) (z : VarSymb),
      (θ.wit y).idxAlong [] = z → (θ'.at y).idxAlong [] = z ∧
      ∃ (Z : VarType) (hz : Δ.wit z = some Z),
        SubE.Sim X ((θ'.at y).atBody z) (((θ.wit y).optBody z).collapse (D.optIn_zero hO hz))
  | k + 1, Γ, Δ, _, D, θ, θ' => ∀ y X, Γ.wit y = some X → ∀ z : VarSymb,
      (θ.wit y).idxAlong [] = z → (θ'.wit (y.collapse k)).idxAlong [] = z.collapse k ∧
      ∃ (Z : VarType) (hz : Δ.wit z = some Z),
        SubE.Sim X ((θ'.wit (y.collapse k)).optBody (z.collapse k))
          (((θ.wit y).optBody z).collapse (D.optIn_succ hz))

/-- ⭐A correspondence's witnesses pass to weakened substitutions with the same witnesses: every
    view but the `□` and `◇` ones. -/
theorem CorrW.transfer {k : ℕ} {Γ Γ₁ Δ₀ Δ₀' Δ₁ Δ₁' : Ctx} {D₀ : Ctx.Collapses k Δ₀ Δ₀'}
    {D₁ : Ctx.Collapses k Δ₁ Δ₁'} {θ₀ : Subst σ Δ₀} {θ₀' : Subst σ Δ₀'} {θ₁ : Subst σ Δ₁}
    {θ₁' : Subst σ Δ₁'} (l : Δ₀.Le Δ₁) (l' : Δ₀'.Le Δ₁') (hcw : CorrW Γ D₀ θ₀ θ₀')
    (hΓ : ∀ y, Γ₁.wit y = Γ.wit y) (hw : ∀ y, θ₁.wit y = (θ₀.wit y).mono l)
    (h0 : k = 0 → ∀ y X, Γ.wit y = some X → θ₁'.at y = (θ₀'.at y).mono l')
    (hs : ∀ k', k = k' + 1 → ∀ y X, Γ.wit y = some X →
      θ₁'.wit (y.collapse k') = (θ₀'.wit (y.collapse k')).mono l') :
    CorrW Γ₁ D₁ θ₁ θ₁' := by
  cases k with
  | zero =>
      intro y X hy hO z hzi
      rw [hΓ] at hy
      rw [hw y, WitE.idxAlong_mono] at hzi
      obtain ⟨hi, Z, hz, hsim⟩ := hcw y X hy hO z hzi
      refine ⟨by rw [h0 rfl y X hy, SubE.idxAlong_mono]; exact hi, Z, l.wit _ _ hz, ?_⟩
      rw [h0 rfl y X hy, hw y, ← SubE.atBody_mono, ← WitE.optBody_mono,
        SubE.collapse_mono (D₀.optIn_zero hO hz) (D₁.optIn_zero hO (l.wit _ _ hz)) (l.optIn _)
          (l'.optInT _)]
      exact hsim.mono _
  | succ k =>
      intro y X hy z hzi
      rw [hΓ] at hy
      rw [hw y, WitE.idxAlong_mono] at hzi
      obtain ⟨hi, Z, hz, hsim⟩ := hcw y X hy z hzi
      refine ⟨by rw [hs k rfl y X hy, WitE.idxAlong_mono]; exact hi, Z, l.wit _ _ hz, ?_⟩
      rw [hs k rfl y X hy, hw y, ← WitE.optBody_mono, ← WitE.optBody_mono,
        SubE.collapse_mono (D₀.optIn_succ hz) (D₁.optIn_succ (l.wit _ _ hz)) (l.optIn _)
          (l'.optIn _)]
      exact hsim.mono _


/-- The `□` view's witnesses correspond: they are the possible objects' entries. -/
theorem CorrW.box (hθ : Ok Γ θ) (hcr : Corr Γ D θ θ') :
    CorrW Γ.boxIn D.boxIn θ.box θ'.box := by
  intro y X hy z hzi
  obtain ⟨hO, hr⟩ := Ctx.boxIn_wit.mp hy
  have hsim := hcr y _ hr
  have he := okRef_at hθ hr
  have he' : (θ'.at (y.collapse k)).OkRef (.VTypeDia X) :=
    hsim.okRef_left (SubE.okRef_collapse D he)
  have hzi' : (θ.at y).idxAlong [] = z := (SubE.idxAlong_toWit hO [] he).symm.trans hzi
  have hi : (θ'.at (y.collapse k)).idxAlong [] = z.collapse k := by
    rw [hsim.idx, SubE.idxAlong_collapse, hzi']
    rfl
  have hi' : (θ'.at (y.collapse k)).toWit.idxAlong [] = z.collapse k :=
    (SubE.idxAlong_toWit hO [] he').trans hi
  refine ⟨hi', ?_⟩
  obtain ⟨Z, hZ⟩ := WitE.wit_of (SubE.okW_toWit hO he) hzi
  refine ⟨Z, hZ, ?_⟩
  change SubE.Sim X ((θ'.at (y.collapse k)).toWit.optBody (z.collapse k))
    (((θ.at y).toWit.optBody z).collapse (D.boxIn.optIn_succ hZ))
  rw [SubE.toWit_optBody_collapse D hO hZ he hzi']
  exact (hsim.toWit hO).optBody hi'

/-- The `◇_x` view's witnesses are the `□` view's. -/
theorem CorrW.dia (hθ : Ok Γ θ) (hcr : Corr Γ D θ θ') (x ιx : VarSymb) :
    CorrW (Γ.diaIn x) (D.diaIn ιx) (θ.dia x ιx) (θ'.dia (x.collapse k) (ιx.collapse k)) :=
  CorrW.transfer (Ctx.le_boxIn_diaIn Δ ιx) (Ctx.le_boxIn_diaIn Δ' (ιx.collapse k))
    (CorrW.box hθ hcr) (fun _ => rfl) (fun _ => rfl) (fun hk => absurd hk (Nat.succ_ne_zero k))
    (fun _ _ _ _ _ => rfl)

theorem CorrW.under (hcw : CorrW Γ D θ θ') {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (T : VarType)
    (h : Δ (.root (.bnd d')) = none) (h' : Δ' (.root (.bnd d')) = none)
    (hr : Δ.RootFresh (.bnd d')) :
    CorrW (Γ.insert (.bnd d) T) (D.insert hr T) (θ.under d d' T h) (θ'.under d d' T h') :=
  CorrW.transfer (Ctx.le_insert h T) (Ctx.le_insert h' T) hcw (fun _ => rfl) (fun _ => rfl)
    (fun _ y X hy => at_under_ne θ' T h' (fun he => by
      rw [hΓ.wit y d he le_rfl] at hy
      cases hy))
    (fun _ _ _ _ _ => rfl)

/-- ⭐**At level 0 a witness's view corresponds to its identity view** (`◇⁰_y` collapsing to
    `◇⁰ᵀ_y`). -/
theorem corr_optIn_zero {Γ' Δ Δ' : Ctx} {D : Ctx.Collapses 0 Δ Δ'} {θ : Subst σ Δ}
    {θ' : Subst σ Δ'} {ι' : VarSymb → VarSymb} (C : Ctx.Collapses 0 Γ Γ') (hθ : Ok Γ θ)
    (hc' : Coh ι' Γ' θ') (hcr : Corr Γ D θ θ') (hcw : CorrW Γ D θ θ')
    (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X)
    {z : VarSymb} (hzi : (θ.wit y).idxAlong [] = z) {Z : VarType} (hz : Δ.wit z = some Z) :
    Corr (Γ.optIn y) (D.optIn_zero hO hz) (θ.optIn y z) (θ'.optInT y z) := by
  have hyT : Γ'.witT y = some X := (C.wit y X hy).1 rfl
  have hi : (θ'.at y).idxAlong [] = z := (hcw y X hy hO z hzi).1
  refine corr_of (ok_optIn hθ hO hy hzi) ?_
  intro v T hlp hv
  by_cases hc : v = .step y .dia
  · subst hc
    rw [Ctx.optIn_content hy] at hv
    cases hv
    rw [VarSymb.collapse_dia_zero_opt hO, at_nonproj _ rfl, optInT_content, optIn_content]
    obtain ⟨-, Z', hz', hsim⟩ := hcw y _ hy hO z hzi
    exact hsim
  · rw [Ctx.optIn_ne hc] at hv
    have href : Γ.ref v = some T := (Ctx.ref_nonproj Γ hlp).trans hv
    rw [at_optInT_of hc' hyT hi _ _ (C v T href), optIn_ne θ z hc,
      SubE.collapse_mono D (D.optIn_zero hO hz) (Ctx.le_optIn Δ z) (Ctx.le_optInT Δ' z)]
    have h₁ := hcr v T href
    rw [at_nonproj θ hlp] at h₁
    exact h₁.mono _

/-- Further in, a witness's view corresponds to the collapsed witness's. -/
theorem corr_optIn_succ {Γ' Δ Δ' : Ctx} {D : Ctx.Collapses (k + 1) Δ Δ'} {θ : Subst σ Δ}
    {θ' : Subst σ Δ'} {ι' : VarSymb → VarSymb} (C : Ctx.Collapses (k + 1) Γ Γ') (hθ : Ok Γ θ)
    (hc' : Coh ι' Γ' θ') (hcr : Corr Γ D θ θ') (hcw : CorrW Γ D θ θ')
    (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X)
    {z : VarSymb} (hzi : (θ.wit y).idxAlong [] = z) {Z : VarType} (hz : Δ.wit z = some Z) :
    Corr (Γ.optIn y) (D.optIn_succ hz) (θ.optIn y z) (θ'.optIn (y.collapse k) (z.collapse k)) := by
  have hy' : Γ'.wit (y.collapse k) = some X := (C.wit y X hy).2 k rfl
  have hi : (θ'.wit (y.collapse k)).idxAlong [] = z.collapse k := (hcw y X hy z hzi).1
  refine corr_of (ok_optIn hθ hO hy hzi) ?_
  intro v T hlp hv
  by_cases hc : v = .step y .dia
  · subst hc
    rw [Ctx.optIn_content hy] at hv
    cases hv
    rw [VarSymb.collapse_level_succ rfl, at_nonproj _ rfl, optIn_content, optIn_content]
    obtain ⟨-, Z', hz', hsim⟩ := hcw y _ hy z hzi
    exact hsim
  · rw [Ctx.optIn_ne hc] at hv
    have href : Γ.ref v = some T := (Ctx.ref_nonproj Γ hlp).trans hv
    rw [at_optIn_of hc' hO hy' hi _ _ (C v T href), optIn_ne θ z hc,
      SubE.collapse_mono D (D.optIn_succ hz) (Ctx.le_optIn Δ z) (Ctx.le_optIn Δ' _)]
    have h₁ := hcr v T href
    rw [at_nonproj θ hlp] at h₁
    exact h₁.mono _

/-- An identity view corresponds to the collapsed possible object's. -/
theorem corr_optInT {Γ' : Ctx} {ι' : VarSymb → VarSymb} (C : Ctx.Collapses k Γ Γ')
    (hθ : Ok Γ θ) (hc' : Coh ι' Γ' θ') (hcr : Corr Γ D θ θ') {y : VarSymb} {X : VarType}
    (hy : Γ.witT y = some X) {z : VarSymb} (hzi : (θ.at y).idxAlong [] = z) {Z : VarType}
    (hz : Δ.witT z = some Z) :
    Corr (Γ.optInT y) (D.optInT hz) (θ.optInT y z) (θ'.optInT (y.collapse k) (z.collapse k)) := by
  obtain ⟨hT, hO, hr⟩ := Ctx.witT_spec hy
  have hy' : Γ'.witT (y.collapse k) = some X := C.witT hy
  have hsim := hcr y _ hr
  have he := okRef_at hθ hr
  have hi : (θ'.at (y.collapse k)).idxAlong [] = z.collapse k := by
    rw [hsim.idx, SubE.idxAlong_collapse, hzi]
    rfl
  refine corr_of (ok_optInT hθ hy hzi) ?_
  intro v T hlp hv
  by_cases hc : v = .step y .at
  · subst hc
    rw [Ctx.optInT_content hy] at hv
    cases hv
    rw [VarSymb.collapse_proj rfl, at_nonproj _ rfl, optInT_content, optInT_content,
      SubE.atBody_collapse D hz he hzi]
    exact hsim.atBody hT hO hi
  · rw [Ctx.optInT_ne hc] at hv
    have href : Γ.ref v = some T := (Ctx.ref_nonproj Γ hlp).trans hv
    rw [at_optInT_of hc' hy' hi _ _ (C v T href), optInT_ne θ z hc,
      SubE.collapse_mono D (D.optInT hz) (Ctx.le_optInT Δ z) (Ctx.le_optInT Δ' _)]
    have h₁ := hcr v T href
    rw [at_nonproj θ hlp] at h₁
    exact h₁.mono _

theorem CorrW.optIn_zero {Γ' Δ Δ' : Ctx} {D : Ctx.Collapses 0 Δ Δ'} {θ : Subst σ Δ}
    {θ' : Subst σ Δ'} {ι' : VarSymb → VarSymb} (C : Ctx.Collapses 0 Γ Γ') (hc' : Coh ι' Γ' θ')
    (hcw : CorrW Γ D θ θ') (hO : ModalSys.Opt = true) {y : VarSymb} {X : VarType}
    (hy : Γ.wit y = some X) {z : VarSymb} (hzi : (θ.wit y).idxAlong [] = z) {Z : VarType}
    (hz : Δ.wit z = some Z) :
    CorrW (Γ.optIn y) (D.optIn_zero hO hz) (θ.optIn y z) (θ'.optInT y z) :=
  CorrW.transfer (Ctx.le_optIn Δ z) (Ctx.le_optInT Δ' z) hcw (fun _ => rfl) (fun _ => rfl)
    (fun _ y' X' hy' => at_optInT_of hc' ((C.wit y X hy).1 rfl) (hcw y X hy hO z hzi).1 _ _
      (Ctx.witT_spec ((C.wit y' X' hy').1 rfl)).2.2)
    (fun _ hk => absurd hk.symm (Nat.succ_ne_zero _))

theorem CorrW.optIn_succ {Δ Δ' : Ctx} {D : Ctx.Collapses (k + 1) Δ Δ'} {θ : Subst σ Δ}
    {θ' : Subst σ Δ'} (hcw : CorrW Γ D θ θ') (y : VarSymb) {z : VarSymb} {Z : VarType}
    (hz : Δ.wit z = some Z) :
    CorrW (Γ.optIn y) (D.optIn_succ hz) (θ.optIn y z) (θ'.optIn (y.collapse k) (z.collapse k)) :=
  CorrW.transfer (Ctx.le_optIn Δ z) (Ctx.le_optIn Δ' _) hcw (fun _ => rfl) (fun _ => rfl)
    (fun hk => absurd hk (Nat.succ_ne_zero k)) (fun _ _ _ _ _ => rfl)

theorem CorrW.optInT {Γ' : Ctx} {ι' : VarSymb → VarSymb} (C : Ctx.Collapses k Γ Γ')
    (hc' : Coh ι' Γ' θ') (hcr : Corr Γ D θ θ') (hcw : CorrW Γ D θ θ') {y : VarSymb}
    {X : VarType} (hy : Γ.witT y = some X) {z : VarSymb} (hzi : (θ.at y).idxAlong [] = z)
    {Z : VarType} (hz : Δ.witT z = some Z) :
    CorrW (Γ.optInT y) (D.optInT hz) (θ.optInT y z) (θ'.optInT (y.collapse k) (z.collapse k)) := by
  obtain ⟨-, -, hr⟩ := Ctx.witT_spec hy
  have hi : (θ'.at (y.collapse k)).idxAlong [] = z.collapse k := by
    rw [(hcr y _ hr).idx, SubE.idxAlong_collapse, hzi]
    rfl
  exact CorrW.transfer (Ctx.le_optInT Δ z) (Ctx.le_optInT Δ' _) hcw (fun _ => rfl)
    (fun _ => rfl)
    (fun hk y' X' hy' => at_optInT_of hc' (C.witT hy) hi _ _
      (Ctx.witT_spec ((C.wit y' X' hy').1 hk)).2.2)
    (fun _ _ _ _ _ => rfl)

/-- A source without witnesses has nothing to correspond. -/
theorem CorrW.of_noWit {k : ℕ} {Γ Δ Δ' : Ctx} {D : Ctx.Collapses k Δ Δ'} {θ : Subst σ Δ}
    {θ' : Subst σ Δ'} (h : ∀ y, Γ.wit y = none) : CorrW Γ D θ θ' := by
  cases k with
  | zero => intro y X hy; rw [h] at hy; cases hy
  | succ k => intro y X hy; rw [h] at hy; cases hy

/-- A single-root substitution's witnesses go to themselves, so at level 0 they correspond. -/
theorem CorrW.single_zero {Λ Ω Ω' : Ctx} {r : Root} {T : VarType} {D : Ctx.Collapses 0 Ω Ω'}
    (hr : Λ.RootFresh r) (hle : Λ.Le Ω) {e : SubE σ Ω} {e' : SubE σ Ω'} :
    CorrW (Λ.insert r T) D (single r e) (single r e') := by
  intro y X hy hO z hzi
  have hz : y = z := hzi
  subst hz
  have hrt : y.rt ≠ r := fun he => by
    change Λ.wit y = some X at hy
    rw [hr.wit y he] at hy
    cases hy
  refine ⟨by rw [at_single_of_rt_ne hrt]; rfl, X, hle.wit y X hy, ?_⟩
  rw [at_single_of_rt_ne hrt]
  change SubE.Sim X (SubE.ren (.step y .at)) (SubE.ren ((VarSymb.step y .dia).collapse 0))
  rw [VarSymb.collapse_dia_zero_opt hO]
  exact .refl _

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
    (_hcw : ModalSys.Opt = true → Subst.CorrW Γ D θ θ' := by wit_triv) →
    WFF.collapse D hΔ (WFF.subst ι θ hθ hc hΓ hΔ φ) =
      WFF.subst ι' θ' hθ' hc' hΓ' hΔ' (WFF.collapse C hΓ φ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr, .atom ρ, _ =>
      congrArg WFF.atom (Rel.collapse_subst C D θ hθ hc θ' hθ' hc' hcr ρ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr, .eq t s, _ =>
      congrArg₂ WFF.eq (Term.collapse_subst_var C D θ hθ hc θ' hθ' hc' hcr t)
        (Term.collapse_subst_var C D θ hθ hc θ' hθ' hc' hcr s)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top, _ => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot, _ => rfl
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .and φ ψ, hcw =>
      congrArg₂ WFF.and (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ hcw)
        (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ hcw)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .or φ ψ, hcw =>
      congrArg₂ WFF.or (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ hcw)
        (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ hcw)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .imp φ ψ, hcw =>
      congrArg₂ WFF.imp (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ hcw)
        (WFF.collapse_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ hcw)
  | _, _, _, _, _, _, _, d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .all T φ, hcw =>
      congrArg (WFF.all T) (WFF.collapse_subst (C.insert (hΓ.rootFresh le_rfl) T)
        (D.insert (hΔ.rootFresh le_rfl) T) (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (θ'.under d d' T hΔ'.root) (Subst.ok_under hθ' T hΔ'.root)
        (Subst.coh_under hθ' hc' hΓ' T hΔ'.root) (hΓ.insert T) (hΓ'.insert T) (hΔ.insert T)
        (hΔ'.insert T)
        (Subst.corr_under hθ hcr hΓ T hΔ.root hΔ'.root (hΔ.rootFresh le_rfl)) φ
        fun hO => (hcw hO).under hΓ T hΔ.root hΔ'.root (hΔ.rootFresh le_rfl))
  | _, _, _, _, _, _, _, d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .ex T φ, hcw =>
      congrArg (WFF.ex T) (WFF.collapse_subst (C.insert (hΓ.rootFresh le_rfl) T)
        (D.insert (hΔ.rootFresh le_rfl) T) (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (θ'.under d d' T hΔ'.root) (Subst.ok_under hθ' T hΔ'.root)
        (Subst.coh_under hθ' hc' hΓ' T hΔ'.root) (hΓ.insert T) (hΓ'.insert T) (hΔ.insert T)
        (hΔ'.insert T)
        (Subst.corr_under hθ hcr hΓ T hΔ.root hΔ'.root (hΔ.rootFresh le_rfl)) φ
        fun hO => (hcw hO).under hΓ T hΔ.root hΔ'.root (hΔ.rootFresh le_rfl))
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .box φ, hcw =>
      congrArg WFF.box (WFF.collapse_subst C.boxIn D.boxIn θ.box (Subst.ok_box hθ)
        (Subst.coh_box hθ hc) θ'.box (Subst.ok_box hθ') (Subst.coh_box hθ' hc') hΓ.boxIn
        hΓ'.boxIn hΔ.boxIn hΔ'.boxIn (Subst.corr_box hθ hcr) φ
        fun _ => Subst.CorrW.box hθ hcr)
  | k, ι, ι', Γ, Γ', Δ, Δ', _, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .dia x hx φ, hcw => by
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
          (hΔ.diaIn (ι x)) hΔy (Subst.corr_dia hθ hcr hx hw hw') φ
          fun _ => Subst.CorrW.dia hθ hcr x (ι x))
      exact key _ hwι _ _ _ _
  | 0, ι, ι', Γ, Γ', Δ, Δ', _, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .optx hO .arrow y hy φ, hcw => by
      obtain ⟨X, hX⟩ := hy
      have hzi : (θ.wit y).idxAlong [] = ι y := hc.wit hO y X hX []
      obtain ⟨Z, hz⟩ := WitE.wit_of (hθ.wit hO y X hX) hzi
      have hyT : Γ'.witT y = some X := (C.wit y X hX).1 rfl
      have hι : ι' y = ι y :=
        (hc' y _ (Ctx.witT_spec hyT).2.2 []).symm.trans ((hcw hO) y X hX hO (ι y) hzi).1
      have key : ∀ (z : VarSymb) (_hz : z = ι y) (P : ∃ Z, Δ'.witT z = some Z)
          (p : Subst.Ok (Γ'.optInT y) (θ'.optInT y z))
          (q : Subst.Coh ι' (Γ'.optInT y) (θ'.optInT y z)) (hΔz : (Δ'.optInT z).SlotsFrom d'),
          WFF.collapse D hΔ (WFF.subst ι θ hθ hc hΓ hΔ (.optx hO .arrow y ⟨X, hX⟩ φ)) =
            .optx hO .ident z P (WFF.subst ι' (θ'.optInT y z) p q (hΓ'.optInT y) hΔz
              (WFF.collapse (C.optIn_zero hO hX) (hΓ.optIn y) φ)) := by
        intro z hz' P p q hΔz
        subst hz'
        exact congrArg (WFF.optx hO .ident (ι y) _) (WFF.collapse_subst (C.optIn_zero hO hX)
          (D.optIn_zero hO hz) (θ.optIn y (ι y)) (Subst.ok_optIn hθ hO hX hzi)
          (Subst.coh_optIn hθ hc hO hX) (θ'.optInT y (ι y)) p q (hΓ.optIn y) (hΓ'.optInT y)
          (hΔ.optIn (ι y)) hΔz
          (Subst.corr_optIn_zero C hθ hc' hcr (hcw hO) hO hX hzi hz) φ
          (fun _ => Subst.CorrW.optIn_zero C hc' (hcw hO) hO hX hzi hz))
      exact key (ι' y) hι _ _ _ _
  | k + 1, ι, ι', Γ, Γ', Δ, Δ', _, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .optx hO .arrow y hy φ, hcw => by
      obtain ⟨X, hX⟩ := hy
      have hzi : (θ.wit y).idxAlong [] = ι y := hc.wit hO y X hX []
      obtain ⟨Z, hz⟩ := WitE.wit_of (hθ.wit hO y X hX) hzi
      have hy' : Γ'.wit (y.collapse k) = some X := (C.wit y X hX).2 k rfl
      have hι : ι' (y.collapse k) = (ι y).collapse k :=
        (hc'.wit hO _ X hy' []).symm.trans ((hcw hO) y X hX (ι y) hzi).1
      have key : ∀ (z : VarSymb) (_hz : z = (ι y).collapse k) (P : ∃ Z, Δ'.wit z = some Z)
          (p : Subst.Ok (Γ'.optIn (y.collapse k)) (θ'.optIn (y.collapse k) z))
          (q : Subst.Coh ι' (Γ'.optIn (y.collapse k)) (θ'.optIn (y.collapse k) z))
          (hΔz : (Δ'.optIn z).SlotsFrom d'),
          WFF.collapse D hΔ (WFF.subst ι θ hθ hc hΓ hΔ (.optx hO .arrow y ⟨X, hX⟩ φ)) =
            .optx hO .arrow z P (WFF.subst ι' (θ'.optIn (y.collapse k) z) p q
              (hΓ'.optIn (y.collapse k)) hΔz
              (WFF.collapse (C.optIn_succ hX) (hΓ.optIn y) φ)) := by
        intro z hz' P p q hΔz
        subst hz'
        exact congrArg (WFF.optx hO .arrow ((ι y).collapse k) _) (WFF.collapse_subst
          (C.optIn_succ hX) (D.optIn_succ hz) (θ.optIn y (ι y)) (Subst.ok_optIn hθ hO hX hzi)
          (Subst.coh_optIn hθ hc hO hX) (θ'.optIn (y.collapse k) ((ι y).collapse k)) p q
          (hΓ.optIn y) (hΓ'.optIn (y.collapse k)) (hΔ.optIn (ι y)) hΔz
          (Subst.corr_optIn_succ C hθ hc' hcr (hcw hO) hO hX hzi hz) φ
          (fun _ => Subst.CorrW.optIn_succ (hcw hO) y hz))
      exact key _ hι _ _ _ _
  | k, ι, ι', Γ, Γ', Δ, Δ', _, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .optx hO .ident y hy φ, hcw => by
      obtain ⟨X, hX⟩ := hy
      obtain ⟨hT, -, hr⟩ := Ctx.witT_spec hX
      have hzi : (θ.at y).idxAlong [] = ι y := hc y _ hr []
      obtain ⟨Z, hZ₀⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hzi
      have hz : Δ.witT (ι y) = some Z := Ctx.witT_of hT hO hZ₀
      have hι : ι' (y.collapse k) = (ι y).collapse k := by
        have h₁ := hc' (y.collapse k) _ (C y _ hr) []
        have h₂ := (hcr y _ hr).idx
        rw [SubE.idxAlong_collapse, hzi] at h₂
        exact h₁.symm.trans h₂
      have key : ∀ (z : VarSymb) (_hz : z = (ι y).collapse k) (P : ∃ Z, Δ'.witT z = some Z)
          (p : Subst.Ok (Γ'.optInT (y.collapse k)) (θ'.optInT (y.collapse k) z))
          (q : Subst.Coh ι' (Γ'.optInT (y.collapse k)) (θ'.optInT (y.collapse k) z))
          (hΔz : (Δ'.optInT z).SlotsFrom d'),
          WFF.collapse D hΔ (WFF.subst ι θ hθ hc hΓ hΔ (.optx hO .ident y ⟨X, hX⟩ φ)) =
            .optx hO .ident z P (WFF.subst ι' (θ'.optInT (y.collapse k) z) p q
              (hΓ'.optInT (y.collapse k)) hΔz
              (WFF.collapse (C.optInT hX) (hΓ.optInT y) φ)) := by
        intro z hz' P p q hΔz
        subst hz'
        exact congrArg (WFF.optx hO .ident ((ι y).collapse k) _) (WFF.collapse_subst
          (C.optInT hX) (D.optInT hz) (θ.optInT y (ι y)) (Subst.ok_optInT hθ hX hzi)
          (Subst.coh_optInT hθ hc hX) (θ'.optInT (y.collapse k) ((ι y).collapse k)) p q
          (hΓ.optInT y) (hΓ'.optInT (y.collapse k)) (hΔ.optInT (ι y)) hΔz
          (Subst.corr_optInT C hθ hc' hcr hX hzi hz) φ
          (fun hO' => Subst.CorrW.optInT C hc' hcr (hcw hO') hX hzi hz))
      exact key _ hι _ _ _ _
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr, .here hT s t _, _ =>
      WFF.here_congr hT (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr s)
        (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr,
      .back hB L s t, _ =>
      WFF.back_congr hB L (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr s)
        (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)
  | _, _, _, _, _, _, _, d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .retS hB S t Φ, _ =>
      WFF.retS_congr hB S (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)
        (WFF.collapse_subst (C.boxIn.insert (hΓ.boxIn.rootFresh le_rfl) _)
          (D.boxIn.insert (hΔ.boxIn.rootFresh le_rfl) _) (θ.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
          (θ'.box.under d d' _ hΔ'.boxIn.root) (Subst.ok_under (Subst.ok_box hθ') _ hΔ'.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ') (Subst.coh_box hθ' hc') hΓ'.boxIn _ hΔ'.boxIn.root)
          (hΓ.boxIn.insert _) (hΓ'.boxIn.insert _) (hΔ.boxIn.insert _) (hΔ'.boxIn.insert _)
          (Subst.corr_under (Subst.ok_box hθ) (Subst.corr_box hθ hcr) hΓ.boxIn _ hΔ.boxIn.root
            hΔ'.boxIn.root (hΔ.boxIn.rootFresh le_rfl)) Φ)
  | k, ι, ι', Γ, Γ', Δ, Δ', d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .retxS hB y hy S t Φ, _ => by
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      have hwι : ι' (y.collapse k) = (ι y).collapse k := hy.elim fun _ hY => by
        have h₁ := hc' (y.collapse k) _ (C y _ hY) []
        have h₂ := (hcr y _ hY).idx
        rw [SubE.idxAlong_collapse, hw] at h₂
        exact h₁.symm.trans h₂
      have hw' : (θ'.at (y.collapse k)).idxAlong [] = (ι y).collapse k :=
        hy.elim fun _ hY => (hc' _ _ (C y _ hY) []).trans hwι
      have hr := (hΔ.diaIn (ι y)).root
      have key : ∀ (z : VarSymb) (_hz : z = (ι y).collapse k)
          (P : ∃ Y, Δ'.ref z = some (.VTypeDia Y)) (hΔz : (Δ'.diaIn z).SlotsFrom d')
          (p : Subst.Ok ((Γ'.diaIn (y.collapse k)).insert (.bnd d) S.ty)
            ((θ'.dia (y.collapse k) z).under d d' _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot ι' d d')
            ((Γ'.diaIn (y.collapse k)).insert (.bnd d) S.ty)
            ((θ'.dia (y.collapse k) z).under d d' _ hΔz.root)),
          WFF.collapse D hΔ (WFF.subst ι θ hθ hc hΓ hΔ (.retxS hB y hy S t Φ)) =
            .retxS hB z P S (Term.subst ι' θ' hθ' hc' (Term.collapse C t))
              (WFF.subst (VarSymb.shiftSlot ι' d d')
                ((θ'.dia (y.collapse k) z).under d d' _ hΔz.root) p q
                ((hΓ'.diaIn (y.collapse k)).insert _) (hΔz.insert _)
                (WFF.collapse ((C.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl) _)
                  ((hΓ.diaIn y).insert _) Φ)) := by
        intro z hz P hΔz p q
        subst hz
        exact WFF.retxS_congr hB _ _ S (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)
          (WFF.collapse_subst ((C.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl) _)
            ((D.diaIn (ι y)).insert ((hΔ.diaIn (ι y)).rootFresh le_rfl) _)
            ((θ.dia y (ι y)).under d d' _ hr) (Subst.ok_under (Subst.ok_dia hθ hy hw) _ hr)
            (Subst.coh_under (Subst.ok_dia hθ hy hw) (Subst.coh_dia hθ hc hy) (hΓ.diaIn y) _ hr)
            _ p q ((hΓ.diaIn y).insert _) ((hΓ'.diaIn (y.collapse k)).insert _)
            ((hΔ.diaIn (ι y)).insert _) (hΔz.insert _)
            (Subst.corr_under (Subst.ok_dia hθ hy hw) (Subst.corr_dia hθ hcr hy hw hw')
              (hΓ.diaIn y) _ hr hΔz.root ((hΔ.diaIn (ι y)).rootFresh le_rfl)) Φ)
      exact key _ hwι _ (hΔ'.diaIn _) _ _
  | _, _, _, _, _, _, _, d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .link hV hF t Φ, _ =>
      WFF.link_congr hV hF (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)
        (WFF.collapse_subst (C.boxIn.insert (hΓ.boxIn.rootFresh le_rfl) _)
          (D.boxIn.insert (hΔ.boxIn.rootFresh le_rfl) _) (θ.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hθ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn _ hΔ.boxIn.root)
          (θ'.box.under d d' _ hΔ'.boxIn.root) (Subst.ok_under (Subst.ok_box hθ') _ hΔ'.boxIn.root)
          (Subst.coh_under (Subst.ok_box hθ') (Subst.coh_box hθ' hc') hΓ'.boxIn _ hΔ'.boxIn.root)
          (hΓ.boxIn.insert _) (hΓ'.boxIn.insert _) (hΔ.boxIn.insert _) (hΔ'.boxIn.insert _)
          (Subst.corr_under (Subst.ok_box hθ) (Subst.corr_box hθ hcr) hΓ.boxIn _ hΔ.boxIn.root
            hΔ'.boxIn.root (hΔ.boxIn.rootFresh le_rfl)) Φ)
  | k, ι, ι', Γ, Γ', Δ, Δ', d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .linkx hV hF y hy (D := Ds) t Φ, _ => by
      have hw : (θ.at y).idxAlong [] = ι y := hy.elim fun _ hY => hc y _ hY []
      have hwι : ι' (y.collapse k) = (ι y).collapse k := hy.elim fun _ hY => by
        have h₁ := hc' (y.collapse k) _ (C y _ hY) []
        have h₂ := (hcr y _ hY).idx
        rw [SubE.idxAlong_collapse, hw] at h₂
        exact h₁.symm.trans h₂
      have hw' : (θ'.at (y.collapse k)).idxAlong [] = (ι y).collapse k :=
        hy.elim fun _ hY => (hc' _ _ (C y _ hY) []).trans hwι
      have hr := (hΔ.diaIn (ι y)).root
      have key : ∀ (z : VarSymb) (_hz : z = (ι y).collapse k)
          (P : ∃ Y, Δ'.ref z = some (.VTypeDia Y)) (hΔz : (Δ'.diaIn z).SlotsFrom d')
          (p : Subst.Ok ((Γ'.diaIn (y.collapse k)).insert (.bnd d) Ds.ty)
            ((θ'.dia (y.collapse k) z).under d d' _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot ι' d d')
            ((Γ'.diaIn (y.collapse k)).insert (.bnd d) Ds.ty)
            ((θ'.dia (y.collapse k) z).under d d' _ hΔz.root)),
          WFF.collapse D hΔ (WFF.subst ι θ hθ hc hΓ hΔ (.linkx hV hF y hy t Φ)) =
            .linkx hV hF z P (Term.subst ι' θ' hθ' hc' (Term.collapse C t))
              (WFF.subst (VarSymb.shiftSlot ι' d d')
                ((θ'.dia (y.collapse k) z).under d d' _ hΔz.root) p q
                ((hΓ'.diaIn (y.collapse k)).insert _) (hΔz.insert _)
                (WFF.collapse ((C.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl) _)
                  ((hΓ.diaIn y).insert _) Φ)) := by
        intro z hz P hΔz p q
        subst hz
        exact WFF.linkx_congr hV hF _ _ (Term.collapse_subst C D θ hθ hc θ' hθ' hc' hcr t)
          (WFF.collapse_subst ((C.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl) _)
            ((D.diaIn (ι y)).insert ((hΔ.diaIn (ι y)).rootFresh le_rfl) _)
            ((θ.dia y (ι y)).under d d' _ hr) (Subst.ok_under (Subst.ok_dia hθ hy hw) _ hr)
            (Subst.coh_under (Subst.ok_dia hθ hy hw) (Subst.coh_dia hθ hc hy) (hΓ.diaIn y) _ hr)
            _ p q ((hΓ.diaIn y).insert _) ((hΓ'.diaIn (y.collapse k)).insert _)
            ((hΔ.diaIn (ι y)).insert _) (hΔz.insert _)
            (Subst.corr_under (Subst.ok_dia hθ hy hw) (Subst.corr_dia hθ hcr hy hw hw')
              (hΓ.diaIn y) _ hr hΔz.root ((hΔ.diaIn (ι y)).rootFresh le_rfl)) Φ)
      exact key _ hwι _ (hΔ'.diaIn _) _ _

end CollapseSubst

end V12M
