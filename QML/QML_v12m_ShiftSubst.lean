import QML.QML_v12m_CollapseSubst

/-!
# QML v12m — shifting commutes with substitution (weak 4)

The facts about moving syntax one view further in that substituting twice, renaming proofs and
the 4 rule need, mirroring `QML_v12m_CollapseSubst`:

* **Shifts commute** with shifts at other levels and with collapses (`Term.shift_shift`,
  `Term.shift_shift_same`, `Term.shift_collapse`), matching the address lemmas.
* **Shifting a substituted term is substituting into the shifted term** (`Term.shift_subst`,
  `WFF.shift_subst`), whenever the second substitution sends each shifted address to the shifted
  entry of the first, up to η (`Subst.ShiftCorr`).
* The `□□` view of a substitution corresponds, across the shift, to its `□` view
  (`Subst.shiftCorr_box_box`).
-/

namespace V12M

/-! ## Annotations -/

theorem Ann.shift_shift : ∀ {T : VarType} (a : Ann T) (k m : ℕ),
    (a.shift (k + 1 + m)).shift m = (a.shift m).shift (k + 2 + m)
  | _, .var, _, _ => rfl
  | _, .one, _, _ => rfl
  | _, .prod a b, k, m => by
      change Ann.prod _ _ = Ann.prod _ _
      rw [Ann.shift_shift a k m, Ann.shift_shift b k m]
  | _, .box a, k, m => by
      change Ann.box ((a.shift (k + 1 + m + 1)).shift (m + 1)) =
        Ann.box ((a.shift (m + 1)).shift (k + 2 + m + 1))
      rw [show k + 1 + m + 1 = k + 1 + (m + 1) by omega,
        show k + 2 + m + 1 = k + 2 + (m + 1) by omega, Ann.shift_shift a k (m + 1)]
  | _, .dia i a, k, m => by
      change Ann.dia ((i.shift (k + 1 + m)).shift m) ((a.shift (k + 1 + m + 1)).shift (m + 1)) =
        Ann.dia ((i.shift m).shift (k + 2 + m)) ((a.shift (m + 1)).shift (k + 2 + m + 1))
      rw [show k + 1 + m + 1 = k + 1 + (m + 1) by omega,
        show k + 2 + m + 1 = k + 2 + (m + 1) by omega, Ann.shift_shift a k (m + 1),
        VarSymb.shift_shift i k m]

/-- The index a path reaches in a shifted annotation. -/
theorem Ann.idxAt_shift : ∀ {T : VarType} (a : Ann T) (k : ℕ) (p : List Step),
    (a.shift k).idxAt p = (a.idxAt p).shift (k + Step.levels p)
  | _, .var, _, [] => rfl
  | _, .var, _, _ :: _ => rfl
  | _, .one, _, [] => rfl
  | _, .one, _, _ :: _ => rfl
  | _, .prod _ _, _, [] => rfl
  | _, .prod a _, k, .fst :: p => by
      change (a.shift k).idxAt p = (a.idxAt p).shift (k + (0 + Step.levels p))
      rw [Ann.idxAt_shift a k p, Nat.zero_add]
  | _, .prod _ b, k, .snd :: p => by
      change (b.shift k).idxAt p = (b.idxAt p).shift (k + (0 + Step.levels p))
      rw [Ann.idxAt_shift b k p, Nat.zero_add]
  | _, .prod _ _, _, .box :: _ => rfl
  | _, .prod _ _, _, .dia :: _ => rfl
  | _, .prod _ _, _, .here :: _ => rfl
  | _, .prod _ _, _, .keep :: _ => rfl
  | _, .box _, _, [] => rfl
  | _, .box a, k, .box :: p => by
      change (a.shift (k + 1)).idxAt p = _
      rw [Ann.idxAt_shift a (k + 1) p]
      change _ = (a.idxAt p).shift (k + (1 + Step.levels p))
      rw [Nat.add_assoc]
  | _, .box a, k, .here :: p => by
      change ((a.shift (k + 1)).idxAt p).collapse (Step.levels p) =
        ((a.idxAt p).collapse (Step.levels p)).shift (k + (0 + Step.levels p))
      rw [Ann.idxAt_shift a (k + 1) p, Nat.zero_add, VarSymb.shift_collapse]
  | _, .box a, k, .keep :: p => by
      change (Ann.box ((a.shift (k + 1)).shift 0)).idxAt p =
        ((Ann.box (a.shift 0)).idxAt p).shift (k + (1 + Step.levels p))
      rw [← Nat.add_assoc, ← Ann.idxAt_shift (Ann.box (a.shift 0)) (k + 1) p]
      change (Ann.box ((a.shift (k + 1 + 0)).shift 0)).idxAt p =
        (Ann.box ((a.shift 0).shift (k + 2 + 0))).idxAt p
      rw [Ann.shift_shift a k 0]
  | _, .box _, _, .fst :: _ => rfl
  | _, .box _, _, .snd :: _ => rfl
  | _, .box _, _, .dia :: _ => rfl
  | _, .dia _ _, _, [] => rfl
  | _, .dia _ a, k, .dia :: p => by
      change (a.shift (k + 1)).idxAt p = _
      rw [Ann.idxAt_shift a (k + 1) p]
      change _ = (a.idxAt p).shift (k + (1 + Step.levels p))
      rw [Nat.add_assoc]
  | _, .dia _ _, _, .fst :: _ => rfl
  | _, .dia _ _, _, .snd :: _ => rfl
  | _, .dia _ _, _, .box :: _ => rfl
  | _, .dia _ _, _, .here :: _ => rfl
  | _, .dia _ _, _, .keep :: _ => rfl

variable [ModalSys]

/-! ## Shifts commute with shifts and collapses -/

mutual
  theorem Func.shift_shift {σ : Signature} {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
      (h₁₂ : Ctx.Shifts m Γ₁ Γ₂) (h₂₃ : Ctx.Shifts (k + 2 + m) Γ₂ Γ₃)
      (h₁₄ : Ctx.Shifts (k + 1 + m) Γ₁ Γ₄) (h₄₃ : Ctx.Shifts m Γ₄ Γ₃) :
      {n : ℕ} → (f : Func σ Γ₁ n) →
      Func.shift h₂₃ (Func.shift h₁₂ f) = Func.shift h₄₃ (Func.shift h₁₄ f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.shift h₂₃ (Func.shift h₁₂ g)) (Term.shift h₂₃ (Term.shift h₁₂ t)) =
          Func.eval (Func.shift h₄₃ (Func.shift h₁₄ g)) (Term.shift h₄₃ (Term.shift h₁₄ t))
        rw [Func.shift_shift h₁₂ h₂₃ h₁₄ h₄₃ g,
          eq_of_heq (Sigma.mk.inj (Term.shift_shift h₁₂ h₂₃ h₁₄ h₄₃ t)).2]
    termination_by structural _ f => f

  /-- A shift outside another shift commutes with it. -/
  theorem Term.shift_shift {σ : Signature} {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
      (h₁₂ : Ctx.Shifts m Γ₁ Γ₂) (h₂₃ : Ctx.Shifts (k + 2 + m) Γ₂ Γ₃)
      (h₁₄ : Ctx.Shifts (k + 1 + m) Γ₁ Γ₄) (h₄₃ : Ctx.Shifts m Γ₄ Γ₃) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      (⟨_, Term.shift h₂₃ (Term.shift h₁₂ t)⟩ : Σ b, Term σ Γ₃ T b) =
        ⟨_, Term.shift h₄₃ (Term.shift h₁₄ t)⟩
    | _, _, .var v _ => sig_var (VarSymb.shift_shift v k m).symm _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.shift h₂₃ (Func.shift h₁₂ f))⟩ : Σ b, Term σ Γ₃ .Var b) =
          ⟨_, Term.func (Func.shift h₄₃ (Func.shift h₁₄ f))⟩
        rw [Func.shift_shift h₁₂ h₂₃ h₁₄ h₄₃ f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.shift_shift h₁₂ h₂₃ h₁₄ h₄₃ s) (Term.shift_shift h₁₂ h₂₃ h₁₄ h₄₃ t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.shift_shift (m := m + 1) h₁₂.boxIn h₂₃.boxIn h₁₄.boxIn h₄₃.boxIn t)
    | _, _, .diatm x hx t => by
        have key : ∀ (y : VarSymb) (_hy : y = (x.shift m).shift (k + 2 + m))
            (P : ∃ X, Γ₃.ref y = some (.VTypeDia X))
            (h' : Ctx.Shifts (m + 1) (Γ₄.diaIn (x.shift (k + 1 + m))) (Γ₃.diaIn y)),
            (⟨_, Term.shift h₂₃ (Term.shift h₁₂ (Term.diatm x hx t))⟩ : Σ b, Term σ Γ₃ _ b) =
              ⟨_, Term.diatm y P (Term.shift h' (Term.shift (h₁₄.diaIn x) t))⟩ := by
          intro y hy P h'
          subst hy
          exact sig_diatm (Term.shift_shift (m := m + 1) (h₁₂.diaIn x) (h₂₃.diaIn _)
            (h₁₄.diaIn x) h' t)
        exact key _ (VarSymb.shift_shift x k m) _ _
    termination_by structural _ _ t => t
end

mutual
  theorem Func.shift_shift_same {σ : Signature} {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
      (h₁₂ : Ctx.Shifts m Γ₁ Γ₂) (h₂₃ : Ctx.Shifts m Γ₂ Γ₃) (h₂₃' : Ctx.Shifts (m + 1) Γ₂ Γ₃) :
      {n : ℕ} → (f : Func σ Γ₁ n) →
      Func.shift h₂₃ (Func.shift h₁₂ f) = Func.shift h₂₃' (Func.shift h₁₂ f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.shift h₂₃ (Func.shift h₁₂ g)) (Term.shift h₂₃ (Term.shift h₁₂ t)) =
          Func.eval (Func.shift h₂₃' (Func.shift h₁₂ g)) (Term.shift h₂₃' (Term.shift h₁₂ t))
        rw [Func.shift_shift_same h₁₂ h₂₃ h₂₃' g,
          eq_of_heq (Sigma.mk.inj (Term.shift_shift_same h₁₂ h₂₃ h₂₃' t)).2]
    termination_by structural _ f => f

  /-- Shifting twice at one level: the two inserted `keep`s are adjacent either way. -/
  theorem Term.shift_shift_same {σ : Signature} {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
      (h₁₂ : Ctx.Shifts m Γ₁ Γ₂) (h₂₃ : Ctx.Shifts m Γ₂ Γ₃) (h₂₃' : Ctx.Shifts (m + 1) Γ₂ Γ₃) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      (⟨_, Term.shift h₂₃ (Term.shift h₁₂ t)⟩ : Σ b, Term σ Γ₃ T b) =
        ⟨_, Term.shift h₂₃' (Term.shift h₁₂ t)⟩
    | _, _, .var v _ => sig_var (VarSymb.shift_shift_same v m) _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.shift h₂₃ (Func.shift h₁₂ f))⟩ : Σ b, Term σ Γ₃ .Var b) =
          ⟨_, Term.func (Func.shift h₂₃' (Func.shift h₁₂ f))⟩
        rw [Func.shift_shift_same h₁₂ h₂₃ h₂₃' f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.shift_shift_same h₁₂ h₂₃ h₂₃' s) (Term.shift_shift_same h₁₂ h₂₃ h₂₃' t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.shift_shift_same (m := m + 1) h₁₂.boxIn h₂₃.boxIn h₂₃'.boxIn t)
    | _, _, .diatm x hx t => by
        have key : ∀ (y : VarSymb) (_hy : y = (x.shift m).shift m)
            (P : ∃ X, Γ₃.ref y = some (.VTypeDia X))
            (h' : Ctx.Shifts (m + 1 + 1) (Γ₂.diaIn (x.shift m)) (Γ₃.diaIn y)),
            (⟨_, Term.shift h₂₃ (Term.shift h₁₂ (Term.diatm x hx t))⟩ : Σ b, Term σ Γ₃ _ b) =
              ⟨_, Term.diatm y P (Term.shift h' (Term.shift (h₁₂.diaIn x) t))⟩ := by
          intro y hy P h'
          subst hy
          exact sig_diatm (Term.shift_shift_same (m := m + 1) (h₁₂.diaIn x) (h₂₃.diaIn _) h' t)
        exact key _ (VarSymb.shift_shift_same x m).symm _ _
    termination_by structural _ _ t => t
end

mutual
  theorem Func.shift_collapse {σ : Signature} {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
      (h₁₂ : Ctx.Shifts (k + 1 + m) Γ₁ Γ₂) (h₂₃ : Ctx.Collapses m Γ₂ Γ₃)
      (h₁₄ : Ctx.Collapses m Γ₁ Γ₄) (h₄₃ : Ctx.Shifts (k + m) Γ₄ Γ₃) :
      {n : ℕ} → (f : Func σ Γ₁ n) →
      Func.collapse h₂₃ (Func.shift h₁₂ f) = Func.shift h₄₃ (Func.collapse h₁₄ f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.collapse h₂₃ (Func.shift h₁₂ g))
            (Term.collapse h₂₃ (Term.shift h₁₂ t)) =
          Func.eval (Func.shift h₄₃ (Func.collapse h₁₄ g)) (Term.shift h₄₃ (Term.collapse h₁₄ t))
        rw [Func.shift_collapse h₁₂ h₂₃ h₁₄ h₄₃ g,
          eq_of_heq (Sigma.mk.inj (Term.shift_collapse h₁₂ h₂₃ h₁₄ h₄₃ t)).2]
    termination_by structural _ f => f

  /-- A shift outside a collapse commutes with it. -/
  theorem Term.shift_collapse {σ : Signature} {k m : ℕ} {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}
      (h₁₂ : Ctx.Shifts (k + 1 + m) Γ₁ Γ₂) (h₂₃ : Ctx.Collapses m Γ₂ Γ₃)
      (h₁₄ : Ctx.Collapses m Γ₁ Γ₄) (h₄₃ : Ctx.Shifts (k + m) Γ₄ Γ₃) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      (⟨_, Term.collapse h₂₃ (Term.shift h₁₂ t)⟩ : Σ b, Term σ Γ₃ T b) =
        ⟨_, Term.shift h₄₃ (Term.collapse h₁₄ t)⟩
    | _, _, .var v _ => sig_var (VarSymb.shift_collapse v k m) _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.collapse h₂₃ (Func.shift h₁₂ f))⟩ :
            Σ b, Term σ Γ₃ .Var b) = ⟨_, Term.func (Func.shift h₄₃ (Func.collapse h₁₄ f))⟩
        rw [Func.shift_collapse h₁₂ h₂₃ h₁₄ h₄₃ f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.shift_collapse h₁₂ h₂₃ h₁₄ h₄₃ s) (Term.shift_collapse h₁₂ h₂₃ h₁₄ h₄₃ t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.shift_collapse (m := m + 1) h₁₂.boxIn h₂₃.boxIn h₁₄.boxIn h₄₃.boxIn t)
    | _, _, .diatm x hx t => by
        have key : ∀ (y : VarSymb) (_hy : y = (x.shift (k + 1 + m)).collapse m)
            (P : ∃ X, Γ₃.ref y = some (.VTypeDia X))
            (h' : Ctx.Shifts (k + m + 1) (Γ₄.diaIn (x.collapse m)) (Γ₃.diaIn y)),
            (⟨_, Term.collapse h₂₃ (Term.shift h₁₂ (Term.diatm x hx t))⟩ :
              Σ b, Term σ Γ₃ _ b) =
              ⟨_, Term.diatm y P (Term.shift h' (Term.collapse (h₁₄.diaIn x) t))⟩ := by
          intro y hy P h'
          subst hy
          exact sig_diatm (Term.shift_collapse (m := m + 1) (h₁₂.diaIn x) (h₂₃.diaIn _)
            (h₁₄.diaIn x) h' t)
        exact key _ (VarSymb.shift_collapse x k m).symm _ _
    termination_by structural _ _ t => t
end

/-! ## Shifting entries -/

namespace SubE

variable {σ : Signature}

/-- Move an entry one view further in. -/
def shift {k : ℕ} {Δ Δ' : Ctx} (D : Ctx.Shifts k Δ Δ') : SubE σ Δ → SubE σ Δ'
  | .hide => .hide
  | .ren w => .ren (w.shift k)
  | .tm s => .tm (Term.shift D s)

theorem shift_mono {k : ℕ} {Δ₁ Δ₂ Δ₁' Δ₂' : Ctx} (D₁ : Ctx.Shifts k Δ₁ Δ₁')
    (D₂ : Ctx.Shifts k Δ₂ Δ₂') (l : Δ₁.Le Δ₂) (l' : Δ₁'.Le Δ₂') :
    ∀ (e : SubE σ Δ₁), (e.mono l).shift D₂ = (e.shift D₁).mono l'
  | .hide => rfl
  | .ren _ => rfl
  | .tm s => congrArg SubE.tm (Term.shift_mono D₁ D₂ l l' s)

theorem unbox_keepE {Δ : Ctx} (hF : ModalSys.Four = true) : ∀ {e : SubE σ Δ} {A : VarType},
    e.OkRef (.VTypeBox A) → e.keepE.unbox = e.unbox.shift (Ctx.shifts_boxIn_boxIn hF Δ)
  | .ren w, _, _ => by
      change SubE.ren (.step (.step w .keep) .box) = SubE.ren ((VarSymb.step w .box).shift 0)
      rw [VarSymb.shift_level_zero rfl]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          rw [keepE_tm _ hF]
          rfl

theorem keepE_keepE {Δ : Ctx} (hF : ModalSys.Four = true) : ∀ {e : SubE σ Δ} {A : VarType},
    e.OkRef (.VTypeBox A) → e.keepE.keepE = e.keepE.shift (Ctx.shifts_boxIn_boxIn hF Δ)
  | .ren w, _, _ => by
      change SubE.ren (.step (.step w .keep) .keep) = SubE.ren ((VarSymb.step w .keep).shift 0)
      rw [VarSymb.shift_level_zero rfl]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          rw [keepE_tm _ hF, keepE_tm _ hF]
          exact tm_eq_of_sig (sig_boxtm (Term.shift_shift_same (m := 0)
            (Ctx.shifts_boxIn_boxIn hF Δ) (Ctx.shifts_boxIn_boxIn hF Δ.boxIn)
            (Ctx.shifts_boxIn_boxIn hF Δ).boxIn t))

variable {k : ℕ} {Δ Δ' : Ctx} (D : Ctx.Shifts k Δ Δ')

theorem okRef_shift : ∀ {e : SubE σ Δ} {T : VarType}, e.OkRef T → (e.shift D).OkRef T
  | .ren w, _, he => D w _ he
  | .tm _, _, he => he
  | .hide, _, he => he.elim

theorem idxAlong_shift : ∀ (e : SubE σ Δ) (p : List Step),
    (e.shift D).idxAlong p = (e.idxAlong p).shift (k + Step.levels p)
  | .ren w, p => (VarSymb.shift_ext w p k).symm
  | .tm (a := a) _, p => Ann.idxAt_shift a k p
  | .hide, _ => rfl

theorem toVar_shift : ∀ (e : SubE σ Δ) (he : e.OkRef .Var),
    Term.shift D (e.toVar he) = (e.shift D).toVar (okRef_shift D he)
  | .ren _, _ => rfl
  | .tm (.var _ _), _ => rfl
  | .tm (.func _), _ => rfl
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _), h => nomatch h
  | .tm (.diatm _ _ _), h => nomatch h
  | .hide, h => False.elim h

theorem unbox_shift : ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) →
    e.unbox.shift D.boxIn = (e.shift D).unbox
  | .ren w, _, _ => by
      change SubE.ren ((VarSymb.step w .box).shift (k + 1)) = SubE.ren (.step (w.shift k) .box)
      rw [VarSymb.shift_level_succ rfl]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem keepE_shift : ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) →
    e.keepE.shift D.boxIn = (e.shift D).keepE
  | .ren w, _, _ => by
      change SubE.ren ((VarSymb.step w .keep).shift (k + 1)) = SubE.ren (.step (w.shift k) .keep)
      rw [VarSymb.shift_level_succ rfl]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s with
      | boxtm t =>
          change (SubE.tm (Term.boxtm t)).keepE.shift D.boxIn =
            (SubE.tm (Term.boxtm (Term.shift D.boxIn t))).keepE
          by_cases hF : ModalSys.Four = true
          · rw [keepE_tm _ hF, keepE_tm _ hF]
            exact tm_eq_of_sig (sig_boxtm (Term.shift_shift (k := k) (m := 0)
              (Ctx.shifts_boxIn_boxIn hF Δ) D.boxIn.boxIn D.boxIn
              (Ctx.shifts_boxIn_boxIn hF Δ') t))
          · rw [show (SubE.tm (Term.boxtm t) : SubE σ Δ).keepE = .hide from dif_neg hF,
              show (SubE.tm (Term.boxtm (Term.shift D.boxIn t)) : SubE σ Δ').keepE = .hide
                from dif_neg hF]
            rfl

/-- The projections of a shifted entry. -/
theorem proj_shift : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step}, e.OkRef U →
    s.isProj = true → U.step s = some T → (e.proj s).shift D = (e.shift D).proj s
  | .ren w, _, _, s, _, hs, _ => by
      change SubE.ren ((VarSymb.step w s).shift k) = SubE.ren (.step (w.shift k) s)
      rw [VarSymb.shift_proj hs]
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
              change ((SubE.tm (Term.boxtm t)).proj .here).shift D =
                (SubE.tm (Term.boxtm (Term.shift D.boxIn t))).proj .here
              rw [proj_boxtm_here _ hT, proj_boxtm_here _ hT]
              exact tm_eq_of_sig (Term.shift_collapse (k := k) (m := 0) D.boxIn
                (Ctx.collapses_boxIn_self hT Δ') (Ctx.collapses_boxIn_self hT Δ) D t).symm
          | _ => cases hst

theorem diaBody_shift {ιx : VarSymb} : ∀ {e : SubE σ Δ} {X : VarType},
    e.OkRef (.VTypeDia X) → e.idxAlong [] = ιx →
    (e.diaBody ιx).shift (D.diaIn ιx) = (e.shift D).diaBody (ιx.shift k)
  | .ren w, _, _, hw => by
      have hw' : w = ιx := hw
      subst hw'
      change SubE.ren ((VarSymb.step w .dia).shift (k + 1)) = SubE.ren (.step (w.shift k) .dia)
      rw [VarSymb.shift_level_succ rfl]
  | .tm (.diatm y hy u), _, _, hw => by
      have hyx : y = ιx := hw
      subst hyx
      rw [diaBody_diatm]
      change SubE.tm (Term.shift (D.diaIn y) u) =
        (SubE.tm (Term.diatm (y.shift k) _ (Term.shift (D.diaIn y) u))).diaBody (y.shift k)
      rw [diaBody_diatm]
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

theorem Sim.shift {T : VarType} {e e' : SubE σ Δ} (h : Sim T e e') :
    Sim T (e.shift D) (e'.shift D) := by
  cases h with
  | refl => exact .refl _
  | eta_ren w hw =>
      change Sim T (SubE.tm (Term.shift D (Term.eta w T hw))) (.ren (w.shift k))
      rw [tm_eq_of_sig (Term.shift_eta D w T hw)]
      exact .eta_ren _ _
  | ren_eta w hw =>
      change Sim T (.ren (w.shift k)) (SubE.tm (Term.shift D (Term.eta w T hw)))
      rw [tm_eq_of_sig (Term.shift_eta D w T hw)]
      exact .ren_eta _ _

end SubE

/-! ## Substitutions corresponding across a shift -/

namespace Subst

variable {σ : Signature}

/-- `θ'` substitutes each shifted address as `θ` substitutes the address, shifted. -/
def ShiftCorr {k : ℕ} (Γ : Ctx) {Δ Δ' : Ctx} (D : Ctx.Shifts k Δ Δ') (θ : Subst σ Δ)
    (θ' : Subst σ Δ') : Prop :=
  ∀ v T, Γ.ref v = some T → SubE.Sim T (θ'.at (v.shift k)) ((θ.at v).shift D)

/-- Under 4, the `□□` view of a substitution corresponds to its `□` view. -/
theorem shiftCorr_box_box_of {Γ Δ : Ctx} (hF : ModalSys.Four = true) {θ : Subst σ Δ}
    (hθ : Ok Γ θ)
    (hvis : ∀ (v : VarSymb) (T : VarType), v.lastProj = false → Γ.boxIn v = some T →
      SubE.Sim T (θ.box.box.at (v.shift 0)) ((θ.box v).shift (Ctx.shifts_boxIn_boxIn hF Δ))) :
    ShiftCorr Γ.boxIn (Ctx.shifts_boxIn_boxIn hF Δ) θ.box θ.box.box := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        cases hU : Γ.boxIn.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            rw [VarSymb.shift_proj hs]
            change SubE.Sim T (if s.isProj then (θ.box.box.at (v.shift 0)).proj s else _)
              ((if s.isProj then (θ.box.at v).proj s else _).shift _)
            rw [if_pos hs, if_pos hs,
              SubE.proj_shift (Ctx.shifts_boxIn_boxIn hF Δ) (okRef_at (ok_box hθ) hU) hs hv]
            exact (ih U hU).proj_step hs hv
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [at_nonproj θ.box hlp]
        exact hvis _ _ hlp (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

theorem shiftCorr_box_box {Γ Δ : Ctx} (hF : ModalSys.Four = true) {θ : Subst σ Δ}
    (hθ : Ok Γ θ) : ShiftCorr Γ.boxIn (Ctx.shifts_boxIn_boxIn hF Δ) θ.box θ.box.box := by
  refine shiftCorr_box_box_of hF hθ ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      change SubE.Sim T ((θ.at u).keepE.unbox) ((θ.at u).unbox.shift _)
      rw [SubE.unbox_keepE hF (okRef_at hθ hu)]
      exact .refl _
  | .step u .keep =>
      obtain ⟨_, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      change SubE.Sim (.VTypeBox A) ((θ.at u).keepE.keepE) ((θ.at u).keepE.shift _)
      rw [SubE.keepE_keepE hF (okRef_at hθ hu)]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

variable {k : ℕ} {Γ Δ Δ' : Ctx} {D : Ctx.Shifts k Δ Δ'} {θ : Subst σ Δ} {θ' : Subst σ Δ'}

theorem shiftCorr_of (hθ : Ok Γ θ)
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T →
      SubE.Sim T (θ'.at (v.shift k)) ((θ v).shift D)) :
    ShiftCorr Γ D θ θ' := by
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
            rw [VarSymb.shift_proj hs]
            change SubE.Sim T (if s.isProj then (θ'.at (v.shift k)).proj s else θ' _)
              ((if s.isProj then (θ.at v).proj s else θ _).shift D)
            rw [if_pos hs, if_pos hs, SubE.proj_shift D (okRef_at hθ hU) hs hv]
            exact (ih U hU).proj_step hs hv
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [at_nonproj θ hlp]
        exact hvis _ _ hlp (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

theorem shiftCorr_box (hθ : Ok Γ θ) (hcr : ShiftCorr Γ D θ θ') :
    ShiftCorr Γ.boxIn D.boxIn θ.box θ'.box := by
  refine shiftCorr_of (ok_box hθ) ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      change SubE.Sim T (θ'.at (u.shift k)).unbox ((θ.at u).unbox.shift D.boxIn)
      rw [SubE.unbox_shift D (okRef_at hθ hu)]
      exact (hcr u _ hu).unbox
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep hv
      change SubE.Sim (.VTypeBox A) (θ'.at (u.shift k)).keepE ((θ.at u).keepE.shift D.boxIn)
      rw [SubE.keepE_shift D (okRef_at hθ hu)]
      exact (hcr u _ hu).keepE hF
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem shiftCorr_dia (hθ : Ok Γ θ) (hcr : ShiftCorr Γ D θ θ') {x ιx : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = ιx)
    (hw' : (θ'.at (x.shift k)).idxAlong [] = ιx.shift k) :
    ShiftCorr (Γ.diaIn x) (D.diaIn ιx) (θ.dia x ιx) (θ'.dia (x.shift k) (ιx.shift k)) := by
  refine shiftCorr_of (ok_dia hθ hx hw) ?_
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
        (if u.shift k = u.shift k then (θ'.at (u.shift k)).diaBody (ιx.shift k) else SubE.hide)
        ((if u = u then (θ.at u).diaBody ιx else SubE.hide).shift (D.diaIn ιx))
      rw [if_pos rfl, if_pos rfl, SubE.diaBody_shift D (okRef_at hθ hX) hw]
      exact (hcr u _ hX).diaBody hw'
  | .step u .box =>
      have hu := Ctx.boxIn_step_box (Γ := Γ) hv
      change SubE.Sim T ((θ'.at (u.shift k)).unbox.mono (Ctx.le_boxIn_diaIn Δ' (ιx.shift k)))
        ((((θ.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ ιx)).shift (D.diaIn ιx))
      rw [SubE.shift_mono D.boxIn (D.diaIn ιx) (Ctx.le_boxIn_diaIn Δ ιx)
          (Ctx.le_boxIn_diaIn Δ' (ιx.shift k)), SubE.unbox_shift D (okRef_at hθ hu)]
      exact ((hcr u _ hu).unbox).mono _
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      change SubE.Sim (.VTypeBox A)
        ((θ'.at (u.shift k)).keepE.mono (Ctx.le_boxIn_diaIn Δ' (ιx.shift k)))
        ((((θ.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ ιx)).shift (D.diaIn ιx))
      rw [SubE.shift_mono D.boxIn (D.diaIn ιx) (Ctx.le_boxIn_diaIn Δ ιx)
          (Ctx.le_boxIn_diaIn Δ' (ιx.shift k)), SubE.keepE_shift D (okRef_at hθ hu)]
      exact ((hcr u _ hu).keepE hF).mono _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem shiftCorr_under (hθ : Ok Γ θ) (hcr : ShiftCorr Γ D θ θ') {d d' : ℕ}
    (hΓ : Γ.SlotsFrom d) (T : VarType) (h : Δ (.root (.bnd d')) = none)
    (h' : Δ' (.root (.bnd d')) = none) (hr : Δ.RootFresh (.bnd d')) :
    ShiftCorr (Γ.insert (.bnd d) T) (D.insert hr T) (θ.under d d' T h) (θ'.under d d' T h') := by
  refine shiftCorr_of (ok_under hθ T h) ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    change SubE.Sim U ((θ'.under d d' T h') (.root (.bnd d)))
      ((θ.under d d' T h (.root (.bnd d))).shift (D.insert hr T))
    rw [show θ'.under d d' T h' (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl,
      show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ .bnd d := fun he => by
      rw [hΓ v d he le_rfl] at hv'
      cases hv'
    rw [at_under_ne θ' T h' (by rwa [VarSymb.shift_rt]),
      show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      SubE.shift_mono D (D.insert hr T) (Ctx.le_insert h T) (Ctx.le_insert h' T)]
    have h₁ := hcr v U ((Ctx.ref_nonproj Γ hlp).trans hv')
    rw [at_nonproj θ hlp] at h₁
    exact h₁.mono _

end Subst

/-! ## Shifting a substituted term -/

section ShiftSubst

variable {σ : Signature}

mutual
  theorem Func.shift_subst {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ Δ' : Ctx}
      (C : Ctx.Shifts k Γ Γ') (D : Ctx.Shifts k Δ Δ')
      (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
      (θ' : Subst σ Δ') (hθ' : Subst.Ok Γ' θ') (hc' : Subst.Coh ι' Γ' θ')
      (hcr : Subst.ShiftCorr Γ D θ θ') :
      {n : ℕ} → (f : Func σ Γ n) →
      Func.shift D (Func.subst ι θ hθ hc f) = Func.subst ι' θ' hθ' hc' (Func.shift C f)
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.shift D (Func.subst ι θ hθ hc g))
            (Term.shift D (Term.subst ι θ hθ hc t)) =
          Func.eval (Func.subst ι' θ' hθ' hc' (Func.shift C g))
            (Term.subst ι' θ' hθ' hc' (Term.shift C t))
        rw [Func.shift_subst C D θ hθ hc θ' hθ' hc' hcr g,
          eq_of_heq (Sigma.mk.inj (Term.shift_subst C D θ hθ hc θ' hθ' hc' hcr t)).2]
    termination_by structural _ f => f

  /-- ⭐Shifting a substituted term is substituting the corresponding entries into the shifted
      term. -/
  theorem Term.shift_subst {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ Δ' : Ctx}
      (C : Ctx.Shifts k Γ Γ') (D : Ctx.Shifts k Δ Δ')
      (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
      (θ' : Subst σ Δ') (hθ' : Subst.Ok Γ' θ') (hc' : Subst.Coh ι' Γ' θ')
      (hcr : Subst.ShiftCorr Γ D θ θ') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.shift D (Term.subst ι θ hθ hc t)⟩ : Σ b, Term σ Δ' T b) =
        ⟨_, Term.subst ι' θ' hθ' hc' (Term.shift C t)⟩
    | _, _, .var v hv =>
        congrArg (Sigma.mk _) ((SubE.toVar_shift D _ _).trans ((hcr v _ hv).toVar _ _).symm)
    | _, _, .func f => by
        change (⟨_, Term.func (Func.shift D (Func.subst ι θ hθ hc f))⟩ :
            Σ b, Term σ Δ' .Var b) = ⟨_, Term.func (Func.subst ι' θ' hθ' hc' (Func.shift C f))⟩
        rw [Func.shift_subst C D θ hθ hc θ' hθ' hc' hcr f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.shift_subst C D θ hθ hc θ' hθ' hc' hcr s)
          (Term.shift_subst C D θ hθ hc θ' hθ' hc' hcr t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.shift_subst C.boxIn D.boxIn θ.box (Subst.ok_box hθ)
          (Subst.coh_box hθ hc) θ'.box (Subst.ok_box hθ') (Subst.coh_box hθ' hc')
          (Subst.shiftCorr_box hθ hcr) t)
    | _, _, .diatm x hx t => by
        have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
        have hwι : ι' (x.shift k) = (ι x).shift k := hx.elim fun _ hX => by
          have h₁ := hc' (x.shift k) _ (C x _ hX) []
          have h₂ := (hcr x _ hX).idx
          rw [SubE.idxAlong_shift, hw] at h₂
          exact h₁.symm.trans h₂
        have hw' : (θ'.at (x.shift k)).idxAlong [] = (ι x).shift k :=
          hx.elim fun _ hX => (hc' _ _ (C x _ hX) []).trans hwι
        have key : ∀ (y : VarSymb) (_hy : y = (ι x).shift k)
            (P : ∃ Y, Δ'.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ'.diaIn (x.shift k)) (θ'.dia (x.shift k) y))
            (q : Subst.Coh ι' (Γ'.diaIn (x.shift k)) (θ'.dia (x.shift k) y)),
            (⟨_, Term.shift D (Term.subst ι θ hθ hc (Term.diatm x hx t))⟩ :
              Σ b, Term σ Δ' _ b) =
              ⟨_, Term.diatm y P
                (Term.subst ι' (θ'.dia (x.shift k) y) p q (Term.shift (C.diaIn x) t))⟩ := by
          intro y hy P p q
          subst hy
          exact sig_diatm (Term.shift_subst (C.diaIn x) (D.diaIn (ι x)) (θ.dia x (ι x))
            (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
            (θ'.dia (x.shift k) ((ι x).shift k)) p q
            (Subst.shiftCorr_dia hθ hcr hx hw hw') t)
        exact key _ hwι _ _ _
    termination_by structural _ _ t => t
end

theorem Term.shift_subst_var {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ Δ' : Ctx}
    (C : Ctx.Shifts k Γ Γ') (D : Ctx.Shifts k Δ Δ')
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (θ' : Subst σ Δ') (hθ' : Subst.Ok Γ' θ') (hc' : Subst.Coh ι' Γ' θ')
    (hcr : Subst.ShiftCorr Γ D θ θ') (t : Term σ Γ .Var .var) :
    Term.shift D (Term.subst ι θ hθ hc t) = Term.subst ι' θ' hθ' hc' (Term.shift C t) :=
  eq_of_heq (Sigma.mk.inj (Term.shift_subst C D θ hθ hc θ' hθ' hc' hcr t)).2

theorem Rel.shift_subst {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ Δ' : Ctx}
    (C : Ctx.Shifts k Γ Γ') (D : Ctx.Shifts k Δ Δ')
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
    (θ' : Subst σ Δ') (hθ' : Subst.Ok Γ' θ') (hc' : Subst.Coh ι' Γ' θ')
    (hcr : Subst.ShiftCorr Γ D θ θ') :
    {n : ℕ} → (ρ : Rel σ Γ n) →
    Rel.shift D (Rel.subst ι θ hθ hc ρ) = Rel.subst ι' θ' hθ' hc' (Rel.shift C ρ)
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.shift D (Rel.subst ι θ hθ hc ρ))
          (Term.shift D (Term.subst ι θ hθ hc t)) =
        Rel.eval (Rel.subst ι' θ' hθ' hc' (Rel.shift C ρ))
          (Term.subst ι' θ' hθ' hc' (Term.shift C t))
      rw [Rel.shift_subst C D θ hθ hc θ' hθ' hc' hcr ρ,
        Term.shift_subst_var C D θ hθ hc θ' hθ' hc' hcr t]

/-- ⭐Shifting a substituted formula is substituting into the shifted formula. -/
theorem WFF.shift_subst : {k : ℕ} → {ι ι' : VarSymb → VarSymb} → {Γ Γ' Δ Δ' : Ctx} →
    {d d' : ℕ} → (C : Ctx.Shifts k Γ Γ') → (D : Ctx.Shifts k Δ Δ') →
    (θ : Subst σ Δ) → (hθ : Subst.Ok Γ θ) → (hc : Subst.Coh ι Γ θ) →
    (θ' : Subst σ Δ') → (hθ' : Subst.Ok Γ' θ') → (hc' : Subst.Coh ι' Γ' θ') →
    (hΓ : Γ.SlotsFrom d) → (hΓ' : Γ'.SlotsFrom d) → (hΔ : Δ.SlotsFrom d') →
    (hΔ' : Δ'.SlotsFrom d') → Subst.ShiftCorr Γ D θ θ' → (φ : WFF σ Γ d) →
    WFF.shift D hΔ (WFF.subst ι θ hθ hc hΓ hΔ φ) =
      WFF.subst ι' θ' hθ' hc' hΓ' hΔ' (WFF.shift C hΓ φ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr, .atom ρ =>
      congrArg WFF.atom (Rel.shift_subst C D θ hθ hc θ' hθ' hc' hcr ρ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', _, _, _, _, hcr, .eq t s =>
      congrArg₂ WFF.eq (Term.shift_subst_var C D θ hθ hc θ' hθ' hc' hcr t)
        (Term.shift_subst_var C D θ hθ hc θ' hθ' hc' hcr s)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .and φ ψ =>
      congrArg₂ WFF.and (WFF.shift_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ)
        (WFF.shift_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .or φ ψ =>
      congrArg₂ WFF.or (WFF.shift_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ)
        (WFF.shift_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.shift_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr φ)
        (WFF.shift_subst C D θ hθ hc θ' hθ' hc' hΓ hΓ' hΔ hΔ' hcr ψ)
  | _, _, _, _, _, _, _, d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .all T φ =>
      congrArg (WFF.all T) (WFF.shift_subst (C.insert (hΓ.rootFresh le_rfl) T)
        (D.insert (hΔ.rootFresh le_rfl) T) (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (θ'.under d d' T hΔ'.root) (Subst.ok_under hθ' T hΔ'.root)
        (Subst.coh_under hθ' hc' hΓ' T hΔ'.root) (hΓ.insert T) (hΓ'.insert T) (hΔ.insert T)
        (hΔ'.insert T)
        (Subst.shiftCorr_under hθ hcr hΓ T hΔ.root hΔ'.root (hΔ.rootFresh le_rfl)) φ)
  | _, _, _, _, _, _, _, d, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .ex T φ =>
      congrArg (WFF.ex T) (WFF.shift_subst (C.insert (hΓ.rootFresh le_rfl) T)
        (D.insert (hΔ.rootFresh le_rfl) T) (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (θ'.under d d' T hΔ'.root) (Subst.ok_under hθ' T hΔ'.root)
        (Subst.coh_under hθ' hc' hΓ' T hΔ'.root) (hΓ.insert T) (hΓ'.insert T) (hΔ.insert T)
        (hΔ'.insert T)
        (Subst.shiftCorr_under hθ hcr hΓ T hΔ.root hΔ'.root (hΔ.rootFresh le_rfl)) φ)
  | _, _, _, _, _, _, _, _, _, C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .box φ =>
      congrArg WFF.box (WFF.shift_subst C.boxIn D.boxIn θ.box (Subst.ok_box hθ)
        (Subst.coh_box hθ hc) θ'.box (Subst.ok_box hθ') (Subst.coh_box hθ' hc') hΓ.boxIn
        hΓ'.boxIn hΔ.boxIn hΔ'.boxIn (Subst.shiftCorr_box hθ hcr) φ)
  | k, ι, ι', Γ, Γ', Δ, Δ', _, d', C, D, θ, hθ, hc, θ', hθ', hc', hΓ, hΓ', hΔ, hΔ', hcr,
      .dia x hx φ => by
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hwι : ι' (x.shift k) = (ι x).shift k := hx.elim fun _ hX => by
        have h₁ := hc' (x.shift k) _ (C x _ hX) []
        have h₂ := (hcr x _ hX).idx
        rw [SubE.idxAlong_shift, hw] at h₂
        exact h₁.symm.trans h₂
      have hw' : (θ'.at (x.shift k)).idxAlong [] = (ι x).shift k :=
        hx.elim fun _ hX => (hc' _ _ (C x _ hX) []).trans hwι
      have key : ∀ (y : VarSymb) (_hy : y = (ι x).shift k)
          (P : ∃ Y, Δ'.ref y = some (.VTypeDia Y))
          (p : Subst.Ok (Γ'.diaIn (x.shift k)) (θ'.dia (x.shift k) y))
          (q : Subst.Coh ι' (Γ'.diaIn (x.shift k)) (θ'.dia (x.shift k) y))
          (hΔy : (Δ'.diaIn y).SlotsFrom d'),
          WFF.shift D hΔ (WFF.subst ι θ hθ hc hΓ hΔ (.dia x hx φ)) =
            .dia y P (WFF.subst ι' (θ'.dia (x.shift k) y) p q (hΓ'.diaIn (x.shift k)) hΔy
              (WFF.shift (C.diaIn x) (hΓ.diaIn x) φ)) := by
        intro y hy P p q hΔy
        subst hy
        exact congrArg (WFF.dia ((ι x).shift k) _) (WFF.shift_subst (C.diaIn x)
          (D.diaIn (ι x)) (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (θ'.dia (x.shift k) ((ι x).shift k)) p q (hΓ.diaIn x) (hΓ'.diaIn (x.shift k))
          (hΔ.diaIn (ι x)) hΔy (Subst.shiftCorr_dia hθ hcr hx hw hw') φ)
      exact key _ hwι _ _ _ _

end ShiftSubst

end V12M
