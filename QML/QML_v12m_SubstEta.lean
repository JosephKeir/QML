import QML.QML_v12m_DiaAbs

/-!
# QML v12m — collapsing a shift, and substituting into an η-expansion

Two facts about the syntax that the equality rules and the canonical model both need, kept here so
that they are available before the proof system: shifting then collapsing at one level undoes
itself where it fixes the addresses (`Term.collapse_shift_same`), and substituting an η-expansion by
a term entry gives that entry (⭐`Term.subst_eta_tm`).  The latter is what makes Leibniz usable at
`◇`-type, since a `◇`-typed slot can only be mentioned as its own η-expansion.
-/

namespace V12M

variable [ModalSys]

/-! ## Collapsing a shift at the same level -/

/-- Shifting then collapsing at level `m` leaves every reachable address as it was. -/
def Ctx.ShiftCollapseId (m : ℕ) (Γ : Ctx) : Prop :=
  ∀ v T, Γ.ref v = some T → (v.shift m).collapse m = v

theorem Ctx.ShiftCollapseId.of_raw {m : ℕ} {Γ : Ctx}
    (h : ∀ v T, v.lastProj = false → Γ v = some T → (v.shift m).collapse m = v) :
    Γ.ShiftCollapseId m := by
  intro v
  induction v with
  | root r => intro T hv; exact h _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        rw [VarSymb.shift_proj hs, VarSymb.collapse_proj hs]
        cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [ih U hU]
      · exact h _ _ (Bool.eq_false_iff.mpr hs) (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

theorem Ctx.ShiftCollapseId.boxIn {m : ℕ} {Γ : Ctx} (h : Γ.ShiftCollapseId m) :
    Γ.boxIn.ShiftCollapseId (m + 1) := by
  refine Ctx.ShiftCollapseId.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      rw [VarSymb.shift_level_succ rfl, VarSymb.collapse_level_succ rfl,
        h u _ (Ctx.boxIn_step_box hv)]
  | .step u .keep =>
      rw [VarSymb.shift_level_succ rfl, VarSymb.collapse_level_succ rfl,
        h u _ (Ctx.boxIn_keep hv).2.1]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem Ctx.ShiftCollapseId.diaIn {m : ℕ} {Γ : Ctx} (h : Γ.ShiftCollapseId m) (x : VarSymb) :
    (Γ.diaIn x).ShiftCollapseId (m + 1) := by
  refine Ctx.ShiftCollapseId.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      cases hx : Γ.ref u with
      | none => rw [hx] at hv; cases hv
      | some U =>
          rw [VarSymb.shift_level_succ rfl, VarSymb.collapse_level_succ rfl, h u _ hx]
  | .step u .box =>
      rw [VarSymb.shift_level_succ rfl, VarSymb.collapse_level_succ rfl,
        h u _ (Ctx.boxIn_step_box (Γ := Γ) hv)]
  | .step u .keep =>
      rw [VarSymb.shift_level_succ rfl, VarSymb.collapse_level_succ rfl,
        h u _ (Ctx.boxIn_keep (Γ := Γ) hv).2.1]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- Under T and 4 a view has only kept entries, so shifting then collapsing its level is the
    identity on it. -/
theorem Ctx.shiftCollapseId_keepOnly (hk : ModalSys.keepOnly = true) (Γ : Ctx) :
    Γ.boxIn.ShiftCollapseId 0 := by
  refine Ctx.ShiftCollapseId.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box => exact absurd ((Ctx.boxIn_box hv).1.symm.trans hk) (by decide)
  | .step u .keep => rw [VarSymb.shift_level_zero rfl, VarSymb.collapse_keep_zero]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

mutual
  theorem Func.collapse_shift_same {σ : Signature} {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
      (hs : Ctx.Shifts m Γ₁ Γ₂) (hc : Ctx.Collapses m Γ₂ Γ₃) (hle : Γ₁.Le Γ₃)
      (hid : Γ₁.ShiftCollapseId m) :
      {n : ℕ} → (f : Func σ Γ₁ n) → Func.collapse hc (Func.shift hs f) = Func.mono hle f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.collapse hc (Func.shift hs g))
            (Term.collapse hc (Term.shift hs t)) = Func.eval (Func.mono hle g) (Term.mono hle t)
        rw [Func.collapse_shift_same hs hc hle hid g,
          eq_of_heq (Sigma.mk.inj (Term.collapse_shift_same hs hc hle hid t)).2]
    termination_by structural _ f => f

  /-- Where shifting then collapsing at one level fixes the addresses, it undoes itself. -/
  theorem Term.collapse_shift_same {σ : Signature} {m : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx}
      (hs : Ctx.Shifts m Γ₁ Γ₂) (hc : Ctx.Collapses m Γ₂ Γ₃) (hle : Γ₁.Le Γ₃)
      (hid : Γ₁.ShiftCollapseId m) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ₁ T a) →
      (⟨_, Term.collapse hc (Term.shift hs t)⟩ : Σ b, Term σ Γ₃ T b) = ⟨_, Term.mono hle t⟩
    | _, _, .var v hv => sig_var (hid v _ hv) _ _
    | _, _, .func f => by
        change (⟨_, Term.func (Func.collapse hc (Func.shift hs f))⟩ : Σ b, Term σ Γ₃ .Var b) =
          ⟨_, Term.func (Func.mono hle f)⟩
        rw [Func.collapse_shift_same hs hc hle hid f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.collapse_shift_same hs hc hle hid s)
          (Term.collapse_shift_same hs hc hle hid t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.collapse_shift_same (m := m + 1) hs.boxIn hc.boxIn hle.boxIn hid.boxIn t)
    | _, _, .diatm x hx t => by
        have key : ∀ (y : VarSymb) (_hy : y = (x.shift m).collapse m)
            (P : ∃ X, Γ₃.ref y = some (.VTypeDia X)) (hle' : (Γ₁.diaIn x).Le (Γ₃.diaIn y)),
            (⟨_, Term.collapse hc (Term.shift hs (Term.diatm x hx t))⟩ : Σ b, Term σ Γ₃ _ b) =
              ⟨_, Term.diatm y P (Term.mono hle' t)⟩ := by
          intro y hy P hle'
          subst hy
          exact sig_diatm (Term.collapse_shift_same (m := m + 1) (hs.diaIn x) (hc.diaIn _) hle'
            (hid.diaIn x) t)
        exact hx.elim fun _ hX => key x (hid x _ hX).symm _ _
    termination_by structural _ _ t => t
end

/-! ## Substituting into an η-expansion

Reading a witness's own content back gives the realising term: the abstraction sends the η-expansion
of `c.dia` to the hole's (`Term.subst_eta_ren`), and filling the hole undoes that expansion.  Under
`keepOnly` the `□` case goes through `keep` and `here`, where shifting then collapsing undoes itself
(`Term.collapse_shift_same`), which is why this lives here. -/

theorem Term.subst_sigma {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {θ : Subst σ Δ}
    {hθ : Subst.Ok Γ θ} {hc : Subst.Coh ι Γ θ} {T : VarType} {p q : Σ b : Ann T, Term σ Γ T b}
    (h : p = q) :
    (⟨_, Term.subst ι θ hθ hc p.2⟩ : Σ b, Term σ Δ T b) = ⟨_, Term.subst ι θ hθ hc q.2⟩ := by
  cases h
  rfl

theorem SubE.tm_sigma {σ : Signature} {Δ : Ctx} {T : VarType} {p q : Σ a : Ann T, Term σ Δ T a}
    (h : p = q) : (SubE.tm p.2 : SubE σ Δ) = SubE.tm q.2 := by
  cases h
  rfl

theorem Term.subst_eta_tm {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
    ∀ (T : VarType) (v : VarSymb) (hv : Γ.ref v = some T) {a : Ann T} (s : Term σ Δ T a),
      θ.at v = .tm s →
      (⟨_, Term.subst ι θ hθ hc (Term.eta v T hv)⟩ : Σ b, Term σ Δ T b) = ⟨a, s⟩
  | .Var, v, hv, _, s, hs => by
      match s with
      | .var v' hv' =>
          refine congrArg (Sigma.mk _) ?_
          change (θ.at v).toVar (Subst.okRef_at hθ hv) = _
          rw [SubE.toVar_congr hs _ rfl]
          exact SubE.toVar_tmSelf _ rfl
      | .func f =>
          refine congrArg (Sigma.mk _) ?_
          change (θ.at v).toVar (Subst.okRef_at hθ hv) = _
          rw [SubE.toVar_congr hs _ rfl]
          exact SubE.toVar_tmSelf _ rfl
  | .VTypeOne, _, _, _, s, _ => by
      match s with
      | .unit => rfl
  | .VTypeProd A B, v, hv, _, s, hs => by
      match s with
      | .pair s₁ s₂ =>
          have h₁ : θ.at (.step v .fst) = .tm s₁ := by
            change (θ.at v).proj .fst = _
            rw [hs]
            rfl
          have h₂ : θ.at (.step v .snd) = .tm s₂ := by
            change (θ.at v).proj .snd = _
            rw [hs]
            rfl
          exact sig_pair (Term.subst_eta_tm θ hθ hc A _ (Ctx.ref_fst_of hv) s₁ h₁)
            (Term.subst_eta_tm θ hθ hc B _ (Ctx.ref_snd_of hv) s₂ h₂)
  | .VTypeBox A, v, hv, _, s, hs => by
      match s with
      | .boxtm b =>
          have hin : θ.box.at v.inner = .tm b := by
            by_cases hk : ModalSys.keepOnly = true
            · have hTF := ModalSys.keepOnly_flags hk
              rw [VarSymb.inner_keepOnly hk]
              change (((θ.at v).keepE).proj .here) = _
              rw [hs, SubE.keepE_tm b hTF.2,
                SubE.proj_boxtm_here _ hTF.1]
              exact SubE.tm_sigma ((Term.collapse_shift_same
                (Ctx.shifts_boxIn_boxIn hTF.2 Δ)
                (Ctx.collapses_boxIn_self hTF.1 Δ.boxIn) (Ctx.Le.refl _)
                (Ctx.shiftCollapseId_keepOnly hk Δ) b).trans
                (congrArg (Sigma.mk _) (Term.mono_refl _ b)))
            · rw [VarSymb.inner_box (Bool.eq_false_iff.mpr hk)]
              change (θ.at v).unbox = _
              rw [hs]
              rfl
          exact sig_boxtm (Term.subst_eta_tm θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) A
            v.inner (Ctx.ref_inner hv) b hin)
  | .VTypeDia A, v, hv, _, s, hs => by
      match s with
      | .diatm y hy b =>
          have hwit : ι v = y := by
            have h := hc v _ hv []
            rw [hs] at h
            exact h.symm
          subst hwit
          have hbody : (θ.dia v (ι v)).at (.step v .dia) =
              .tm (Term.mono (Ctx.Le.refl _) b) := by
            change (if v = v then (θ.at v).diaBody (ι v) else .hide) = _
            rw [if_pos rfl, hs]
            change (if _h : ι v = ι v then SubE.tm (Term.mono _ b) else .hide) = _
            rw [dif_pos rfl]
          have hinner := (Term.subst_eta_tm (θ.dia v (ι v)) (Subst.ok_dia hθ ⟨A, hv⟩
              (by rw [hs]; rfl)) (Subst.coh_dia hθ hc ⟨A, hv⟩) A (.step v .dia)
            (Ctx.ref_diaIn_of hv) _ hbody).trans
            (congrArg (Sigma.mk _) (Term.mono_refl _ b))
          exact sig_diatm (hx := hy) (hx' := hy) hinner



/-! ## Reading a pair content componentwise

The hole term built from the **slot's own projection** — `η (slot.fst)` — reads a pair content down
to its first component, on both sides of `Proof.here_beta`: inside the view (`Term.viewReadTm`) and
here (`Term.hereRead`).  Both are `Term.subst_eta_tm` at a *term* entry, whose projection
`SubE.proj` takes apart; the `Sigma` is because substitution moves the annotation.  This is what
`here_beta`'s value type had to be general for.
-/

section PairHole

variable {σ : Signature} {Γ : Ctx} [Γ.NoSlots] {A B : VarType} {a : Ann A} {b : Ann B}

theorem Term.viewReadTm_eta_fst {x : VarSymb} (bd₁ : Term σ (Γ.diaIn x) A a)
    (bd₂ : Term σ (Γ.diaIn x) B b) :
    (⟨_, Term.viewReadTm (Term.pair bd₁ bd₂)
        (Term.eta (.step (.root (.bnd 0)) .fst) A
          (Ctx.ref_insert_fst Γ.boxIn (.bnd 0) A B))⟩ : Σ c, Term σ (Γ.diaIn x) A c) =
      ⟨a, bd₁⟩ := by
  simp only [Term.viewReadTm]
  rw [Term.mono_eta]
  exact Term.subst_eta_tm _ _ _ A _ _ bd₁ (Subst.at_single_fst _ bd₁ bd₂)

theorem Term.viewReadTm_eta_snd {x : VarSymb} (bd₁ : Term σ (Γ.diaIn x) A a)
    (bd₂ : Term σ (Γ.diaIn x) B b) :
    (⟨_, Term.viewReadTm (Term.pair bd₁ bd₂)
        (Term.eta (.step (.root (.bnd 0)) .snd) B
          (Ctx.ref_insert_snd Γ.boxIn (.bnd 0) A B))⟩ : Σ c, Term σ (Γ.diaIn x) B c) =
      ⟨b, bd₂⟩ := by
  simp only [Term.viewReadTm]
  rw [Term.mono_eta]
  exact Term.subst_eta_tm _ _ _ B _ _ bd₂ (Subst.at_single_snd _ bd₁ bd₂)

theorem Term.hereRead_eta_fst (hT : ModalSys.T = true) (t₁ : Term σ Γ A a) (t₂ : Term σ Γ B b) :
    (⟨_, Term.hereRead hT (Term.pair t₁ t₂)
        (Term.eta (.step (.root (.bnd 0)) .fst) A
          (Ctx.ref_insert_fst Γ.boxIn (.bnd 0) A B))⟩ : Σ c, Term σ Γ A c) = ⟨a, t₁⟩ := by
  simp only [Term.hereRead]
  refine (sig_subst _ _ _ (Term.collapse_eta _ _ A _)).trans ?_
  exact Term.subst_eta_tm _ _ _ A _ _ t₁ (Subst.at_single_fst _ t₁ t₂)

theorem Term.hereRead_eta_snd (hT : ModalSys.T = true) (t₁ : Term σ Γ A a) (t₂ : Term σ Γ B b) :
    (⟨_, Term.hereRead hT (Term.pair t₁ t₂)
        (Term.eta (.step (.root (.bnd 0)) .snd) B
          (Ctx.ref_insert_snd Γ.boxIn (.bnd 0) A B))⟩ : Σ c, Term σ Γ B c) = ⟨b, t₂⟩ := by
  simp only [Term.hereRead]
  refine (sig_subst _ _ _ (Term.collapse_eta _ _ B _)).trans ?_
  exact Term.subst_eta_tm _ _ _ B _ _ t₂ (Subst.at_single_snd _ t₁ t₂)

end PairHole

end V12M
