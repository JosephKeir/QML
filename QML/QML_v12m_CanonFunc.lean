import QML.QML_v12m_CanonDom
import QML.QML_v12m_LeibnizSpine

/-!
# QML v12m — the canonical model: the function algebra

* Argument spines from functions (`Spine.ofFn`), their values (`interpFunc_fill`,
  `relSat_fillR`), and **congruence**: provably equal arguments give provably equal
  applications and equivalent atoms (`Proof.spineCong`, `Proof.spineRelCong`).
* The canonical interpretation of the signature on classes (`canonFunc`, `canonRel`), computed on
  representatives, and its value on classes of terms at one stage (`canonFunc_cls`,
  `canonRel_cls`).
* Raw evaluation of the function algebra (`rawEval`), syntactic application of a definable map to a
  term (`applyG`; under T `extract` collapses the body, under 4 `dup` gives `□□` of the shifted
  body), which commutes with collapsing and shifting (`applyG_collapse`, `applyG_shift`), and
  ⭐`rden_applyG`: the denotation of the applied term is the evaluation.  For `dup` this is
  `rden_dup`; under T and 4 it needs shifting then collapsing one level to undo itself
  (`Term.collapse_shift_same`), which holds because views then have only kept entries.  So
  definable objects are closed under the function algebra (`definable_rawEval`).
-/

namespace V12M

variable [ModalSys]

/-! ## Spines from functions -/

/-- The spine of the arguments `ts 0, ts 1, …`. -/
def Spine.ofFn {σ : Signature} {Δ : Ctx} : {n : ℕ} → (Fin n → Term σ Δ .Var .var) → Spine σ Δ n
  | 0, _ => .nil
  | _ + 1, ts => .cons (ts 0) (Spine.ofFn fun k => ts k.succ)

theorem Spine.mono_ofFn {σ : Signature} {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ {n : ℕ} (ts : Fin n → Term σ Δ .Var .var),
      (Spine.ofFn ts).mono h = Spine.ofFn (fun k => Term.mono h (ts k))
  | 0, _ => rfl
  | _ + 1, ts => congrArg (Spine.cons _) (Spine.mono_ofFn h (fun k => ts k.succ))

theorem Term.mono_fill {σ : Signature} {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ {n : ℕ} (S : Spine σ Δ n) (f : Func σ Δ n),
      Term.mono h (.func (S.fill f)) = .func ((S.mono h).fill (Func.mono h f))
  | _, .nil, _ => rfl
  | _, .cons t S, f => Term.mono_fill h S (.eval f t)

theorem WFF.mono_fillR {σ : Signature} {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ {n : ℕ} (S : Spine σ Δ n) (ρ : Rel σ Δ n),
      WFF.mono h (.atom (S.fillR ρ) : WFF σ Δ 0) = .atom ((S.mono h).fillR (Rel.mono h ρ))
  | _, .nil, _ => rfl
  | _, .cons t S, ρ => WFF.mono_fillR h S (.eval ρ t)

/-- A spine moved down a collapsed level. -/
def Spine.collapse {σ : Signature} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) :
    {n : ℕ} → Spine σ Γ₁ n → Spine σ Γ₂ n
  | _, .nil => .nil
  | _, .cons t S => .cons (Term.collapse h t) (S.collapse h)

theorem Func.collapse_fill {σ : Signature} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) :
    ∀ {n : ℕ} (S : Spine σ Γ₁ n) (f : Func σ Γ₁ n),
      Func.collapse h (S.fill f) = (S.collapse h).fill (Func.collapse h f)
  | _, .nil, _ => rfl
  | _, .cons t S, f => Func.collapse_fill h S (.eval f t)

theorem Spine.collapse_ofFn {σ : Signature} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) :
    ∀ {n : ℕ} (ts : Fin n → Term σ Γ₁ .Var .var),
      (Spine.ofFn ts).collapse h = Spine.ofFn (fun k => Term.collapse h (ts k))
  | 0, _ => rfl
  | _ + 1, ts => congrArg (Spine.cons _) (Spine.collapse_ofFn h (fun k => ts k.succ))

/-- A spine moved one view further in. -/
def Spine.shift {σ : Signature} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂) :
    {n : ℕ} → Spine σ Γ₁ n → Spine σ Γ₂ n
  | _, .nil => .nil
  | _, .cons t S => .cons (Term.shift h t) (S.shift h)

theorem Func.shift_fill {σ : Signature} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂) :
    ∀ {n : ℕ} (S : Spine σ Γ₁ n) (f : Func σ Γ₁ n),
      Func.shift h (S.fill f) = (S.shift h).fill (Func.shift h f)
  | _, .nil, _ => rfl
  | _, .cons t S, f => Func.shift_fill h S (.eval f t)

theorem Spine.shift_ofFn {σ : Signature} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂) :
    ∀ {n : ℕ} (ts : Fin n → Term σ Γ₁ .Var .var),
      (Spine.ofFn ts).shift h = Spine.ofFn (fun k => Term.shift h (ts k))
  | 0, _ => rfl
  | _ + 1, ts => congrArg (Spine.cons _) (Spine.shift_ofFn h (fun k => ts k.succ))

namespace Model

variable {σ : Signature} {M : Model.{u} σ}

theorem interpFunc_fill {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {n : ℕ} (ts : Fin n → Term σ Δ .Var .var) (g : Func σ Δ n),
      interpFunc env ((Spine.ofFn ts).fill g) Fin.elim0 =
        interpFunc env g (fun k => interp env (ts k))
  | 0, _, g => congrArg (interpFunc env g) (funext fun k => k.elim0)
  | n + 1, ts, g => by
      change interpFunc env ((Spine.ofFn fun k => ts k.succ).fill (.eval g (ts 0))) Fin.elim0 = _
      rw [interpFunc_fill env (fun k => ts k.succ) (.eval g (ts 0))]
      change interpFunc env g (Fin.cons (interp env (ts 0)) fun k => interp env (ts k.succ)) = _
      congr 1
      funext k
      cases k using Fin.cases <;> simp

theorem relSat_fillR {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    ∀ {n : ℕ} (ts : Fin n → Term σ Δ .Var .var) (ρ : Rel σ Δ n),
      relSat env ((Spine.ofFn ts).fillR ρ) Fin.elim0 ↔
        relSat env ρ (fun k => interp env (ts k))
  | 0, ts, ρ => by
      have e : (fun k => interp env (ts k)) = (Fin.elim0 : Fin 0 → M.frame.D w) :=
        funext fun k => k.elim0
      rw [e]
      rfl
  | n + 1, ts, ρ => by
      change relSat env ((Spine.ofFn fun k => ts k.succ).fillR (.eval ρ (ts 0))) Fin.elim0 ↔ _
      rw [relSat_fillR env (fun k => ts k.succ) (.eval ρ (ts 0))]
      change relSat env ρ (Fin.cons (interp env (ts 0)) fun k => interp env (ts k.succ)) ↔ _
      have e : (Fin.cons (interp env (ts 0)) fun k => interp env (ts k.succ) : Fin (n + 1) → _) =
          fun k => interp env (ts k) := by
        funext k
        cases k using Fin.cases <;> simp
      rw [e]

end Model

/-! ## Congruence -/

/-- Provably equal arguments give provably equal applications. -/
def Proof.spineCong {σ : Signature} {Δ : Ctx} [Δ.NoSlots] {E : List (WFF σ Δ 0)} :
    ∀ {n : ℕ} (S S' : Fin n → Term σ Δ .Var .var) (G : Func σ Δ n),
      (∀ k, Proof σ Δ E (.eq (S k) (S' k))) →
      Proof σ Δ E (.eq (.func ((Spine.ofFn S).fill G)) (.func ((Spine.ofFn S').fill G)))
  | 0, _, _, _, _ => Proof.eq_intro _
  | _ + 1, S, S', G, h =>
      have p₁ := Proof.spineCong (fun k => S k.succ) (fun k => S' k.succ) (.eval G (S 0))
        (fun k => h k.succ)
      have p₂ := Proof.eq_elim (φ := WFF.eq (Term.mono holeLe (.func ((Spine.ofFn S).fill G)))
          (Term.func ((Spine.cons hole ((Spine.ofFn fun k => S' k.succ).mono holeLe)).fill
            (Func.mono holeLe G))))
        (S 0) (S' 0) (h 0)
        (Proof.conv (instantiate_funcHole _ _ G (S 0)).symm p₁)
      Proof.conv (instantiate_funcHole _ _ G (S' 0)) p₂

/-- Provably equal arguments give equivalent atoms. -/
def Proof.spineRelCong {σ : Signature} {Δ : Ctx} [Δ.NoSlots] {E : List (WFF σ Δ 0)} :
    ∀ {n : ℕ} (S S' : Fin n → Term σ Δ .Var .var) (ρ : Rel σ Δ n),
      (∀ k, Proof σ Δ E (.eq (S k) (S' k))) →
      Proof σ Δ (.atom ((Spine.ofFn S).fillR ρ) :: E) (.atom ((Spine.ofFn S').fillR ρ))
  | 0, _, _, _, _ => Proof.lookup List.mem_cons_self
  | _ + 1, S, S', ρ, h =>
      have p₁ := Proof.spineRelCong (fun k => S k.succ) (fun k => S' k.succ) (.eval ρ (S 0))
        (fun k => h k.succ)
      have p₂ := Proof.eq_elim
          (φ := WFF.atom ((Spine.cons hole ((Spine.ofFn fun k => S' k.succ).mono holeLe)).fillR
            (Rel.mono holeLe ρ)))
        (S 0) (S' 0) (Proof.weak _ (h 0))
        (Proof.conv (instantiate_relHole _ ρ (S 0)).symm p₁)
      Proof.conv (instantiate_relHole _ ρ (S' 0)) p₂

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

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

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

omit [ModalSys] in
theorem Subst.diaAbsIdx_dia_self (c : ℕ) :
    Subst.diaAbsIdx c (.step (.root (.free c)) .dia) = .root (.bnd 0) :=
  Subst.diaAbsIdx_dia c []

/-- The abstraction is a renaming by `Subst.diaAbsIdx`. -/
theorem Subst.isRen_diaAbs {σ : Signature} {Γ : Ctx} {c : ℕ} {A : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    (h₀ : Γ.boxIn (.root (.bnd 0)) = none) :
    Subst.IsRen (Subst.diaAbsIdx c) (Γ.diaIn (.root (.free c)))
      (Subst.diaAbs σ (Γ.boxIn.insert (.bnd 0) A) c) := by
  refine Subst.isRen_of (Subst.coh_diaAbs hcA hfr h₀) ?_
  intro u U _ hu
  rcases Subst.diaIn_cases hcA hfr hu with ⟨rfl, _⟩ | ⟨hrt, _, hen, _⟩
  · change (if (VarSymb.root (.free c)) = .root (.free c) then SubE.ren (.root (.bnd 0))
      else .hide) = _
    rw [if_pos rfl, Subst.diaAbsIdx_dia_self c]
  · rw [hen (Γ.boxIn.insert (.bnd 0) A), Subst.diaAbsIdx_of_rt_ne hrt]

/-- ⭐Realising the witness's own content gives the realising term back: the canonical model reads
    the content off the η-expansion of the witness's address. -/
theorem Term.realiseAt_eta {σ : Signature} {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true)
    (c : ℕ) {A : VarType} (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀) :
    (⟨_, Term.realiseAt hT c hcA hfr t₀
        (Term.eta (.step (.root (.free c)) .dia) A (Ctx.ref_diaIn_of hcA))⟩ :
      Σ b, Term σ Γ A b) = ⟨a₀, t₀⟩ := by
  have h₀ : Γ.boxIn (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root
  have hrf : Γ.boxIn.RootFresh (.bnd 0) := (Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)
  -- the abstraction sends the witness content's η-expansion to the hole's
  have habs : (⟨_, Term.diaAbs c hcA hfr
        (Term.eta (.step (.root (.free c)) .dia) A (Ctx.ref_diaIn_of hcA))⟩ :
      Σ b, Term σ (Γ.boxIn.insert (.bnd 0) A) A b) =
      ⟨_, Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A)⟩ := by
    refine (Term.subst_eta_ren _ _ _ (Subst.isRen_diaAbs hcA hfr h₀) A _ (Ctx.ref_diaIn_of hcA)
      (by rw [Subst.diaAbsIdx_dia_self c]; exact Ctx.ref_insert_root _ (.bnd 0) A)).trans ?_
    exact Term.eta_congr (Subst.diaAbsIdx_dia_self c) A _ _
  -- and filling the hole gives the realising term
  refine (Term.hereRead_sigma hT t₀ habs).trans ?_
  simp only [Term.hereRead]
  refine (Term.subst_sigma (Term.collapse_eta ((Ctx.collapses_boxIn_self hT Γ).insert hrf A)
    (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A))).trans ?_
  refine Term.subst_eta_tm _ _ _ A (.root (.bnd 0)) (Ctx.ref_insert_root _ (.bnd 0) A) t₀ ?_
  change (if (VarSymb.root (Root.bnd 0)) = .root (.bnd 0) then SubE.tm t₀
    else SubE.ren (VarSymb.root (Root.bnd 0))) = _
  rw [if_pos rfl]

/-! ## The signature on classes -/

omit [ModalSys] in
/-- A common stage for finitely many stages. -/
def stageSup {n : ℕ} (f : Fin n → ℕ × ℕ) : ℕ × ℕ := Finset.univ.sup f

omit [ModalSys] in
theorem le_stageSup {n : ℕ} (f : Fin n → ℕ × ℕ) (k : Fin n) : f k ≤ stageSup f :=
  Finset.le_sup (Finset.mem_univ k)

/-- Representatives of classes, at a common stage. -/
noncomputable def World.outArgs (w : World σ N₀) {n : ℕ} (args : Fin n → w.D) :
    Fin n → Term σ (w.L.ctx (stageSup fun k => (args k).out.1)) .Var .var :=
  fun k => w.liftT (le_stageSup (fun k => (args k).out.1) k) (args k).out.2

/-- ⭐The canonical interpretation of a function symbol. -/
noncomputable def canonFunc (w : World σ N₀) (f : σ.FuncSyms)
    (args : Fin (σ.funcArity f) → w.D) : w.D :=
  w.cls (stageSup fun k => (args k).out.1)
    (.func ((Spine.ofFn (w.outArgs args)).fill (.F ⟨f, rfl⟩)))

/-- ⭐The canonical interpretation of a relation symbol. -/
noncomputable def canonRel (w : World σ N₀) (r : σ.RelSyms)
    (args : Fin (σ.relArity r) → w.D) : Prop :=
  (⟨stageSup fun k => (args k).out.1, .atom ((Spine.ofFn (w.outArgs args)).fillR (.R ⟨r, rfl⟩))⟩ :
    w.L.sys.Sentence σ) ∈ w.T

/-- The representatives of classes of terms at one stage are equal to them, at a common stage. -/
theorem outArgs_eq {w : World σ N₀} {n : ℕ} {i : ℕ × ℕ} (ts : Fin n → Term σ (w.L.ctx i) .Var .var)
    (K : ℕ × ℕ) (hs : (stageSup fun k => (w.cls i (ts k)).out.1) ≤ K) (hi : i ≤ K) (k : Fin n) :
    (⟨K, .eq (w.liftT hs (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT hi (ts k))⟩ :
      w.L.sys.Sentence σ) ∈ w.T := by
  have h := Quotient.out_eq (s := w.setoid) (w.cls i (ts k))
  have h' : w.TEq (w.cls i (ts k)).out ⟨i, ts k⟩ := Quotient.exact h
  rw [World.TEq_iff ((le_stageSup _ k).trans hs) hi] at h'
  unfold World.outArgs
  rw [World.liftT_liftT]
  exact h'

theorem canonFunc_cls {w : World σ N₀} (f : σ.FuncSyms) {i : ℕ × ℕ}
    (ts : Fin (σ.funcArity f) → Term σ (w.L.ctx i) .Var .var) :
    canonFunc w f (fun k => w.cls i (ts k)) =
      w.cls i (.func ((Spine.ofFn ts).fill (.F ⟨f, rfl⟩))) := by
  unfold canonFunc
  set s := stageSup fun k => (w.cls i (ts k)).out.1
  refine (World.cls_eq_iff (K := s ⊔ i) le_sup_left le_sup_right).mpr ?_
  change (⟨s ⊔ i, .eq (Term.mono _ (.func ((Spine.ofFn (w.outArgs _)).fill (.F ⟨f, rfl⟩))))
    (Term.mono _ (.func ((Spine.ofFn ts).fill (.F ⟨f, rfl⟩))))⟩ : w.L.sys.Sentence σ) ∈ w.T
  rw [Term.mono_fill, Term.mono_fill, Spine.mono_ofFn, Spine.mono_ofFn]
  refine World.mem_of_provable (Δ := List.ofFn fun k => WFF.eq
      (w.liftT le_sup_left (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT le_sup_right (ts k)))
    (fun ψ hψ => ?_) ⟨Proof.spineCong _ _ _ fun k => Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩)⟩
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
  exact outArgs_eq ts _ le_sup_left le_sup_right k

theorem canonRel_cls {w : World σ N₀} (r : σ.RelSyms) {i : ℕ × ℕ}
    (ts : Fin (σ.relArity r) → Term σ (w.L.ctx i) .Var .var) :
    canonRel w r (fun k => w.cls i (ts k)) ↔
      (⟨i, .atom ((Spine.ofFn ts).fillR (.R ⟨r, rfl⟩))⟩ : w.L.sys.Sentence σ) ∈ w.T := by
  unfold canonRel
  set s := stageSup fun k => (w.cls i (ts k)).out.1
  rw [World.mem_lift (le_sup_left : s ≤ s ⊔ i), World.mem_lift (le_sup_right : i ≤ s ⊔ i),
    WFF.mono_fillR, WFF.mono_fillR, Spine.mono_ofFn, Spine.mono_ofFn]
  have heqs : ∀ k, (⟨s ⊔ i, .eq (w.liftT le_sup_left (w.outArgs (fun k => w.cls i (ts k)) k))
      (w.liftT le_sup_right (ts k))⟩ : w.L.sys.Sentence σ) ∈ w.T :=
    outArgs_eq ts _ le_sup_left le_sup_right
  constructor
  · intro h
    refine World.mem_of_provable (Δ := _ :: List.ofFn fun k => WFF.eq
        (w.liftT le_sup_left (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT le_sup_right (ts k)))
      (fun ψ hψ => ?_) ⟨Proof.spineRelCong _ _ _ fun k =>
        Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩)⟩
    · rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
        exact heqs k
  · intro h
    refine World.mem_of_provable (Δ := _ :: List.ofFn fun k => WFF.eq
        (w.liftT le_sup_left (w.outArgs (fun k => w.cls i (ts k)) k)) (w.liftT le_sup_right (ts k)))
      (fun ψ hψ => ?_) ⟨Proof.spineRelCong _ _ _ fun k =>
        Proof.eq_symm_base (Proof.lookup (List.mem_ofFn.mpr ⟨k, rfl⟩))⟩
    · rcases List.mem_cons.mp hψ with rfl | hψ
      · exact h
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hψ
        exact heqs k

/-! ## Raw evaluation and application -/

/-- ⭐The function algebra on raw objects. -/
noncomputable def rawEval :
    {A B : VarType} → GFunc σ A B → (w : World σ N₀) → RDom A w → RDom B w
  | _, _, .id _, _, o => o
  | _, _, .comp g f, w, o => rawEval g w (rawEval f w o)
  | _, _, .fst, _, o => o.1
  | _, _, .snd, _, o => o.2
  | _, _, .pair f g, w, o => (rawEval f w o, rawEval g w o)
  | _, _, .unit _, _, _ => PUnit.unit
  | _, _, .func f args, w, o => canonFunc w f (fun k => rawEval (args k) w o)
  | _, _, .boxMap f, _, o => fun w' => rawEval f w'.1 (o w')
  | _, _, .boxPair _ _, _, o => fun w' => (o.1 w', o.2 w')
  | _, _, .boxUnit, _, _ => fun _ => PUnit.unit
  | _, _, .diaMap f, _, o => ⟨o.1, fun w' => rawEval f w'.1.1 (o.2 w')⟩
  | _, _, .strength _ _, _, o => ⟨o.2.1, fun w' => (o.1 w'.1, o.2.2 w')⟩
  | _, _, .extract hT, w, o => o ⟨w, R.refl hT w⟩
  | _, _, .dup hF, _, o => fun v s => o ⟨s.1, R.trans hF v.2 s.2⟩

/-- A base-typed term with its (only possible) annotation. -/
def varTerm {Γ : Ctx} : (Σ b : Ann .Var, Term σ Γ .Var b) → Term σ Γ .Var .var
  | ⟨.var, t⟩ => t

/-- A definable map applied to a term. -/
def applyG :
    {A B : VarType} → GFunc σ A B → {Γ : Ctx} → {a : Ann A} → Term σ Γ A a →
    Σ b : Ann B, Term σ Γ B b
  | _, _, .id _, _, _, t => ⟨_, t⟩
  | _, _, .comp g f, _, _, t => applyG g (applyG f t).2
  | _, _, .fst, _, _, .pair s _ => ⟨_, s⟩
  | _, _, .snd, _, _, .pair _ u => ⟨_, u⟩
  | _, _, .pair f g, _, _, t => ⟨_, .pair (applyG f t).2 (applyG g t).2⟩
  | _, _, .unit _, _, _, _ => ⟨.one, .unit⟩
  | _, _, .func f args, _, _, t =>
      ⟨.var, .func ((Spine.ofFn fun k => varTerm (applyG (args k) t)).fill (.F ⟨f, rfl⟩))⟩
  | _, _, .boxMap f, _, _, .boxtm b => ⟨_, .boxtm (applyG f b).2⟩
  | _, _, .boxPair _ _, _, _, .pair (.boxtm b) (.boxtm c) => ⟨_, .boxtm (.pair b c)⟩
  | _, _, .boxUnit, _, _, .unit => ⟨_, .boxtm .unit⟩
  | _, _, .diaMap f, _, _, .diatm x hx c => ⟨_, .diatm x hx (applyG f c).2⟩
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c) =>
      ⟨_, .diatm x hx (.pair (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) c)⟩
  | _, _, .extract hT, Γ, _, .boxtm b => ⟨_, Term.collapse (Ctx.collapses_boxIn_self hT Γ) b⟩
  | _, _, .dup hF, Γ, _, .boxtm b =>
      ⟨_, .boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))⟩

theorem varTerm_collapse {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ₁ .Var b),
      varTerm (⟨p.1.collapse k, Term.collapse h p.2⟩ : Σ b : Ann .Var, Term σ Γ₂ .Var b) =
        Term.collapse h (varTerm p)
  | ⟨.var, _⟩ => rfl

/-- Applying a definable map commutes with collapsing. -/
theorem applyG_collapse :
    ∀ {A B : VarType} (g : GFunc σ A B) {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂)
      {a : Ann A} (t : Term σ Γ₁ A a),
    applyG g (Term.collapse h t) = ⟨(applyG g t).1.collapse k, Term.collapse h (applyG g t).2⟩
  | _, _, .id _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, _, h, _, t => by
      have hf := applyG_collapse f h t
      simp only [applyG]
      rw [hf]
      exact applyG_collapse g h _
  | _, _, .fst, _, _, _, _, _, .pair _ _ => rfl
  | _, _, .snd, _, _, _, _, _, .pair _ _ => rfl
  | _, _, .pair f g, _, _, _, h, _, t => by
      have hf := applyG_collapse f h t
      have hg := applyG_collapse g h t
      simp only [applyG, Term.collapse]
      rw [hf, hg]
      rfl
  | _, _, .unit _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, _, h, _, t => by
      have hj : ∀ j, varTerm (applyG (args j) (Term.collapse h t)) =
          Term.collapse h (varTerm (applyG (args j) t)) := fun j => by
        rw [applyG_collapse (args j) h t]
        exact varTerm_collapse h _
      simp only [applyG, Term.collapse]
      rw [Func.collapse_fill, Spine.collapse_ofFn]
      simp only [hj]
      rfl
  | _, _, .boxMap f, _, _, _, h, _, .boxtm b => by
      have hf := applyG_collapse f h.boxIn b
      simp only [applyG, Term.collapse]
      rw [hf]
      rfl
  | _, _, .boxPair _ _, _, _, _, _, _, .pair (.boxtm _) (.boxtm _) => rfl
  | _, _, .boxUnit, _, _, _, _, _, .unit => rfl
  | _, _, .diaMap f, _, _, _, h, _, .diatm x _ c => by
      have hf := applyG_collapse f (h.diaIn x) c
      simp only [applyG, Term.collapse]
      rw [hf]
      rfl
  | _, _, .strength _ _, _, Γ₁, Γ₂, h, _, .pair (.boxtm b) (.diatm x _ c) => by
      simp only [applyG, Term.collapse]
      rw [Term.collapse_mono h.boxIn (h.diaIn x) (Ctx.le_boxIn_diaIn Γ₁ x)
        (Ctx.le_boxIn_diaIn Γ₂ _) b]
      rfl
  | _, _, .extract hT, k, Γ₁, Γ₂, h, _, .boxtm b => by
      simp only [applyG, Term.collapse]
      exact Term.collapse_collapse (k := k) (m := 0) h.boxIn (Ctx.collapses_boxIn_self hT Γ₂)
        (Ctx.collapses_boxIn_self hT Γ₁) h b
  | _, _, .dup hF, k, Γ₁, Γ₂, h, _, .boxtm b => by
      simp only [applyG, Term.collapse]
      exact (sig_boxtm (sig_boxtm (Term.collapse_shift (k := k) (m := 0)
        (Ctx.shifts_boxIn_boxIn hF Γ₁) h.boxIn.boxIn h.boxIn
        (Ctx.shifts_boxIn_boxIn hF Γ₂) b))).symm

/-! ### Substitution

Applying a definable map commutes with substitution too, which is what the content of a realised
witness needs (strong T): realisation is a substitution, a collapse and a substitution. -/

/-- A spine substituted. -/
def Spine.subst {σ : Signature} (ι : VarSymb → VarSymb) {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) : {n : ℕ} → Spine σ Γ n → Spine σ Δ n
  | _, .nil => .nil
  | _, .cons t S => .cons (Term.subst ι θ hθ hc t) (Spine.subst ι θ hθ hc S)

theorem Func.subst_fill {σ : Signature} (ι : VarSymb → VarSymb) {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
    ∀ {n : ℕ} (S : Spine σ Γ n) (f : Func σ Γ n),
      Func.subst ι θ hθ hc (S.fill f) =
        (Spine.subst ι θ hθ hc S).fill (Func.subst ι θ hθ hc f)
  | _, .nil, _ => rfl
  | _, .cons t S, f => Func.subst_fill ι θ hθ hc S (.eval f t)

theorem Spine.subst_ofFn {σ : Signature} (ι : VarSymb → VarSymb) {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
    ∀ {n : ℕ} (ts : Fin n → Term σ Γ .Var .var),
      Spine.subst ι θ hθ hc (Spine.ofFn ts) = Spine.ofFn (fun k => Term.subst ι θ hθ hc (ts k))
  | 0, _ => rfl
  | _ + 1, ts => congrArg (Spine.cons _) (Spine.subst_ofFn ι θ hθ hc (fun k => ts k.succ))

theorem Func.mono_fill {σ : Signature} {Δ Δ' : Ctx} (h : Δ.Le Δ') :
    ∀ {n : ℕ} (S : Spine σ Δ n) (f : Func σ Δ n),
      Func.mono h (S.fill f) = (S.mono h).fill (Func.mono h f)
  | _, .nil, _ => rfl
  | _, .cons t S, f => Func.mono_fill h S (.eval f t)

theorem varTerm_mono {σ : Signature} {Γ Δ : Ctx} (h : Γ.Le Δ) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b),
      varTerm (⟨p.1, Term.mono h p.2⟩ : Σ b : Ann .Var, Term σ Δ .Var b) =
        Term.mono h (varTerm p)
  | ⟨.var, _⟩ => rfl

theorem varTerm_subst {σ : Signature} (ι : VarSymb → VarSymb) {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b),
      varTerm (⟨p.1.mapIdx ι, Term.subst ι θ hθ hc p.2⟩ : Σ b : Ann .Var, Term σ Δ .Var b) =
        Term.subst ι θ hθ hc (varTerm p)
  | ⟨.var, _⟩ => rfl

/-- Substituting into the `◇_x` view of a term weakened from the `□` view is weakening its
    substitution into the `□` view. -/
theorem Term.subst_dia_mono {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = ι x) {A : VarType}
    {a : Ann A} (b : Term σ Γ.boxIn A a) :
    Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
        (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) =
      Term.mono (Ctx.le_boxIn_diaIn Δ (ι x))
        (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) b) := by
  rw [Term.subst_mono, Term.mono_subst]
  refine eq_of_heq (Sigma.mk.inj (Term.subst_congr _ _ _ _ _ _ ?_ b)).2
  intro v T hv
  rw [Subst.dia_eq_box_mono θ x (ι x) v T hv, ← Subst.at_mono]
  exact .refl _

theorem varTerm_shift {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ₁ .Var b),
      varTerm (⟨p.1.shift k, Term.shift h p.2⟩ : Σ b : Ann .Var, Term σ Γ₂ .Var b) =
        Term.shift h (varTerm p)
  | ⟨.var, _⟩ => rfl

/-- Applying a definable map commutes with shifting. -/
theorem applyG_shift :
    ∀ {A B : VarType} (g : GFunc σ A B) {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂)
      {a : Ann A} (t : Term σ Γ₁ A a),
    applyG g (Term.shift h t) = ⟨(applyG g t).1.shift k, Term.shift h (applyG g t).2⟩
  | _, _, .id _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, _, h, _, t => by
      have hf := applyG_shift f h t
      simp only [applyG]
      rw [hf]
      exact applyG_shift g h _
  | _, _, .fst, _, _, _, _, _, .pair _ _ => rfl
  | _, _, .snd, _, _, _, _, _, .pair _ _ => rfl
  | _, _, .pair f g, _, _, _, h, _, t => by
      have hf := applyG_shift f h t
      have hg := applyG_shift g h t
      simp only [applyG, Term.shift]
      rw [hf, hg]
      rfl
  | _, _, .unit _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, _, h, _, t => by
      have hj : ∀ j, varTerm (applyG (args j) (Term.shift h t)) =
          Term.shift h (varTerm (applyG (args j) t)) := fun j => by
        rw [applyG_shift (args j) h t]
        exact varTerm_shift h _
      simp only [applyG, Term.shift]
      rw [Func.shift_fill, Spine.shift_ofFn]
      simp only [hj]
      rfl
  | _, _, .boxMap f, _, _, _, h, _, .boxtm b => by
      have hf := applyG_shift f h.boxIn b
      simp only [applyG, Term.shift]
      rw [hf]
      rfl
  | _, _, .boxPair _ _, _, _, _, _, _, .pair (.boxtm _) (.boxtm _) => rfl
  | _, _, .boxUnit, _, _, _, _, _, .unit => rfl
  | _, _, .diaMap f, _, _, _, h, _, .diatm x _ c => by
      have hf := applyG_shift f (h.diaIn x) c
      simp only [applyG, Term.shift]
      rw [hf]
      rfl
  | _, _, .strength _ _, _, Γ₁, Γ₂, h, _, .pair (.boxtm b) (.diatm x _ c) => by
      simp only [applyG, Term.shift]
      rw [Term.shift_mono h.boxIn (h.diaIn x) (Ctx.le_boxIn_diaIn Γ₁ x)
        (Ctx.le_boxIn_diaIn Γ₂ _) b]
      rfl
  | _, _, .extract hT, k, Γ₁, Γ₂, h, _, .boxtm b => by
      simp only [applyG, Term.shift]
      exact Term.shift_collapse (k := k) (m := 0) h.boxIn (Ctx.collapses_boxIn_self hT Γ₂)
        (Ctx.collapses_boxIn_self hT Γ₁) h b
  | _, _, .dup hF, k, Γ₁, Γ₂, h, _, .boxtm b => by
      simp only [applyG, Term.shift]
      exact (sig_boxtm (sig_boxtm (Term.shift_shift (k := k) (m := 0)
        (Ctx.shifts_boxIn_boxIn hF Γ₁) h.boxIn.boxIn h.boxIn
        (Ctx.shifts_boxIn_boxIn hF Γ₂) b))).symm

/-- ⭐Applying a definable map commutes with substitution. -/
theorem applyG_subst :
    ∀ {A B : VarType} (g : GFunc σ A B) {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ)
      (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) {a : Ann A} (t : Term σ Γ A a),
    applyG g (Term.subst ι θ hθ hc t) =
      ⟨(applyG g t).1.mapIdx ι, Term.subst ι θ hθ hc (applyG g t).2⟩
  | _, _, .id _, _, _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, _, θ, hθ, hc, _, t => by
      have hf := applyG_subst f θ hθ hc t
      simp only [applyG]
      rw [hf]
      exact applyG_subst g θ hθ hc _
  | _, _, .fst, _, _, _, _, _, _, _, .pair _ _ => rfl
  | _, _, .snd, _, _, _, _, _, _, _, .pair _ _ => rfl
  | _, _, .pair f g, _, _, _, θ, hθ, hc, _, t => by
      have hf := applyG_subst f θ hθ hc t
      have hg := applyG_subst g θ hθ hc t
      simp only [applyG, Term.subst]
      rw [hf, hg]
      rfl
  | _, _, .unit _, _, _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, ι, _, _, θ, hθ, hc, _, t => by
      have hj : ∀ j, varTerm (applyG (args j) (Term.subst ι θ hθ hc t)) =
          Term.subst ι θ hθ hc (varTerm (applyG (args j) t)) := fun j => by
        rw [applyG_subst (args j) θ hθ hc t]
        exact varTerm_subst ι θ hθ hc _
      simp only [applyG, Term.subst]
      rw [Func.subst_fill, Spine.subst_ofFn]
      simp only [hj]
      rfl
  | _, _, .boxMap f, _, _, _, θ, hθ, hc, _, .boxtm b => by
      have hf := applyG_subst f θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) b
      simp only [applyG, Term.subst]
      rw [hf]
      rfl
  | _, _, .boxPair _ _, _, _, _, _, _, _, _, .pair (.boxtm _) (.boxtm _) => rfl
  | _, _, .boxUnit, _, _, _, _, _, _, _, .unit => rfl
  | _, _, .diaMap f, ι, _, _, θ, hθ, hc, _, .diatm x hx c => by
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      have hf := applyG_subst f (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) c
      simp only [applyG, Term.subst]
      rw [hf]
      rfl
  | _, _, .strength _ _, ι, _, _, θ, hθ, hc, _, .pair (.boxtm b) (.diatm x hx c) => by
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      simp only [applyG, Term.subst]
      rw [Term.subst_dia_mono θ hθ hc hx hw b]
      rfl
  | _, _, .extract hT, _, Γ, Δ, θ, hθ, hc, _, .boxtm b => by
      simp only [applyG, Term.subst]
      exact Term.collapse_subst (Ctx.collapses_boxIn_self hT Γ) (Ctx.collapses_boxIn_self hT Δ)
        θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) θ hθ hc (Subst.corr_box_self hT hθ) b
  | _, _, .dup hF, _, Γ, Δ, θ, hθ, hc, _, .boxtm b => by
      simp only [applyG, Term.subst]
      exact sig_boxtm (sig_boxtm (Term.shift_subst (Ctx.shifts_boxIn_boxIn hF Γ)
        (Ctx.shifts_boxIn_boxIn hF Δ) θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        θ.box.box (Subst.ok_box (Subst.ok_box hθ))
        (Subst.coh_box (Subst.ok_box hθ) (Subst.coh_box hθ hc))
        (Subst.shiftCorr_box_box hF hθ) b))

/-- Applying a definable map commutes with weakening. -/
theorem applyG_mono :
    ∀ {A B : VarType} (g : GFunc σ A B) {Γ Δ : Ctx} (h : Γ.Le Δ) {a : Ann A} (t : Term σ Γ A a),
    applyG g (Term.mono h t) = ⟨(applyG g t).1, Term.mono h (applyG g t).2⟩
  | _, _, .id _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, h, _, t => by
      have hf := applyG_mono f h t
      simp only [applyG]
      rw [hf]
      exact applyG_mono g h _
  | _, _, .fst, _, _, _, _, .pair _ _ => rfl
  | _, _, .snd, _, _, _, _, .pair _ _ => rfl
  | _, _, .pair f g, _, _, h, _, t => by
      have hf := applyG_mono f h t
      have hg := applyG_mono g h t
      simp only [applyG, Term.mono]
      rw [hf, hg]
  | _, _, .unit _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, h, _, t => by
      have hj : ∀ j, varTerm (applyG (args j) (Term.mono h t)) =
          Term.mono h (varTerm (applyG (args j) t)) := fun j => by
        rw [applyG_mono (args j) h t]
        exact varTerm_mono h _
      simp only [applyG, Term.mono]
      rw [Func.mono_fill, Spine.mono_ofFn]
      simp only [hj]
      rfl
  | _, _, .boxMap f, _, _, h, _, .boxtm b => by
      have hf := applyG_mono f h.boxIn b
      simp only [applyG, Term.mono]
      rw [hf]
  | _, _, .boxPair _ _, _, _, _, _, .pair (.boxtm _) (.boxtm _) => rfl
  | _, _, .boxUnit, _, _, _, _, .unit => rfl
  | _, _, .diaMap f, _, _, h, _, .diatm x _ c => by
      have hf := applyG_mono f (h.diaIn x) c
      simp only [applyG, Term.mono]
      rw [hf]
  | _, _, .strength _ _, Γ, Δ, h, _, .pair (.boxtm b) (.diatm x _ c) => by
      simp only [applyG, Term.mono]
      rw [Term.mono_mono, Term.mono_mono]
  | _, _, .extract hT, Γ, Δ, h, _, .boxtm b => by
      simp only [applyG, Term.mono]
      exact Term.collapse_mono (Ctx.collapses_boxIn_self hT Γ) (Ctx.collapses_boxIn_self hT Δ)
        h.boxIn h b ▸ rfl
  | _, _, .dup hF, Γ, Δ, h, _, .boxtm b => by
      simp only [applyG, Term.mono]
      rw [Term.shift_mono (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.shifts_boxIn_boxIn hF Δ) h.boxIn
        h.boxIn.boxIn b]

/-- ⭐Applying a definable map commutes with realisation (strong T): realisation is a
    substitution, a collapse and a substitution. -/
theorem applyG_realiseAt {A B : VarType} (g : GFunc σ A B) {Γ : Ctx} [Γ.NoSlots]
    (hT : ModalSys.T = true) (c : ℕ) {X : VarType}
    (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia X))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a₀ : Ann X} (t₀ : Term σ Γ X a₀) {a : Ann A}
    (t : Term σ (Γ.diaIn (.root (.free c))) A a) :
    applyG g (Term.realiseAt hT c hcA hfr t₀ t) =
      ⟨_, Term.realiseAt hT c hcA hfr t₀ (applyG g t).2⟩ := by
  have habs : applyG g (Term.diaAbs c hcA hfr t) = ⟨_, Term.diaAbs c hcA hfr (applyG g t).2⟩ := by
    simp only [Term.diaAbs, applyG_subst]
  simp only [Term.realiseAt, Term.hereRead, applyG_subst]
  rw [applyG_collapse g _ (Term.diaAbs c hcA hfr t), habs]

/-- ⭐Applying a definable map commutes with the realised content of a witness. -/
theorem applyG_realisedTerm {A B : VarType} (g : GFunc σ A B) {w : World σ N₀} {x : VarSymb}
    (hr : w.Realised x) {Γ : Ctx} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i))
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    realisedTerm w hr e hx (applyG g t).2 = applyG g (realisedTerm w hr e hx t).2 := by
  simp only [realisedTerm]
  rw [applyG_realiseAt, applyG_mono]

theorem shiftIter_sigma {n : ℕ} (hF : n ≠ 0 → ModalSys.Four = true) {Γ : Ctx} {A : VarType}
    {p q : Σ b : Ann A, Term σ Γ.boxIn A b} (h : p = q) :
    (⟨_, Term.shiftIter n hF p.2⟩ : Σ b, Term σ (Ctx.boxIter (n + 1) Γ) A b) =
      ⟨_, Term.shiftIter n hF q.2⟩ := by
  subst h
  rfl

/-- Applying a definable map commutes with iterated shifting. -/
theorem applyG_shiftIter {A B : VarType} (g : GFunc σ A B) :
    ∀ (n : ℕ) (hF : n ≠ 0 → ModalSys.Four = true) {Γ : Ctx} {a : Ann A}
      (t : Term σ Γ.boxIn A a),
      applyG g (Term.shiftIter n hF t) = ⟨_, Term.shiftIter n hF (applyG g t).2⟩
  | 0, _, _, _, _ => rfl
  | n + 1, hF, Γ, _, t => by
      have hF' := hF (Nat.succ_ne_zero n)
      change applyG g (Term.shiftIter n (fun _ => hF')
        (Term.shift (Ctx.shifts_boxIn_boxIn hF' Γ) t)) = _
      rw [applyG_shiftIter g n (fun _ => hF') (Term.shift (Ctx.shifts_boxIn_boxIn hF' Γ) t)]
      exact shiftIter_sigma _ (applyG_shift g _ t)

theorem Term.shiftIter_pair : ∀ (n : ℕ) (hF : n ≠ 0 → ModalSys.Four = true) {Γ : Ctx}
    {A B : VarType} {a : Ann A} {b : Ann B} (s : Term σ Γ.boxIn A a) (t : Term σ Γ.boxIn B b),
    (⟨_, Term.shiftIter n hF (.pair s t)⟩ :
        Σ c, Term σ (Ctx.boxIter (n + 1) Γ) (.VTypeProd A B) c) =
      ⟨_, .pair (Term.shiftIter n hF s) (Term.shiftIter n hF t)⟩
  | 0, _, _, _, _, _, _, _, _ => rfl
  | n + 1, hF, Γ, _, _, _, _, s, t =>
      Term.shiftIter_pair n (fun _ => hF (Nat.succ_ne_zero n))
        (Term.shift (Ctx.shifts_boxIn_boxIn (hF (Nat.succ_ne_zero n)) Γ) s)
        (Term.shift (Ctx.shifts_boxIn_boxIn (hF (Nat.succ_ne_zero n)) Γ) t)

theorem rden_varTerm {Γ : Ctx} (w : World σ N₀) (i : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)) :
    ∀ p : (Σ b : Ann .Var, Term σ Γ .Var b), rden w i e (varTerm p) = rden w i e p.2
  | ⟨.var, _⟩ => rfl

theorem rden_var_mono {Γ : Ctx} {w : World σ N₀} {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) :
    ∀ u : Term σ Γ .Var .var, rden w i e u = w.cls i (Term.mono e u)
  | .var _ _ => rfl
  | .func _ => rfl

theorem Succ.depth_le {w : World σ N₀} (w' : Succ w) : w.depth ≤ w'.1.depth := by
  have := w'.chain.1.depth
  omega

/-- ⭐Under 4, `□□` of the shifted body reads, two steps on, what `□` of the body reads at the
    composite successor. -/
theorem rden_dup (hF : ModalSys.Four = true) : ∀ (p : ℕ) {A : VarType} {a : Ann A} {Γ : Ctx}
    (b : Term σ Γ.boxIn A a) (w : World σ N₀) (i : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)) (v : Succ w),
    v.1.depth - w.depth = p → ∀ (s : Succ v.1),
      rden w i e (.boxtm (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))) v s =
        rden w i e (.boxtm b) ⟨s.1, R.trans hF v.2 s.2⟩
  | 0, _, _, Γ, b, w, i, e, ⟨v, hv⟩, hp, s => by
      obtain ⟨hT, hw⟩ := Succ.self ⟨v, hv⟩ hp
      change v = w at hw
      subst hw
      rw [rden_boxtm_self e _ ⟨v, hv⟩ hp]
      have h₁ := rden_sigma (w := v) (i := i) e (sig_boxtm (Term.collapse_shift_self (m := 0)
        (Ctx.shifts_boxIn_boxIn hF Γ) (Ctx.collapses_boxIn_self hT Γ).boxIn (Ctx.Le.refl _) b))
      rw [Term.mono_refl] at h₁
      exact congrFun h₁ s
  | 1, _, _, Γ, b, w, i, e, v, hp, s => by
      rw [rden_boxtm_acc e _ v hp]
      rcases hq : s.1.depth - v.1.depth with _ | q
      · obtain ⟨hT, hsv⟩ := s.self hq
        have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
        have hs1 : s.1.depth - w.depth = 1 := by
          rw [hsv]
          exact hp
        rw [rden_boxtm_self _ _ s hq, rden_boxtm_acc e b ⟨s.1, R.trans hF v.2 s.2⟩ hs1]
        exact (rden_sigma _ (Term.collapse_shift_same (Ctx.shifts_boxIn_boxIn hF Γ)
          (Ctx.collapses_boxIn_self hT Γ.boxIn) (Ctx.Le.refl _)
          (Ctx.shiftCollapseId_keepOnly hk Γ) b)).trans (rden_mono _ _ _ _ _)
      · have hs2 : s.1.depth - w.depth = q + 1 + 1 := by omega
        exact (rden_boxtm_far _ _ s hq).trans
          (rden_boxtm_far e b ⟨s.1, R.trans hF v.2 s.2⟩ hs2).symm
  | p + 2, _, _, Γ, b, w, i, e, v, hp, s => by
      obtain ⟨u, hu, hr, hd⟩ := v.split hp
      have hne : v.1.depth - u.depth ≠ 0 := by omega
      have hsu : s.1.depth - u.depth ≠ 0 := by
        have := s.depth_le
        omega
      have hsh := Term.shift_shift_same (m := 0) (Ctx.shifts_boxIn_boxIn hF Γ)
        (Ctx.shifts_boxIn_boxIn hF Γ.boxIn) (Ctx.shifts_boxIn_boxIn hF Γ).boxIn b
      exact (congrFun (rden_boxtm_step hF e (.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b))
          v hu hr hne) s).trans
        ((congrFun (congrFun (rden_sigma _ (sig_boxtm (sig_boxtm hsh.symm))) ⟨v.1, hr⟩) s).trans
          ((rden_dup hF (p + 1) (Term.shift (Ctx.shifts_boxIn_boxIn hF Γ) b) u (childStage i) _
              ⟨v.1, hr⟩ hd s).trans
            (rden_boxtm_step hF e b ⟨s.1, R.trans hF v.2 s.2⟩ hu (R.trans hF hr s.2) hsu).symm))

/-! ### The strong-T gap

Two facts about the content a realised witness has at the world itself.  Both are instances of a
general `applyG_subst` — the substitution analogue of `applyG_collapse`, which needs a `Spine.subst`
and `Func.subst_fill` — composed with `applyG_collapse` itself, because realisation is a
substitution, a collapse and a substitution (`Term.realiseAt`).  Nothing else in the canonical
model depends on them, so they are isolated here while that lemma is written. -/

theorem rawEval_transport {A B : VarType} (g : GFunc σ A B) {w₁ w₂ : World σ N₀} (hw : w₁ = w₂)
    (o : RDom A w₁) : hw ▸ (rawEval g w₁ o) = rawEval g w₂ (hw ▸ o) := by
  cases hw
  rfl

/-- ⭐The denotation of an applied map is its raw evaluation.  Under strong T the extent has the
    world itself in it, where the content is a realisation (`applyG_realisedTerm`,
    `rden_realisedTerm_mono_boxIn`). -/
theorem rden_applyG :
    ∀ {A B : VarType} (g : GFunc σ A B) {Γ : Ctx} {a : Ann A} (t : Term σ Γ A a)
      (w : World σ N₀) (i : ℕ × ℕ) (e : Γ.Le (w.L.ctx i)),
    rden w i e (applyG g t).2 = rawEval g w (rden w i e t)
  | _, _, .id _, _, _, _, _, _, _ => rfl
  | _, _, .comp g f, _, _, t, w, i, e =>
      (rden_applyG g _ w i e).trans (congrArg (rawEval g w) (rden_applyG f t w i e))
  | _, _, .fst, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .snd, _, _, .pair _ _, _, _, _ => rfl
  | _, _, .pair f g, _, _, t, w, i, e => Prod.ext (rden_applyG f t w i e) (rden_applyG g t w i e)
  | _, _, .unit _, _, _, _, _, _, _ => rfl
  | _, _, .func f args, _, _, t, w, i, e => by
      change rden w i e (.func _) = canonFunc w f (fun k => rawEval (args k) w (rden w i e t))
      have hk : (fun k => rawEval (args k) w (rden w i e t)) =
          fun k => w.cls i (Term.mono e (varTerm (applyG (args k) t))) := by
        funext k
        rw [← rden_applyG (args k) t w i e, ← rden_varTerm, rden_var_mono]
      rw [hk, canonFunc_cls, rden_var_mono, Term.mono_fill, Spine.mono_ofFn]
      rfl
  | _, _, .boxMap f, Γ, _, .boxtm b, w, i, e => funext fun w' => by
      change rden w i e (.boxtm (applyG f b).2) w' = rawEval f w'.1 (rden w i e (.boxtm b) w')
      rcases hd : w'.1.depth - w.depth with _ | d
      · rw [rden_boxtm_self e _ w' hd, rden_boxtm_self e b w' hd]
        exact (rden_sigma _
          (applyG_collapse f (Ctx.collapses_boxIn_self (w'.self hd).1 Γ) b)).symm.trans
          (rden_applyG f _ w'.1 i _)
      · rw [rden_boxtm_far e _ w' hd, rden_boxtm_far e b w' hd]
        exact (rden_sigma _ (applyG_shiftIter f d (w'.four hd) b)).symm.trans
          (rden_applyG f _ w'.1 _ _)
  | _, _, .boxPair _ _, _, _, .pair (.boxtm b) (.boxtm c), w, i, e => funext fun w' => by
      change rden w i e (.boxtm (.pair b c)) w' =
        (rden w i e (.boxtm b) w', rden w i e (.boxtm c) w')
      rcases hd : w'.1.depth - w.depth with _ | d
      · rw [rden_boxtm_self e _ w' hd, rden_boxtm_self e b w' hd, rden_boxtm_self e c w' hd]
        rfl
      · rw [rden_boxtm_far e _ w' hd, rden_boxtm_far e b w' hd, rden_boxtm_far e c w' hd]
        exact rden_sigma _ (Term.shiftIter_pair d (w'.four hd) b c)
  | _, _, .boxUnit, _, _, .unit, _, _, _ => rfl
  | _, _, .diaMap f, _, _, .diatm x hx c, w, i, e =>
      congrArg (Sigma.mk _) (funext fun w' => by
        by_cases hd : w'.1.1.depth - w.depth = 0
        · have hr := (extent_self w'.2 hd).2
          rw [rden_diatm_self e hx c w' hd, ← rawEval_transport f _ _]
          simp only [dif_pos hd]
          refine rden_transport_congr _ ?_
          exact (rden_sigma _ (applyG_realisedTerm f hr e hx c)).trans (rden_applyG f _ w _ _)
        · simp only [rden, dif_neg hd]
          exact rden_applyG f c w'.1.1 (childStage i) _)
  | _, _, .strength _ _, Γ, _, .pair (.boxtm b) (.diatm x hx c), w, i, e =>
      congrArg (Sigma.mk _) (funext fun w' => by
        by_cases hd : w'.1.1.depth - w.depth = 0
        · have hr := (extent_self w'.2 hd).2
          change _ = (rden w i e (Term.boxtm b) w'.1, (rden w i e (Term.diatm x hx c)).2 w')
          rw [rden_diatm_self e hx c w' hd, rden_boxtm_self e b w'.1 hd]
          simp only [dif_pos hd]
          rw [rden_realisedTerm_pair hr e hx, rden_transport_pair]
          refine Prod.ext ?_ rfl
          refine (rden_transport_congr _ (rden_realisedTerm_mono_boxIn hr e hx b)).trans ?_
          exact rden_transport_world _ _ _ _
        · simp only [rden, dif_neg hd]
          exact Prod.ext
            ((rden_mono _ _ _ _ _).trans
              (rden_boxtm_acc e b w'.1 (extent_dist w'.2 hd)).symm) rfl)
  | _, _, .extract hT, _, _, .boxtm b, w, _, e =>
      (rden_boxtm_self e b ⟨w, R.refl hT w⟩ (Nat.sub_self _)).symm
  | _, _, .dup hF, _, _, .boxtm b, w, i, e =>
      funext fun v => funext fun s => rden_dup hF _ b w i e v rfl s

/-- ⭐Definable objects are closed under the function algebra. -/
-- (`applyG_realisedTerm`, `rawEval_transport` and `strength_self` above are the strong-T gap;
-- see the note before `rden_applyG`.)
theorem definable_rawEval {A B : VarType} (g : GFunc σ A B) {w : World σ N₀}
    {o : RDom A w}
    (h : Definable A w o) : Definable B w (rawEval g w o) := by
  obtain ⟨i, a, t, rfl⟩ := h
  exact ⟨i, _, (applyG g t).2, rden_applyG g t w i _⟩


/-! ### The witness's own content -/

/-- Realisation respects equality of the view term, annotations and all. -/
theorem Term.realiseAt_sigma {Γ : Ctx} [Γ.NoSlots] (hT : ModalSys.T = true)
    (c : ℕ) {A : VarType} (hcA : Γ.ref (.root (.free c)) = some (.VTypeDia A))
    (hfr : ∀ v : VarSymb, v.rt = .free c → v ≠ .root (.free c) → Γ v = none)
    {a₀ : Ann A} (t₀ : Term σ Γ A a₀) {T : VarType} {b b' : Ann T}
    {t : Term σ (Γ.diaIn (.root (.free c))) T b} {t' : Term σ (Γ.diaIn (.root (.free c))) T b'}
    (h : (⟨b, t⟩ : Σ z : Ann T, Term σ (Γ.diaIn (.root (.free c))) T z) = ⟨b', t'⟩) :
    (⟨_, Term.realiseAt hT c hcA hfr t₀ t⟩ : Σ z : Ann T, Term σ Γ T z) =
      ⟨_, Term.realiseAt hT c hcA hfr t₀ t'⟩ := by
  cases h
  rfl

/-- ⭐The realised content of the witness's own content is the realising term: this is what makes
    every object the content, at the world itself, of a possible object. -/
theorem rden_realisedTerm_eta {w : World σ N₀} {x : VarSymb} (hr : w.Realised x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (hdia : (Γ.diaIn x).ref (.step x .dia) = some hr.data.A) :
    rden w (i ⊔ hr.data.i₀) (Ctx.Le.refl _)
        (realisedTerm w hr e hx (Term.eta (.step x .dia) hr.data.A hdia)).2 =
      rden w hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀ := by
  have hmono : (⟨_, Term.mono (realisedLe w hr e) (Term.eta (.step x .dia) hr.data.A hdia)⟩ :
      Σ z : Ann hr.data.A,
        Term σ ((w.L.ctx (i ⊔ hr.data.i₀)).diaIn (.root (.free hr.data.c))) hr.data.A z) =
      ⟨_, Term.eta (.step (.root (.free hr.data.c)) .dia) hr.data.A
        (Ctx.ref_diaIn_of (realisedDecl hr e hx))⟩ := by
    rw [Term.mono_eta]
    exact Term.eta_congr (congrArg (fun v => VarSymb.step v .dia) hr.data.hx) _ _ _
  simp only [realisedTerm]
  rw [rden_sigma _ (Term.realiseAt_sigma hr.data.hT hr.data.c (realisedDecl hr e hx)
      (hr.data.hfr _) _ hmono),
    rden_sigma _ (Term.realiseAt_eta hr.data.hT hr.data.c (realisedDecl hr e hx)
      (hr.data.hfr _) (Term.mono (w.L.ctx_le le_sup_right) hr.data.t₀)),
    rden_mono]
  exact rden_congr _ _ _ _ _ _

/-- The same, with the type of the content given separately. -/
theorem rden_realisedTerm_eta_sigma {w : World σ N₀} {x : VarSymb} (hr : w.Realised x) {Γ : Ctx}
    {i : ℕ × ℕ} (e : Γ.Le (w.L.ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    (hA : hr.data.A = A) (hdia : (Γ.diaIn x).ref (.step x .dia) = some A) :
    (⟨A, rden w (i ⊔ hr.data.i₀) (Ctx.Le.refl _)
        (realisedTerm w hr e hx (Term.eta (.step x .dia) A hdia)).2⟩ : Σ B, RDom B w) =
      ⟨hr.data.A, rden w hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀⟩ := by
  subst hA
  exact congrArg _ (rden_realisedTerm_eta hr e hx hdia)

/-- ⭐The content, at the world itself, of the possible object a realised witness names: what its
    realising term denotes.  Stated in terms of the world's own choice. -/
theorem rden_eta_realised {w : World σ N₀} {x : VarSymb} (hr : w.Realised x)
    {k : ℕ × ℕ} (hdecl : (w.L.ctx k).ref x = some (.VTypeDia hr.data.A)) :
    (rden w k (Ctx.Le.refl _) (Term.eta x (.VTypeDia hr.data.A) hdecl)).2
        ⟨⟨w, R.refl hr.T w⟩, self_mem_extent hr⟩ =
      rden w hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀ :=
  (rden_diatm_self (Ctx.Le.refl _) ⟨hr.data.A, hdecl⟩
    (Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl))
    ⟨⟨w, R.refl hr.T w⟩, self_mem_extent hr⟩ (Nat.sub_self _)).trans
    (rden_realisedTerm_eta hr (Ctx.Le.refl _) ⟨hr.data.A, hdecl⟩ (Ctx.ref_diaIn_of hdecl))

/-- The same for any datum the world's choice is known to be.  Taking the datum as a variable with
    an equation turns the identification into a `subst`, so callers never have to rewrite under
    `realisedTerm`, where it sits in dependent positions. -/
theorem rden_eta_realised_of_eq {w : World σ N₀} {c : ℕ} (hr : w.Realised (.root (.free c)))
    (D : w.RealData (.root (.free c))) (hD : hr.data = D) {k : ℕ × ℕ}
    (hdecl : (w.L.ctx k).ref (.root (.free c)) = some (.VTypeDia D.A)) :
    (rden w k (Ctx.Le.refl _) (Term.eta (.root (.free c)) (.VTypeDia D.A) hdecl)).2
        ⟨⟨w, R.refl hr.T w⟩, self_mem_extent hr⟩ =
      rden w D.i₀ (Ctx.Le.refl _) D.t₀ := by
  subst hD
  exact rden_eta_realised hr hdecl

/-- ⭐What a world names at a root, as the model uses it: the content, at the world itself, of the
    possible object that root denotes is what the named realising term denotes. -/
theorem rden_eta_of_real {w : World σ N₀} {c : ℕ} {d : RealDatum σ w.L w.T c}
    (hsome : w.real c = some d) {k : ℕ × ℕ}
    (hdecl : (w.L.ctx k).ref (.root (.free c)) = some (.VTypeDia d.A)) :
    (rden w k (Ctx.Le.refl _) (Term.eta (.root (.free c)) (.VTypeDia d.A) hdecl)).2
        ⟨⟨w, R.refl (World.realised_of_real hsome).T w⟩,
          self_mem_extent (World.realised_of_real hsome)⟩ =
      rden w d.i₀ (Ctx.Le.refl _) d.t₀ :=
  rden_eta_realised_of_eq _ ⟨c, rfl, d⟩ (World.data_of_real hsome) hdecl

end Canon

end V12M
