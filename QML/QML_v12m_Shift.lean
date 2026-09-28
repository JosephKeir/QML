import QML.QML_v12m_Collapse

/-!
# QML v12m — shifting a level (weak 4)

Under 4 a necessary object is kept, restricted, inside a `□` (`u.keep`).  Syntactically this moves
a term or formula written in a `□` view one view further in: every address that descends through
the shifted level is reached through a `keep` first (`u.box ↦ u.keep.box`,
`u.keep ↦ u.keep.keep`).  Inside the moved syntax there are further views, so the shifted step is
the level step with exactly `k` level steps after it (`VarSymb.shift k`).

* `Ctx.Shifts k Γ₁ Γ₂`: everything `Γ₁` reaches, `Γ₂` reaches after shifting.  It holds for
  `Γ.boxIn` and `Γ.boxIn.boxIn` under 4 (`Ctx.shifts_boxIn_boxIn`) and passes into views and
  binders.
* `Term.shift`, `WFF.shift`: the syntactic operations.
-/

namespace V12M

/-! ## Shifting addresses -/

namespace VarSymb

/-- A shift outside another shift commutes with it (the outer one moves out by one). -/
theorem shift_shift : ∀ (v : VarSymb) (k m : ℕ),
    (v.shift (k + 1 + m)).shift m = (v.shift m).shift (k + 2 + m)
  | root _, _, _ => rfl
  | step v s, k, m => by
      by_cases hs : s.isProj = true
      · simp only [shift_proj hs, shift_shift v k m]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases m with
        | zero =>
            simp only [Nat.add_zero, shift_level_succ hs', shift_level_zero hs',
              shift_level_succ (s := Step.keep) rfl]
        | succ m =>
            rw [show k + 1 + (m + 1) = (k + 1 + m) + 1 by omega,
              show k + 2 + (m + 1) = (k + 2 + m) + 1 by omega]
            simp only [shift_level_succ hs']
            rw [shift_shift v k m]

/-- Shifting twice at the same level inserts two adjacent `keep`s, in either order. -/
theorem shift_shift_same : ∀ (v : VarSymb) (m : ℕ),
    (v.shift m).shift m = (v.shift m).shift (m + 1)
  | root _, _ => rfl
  | step v s, m => by
      by_cases hs : s.isProj = true
      · simp only [shift_proj hs, shift_shift_same v m]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases m with
        | zero =>
            simp only [shift_level_zero hs', shift_level_succ hs',
              shift_level_zero (s := Step.keep) rfl]
        | succ m =>
            simp only [shift_level_succ hs']
            rw [shift_shift_same v m]

/-- A shift outside a collapse commutes with it (the shift moves in by one). -/
theorem shift_collapse : ∀ (v : VarSymb) (k m : ℕ),
    (v.shift (k + 1 + m)).collapse m = (v.collapse m).shift (k + m)
  | root _, _, _ => rfl
  | step v s, k, m => by
      by_cases hs : s.isProj = true
      · simp only [shift_proj hs, collapse_proj hs, shift_collapse v k m]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases m with
        | zero =>
            by_cases hk : s = .keep
            · subst hk
              simp only [Nat.add_zero, shift_level_succ (s := Step.keep) rfl, collapse_keep_zero]
            · simp only [Nat.add_zero, shift_level_succ hs', collapse_level_zero hs' hk,
                shift_proj (s := Step.here) rfl]
        | succ m =>
            rw [show k + 1 + (m + 1) = (k + 1 + m) + 1 by omega,
              show k + (m + 1) = (k + m) + 1 by omega]
            simp only [shift_level_succ hs', collapse_level_succ hs']
            rw [shift_collapse v k m]

/-- Collapsing just outside a shift removes the inserted `keep`. -/
theorem collapse_shift_self : ∀ (v : VarSymb) (m : ℕ), (v.shift m).collapse (m + 1) = v
  | root _, _ => rfl
  | step v s, m => by
      by_cases hs : s.isProj = true
      · simp only [shift_proj hs, collapse_proj hs, collapse_shift_self v m]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases m with
        | zero =>
            simp only [shift_level_zero hs', collapse_level_succ hs', collapse_keep_zero]
        | succ m =>
            simp only [shift_level_succ hs', collapse_level_succ hs', collapse_shift_self v m]

theorem shift_ext : ∀ (w : VarSymb) (p : List Step) (k : ℕ),
    (w.ext p).shift (k + Step.levels p) = (w.shift k).ext p
  | _, [], _ => rfl
  | w, s :: p, k => by
      change ((VarSymb.step w s).ext p).shift _ = (VarSymb.step (w.shift k) s).ext p
      by_cases hs : s.isProj = true
      · rw [Step.levels_cons, if_pos hs, Nat.zero_add, VarSymb.shift_ext (.step w s) p k,
          VarSymb.shift_proj hs]
      · rw [Step.levels_cons, if_neg hs, show k + (1 + Step.levels p) = (k + 1) + Step.levels p
          by omega, VarSymb.shift_ext (.step w s) p (k + 1),
          VarSymb.shift_level_succ (Bool.eq_false_iff.mpr hs)]

end VarSymb

variable [ModalSys]

/-- Shifting a level further out keeps a contents address a contents address. -/
theorem VarSymb.inner_shift_succ (u : VarSymb) (k : ℕ) :
    u.inner.shift (k + 1) = (u.shift k).inner := by
  unfold VarSymb.inner
  split_ifs
  · rw [VarSymb.shift_proj (s := .here) rfl, VarSymb.shift_level_succ (s := .keep) rfl]
  · rw [VarSymb.shift_level_succ (s := .box) rfl]

/-- Shifting the view of a contents address gives the contents of the kept object. -/
theorem VarSymb.inner_shift_zero (u : VarSymb) :
    u.inner.shift 0 = (VarSymb.step u .keep).inner := by
  unfold VarSymb.inner
  split_ifs
  · rw [VarSymb.shift_proj (s := .here) rfl, VarSymb.shift_level_zero (s := .keep) rfl]
  · rw [VarSymb.shift_level_zero (s := .box) rfl]

/-! ## Shifting contexts -/

namespace Ctx

/-- `Γ₂` reaches everything `Γ₁` reaches, with a level inserted below the level `k`. -/
def Shifts (k : ℕ) (Γ₁ Γ₂ : Ctx) : Prop :=
  ∀ v T, Γ₁.ref v = some T → Γ₂.ref (v.shift k) = some T

/-- It suffices to check the visible non-projection addresses. -/
theorem Shifts.of_raw {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : ∀ v T, v.lastProj = false → Γ₁ v = some T → Γ₂.ref (v.shift k) = some T) :
    Shifts k Γ₁ Γ₂ := by
  intro v
  induction v with
  | root r => intro T hv; exact h _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        rw [VarSymb.shift_proj hs, Ctx.ref_step_proj _ _ hs]
        cases hU : Γ₁.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [hU] at hv; rw [ih U hU]; exact hv
      · exact h _ _ (show s.isProj = false from Bool.eq_false_iff.mpr hs)
          (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

/-- Under 4, a reachable necessary address is kept inside `□`. -/
theorem ref_keep_of {Γ : Ctx} (hF : ModalSys.Four = true) {w : VarSymb} {A : VarType}
    (h : Γ.ref w = some (.VTypeBox A)) : Γ.boxIn.ref (.step w .keep) = some (.VTypeBox A) :=
  (Ctx.ref_nonproj Γ.boxIn (v := .step w .keep) rfl).trans (boxIn_keep_of hF h)

/-- The contents address of a reachable necessary address is reachable inside `□`. -/
theorem ref_inner {Γ : Ctx} {w : VarSymb} {A : VarType} (h : Γ.ref w = some (.VTypeBox A)) :
    Γ.boxIn.ref w.inner = some A := by
  cases hk : ModalSys.keepOnly with
  | true =>
      obtain ⟨hT, hF⟩ := ModalSys.keepOnly_flags hk
      rw [VarSymb.inner_keepOnly hk, Ctx.ref_step_proj _ _ rfl, ref_keep_of hF h]
      simp only [Option.bind_some, VarType.step, hT, if_true]
  | false =>
      rw [VarSymb.inner_box hk, Ctx.ref_nonproj _ rfl]
      exact boxIn_box_of hk h

/-- ⭐Under 4 the `□` view shifts one view further in. -/
theorem shifts_boxIn_boxIn (hF : ModalSys.Four = true) (Γ : Ctx) :
    Shifts 0 Γ.boxIn Γ.boxIn.boxIn := by
  refine Shifts.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := boxIn_box hv
      rw [VarSymb.shift_level_zero rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_box_of hk (ref_keep_of hF hu)
  | .step u .keep =>
      obtain ⟨_, hu, A, rfl⟩ := boxIn_keep hv
      rw [VarSymb.shift_level_zero rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_keep_of hF (ref_keep_of hF hu)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem Shifts.boxIn {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Shifts k Γ₁ Γ₂) :
    Shifts (k + 1) Γ₁.boxIn Γ₂.boxIn := by
  refine Shifts.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      obtain ⟨hk, hu⟩ := boxIn_box hv
      rw [VarSymb.shift_level_succ rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_box_of hk (h u _ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := boxIn_keep hv
      rw [VarSymb.shift_level_succ rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_keep_of hF (h u _ hu)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem Shifts.diaIn {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Shifts k Γ₁ Γ₂) (x : VarSymb) :
    Shifts (k + 1) (Γ₁.diaIn x) (Γ₂.diaIn (x.shift k)) := by
  refine Shifts.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ₁.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      subst hux
      cases hx : Γ₁.ref u with
      | none => rw [hx] at hv; cases hv
      | some U =>
          rw [hx] at hv
          rw [VarSymb.shift_level_succ rfl, Ctx.ref_nonproj _ rfl]
          change (if u.shift k = u.shift k then
            (match Γ₂.ref (u.shift k) with | some (.VTypeDia X) => some X | _ => none)
            else none) = some T
          rw [if_pos rfl, h u _ hx]
          exact hv
  | .step u .box =>
      obtain ⟨hk, hu⟩ := boxIn_box (Γ := Γ₁) hv
      rw [VarSymb.shift_level_succ rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_box_of (Γ := Γ₂) hk (h u _ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := boxIn_keep (Γ := Γ₁) hv
      rw [VarSymb.shift_level_succ rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_keep_of hF (h u _ hu)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem Shifts.insert {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Shifts k Γ₁ Γ₂) {r : Root}
    (hr : Γ₁.RootFresh r) (T : VarType) : Shifts k (Γ₁.insert r T) (Γ₂.insert r T) := by
  refine Shifts.of_raw ?_
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact ref_insert_root Γ₂ r T
  · have hv' : Γ₁ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ r := fun he => by rw [hr v he] at hv'; cases hv'
    rw [ref_insert_ne T (by rwa [VarSymb.shift_rt])]
    exact h v U ((Ctx.ref_nonproj Γ₁ hlp).trans hv')

end Ctx

/-! ## Shifting terms and formulas -/

mutual
  def Func.shift {σ : Signature} {k : ℕ} : {Γ₁ Γ₂ : Ctx} → Ctx.Shifts k Γ₁ Γ₂ →
      {n : ℕ} → Func σ Γ₁ n → Func σ Γ₂ n
    | _, _, _, _, .F f => .F f
    | _, _, h, _, .eval g t => .eval (Func.shift h g) (Term.shift h t)

  /-- ⭐Moving a term one view further in. -/
  def Term.shift {σ : Signature} {k : ℕ} : {Γ₁ Γ₂ : Ctx} → Ctx.Shifts k Γ₁ Γ₂ →
      {T : VarType} → {a : Ann T} → Term σ Γ₁ T a → Term σ Γ₂ T (a.shift k)
    | _, _, h, _, _, .var v hv => .var (v.shift k) (h v _ hv)
    | _, _, h, _, _, .func f => .func (Func.shift h f)
    | _, _, _, _, _, .unit => .unit
    | _, _, h, _, _, .pair s t => .pair (Term.shift h s) (Term.shift h t)
    | _, _, h, _, _, .boxtm t => .boxtm (Term.shift h.boxIn t)
    | _, _, h, _, _, .diatm x hx t =>
        .diatm (x.shift k) (hx.imp fun _ hX => h x _ hX) (Term.shift (h.diaIn x) t)
end

def Rel.shift {σ : Signature} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Shifts k Γ₁ Γ₂) :
    {n : ℕ} → Rel σ Γ₁ n → Rel σ Γ₂ n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.shift h ρ) (Term.shift h t)

/-- ⭐Moving a formula one view further in. -/
def WFF.shift {σ : Signature} : {k : ℕ} → {Γ₁ Γ₂ : Ctx} → {d : ℕ} →
    Ctx.Shifts k Γ₁ Γ₂ → Γ₁.SlotsFrom d → WFF σ Γ₁ d → WFF σ Γ₂ d
  | _, _, _, _, h, _, .atom ρ => .atom (Rel.shift h ρ)
  | _, _, _, _, h, _, .eq t s => .eq (Term.shift h t) (Term.shift h s)
  | _, _, _, _, _, _, .top => .top
  | _, _, _, _, _, _, .bot => .bot
  | _, _, _, _, h, hs, .and φ ψ => .and (WFF.shift h hs φ) (WFF.shift h hs ψ)
  | _, _, _, _, h, hs, .or φ ψ => .or (WFF.shift h hs φ) (WFF.shift h hs ψ)
  | _, _, _, _, h, hs, .imp φ ψ => .imp (WFF.shift h hs φ) (WFF.shift h hs ψ)
  | _, _, _, _, h, hs, .all T φ =>
      .all T (WFF.shift (h.insert (hs.rootFresh le_rfl) T) (hs.insert T) φ)
  | _, _, _, _, h, hs, .ex T φ =>
      .ex T (WFF.shift (h.insert (hs.rootFresh le_rfl) T) (hs.insert T) φ)
  | _, _, _, _, h, hs, .box φ => .box (WFF.shift h.boxIn hs.boxIn φ)
  | k, _, _, _, h, hs, .dia x hx φ =>
      .dia (x.shift k) (hx.imp fun _ hX => h x _ hX) (WFF.shift (h.diaIn x) (hs.diaIn x) φ)
  | _, _, _, _, h, _, .here hT hA s t => .here hT hA (Term.shift h s) (Term.shift h t)


/-- ⭐Shifting commutes with equality at every type, as `eqRec_collapse` does for collapsing: what a
    `□`-equation gives at a proper successor, one step in. -/
theorem eqRec_shift {σ : Signature} {k : ℕ} {d : ℕ} : {Γ₁ Γ₂ : Ctx} →
    (h : Ctx.Shifts k Γ₁ Γ₂) → (hs : Γ₁.SlotsFrom d) → (T : VarType) → {a : Ann T} →
    (t s : Term σ Γ₁ T a) →
    WFF.shift h hs (eqRec T t s : WFF σ Γ₁ d) = eqRec T (Term.shift h t) (Term.shift h s)
  | _, _, h, hs, .Var, .var, t, s =>
      (congrArg (WFF.shift h hs) (eqRec_Var t s)).trans (eqRec_Var _ _).symm
  | _, _, _, _, .VTypeOne, .one, .unit, .unit => rfl
  | _, _, h, hs, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change WFF.and (WFF.shift h hs (eqRec A t₁ s₁)) (WFF.shift h hs (eqRec B t₂ s₂)) = _
      rw [eqRec_shift h hs A, eqRec_shift h hs B]
      rfl
  | _, _, h, hs, .VTypeBox A, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.shift h.boxIn hs.boxIn (eqRec A t s)) = _
      rw [eqRec_shift h.boxIn hs.boxIn A]
      rfl
  | _, _, h, hs, .VTypeDia A, .dia x _, .diatm _ _ t, .diatm _ _ s => by
      change WFF.imp (WFF.dia _ _ (WFF.imp (WFF.shift (h.diaIn x) (hs.diaIn x)
        (eqRec A t s)) .bot)) .bot = _
      rw [eqRec_shift (h.diaIn x) (hs.diaIn x) A]
      rfl

end V12M
