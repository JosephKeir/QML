import QML.QML_v12m_WFF

/-!
# QML v12m — collapsing a level (weak T)

Under T a necessary object can be read at the current world.  Syntactically this moves a term or
formula written in a `□` view down to the current level: every address that descends through the
collapsed `box` reads `here` instead.  Inside the moved syntax there are further views, so the
collapsed step is the level step with exactly `k` level steps after it, `k` being the number of
views entered since (`VarSymb.collapse k`).

* `Ctx.Collapses k Γ₁ Γ₂`: everything `Γ₁` reaches, `Γ₂` reaches after collapsing.  It holds for
  `Γ.boxIn` and `Γ` under T (`Ctx.collapses_boxIn_self`) and passes into views and binders.
* `Term.collapse`, `WFF.collapse`: the syntactic operations.  Annotations collapse with the level
  they sit at (`Ann.collapse`), consistently with `Ann.idxAt` (`Ann.idxAt_collapse`).
-/

namespace V12M

/-! ## Collapsing addresses -/

namespace VarSymb

theorem collapse_proj {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = true) :
    (step v s).collapse k = step (v.collapse k) s := by
  simp only [collapse, if_pos hs]

theorem collapse_level_zero {v : VarSymb} {s : Step} (hs : s.isProj = false) :
    (step v s).collapse 0 = step v .here := by
  simp only [collapse, hs, Bool.false_eq_true, if_false]

theorem collapse_level_succ {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = false) :
    (step v s).collapse (k + 1) = step (v.collapse k) s := by
  simp only [collapse, hs, Bool.false_eq_true, if_false]

/-- Collapses at two levels commute (the outer one shifts by one). -/
theorem collapse_collapse : ∀ (v : VarSymb) (k m : ℕ),
    (v.collapse (k + 1 + m)).collapse m = (v.collapse m).collapse (k + m)
  | root _, _, _ => rfl
  | step v s, k, m => by
      by_cases hs : s.isProj = true
      · rw [collapse_proj hs, collapse_proj hs, collapse_proj hs, collapse_proj hs,
          collapse_collapse v k m]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases m with
        | zero =>
            simp only [Nat.add_zero, collapse_level_succ hs', collapse_level_zero hs',
              collapse_proj (s := Step.here) rfl]
        | succ m =>
            rw [show k + 1 + (m + 1) = (k + 1 + m) + 1 by omega,
              show k + (m + 1) = (k + m) + 1 by omega]
            simp only [collapse_level_succ hs']
            rw [collapse_collapse v k m]

end VarSymb

theorem Step.levels_cons (s : Step) (p : List Step) :
    Step.levels (s :: p) = (if s.isProj then 0 else 1) + Step.levels p := rfl

/-- The index a path reaches in a collapsed annotation. -/
theorem Ann.idxAt_collapse : ∀ {T : VarType} (a : Ann T) (k : ℕ) (p : List Step),
    (a.collapse k).idxAt p = (a.idxAt p).collapse (k + Step.levels p)
  | _, .var, _, [] => rfl
  | _, .var, _, _ :: _ => rfl
  | _, .one, _, [] => rfl
  | _, .one, _, _ :: _ => rfl
  | _, .prod _ _, _, [] => rfl
  | _, .prod a _, k, .fst :: p => by
      change (a.collapse k).idxAt p = (a.idxAt p).collapse (k + (0 + Step.levels p))
      rw [Ann.idxAt_collapse a k p, Nat.zero_add]
  | _, .prod _ b, k, .snd :: p => by
      change (b.collapse k).idxAt p = (b.idxAt p).collapse (k + (0 + Step.levels p))
      rw [Ann.idxAt_collapse b k p, Nat.zero_add]
  | _, .prod _ _, _, .box :: _ => rfl
  | _, .prod _ _, _, .dia :: _ => rfl
  | _, .prod _ _, _, .here :: _ => rfl
  | _, .box _, _, [] => rfl
  | _, .box a, k, .box :: p => by
      change (a.collapse (k + 1)).idxAt p = _
      rw [Ann.idxAt_collapse a (k + 1) p]
      change _ = (a.idxAt p).collapse (k + (1 + Step.levels p))
      rw [Nat.add_assoc]
  | _, .box a, k, .here :: p => by
      change ((a.collapse (k + 1)).idxAt p).collapse (Step.levels p) =
        ((a.idxAt p).collapse (Step.levels p)).collapse (k + (0 + Step.levels p))
      rw [Ann.idxAt_collapse a (k + 1) p, Nat.zero_add, VarSymb.collapse_collapse]
  | _, .box _, _, .fst :: _ => rfl
  | _, .box _, _, .snd :: _ => rfl
  | _, .box _, _, .dia :: _ => rfl
  | _, .dia _ _, _, [] => rfl
  | _, .dia _ a, k, .dia :: p => by
      change (a.collapse (k + 1)).idxAt p = _
      rw [Ann.idxAt_collapse a (k + 1) p]
      change _ = (a.idxAt p).collapse (k + (1 + Step.levels p))
      rw [Nat.add_assoc]
  | _, .dia _ _, _, .fst :: _ => rfl
  | _, .dia _ _, _, .snd :: _ => rfl
  | _, .dia _ _, _, .box :: _ => rfl
  | _, .dia _ _, _, .here :: _ => rfl

variable [ModalSys]

/-! ## Collapsing contexts -/

namespace Ctx

theorem boxIn_step_box {Γ : Ctx} {u : VarSymb} {T : VarType}
    (h : Γ.boxIn (.step u .box) = some T) : Γ.ref u = some (.VTypeBox T) := by
  change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at h
  cases hu : Γ.ref u with
  | none => rw [hu] at h; cases h
  | some U =>
      rw [hu] at h
      cases U <;> first | (cases h; done) | (cases h; rfl)

theorem ref_insert_ne {Γ : Ctx} {r : Root} (T : VarType) :
    ∀ {v : VarSymb}, v.rt ≠ r → (Γ.insert r T).ref v = Γ.ref v
  | .root r', h => by
      change (if VarSymb.root r' = .root r then some T else Γ (.root r')) = Γ (.root r')
      rw [if_neg (fun he => h (by cases he; rfl))]
  | .step v s, h => by
      simp only [Ctx.ref]
      split_ifs
      · rw [ref_insert_ne T (v := v) h]
      · change (if VarSymb.step v s = .root r then some T else Γ (.step v s)) = _
        rw [if_neg (fun he => by cases he)]

/-- `Γ₂` reaches everything `Γ₁` reaches, with the level `k` below collapsed. -/
def Collapses (k : ℕ) (Γ₁ Γ₂ : Ctx) : Prop :=
  ∀ v T, Γ₁.ref v = some T → Γ₂.ref (v.collapse k) = some T

/-- It suffices to check the visible non-projection addresses. -/
theorem Collapses.of_raw {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : ∀ v T, v.lastProj = false → Γ₁ v = some T → Γ₂.ref (v.collapse k) = some T) :
    Collapses k Γ₁ Γ₂ := by
  intro v
  induction v with
  | root r => intro T hv; exact h _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        rw [VarSymb.collapse_proj hs, Ctx.ref_step_proj _ _ hs]
        cases hU : Γ₁.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [hU] at hv; rw [ih U hU]; exact hv
      · exact h _ _ (show s.isProj = false from Bool.eq_false_iff.mpr hs)
          (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

/-- ⭐Under T the `□` view collapses onto the current level. -/
theorem collapses_boxIn_self (hT : ModalSys.T = true) (Γ : Ctx) : Collapses 0 Γ.boxIn Γ := by
  refine Collapses.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      rw [VarSymb.collapse_level_zero rfl, Ctx.ref_step_proj _ _ rfl, boxIn_step_box hv]
      simp only [Option.bind_some, VarType.step, hT, if_true]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem Collapses.boxIn {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Collapses k Γ₁ Γ₂) :
    Collapses (k + 1) Γ₁.boxIn Γ₂.boxIn := by
  refine Collapses.of_raw ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      rw [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl]
      change (match Γ₂.ref (u.collapse k) with | some (.VTypeBox A) => some A | _ => none) =
        some T
      rw [h u _ (boxIn_step_box hv)]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem Collapses.diaIn {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Collapses k Γ₁ Γ₂) (x : VarSymb) :
    Collapses (k + 1) (Γ₁.diaIn x) (Γ₂.diaIn (x.collapse k)) := by
  refine Collapses.of_raw ?_
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
          rw [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl]
          change (if u.collapse k = u.collapse k then
            (match Γ₂.ref (u.collapse k) with | some (.VTypeDia X) => some X | _ => none)
            else none) = some T
          rw [if_pos rfl, h u _ hx]
          exact hv
  | .step u .box =>
      rw [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl]
      change (match Γ₂.ref (u.collapse k) with | some (.VTypeBox A) => some A | _ => none) =
        some T
      rw [h u _ (boxIn_step_box hv)]
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

theorem Collapses.insert {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Collapses k Γ₁ Γ₂) {r : Root}
    (hr : Γ₁.RootFresh r) (T : VarType) : Collapses k (Γ₁.insert r T) (Γ₂.insert r T) := by
  refine Collapses.of_raw ?_
  intro v U hlp hv
  by_cases hvr : v = .root r
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    exact ref_insert_root Γ₂ r T
  · have hv' : Γ₁ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ r := fun he => by rw [hr v he] at hv'; cases hv'
    rw [ref_insert_ne T (by rwa [VarSymb.collapse_rt])]
    exact h v U ((Ctx.ref_nonproj Γ₁ hlp).trans hv')

end Ctx

/-! ## Collapsing terms and formulas -/

mutual
  def Func.collapse {σ : Signature} {k : ℕ} : {Γ₁ Γ₂ : Ctx} → Ctx.Collapses k Γ₁ Γ₂ →
      {n : ℕ} → Func σ Γ₁ n → Func σ Γ₂ n
    | _, _, _, _, .F f => .F f
    | _, _, h, _, .eval g t => .eval (Func.collapse h g) (Term.collapse h t)

  /-- ⭐Moving a term down a collapsed level. -/
  def Term.collapse {σ : Signature} {k : ℕ} : {Γ₁ Γ₂ : Ctx} → Ctx.Collapses k Γ₁ Γ₂ →
      {T : VarType} → {a : Ann T} → Term σ Γ₁ T a → Term σ Γ₂ T (a.collapse k)
    | _, _, h, _, _, .var v hv => .var (v.collapse k) (h v _ hv)
    | _, _, h, _, _, .func f => .func (Func.collapse h f)
    | _, _, _, _, _, .unit => .unit
    | _, _, h, _, _, .pair s t => .pair (Term.collapse h s) (Term.collapse h t)
    | _, _, h, _, _, .boxtm t => .boxtm (Term.collapse h.boxIn t)
    | _, _, h, _, _, .diatm x hx t =>
        .diatm (x.collapse k) (hx.imp fun _ hX => h x _ hX) (Term.collapse (h.diaIn x) t)
end

def Rel.collapse {σ : Signature} {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : Ctx.Collapses k Γ₁ Γ₂) :
    {n : ℕ} → Rel σ Γ₁ n → Rel σ Γ₂ n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.collapse h ρ) (Term.collapse h t)

/-- ⭐Moving a formula down a collapsed level. -/
def WFF.collapse {σ : Signature} : {k : ℕ} → {Γ₁ Γ₂ : Ctx} → {d : ℕ} →
    Ctx.Collapses k Γ₁ Γ₂ → Γ₁.SlotsFrom d → WFF σ Γ₁ d → WFF σ Γ₂ d
  | _, _, _, _, h, _, .atom ρ => .atom (Rel.collapse h ρ)
  | _, _, _, _, h, _, .eq t s => .eq (Term.collapse h t) (Term.collapse h s)
  | _, _, _, _, _, _, .top => .top
  | _, _, _, _, _, _, .bot => .bot
  | _, _, _, _, h, hs, .and φ ψ => .and (WFF.collapse h hs φ) (WFF.collapse h hs ψ)
  | _, _, _, _, h, hs, .or φ ψ => .or (WFF.collapse h hs φ) (WFF.collapse h hs ψ)
  | _, _, _, _, h, hs, .imp φ ψ => .imp (WFF.collapse h hs φ) (WFF.collapse h hs ψ)
  | _, _, _, _, h, hs, .all T φ =>
      .all T (WFF.collapse (h.insert (hs.rootFresh le_rfl) T) (hs.insert T) φ)
  | _, _, _, _, h, hs, .ex T φ =>
      .ex T (WFF.collapse (h.insert (hs.rootFresh le_rfl) T) (hs.insert T) φ)
  | _, _, _, _, h, hs, .box φ => .box (WFF.collapse h.boxIn hs.boxIn φ)
  | k, _, _, _, h, hs, .dia x hx φ =>
      .dia (x.collapse k) (hx.imp fun _ hX => h x _ hX) (WFF.collapse (h.diaIn x) (hs.diaIn x) φ)

end V12M
