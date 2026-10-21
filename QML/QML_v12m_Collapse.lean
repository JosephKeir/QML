import QML.QML_v12m_WFF

/-!
# QML v12m — collapsing a level (weak T)

Under T a necessary object can be read at the current world.  Syntactically this moves a term or
formula written in a `□` view down to the current level: every address that descends through the
collapsed `box` reads `here` instead, and one that keeps an object through it (`keep`, under 4)
reads the object itself.  Inside the moved syntax there are further views, so the collapsed step
is the level step with exactly `k` level steps after it, `k` being the number of views entered
since (`VarSymb.collapse k`).

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

theorem collapse_level_zero {v : VarSymb} {s : Step} (hs : s.isProj = false) (hk : s ≠ .keep) :
    (step v s).collapse 0 = step v .here := by
  simp only [collapse, hs, Bool.false_eq_true, if_false, if_neg hk]

theorem collapse_keep_zero {v : VarSymb} : (step v .keep).collapse 0 = v := rfl

theorem collapse_level_succ {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = false) :
    (step v s).collapse (k + 1) = step (v.collapse k) s := by
  simp only [collapse, hs, Bool.false_eq_true, if_false]

theorem shift_proj {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = true) :
    (step v s).shift k = step (v.shift k) s := by
  simp only [shift, if_pos hs]

theorem shift_level_zero {v : VarSymb} {s : Step} (hs : s.isProj = false) :
    (step v s).shift 0 = step (step v .keep) s := by
  simp only [shift, hs, Bool.false_eq_true, if_false]

theorem shift_level_succ {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = false) :
    (step v s).shift (k + 1) = step (v.shift k) s := by
  simp only [shift, hs, Bool.false_eq_true, if_false]

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
            by_cases hk : s = .keep
            · subst hk
              simp only [Nat.add_zero, collapse_level_succ (s := Step.keep) rfl, collapse_keep_zero]
            · simp only [Nat.add_zero, collapse_level_succ hs', collapse_level_zero hs' hk,
                collapse_proj (s := Step.here) rfl]
        | succ m =>
            rw [show k + 1 + (m + 1) = (k + 1 + m) + 1 by omega,
              show k + (m + 1) = (k + m) + 1 by omega]
            simp only [collapse_level_succ hs']
            rw [collapse_collapse v k m]

/-- A collapse outside a shift commutes with it (the collapse moves out by one). -/
theorem collapse_shift : ∀ (v : VarSymb) (k m : ℕ),
    (v.collapse (k + 1 + m)).shift m = (v.shift m).collapse (k + 2 + m)
  | root _, _, _ => rfl
  | step v s, k, m => by
      by_cases hs : s.isProj = true
      · rw [collapse_proj hs, shift_proj hs, shift_proj hs, collapse_proj hs, collapse_shift v k m]
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases m with
        | zero =>
            simp only [Nat.add_zero, collapse_level_succ hs', shift_level_zero hs',
              collapse_level_succ (s := Step.keep) rfl]
        | succ m =>
            rw [show k + 1 + (m + 1) = (k + 1 + m) + 1 by omega,
              show k + 2 + (m + 1) = (k + 2 + m) + 1 by omega]
            simp only [collapse_level_succ hs', shift_level_succ hs']
            rw [collapse_shift v k m]

end VarSymb

theorem Step.levels_cons (s : Step) (p : List Step) :
    Step.levels (s :: p) = (if s.isProj then 0 else 1) + Step.levels p := rfl

/-- A collapse outside a shift commutes with it, on annotations. -/
theorem Ann.collapse_shift : ∀ {T : VarType} (a : Ann T) (k m : ℕ),
    (a.collapse (k + 1 + m)).shift m = (a.shift m).collapse (k + 2 + m)
  | _, .var, _, _ => rfl
  | _, .one, _, _ => rfl
  | _, .prod a b, k, m => by
      change Ann.prod _ _ = Ann.prod _ _
      rw [Ann.collapse_shift a k m, Ann.collapse_shift b k m]
  | _, .box a, k, m => by
      change Ann.box ((a.collapse (k + 1 + m + 1)).shift (m + 1)) =
        Ann.box ((a.shift (m + 1)).collapse (k + 2 + m + 1))
      rw [show k + 1 + m + 1 = k + 1 + (m + 1) by omega,
        show k + 2 + m + 1 = k + 2 + (m + 1) by omega, Ann.collapse_shift a k (m + 1)]
  | _, .dia i a, k, m => by
      change Ann.dia ((i.collapse (k + 1 + m)).shift m)
          ((a.collapse (k + 1 + m + 1)).shift (m + 1)) =
        Ann.dia ((i.shift m).collapse (k + 2 + m)) ((a.shift (m + 1)).collapse (k + 2 + m + 1))
      rw [show k + 1 + m + 1 = k + 1 + (m + 1) by omega,
        show k + 2 + m + 1 = k + 2 + (m + 1) by omega, Ann.collapse_shift a k (m + 1),
        VarSymb.collapse_shift i k m]

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
  | _, .prod _ _, _, .keep :: _ => rfl
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
  | _, .box a, k, .keep :: p => by
      change (Ann.box ((a.collapse (k + 1)).shift 0)).idxAt p =
        ((Ann.box (a.shift 0)).idxAt p).collapse (k + (1 + Step.levels p))
      rw [← Nat.add_assoc, ← Ann.idxAt_collapse (Ann.box (a.shift 0)) (k + 1) p]
      change (Ann.box ((a.collapse (k + 1 + 0)).shift 0)).idxAt p =
        (Ann.box ((a.shift 0).collapse (k + 2 + 0))).idxAt p
      rw [Ann.collapse_shift a k 0]
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
  | _, .dia _ _, _, .keep :: _ => rfl

variable [ModalSys]

/-- Collapsing a level further out keeps a contents address a contents address. -/
theorem VarSymb.inner_collapse_succ (u : VarSymb) (k : ℕ) :
    u.inner.collapse (k + 1) = (u.collapse k).inner := by
  unfold VarSymb.inner
  split_ifs
  · rw [VarSymb.collapse_proj (s := .here) rfl, VarSymb.collapse_level_succ (s := .keep) rfl]
  · rw [VarSymb.collapse_level_succ (s := .box) rfl]

/-- Collapsing the view of a contents address reads the object here. -/
theorem VarSymb.inner_collapse_zero (u : VarSymb) : u.inner.collapse 0 = .step u .here := by
  unfold VarSymb.inner
  split_ifs
  · rw [VarSymb.collapse_proj (s := .here) rfl, VarSymb.collapse_keep_zero]
  · exact VarSymb.collapse_level_zero rfl (by decide)

/-! ## Collapsing contexts -/

namespace Ctx

theorem boxIn_step_box {Γ : Ctx} {u : VarSymb} {T : VarType}
    (h : Γ.boxIn (.step u .box) = some T) : Γ.ref u = some (.VTypeBox T) :=
  (boxIn_box h).2

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
      rw [VarSymb.collapse_level_zero rfl (by decide), Ctx.ref_step_proj _ _ rfl,
        boxIn_step_box hv]
      simp only [Option.bind_some, VarType.step, hT, if_true]
  | .step u .keep =>
      rw [VarSymb.collapse_keep_zero]
      exact (boxIn_keep hv).2.1
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
      obtain ⟨hk, hu⟩ := boxIn_box hv
      rw [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_box_of hk (h u _ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := boxIn_keep hv
      rw [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_keep_of hF (h u _ hu)
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
      obtain ⟨hk, hu⟩ := boxIn_box (Γ := Γ₁) hv
      rw [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_box_of (Γ := Γ₂) hk (h u _ hu)
  | .step u .keep =>
      obtain ⟨hF, hu, A, rfl⟩ := boxIn_keep (Γ := Γ₁) hv
      rw [VarSymb.collapse_level_succ rfl, Ctx.ref_nonproj _ rfl]
      exact boxIn_keep_of hF (h u _ hu)
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
  | _, _, _, _, h, _, .here hT s t => .here hT (Term.collapse h s) (Term.collapse h t)
  | _, _, _, _, h, _, .back hB L s t => .back hB L (Term.collapse h s) (Term.collapse h t)
  | _, _, _, _, h, hs, .retSH hB S Zs hZs ws t cs Φ =>
      .retSH hB S Zs hZs (ws.map fun p => ⟨_, Term.collapse h.boxIn p⟩) (Term.collapse h t)
        (cs.map fun p => ⟨_, Term.collapse h p⟩)
        (WFF.collapse (h.boxIn.insert (hs.boxIn.rootFresh le_rfl) _) (hs.boxIn.insert _) Φ)
  | k, _, _, _, h, hs, .retxSH hB y hy S Zs hZs ws t cs Φ =>
      .retxSH hB (y.collapse k) (hy.imp fun _ hY => h y _ hY) S Zs hZs
        (ws.map fun p => ⟨_, Term.collapse (h.diaIn y) p⟩) (Term.collapse h t)
        (cs.map fun p => ⟨_, Term.collapse h p⟩)
        (WFF.collapse ((h.diaIn y).insert ((hs.diaIn y).rootFresh le_rfl) _)
          ((hs.diaIn y).insert _) Φ)


/-- ⭐Collapsing commutes with equality at every type — `eqRec` is structural, so each clause is the
    corresponding clause of `WFF.collapse`.  Needed where a `□`-equation is read at the world itself
    (`Proof.T_box`), which is the self branch of a necessary term's denotation. -/
theorem eqRec_collapse {σ : Signature} {k : ℕ} {d : ℕ} : {Γ₁ Γ₂ : Ctx} →
    (h : Ctx.Collapses k Γ₁ Γ₂) → (hs : Γ₁.SlotsFrom d) → (T : VarType) → {a : Ann T} →
    (t s : Term σ Γ₁ T a) →
    WFF.collapse h hs (eqRec T t s : WFF σ Γ₁ d) =
      eqRec T (Term.collapse h t) (Term.collapse h s)
  | _, _, h, hs, .Var, .var, t, s =>
      (congrArg (WFF.collapse h hs) (eqRec_Var t s)).trans (eqRec_Var _ _).symm
  | _, _, _, _, .VTypeOne, .one, .unit, .unit => rfl
  | _, _, h, hs, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change WFF.and (WFF.collapse h hs (eqRec A t₁ s₁)) (WFF.collapse h hs (eqRec B t₂ s₂)) = _
      rw [eqRec_collapse h hs A, eqRec_collapse h hs B]
      rfl
  | _, _, h, hs, .VTypeBox A, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.collapse h.boxIn hs.boxIn (eqRec A t s)) = _
      rw [eqRec_collapse h.boxIn hs.boxIn A]
      rfl
  | _, _, h, hs, .VTypeDia A, .dia x _, .diatm _ _ t, .diatm _ _ s => by
      change WFF.imp (WFF.dia _ _ (WFF.imp (WFF.collapse (h.diaIn x) (hs.diaIn x)
        (eqRec A t s)) .bot)) .bot = _
      rw [eqRec_collapse (h.diaIn x) (hs.diaIn x) A]
      rfl

end V12M
