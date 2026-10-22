import QML.QML_v12m_SubstTwice
import QML.QML_v12m_Eq

/-!
# QML v12m — the Leibniz principle

From `t = s` (at any type, `eqRec`) and `φ[t]` derive `φ[s]`.

Proved for substitutions in general: two substitutions whose entries are equal-or-provably-equal
(`EqE`) send any formula to formulas that prove each other.  The quantifier cases need
eigenvariables, computed from the context's presentation (`Ctx.Presented`), and the substitution
lemmas.
-/

namespace V12M

variable [ModalSys]

/-! ## Substitutions that rename every visible address to itself -/

namespace Subst

variable {σ : Signature} {Δ : Ctx}

theorem at_ren_of {Γ : Ctx} {θ : Subst σ Δ}
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T → θ v = .ren v) :
    ∀ v T, Γ.ref v = some T → θ.at v = .ren v := by
  intro v
  induction v with
  | root r => intro T hv; exact hvis _ _ rfl hv
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [ih U hU]; rfl
      · exact hvis _ _ (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs) hv

theorem ren_box {Γ : Ctx} {θ : Subst σ Δ} (hid : ∀ v T, Γ.ref v = some T → θ.at v = .ren v) :
    ∀ v T, Γ.boxIn.ref v = some T → θ.box.at v = .ren v :=
  at_ren_of fun v T _ hv => by
    match v with
    | .step u .box =>
        obtain ⟨hk, hu⟩ := Ctx.boxIn_box hv
        change (θ.at u).unbox = _
        rw [hid u _ hu]
        change SubE.ren u.inner = _
        rw [VarSymb.inner_box hk]
    | .step u .keep =>
        obtain ⟨_, hu, _⟩ := Ctx.boxIn_keep hv
        change (θ.at u).keepE = _
        rw [hid u _ hu]
        rfl
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .dia => cases hv

theorem ren_dia {Γ : Ctx} {θ : Subst σ Δ} (hid : ∀ v T, Γ.ref v = some T → θ.at v = .ren v)
    (x : VarSymb) : ∀ v T, (Γ.diaIn x).ref v = some T → (θ.dia x x).at v = .ren v :=
  at_ren_of fun v T _ hv => by
    match v with
    | .step u .dia =>
        change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        split_ifs at hv with hux
        · subst hux
          cases hx : Γ.ref u with
          | none => rw [hx] at hv; cases hv
          | some U =>
              change (if u = u then (θ.at u).diaBody u else SubE.hide) = _
              rw [if_pos rfl, hid u U hx]
              rfl
    | .step u .box =>
        obtain ⟨hk, hu⟩ := Ctx.boxIn_box (Γ := Γ) hv
        change ((θ.at u).unbox).mono _ = _
        rw [hid u _ hu]
        change SubE.ren u.inner = _
        rw [VarSymb.inner_box hk]
    | .step u .keep =>
        obtain ⟨_, hu, _⟩ := Ctx.boxIn_keep (Γ := Γ) hv
        change ((θ.at u).keepE).mono _ = _
        rw [hid u _ hu]
        rfl
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv

theorem idx_ren {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hc : Coh ι Γ θ)
    (hid : ∀ v T, Γ.ref v = some T → θ.at v = .ren v) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) : ι x = x := by
  obtain ⟨X, hX⟩ := hx
  have h₁ : (θ.at x).idxAlong [] = ι x := hc x _ hX []
  rw [← h₁, hid x _ hX]
  rfl

end Subst

mutual
  theorem Func.subst_ren {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (hle : Γ.Le Δ)
      (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
      (hid : ∀ v T, Γ.ref v = some T → θ.at v = .ren v) :
      {n : ℕ} → (f : Func σ Γ n) → Func.subst ι θ hθ hc f = Func.mono hle f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι θ hθ hc g) (Term.subst ι θ hθ hc t) =
          Func.eval (Func.mono hle g) (Term.mono hle t)
        rw [Func.subst_ren hle θ hθ hc hid g,
          eq_of_heq (Sigma.mk.inj (Term.subst_ren hle θ hθ hc hid t)).2]
    termination_by structural _ f => f

  /-- ⭐A substitution renaming every visible address to itself acts as weakening. -/
  theorem Term.subst_ren {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (hle : Γ.Le Δ)
      (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ)
      (hid : ∀ v T, Γ.ref v = some T → θ.at v = .ren v) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.subst ι θ hθ hc t⟩ : Σ b, Term σ Δ T b) = ⟨_, Term.mono hle t⟩
    | _, _, .var v hv => congrArg (Sigma.mk _) (SubE.toVar_congr (hid v _ hv) _ (hle.ref hv))
    | _, _, .func f => by
        change (⟨_, Term.func (Func.subst ι θ hθ hc f)⟩ : Σ b, Term σ Δ .Var b) =
          ⟨_, Term.func (Func.mono hle f)⟩
        rw [Func.subst_ren hle θ hθ hc hid f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.subst_ren hle θ hθ hc hid s) (Term.subst_ren hle θ hθ hc hid t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.subst_ren hle.boxIn θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
          (Subst.ren_box hid) t)
    | _, _, .diatm x hx t => by
        have key : ∀ (y : VarSymb) (_hy : x = y) (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ.diaIn x) (θ.dia x y)) (q : Subst.Coh ι (Γ.diaIn x) (θ.dia x y)),
            (⟨_, Term.diatm y P (Term.subst ι (θ.dia x y) p q t)⟩ : Σ b, Term σ Δ _ b) =
              ⟨_, Term.mono hle (Term.diatm x hx t)⟩ := by
          intro y hy P p q
          subst hy
          exact sig_diatm (Term.subst_ren (hle.diaIn x) (θ.dia x x) p q (Subst.ren_dia hid x) t)
        exact key (ι x) (Subst.idx_ren hc hid hx).symm _ _ _
    termination_by structural _ _ t => t
end

/-! ## Sending the slot to a free root -/

def VarSymb.slotToFree (ι : VarSymb → VarSymb) (d u : ℕ) : VarSymb → VarSymb :=
  fun i => if i.rt = .bnd d then i.reroot (.free u) else ι i

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- Under a binder, with the slot sent to the free root `u` instead of a target slot. -/
def toFree (θ : Subst σ Δ) (d u : ℕ) (T : VarType) (h : Δ (.root (.free u)) = none) :
    Subst σ (Δ.insert (.free u) T) := fun v =>
  if v = .root (.bnd d) then .ren (.root (.free u)) else (θ v).mono (Ctx.le_insert h T)

theorem ok_toFree {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {d u : ℕ} (T : VarType)
    (h : Δ (.root (.free u)) = none) : Ok (Γ.insert (.bnd d) T) (θ.toFree d u T h) := by
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [show θ.toFree d u T h (.root (.bnd d)) = .ren (.root (.free u)) from if_pos rfl]
    exact Ctx.ref_insert_root Δ _ T
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show θ.toFree d u T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr]
    exact SubE.okRef_mono _ (hθ v U hlp hv')

theorem coh_toFree {ι : VarSymb → VarSymb} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hc : Coh ι Γ θ) {d u : ℕ} (hΓ : Γ.SlotsFrom d) (T : VarType)
    (h : Δ (.root (.free u)) = none) :
    Coh (VarSymb.slotToFree ι d u) (Γ.insert (.bnd d) T) (θ.toFree d u T h) := by
  refine coh_of (ok_toFree hθ T h) ?_
  intro v U hlp hv p
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    rw [show θ.toFree d u T h (.root (.bnd d)) = .ren (.root (.free u)) from if_pos rfl]
    change (VarSymb.root (.free u)).ext p =
      (if ((VarSymb.root (.bnd d)).ext p).rt = .bnd d then
        ((VarSymb.root (.bnd d)).ext p).reroot (.free u) else ι _)
    have hc0 : (VarSymb.root (Root.bnd d)).rt = Root.bnd d := rfl
    rw [VarSymb.ext_rt, if_pos hc0]
    exact (VarSymb.reroot_ext (.free u) (.root (.bnd d)) p).symm
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ .bnd d := fun he => by
      rw [hΓ v d he le_rfl] at hv'
      cases hv'
    rw [show θ.toFree d u T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      SubE.idxAlong_mono, ← at_nonproj θ hlp, hc v U ((Ctx.ref_nonproj Γ hlp).trans hv') p]
    change ι (v.ext p) = if (v.ext p).rt = .bnd d then _ else ι (v.ext p)
    rw [VarSymb.ext_rt, if_neg hrt]

end Subst

end V12M
