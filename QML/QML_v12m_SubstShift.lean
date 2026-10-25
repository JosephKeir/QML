import QML.QML_v12m_ShiftSubst
import QML.QML_v12m_SubstTwice

/-!
# QML v12m — substituting into a shifted term

`Term.shift_subst` moves a shift inside a substitution.  This file goes the other way: substituting
into a shifted term is substituting into the term, by the entries the substitution has at the
shifted addresses (`Subst.PreShift`), up to η:

* `Subst.preShift_of`, `preShift_box`, `preShift_dia`: the correspondence at the reachable
  addresses, under `□` and `◇`;
* ⭐`Term.subst_shift`: `subst Ψ (shift t) = subst Ψ' t` when `Ψ (v.shift k) ∼ Ψ' v`.

The growing tree needs it for strong 4's `◇`-lift (`docs/v12-modal-extensions.md` §3 4, D-H1): a
term kept along the edge of a lifted view tuple is the translation of its shift.
-/

namespace V12M

variable [ModalSys]

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- `Ψ` substitutes each address shifted at `k` as `Ψ'` substitutes the address, up to η. -/
def PreShift (k : ℕ) (Γ : Ctx) (Ψ Ψ' : Subst σ Δ) : Prop :=
  ∀ v T, Γ.ref v = some T → SubE.Sim T (Ψ.at (v.shift k)) (Ψ'.at v)

theorem preShift_of {k : ℕ} {Γ : Ctx} {Ψ Ψ' : Subst σ Δ}
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T → SubE.Sim T (Ψ.at (v.shift k)) (Ψ' v)) :
    PreShift k Γ Ψ Ψ' := by
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
            change SubE.Sim T (if s.isProj then (Ψ.at (v.shift k)).proj s else Ψ _)
              (if s.isProj then (Ψ'.at v).proj s else Ψ' _)
            rw [if_pos hs, if_pos hs]
            exact (ih U hU).proj_step hs hv
      · have hlp : (VarSymb.step v s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [at_nonproj Ψ' hlp]
        exact hvis _ _ hlp (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

theorem preShift_box {k : ℕ} {Γ : Ctx} {Ψ Ψ' : Subst σ Δ} (hp : PreShift k Γ Ψ Ψ') :
    PreShift (k + 1) Γ.boxIn Ψ.box Ψ'.box := by
  refine preShift_of ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      have hu := Ctx.boxIn_step_box hv
      rw [VarSymb.shift_level_succ rfl, at_nonproj _ rfl]
      exact (hp u _ hu).unbox
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      rw [VarSymb.shift_level_succ rfl, at_nonproj _ rfl]
      exact (hp u _ hu).keepE' hF hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem preShift_dia {k : ℕ} {Γ : Ctx} {Ψ Ψ' : Subst σ Δ} (hp : PreShift k Γ Ψ Ψ')
    {x ιx : VarSymb} (hw : (Ψ.at (x.shift k)).idxAlong [] = ιx) :
    PreShift (k + 1) (Γ.diaIn x) (Ψ.dia (x.shift k) ιx) (Ψ'.dia x ιx) := by
  refine preShift_of ?_
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
          rw [hx] at hv
          cases U <;> try cases hv
          rw [VarSymb.shift_level_succ rfl, at_nonproj _ rfl]
          change SubE.Sim _ (if u.shift k = u.shift k then (Ψ.at (u.shift k)).diaBody ιx
            else SubE.hide) (if u = u then (Ψ'.at u).diaBody ιx else SubE.hide)
          rw [if_pos rfl, if_pos rfl]
          exact (hp u _ hx).diaBody hw
  | .step u .box =>
      have hu := Ctx.boxIn_step_box (Γ := Γ) hv
      rw [VarSymb.shift_level_succ rfl, at_nonproj _ rfl]
      exact (hp u _ hu).unbox.mono _
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      rw [VarSymb.shift_level_succ rfl, at_nonproj _ rfl]
      exact ((hp u _ hu).keepE' hF hk).mono _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

end Subst

section SubstShift

variable {σ : Signature}

mutual
  theorem Func.subst_shift {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ : Ctx}
      (C : Ctx.Shifts k Γ Γ') (Ψ : Subst σ Δ) (hΨ : Subst.Ok Γ' Ψ) (hc : Subst.Coh ι Γ' Ψ)
      (Ψ' : Subst σ Δ) (hΨ' : Subst.Ok Γ Ψ') (hc' : Subst.Coh ι' Γ Ψ')
      (hp : Subst.PreShift k Γ Ψ Ψ') :
      {n : ℕ} → (f : Func σ Γ n) →
      Func.subst ι Ψ hΨ hc (Func.shift C f) = Func.subst ι' Ψ' hΨ' hc' f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι Ψ hΨ hc (Func.shift C g))
            (Term.subst ι Ψ hΨ hc (Term.shift C t)) =
          Func.eval (Func.subst ι' Ψ' hΨ' hc' g) (Term.subst ι' Ψ' hΨ' hc' t)
        rw [Func.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp g,
          eq_of_heq (Sigma.mk.inj (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp t)).2]
    termination_by structural _ f => f

  /-- ⭐**Substituting into a shifted term** is substituting into the term, by the entries at the
      shifted addresses. -/
  theorem Term.subst_shift {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ : Ctx}
      (C : Ctx.Shifts k Γ Γ') (Ψ : Subst σ Δ) (hΨ : Subst.Ok Γ' Ψ) (hc : Subst.Coh ι Γ' Ψ)
      (Ψ' : Subst σ Δ) (hΨ' : Subst.Ok Γ Ψ') (hc' : Subst.Coh ι' Γ Ψ')
      (hp : Subst.PreShift k Γ Ψ Ψ') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.subst ι Ψ hΨ hc (Term.shift C t)⟩ : Σ b, Term σ Δ T b) =
        ⟨_, Term.subst ι' Ψ' hΨ' hc' t⟩
    | _, _, .var v hv =>
        congrArg (Sigma.mk _) ((hp v _ hv).toVar _ _)
    | _, _, .func f => by
        change (⟨_, Term.func (Func.subst ι Ψ hΨ hc (Func.shift C f))⟩ :
            Σ b, Term σ Δ .Var b) = ⟨_, Term.func (Func.subst ι' Ψ' hΨ' hc' f)⟩
        rw [Func.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp s)
          (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.subst_shift C.boxIn Ψ.box (Subst.ok_box hΨ) (Subst.coh_box hΨ hc)
          Ψ'.box (Subst.ok_box hΨ') (Subst.coh_box hΨ' hc') (Subst.preShift_box hp) t)
    | _, _, .diatm x hx t => by
        have hw : (Ψ.at (x.shift k)).idxAlong [] = ι (x.shift k) :=
          hx.elim fun _ hX => hc _ _ (C x _ hX) []
        have hw' : (Ψ'.at x).idxAlong [] = ι' x := hx.elim fun _ hX => hc' x _ hX []
        have hι : ι (x.shift k) = ι' x :=
          hx.elim fun _ hX => hw.symm.trans (((hp x _ hX).idx).trans hw')
        have key : ∀ (y y' : VarSymb) (_hy : y = y') (hwy : (Ψ.at (x.shift k)).idxAlong [] = y)
            (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ'.diaIn (x.shift k)) (Ψ.dia (x.shift k) y))
            (q : Subst.Coh ι (Γ'.diaIn (x.shift k)) (Ψ.dia (x.shift k) y))
            (P' : ∃ Y, Δ.ref y' = some (.VTypeDia Y))
            (p' : Subst.Ok (Γ.diaIn x) (Ψ'.dia x y')) (q' : Subst.Coh ι' (Γ.diaIn x) (Ψ'.dia x y')),
            (⟨_, Term.diatm y P (Term.subst ι (Ψ.dia (x.shift k) y) p q
                (Term.shift (C.diaIn x) t))⟩ : Σ b, Term σ Δ _ b) =
              ⟨_, Term.diatm y' P' (Term.subst ι' (Ψ'.dia x y') p' q' t)⟩ := by
          intro y y' hy hwy P p q P' p' q'
          subst hy
          exact sig_diatm (Term.subst_shift (C.diaIn x) _ p q _ p' q' (Subst.preShift_dia hp hwy) t)
        exact key _ _ hι hw _ _ _ _ _ _
    termination_by structural _ _ t => t
end

end SubstShift

end V12M
