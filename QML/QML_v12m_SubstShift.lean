import QML.QML_v12m_ShiftSubst
import QML.QML_v12m_SubstTwice

/-!
# QML v12m — substituting into a shifted term

`Term.shift_subst` moves a shift inside a substitution.  This file goes the other way: substituting
into a shifted term is substituting into the term, by the entries the substitution has at the
shifted addresses (`Subst.PreShift`), up to η:

* `Subst.preShift_of`, `preShift_box`, `preShift_dia`: the correspondence at the reachable
  addresses, under `□` and `◇`;
* ⭐`Term.subst_shift`: `subst Ψ (shift t) = subst Ψ' t` when `Ψ (v.shift k) ∼ Ψ' v`;
* `preShift_under` and ⭐`WFF.subst_shift`, the same for formulas.  5 on the growing tree needs
  it: `five_box`'s shift meets an edge's translation (docs §3 5, `GCluPre`).

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

namespace Subst

variable {σ : Signature} {Δ : Ctx}

theorem preShift_under {k : ℕ} {Γ : Ctx} {Ψ Ψ' : Subst σ Δ} (hp : PreShift k Γ Ψ Ψ') {d d' : ℕ}
    (hΓ : Γ.SlotsFrom d) (T : VarType) (h : Δ (.root (.bnd d')) = none) :
    PreShift k (Γ.insert (.bnd d) T) (Ψ.under d d' T h) (Ψ'.under d d' T h) := by
  refine preShift_of ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    change SubE.Sim U ((Ψ.under d d' T h).at (.root (.bnd d)))
      ((Ψ'.under d d' T h) (.root (.bnd d)))
    rw [show (Ψ.under d d' T h).at (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl,
      show Ψ'.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ .bnd d := fun he => by
      rw [hΓ v d he le_rfl] at hv'
      cases hv'
    rw [at_under_ne Ψ T h (by rwa [VarSymb.shift_rt]),
      show Ψ'.under d d' T h v = (Ψ' v).mono (Ctx.le_insert h T) from if_neg hvr]
    have h₁ := hp v U ((Ctx.ref_nonproj Γ hlp).trans hv')
    rw [at_nonproj Ψ' hlp] at h₁
    exact h₁.mono _

end Subst

section SubstShiftW

variable {σ : Signature}

theorem Rel.subst_shift {k : ℕ} {ι ι' : VarSymb → VarSymb} {Γ Γ' Δ : Ctx}
    (C : Ctx.Shifts k Γ Γ') (Ψ : Subst σ Δ) (hΨ : Subst.Ok Γ' Ψ) (hc : Subst.Coh ι Γ' Ψ)
    (Ψ' : Subst σ Δ) (hΨ' : Subst.Ok Γ Ψ') (hc' : Subst.Coh ι' Γ Ψ')
    (hp : Subst.PreShift k Γ Ψ Ψ') :
    {n : ℕ} → (ρ : Rel σ Γ n) →
    Rel.subst ι Ψ hΨ hc (Rel.shift C ρ) = Rel.subst ι' Ψ' hΨ' hc' ρ
  | _, .R _ => rfl
  | _, .eval ρ t => by
      change Rel.eval (Rel.subst ι Ψ hΨ hc (Rel.shift C ρ))
          (Term.subst ι Ψ hΨ hc (Term.shift C t)) =
        Rel.eval (Rel.subst ι' Ψ' hΨ' hc' ρ) (Term.subst ι' Ψ' hΨ' hc' t)
      rw [Rel.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp ρ,
        eq_of_heq (Sigma.mk.inj (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp t)).2]

/-- ⭐**Substituting into a shifted formula** is substituting into the formula, by the entries at
    the shifted addresses. -/
theorem WFF.subst_shift : {k : ℕ} → {ι ι' : VarSymb → VarSymb} → {Γ Γ' Δ : Ctx} → {d d' : ℕ} →
    (C : Ctx.Shifts k Γ Γ') → (hΓ : Γ.SlotsFrom d) → (hΓ' : Γ'.SlotsFrom d) →
    (Ψ : Subst σ Δ) → (hΨ : Subst.Ok Γ' Ψ) → (hc : Subst.Coh ι Γ' Ψ) →
    (Ψ' : Subst σ Δ) → (hΨ' : Subst.Ok Γ Ψ') → (hc' : Subst.Coh ι' Γ Ψ') →
    (hΔ : Δ.SlotsFrom d') → Subst.PreShift k Γ Ψ Ψ' → (φ : WFF σ Γ d) →
    WFF.subst ι Ψ hΨ hc hΓ' hΔ (WFF.shift C hΓ φ) = WFF.subst ι' Ψ' hΨ' hc' hΓ hΔ φ
  | _, _, _, _, _, _, _, _, C, _, _, Ψ, hΨ, hc, Ψ', hΨ', hc', _, hp, .atom ρ =>
      congrArg WFF.atom (Rel.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp ρ)
  | _, _, _, _, _, _, _, _, C, _, _, Ψ, hΨ, hc, Ψ', hΨ', hc', _, hp, .eq t s =>
      congrArg₂ WFF.eq (eq_of_heq (Sigma.mk.inj (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp t)).2)
        (eq_of_heq (Sigma.mk.inj (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp s)).2)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .top => rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .bot => rfl
  | _, _, _, _, _, _, _, _, C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .and φ ψ =>
      congrArg₂ WFF.and (WFF.subst_shift C hΓ hΓ' Ψ hΨ hc Ψ' hΨ' hc' hΔ hp φ)
        (WFF.subst_shift C hΓ hΓ' Ψ hΨ hc Ψ' hΨ' hc' hΔ hp ψ)
  | _, _, _, _, _, _, _, _, C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .or φ ψ =>
      congrArg₂ WFF.or (WFF.subst_shift C hΓ hΓ' Ψ hΨ hc Ψ' hΨ' hc' hΔ hp φ)
        (WFF.subst_shift C hΓ hΓ' Ψ hΨ hc Ψ' hΨ' hc' hΔ hp ψ)
  | _, _, _, _, _, _, _, _, C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .imp φ ψ =>
      congrArg₂ WFF.imp (WFF.subst_shift C hΓ hΓ' Ψ hΨ hc Ψ' hΨ' hc' hΔ hp φ)
        (WFF.subst_shift C hΓ hΓ' Ψ hΨ hc Ψ' hΨ' hc' hΔ hp ψ)
  | _, _, _, _, _, _, d, d', C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .all T φ =>
      congrArg (WFF.all T) (WFF.subst_shift (C.insert (hΓ.rootFresh le_rfl) T) (hΓ.insert T)
        (hΓ'.insert T) (Ψ.under d d' T hΔ.root) (Subst.ok_under hΨ T hΔ.root)
        (Subst.coh_under hΨ hc hΓ' T hΔ.root) (Ψ'.under d d' T hΔ.root)
        (Subst.ok_under hΨ' T hΔ.root) (Subst.coh_under hΨ' hc' hΓ T hΔ.root) (hΔ.insert T)
        (Subst.preShift_under hp hΓ T hΔ.root) φ)
  | _, _, _, _, _, _, d, d', C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .ex T φ =>
      congrArg (WFF.ex T) (WFF.subst_shift (C.insert (hΓ.rootFresh le_rfl) T) (hΓ.insert T)
        (hΓ'.insert T) (Ψ.under d d' T hΔ.root) (Subst.ok_under hΨ T hΔ.root)
        (Subst.coh_under hΨ hc hΓ' T hΔ.root) (Ψ'.under d d' T hΔ.root)
        (Subst.ok_under hΨ' T hΔ.root) (Subst.coh_under hΨ' hc' hΓ T hΔ.root) (hΔ.insert T)
        (Subst.preShift_under hp hΓ T hΔ.root) φ)
  | _, _, _, _, _, _, _, _, C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .box φ =>
      congrArg WFF.box (WFF.subst_shift C.boxIn hΓ.boxIn hΓ'.boxIn Ψ.box (Subst.ok_box hΨ)
        (Subst.coh_box hΨ hc) Ψ'.box (Subst.ok_box hΨ') (Subst.coh_box hΨ' hc') hΔ.boxIn
        (Subst.preShift_box hp) φ)
  | k, ι, ι', Γ, Γ', Δ, _, d', C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .dia x hx φ => by
      have hw : (Ψ.at (x.shift k)).idxAlong [] = ι (x.shift k) :=
        hx.elim fun _ hX => hc _ _ (C x _ hX) []
      have hw' : (Ψ'.at x).idxAlong [] = ι' x := hx.elim fun _ hX => hc' x _ hX []
      have hι : ι (x.shift k) = ι' x :=
        hx.elim fun _ hX => hw.symm.trans (((hp x _ hX).idx).trans hw')
      have key : ∀ (y y' : VarSymb) (_hy : y = y') (hwy : (Ψ.at (x.shift k)).idxAlong [] = y)
          (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
          (p : Subst.Ok (Γ'.diaIn (x.shift k)) (Ψ.dia (x.shift k) y))
          (q : Subst.Coh ι (Γ'.diaIn (x.shift k)) (Ψ.dia (x.shift k) y))
          (hΔy : (Δ.diaIn y).SlotsFrom d')
          (P' : ∃ Y, Δ.ref y' = some (.VTypeDia Y))
          (p' : Subst.Ok (Γ.diaIn x) (Ψ'.dia x y')) (q' : Subst.Coh ι' (Γ.diaIn x) (Ψ'.dia x y'))
          (hΔy' : (Δ.diaIn y').SlotsFrom d'),
          (WFF.dia y P (WFF.subst ι (Ψ.dia (x.shift k) y) p q (hΓ'.diaIn (x.shift k)) hΔy
              (WFF.shift (C.diaIn x) (hΓ.diaIn x) φ)) : WFF σ Δ d') =
            WFF.dia y' P' (WFF.subst ι' (Ψ'.dia x y') p' q' (hΓ.diaIn x) hΔy' φ) := by
        intro y y' hy hwy P p q hΔy P' p' q' hΔy'
        subst hy
        exact congrArg (WFF.dia y _) (WFF.subst_shift (C.diaIn x) (hΓ.diaIn x)
          (hΓ'.diaIn (x.shift k)) _ p q _ p' q' hΔy (Subst.preShift_dia hp hwy) φ)
      exact key _ _ hι hw _ _ _ _ _ _ _ _
  | _, _, _, _, _, _, _, _, C, _, _, Ψ, hΨ, hc, Ψ', hΨ', hc', _, hp, .here hT s t =>
      WFF.here_congr hT (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp s)
        (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp t)
  | _, _, _, _, _, _, _, _, C, _, _, Ψ, hΨ, hc, Ψ', hΨ', hc', _, hp, .back hB L s t =>
      WFF.back_congr hB L (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp s)
        (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp t)
  | _, _, _, _, _, _, d, d', C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp, .retS hB S t Φ =>
      WFF.retS_congr hB S (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp t)
        (WFF.subst_shift (C.boxIn.insert (hΓ.boxIn.rootFresh le_rfl) _) (hΓ.boxIn.insert _)
          (hΓ'.boxIn.insert _) (Ψ.box.under d d' _ hΔ.boxIn.root)
          (Subst.ok_under (Subst.ok_box hΨ) _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hΨ) (Subst.coh_box hΨ hc) hΓ'.boxIn _ hΔ.boxIn.root)
          (Ψ'.box.under d d' _ hΔ.boxIn.root) (Subst.ok_under (Subst.ok_box hΨ') _ hΔ.boxIn.root)
          (Subst.coh_under (Subst.ok_box hΨ') (Subst.coh_box hΨ' hc') hΓ.boxIn _ hΔ.boxIn.root)
          (hΔ.boxIn.insert _) (Subst.preShift_under (Subst.preShift_box hp) hΓ.boxIn _
            hΔ.boxIn.root) Φ)
  | k, ι, ι', Γ, Γ', Δ, d, d', C, hΓ, hΓ', Ψ, hΨ, hc, Ψ', hΨ', hc', hΔ, hp,
      .retxS hB y hy S t Φ => by
      have hw : (Ψ.at (y.shift k)).idxAlong [] = ι (y.shift k) :=
        hy.elim fun _ hY => hc _ _ (C y _ hY) []
      have hw' : (Ψ'.at y).idxAlong [] = ι' y := hy.elim fun _ hY => hc' y _ hY []
      have hι : ι (y.shift k) = ι' y :=
        hy.elim fun _ hY => hw.symm.trans (((hp y _ hY).idx).trans hw')
      have key : ∀ (z z' : VarSymb) (_hz : z = z') (hwz : (Ψ.at (y.shift k)).idxAlong [] = z)
          (P : ∃ Y, Δ.ref z = some (.VTypeDia Y)) (hΔz : (Δ.diaIn z).SlotsFrom d')
          (p : Subst.Ok ((Γ'.diaIn (y.shift k)).insert (.bnd d) S.ty)
            ((Ψ.dia (y.shift k) z).under d d' _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot ι d d') ((Γ'.diaIn (y.shift k)).insert (.bnd d) S.ty)
            ((Ψ.dia (y.shift k) z).under d d' _ hΔz.root))
          (P' : ∃ Y, Δ.ref z' = some (.VTypeDia Y)) (hΔz' : (Δ.diaIn z').SlotsFrom d')
          (p' : Subst.Ok ((Γ.diaIn y).insert (.bnd d) S.ty)
            ((Ψ'.dia y z').under d d' _ hΔz'.root))
          (q' : Subst.Coh (VarSymb.shiftSlot ι' d d') ((Γ.diaIn y).insert (.bnd d) S.ty)
            ((Ψ'.dia y z').under d d' _ hΔz'.root)),
          (WFF.retxS hB z P S (Term.subst ι Ψ hΨ hc (Term.shift C t))
              (WFF.subst (VarSymb.shiftSlot ι d d') ((Ψ.dia (y.shift k) z).under d d' _ hΔz.root)
                p q ((hΓ'.diaIn (y.shift k)).insert _) (hΔz.insert _)
                (WFF.shift ((C.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl) _)
                  ((hΓ.diaIn y).insert _) Φ)) : WFF σ Δ d') =
            WFF.retxS hB z' P' S (Term.subst ι' Ψ' hΨ' hc' t)
              (WFF.subst (VarSymb.shiftSlot ι' d d') ((Ψ'.dia y z').under d d' _ hΔz'.root)
                p' q' ((hΓ.diaIn y).insert _) (hΔz'.insert _) Φ) := by
        intro z z' hz hwz P hΔz p q P' hΔz' p' q'
        subst hz
        exact WFF.retxS_congr hB _ _ S (Term.subst_shift C Ψ hΨ hc Ψ' hΨ' hc' hp t)
          (WFF.subst_shift ((C.diaIn y).insert ((hΓ.diaIn y).rootFresh le_rfl) _)
            ((hΓ.diaIn y).insert _) ((hΓ'.diaIn (y.shift k)).insert _) _ p q _ p' q'
            (hΔz.insert _) (Subst.preShift_under (Subst.preShift_dia hp hwz) (hΓ.diaIn y) _
              hΔz.root) Φ)
      exact key _ _ hι hw _ (hΔ.diaIn _) _ _ _ (hΔ.diaIn _) _ _

end SubstShiftW

end V12M
