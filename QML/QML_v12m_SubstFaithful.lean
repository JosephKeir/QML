import QML.QML_v12m_SubstCongr
import QML.QML_v12m_SubstId

/-!
# QML v12m — substitution reads only η-faithful addresses

Only base-typed addresses are terms, and a possible term names its witness; so a substitution is
read only at addresses whose type has a base or a possible part (`VarType.etaInj`).  Two
substitutions agreeing there, up to η, substitute every term alike (⭐`Term.subst_congrF`).

At the other types (built from `𝟙`, `×` and `□`) η-expansion is not injective, and names need
not be unique (`docs/v12-modal-extensions.md` §3 5); this is why that does not matter for terms.

* `VarType.etaInj`, `VarType.etaInj_of_step`;
* `Subst.SimF`, `simF_of`, `simF_box`, `simF_dia`, `Subst.idx_eqF`;
* ⭐`Func.subst_congrF`, ⭐`Term.subst_congrF`, `Term.subst_congrF_var`.
-/

namespace V12M

/-- The types at which η-expansion is injective: those with a base or a possible part. -/
def VarType.etaInj : VarType → Bool
  | .Var => true
  | .VTypeOne => false
  | .VTypeProd A B => A.etaInj || B.etaInj
  | .VTypeBox A => A.etaInj
  | .VTypeDia _ => true

variable [ModalSys]

/-- A step out of a type without a base or a possible part leads to another such type. -/
theorem VarType.etaInj_of_step {U T : VarType} {s : Step} (h : U.step s = some T)
    (hT : T.etaInj = true) : U.etaInj = true := by
  cases U with
  | Var => cases s <;> cases h
  | VTypeOne => cases s <;> cases h
  | VTypeProd A B =>
      cases s with
      | fst => cases h; simp [VarType.etaInj, hT]
      | snd => cases h; simp [VarType.etaInj, hT]
      | _ => cases h
  | VTypeBox A =>
      cases s with
      | box => cases h; exact hT
      | here => obtain ⟨-, rfl⟩ := VarType.step_here h; exact hT
      | _ => cases h
  | VTypeDia _ => rfl

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- Two substitutions agree up to η at every reachable η-faithful address of `Γ`. -/
def SimF (Γ : Ctx) (θ θ' : Subst σ Δ) : Prop :=
  ∀ v T, Γ.ref v = some T → T.etaInj = true → SubE.Sim T (θ.at v) (θ'.at v)

theorem simF_of {Γ : Ctx} {θ θ' : Subst σ Δ}
    (hvis : ∀ v T, v.lastProj = false → Γ v = some T → T.etaInj = true →
      SubE.Sim T (θ v) (θ' v)) :
    SimF Γ θ θ' := by
  intro v
  induction v with
  | root r => intro T hv hT; exact hvis _ _ rfl hv hT
  | step v s ih =>
      intro T hv hT
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            exact (ih U hU (VarType.etaInj_of_step hv hT)).proj_step hs hv
      · exact hvis _ _ (show (VarSymb.step v s).lastProj = false from Bool.eq_false_iff.mpr hs)
          hv hT

theorem simF_box {Γ : Ctx} {θ θ' : Subst σ Δ} (hs : SimF Γ θ θ') :
    SimF Γ.boxIn θ.box θ'.box := by
  refine simF_of ?_
  intro v T _ hv hT
  match v with
  | .step u .box => exact (hs u _ (Ctx.boxIn_step_box hv) hT).unbox
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep hv
      exact (hs u _ hu hT).keepE' hF hk
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

theorem simF_dia {Γ : Ctx} {θ θ' : Subst σ Δ} (hs : SimF Γ θ θ') {x ιx : VarSymb}
    (hw : (θ.at x).idxAlong [] = ιx) : SimF (Γ.diaIn x) (θ.dia x ιx) (θ'.dia x ιx) := by
  refine simF_of ?_
  intro v T _ hv hT
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · subst hux
        cases hx : Γ.ref u with
        | none => rw [hx] at hv; cases hv
        | some U =>
            rw [hx] at hv
            cases U <;> try cases hv
            change SubE.Sim _ (if u = u then (θ.at u).diaBody ιx else SubE.hide)
              (if u = u then (θ'.at u).diaBody ιx else SubE.hide)
            rw [if_pos rfl, if_pos rfl]
            exact (hs u _ hx rfl).diaBody hw
  | .step u .box => exact (hs u _ (Ctx.boxIn_step_box (Γ := Γ) hv) hT).unbox.mono _
  | .step u .keep =>
      obtain ⟨hF, hu, hk⟩ := Ctx.boxIn_keep (Γ := Γ) hv
      exact ((hs u _ hu hT).keepE' hF hk).mono _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- Coherent substitutions agreeing at η-faithful addresses pick the same witnesses. -/
theorem idx_eqF {ι ι' : VarSymb → VarSymb} {Γ : Ctx} {θ θ' : Subst σ Δ}
    (hc : Subst.Coh ι Γ θ) (hc' : Subst.Coh ι' Γ θ') (hs : SimF Γ θ θ') {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) : ι' x = ι x := by
  obtain ⟨X, hX⟩ := hx
  have h₁ : (θ.at x).idxAlong [] = ι x := hc x _ hX []
  have h₂ : (θ'.at x).idxAlong [] = ι' x := hc' x _ hX []
  exact h₂.symm.trans ((hs x _ hX rfl).idx.symm.trans h₁)

end Subst

section Congr

variable {σ : Signature}

mutual
  theorem Func.subst_congrF {ι ι' : VarSymb → VarSymb} {Γ Δ : Ctx} (θ θ' : Subst σ Δ)
      (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
      (hc' : Subst.Coh ι' Γ θ') (hs : Subst.SimF Γ θ θ') :
      {n : ℕ} → (f : Func σ Γ n) → Func.subst ι θ hθ hc f = Func.subst ι' θ' hθ' hc' f
    | _, .F _ => rfl
    | _, .eval g t => by
        change Func.eval (Func.subst ι θ hθ hc g) (Term.subst ι θ hθ hc t) =
          Func.eval (Func.subst ι' θ' hθ' hc' g) (Term.subst ι' θ' hθ' hc' t)
        rw [Func.subst_congrF θ θ' hθ hθ' hc hc' hs g,
          eq_of_heq (Sigma.mk.inj (Term.subst_congrF θ θ' hθ hθ' hc hc' hs t)).2]
    termination_by structural _ f => f

  /-- ⭐**Substitution reads only η-faithful addresses**: substitutions agreeing there, up to η,
      substitute every term alike.  Stated for `Σ`-packed terms. -/
  theorem Term.subst_congrF {ι ι' : VarSymb → VarSymb} {Γ Δ : Ctx} (θ θ' : Subst σ Δ)
      (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
      (hc' : Subst.Coh ι' Γ θ') (hs : Subst.SimF Γ θ θ') :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      (⟨_, Term.subst ι θ hθ hc t⟩ : Σ b, Term σ Δ T b) = ⟨_, Term.subst ι' θ' hθ' hc' t⟩
    | _, _, .var v hv => congrArg (Sigma.mk _) ((hs v _ hv rfl).toVar _ _)
    | _, _, .func f => by
        change (⟨_, Term.func (Func.subst ι θ hθ hc f)⟩ : Σ b, Term σ Δ .Var b) =
          ⟨_, Term.func (Func.subst ι' θ' hθ' hc' f)⟩
        rw [Func.subst_congrF θ θ' hθ hθ' hc hc' hs f]
    | _, _, .unit => rfl
    | _, _, .pair s t =>
        sig_pair (Term.subst_congrF θ θ' hθ hθ' hc hc' hs s)
          (Term.subst_congrF θ θ' hθ hθ' hc hc' hs t)
    | _, _, .boxtm t =>
        sig_boxtm (Term.subst_congrF θ.box θ'.box (Subst.ok_box hθ) (Subst.ok_box hθ')
          (Subst.coh_box hθ hc) (Subst.coh_box hθ' hc') (Subst.simF_box hs) t)
    | _, _, .diatm x hx t => by
        have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
        have key : ∀ (y : VarSymb) (_hy : y = ι x) (P : ∃ Y, Δ.ref y = some (.VTypeDia Y))
            (p : Subst.Ok (Γ.diaIn x) (θ'.dia x y))
            (q : Subst.Coh ι' (Γ.diaIn x) (θ'.dia x y)),
            (⟨_, Term.subst ι θ hθ hc (Term.diatm x hx t)⟩ : Σ b, Term σ Δ _ b) =
              ⟨_, Term.diatm y P (Term.subst ι' (θ'.dia x y) p q t)⟩ := by
          intro y hy P p q
          subst hy
          exact sig_diatm (Term.subst_congrF (θ.dia x (ι x)) (θ'.dia x (ι x))
            (Subst.ok_dia hθ hx hw) p (Subst.coh_dia hθ hc hx) q (Subst.simF_dia hs hw) t)
        exact key (ι' x) (Subst.idx_eqF hc hc' hs hx) _ _ _
    termination_by structural _ _ t => t
end

theorem Term.subst_congrF_var {ι ι' : VarSymb → VarSymb} {Γ Δ : Ctx} (θ θ' : Subst σ Δ)
    (hθ : Subst.Ok Γ θ) (hθ' : Subst.Ok Γ θ') (hc : Subst.Coh ι Γ θ)
    (hc' : Subst.Coh ι' Γ θ') (hs : Subst.SimF Γ θ θ') (t : Term σ Γ .Var .var) :
    Term.subst ι θ hθ hc t = Term.subst ι' θ' hθ' hc' t :=
  eq_of_heq (Sigma.mk.inj (Term.subst_congrF θ θ' hθ hθ' hc hc' hs t)).2

end Congr

end V12M
