import QML.QML_v11_Proof

/-!
# QML v11 — substitution reduction lemmas

`Term.substVar` / `WFF.substVar` are well-founded definitions written in tactic mode with a
dispatcher on `V.firstPairVar`, so they do not reduce definitionally.  This file extracts the
COMPUTATION RULES: one equation per constructor, in the PAIR-FREE case, which is where every
consumer lives (`eqRec`'s core, atomic symmetry, Leibniz).

The v11 dispatcher is easier to see through than v10's: it matches on `V.firstPairVar` — the BASE
context — rather than the extended one, so a single `h_pv : V.firstPairVar = none` plus
`S.isPair = false` lands directly in the structural pass.
-/

/-! ## Term level: the dispatcher -/

/-- The dispatcher hands off to the structural pass whenever the base context is pair-free and the
    substituted type is not a product.  `PairFree` is a `Prop`, so the particular proof carried is
    irrelevant and may be supplied by the caller. -/
theorem Term.substVar_eq_substCore {σ : Signature} {V : VarCtx} {x : VarSymb} {S S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (h_pv : V.firstPairVar = none) (hSp : S.isPair = false)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S') :
    Term.substVar hx s t = Term.substCore hx h_pf s t := by
  conv_lhs => unfold Term.substVar
  split
  · exfalso; rename_i heq; rw [h_pv] at heq; exact absurd heq (by simp)
  · split
    · rfl
    · exfalso; rename_i heq2; rw [hSp] at heq2; exact absurd heq2 (by simp)

/-! ## Term level: vacuous substitution

`substCore ∘ ctx_extU = id` at a `.Var`-typed user binder — restricting a freshly-added variable
cancels the weakening that added it.  This is what makes `eq_elim` usable: the Leibniz formula
`φ := (v ≐ a↑)` has `φ[c] = (c ≐ a)` for every `c`, with the `a` untouched.

At `T = .Var` both `ctx_extU`'s and `substCore`'s modal arms pass straight through — `.Var` is
neither box- nor pair-typed — so only `func` and `pair` recurse, and `numNodes` is the measure. -/

mutual
theorem Term.substCore_ctx_extU {σ : Signature} {V : VarCtx} {u : UserSymb} {S' : VarType}
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨u.toVar, VarType.Var⟩ V hu).PairFree)
    (s : Term σ V .Var) (t : Term σ V S') :
    Term.substCore hu h_pf s (Term.ctx_extU u .Var hu t) = t := by
  match t with
  | .var ⟨w, hw⟩ =>
      have hwx : (⟨w, VarType.Var⟩ : VarSymb × VarType) ≠ ⟨u.toVar, VarType.Var⟩ := fun h =>
        hu (Finset.mem_image.mpr ⟨_, hw, (Prod.mk.inj h).1⟩)
      conv_lhs => unfold Term.ctx_extU
      conv_lhs => unfold Term.substCore
      rw [dif_neg hwx]
  | .func fn =>
      have ih := Func.substCore_ctx_extU hu h_pf s fn
      conv_lhs => unfold Term.ctx_extU
      conv_lhs => unfold Term.substCore
      rw [ih]
  | .unit =>
      conv_lhs => unfold Term.ctx_extU
      conv_lhs => unfold Term.substCore
  | .pair t1 t2 =>
      have ih1 := Term.substCore_ctx_extU hu h_pf s t1
      have ih2 := Term.substCore_ctx_extU hu h_pf s t2
      conv_lhs => unfold Term.ctx_extU
      conv_lhs => unfold Term.substCore
      rw [ih1, ih2]
  | @Term.boxterm _ V_inner S_inner _ tt hsub hne =>
      have hu_ninner : u.toVar ∉ VarCtx_to_VarSymbs V_inner := fun h => by
        obtain ⟨⟨w', T'⟩, hw'T', hw'eq⟩ := Finset.mem_image.mp h
        simp only at hw'eq
        exact hu (Finset.mem_image.mpr
          ⟨⟨w', T'.VTypeBox⟩, hsub (Finset.mem_image.mpr ⟨⟨w', T'⟩, hw'T', rfl⟩), hw'eq⟩)
      conv_lhs => unfold Term.ctx_extU
      conv_lhs => unfold Term.substCore
      rw [dif_neg hu_ninner]
  | @Term.diaterm _ V_inner S_inner _ xv hxv tt hsub hne =>
      have hxv_ne : ¬ (xv.1 = u.toVar) := fun h => by
        refine hu (Finset.mem_image.mpr ⟨⟨xv.1, xv.2.VTypeDia⟩, hsub ?_, h⟩)
        rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
      have hu_ninner : u.toVar ∉ VarCtx_to_VarSymbs V_inner := fun h => by
        obtain ⟨⟨w', T'⟩, hw'T', hw'eq⟩ := Finset.mem_image.mp h
        simp only at hw'eq
        refine hu (Finset.mem_image.mpr ⟨⟨w', T'.VTypeBox⟩, hsub ?_, hw'eq⟩)
        rw [VarCtx_dia_fst]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨w', T'⟩, hw'T', rfl⟩)
      conv_lhs => unfold Term.ctx_extU
      conv_lhs => unfold Term.substCore
      rw [dif_neg hxv_ne, dif_neg hu_ninner]
  | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
      exact absurd
        (Finset.mem_insert_of_mem
          (show (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∈ _ from by
            rw [← w₂eq]; exact Finset.mem_insert_self _ _))
        (h_pf z T₁ T₂)
  termination_by Term.numNodes t
  decreasing_by all_goals (simp only [Term.numNodes]; omega)

theorem Func.substCore_ctx_extU {σ : Signature} {V : VarCtx} {u : UserSymb} {N : ℕ}
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨u.toVar, VarType.Var⟩ V hu).PairFree)
    (s : Term σ V .Var) (fn : Func σ V N) :
    Func.substCore hu h_pf s (Func.ctx_extU u .Var hu fn) = fn := by
  match fn with
  | .F fs =>
      conv_lhs => unfold Func.ctx_extU
      conv_lhs => unfold Func.substCore
  | .eval g t =>
      have ihg := Func.substCore_ctx_extU hu h_pf s g
      have iht := Term.substCore_ctx_extU hu h_pf s t
      conv_lhs => unfold Func.ctx_extU
      conv_lhs => unfold Func.substCore
      rw [ihg, iht]
  termination_by Func.numNodes fn
  decreasing_by all_goals (simp only [Func.numNodes]; omega)
end

/-- Substituting for the variable itself. -/
theorem Term.substCore_var_self {σ : Signature} {V : VarCtx} {x : VarSymb}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, VarType.Var⟩ V hx).PairFree)
    (s : Term σ V .Var)
    (hmem : (⟨x, VarType.Var⟩ : VarSymb × VarType)
      ∈ (VarCtx_insert ⟨x, VarType.Var⟩ V hx).1) :
    Term.substCore hx h_pf s (Term.var ⟨x, hmem⟩) = s := by
  conv_lhs => unfold Term.substCore
  rw [dif_pos (rfl : (⟨x, VarType.Var⟩ : VarSymb × VarType) = ⟨x, VarType.Var⟩)]

/-! ## WFF level -/

/-- ⭐The dispatcher at an ALREADY user-named variable hands straight off to the structural pass —
    no α-rename in the way.  This is the equation that makes the whole `subst` package compute. -/
theorem WFF.subst_eq_substCore {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hxu : x.isUsr = true) (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none) (hSp : S.isPair = false)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.subst hx s φ = (WFF.substCore hxu hx h_pf s φ).val := by
  unfold WFF.subst
  conv_lhs => unfold WFF.substVar
  split
  · exfalso; rename_i heq; rw [h_pv] at heq; exact absurd heq (by simp)
  · split
    · split
      · rfl
      · exfalso; rename_i heq3; rw [hxu] at heq3; exact absurd heq3 (by simp)
    · exfalso; rename_i heq2; rw [hSp] at heq2; exact absurd heq2 (by simp)

/-- The structural pass at the `eq` arm. -/
theorem WFF.substCore_eq {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hxu : x.isUsr = true) (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree) (s : Term σ V S)
    (s' t' : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var) :
    (WFF.substCore hxu hx h_pf s (WFF.eq s' t')).val
      = WFF.eq (Term.substCore hx h_pf s s') (Term.substCore hx h_pf s t') := by
  conv_lhs => unfold WFF.substCore

/-! ## Atomic symmetry

`eq_elim` with the Leibniz formula `φ := (v ≐ a↑)`: `φ[a]` is `a ≐ a`, which is `eq_intro`, and
`eq_elim` transports it along `a ≐ b` to `φ[b] = (b ≐ a)`. -/

def Proof.eqSymmAtomic {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)}
    (hfp : V.firstPairVar = none) (a b : Term σ V .Var)
    (p : Proof σ V Γ (WFF.eq a b)) : Proof σ V Γ (WFF.eq b a) := by
  set u : UserSymb := UserSymb.fresh (VarCtx_to_VarSymbs V) with hudef
  have hu : u.toVar ∉ VarCtx_to_VarSymbs V := UserSymb.fresh_not_mem _
  have h_pf : (VarCtx_insert ⟨u.toVar, VarType.Var⟩ V hu).PairFree :=
    VarCtx.pairFree_insert hu (VarCtx.pairFree_of_firstPairVar_none hfp)
      (fun _ _ h => VarType.noConfusion h)
  have hmem : (⟨u.toVar, VarType.Var⟩ : VarSymb × VarType)
      ∈ (VarCtx_insert ⟨u.toVar, VarType.Var⟩ V hu).1 := Finset.mem_insert_self _ _
  set φ : WFF σ (VarCtx_insert ⟨u.toVar, VarType.Var⟩ V hu) :=
    WFF.eq (Term.var ⟨u.toVar, hmem⟩) (Term.ctx_extU u .Var hu a) with hφ
  have key : ∀ (c : Term σ V .Var), WFF.subst hu c φ = WFF.eq c a := by
    intro c
    rw [hφ, WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hu hfp rfl h_pf c,
        WFF.substCore_eq, Term.substCore_var_self, Term.substCore_ctx_extU]
  have pa : Proof σ V Γ (WFF.subst hu a φ) := (key a).symm ▸ Proof.eq_intro a
  have pb : Proof σ V Γ (WFF.subst hu b φ) := Proof.eq_elim u hu a b p pa
  exact (key b) ▸ pb

/-- Atomic symmetry in the object-implication form the `eqRec` symmetry proof wants. -/
theorem varSymm {σ : Signature} (W : VarCtx) (hfp : W.firstPairVar = none)
    (u v : Term σ W .Var) :
    Nonempty (Proof σ W ∅ ((WFF.eq u v).imp (WFF.eq v u))) :=
  ⟨Proof.imp_intro (Proof.eqSymmAtomic hfp u v (Proof.ax (by simp)))⟩
