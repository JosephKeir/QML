import QML.QML_v11_Eq

/-!
# QML v11 — Leibniz's law for the defined equality

With equality DEFINED (`eqRec`), the primitive `eq_elim` survives only at `.Var`.  Its full
strength has to come back as a THEOREM:

    `a ≐ b ⊢ φ[a] → φ[b]`   at every type.

⭐**The induction is on the TYPE, and it is much shorter than it looks.**  `eqRec_leibniz_Var`
below covers EVERY `φ` at `S = .Var` in one line — at that type the defined equality IS the
primitive one, so Leibniz is `eq_elim` repackaged.  `Leib.of_unitType` covers every `φ` at
`S = 𝟙` because a pair-free context has only one unit-typed term.  A product `S` is excluded by
the pair-freeness side condition (it would put a pair variable in the extended context).  So the
case analysis on `φ` is needed ONLY at `S = □A` and `S = ◇A` — exactly the two types whose
extensionality principles `eqRec` consumes.

The equation sits in the HYPOTHESIS SET rather than as an antecedent: that is the form `K_box` /
`K_dia` transport through a modality, so the box case can hand the inner instance straight to
`K_box`.
-/

/-! ## Congruences at an ARBITRARY hypothesis set

`QML_v11_Eq` has the `∅` versions, which suffice for symmetry (where the equation is an
antecedent).  Leibniz keeps the equation in `Γ`, so it needs these. -/

/-- `∨`-congruence. -/
def Proof.congOr {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {p p' q q' : WFF σ V}
    (hp : Proof σ V Γ (p.imp p')) (hq : Proof σ V Γ (q.imp q')) :
    Proof σ V Γ ((p.or q).imp (p'.or q')) := by
  have hdisj : Proof σ V (Γ ∪ {p.or q}) (p.or q) := Proof.ax (by simp)
  refine Proof.imp_intro (Proof.or_elim hdisj ?_ ?_)
  · exact Proof.or_intro_l
      (Proof.imp_elim (Proof.weak (Proof.weak hp)) (Proof.ax (by simp)))
  · exact Proof.or_intro_r
      (Proof.imp_elim (Proof.weak (Proof.weak hq)) (Proof.ax (by simp)))

/-- `→`-congruence.  CONTRAVARIANT in the antecedent — which is exactly why Leibniz's `imp` case
    needs symmetry, to get the reversed instance there. -/
def Proof.congImp {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {p p' q q' : WFF σ V}
    (hp : Proof σ V Γ (p'.imp p)) (hq : Proof σ V Γ (q.imp q')) :
    Proof σ V Γ ((p.imp q).imp (p'.imp q')) := by
  refine Proof.imp_intro (Proof.imp_intro ?_)
  have hp_ : Proof σ V ((Γ ∪ {p.imp q}) ∪ {p'}) p :=
    Proof.imp_elim (Proof.weak (Proof.weak hp)) (Proof.ax (by simp))
  exact Proof.imp_elim (Proof.weak (Proof.weak hq))
    (Proof.imp_elim (Proof.ax (by simp)) hp_)

/-- Cut. -/
def Proof.cut {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {φ ψ : WFF σ V}
    (h1 : Proof σ V Γ φ) (h2 : Proof σ V (Γ ∪ {φ}) ψ) : Proof σ V Γ ψ :=
  Proof.imp_elim (Proof.imp_intro h2) h1

/-- Replace the single hypothesis `φ` by anything that entails it. -/
def Proof.reHyp {σ : Signature} {V : VarCtx} {φ φ' ψ : WFF σ V}
    (h : Proof σ V ∅ (φ'.imp φ)) (p : Proof σ V {φ} ψ) : Proof σ V {φ'} ψ := by
  have hw : Proof σ V {φ'} (φ'.imp φ) :=
    Proof.hyp_cast (by simp) (Proof.weak (ψ := φ') h)
  have hφ : Proof σ V {φ'} φ := Proof.imp_elim hw (Proof.ax (by simp))
  have hi : Proof σ V ∅ (φ.imp ψ) := Proof.imp_intro (Proof.hyp_cast (by simp) p)
  exact Proof.imp_elim (Proof.hyp_cast (by simp) (Proof.weak (ψ := φ') hi)) hφ

/-! ## Leibniz -/

/-- Leibniz's law for the single formula `φ`: from `a ≐ b`, `φ[a] → φ[b]`. -/
def Leib {σ : Signature} {V : VarCtx} {S : VarType} {u : UserSymb}
    (hV : V.AllUsr) (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (a b : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨u.toVar, S⟩ V hu)) : Prop :=
  Nonempty (Proof σ V {eqRec V hV S a b} ((WFF.subst hu a φ).imp (WFF.subst hu b φ)))

/-! ### ⭐The atomic type: EVERY formula at once

At `S = .Var` the defined equality IS `WFF.eq`, so this is `Proof.eq_elim` packaged as an object
implication — no induction on `φ` at all. -/

theorem eqRec_leibniz_Var {σ : Signature} {V : VarCtx} {u : UserSymb}
    (hV : V.AllUsr) (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (hfp : V.firstPairVar = none) (a b : Term σ V .Var)
    (φ : WFF σ (VarCtx_insert ⟨u.toVar, VarType.Var⟩ V hu)) :
    Leib hV hu a b φ := by
  unfold Leib
  rw [eqRec_of_none hfp, eqRecCore_var]
  exact ⟨Proof.imp_intro
    (Proof.eq_elim u hu a b (Proof.ax (by simp)) (Proof.ax (by simp)))⟩

/-! ### Propositional cases

Each is the matching `substCore` reduction lemma plus the matching congruence at
`Γ = {a ≐ b}`.  Only `imp` is not a plain recursion: being contravariant in its antecedent it
needs the REVERSED instance, which `eqRec_symm'` supplies. -/

variable {σ : Signature} {V : VarCtx} {S : VarType} {u : UserSymb}

theorem Leib.top (hV : V.AllUsr) (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none) (hSp : S.isPair = false) (a b : Term σ V S) :
    Leib hV hu a b WFF.top := by
  unfold Leib
  rw [WFF.subst_top (UserSymb.isUsr_toVar u) hu h_pv hSp a,
      WFF.subst_top (UserSymb.isUsr_toVar u) hu h_pv hSp b]
  exact ⟨Proof.impId⟩

theorem Leib.bot (hV : V.AllUsr) (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none) (hSp : S.isPair = false) (a b : Term σ V S) :
    Leib hV hu a b WFF.bot := by
  unfold Leib
  rw [WFF.subst_bot (UserSymb.isUsr_toVar u) hu h_pv hSp a,
      WFF.subst_bot (UserSymb.isUsr_toVar u) hu h_pv hSp b]
  exact ⟨Proof.impId⟩

theorem Leib.and (hV : V.AllUsr) (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none) (hSp : S.isPair = false) {a b : Term σ V S}
    {φ ψ : WFF σ (VarCtx_insert ⟨u.toVar, S⟩ V hu)}
    (ihφ : Leib hV hu a b φ) (ihψ : Leib hV hu a b ψ) : Leib hV hu a b (φ.and ψ) := by
  unfold Leib at *
  rw [WFF.subst_and (UserSymb.isUsr_toVar u) hu h_pv hSp a φ ψ,
      WFF.subst_and (UserSymb.isUsr_toVar u) hu h_pv hSp b φ ψ]
  exact ⟨Proof.congAnd ihφ.some ihψ.some⟩

theorem Leib.or (hV : V.AllUsr) (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none) (hSp : S.isPair = false) {a b : Term σ V S}
    {φ ψ : WFF σ (VarCtx_insert ⟨u.toVar, S⟩ V hu)}
    (ihφ : Leib hV hu a b φ) (ihψ : Leib hV hu a b ψ) : Leib hV hu a b (φ.or ψ) := by
  unfold Leib at *
  rw [WFF.subst_or (UserSymb.isUsr_toVar u) hu h_pv hSp a φ ψ,
      WFF.subst_or (UserSymb.isUsr_toVar u) hu h_pv hSp b φ ψ]
  exact ⟨Proof.congOr ihφ.some ihψ.some⟩

/-- The `→` case.  Contravariance means the antecedent needs the instance the other way round;
    `eqRec_symm'` converts the hypothesis `a ≐ b` into the `b ≐ a` that instance expects. -/
theorem Leib.imp (hV : V.AllUsr) (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none) (hSp : S.isPair = false) {a b : Term σ V S}
    {φ ψ : WFF σ (VarCtx_insert ⟨u.toVar, S⟩ V hu)}
    (ihφ : Leib hV hu b a φ) (ihψ : Leib hV hu a b ψ) : Leib hV hu a b (φ.imp ψ) := by
  unfold Leib at *
  rw [WFF.subst_imp (UserSymb.isUsr_toVar u) hu h_pv hSp a φ ψ,
      WFF.subst_imp (UserSymb.isUsr_toVar u) hu h_pv hSp b φ ψ]
  exact ⟨Proof.congImp (Proof.reHyp (eqRec_symm' V hV S a b).some ihφ.some) ihψ.some⟩

/-! ### ⭐The unit type: EVERY formula at once

A pair-free context has exactly one unit-typed term (`.pair_elim` is the only other constructor
that could produce one, and it would need a pair variable), so `a` and `b` are literally equal and
both sides of the implication are the same formula. -/

theorem Term.unit_unique {σ : Signature} {V : VarCtx} (hV : V.PairFree)
    (t : Term σ V .VTypeOne) : t = Term.unit := by
  match t with
  | .unit => rfl
  | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
      exact absurd
        (show (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∈ V.1 from by
          rw [← w₂eq]; exact Finset.mem_insert_self _ _)
        (hV z T₁ T₂)

theorem Leib.of_unitType (hV : V.AllUsr) (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none) (a b : Term σ V .VTypeOne)
    (φ : WFF σ (VarCtx_insert ⟨u.toVar, VarType.VTypeOne⟩ V hu)) :
    Leib hV hu a b φ := by
  have ha := Term.unit_unique (VarCtx.pairFree_of_firstPairVar_none h_pv) a
  have hb := Term.unit_unique (VarCtx.pairFree_of_firstPairVar_none h_pv) b
  subst ha; subst hb
  exact ⟨Proof.impId⟩
