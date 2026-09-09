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

/-! ### The `box` case — where `box_ext` is consumed

⭐This is the case the whole reform is aimed at.  `eqRec` at `□T` IS `□` of the inner equality
(`eqRecCore_box`), and `subst` of a `boxterm` into a `box` IS `box` of the inner substitution
(`WFF.substCore_box_erased`), with the substituted variable UNBOXED inside.  So both sides of the
goal are `□` of the inner Leibniz instance, and `K_box` — in its hypothesis-set form `congBoxG` —
carries it out.  The recursion drops both the formula (`χ < □χ`) and the type (`T < □T`).

The two boxterms share one inner context and one pair of side conditions; that is not a
restriction but `boxterm_ctx_unique`, which forces it. -/

/-- `Γ ⊢ φ → ψ` gives `□Γ ⊢ □φ → □ψ`. -/
def Proof.congBoxG {σ : Signature} {V W : VarCtx} {Γ : Finset (WFF σ V)} {φ ψ : WFF σ V}
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hφψ : Proof σ V Γ (φ.imp ψ)) :
    Proof σ W (WFF.box_Finset hsub h Γ) ((WFF.box φ hsub h).imp (WFF.box ψ hsub h)) := by
  have h1 : Proof σ V (Γ ∪ {φ}) ψ := Proof.imp_elim (Proof.weak hφψ) (Proof.ax (by simp))
  have hK := Proof.K_box hsub h h1
  rw [show WFF.box_Finset hsub h (Γ ∪ {φ})
        = WFF.box_Finset hsub h Γ ∪ {WFF.box φ hsub h} by
      simp [WFF.box_Finset]] at hK
  exact Proof.imp_intro hK

theorem Leib.box {σ : Signature} {V_inner W : VarCtx} {u : UserSymb} {T : VarType}
    (hW : W.AllUsr) (hxW : u.toVar ∉ VarCtx_to_VarSymbs W)
    (h_pv : W.firstPairVar = none)
    (hxT_in : (⟨u.toVar, T⟩ : VarSymb × VarType) ∈ V_inner.1)
    (t s : Term σ (VarCtx_erase V_inner ⟨u.toVar, T⟩) T)
    (s_hsub : (VarCtx_box (VarCtx_erase V_inner ⟨u.toVar, T⟩)).1 ⊆ W.1)
    (s_hne : ∀ p ∈ W.1, VarType.isBox p.2 = true
               → p ∈ (VarCtx_box (VarCtx_erase V_inner ⟨u.toVar, T⟩)).1)
    (χ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨u.toVar, T.VTypeBox⟩ W hxW).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨u.toVar, T.VTypeBox⟩ W hxW).1, VarType.isBox p.2 = true
             → p ∈ (VarCtx_box V_inner).1)
    (ih : Leib (hW.of_box_sub s_hsub) (VarCtx_erase_fresh hxT_in) t s
            ((VarCtx_insert_erase hxT_in (VarCtx_erase_fresh hxT_in)).symm ▸ χ)) :
    Leib hW hxW (Term.boxterm t s_hsub s_hne) (Term.boxterm s s_hsub s_hne)
      (WFF.box χ hsub hne) := by
  have hSp : (T.VTypeBox).isPair = false := rfl
  unfold Leib at ih ⊢
  rw [WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hxW h_pv hSp
        (pairFree_ext hxW h_pv hSp) (Term.boxterm t s_hsub s_hne) (WFF.box χ hsub hne),
      WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hxW h_pv hSp
        (pairFree_ext hxW h_pv hSp) (Term.boxterm s s_hsub s_hne) (WFF.box χ hsub hne),
      WFF.substCore_box_erased (hxT_in := hxT_in), WFF.substCore_box_erased (hxT_in := hxT_in),
      eqRec_of_none h_pv, eqRecCore_box, boxCast_id]
  refine ⟨Proof.hyp_cast ?_ (Proof.congBoxG s_hsub s_hne ih.some)⟩
  simp [WFF.box_Finset]

/-- The `box` PASS-THROUGH: the substituted variable does not occur inside the box, so both sides
    of the implication are literally the same formula. -/
theorem Leib.box_out {σ : Signature} {V_inner W : VarCtx} {u : UserSymb} {S : VarType}
    (hW : W.AllUsr) (hxW : u.toVar ∉ VarCtx_to_VarSymbs W)
    (h_pv : W.firstPairVar = none) (hSp : S.isPair = false) (a b : Term σ W S)
    (χ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨u.toVar, S⟩ W hxW).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨u.toVar, S⟩ W hxW).1, VarType.isBox p.2 = true
             → p ∈ (VarCtx_box V_inner).1)
    (h_x_out : u.toVar ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_box V_inner).1 ⊆ W.1)
    (hne' : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    Leib hW hxW a b (WFF.box χ hsub hne) := by
  unfold Leib
  rw [WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hxW h_pv hSp
        (pairFree_ext hxW h_pv hSp) a (WFF.box χ hsub hne),
      WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hxW h_pv hSp
        (pairFree_ext hxW h_pv hSp) b (WFF.box χ hsub hne),
      WFF.substCore_box_out (h_x_out := h_x_out) (hsub' := hsub') (hne' := hne'),
      WFF.substCore_box_out (h_x_out := h_x_out) (hsub' := hsub') (hne' := hne')]
  exact ⟨Proof.impId⟩

/-! ### The `dia` case — modal β, and where `dia_ext` is consumed

The `◇` analogue of `Leib.box`, but genuinely different in shape: the substituted variable IS the
`◇`-binder's witness, so `subst` performs a MODAL β reduction — the outer `◇_x` binder is REPLACED
by the substituted diaterm's own witness `xv_s`, and the body is weakened by `xv_s` and reordered.
Meanwhile `eqRec` at `◇A` is a `□_{xv_s}` of the inner equality, and `□_x` is exactly `K_dia`'s
witnessed-hypothesis slot — so the two fit together and `congDiaG` carries the inner instance out
through the `◇`.

Both diaterms carry the SAME witness: for different witnesses `eqRec` is `⊥` (`eqRecCore_dia_ne`)
and the instance is vacuous. -/

/-- `Δ ⊢ φ → ψ` gives `□_xΔ ⊢ ◇_xφ → ◇_xψ` — `K_dia` with the plain-`□` slot empty. -/
def Proof.congDiaG {σ : Signature} {V W : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V} {Δ : Finset (WFF σ (VarCtx_insert x V hx))}
    {φ ψ : WFF σ (VarCtx_insert x V hx)}
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (hφψ : Proof σ (VarCtx_insert x V hx) Δ (φ.imp ψ)) :
    Proof σ W (WFF.box_x_Finset x hx hsub h Δ)
      ((WFF.dia x hx φ hsub h).imp (WFF.dia x hx ψ hsub h)) := by
  have h1 : Proof σ (VarCtx_insert x V hx) (Δ ∪ {φ}) ψ :=
    Proof.imp_elim (Proof.weak hφψ) (Proof.ax (by simp))
  have hK := Proof.K_dia (Γ := (∅ : Finset (WFF σ V))) (Δ := Δ) x hx hsub h
    (by simpa [WFF.ctx_ext_Finset] using h1)
  simp only [WFF.box_Finset, Finset.image_empty, Finset.empty_union] at hK
  exact Proof.imp_intro hK

theorem Leib.dia {σ : Signature} {V V_inner : VarCtx} {u : UserSymb} {A : VarType}
    (hV : V.AllUsr) (hx : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none)
    (hxv : u.toVar ∉ VarCtx_to_VarSymbs V_inner)
    {xv_s : VarSymb × VarType} (hxv_s : xv_s.1 ∉ VarCtx_to_VarSymbs V_inner)
    (tt tt' : Term σ (VarCtx_insert xv_s V_inner hxv_s) A)
    (hsub_s : (VarCtx_dia xv_s V_inner hxv_s).1 ⊆ V.1)
    (hne_s : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv_s V_inner hxv_s).1)
    (inner : WFF σ (VarCtx_insert (⟨u.toVar, A⟩ : VarSymb × VarType) V_inner hxv))
    (hsub : (VarCtx_dia (⟨u.toVar, A⟩ : VarSymb × VarType) V_inner hxv).1
              ⊆ (VarCtx_insert ⟨u.toVar, A.VTypeDia⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨u.toVar, A.VTypeDia⟩ V hx).1, VarType.isBox p.2 = true
             → p ∈ (VarCtx_dia (⟨u.toVar, A⟩ : VarSymb × VarType) V_inner hxv).1)
    (hxv_s_outer : xv_s.1
      ∉ VarCtx_to_VarSymbs (VarCtx_insert (⟨u.toVar, A⟩ : VarSymb × VarType) V_inner hxv))
    (hx_inner : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s))
    (hcomm : VarCtx_insert xv_s (VarCtx_insert (⟨u.toVar, A⟩ : VarSymb × VarType) V_inner hxv)
                 hxv_s_outer
               = VarCtx_insert (⟨u.toVar, A⟩ : VarSymb × VarType)
                   (VarCtx_insert xv_s V_inner hxv_s) hx_inner)
    (ih : Leib (hV.of_dia_sub hsub_s) hx_inner tt tt'
            (hcomm ▸ WFF.ctx_ext xv_s hxv_s_outer inner)) :
    Leib hV hx (Term.diaterm xv_s hxv_s tt hsub_s hne_s)
               (Term.diaterm xv_s hxv_s tt' hsub_s hne_s)
      (WFF.dia ⟨u.toVar, A⟩ hxv inner hsub hne) := by
  have hSp : (A.VTypeDia).isPair = false := rfl
  unfold Leib at ih ⊢
  rw [WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hx h_pv hSp
        (pairFree_ext hx h_pv hSp) (Term.diaterm xv_s hxv_s tt hsub_s hne_s)
        (WFF.dia ⟨u.toVar, A⟩ hxv inner hsub hne),
      WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hx h_pv hSp
        (pairFree_ext hx h_pv hSp) (Term.diaterm xv_s hxv_s tt' hsub_s hne_s)
        (WFF.dia ⟨u.toVar, A⟩ hxv inner hsub hne),
      WFF.substCore_dia_beta (hcomm := hcomm), WFF.substCore_dia_beta (hcomm := hcomm),
      eqRec_of_none h_pv, eqRecCore_dia_same _ _ _ _ _ _ _ _ rfl, diaCast_id]
  refine ⟨Proof.hyp_cast ?_ (Proof.congDiaG hsub_s hne_s ih.some)⟩
  simp [WFF.box_x_Finset]

/-- The `dia` PASS-THROUGH: neither the witness nor the interior mentions the substituted
    variable, so both sides of the implication are literally the same formula. -/
theorem Leib.dia_out {σ : Signature} {V V_inner : VarCtx} {u : UserSymb} {S : VarType}
    (hV : V.AllUsr) (hx : u.toVar ∉ VarCtx_to_VarSymbs V)
    (h_pv : V.firstPairVar = none) (hSp : S.isPair = false) (a b : Term σ V S)
    {xv : VarSymb × VarType} (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (inner : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨u.toVar, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨u.toVar, S⟩ V hx).1, VarType.isBox p.2 = true
             → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (h_xv_ne : ¬ (xv.1 = u.toVar)) (h_x_out : u.toVar ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1)
    (hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    Leib hV hx a b (WFF.dia xv hxv inner hsub hne) := by
  unfold Leib
  rw [WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hx h_pv hSp
        (pairFree_ext hx h_pv hSp) a (WFF.dia xv hxv inner hsub hne),
      WFF.subst_eq_substCore (UserSymb.isUsr_toVar u) hx h_pv hSp
        (pairFree_ext hx h_pv hSp) b (WFF.dia xv hxv inner hsub hne),
      WFF.substCore_dia_out (h_xv_ne := h_xv_ne) (h_x_out := h_x_out)
        (hsub' := hsub') (hne' := hne'),
      WFF.substCore_dia_out (h_xv_ne := h_xv_ne) (h_x_out := h_x_out)
        (hsub' := hsub') (hne' := hne')]
  exact ⟨Proof.impId⟩
