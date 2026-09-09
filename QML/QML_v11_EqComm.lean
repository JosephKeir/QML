import QML.QML_v11_Eq

/-!
# QML v11 — `eqRec` commutes with weakening (`hcomm`)

Leibniz's `dia_box` case needs `eqRec` to commute with extending the context.  In v10 this had to
be stated as an object IMPLICATION: the peel's fresh component names are drawn from the context, so
weakening moves them, and v10's `WFF.pairElim v₁ v₂ z …` keeps those names IN THE OUTPUT — the two
sides were genuine α-variants, and α-variants of a stuck positive eliminator are not derivably
equal (which is exactly why `pair_elim_alpha` was primitive there).

⭐**In v11 it is an EQUALITY.**  `eqRecPeel` ends in `pairElim … (bindPair T₁ T₂ u₁ u₂ …)`, and
`WFF.bindPair` renames both components onto canonical SLOTS, so `u₁`/`u₂` never reach the output.
The names still move — `UserSymb.fresh` reads the erased context — but the movement is erased.

**What this file proves.**  The commutation, in full, for every weakening type that `ctx_extU`
passes straight through: `Var`, `𝟙` and `◇X` — i.e. everything except `□U` (which descends into a
box's inner context) and `A ×ᵥ B` (which peels).  The base context is taken pair-free, which is
where Leibniz lives.

⭐**The modal arms need NO induction hypothesis at all**, which is why this is short.  A
pass-through weakening leaves a `boxterm`/`diaterm`'s inner context and inner term completely
alone, and `eqRecCore`'s modal arms recurse into exactly that untouched inner context — so both
sides land on the same inner `eqRec` call.  Only the product arm recurses, and it stays at the SAME
context, so the whole induction is a plain one on `sizeOf S`.

**What is left, and why.**  Two weakening shapes and the peel:
* `T = □U` descends, so the recursion lands at the boxterm's INNER context, whose pair-freeness is
  not derivable from the outer context's (`⟨z,(A×B)□⟩` is box-typed, not `VTypeProd`) — so that
  case needs the peel case too.
* `T = A ×ᵥ B` makes `ctx_extU` itself peel.
* ⚠️The peel case is NOT free.  `firstPairVar` reads `V.1.sort (· ≤ ·)`, so it is name-order
  sensitive and a commutation along an ARBITRARY context bijection would be FALSE — a permutation
  can change which variable peels first, hence the nesting of the `pair_elim`s.  What rescues the
  instance needed here is that `UserSymb.fresh` is `max index + 1`: every peel-introduced name sits
  above all of `V₀` on both sides, so the peel SEQUENCE is unchanged.  That invariant is the
  substance of the remaining proof.
-/

/-! ## Pair-freeness and `firstPairVar` -/

/-- The converse of `pairFree_of_firstPairVar_none`: `firstPairVar`'s `some` carries a membership
    proof, which a pair-free context refutes outright. -/
theorem VarCtx.firstPairVar_eq_none_of_pairFree {V : VarCtx} (h : V.PairFree) :
    V.firstPairVar = none := by
  cases hfp : V.firstPairVar with
  | none => rfl
  | some p => exact absurd p.2 (h _ _ _)

/-- Inserting a NON-product entry into a pair-free context keeps it pair-free. -/
theorem VarCtx.firstPairVar_insert_notPair {V : VarCtx} {x : VarSymb} {T : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (hfp : V.firstPairVar = none) (hT : T.isPair = false) :
    (VarCtx_insert ⟨x, T⟩ V hx).firstPairVar = none :=
  VarCtx.firstPairVar_eq_none_of_pairFree
    (VarCtx.pairFree_insert hx (VarCtx.pairFree_of_firstPairVar_none hfp)
      (fun _ _ h => by subst h; simp [VarType.isPair] at hT))

/-! ## `ctx_extU` computation rules

All are one `conv_lhs => unfold`.  The side-condition arguments are `Prop`s, so the caller may
supply any proof. -/

variable {σ : Signature}

theorem Term.ctx_extU_pair {V : VarCtx} {A B : VarType} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (a : Term σ V A) (b : Term σ V B) :
    Term.ctx_extU u T hu (Term.pair a b)
      = Term.pair (Term.ctx_extU u T hu a) (Term.ctx_extU u T hu b) := by
  conv_lhs => unfold Term.ctx_extU

theorem WFF.ctx_extU_eq {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (a b : Term σ V .Var) :
    WFF.ctx_extU u T hu (WFF.eq a b)
      = WFF.eq (Term.ctx_extU u T hu a) (Term.ctx_extU u T hu b) := by
  conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_top {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) :
    WFF.ctx_extU u T hu (WFF.top : WFF σ V) = WFF.top := by
  conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_bot {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) :
    WFF.ctx_extU u T hu (WFF.bot : WFF σ V) = WFF.bot := by
  conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_and {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (φ ψ : WFF σ V) :
    WFF.ctx_extU u T hu (WFF.and φ ψ)
      = WFF.and (WFF.ctx_extU u T hu φ) (WFF.ctx_extU u T hu ψ) := by
  conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_imp {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (φ ψ : WFF σ V) :
    WFF.ctx_extU u T hu (WFF.imp φ ψ)
      = WFF.imp (WFF.ctx_extU u T hu φ) (WFF.ctx_extU u T hu ψ) := by
  conv_lhs => unfold WFF.ctx_extU

/-! ### The modal arms at a PASS-THROUGH weakening type

`ctx_extU`'s `boxterm`/`diaterm` arms match on the CONSTRUCTOR of `T`: `□U'` descends into the
inner context and `A ×ᵥ B` peels, but `Var`, `𝟙` and `◇X` all take the same branch, which leaves
the inner context and inner term completely alone and only restates the side conditions.  `cases T`
collects those three at once, with the two excluded shapes discharged by the hypotheses. -/

theorem Term.ctx_extU_boxterm_pass {V V_inner : VarCtx} {A : VarType} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (tt : Term σ V_inner A)
    (hsub : (VarCtx_box V_inner).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (hsub' : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1)
    (hne' : ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
              VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    Term.ctx_extU u T hu (Term.boxterm tt hsub hne) = Term.boxterm tt hsub' hne' := by
  cases T with
  | VTypeBox _ => simp [VarType.isBox] at hTb
  | VTypeProd _ _ => simp [VarType.isPair] at hTp
  | _ => conv_lhs => unfold Term.ctx_extU

theorem Term.ctx_extU_diaterm_pass {V V_inner : VarCtx} {A : VarType} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {xv : VarSymb × VarType}
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) A)
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1)
    (hne' : ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
              VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    Term.ctx_extU u T hu (Term.diaterm xv hxv tt hsub hne)
      = Term.diaterm xv hxv tt hsub' hne' := by
  cases T with
  | VTypeBox _ => simp [VarType.isBox] at hTb
  | VTypeProd _ _ => simp [VarType.isPair] at hTp
  | _ => conv_lhs => unfold Term.ctx_extU

theorem WFF.ctx_extU_box_pass {V V_inner : VarCtx} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) (χ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (hsub' : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1)
    (hne' : ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
              VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    WFF.ctx_extU u T hu (WFF.box χ hsub hne) = WFF.box χ hsub' hne' := by
  cases T with
  | VTypeBox _ => simp [VarType.isBox] at hTb
  | VTypeProd _ _ => simp [VarType.isPair] at hTp
  | _ => conv_lhs => unfold WFF.ctx_extU

theorem WFF.ctx_extU_dia_pass {V V_inner : VarCtx} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {xv : VarSymb × VarType}
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (χ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1)
    (hne' : ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
              VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    WFF.ctx_extU u T hu (WFF.dia xv hxv χ hsub hne) = WFF.dia xv hxv χ hsub' hne' := by
  cases T with
  | VTypeBox _ => simp [VarType.isBox] at hTb
  | VTypeProd _ _ => simp [VarType.isPair] at hTp
  | _ => conv_lhs => unfold WFF.ctx_extU

/-- `□_x` is `¬◇_x¬`, so its weakening rule follows from `dia`'s and the propositional ones. -/
theorem WFF.ctx_extU_box_x_pass {V V_inner : VarCtx} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {xv : VarSymb × VarType}
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (χ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1)
    (hne' : ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
              VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    WFF.ctx_extU u T hu (WFF.box_x xv hxv hsub hne χ) = WFF.box_x xv hxv hsub' hne' χ := by
  unfold WFF.box_x neg
  rw [WFF.ctx_extU_imp,
      WFF.ctx_extU_dia_pass u T hTb hTp hu hxv _ hsub hne hsub' hne',
      WFF.ctx_extU_bot]

/-! ## Side-condition transfer

The new entry `⟨u, T⟩` is not box-typed, so it can neither be needed by a `⊆` nor act as a
box-typed extra. -/

theorem box_sub_insert_pass {V V_inner : VarCtx} {u : UserSymb} {T : VarType}
    {hu : u.toVar ∉ VarCtx_to_VarSymbs V} (hsub : (VarCtx_box V_inner).1 ⊆ V.1) :
    (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1 :=
  fun _ hp => Finset.mem_insert_of_mem (hsub hp)

theorem box_extras_insert_pass {V V_inner : VarCtx} {u : UserSymb} {T : VarType}
    {hu : u.toVar ∉ VarCtx_to_VarSymbs V} (hTb : T.isBox = false)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
      VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1 := by
  intro p hp h_box
  rcases Finset.mem_insert.mp hp with rfl | hp_V
  · exact absurd h_box (by simp [hTb])
  · exact hne p hp_V h_box

theorem dia_sub_insert_pass {V V_inner : VarCtx} {u : UserSymb} {T : VarType}
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner}
    {hu : u.toVar ∉ VarCtx_to_VarSymbs V} (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1) :
    (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1 :=
  fun _ hp => Finset.mem_insert_of_mem (hsub hp)

theorem dia_extras_insert_pass {V V_inner : VarCtx} {u : UserSymb} {T : VarType}
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner}
    {hu : u.toVar ∉ VarCtx_to_VarSymbs V} (hTb : T.isBox = false)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    ∀ p ∈ (VarCtx_insert ⟨u.toVar, T⟩ V hu).1,
      VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1 := by
  intro p hp h_box
  rcases Finset.mem_insert.mp hp with rfl | hp_V
  · exact absurd h_box (by simp [hTb])
  · exact hne p hp_V h_box

/-- ⚠️`diaCast` is insensitive to its side-condition arguments — and, crucially, to the AMBIENT
    context they mention.  That is not `rfl`: the `Eq.rec` it compiles to has the ambient context in
    its motive, so the two sides are genuinely different terms until `diaterm_ctx_unique`'s
    equality is substituted away.  (`boxCast` needs no such lemma; its ambient context does not
    reach the motive, so `boxCast_id` covers it.) -/
theorem diaCast_irrel {A : VarType} {x₁ x₂ : VarSymb × VarType} {V₁ V₂ W W' : VarCtx}
    {hx₁ : x₁.1 ∉ VarCtx_to_VarSymbs V₁} {hx₂ : x₂.1 ∉ VarCtx_to_VarSymbs V₂}
    (hx : x₁ = x₂)
    (hsub₁ : (VarCtx_dia x₁ V₁ hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₁ V₁ hx₁).1)
    (hsub₂ : (VarCtx_dia x₂ V₂ hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₂ V₂ hx₂).1)
    (hsub₁' : (VarCtx_dia x₁ V₁ hx₁).1 ⊆ W'.1)
    (h₁' : ∀ p ∈ W'.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₁ V₁ hx₁).1)
    (hsub₂' : (VarCtx_dia x₂ V₂ hx₂).1 ⊆ W'.1)
    (h₂' : ∀ p ∈ W'.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₂ V₂ hx₂).1)
    (tt : Term σ (VarCtx_insert x₂ V₂ hx₂) A) :
    diaCast hx hsub₁' h₁' hsub₂' h₂' tt = diaCast hx hsub₁ h₁ hsub₂ h₂ tt := by
  subst hx
  have hV : V₁ = V₂ := diaterm_ctx_unique hsub₁ h₁ hsub₂ h₂
  subst hV
  rfl

/-! ## The structural half of `hcomm`

⭐**The modal arms need NO induction hypothesis.**  A pass-through weakening leaves a
`boxterm`/`diaterm`'s INNER context and inner term completely alone and only restates the side
conditions — and `eqRecCore`'s modal arms recurse into exactly that untouched inner context.  Both
sides therefore land on the same inner `eqRec` call.  Only the product arm recurses, at `A` and
`B`, and at the SAME context. -/

theorem eqRecCore_ctx_extU_pass {σ : Signature} (w : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false) :
    ∀ (V : VarCtx) (hV : V.AllUsr) (hw : w.toVar ∉ VarCtx_to_VarSymbs V) (S : VarType)
      (hfp : V.firstPairVar = none)
      (hfp' : (VarCtx_insert ⟨w.toVar, T⟩ V hw).firstPairVar = none)
      (hVU : (VarCtx_insert ⟨w.toVar, T⟩ V hw).AllUsr)
      (t s : Term σ V S),
      (∀ (A : VarType), sizeOf A < sizeOf S → ∀ (a b : Term σ V A),
          eqRec (VarCtx_insert ⟨w.toVar, T⟩ V hw) hVU A
              (Term.ctx_extU w T hw a) (Term.ctx_extU w T hw b)
            = WFF.ctx_extU w T hw (eqRec V hV A a b)) →
      eqRecCore (VarCtx_insert ⟨w.toVar, T⟩ V hw) hVU S hfp'
          (Term.ctx_extU w T hw t) (Term.ctx_extU w T hw s)
        = WFF.ctx_extU w T hw (eqRecCore V hV S hfp t s)
  | _, _, _, .Var, _, _, _, _, _, _ => by
      rw [eqRecCore_var, eqRecCore_var, WFF.ctx_extU_eq]
  | _, _, _, .VTypeOne, _, _, _, _, _, _ => by
      rw [eqRecCore_unit, eqRecCore_unit, WFF.ctx_extU_top]
  | _, _, _, .VTypeProd A B, _, _, _, .pair a b, .pair c d, IH => by
      rw [Term.ctx_extU_pair, Term.ctx_extU_pair, eqRecCore_prod, eqRecCore_prod,
          WFF.ctx_extU_and, IH A (by simp; try omega) a c,
          IH B (by simp; try omega) b d]
  | _, _, _, .VTypeBox _, _, _, _, .boxterm _ hsub₁ h₁, .boxterm _ hsub₂ h₂, _ => by
      rw [Term.ctx_extU_boxterm_pass w T hTb hTp _ _ _ _
            (box_sub_insert_pass hsub₁) (box_extras_insert_pass hTb h₁),
          Term.ctx_extU_boxterm_pass w T hTb hTp _ _ _ _
            (box_sub_insert_pass hsub₂) (box_extras_insert_pass hTb h₂),
          eqRecCore_box, eqRecCore_box,
          WFF.ctx_extU_box_pass w T hTb hTp _ _ _ _
            (box_sub_insert_pass hsub₁) (box_extras_insert_pass hTb h₁)]
      -- what is left differs only in `boxCast`'s subset/no-extras arguments, which it consumes
      -- solely through `boxterm_ctx_unique`'s EQUALITY — proof-irrelevant.
      rfl
  | _, _, _, .VTypeDia _, _, _, _, .diaterm x₁ _ _ hsub₁ h₁, .diaterm x₂ _ _ hsub₂ h₂, _ => by
      rw [Term.ctx_extU_diaterm_pass w T hTb hTp _ _ _ _ _
            (dia_sub_insert_pass hsub₁) (dia_extras_insert_pass hTb h₁),
          Term.ctx_extU_diaterm_pass w T hTb hTp _ _ _ _ _
            (dia_sub_insert_pass hsub₂) (dia_extras_insert_pass hTb h₂)]
      by_cases hx : x₁ = x₂
      · rw [eqRecCore_dia_same _ _ _ _ _ _ _ _ hx, eqRecCore_dia_same _ _ _ _ _ _ _ _ hx,
            WFF.ctx_extU_box_x_pass w T hTb hTp _ _ _ _ _
              (dia_sub_insert_pass hsub₁) (dia_extras_insert_pass hTb h₁),
            diaCast_irrel hx hsub₁ h₁ hsub₂ h₂]
      · rw [eqRecCore_dia_ne _ _ _ _ _ _ _ _ hx, eqRecCore_dia_ne _ _ _ _ _ _ _ _ hx,
            WFF.ctx_extU_bot]
  | _, _, _, _, hfp, _, _, .pair_elim _ _ _ _ _ w₂eq _, _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
  | _, _, _, _, hfp, _, _, _, .pair_elim _ _ _ _ _ w₂eq _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim

/-- ⭐**`hcomm` for a PASS-THROUGH weakening in a pair-free context**: `eqRec` commutes with
    extending the context by a user variable whose type is neither box- nor product-typed.
    Self-contained — the peel never fires, and the only recursion is the product arm, which stays
    at the same context, so the induction is a plain one on `sizeOf S`. -/
theorem eqRec_ctx_extU_pass {σ : Signature} (w : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false) :
    ∀ (V : VarCtx) (hV : V.AllUsr) (hw : w.toVar ∉ VarCtx_to_VarSymbs V)
      (_hfp : V.firstPairVar = none) (S : VarType) (t s : Term σ V S),
      eqRec (VarCtx_insert ⟨w.toVar, T⟩ V hw) (hV.insert hw rfl) S
          (Term.ctx_extU w T hw t) (Term.ctx_extU w T hw s)
        = WFF.ctx_extU w T hw (eqRec V hV S t s)
  | V, hV, hw, hfp, S, t, s => by
      have hfp' : (VarCtx_insert ⟨w.toVar, T⟩ V hw).firstPairVar = none :=
        VarCtx.firstPairVar_insert_notPair hw hfp hTp
      rw [eqRec_of_none hfp', eqRec_of_none hfp]
      exact eqRecCore_ctx_extU_pass w T hTb hTp V hV hw S hfp hfp' (hV.insert hw rfl) t s
        (fun A _ a b => eqRec_ctx_extU_pass w T hTb hTp V hV hw hfp A a b)
termination_by _ _ _ _ S _ _ => sizeOf S
