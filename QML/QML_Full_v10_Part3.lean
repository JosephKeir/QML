import QML.QML_Full_v10_Part2

/-!
# v10 Part 3 — "equality by extensionality" reform (staging)

Develops the recursive `WFF.eq` (`eqRec`) additively, using the *existing* `WFF.eq` constructor
as the atomic (`.Var`) base, so everything stays green while the definition is built.  Once
validated, `eqRec` replaces the general `WFF.eq` constructor (Var-only `primEq` remains primitive),
and `box_ext`/`dia_ext`/`pair_elim_alpha` are retired (definitional / derived).

This file first establishes the **inner-context determinacy** lemmas: `h_no_box_extras` pins
`VarCtx_box V` to exactly the box-typed part of `W`, so a box/dia term's inner context is
determined by `W` (up to the ◇-witness). These let the modal cases of `eqRec` recurse without any
weakening.
-/

/-- Every entry of `VarCtx_box V` is box-typed. -/
theorem VarCtx_box_entry_isBox {V : VarCtx} {p : VarSymb × VarType}
    (hp : p ∈ (VarCtx_box V).1) : VarType.isBox p.2 = true := by
  simp only [VarCtx_box] at hp
  rcases Finset.mem_image.mp hp with ⟨⟨v, S⟩, _, heq⟩
  subst heq; rfl

/-- **Box-term inner-context determinacy.** Two boxterms of the same type in the same `W` have the
    same inner context: `hsub` (⊆) and `h_no_box_extras` (⊇) pin `VarCtx_box Vᵢ` to the box-typed
    part of `W`, and `VarCtx_box` is injective. -/
theorem boxterm_ctx_unique {V₁ V₂ W : VarCtx}
    (hsub₁ : (VarCtx_box V₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₁).1)
    (hsub₂ : (VarCtx_box V₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₂).1) :
    V₁ = V₂ := by
  apply VarCtx_box_inj
  apply VarCtx_ext
  apply Finset.Subset.antisymm
  · intro p hp; exact h₂ p (hsub₁ hp) (VarCtx_box_entry_isBox hp)
  · intro p hp; exact h₁ p (hsub₂ hp) (VarCtx_box_entry_isBox hp)

/-- `VarCtx_box V` sits inside `VarCtx_dia x V` (which adds only the dia-typed witness). -/
theorem VarCtx_box_subset_dia {x : VarSymb × VarType} {V : VarCtx}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) : (VarCtx_box V).1 ⊆ (VarCtx_dia x V hx).1 :=
  fun _ hp => Finset.mem_insert_of_mem hp

/-- A box-typed entry of `VarCtx_dia x V` lies in `VarCtx_box V` (the witness is dia-typed). -/
theorem dia_box_entry_in_box {x : VarSymb × VarType} {V : VarCtx}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) {p : VarSymb × VarType}
    (hp : p ∈ (VarCtx_dia x V hx).1) (hbox : VarType.isBox p.2 = true) :
    p ∈ (VarCtx_box V).1 := by
  rcases Finset.mem_insert.mp hp with heq | hbox_mem
  · subst heq; simp [VarType.isBox] at hbox
  · exact hbox_mem

/-- **Dia-term inner-context determinacy** (same witness): two diaterms of the same type in the same
    `W` sharing the ◇-witness `x` have the same inner context. Reduces to `boxterm_ctx_unique` on the
    box part (`VarCtx_dia` only adds the dia-typed witness). -/
theorem diaterm_ctx_unique {x : VarSymb × VarType} {V₁ V₂ W : VarCtx}
    {hx₁ : x.1 ∉ VarCtx_to_VarSymbs V₁} {hx₂ : x.1 ∉ VarCtx_to_VarSymbs V₂}
    (hsub₁ : (VarCtx_dia x V₁ hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V₁ hx₁).1)
    (hsub₂ : (VarCtx_dia x V₂ hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V₂ hx₂).1) :
    V₁ = V₂ :=
  boxterm_ctx_unique
    (fun _ hp => hsub₁ (VarCtx_box_subset_dia hx₁ hp))
    (fun p hp hbox => dia_box_entry_in_box hx₁ (h₁ p hp hbox) hbox)
    (fun _ hp => hsub₂ (VarCtx_box_subset_dia hx₂ hp))
    (fun p hp hbox => dia_box_entry_in_box hx₂ (h₂ p hp hbox) hbox)

/-- A `pair_elim`'s result context contains the product-typed variable `z` it eliminates.  Used to
    discharge the (unreachable) `pair_elim` cases in `eqRec`'s pair-free branch WITHOUT `subst`, so
    that `eqRec` still reduces definitionally on concrete inputs. -/
theorem pair_elim_ctx_mem {V pe_V : VarCtx} {v₁ v₂ : VarSymb × VarType}
    {z : VarSymb} {hz : z ∉ VarCtx_to_VarSymbs pe_V}
    (w₂eq : VarCtx_insert ⟨z, v₁.2.VTypeProd v₂.2⟩ pe_V hz = V) :
    (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∈ V.1 := by
  rw [← w₂eq]; exact Finset.mem_insert_self _ _

/-! ## The recursive extensional equality `eqRec` (STAGING, additive)

Dispatches on `V.firstPairVar` (mirroring `ctx_rest_MU`/`substVar_peel`): if the context has a
product var `z`, PEEL — unpair BOTH terms at `z` with shared combined-fresh `v1,v2`, recurse, and
re-pair via `WFF.pairElim`; otherwise the context is pair-free (so no term is a `pair_elim`) and we
reduce on the type — `.Var` base is the existing `WFF.eq` constructor (→ Var-only `primEq` after the
swap), `□`/`◇` via the determinacy casts (`boxterm`/`diaterm`), product = `∧` of components,
`VTypeOne` = `⊤`.  COMPLETE + axiom-clean (no `sorry`). -/
def eqRec {σ : Signature} :
    (V : VarCtx) → (S : VarType) → Term σ V S → Term σ V S → WFF σ V
  | V, S, t, s =>
    match hfp : V.firstPairVar with
    | some ⟨⟨z, V1, V2⟩, hzmem⟩ =>
        -- NEUTRAL PAIR-ELIM PEEL (mirrors `substVar_peel`): unpair BOTH terms at the first product
        -- var `z` using shared combined-fresh `v1,v2`, recurse, re-pair via `WFF.pairElim`.
        let V₀ := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩
        have hz_fresh : z ∉ VarCtx_to_VarSymbs V₀ := VarCtx_erase_fresh hzmem
        have V_eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V₀ hz_fresh = V :=
          VarCtx_insert_erase hzmem hz_fresh
        let avoid : Finset VarSymb :=
          VarCtx_to_VarSymbs V ∪ Term.boundVars t ∪ Term.boundVars s
        let v1 : VarSymb := VarSymb.fresh avoid
        have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem _
        let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
        have hv2_avoid_v1 : v2 ∉ insert v1 avoid := VarSymb.fresh_not_mem _
        have hv2_avoid : v2 ∉ avoid := fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
        have hv1v2 : v1 ≠ v2 := fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
        have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun _ h =>
          Finset.mem_union_left _ (Finset.mem_union_left _ h)
        have h_avoid_t : Term.boundVars t ⊆ avoid := fun _ h =>
          Finset.mem_union_left _ (Finset.mem_union_right _ h)
        have h_avoid_s : Term.boundVars s ⊆ avoid := fun _ h => Finset.mem_union_right _ h
        have hv1_V : v1 ∉ VarCtx_to_VarSymbs V := fun h => hv1_avoid (h_avoid_V h)
        have hv2_V : v2 ∉ VarCtx_to_VarSymbs V := fun h => hv2_avoid (h_avoid_V h)
        have hv1_V₀ : v1 ∉ VarCtx_to_VarSymbs V₀ :=
          fun h => hv1_V (VarCtx_to_VarSymbs_erase_subset h)
        have hv2_V₀ : v2 ∉ VarCtx_to_VarSymbs V₀ :=
          fun h => hv2_V (VarCtx_to_VarSymbs_erase_subset h)
        have hv1_nb_t : v1 ∉ Term.boundVars t := fun h => hv1_avoid (h_avoid_t h)
        have hv2_nb_t : v2 ∉ Term.boundVars t := fun h => hv2_avoid (h_avoid_t h)
        have hv1_nb_s : v1 ∉ Term.boundVars s := fun h => hv1_avoid (h_avoid_s h)
        have hv2_nb_s : v2 ∉ Term.boundVars s := fun h => hv2_avoid (h_avoid_s h)
        let two_comp : VarCtx := VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V₀ hv1_V₀ hv2_V₀ hv1v2
        let t' : Term σ two_comp S :=
          Term.unpair z V1 V2 v1 v2 V₀ V two_comp S hz_fresh hv1_V₀ hv2_V₀ hv1v2
            V_eq.symm rfl t hv1_nb_t hv2_nb_t
        let s' : Term σ two_comp S :=
          Term.unpair z V1 V2 v1 v2 V₀ V two_comp S hz_fresh hv1_V₀ hv2_V₀ hv1v2
            V_eq.symm rfl s hv1_nb_s hv2_nb_s
        V_eq ▸ WFF.pairElim ⟨v1, V1⟩ ⟨v2, V2⟩ z hv1_V₀ hv2_V₀ hv1v2 hz_fresh rfl rfl
          (eqRec two_comp S t' s')
    | none =>
        match S, t, s with
        | _, .pair_elim _ _ _ _ _ _ _ _ w₂eq _, _ =>
            (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
        | _, _, .pair_elim _ _ _ _ _ _ _ _ w₂eq _ =>
            (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
        | .Var, t, s => WFF.eq t s
        | .VTypeOne, _, _ => WFF.top
        | .VTypeProd A B, .pair a b, .pair c d => WFF.and (eqRec _ A a c) (eqRec _ B b d)
        | .VTypeBox A, .boxterm tt₁ hsub₁ h₁, .boxterm tt₂ hsub₂ h₂ =>
            WFF.box (eqRec _ A tt₁ ((boxterm_ctx_unique hsub₁ h₁ hsub₂ h₂).symm ▸ tt₂)) hsub₁ h₁
        | .VTypeDia A, .diaterm x₁ hx₁ tt₁ hsub₁ h₁, .diaterm x₂ hx₂ tt₂ hsub₂ h₂ => by
            by_cases h_x : x₁ = x₂
            · subst h_x
              have hV := diaterm_ctx_unique hsub₁ h₁ hsub₂ h₂
              subst hV
              exact WFF.box_x x₁ hx₁ hsub₁ h₁ (eqRec _ A tt₁ tt₂)
            · exact WFF.bot
termination_by V S _ _ => (sizeOf S, V.pairDepth)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right
       exact VarCtx.pairDepth_unpair_lt hzmem hv1_V₀ hv2_V₀ hv1v2)
    | (apply Prod.Lex.left; simp_wf; try omega)

/-! ### Extensionality equations (pair-free context): how `eqRec` computes.

In a pair-free context the `firstPairVar = none` branch fires and `eqRec` reduces on the type.
The `.Var`/`.VTypeOne`/`.VTypeProd` cases reduce via `simp only [eqRec, hfp]`; the `□`/`◇` cases
require reducing the nested dependent match past the (unreachable) `pair_elim` arms — a Lean
match-reduction issue still to be resolved (their RHS `eqRec` is at a different context, so plain
`simp only [eqRec]` loops). -/

theorem eqRec_var {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    (t s : Term σ V .Var) : eqRec V .Var t s = WFF.eq t s := by
  simp only [eqRec, hfp]

theorem eqRec_unit {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    (t s : Term σ V .VTypeOne) : eqRec V .VTypeOne t s = WFF.top := by
  simp only [eqRec, hfp]

theorem eqRec_prod {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none) {A B : VarType}
    (a c : Term σ V A) (b d : Term σ V B) :
    eqRec V (.VTypeProd A B) (.pair a b) (.pair c d)
      = WFF.and (eqRec V A a c) (eqRec V B b d) := by
  simp only [eqRec, hfp]
