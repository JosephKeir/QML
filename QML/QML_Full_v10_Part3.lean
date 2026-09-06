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

/-- The **box determinacy cast**: `boxterm_ctx_unique` says two same-typed boxterms in the same
    outer context share their inner context, so the second inner term transports into the first's.
    Given a NAME (rather than an inline `▸`) so that `eqRecCore`'s box arm and its extensionality
    equation are syntactically identical. -/
def boxCast {σ : Signature} {A : VarType} {V₁ V₂ W : VarCtx}
    (hsub₁ : (VarCtx_box V₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₁).1)
    (hsub₂ : (VarCtx_box V₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₂).1)
    (tt₂ : Term σ V₂ A) : Term σ V₁ A :=
  (boxterm_ctx_unique hsub₁ h₁ hsub₂ h₂).symm ▸ tt₂

/-- The **dia determinacy cast** (same ◇-witness): with `x₁ = x₂`, `diaterm_ctx_unique` gives
    `V₁ = V₂`, and the two inner contexts agree (the freshness fields are `Prop`s, so proof
    irrelevance makes them defeq).  Isolated in its own definition so that the `subst`s stay OUT of
    `eqRecCore`'s matcher. -/
def diaCast {σ : Signature} {A : VarType} {x₁ x₂ : VarSymb × VarType} {V₁ V₂ W : VarCtx}
    {hx₁ : x₁.1 ∉ VarCtx_to_VarSymbs V₁} {hx₂ : x₂.1 ∉ VarCtx_to_VarSymbs V₂}
    (hx : x₁ = x₂)
    (hsub₁ : (VarCtx_dia x₁ V₁ hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₁ V₁ hx₁).1)
    (hsub₂ : (VarCtx_dia x₂ V₂ hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₂ V₂ hx₂).1)
    (tt₂ : Term σ (VarCtx_insert x₂ V₂ hx₂) A) : Term σ (VarCtx_insert x₁ V₁ hx₁) A := by
  subst hx
  have hV := diaterm_ctx_unique hsub₁ h₁ hsub₂ h₂
  subst hV
  exact tt₂

/-! ## The recursive extensional equality `eqRec` (STAGING, additive)

Split into a **dispatcher** (`eqRec`) and a **pair-free core** (`eqRecCore`):

* `eqRec` dispatches on `V.firstPairVar` (mirroring `ctx_rest_MU`/`substVar_peel`): if the context
  has a product var `z`, PEEL — unpair BOTH terms at `z` with shared combined-fresh `v1,v2`,
  recurse, re-pair via `WFF.pairElim`; otherwise hand `hfp` to the core.
* `eqRecCore` takes `hfp : V.firstPairVar = none` as an ordinary argument and matches directly on
  `(S, t, s)`: `.Var` base is the existing `WFF.eq` constructor (→ Var-only `primEq` after the
  swap), `□`/`◇` via the determinacy casts, product = `∧` of components, `VTypeOne` = `⊤`.  The
  (unreachable) `pair_elim` arms come LAST so the constructive arms lead the matcher.

Why the split: with one catch-all arm the generated equation held the *entire* nested match, so
`simp only [eqRec]` re-exposed the peel branch (whose recursive call sits at a different context)
and looped.  `eqRecCore` has per-arm patterns, so `simp only [eqRecCore]` rewrites ONE case and
leaves the `eqRec` occurrences on the right alone — which is what makes the modal extensionality
equations extractable. -/
mutual

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
    | none => eqRecCore V S hfp t s
termination_by V S _ _ => (sizeOf S, V.pairDepth, 1)
decreasing_by
  all_goals
    apply Prod.Lex.right
    first
      | (apply Prod.Lex.left
         exact VarCtx.pairDepth_unpair_lt hzmem hv1_V₀ hv2_V₀ hv1v2)
      | (apply Prod.Lex.right; omega)

def eqRecCore {σ : Signature} :
    (V : VarCtx) → (S : VarType) → V.firstPairVar = none →
      Term σ V S → Term σ V S → WFF σ V
  | _, .Var,           _,   t,                     s                     => WFF.eq t s
  | _, .VTypeOne,      _,   _,                     _                     => WFF.top
  | _, .VTypeProd A B, _,   .pair a b,             .pair c d             =>
      WFF.and (eqRec _ A a c) (eqRec _ B b d)
  | _, .VTypeBox A,    _,   .boxterm tt₁ hsub₁ h₁, .boxterm tt₂ hsub₂ h₂ =>
      WFF.box (eqRec _ A tt₁ (boxCast hsub₁ h₁ hsub₂ h₂ tt₂)) hsub₁ h₁
  | _, .VTypeDia A,    _,   .diaterm x₁ hx₁ tt₁ hsub₁ h₁,
                            .diaterm x₂ hx₂ tt₂ hsub₂ h₂ =>
      if hx : x₁ = x₂ then
        WFF.box_x x₁ hx₁ hsub₁ h₁ (eqRec _ A tt₁ (diaCast hx hsub₁ h₁ hsub₂ h₂ tt₂))
      else WFF.bot
  -- The (unreachable) neutral `pair_elim` arms come LAST, so the constructive arms lead the
  -- matcher and reduce on concrete inputs.  A `pair_elim`'s context holds a product var,
  -- contradicting `hfp`.
  | _, _,              hfp, .pair_elim _ _ _ _ _ _ _ _ w₂eq _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
  | _, _,              hfp, _, .pair_elim _ _ _ _ _ _ _ _ w₂eq _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
termination_by V S _ _ _ => (sizeOf S, V.pairDepth, 0)
decreasing_by
  all_goals (apply Prod.Lex.left; simp_wf; try omega)

end

/-! ### Extensionality equations: how `eqRec` computes.

`eqRec_of_none` is the one-step dispatcher equation.  The `eqRecCore_*` equations then unfold ONE
constructive arm each — `simp only [eqRecCore]` leaves the `eqRec` occurrences on the right-hand
side alone, so nothing loops (which is exactly what the dispatcher/core split buys).  Composing
them yields the modal extensionality equations: **`box_ext` and `dia_ext` as defining equations.** -/

theorem eqRec_of_none {σ : Signature} {V : VarCtx} {S : VarType}
    (hfp : V.firstPairVar = none) (t s : Term σ V S) :
    eqRec V S t s = eqRecCore V S hfp t s := by
  unfold eqRec
  split
  all_goals first
    | rfl
    | (rename_i hsome; rw [hfp] at hsome; exact absurd hsome (by simp))

theorem eqRecCore_var {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    (t s : Term σ V .Var) : eqRecCore V .Var hfp t s = WFF.eq t s := by
  simp only [eqRecCore]

theorem eqRecCore_unit {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    (t s : Term σ V .VTypeOne) : eqRecCore V .VTypeOne hfp t s = WFF.top := by
  simp only [eqRecCore]

theorem eqRecCore_prod {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    {A B : VarType} (a c : Term σ V A) (b d : Term σ V B) :
    eqRecCore V (.VTypeProd A B) hfp (.pair a b) (.pair c d)
      = WFF.and (eqRec V A a c) (eqRec V B b d) := by
  simp only [eqRecCore]

/-- **`box_ext` as a defining equation**: necessary-object equality IS the `box` of the inner
    equality (the second inner term transported by the determinacy cast). -/
theorem eqRecCore_box {σ : Signature} {W : VarCtx} (hfp : W.firstPairVar = none)
    {A : VarType} {V₁ V₂ : VarCtx}
    (tt₁ : Term σ V₁ A) (tt₂ : Term σ V₂ A)
    (hsub₁ : (VarCtx_box V₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₁).1)
    (hsub₂ : (VarCtx_box V₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₂).1) :
    eqRecCore W (.VTypeBox A) hfp (.boxterm tt₁ hsub₁ h₁) (.boxterm tt₂ hsub₂ h₂)
      = WFF.box (eqRec V₁ A tt₁ (boxCast hsub₁ h₁ hsub₂ h₂ tt₂)) hsub₁ h₁ := by
  simp only [eqRecCore]

/-- **`dia_ext` as a defining equation** (same ◇-witness): possible-object equality IS the
    witnessed `box_x` of the inner equality. -/
theorem eqRecCore_dia_same {σ : Signature} {W : VarCtx} (hfp : W.firstPairVar = none)
    {A : VarType} {x₁ x₂ : VarSymb × VarType} {V₁ V₂ : VarCtx}
    {hx₁ : x₁.1 ∉ VarCtx_to_VarSymbs V₁} {hx₂ : x₂.1 ∉ VarCtx_to_VarSymbs V₂}
    (tt₁ : Term σ (VarCtx_insert x₁ V₁ hx₁) A) (tt₂ : Term σ (VarCtx_insert x₂ V₂ hx₂) A)
    (hsub₁ : (VarCtx_dia x₁ V₁ hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₁ V₁ hx₁).1)
    (hsub₂ : (VarCtx_dia x₂ V₂ hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₂ V₂ hx₂).1)
    (hx : x₁ = x₂) :
    eqRecCore W (.VTypeDia A) hfp (.diaterm x₁ hx₁ tt₁ hsub₁ h₁) (.diaterm x₂ hx₂ tt₂ hsub₂ h₂)
      = WFF.box_x x₁ hx₁ hsub₁ h₁
          (eqRec (VarCtx_insert x₁ V₁ hx₁) A tt₁ (diaCast hx hsub₁ h₁ hsub₂ h₂ tt₂)) := by
  simp only [eqRecCore, dif_pos hx]

/-- Different ◇-witnesses denote possibly-distinct possible objects, so they are not equated. -/
theorem eqRecCore_dia_ne {σ : Signature} {W : VarCtx} (hfp : W.firstPairVar = none)
    {A : VarType} {x₁ x₂ : VarSymb × VarType} {V₁ V₂ : VarCtx}
    {hx₁ : x₁.1 ∉ VarCtx_to_VarSymbs V₁} {hx₂ : x₂.1 ∉ VarCtx_to_VarSymbs V₂}
    (tt₁ : Term σ (VarCtx_insert x₁ V₁ hx₁) A) (tt₂ : Term σ (VarCtx_insert x₂ V₂ hx₂) A)
    (hsub₁ : (VarCtx_dia x₁ V₁ hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₁ V₁ hx₁).1)
    (hsub₂ : (VarCtx_dia x₂ V₂ hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₂ V₂ hx₂).1)
    (hx : ¬ x₁ = x₂) :
    eqRecCore W (.VTypeDia A) hfp (.diaterm x₁ hx₁ tt₁ hsub₁ h₁) (.diaterm x₂ hx₂ tt₂ hsub₂ h₂)
      = WFF.bot := by
  simp only [eqRecCore, dif_neg hx]

/-! ### The same equations at the `eqRec` level (pair-free context). -/

theorem eqRec_var {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    (t s : Term σ V .Var) : eqRec V .Var t s = WFF.eq t s := by
  rw [eqRec_of_none hfp, eqRecCore_var]

theorem eqRec_unit {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    (t s : Term σ V .VTypeOne) : eqRec V .VTypeOne t s = WFF.top := by
  rw [eqRec_of_none hfp, eqRecCore_unit]

theorem eqRec_prod {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    {A B : VarType} (a c : Term σ V A) (b d : Term σ V B) :
    eqRec V (.VTypeProd A B) (.pair a b) (.pair c d)
      = WFF.and (eqRec V A a c) (eqRec V B b d) := by
  rw [eqRec_of_none hfp, eqRecCore_prod]

/-- **`box_ext`, definitionally** — at the `eqRec` level. -/
theorem eqRec_box {σ : Signature} {W : VarCtx} (hfp : W.firstPairVar = none)
    {A : VarType} {V₁ V₂ : VarCtx}
    (tt₁ : Term σ V₁ A) (tt₂ : Term σ V₂ A)
    (hsub₁ : (VarCtx_box V₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₁).1)
    (hsub₂ : (VarCtx_box V₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₂).1) :
    eqRec W (.VTypeBox A) (.boxterm tt₁ hsub₁ h₁) (.boxterm tt₂ hsub₂ h₂)
      = WFF.box (eqRec V₁ A tt₁ (boxCast hsub₁ h₁ hsub₂ h₂ tt₂)) hsub₁ h₁ := by
  rw [eqRec_of_none hfp, eqRecCore_box]

/-- **`dia_ext`, definitionally** — at the `eqRec` level. -/
theorem eqRec_dia_same {σ : Signature} {W : VarCtx} (hfp : W.firstPairVar = none)
    {A : VarType} {x₁ x₂ : VarSymb × VarType} {V₁ V₂ : VarCtx}
    {hx₁ : x₁.1 ∉ VarCtx_to_VarSymbs V₁} {hx₂ : x₂.1 ∉ VarCtx_to_VarSymbs V₂}
    (tt₁ : Term σ (VarCtx_insert x₁ V₁ hx₁) A) (tt₂ : Term σ (VarCtx_insert x₂ V₂ hx₂) A)
    (hsub₁ : (VarCtx_dia x₁ V₁ hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₁ V₁ hx₁).1)
    (hsub₂ : (VarCtx_dia x₂ V₂ hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₂ V₂ hx₂).1)
    (hx : x₁ = x₂) :
    eqRec W (.VTypeDia A) (.diaterm x₁ hx₁ tt₁ hsub₁ h₁) (.diaterm x₂ hx₂ tt₂ hsub₂ h₂)
      = WFF.box_x x₁ hx₁ hsub₁ h₁
          (eqRec (VarCtx_insert x₁ V₁ hx₁) A tt₁ (diaCast hx hsub₁ h₁ hsub₂ h₂ tt₂)) := by
  rw [eqRec_of_none hfp, eqRecCore_dia_same _ _ _ _ _ _ _ hx]

