import QML.SubstitutionLemmas10

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
/-- The peel's final re-pairing, with the base context and component TYPES as EXPLICIT arguments.
    `eqRecPeel` ends in this, so its equation mentions `peelWrap` directly — which is what lets the
    congruence lemmas below unify against it.  (Going through `WFF.pairElim` raw, the base context
    and `W₁` are reachable only via `.2` projections of the binder pairs and via proof arguments,
    neither of which the unifier uses.) -/
def peelWrap {σ : Signature} (V₀ : VarCtx) (S1 S2 : VarType) (w1 w2 z : VarSymb)
    (hw1 : w1 ∉ VarCtx_to_VarSymbs V₀) (hw2 : w2 ∉ VarCtx_to_VarSymbs V₀) (hw : w1 ≠ w2)
    (hz : z ∉ VarCtx_to_VarSymbs V₀)
    (φ : WFF σ (VarCtx_insert_twice ⟨w1, S1⟩ ⟨w2, S2⟩ V₀ hw1 hw2 hw)) :
    WFF σ (VarCtx_insert ⟨z, S1.VTypeProd S2⟩ V₀ hz) :=
  WFF.pairElim ⟨w1, S1⟩ ⟨w2, S2⟩ z hw1 hw2 hw hz rfl rfl φ

mutual

def eqRec {σ : Signature} :
    (V : VarCtx) → (S : VarType) → Term σ V S → Term σ V S → WFF σ V
  | V, S, t, s =>
    match hfp : V.firstPairVar with
    | some ⟨⟨z, V1, V2⟩, hzmem⟩ =>
        eqRecPeelA V S z V1 V2 hzmem
          (VarCtx_to_VarSymbs V ∪ Term.boundVars t ∪ Term.boundVars s)
          (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)) t s
          (fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h))
          (fun _ h => Finset.mem_union_right _ h)
    | none => eqRecCore V S hfp t s
termination_by V S _ _ => (sizeOf S, V.pairDepth, 2)
decreasing_by all_goals (apply Prod.Lex.right; apply Prod.Lex.right; omega)

/-- The **neutral pair-elim peel**, PARAMETERISED over the `avoid` set used to pick the two fresh
    component names (with the three subset facts it must satisfy).  `eqRec` supplies the canonical
    `VarCtx_to_VarSymbs V ∪ boundVars t ∪ boundVars s`.

    Taking `avoid` as a parameter is what makes symmetry's peel case tractable: `eqRecPeelA … a b`
    and `eqRecPeelA … b a` at the SAME `avoid` unfold to literally the same `v1`, `v2`, `two_comp`
    and unpaired terms — those are functions of `avoid` alone — so no rewriting happens inside the
    unfolded peel at all.  The commutation of the two canonical avoid sets is then a rewrite on a
    small explicit ARGUMENT, done in `eqRec_symm` rather than inside the peel. -/
def eqRecPeelA {σ : Signature} (V : VarCtx) (S : VarType) (z : VarSymb) (V1 V2 : VarType)
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1)
    (avoid : Finset VarSymb) (h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid)
    (t s : Term σ V S)
    (h_avoid_t : Term.boundVars t ⊆ avoid) (h_avoid_s : Term.boundVars s ⊆ avoid) : WFF σ V :=
  let V₀ := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩
  have hz_fresh : z ∉ VarCtx_to_VarSymbs V₀ := VarCtx_erase_fresh hzmem
  have V_eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V₀ hz_fresh = V :=
    VarCtx_insert_erase hzmem hz_fresh
  let v1 : VarSymb := VarSymb.fresh avoid
  have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem _
  let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
  have hv2_avoid_v1 : v2 ∉ insert v1 avoid := VarSymb.fresh_not_mem _
  have hv2_avoid : v2 ∉ avoid := fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
  have hv1v2 : v1 ≠ v2 := fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
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
  V_eq ▸ peelWrap V₀ V1 V2 v1 v2 z hv1_V₀ hv2_V₀ hv1v2 hz_fresh (eqRec two_comp S t' s')
termination_by (sizeOf S, V.pairDepth, 1)
decreasing_by
  apply Prod.Lex.right
  apply Prod.Lex.left
  exact VarCtx.pairDepth_unpair_lt hzmem hv1_V₀ hv2_V₀ hv1v2

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


/-! ## Proof-theoretic infrastructure

Everything is stated at the EMPTY hypothesis set (`⊢ φ`) — that is what necessitation needs;
a general `Γ` follows by weakening. -/

/-- Transport a closed proof along a context identity. -/
def Proof.ctx_cast {σ : Signature} {V W : VarCtx} (h : V = W) {φ : WFF σ V}
    (p : Proof σ V ∅ φ) : Proof σ W ∅ (h ▸ φ) := by
  cases h; exact p

/-- **Necessitation**: `⊢ φ` gives `⊢ □φ` (`K_box` at the empty hypothesis set). -/
def Proof.nec {σ : Signature} {V W : VarCtx} {φ : WFF σ V}
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (p : Proof σ V ∅ φ) : Proof σ W ∅ (WFF.box φ hsub h) := by
  have hK := Proof.K_box hsub h p
  simpa [WFF.box_Finset] using hK

/-- The `pair_elim` rule at the empty hypothesis set. -/
def Proof.peElim {σ : Signature} {V W₁ W₂ : VarCtx} {φ : WFF σ W₁}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (p : Proof σ W₁ ∅ φ) :
    Proof σ W₂ ∅ (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ) := by
  have hP := Proof.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq p
  simpa [WFF.pairElim_Finset] using hP

/-- The `pair_elim` rule at the empty hypothesis set, in `peelWrap` shape. -/
def Proof.peelWrapI {σ : Signature} {V₀ : VarCtx} {S1 S2 : VarType} {w1 w2 z : VarSymb}
    {hw1 : w1 ∉ VarCtx_to_VarSymbs V₀} {hw2 : w2 ∉ VarCtx_to_VarSymbs V₀} {hw : w1 ≠ w2}
    {hz : z ∉ VarCtx_to_VarSymbs V₀}
    {φ : WFF σ (VarCtx_insert_twice ⟨w1, S1⟩ ⟨w2, S2⟩ V₀ hw1 hw2 hw)}
    (h : Proof σ (VarCtx_insert_twice ⟨w1, S1⟩ ⟨w2, S2⟩ V₀ hw1 hw2 hw) ∅ φ) :
    Proof σ (VarCtx_insert ⟨z, S1.VTypeProd S2⟩ V₀ hz) ∅
      (peelWrap V₀ S1 S2 w1 w2 z hw1 hw2 hw hz φ) :=
  Proof.peElim _ _ _ _ _ _ _ rfl rfl h

/-- **Witnessed necessitation**: `⊢ φ` gives `⊢ □_x φ`.  DERIVED (not primitive): from `⊢ φ` we get
    `¬φ ⊢ ⊥`, so `K_dia` gives `◇_x¬φ ⊢ ◇_x⊥`, `dia_bot` gives `◇_x¬φ ⊢ ⊥`, and `imp_intro` gives
    `⊢ ¬◇_x¬φ`, which is `□_x φ` by definition. -/
def Proof.necx {σ : Signature} {V W : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V} {φ : WFF σ (VarCtx_insert x V hx)}
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (p : Proof σ (VarCtx_insert x V hx) ∅ φ) :
    Proof σ W ∅ (WFF.box_x x hx hsub h φ) := by
  have hneg : Proof σ (VarCtx_insert x V hx) (∅ ∪ {neg φ}) WFF.bot :=
    Proof.imp_elim (Proof.ax (by simp)) (Proof.weak p)
  have hK := Proof.K_dia (Γ := (∅ : Finset (WFF σ V)))
    (Δ := (∅ : Finset (WFF σ (VarCtx_insert x V hx)))) x hx hsub h
    (by simpa [WFF.ctx_ext_Finset] using hneg)
  simp only [WFF.box_Finset, WFF.box_x_Finset, Finset.image_empty, Finset.empty_union] at hK
  have hbot := Proof.dia_bot x hx hsub h hK
  exact Proof.imp_intro (by simpa using hbot)

/-! ## Reflexivity of `eqRec`

`⊢ t ≐ t` for every term, at every type.  The modal cases are exactly the prototype's: the box case
is `necessitation` of the inner reflexivity, the ◇ case is witnessed necessitation. -/

/-- On the diagonal the box determinacy cast is the identity (the transported equality is a proof of
    `V₁ = V₁`, hence `rfl` by proof irrelevance). -/
theorem boxCast_self {σ : Signature} {A : VarType} {V W : VarCtx}
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (tt : Term σ V A) : boxCast hsub h hsub h tt = tt := rfl

/-- On the diagonal the dia determinacy cast is the identity. -/
theorem diaCast_self {σ : Signature} {A : VarType} {x : VarSymb × VarType} {V W : VarCtx}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V}
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (tt : Term σ (VarCtx_insert x V hx) A) : diaCast rfl hsub h hsub h tt = tt := rfl

/-- Reflexivity for the PEEL branch, given the induction hypothesis at strictly smaller
    `pairDepth` (which is where the peel recurses). -/
theorem eqRecPeelA_refl {σ : Signature} (V : VarCtx) (S : VarType) (z : VarSymb) (V1 V2 : VarType)
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1)
    (avoid : Finset VarSymb) (h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid)
    (t : Term σ V S) (h_avoid_t : Term.boundVars t ⊆ avoid)
    (IH : ∀ (W : VarCtx), W.pairDepth < V.pairDepth → ∀ (u : Term σ W S),
            Nonempty (Proof σ W ∅ (eqRec W S u u))) :
    Nonempty (Proof σ V ∅
      (eqRecPeelA V S z V1 V2 hzmem avoid h_avoid_V t t h_avoid_t h_avoid_t)) := by
  unfold eqRecPeelA
  obtain ⟨p⟩ := IH _ (VarCtx.pairDepth_unpair_lt hzmem _ _ _) _
  exact ⟨Proof.ctx_cast (VarCtx_insert_erase hzmem (VarCtx_erase_fresh hzmem)) (Proof.peelWrapI p)⟩
/-- Reflexivity for the PAIR-FREE CORE, given the induction hypothesis at strictly smaller type
    (which is where the core recurses). -/
theorem eqRecCore_refl {σ : Signature} : ∀ (V : VarCtx) (S : VarType)
    (hfp : V.firstPairVar = none) (t : Term σ V S),
    (∀ (A : VarType), sizeOf A < sizeOf S → ∀ (W : VarCtx) (u : Term σ W A),
        Nonempty (Proof σ W ∅ (eqRec W A u u))) →
    Nonempty (Proof σ V ∅ (eqRecCore V S hfp t t))
  | _, .Var, hfp, t, _ => by rw [eqRecCore_var]; exact ⟨Proof.eq_intro t⟩
  | _, .VTypeOne, hfp, t, _ => by rw [eqRecCore_unit]; exact ⟨Proof.top_intro⟩
  | V, .VTypeProd A B, hfp, .pair a b, IH => by
      rw [eqRecCore_prod]
      obtain ⟨pa⟩ := IH A (by simp; try omega) V a
      obtain ⟨pb⟩ := IH B (by simp; try omega) V b
      exact ⟨Proof.and_intro pa pb⟩
  | _, .VTypeBox A, hfp, .boxterm tt hsub h, IH => by
      rw [eqRecCore_box, boxCast_self]
      obtain ⟨p⟩ := IH A (by simp; try omega) _ tt
      exact ⟨Proof.nec hsub h p⟩
  | _, .VTypeDia A, hfp, .diaterm x hx tt hsub h, IH => by
      rw [eqRecCore_dia_same _ _ _ _ _ _ _ rfl, diaCast_self]
      obtain ⟨p⟩ := IH A (by simp; try omega) _ tt
      exact ⟨Proof.necx hsub h p⟩
  | _, _, hfp, .pair_elim _ _ _ _ _ _ _ _ w₂eq _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim

/-- **Reflexivity of the defined equality**: `⊢ t ≐ t`. -/
theorem eqRec_refl {σ : Signature} : ∀ (V : VarCtx) (S : VarType) (t : Term σ V S),
    Nonempty (Proof σ V ∅ (eqRec V S t t))
  | V, S, t => by
    unfold eqRec
    split
    · exact eqRecPeelA_refl _ _ _ _ _ _ _ _ t _ (fun W hW u => eqRec_refl W S u)
    · exact eqRecCore_refl _ _ _ t (fun A hA W u => eqRec_refl W A u)
termination_by V S _ => (sizeOf S, V.pairDepth)
decreasing_by
  · exact Prod.Lex.right _ hW
  · exact Prod.Lex.left _ _ hA


/-! ## Congruence / K-distribution infrastructure (for symmetry)

Symmetry must be an OBJECT implication `⊢ (a ≐ b) → (b ≐ a)`, because the modal cases transform the
equality UNDER a `□`/`□_x` — which needs K distribution, not just necessitation. -/

/-- Transport a proof along an equality of hypothesis sets. -/
def Proof.cast_ctx {σ : Signature} {V : VarCtx} {Γ Γ' : Finset (WFF σ V)} {φ : WFF σ V}
    (h : Γ = Γ') (p : Proof σ V Γ φ) : Proof σ V Γ' φ := h ▸ p

def Proof.impId {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {φ : WFF σ V} :
    Proof σ V Γ (φ.imp φ) :=
  Proof.imp_intro (Proof.ax (by simp))

/-- `∧`-congruence. -/
def Proof.congAnd {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {p p' q q' : WFF σ V}
    (hp : Proof σ V Γ (p.imp p')) (hq : Proof σ V Γ (q.imp q')) :
    Proof σ V Γ ((p.and q).imp (p'.and q')) := by
  have hax : Proof σ V (Γ ∪ {p.and q}) (p.and q) := Proof.ax (by simp)
  exact Proof.imp_intro (Proof.and_intro
    (Proof.imp_elim (Proof.weak hp) (Proof.and_elim_l hax))
    (Proof.imp_elim (Proof.weak hq) (Proof.and_elim_r hax)))

/-- **K distribution for `□`**: `⊢ φ → ψ` gives `⊢ □φ → □ψ` (`K_box` at a singleton context). -/
def Proof.congBox {σ : Signature} {V W : VarCtx} {φ ψ : WFF σ V}
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hφψ : Proof σ V ∅ (φ.imp ψ)) :
    Proof σ W ∅ ((WFF.box φ hsub h).imp (WFF.box ψ hsub h)) := by
  have h1 : Proof σ V (∅ ∪ {φ}) ψ := Proof.imp_elim (Proof.weak hφψ) (Proof.ax (by simp))
  have hK := Proof.K_box hsub h h1
  simp only [WFF.box_Finset, Finset.empty_union, Finset.image_singleton] at hK
  exact Proof.imp_intro (by simpa using hK)

/-- `pairElim`-congruence. -/
def Proof.congPairElim {σ : Signature} {V W₁ W₂ : VarCtx} {φ ψ : WFF σ W₁}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (hφψ : Proof σ W₁ ∅ (φ.imp ψ)) :
    Proof σ W₂ ∅ ((WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ).imp
                   (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ)) := by
  have h1 : Proof σ W₁ (∅ ∪ {φ}) ψ := Proof.imp_elim (Proof.weak hφψ) (Proof.ax (by simp))
  have hP := Proof.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq h1
  simp only [WFF.pairElim_Finset, Finset.empty_union, Finset.image_singleton] at hP
  exact Proof.imp_intro (by simpa using hP)

/-- **K distribution for the witnessed `□_x`**: `⊢ φ → ψ` gives `⊢ □_xφ → □_xψ`.  Derived from
    `K_dia`: `¬ψ ⊢ ¬φ`, hence `◇_x¬ψ ⊢ ◇_x¬φ`; since `□_xφ = ¬◇_x¬φ` that contradicts, giving
    `□_xφ, ◇_x¬ψ ⊢ ⊥`, and two `imp_intro`s finish. -/
def Proof.congBoxx {σ : Signature} {V W : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V} {φ ψ : WFF σ (VarCtx_insert x V hx)}
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (hφψ : Proof σ (VarCtx_insert x V hx) ∅ (φ.imp ψ)) :
    Proof σ W ∅ ((WFF.box_x x hx hsub h φ).imp (WFF.box_x x hx hsub h ψ)) := by
  have hnn : Proof σ (VarCtx_insert x V hx) (∅ ∪ {neg ψ}) (neg φ) :=
    Proof.imp_intro (Proof.imp_elim (Proof.ax (by simp))
      (Proof.imp_elim (Proof.weak (Proof.weak hφψ)) (Proof.ax (by simp))))
  have hK := Proof.K_dia (Γ := (∅ : Finset (WFF σ V)))
    (Δ := (∅ : Finset (WFF σ (VarCtx_insert x V hx)))) x hx hsub h
    (by simpa [WFF.ctx_ext_Finset] using hnn)
  simp only [WFF.box_Finset, WFF.box_x_Finset, Finset.image_empty, Finset.empty_union] at hK
  refine Proof.imp_intro (Proof.imp_intro ?_)
  have hd : Proof σ W ((∅ ∪ {WFF.box_x x hx hsub h φ}) ∪ {WFF.dia x hx (neg ψ) hsub h})
      (WFF.dia x hx (neg φ) hsub h) :=
    Proof.cast_ctx (by rw [Finset.empty_union]; exact Finset.union_comm _ _) (Proof.weak hK)
  have hbx : Proof σ W ((∅ ∪ {WFF.box_x x hx hsub h φ}) ∪ {WFF.dia x hx (neg ψ) hsub h})
      (WFF.box_x x hx hsub h φ) := Proof.ax (by simp)
  exact Proof.imp_elim hbx hd

/-! ## Symmetry of `eqRec`

Stated as an object implication `⊢ (a ≐ b) → (b ≐ a)`.  The `.Var` base is ATOMIC symmetry of the
primitive equality — a Leibniz derivation via `eq_elim` that needs the `substVar` reduction lemmas
(available for v9 in `SubstitutionLemmas9`, not yet ported to v10).  It is therefore taken as a
hypothesis, isolating that single dependency; everything structural and modal is proved here. -/

/-- Same-context box cast is the identity (proof irrelevance on the transported equality). -/
theorem boxCast_id {σ : Signature} {A : VarType} {V W : VarCtx}
    (hsub₁ : (VarCtx_box V).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hsub₂ : (VarCtx_box V).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (tt : Term σ V A) : boxCast hsub₁ h₁ hsub₂ h₂ tt = tt := rfl

/-- Same-context, same-witness dia cast is the identity. -/
theorem diaCast_id {σ : Signature} {A : VarType} {x : VarSymb × VarType} {V W : VarCtx}
    {hx₁ hx₂ : x.1 ∉ VarCtx_to_VarSymbs V}
    (hsub₁ : (VarCtx_dia x V hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx₁).1)
    (hsub₂ : (VarCtx_dia x V hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx₂).1)
    (tt : Term σ (VarCtx_insert x V hx₂) A) :
    diaCast rfl hsub₁ h₁ hsub₂ h₂ tt = tt := rfl

/-- **Symmetry for the pair-free core**, given atomic Var-symmetry and the IH at smaller type. -/
theorem eqRecCore_symm {σ : Signature}
    (hVarSymm : ∀ (W : VarCtx), W.firstPairVar = none → ∀ (u v : Term σ W .Var),
      Nonempty (Proof σ W ∅ ((WFF.eq u v).imp (WFF.eq v u)))) :
    ∀ (V : VarCtx) (S : VarType) (hfp : V.firstPairVar = none) (a b : Term σ V S),
    (∀ (A : VarType), sizeOf A < sizeOf S → ∀ (W : VarCtx) (u v : Term σ W A),
        Nonempty (Proof σ W ∅ ((eqRec W A u v).imp (eqRec W A v u)))) →
    Nonempty (Proof σ V ∅ ((eqRecCore V S hfp a b).imp (eqRecCore V S hfp b a)))
  | _, .Var, hfp, a, b, _ => by
      rw [eqRecCore_var, eqRecCore_var]; exact hVarSymm _ hfp a b
  | _, .VTypeOne, hfp, a, b, _ => by
      rw [eqRecCore_unit, eqRecCore_unit]; exact ⟨Proof.impId⟩
  | V, .VTypeProd A B, hfp, .pair a b, .pair c d, IH => by
      rw [eqRecCore_prod, eqRecCore_prod]
      obtain ⟨p1⟩ := IH A (by simp; try omega) V a c
      obtain ⟨p2⟩ := IH B (by simp; try omega) V b d
      exact ⟨Proof.congAnd p1 p2⟩
  | _, .VTypeBox A, hfp, .boxterm tt₁ hsub₁ h₁, .boxterm tt₂ hsub₂ h₂, IH => by
      have hV := boxterm_ctx_unique hsub₁ h₁ hsub₂ h₂
      subst hV
      rw [eqRecCore_box, eqRecCore_box, boxCast_id, boxCast_id]
      obtain ⟨p⟩ := IH A (by simp; try omega) _ tt₁ tt₂
      exact ⟨Proof.congBox hsub₁ h₁ p⟩
  | _, .VTypeDia A, hfp, .diaterm x₁ hx₁ tt₁ hsub₁ h₁, .diaterm x₂ hx₂ tt₂ hsub₂ h₂, IH => by
      by_cases hx : x₁ = x₂
      · subst hx
        have hV := diaterm_ctx_unique hsub₁ h₁ hsub₂ h₂
        subst hV
        rw [eqRecCore_dia_same _ _ _ _ _ _ _ rfl, eqRecCore_dia_same _ _ _ _ _ _ _ rfl,
            diaCast_id, diaCast_id]
        obtain ⟨p⟩ := IH A (by simp; try omega) _ tt₁ tt₂
        exact ⟨Proof.congBoxx hsub₁ h₁ p⟩
      · rw [eqRecCore_dia_ne _ _ _ _ _ _ _ hx,
            eqRecCore_dia_ne _ _ _ _ _ _ _ (fun hh => hx hh.symm)]
        exact ⟨Proof.impId⟩
  | _, _, hfp, .pair_elim _ _ _ _ _ _ _ _ w₂eq _, _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
  | _, _, hfp, _, .pair_elim _ _ _ _ _ _ _ _ w₂eq _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim

/-- **Symmetry at the `eqRec` level, for a pair-free context** (superseded by `eqRec_symm`, which
    covers every context; kept because it is the form the core case is stated in). -/
theorem eqRec_symm_of_none {σ : Signature}
    (hVarSymm : ∀ (W : VarCtx), W.firstPairVar = none → ∀ (u v : Term σ W .Var),
      Nonempty (Proof σ W ∅ ((WFF.eq u v).imp (WFF.eq v u))))
    (V : VarCtx) (S : VarType) (hfp : V.firstPairVar = none) (a b : Term σ V S)
    (IH : ∀ (A : VarType), sizeOf A < sizeOf S → ∀ (W : VarCtx) (u v : Term σ W A),
        Nonempty (Proof σ W ∅ ((eqRec W A u v).imp (eqRec W A v u)))) :
    Nonempty (Proof σ V ∅ ((eqRec V S a b).imp (eqRec V S b a))) := by
  rw [eqRec_of_none hfp, eqRec_of_none hfp]
  exact eqRecCore_symm hVarSymm V S hfp a b IH


/-! ## Atomic (`.Var`) symmetry — discharging `eqRecCore_symm`'s hypothesis

The Leibniz derivation via `eq_elim` with `φ := (x ≐ a↑)`, which needs the `substVar` reduction
lemmas (now available for v10 via `SubstitutionLemmas10`).  They carry a pair-free side condition
on the EXTENDED context, which follows from the pair-free context we are already in. -/

/-- Adding a `.Var`-typed entry preserves pair-freeness: a product-typed entry of the extension
    cannot be the new `.Var` entry, so it already lay in `V`. -/
theorem firstPairVar_insert_Var {V : VarCtx} {x : VarSymb} (hx : x ∉ VarCtx_to_VarSymbs V)
    (hfp : V.firstPairVar = none) :
    (VarCtx_insert ⟨x, VarType.Var⟩ V hx).firstPairVar = none := by
  cases h : (VarCtx_insert ⟨x, VarType.Var⟩ V hx).firstPairVar with
  | none => rfl
  | some p =>
      exfalso
      obtain ⟨⟨z, V1, V2⟩, hzmem⟩ := p
      rcases Finset.mem_insert.mp hzmem with heq | hmem
      · exact VarType.noConfusion (congrArg Prod.snd heq)
      · exact VarCtx.firstPairVar_none_no_pair hfp hmem

/-- Public re-derivation of the (private) `Term.substVar_eq_ctx_rest`: for a pair-free extended
    context, `substVar` coincides with `ctx_rest`. -/
theorem Term.substVar_eq_ctx_rest' {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S')
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) :
    Term.substVar hx s t = Term.ctx_rest hx hpf s t := by
  simp only [Term.substVar]
  conv_lhs => unfold Term.ctx_rest_MU
  split
  · rfl
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

/-- **Atomic symmetry of the primitive equality** (Leibniz via `eq_elim`, `φ := (x ≐ a↑)`):
    `substVar a φ = (a ≐ a)` is `eq_intro`, and `eq_elim` transports it along `a ≐ b` to
    `substVar b φ = (b ≐ a)`. -/
def Proof.eqSymmAtomic {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)}
    (hfp : V.firstPairVar = none) (a b : Term σ V .Var)
    (p : Proof σ V Γ (WFF.eq a b)) : Proof σ V Γ (WFF.eq b a) := by
  set x : VarSymb := VarSymb.fresh (VarCtx_to_VarSymbs V) with hxdef
  have hx : x ∉ VarCtx_to_VarSymbs V := VarSymb.fresh_not_mem _
  have hpf : (VarCtx_insert ⟨x, VarType.Var⟩ V hx).firstPairVar = none :=
    firstPairVar_insert_Var hx hfp
  set xv : VarSymb × VarType := ⟨x, VarType.Var⟩ with hxv
  have hxmem : (⟨x, VarType.Var⟩ : VarSymb × VarType) ∈ (VarCtx_insert xv V hx).1 :=
    Finset.mem_insert_self _ _
  set φ : WFF σ (VarCtx_insert xv V hx) :=
    WFF.eq (Term.var ⟨x, hxmem⟩) (Term.ctx_ext xv hx a) with hφ
  have key : ∀ (c : Term σ V .Var), WFF.substVar hx c φ = WFF.eq c a := by
    intro c
    rw [hφ, WFF.substVar_eq hx c hpf]
    congr 1
    · rw [Term.substVar_var hx c hpf x hxmem, dif_pos rfl]
    · rw [Term.substVar_eq_ctx_rest' hx c (Term.ctx_ext xv hx a) hpf]
      exact Term.ctx_rest_ctx_ext hx hpf c a
  have pa : Proof σ V Γ (WFF.substVar hx a φ) := (key a).symm ▸ Proof.eq_intro a
  have pb : Proof σ V Γ (WFF.substVar hx b φ) := Proof.eq_elim xv hx a b p pa
  exact (key b) ▸ pb

/-- Atomic symmetry in the object-implication form `eqRecCore_symm` wants. -/
theorem varSymm {σ : Signature} (W : VarCtx) (hfp : W.firstPairVar = none)
    (u v : Term σ W .Var) :
    Nonempty (Proof σ W ∅ ((WFF.eq u v).imp (WFF.eq v u))) :=
  ⟨Proof.imp_intro (Proof.eqSymmAtomic hfp u v (Proof.ax (by simp)))⟩

/-- **Symmetry for a pair-free context, with the atomic base discharged.**  No hypotheses beyond
    the induction hypothesis at smaller type. -/
theorem eqRec_symm_of_none' {σ : Signature}
    (V : VarCtx) (S : VarType) (hfp : V.firstPairVar = none) (a b : Term σ V S)
    (IH : ∀ (A : VarType), sizeOf A < sizeOf S → ∀ (W : VarCtx) (u v : Term σ W A),
        Nonempty (Proof σ W ∅ ((eqRec W A u v).imp (eqRec W A v u)))) :
    Nonempty (Proof σ V ∅ ((eqRec V S a b).imp (eqRec V S b a))) :=
  eqRec_symm_of_none varSymm V S hfp a b IH


/-! ## Symmetry: the peel case

`eqRecPeel … a b` and `eqRecPeel … b a` choose fresh names from `… ∪ boundVars a ∪ boundVars b`
and `… ∪ boundVars b ∪ boundVars a`.  Those differ only by `Finset.union_right_comm`, and rewriting
ALL their occurrences simultaneously is motive-correct (each occurrence feeds either
`VarSymb.fresh avoid` or a proof about `avoid`), so the two sides end up with literally the same
fresh names, `two_comp`, and unpaired terms — after which `congPairElim` of the IH finishes. -/

/-- Context transport distributes over implication. -/
theorem WFF_ctx_cast_imp {σ : Signature} {V W : VarCtx} (h : V = W) (φ ψ : WFF σ V) :
    h ▸ (φ.imp ψ) = (h ▸ φ).imp (h ▸ ψ) := by cases h; rfl

/-- `pairElim`-congruence in exactly the shape the peel produces.  Stating the conclusion's context
    as `VarCtx_insert ⟨z, S1.VTypeProd S2⟩ V₀ hz` — with the component types as direct parameters
    rather than as `.2` projections of the binder pairs — is what lets `apply` unify it against the
    unfolded peel. -/
def Proof.congPeel {σ : Signature} {V₀ : VarCtx} {S1 S2 : VarType} {w1 w2 z : VarSymb}
    {hw1 : w1 ∉ VarCtx_to_VarSymbs V₀} {hw2 : w2 ∉ VarCtx_to_VarSymbs V₀} {hw : w1 ≠ w2}
    {hz : z ∉ VarCtx_to_VarSymbs V₀}
    {φ ψ : WFF σ (VarCtx_insert_twice ⟨w1, S1⟩ ⟨w2, S2⟩ V₀ hw1 hw2 hw)}
    (h : Proof σ (VarCtx_insert_twice ⟨w1, S1⟩ ⟨w2, S2⟩ V₀ hw1 hw2 hw) ∅ (φ.imp ψ)) :
    Proof σ (VarCtx_insert ⟨z, S1.VTypeProd S2⟩ V₀ hz) ∅
      ((peelWrap V₀ S1 S2 w1 w2 z hw1 hw2 hw hz φ).imp
        (peelWrap V₀ S1 S2 w1 w2 z hw1 hw2 hw hz ψ)) :=
  Proof.congPairElim _ _ _ _ _ _ _ rfl rfl h


/-! ## Leibniz

The statement to derive is, for a pair-free context,

  `⊢ (a ≐ b) → (φ[a] → φ[b])`,   where `φ[t] := WFF.substVar hx t φ`

for `a b : Term σ V S` at EVERY type `S`, using only the `.Var`-level `eq_elim`.  At `.Var` the
defined equality IS the primitive equality, so Leibniz is exactly `eq_elim` repackaged; the content
of the reform is that the higher types are then derivable rather than primitive. -/

/-- **Leibniz at the atomic type.**  `eqRec V .Var a b` is the primitive `WFF.eq a b`, so this is
    `eq_elim` packaged as an object implication. -/
theorem eqRec_leibniz_Var {σ : Signature} {V : VarCtx} (hfp : V.firstPairVar = none)
    (x : VarSymb) (hx : x ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨x, VarType.Var⟩ V hx)) (a b : Term σ V .Var) :
    Nonempty (Proof σ V ∅ ((eqRec V .Var a b).imp
      ((WFF.substVar hx a φ).imp (WFF.substVar hx b φ)))) := by
  rw [eqRec_var hfp]
  exact ⟨Proof.imp_intro (Proof.imp_intro
    (Proof.eq_elim ⟨x, VarType.Var⟩ hx a b (Proof.ax (by simp)) (Proof.ax (by simp))))⟩



theorem eqRecPeelA_symm {σ : Signature} (V : VarCtx) (S : VarType) (z : VarSymb) (V1 V2 : VarType)
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1)
    (avoid : Finset VarSymb) (h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid)
    (a b : Term σ V S) (ha : Term.boundVars a ⊆ avoid) (hb : Term.boundVars b ⊆ avoid)
    (IH : ∀ (W : VarCtx), W.pairDepth < V.pairDepth → ∀ (u v : Term σ W S),
            Nonempty (Proof σ W ∅ ((eqRec W S u v).imp (eqRec W S v u)))) :
    Nonempty (Proof σ V ∅
      ((eqRecPeelA V S z V1 V2 hzmem avoid h_avoid_V a b ha hb).imp
       (eqRecPeelA V S z V1 V2 hzmem avoid h_avoid_V b a hb ha))) := by
  unfold eqRecPeelA
  rw [← WFF_ctx_cast_imp]
  refine ⟨Proof.ctx_cast (VarCtx_insert_erase hzmem (VarCtx_erase_fresh hzmem)) ?_⟩
  apply Proof.congPeel
  exact (IH _ (VarCtx.pairDepth_unpair_lt hzmem _ _ _) _ _).some

/-- **Symmetry of the defined equality**: `⊢ (a ≐ b) → (b ≐ a)`, at every type and every context. -/
theorem eqRec_symm {σ : Signature} : ∀ (V : VarCtx) (S : VarType) (a b : Term σ V S),
    Nonempty (Proof σ V ∅ ((eqRec V S a b).imp (eqRec V S b a)))
  | V, S, a, b => by
    unfold eqRec
    split
    · have h : VarCtx_to_VarSymbs V ∪ Term.boundVars b ∪ Term.boundVars a
             = VarCtx_to_VarSymbs V ∪ Term.boundVars a ∪ Term.boundVars b :=
        Finset.union_right_comm _ _ _
      simp only [h]
      exact eqRecPeelA_symm _ _ _ _ _ _ _ _ a b _ _ (fun W hW u v => eqRec_symm W S u v)
    · exact eqRecCore_symm varSymm _ _ _ a b (fun A hA W u v => eqRec_symm W A u v)
termination_by V S _ _ => (sizeOf S, V.pairDepth)
decreasing_by
  · exact Prod.Lex.right _ hW
  · exact Prod.Lex.left _ _ hA


/-! ### Propositional congruences (for Leibniz's easy cases) -/
/-! ### Propositional congruences (for Leibniz's easy cases).

All stated at an ARBITRARY hypothesis set `Γ` — Leibniz carries the equation `a ≐ b` as a
hypothesis rather than as an antecedent (that is the form `K_box`/`K_dia` transport through a
modality), so its connective cases need these at `Γ = {a ≐ b}`. -/

/-- `∨`-congruence. -/
def Proof.congOr {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {p p' q q' : WFF σ V}
    (hp : Proof σ V Γ (p.imp p')) (hq : Proof σ V Γ (q.imp q')) :
    Proof σ V Γ ((p.or q).imp (p'.or q')) := by
  have hdisj : Proof σ V (Γ ∪ {p.or q}) (p.or q) := Proof.ax (by simp)
  refine Proof.imp_intro (Proof.or_elim hdisj ?_ ?_)
  · have hax : Proof σ V ((Γ ∪ {p.or q}) ∪ {p}) p := Proof.ax (by simp)
    have hpw : Proof σ V ((Γ ∪ {p.or q}) ∪ {p}) (p.imp p') := Proof.weak (Proof.weak hp)
    exact Proof.or_intro_l (Proof.imp_elim hpw hax)
  · have hax : Proof σ V ((Γ ∪ {p.or q}) ∪ {q}) q := Proof.ax (by simp)
    have hqw : Proof σ V ((Γ ∪ {p.or q}) ∪ {q}) (q.imp q') := Proof.weak (Proof.weak hq)
    exact Proof.or_intro_r (Proof.imp_elim hqw hax)

/-- `→`-congruence.  Note it is CONTRAVARIANT in the antecedent — which is exactly why Leibniz's
    `imp` case needs symmetry (to get the reversed direction on the antecedent). -/
def Proof.congImp {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {p p' q q' : WFF σ V}
    (hp : Proof σ V Γ (p'.imp p)) (hq : Proof σ V Γ (q.imp q')) :
    Proof σ V Γ ((p.imp q).imp (p'.imp q')) := by
  refine Proof.imp_intro (Proof.imp_intro ?_)
  have hp_ : Proof σ V ((Γ ∪ {p.imp q}) ∪ {p'}) p :=
    Proof.imp_elim (Proof.weak (Proof.weak hp)) (Proof.ax (by simp))
  have hq_ : Proof σ V ((Γ ∪ {p.imp q}) ∪ {p'}) q :=
    Proof.imp_elim (Proof.ax (by simp)) hp_
  exact Proof.imp_elim (Proof.weak (Proof.weak hq)) hq_

/-- Cut. -/
def Proof.cut {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {φ ψ : WFF σ V}
    (h1 : Proof σ V Γ φ) (h2 : Proof σ V (Γ ∪ {φ}) ψ) : Proof σ V Γ ψ :=
  Proof.imp_elim (Proof.imp_intro h2) h1
/-- Replace the single hypothesis `φ` by anything that entails it. -/
def Proof.reHyp {σ : Signature} {V : VarCtx} {φ φ' ψ : WFF σ V}
    (h : Proof σ V ∅ (φ'.imp φ)) (p : Proof σ V {φ} ψ) : Proof σ V {φ'} ψ := by
  have hax : Proof σ V {φ'} φ' := Proof.ax (by simp)
  have hw : Proof σ V {φ'} (φ'.imp φ) := Proof.cast_ctx (by simp) (Proof.weak (ψ := φ') h)
  have hφ : Proof σ V {φ'} φ := Proof.imp_elim hw hax
  have hi : Proof σ V ∅ (φ.imp ψ) := Proof.imp_intro (Proof.cast_ctx (by simp) p)
  exact Proof.imp_elim (Proof.cast_ctx (by simp) (Proof.weak (ψ := φ') hi)) hφ

/-! ## Leibniz substitution for the defined equality

With equality DEFINED (`eqRec`), the primitive `eq_elim` survives only at `.Var`.  Its full
strength has to come back as a THEOREM: `a ≐ b ⊢ φ[a] → φ[b]` at every type.  The induction is on
the shape of `φ`, not on the type — connectives recurse, quantifiers pass through, and the modal
constructors are where the defining equations `box_ext`/`dia_ext` are consumed.

`Leib` states one instance.  The equation sits in the HYPOTHESIS SET rather than as an antecedent:
that is the form `K_box`/`K_dia` transport through a modality, so the box case can hand the inner
instance straight to `K_box`. -/

/-- Leibniz's law for the single formula `φ`: from `a ≐ b`, `φ[a] → φ[b]`. -/
def Leib {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    (hx : x ∉ VarCtx_to_VarSymbs V) (a b : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) : Prop :=
  Nonempty (Proof σ V {eqRec V S a b} ((WFF.substVar hx a φ).imp (WFF.substVar hx b φ)))

/-! ### Propositional cases.

All four are immediate: the `substVar` reduction lemma splits both sides, and the matching
congruence closes the goal at `Γ = {a ≐ b}`.  Only `imp` is not a plain recursion — being
contravariant in its antecedent it needs the REVERSED instance, which `eqRec_symm` supplies. -/

theorem Leib.top {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V} (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (a b : Term σ V S) : Leib hx a b WFF.top := by
  unfold Leib
  rw [WFF.substVar_top hx a hpf, WFF.substVar_top hx b hpf]
  exact ⟨Proof.impId⟩

theorem Leib.bot {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V} (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (a b : Term σ V S) : Leib hx a b WFF.bot := by
  unfold Leib
  rw [WFF.substVar_bot hx a hpf, WFF.substVar_bot hx b hpf]
  exact ⟨Proof.impId⟩

theorem Leib.and {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V} (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    {a b : Term σ V S} {φ ψ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)}
    (ihφ : Leib hx a b φ) (ihψ : Leib hx a b ψ) : Leib hx a b (φ.and ψ) := by
  unfold Leib at *
  rw [WFF.substVar_and hx a hpf φ ψ, WFF.substVar_and hx b hpf φ ψ]
  exact ⟨Proof.congAnd ihφ.some ihψ.some⟩

theorem Leib.or {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V} (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    {a b : Term σ V S} {φ ψ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)}
    (ihφ : Leib hx a b φ) (ihψ : Leib hx a b ψ) : Leib hx a b (φ.or ψ) := by
  unfold Leib at *
  rw [WFF.substVar_or hx a hpf φ ψ, WFF.substVar_or hx b hpf φ ψ]
  exact ⟨Proof.congOr ihφ.some ihψ.some⟩

/-- The `→` case.  Contravariance means the antecedent needs the instance the OTHER way round;
    `eqRec_symm` converts the hypothesis `a ≐ b` into the `b ≐ a` that instance expects. -/
theorem Leib.imp {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V} (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    {a b : Term σ V S} {φ ψ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)}
    (ihφ : Leib hx b a φ) (ihψ : Leib hx a b ψ) : Leib hx a b (φ.imp ψ) := by
  unfold Leib at *
  rw [WFF.substVar_imp hx a hpf φ ψ, WFF.substVar_imp hx b hpf φ ψ]
  exact ⟨Proof.congImp (Proof.reHyp (eqRec_symm V S a b).some ihφ.some) ihψ.some⟩

/-! ### Modal congruences at an arbitrary hypothesis set.

The `∅` versions above suffice for symmetry, where the equation is an antecedent.  Leibniz keeps
the equation in `Γ`, and this is precisely the form `K_box`/`K_dia` were built for: they carry a
hypothesis SET through the modality, turning the inner equation into `□(t₁ ≐ t₂)` — which, by the
defining equation `eqRec_box`, IS the outer equation at `□A`.  So the box case of Leibniz is just
`K_box` applied to the inner instance. -/

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
      simp [WFF.box_Finset, Finset.image_union]] at hK
  exact Proof.imp_intro hK

/-- `Δ ⊢ φ → ψ` gives `□_xΔ ⊢ □_xφ → □_xψ`. -/
def Proof.congBoxxG {σ : Signature} {V W : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V} {Δ : Finset (WFF σ (VarCtx_insert x V hx))}
    {φ ψ : WFF σ (VarCtx_insert x V hx)}
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (hφψ : Proof σ (VarCtx_insert x V hx) Δ (φ.imp ψ)) :
    Proof σ W (WFF.box_x_Finset x hx hsub h Δ)
      ((WFF.box_x x hx hsub h φ).imp (WFF.box_x x hx hsub h ψ)) := by
  -- `¬ψ ⊢ ¬φ` in the inner context, then `K_dia` with `Γ = ∅` and the given `Δ`.
  have hnn : Proof σ (VarCtx_insert x V hx) (Δ ∪ {neg ψ}) (neg φ) :=
    Proof.imp_intro (Proof.imp_elim (Proof.ax (by simp))
      (Proof.imp_elim (Proof.weak (Proof.weak hφψ)) (Proof.ax (by simp))))
  have hK := Proof.K_dia (Γ := (∅ : Finset (WFF σ V))) (Δ := Δ) x hx hsub h
    (by simpa [WFF.ctx_ext_Finset] using hnn)
  simp only [WFF.box_Finset, Finset.image_empty, Finset.empty_union] at hK
  refine Proof.imp_intro (Proof.imp_intro ?_)
  have hd : Proof σ W ((WFF.box_x_Finset x hx hsub h Δ ∪ {WFF.box_x x hx hsub h φ})
      ∪ {WFF.dia x hx (neg ψ) hsub h}) (WFF.dia x hx (neg φ) hsub h) :=
    Proof.cast_ctx (by
      rw [Finset.union_right_comm]) (Proof.weak (ψ := WFF.box_x x hx hsub h φ) hK)
  have hbx : Proof σ W ((WFF.box_x_Finset x hx hsub h Δ ∪ {WFF.box_x x hx hsub h φ})
      ∪ {WFF.dia x hx (neg ψ) hsub h}) (WFF.box_x x hx hsub h φ) := Proof.ax (by simp)
  exact Proof.imp_elim hbx hd

/-! ### The `box` case — where `box_ext` is consumed.

This is the case the whole reform is aimed at.  `eqRec` at `□A` IS `□` of the inner equality
(`eqRec_box`), and `substVar` of a `boxterm` into a `box` IS `box` of the inner substitution
(`substVar_boxterm_box_gen_base`), with the substituted variable UNBOXED inside.  So both sides
of the goal are `□` of the inner Leibniz instance, and `K_box` — in its hypothesis-set form
`congBoxG` — carries the inner instance out.  The recursion drops both the formula (`χ < □χ`) and
the type (`A < □A`).

The two boxterms share one inner context and one pair of side conditions; that is not a
restriction but `boxterm_ctx_unique`, which forces it. -/

theorem Leib.box {σ : Signature} {x : VarSymb × VarType} {V W : VarCtx}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (hnbe : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hpfW : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar = none)
    (hpf : W.firstPairVar = none)
    (t s : Term σ V x.2) (χ : WFF σ (VarCtx_insert x V hx))
    (ih : Leib hx t s χ) :
    Leib hxW (Term.boxterm t hsub hnbe) (Term.boxterm s hsub hnbe)
      (WFF.box χ (box_hsub_insert hx hxW hsub) (box_extras_insert hx hxW hnbe)) := by
  unfold Leib at ih ⊢
  rw [WFF.substVar_boxterm_box_gen_base hx hxW hsub hnbe hpfW t χ,
      WFF.substVar_boxterm_box_gen_base hx hxW hsub hnbe hpfW s χ,
      eqRec_box hpf t s hsub hnbe hsub hnbe, boxCast_id]
  refine ⟨Proof.cast_ctx ?_ (Proof.congBoxG hsub hnbe ih.some)⟩
  simp [WFF.box_Finset]

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

/-! ### The `dia` case — modal β, and where `dia_ext` is consumed.

The `◇` analogue of `Leib.box`, but genuinely different in shape: the substituted variable IS the
`◇`-binder's witness, so `substVar` performs a modal-β reduction — the outer `◇_xv` binder is
REPLACED by the substituted diaterm's own witness `xv_s`, and the body is reordered accordingly
(`WFF.dia_arm_case3_reorder`).  Meanwhile `eqRec` at `◇A` is a `□_xv_s` of the inner equality, and
`□_xv_s` is exactly `K_dia`'s witnessed-hypothesis slot.  So the two fit together: `congDiaG`
carries the inner instance out through the `◇`.

Both diaterms carry the SAME witness `xv_s` — for different witnesses `eqRec` is `⊥`
(`eqRecCore_dia_ne`) and the instance is vacuous. -/

theorem Leib.dia {σ : Signature} {V_inner W : VarCtx}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (hxW : xv.1 ∉ VarCtx_to_VarSymbs W)
    (xv_s : VarSymb × VarType) (hxv_s : xv_s.1 ∉ VarCtx_to_VarSymbs V_inner)
    (h_ne : xv.1 ≠ xv_s.1)
    (tt tt' : Term σ (VarCtx_insert xv_s V_inner hxv_s) xv.2)
    (hsub_s : (VarCtx_dia xv_s V_inner hxv_s).1 ⊆ W.1)
    (h_s : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv_s V_inner hxv_s).1)
    (hpfW : (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ W hxW).firstPairVar = none)
    (hpf : W.firstPairVar = none)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1
              ⊆ (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ W hxW).1)
    (hextras : ∀ p ∈ (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ W hxW).1,
                VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (ih : Leib (WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s h_ne rfl ψ).1 tt tt'
              (WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s h_ne rfl ψ).2.1) :
    Leib hxW (Term.diaterm xv_s hxv_s tt hsub_s h_s)
             (Term.diaterm xv_s hxv_s tt' hsub_s h_s)
      (WFF.dia xv hxv ψ hsub hextras) := by
  unfold Leib at ih ⊢
  rw [WFF.substVar_diaterm_dia_gen_base xv hxv hxW xv_s hxv_s h_ne tt hsub_s h_s hpfW
        ψ hsub hextras,
      WFF.substVar_diaterm_dia_gen_base xv hxv hxW xv_s hxv_s h_ne tt' hsub_s h_s hpfW
        ψ hsub hextras,
      eqRec_dia_same hpf tt tt' hsub_s h_s hsub_s h_s rfl, diaCast_id]
  refine ⟨Proof.cast_ctx ?_ (Proof.congDiaG hsub_s h_s ih.some)⟩
  simp [WFF.box_x_Finset]

/-! ## Reflecting a free variable back into a term (`Term.eta`)

`Term.var` is deliberately `.Var`-only, so a free variable of higher type has no *immediate* term
form.  It does have a canonical one, built by recursion on the TYPE — a product variable is
destructured and repaired, a `□`/`◇` variable is re-wrapped with itself as the inner (resp.
witness) variable.  This is what `all_elim` needs in order to instantiate a quantifier at a fresh
free variable, which in turn is what Leibniz's `all`/`ex` cases need:

    assume `P → Q` and `∀x:A. P`;  extend the context by a fresh `y : A`;
    `all_elim` at `η y` gives `P`;  modus ponens gives `Q`;  `all_intro` on `y` gives `∀y:A. Q`.

Note this does NOT say every bound variable has a term — only every FREE one.

The `□`/`◇` cases need the inverse of `VarCtx_box`: the inner context a `boxterm` in ambient `W`
must have, which by `boxterm_ctx_unique` is forced to be exactly `W`'s box-typed part, unboxed. -/
/-- Strip one `□`. -/
def VarType.debox : VarType → VarType
  | .VTypeBox S => S
  | S           => S

@[simp] theorem VarType.debox_box (S : VarType) : (VarType.VTypeBox S).debox = S := rfl

def VarCtx_unbox (W : VarCtx) : VarCtx := by
  refine ⟨(W.1.filter (fun p => p.2.isBox)).image
            (fun p => (⟨p.1, p.2.debox⟩ : VarSymb × VarType)), ?_⟩
  intro v hv w hw heq
  rcases Finset.mem_image.mp hv with ⟨⟨av, aS⟩, hav, rfl⟩
  rcases Finset.mem_image.mp hw with ⟨⟨bv, bS⟩, hbw, rfl⟩
  exact congrArg VarType.debox
    (W.2 ⟨av, aS⟩ (Finset.mem_filter.mp hav).1 ⟨bv, bS⟩ (Finset.mem_filter.mp hbw).1 heq)

theorem mem_VarCtx_unbox {W : VarCtx} {v : VarSymb} {S : VarType}
    (hmem : (⟨v, S.VTypeBox⟩ : VarSymb × VarType) ∈ W.1) :
    (⟨v, S⟩ : VarSymb × VarType) ∈ (VarCtx_unbox W).1 :=
  Finset.mem_image.mpr ⟨⟨v, S.VTypeBox⟩, Finset.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩

/-- In a pair-free context every box-typed entry is literally a `□`, so `debox` really is inverse
    to boxing and `VarCtx_box (VarCtx_unbox W)` recovers exactly `W`'s box-typed part. -/
theorem VarCtx_box_unbox_subset {W : VarCtx} (hpf : W.firstPairVar = none) :
    (VarCtx_box (VarCtx_unbox W)).1 ⊆ W.1 := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨⟨av, aS⟩, hav, rfl⟩
  rcases Finset.mem_image.mp hav with ⟨⟨bv, bS⟩, hbv, hbeq⟩
  obtain ⟨hbmem, hbbox⟩ := Finset.mem_filter.mp hbv
  have hv : bv = av := congrArg Prod.fst hbeq
  have hS : bS.debox = aS := congrArg Prod.snd hbeq
  subst hv
  show (⟨bv, aS.VTypeBox⟩ : VarSymb × VarType) ∈ W.1
  cases bS with
  | VTypeBox T => cases hS; exact hbmem
  | VTypeProd T1 T2 => exact (VarCtx.firstPairVar_none_no_pair hpf hbmem).elim
  | Var => simp [VarType.isBox] at hbbox
  | VTypeDia T => simp [VarType.isBox] at hbbox
  | VTypeOne => simp [VarType.isBox] at hbbox

theorem VarCtx_unbox_no_box_extras {W : VarCtx} (hpf : W.firstPairVar = none) :
    ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box (VarCtx_unbox W)).1 := by
  rintro ⟨v, S⟩ hmem hbox
  cases S with
  | VTypeBox T => exact Finset.mem_image.mpr ⟨⟨v, T⟩, mem_VarCtx_unbox hmem, rfl⟩
  | VTypeProd T1 T2 => exact (VarCtx.firstPairVar_none_no_pair hpf hmem).elim
  | Var => simp [VarType.isBox] at hbox
  | VTypeDia T => simp [VarType.isBox] at hbox
  | VTypeOne => simp [VarType.isBox] at hbox

/-- A non-box-typed entry's symbol is absent from the unboxed context. -/
theorem not_mem_VarCtx_unbox {W : VarCtx} {v : VarSymb} {S : VarType}
    (hmem : (⟨v, S⟩ : VarSymb × VarType) ∈ W.1) (hnb : VarType.isBox S = false) :
    v ∉ VarCtx_to_VarSymbs (VarCtx_unbox W) := by
  intro hv
  rcases Finset.mem_image.mp hv with ⟨p, hp, hpeq⟩
  rcases Finset.mem_image.mp hp with ⟨q, hq, hqeq⟩
  obtain ⟨hqmem, hqbox⟩ := Finset.mem_filter.mp hq
  have hq1 : q.1 = v := by rw [← hpeq, ← hqeq]
  have hqS : q.2 = S := W.2 q hqmem ⟨v, S⟩ hmem hq1
  rw [hqS, hnb] at hqbox
  exact Bool.noConfusion hqbox

/-- Context functionality: a pair variable in `W` is a different variable from any target whose
    type is not that pair. -/
theorem eta_pairvar_ne {W : VarCtx} {v z : VarSymb} {T V1 V2 : VarType}
    (hmem : (⟨v, T⟩ : VarSymb × VarType) ∈ W.1)
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W.1)
    (hT : T ≠ V1.VTypeProd V2) : z ≠ v := by
  rintro rfl
  exact hT (W.2 ⟨z, T⟩ hmem ⟨z, V1.VTypeProd V2⟩ hzmem rfl)

mutual

/-- **Reflection of a free variable into a term.**  `Term.var` covers only `.Var`; every other
    type gets its canonical form, by recursion on the TYPE:

    * `.VTypeOne`  — `unit` (the type is a singleton, so this is forced);
    * `.VTypeProd` — destructure the variable and re-pair the two component reflections;
    * `.VTypeBox`  — `boxterm` over `VarCtx_unbox W`, the inner context `boxterm_ctx_unique` forces,
                     with the unboxed variable inside;
    * `.VTypeDia`  — `diaterm` **with the variable itself as the ◇-witness**.  No rule GENERATES a
                     possible object, but reading an existing free ◇-variable back out is not
                     generating one.

    `box`/`dia` cannot be formed over a context holding a pair variable (`no_box_extras` would
    fail), so those two arms first peel any pair variable away — the same dispatcher/peel shape as
    `eqRec`, and unary here, so the fresh names come from `W` alone. -/
def Term.eta {σ : Signature} (W : VarCtx) (v : VarSymb) :
    (T : VarType) → (⟨v, T⟩ : VarSymb × VarType) ∈ W.1 → Term σ W T
  | .Var,      hmem => Term.var ⟨v, hmem⟩
  | .VTypeOne, _    => Term.unit
  | .VTypeProd A B, hmem =>
      -- The target IS a pair variable: destructure it and re-pair the component reflections.
      let V₀ := VarCtx_erase W ⟨v, A.VTypeProd B⟩
      have hz_fresh : v ∉ VarCtx_to_VarSymbs V₀ := VarCtx_erase_fresh hmem
      have W_eq : VarCtx_insert ⟨v, A.VTypeProd B⟩ V₀ hz_fresh = W :=
        VarCtx_insert_erase hmem hz_fresh
      let v1 : VarSymb := VarSymb.fresh (VarCtx_to_VarSymbs W)
      have hv1_W : v1 ∉ VarCtx_to_VarSymbs W := VarSymb.fresh_not_mem _
      let v2 : VarSymb := VarSymb.fresh (insert v1 (VarCtx_to_VarSymbs W))
      have hv2_i : v2 ∉ insert v1 (VarCtx_to_VarSymbs W) := VarSymb.fresh_not_mem _
      have hv2_W : v2 ∉ VarCtx_to_VarSymbs W := fun h => hv2_i (Finset.mem_insert_of_mem h)
      have hv1v2 : v1 ≠ v2 := fun h => hv2_i (h ▸ Finset.mem_insert_self _ _)
      have hv1_V₀ : v1 ∉ VarCtx_to_VarSymbs V₀ :=
        fun h => hv1_W (VarCtx_to_VarSymbs_erase_subset h)
      have hv2_V₀ : v2 ∉ VarCtx_to_VarSymbs V₀ :=
        fun h => hv2_W (VarCtx_to_VarSymbs_erase_subset h)
      W_eq ▸ Term.pair_elim ⟨v1, A⟩ ⟨v2, B⟩ v hv1_V₀ hv2_V₀ hv1v2 hz_fresh rfl rfl
        (Term.pair
          (Term.eta (VarCtx_insert_twice ⟨v1, A⟩ ⟨v2, B⟩ V₀ hv1_V₀ hv2_V₀ hv1v2) v1 A
            (Finset.mem_insert_self _ _))
          (Term.eta (VarCtx_insert_twice ⟨v1, A⟩ ⟨v2, B⟩ V₀ hv1_V₀ hv2_V₀ hv1v2) v2 B
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  | .VTypeBox U, hmem =>
      match hfp : W.firstPairVar with
      | some ⟨⟨z, V1, V2⟩, hzmem⟩ =>
          Term.etaPeel W v (.VTypeBox U) hmem z V1 V2 hzmem
            (eta_pairvar_ne hmem hzmem (fun h => VarType.noConfusion h))
      | none =>
          Term.boxterm (Term.eta (VarCtx_unbox W) v U (mem_VarCtx_unbox hmem))
            (VarCtx_box_unbox_subset hfp) (VarCtx_unbox_no_box_extras hfp)
  | .VTypeDia U, hmem =>
      match hfp : W.firstPairVar with
      | some ⟨⟨z, V1, V2⟩, hzmem⟩ =>
          Term.etaPeel W v (.VTypeDia U) hmem z V1 V2 hzmem
            (eta_pairvar_ne hmem hzmem (fun h => VarType.noConfusion h))
      | none =>
          have hfresh : v ∉ VarCtx_to_VarSymbs (VarCtx_unbox W) :=
            not_mem_VarCtx_unbox hmem rfl
          Term.diaterm ⟨v, U⟩ hfresh
            (Term.eta (VarCtx_insert ⟨v, U⟩ (VarCtx_unbox W) hfresh) v U
              (Finset.mem_insert_self _ _))
            (by
              intro p hp
              rcases Finset.mem_insert.mp hp with rfl | hrest
              · exact hmem
              · exact VarCtx_box_unbox_subset hfp hrest)
            (fun p hp hbox =>
              Finset.mem_insert_of_mem (VarCtx_unbox_no_box_extras hfp p hp hbox))
termination_by T _ => (sizeOf T, W.pairDepth, 1)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left; simp_wf; omega)
      | (apply Prod.Lex.left; simp_wf; done)
      | (apply Prod.Lex.right; apply Prod.Lex.right; simp_wf; omega)
      | (apply Prod.Lex.right; apply Prod.Lex.right; simp_wf; done)

/-- Peel a pair variable `⟨z, V1×V2⟩` (with `z ≠ v`) out of `W`, reflect the target in the peeled
    context, and re-pair.  Needed because `box`/`dia` cannot be formed while a pair variable is
    in the ambient context. -/
def Term.etaPeel {σ : Signature} (W : VarCtx) (v : VarSymb) (T : VarType)
    (hmem : (⟨v, T⟩ : VarSymb × VarType) ∈ W.1)
    (z : VarSymb) (V1 V2 : VarType)
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W.1)
    (hzv : z ≠ v) : Term σ W T :=
  let V₀ := VarCtx_erase W ⟨z, V1.VTypeProd V2⟩
  have hz_fresh : z ∉ VarCtx_to_VarSymbs V₀ := VarCtx_erase_fresh hzmem
  have W_eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V₀ hz_fresh = W :=
    VarCtx_insert_erase hzmem hz_fresh
  let v1 : VarSymb := VarSymb.fresh (VarCtx_to_VarSymbs W)
  have hv1_W : v1 ∉ VarCtx_to_VarSymbs W := VarSymb.fresh_not_mem _
  let v2 : VarSymb := VarSymb.fresh (insert v1 (VarCtx_to_VarSymbs W))
  have hv2_i : v2 ∉ insert v1 (VarCtx_to_VarSymbs W) := VarSymb.fresh_not_mem _
  have hv2_W : v2 ∉ VarCtx_to_VarSymbs W := fun h => hv2_i (Finset.mem_insert_of_mem h)
  have hv1v2 : v1 ≠ v2 := fun h => hv2_i (h ▸ Finset.mem_insert_self _ _)
  have hv1_V₀ : v1 ∉ VarCtx_to_VarSymbs V₀ :=
    fun h => hv1_W (VarCtx_to_VarSymbs_erase_subset h)
  have hv2_V₀ : v2 ∉ VarCtx_to_VarSymbs V₀ :=
    fun h => hv2_W (VarCtx_to_VarSymbs_erase_subset h)
  W_eq ▸ Term.pair_elim ⟨v1, V1⟩ ⟨v2, V2⟩ z hv1_V₀ hv2_V₀ hv1v2 hz_fresh rfl rfl
    (Term.eta (VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V₀ hv1_V₀ hv2_V₀ hv1v2) v T
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun h => hzv (congrArg Prod.fst h).symm, hmem⟩))))
termination_by (sizeOf T, W.pairDepth, 0)
decreasing_by
  exact Prod.Lex.right _ (Prod.Lex.left _ _
    (VarCtx.pairDepth_unpair_lt hzmem hv1_V₀ hv2_V₀ hv1v2))

end

/-! ## Term-level congruence

`Leibniz`'s `atom` and `eq` cases bottom out here: a box-typed ambient variable can only occur in
a term through a `boxterm` (its inner context holds the unboxed variable), so substituting into an
atom genuinely changes it, and we need

    a ≐ b  ⊢  u[a] ≐ u[b]

by induction on the TERM `u`.  Unlike `Leib` this is a direct entailment, not an implication —
the conclusion is an equality, and the modal cases are again `K_box`/`K_dia` carrying the
hypothesis through. -/

/-- Weakening a closed proof to a single hypothesis. -/
def Proof.ofEmpty {σ : Signature} {V : VarCtx} {ψ φ : WFF σ V}
    (p : Proof σ V ∅ φ) : Proof σ V {ψ} φ :=
  Proof.cast_ctx (by simp) (Proof.weak (ψ := ψ) p)

/-- Term-level Leibniz for the single term `u`. -/
def TermLeib {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    (hx : x ∉ VarCtx_to_VarSymbs V) (a b : Term σ V S) {T : VarType}
    (u : Term σ (VarCtx_insert ⟨x, S⟩ V hx) T) : Prop :=
  Nonempty (Proof σ V {eqRec V S a b}
    (eqRec V T (Term.substVar hx a u) (Term.substVar hx b u)))

theorem TermLeib.unit {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (hpfV : V.firstPairVar = none)
    (a b : Term σ V S) : TermLeib hx a b (Term.unit) := by
  unfold TermLeib
  rw [Term.substVar_unit hx a hpf, Term.substVar_unit hx b hpf, eqRec_unit hpfV]
  exact ⟨Proof.top_intro⟩

theorem TermLeib.pair {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (hpfV : V.firstPairVar = none)
    {a b : Term σ V S} {T1 T2 : VarType}
    {u : Term σ (VarCtx_insert ⟨x, S⟩ V hx) T1} {w : Term σ (VarCtx_insert ⟨x, S⟩ V hx) T2}
    (ihu : TermLeib hx a b u) (ihw : TermLeib hx a b w) :
    TermLeib hx a b (Term.pair u w) := by
  unfold TermLeib at *
  rw [Term.substVar_pair hx a hpf u w, Term.substVar_pair hx b hpf u w,
      eqRec_prod hpfV]
  exact ⟨Proof.and_intro ihu.some ihw.some⟩

/-- The `.var` base.  Either the variable IS the substituted one — and then `S = .Var`, both sides
    are `a` and `b`, and the goal is the hypothesis — or it is some other variable, untouched by
    the substitution, and the goal is reflexivity. -/
theorem TermLeib.var {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (a b : Term σ V S) (w : VarSymb)
    (hw : (⟨w, VarType.Var⟩ : VarSymb × VarType) ∈ (VarCtx_insert ⟨x, S⟩ V hx).1) :
    TermLeib hx a b (Term.var ⟨w, hw⟩) := by
  unfold TermLeib
  rw [Term.substVar_var hx a hpf w hw, Term.substVar_var hx b hpf w hw]
  by_cases h_eq : (⟨w, VarType.Var⟩ : VarSymb × VarType) = ⟨x, S⟩
  · simp only [dif_pos h_eq]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
    exact ⟨Proof.ax (by simp)⟩
  · simp only [dif_neg h_eq]
    exact ⟨Proof.ofEmpty (eqRec_refl V VarType.Var _).some⟩

/-- The `boxterm` case: the exact term-level mirror of `Leib.box`.  A box-typed ambient variable
    lives inside the box (unboxed), so the substitution descends and `K_box` carries the inner
    equality back out. -/
theorem TermLeib.boxterm {σ : Signature} {x : VarSymb × VarType} {V W : VarCtx}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (hnbe : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hpfW : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar = none)
    (hpf : W.firstPairVar = none)
    (t s : Term σ V x.2) {Sφ : VarType} (u : Term σ (VarCtx_insert x V hx) Sφ)
    (ih : TermLeib hx t s u) :
    TermLeib hxW (Term.boxterm t hsub hnbe) (Term.boxterm s hsub hnbe)
      (Term.boxterm u (box_hsub_insert hx hxW hsub) (box_extras_insert hx hxW hnbe)) := by
  unfold TermLeib at ih ⊢
  rw [Term.substVar_boxterm hx hxW hsub hnbe hpfW t u,
      Term.substVar_boxterm hx hxW hsub hnbe hpfW s u,
      eqRec_box hpf t s hsub hnbe hsub hnbe,
      eqRec_box hpf (Term.substVar hx t u) (Term.substVar hx s u) hsub hnbe hsub hnbe]
  simp only [boxCast_id]
  refine ⟨Proof.cast_ctx ?_ (Proof.K_box hsub hnbe ih.some)⟩
  simp [WFF.box_Finset]

/-! ### Atomic congruence

`Rel` and `Func` take `.Var`-TYPED ARGUMENTS ONLY (`eval : Rel σ V (n+1) → Term σ V .Var → Rel σ V n`),
so an atom's dependence on a higher-typed variable is entirely through those `.Var` argument terms.
`TermLeib` gives us `u[a] ≐ u[b]` for each of them, and `eqRec_leibniz_Var` — the primitive
`eq_elim`, the one equality rule the reform keeps — turns those into the atom congruence.

The induction changes one argument at a time, from the outermost inwards, so it has to carry the
arguments already changed.  `Rel.closeN` is that carrier: the arity is an EXPLICIT `ℕ` with the
list length matched by a `Prop` hypothesis, which keeps every rewrite below off the type index.

(NB: inside the `Rel` namespace the identifier `R` resolves to the constructor `Rel.R`, so the
head relation is spelled `Rl` in every pattern below.) -/

/-- Apply `args` to an arity-`n` relation, first element innermost. -/
def Rel.closeN {σ : Signature} {V : VarCtx} :
    (n : ℕ) → Rel σ V n → (args : List (Term σ V .Var)) → args.length = n → Rel σ V 0
  | 0,     Rl, [],        _ => Rl
  | n + 1, Rl, u :: rest, h => Rel.closeN n (Rl.eval u) rest (by simpa using h)
  | 0,     _,  _ :: _,    h => absurd h (by simp)
  | _ + 1, _,  [],        h => absurd h (by simp)

/-- Peeling one argument off the front is the same as `eval`-ing it on. -/
theorem Rel.closeN_eval {σ : Signature} {V : VarCtx} (n : ℕ)
    (Rl : Rel σ V (n + 1)) (w : Term σ V .Var) (args : List (Term σ V .Var))
    (h : args.length = n) (h' : (w :: args).length = n + 1) :
    Rel.closeN n (Rl.eval w) args h = Rel.closeN (n + 1) Rl (w :: args) h' := rfl

theorem Rel.ctx_rest_eval {σ : Signature} {V : VarCtx} {n : ℕ} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (s : Term σ V S)
    (Rl : Rel σ (VarCtx_insert ⟨x, S⟩ V hx) (n + 1))
    (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var) :
    Rel.ctx_rest hx hpf s (Rl.eval t)
      = (Rel.ctx_rest hx hpf s Rl).eval (Term.ctx_rest hx hpf s t) := rfl

/-- Substitution commutes with closing: it acts on the head relation and on each argument. -/
theorem Rel.ctx_rest_closeN {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (s : Term σ V S) :
    ∀ (n : ℕ) (Rl : Rel σ (VarCtx_insert ⟨x, S⟩ V hx) n)
      (args : List (Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var)) (h : args.length = n)
      (h' : (args.map (Term.ctx_rest hx hpf s)).length = n),
      Rel.ctx_rest hx hpf s (Rel.closeN n Rl args h)
        = Rel.closeN n (Rel.ctx_rest hx hpf s Rl) (args.map (Term.ctx_rest hx hpf s)) h'
  | 0,     _,  [],        _, _  => rfl
  | n + 1, Rl, u :: rest, h, _  => by
      show Rel.ctx_rest hx hpf s (Rel.closeN n (Rl.eval u) rest _) = _
      rw [Rel.ctx_rest_closeN hx hpf s n (Rl.eval u) rest (by simpa using h) (by simpa using h)]
      rfl
  | 0,     _,  _ :: _,    h, _  => absurd h (by simp)
  | _ + 1, _,  [],        h, _  => absurd h (by simp)

/-- `closeN` depends on its length proof only proof-irrelevantly. -/
theorem Rel.closeN_congr {σ : Signature} {V : VarCtx} (n : ℕ)
    (Rl Rl' : Rel σ V n) (args args' : List (Term σ V .Var))
    (h : args.length = n) (h' : args'.length = n)
    (hR : Rl = Rl') (ha : args = args') :
    Rel.closeN n Rl args h = Rel.closeN n Rl' args' h' := by
  subst hR; subst ha; rfl

/-- Composition of two object implications under a common hypothesis set. -/
def Proof.impTrans {σ : Signature} {V : VarCtx} {Γ : Finset (WFF σ V)} {p q r : WFF σ V}
    (h1 : Proof σ V Γ (p.imp q)) (h2 : Proof σ V Γ (q.imp r)) : Proof σ V Γ (p.imp r) := by
  have hp : Proof σ V (Γ ∪ {p}) p := Proof.ax (by simp)
  exact Proof.imp_intro (Proof.imp_elim (Proof.weak h2) (Proof.imp_elim (Proof.weak h1) hp))

/-- The one-argument abstraction the `eq_elim` step needs: an atom with its innermost argument
    replaced by a fresh variable, and what substituting for that variable gives back. -/
theorem atom_abstract_key {σ : Signature} {V : VarCtx} {y : VarSymb}
    (hy : y ∉ VarCtx_to_VarSymbs V)
    (hpfy : (VarCtx_insert ⟨y, VarType.Var⟩ V hy).firstPairVar = none)
    (n : ℕ) (Rl : Rel σ V (n + 1)) (args : List (Term σ V .Var)) (h : args.length = n)
    (c : Term σ V .Var) :
    WFF.substVar hy c (WFF.atom (Rel.closeN (n + 1)
        (Rel.ctx_ext ⟨y, VarType.Var⟩ hy Rl)
        (Term.var ⟨y, Finset.mem_insert_self _ _⟩
          :: args.map (Term.ctx_ext ⟨y, VarType.Var⟩ hy)) (by simp [h])))
      = WFF.atom (Rel.closeN (n + 1) Rl (c :: args) (by simp [h])) := by
  rw [WFF.substVar_atom hy c hpfy,
      Rel.ctx_rest_closeN hy hpfy c (n + 1) _ _ (by simp [h]) (by simp [h])]
  refine congrArg WFF.atom (Rel.closeN_congr _ _ _ _ _ _ _ ?_ ?_)
  · exact Rel.ctx_rest_ctx_ext hy hpfy c Rl
  · rw [List.map_cons, List.map_map]
    congr 1
    · rw [← Term.substVar_eq_ctx_rest' hy c _ hpfy,
          Term.substVar_var hy c hpfy y (Finset.mem_insert_self _ _), dif_pos rfl]
    · rw [show (Term.ctx_rest hy hpfy c ∘ Term.ctx_ext ⟨y, VarType.Var⟩ hy) = id from
            funext fun t => Term.ctx_rest_ctx_ext hy hpfy c t]
      exact List.map_id args

/-- **Atomic congruence.**  By induction on the relation, changing one argument at a time from the
    outermost inwards; `args` carries the arguments already switched from `a` to `b`.  Each single
    change is `eqRec_leibniz_Var` — the primitive `.Var` `eq_elim` — applied to the argument
    equality that `TermLeib` supplies. -/
theorem relLeibClosed {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (hpfV : V.firstPairVar = none) (a b : Term σ V S)
    (hterm : ∀ (u : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var), TermLeib hx a b u) :
    ∀ (n : ℕ) (Rl : Rel σ (VarCtx_insert ⟨x, S⟩ V hx) n)
      (args : List (Term σ V .Var)) (h : args.length = n),
      Nonempty (Proof σ V {eqRec V S a b}
        ((WFF.atom (Rel.closeN n (Rel.ctx_rest hx hpf a Rl) args h)).imp
         (WFF.atom (Rel.closeN n (Rel.ctx_rest hx hpf b Rl) args h))))
  | _, .R _,        _,    _ => ⟨Proof.impId⟩
  | n, .eval Rl' u, args, h => by
      set y : VarSymb := VarSymb.fresh (VarCtx_to_VarSymbs V) with hydef
      have hy : y ∉ VarCtx_to_VarSymbs V := VarSymb.fresh_not_mem _
      have hpfy : (VarCtx_insert ⟨y, VarType.Var⟩ V hy).firstPairVar = none :=
        firstPairVar_insert_Var hy hpfV
      set ua : Term σ V .Var := Term.ctx_rest hx hpf a u with huadef
      set ub : Term σ V .Var := Term.ctx_rest hx hpf b u with hubdef
      set Ra : Rel σ V (n + 1) := Rel.ctx_rest hx hpf a Rl' with hRadef
      -- STEP B: switch the innermost argument, by `.Var` Leibniz at a fresh variable.
      have hkey := atom_abstract_key hy hpfy n Ra args h
      have hleib := eqRec_leibniz_Var hpfV y hy
        (WFF.atom (Rel.closeN (n + 1) (Rel.ctx_ext ⟨y, VarType.Var⟩ hy Ra)
          (Term.var ⟨y, Finset.mem_insert_self _ _⟩
            :: args.map (Term.ctx_ext ⟨y, VarType.Var⟩ hy)) (by simp [h]))) ua ub
      rw [hkey ua, hkey ub] at hleib
      have harg : Proof σ V {eqRec V S a b} (eqRec V VarType.Var ua ub) := by
        have := (hterm u).some
        rw [Term.substVar_eq_ctx_rest' hx a u hpf, Term.substVar_eq_ctx_rest' hx b u hpf] at this
        exact this
      have stepB : Proof σ V {eqRec V S a b}
          ((WFF.atom (Rel.closeN (n + 1) Ra (ua :: args) (by simp [h]))).imp
           (WFF.atom (Rel.closeN (n + 1) Ra (ub :: args) (by simp [h])))) :=
        Proof.imp_elim (Proof.ofEmpty hleib.some) harg
      -- STEP A: the induction hypothesis, with the switched argument already in `args`.
      have stepA := (relLeibClosed hx hpf hpfV a b hterm (n + 1) Rl' (ub :: args) (by simp [h])).some
      exact ⟨Proof.impTrans stepB stepA⟩
  termination_by _ Rl _ _ => sizeOf Rl

/-- The `atom` case of Leibniz: `relLeibClosed` at arity `0` with no carried arguments. -/
theorem Leib.atom {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (hpfV : V.firstPairVar = none)
    {a b : Term σ V S}
    (hterm : ∀ (u : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var), TermLeib hx a b u)
    (R : Rel σ (VarCtx_insert ⟨x, S⟩ V hx) 0) :
    Leib hx a b (WFF.atom R) := by
  unfold Leib
  rw [WFF.substVar_atom hx a hpf R, WFF.substVar_atom hx b hpf R]
  exact relLeibClosed hx hpf hpfV a b hterm 0 R [] rfl

/-! ### Function-symbol congruence

The `Func` mirror of the above, for `TermLeib`'s `.func` case.  The conclusion is an EQUALITY
rather than an implication, so instead of composing two implications we run the single Leibniz
step in the reverse direction (`Proof.eqSymmAtomic` on the argument equality), which lands the
induction hypothesis and the goal on the two sides of one substitution.

(Inside the `Func` namespace `F` is the constructor `Func.F`, so the head is spelled `Fl`.) -/

def Func.closeN {σ : Signature} {V : VarCtx} :
    (n : ℕ) → Func σ V n → (args : List (Term σ V .Var)) → args.length = n → Func σ V 0
  | 0,     Fl, [],        _ => Fl
  | n + 1, Fl, u :: rest, h => Func.closeN n (Fl.eval u) rest (by simpa using h)
  | 0,     _,  _ :: _,    h => absurd h (by simp)
  | _ + 1, _,  [],        h => absurd h (by simp)

theorem Func.closeN_congr {σ : Signature} {V : VarCtx} (n : ℕ)
    (Fl Fl' : Func σ V n) (args args' : List (Term σ V .Var))
    (h : args.length = n) (h' : args'.length = n)
    (hF : Fl = Fl') (ha : args = args') :
    Func.closeN n Fl args h = Func.closeN n Fl' args' h' := by
  subst hF; subst ha; rfl

theorem Func.ctx_rest_eval {σ : Signature} {V : VarCtx} {n : ℕ} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (s : Term σ V S)
    (Fl : Func σ (VarCtx_insert ⟨x, S⟩ V hx) (n + 1))
    (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var) :
    Func.ctx_rest hx hpf s (Fl.eval t)
      = (Func.ctx_rest hx hpf s Fl).eval (Term.ctx_rest hx hpf s t) := by
  conv_lhs => unfold Func.ctx_rest

theorem Func.ctx_rest_closeN {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (s : Term σ V S) :
    ∀ (n : ℕ) (Fl : Func σ (VarCtx_insert ⟨x, S⟩ V hx) n)
      (args : List (Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var)) (h : args.length = n)
      (h' : (args.map (Term.ctx_rest hx hpf s)).length = n),
      Func.ctx_rest hx hpf s (Func.closeN n Fl args h)
        = Func.closeN n (Func.ctx_rest hx hpf s Fl) (args.map (Term.ctx_rest hx hpf s)) h'
  | 0,     _,  [],        _, _  => rfl
  | n + 1, Fl, u :: rest, h, _  => by
      show Func.ctx_rest hx hpf s (Func.closeN n (Fl.eval u) rest _) = _
      rw [Func.ctx_rest_closeN hx hpf s n (Fl.eval u) rest (by simpa using h) (by simpa using h),
          Func.ctx_rest_eval]
      rfl
  | 0,     _,  _ :: _,    h, _  => absurd h (by simp)
  | _ + 1, _,  [],        h, _  => absurd h (by simp)

theorem Func.ctx_rest_F {σ : Signature} {V : VarCtx} {n : ℕ} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (s : Term σ V S)
    (hsym : {f : σ.FuncSyms // σ.funcArity f = n}) :
    Func.ctx_rest hx hpf s (Func.F (V := VarCtx_insert ⟨x, S⟩ V hx) hsym) = Func.F hsym := by
  conv_lhs => unfold Func.ctx_rest

/-- The `Func` mirror of `atom_abstract_key`: one argument abstracted to a fresh variable, with
    the (already finished) right-hand side merely weakened so that it restores untouched. -/
theorem func_abstract_key {σ : Signature} {V : VarCtx} {y : VarSymb}
    (hy : y ∉ VarCtx_to_VarSymbs V)
    (hpfy : (VarCtx_insert ⟨y, VarType.Var⟩ V hy).firstPairVar = none)
    (n : ℕ) (Fl : Func σ V (n + 1)) (args : List (Term σ V .Var)) (h : args.length = n)
    (rhs : Term σ V .Var) (c : Term σ V .Var) :
    WFF.substVar hy c (WFF.eq
        (Term.func (Func.closeN (n + 1) (Func.ctx_ext ⟨y, VarType.Var⟩ hy Fl)
          (Term.var ⟨y, Finset.mem_insert_self _ _⟩
            :: args.map (Term.ctx_ext ⟨y, VarType.Var⟩ hy)) (by simp [h])))
        (Term.ctx_ext ⟨y, VarType.Var⟩ hy rhs))
      = WFF.eq (Term.func (Func.closeN (n + 1) Fl (c :: args) (by simp [h]))) rhs := by
  rw [WFF.substVar_eq hy c hpfy]
  congr 1
  · rw [Term.substVar_func hy c hpfy,
        Func.ctx_rest_closeN hy hpfy c (n + 1) _ _ (by simp [h]) (by simp [h])]
    refine congrArg Term.func (Func.closeN_congr _ _ _ _ _ _ _ ?_ ?_)
    · exact Func.ctx_rest_ctx_ext hy hpfy c Fl
    · rw [List.map_cons, List.map_map]
      congr 1
      · rw [← Term.substVar_eq_ctx_rest' hy c _ hpfy,
            Term.substVar_var hy c hpfy y (Finset.mem_insert_self _ _), dif_pos rfl]
      · rw [show (Term.ctx_rest hy hpfy c ∘ Term.ctx_ext ⟨y, VarType.Var⟩ hy) = id from
              funext fun t => Term.ctx_rest_ctx_ext hy hpfy c t]
        exact List.map_id args
  · rw [Term.substVar_eq_ctx_rest' hy c _ hpfy]
    exact Term.ctx_rest_ctx_ext hy hpfy c rhs

/-- **Function-symbol congruence.**  Same induction as `relLeibClosed`; the Leibniz step is run
    on the REVERSED argument equality so that the induction hypothesis and the goal sit on the two
    sides of a single substitution — no transitivity of equality needed. -/
theorem funcLeibClosed {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (hpfV : V.firstPairVar = none) (a b : Term σ V S)
    (hterm : ∀ (u : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var), TermLeib hx a b u) :
    ∀ (n : ℕ) (Fl : Func σ (VarCtx_insert ⟨x, S⟩ V hx) n)
      (args : List (Term σ V .Var)) (h : args.length = n),
      Nonempty (Proof σ V {eqRec V S a b}
        (WFF.eq (Term.func (Func.closeN n (Func.ctx_rest hx hpf a Fl) args h))
                (Term.func (Func.closeN n (Func.ctx_rest hx hpf b Fl) args h))))
  | _, .F hsym,     _,    _ => by
      rw [Func.ctx_rest_F hx hpf a hsym, Func.ctx_rest_F hx hpf b hsym]
      exact ⟨Proof.eq_intro _⟩
  | n, .eval Fl' u, args, h => by
      set y : VarSymb := VarSymb.fresh (VarCtx_to_VarSymbs V) with hydef
      have hy : y ∉ VarCtx_to_VarSymbs V := VarSymb.fresh_not_mem _
      have hpfy : (VarCtx_insert ⟨y, VarType.Var⟩ V hy).firstPairVar = none :=
        firstPairVar_insert_Var hy hpfV
      set ua : Term σ V .Var := Term.ctx_rest hx hpf a u with huadef
      set ub : Term σ V .Var := Term.ctx_rest hx hpf b u with hubdef
      set Fa : Func σ V (n + 1) := Func.ctx_rest hx hpf a Fl' with hFadef
      set Fb : Func σ V (n + 1) := Func.ctx_rest hx hpf b Fl' with hFbdef
      rw [Func.ctx_rest_eval hx hpf a Fl' u, Func.ctx_rest_eval hx hpf b Fl' u]
      set rhs : Term σ V .Var :=
        Term.func (Func.closeN (n + 1) Fb (ub :: args) (by simp [h])) with hrhs
      have hkey := func_abstract_key hy hpfy n Fa args h rhs
      have hleib := eqRec_leibniz_Var hpfV y hy
        (WFF.eq (Term.func (Func.closeN (n + 1) (Func.ctx_ext ⟨y, VarType.Var⟩ hy Fa)
            (Term.var ⟨y, Finset.mem_insert_self _ _⟩
              :: args.map (Term.ctx_ext ⟨y, VarType.Var⟩ hy)) (by simp [h])))
          (Term.ctx_ext ⟨y, VarType.Var⟩ hy rhs)) ub ua
      rw [hkey ub, hkey ua] at hleib
      have harg : Proof σ V {eqRec V S a b} (eqRec V VarType.Var ua ub) := by
        have hu := (hterm u).some
        rw [Term.substVar_eq_ctx_rest' hx a u hpf, Term.substVar_eq_ctx_rest' hx b u hpf] at hu
        exact hu
      have hargSym : Proof σ V {eqRec V S a b} (eqRec V VarType.Var ub ua) := by
        rw [eqRec_var hpfV] at harg ⊢
        exact Proof.eqSymmAtomic hpfV ua ub harg
      have hIH := (funcLeibClosed hx hpf hpfV a b hterm (n + 1) Fl' (ub :: args) (by simp [h])).some
      exact ⟨Proof.imp_elim (Proof.imp_elim (Proof.ofEmpty hleib.some) hargSym) hIH⟩
  termination_by _ Fl _ _ => sizeOf Fl

/-- The `.func` case of `TermLeib`: `funcLeibClosed` at arity `0`. -/
theorem TermLeib.func {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (hpfV : V.firstPairVar = none)
    {a b : Term σ V S}
    (hterm : ∀ (u : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var), TermLeib hx a b u)
    (f : Func σ (VarCtx_insert ⟨x, S⟩ V hx) 0) :
    TermLeib hx a b (Term.func f) := by
  unfold TermLeib
  rw [Term.substVar_func hx a hpf f, Term.substVar_func hx b hpf f, eqRec_var hpfV]
  exact funcLeibClosed hx hpf hpfV a b hterm 0 f [] rfl

/-- The `eq` case of Leibniz, at `.Var` — the only type at which the reform keeps a primitive
    equality.  Two `eq_elim` steps, one per side, each abstracting that side to a fresh variable. -/
theorem Leib.eqVar {σ : Signature} {V : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (hpfV : V.firstPairVar = none)
    {a b : Term σ V S} (t1 t2 : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var)
    (ih1 : TermLeib hx a b t1) (ih2 : TermLeib hx a b t2) :
    Leib hx a b (WFF.eq t1 t2) := by
  unfold Leib TermLeib at *
  rw [WFF.substVar_eq hx a hpf t1 t2, WFF.substVar_eq hx b hpf t1 t2]
  rw [eqRec_var hpfV] at ih1 ih2
  have hy : VarSymb.fresh (VarCtx_to_VarSymbs V) ∉ VarCtx_to_VarSymbs V :=
    VarSymb.fresh_not_mem _
  set y : VarSymb := VarSymb.fresh (VarCtx_to_VarSymbs V) with hydef
  have hpfy : (VarCtx_insert ⟨y, VarType.Var⟩ V hy).firstPairVar = none :=
    firstPairVar_insert_Var hy hpfV
  have hymem : (⟨y, VarType.Var⟩ : VarSymb × VarType)
      ∈ (VarCtx_insert (⟨y, VarType.Var⟩ : VarSymb × VarType) V hy).1 :=
    Finset.mem_insert_self _ _
  -- Abstract the LEFT side of the equation.
  set φ1 : WFF σ (VarCtx_insert (⟨y, VarType.Var⟩ : VarSymb × VarType) V hy) :=
    WFF.eq (Term.var ⟨y, hymem⟩)
      (Term.ctx_ext ⟨y, VarType.Var⟩ hy (Term.substVar hx a t2)) with hφ1
  have key1 : ∀ (c : Term σ V .Var),
      WFF.substVar hy c φ1 = WFF.eq c (Term.substVar hx a t2) := by
    intro c
    rw [hφ1, WFF.substVar_eq hy c hpfy]
    congr 1
    · rw [Term.substVar_var hy c hpfy y hymem, dif_pos rfl]
    · rw [Term.substVar_eq_ctx_rest' hy c _ hpfy]
      exact Term.ctx_rest_ctx_ext hy hpfy c _
  -- Abstract the RIGHT side.
  set φ2 : WFF σ (VarCtx_insert (⟨y, VarType.Var⟩ : VarSymb × VarType) V hy) :=
    WFF.eq (Term.ctx_ext ⟨y, VarType.Var⟩ hy (Term.substVar hx b t1))
      (Term.var ⟨y, hymem⟩) with hφ2
  have key2 : ∀ (c : Term σ V .Var),
      WFF.substVar hy c φ2 = WFF.eq (Term.substVar hx b t1) c := by
    intro c
    rw [hφ2, WFF.substVar_eq hy c hpfy]
    congr 1
    · rw [Term.substVar_eq_ctx_rest' hy c _ hpfy]
      exact Term.ctx_rest_ctx_ext hy hpfy c _
    · rw [Term.substVar_var hy c hpfy y hymem, dif_pos rfl]
  refine ⟨Proof.imp_intro ?_⟩
  have hhyp : Proof σ V ({eqRec V S a b}
      ∪ {WFF.eq (Term.substVar hx a t1) (Term.substVar hx a t2)})
      (WFF.eq (Term.substVar hx a t1) (Term.substVar hx a t2)) := Proof.ax (by simp)
  have h1 := Proof.weak (ψ := WFF.eq (Term.substVar hx a t1) (Term.substVar hx a t2)) ih1.some
  have h2 := Proof.weak (ψ := WFF.eq (Term.substVar hx a t1) (Term.substVar hx a t2)) ih2.some
  -- Step 1: replace `t1[a]` by `t1[b]` on the left.
  have hs1 : Proof σ V ({eqRec V S a b}
      ∪ {WFF.eq (Term.substVar hx a t1) (Term.substVar hx a t2)})
      (WFF.substVar hy (Term.substVar hx a t1) φ1) := by
    rw [key1]; exact hhyp
  have step1 := Proof.eq_elim ⟨y, VarType.Var⟩ hy
    (Term.substVar hx a t1) (Term.substVar hx b t1) h1 hs1
  rw [key1] at step1
  -- Step 2: replace `t2[a]` by `t2[b]` on the right.
  have hs2 : Proof σ V ({eqRec V S a b}
      ∪ {WFF.eq (Term.substVar hx a t1) (Term.substVar hx a t2)})
      (WFF.substVar hy (Term.substVar hx a t2) φ2) := by
    rw [key2]; exact step1
  have step2 := Proof.eq_elim ⟨y, VarType.Var⟩ hy
    (Term.substVar hx a t2) (Term.substVar hx b t2) h2 hs2
  rw [key2] at step2
  exact step2

/-! ### The vacuous cases

A `pair_elim`-headed formula or term carries a product variable in its own context, which
contradicts pair-freeness.  So — exactly as for `eqRecCore`'s two trailing arms — there is no
pair-free Leibniz instance at a `pair_elim`, and the honest content is the vacuity.

Likewise `.VTypeOne` is a singleton: in a pair-free context the only term of that type is `unit`,
so `a` and `b` coincide and the whole type is trivial. -/

theorem Leib.pair_elim {σ : Signature} {V V₀ : VarCtx} {S : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (a b : Term σ V S)
    {W₁ : VarCtx} (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V₀) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V₀)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V₀)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V₀ hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, v₁.2.VTypeProd v₂.2⟩ V₀ hz = VarCtx_insert ⟨x, S⟩ V hx)
    (ψ : WFF σ W₁) :
    Leib hx a b (WFF.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ) :=
  (VarCtx.firstPairVar_none_no_pair hpf (pair_elim_ctx_mem w₂eq)).elim

theorem TermLeib.pair_elim {σ : Signature} {V V₀ : VarCtx} {S T : VarType} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) (a b : Term σ V S)
    {W₁ : VarCtx} (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V₀) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V₀)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V₀)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V₀ hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, v₁.2.VTypeProd v₂.2⟩ V₀ hz = VarCtx_insert ⟨x, S⟩ V hx)
    (body : Term σ W₁ T) :
    TermLeib hx a b (Term.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body) :=
  (VarCtx.firstPairVar_none_no_pair hpf (pair_elim_ctx_mem w₂eq)).elim

/-- In a pair-free context the only term of type `.VTypeOne` is `unit`. -/
theorem Term.unit_of_VTypeOne {σ : Signature} {V : VarCtx} (hpf : V.firstPairVar = none)
    (t : Term σ V .VTypeOne) : t = Term.unit := by
  cases t with
  | unit => rfl
  | pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body =>
      exact (VarCtx.firstPairVar_none_no_pair hpf (pair_elim_ctx_mem w₂eq)).elim

/-- Substituting at `.VTypeOne` is trivial: the two terms are equal. -/
theorem Leib.of_unitType {σ : Signature} {V : VarCtx} {x : VarSymb}
    {hx : x ∉ VarCtx_to_VarSymbs V} (hpfV : V.firstPairVar = none)
    (a b : Term σ V .VTypeOne) (φ : WFF σ (VarCtx_insert ⟨x, VarType.VTypeOne⟩ V hx)) :
    Leib hx a b φ := by
  unfold Leib
  rw [Term.unit_of_VTypeOne hpfV a, Term.unit_of_VTypeOne hpfV b]
  exact ⟨Proof.impId⟩

theorem TermLeib.of_unitType {σ : Signature} {V : VarCtx} {x : VarSymb} {T : VarType}
    {hx : x ∉ VarCtx_to_VarSymbs V} (hpfV : V.firstPairVar = none)
    (a b : Term σ V .VTypeOne)
    (u : Term σ (VarCtx_insert ⟨x, VarType.VTypeOne⟩ V hx) T) :
    TermLeib hx a b u := by
  unfold TermLeib
  rw [Term.unit_of_VTypeOne hpfV a, Term.unit_of_VTypeOne hpfV b]
  exact ⟨Proof.ofEmpty (eqRec_refl V T _).some⟩

/-- **Witnessed necessitation with hypotheses**: `Δ ⊢ φ` gives `□_xΔ ⊢ □_xφ`.  `Proof.necx` is the
    `Δ = ∅` case; this is what the term-level ◇ case needs. -/
def Proof.necxG {σ : Signature} {V W : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V} {Δ : Finset (WFF σ (VarCtx_insert x V hx))}
    {φ : WFF σ (VarCtx_insert x V hx)}
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (p : Proof σ (VarCtx_insert x V hx) Δ φ) :
    Proof σ W (WFF.box_x_Finset x hx hsub h Δ) (WFF.box_x x hx hsub h φ) := by
  have hneg : Proof σ (VarCtx_insert x V hx) (Δ ∪ {neg φ}) WFF.bot :=
    Proof.imp_elim (Proof.ax (by simp)) (Proof.weak p)
  have hK := Proof.K_dia (Γ := (∅ : Finset (WFF σ V))) (Δ := Δ) x hx hsub h
    (by simpa [WFF.ctx_ext_Finset] using hneg)
  simp only [WFF.box_Finset, Finset.image_empty, Finset.empty_union] at hK
  exact Proof.imp_intro (Proof.dia_bot x hx hsub h hK)

/-- The term-level ◇ case, modal β: the substituted variable IS the diaterm's witness, so
    `substVar` replaces the witness and reorders the body.  `necxG` carries the inner equality out
    through `□_xv_s`, which by `dia_ext` is exactly the outer equality at `◇`. -/
theorem TermLeib.diaterm_beta {σ : Signature} {V V_inner : VarCtx} {S_tt : VarType}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (hx : xv.1 ∉ VarCtx_to_VarSymbs V)
    (xv_s : VarSymb × VarType) (hxv_s : xv_s.1 ∉ VarCtx_to_VarSymbs V_inner)
    (h_xv_ne_xv_s : xv.1 ≠ xv_s.1)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) S_tt)
    (hsub_t : (VarCtx_dia xv V_inner hxv).1
                ⊆ (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ V hx).1)
    (h_no_extras_t : ∀ p ∈ (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ V hx).1,
                      VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (tt_s tt_s' : Term σ (VarCtx_insert xv_s V_inner hxv_s) xv.2)
    (hsub_s : (VarCtx_dia xv_s V_inner hxv_s).1 ⊆ V.1)
    (h_no_extras_s : ∀ p ∈ V.1, VarType.isBox p.2 = true
                      → p ∈ (VarCtx_dia xv_s V_inner hxv_s).1)
    (hpf : (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ V hx).firstPairVar = none)
    (hpfV : V.firstPairVar = none)
    (hxv_s_outer : xv_s.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V_inner hxv))
    (hxv_xv_s_outer : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s))
    (h_x_inner : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s))
    (h_reorder : VarCtx_insert xv_s (VarCtx_insert xv V_inner hxv) hxv_s_outer
               = VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer)
    (h_reform : VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer
              = VarCtx_insert ⟨xv.1, xv.2⟩ (VarCtx_insert xv_s V_inner hxv_s) h_x_inner)
    (ih : TermLeib h_x_inner tt_s tt_s'
            (h_reform ▸ h_reorder ▸ Term.ctx_ext xv_s hxv_s_outer tt)) :
    TermLeib hx (Term.diaterm xv_s hxv_s tt_s hsub_s h_no_extras_s)
                (Term.diaterm xv_s hxv_s tt_s' hsub_s h_no_extras_s)
                (Term.diaterm xv hxv tt hsub_t h_no_extras_t) := by
  unfold TermLeib at ih ⊢
  rw [Term.substVar_diaterm_modal_beta xv hxv hx xv_s hxv_s h_xv_ne_xv_s tt hsub_t h_no_extras_t
        tt_s hsub_s h_no_extras_s hpf hxv_s_outer hxv_xv_s_outer h_x_inner h_reorder h_reform,
      Term.substVar_diaterm_modal_beta xv hxv hx xv_s hxv_s h_xv_ne_xv_s tt hsub_t h_no_extras_t
        tt_s' hsub_s h_no_extras_s hpf hxv_s_outer hxv_xv_s_outer h_x_inner h_reorder h_reform,
      eqRec_dia_same hpfV tt_s tt_s' hsub_s h_no_extras_s hsub_s h_no_extras_s rfl,
      eqRec_dia_same hpfV _ _ hsub_s h_no_extras_s hsub_s h_no_extras_s rfl]
  simp only [diaCast_id]
  refine ⟨Proof.cast_ctx ?_ (Proof.necxG hsub_s h_no_extras_s ih.some)⟩
  simp [WFF.box_x_Finset]

/-! ### Pass-through: when the substituted variable never reaches inside the modality

A `box`'s inner context holds only the UNBOXED images of the ambient's box-typed variables, so a
variable of non-box type simply is not there: the substitution passes the whole `box` through
untouched, `φ[a] = φ[b]`, and `impId` finishes.  `WFF.ctx_rest_box_arm` already branches on exactly
this (`by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner`) — these lemmas name its `else` branch,
which `SubstitutionLemmas10` never needed. -/

/-- If the substituted variable occurs in a `box`'s inner context, its type must be a `□`. -/
theorem box_inner_mem_forces_box {V V_inner : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (h_x_in : x ∈ VarCtx_to_VarSymbs V_inner) : ∃ T : VarType, S = T.VTypeBox := by
  obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
  simp only at hx'_eq; subst hx'_eq
  have hbox_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType) ∈ (VarCtx_box V_inner).1 :=
    Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
  rcases Finset.mem_insert.mp (hsub hbox_in) with h_eq | h_in_V
  · exact ⟨T', ((Prod.mk.inj h_eq).2).symm⟩
  · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩) hx

theorem box_inner_not_mem {V V_inner : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hS : ∀ T : VarType, S ≠ T.VTypeBox) : x ∉ VarCtx_to_VarSymbs V_inner := fun h =>
  let ⟨T, hT⟩ := box_inner_mem_forces_box hx hsub h
  hS T hT

theorem WFF.substVar_box_passthrough {σ : Signature} {V V_inner : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S) (ψ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
            VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (h_x_out : x ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_box V_inner).1 ⊆ V.1)
    (hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    WFF.substVar hx s (WFF.box ψ hsub hne) = WFF.box ψ hsub' hne' := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_box_arm]
    rw [dif_neg h_x_out]
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

/-- The `box` case of Leibniz when the substituted variable is not of box type: nothing to do. -/
theorem Leib.box_passthrough {σ : Signature} {V V_inner : VarCtx}
    {x : VarSymb} {S : VarType} {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (a b : Term σ V S) (ψ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
            VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (hS : ∀ T : VarType, S ≠ T.VTypeBox) :
    Leib hx a b (WFF.box ψ hsub hne) := by
  have h_x_out : x ∉ VarCtx_to_VarSymbs V_inner := box_inner_not_mem hx hsub hS
  have hsub' : (VarCtx_box V_inner).1 ⊆ V.1 := by
    intro p hp
    rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
    · exfalso
      rcases Finset.mem_image.mp hp with ⟨w, hw, hweq⟩
      exact h_x_out (Finset.mem_image.mpr
        ⟨w, hw, (Prod.mk.inj (hweq.trans h_eq)).1⟩)
    · exact h_V
  have hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1 :=
    fun p hp h_box => hne p (Finset.mem_insert_of_mem hp) h_box
  unfold Leib
  rw [WFF.substVar_box_passthrough hx hpf a ψ hsub hne h_x_out hsub' hne',
      WFF.substVar_box_passthrough hx hpf b ψ hsub hne h_x_out hsub' hne']
  exact ⟨Proof.impId⟩

/-- The `dia` analogue: if the substituted variable occurs in a `dia`'s inner context and is not
    the witness, its type must be a `□` (the non-witness part of `VarCtx_dia` is `VarCtx_box`). -/
theorem dia_inner_mem_forces_box {V V_inner : VarCtx} {x : VarSymb} {S : VarType}
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (h_x_in : x ∈ VarCtx_to_VarSymbs V_inner) : ∃ T : VarType, S = T.VTypeBox := by
  obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
  simp only at hx'_eq; subst hx'_eq
  have hbox_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
      ∈ (VarCtx_dia xv V_inner hxv).1 := by
    rw [VarCtx_dia_fst]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩)
  rcases Finset.mem_insert.mp (hsub hbox_in) with h_eq | h_in_V
  · exact ⟨T', ((Prod.mk.inj h_eq).2).symm⟩
  · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩) hx

theorem WFF.substVar_dia_passthrough {σ : Signature} {V V_inner : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
            VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (h_xv_ne : ¬ (xv.1 = x)) (h_x_out : x ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1)
    (hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    WFF.substVar hx s (WFF.dia xv hxv ψ hsub hne) = WFF.dia xv hxv ψ hsub' hne' := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_dia_arm]
    rw [dif_neg h_xv_ne, dif_neg h_x_out]
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

/-- The `dia` case of Leibniz when the substituted variable is neither the witness nor of box
    type — so it does not occur under the modality at all. -/
theorem Leib.dia_passthrough {σ : Signature} {V V_inner : VarCtx}
    {x : VarSymb} {S : VarType} {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (a b : Term σ V S)
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
            VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (h_xv_ne : ¬ (xv.1 = x)) (hS : ∀ T : VarType, S ≠ T.VTypeBox) :
    Leib hx a b (WFF.dia xv hxv ψ hsub hne) := by
  have h_x_out : x ∉ VarCtx_to_VarSymbs V_inner := fun h =>
    let ⟨T, hT⟩ := dia_inner_mem_forces_box hx hsub h
    hS T hT
  have hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1 := by
    rw [VarCtx_dia_fst]
    intro p hp
    rcases Finset.mem_insert.mp hp with h_eq | hp_box
    · subst h_eq
      have hp_in_dia : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType)
          ∈ (VarCtx_dia xv V_inner hxv).1 := by
        rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq' | h_in_V
      · exact absurd (Prod.mk.inj h_eq').1 h_xv_ne
      · exact h_in_V
    · have hp_in_dia : p ∈ (VarCtx_dia xv V_inner hxv).1 := by
        rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_box
      rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq | h_in_V
      · subst h_eq
        exfalso
        rcases Finset.mem_image.mp hp_box with ⟨q, hq_in, hq_eq⟩
        exact h_x_out (Finset.mem_image.mpr ⟨q, hq_in, (Prod.mk.inj hq_eq).1⟩)
      · exact h_in_V
  have hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1 :=
    fun p hp h_box => hne p (Finset.mem_insert_of_mem hp) h_box
  unfold Leib
  rw [WFF.substVar_dia_passthrough hx hpf a xv hxv ψ hsub hne h_xv_ne h_x_out hsub' hne',
      WFF.substVar_dia_passthrough hx hpf b xv hxv ψ hsub hne h_xv_ne h_x_out hsub' hne']
  exact ⟨Proof.impId⟩

/-! ### Term-level pass-through (the `Term.ctx_rest` mirrors of the two above). -/

theorem Term.substVar_boxterm_passthrough {σ : Signature} {V V_inner : VarCtx}
    {x : VarSymb} {S T : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S) (tt : Term σ V_inner T)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
            VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (h_x_out : x ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_box V_inner).1 ⊆ V.1)
    (hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    Term.substVar hx s (Term.boxterm tt hsub hne) = Term.boxterm tt hsub' hne' := by
  simp only [Term.substVar]
  conv_lhs => unfold Term.ctx_rest_MU
  split
  · conv_lhs => unfold Term.ctx_rest
    dsimp only
    rw [dif_neg h_x_out]
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

theorem TermLeib.boxterm_passthrough {σ : Signature} {V V_inner : VarCtx}
    {x : VarSymb} {S T : VarType} {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (a b : Term σ V S) (tt : Term σ V_inner T)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
            VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (hS : ∀ U : VarType, S ≠ U.VTypeBox) :
    TermLeib hx a b (Term.boxterm tt hsub hne) := by
  have h_x_out : x ∉ VarCtx_to_VarSymbs V_inner := box_inner_not_mem hx hsub hS
  have hsub' : (VarCtx_box V_inner).1 ⊆ V.1 := by
    intro p hp
    rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
    · exfalso
      rcases Finset.mem_image.mp hp with ⟨w, hw, hweq⟩
      exact h_x_out (Finset.mem_image.mpr ⟨w, hw, (Prod.mk.inj (hweq.trans h_eq)).1⟩)
    · exact h_V
  have hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1 :=
    fun p hp h_box => hne p (Finset.mem_insert_of_mem hp) h_box
  unfold TermLeib
  rw [Term.substVar_boxterm_passthrough hx hpf a tt hsub hne h_x_out hsub' hne',
      Term.substVar_boxterm_passthrough hx hpf b tt hsub hne h_x_out hsub' hne']
  exact ⟨Proof.ofEmpty (eqRec_refl V T.VTypeBox _).some⟩

theorem Term.substVar_diaterm_passthrough {σ : Signature} {V V_inner : VarCtx}
    {x : VarSymb} {S T : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) T)
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
            VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (h_xv_ne : ¬ (xv.1 = x)) (h_x_out : x ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1)
    (hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    Term.substVar hx s (Term.diaterm xv hxv tt hsub hne)
      = Term.diaterm xv hxv tt hsub' hne' := by
  simp only [Term.substVar]
  conv_lhs => unfold Term.ctx_rest_MU
  split
  · conv_lhs => unfold Term.ctx_rest
    dsimp only
    rw [dif_neg h_xv_ne, dif_neg h_x_out]
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

theorem TermLeib.diaterm_passthrough {σ : Signature} {V V_inner : VarCtx}
    {x : VarSymb} {S T : VarType} {hx : x ∉ VarCtx_to_VarSymbs V}
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (a b : Term σ V S)
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) T)
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
            VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (h_xv_ne : ¬ (xv.1 = x)) (hS : ∀ U : VarType, S ≠ U.VTypeBox) :
    TermLeib hx a b (Term.diaterm xv hxv tt hsub hne) := by
  have h_x_out : x ∉ VarCtx_to_VarSymbs V_inner := fun h =>
    let ⟨U, hU⟩ := dia_inner_mem_forces_box hx hsub h
    hS U hU
  have hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1 := by
    rw [VarCtx_dia_fst]
    intro p hp
    rcases Finset.mem_insert.mp hp with h_eq | hp_box
    · subst h_eq
      have hp_in_dia : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType)
          ∈ (VarCtx_dia xv V_inner hxv).1 := by
        rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq' | h_in_V
      · exact absurd (Prod.mk.inj h_eq').1 h_xv_ne
      · exact h_in_V
    · have hp_in_dia : p ∈ (VarCtx_dia xv V_inner hxv).1 := by
        rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_box
      rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq | h_in_V
      · subst h_eq
        exfalso
        rcases Finset.mem_image.mp hp_box with ⟨q, hq_in, hq_eq⟩
        exact h_x_out (Finset.mem_image.mpr ⟨q, hq_in, (Prod.mk.inj hq_eq).1⟩)
      · exact h_in_V
  have hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1 :=
    fun p hp h_box => hne p (Finset.mem_insert_of_mem hp) h_box
  unfold TermLeib
  rw [Term.substVar_diaterm_passthrough hx hpf a xv hxv tt hsub hne h_xv_ne h_x_out hsub' hne',
      Term.substVar_diaterm_passthrough hx hpf b xv hxv tt hsub hne h_xv_ne h_x_out hsub' hne']
  exact ⟨Proof.ofEmpty (eqRec_refl V T.VTypeDia _).some⟩

/-- `K_dia` with the WITNESSED slot empty: `□Γ ⊢ ◇_xφ → ◇_xψ` from `Γ↑ ⊢ φ → ψ`.  This is the
    variant the "box variable under a ◇" case needs — its equation hypothesis is a plain `□`. -/
def Proof.congDiaBoxG {σ : Signature} {V W : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V} {Γ : Finset (WFF σ V)}
    {φ ψ : WFF σ (VarCtx_insert x V hx)}
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (hφψ : Proof σ (VarCtx_insert x V hx) (WFF.ctx_ext_Finset x hx Γ) (φ.imp ψ)) :
    Proof σ W (WFF.box_Finset (box_subs_of_dia_subs hsub) (in_box_of_in_dia h) Γ)
      ((WFF.dia x hx φ hsub h).imp (WFF.dia x hx ψ hsub h)) := by
  have h1 : Proof σ (VarCtx_insert x V hx) (WFF.ctx_ext_Finset x hx Γ ∪ {φ}) ψ :=
    Proof.imp_elim (Proof.weak hφψ) (Proof.ax (by simp))
  have hK := Proof.K_dia (Γ := Γ) (Δ := (∅ : Finset (WFF σ (VarCtx_insert x V hx))))
    x hx hsub h (by simpa using h1)
  simp only [WFF.box_x_Finset, Finset.image_empty, Finset.union_empty] at hK
  exact Proof.imp_intro hK

/-! ### A `□`-typed variable under a `◇`

The last modal case: the substituted variable is box-typed and the formula is a `◇` whose witness
is some OTHER variable.  `substVar` descends under the `◇` — weakening the boxterm's inner term
past the witness and reordering the body — and `K_dia`'s plain-`□` slot carries the equation in.

The one thing this needs and does not yet have is that **`eqRec` commutes with weakening**; it is
taken as the hypothesis `hcomm`, isolating that single dependency exactly as `eqRecCore_symm` once
took atomic symmetry.

`hcomm` is stated as an OBJECT IMPLICATION, not an equality, and deliberately so: the equality is
very likely FALSE.  `eqRecPeelA` picks its two fresh component names from
`VarCtx_to_VarSymbs V ∪ boundVars t ∪ boundVars s`, so weakening the context changes the avoid set
and hence the names — the two sides end up α-variants rather than syntactically equal.  The
implication is what is actually true, and is exactly what the reform buys: with equality defined,
α-variants are PROVABLY equivalent (`pair_elim_alpha` derivable) rather than equal.  `Proof.reHyp`
consumes it. -/

theorem Leib.dia_box {σ : Signature} {x : VarSymb × VarType} {V W : VarCtx}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (hnbe : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hpfW : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar = none)
    (hpf : W.firstPairVar = none)
    (t s : Term σ V x.2)
    (xv : VarSymb × VarType) (hxv_ne : xv.1 ≠ x.1)
    (hxv_V : xv.1 ∉ VarCtx_to_VarSymbs V)
    (hxv_outer : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx))
    (hx_out : x.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxv_V))
    (h_reorder : VarCtx_insert xv (VarCtx_insert x V hx) hxv_outer
               = VarCtx_insert ⟨x.1, x.2⟩ (VarCtx_insert xv V hxv_V) hx_out)
    (ψ : WFF σ (VarCtx_insert xv (VarCtx_insert x V hx) hxv_outer))
    (P : (VarCtx_dia xv (VarCtx_insert x V hx) hxv_outer).1
          ⊆ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1)
    (Q : ∀ p ∈ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1, VarType.isBox p.2 = true
          → p ∈ (VarCtx_dia xv (VarCtx_insert x V hx) hxv_outer).1)
    (P' : (VarCtx_dia xv V hxv_V).1 ⊆ W.1)
    (Q' : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V hxv_V).1)
    (hcomm : Nonempty (Proof σ (VarCtx_insert xv V hxv_V) ∅
      ((WFF.ctx_ext xv hxv_V (eqRec V x.2 t s)).imp
        (eqRec (VarCtx_insert xv V hxv_V) x.2
          (Term.ctx_ext xv hxv_V t) (Term.ctx_ext xv hxv_V s)))))
    (ih : Leib hx_out (Term.ctx_ext xv hxv_V t) (Term.ctx_ext xv hxv_V s) (h_reorder ▸ ψ)) :
    Leib hxW (Term.boxterm t hsub hnbe) (Term.boxterm s hsub hnbe)
      (WFF.dia xv hxv_outer ψ P Q) := by
  unfold Leib at ih ⊢
  rw [WFF.substVar_boxterm_dia_gen_base hx hxW hsub hnbe hpfW t xv hxv_ne hxv_V hxv_outer
        hx_out h_reorder ψ P Q P' Q',
      WFF.substVar_boxterm_dia_gen_base hx hxW hsub hnbe hpfW s xv hxv_ne hxv_V hxv_outer
        hx_out h_reorder ψ P Q P' Q',
      eqRec_box hpf t s hsub hnbe hsub hnbe]
  simp only [boxCast_id]
  have hinner : Proof σ (VarCtx_insert xv V hxv_V)
      (WFF.ctx_ext_Finset xv hxv_V {eqRec V x.2 t s})
      ((WFF.substVar hx_out (Term.ctx_ext xv hxv_V t) (h_reorder ▸ ψ)).imp
       (WFF.substVar hx_out (Term.ctx_ext xv hxv_V s) (h_reorder ▸ ψ))) := by
    rw [WFF.ctx_ext_Finset, Finset.image_singleton]
    exact Proof.reHyp hcomm.some ih.some
  refine ⟨Proof.cast_ctx ?_ (Proof.congDiaBoxG P' Q' hinner)⟩
  simp [WFF.box_Finset]

/-- Witnessed necessitation whose hypotheses arrive as plain `□`s: `Γ↑ ⊢ φ` gives `□Γ ⊢ □_xφ`.
    (`necxG` is the same with the hypotheses already witnessed; `necx` is both at `Γ = ∅`.) -/
def Proof.necxBoxG {σ : Signature} {V W : VarCtx} {x : VarSymb × VarType}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V} {Γ : Finset (WFF σ V)}
    {φ : WFF σ (VarCtx_insert x V hx)}
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (h : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    (p : Proof σ (VarCtx_insert x V hx) (WFF.ctx_ext_Finset x hx Γ) φ) :
    Proof σ W (WFF.box_Finset (box_subs_of_dia_subs hsub) (in_box_of_in_dia h) Γ)
      (WFF.box_x x hx hsub h φ) := by
  have hneg : Proof σ (VarCtx_insert x V hx) (WFF.ctx_ext_Finset x hx Γ ∪ {neg φ}) WFF.bot :=
    Proof.imp_elim (Proof.ax (by simp)) (Proof.weak p)
  have hK := Proof.K_dia (Γ := Γ) (Δ := (∅ : Finset (WFF σ (VarCtx_insert x V hx))))
    x hx hsub h (by simpa using hneg)
  simp only [WFF.box_x_Finset, Finset.image_empty, Finset.union_empty] at hK
  exact Proof.imp_intro (Proof.dia_bot x hx hsub h hK)

/-- The term-level mirror of `Leib.dia_box`: a box-typed variable substituted into a `diaterm`
    whose witness is some other variable.  Same `hcomm` dependency. -/
theorem TermLeib.diaterm_box {σ : Signature} {x : VarSymb × VarType} {V W : VarCtx}
    {Sψ : VarType}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (hnbe : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hpfW : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar = none)
    (hpf : W.firstPairVar = none)
    (t s : Term σ V x.2)
    (xv : VarSymb × VarType) (hxv_ne : xv.1 ≠ x.1)
    (hxv_V : xv.1 ∉ VarCtx_to_VarSymbs V)
    (hxv_outer : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx))
    (hx_out : x.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxv_V))
    (h_reorder : VarCtx_insert xv (VarCtx_insert x V hx) hxv_outer
               = VarCtx_insert ⟨x.1, x.2⟩ (VarCtx_insert xv V hxv_V) hx_out)
    (ψ : Term σ (VarCtx_insert xv (VarCtx_insert x V hx) hxv_outer) Sψ)
    (P : (VarCtx_dia xv (VarCtx_insert x V hx) hxv_outer).1
          ⊆ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1)
    (Q : ∀ p ∈ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1, VarType.isBox p.2 = true
          → p ∈ (VarCtx_dia xv (VarCtx_insert x V hx) hxv_outer).1)
    (P' : (VarCtx_dia xv V hxv_V).1 ⊆ W.1)
    (Q' : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V hxv_V).1)
    (hcomm : Nonempty (Proof σ (VarCtx_insert xv V hxv_V) ∅
      ((WFF.ctx_ext xv hxv_V (eqRec V x.2 t s)).imp
        (eqRec (VarCtx_insert xv V hxv_V) x.2
          (Term.ctx_ext xv hxv_V t) (Term.ctx_ext xv hxv_V s)))))
    (ih : TermLeib hx_out (Term.ctx_ext xv hxv_V t) (Term.ctx_ext xv hxv_V s)
            (h_reorder ▸ ψ)) :
    TermLeib hxW (Term.boxterm t hsub hnbe) (Term.boxterm s hsub hnbe)
      (Term.diaterm xv hxv_outer ψ P Q) := by
  unfold TermLeib at ih ⊢
  rw [Term.substVar_diaterm_base hx hxW hsub hnbe hpfW t xv hxv_ne hxv_V hxv_outer
        hx_out h_reorder ψ P Q P' Q',
      Term.substVar_diaterm_base hx hxW hsub hnbe hpfW s xv hxv_ne hxv_V hxv_outer
        hx_out h_reorder ψ P Q P' Q',
      eqRec_box hpf t s hsub hnbe hsub hnbe,
      eqRec_dia_same hpf _ _ P' Q' P' Q' rfl]
  simp only [boxCast_id, diaCast_id]
  have hinner : Proof σ (VarCtx_insert xv V hxv_V)
      (WFF.ctx_ext_Finset xv hxv_V {eqRec V x.2 t s})
      (eqRec (VarCtx_insert xv V hxv_V) Sψ
        (Term.substVar hx_out (Term.ctx_ext xv hxv_V t) (h_reorder ▸ ψ))
        (Term.substVar hx_out (Term.ctx_ext xv hxv_V s) (h_reorder ▸ ψ))) := by
    rw [WFF.ctx_ext_Finset, Finset.image_singleton]
    exact Proof.reHyp hcomm.some ih.some
  refine ⟨Proof.cast_ctx ?_ (Proof.necxBoxG P' Q' hinner)⟩
  simp [WFF.box_Finset]
