import QML.QML_Full_v9

/-!
# Substitution / box commutation lemmas

Substituting a boxed term for a box-typed variable inside a `box` commutes with
the `box` — but only cleanly when the outer context is pair-free.  For a general
context the substitution is threaded through the context's pair-structure, so we
provide TWO lemmas ("max unpair → commute with box → re-pair"):

* `WFF.substVar_boxterm_box_gen_base` — the clean commutation for a PAIR-FREE
  outer context (`firstPairVar = none`):
    `substVar_W (boxterm t) (box φ)  =  box (substVar_V t φ)`
  Generalises the special case (ambient `= VarCtx_box V`) to any `W ⊇ VarCtx_box V`.
  One `hsub`, one `h_no_box_extras`; the LHS `box`'s side conditions are DERIVED
  (`box_hsub_insert` / `box_extras_insert`).  `hxW : x.1 ∉ VarCtx_to_VarSymbs W`
  is a genuine hypothesis (x.1 may appear in W with a non-box type).

* `WFF.substVar_boxterm_box_gen_peel` — the peel-step for a context carrying a
  pair var `z` (`firstPairVar = some z`, `z ≠ x.1`):
    `substVar_W (box φ)  =  pairElim_z v1 v2 (substVar_{W'} (box φ))`
  where `v1,v2` are the SPECIFIC fresh vars `ctx_rest_MU` picks and `W'` is `W`
  with `z` unpaired.  (Fresh vars must be the specific ones: a syntactic equality
  can't hold for arbitrary bound-variable names; α-renaming is a separate layer.)

Usage: peel once/twice to expose the concrete fresh vars, then hit the base once
the context is pair-free.

WHY NOT the naive general `substVar_W (box φ) = box (substVar φ)`:  it is FALSE
when `W` has pair vars.  `WFF.pairElim` is STUCK at `box` (its box arm wraps the
`box` in a `pair_elim` node — see `WFF.pairElim_box_is_stuck`), so the pair
operation does not cancel.  The correct picture is NATURALITY of `substVar` in
the context's pair-decomposition (the peel-step) composed with the box-commutation
on the pair-free base — NOT a conjugation by an involution (`unpair` and `pairElim`
are not inverse on a `box`).  (For this specific lemma the wrapped `pair_elim`s
happen to be vacuous, so the clean form still holds semantically; for a general
box-typed substituted term the pair components can be semantically active.)

Building blocks proved here: pass-through sublemmas `Term.unpair_boxterm`,
`WFF.unpair_box`; the stuck `WFF.pairElim_box_is_stuck`; side-condition
derivations `box_hsub_insert` / `box_extras_insert`; peel bookkeeping
`boxsub_peel` / `extras_peel` / `prod_not_box_of_mem` / `phi_cast_eq` /
`box_ctx_cast`; and local copies of two `private` v8 cast helpers
(`eqRec_fun3_local`, `box_ctx_rest_MU_cast_local`, `VarCtx_ext_local`).
Axiom trail of both main lemmas: `propext, Classical.choice, Quot.sound`.
-/

variable {V W : VarCtx} {x : VarSymb × VarType}

/-- Derive the LHS `box`'s subset condition from the single `hsub`. -/
lemma box_hsub_insert (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W) (hsub : (VarCtx_box V).1 ⊆ W.1) :
    (VarCtx_box (VarCtx_insert x V hx)).1
      ⊆ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1 := by
  rw [VarCtx_box_fst_insert x V hx]
  exact Finset.insert_subset_insert _ hsub

/-- Derive the LHS `box`'s no-box-extras condition from the single `h_no_box_extras`. -/
lemma box_extras_insert (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (h_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1) :
    ∀ p ∈ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1, VarType.isBox p.2 = true
      → p ∈ (VarCtx_box (VarCtx_insert x V hx)).1 := by
  intro p hp hbox
  rw [VarCtx_box_fst_insert x V hx]
  rcases Finset.mem_insert.mp hp with h_eq | h_inW
  · exact Finset.mem_insert.mpr (Or.inl h_eq)
  · exact Finset.mem_insert.mpr (Or.inr (h_extras p h_inW hbox))

/-! ### Pass-through sublemmas (checkpoints)

`Term.unpair` and `WFF.unpair` are the identity on the modal formers
`boxterm` / `box` (they only re-index the ambient context and re-derive the
proof-irrelevant side conditions).  Both close by `unfold …; rfl`
(definitional proof-irrelevance on the `⊆` / `∀ … → … ∈ …` Prop arguments).
These are sublemmas (a) and (b) from the proof architecture. -/

/-- Sublemma (a): `Term.unpair` passes through a `boxterm`, keeping the same
    inner term. -/
private theorem Term.unpair_boxterm {σ : Signature} (z : VarSymb) (V1 V2 : VarType)
    (v1 v2 : VarSymb) (V₀ W₁ W₂ : VarCtx) (S : VarType)
    (hz : z ∉ VarCtx_to_VarSymbs V₀)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V₀) (hv2 : v2 ∉ VarCtx_to_VarSymbs V₀)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V₀ hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V₀ hv1 hv2 hv1v2)
    {Vt : VarCtx} (t : Term σ Vt S)
    (hsub : (VarCtx_box Vt).1 ⊆ W₁.1)
    (h : ∀ p ∈ W₁.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box Vt).1)
    (hnb1 : v1 ∉ Term.boundVars (Term.boxterm t hsub h))
    (hnb2 : v2 ∉ Term.boundVars (Term.boxterm t hsub h))
    (hsub' : (VarCtx_box Vt).1 ⊆ W₂.1)
    (h' : ∀ p ∈ W₂.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box Vt).1) :
    Term.unpair z V1 V2 v1 v2 V₀ W₁ W₂ S.VTypeBox hz hv1 hv2 hv1v2 W₁def W₂def
        (Term.boxterm t hsub h) hnb1 hnb2
      = Term.boxterm t hsub' h' := by
  unfold Term.unpair; rfl

/-- Sublemma (b): `WFF.unpair` passes through a `box`, keeping the same inner
    formula. -/
private theorem WFF.unpair_box {σ : Signature} (z : VarSymb) (V1 V2 : VarType)
    (v1 v2 : VarSymb) (V₀ W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V₀)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V₀) (hv2 : v2 ∉ VarCtx_to_VarSymbs V₀)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V₀ hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V₀ hv1 hv2 hv1v2)
    {Vi : VarCtx} (ψ : WFF σ Vi)
    (hsub : (VarCtx_box Vi).1 ⊆ W₁.1)
    (h : ∀ p ∈ W₁.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box Vi).1)
    (hnb1 : v1 ∉ WFF.boundVars (WFF.box ψ hsub h))
    (hnb2 : v2 ∉ WFF.boundVars (WFF.box ψ hsub h))
    (hsub' : (VarCtx_box Vi).1 ⊆ W₂.1)
    (h' : ∀ p ∈ W₂.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box Vi).1) :
    WFF.unpair z V1 V2 v1 v2 V₀ W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def
        (WFF.box ψ hsub h) hnb1 hnb2
      = WFF.box ψ hsub' h' := by
  unfold WFF.unpair; rfl

/-- Sublemma (c), CORRECTED.  Contrary to the proof architecture in the top
    docstring, `WFF.pairElim` does NOT pass through a `box`: its box arm
    (`QML_Full_v8.lean` line 5038) is a "stuck" arm that WRAPS the box in a
    `WFF.pair_elim` node.  This is the exact obstruction that makes the general
    keystone lemma FALSE — see the comment on `substVar_boxterm_box_gen`. -/
private theorem WFF.pairElim_box_is_stuck {σ : Signature} {V₀ W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V₀) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V₀)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V₀)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V₀ hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V₀ hz = W₂)
    {Vi : VarCtx} (φ : WFF σ Vi)
    (hsub : (VarCtx_box Vi).1 ⊆ W₁.1)
    (hnbe : ∀ p ∈ W₁.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box Vi).1) :
    WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq (WFF.box φ hsub hnbe)
      = WFF.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq (WFF.box φ hsub hnbe) := by
  unfold WFF.pairElim; rfl

/-! ### Local (non-`private`) copies of two v8 cast helpers.

`eqRec_fun3` and `box_ctx_rest_MU_cast` are `private` in `QML_Full_v8.lean`, so
they cannot be named from this file.  We re-derive verbatim copies. -/

/-- Local copy of v8's private `VarCtx_ext`. -/
private lemma VarCtx_ext_local (V W : VarCtx) (h : V.1 = W.1) : V = W := by
  obtain ⟨v, pv⟩ := V
  obtain ⟨w, pw⟩ := W
  subst h
  exact congrArg (PSigma.mk v) (proof_irrel pv pw)

/-- Local copy of v8's `eqRec_fun3`. -/
private theorem eqRec_fun3_local {α : Sort u} {a b : α}
    {F1 : α → Sort v1} {F2 : α → Sort v2} {F3 : α → Sort v3} {C : Sort w}
    (g : F1 a → F2 a → F3 a → C) (h : a = b)
    (u1 : F1 b) (u2 : F2 b) (u3 : F3 b) :
    (Eq.rec (motive := fun z _ => F1 z → F2 z → F3 z → C) g h) u1 u2 u3
      = g (h ▸ u1) (h ▸ u2) (h ▸ u3) := by
  subst h; rfl

/-- Local copy of v8's `box_ctx_rest_MU_cast`. -/
private theorem box_ctx_rest_MU_cast_local {σ : Signature} {E V Wout : VarCtx}
    {x : VarSymb} {S : VarType} (hEV : E = V)
    (hxE : x ∉ VarCtx_to_VarSymbs E) (hxV : x ∉ VarCtx_to_VarSymbs V)
    (tE : Term σ E S) (tV : Term σ V S) (ht : HEq tE tV)
    (ψE : WFF σ (VarCtx_insert ⟨x, S⟩ E hxE))
    (ψV : WFF σ (VarCtx_insert ⟨x, S⟩ V hxV)) (hψ : HEq ψE ψV)
    (p1 : (VarCtx_box E).1 ⊆ Wout.1)
    (q1 : ∀ p ∈ Wout.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box E).1)
    (p2 : (VarCtx_box V).1 ⊆ Wout.1)
    (q2 : ∀ p ∈ Wout.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1) :
    WFF.box (WFF.ctx_rest_MU hxE tE ψE).val p1 q1
      = WFF.box (WFF.ctx_rest_MU hxV tV ψV).val p2 q2 := by
  subst hEV
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hψ
  rfl

/-! ### LEMMA 1 — GENERAL BASE CASE (pair-free outer context). -/

/-- The clean `substVar`/`box` commutation for an ARBITRARY ambient `W` whose
    insert is pair-free (`firstPairVar = none`).  Generalises the v8 special
    case `WFF.substVar_boxterm_box` (which fixed `W = VarCtx_box V`). -/
theorem WFF.substVar_boxterm_box_gen_base {σ : Signature}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hpf : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar = none)
    (t : Term σ V x.2)
    (φ : WFF σ (VarCtx_insert x V hx)) :
    WFF.substVar hxW (Term.boxterm t hsub h_no_box_extras)
        (WFF.box φ (box_hsub_insert hx hxW hsub)
                   (box_extras_insert hx hxW h_no_box_extras))
      = WFF.box (WFF.substVar hx t φ) hsub h_no_box_extras := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_box_arm]
    have hx_in : x.1 ∈ VarCtx_to_VarSymbs (VarCtx_insert x V hx) := by
      rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_self _ _
    have hxS_in : (⟨x.1, x.2⟩ : VarSymb × VarType) ∈ (VarCtx_insert x V hx).fst :=
      Finset.mem_insert_self _ _
    rw [dif_pos hx_in, dif_pos hxS_in]
    rw [eqRec_fun3_local (F1 := fun z => Term σ z x.2)
          (F2 := fun z => (VarCtx_box z).fst ⊆ W.fst)
          (F3 := fun z => ∀ p ∈ W.fst,
                    VarType.isBox p.2 = true → p ∈ (VarCtx_box z).fst)]
    dsimp only
    refine box_ctx_rest_MU_cast_local ?_ _ hx _ t ?_ _ φ ?_ _ _ hsub h_no_box_extras
    · apply VarCtx_ext_local
      change (insert (x : VarSymb × VarType) V.1).erase x = V.1
      exact Finset.erase_insert
        (fun hmem => hx (Finset.mem_image.mpr ⟨_, hmem, rfl⟩))
    · exact eqRec_heq (φ := fun z => Term σ z x.2) _ t
    · exact eqRec_heq (φ := fun z => WFF σ z) _ φ
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

/-! ### LEMMA 2 — PEEL STEP.

Helper lemmas: casting a `box` through a context equality, and the two
"peeling preserves the boxterm/box side conditions" facts. -/

/-- Casting a `box` along an equality of its ambient context yields the same
    `box` (with proof-irrelevant side conditions). -/
private theorem box_ctx_cast {σ : Signature} {V_inner Wa Wb : VarCtx}
    (h : Wa = Wb) (φ : WFF σ V_inner)
    (P : (VarCtx_box V_inner).1 ⊆ Wa.1)
    (Q : ∀ p ∈ Wa.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (P' : (VarCtx_box V_inner).1 ⊆ Wb.1)
    (Q' : ∀ p ∈ Wb.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    (h ▸ WFF.box φ P Q : WFF σ Wb) = WFF.box φ P' Q' := by
  subst h; rfl

/-- A pair-typed member `⟨z, V1 ×ᵥ V2⟩` of an ambient with `no_box_extras` must
    be non-box (else it would be forced into the box image, impossible). -/
private theorem prod_not_box_of_mem {V W : VarCtx} {z : VarSymb} {V1 V2 : VarType}
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hzmem_V : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W.1) :
    (V1.VTypeProd V2).isBox = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have hin := h_no_box_extras _ hzmem_V h
  rcases Finset.mem_image.mp hin with ⟨⟨_, _⟩, _, hveq⟩
  exact VarType.noConfusion (Prod.mk.inj hveq).2

/-- H1: `VarCtx_box V ⊆ W` survives peeling `⟨z, V1×V2⟩` and adding `v1,v2`. -/
private theorem boxsub_peel {V W : VarCtx} {z : VarSymb} {V1 V2 : VarType}
    {v1 v2 : VarSymb}
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs (VarCtx_erase W ⟨z, V1.VTypeProd V2⟩))
    (hv2 : v2 ∉ VarCtx_to_VarSymbs (VarCtx_erase W ⟨z, V1.VTypeProd V2⟩))
    (hv1v2 : v1 ≠ v2) :
    (VarCtx_box V).1 ⊆ (VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
        (VarCtx_erase W ⟨z, V1.VTypeProd V2⟩) hv1 hv2 hv1v2).1 := by
  intro q hq
  have hqW : q ∈ W.1 := hsub hq
  rcases Finset.mem_image.mp hq with ⟨⟨qv, qS⟩, _, hqeq⟩
  change q ∈ insert (⟨v1, V1⟩ : VarSymb × VarType)
      (insert ⟨v2, V2⟩ (W.1.erase ⟨z, V1.VTypeProd V2⟩))
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
  refine Finset.mem_erase.mpr ⟨?_, hqW⟩
  rw [← hqeq]
  intro hcontra
  exact VarType.noConfusion (Prod.mk.inj hcontra).2

/-- H2: the `no_box_extras` condition survives peeling `⟨z, V1×V2⟩` and adding
    `v1,v2` (which are non-box because `⟨z, V1×V2⟩` is non-box). -/
private theorem extras_peel {V W : VarCtx} {z : VarSymb} {V1 V2 : VarType}
    {v1 v2 : VarSymb}
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hzmem_V : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W.1)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs (VarCtx_erase W ⟨z, V1.VTypeProd V2⟩))
    (hv2 : v2 ∉ VarCtx_to_VarSymbs (VarCtx_erase W ⟨z, V1.VTypeProd V2⟩))
    (hv1v2 : v1 ≠ v2) :
    ∀ p ∈ (VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
        (VarCtx_erase W ⟨z, V1.VTypeProd V2⟩) hv1 hv2 hv1v2).1,
      VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1 := by
  have hprod : (V1.VTypeProd V2).isBox = false :=
    prod_not_box_of_mem h_no_box_extras hzmem_V
  simp only [VarType.isBox, decide_eq_false_iff_not, not_or, Bool.not_eq_true] at hprod
  obtain ⟨hV1, hV2⟩ := hprod
  intro p hp hbox
  change p ∈ insert (⟨v1, V1⟩ : VarSymb × VarType)
      (insert ⟨v2, V2⟩ (W.1.erase ⟨z, V1.VTypeProd V2⟩)) at hp
  rcases Finset.mem_insert.mp hp with rfl | hp2
  · rw [hV1] at hbox; exact absurd hbox (by simp)
  · rcases Finset.mem_insert.mp hp2 with rfl | hp3
    · rw [hV2] at hbox; exact absurd hbox (by simp)
    · exact h_no_box_extras p (Finset.erase_subset _ _ hp3) hbox

/-- Combined cast/unpair/cast normal form of the internally-unpaired `φ'_cast`:
    `Ctx_cast ▸ (WFF.unpair … (Ctx_cast ▸ box φ P Q)) = box φ P' Q'`.  Both casts
    are discharged by `subst`, leaving sublemma (b) `WFF.unpair_box`. -/
private theorem phi_cast_eq {σ : Signature} {V_inner Va Cc Cd : VarCtx}
    (z v1 v2 : VarSymb) (V1 V2 : VarType)
    (hz : z ∉ VarCtx_to_VarSymbs Va)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs Va) (hv2 : v2 ∉ VarCtx_to_VarSymbs Va)
    (hv1v2 : v1 ≠ v2)
    (φ : WFF σ V_inner)
    (P : (VarCtx_box V_inner).1 ⊆ Cc.1)
    (Q : ∀ p ∈ Cc.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (hc1 : Cc = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ Va hz)
    (hnb1 : v1 ∉ WFF.boundVars (hc1 ▸ WFF.box φ P Q))
    (hnb2 : v2 ∉ WFF.boundVars (hc1 ▸ WFF.box φ P Q))
    (hc2 : VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ Va hv1 hv2 hv1v2 = Cd)
    (P' : (VarCtx_box V_inner).1 ⊆ Cd.1)
    (Q' : ∀ p ∈ Cd.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    (hc2 ▸ WFF.unpair z V1 V2 v1 v2 Va
        (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ Va hz)
        (VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ Va hv1 hv2 hv1v2)
        hz hv1 hv2 hv1v2 rfl rfl (hc1 ▸ WFF.box φ P Q) hnb1 hnb2)
      = WFF.box φ P' Q' := by
  subst hc2
  subst hc1
  exact WFF.unpair_box z V1 V2 v1 v2 Va _ _ hz hv1 hv2 hv1v2 rfl rfl φ P Q
    hnb1 hnb2 P' Q'

/-- The peel step: for a pair var `z ≠ x.1` in `W`, `substVar` over `W` peels
    `z` with a `pairElim` and continues as a `substVar` over the unpaired
    context `W ∖ z ∪ {v1,v2}`, still of `boxterm t` / `box φ`. -/
theorem WFF.substVar_boxterm_box_gen_peel {σ : Signature}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (t : Term σ V x.2)
    (φ : WFF σ (VarCtx_insert x V hx))
    (z : VarSymb) (V1 V2 : VarType)
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
              ∈ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1)
    (hfp : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar
              = some ⟨(z, V1, V2), hzmem⟩) :
    WFF.substVar hxW (Term.boxterm t hsub h_no_box_extras)
        (WFF.box φ (box_hsub_insert hx hxW hsub)
                   (box_extras_insert hx hxW h_no_box_extras))
      =
      (have hzmem_V : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W.1 := by
        rcases Finset.mem_insert.mp hzmem with heq2 | hin
        · exact absurd (Prod.mk.inj heq2).2 (by simp)
        · exact hin
       let V_minus_z := VarCtx_erase W ⟨z, V1.VTypeProd V2⟩
       have hz_fresh : z ∉ VarCtx_to_VarSymbs V_minus_z := VarCtx_erase_fresh hzmem_V
       have V_eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z hz_fresh = W :=
         VarCtx_insert_erase hzmem_V hz_fresh
       let avoid : Finset VarSymb :=
         VarCtx_to_VarSymbs W ∪ {x.1}
           ∪ Term.boundVars (Term.boxterm t hsub h_no_box_extras)
           ∪ WFF.boundVars (WFF.box φ (box_hsub_insert hx hxW hsub)
                             (box_extras_insert hx hxW h_no_box_extras))
       let v1 : VarSymb := VarSymb.fresh avoid
       have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem avoid
       let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
       have hv2_avoid_v1 : v2 ∉ insert v1 avoid := VarSymb.fresh_not_mem (insert v1 avoid)
       have hv2_avoid : v2 ∉ avoid := fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
       have hv1v2_ne : v1 ≠ v2 := fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
       have h_avoid_V : VarCtx_to_VarSymbs W ⊆ avoid := fun y h =>
         Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
       have h_avoid_x : x.1 ∈ avoid := Finset.mem_union_left _
         (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)))
       have hv1_V : v1 ∉ VarCtx_to_VarSymbs W := fun h => hv1_avoid (h_avoid_V h)
       have hv2_V : v2 ∉ VarCtx_to_VarSymbs W := fun h => hv2_avoid (h_avoid_V h)
       have hv1_Vmz : v1 ∉ VarCtx_to_VarSymbs V_minus_z :=
         fun h => hv1_V (VarCtx_to_VarSymbs_erase_subset h)
       have hv2_Vmz : v2 ∉ VarCtx_to_VarSymbs V_minus_z :=
         fun h => hv2_V (VarCtx_to_VarSymbs_erase_subset h)
       have hx_Vmz : x.1 ∉ VarCtx_to_VarSymbs V_minus_z :=
         fun h => hxW (VarCtx_to_VarSymbs_erase_subset h)
       have hv1_x_ne : v1 ≠ x.1 := fun h => hv1_avoid (h ▸ h_avoid_x)
       have hv2_x_ne : v2 ≠ x.1 := fun h => hv2_avoid (h ▸ h_avoid_x)
       have hx_Vmz_v1v2 : x.1 ∉ VarCtx_to_VarSymbs
           (VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne) :=
         not_mem_VarSymbs_insert_twice (fun h => hv1_x_ne h.symm)
           (fun h => hv2_x_ne h.symm) hx_Vmz
       have H1 : (VarCtx_box V).1 ⊆ (VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
           V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne).1 :=
         boxsub_peel hsub hv1_Vmz hv2_Vmz hv1v2_ne
       have H2 : ∀ p ∈ (VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
           V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne).1,
           VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1 :=
         extras_peel h_no_box_extras hzmem_V hv1_Vmz hv2_Vmz hv1v2_ne
       V_eq ▸ WFF.pairElim ⟨v1, V1⟩ ⟨v2, V2⟩ z hv1_Vmz hv2_Vmz hv1v2_ne hz_fresh rfl rfl
         (WFF.substVar hx_Vmz_v1v2 (Term.boxterm t H1 H2)
           (WFF.box φ (box_hsub_insert hx hx_Vmz_v1v2 H1)
             (box_extras_insert hx hx_Vmz_v1v2 H2)))) := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · rename_i hn
    exact absurd (hn.symm.trans hfp) (by simp)
  · rename_i z' V1' V2' hzmem' heq'
    have hzx' : ¬ z' = x.1 := by
      intro h
      rcases Finset.mem_insert.mp hzmem' with heq2 | hin
      · exact VarType.noConfusion (Prod.mk.inj heq2).2
      · exact hxW (Finset.mem_image.mpr ⟨_, hin, h⟩)
    rw [dif_neg hzx']
    obtain ⟨rfl, rfl, rfl⟩ : z' = z ∧ V1' = V1 ∧ V2' = V2 := by
      have h := Option.some.inj (heq'.symm.trans hfp)
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    -- Reconstruct the Case B data (proofs are proof-irrelevant, so any witness
    -- yields a value definitionally equal to the internal one).
    have hzmem_V : (⟨z', V1'.VTypeProd V2'⟩ : VarSymb × VarType) ∈ W.1 := by
      rcases Finset.mem_insert.mp hzmem' with heq2 | hin
      · exact absurd (Prod.mk.inj heq2).2 (by simp)
      · exact hin
    let V_minus_z := VarCtx_erase W ⟨z', V1'.VTypeProd V2'⟩
    have hz_fresh : z' ∉ VarCtx_to_VarSymbs V_minus_z := VarCtx_erase_fresh hzmem_V
    have V_eq : VarCtx_insert ⟨z', V1'.VTypeProd V2'⟩ V_minus_z hz_fresh = W :=
      VarCtx_insert_erase hzmem_V hz_fresh
    let avoid : Finset VarSymb :=
      VarCtx_to_VarSymbs W ∪ {x.1}
        ∪ Term.boundVars (Term.boxterm t hsub h_no_box_extras)
        ∪ WFF.boundVars (WFF.box φ (box_hsub_insert hx hxW hsub)
                          (box_extras_insert hx hxW h_no_box_extras))
    let v1 : VarSymb := VarSymb.fresh avoid
    have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem avoid
    let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
    have hv2_avoid_v1 : v2 ∉ insert v1 avoid := VarSymb.fresh_not_mem (insert v1 avoid)
    have hv2_avoid : v2 ∉ avoid := fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
    have hv1v2_ne : v1 ≠ v2 := fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
    have h_avoid_V : VarCtx_to_VarSymbs W ⊆ avoid := fun y h =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have h_avoid_x : x.1 ∈ avoid := Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)))
    have h_avoid_s : Term.boundVars (Term.boxterm t hsub h_no_box_extras) ⊆ avoid :=
      fun y h => Finset.mem_union_left _ (Finset.mem_union_right _ h)
    have h_avoid_φ : WFF.boundVars (WFF.box φ (box_hsub_insert hx hxW hsub)
        (box_extras_insert hx hxW h_no_box_extras)) ⊆ avoid := fun y h =>
      Finset.mem_union_right _ h
    have hv1_V : v1 ∉ VarCtx_to_VarSymbs W := fun h => hv1_avoid (h_avoid_V h)
    have hv2_V : v2 ∉ VarCtx_to_VarSymbs W := fun h => hv2_avoid (h_avoid_V h)
    have hv1_Vmz : v1 ∉ VarCtx_to_VarSymbs V_minus_z :=
      fun h => hv1_V (VarCtx_to_VarSymbs_erase_subset h)
    have hv2_Vmz : v2 ∉ VarCtx_to_VarSymbs V_minus_z :=
      fun h => hv2_V (VarCtx_to_VarSymbs_erase_subset h)
    have hx_Vmz : x.1 ∉ VarCtx_to_VarSymbs V_minus_z :=
      fun h => hxW (VarCtx_to_VarSymbs_erase_subset h)
    have hv1_x_ne : v1 ≠ x.1 := fun h => hv1_avoid (h ▸ h_avoid_x)
    have hv2_x_ne : v2 ≠ x.1 := fun h => hv2_avoid (h ▸ h_avoid_x)
    have hv1_nb_φ : v1 ∉ WFF.boundVars (WFF.box φ (box_hsub_insert hx hxW hsub)
        (box_extras_insert hx hxW h_no_box_extras)) := fun h => hv1_avoid (h_avoid_φ h)
    have hv2_nb_φ : v2 ∉ WFF.boundVars (WFF.box φ (box_hsub_insert hx hxW hsub)
        (box_extras_insert hx hxW h_no_box_extras)) := fun h => hv2_avoid (h_avoid_φ h)
    have hv1_nb_s : v1 ∉ Term.boundVars (Term.boxterm t hsub h_no_box_extras) :=
      fun h => hv1_avoid (h_avoid_s h)
    have hv2_nb_s : v2 ∉ Term.boundVars (Term.boxterm t hsub h_no_box_extras) :=
      fun h => hv2_avoid (h_avoid_s h)
    have hx_Vmz_v1v2 : x.1 ∉ VarCtx_to_VarSymbs
        (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne) :=
      not_mem_VarSymbs_insert_twice (fun h => hv1_x_ne h.symm)
        (fun h => hv2_x_ne h.symm) hx_Vmz
    have H1 : (VarCtx_box V).1 ⊆ (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩
        V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne).1 :=
      boxsub_peel hsub hv1_Vmz hv2_Vmz hv1v2_ne
    have H2 : ∀ p ∈ (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩
        V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne).1,
        VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1 :=
      extras_peel h_no_box_extras hzmem_V hv1_Vmz hv2_Vmz hv1v2_ne
    have hx_Vmz_gen : x.1 ∉ VarCtx_to_VarSymbs V_minus_z := hx_Vmz
    let V_minus_z_x : VarCtx := VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ V_minus_z hx_Vmz_gen
    have hz_Vmz_x : z' ∉ VarCtx_to_VarSymbs V_minus_z_x :=
      not_mem_VarSymbs_insert hzx' hz_fresh
    have hv1_Vmz_x : v1 ∉ VarCtx_to_VarSymbs V_minus_z_x :=
      not_mem_VarSymbs_insert hv1_x_ne hv1_Vmz
    have hv2_Vmz_x : v2 ∉ VarCtx_to_VarSymbs V_minus_z_x :=
      not_mem_VarSymbs_insert hv2_x_ne hv2_Vmz
    have h_cast_φ : VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW
        = VarCtx_insert ⟨z', V1'.VTypeProd V2'⟩ V_minus_z_x hz_Vmz_x := by
      apply VarCtx_ext_local
      change insert (⟨x.1, x.2.VTypeBox⟩ : VarSymb × VarType) W.1
           = insert (⟨z', V1'.VTypeProd V2'⟩ : VarSymb × VarType)
               (insert ⟨x.1, x.2.VTypeBox⟩ V_minus_z.1)
      rw [show W.1 = insert (⟨z', V1'.VTypeProd V2'⟩ : VarSymb × VarType) V_minus_z.1
            from (Finset.insert_erase hzmem_V).symm]
      exact Finset.insert_comm _ _ _
    let φ_cast : WFF σ (VarCtx_insert ⟨z', V1'.VTypeProd V2'⟩ V_minus_z_x hz_Vmz_x) :=
      h_cast_φ ▸ WFF.box φ (box_hsub_insert hx hxW hsub)
                          (box_extras_insert hx hxW h_no_box_extras)
    have hv1_nb_φ_cast : v1 ∉ WFF.boundVars φ_cast := by
      show v1 ∉ WFF.boundVars (h_cast_φ ▸ WFF.box φ (box_hsub_insert hx hxW hsub)
                                (box_extras_insert hx hxW h_no_box_extras))
      rw [WFF.boundVars_ctx_cast]; exact hv1_nb_φ
    have hv2_nb_φ_cast : v2 ∉ WFF.boundVars φ_cast := by
      show v2 ∉ WFF.boundVars (h_cast_φ ▸ WFF.box φ (box_hsub_insert hx hxW hsub)
                                (box_extras_insert hx hxW h_no_box_extras))
      rw [WFF.boundVars_ctx_cast]; exact hv2_nb_φ
    let φ' : WFF σ (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z_x
        hv1_Vmz_x hv2_Vmz_x hv1v2_ne) :=
      WFF.unpair z' V1' V2' v1 v2 V_minus_z_x
        (VarCtx_insert ⟨z', V1'.VTypeProd V2'⟩ V_minus_z_x hz_Vmz_x)
        (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z_x hv1_Vmz_x hv2_Vmz_x hv1v2_ne)
        hz_Vmz_x hv1_Vmz_x hv2_Vmz_x hv1v2_ne rfl rfl φ_cast hv1_nb_φ_cast hv2_nb_φ_cast
    have h_cast_φ' : VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z_x
        hv1_Vmz_x hv2_Vmz_x hv1v2_ne
        = VarCtx_insert ⟨x.1, x.2.VTypeBox⟩
            (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne)
            hx_Vmz_v1v2 := by
      apply VarCtx_ext_local
      change insert (⟨v1, V1'⟩ : VarSymb × VarType)
          (insert ⟨v2, V2'⟩ (insert ⟨x.1, x.2.VTypeBox⟩ V_minus_z.1))
        = insert (⟨x.1, x.2.VTypeBox⟩ : VarSymb × VarType)
          (insert ⟨v1, V1'⟩ (insert ⟨v2, V2'⟩ V_minus_z.1))
      rw [Finset.insert_comm (⟨v2, V2'⟩ : VarSymb × VarType) ⟨x.1, x.2.VTypeBox⟩,
          Finset.insert_comm (⟨v1, V1'⟩ : VarSymb × VarType) ⟨x.1, x.2.VTypeBox⟩]
    let φ'_cast : WFF σ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩
        (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne)
        hx_Vmz_v1v2) := h_cast_φ' ▸ φ'
    let s' : Term σ (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z
        hv1_Vmz hv2_Vmz hv1v2_ne) x.2.VTypeBox :=
      Term.unpair z' V1' V2' v1 v2 V_minus_z W
        (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne)
        x.2.VTypeBox hz_fresh hv1_Vmz hv2_Vmz hv1v2_ne V_eq.symm rfl
        (Term.boxterm t hsub h_no_box_extras) hv1_nb_s hv2_nb_s
    have hs' : s' = Term.boxterm t H1 H2 :=
      Term.unpair_boxterm z' V1' V2' v1 v2 V_minus_z W
        (VarCtx_insert_twice ⟨v1, V1'⟩ ⟨v2, V2'⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne)
        x.2 hz_fresh hv1_Vmz hv2_Vmz hv1v2_ne V_eq.symm rfl t hsub h_no_box_extras
        hv1_nb_s hv2_nb_s H1 H2
    have hφ' : φ'_cast = WFF.box φ (box_hsub_insert hx hx_Vmz_v1v2 H1)
        (box_extras_insert hx hx_Vmz_v1v2 H2) :=
      phi_cast_eq z' v1 v2 V1' V2' hz_Vmz_x hv1_Vmz_x hv2_Vmz_x hv1v2_ne φ
        (box_hsub_insert hx hxW hsub) (box_extras_insert hx hxW h_no_box_extras)
        h_cast_φ hv1_nb_φ_cast hv2_nb_φ_cast h_cast_φ'
        (box_hsub_insert hx hx_Vmz_v1v2 H1) (box_extras_insert hx hx_Vmz_v1v2 H2)
    show V_eq ▸ WFF.pairElim ⟨v1, V1'⟩ ⟨v2, V2'⟩ z' hv1_Vmz hv2_Vmz hv1v2_ne hz_fresh
        rfl rfl (WFF.ctx_rest_MU hx_Vmz_v1v2 s' φ'_cast).val = _
    rw [hs', hφ']

/-! ### DIA analogs of the box-substitution lemmas.

`substVar` of a `boxterm` for a box-typed variable, pushed through a `WFF.dia`.
Controlled by `WFF.ctx_rest_dia_arm` (v8).  Case 2 (`xv.1 ≠ x`, `x ∈ V_inner`,
`S = T.VTypeBox`) is the "box-like" recursion — LEMMA D1 below.  Case 3
(`xv.1 = x`, so `S = xv.2.VTypeDia` and the substituted term is a `diaterm`) is
the modal-β reduction with no box analog — LEMMA D2 below.

Side-condition derivations for the `dia`: unlike the box case, a `dia` also
carries its designated witness `⟨xv.1, xv.2.VTypeDia⟩`, which is NOT covered by
`hsub`; it must be supplied separately (`hxv_amb`).  -/

/-- Derive the LHS `dia`'s subset condition (over `V_inner = insert x V`) from
    `hsub` plus the witness membership `hxv_amb`. -/
lemma dia_hsub_insert (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W) (hsub : (VarCtx_box V).1 ⊆ W.1)
    {xv : VarSymb × VarType}
    (hxv_outer : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx))
    (hxv_amb : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈ W.1) :
    (VarCtx_dia xv (VarCtx_insert x V hx) hxv_outer).1
      ⊆ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1 := by
  rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
  intro p hp
  change p ∈ insert (⟨x.1, x.2.VTypeBox⟩ : VarSymb × VarType) W.1
  rcases Finset.mem_insert.mp hp with h_eq | hp2
  · subst h_eq; exact Finset.mem_insert_of_mem hxv_amb
  · rcases Finset.mem_insert.mp hp2 with h_eq2 | hp3
    · exact Finset.mem_insert.mpr (Or.inl h_eq2)
    · exact Finset.mem_insert_of_mem (hsub hp3)

/-- Derive the LHS `dia`'s no-box-extras condition from `h_no_box_extras`. -/
lemma dia_extras_insert (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (h_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    {xv : VarSymb × VarType}
    (hxv_outer : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx)) :
    ∀ p ∈ (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).1, VarType.isBox p.2 = true
      → p ∈ (VarCtx_dia xv (VarCtx_insert x V hx) hxv_outer).1 := by
  intro p hp hbox
  rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
  rcases Finset.mem_insert.mp hp with h_eq | hp2
  · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h_eq))
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (h_extras p hp2 hbox))

/-- Derive the RHS `dia`'s subset condition (over `V`) from `hsub` + witness. -/
lemma dia_hsub_base (hsub : (VarCtx_box V).1 ⊆ W.1)
    {xv : VarSymb × VarType} (hxv_V : xv.1 ∉ VarCtx_to_VarSymbs V)
    (hxv_amb : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈ W.1) :
    (VarCtx_dia xv V hxv_V).1 ⊆ W.1 := by
  rw [VarCtx_dia_fst]
  intro p hp
  rcases Finset.mem_insert.mp hp with h_eq | hp_box
  · subst h_eq; exact hxv_amb
  · exact hsub hp_box

/-- Derive the RHS `dia`'s no-box-extras condition from `h_no_box_extras`. -/
lemma dia_extras_base
    (h_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    {xv : VarSymb × VarType} (hxv_V : xv.1 ∉ VarCtx_to_VarSymbs V) :
    ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V hxv_V).1 := by
  intro p hp hbox
  rw [VarCtx_dia_fst]
  exact Finset.mem_insert_of_mem (h_extras p hp hbox)

/-- Dia analog of `box_ctx_rest_MU_cast_local`: recasting the recursive
    `ctx_rest_MU` result along `E = V`, wrapped in `.dia xv`.  The lifted term is
    `Term.ctx_ext xv _`-ed inside the lemma, so the caller supplies the plain
    inner term (transported by `HEq`, dischargeable by `eqRec_heq` exactly like
    the box base); the reordered body is transported likewise.  The `dia`'s side
    conditions are proof-irrelevant. -/
private theorem dia_ctx_rest_MU_cast {σ : Signature} {E V Wout : VarCtx}
    {x : VarSymb} {T : VarType} {xv : VarSymb × VarType} (hEV : E = V)
    (hxvE : xv.1 ∉ VarCtx_to_VarSymbs E) (hxvV : xv.1 ∉ VarCtx_to_VarSymbs V)
    (hxE : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv E hxvE))
    (hxV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxvV))
    (tE : Term σ E T) (tV : Term σ V T) (ht : HEq tE tV)
    (ψE : WFF σ (VarCtx_insert ⟨x, T⟩ (VarCtx_insert xv E hxvE) hxE))
    (ψV : WFF σ (VarCtx_insert ⟨x, T⟩ (VarCtx_insert xv V hxvV) hxV)) (hψ : HEq ψE ψV)
    (p1 : (VarCtx_dia xv E hxvE).1 ⊆ Wout.1)
    (q1 : ∀ p ∈ Wout.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv E hxvE).1)
    (p2 : (VarCtx_dia xv V hxvV).1 ⊆ Wout.1)
    (q2 : ∀ p ∈ Wout.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V hxvV).1) :
    WFF.dia xv hxvE
        (WFF.ctx_rest_MU hxE (Term.ctx_ext xv hxvE tE) ψE).val p1 q1
      = WFF.dia xv hxvV
        (WFF.ctx_rest_MU hxV (Term.ctx_ext xv hxvV tV) ψV).val p2 q2 := by
  subst hEV
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hψ
  rfl

/-! ### LEMMA D1 — DIA BASE CASE (box-like recursion, pair-free outer context).

Case 2 of `WFF.ctx_rest_dia_arm` (`xv.1 ≠ x`, `x ∈ V_inner`, `S = x.2.VTypeBox`,
substituted term a `boxterm`).  Clean commutation of `substVar (boxterm t)` past
`WFF.dia xv`.  Because substituting `x` under the `dia` binder `xv` requires
weakening `t` past `xv` (`Term.ctx_ext`) and reordering the body so `x` is
outermost (`h_reorder ▸ ψ`), the RHS is stated with those two operations — this
is faithful to what the arm computes and is the closest "clean" analog of
`WFF.substVar_boxterm_box_gen_base`.  The `dia`'s designated witness
`⟨xv.1, xv.2.VTypeDia⟩` is not covered by `hsub`; the LHS/RHS side conditions
`P Q P' Q'` are passed explicitly (proof-irrelevant); `dia_hsub_insert` /
`dia_extras_insert` / `dia_hsub_base` / `dia_extras_base` construct canonical
witnesses. -/

theorem WFF.substVar_boxterm_dia_gen_base {σ : Signature}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hpf : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar = none)
    (t : Term σ V x.2)
    (xv : VarSymb × VarType)
    (hxv_ne : xv.1 ≠ x.1)
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
    (Q' : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V hxv_V).1) :
    WFF.substVar hxW (Term.boxterm t hsub h_no_box_extras)
        (WFF.dia xv hxv_outer ψ P Q)
      = WFF.dia xv hxv_V
          (WFF.substVar hx_out (Term.ctx_ext xv hxv_V t) (h_reorder ▸ ψ)) P' Q' := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_dia_arm]
    rw [dif_neg hxv_ne]
    have h_x_in_symb : x.1 ∈ VarCtx_to_VarSymbs (VarCtx_insert x V hx) := by
      rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_self _ _
    have hxT_in : (⟨x.1, x.2⟩ : VarSymb × VarType) ∈ (VarCtx_insert x V hx).fst :=
      Finset.mem_insert_self _ _
    rw [dif_pos h_x_in_symb, dif_pos hxT_in]
    rw [eqRec_fun3_local (F1 := fun z => Term σ z x.2)
          (F2 := fun z => (VarCtx_box z).fst ⊆ W.fst)
          (F3 := fun z => ∀ p ∈ W.fst,
                    VarType.isBox p.2 = true → p ∈ (VarCtx_box z).fst)]
    dsimp only
    refine dia_ctx_rest_MU_cast ?_ _ hxv_V _ hx_out _ t ?_ _ (h_reorder ▸ ψ) ?_ _ _ P' Q'
    · apply VarCtx_ext_local
      change (insert (x : VarSymb × VarType) V.1).erase ⟨x.1, x.2⟩ = V.1
      exact Finset.erase_insert
        (fun hmem => hx (Finset.mem_image.mpr ⟨_, hmem, rfl⟩))
    · exact eqRec_heq (φ := fun z => Term σ z x.2) _ t
    · exact HEq.trans (eqRec_heq (φ := fun z => WFF σ z) _ ψ)
        (eqRec_heq (φ := fun z => WFF σ z) _ ψ).symm
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq


/-- `.val` of a subtype built by eliminating a proof-level `And` (as produced by
    the `obtain ⟨…⟩ := WFF.dia_arm_case3_reorder …` in Case 3) is just the carried
    value, since it does not depend on the `And`'s fields.  `And.rec` on an
    abstract proof does not iota-reduce, so this is proved by `cases`. -/
private theorem subtype_val_and_rec {α : Sort u} {A B : Prop} {Q : α → Prop}
    (p : A ∧ B) (a : α) (g : A → B → Q a) :
    (And.rec (motive := fun _ => {res : α // Q res})
        (fun l r => ⟨a, g l r⟩) p).val = a := by
  obtain ⟨l, r⟩ := p; rfl

/-! ### LEMMA D2 — DIA MODAL-BETA (modal-β reduction; no box analog).

Case 3 of `WFF.ctx_rest_dia_arm` (`xv.1 = x`, so `S = xv.2.VTypeDia` and the
substituted term is a `Term.diaterm`).  The dia-witness IS the substituted
variable, so this is the genuine modal-β reduction with no box analog.  The arm
reorders `ψ` (via `WFF.dia_arm_case3_reorder`), substitutes the diaterm's inner
`tt_s` for `x` into the reordered body, and rewraps `.dia xv_s`.  The statement
is derived faithfully from what the arm computes: the RHS exposes the reorder
helper `WFF.dia_arm_case3_reorder` (its `.1` = freshness, `.2.1` = reordered
body).  The diaterm and the outer dia must share the same inner context
`V_inner` (this is forced inside the arm by `VarCtx_box_inj`; here we take it as
the shared parameter). -/

theorem WFF.substVar_diaterm_dia_gen_base {σ : Signature} {V_inner W : VarCtx}
    (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (hxW : xv.1 ∉ VarCtx_to_VarSymbs W)
    (xv_s : VarSymb × VarType) (hxv_s : xv_s.1 ∉ VarCtx_to_VarSymbs V_inner)
    (h_xv_ne_xv_s : xv.1 ≠ xv_s.1)
    (tt_s : Term σ (VarCtx_insert xv_s V_inner hxv_s) xv.2)
    (hsub_s : (VarCtx_dia xv_s V_inner hxv_s).1 ⊆ W.1)
    (h_no_extras_s : ∀ p ∈ W.1, VarType.isBox p.2 = true
                      → p ∈ (VarCtx_dia xv_s V_inner hxv_s).1)
    (hpf : (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ W hxW).firstPairVar = none)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1
              ⊆ (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ W hxW).1)
    (h_no_extras : ∀ p ∈ (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ W hxW).1,
                    VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    WFF.substVar hxW (Term.diaterm xv_s hxv_s tt_s hsub_s h_no_extras_s)
        (WFF.dia xv hxv ψ hsub h_no_extras)
      = WFF.dia xv_s hxv_s
          (WFF.ctx_rest_MU
            (WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s h_xv_ne_xv_s rfl ψ).1
            tt_s
            (WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s h_xv_ne_xv_s rfl ψ).2.1).val
          hsub_s h_no_extras_s := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_dia_arm]
    rw [dif_pos (show True from trivial)]
    exact subtype_val_and_rec _ _ _
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq



/-! ### GENERIC PEEL STEP.

`WFF.substVar_peel` is `WFF.ctx_rest_MU`'s Case B (v8 lines ~8962–9069, the
`firstPairVar = some ⟨z,V1,V2⟩` with `z ≠ x` branch) in user-facing form: the
pair-handling of `substVar`, factored out and generic over the substituted term
`s : Term σ V S` and the formula `φ`.  It is the strict simplification of
`WFF.substVar_boxterm_box_gen_peel` obtained by generalising `boxterm t → s`,
`box φ → φ` and NOT folding the internally-unpaired `s' = Term.unpair …`,
`φ' = WFF.unpair …` back (those folds, via sublemmas (a)/(b), were the
box-specific specialisation).

NB: unlike the box peel-step, `z ≠ x` cannot be derived here — for a general `S`
the substituted variable `⟨x, S⟩` could itself be the pair var (`S = V1×V2`),
which is Case A, not the peel.  So `h_z_ne_x : z ≠ x` is an explicit hypothesis;
it is precisely the defining condition of Case B. -/
theorem WFF.substVar_peel {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx))
    (z : VarSymb) (V1 V2 : VarType)
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
              ∈ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hfp : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = some ⟨(z, V1, V2), hzmem⟩)
    (h_z_ne_x : z ≠ x) :
    WFF.substVar hx s φ
      =
      (have hzmem_V : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1 := by
        rcases Finset.mem_insert.mp hzmem with h_eq | h_in_V
        · exact absurd (Prod.mk.inj h_eq).1 h_z_ne_x
        · exact h_in_V
       let V_minus_z := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩
       have hz_fresh : z ∉ VarCtx_to_VarSymbs V_minus_z := VarCtx_erase_fresh hzmem_V
       have V_eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z hz_fresh = V :=
         VarCtx_insert_erase hzmem_V hz_fresh
       let avoid : Finset VarSymb :=
         VarCtx_to_VarSymbs V ∪ {x} ∪ Term.boundVars s ∪ WFF.boundVars φ
       let v1 : VarSymb := VarSymb.fresh avoid
       have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem avoid
       let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
       have hv2_avoid_v1 : v2 ∉ insert v1 avoid := VarSymb.fresh_not_mem (insert v1 avoid)
       have hv2_avoid : v2 ∉ avoid := fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
       have hv1v2_ne : v1 ≠ v2 := fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
       have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun y h =>
         Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
       have h_avoid_φ : WFF.boundVars φ ⊆ avoid := fun y h => Finset.mem_union_right _ h
       have h_avoid_s : Term.boundVars s ⊆ avoid := fun y h =>
         Finset.mem_union_left _ (Finset.mem_union_right _ h)
       have h_avoid_x : x ∈ avoid := Finset.mem_union_left _
         (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)))
       have hv1_V : v1 ∉ VarCtx_to_VarSymbs V := fun h => hv1_avoid (h_avoid_V h)
       have hv2_V : v2 ∉ VarCtx_to_VarSymbs V := fun h => hv2_avoid (h_avoid_V h)
       have hv1_Vmz : v1 ∉ VarCtx_to_VarSymbs V_minus_z :=
         fun h => hv1_V (VarCtx_to_VarSymbs_erase_subset h)
       have hv2_Vmz : v2 ∉ VarCtx_to_VarSymbs V_minus_z :=
         fun h => hv2_V (VarCtx_to_VarSymbs_erase_subset h)
       have hv1_x_ne : v1 ≠ x := fun h => hv1_avoid (h ▸ h_avoid_x)
       have hv2_x_ne : v2 ≠ x := fun h => hv2_avoid (h ▸ h_avoid_x)
       have hv1_nb_φ : v1 ∉ WFF.boundVars φ := fun h => hv1_avoid (h_avoid_φ h)
       have hv2_nb_φ : v2 ∉ WFF.boundVars φ := fun h => hv2_avoid (h_avoid_φ h)
       have hv1_nb_s : v1 ∉ Term.boundVars s := fun h => hv1_avoid (h_avoid_s h)
       have hv2_nb_s : v2 ∉ Term.boundVars s := fun h => hv2_avoid (h_avoid_s h)
       have hx_Vmz : x ∉ VarCtx_to_VarSymbs V_minus_z :=
         fun h => hx (VarCtx_to_VarSymbs_erase_subset h)
       let V_minus_z_x : VarCtx := VarCtx_insert ⟨x, S⟩ V_minus_z hx_Vmz
       have hz_Vmz_x : z ∉ VarCtx_to_VarSymbs V_minus_z_x :=
         not_mem_VarSymbs_insert h_z_ne_x hz_fresh
       have h_cast_φ :
           VarCtx_insert ⟨x, S⟩ V hx =
           VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z_x hz_Vmz_x := by
         apply VarCtx_ext_local
         change insert (⟨x, S⟩ : VarSymb × VarType) V.1 =
              insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
                (insert ⟨x, S⟩ V_minus_z.1)
         rw [show V.1 = insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) V_minus_z.1
               from (Finset.insert_erase hzmem_V).symm]
         exact Finset.insert_comm _ _ _
       let φ_cast : WFF σ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z_x hz_Vmz_x) :=
         h_cast_φ ▸ φ
       have hv1_Vmz_x : v1 ∉ VarCtx_to_VarSymbs V_minus_z_x :=
         not_mem_VarSymbs_insert hv1_x_ne hv1_Vmz
       have hv2_Vmz_x : v2 ∉ VarCtx_to_VarSymbs V_minus_z_x :=
         not_mem_VarSymbs_insert hv2_x_ne hv2_Vmz
       let V_minus_z_x_v1v2 : VarCtx :=
         VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_minus_z_x hv1_Vmz_x hv2_Vmz_x hv1v2_ne
       have hv1_nb_φ_cast : v1 ∉ WFF.boundVars φ_cast := by
         change v1 ∉ WFF.boundVars (h_cast_φ ▸ φ)
         rw [WFF.boundVars_ctx_cast]; exact hv1_nb_φ
       have hv2_nb_φ_cast : v2 ∉ WFF.boundVars φ_cast := by
         change v2 ∉ WFF.boundVars (h_cast_φ ▸ φ)
         rw [WFF.boundVars_ctx_cast]; exact hv2_nb_φ
       let φ' : WFF σ V_minus_z_x_v1v2 :=
         WFF.unpair z V1 V2 v1 v2 V_minus_z_x _ V_minus_z_x_v1v2
           hz_Vmz_x hv1_Vmz_x hv2_Vmz_x hv1v2_ne rfl rfl φ_cast
           hv1_nb_φ_cast hv2_nb_φ_cast
       let V_minus_z_v1v2 : VarCtx :=
         VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne
       let s' : Term σ V_minus_z_v1v2 S :=
         Term.unpair z V1 V2 v1 v2 V_minus_z V V_minus_z_v1v2 S
           hz_fresh hv1_Vmz hv2_Vmz hv1v2_ne V_eq.symm rfl s hv1_nb_s hv2_nb_s
       have hx_Vmz_v1v2 : x ∉ VarCtx_to_VarSymbs V_minus_z_v1v2 :=
         not_mem_VarSymbs_insert_twice
           (fun h => hv1_x_ne h.symm) (fun h => hv2_x_ne h.symm) hx_Vmz
       have h_cast_φ' :
           V_minus_z_x_v1v2 = VarCtx_insert ⟨x, S⟩ V_minus_z_v1v2 hx_Vmz_v1v2 := by
         apply VarCtx_ext_local
         change insert (⟨v1, V1⟩ : VarSymb × VarType)
                (insert ⟨v2, V2⟩ (insert ⟨x, S⟩ V_minus_z.1)) =
              insert ⟨x, S⟩ (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ V_minus_z.1))
         rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) ⟨x, S⟩,
             Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) ⟨x, S⟩]
       let φ'_cast : WFF σ (VarCtx_insert ⟨x, S⟩ V_minus_z_v1v2 hx_Vmz_v1v2) :=
         h_cast_φ' ▸ φ'
       V_eq ▸ WFF.pairElim ⟨v1, V1⟩ ⟨v2, V2⟩ z
         hv1_Vmz hv2_Vmz hv1v2_ne hz_fresh rfl rfl
         (WFF.substVar hx_Vmz_v1v2 s' φ'_cast)) := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · rename_i hn
    exact absurd (hn.symm.trans hfp) (by simp)
  · rename_i z' V1' V2' hzmem' heq'
    obtain ⟨rfl, rfl, rfl⟩ : z' = z ∧ V1' = V1 ∧ V2' = V2 := by
      have h := Option.some.inj (heq'.symm.trans hfp)
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    rw [dif_neg h_z_ne_x]



/-! ### PAIR-FREE BASE CASES for the propositional connectives and quantifiers.

In the pair-free branch (`firstPairVar = none`), `WFF.substVar hx s φ =
(WFF.ctx_rest hx hpf s φ).val`, and `WFF.ctx_rest` dispatches on `φ`'s head
constructor.  Pairs are handled separately by `WFF.substVar_peel`. -/

/-- In the pair-free branch, `substVar` is exactly `ctx_rest` (the `some` branch
    is impossible; `ctx_rest_MU`'s `none` branch delegates to `ctx_rest`, and the
    two `firstPairVar = none` witnesses are proof-irrelevant). -/
private theorem substVar_eq_ctx_rest {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx))
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) :
    WFF.substVar hx s φ = (WFF.ctx_rest hx hpf s φ).val := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · rfl
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

theorem WFF.substVar_and {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (φ ψ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.substVar hx s (φ.and ψ)
      = (WFF.substVar hx s φ).and (WFF.substVar hx s ψ) := by
  rw [substVar_eq_ctx_rest hx s φ hpf, substVar_eq_ctx_rest hx s ψ hpf,
      substVar_eq_ctx_rest hx s (φ.and ψ) hpf]
  conv_lhs => unfold WFF.ctx_rest

theorem WFF.substVar_or {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (φ ψ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.substVar hx s (φ.or ψ)
      = (WFF.substVar hx s φ).or (WFF.substVar hx s ψ) := by
  rw [substVar_eq_ctx_rest hx s φ hpf, substVar_eq_ctx_rest hx s ψ hpf,
      substVar_eq_ctx_rest hx s (φ.or ψ) hpf]
  conv_lhs => unfold WFF.ctx_rest

theorem WFF.substVar_imp {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (φ ψ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.substVar hx s (φ.imp ψ)
      = (WFF.substVar hx s φ).imp (WFF.substVar hx s ψ) := by
  rw [substVar_eq_ctx_rest hx s φ hpf, substVar_eq_ctx_rest hx s ψ hpf,
      substVar_eq_ctx_rest hx s (φ.imp ψ) hpf]
  conv_lhs => unfold WFF.ctx_rest

theorem WFF.substVar_top {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) :
    WFF.substVar hx s (WFF.top : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) = WFF.top := by
  rw [substVar_eq_ctx_rest hx s WFF.top hpf]
  conv_lhs => unfold WFF.ctx_rest

theorem WFF.substVar_bot {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) :
    WFF.substVar hx s (WFF.bot : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) = WFF.bot := by
  rw [substVar_eq_ctx_rest hx s WFF.bot hpf]
  conv_lhs => unfold WFF.ctx_rest

/-! ### QUANTIFIER pair-free base cases.

`WFF.ctx_rest` delegates `.all`/`.ex` to `WFF.ctx_rest_quant_arm` (v8), which —
like the dia base case — weakens the substituted term past the quantified
variable `xv` (`Term.ctx_ext xv`) and reorders the body so the substituted
variable `⟨x,S⟩` is outermost (`h_reorder ▸ ψ`), then recurses via `ctx_rest_MU`
(= `substVar`).  Unlike the dia base, the recursion context is exactly
`VarCtx_insert xv V hxa_V` (no `erase`), so no cast helper is needed: the RHS
matches the arm's output up to proof-irrelevance of the freshness / reorder
proofs. -/

theorem WFF.substVar_all {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨x, S⟩ V hx))
    (hxa_V : xv.1 ∉ VarCtx_to_VarSymbs V)
    (hx_xaV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxa_V))
    (h_reorder : VarCtx_insert xv (VarCtx_insert ⟨x, S⟩ V hx) hxv
               = VarCtx_insert ⟨x, S⟩ (VarCtx_insert xv V hxa_V) hx_xaV)
    (ψ : WFF σ (VarCtx_insert xv (VarCtx_insert ⟨x, S⟩ V hx) hxv)) :
    WFF.substVar hx s (@WFF.all σ (VarCtx_insert ⟨x, S⟩ V hx) xv hxv ψ)
      = @WFF.all σ V xv hxa_V
          (WFF.substVar hx_xaV (Term.ctx_ext xv hxa_V s) (h_reorder ▸ ψ)) := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_quant_arm]
    rfl
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

theorem WFF.substVar_ex {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨x, S⟩ V hx))
    (hxa_V : xv.1 ∉ VarCtx_to_VarSymbs V)
    (hx_xaV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxa_V))
    (h_reorder : VarCtx_insert xv (VarCtx_insert ⟨x, S⟩ V hx) hxv
               = VarCtx_insert ⟨x, S⟩ (VarCtx_insert xv V hxa_V) hx_xaV)
    (ψ : WFF σ (VarCtx_insert xv (VarCtx_insert ⟨x, S⟩ V hx) hxv)) :
    WFF.substVar hx s (@WFF.ex σ (VarCtx_insert ⟨x, S⟩ V hx) xv hxv ψ)
      = @WFF.ex σ V xv hxa_V
          (WFF.substVar hx_xaV (Term.ctx_ext xv hxa_V s) (h_reorder ▸ ψ)) := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_quant_arm]
    rfl
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq


/-! ### TERM-LEVEL substitution package (pair-free base cases).

`Term.substVar` is the term-level analog of `WFF.substVar`; `Term.ctx_rest_MU`
returns a `Term` directly (no Subtype), and in the pair-free branch delegates to
`Term.ctx_rest`, which dispatches on the term constructor.  `Func`/`Rel` have no
pair-elim constructor, so their `ctx_rest` is the direct structural pass (taking
`hpf`); the `func`/`atom`/`eq` lemmas expose those directly. -/

/-- Public term-level substitution wrapper, mirroring `WFF.substVar`. -/
def Term.substVar {σ : Signature} {V : VarCtx} {x : VarSymb} {S S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S') : Term σ V S' :=
  Term.ctx_rest_MU hx s t

/-- In the pair-free branch, `Term.substVar` is exactly `Term.ctx_rest`. -/
private theorem Term.substVar_eq_ctx_rest {σ : Signature} {V : VarCtx}
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

theorem Term.substVar_unit {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none) :
    Term.substVar hx s (Term.unit : Term σ (VarCtx_insert ⟨x, S⟩ V hx) _)
      = Term.unit := by
  rw [Term.substVar_eq_ctx_rest hx s Term.unit hpf]
  conv_lhs => unfold Term.ctx_rest

theorem Term.substVar_pair {σ : Signature} {V : VarCtx} {x : VarSymb}
    {S T1 T2 : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (a : Term σ (VarCtx_insert ⟨x, S⟩ V hx) T1)
    (b : Term σ (VarCtx_insert ⟨x, S⟩ V hx) T2) :
    Term.substVar hx s (Term.pair a b)
      = Term.pair (Term.substVar hx s a) (Term.substVar hx s b) := by
  rw [Term.substVar_eq_ctx_rest hx s a hpf, Term.substVar_eq_ctx_rest hx s b hpf,
      Term.substVar_eq_ctx_rest hx s (Term.pair a b) hpf]
  conv_lhs => unfold Term.ctx_rest

theorem Term.substVar_func {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (f : Func σ (VarCtx_insert ⟨x, S⟩ V hx) 0) :
    Term.substVar hx s (Term.func f)
      = Term.func (Func.ctx_rest hx hpf s f) := by
  rw [Term.substVar_eq_ctx_rest hx s (Term.func f) hpf]
  conv_lhs => unfold Term.ctx_rest

/-- The `.var` base case, stated faithfully to `Term.ctx_rest`'s `.var` arm: if
    the variable `⟨w, .Var⟩` is the substituted variable `⟨x, S⟩` (which forces
    `S = .Var`), the result is `s` (transported along `S = .Var`); otherwise it
    is the same variable, re-homed into `V`. -/
theorem Term.substVar_var {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (w : VarSymb)
    (hw : (⟨w, VarType.Var⟩ : VarSymb × VarType) ∈ (VarCtx_insert ⟨x, S⟩ V hx).1) :
    Term.substVar hx s (Term.var ⟨w, hw⟩)
      = if h_eq : (⟨w, VarType.Var⟩ : VarSymb × VarType) = ⟨x, S⟩
        then (Prod.mk.inj h_eq).2.symm ▸ s
        else Term.var ⟨w, (Finset.mem_insert.mp hw).resolve_left h_eq⟩ := by
  rw [Term.substVar_eq_ctx_rest hx s (Term.var ⟨w, hw⟩) hpf]
  conv_lhs => unfold Term.ctx_rest
  split_ifs with h_eq
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
    rfl
  · rfl

/-! ### The `eq` / `atom` WFF base cases (unblocked by the term package). -/

theorem WFF.substVar_eq {σ : Signature} {V : VarCtx} {x : VarSymb} {S T : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (t1 t2 : Term σ (VarCtx_insert ⟨x, S⟩ V hx) T) :
    WFF.substVar hx s (WFF.eq t1 t2)
      = WFF.eq (Term.substVar hx s t1) (Term.substVar hx s t2) := by
  rw [substVar_eq_ctx_rest hx s (WFF.eq t1 t2) hpf,
      Term.substVar_eq_ctx_rest hx s t1 hpf, Term.substVar_eq_ctx_rest hx s t2 hpf]
  conv_lhs => unfold WFF.ctx_rest

theorem WFF.substVar_atom {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (R : Rel σ (VarCtx_insert ⟨x, S⟩ V hx) 0) :
    WFF.substVar hx s (WFF.atom R)
      = WFF.atom (Rel.ctx_rest hx hpf s R) := by
  rw [substVar_eq_ctx_rest hx s (WFF.atom R) hpf]
  conv_lhs => unfold WFF.ctx_rest

/-! ### GROUP 2 — modal term-formers.

`Term.ctx_rest`'s `.boxterm`/`.diaterm`/`.pair_elim` arms mirror the WFF
`box`/`dia`/`pair_elim` arms exactly.  The `.pair_elim` arm is `exfalso`: a
`pair_elim`-headed term cannot inhabit a pair-free extended context. -/

/-- The `.pair_elim` arm of `Term.ctx_rest` is unreachable in the pair-free
    branch: the `pair_elim` node's `W₂` context carries the pair binder
    `⟨z, v1.2 ×ᵥ v2.2⟩`, contradicting `hpf`.  So there is no pair-free
    `substVar` into a `pair_elim`; the honest content is this vacuity. -/
theorem Term.substVar_pair_elim {σ : Signature} {V V₀ W₁ : VarCtx} {x : VarSymb}
    {S S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (v1 v2 : VarSymb × VarType) (z : VarSymb)
    (hv1 : v1.1 ∉ VarCtx_to_VarSymbs V₀) (hv2 : v2.1 ∉ VarCtx_to_VarSymbs V₀)
    (hv1v2 : v1.1 ≠ v2.1) (hz : z ∉ VarCtx_to_VarSymbs V₀)
    (w1eq : VarCtx_insert_twice v1 v2 V₀ hv1 hv2 hv1v2 = W₁)
    (w2eq : VarCtx_insert ⟨z, v1.2.VTypeProd v2.2⟩ V₀ hz
              = VarCtx_insert ⟨x, S⟩ V hx)
    (body : Term σ W₁ S') :
    False := by
  have h_z_in : (⟨z, v1.2.VTypeProd v2.2⟩ : VarSymb × VarType)
      ∈ (VarCtx_insert ⟨x, S⟩ V hx).1 := by
    rw [← w2eq]; exact Finset.mem_insert_self _ _
  exact VarCtx.firstPairVar_none_no_pair hpf h_z_in

/-- Term-level analog of `box_ctx_rest_MU_cast_local` (wraps `Term.boxterm`
    around `Term.ctx_rest_MU` instead of `WFF.box` around `WFF.ctx_rest_MU`). -/
private theorem boxterm_ctx_rest_MU_cast {σ : Signature} {E V Wout : VarCtx}
    {x : VarSymb} {S Sφ : VarType} (hEV : E = V)
    (hxE : x ∉ VarCtx_to_VarSymbs E) (hxV : x ∉ VarCtx_to_VarSymbs V)
    (tE : Term σ E S) (tV : Term σ V S) (ht : HEq tE tV)
    (φE : Term σ (VarCtx_insert ⟨x, S⟩ E hxE) Sφ)
    (φV : Term σ (VarCtx_insert ⟨x, S⟩ V hxV) Sφ) (hφ : HEq φE φV)
    (p1 : (VarCtx_box E).1 ⊆ Wout.1)
    (q1 : ∀ p ∈ Wout.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box E).1)
    (p2 : (VarCtx_box V).1 ⊆ Wout.1)
    (q2 : ∀ p ∈ Wout.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1) :
    Term.boxterm (Term.ctx_rest_MU hxE tE φE) p1 q1
      = Term.boxterm (Term.ctx_rest_MU hxV tV φV) p2 q2 := by
  subst hEV
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hφ
  rfl

/-- Term-level analog of `WFF.substVar_boxterm_box_gen_base`: substituting a
    box-typed variable (via a `boxterm`) into a `Term.boxterm`, pair-free
    ambient.  Clean commutation with the recursion pushed inside the box. -/
theorem Term.substVar_boxterm {σ : Signature} {Sφ : VarType}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hpf : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar = none)
    (t : Term σ V x.2)
    (φ : Term σ (VarCtx_insert x V hx) Sφ) :
    Term.substVar hxW (Term.boxterm t hsub h_no_box_extras)
        (Term.boxterm φ (box_hsub_insert hx hxW hsub)
                        (box_extras_insert hx hxW h_no_box_extras))
      = Term.boxterm (Term.substVar hx t φ) hsub h_no_box_extras := by
  simp only [Term.substVar]
  conv_lhs => unfold Term.ctx_rest_MU
  split
  · conv_lhs => unfold Term.ctx_rest
    dsimp only
    have hx_in : x.1 ∈ VarCtx_to_VarSymbs (VarCtx_insert x V hx) := by
      rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_self _ _
    have hxS_in : (⟨x.1, x.2⟩ : VarSymb × VarType) ∈ (VarCtx_insert x V hx).fst :=
      Finset.mem_insert_self _ _
    rw [dif_pos hx_in, dif_pos hxS_in]
    simp only []
    rw [eqRec_fun3_local (F1 := fun z => Term σ z x.2)
          (F2 := fun z => (VarCtx_box z).fst ⊆ W.fst)
          (F3 := fun z => ∀ p ∈ W.fst,
                    VarType.isBox p.2 = true → p ∈ (VarCtx_box z).fst)]
    refine boxterm_ctx_rest_MU_cast ?_ _ hx _ t ?_ _ φ ?_ _ _ hsub h_no_box_extras
    · apply VarCtx_ext_local
      change (insert (x : VarSymb × VarType) V.1).erase x = V.1
      exact Finset.erase_insert
        (fun hmem => hx (Finset.mem_image.mpr ⟨_, hmem, rfl⟩))
    · exact eqRec_heq (φ := fun z => Term σ z x.2) _ t
    · exact eqRec_heq (φ := fun z => Term σ z Sφ) _ φ
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq


/-- Term-level analog of `dia_ctx_rest_MU_cast`: wraps `Term.diaterm` around
    `Term.ctx_rest_MU` (with the term `ctx_ext`-ed past the dia witness inside),
    recasting along `E = V`. -/
private theorem diaterm_ctx_rest_MU_cast {σ : Signature} {E V Wout : VarCtx}
    {x : VarSymb} {T Sψ : VarType} {xv : VarSymb × VarType} (hEV : E = V)
    (hxvE : xv.1 ∉ VarCtx_to_VarSymbs E) (hxvV : xv.1 ∉ VarCtx_to_VarSymbs V)
    (hxE : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv E hxvE))
    (hxV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxvV))
    (tE : Term σ E T) (tV : Term σ V T) (ht : HEq tE tV)
    (ψE : Term σ (VarCtx_insert ⟨x, T⟩ (VarCtx_insert xv E hxvE) hxE) Sψ)
    (ψV : Term σ (VarCtx_insert ⟨x, T⟩ (VarCtx_insert xv V hxvV) hxV) Sψ)
    (hψ : HEq ψE ψV)
    (p1 : (VarCtx_dia xv E hxvE).1 ⊆ Wout.1)
    (q1 : ∀ p ∈ Wout.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv E hxvE).1)
    (p2 : (VarCtx_dia xv V hxvV).1 ⊆ Wout.1)
    (q2 : ∀ p ∈ Wout.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V hxvV).1) :
    Term.diaterm xv hxvE
        (Term.ctx_rest_MU hxE (Term.ctx_ext xv hxvE tE) ψE) p1 q1
      = Term.diaterm xv hxvV
        (Term.ctx_rest_MU hxV (Term.ctx_ext xv hxvV tV) ψV) p2 q2 := by
  subst hEV
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hψ
  rfl

/-- Term-level analog of `WFF.substVar_boxterm_dia_gen_base` (D1): the box-like
    recursion sub-case of `Term.ctx_rest`'s `.diaterm` arm (`xv.1 ≠ x`,
    `x ∈ V_inner`, substituted term a `boxterm`).  Substituting `x` under the dia
    witness `xv` weakens `t` past `xv` and reorders the body so `x` is outermost,
    exactly as at the WFF level. -/
theorem Term.substVar_diaterm_base {σ : Signature} {Sψ : VarType}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hxW : x.1 ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box V).1 ⊆ W.1)
    (h_no_box_extras : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hpf : (VarCtx_insert ⟨x.1, x.2.VTypeBox⟩ W hxW).firstPairVar = none)
    (t : Term σ V x.2)
    (xv : VarSymb × VarType)
    (hxv_ne : xv.1 ≠ x.1)
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
    (Q' : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V hxv_V).1) :
    Term.substVar hxW (Term.boxterm t hsub h_no_box_extras)
        (Term.diaterm xv hxv_outer ψ P Q)
      = Term.diaterm xv hxv_V
          (Term.substVar hx_out (Term.ctx_ext xv hxv_V t) (h_reorder ▸ ψ)) P' Q' := by
  simp only [Term.substVar]
  conv_lhs => unfold Term.ctx_rest_MU
  split
  · conv_lhs => unfold Term.ctx_rest
    dsimp only
    rw [dif_neg hxv_ne]
    have h_x_in_symb : x.1 ∈ VarCtx_to_VarSymbs (VarCtx_insert x V hx) := by
      rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_self _ _
    have hxT_in : (⟨x.1, x.2⟩ : VarSymb × VarType) ∈ (VarCtx_insert x V hx).fst :=
      Finset.mem_insert_self _ _
    rw [dif_pos h_x_in_symb, dif_pos hxT_in]
    simp only []
    rw [eqRec_fun3_local (F1 := fun z => Term σ z x.2)
          (F2 := fun z => (VarCtx_box z).fst ⊆ W.fst)
          (F3 := fun z => ∀ p ∈ W.fst,
                    VarType.isBox p.2 = true → p ∈ (VarCtx_box z).fst)]
    refine diaterm_ctx_rest_MU_cast ?_ _ hxv_V _ hx_out _ t ?_ _ (h_reorder ▸ ψ)
      ?_ _ _ P' Q'
    · apply VarCtx_ext_local
      change (insert (x : VarSymb × VarType) V.1).erase ⟨x.1, x.2⟩ = V.1
      exact Finset.erase_insert
        (fun hmem => hx (Finset.mem_image.mpr ⟨_, hmem, rfl⟩))
    · exact eqRec_heq (φ := fun z => Term σ z x.2) _ t
    · exact HEq.trans (eqRec_heq (φ := fun z => Term σ z Sψ) _ ψ)
        (eqRec_heq (φ := fun z => Term σ z Sψ) _ ψ).symm
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq

/-- Term-level analog of `WFF.substVar_diaterm_dia_gen_base` (D2, modal-β): the
    witness sub-case of `Term.ctx_rest`'s `.diaterm` arm (`xv.1 = x`, so the dia
    witness IS the substituted variable, forcing the substituted term to be a
    `diaterm`).  The `.diaterm` arm reorders the body inline (via `Term.ctx_ext`
    past `xv_s` plus two context casts) and substitutes the inner `tt_s`; the RHS
    is stated faithfully to that computation. -/
theorem Term.substVar_diaterm_modal_beta {σ : Signature} {V V_inner : VarCtx}
    {S_tt : VarType}
    (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (hx : xv.1 ∉ VarCtx_to_VarSymbs V)
    (xv_s : VarSymb × VarType) (hxv_s : xv_s.1 ∉ VarCtx_to_VarSymbs V_inner)
    (h_xv_ne_xv_s : xv.1 ≠ xv_s.1)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) S_tt)
    (hsub_t : (VarCtx_dia xv V_inner hxv).1
                ⊆ (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ V hx).1)
    (h_no_extras_t : ∀ p ∈ (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ V hx).1,
                      VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (tt_s : Term σ (VarCtx_insert xv_s V_inner hxv_s) xv.2)
    (hsub_s : (VarCtx_dia xv_s V_inner hxv_s).1 ⊆ V.1)
    (h_no_extras_s : ∀ p ∈ V.1, VarType.isBox p.2 = true
                      → p ∈ (VarCtx_dia xv_s V_inner hxv_s).1)
    (hpf : (VarCtx_insert ⟨xv.1, xv.2.VTypeDia⟩ V hx).firstPairVar = none)
    (hxv_s_outer : xv_s.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V_inner hxv))
    (hxv_xv_s_outer : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s))
    (h_x_inner : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s))
    (h_reorder : VarCtx_insert xv_s (VarCtx_insert xv V_inner hxv) hxv_s_outer
               = VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer)
    (h_reform : VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer
              = VarCtx_insert ⟨xv.1, xv.2⟩ (VarCtx_insert xv_s V_inner hxv_s) h_x_inner) :
    Term.substVar hx
        (Term.diaterm xv_s hxv_s tt_s hsub_s h_no_extras_s)
        (Term.diaterm xv hxv tt hsub_t h_no_extras_t)
      = Term.diaterm xv_s hxv_s
          (Term.substVar h_x_inner tt_s
            (h_reform ▸ h_reorder ▸ Term.ctx_ext xv_s hxv_s_outer tt))
          hsub_s h_no_extras_s := by
  simp only [Term.substVar]
  conv_lhs => unfold Term.ctx_rest_MU
  split
  · conv_lhs => unfold Term.ctx_rest
    dsimp only
    rw [dif_pos rfl]
    simp only []
  · exfalso
    rename_i z V1 V2 hzmem heq
    rw [hpf] at heq
    simp at heq


/-! Vacuous substitution: restricting a freshly-added `.Var` variable cancels the
    weakening that added it.  `ctx_rest ∘ ctx_ext = id` for a `.Var`-typed binder. -/

mutual
theorem Term.ctx_rest_ctx_ext {σ : Signature} {V : VarCtx} {x : VarSymb} {S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, .Var⟩ V hx).firstPairVar = none)
    (s : Term σ V .Var)
    (t : Term σ V S') :
    Term.ctx_rest hx hpf s (Term.ctx_ext ⟨x, .Var⟩ hx t) = t := by
  match t with
  | .var ⟨w, hw⟩ =>
      have hwx : (⟨w, .Var⟩ : VarSymb × VarType) ≠ ⟨x, .Var⟩ := by
        intro h; exact hx (Finset.mem_image.mpr ⟨_, hw, (Prod.mk.inj h).1⟩)
      simp only [Term.ctx_ext]
      unfold Term.ctx_rest
      rw [dif_neg hwx]
  | .func f =>
      have ih := Func.ctx_rest_ctx_ext hx hpf s f
      simp only [Term.ctx_ext]
      unfold Term.ctx_rest
      rw [ih]
  | .unit =>
      simp only [Term.ctx_ext]
      unfold Term.ctx_rest
      rfl
  | .pair t1 t2 =>
      have ih1 := Term.ctx_rest_ctx_ext hx hpf s t1
      have ih2 := Term.ctx_rest_ctx_ext hx hpf s t2
      simp only [Term.ctx_ext]
      unfold Term.ctx_rest
      rw [ih1, ih2]
  | @Term.boxterm _ V_inner S_inner _ tt hsub h_no_extras =>
      have hx_ninner : x ∉ VarCtx_to_VarSymbs V_inner := by
        intro h
        obtain ⟨⟨w', T'⟩, hw'T', hw'eq⟩ := Finset.mem_image.mp h
        simp only at hw'eq; subst hw'eq
        have hbox : (⟨w', T'.VTypeBox⟩ : VarSymb × VarType) ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨w', T'⟩, hw'T', rfl⟩
        exact hx (Finset.mem_image.mpr ⟨_, hsub hbox, rfl⟩)
      simp only [Term.ctx_ext]
      unfold Term.ctx_rest
      rw [dif_neg hx_ninner]
  | @Term.diaterm _ V_inner S_inner _ xv_t hxv_t tt hsub h_no_extras =>
      have hxvt_ne_x : xv_t.1 ≠ x := by
        intro h
        apply hx
        have hdia : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
            ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
          rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        exact Finset.mem_image.mpr ⟨_, hsub hdia, h⟩
      have hx_ninner : x ∉ VarCtx_to_VarSymbs V_inner := by
        intro h
        obtain ⟨⟨w', T'⟩, hw'T', hw'eq⟩ := Finset.mem_image.mp h
        simp only at hw'eq; subst hw'eq
        have hbox : (⟨w', T'.VTypeBox⟩ : VarSymb × VarType) ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨w', T'⟩, hw'T', rfl⟩
        have hboxdia : (⟨w', T'.VTypeBox⟩ : VarSymb × VarType)
            ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
          rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hbox
        exact hx (Finset.mem_image.mpr ⟨_, hsub hboxdia, rfl⟩)
      simp only [Term.ctx_ext]
      unfold Term.ctx_rest
      rw [dif_neg hxvt_ne_x, dif_neg hx_ninner]
  | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body =>
      exfalso
      have h_z_in_V : (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType) ∈ V.1 := by
        rw [← w2eq]; exact Finset.mem_insert_self _ _
      exact VarCtx.firstPairVar_none_no_pair hpf (Finset.mem_insert_of_mem h_z_in_V)
  termination_by Term.numNodes t
  decreasing_by all_goals (simp only [Term.numNodes]; omega)

theorem Func.ctx_rest_ctx_ext {σ : Signature} {V : VarCtx} {x : VarSymb} {N : ℕ}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, .Var⟩ V hx).firstPairVar = none)
    (s : Term σ V .Var)
    (f : Func σ V N) :
    Func.ctx_rest hx hpf s (Func.ctx_ext ⟨x, .Var⟩ hx f) = f := by
  match f with
  | .F h =>
      simp only [Func.ctx_ext]
      unfold Func.ctx_rest
      rfl
  | .eval g t =>
      have ihg := Func.ctx_rest_ctx_ext hx hpf s g
      have iht := Term.ctx_rest_ctx_ext hx hpf s t
      simp only [Func.ctx_ext]
      unfold Func.ctx_rest
      rw [ihg, iht]
  termination_by Func.numNodes f
  decreasing_by all_goals (simp only [Func.numNodes]; omega)
end

/-- `Rel` version: restricting a freshly-added `.Var` variable cancels the weakening. -/
theorem Rel.ctx_rest_ctx_ext {σ : Signature} {V : VarCtx} {x : VarSymb} {n : ℕ}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, .Var⟩ V hx).firstPairVar = none)
    (s : Term σ V .Var)
    (R : Rel σ V n) :
    Rel.ctx_rest hx hpf s (Rel.ctx_ext ⟨x, .Var⟩ hx R) = R := by
  induction R with
  | R h => simp only [Rel.ctx_ext]; unfold Rel.ctx_rest; rfl
  | eval R' t ih =>
      simp only [Rel.ctx_ext]
      unfold Rel.ctx_rest
      rw [ih, Term.ctx_rest_ctx_ext hx hpf s t]

/-! ctx_ext / ctx_ext commutation for distinct `.Var` binders (eq form with a
    context-swap transport). `.Var`-restricted + `hpf` ⇒ boxterm/diaterm are
    passthroughs and pair_elim is vacuous, exactly as in the vacuous lemma. -/

-- Cast helpers: push a context transport through each constructor (generic ⇒ `subst`).
private theorem Term.cast_var {σ : Signature} {A B : VarCtx} (h : A = B)
    (e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ A.1}) :
    (h ▸ (Term.var e : Term σ A .Var)) = Term.var (h ▸ e) := by subst h; rfl

private theorem cast_subtype_val {A B : VarCtx} (h : A = B)
    (e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ A.1}) :
    ((h ▸ e : {v : VarSymb // (⟨v, .Var⟩ : VarSymb × VarType) ∈ B.1}) : VarSymb)
      = (e : VarSymb) := by subst h; rfl

private theorem Term.cast_func {σ : Signature} {A B : VarCtx} (h : A = B)
    (f : Func σ A 0) : (h ▸ (Term.func f : Term σ A .Var)) = Term.func (h ▸ f) := by
  subst h; rfl

private theorem Term.cast_unit {σ : Signature} {A B : VarCtx} (h : A = B) :
    (h ▸ (Term.unit : Term σ A .VTypeOne)) = Term.unit := by subst h; rfl

private theorem Term.cast_pair {σ : Signature} {A B : VarCtx} {S T : VarType} (h : A = B)
    (a : Term σ A S) (b : Term σ A T) :
    (h ▸ (Term.pair a b : Term σ A (S.VTypeProd T))) = Term.pair (h ▸ a) (h ▸ b) := by
  subst h; rfl

private theorem Term.cast_boxterm {σ : Signature} {W W' V_inner : VarCtx} {S_inner : VarType}
    (h : W = W') (tt : Term σ V_inner S_inner) (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    (h ▸ (Term.boxterm tt hsub hne : Term σ W S_inner.VTypeBox))
      = Term.boxterm tt (h ▸ hsub) (h ▸ hne) := by subst h; rfl

private theorem Term.cast_diaterm {σ : Signature} {W W' V_inner : VarCtx} {S_inner : VarType}
    (h : W = W') (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) S_inner)
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    (h ▸ (Term.diaterm xv hxv tt hsub hne : Term σ W S_inner.VTypeDia))
      = Term.diaterm xv hxv tt (h ▸ hsub) (h ▸ hne) := by subst h; rfl

private theorem Func.cast_F {σ : Signature} {A B : VarCtx} {N : ℕ} (h : A = B)
    (hr : {f // σ.funcArity f = N}) :
    (h ▸ (Func.F hr : Func σ A N)) = Func.F hr := by subst h; rfl

private theorem Func.cast_eval {σ : Signature} {A B : VarCtx} {N : ℕ} (h : A = B)
    (g : Func σ A (N+1)) (t : Term σ A .Var) :
    (h ▸ (Func.eval g t : Func σ A N)) = Func.eval (h ▸ g) (h ▸ t) := by subst h; rfl

private theorem Rel.cast_R {σ : Signature} {A B : VarCtx} {n : ℕ} (h : A = B)
    (hr : {r // σ.relArity r = n}) :
    (h ▸ (Rel.R hr : Rel σ A n)) = Rel.R hr := by subst h; rfl

private theorem Rel.cast_eval {σ : Signature} {A B : VarCtx} {n : ℕ} (h : A = B)
    (R' : Rel σ A (n+1)) (t : Term σ A .Var) :
    (h ▸ (Rel.eval R' t : Rel σ A n)) = Rel.eval (h ▸ R') (h ▸ t) := by subst h; rfl

mutual
theorem Term.ctx_ext_comm {σ : Signature} {V : VarCtx} {x y : VarSymb} {S' : VarType}
    (hpf : V.firstPairVar = none)
    (hy_V : y ∉ VarCtx_to_VarSymbs V) (hx_V : x ∉ VarCtx_to_VarSymbs V)
    (hx_yV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨y, .Var⟩ V hy_V))
    (hy_xV : y ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨x, .Var⟩ V hx_V))
    (t : Term σ V S') :
    Term.ctx_ext ⟨x, .Var⟩ hx_yV (Term.ctx_ext ⟨y, .Var⟩ hy_V t)
      = (@VarCtx_insert_comm ⟨y, .Var⟩ ⟨x, .Var⟩ V hx_V hy_V hy_xV hx_yV) ▸
          Term.ctx_ext ⟨y, .Var⟩ hy_xV (Term.ctx_ext ⟨x, .Var⟩ hx_V t) := by
  match t with
  | .var ⟨w, hw⟩ =>
      simp only [Term.ctx_ext, Term.cast_var]
      congr 1
      apply Subtype.ext
      rw [cast_subtype_val]
  | .func f =>
      have ih := Func.ctx_ext_comm hpf hy_V hx_V hx_yV hy_xV f
      simp only [Term.ctx_ext, Term.cast_func]
      rw [ih]
  | .unit =>
      simp only [Term.ctx_ext, Term.cast_unit]
  | .pair t1 t2 =>
      have ih1 := Term.ctx_ext_comm hpf hy_V hx_V hx_yV hy_xV t1
      have ih2 := Term.ctx_ext_comm hpf hy_V hx_V hx_yV hy_xV t2
      simp only [Term.ctx_ext, Term.cast_pair]
      rw [ih1, ih2]
  | @Term.boxterm _ V_inner S_inner _ tt hsub h_no_extras =>
      simp only [Term.ctx_ext, Term.cast_boxterm]
  | @Term.diaterm _ V_inner S_inner _ xv_t hxv_t tt hsub h_no_extras =>
      simp only [Term.ctx_ext, Term.cast_diaterm]
  | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body =>
      exfalso
      have h_z_in_V : (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType) ∈ V.1 := by
        rw [← w2eq]; exact Finset.mem_insert_self _ _
      exact VarCtx.firstPairVar_none_no_pair hpf h_z_in_V
  termination_by Term.numNodes t
  decreasing_by all_goals (simp only [Term.numNodes]; omega)

theorem Func.ctx_ext_comm {σ : Signature} {V : VarCtx} {x y : VarSymb} {N : ℕ}
    (hpf : V.firstPairVar = none)
    (hy_V : y ∉ VarCtx_to_VarSymbs V) (hx_V : x ∉ VarCtx_to_VarSymbs V)
    (hx_yV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨y, .Var⟩ V hy_V))
    (hy_xV : y ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨x, .Var⟩ V hx_V))
    (f : Func σ V N) :
    Func.ctx_ext ⟨x, .Var⟩ hx_yV (Func.ctx_ext ⟨y, .Var⟩ hy_V f)
      = (@VarCtx_insert_comm ⟨y, .Var⟩ ⟨x, .Var⟩ V hx_V hy_V hy_xV hx_yV) ▸
          Func.ctx_ext ⟨y, .Var⟩ hy_xV (Func.ctx_ext ⟨x, .Var⟩ hx_V f) := by
  match f with
  | .F hr =>
      simp only [Func.ctx_ext, Func.cast_F]
  | .eval g t =>
      have ihg := Func.ctx_ext_comm hpf hy_V hx_V hx_yV hy_xV g
      have iht := Term.ctx_ext_comm hpf hy_V hx_V hx_yV hy_xV t
      simp only [Func.ctx_ext, Func.cast_eval]
      rw [ihg, iht]
  termination_by Func.numNodes f
  decreasing_by all_goals (simp only [Func.numNodes]; omega)
end

theorem Rel.ctx_ext_comm {σ : Signature} {V : VarCtx} {x y : VarSymb} {n : ℕ}
    (hpf : V.firstPairVar = none)
    (hy_V : y ∉ VarCtx_to_VarSymbs V) (hx_V : x ∉ VarCtx_to_VarSymbs V)
    (hx_yV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨y, .Var⟩ V hy_V))
    (hy_xV : y ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨x, .Var⟩ V hx_V))
    (R : Rel σ V n) :
    Rel.ctx_ext ⟨x, .Var⟩ hx_yV (Rel.ctx_ext ⟨y, .Var⟩ hy_V R)
      = (@VarCtx_insert_comm ⟨y, .Var⟩ ⟨x, .Var⟩ V hx_V hy_V hy_xV hx_yV) ▸
          Rel.ctx_ext ⟨y, .Var⟩ hy_xV (Rel.ctx_ext ⟨x, .Var⟩ hx_V R) := by
  induction R with
  | R hr => simp only [Rel.ctx_ext, Rel.cast_R]
  | eval R' t ih =>
      have iht := Term.ctx_ext_comm hpf hy_V hx_V hx_yV hy_xV t
      simp only [Rel.ctx_ext, Rel.cast_eval]
      rw [ih, iht]
