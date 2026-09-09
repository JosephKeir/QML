import QML.QML_v11_Proof

/-!
# QML v11 — equality by extensionality (staging)

The v11 port of the `eqRec` reform (v10 `QML_Full_v10_Part3.lean`).  Equality is now PRIMITIVE ONLY
AT `.Var`; `eqRec` builds it at every compound type by recursion, and the modal extensionality
principles `box_ext`/`dia_ext` — which were rules in v10 — become *defining equations* of `eqRec`.

This file starts with the two ingredients that everything else needs:

* **Inner-context determinacy.**  `h_no_box_extras` pins `VarCtx_box V` to exactly the box-typed
  part of `W`, so a `boxterm`'s inner context is a FUNCTION of `W`; likewise a `diaterm`'s, given
  the ◇-witness.  That is what lets `eqRec`'s modal cases recurse with no weakening at all.
* **Proof-theoretic infrastructure** at the EMPTY hypothesis set (`⊢ φ`), which is what
  necessitation needs; a general `Γ` follows by weakening.
-/

/-! ## Inner-context determinacy -/

/-- Every entry of `VarCtx_box V` is box-typed. -/
theorem VarCtx_box_entry_isBox {V : VarCtx} {p : VarSymb × VarType}
    (hp : p ∈ (VarCtx_box V).1) : VarType.isBox p.2 = true := by
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
  simp [VarType.isBox]

/-- **Box-term inner-context determinacy.**  Two boxterms of the same type in the same `W` have the
    same inner context: `hsub` (⊆) and `h_no_box_extras` (⊇) pin `VarCtx_box Vᵢ` to the box-typed
    part of `W`, and `VarCtx_box` is injective. -/
theorem boxterm_ctx_unique {V₁ V₂ W : VarCtx}
    (hsub₁ : (VarCtx_box V₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₁).1)
    (hsub₂ : (VarCtx_box V₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₂).1) :
    V₁ = V₂ := by
  refine VarCtx_box_inj (VarCtx_ext _ _ (Finset.Subset.antisymm ?_ ?_))
  · intro p hp; exact h₂ p (hsub₁ hp) (VarCtx_box_entry_isBox hp)
  · intro p hp; exact h₁ p (hsub₂ hp) (VarCtx_box_entry_isBox hp)

/-- `VarCtx_box V` sits inside `VarCtx_dia x V` (which adds only the dia-typed witness). -/
theorem VarCtx_box_subset_dia {x : VarSymb × VarType} {V : VarCtx}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) : (VarCtx_box V).1 ⊆ (VarCtx_dia x V hx).1 := by
  intro p hp
  rw [VarCtx_dia_fst]
  exact Finset.mem_insert_of_mem hp

/-- A box-typed entry of `VarCtx_dia x V` lies in `VarCtx_box V` (the witness is dia-typed). -/
theorem dia_box_entry_in_box {x : VarSymb × VarType} {V : VarCtx}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) {p : VarSymb × VarType}
    (hp : p ∈ (VarCtx_dia x V hx).1) (hbox : VarType.isBox p.2 = true) :
    p ∈ (VarCtx_box V).1 := by
  rw [VarCtx_dia_fst] at hp
  rcases Finset.mem_insert.mp hp with rfl | hbox_mem
  · simp [VarType.isBox] at hbox
  · exact hbox_mem

/-- **Dia-term inner-context determinacy** (same witness): two diaterms of the same type in the same
    `W` sharing the ◇-witness `x` have the same inner context.  Reduces to `boxterm_ctx_unique` on
    the box part, since `VarCtx_dia` only adds the dia-typed witness. -/
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
    discharge the (unreachable) `pair_elim` arms in `eqRec`'s pair-free branch WITHOUT `subst`, so
    that `eqRec` still reduces definitionally on concrete inputs. -/
theorem pair_elim_ctx_mem {V pe_V : VarCtx} {T₁ T₂ : VarType}
    {z : VarSymb} {hz : z ∉ VarCtx_to_VarSymbs pe_V}
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = V) :
    (⟨z, T₁.VTypeProd T₂⟩ : VarSymb × VarType) ∈ V.1 := by
  rw [← w₂eq]; exact Finset.mem_insert_self _ _

/-! ## Determinacy casts

Given NAMES rather than inline `▸`s, so that `eqRec`'s modal arms and their extensionality
equations are syntactically identical — which is what lets the equations be extracted at all. -/

/-- The **box determinacy cast**: `boxterm_ctx_unique` says two same-typed boxterms in the same
    outer context share their inner context, so the second inner term transports into the
    first's. -/
def boxCast {σ : Signature} {A : VarType} {V₁ V₂ W : VarCtx}
    (hsub₁ : (VarCtx_box V₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₁).1)
    (hsub₂ : (VarCtx_box V₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₂).1)
    (tt₂ : Term σ V₂ A) : Term σ V₁ A :=
  (boxterm_ctx_unique hsub₁ h₁ hsub₂ h₂).symm ▸ tt₂

/-- The **dia determinacy cast** (same ◇-witness).  Isolated in its own definition so the `subst`s
    stay OUT of `eqRec`'s matcher. -/
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

/-- On the diagonal the box determinacy cast is the identity (the transported equality proves
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

/-! ## Proof-theoretic infrastructure

Everything is stated at the EMPTY hypothesis set (`⊢ φ`) — that is what necessitation needs; a
general `Γ` follows by weakening. -/

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

/-- **Witnessed necessitation**: `⊢ φ` gives `⊢ □_x φ`.  DERIVED, not primitive: from `⊢ φ` we get
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

/-! ## All-user contexts

⭐`eqRec`'s peel re-pairs at the context's pair variable, and `WFF.pairElim` can only bind a
USER-named one (its quantifier arm needs `bndLevel (V + ⟨z,T₁×T₂⟩) = bndLevel V`).  So `eqRec`
carries the invariant that its context holds only user symbols.

That is not a restriction in practice: it is exactly the design principle that **contexts hold only
FREE variables, and free variables are user-named**.  Every proof rule preserves it — `weak_ctx`,
`all_intro`, `ex_elim` and `pair_elim` all extend by `UserSymb`s, and `K_box`/`K_dia`'s premise
contexts are the un-boxed / witness-extended versions of their conclusion's.  Slots live inside
formulas, under binders, never in a context a derivation is carried out in. -/

def VarCtx.AllUsr (V : VarCtx) : Prop := ∀ p ∈ V.1, p.1.isUsr = true

theorem VarCtx.AllUsr.insert {V : VarCtx} (hV : V.AllUsr) {x : VarSymb × VarType}
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hu : x.1.isUsr = true) :
    (VarCtx_insert x V hx).AllUsr := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp'
  · exact hu
  · exact hV p hp'

theorem VarCtx.AllUsr.erase {V : VarCtx} (hV : V.AllUsr) (x : VarSymb × VarType) :
    (VarCtx_erase V x).AllUsr :=
  fun p hp => hV p (Finset.erase_subset _ _ hp)

/-- A `boxterm`'s inner context inherits it: every `⟨v, T⟩` inside appears as `⟨v, □T⟩` outside. -/
theorem VarCtx.AllUsr.of_box_sub {V_inner V : VarCtx} (hV : V.AllUsr)
    (hsub : (VarCtx_box V_inner).1 ⊆ V.1) : V_inner.AllUsr := by
  intro p hp
  exact hV ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, by cases p; rfl⟩))

/-- A `diaterm`'s inner context, witness included. -/
theorem VarCtx.AllUsr.of_dia_sub {x : VarSymb × VarType} {V_inner V : VarCtx}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V_inner} (hV : V.AllUsr)
    (hsub : (VarCtx_dia x V_inner hx).1 ⊆ V.1) :
    (VarCtx_insert x V_inner hx).AllUsr := by
  refine (hV.of_box_sub (fun p hp => hsub (VarCtx_box_subset_dia hx hp))).insert hx ?_
  refine hV ⟨x.1, x.2.VTypeDia⟩ (hsub ?_)
  rw [VarCtx_dia_fst]
  exact Finset.mem_insert_self _ _

/-! ## Unbinding a slot pair onto user names

The inverse of `WFF.bindPair`, at the TERM level: `Term.unpair` lands on the canonical slots, and
the peel needs the components as FREE user variables so that its re-pairing has exactly the shape
`Proof.pair_elim` discharges.  Same two-renames-and-a-commute shape as `bindPair`, run backwards. -/

def Term.unbindPair {σ : Signature} {V : VarCtx} (T₁ T₂ : VarType) (u₁ u₂ : UserSymb)
    (hu₁ : u₁.toVar ∉ VarCtx_to_VarSymbs V)
    (hu₂ : u₂.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁))
    {S : VarType} (t : Term σ (VarCtx.insertBnd2 T₁ T₂ V) S) :
    Term σ (VarCtx_insert ⟨u₂.toVar, T₂⟩ (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂) S := by
  have hu₁V : u₁.toVar ∉ VarCtx_to_VarSymbs V := hu₁
  have hu₂V : u₂.toVar ∉ VarCtx_to_VarSymbs V := fun h =>
    hu₂ (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem h)
  have hu₂bnd : u₂.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T₁ V) :=
    VarCtx.notMem_insertBnd_of_isUsr rfl T₁ hu₂V
  -- STEP 1 — rename the top slot onto `u₂`
  have t₂ := Term.rename (VarCtx.insertBnd T₁ V).nextBnd u₂.toVar T₂
    (VarCtx.nextBnd_not_mem (VarCtx.insertBnd T₁ V)) hu₂bnd t
  -- STEP 2 — commute, so the first slot is on top
  have hs₁ : V.nextBnd ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₂.toVar, T₂⟩ V hu₂V) :=
    not_mem_VarSymbs_insert (VarCtx.ne_nextBnd_of_isUsr rfl V).symm (VarCtx.nextBnd_not_mem V)
  have t₃ := (VarCtx_insert_comm
      (a := (⟨u₂.toVar, T₂⟩ : VarSymb × VarType))
      (b := (⟨V.nextBnd, T₁⟩ : VarSymb × VarType)) hu₂bnd hs₁ ▸ t₂ :
    Term σ (VarCtx_insert ⟨V.nextBnd, T₁⟩ (VarCtx_insert ⟨u₂.toVar, T₂⟩ V hu₂V) hs₁) S)
  -- STEP 3 — rename the first slot onto `u₁`
  have hu₁mem : u₁.toVar ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) := by
    rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_self _ _
  have hu₁u₂ : u₁.toVar ≠ u₂.toVar := fun h => hu₂ (h ▸ hu₁mem)
  have hu₁' : u₁.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₂.toVar, T₂⟩ V hu₂V) :=
    not_mem_VarSymbs_insert hu₁u₂ hu₁V
  have t₄ := Term.rename V.nextBnd u₁.toVar T₁ hs₁ hu₁' t₃
  -- STEP 4 — commute back
  exact VarCtx_insert_comm
    (a := (⟨u₁.toVar, T₁⟩ : VarSymb × VarType))
    (b := (⟨u₂.toVar, T₂⟩ : VarSymb × VarType)) hu₁' hu₂ ▸ t₄

/-! ## The recursive extensional equality `eqRec`

Split into a **dispatcher** (`eqRec`), a **peel** and a **pair-free core**:

* `eqRec` dispatches on `V.firstPairVar`: if the context holds a product variable `z`, PEEL —
  unpair BOTH terms at `z` onto fresh USER components, recurse, and re-pair; otherwise hand `hfp`
  to the core.
* `eqRecCore` matches directly on `(S, t, s)`: `.Var` is the primitive `WFF.eq`, `□`/`◇` go through
  the determinacy casts, a product is the `∧` of its components, `VTypeOne` is `⊤`.  The
  (unreachable) `pair_elim` arms come LAST so the constructive arms lead the matcher.

⭐The peel is where v11 pays off twice over.  v10 needed an `avoid` set threaded as a parameter, two
`VarSymb.fresh` picks, four `boundVars` side conditions, and the whole `avoid`-parameterisation
trick to make symmetry's peel case tractable.  Here `Term.unpair` targets the canonical slots, so
freshness is one `UserSymb.fresh` and `eqRecPeel … a b` / `… b a` land on the same components
automatically.

Why the dispatcher/core split (v10's finding, still true): with one catch-all arm the generated
equation holds the ENTIRE nested match, so `simp only [eqRec]` re-exposes the peel branch — whose
recursive call sits at a different context — and loops.  `eqRecCore` has per-arm patterns, so
`simp only [eqRecCore]` rewrites ONE case and leaves the `eqRec` occurrences alone.  That is what
makes the modal extensionality equations extractable. -/

mutual

def eqRec {σ : Signature} :
    (V : VarCtx) → V.AllUsr → (S : VarType) → Term σ V S → Term σ V S → WFF σ V
  | V, hV, S, t, s =>
    match hfp : V.firstPairVar with
    | some ⟨⟨z, V1, V2⟩, hzmem⟩ => eqRecPeel V hV S z V1 V2 hzmem t s
    | none => eqRecCore V hV S hfp t s
termination_by V _ S _ _ => (sizeOf S, V.pairDepth, 2)
decreasing_by
  all_goals exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

/-- The **neutral pair-elim peel**: unpair both terms at `z` onto FRESH USER components, recurse,
    then bind those components back onto the canonical slots and re-pair.  The result has exactly
    the shape `Proof.pair_elim` discharges. -/
def eqRecPeel {σ : Signature} (V : VarCtx) (hV : V.AllUsr) (S : VarType)
    (z : VarSymb) (V1 V2 : VarType)
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1)
    (t s : Term σ V S) : WFF σ V :=
  let V₀ := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩
  have hz_fresh : z ∉ VarCtx_to_VarSymbs V₀ := VarCtx_erase_fresh hzmem
  have V_eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V₀ hz_fresh = V :=
    VarCtx_insert_erase hzmem hz_fresh
  have hzu : z.isUsr = true := hV _ hzmem
  have hu₁ : (UserSymb.fresh (VarCtx_to_VarSymbs V₀)).toVar ∉ VarCtx_to_VarSymbs V₀ :=
    UserSymb.fresh_not_mem _
  have hu₂ : (UserSymb.fresh (VarCtx_to_VarSymbs
        (VarCtx_insert ⟨(UserSymb.fresh (VarCtx_to_VarSymbs V₀)).toVar, V1⟩ V₀ hu₁))).toVar
      ∉ VarCtx_to_VarSymbs
        (VarCtx_insert ⟨(UserSymb.fresh (VarCtx_to_VarSymbs V₀)).toVar, V1⟩ V₀ hu₁) :=
    UserSymb.fresh_not_mem _
  have hT : Term σ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V₀ hz_fresh) S = Term σ V S := by rw [V_eq]
  have hW : WFF σ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V₀ hz_fresh) = WFF σ V := by rw [V_eq]
  cast hW (WFF.pairElim V1 V2 z hzu hz_fresh rfl rfl
    (WFF.bindPair V1 V2 _ _ hu₁ hu₂
      (eqRec _ (((hV.erase _).insert hu₁ rfl).insert hu₂ rfl) S
        (Term.unbindPair V1 V2 _ _ hu₁ hu₂
          (Term.unpair V1 V2 z hzu hz_fresh (cast hT.symm t)))
        (Term.unbindPair V1 V2 _ _ hu₁ hu₂
          (Term.unpair V1 V2 z hzu hz_fresh (cast hT.symm s))))))
termination_by (sizeOf S, V.pairDepth, 1)
decreasing_by
  refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
  have hV0 := VarCtx.pairDepth_insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
    (VarCtx_erase V ⟨z, V1.VTypeProd V2⟩) (VarCtx_erase_fresh hzmem)
  rw [VarCtx_insert_erase hzmem (VarCtx_erase_fresh hzmem)] at hV0
  simp only [VarCtx.pairDepth_insert, VarType.pairDepth] at hV0 ⊢
  omega

def eqRecCore {σ : Signature} :
    (V : VarCtx) → V.AllUsr → (S : VarType) → V.firstPairVar = none →
      Term σ V S → Term σ V S → WFF σ V
  | _, _,  .Var,           _,   t,         s         => WFF.eq t s
  | _, _,  .VTypeOne,      _,   _,         _         => WFF.top
  | V, hV, .VTypeProd A B, _,   .pair a b, .pair c d =>
      WFF.and (eqRec V hV A a c) (eqRec V hV B b d)
  | _, hV, .VTypeBox A,    _,   .boxterm tt₁ hsub₁ h₁, .boxterm tt₂ hsub₂ h₂ =>
      WFF.box (eqRec _ (hV.of_box_sub hsub₁) A tt₁ (boxCast hsub₁ h₁ hsub₂ h₂ tt₂)) hsub₁ h₁
  | _, hV, .VTypeDia A,    _,   .diaterm x₁ hx₁ tt₁ hsub₁ h₁,
                                .diaterm x₂ hx₂ tt₂ hsub₂ h₂ =>
      if hx : x₁ = x₂ then
        WFF.box_x x₁ hx₁ hsub₁ h₁
          (eqRec _ (hV.of_dia_sub hsub₁) A tt₁ (diaCast hx hsub₁ h₁ hsub₂ h₂ tt₂))
      else WFF.bot
  -- The (unreachable) neutral `pair_elim` arms come LAST, so the constructive arms lead the
  -- matcher and reduce on concrete inputs.  A `pair_elim`'s context holds a product variable,
  -- contradicting `hfp`.
  | _, _,  _,              hfp, .pair_elim _ _ _ _ _ w₂eq _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
  | _, _,  _,              hfp, _, .pair_elim _ _ _ _ _ w₂eq _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
termination_by V _ S _ _ _ => (sizeOf S, V.pairDepth, 0)
decreasing_by
  all_goals (refine Prod.Lex.left _ _ ?_; simp; try omega)

end
