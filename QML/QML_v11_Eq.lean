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

/-- Extract the `UserSymb` behind a user-named symbol.  `eqRec`'s peel needs this: `firstPairVar`
    hands back a `VarSymb`, `AllUsr` says it is user-named, and `Proof.pair_elim` takes the
    user-facing TYPE. -/
def VarSymb.toUser : (v : VarSymb) → v.isUsr = true → UserSymb
  | .mk n, _  => ⟨n⟩
  | .bnd _, h => absurd h (by simp [VarSymb.isUsr])

@[simp] theorem VarSymb.toUser_toVar (v : VarSymb) (h : v.isUsr = true) :
    (v.toUser h).toVar = v := by
  cases v with
  | mk n => rfl
  | bnd n => simp [VarSymb.isUsr] at h

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
    | some ⟨⟨z, V1, V2⟩, hzmem⟩ =>
        eqRecPeel V hV S (z.toUser (hV _ hzmem)) V1 V2
          (by rw [VarSymb.toUser_toVar]; exact hzmem) t s
    | none => eqRecCore V hV S hfp t s
termination_by V _ S _ _ => (sizeOf S, V.pairDepth, 2)
decreasing_by
  all_goals exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

/-- The **neutral pair-elim peel**: unpair both terms at `z` onto FRESH USER components, recurse,
    then bind those components back onto the canonical slots and re-pair.  The result has exactly
    the shape `Proof.pair_elim` discharges. -/
def eqRecPeel {σ : Signature} (V : VarCtx) (hV : V.AllUsr) (S : VarType)
    (z : UserSymb) (V1 V2 : VarType)
    (hzmem : (⟨z.toVar, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1)
    (t s : Term σ V S) : WFF σ V :=
  let V₀ := VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩
  have hz_fresh : z.toVar ∉ VarCtx_to_VarSymbs V₀ := VarCtx_erase_fresh hzmem
  have V_eq : VarCtx_insert ⟨z.toVar, V1.VTypeProd V2⟩ V₀ hz_fresh = V :=
    VarCtx_insert_erase hzmem hz_fresh
  have hu₁ : (UserSymb.fresh (VarCtx_to_VarSymbs V₀)).toVar ∉ VarCtx_to_VarSymbs V₀ :=
    UserSymb.fresh_not_mem _
  have hu₂ : (UserSymb.fresh (VarCtx_to_VarSymbs
        (VarCtx_insert ⟨(UserSymb.fresh (VarCtx_to_VarSymbs V₀)).toVar, V1⟩ V₀ hu₁))).toVar
      ∉ VarCtx_to_VarSymbs
        (VarCtx_insert ⟨(UserSymb.fresh (VarCtx_to_VarSymbs V₀)).toVar, V1⟩ V₀ hu₁) :=
    UserSymb.fresh_not_mem _
  have hT : Term σ (VarCtx_insert ⟨z.toVar, V1.VTypeProd V2⟩ V₀ hz_fresh) S = Term σ V S := by
    rw [V_eq]
  V_eq ▸ (WFF.pairElim V1 V2 z.toVar rfl hz_fresh rfl rfl
    (WFF.bindPair V1 V2 _ _ hu₁ hu₂
      (eqRec _ (((hV.erase _).insert hu₁ rfl).insert hu₂ rfl) S
        (Term.unbindPair V1 V2 _ _ hu₁ hu₂
          (Term.unpair V1 V2 z.toVar rfl hz_fresh (cast hT.symm t)))
        (Term.unbindPair V1 V2 _ _ hu₁ hu₂
          (Term.unpair V1 V2 z.toVar rfl hz_fresh (cast hT.symm s))))))
termination_by (sizeOf S, V.pairDepth, 1)
decreasing_by
  refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
  have hV0 := VarCtx.pairDepth_insert (⟨z.toVar, V1.VTypeProd V2⟩ : VarSymb × VarType)
    (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) (VarCtx_erase_fresh hzmem)
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

/-! ### How `eqRec` computes

`eqRec_of_none` is the one-step dispatcher equation.  The `eqRecCore_*` equations then unfold ONE
constructive arm each, leaving the `eqRec` occurrences on the right alone — which is exactly what
the dispatcher/core split buys.  Composing them gives the modal extensionality equations:
⭐**`box_ext` and `dia_ext` as DEFINING EQUATIONS**, which is why they are no longer rules. -/

theorem eqRec_of_none {σ : Signature} {V : VarCtx} {hV : V.AllUsr} {S : VarType}
    (hfp : V.firstPairVar = none) (t s : Term σ V S) :
    eqRec V hV S t s = eqRecCore V hV S hfp t s := by
  unfold eqRec
  split
  all_goals first
    | rfl
    | (rename_i hsome; rw [hfp] at hsome; exact absurd hsome (by simp))

theorem eqRecCore_var {σ : Signature} {V : VarCtx} (hV : V.AllUsr)
    (hfp : V.firstPairVar = none) (t s : Term σ V .Var) :
    eqRecCore V hV .Var hfp t s = WFF.eq t s := by simp only [eqRecCore]

theorem eqRecCore_unit {σ : Signature} {V : VarCtx} (hV : V.AllUsr)
    (hfp : V.firstPairVar = none) (t s : Term σ V .VTypeOne) :
    eqRecCore V hV .VTypeOne hfp t s = WFF.top := by simp only [eqRecCore]

theorem eqRecCore_prod {σ : Signature} {V : VarCtx} (hV : V.AllUsr)
    (hfp : V.firstPairVar = none) {A B : VarType}
    (a c : Term σ V A) (b d : Term σ V B) :
    eqRecCore V hV (.VTypeProd A B) hfp (.pair a b) (.pair c d)
      = WFF.and (eqRec V hV A a c) (eqRec V hV B b d) := by simp only [eqRecCore]

/-- ⭐**`box_ext`, definitionally.** -/
theorem eqRecCore_box {σ : Signature} {W : VarCtx} (hW : W.AllUsr)
    (hfp : W.firstPairVar = none) {A : VarType} {V₁ V₂ : VarCtx}
    (tt₁ : Term σ V₁ A) (tt₂ : Term σ V₂ A)
    (hsub₁ : (VarCtx_box V₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₁).1)
    (hsub₂ : (VarCtx_box V₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V₂).1) :
    eqRecCore W hW (.VTypeBox A) hfp (.boxterm tt₁ hsub₁ h₁) (.boxterm tt₂ hsub₂ h₂)
      = WFF.box (eqRec V₁ (hW.of_box_sub hsub₁) A tt₁ (boxCast hsub₁ h₁ hsub₂ h₂ tt₂))
          hsub₁ h₁ := by
  simp only [eqRecCore]

/-- ⭐**`dia_ext`, definitionally** (same ◇-witness). -/
theorem eqRecCore_dia_same {σ : Signature} {W : VarCtx} (hW : W.AllUsr)
    (hfp : W.firstPairVar = none) {A : VarType} {x₁ x₂ : VarSymb × VarType} {V₁ V₂ : VarCtx}
    {hx₁ : x₁.1 ∉ VarCtx_to_VarSymbs V₁} {hx₂ : x₂.1 ∉ VarCtx_to_VarSymbs V₂}
    (tt₁ : Term σ (VarCtx_insert x₁ V₁ hx₁) A) (tt₂ : Term σ (VarCtx_insert x₂ V₂ hx₂) A)
    (hsub₁ : (VarCtx_dia x₁ V₁ hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₁ V₁ hx₁).1)
    (hsub₂ : (VarCtx_dia x₂ V₂ hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₂ V₂ hx₂).1)
    (hx : x₁ = x₂) :
    eqRecCore W hW (.VTypeDia A) hfp (.diaterm x₁ hx₁ tt₁ hsub₁ h₁)
        (.diaterm x₂ hx₂ tt₂ hsub₂ h₂)
      = WFF.box_x x₁ hx₁ hsub₁ h₁
          (eqRec (VarCtx_insert x₁ V₁ hx₁) (hW.of_dia_sub hsub₁) A tt₁
            (diaCast hx hsub₁ h₁ hsub₂ h₂ tt₂)) := by
  simp only [eqRecCore, dif_pos hx]

/-! ## Reflexivity of `eqRec`

`⊢ t ≐ t` at every type.  The modal cases are necessitation of the inner reflexivity — plain for
`□`, witnessed for `◇` — and the peel case is exactly `Proof.pair_elim`, which is what the
user-named components were for. -/

theorem eqRecPeel_refl {σ : Signature} (V : VarCtx) (hV : V.AllUsr) (S : VarType)
    (z : UserSymb) (V1 V2 : VarType)
    (hzmem : (⟨z.toVar, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1)
    (t : Term σ V S)
    (IH : ∀ (W : VarCtx) (hW : W.AllUsr), W.pairDepth < V.pairDepth →
            ∀ (u : Term σ W S), Nonempty (Proof σ W ∅ (eqRec W hW S u u))) :
    Nonempty (Proof σ V ∅ (eqRecPeel V hV S z V1 V2 hzmem t t)) := by
  have hz_fresh : z.toVar ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) :=
    VarCtx_erase_fresh hzmem
  have V_eq : VarCtx_insert ⟨z.toVar, V1.VTypeProd V2⟩
      (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hz_fresh = V :=
    VarCtx_insert_erase hzmem hz_fresh
  have hu₁ : (UserSymb.fresh (VarCtx_to_VarSymbs
        (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩))).toVar
      ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) :=
    UserSymb.fresh_not_mem _
  have hu₂ : (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx_insert
        ⟨(UserSymb.fresh (VarCtx_to_VarSymbs
          (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩))).toVar, V1⟩
        (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hu₁))).toVar
      ∉ VarCtx_to_VarSymbs (VarCtx_insert
        ⟨(UserSymb.fresh (VarCtx_to_VarSymbs
          (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩))).toVar, V1⟩
        (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hu₁) :=
    UserSymb.fresh_not_mem _
  have hlt : (VarCtx_insert ⟨_, V2⟩ (VarCtx_insert ⟨_, V1⟩
      (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hu₁) hu₂).pairDepth < V.pairDepth := by
    have hV0 := VarCtx.pairDepth_insert (⟨z.toVar, V1.VTypeProd V2⟩ : VarSymb × VarType)
      (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hz_fresh
    rw [V_eq] at hV0
    simp only [VarCtx.pairDepth_insert, VarType.pairDepth] at hV0 ⊢
    omega
  unfold eqRecPeel
  obtain ⟨p⟩ := IH _ (((hV.erase _).insert hu₁ rfl).insert hu₂ rfl) hlt _
  refine ⟨Proof.ctx_cast V_eq ?_⟩
  have hP := Proof.pair_elim V1 V2 _ _ z hu₁ hu₂ hz_fresh rfl p
  simpa [WFF.pairElim_Finset, WFF.bindPair_Finset] using hP

/-- Reflexivity for the PAIR-FREE CORE, given the induction hypothesis at strictly smaller type. -/
theorem eqRecCore_refl {σ : Signature} : ∀ (V : VarCtx) (hV : V.AllUsr) (S : VarType)
    (hfp : V.firstPairVar = none) (t : Term σ V S),
    (∀ (A : VarType), sizeOf A < sizeOf S → ∀ (W : VarCtx) (hW : W.AllUsr) (u : Term σ W A),
        Nonempty (Proof σ W ∅ (eqRec W hW A u u))) →
    Nonempty (Proof σ V ∅ (eqRecCore V hV S hfp t t))
  | _, hV, .Var, hfp, t, _ => by rw [eqRecCore_var]; exact ⟨Proof.eq_intro t⟩
  | _, hV, .VTypeOne, hfp, t, _ => by rw [eqRecCore_unit]; exact ⟨Proof.top_intro⟩
  | V, hV, .VTypeProd A B, hfp, .pair a b, IH => by
      rw [eqRecCore_prod]
      obtain ⟨pa⟩ := IH A (by simp; try omega) V hV a
      obtain ⟨pb⟩ := IH B (by simp; try omega) V hV b
      exact ⟨Proof.and_intro pa pb⟩
  | _, hV, .VTypeBox A, hfp, .boxterm tt hsub h, IH => by
      rw [eqRecCore_box, boxCast_self]
      obtain ⟨p⟩ := IH A (by simp; try omega) _ (hV.of_box_sub hsub) tt
      exact ⟨Proof.nec hsub h p⟩
  | _, hV, .VTypeDia A, hfp, .diaterm x hx tt hsub h, IH => by
      rw [eqRecCore_dia_same _ _ _ _ _ _ _ _ rfl, diaCast_self]
      obtain ⟨p⟩ := IH A (by simp; try omega) _ (hV.of_dia_sub hsub) tt
      exact ⟨Proof.necx hsub h p⟩
  | _, _, _, hfp, .pair_elim _ _ _ _ _ w₂eq _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim

/-- ⭐**Reflexivity of the defined equality**: `⊢ t ≐ t`. -/
theorem eqRec_refl {σ : Signature} : ∀ (V : VarCtx) (hV : V.AllUsr) (S : VarType) (t : Term σ V S),
    Nonempty (Proof σ V ∅ (eqRec V hV S t t))
  | V, hV, S, t => by
    unfold eqRec
    split
    · exact eqRecPeel_refl _ _ _ _ _ _ _ t (fun W hW _ u => eqRec_refl W hW S u)
    · exact eqRecCore_refl _ _ _ _ t (fun A _ W hW u => eqRec_refl W hW A u)
termination_by V _ S _ => (sizeOf S, V.pairDepth)
decreasing_by
  · exact Prod.Lex.right _ (by assumption)
  · exact Prod.Lex.left _ _ (by assumption)

/-! ## Congruence / K-distribution infrastructure (for symmetry)

Symmetry must be an OBJECT implication `⊢ (a ≐ b) → (b ≐ a)`, because the modal cases transform the
equality UNDER a `□`/`□_x` — which needs K distribution, not just necessitation.  The peel case
needs the same thing for `pairElim`, which is `pair_elim` applied to a singleton hypothesis set. -/

/-- Transport a proof along an equality of HYPOTHESIS SETS (`Proof.ctx_cast` moves the `VarCtx`). -/
def Proof.hyp_cast {σ : Signature} {V : VarCtx} {Γ Γ' : Finset (WFF σ V)} {φ : WFF σ V}
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
    Proof.hyp_cast (by rw [Finset.empty_union]; exact Finset.union_comm _ _) (Proof.weak hK)
  have hbx : Proof σ W ((∅ ∪ {WFF.box_x x hx hsub h φ}) ∪ {WFF.dia x hx (neg ψ) hsub h})
      (WFF.box_x x hx hsub h φ) := Proof.ax (by simp)
  exact Proof.imp_elim hbx hd

/-- **`pairElim`-congruence**, in exactly the shape `eqRecPeel` produces: the peel's body is
    `pairElim ∘ bindPair`, so this is `Proof.pair_elim` at the singleton hypothesis set `{φ}`. -/
def Proof.congPeel {σ : Signature} {V W₂ : VarCtx} (T₁ T₂ : VarType) (u₁ u₂ z : UserSymb)
    (hu₁ : u₁.toVar ∉ VarCtx_to_VarSymbs V)
    (hu₂ : u₂.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁))
    (hz : z.toVar ∉ VarCtx_to_VarSymbs V)
    (w₂eq : VarCtx_insert ⟨z.toVar, .VTypeProd T₁ T₂⟩ V hz = W₂)
    {φ ψ : WFF σ (VarCtx_insert ⟨u₂.toVar, T₂⟩ (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂)}
    (hφψ : Proof σ (VarCtx_insert ⟨u₂.toVar, T₂⟩ (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂) ∅
             (φ.imp ψ)) :
    Proof σ W₂ ∅
      ((WFF.pairElim T₁ T₂ z.toVar rfl hz rfl w₂eq (WFF.bindPair T₁ T₂ u₁ u₂ hu₁ hu₂ φ)).imp
       (WFF.pairElim T₁ T₂ z.toVar rfl hz rfl w₂eq (WFF.bindPair T₁ T₂ u₁ u₂ hu₁ hu₂ ψ))) := by
  have h1 : Proof σ (VarCtx_insert ⟨u₂.toVar, T₂⟩ (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂)
      (∅ ∪ {φ}) ψ := Proof.imp_elim (Proof.weak hφψ) (Proof.ax (by simp))
  have hP := Proof.pair_elim T₁ T₂ u₁ u₂ z hu₁ hu₂ hz w₂eq h1
  simp only [WFF.pairElim_Finset, WFF.bindPair_Finset, Finset.empty_union,
    Finset.image_singleton] at hP
  exact Proof.imp_intro (by simpa using hP)

/-- Context transport distributes over implication. -/
theorem WFF_ctx_cast_imp {σ : Signature} {V W : VarCtx} (h : V = W) (φ ψ : WFF σ V) :
    h ▸ (φ.imp ψ) = (h ▸ φ).imp (h ▸ ψ) := by cases h; rfl

/-! ### Determinacy casts on the diagonal, with INDEPENDENT proof arguments

`eqRecCore_symm` rewrites both orientations, and the reversed one supplies the two subset/no-extras
proofs the other way round.  They are `Prop`s, so the cast is still the identity — but the equation
has to be stated with four independent arguments for `rw` to fire on it. -/

theorem boxCast_id {σ : Signature} {A : VarType} {V W : VarCtx}
    (hsub₁ : (VarCtx_box V).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (hsub₂ : (VarCtx_box V).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
    (tt : Term σ V A) : boxCast hsub₁ h₁ hsub₂ h₂ tt = tt := rfl

theorem diaCast_id {σ : Signature} {A : VarType} {x : VarSymb × VarType} {V W : VarCtx}
    {hx₁ hx₂ : x.1 ∉ VarCtx_to_VarSymbs V}
    (hsub₁ : (VarCtx_dia x V hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx₁).1)
    (hsub₂ : (VarCtx_dia x V hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx₂).1)
    (tt : Term σ (VarCtx_insert x V hx₂) A) :
    diaCast rfl hsub₁ h₁ hsub₂ h₂ tt = tt := rfl

/-- The ◇-arm at DIFFERENT witnesses: distinct witnesses can never be equated, so the defined
    equality is `⊥`.  (Needed only for symmetry, where `⊥ → ⊥` is `impId`.) -/
theorem eqRecCore_dia_ne {σ : Signature} {W : VarCtx} (hW : W.AllUsr)
    (hfp : W.firstPairVar = none) {A : VarType} {x₁ x₂ : VarSymb × VarType} {V₁ V₂ : VarCtx}
    {hx₁ : x₁.1 ∉ VarCtx_to_VarSymbs V₁} {hx₂ : x₂.1 ∉ VarCtx_to_VarSymbs V₂}
    (tt₁ : Term σ (VarCtx_insert x₁ V₁ hx₁) A) (tt₂ : Term σ (VarCtx_insert x₂ V₂ hx₂) A)
    (hsub₁ : (VarCtx_dia x₁ V₁ hx₁).1 ⊆ W.1)
    (h₁ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₁ V₁ hx₁).1)
    (hsub₂ : (VarCtx_dia x₂ V₂ hx₂).1 ⊆ W.1)
    (h₂ : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x₂ V₂ hx₂).1)
    (hx : ¬ (x₁ = x₂)) :
    eqRecCore W hW (.VTypeDia A) hfp (.diaterm x₁ hx₁ tt₁ hsub₁ h₁)
        (.diaterm x₂ hx₂ tt₂ hsub₂ h₂)
      = WFF.bot := by
  simp only [eqRecCore, dif_neg hx]

/-! ## Symmetry of `eqRec`

Stated as an object implication `⊢ (a ≐ b) → (b ≐ a)`.  The `.Var` base is ATOMIC symmetry of the
primitive equality — a Leibniz derivation via `eq_elim` that needs the `substVar` reduction lemmas,
not yet ported to v11 — so it is taken as a hypothesis, isolating that single dependency;
everything structural and modal is proved here.

⭐**The peel case is where v11 pays off.**  In v10 the peel chose its fresh names from
`… ∪ boundVars a ∪ boundVars b`, so `eqRecPeel … a b` and `eqRecPeel … b a` picked names differing
by a `Finset.union_right_comm`, and symmetry had to rewrite them into agreement.  In v11 the names
come from the ERASED CONTEXT alone — the terms play no part — so the two sides are literally the
same peel applied to swapped arguments, and `congPeel` of the induction hypothesis finishes. -/

/-- **Symmetry for the pair-free core**, given atomic Var-symmetry and the IH at smaller type. -/
theorem eqRecCore_symm {σ : Signature}
    (hVarSymm : ∀ (W : VarCtx), W.firstPairVar = none → ∀ (u v : Term σ W .Var),
      Nonempty (Proof σ W ∅ ((WFF.eq u v).imp (WFF.eq v u)))) :
    ∀ (V : VarCtx) (hV : V.AllUsr) (S : VarType) (hfp : V.firstPairVar = none) (a b : Term σ V S),
    (∀ (A : VarType), sizeOf A < sizeOf S → ∀ (W : VarCtx) (hW : W.AllUsr) (u v : Term σ W A),
        Nonempty (Proof σ W ∅ ((eqRec W hW A u v).imp (eqRec W hW A v u)))) →
    Nonempty (Proof σ V ∅ ((eqRecCore V hV S hfp a b).imp (eqRecCore V hV S hfp b a)))
  | _, hV, .Var, hfp, a, b, _ => by
      rw [eqRecCore_var, eqRecCore_var]; exact hVarSymm _ hfp a b
  | _, hV, .VTypeOne, hfp, a, b, _ => by
      rw [eqRecCore_unit, eqRecCore_unit]; exact ⟨Proof.impId⟩
  | V, hV, .VTypeProd A B, hfp, .pair a b, .pair c d, IH => by
      rw [eqRecCore_prod, eqRecCore_prod]
      obtain ⟨p1⟩ := IH A (by simp; try omega) V hV a c
      obtain ⟨p2⟩ := IH B (by simp; try omega) V hV b d
      exact ⟨Proof.congAnd p1 p2⟩
  | _, hV, .VTypeBox A, hfp, .boxterm tt₁ hsub₁ h₁, .boxterm tt₂ hsub₂ h₂, IH => by
      have hVeq := boxterm_ctx_unique hsub₁ h₁ hsub₂ h₂
      subst hVeq
      rw [eqRecCore_box, eqRecCore_box, boxCast_id, boxCast_id]
      obtain ⟨p⟩ := IH A (by simp; try omega) _ (hV.of_box_sub hsub₁) tt₁ tt₂
      exact ⟨Proof.congBox hsub₁ h₁ p⟩
  | _, hV, .VTypeDia A, hfp, .diaterm x₁ hx₁ tt₁ hsub₁ h₁, .diaterm x₂ hx₂ tt₂ hsub₂ h₂, IH => by
      by_cases hx : x₁ = x₂
      · subst hx
        have hVeq := diaterm_ctx_unique hsub₁ h₁ hsub₂ h₂
        subst hVeq
        rw [eqRecCore_dia_same _ _ _ _ _ _ _ _ rfl, eqRecCore_dia_same _ _ _ _ _ _ _ _ rfl,
            diaCast_id, diaCast_id]
        obtain ⟨p⟩ := IH A (by simp; try omega) _ (hV.of_dia_sub hsub₁) tt₁ tt₂
        exact ⟨Proof.congBoxx hsub₁ h₁ p⟩
      · rw [eqRecCore_dia_ne _ _ _ _ _ _ _ _ hx,
            eqRecCore_dia_ne _ _ _ _ _ _ _ _ (fun hh => hx hh.symm)]
        exact ⟨Proof.impId⟩
  | _, _, _, hfp, .pair_elim _ _ _ _ _ w₂eq _, _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim
  | _, _, _, hfp, _, .pair_elim _ _ _ _ _ w₂eq _, _ =>
      (VarCtx.firstPairVar_none_no_pair hfp (pair_elim_ctx_mem w₂eq)).elim

/-- **Symmetry for the peel case.**  Both orientations peel with the SAME fresh names, so this is
    `congPeel` of the induction hypothesis at the unpaired context. -/
theorem eqRecPeel_symm {σ : Signature} (V : VarCtx) (hV : V.AllUsr) (S : VarType)
    (z : UserSymb) (V1 V2 : VarType)
    (hzmem : (⟨z.toVar, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1)
    (a b : Term σ V S)
    (IH : ∀ (W : VarCtx) (hW : W.AllUsr), W.pairDepth < V.pairDepth →
            ∀ (u v : Term σ W S),
              Nonempty (Proof σ W ∅ ((eqRec W hW S u v).imp (eqRec W hW S v u)))) :
    Nonempty (Proof σ V ∅ ((eqRecPeel V hV S z V1 V2 hzmem a b).imp
                           (eqRecPeel V hV S z V1 V2 hzmem b a))) := by
  have hz_fresh : z.toVar ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) :=
    VarCtx_erase_fresh hzmem
  have V_eq : VarCtx_insert ⟨z.toVar, V1.VTypeProd V2⟩
      (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hz_fresh = V :=
    VarCtx_insert_erase hzmem hz_fresh
  have hu₁ : (UserSymb.fresh (VarCtx_to_VarSymbs
        (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩))).toVar
      ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) :=
    UserSymb.fresh_not_mem _
  have hu₂ : (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx_insert
        ⟨(UserSymb.fresh (VarCtx_to_VarSymbs
          (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩))).toVar, V1⟩
        (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hu₁))).toVar
      ∉ VarCtx_to_VarSymbs (VarCtx_insert
        ⟨(UserSymb.fresh (VarCtx_to_VarSymbs
          (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩))).toVar, V1⟩
        (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hu₁) :=
    UserSymb.fresh_not_mem _
  have hlt : (VarCtx_insert ⟨_, V2⟩ (VarCtx_insert ⟨_, V1⟩
      (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hu₁) hu₂).pairDepth < V.pairDepth := by
    have hV0 := VarCtx.pairDepth_insert (⟨z.toVar, V1.VTypeProd V2⟩ : VarSymb × VarType)
      (VarCtx_erase V ⟨z.toVar, V1.VTypeProd V2⟩) hz_fresh
    rw [V_eq] at hV0
    simp only [VarCtx.pairDepth_insert, VarType.pairDepth] at hV0 ⊢
    omega
  unfold eqRecPeel
  rw [← WFF_ctx_cast_imp]
  refine ⟨Proof.ctx_cast V_eq ?_⟩
  exact Proof.congPeel V1 V2 _ _ z hu₁ hu₂ hz_fresh rfl
    (IH _ (((hV.erase _).insert hu₁ rfl).insert hu₂ rfl) hlt _ _).some

/-- ⭐**Symmetry of the defined equality**: `⊢ (a ≐ b) → (b ≐ a)`, at every type and context. -/
theorem eqRec_symm {σ : Signature}
    (hVarSymm : ∀ (W : VarCtx), W.firstPairVar = none → ∀ (u v : Term σ W .Var),
      Nonempty (Proof σ W ∅ ((WFF.eq u v).imp (WFF.eq v u)))) :
    ∀ (V : VarCtx) (hV : V.AllUsr) (S : VarType) (a b : Term σ V S),
    Nonempty (Proof σ V ∅ ((eqRec V hV S a b).imp (eqRec V hV S b a)))
  | V, hV, S, a, b => by
    unfold eqRec
    split
    · exact eqRecPeel_symm _ _ _ _ _ _ _ a b
        (fun W hW _ u v => eqRec_symm hVarSymm W hW S u v)
    · exact eqRecCore_symm hVarSymm _ _ _ _ a b
        (fun A _ W hW u v => eqRec_symm hVarSymm W hW A u v)
termination_by V _ S _ _ => (sizeOf S, V.pairDepth)
decreasing_by
  · exact Prod.Lex.right _ (by assumption)
  · exact Prod.Lex.left _ _ (by assumption)
