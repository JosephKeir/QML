import QML.QML_v11_WFFSubst

/-!
# QML v11 — the proof system

Classical natural deduction: exactly one formula in the consequent, ELIM rules rather than
left-introduction plus cut.  Freshness and eigenvariable side conditions are discharged by the
context typing rather than carried as premises.

⭐**Where the v11 redesign shows up.**  This is the file the whole "canonical bound variables"
reform was for, and it changes in exactly the way the design predicted:

* **Binder-introducing rules take a `UserSymb`.**  `all_intro`'s eigenvariable is user-facing —
  it is FREE in the subproof, so it has a meaningful name — and the conclusion's binder is
  canonical.  The rule renames the one to the other with `rename`, landing DEFINITIONALLY in
  `insertBnd T V` (no cast): `insertBnd T V` unfolds to `VarCtx_insert ⟨V.nextBnd, T⟩ V _`.
  The user-facing type is injected at the rule boundary and nowhere else, which is the whole
  point of using a type rather than an `isUsr` predicate.
* **Binder-eliminating rules mention no variable at all.**  `all_elim` takes the TYPE and a term;
  the slot substituted for is `V.nextBnd`, a function of the context.
* ⛔**`box_ext` / `dia_ext` are GONE, and `eq` is PRIMITIVE ONLY AT `.Var`.**  Equality at every
  compound type is DEFINED from the `.Var` one by `eqRec`, recursing through exactly those two
  extensionality principles — so they are definitional unfoldings of that definition, not rules.
  ⚠️Until `eqRec` is ported to v11 there is NO compound-type equality here at all; nothing uses it
  yet, but that is a real gap rather than a no-op.
* ⛔**`pair_elim_alpha` is GONE.**  v10 needed it as a PRIMITIVE rule: α-variants of a stuck
  `pair_elim` are not derivable (pair-β fires only on a literal pair, and a positive product has
  no projections to η-expand a neutral `z`).  In v11 they are not even EXPRESSIBLE — two
  `pair_elim`s over the same base context necessarily carry the same slots — so the rule is
  vacuous and the soundness obligation it created (α-invariance of `interpTerm`) disappears.
-/

/-! ## Finset liftings and the public substitution API -/

/-- The public substitution API: `substVar`'s value, with its `binderPairDepth` bound dropped. -/
def WFF.subst {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) : WFF σ V :=
  (WFF.substVar hx s φ).val

theorem WFF.binderPairDepth_subst {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.subst hx s φ) ≤ WFF.binderPairDepth φ :=
  (WFF.substVar hx s φ).property

/-- Weakening a hypothesis set by a user variable. -/
def WFF.ctx_extU_Finset {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) :
    Finset (WFF σ V) → Finset (WFF σ (VarCtx_insert ⟨u.toVar, T⟩ V hu)) :=
  fun Γ => Γ.image (WFF.ctx_extU u T hu)

/-- Weakening a hypothesis set by an ARBITRARY symbol (what `K_dia` needs, since a `◇`-witness
    is a promoted free variable and need not be user-named). -/
def WFF.ctx_ext_Finset {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) :
    Finset (WFF σ V) → Finset (WFF σ (VarCtx_insert xv V hv)) :=
  fun Γ => Γ.image (WFF.ctx_ext xv hv)

/-- Distributing a `pair_elim` over a hypothesis set. -/
def WFF.pairElim_Finset {σ : Signature} {V W₁ W₂ : VarCtx}
    (T₁ T₂ : VarType) (z : VarSymb) (hzu : z.isUsr = true)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) :
    Finset (WFF σ W₁) → Finset (WFF σ W₂) :=
  fun Γ => Γ.image (WFF.pairElim T₁ T₂ z hzu hz w₁eq w₂eq)

/-! ## Binding a user-named component pair onto the canonical slots

⭐The `pair_elim` rule is the exact parallel of `all_intro`: the user builds the subproof with
FREE, user-named components, and the rule renames them to the canonical slots as it BINDS them.
Renaming happens on the FORMULA, never on the proof — which is what makes `all_intro` cheap and
makes this cheap too.

⚠️Getting this wrong is what put SLOTS into a proof context.  The earlier version stated the
premise directly over `insertBnd2 T₁ T₂ V`, so a proof context held `⟨.bnd n, T₁⟩` — pair-typed
whenever `T₁` is a product, which is exactly the case `eqRec`'s peel cannot re-pair.  Contexts hold
only FREE variables, so they must never contain reserved bound names; this restores that. -/

/-- Move a formula from a split context with USER-named components onto the canonical slots.
    `rename` acts on the TOP entry, so the second component goes first, then the pair is commuted,
    then the first.  Targeting `V.nextBnd` and `(insertBnd T₁ V).nextBnd` makes the landing context
    `insertBnd2 T₁ T₂ V` DEFINITIONALLY — there is no final cast. -/
def WFF.bindPair {σ : Signature} {V : VarCtx} (T₁ T₂ : VarType) (u₁ u₂ : UserSymb)
    (hu₁ : u₁.toVar ∉ VarCtx_to_VarSymbs V)
    (hu₂ : u₂.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁))
    (φ : WFF σ (VarCtx_insert ⟨u₂.toVar, T₂⟩ (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂)) :
    WFF σ (VarCtx.insertBnd2 T₁ T₂ V) := by
  have hlvl : VarCtx.bndLevel (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) = VarCtx.bndLevel V :=
    VarCtx.bndLevel_insert_isUsr _ _ _ rfl
  -- the second slot is fresh for the user-named split context …
  have hs₂u : (VarCtx.insertBnd T₁ V).nextBnd
      ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) := by
    change VarSymb.bnd (VarCtx.bndLevel (VarCtx.insertBnd T₁ V)) ∉ _
    rw [VarCtx.bndLevel_insertBnd]
    exact VarCtx.notMem_bnd_of_le (by omega)
  -- … and for `V` itself
  have hs₂V : (VarCtx.insertBnd T₁ V).nextBnd ∉ VarCtx_to_VarSymbs V := by
    change VarSymb.bnd (VarCtx.bndLevel (VarCtx.insertBnd T₁ V)) ∉ _
    rw [VarCtx.bndLevel_insertBnd]
    exact VarCtx.notMem_bnd_of_le (by omega)
  -- STEP 1 — rename the top (second) component onto the second slot
  have φ₂ := WFF.rename u₂.toVar (VarCtx.insertBnd T₁ V).nextBnd T₂ hu₂ hs₂u φ
  -- STEP 2 — commute, so the first component is on top
  have hu₁' : u₁.toVar ∉ VarCtx_to_VarSymbs
      (VarCtx_insert ⟨(VarCtx.insertBnd T₁ V).nextBnd, T₂⟩ V hs₂V) :=
    not_mem_VarSymbs_insert
      (by
        change u₁.toVar ≠ VarSymb.bnd (VarCtx.bndLevel (VarCtx.insertBnd T₁ V))
        exact VarCtx.ne_nextBnd_of_isUsr rfl _)
      hu₁
  have φ₃ := (VarCtx_insert_comm
      (a := (⟨(VarCtx.insertBnd T₁ V).nextBnd, T₂⟩ : VarSymb × VarType))
      (b := (⟨u₁.toVar, T₁⟩ : VarSymb × VarType)) hs₂u hu₁' ▸ φ₂ :
    WFF σ (VarCtx_insert ⟨u₁.toVar, T₁⟩
      (VarCtx_insert ⟨(VarCtx.insertBnd T₁ V).nextBnd, T₂⟩ V hs₂V) hu₁'))
  -- STEP 3 — rename the first component onto the first slot
  have hs₁ : V.nextBnd ∉ VarCtx_to_VarSymbs
      (VarCtx_insert ⟨(VarCtx.insertBnd T₁ V).nextBnd, T₂⟩ V hs₂V) := by
    refine not_mem_VarSymbs_insert ?_ (VarCtx.nextBnd_not_mem V)
    change VarSymb.bnd (VarCtx.bndLevel V)
      ≠ VarSymb.bnd (VarCtx.bndLevel (VarCtx.insertBnd T₁ V))
    rw [VarCtx.bndLevel_insertBnd]
    simp
  have φ₄ := WFF.rename u₁.toVar V.nextBnd T₁ hu₁' hs₁ φ₃
  -- STEP 4 — commute back; the target is `insertBnd2 T₁ T₂ V` definitionally
  change WFF σ (VarCtx_insert (⟨(VarCtx.insertBnd T₁ V).nextBnd, T₂⟩ : VarSymb × VarType)
    (VarCtx_insert (⟨V.nextBnd, T₁⟩ : VarSymb × VarType) V (VarCtx.nextBnd_not_mem V))
    (VarCtx.nextBnd_not_mem (VarCtx.insertBnd T₁ V)))
  exact VarCtx_insert_comm
    (a := (⟨V.nextBnd, T₁⟩ : VarSymb × VarType))
    (b := (⟨(VarCtx.insertBnd T₁ V).nextBnd, T₂⟩ : VarSymb × VarType))
    hs₁ (VarCtx.nextBnd_not_mem (VarCtx.insertBnd T₁ V)) ▸ φ₄

/-- `bindPair` on a hypothesis set. -/
def WFF.bindPair_Finset {σ : Signature} {V : VarCtx} (T₁ T₂ : VarType) (u₁ u₂ : UserSymb)
    (hu₁ : u₁.toVar ∉ VarCtx_to_VarSymbs V)
    (hu₂ : u₂.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁)) :
    Finset (WFF σ (VarCtx_insert ⟨u₂.toVar, T₂⟩ (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂))
      → Finset (WFF σ (VarCtx.insertBnd2 T₁ T₂ V)) :=
  fun Γ => Γ.image (WFF.bindPair T₁ T₂ u₁ u₂ hu₁ hu₂)

/-! ## Modal bridging (ported verbatim from v10)

`◇_x`'s context contains `□`'s, so a `◇`-side hypothesis restricts to a `□`-side one.  Used by
`K_dia` to state the plain-`□` part of its hypothesis set. -/

lemma in_box_of_in_dia {x : VarSymb × VarType} {V W : VarCtx}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V}
    (in_dia : ∀ p ∈ W.1, p.2.isBox = true → p ∈ (VarCtx_dia x V hx).1) :
    ∀ p ∈ W.1, p.2.isBox = true → p ∈ (VarCtx_box V).1 := by
  intro p pmemW pbox
  have pmem := in_dia p pmemW pbox
  rw [VarCtx_dia_fst] at pmem
  rcases Finset.mem_insert.mp pmem with diacase | boxcase
  · exfalso
    rw [diacase] at pbox
    simp [VarType.isBox] at pbox
  · exact boxcase

lemma box_subs_of_dia_subs {x : VarSymb × VarType} {V W : VarCtx}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V}
    (dia_in_W : (VarCtx_dia x V hx).1 ⊆ W.1) :
    (VarCtx_box V).1 ⊆ W.1 := by
  intro y ybox
  refine dia_in_W ?_
  rw [VarCtx_dia_fst]
  exact Finset.mem_insert_of_mem ybox

/-! ## Deduction rules -/

inductive Proof (σ : Signature) : (V : VarCtx) → Finset (WFF σ V) → WFF σ V → Type where
  -- Structural
  | ax       : φ ∈ (Γ : Finset (WFF σ V))
               → Proof σ V Γ φ
  | weak     : Proof σ V Γ φ
               → Proof σ V (Γ ∪ {ψ}) φ
  | weak_ctx : (u : UserSymb) → (T : VarType) → (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
               → Proof σ V Γ φ
               → Proof σ (VarCtx_insert ⟨u.toVar, T⟩ V hu)
                   (WFF.ctx_extU_Finset u T hu Γ) (WFF.ctx_extU u T hu φ)
  -- Conjunction
  | and_intro  : Proof σ V Γ φ → Proof σ V Γ ψ → Proof σ V Γ (φ.and ψ)
  | and_elim_l : Proof σ V Γ (φ.and ψ) → Proof σ V Γ φ
  | and_elim_r : {φ : WFF σ V} → Proof σ V Γ (φ.and ψ) → Proof σ V Γ ψ
  -- Disjunction
  | or_intro_l : Proof σ V Γ φ → Proof σ V Γ (φ.or ψ)
  | or_intro_r : {φ : WFF σ V} → Proof σ V Γ ψ → Proof σ V Γ (φ.or ψ)
  | or_elim    : Proof σ V Γ (φ.or ψ)
                 → Proof σ V (Γ ∪ {φ}) χ → Proof σ V (Γ ∪ {ψ}) χ
                 → Proof σ V Γ χ
  -- Implication
  | imp_intro  : Proof σ V (Γ ∪ {φ}) ψ → Proof σ V Γ (φ.imp ψ)
  | imp_elim   : Proof σ V Γ (φ.imp ψ) → Proof σ V Γ φ → Proof σ V Γ ψ
  -- Truth and falsity
  | top_intro  : Proof σ V Γ .top
  | bot_elim   : Proof σ V Γ .bot → Proof σ V Γ φ
  -- Classical logic
  | lem        : (φ : WFF σ V) → Proof σ V Γ (φ.or (neg φ))
  -- ⭐Universal quantifier.  The eigenvariable is USER-facing (free in the subproof); the
  -- conclusion's binder is the canonical slot, and `rename` moves one to the other.  The
  -- target context `VarCtx_insert ⟨V.nextBnd, T⟩ V _` IS `VarCtx.insertBnd T V`, definitionally.
  | all_intro  : (u : UserSymb) → (T : VarType) → (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert ⟨u.toVar, T⟩ V hu)}
                 → Proof σ (VarCtx_insert ⟨u.toVar, T⟩ V hu) (WFF.ctx_extU_Finset u T hu Γ) φ
                 → Proof σ V Γ
                     (.all T (WFF.rename u.toVar V.nextBnd T hu (VarCtx.nextBnd_not_mem V) φ))
  -- Elimination mentions no variable at all: the slot is a function of `V`.
  | all_elim   : (T : VarType) → {φ : WFF σ (VarCtx.insertBnd T V)}
                 → (t : Term σ V T)
                 → Proof σ V Γ (.all T φ)
                 → Proof σ V Γ (WFF.subst (VarCtx.nextBnd_not_mem V) t φ)
  -- Existential quantifier
  | ex_intro   : (T : VarType) → {φ : WFF σ (VarCtx.insertBnd T V)}
                 → (t : Term σ V T)
                 → Proof σ V Γ (WFF.subst (VarCtx.nextBnd_not_mem V) t φ)
                 → Proof σ V Γ (.ex T φ)
  | ex_elim    : (u : UserSymb) → (T : VarType) → (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert ⟨u.toVar, T⟩ V hu)}
                 → Proof σ V Γ
                     (.ex T (WFF.rename u.toVar V.nextBnd T hu (VarCtx.nextBnd_not_mem V) φ))
                 → Proof σ (VarCtx_insert ⟨u.toVar, T⟩ V hu)
                     (WFF.ctx_extU_Finset u T hu Γ ∪ {φ}) (WFF.ctx_extU u T hu ψ)
                 → Proof σ V Γ ψ
  -- ⭐Equality, PRIMITIVE ONLY AT `.Var`.  Equality at compound types is DEFINED from this one by
  -- `eqRec`, recursing through the extensionality principles; `box_ext` / `dia_ext` are therefore
  -- not rules here but definitional unfoldings of that definition, and are gone.
  | eq_intro   : (t : Term σ V .Var) → Proof σ V Γ (WFF.eq t t)
  | eq_elim    : (u : UserSymb) → (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert ⟨u.toVar, .Var⟩ V hu)} → (t s : Term σ V .Var)
                 → Proof σ V Γ (WFF.eq t s)
                 → Proof σ V Γ (WFF.subst hu t φ)
                 → Proof σ V Γ (WFF.subst hu s φ)
  -- ⭐Pairing: the positive eliminator, and the exact parallel of `all_intro`.  The subproof is
  -- built with FREE, USER-named components `u₁ u₂`; the rule renames them onto the canonical slots
  -- as it BINDS them (`bindPair`), renaming the FORMULA rather than the proof.  `z` stays named
  -- because it stays FREE in `W₂`.
  -- ⚠️Stating the premise directly over `insertBnd2 T₁ T₂ V` — as an earlier version did — puts
  -- SLOTS into a proof context, and they are pair-typed whenever `T₁`/`T₂` is a product.  That is
  -- the one case `eqRec`'s peel cannot re-pair, and it is why contexts must hold only free
  -- (user-named) variables.
  | pair_elim  : (T₁ T₂ : VarType) → (u₁ u₂ : UserSymb) → (z : UserSymb)
                 → (hu₁ : u₁.toVar ∉ VarCtx_to_VarSymbs V)
                 → (hu₂ : u₂.toVar
                     ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁))
                 → (hz : z.toVar ∉ VarCtx_to_VarSymbs V)
                 → (w₂eq : VarCtx_insert ⟨z.toVar, .VTypeProd T₁ T₂⟩ V hz = W₂)
                 → {Γ : Finset (WFF σ (VarCtx_insert ⟨u₂.toVar, T₂⟩
                     (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂))}
                 → {φ : WFF σ (VarCtx_insert ⟨u₂.toVar, T₂⟩
                     (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂)}
                 → Proof σ (VarCtx_insert ⟨u₂.toVar, T₂⟩
                     (VarCtx_insert ⟨u₁.toVar, T₁⟩ V hu₁) hu₂) Γ φ
                 → Proof σ W₂
                     (WFF.pairElim_Finset T₁ T₂ z.toVar rfl hz rfl w₂eq
                       (WFF.bindPair_Finset T₁ T₂ u₁ u₂ hu₁ hu₂ Γ))
                     (WFF.pairElim T₁ T₂ z.toVar rfl hz rfl w₂eq
                       (WFF.bindPair T₁ T₂ u₁ u₂ hu₁ hu₂ φ))
  -- Modal K
  | K_box      : (hsub : (VarCtx_box V).1 ⊆ W.1)
                 → (h_no_box_extras :
                     ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
                 → Proof σ V Γ φ
                 → Proof σ W (WFF.box_Finset hsub h_no_box_extras Γ)
                     (WFF.box φ hsub h_no_box_extras)
  -- The multi-conclusion K rule in single-conclusion form: from `Γ, Δ, ψ ⊢ φ` conclude
  -- `□Γ, □_x Δ, ◇_x ψ ⊢ ◇_x φ`.  `Γ` is `x`-free (plain `□`); `Δ` may mention the witness `x`
  -- (witnessed box `□_x = ¬◇_x¬`).
  | K_dia      : (x : VarSymb × VarType)
                 → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
                 → (h_no_box_extras :
                     ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
                 → {φ ψ : WFF σ (VarCtx_insert x V hx)}
                 → {Γ : Finset (WFF σ V)}
                 → {Δ : Finset (WFF σ (VarCtx_insert x V hx))}
                 → Proof σ (VarCtx_insert x V hx)
                     ((WFF.ctx_ext_Finset x hx Γ) ∪ Δ ∪ {ψ}) φ
                 → Proof σ W ((WFF.box_Finset (box_subs_of_dia_subs hsub)
                       (in_box_of_in_dia h_no_box_extras) Γ)
                     ∪ (WFF.box_x_Finset x hx hsub h_no_box_extras Δ)
                     ∪ {WFF.dia x hx ψ hsub h_no_box_extras})
                     (WFF.dia x hx φ hsub h_no_box_extras)
  | dia_bot    : (x : VarSymb × VarType)
                 → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {W : VarCtx}
                 → (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
                 → (h_no_box_extras :
                     ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
                 → {Γ : Finset (WFF σ W)}
                 → Proof σ W Γ (WFF.dia x hx WFF.bot hsub h_no_box_extras)
                 → Proof σ W Γ WFF.bot
