import QML.QML_Full_v10_Part1

/-! ## Relation Symbols -/

-- `Rel σ V n`: an n-ary relation symbol partially applied to terms over `V`.
-- Note: there is NO `pair_elim` constructor here.  Since `Rel.eval` only takes
-- `Term σ V .Var` (a Var-typed term, which has no modal binders inside),
-- `Rel.pairElim` (below) never has a "stuck" case — it always fully distributes
-- through `Rel` down to the `Term` components.  Stuck cases (modal binders)
-- only arise at the WFF layer, where the WFF-level `pair_elim` constructor
-- handles them.
inductive Rel (σ : Signature) (V : VarCtx) : ℕ → Type where
  | R    : {r : σ.RelSyms // σ.relArity r = n} → Rel σ V n
  | eval : Rel σ V (Nat.succ n) → Term σ V .Var → Rel σ V n
  deriving DecidableEq


/-! ### Bound Variables -/

-- Collect the bound variable symbols inside a Rel.  Mirrors `Func.boundVars`.
-- Used to require that `new` doesn't clash with any binder when renaming.
def Rel.boundVars {σ : Signature} {V : VarCtx} {n : ℕ} :
    Rel σ V n → Finset VarSymb
  | .R _       => ∅
  | .eval R' t => Rel.boundVars R' ∪ Term.boundVars t

/-! ### Node Count -/

-- Count constructor nodes inside a Rel.  Used as part of the `ctx_rest`
-- termination measure (rename-invariant; see `Rel.numNodes_rename`).
def Rel.numNodes {σ : Signature} {V : VarCtx} {n : ℕ} :
    Rel σ V n → Nat
  | .R _       => 1
  | .eval R' t => 1 + Rel.numNodes R' + Term.numNodes t

-- Count `.diaterm` constructors inside a Rel (via its `.eval` Term arguments).
-- Mirrors `Func.diaCount`'s delegation pattern.  Used as part of
-- `WFF.ctx_rest`'s termination measure (modal beta on `.dia` mirrors
-- `Term.ctx_rest`'s `.diaterm` Case 3 handling).
def Rel.diaCount {σ : Signature} {V : VarCtx} {n : ℕ} :
    Rel σ V n → Nat
  | .R _       => 0
  | .eval R' t => Rel.diaCount R' + Term.diaCount t

/-! ### Variable Renaming -/

-- Rename `old → new` inside a Rel.  Mirrors `Func.rename`; structural
-- recursion on the Rel, delegating to `Term.rename` for term components.
-- Requires `new ∉ Rel.boundVars R` to avoid capture.
def Rel.rename {σ : Signature} (old new : VarSymb) (repl_type : VarType)
    (V W : VarCtx) (n : ℕ)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (R : Rel σ W n) (new_not_bound : new ∉ Rel.boundVars R)
    : Rel σ (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) n := by
  match R, new_not_bound with
  | .R h, _ => exact .R h
  | .eval R' t, h_nb =>
      have h_nb_R : new ∉ Rel.boundVars R' :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      exact .eval
        (Rel.rename old new repl_type V W _ old_fresh new_fresh Wdef R' h_nb_R)
        (Term.rename old new repl_type V W _ old_fresh new_fresh Wdef t h_nb_t)

-- `Rel.rename` only swaps VarSymbs, never adding constructor nodes.
theorem Rel.numNodes_rename {σ : Signature}
    (old new : VarSymb) (repl_type : VarType) (V W : VarCtx) (n : ℕ)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (R : Rel σ W n) (h_nb : new ∉ Rel.boundVars R) :
    Rel.numNodes (Rel.rename old new repl_type V W n
                    old_fresh new_fresh Wdef R h_nb)
      = Rel.numNodes R := by
  match R, h_nb with
  | .R _, _ => rfl
  | .eval R' t, h_nb_eval =>
      have h_nb_R : new ∉ Rel.boundVars R' :=
        fun hmem => h_nb_eval (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t :=
        fun hmem => h_nb_eval (Finset.mem_union_right _ hmem)
      have ih_R := Rel.numNodes_rename old new repl_type V W _
                     old_fresh new_fresh Wdef R' h_nb_R
      have ih_t := Term.numNodes_rename old new repl_type V W _
                     old_fresh new_fresh Wdef t h_nb_t
      change 1 + Rel.numNodes _ + Term.numNodes _
           = 1 + Rel.numNodes R' + Term.numNodes t
      omega

-- `Rel.rename` only swaps VarSymbs, never introducing `.diaterm` constructors.
-- Mirrors `Rel.numNodes_rename`'s case structure.
theorem Rel.diaCount_rename {σ : Signature}
    (old new : VarSymb) (repl_type : VarType) (V W : VarCtx) (n : ℕ)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (R : Rel σ W n) (h_nb : new ∉ Rel.boundVars R) :
    Rel.diaCount (Rel.rename old new repl_type V W n
                    old_fresh new_fresh Wdef R h_nb)
      = Rel.diaCount R := by
  match R, h_nb with
  | .R _, _ => rfl
  | .eval R' t, h_nb_eval =>
      have h_nb_R : new ∉ Rel.boundVars R' :=
        fun hmem => h_nb_eval (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t :=
        fun hmem => h_nb_eval (Finset.mem_union_right _ hmem)
      have ih_R := Rel.diaCount_rename old new repl_type V W _
                     old_fresh new_fresh Wdef R' h_nb_R
      have ih_t := Term.diaCount_rename old new repl_type V W _
                     old_fresh new_fresh Wdef t h_nb_t
      change Rel.diaCount _ + Term.diaCount _
           = Rel.diaCount R' + Term.diaCount t
      omega

-- `Rel.rename`'s bound vars stay within the original's plus `new`.
theorem Rel.boundVars_rename_subset {σ : Signature}
    (old new : VarSymb) (repl_type : VarType) (V W : VarCtx) (n : ℕ)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (R : Rel σ W n) (h_nb : new ∉ Rel.boundVars R) :
    Rel.boundVars (Rel.rename old new repl_type V W n
                     old_fresh new_fresh Wdef R h_nb)
      ⊆ insert new (Rel.boundVars R) := by
  match R, h_nb with
  | .R _, _ => exact Finset.empty_subset _
  | .eval R' t, h_nb_eval =>
      have h_nb_R : new ∉ Rel.boundVars R' :=
        fun hmem => h_nb_eval (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t :=
        fun hmem => h_nb_eval (Finset.mem_union_right _ hmem)
      have ih_R := Rel.boundVars_rename_subset old new repl_type V W _
                     old_fresh new_fresh Wdef R' h_nb_R
      have ih_t := Term.boundVars_rename_subset old new repl_type V W _
                     old_fresh new_fresh Wdef t h_nb_t
      intro x hx
      rcases Finset.mem_union.mp hx with hR | ht
      · rcases Finset.mem_insert.mp (ih_R hR) with rfl | hR'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hR')
      · rcases Finset.mem_insert.mp (ih_t ht) with rfl | ht'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ht')

/-! ### Context Extension -/

-- Lift a Rel into a larger context (adding one variable `xv`).  Mirrors
-- `Func.ctx_ext` / `Term.ctx_ext`.  The `.pair_elim` arm mirrors
-- `Term.ctx_ext`'s `.pair_elim` arm: detect collisions between xv and
-- the pair_elim binders, α-rename via `Rel.rename` when needed, then recurse
-- on the body.
def Rel.ctx_ext {σ : Signature} {V : VarCtx} {n : ℕ}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (R : Rel σ V n) : Rel σ (VarCtx_insert xv V hxv) n := by
  match R with
  | .R h       => exact .R h
  | .eval R' t =>
      exact .eval (Rel.ctx_ext xv hxv R')
                  (Term.ctx_ext xv hxv t)

-- `Rel.ctx_ext` preserves `diaCount` (only delegates to `Term.ctx_ext`,
-- which preserves `Term.diaCount`).  Mirrors `Func.diaCount_ctx_ext`.
theorem Rel.diaCount_ctx_ext {σ : Signature} {V : VarCtx} {n : ℕ}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (R : Rel σ V n) :
    Rel.diaCount (Rel.ctx_ext xv hxv R) = Rel.diaCount R := by
  match R with
  | .R _ =>
      unfold Rel.ctx_ext
      rfl
  | .eval R' t =>
      have ih_R := Rel.diaCount_ctx_ext xv hxv R'
      have ih_t := Term.diaCount_ctx_ext xv hxv t
      unfold Rel.ctx_ext
      simp only [Rel.diaCount]
      omega

/-! ### Context Restriction -/

-- Substitute the variable `⟨x, S⟩` with the term `s` inside a Rel.  Mirrors
-- `Func.ctx_rest`; structural recursion on the Rel, delegating the
-- Term-level restriction to `Term.ctx_rest`.  The `h_pf` precondition
-- (no pair-typed binders in the extended context) is propagated through.
def Rel.ctx_rest {σ : Signature} {V : VarCtx} {n : ℕ}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (R : Rel σ (VarCtx_insert ⟨x, S⟩ V hx) n) : Rel σ V n := by
  match R with
  | .R h       => exact .R h
  | .eval R' t =>
      exact .eval (Rel.ctx_rest hx h_pf s R')
                  (Term.ctx_rest hx h_pf s t)

/-! ### Unpair -/

-- Translate a Rel from a "joined" context `W₁ = V + ⟨z, V1×V2⟩` to a "split"
-- context `W₂ = V + {v1, v2}` (with v1 : V1, v2 : V2).  Mirrors `Func.unpair`:
-- structural recursion delegating to `Term.unpair` for term components.
-- `z` cannot appear as a `.Var` at the leaves (Rel uses `Term σ V .Var`-typed
-- arguments and z is `.VTypeProd`), so the leaves are well-handled.
def Rel.unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
    (V W₁ W₂ : VarCtx) (N : ℕ)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (input : Rel σ W₁ N)
    (h_v1_nb : v1 ∉ Rel.boundVars input)
    (h_v2_nb : v2 ∉ Rel.boundVars input)
    : Rel σ W₂ N := by
  match input, h_v1_nb, h_v2_nb with
  | .R h, _, _ => exact .R h
  | .eval R' t, hf1, hf2 =>
      have hg1 : v1 ∉ Rel.boundVars R' :=
        fun hmem => hf1 (Finset.mem_union_left _ hmem)
      have hg2 : v2 ∉ Rel.boundVars R' :=
        fun hmem => hf2 (Finset.mem_union_left _ hmem)
      have ht1 : v1 ∉ Term.boundVars t :=
        fun hmem => hf1 (Finset.mem_union_right _ hmem)
      have ht2 : v2 ∉ Term.boundVars t :=
        fun hmem => hf2 (Finset.mem_union_right _ hmem)
      exact .eval
        (Rel.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def R' hg1 hg2)
        (Term.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def t ht1 ht2)

-- `Rel.unpair` preserves `diaCount`.  Structural on the two Rel constructors.
theorem Rel.diaCount_unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType)
    (v1 v2 : VarSymb) (V W₁ W₂ : VarCtx) (N : ℕ)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (input : Rel σ W₁ N)
    (h_v1_nb : v1 ∉ Rel.boundVars input)
    (h_v2_nb : v2 ∉ Rel.boundVars input) :
    Rel.diaCount (Rel.unpair z V1 V2 v1 v2 V W₁ W₂ N
                    hz hv1 hv2 hv1v2 W₁def W₂def input h_v1_nb h_v2_nb)
      = Rel.diaCount input := by
  match input, h_v1_nb, h_v2_nb with
  | .R _, _, _ =>
      unfold Rel.unpair
      rfl
  | .eval R' t, hf1, hf2 =>
      have hg1 : v1 ∉ Rel.boundVars R' :=
        fun hmem => hf1 (Finset.mem_union_left _ hmem)
      have hg2 : v2 ∉ Rel.boundVars R' :=
        fun hmem => hf2 (Finset.mem_union_left _ hmem)
      have ht1 : v1 ∉ Term.boundVars t :=
        fun hmem => hf1 (Finset.mem_union_right _ hmem)
      have ht2 : v2 ∉ Term.boundVars t :=
        fun hmem => hf2 (Finset.mem_union_right _ hmem)
      have ih_R := Rel.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂ _
        hz hv1 hv2 hv1v2 W₁def W₂def R' hg1 hg2
      have ih_t := Term.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂ _
        hz hv1 hv2 hv1v2 W₁def W₂def t ht1 ht2
      unfold Rel.unpair
      simp only [Rel.diaCount, ih_R, ih_t]

/-! ### Pair-Elim Distribution (η-Normalisation) -/

-- `Rel.pairElim` distributes a `pair_elim` over the structure of a Rel:
-- given a Rel at the components context `W₁ = V + {v₁, v₂}`, produce the
-- corresponding Rel at the pair context `W₂ = V + {z : v₁.2 × v₂.2}`.
--
-- Unlike `Term.pairElim`, this has NO stuck case: `Rel` has no modal binders
-- (no `.boxterm` / `.diaterm`) and no `.pair_elim` constructor of its own,
-- so the distribution always reaches the `Term σ V .Var` leaves inside
-- `.eval`, where `Term.pairElim` takes over.  (If a modal binder needs to
-- hold the pair_elim out, that's handled at the WFF layer.)
def Rel.pairElim {σ : Signature} {V W₁ W₂ : VarCtx} {n : ℕ}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂) :
    Rel σ W₁ n → Rel σ W₂ n
  | .R h        => .R h
  | .eval R' t  =>
      Rel.eval
        (Rel.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq R')
        (Term.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t)

-- `Rel.pairElim` preserves `diaCount`: it only redistributes through `.eval`
-- and delegates the term component to `Term.pairElim` (preservation lemma
-- `Term.diaCount_pairElim`).  Mirrors `Func.diaCount_pairElim`'s structure.
theorem Rel.diaCount_pairElim {σ : Signature} {V : VarCtx} {n : ℕ}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (R : Rel σ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂) n) :
    Rel.diaCount (Rel.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz rfl rfl R)
      = Rel.diaCount R := by
  match R with
  | .R _ => rfl
  | .eval R' t =>
      have ih_R := Rel.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz R'
      have ih_t := Term.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz t
      simp only [Rel.pairElim, Rel.diaCount, ih_R, ih_t]

-- Generalized version: allow arbitrary W₁/W₂.  Mirrors
-- `Term.diaCount_pairElim_gen` / `Func.diaCount_pairElim_gen`.
theorem Rel.diaCount_pairElim_gen {σ : Signature} {V W₁ W₂ : VarCtx} {n : ℕ}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (R : Rel σ W₁ n) :
    Rel.diaCount (Rel.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq R)
      = Rel.diaCount R := by
  subst w₁eq
  subst w₂eq
  exact Rel.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz R


/-! ### Well Formed Formulas -/

inductive WFF (σ : Signature) : VarCtx → Type where
  | atom : Rel σ V 0 → WFF σ V
  | top  : WFF σ V
  | bot  : WFF σ V
  | and  : WFF σ V → WFF σ V → WFF σ V
  | or   : WFF σ V → WFF σ V → WFF σ V
  | imp  : WFF σ V → WFF σ V → WFF σ V
  | all  : (x : VarSymb × VarType) → {hx : x.1 ∉ VarCtx_to_VarSymbs V}
      → WFF σ (VarCtx_insert x V hx) → WFF σ V
  | ex   : (x : VarSymb × VarType) → {hx : x.1 ∉ VarCtx_to_VarSymbs V}
      → WFF σ (VarCtx_insert x V hx) → WFF σ V
  | eq   : Term σ V S → Term σ V S → WFF σ V
  | box : WFF σ V → (hsub : (VarCtx_box V).1 ⊆ W.1) →
          (h_no_box_extras :
            ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1) →
          WFF σ W
  | dia : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V) →
          WFF σ (VarCtx_insert x V hx) →
          (hsub : (VarCtx_dia x V hx).1 ⊆ W.1) →
          (h_no_box_extras :
            ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1) →
          WFF σ W
  | pair_elim : (v₁ v₂ : VarSymb × VarType) → (z : VarSymb) →
                  (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) → (hv₂: v₂.1 ∉ VarCtx_to_VarSymbs V) →
                  (hv₁v₂ : v₁.1 ≠ v₂.1) → (hz : z ∉ VarCtx_to_VarSymbs V) →
                  VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁ →
                  VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂ →
                  WFF σ W₁ →
                  WFF σ W₂
  deriving DecidableEq

abbrev neg (φ : WFF σ V) : WFF σ V := φ.imp .bot

def WFF.box_Finset (hsub : (VarCtx_box V).1 ⊆ W.1)
          (h_no_box_extras :
            ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
  : (Finset (WFF σ V)) → (Finset (WFF σ W))
  := fun Γ => Finset.image (fun ψ => (WFF.box ψ hsub h_no_box_extras)) Γ

def WFF.dia_Finset (x : VarSymb × VarType)
          (hx : x.1 ∉ VarCtx_to_VarSymbs V)
          (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
          (h_no_box_extras :
            ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
  : (Finset (WFF σ (VarCtx_insert x V hx))) → (Finset (WFF σ W))
  := fun Γ => Finset.image (fun ψ => (WFF.dia x hx ψ hsub h_no_box_extras)) Γ

/-- The **witnessed box** `□_x φ := ¬◇_x¬φ` — "at every realization of the possible object `x`,
    `φ`."  Dual of `WFF.dia` (`◇_x`).  Used as the `x`-dependent side-hypothesis family of the
    general modal-`K` rule `K_dia` (which introduces plain `□` on `x`-free hypotheses *and* `□_x`
    on `x`-dependent ones simultaneously). -/
def WFF.box_x (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V)
          (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
          (h_no_box_extras :
            ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
          (φ : WFF σ (VarCtx_insert x V hx)) : WFF σ W
  := neg (WFF.dia x hx (neg φ) hsub h_no_box_extras)

/-- `□_x` applied pointwise to a finite hypothesis set (mirrors `WFF.dia_Finset`). -/
def WFF.box_x_Finset (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V)
          (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
          (h_no_box_extras :
            ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
  : (Finset (WFF σ (VarCtx_insert x V hx))) → (Finset (WFF σ W))
  := fun Γ => Finset.image (fun ψ => (WFF.box_x x hx hsub h_no_box_extras ψ)) Γ

/-! ### Pair-Elim Distribution (η-Normalisation) -/

-- `WFF.pairElim` distributes a `pair_elim` over the structure of a WFF.
-- Mirrors `Term.pairElim` and `Rel.pairElim`: structural connectives
-- (`atom`, `top`, `bot`, `and`, `or`, `imp`, `eq`) push the destructure
-- inside, handing off to `Rel.pairElim` for atoms and `Term.pairElim` for
-- equalities.  Modal binders (`box`, `dia`), quantifier binders (`all`,
-- `ex`), and nested `pair_elim` are "stuck": they wrap with the outer
-- `WFF.pair_elim` constructor (because moving the destructure past a
-- binder would require collision-handling/α-renaming that the WFF.rename
-- machinery has not been built yet).
def WFF.pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂) :
    WFF σ W₁ → WFF σ W₂
  | .atom R   =>
      .atom (Rel.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq R)
  | .top      => .top
  | .bot      => .bot
  | .and φ ψ  =>
      .and (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ)
           (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ)
  | .or  φ ψ  =>
      .or  (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ)
           (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ)
  | .imp φ ψ  =>
      .imp (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ)
           (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ)
  | .eq s t   =>
      .eq (Term.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq s)
          (Term.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t)
  | .all x φ  =>
      -- Stuck: quantifier binder.  Wrap with WFF.pair_elim constructor.
      .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq (.all x φ)
  | .ex  x φ  =>
      .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq (.ex  x φ)
  | @WFF.box _ V_inner _ φ hsub h_no_box_extras =>
      -- Stuck: modal binder.
      .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq
        (@WFF.box σ V_inner W₁ φ hsub h_no_box_extras)
  | @WFF.dia _ V_inner _ x hx φ hsub h_no_box_extras =>
      .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq
        (@WFF.dia σ V_inner W₁ x hx φ hsub h_no_box_extras)
  | .pair_elim v₁' v₂' z' hv₁' hv₂' hv₁v₂' hz' w₁eq' w₂eq' body =>
      -- Stuck: nested pair_elim.
      .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq
        (.pair_elim v₁' v₂' z' hv₁' hv₂' hv₁v₂' hz' w₁eq' w₂eq' body)

def WFF.pairElim_Finset {σ : Signature} {V W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂) :
    Finset (WFF σ W₁) → Finset (WFF σ W₂) :=
  fun Γ => Finset.image (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq) Γ

/-! ### Bound Variables -/

-- Collect bound variable symbols inside a WFF.  Used to require that `new`
-- doesn't clash with any binder when renaming.
def WFF.boundVars {σ : Signature} : {V : VarCtx} → WFF σ V → Finset VarSymb
  | _, .atom R                            => Rel.boundVars R
  | _, .top                               => ∅
  | _, .bot                               => ∅
  | _, .and φ ψ                           => WFF.boundVars φ ∪ WFF.boundVars ψ
  | _, .or  φ ψ                           => WFF.boundVars φ ∪ WFF.boundVars ψ
  | _, .imp φ ψ                           => WFF.boundVars φ ∪ WFF.boundVars ψ
  | _, .all x φ                           => insert x.1 (WFF.boundVars φ)
  | _, .ex  x φ                           => insert x.1 (WFF.boundVars φ)
  | _, .eq  s t                           => Term.boundVars s ∪ Term.boundVars t
  | _, .box φ _ _                         => WFF.boundVars φ
  | _, .dia x _ φ _ _                     => insert x.1 (WFF.boundVars φ)
  | _, .pair_elim v₁ v₂ z _ _ _ _ _ _ body =>
      insert v₁.1 (insert v₂.1 (insert z (WFF.boundVars body)))

/-! ### Node Count -/

-- Count constructor nodes inside a WFF.  Used as part of the `ctx_rest` termination
-- measure (rename-invariant; see `WFF.numNodes_rename`).
def WFF.numNodes {σ : Signature} : {V : VarCtx} → WFF σ V → Nat
  | _, .atom R                            => 1 + Rel.numNodes R
  | _, .top                               => 1
  | _, .bot                               => 1
  | _, .and φ ψ                           => 1 + WFF.numNodes φ + WFF.numNodes ψ
  | _, .or  φ ψ                           => 1 + WFF.numNodes φ + WFF.numNodes ψ
  | _, .imp φ ψ                           => 1 + WFF.numNodes φ + WFF.numNodes ψ
  | _, .all _ φ                           => 1 + WFF.numNodes φ
  | _, .ex  _ φ                           => 1 + WFF.numNodes φ
  | _, .eq  s t                           => 1 + Term.numNodes s + Term.numNodes t
  | _, .box φ _ _                         => 1 + WFF.numNodes φ
  | _, .dia _ _ φ _ _                     => 1 + WFF.numNodes φ
  | _, .pair_elim _ _ _ _ _ _ _ _ _ body  => 1 + WFF.numNodes body

-- Sum of pair-depths of all quantifier/modal binders inside a WFF.
-- Key invariant: when going into a binder (e.g., `.all x_a ψ` → ψ at
-- extended V), `V_ext.pairDepth + binderPairDepth φ` is unchanged
-- (the binder's pair-depth moves from φ's measure into V_ext's measure).
-- Used as part of `WFF.ctx_rest`'s termination measure to handle the
-- `.all`/`.ex` recursive descent.
def WFF.binderPairDepth {σ : Signature} : {V : VarCtx} → WFF σ V → Nat
  | _, .atom _                            => 0
  | _, .top                               => 0
  | _, .bot                               => 0
  | _, .and φ ψ                           =>
      WFF.binderPairDepth φ + WFF.binderPairDepth ψ
  | _, .or  φ ψ                           =>
      WFF.binderPairDepth φ + WFF.binderPairDepth ψ
  | _, .imp φ ψ                           =>
      WFF.binderPairDepth φ + WFF.binderPairDepth ψ
  | _, .all x φ                           =>
      x.2.pairDepth + WFF.binderPairDepth φ
  | _, .ex  x φ                           =>
      x.2.pairDepth + WFF.binderPairDepth φ
  | _, .eq  _ _                           => 0
  | _, .box φ _ _                         => WFF.binderPairDepth φ
  -- `.dia` does NOT add x.2.pairDepth: dia is not a true binder — the named
  -- variable is the outer-context one promoted to a diamond context (going
  -- inside, it is replaced by itself with one diamond removed), so no new
  -- pair structure enters scope.  Quantifiers differ: they introduce a
  -- genuinely new variable whose type may contain products.  (Design
  -- decision 2026-07-05; also makes modal beta bpd-preserving.)
  | _, .dia _ _ φ _ _                     => WFF.binderPairDepth φ
  | _, .pair_elim _ _ _ _ _ _ _ _ _ body  => WFF.binderPairDepth body

-- Count `.dia` constructors inside a WFF (and via Term/Rel components, every
-- `.diaterm` in the term layer).  Mirrors `Term.diaCount`'s structure.  Used
-- as part of `WFF.ctx_rest_dia_arm`'s Case 3 (modal beta) termination measure
-- — the recursive MU call's WFF `ψ_for_sub` is a `ctx_ext`-extended version of
-- `ψ` (which preserves diaCount), while the outer `.dia` constructor
-- contributes 1, giving strict decrease.
def WFF.diaCount {σ : Signature} : {V : VarCtx} → WFF σ V → Nat
  | _, .atom R                            => Rel.diaCount R
  | _, .top                               => 0
  | _, .bot                               => 0
  | _, .and φ ψ                           => WFF.diaCount φ + WFF.diaCount ψ
  | _, .or  φ ψ                           => WFF.diaCount φ + WFF.diaCount ψ
  | _, .imp φ ψ                           => WFF.diaCount φ + WFF.diaCount ψ
  | _, .all _ φ                           => WFF.diaCount φ
  | _, .ex  _ φ                           => WFF.diaCount φ
  | _, .eq  s t                           => Term.diaCount s + Term.diaCount t
  | _, .box φ _ _                         => WFF.diaCount φ
  | _, .dia _ _ φ _ _                     => 1 + WFF.diaCount φ
  | _, .pair_elim _ _ _ _ _ _ _ _ _ body  => WFF.diaCount body

-- `WFF.boundVars`, `WFF.numNodes`, `WFF.binderPairDepth`, `WFF.diaCount` are
-- all invariant under VarCtx-equality casts.
lemma WFF.boundVars_ctx_cast {σ : Signature} {V V' : VarCtx}
    (h : V = V') (φ : WFF σ V) :
    WFF.boundVars (h ▸ φ) = WFF.boundVars φ := by
  cases h; rfl

lemma WFF.numNodes_ctx_cast {σ : Signature} {V V' : VarCtx}
    (h : V = V') (φ : WFF σ V) :
    WFF.numNodes (h ▸ φ) = WFF.numNodes φ := by
  cases h; rfl

lemma WFF.binderPairDepth_ctx_cast {σ : Signature} {V V' : VarCtx}
    (h : V = V') (φ : WFF σ V) :
    WFF.binderPairDepth (h ▸ φ) = WFF.binderPairDepth φ := by
  cases h; rfl

lemma WFF.diaCount_ctx_cast {σ : Signature} {V V' : VarCtx}
    (h : V = V') (φ : WFF σ V) :
    WFF.diaCount (h ▸ φ) = WFF.diaCount φ := by
  cases h; rfl

-- Variant of `Prod.Lex.right` that takes a PROPOSITIONAL equality instead
-- of requiring the first component of both pairs to be syntactically equal.
-- Useful in `decreasing_by` proofs where caller and callee first components
-- are equal numerically (via `omega`/`ring`) but not syntactically.
theorem Prod.Lex.rightEq {α β} {r : α → α → Prop} {s : β → β → Prop}
    {a1 a2 : α} {b1 b2 : β} (h_eq : a1 = a2) (h_s : s b1 b2) :
    Prod.Lex r s (a1, b1) (a2, b2) := by
  rw [h_eq]
  exact Prod.Lex.right a2 h_s

-- Convert a `Prod.Lex` proof obligation to a disjunctive Nat form that
-- `omega` can prove directly (avoiding per-call-site `by_cases`).
theorem Prod.Lex.of_lt_or_eq_lt {a1 a2 b1 b2 : Nat}
    (h : a1 < a2 ∨ (a1 = a2 ∧ b1 < b2)) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with hlt | ⟨heq, hb⟩
  · exact Prod.Lex.left _ _ hlt
  · exact Prod.Lex.rightEq heq hb

-- 3-tuple lex disjunction form.
theorem Prod.Lex.of_lt_or_eq_lt_or_eq_lt {a1 a2 b1 b2 c1 c2 : Nat}
    (h : a1 < a2 ∨ (a1 = a2 ∧ (b1 < b2 ∨ (b1 = b2 ∧ c1 < c2)))) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a1, b1, c1) (a2, b2, c2) := by
  rcases h with hlt | ⟨heq, hrest⟩
  · exact Prod.Lex.left _ _ hlt
  · exact Prod.Lex.rightEq heq (Prod.Lex.of_lt_or_eq_lt hrest)

-- 4-tuple lex disjunction form.  Used for the refactored WFF substitution
-- measures where we split `bpd + dC` (previously in comp 1) into separate
-- slots so that MU-substitution's dC growth doesn't block termination.
theorem Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt
    {a1 a2 b1 b2 c1 c2 d1 d2 : Nat}
    (h : a1 < a2 ∨ (a1 = a2 ∧ (b1 < b2 ∨ (b1 = b2 ∧
           (c1 < c2 ∨ (c1 = c2 ∧ d1 < d2)))))) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))
      (a1, b1, c1, d1) (a2, b2, c2, d2) := by
  rcases h with hlt | ⟨heq, hrest⟩
  · exact Prod.Lex.left _ _ hlt
  · exact Prod.Lex.rightEq heq (Prod.Lex.of_lt_or_eq_lt_or_eq_lt hrest)

-- `WFF.pairElim` preserves `diaCount`.  Structural arms push diaCount through
-- (atom: via Rel.diaCount_pairElim; and/or/imp: structural sum; eq: via
-- Term.diaCount_pairElim).  "Stuck" arms (all/ex/box/dia/nested pair_elim)
-- wrap with the `.pair_elim` constructor, and `diaCount (.pair_elim _ _ _ _
-- _ _ _ _ _ body) = diaCount body` matches the input's diaCount.  Mirrors
-- `Term.diaCount_pairElim`'s structure.
theorem WFF.diaCount_pairElim {σ : Signature} {V : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂)) :
    WFF.diaCount (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz rfl rfl φ)
      = WFF.diaCount φ := by
  match φ with
  | .atom R =>
      have ih := Rel.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz R
      simp only [WFF.pairElim, WFF.diaCount, ih]
  | .top => rfl
  | .bot => rfl
  | .and φ' ψ' =>
      have ih_1 := WFF.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz φ'
      have ih_2 := WFF.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz ψ'
      simp only [WFF.pairElim, WFF.diaCount, ih_1, ih_2]
  | .or φ' ψ' =>
      have ih_1 := WFF.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz φ'
      have ih_2 := WFF.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz ψ'
      simp only [WFF.pairElim, WFF.diaCount, ih_1, ih_2]
  | .imp φ' ψ' =>
      have ih_1 := WFF.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz φ'
      have ih_2 := WFF.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz ψ'
      simp only [WFF.pairElim, WFF.diaCount, ih_1, ih_2]
  | .eq s t =>
      have ih_s := Term.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz s
      have ih_t := Term.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz t
      simp only [WFF.pairElim, WFF.diaCount, ih_s, ih_t]
  | .all _ _ => rfl
  | .ex  _ _ => rfl
  | .box _ _ _ => rfl
  | .dia _ _ _ _ _ => rfl
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => rfl
termination_by WFF.numNodes φ
decreasing_by all_goals (simp [WFF.numNodes]; try omega)

-- Generalized version: allow arbitrary W₁/W₂.  Mirrors
-- `Term.diaCount_pairElim_gen` / `Func.diaCount_pairElim_gen`.
theorem WFF.diaCount_pairElim_gen {σ : Signature} {V W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (φ : WFF σ W₁) :
    WFF.diaCount (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ)
      = WFF.diaCount φ := by
  subst w₁eq
  subst w₂eq
  exact WFF.diaCount_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz φ

-- `WFF.pairElim` preserves `binderPairDepth`.  Mirrors
-- `WFF.diaCount_pairElim`'s structure.  Atomic / structural arms (atom: 0;
-- and/or/imp: sum) push through; stuck arms (.all/.ex/.box/.dia/nested
-- .pair_elim) wrap with `.pair_elim`, which has
-- `binderPairDepth (.pair_elim ... body) = binderPairDepth body`,
-- matching the input's binderPairDepth.
theorem WFF.binderPairDepth_pairElim {σ : Signature} {V : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂)) :
    WFF.binderPairDepth (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz rfl rfl φ)
      = WFF.binderPairDepth φ := by
  match φ with
  | .atom _ => simp only [WFF.pairElim, WFF.binderPairDepth]
  | .top => rfl
  | .bot => rfl
  | .and φ' ψ' =>
      have ih_1 := WFF.binderPairDepth_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz φ'
      have ih_2 := WFF.binderPairDepth_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz ψ'
      simp only [WFF.pairElim, WFF.binderPairDepth, ih_1, ih_2]
  | .or φ' ψ' =>
      have ih_1 := WFF.binderPairDepth_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz φ'
      have ih_2 := WFF.binderPairDepth_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz ψ'
      simp only [WFF.pairElim, WFF.binderPairDepth, ih_1, ih_2]
  | .imp φ' ψ' =>
      have ih_1 := WFF.binderPairDepth_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz φ'
      have ih_2 := WFF.binderPairDepth_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz ψ'
      simp only [WFF.pairElim, WFF.binderPairDepth, ih_1, ih_2]
  | .eq _ _ => simp only [WFF.pairElim, WFF.binderPairDepth]
  | .all _ _ => rfl
  | .ex  _ _ => rfl
  | .box _ _ _ => rfl
  | .dia _ _ _ _ _ => rfl
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => rfl
termination_by WFF.numNodes φ
decreasing_by all_goals (simp [WFF.numNodes]; try omega)

-- Generalized version, mirrors `WFF.diaCount_pairElim_gen`.
theorem WFF.binderPairDepth_pairElim_gen {σ : Signature} {V W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (φ : WFF σ W₁) :
    WFF.binderPairDepth (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ)
      = WFF.binderPairDepth φ := by
  subst w₁eq
  subst w₂eq
  exact WFF.binderPairDepth_pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz φ

/-! ### Variable Renaming -/

-- Rename `old → new` inside a WFF.  Mirrors `Term.rename` / `Rel.rename`;
-- structural recursion with delegation to `Rel.rename` for atomic relations
-- and `Term.rename` for equality terms.  The binder cases (`all`, `ex`,
-- `box`, `dia`, `pair_elim`) need careful context manipulation:
--   * `all`/`ex`: their bound variable `x.1` is automatically ≠ `old` (since
--     `hx : x.1 ∉ symbols(W)` and `old ∈ symbols(W)` via Wdef), so we just
--     recurse on the body with binder and `old` insertion commuted.
--   * `box`: `W = VarCtx_box V_inner` forces `repl_type = T.VTypeBox` for
--     some T; recurse on body with `⟨old, T⟩ → ⟨new, T⟩`.  Other repl_type
--     cases are unreachable (exfalso via Wdef).
--   * `dia`: Case A (binder x is what's being renamed: x.1 = old and
--     repl_type = x.2.VTypeDia) rebinds x to ⟨new, x.2⟩; Case B (otherwise)
--     handles like `box`.
--   * `pair_elim`: mirrors `Term.rename`'s pair_elim arm — Case A rebinds z
--     to new, Case B recurses with rename inside body.
-- Requires `new ∉ WFF.boundVars φ` to avoid capture.
def WFF.rename {σ : Signature} (old new : VarSymb) (repl_type : VarType)
    (V W : VarCtx)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (φ : WFF σ W) (new_not_bound : new ∉ WFF.boundVars φ)
    : WFF σ (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) := by
  match φ, new_not_bound with
  | .atom R, h_nb =>
      exact .atom
        (Rel.rename old new repl_type V W 0 old_fresh new_fresh Wdef R h_nb)
  | .top, _ => exact .top
  | .bot, _ => exact .bot
  | .and ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      exact .and
        (WFF.rename old new repl_type V W old_fresh new_fresh Wdef ψ₁ h_nb_1)
        (WFF.rename old new repl_type V W old_fresh new_fresh Wdef ψ₂ h_nb_2)
  | .or  ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      exact .or
        (WFF.rename old new repl_type V W old_fresh new_fresh Wdef ψ₁ h_nb_1)
        (WFF.rename old new repl_type V W old_fresh new_fresh Wdef ψ₂ h_nb_2)
  | .imp ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      exact .imp
        (WFF.rename old new repl_type V W old_fresh new_fresh Wdef ψ₁ h_nb_1)
        (WFF.rename old new repl_type V W old_fresh new_fresh Wdef ψ₂ h_nb_2)
  | .eq s t, h_nb =>
      have h_nb_s : new ∉ Term.boundVars s :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      exact .eq
        (Term.rename old new repl_type V W _ old_fresh new_fresh Wdef s h_nb_s)
        (Term.rename old new repl_type V W _ old_fresh new_fresh Wdef t h_nb_t)
  | @WFF.all _ _ x hx ψ, h_nb =>
      -- hx : x.1 ∉ symbols(W).  Via Wdef, symbols(W) = insert old (symbols V).
      -- So x.1 ≠ old AND x.1 ∉ symbols(V).
      have hx_W : x.1 ∉ VarCtx_to_VarSymbs W := hx
      have h_W_symbols : VarCtx_to_VarSymbs W =
          insert old (VarCtx_to_VarSymbs V) := by
        rw [Wdef]; exact VarCtx_to_VarSymbs_insert _ _ _
      have hx_ne_old : x.1 ≠ old := fun h_eq =>
        hx_W (h_W_symbols ▸ Finset.mem_insert.mpr (Or.inl h_eq))
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := fun h_in =>
        hx_W (h_W_symbols ▸ Finset.mem_insert_of_mem h_in)
      have hx_ne_new : x.1 ≠ new := fun h_eq =>
        h_nb (Finset.mem_insert.mpr (Or.inl h_eq.symm))
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      -- Build the freshness proofs and Wdef for the recursive call.
      have hold_V_x : old ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_old h.symm) old_fresh
      have hnew_V_x : new ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_new h.symm) new_fresh
      have Wdef_inner :
          VarCtx_insert x W hx = VarCtx_insert ⟨old, repl_type⟩
            (VarCtx_insert x V hx_V) hold_V_x := by
        apply VarCtx_ext
        change insert x W.1 = insert ⟨old, repl_type⟩ (insert x V.1)
        rw [Wdef]
        change insert x (insert ⟨old, repl_type⟩ V.1) = _
        exact Finset.insert_comm _ _ _
      let ψ_renamed := WFF.rename old new repl_type
          (VarCtx_insert x V hx_V) (VarCtx_insert x W hx)
          hold_V_x hnew_V_x Wdef_inner ψ h_nb_ψ
      -- ψ_renamed : WFF σ (VarCtx_insert ⟨new, repl_type⟩ (VarCtx_insert x V hx_V) hnew_V_x)
      -- We want WFF σ (VarCtx_insert x (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) hx_V_new)
      have hx_V_new : x.1 ∉ VarCtx_to_VarSymbs
          (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) :=
        not_mem_VarSymbs_insert hx_ne_new hx_V
      have h_swap :
          VarCtx_insert ⟨new, repl_type⟩
            (VarCtx_insert x V hx_V) hnew_V_x =
          VarCtx_insert x
            (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) hx_V_new := by
        apply VarCtx_ext
        change insert ⟨new, repl_type⟩ (insert x V.1)
             = insert x (insert ⟨new, repl_type⟩ V.1)
        exact Finset.insert_comm _ _ _
      exact .all x (hx := hx_V_new) (h_swap ▸ ψ_renamed)
  | @WFF.ex _ _ x hx ψ, h_nb =>
      -- Symmetric to .all
      have hx_W : x.1 ∉ VarCtx_to_VarSymbs W := hx
      have h_W_symbols : VarCtx_to_VarSymbs W =
          insert old (VarCtx_to_VarSymbs V) := by
        rw [Wdef]; exact VarCtx_to_VarSymbs_insert _ _ _
      have hx_ne_old : x.1 ≠ old := fun h_eq =>
        hx_W (h_W_symbols ▸ Finset.mem_insert.mpr (Or.inl h_eq))
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := fun h_in =>
        hx_W (h_W_symbols ▸ Finset.mem_insert_of_mem h_in)
      have hx_ne_new : x.1 ≠ new := fun h_eq =>
        h_nb (Finset.mem_insert.mpr (Or.inl h_eq.symm))
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      have hold_V_x : old ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_old h.symm) old_fresh
      have hnew_V_x : new ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_new h.symm) new_fresh
      have Wdef_inner :
          VarCtx_insert x W hx = VarCtx_insert ⟨old, repl_type⟩
            (VarCtx_insert x V hx_V) hold_V_x := by
        apply VarCtx_ext
        change insert x W.1 = insert ⟨old, repl_type⟩ (insert x V.1)
        rw [Wdef]
        change insert x (insert ⟨old, repl_type⟩ V.1) = _
        exact Finset.insert_comm _ _ _
      let ψ_renamed := WFF.rename old new repl_type
          (VarCtx_insert x V hx_V) (VarCtx_insert x W hx)
          hold_V_x hnew_V_x Wdef_inner ψ h_nb_ψ
      have hx_V_new : x.1 ∉ VarCtx_to_VarSymbs
          (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) :=
        not_mem_VarSymbs_insert hx_ne_new hx_V
      have h_swap :
          VarCtx_insert ⟨new, repl_type⟩
            (VarCtx_insert x V hx_V) hnew_V_x =
          VarCtx_insert x
            (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) hx_V_new := by
        apply VarCtx_ext
        change insert ⟨new, repl_type⟩ (insert x V.1)
             = insert x (insert ⟨new, repl_type⟩ V.1)
        exact Finset.insert_comm _ _ _
      exact .ex x (hx := hx_V_new) (h_swap ▸ ψ_renamed)
  | .box ψ box_context_sub h_box_no_extras, h_nb =>
      rename_i V_inner
      rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩
      · -- Var
        refine .box ψ ?_ (by
          intro p hp h_box
          rcases Finset.mem_insert.mp hp with h_eq | hp_V
          · subst h_eq; simp [VarType.isBox] at h_box
          · exact h_box_no_extras p (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V)
              h_box)
        have hsub_V : (VarCtx_box V_inner).1 ⊆ V.1 := by
          intro x x_in_box_inner
          rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub x_in_box_inner) with xold | xV
          · rcases xold ▸ Finset.mem_image.mp x_in_box_inner with ⟨w, weq⟩
            have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
            simp only [reduceCtorEq, and_false] at this
          · exact xV
        exact (Finset.subset_insert_iff_of_notMem fun a ↦
          new_fresh (Finset.mem_image.mpr ⟨_, hsub_V a, rfl⟩)).mpr hsub_V
      · -- VTypeBox: recurse into ψ if old is bound in V_inner, else impossible.
        if h : ⟨old, innertype⟩ ∈ V_inner.1 then
          let V_inner' := VarCtx_erase V_inner ⟨old, innertype⟩
          have oldinner_fresh : old ∉ VarCtx_to_VarSymbs V_inner' := VarCtx_erase_fresh h
          have V_inner_eq : V_inner =
              VarCtx_insert ⟨old, innertype⟩ V_inner' oldinner_fresh :=
            (VarCtx_insert_erase h oldinner_fresh).symm
          have hbox_sub : (VarCtx_box V_inner').1 ⊆ V.1 := by
            intro y hy
            have hy_inner : y ∈ (VarCtx_box V_inner).1 := by
              rcases Finset.mem_image.mp hy with ⟨w, hvin, hveq⟩
              exact Finset.mem_image.mpr ⟨w, Finset.erase_subset _ _ hvin, hveq⟩
            rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub hy_inner) with rfl | hV
            · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, hvin, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, innertype⟩,
                hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin, rfl⟩)).elim
            · exact hV
          have newinner_fresh : new ∉ VarCtx_to_VarSymbs V_inner' := fun hmem => by
            rcases Finset.mem_image.mp hmem with ⟨w, hvin, hveq⟩
            exact new_fresh (Finset.mem_image.mpr ⟨⟨w.1, w.2.VTypeBox⟩,
              hbox_sub (Finset.mem_image.mpr ⟨w, hvin, rfl⟩), hveq⟩)
          let renamed_ψ := WFF.rename old new innertype V_inner' V_inner
                            oldinner_fresh newinner_fresh V_inner_eq ψ h_nb
          refine .box renamed_ψ ?_ (by
            intro p hp h_box
            rw [VarCtx_box_fst_insert]
            rcases Finset.mem_insert.mp hp with h_eq | hp_V
            · subst h_eq
              exact Finset.mem_insert_self _ _
            · have hp1_ne_old : p.1 ≠ old := fun h_eq =>
                old_fresh (Finset.mem_image.mpr ⟨p, hp_V, h_eq⟩)
              have hp_W : p ∈ W.1 := by
                rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
              have hp_box_inner : p ∈ (VarCtx_box V_inner).1 :=
                h_box_no_extras p hp_W h_box
              rcases Finset.mem_image.mp hp_box_inner with ⟨⟨v, S⟩, hvS_in, hvS_eq⟩
              have hp_eq_v : p.1 = v := (Prod.mk.inj hvS_eq).1.symm
              have hv_ne_old : v ≠ old := hp_eq_v ▸ hp1_ne_old
              apply Finset.mem_insert_of_mem
              refine Finset.mem_image.mpr ⟨⟨v, S⟩, ?_, hvS_eq⟩
              change ⟨v, S⟩ ∈ (V_inner.1.erase _)
              exact Finset.mem_erase.mpr ⟨fun h_eq => hv_ne_old (Prod.mk.inj h_eq).1, hvS_in⟩)
          rw [VarCtx_box_fst_insert]
          exact Finset.insert_subset_insert _ hbox_sub
        else
          -- Impossible: W contains ⟨old, innertype.VTypeBox⟩, h_box_no_extras
          -- forces it into VarCtx_box V_inner, hence ⟨old, innertype⟩ ∈ V_inner.
          refine .box ψ ?_ (by
            exfalso
            have h_old_in_W : (⟨old, innertype.VTypeBox⟩ : VarSymb × VarType) ∈ W.1 := by
              rw [Wdef]; exact Finset.mem_insert_self _ _
            have h_in_box : (⟨old, innertype.VTypeBox⟩ : VarSymb × VarType)
                              ∈ (VarCtx_box V_inner).1 :=
              h_box_no_extras _ h_old_in_W rfl
            rcases Finset.mem_image.mp h_in_box with ⟨⟨v, S⟩, hvin, hveq⟩
            simp only [Prod.mk.injEq] at hveq
            exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin))
          have hbox_old_not : ⟨old, innertype.VTypeBox⟩ ∉ (VarCtx_box V_inner).1 := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
            simp only [Prod.mk.injEq] at hveq
            exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin)
          have hsub : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro y hy
            rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub hy) with rfl | hV
            · exact absurd hy hbox_old_not
            · exact hV
          exact Finset.Subset.trans hsub (Finset.subset_insert _ _)
      -- remaining cases: VTypeDia, VTypeOne, VTypeProd. Same shape as Var.
      all_goals refine .box ψ ?_ (by
        intro p hp h_box
        rcases Finset.mem_insert.mp hp with h_eq | hp_V
        · subst h_eq
          first
          | (simp [VarType.isBox] at h_box) <;> done
          | (exfalso
             rename_i V1' V2'
             have h_old_W : (⟨old, V1'.VTypeProd V2'⟩ : VarSymb × VarType) ∈ W.1 := by
               rw [Wdef]; exact Finset.mem_insert_self _ _
             have h_old_in_box := h_box_no_extras _ h_old_W h_box
             rcases Finset.mem_image.mp h_old_in_box with ⟨⟨_, _⟩, _, hveq⟩
             simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq)
        · exact h_box_no_extras p
            (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V) h_box)
      all_goals have : (VarCtx_box V_inner).1 ⊆ V.1 := by
        { intro x x_in_box_inner
          rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub x_in_box_inner) with xold | xV
          · rcases xold ▸ Finset.mem_image.mp x_in_box_inner with ⟨w, weq⟩
            have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
            simp only [reduceCtorEq, and_false] at this
          · exact xV
        }
      all_goals exact (Finset.subset_insert_iff_of_notMem fun a ↦
        new_fresh (Finset.mem_image.mpr ⟨_, this a, rfl⟩)).mpr this
  | .dia x hx ψ dia_ctx_sub h_dia_no_extras, h_nb =>
      rename_i V_inner
      match repl_type with
      | .Var | .VTypeOne | .VTypeProd _ _ =>
          -- repl_type is none of VTypeBox/VTypeDia, so ⟨old, repl_type⟩ can't
          -- appear in VarCtx_dia; everything else in VarCtx_dia lies in V.
          refine .dia x hx ψ ?_ (by
            intro p hp h_box
            rcases Finset.mem_insert.mp hp with h_eq | hp_V
            · subst h_eq
              first
              | (simp [VarType.isBox] at h_box) <;> done
              | (exfalso
                 rename_i V1' V2'
                 have h_old_W : (⟨old, V1'.VTypeProd V2'⟩ : VarSymb × VarType) ∈ W.1 := by
                   rw [Wdef]; exact Finset.mem_insert_self _ _
                 have h_old_in_dia := h_dia_no_extras _ h_old_W h_box
                 rcases Finset.mem_insert.mp h_old_in_dia with hxeq | hbox
                 · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
                 · rcases Finset.mem_image.mp hbox with ⟨⟨_, _⟩, _, hveq⟩
                   simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq)
            · exact h_dia_no_extras p
                (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V) h_box)
          intro y y_in_dia_inner
          rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub y_in_dia_inner) with yold | yV
          · subst yold
            rcases Finset.mem_insert.mp y_in_dia_inner with heq | hmem
            · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
            · rcases Finset.mem_image.mp hmem with ⟨w, weq⟩
              have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
              simp only [reduceCtorEq, and_false] at this
          · exact Finset.mem_insert_of_mem yV
      | .VTypeBox repl_inner_type =>
          -- VTypeBox: recurse into ψ if old is bound in V_inner, else impossible.
          if h : ⟨old, repl_inner_type⟩ ∈ V_inner.1 then
            let V_inner' := VarCtx_erase V_inner ⟨old, repl_inner_type⟩
            have oldinner_fresh : old ∉ VarCtx_to_VarSymbs V_inner' :=
              VarCtx_erase_fresh h
            have hx_ne_old : x.1 ≠ old := fun heq =>
              hx (Finset.mem_image.mpr ⟨⟨old, repl_inner_type⟩, h, heq.symm⟩)
            have hx' : x.1 ∉ VarCtx_to_VarSymbs V_inner' :=
              fun hmem => hx (VarCtx_to_VarSymbs_erase_subset hmem)
            have hbox_sub : (VarCtx_box V_inner').1 ⊆ V.1 := by
              intro y hy
              have hy_inner_box : y ∈ (VarCtx_box V_inner).1 := by
                rcases Finset.mem_image.mp hy with ⟨w, hvin, hveq⟩
                exact Finset.mem_image.mpr ⟨w, Finset.erase_subset _ _ hvin, hveq⟩
              have hy_dia : y ∈ (VarCtx_dia x V_inner hx).1 :=
                Finset.mem_insert_of_mem hy_inner_box
              rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy_dia) with rfl | hV
              · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, hvin, hveq⟩
                simp only [Prod.mk.injEq] at hveq
                exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, repl_inner_type⟩,
                  hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin, rfl⟩)).elim
              · exact hV
            have hx1_in_V : ⟨x.1, x.2.VTypeDia⟩ ∈ V.1 := by
              have hx_in_dia : ⟨x.1, x.2.VTypeDia⟩ ∈ (VarCtx_dia x V_inner hx).1 :=
                Finset.mem_insert_self _ _
              rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hx_in_dia) with heq | hV
              · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
              · exact hV
            have hnew_ne_x : new ≠ x.1 := fun heq =>
              new_fresh (Finset.mem_image.mpr
                ⟨⟨x.1, x.2.VTypeDia⟩, hx1_in_V, heq.symm⟩)
            have newinner_fresh : new ∉ VarCtx_to_VarSymbs V_inner' := fun hmem => by
              rcases Finset.mem_image.mp hmem with ⟨w, hvin, hveq⟩
              exact new_fresh (Finset.mem_image.mpr ⟨⟨w.1, w.2.VTypeBox⟩,
                hbox_sub (Finset.mem_image.mpr ⟨w, hvin, rfl⟩), hveq⟩)
            have oldinnerX_fresh :=
              not_mem_VarSymbs_insert (x := x) (hx := hx') hx_ne_old.symm oldinner_fresh
            have newinnerX_fresh :=
              not_mem_VarSymbs_insert (x := x) (hx := hx') hnew_ne_x newinner_fresh
            have hx_target :=
              not_mem_VarSymbs_insert (x := ⟨new, repl_inner_type⟩)
                (hx := newinner_fresh) hnew_ne_x.symm hx'
            have V_inner_eq : VarCtx_insert x V_inner hx =
                VarCtx_insert ⟨old, repl_inner_type⟩
                              (VarCtx_insert x V_inner' hx') oldinnerX_fresh :=
              VarCtx_ext _ _ <| by
                change insert x V_inner.1 =
                     insert ⟨old, repl_inner_type⟩ (insert x V_inner'.1)
                rw [← Finset.insert_erase h]; exact Finset.insert_comm _ _ _
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            let renamed_ψ := WFF.rename old new repl_inner_type
                               (VarCtx_insert x V_inner' hx')
                               (VarCtx_insert x V_inner hx)
                               oldinnerX_fresh newinnerX_fresh V_inner_eq ψ h_nb_inner
            have ctx_swap :
                VarCtx_insert ⟨new, repl_inner_type⟩
                              (VarCtx_insert x V_inner' hx') newinnerX_fresh =
                VarCtx_insert x
                  (VarCtx_insert ⟨new, repl_inner_type⟩ V_inner' newinner_fresh)
                  hx_target :=
              VarCtx_insert_comm _ _
            refine .dia x hx_target (ctx_swap ▸ renamed_ψ) ?_ (by
              intro p hp h_box
              rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
              rcases Finset.mem_insert.mp hp with h_eq | hp_V
              · subst h_eq
                exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              · have hp1_ne_old : p.1 ≠ old := fun h_eq =>
                  old_fresh (Finset.mem_image.mpr ⟨p, hp_V, h_eq⟩)
                have hp_W : p ∈ W.1 := by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
                have hp_dia_inner : p ∈ (VarCtx_dia x V_inner hx).1 :=
                  h_dia_no_extras p hp_W h_box
                rw [VarCtx_dia_fst] at hp_dia_inner
                rcases Finset.mem_insert.mp hp_dia_inner with hpx | hp_box_inner
                · subst hpx; simp [VarType.isBox] at h_box
                · rcases Finset.mem_image.mp hp_box_inner with ⟨⟨v, S⟩, hvS_in, hvS_eq⟩
                  have hp_eq_v : p.1 = v := (Prod.mk.inj hvS_eq).1.symm
                  have hv_ne_old : v ≠ old := hp_eq_v ▸ hp1_ne_old
                  apply Finset.mem_insert_of_mem
                  apply Finset.mem_insert_of_mem
                  refine Finset.mem_image.mpr ⟨⟨v, S⟩, ?_, hvS_eq⟩
                  change ⟨v, S⟩ ∈ V_inner.1.erase _
                  exact Finset.mem_erase.mpr
                    ⟨fun h_eq => hv_ne_old (Prod.mk.inj h_eq).1, hvS_in⟩)
            rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
            intro y hy
            rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact Finset.mem_insert_of_mem hx1_in_V
            rcases Finset.mem_insert.mp hy' with rfl | hy''
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (hbox_sub hy'')
          else
            -- Impossible under no-box-extras.
            refine .dia x hx ψ ?_ (by
              exfalso
              have h_old_in_W : (⟨old, repl_inner_type.VTypeBox⟩ : VarSymb × VarType) ∈ W.1 := by
                rw [Wdef]; exact Finset.mem_insert_self _ _
              have h_in_dia : (⟨old, repl_inner_type.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_dia x V_inner hx).1 :=
                h_dia_no_extras _ h_old_in_W rfl
              rcases Finset.mem_insert.mp h_in_dia with hxeq | hbox
              · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
              · rcases Finset.mem_image.mp hbox with ⟨⟨v, S⟩, hvin, hveq⟩
                simp only [Prod.mk.injEq] at hveq
                exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin))
            have hdia_old_not :
                ⟨old, repl_inner_type.VTypeBox⟩ ∉ (VarCtx_dia x V_inner hx).1 := by
              intro hmem
              rcases Finset.mem_insert.mp hmem with heq | hbox
              · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
              · rcases Finset.mem_image.mp hbox with ⟨⟨v, S⟩, hvin, hveq⟩
                simp only [Prod.mk.injEq] at hveq
                exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin)
            have hsub : (VarCtx_dia x V_inner hx).1 ⊆ V.1 := by
              intro y hy
              rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy) with rfl | hV
              · exact absurd hy hdia_old_not
              · exact hV
            exact Finset.Subset.trans hsub (Finset.subset_insert _ _)
      | .VTypeDia repl_inner_type =>
          -- VTypeDia: if x is the bound variable being renamed, rebind to
          -- ⟨new, repl_inner_type⟩ and rename inside ψ; otherwise pass through.
          if h_x : x = ⟨old, repl_inner_type⟩ then
            have hx_eq_old : x.1 = old := congrArg Prod.fst h_x
            have hx_old : old ∉ VarCtx_to_VarSymbs V_inner := hx_eq_old ▸ hx
            have hbox_sub : (VarCtx_box V_inner).1 ⊆ V.1 := by
              intro y hy
              have hy_dia : y ∈ (VarCtx_dia x V_inner hx).1 :=
                Finset.mem_insert_of_mem hy
              rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy_dia) with rfl | hV
              · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, _, hveq⟩
                simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
              · exact hV
            have hnew_fresh_inner : new ∉ VarCtx_to_VarSymbs V_inner := fun hmem => by
              rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
              exact new_fresh (Finset.mem_image.mpr ⟨⟨v, S.VTypeBox⟩,
                hbox_sub (Finset.mem_image.mpr ⟨⟨v, S⟩, hvin, rfl⟩), hveq⟩)
            have Wdef_inner : VarCtx_insert x V_inner hx =
                VarCtx_insert ⟨old, repl_inner_type⟩ V_inner hx_old :=
              VarCtx_ext _ _ (by
                change insert x V_inner.1 = insert ⟨old, repl_inner_type⟩ V_inner.1
                rw [h_x])
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            let renamed_ψ := WFF.rename old new repl_inner_type
                               V_inner
                               (VarCtx_insert x V_inner hx)
                               hx_old hnew_fresh_inner Wdef_inner ψ h_nb_inner
            refine .dia ⟨new, repl_inner_type⟩ hnew_fresh_inner renamed_ψ ?_ (by
              intro p hp h_box
              rw [VarCtx_dia_fst]
              rcases Finset.mem_insert.mp hp with h_eq | hp_V
              · subst h_eq; simp [VarType.isBox] at h_box
              · have hp_W : p ∈ W.1 := by
                  rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
                have hp_dia_inner : p ∈ (VarCtx_dia x V_inner hx).1 :=
                  h_dia_no_extras p hp_W h_box
                rw [VarCtx_dia_fst] at hp_dia_inner
                rcases Finset.mem_insert.mp hp_dia_inner with hpx | hp_box
                · subst hpx; simp [VarType.isBox] at h_box
                · exact Finset.mem_insert_of_mem hp_box)
            rw [VarCtx_dia_fst]
            exact Finset.insert_subset_insert _ hbox_sub
          else
            refine .dia x hx ψ ?_ (by
              intro p hp h_box
              rcases Finset.mem_insert.mp hp with h_eq | hp_V
              · subst h_eq; simp [VarType.isBox] at h_box
              · exact h_dia_no_extras p
                  (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V) h_box)
            intro y hy
            rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy) with rfl | hyV
            · exfalso
              rcases Finset.mem_insert.mp hy with hxeq | hbox
              · apply h_x
                simp only [Prod.mk.injEq] at hxeq
                exact Prod.ext hxeq.1.symm (VarType.VTypeDia.inj hxeq.2).symm
              · rcases Finset.mem_image.mp hbox with ⟨⟨v, S⟩, _, hveq⟩
                simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
            · exact Finset.mem_insert_of_mem hyV
  | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁_eq w₂_eq inner_wff, h_nb =>
      -- Mirrors `Term.rename`'s pair_elim arm.  Two cases:
      --   A: the pair_elim's z (with type .VTypeProd v₁.2 v₂.2) IS the binder
      --      `⟨old, repl_type⟩`.  Rebind z to new; inner_wff unchanged.
      --   B: ⟨old, repl_type⟩ lives in the constructor's inner context pe_V.
      --      Erase it from pe_V, rename inside inner_wff, rebuild with same z.
      rename_i pe_V pe_W₁
      have h_v₁_ne_new : v₁.1 ≠ new := fun heq =>
        h_nb (Finset.mem_insert.mpr (Or.inl heq.symm))
      have h_v₂_ne_new : v₂.1 ≠ new := fun heq =>
        h_nb (Finset.mem_insert.mpr (Or.inr
          (Finset.mem_insert.mpr (Or.inl heq.symm))))
      have h_z_ne_new : z ≠ new := fun heq =>
        h_nb (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
          (Finset.mem_insert.mpr (Or.inl heq.symm))))))
      have h_nb_inner : new ∉ WFF.boundVars inner_wff := fun hmem =>
        h_nb (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
          (Finset.mem_insert.mpr (Or.inr hmem))))))
      by_cases h_case :
          (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
      · -- Case A: z is what's being renamed.
        have h_z_eq : z = old := congrArg Prod.fst h_case
        have h_repl_eq : (VarType.VTypeProd v₁.2 v₂.2) = repl_type :=
          congrArg Prod.snd h_case
        -- Show pe_V = V by canceling the common insert via h_case.
        have h_pe_V_eq_V : pe_V = V := by
          apply VarCtx_ext
          have h_not_in_pe : (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                              ∉ pe_V.1 :=
            fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          have h_not_in_V_old : (⟨old, repl_type⟩ : VarSymb × VarType) ∉ V.1 :=
            fun h => old_fresh (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          have h_not_in_V : (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                             ∉ V.1 := h_case ▸ h_not_in_V_old
          have h_set : insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                            pe_V.1
                     = insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V.1 := by
            have orig : insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                            pe_V.1
                      = insert ⟨old, repl_type⟩ V.1 :=
              congrArg PSigma.fst (w₂_eq.trans Wdef)
            rw [← h_case] at orig
            exact orig
          change pe_V.1 = V.1
          rw [← Finset.erase_insert h_not_in_pe, h_set,
              Finset.erase_insert h_not_in_V]
        have hv₁_V : v₁.1 ∉ VarCtx_to_VarSymbs V := h_pe_V_eq_V ▸ hv₁
        have hv₂_V : v₂.1 ∉ VarCtx_to_VarSymbs V := h_pe_V_eq_V ▸ hv₂
        have w₁_eq_V : VarCtx_insert_twice v₁ v₂ V hv₁_V hv₂_V hv₁v₂ = pe_W₁ :=
          h_pe_V_eq_V ▸ w₁_eq
        have w₂_eq_V :
            VarCtx_insert ⟨new, .VTypeProd v₁.2 v₂.2⟩ V new_fresh =
            VarCtx_insert ⟨new, repl_type⟩ V new_fresh :=
          congrArg (fun T => VarCtx_insert ⟨new, T⟩ V new_fresh) h_repl_eq
        exact .pair_elim v₁ v₂ new hv₁_V hv₂_V hv₁v₂ new_fresh
          w₁_eq_V w₂_eq_V inner_wff
      · -- Case B: ⟨old, repl_type⟩ ∈ pe_V.  Erase, recurse inside inner_wff.
        have h_old_in_pe_V : ⟨old, repl_type⟩ ∈ pe_V.1 := by
          have h_old_in_W : ⟨old, repl_type⟩ ∈ W.1 := by
            rw [Wdef]; exact Finset.mem_insert_self _ _
          rw [← w₂_eq] at h_old_in_W
          rcases Finset.mem_insert.mp h_old_in_W with h_eq | h_pe_V
          · exact absurd h_eq.symm h_case
          · exact h_pe_V
        let pe_V' := VarCtx_erase pe_V ⟨old, repl_type⟩
        have old_fresh_pe_V' : old ∉ VarCtx_to_VarSymbs pe_V' :=
          VarCtx_erase_fresh h_old_in_pe_V
        have hv₁' : v₁.1 ∉ VarCtx_to_VarSymbs pe_V' :=
          fun hmem => hv₁ (VarCtx_to_VarSymbs_erase_subset hmem)
        have hv₂' : v₂.1 ∉ VarCtx_to_VarSymbs pe_V' :=
          fun hmem => hv₂ (VarCtx_to_VarSymbs_erase_subset hmem)
        have hz' : z ∉ VarCtx_to_VarSymbs pe_V' :=
          fun hmem => hz (VarCtx_to_VarSymbs_erase_subset hmem)
        have h_v₁_ne_old : v₁.1 ≠ old := fun heq =>
          hv₁ (Finset.mem_image.mpr ⟨_, h_old_in_pe_V, heq.symm⟩)
        have h_v₂_ne_old : v₂.1 ≠ old := fun heq =>
          hv₂ (Finset.mem_image.mpr ⟨_, h_old_in_pe_V, heq.symm⟩)
        have new_fresh_pe_V' : new ∉ VarCtx_to_VarSymbs pe_V' := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin_pe_V', hveq⟩
          have hvin_W : (⟨v, S⟩ : VarSymb × VarType) ∈ W.1 := by
            rw [← w₂_eq]; exact Finset.mem_insert_of_mem
              (Finset.erase_subset _ _ hvin_pe_V')
          rw [Wdef] at hvin_W
          rcases Finset.mem_insert.mp hvin_W with h_eq | h_inV
          · exact (Finset.mem_erase.mp hvin_pe_V').1 h_eq
          · exact new_fresh (Finset.mem_image.mpr ⟨⟨v, S⟩, h_inV, hveq⟩)
        let pe_W₁_inner := VarCtx_insert_twice v₁ v₂ pe_V' hv₁' hv₂' hv₁v₂
        have old_fresh_pe_W₁_inner : old ∉ VarCtx_to_VarSymbs pe_W₁_inner :=
          not_mem_VarSymbs_insert_twice h_v₁_ne_old.symm h_v₂_ne_old.symm
            old_fresh_pe_V'
        have new_fresh_pe_W₁_inner : new ∉ VarCtx_to_VarSymbs pe_W₁_inner :=
          not_mem_VarSymbs_insert_twice h_v₁_ne_new.symm h_v₂_ne_new.symm
            new_fresh_pe_V'
        have Wdef_inner : pe_W₁ =
            VarCtx_insert ⟨old, repl_type⟩ pe_W₁_inner old_fresh_pe_W₁_inner := by
          apply VarCtx_ext
          rw [← w₁_eq]
          change insert v₁ (insert v₂ pe_V.1) =
                 insert ⟨old, repl_type⟩ (insert v₁ (insert v₂ pe_V'.1))
          rw [← Finset.insert_erase h_old_in_pe_V,
              Finset.insert_comm v₂ ⟨old, repl_type⟩,
              Finset.insert_comm v₁ ⟨old, repl_type⟩]
          rfl
        let renamed_inner := WFF.rename old new repl_type
                               pe_W₁_inner pe_W₁
                               old_fresh_pe_W₁_inner new_fresh_pe_W₁_inner
                               Wdef_inner inner_wff h_nb_inner
        have hv₁_new : v₁.1 ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V') :=
          not_mem_VarSymbs_insert (x := ⟨new, repl_type⟩)
            (hx := new_fresh_pe_V') h_v₁_ne_new hv₁'
        have hv₂_new : v₂.1 ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V') :=
          not_mem_VarSymbs_insert (x := ⟨new, repl_type⟩)
            (hx := new_fresh_pe_V') h_v₂_ne_new hv₂'
        have hz_new : z ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V') :=
          not_mem_VarSymbs_insert (x := ⟨new, repl_type⟩)
            (hx := new_fresh_pe_V') h_z_ne_new hz'
        have ctx_swap : VarCtx_insert ⟨new, repl_type⟩
                          pe_W₁_inner new_fresh_pe_W₁_inner =
            VarCtx_insert_twice v₁ v₂
              (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V')
              hv₁_new hv₂_new hv₁v₂ :=
          VarCtx_insert_twice_insert_comm new_fresh_pe_W₁_inner hv₁_new hv₂_new
        have w₂_eq_new :
            VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩
              (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V') hz_new =
            VarCtx_insert ⟨new, repl_type⟩ V new_fresh := by
          apply VarCtx_ext
          change insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                   (insert ⟨new, repl_type⟩ pe_V'.1) =
                 insert ⟨new, repl_type⟩ V.1
          have h_old_not_in_V : (⟨old, repl_type⟩ : VarSymb × VarType) ∉ V.1 :=
            fun h => old_fresh (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          have h_W_set : insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                             pe_V.1
                       = insert ⟨old, repl_type⟩ V.1 :=
            congrArg PSigma.fst (w₂_eq.trans Wdef)
          have h_erased :
              insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V'.1
                = V.1 := by
            have step : (insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                           pe_V.1).erase ⟨old, repl_type⟩ = V.1 := by
              rw [h_W_set, Finset.erase_insert h_old_not_in_V]
            rwa [Finset.erase_insert_of_ne h_case] at step
          rw [← h_erased, Finset.insert_comm]
        exact .pair_elim v₁ v₂ z hv₁_new hv₂_new hv₁v₂ hz_new rfl
          w₂_eq_new (ctx_swap ▸ renamed_inner)

-- `WFF.rename` only swaps VarSymbs, never adding constructor nodes.
-- Mirrors `Term.numNodes_rename`'s case structure.
theorem WFF.numNodes_rename {σ : Signature}
    (old new : VarSymb) (repl_type : VarType) (V W : VarCtx)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (φ : WFF σ W) (h_nb : new ∉ WFF.boundVars φ) :
    WFF.numNodes (WFF.rename old new repl_type V W
                    old_fresh new_fresh Wdef φ h_nb)
      = WFF.numNodes φ := by
  match φ, h_nb with
  | .atom R, h_nb =>
      have ih := Rel.numNodes_rename old new repl_type V W 0
        old_fresh new_fresh Wdef R h_nb
      change 1 + Rel.numNodes _ = 1 + Rel.numNodes R
      omega
  | .top, _ => rfl
  | .bot, _ => rfl
  | .and ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.numNodes_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.numNodes_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change 1 + WFF.numNodes _ + WFF.numNodes _
           = 1 + WFF.numNodes ψ₁ + WFF.numNodes ψ₂
      omega
  | .or ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.numNodes_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.numNodes_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change 1 + WFF.numNodes _ + WFF.numNodes _
           = 1 + WFF.numNodes ψ₁ + WFF.numNodes ψ₂
      omega
  | .imp ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.numNodes_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.numNodes_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change 1 + WFF.numNodes _ + WFF.numNodes _
           = 1 + WFF.numNodes ψ₁ + WFF.numNodes ψ₂
      omega
  | .eq s t, h_nb =>
      have h_nb_s : new ∉ Term.boundVars s :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_s := Term.numNodes_rename old new repl_type V W _
        old_fresh new_fresh Wdef s h_nb_s
      have ih_t := Term.numNodes_rename old new repl_type V W _
        old_fresh new_fresh Wdef t h_nb_t
      change 1 + Term.numNodes _ + Term.numNodes _
           = 1 + Term.numNodes s + Term.numNodes t
      omega
  | @WFF.all _ _ x hx ψ, h_nb =>
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      -- WFF.rename produces `.all x (h_swap ▸ ψ_renamed)`.
      -- numNodes is invariant under ctx_cast and under rename (IH).
      unfold WFF.rename
      dsimp only
      change 1 + WFF.numNodes _ = 1 + WFF.numNodes ψ
      rw [WFF.numNodes_ctx_cast]
      congr 1
      exact WFF.numNodes_rename old new repl_type _ _ _ _ _ ψ h_nb_ψ
  | @WFF.ex _ _ x hx ψ, h_nb =>
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      unfold WFF.rename
      dsimp only
      change 1 + WFF.numNodes _ = 1 + WFF.numNodes ψ
      rw [WFF.numNodes_ctx_cast]
      congr 1
      exact WFF.numNodes_rename old new repl_type _ _ _ _ _ ψ h_nb_ψ
  | .box ψ hsub h_no_extras, h_nb =>
      rename_i V_inner
      unfold WFF.rename
      rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩ <;> dsimp only
      · rfl
      · split_ifs with h
        · change 1 + WFF.numNodes _ = 1 + WFF.numNodes ψ
          congr 1
          exact WFF.numNodes_rename old new innertype
            (VarCtx_erase V_inner ⟨old, innertype⟩) V_inner _ _ _ ψ h_nb
        · rfl
      · rfl
      · rfl
      · rfl
  | .dia x hx ψ hsub h_no_extras, h_nb =>
      rename_i V_inner
      unfold WFF.rename
      match repl_type with
      | .Var | .VTypeOne | .VTypeProd _ _ => rfl
      | .VTypeBox repl_inner =>
          dsimp only
          split_ifs with h
          · change 1 + WFF.numNodes _ = 1 + WFF.numNodes ψ
            congr 1
            rw [WFF.numNodes_ctx_cast]
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            exact WFF.numNodes_rename old new repl_inner
              (VarCtx_insert x (VarCtx_erase V_inner ⟨old, repl_inner⟩) _)
              (VarCtx_insert x V_inner hx) _ _ _ ψ h_nb_inner
          · rfl
      | .VTypeDia repl_inner =>
          dsimp only
          split_ifs with h_x
          · change 1 + WFF.numNodes _ = 1 + WFF.numNodes ψ
            congr 1
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            exact WFF.numNodes_rename old new repl_inner V_inner
              (VarCtx_insert x V_inner hx) _ _ _ ψ h_nb_inner
          · rfl
  | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁_eq w₂_eq inner_wff, h_nb =>
      rename_i pe_V pe_W₁
      unfold WFF.rename
      by_cases h_case :
          (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
      · rw [dif_pos h_case]
        rfl
      · rw [dif_neg h_case]
        change 1 + WFF.numNodes _ = 1 + WFF.numNodes inner_wff
        congr 1
        rw [WFF.numNodes_ctx_cast]
        have h_nb_inner : new ∉ WFF.boundVars inner_wff :=
          fun hmem => h_nb
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem hmem)))
        exact WFF.numNodes_rename old new repl_type
          (VarCtx_insert_twice v₁ v₂ (VarCtx_erase pe_V ⟨old, repl_type⟩) _ _ _)
          pe_W₁ _ _ _ inner_wff h_nb_inner

-- `WFF.rename`'s bound vars stay within the original's plus `new`.
-- Mirrors `Term.boundVars_rename_subset`'s case structure.
theorem WFF.boundVars_rename_subset {σ : Signature}
    (old new : VarSymb) (repl_type : VarType) (V W : VarCtx)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (φ : WFF σ W) (h_nb : new ∉ WFF.boundVars φ) :
    WFF.boundVars (WFF.rename old new repl_type V W
                     old_fresh new_fresh Wdef φ h_nb)
      ⊆ insert new (WFF.boundVars φ) := by
  match φ, h_nb with
  | .atom R, h_nb =>
      have ih := Rel.boundVars_rename_subset old new repl_type V W 0
        old_fresh new_fresh Wdef R h_nb
      intro x hx
      exact ih hx
  | .top, _ => exact Finset.empty_subset _
  | .bot, _ => exact Finset.empty_subset _
  | .and ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.boundVars_rename_subset old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.boundVars_rename_subset old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      intro x hx
      rcases Finset.mem_union.mp hx with h1 | h2
      · rcases Finset.mem_insert.mp (ih_1 h1) with rfl | h1'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h1')
      · rcases Finset.mem_insert.mp (ih_2 h2) with rfl | h2'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h2')
  | .or ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.boundVars_rename_subset old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.boundVars_rename_subset old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      intro x hx
      rcases Finset.mem_union.mp hx with h1 | h2
      · rcases Finset.mem_insert.mp (ih_1 h1) with rfl | h1'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h1')
      · rcases Finset.mem_insert.mp (ih_2 h2) with rfl | h2'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h2')
  | .imp ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.boundVars_rename_subset old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.boundVars_rename_subset old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      intro x hx
      rcases Finset.mem_union.mp hx with h1 | h2
      · rcases Finset.mem_insert.mp (ih_1 h1) with rfl | h1'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h1')
      · rcases Finset.mem_insert.mp (ih_2 h2) with rfl | h2'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h2')
  | .eq s t, h_nb =>
      have h_nb_s : new ∉ Term.boundVars s :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_s := Term.boundVars_rename_subset old new repl_type V W _
        old_fresh new_fresh Wdef s h_nb_s
      have ih_t := Term.boundVars_rename_subset old new repl_type V W _
        old_fresh new_fresh Wdef t h_nb_t
      intro x hx
      rcases Finset.mem_union.mp hx with h1 | h2
      · rcases Finset.mem_insert.mp (ih_s h1) with rfl | h1'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h1')
      · rcases Finset.mem_insert.mp (ih_t h2) with rfl | h2'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h2')
  | @WFF.all _ _ x hx ψ, h_nb =>
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      have hx_W : x.1 ∉ VarCtx_to_VarSymbs W := hx
      have h_W_symbols : VarCtx_to_VarSymbs W =
          insert old (VarCtx_to_VarSymbs V) := by
        rw [Wdef]; exact VarCtx_to_VarSymbs_insert _ _ _
      have hx_ne_old : x.1 ≠ old := fun h_eq =>
        hx_W (h_W_symbols ▸ Finset.mem_insert.mpr (Or.inl h_eq))
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := fun h_in =>
        hx_W (h_W_symbols ▸ Finset.mem_insert_of_mem h_in)
      have hx_ne_new : x.1 ≠ new := fun h_eq =>
        h_nb (Finset.mem_insert.mpr (Or.inl h_eq.symm))
      have hold_V_x : old ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_old h.symm) old_fresh
      have hnew_V_x : new ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_new h.symm) new_fresh
      have Wdef_inner :
          VarCtx_insert x W hx = VarCtx_insert ⟨old, repl_type⟩
            (VarCtx_insert x V hx_V) hold_V_x := by
        apply VarCtx_ext
        change insert x W.1 = insert ⟨old, repl_type⟩ (insert x V.1)
        rw [Wdef]
        change insert x (insert ⟨old, repl_type⟩ V.1) = _
        exact Finset.insert_comm _ _ _
      have ih := WFF.boundVars_rename_subset old new repl_type
        (VarCtx_insert x V hx_V) (VarCtx_insert x W hx)
        hold_V_x hnew_V_x Wdef_inner ψ h_nb_ψ
      unfold WFF.rename
      dsimp only
      intro y hy
      simp only [WFF.boundVars] at hy
      rw [WFF.boundVars_ctx_cast] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rcases Finset.mem_insert.mp (ih hy') with rfl | hy''
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy'')
  | @WFF.ex _ _ x hx ψ, h_nb =>
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      have hx_W : x.1 ∉ VarCtx_to_VarSymbs W := hx
      have h_W_symbols : VarCtx_to_VarSymbs W =
          insert old (VarCtx_to_VarSymbs V) := by
        rw [Wdef]; exact VarCtx_to_VarSymbs_insert _ _ _
      have hx_ne_old : x.1 ≠ old := fun h_eq =>
        hx_W (h_W_symbols ▸ Finset.mem_insert.mpr (Or.inl h_eq))
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := fun h_in =>
        hx_W (h_W_symbols ▸ Finset.mem_insert_of_mem h_in)
      have hx_ne_new : x.1 ≠ new := fun h_eq =>
        h_nb (Finset.mem_insert.mpr (Or.inl h_eq.symm))
      have hold_V_x : old ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_old h.symm) old_fresh
      have hnew_V_x : new ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_new h.symm) new_fresh
      have Wdef_inner :
          VarCtx_insert x W hx = VarCtx_insert ⟨old, repl_type⟩
            (VarCtx_insert x V hx_V) hold_V_x := by
        apply VarCtx_ext
        change insert x W.1 = insert ⟨old, repl_type⟩ (insert x V.1)
        rw [Wdef]
        change insert x (insert ⟨old, repl_type⟩ V.1) = _
        exact Finset.insert_comm _ _ _
      have ih := WFF.boundVars_rename_subset old new repl_type
        (VarCtx_insert x V hx_V) (VarCtx_insert x W hx)
        hold_V_x hnew_V_x Wdef_inner ψ h_nb_ψ
      unfold WFF.rename
      dsimp only
      intro y hy
      simp only [WFF.boundVars] at hy
      rw [WFF.boundVars_ctx_cast] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rcases Finset.mem_insert.mp (ih hy') with rfl | hy''
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy'')
  | .box ψ hsub h_no_extras, h_nb =>
      rename_i V_inner
      unfold WFF.rename
      rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩ <;> dsimp only
      · intro x hx
        exact Finset.mem_insert_of_mem hx
      · split_ifs with h
        · intro x hx
          exact (WFF.boundVars_rename_subset old new innertype
                   (VarCtx_erase V_inner ⟨old, innertype⟩) V_inner _ _ _ ψ h_nb) hx
        · intro x hx
          exact Finset.mem_insert_of_mem hx
      all_goals (intro x hx; exact Finset.mem_insert_of_mem hx)
  | .dia x hx ψ hsub h_no_extras, h_nb =>
      rename_i V_inner
      unfold WFF.rename
      match repl_type with
      | .Var | .VTypeOne | .VTypeProd _ _ =>
          intro y hy
          exact Finset.mem_insert_of_mem hy
      | .VTypeBox repl_inner =>
          dsimp only
          split_ifs with h
          · intro y hy
            simp only [WFF.boundVars] at hy
            rw [WFF.boundVars_ctx_cast] at hy
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            · rcases Finset.mem_insert.mp
                (WFF.boundVars_rename_subset old new repl_inner
                  (VarCtx_insert x (VarCtx_erase V_inner ⟨old, repl_inner⟩) _) _ _ _ _
                  ψ h_nb_inner hy') with rfl | hy''
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy'')
          · intro y hy
            exact Finset.mem_insert_of_mem hy
      | .VTypeDia repl_inner =>
          dsimp only
          split_ifs with h_x
          · intro y hy
            simp only [WFF.boundVars] at hy
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact Finset.mem_insert_self _ _
            · rcases Finset.mem_insert.mp
                (WFF.boundVars_rename_subset old new repl_inner V_inner _ _ _ _
                  ψ h_nb_inner hy') with rfl | hy''
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy'')
          · intro y hy
            exact Finset.mem_insert_of_mem hy
  | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁_eq w₂_eq inner_wff, h_nb =>
      rename_i pe_V pe_W₁
      unfold WFF.rename
      by_cases h_case :
          (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
      · rw [dif_pos h_case]
        intro y hy
        simp only [WFF.boundVars] at hy
        rcases Finset.mem_insert.mp hy with rfl | hy1
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        rcases Finset.mem_insert.mp hy1 with rfl | hy2
        · exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        rcases Finset.mem_insert.mp hy2 with rfl | hy3
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy3)))
      · rw [dif_neg h_case]
        intro y hy
        simp only [WFF.boundVars] at hy
        rw [WFF.boundVars_ctx_cast] at hy
        have h_nb_inner : new ∉ WFF.boundVars inner_wff :=
          fun hmem => h_nb
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem hmem)))
        rcases Finset.mem_insert.mp hy with rfl | hy1
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        rcases Finset.mem_insert.mp hy1 with rfl | hy2
        · exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        rcases Finset.mem_insert.mp hy2 with rfl | hy3
        · exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        · rcases Finset.mem_insert.mp
            (WFF.boundVars_rename_subset old new repl_type
              (VarCtx_insert_twice v₁ v₂ (VarCtx_erase pe_V ⟨old, repl_type⟩) _ _ _)
              pe_W₁ _ _ _ inner_wff h_nb_inner hy3) with rfl | hy4
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem hy4)))

-- `WFF.rename` only swaps VarSymbs, never introducing `.dia` constructors.
-- Mirrors `WFF.numNodes_rename`'s case structure.  Used as part of the
-- `.dia`/`.box`/`.pair_elim` arms' termination measure in any future
-- `WFF.ctx_rest_dia_arm` Case 3 (modal beta) implementation.
theorem WFF.diaCount_rename {σ : Signature}
    (old new : VarSymb) (repl_type : VarType) (V W : VarCtx)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (φ : WFF σ W) (h_nb : new ∉ WFF.boundVars φ) :
    WFF.diaCount (WFF.rename old new repl_type V W
                    old_fresh new_fresh Wdef φ h_nb)
      = WFF.diaCount φ := by
  match φ, h_nb with
  | .atom R, h_nb =>
      have ih := Rel.diaCount_rename old new repl_type V W 0
        old_fresh new_fresh Wdef R h_nb
      change Rel.diaCount _ = Rel.diaCount R
      exact ih
  | .top, _ => rfl
  | .bot, _ => rfl
  | .and ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.diaCount_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.diaCount_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change WFF.diaCount _ + WFF.diaCount _
           = WFF.diaCount ψ₁ + WFF.diaCount ψ₂
      omega
  | .or ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.diaCount_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.diaCount_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change WFF.diaCount _ + WFF.diaCount _
           = WFF.diaCount ψ₁ + WFF.diaCount ψ₂
      omega
  | .imp ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.diaCount_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.diaCount_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change WFF.diaCount _ + WFF.diaCount _
           = WFF.diaCount ψ₁ + WFF.diaCount ψ₂
      omega
  | .eq s t, h_nb =>
      have h_nb_s : new ∉ Term.boundVars s :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_s := Term.diaCount_rename old new repl_type V W _
        old_fresh new_fresh Wdef s h_nb_s
      have ih_t := Term.diaCount_rename old new repl_type V W _
        old_fresh new_fresh Wdef t h_nb_t
      change Term.diaCount _ + Term.diaCount _
           = Term.diaCount s + Term.diaCount t
      omega
  | @WFF.all _ _ x hx ψ, h_nb =>
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      unfold WFF.rename
      simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
      exact WFF.diaCount_rename old new repl_type _ _ _ _ _ ψ h_nb_ψ
  | @WFF.ex _ _ x hx ψ, h_nb =>
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      unfold WFF.rename
      simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
      exact WFF.diaCount_rename old new repl_type _ _ _ _ _ ψ h_nb_ψ
  | .box ψ hsub h_no_extras, h_nb =>
      rename_i V_inner
      unfold WFF.rename
      rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩ <;> dsimp only
      · rfl
      · split_ifs with h
        · change WFF.diaCount _ = WFF.diaCount ψ
          exact WFF.diaCount_rename old new innertype
            (VarCtx_erase V_inner ⟨old, innertype⟩) V_inner _ _ _ ψ h_nb
        · rfl
      · rfl
      · rfl
      · rfl
  | .dia x hx ψ hsub h_no_extras, h_nb =>
      rename_i V_inner
      unfold WFF.rename
      match repl_type with
      | .Var | .VTypeOne | .VTypeProd _ _ => rfl
      | .VTypeBox repl_inner =>
          dsimp only
          split_ifs with h
          · change 1 + WFF.diaCount _ = 1 + WFF.diaCount ψ
            rw [WFF.diaCount_ctx_cast]
            congr 1
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            exact WFF.diaCount_rename old new repl_inner
              (VarCtx_insert x (VarCtx_erase V_inner ⟨old, repl_inner⟩) _)
              (VarCtx_insert x V_inner hx) _ _ _ ψ h_nb_inner
          · rfl
      | .VTypeDia repl_inner =>
          dsimp only
          split_ifs with h_x
          · change 1 + WFF.diaCount _ = 1 + WFF.diaCount ψ
            congr 1
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            exact WFF.diaCount_rename old new repl_inner V_inner
              (VarCtx_insert x V_inner hx) _ _ _ ψ h_nb_inner
          · rfl
  | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁_eq w₂_eq inner_wff, h_nb =>
      rename_i pe_V pe_W₁
      unfold WFF.rename
      by_cases h_case :
          (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
      · rw [dif_pos h_case]
        rfl
      · rw [dif_neg h_case]
        simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
        have h_nb_inner : new ∉ WFF.boundVars inner_wff :=
          fun hmem => h_nb
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem hmem)))
        exact WFF.diaCount_rename old new repl_type
          (VarCtx_insert_twice v₁ v₂ (VarCtx_erase pe_V ⟨old, repl_type⟩) _ _ _)
          pe_W₁ _ _ _ inner_wff h_nb_inner

-- `WFF.rename` preserves binder pair-depth (since rename only changes
-- symbols, not binder types).  Mirrors `WFF.numNodes_rename`'s case
-- structure.
theorem WFF.binderPairDepth_rename {σ : Signature}
    (old new : VarSymb) (repl_type : VarType) (V W : VarCtx)
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (φ : WFF σ W) (h_nb : new ∉ WFF.boundVars φ) :
    WFF.binderPairDepth (WFF.rename old new repl_type V W
                           old_fresh new_fresh Wdef φ h_nb)
      = WFF.binderPairDepth φ := by
  match φ, h_nb with
  | .atom _, _ => rfl
  | .top, _ => rfl
  | .bot, _ => rfl
  | .and ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.binderPairDepth_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.binderPairDepth_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change WFF.binderPairDepth _ + WFF.binderPairDepth _
           = WFF.binderPairDepth ψ₁ + WFF.binderPairDepth ψ₂
      omega
  | .or ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.binderPairDepth_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.binderPairDepth_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change WFF.binderPairDepth _ + WFF.binderPairDepth _
           = WFF.binderPairDepth ψ₁ + WFF.binderPairDepth ψ₂
      omega
  | .imp ψ₁ ψ₂, h_nb =>
      have h_nb_1 : new ∉ WFF.boundVars ψ₁ :=
        fun hmem => h_nb (Finset.mem_union_left _ hmem)
      have h_nb_2 : new ∉ WFF.boundVars ψ₂ :=
        fun hmem => h_nb (Finset.mem_union_right _ hmem)
      have ih_1 := WFF.binderPairDepth_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₁ h_nb_1
      have ih_2 := WFF.binderPairDepth_rename old new repl_type V W
        old_fresh new_fresh Wdef ψ₂ h_nb_2
      change WFF.binderPairDepth _ + WFF.binderPairDepth _
           = WFF.binderPairDepth ψ₁ + WFF.binderPairDepth ψ₂
      omega
  | .eq _ _, _ => rfl
  | @WFF.all _ _ x hx ψ, h_nb =>
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      unfold WFF.rename
      dsimp only
      change x.2.pairDepth + WFF.binderPairDepth _
           = x.2.pairDepth + WFF.binderPairDepth ψ
      rw [WFF.binderPairDepth_ctx_cast]
      congr 1
      exact WFF.binderPairDepth_rename old new repl_type _ _ _ _ _ ψ h_nb_ψ
  | @WFF.ex _ _ x hx ψ, h_nb =>
      have h_nb_ψ : new ∉ WFF.boundVars ψ :=
        fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
      unfold WFF.rename
      dsimp only
      change x.2.pairDepth + WFF.binderPairDepth _
           = x.2.pairDepth + WFF.binderPairDepth ψ
      rw [WFF.binderPairDepth_ctx_cast]
      congr 1
      exact WFF.binderPairDepth_rename old new repl_type _ _ _ _ _ ψ h_nb_ψ
  | .box ψ hsub h_no_extras, h_nb =>
      rename_i V_inner
      unfold WFF.rename
      rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩ <;> dsimp only
      · rfl
      · split_ifs with h
        · change WFF.binderPairDepth _ = WFF.binderPairDepth ψ
          exact WFF.binderPairDepth_rename old new innertype
            (VarCtx_erase V_inner ⟨old, innertype⟩) V_inner _ _ _ ψ h_nb
        · rfl
      · rfl
      · rfl
      · rfl
  | .dia x hx ψ hsub h_no_extras, h_nb =>
      rename_i V_inner
      unfold WFF.rename
      match repl_type with
      | .Var | .VTypeOne | .VTypeProd _ _ => rfl
      | .VTypeBox repl_inner =>
          dsimp only
          split_ifs with h
          · -- bpd's `.dia` clause no longer adds x.2.pairDepth, so no peel:
            -- reduce the `.dia` clause and the cast, then apply the IH.
            simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            exact WFF.binderPairDepth_rename old new repl_inner
              (VarCtx_insert x (VarCtx_erase V_inner ⟨old, repl_inner⟩) _)
              (VarCtx_insert x V_inner hx) _ _ _ ψ h_nb_inner
          · rfl
      | .VTypeDia repl_inner =>
          dsimp only
          split_ifs with h_x
          · simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
            have h_nb_inner : new ∉ WFF.boundVars ψ :=
              fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
            exact WFF.binderPairDepth_rename old new repl_inner V_inner
              (VarCtx_insert x V_inner hx) _ _ _ ψ h_nb_inner
          · rfl
  | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁_eq w₂_eq inner_wff, h_nb =>
      rename_i pe_V pe_W₁
      unfold WFF.rename
      by_cases h_case :
          (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
      · rw [dif_pos h_case]
        rfl
      · rw [dif_neg h_case]
        simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
        have h_nb_inner : new ∉ WFF.boundVars inner_wff :=
          fun hmem => h_nb
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem hmem)))
        exact WFF.binderPairDepth_rename old new repl_type
          (VarCtx_insert_twice v₁ v₂ (VarCtx_erase pe_V ⟨old, repl_type⟩) _ _ _)
          pe_W₁ _ _ _ inner_wff h_nb_inner

/-! ### Context Extension -/

-- Extend a WFF `φ : WFF σ V` to `WFF σ (VarCtx_insert xv V hxv)`, mirroring
-- `Term.ctx_ext`.  The caller does NOT need to guarantee freshness of `xv.1`
-- against `φ`'s bound vars — collisions at the binder cases (`.all`, `.ex`,
-- `.dia`, `.pair_elim`) are handled internally via `WFF.rename`.
--
-- Termination: lex `(sizeOf xv.2, WFF.numNodes φ)`.  `WFF.numNodes` is
-- preserved by `WFF.rename`, so collision branches decrease on the second
-- component via the standard subterm argument.
--
-- The `.pair_elim` arm is factored into `WFF.ctx_ext_pe_arm` (defined in the
-- same `mutual` block so it can recurse on `WFF.ctx_ext`).  Both share the
-- `(sizeOf xv.2, WFF.numNodes φ)` lex measure (with the helper's "φ" being
-- the reconstructed `.pair_elim` constructor).
mutual

def WFF.ctx_ext {σ : Signature} {V : VarCtx}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ V) : WFF σ (VarCtx_insert xv V hxv) := by
  match φ with
  | .atom R => exact .atom (Rel.ctx_ext xv hxv R)
  | .top => exact .top
  | .bot => exact .bot
  | .and φ' ψ =>
      exact .and (WFF.ctx_ext xv hxv φ') (WFF.ctx_ext xv hxv ψ)
  | .or φ' ψ =>
      exact .or (WFF.ctx_ext xv hxv φ') (WFF.ctx_ext xv hxv ψ)
  | .imp φ' ψ =>
      exact .imp (WFF.ctx_ext xv hxv φ') (WFF.ctx_ext xv hxv ψ)
  | .eq s t =>
      exact .eq (Term.ctx_ext xv hxv s) (Term.ctx_ext xv hxv t)
  | @WFF.all _ _ x hx ψ =>
      -- α-rename x if xv.1 = x.1 (collision), then recurse on ψ at the
      -- extended context, swap inserts, wrap with .all.
      by_cases h_col : xv.1 = x.1
      · -- Collision: rename x.1 → x'_sym in ψ.
        let avoid : Finset VarSymb :=
          VarCtx_to_VarSymbs V ∪ {xv.1} ∪ WFF.boundVars ψ
        let x'_sym := VarSymb.fresh avoid
        have hx'_avoid : x'_sym ∉ avoid := VarSymb.fresh_not_mem _
        have hx'_V : x'_sym ∉ VarCtx_to_VarSymbs V := fun h =>
          hx'_avoid (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have hx'_ne_xv : x'_sym ≠ xv.1 := fun h =>
          hx'_avoid (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_singleton.mpr h)))
        have hx'_nb_ψ : x'_sym ∉ WFF.boundVars ψ := fun h =>
          hx'_avoid (Finset.mem_union_right _ h)
        have hWdef : VarCtx_insert x V hx = VarCtx_insert ⟨x.1, x.2⟩ V hx := by
          apply VarCtx_ext; rfl
        let ψ_renamed : WFF σ (VarCtx_insert ⟨x'_sym, x.2⟩ V hx'_V) :=
          WFF.rename x.1 x'_sym x.2 V (VarCtx_insert x V hx)
            hx hx'_V hWdef ψ hx'_nb_ψ
        have hxv_x' : xv.1 ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨x'_sym, x.2⟩ V hx'_V) :=
          not_mem_VarSymbs_insert (fun h => hx'_ne_xv h.symm) hxv
        let ψ_ext := WFF.ctx_ext xv hxv_x' ψ_renamed
        have hx'_xv_V : x'_sym ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxv) :=
          not_mem_VarSymbs_insert hx'_ne_xv hx'_V
        have h_swap :
            VarCtx_insert xv (VarCtx_insert ⟨x'_sym, x.2⟩ V hx'_V) hxv_x' =
            VarCtx_insert ⟨x'_sym, x.2⟩ (VarCtx_insert xv V hxv) hx'_xv_V := by
          apply VarCtx_ext
          change insert xv (insert (⟨x'_sym, x.2⟩ : VarSymb × VarType) V.1) =
                 insert (⟨x'_sym, x.2⟩ : VarSymb × VarType) (insert xv V.1)
          exact Finset.insert_comm _ _ _
        exact .all ⟨x'_sym, x.2⟩ (hx := hx'_xv_V) (h_swap ▸ ψ_ext)
      · -- No collision.
        have hxv_x : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) :=
          not_mem_VarSymbs_insert h_col hxv
        let ψ_ext := WFF.ctx_ext xv hxv_x ψ
        have hx_xv_V : x.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxv) :=
          not_mem_VarSymbs_insert (fun h => h_col h.symm) hx
        have h_swap :
            VarCtx_insert xv (VarCtx_insert x V hx) hxv_x =
            VarCtx_insert x (VarCtx_insert xv V hxv) hx_xv_V := by
          apply VarCtx_ext
          change insert xv (insert x V.1) = insert x (insert xv V.1)
          exact Finset.insert_comm _ _ _
        exact .all x (hx := hx_xv_V) (h_swap ▸ ψ_ext)
  | @WFF.ex _ _ x hx ψ =>
      -- Symmetric to .all.
      by_cases h_col : xv.1 = x.1
      · let avoid : Finset VarSymb :=
          VarCtx_to_VarSymbs V ∪ {xv.1} ∪ WFF.boundVars ψ
        let x'_sym := VarSymb.fresh avoid
        have hx'_avoid : x'_sym ∉ avoid := VarSymb.fresh_not_mem _
        have hx'_V : x'_sym ∉ VarCtx_to_VarSymbs V := fun h =>
          hx'_avoid (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have hx'_ne_xv : x'_sym ≠ xv.1 := fun h =>
          hx'_avoid (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_singleton.mpr h)))
        have hx'_nb_ψ : x'_sym ∉ WFF.boundVars ψ := fun h =>
          hx'_avoid (Finset.mem_union_right _ h)
        have hWdef : VarCtx_insert x V hx = VarCtx_insert ⟨x.1, x.2⟩ V hx := by
          apply VarCtx_ext; rfl
        let ψ_renamed : WFF σ (VarCtx_insert ⟨x'_sym, x.2⟩ V hx'_V) :=
          WFF.rename x.1 x'_sym x.2 V (VarCtx_insert x V hx)
            hx hx'_V hWdef ψ hx'_nb_ψ
        have hxv_x' : xv.1 ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨x'_sym, x.2⟩ V hx'_V) :=
          not_mem_VarSymbs_insert (fun h => hx'_ne_xv h.symm) hxv
        let ψ_ext := WFF.ctx_ext xv hxv_x' ψ_renamed
        have hx'_xv_V : x'_sym ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxv) :=
          not_mem_VarSymbs_insert hx'_ne_xv hx'_V
        have h_swap :
            VarCtx_insert xv (VarCtx_insert ⟨x'_sym, x.2⟩ V hx'_V) hxv_x' =
            VarCtx_insert ⟨x'_sym, x.2⟩ (VarCtx_insert xv V hxv) hx'_xv_V := by
          apply VarCtx_ext
          change insert xv (insert (⟨x'_sym, x.2⟩ : VarSymb × VarType) V.1) =
                 insert (⟨x'_sym, x.2⟩ : VarSymb × VarType) (insert xv V.1)
          exact Finset.insert_comm _ _ _
        exact .ex ⟨x'_sym, x.2⟩ (hx := hx'_xv_V) (h_swap ▸ ψ_ext)
      · have hxv_x : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) :=
          not_mem_VarSymbs_insert h_col hxv
        let ψ_ext := WFF.ctx_ext xv hxv_x ψ
        have hx_xv_V : x.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V hxv) :=
          not_mem_VarSymbs_insert (fun h => h_col h.symm) hx
        have h_swap :
            VarCtx_insert xv (VarCtx_insert x V hx) hxv_x =
            VarCtx_insert x (VarCtx_insert xv V hxv) hx_xv_V := by
          apply VarCtx_ext
          change insert xv (insert x V.1) = insert x (insert xv V.1)
          exact Finset.insert_comm _ _ _
        exact .ex x (hx := hx_xv_V) (h_swap ▸ ψ_ext)
  | .box ψ hsub h_no_extras =>
      rename_i V_inner
      -- xv.1 ∉ V_inner.symbols (derived from hxv via hsub).
      have hxv_inner : xv.1 ∉ VarCtx_to_VarSymbs V_inner := by
        intro h_in_inner
        apply hxv
        obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
        cases q with
        | mk qv qT =>
          have hbox_in_inner : (⟨qv, qT.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩
          exact Finset.mem_image.mpr ⟨_, hsub hbox_in_inner, hq_eq⟩
      match h_xv2 : xv.2 with
      | .VTypeBox U' =>
          let V_inner_ext := VarCtx_insert ⟨xv.1, U'⟩ V_inner hxv_inner
          have h_xv_sz_lt : sizeOf U' < sizeOf xv.2 := by
            rw [h_xv2]; simp +arith
          let ψ' : WFF σ V_inner_ext :=
            WFF.ctx_ext ⟨xv.1, U'⟩ hxv_inner ψ
          have h_xv_eq : (⟨xv.1, U'.VTypeBox⟩ : VarSymb × VarType) = xv :=
            Prod.ext rfl h_xv2.symm
          have hsub' : (VarCtx_box V_inner_ext).1 ⊆
                       (VarCtx_insert xv V hxv).1 := by
            rw [VarCtx_box_fst_insert]
            intro p hp
            rcases Finset.mem_insert.mp hp with h_eq | hp_box
            · subst h_eq; rw [h_xv_eq]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (hsub hp_box)
          have h_no_extras' :
              ∀ p ∈ (VarCtx_insert xv V hxv).1,
                VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner_ext).1 := by
            intro p hp h_box
            rw [VarCtx_box_fst_insert]
            rcases Finset.mem_insert.mp hp with h_eq | hp_V
            · subst h_eq; rw [← h_xv_eq]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (h_no_extras p hp_V h_box)
          exact .box ψ' hsub' h_no_extras'
      | .Var =>
          refine .box ψ
            (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
          intro p hp h_box
          rcases Finset.mem_insert.mp hp with h_eq | hp_V
          · subst h_eq; rw [h_xv2] at h_box; simp [VarType.isBox] at h_box
          · exact h_no_extras p hp_V h_box
      | .VTypeOne =>
          refine .box ψ
            (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
          intro p hp h_box
          rcases Finset.mem_insert.mp hp with h_eq | hp_V
          · subst h_eq; rw [h_xv2] at h_box; simp [VarType.isBox] at h_box
          · exact h_no_extras p hp_V h_box
      | .VTypeDia U' =>
          refine .box ψ
            (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
          intro p hp h_box
          rcases Finset.mem_insert.mp hp with h_eq | hp_V
          · subst h_eq; rw [h_xv2] at h_box; simp [VarType.isBox] at h_box
          · exact h_no_extras p hp_V h_box
      | .VTypeProd a b =>
          -- Peel: extend with ⟨w1, a⟩ then ⟨w2, b⟩, wrap with `.pair_elim`
          -- via WFF.pairElim η-distribution.
          let pe_t : WFF σ V := .box ψ hsub h_no_extras
          have h_a_sz_lt : sizeOf a < sizeOf xv.2 := by
            rw [h_xv2]; simp +arith
          have h_b_sz_lt : sizeOf b < sizeOf xv.2 := by
            rw [h_xv2]; simp +arith
          let avoid_1 : Finset VarSymb :=
            VarCtx_to_VarSymbs V ∪ {xv.1} ∪ WFF.boundVars pe_t
          let w1 : VarSymb := VarSymb.fresh avoid_1
          have hw1_avoid_1 : w1 ∉ avoid_1 := VarSymb.fresh_not_mem _
          have hw1_V : w1 ∉ VarCtx_to_VarSymbs V := fun h =>
            hw1_avoid_1 (Finset.mem_union_left _ (Finset.mem_union_left _ h))
          let t1 := WFF.ctx_ext ⟨w1, a⟩ hw1_V pe_t
          let V_plus_w1 := VarCtx_insert ⟨w1, a⟩ V hw1_V
          let w2 : VarSymb := VarSymb.fresh (insert w1 avoid_1)
          have hw2_avoid_w1 : w2 ∉ insert w1 avoid_1 := VarSymb.fresh_not_mem _
          have hw2_V : w2 ∉ VarCtx_to_VarSymbs V := fun h =>
            hw2_avoid_w1 (Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
          have hw1w2_ne : w1 ≠ w2 := fun h =>
            hw2_avoid_w1 (h ▸ Finset.mem_insert_self _ _)
          have hw2_V_plus_w1 : w2 ∉ VarCtx_to_VarSymbs V_plus_w1 :=
            not_mem_VarSymbs_insert (fun h => hw1w2_ne h.symm) hw2_V
          let t2 := WFF.ctx_ext ⟨w2, b⟩ hw2_V_plus_w1 t1
          have h_swap_eq :
              VarCtx_insert ⟨w2, b⟩ V_plus_w1 hw2_V_plus_w1 =
              VarCtx_insert_twice ⟨w1, a⟩ ⟨w2, b⟩ V hw1_V hw2_V hw1w2_ne := by
            apply VarCtx_ext
            change insert (⟨w2, b⟩ : VarSymb × VarType) (insert ⟨w1, a⟩ V.1)
                 = insert ⟨w1, a⟩ (insert ⟨w2, b⟩ V.1)
            exact Finset.insert_comm _ _ _
          let t2_cast := h_swap_eq ▸ t2
          have hxv_eq : (⟨xv.1, a.VTypeProd b⟩ : VarSymb × VarType) = xv :=
            Prod.ext rfl h_xv2.symm
          have h_W2_eq :
              VarCtx_insert (⟨xv.1, a.VTypeProd b⟩ : VarSymb × VarType) V hxv =
              VarCtx_insert xv V hxv := by
            apply VarCtx_ext
            change insert (⟨xv.1, a.VTypeProd b⟩ : VarSymb × VarType) V.1
                 = insert xv V.1
            rw [hxv_eq]
          exact h_W2_eq ▸ WFF.pairElim ⟨w1, a⟩ ⟨w2, b⟩ xv.1
            hw1_V hw2_V hw1w2_ne hxv rfl rfl t2_cast
  | .dia x_t hx_t ψ hsub h_no_extras =>
      rename_i V_inner
      have hxv_inner : xv.1 ∉ VarCtx_to_VarSymbs V_inner := by
        intro h_in_inner
        apply hxv
        obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
        cases q with
        | mk qv qT =>
          have hbox_in_inner : (⟨qv, qT.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩
          have hbox_in_dia : (⟨qv, qT.VTypeBox⟩ : VarSymb × VarType)
                              ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
            rw [VarCtx_dia_fst]
            exact Finset.mem_insert_of_mem hbox_in_inner
          exact Finset.mem_image.mpr ⟨_, hsub hbox_in_dia, hq_eq⟩
      match h_xv2 : xv.2 with
      | .VTypeBox U' =>
          have h_xv_eq : xv = (⟨xv.1, U'.VTypeBox⟩ : VarSymb × VarType) :=
            Prod.ext rfl h_xv2
          have h_xv_sz_lt : sizeOf U' < sizeOf xv.2 := by
            rw [h_xv2]; simp +arith
          have hxv_ne_x_t : xv.1 ≠ x_t.1 := by
            intro h_eq
            apply hxv
            have hdia_in : (⟨x_t.1, x_t.2.VTypeDia⟩ : VarSymb × VarType)
                            ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
            exact Finset.mem_image.mpr ⟨_, hsub hdia_in, h_eq.symm⟩
          let V_inner_ext := VarCtx_insert ⟨xv.1, U'⟩ V_inner hxv_inner
          have hx_t_inner_ext : x_t.1 ∉ VarCtx_to_VarSymbs V_inner_ext :=
            not_mem_VarSymbs_insert hxv_ne_x_t.symm hx_t
          have hxv_outer : xv.1 ∉ VarCtx_to_VarSymbs
                            (VarCtx_insert x_t V_inner hx_t) :=
            not_mem_VarSymbs_insert hxv_ne_x_t hxv_inner
          let ψ_ext_pre :
              WFF σ (VarCtx_insert ⟨xv.1, U'⟩
                        (VarCtx_insert x_t V_inner hx_t) hxv_outer) :=
            WFF.ctx_ext ⟨xv.1, U'⟩ hxv_outer ψ
          have h_swap :
              VarCtx_insert ⟨xv.1, U'⟩
                  (VarCtx_insert x_t V_inner hx_t) hxv_outer =
              VarCtx_insert x_t V_inner_ext hx_t_inner_ext :=
            @VarCtx_insert_comm ⟨xv.1, U'⟩ x_t V_inner hx_t hxv_inner
              hxv_outer hx_t_inner_ext
          let ψ_ext : WFF σ (VarCtx_insert x_t V_inner_ext hx_t_inner_ext) :=
            h_swap ▸ ψ_ext_pre
          have hsub' : (VarCtx_dia x_t V_inner_ext hx_t_inner_ext).1 ⊆
                       (VarCtx_insert xv V hxv).1 := by
            rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
            intro p hp
            rcases Finset.mem_insert.mp hp with h_eq | hp_rest
            · subst h_eq
              have hdia_in_orig :
                  (⟨x_t.1, x_t.2.VTypeDia⟩ : VarSymb × VarType)
                    ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
                rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
              exact Finset.mem_insert_of_mem (hsub hdia_in_orig)
            · rcases Finset.mem_insert.mp hp_rest with h_eq | hp_box
              · subst h_eq
                exact Finset.mem_insert.mpr (Or.inl h_xv_eq.symm)
              · have hp_dia_orig : p ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
                  rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_box
                exact Finset.mem_insert_of_mem (hsub hp_dia_orig)
          have h_no_extras' :
              ∀ p ∈ (VarCtx_insert xv V hxv).1, VarType.isBox p.2 = true →
                p ∈ (VarCtx_dia x_t V_inner_ext hx_t_inner_ext).1 := by
            intro p hp h_box
            rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
            rcases Finset.mem_insert.mp hp with h_eq | hp_V
            · subst h_eq
              apply Finset.mem_insert_of_mem
              exact Finset.mem_insert.mpr (Or.inl h_xv_eq)
            · have hp_in_dia := h_no_extras p hp_V h_box
              rw [VarCtx_dia_fst] at hp_in_dia
              rcases Finset.mem_insert.mp hp_in_dia with h_eq | hp_box_in
              · subst h_eq; exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hp_box_in)
          exact .dia x_t hx_t_inner_ext ψ_ext hsub' h_no_extras'
      | .Var =>
          refine .dia x_t hx_t ψ
            (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
          intro p hp h_box
          rcases Finset.mem_insert.mp hp with h_eq | hp_V
          · subst h_eq; rw [h_xv2] at h_box; simp [VarType.isBox] at h_box
          · exact h_no_extras p hp_V h_box
      | .VTypeOne =>
          refine .dia x_t hx_t ψ
            (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
          intro p hp h_box
          rcases Finset.mem_insert.mp hp with h_eq | hp_V
          · subst h_eq; rw [h_xv2] at h_box; simp [VarType.isBox] at h_box
          · exact h_no_extras p hp_V h_box
      | .VTypeDia _ =>
          refine .dia x_t hx_t ψ
            (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
          intro p hp h_box
          rcases Finset.mem_insert.mp hp with h_eq | hp_V
          · subst h_eq; rw [h_xv2] at h_box; simp [VarType.isBox] at h_box
          · exact h_no_extras p hp_V h_box
      | .VTypeProd a b =>
          let pe_t : WFF σ V := .dia x_t hx_t ψ hsub h_no_extras
          have h_a_sz_lt : sizeOf a < sizeOf xv.2 := by
            rw [h_xv2]; simp +arith
          have h_b_sz_lt : sizeOf b < sizeOf xv.2 := by
            rw [h_xv2]; simp +arith
          let avoid_1 : Finset VarSymb :=
            VarCtx_to_VarSymbs V ∪ {xv.1} ∪ WFF.boundVars pe_t
          let w1 : VarSymb := VarSymb.fresh avoid_1
          have hw1_avoid_1 : w1 ∉ avoid_1 := VarSymb.fresh_not_mem _
          have hw1_V : w1 ∉ VarCtx_to_VarSymbs V := fun h =>
            hw1_avoid_1 (Finset.mem_union_left _ (Finset.mem_union_left _ h))
          let t1 := WFF.ctx_ext ⟨w1, a⟩ hw1_V pe_t
          let V_plus_w1 := VarCtx_insert ⟨w1, a⟩ V hw1_V
          let w2 : VarSymb := VarSymb.fresh (insert w1 avoid_1)
          have hw2_avoid_w1 : w2 ∉ insert w1 avoid_1 := VarSymb.fresh_not_mem _
          have hw2_V : w2 ∉ VarCtx_to_VarSymbs V := fun h =>
            hw2_avoid_w1 (Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
          have hw1w2_ne : w1 ≠ w2 := fun h =>
            hw2_avoid_w1 (h ▸ Finset.mem_insert_self _ _)
          have hw2_V_plus_w1 : w2 ∉ VarCtx_to_VarSymbs V_plus_w1 :=
            not_mem_VarSymbs_insert (fun h => hw1w2_ne h.symm) hw2_V
          let t2 := WFF.ctx_ext ⟨w2, b⟩ hw2_V_plus_w1 t1
          have h_swap_eq :
              VarCtx_insert ⟨w2, b⟩ V_plus_w1 hw2_V_plus_w1 =
              VarCtx_insert_twice ⟨w1, a⟩ ⟨w2, b⟩ V hw1_V hw2_V hw1w2_ne := by
            apply VarCtx_ext
            change insert (⟨w2, b⟩ : VarSymb × VarType) (insert ⟨w1, a⟩ V.1)
                 = insert ⟨w1, a⟩ (insert ⟨w2, b⟩ V.1)
            exact Finset.insert_comm _ _ _
          let t2_cast := h_swap_eq ▸ t2
          have hxv_eq : (⟨xv.1, a.VTypeProd b⟩ : VarSymb × VarType) = xv :=
            Prod.ext rfl h_xv2.symm
          have h_W2_eq :
              VarCtx_insert (⟨xv.1, a.VTypeProd b⟩ : VarSymb × VarType) V hxv =
              VarCtx_insert xv V hxv := by
            apply VarCtx_ext
            change insert (⟨xv.1, a.VTypeProd b⟩ : VarSymb × VarType) V.1
                 = insert xv V.1
            rw [hxv_eq]
          exact h_W2_eq ▸ WFF.pairElim ⟨w1, a⟩ ⟨w2, b⟩ xv.1
            hw1_V hw2_V hw1w2_ne hxv rfl rfl t2_cast
  | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body =>
      rename_i pe_V pe_W₁
      exact WFF.ctx_ext_pe_arm xv hxv pe_V pe_W₁
        v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body
termination_by (sizeOf xv.2, WFF.numNodes φ, 1)
decreasing_by
  all_goals first
    -- pair_elim case: dispatch to pe_arm at same (sizeOf, numNodes) but
    -- lower phase (1 → 0).
    | (refine Prod.Lex.right _ (Prod.Lex.right _ ?_); decide)
    | (refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
       simp only [WFF.numNodes, WFF.numNodes_rename, WFF.numNodes_ctx_cast]
       omega)
    | (refine Prod.Lex.left _ _ ?_; assumption)

-- Helper for `WFF.ctx_ext`'s `.pair_elim` arm.  Factored out to keep the
-- main function's elaboration tractable.  Mirrors `Term.ctx_ext`'s
-- pair_elim arm: detects collisions between `xv` and the binders `v1`,
-- `v2`, α-renames body via `WFF.rename` when needed, then recurses on
-- the extended body via `WFF.ctx_ext`, finally re-pairs via `WFF.pairElim`.
def WFF.ctx_ext_pe_arm {σ : Signature} {V : VarCtx}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (pe_V pe_W₁ : VarCtx)
    (v1 v2 : VarSymb × VarType) (z : VarSymb)
    (hv1 : v1.1 ∉ VarCtx_to_VarSymbs pe_V)
    (hv2 : v2.1 ∉ VarCtx_to_VarSymbs pe_V)
    (hv1v2 : v1.1 ≠ v2.1)
    (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w1eq : VarCtx_insert_twice v1 v2 pe_V hv1 hv2 hv1v2 = pe_W₁)
    (w2eq : VarCtx_insert ⟨z, .VTypeProd v1.2 v2.2⟩ pe_V hz = V)
    (body : WFF σ pe_W₁) :
    WFF σ (VarCtx_insert xv V hxv) := by
  have hxv_pe_V : xv.1 ∉ VarCtx_to_VarSymbs pe_V := by
    intro h
    apply hxv
    obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h
    have hq_in_V : q ∈ V.1 := by
      rw [← w2eq]; exact Finset.mem_insert_of_mem hq_in
    exact Finset.mem_image.mpr ⟨q, hq_in_V, hq_eq⟩
  have hxv_ne_z : xv.1 ≠ z := by
    intro h
    apply hxv
    have h_z_in_V : (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType) ∈ V.1 := by
      rw [← w2eq]; exact Finset.mem_insert_self _ _
    exact Finset.mem_image.mpr ⟨⟨z, .VTypeProd v1.2 v2.2⟩, h_z_in_V, h.symm⟩
  by_cases h_col_v1 : xv.1 = v1.1
  · -- Collision on v1.
    have hxv_ne_v2 : xv.1 ≠ v2.1 := fun h => hv1v2 (h_col_v1.symm.trans h)
    let avoid_v1 : Finset VarSymb :=
      VarCtx_to_VarSymbs pe_V ∪ {xv.1, v2.1, z} ∪ WFF.boundVars body
    let v1'_sym : VarSymb := VarSymb.fresh avoid_v1
    have hv1'_avoid : v1'_sym ∉ avoid_v1 := VarSymb.fresh_not_mem _
    have hv1'_pe_V : v1'_sym ∉ VarCtx_to_VarSymbs pe_V := fun h =>
      hv1'_avoid (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hv1'_xv : v1'_sym ≠ xv.1 := fun h => hv1'_avoid
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_insert.mpr (Or.inl h))))
    have hv1'_v2 : v1'_sym ≠ v2.1 := fun h => hv1'_avoid
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h)))))
    have hv1'_body : v1'_sym ∉ WFF.boundVars body := fun h =>
      hv1'_avoid (Finset.mem_union_right _ h)
    have hv1_V_v2 : v1.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v2 pe_V hv2) :=
      not_mem_VarSymbs_insert hv1v2 hv1
    have hv1'_V_v2 : v1'_sym ∉ VarCtx_to_VarSymbs
        (VarCtx_insert v2 pe_V hv2) :=
      not_mem_VarSymbs_insert hv1'_v2 hv1'_pe_V
    have hWdef1 : pe_W₁ = VarCtx_insert ⟨v1.1, v1.2⟩
        (VarCtx_insert v2 pe_V hv2) hv1_V_v2 := by
      apply VarCtx_ext
      change pe_W₁.1 = insert v1 (insert v2 pe_V.1)
      exact (congrArg PSigma.fst w1eq).symm
    let body1 : WFF σ (VarCtx_insert ⟨v1'_sym, v1.2⟩
        (VarCtx_insert v2 pe_V hv2) hv1'_V_v2) :=
      WFF.rename v1.1 v1'_sym v1.2 (VarCtx_insert v2 pe_V hv2) pe_W₁
        hv1_V_v2 hv1'_V_v2 hWdef1 body hv1'_body
    let v1' : VarSymb × VarType := ⟨v1'_sym, v1.2⟩
    have hv1'_pe_V' : v1'.1 ∉ VarCtx_to_VarSymbs pe_V := hv1'_pe_V
    have hv1'v2_ne : v1'.1 ≠ v2.1 := hv1'_v2
    let new_pe_W₁ : VarCtx :=
      VarCtx_insert_twice v1' v2 pe_V hv1'_pe_V' hv2 hv1'v2_ne
    have h_body1_cast :
        VarCtx_insert ⟨v1'_sym, v1.2⟩ (VarCtx_insert v2 pe_V hv2) hv1'_V_v2 =
        new_pe_W₁ := by
      apply VarCtx_ext; rfl
    let body1_cast : WFF σ new_pe_W₁ := h_body1_cast ▸ body1
    have hxv_new_pe_W₁ : xv.1 ∉ VarCtx_to_VarSymbs new_pe_W₁ := by
      intro h
      obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h
      change q ∈ insert v1' (insert v2 pe_V.1) at hq_in
      rcases Finset.mem_insert.mp hq_in with h_v1 | hq_in'
      · subst h_v1; exact hv1'_xv hq_eq
      · rcases Finset.mem_insert.mp hq_in' with h_v2 | h_pe
        · subst h_v2; exact hxv_ne_v2 hq_eq.symm
        · exact hxv_pe_V (Finset.mem_image.mpr ⟨q, h_pe, hq_eq⟩)
    let body_ext := WFF.ctx_ext xv hxv_new_pe_W₁ body1_cast
    have hv1'_pe_ext : v1'.1 ∉ VarCtx_to_VarSymbs
        (VarCtx_insert xv pe_V hxv_pe_V) :=
      not_mem_VarSymbs_insert hv1'_xv hv1'_pe_V'
    have hv2_pe_ext : v2.1 ∉ VarCtx_to_VarSymbs
        (VarCtx_insert xv pe_V hxv_pe_V) :=
      not_mem_VarSymbs_insert (fun h => hxv_ne_v2 h.symm) hv2
    have hz_pe_ext : z ∉ VarCtx_to_VarSymbs
        (VarCtx_insert xv pe_V hxv_pe_V) :=
      not_mem_VarSymbs_insert (fun h => hxv_ne_z h.symm) hz
    have h_ctx_eq :
        VarCtx_insert xv new_pe_W₁ hxv_new_pe_W₁ =
        VarCtx_insert_twice v1' v2 (VarCtx_insert xv pe_V hxv_pe_V)
          hv1'_pe_ext hv2_pe_ext hv1'v2_ne := by
      apply VarCtx_ext
      change insert xv (insert v1' (insert v2 pe_V.1))
           = insert v1' (insert v2 (insert xv pe_V.1))
      rw [Finset.insert_comm xv v1', Finset.insert_comm xv v2]
    let body_cast : WFF σ (VarCtx_insert_twice v1' v2
        (VarCtx_insert xv pe_V hxv_pe_V) hv1'_pe_ext hv2_pe_ext hv1'v2_ne) :=
      h_ctx_eq ▸ body_ext
    have h_w2_eq :
        VarCtx_insert ⟨z, .VTypeProd v1'.2 v2.2⟩
          (VarCtx_insert xv pe_V hxv_pe_V) hz_pe_ext =
        VarCtx_insert xv V hxv := by
      apply VarCtx_ext
      have hfst : V.1 = insert (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType) pe_V.1 :=
        (congrArg PSigma.fst w2eq).symm
      change insert (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType)
               (insert xv pe_V.1) = insert xv V.1
      rw [hfst, Finset.insert_comm]
    exact WFF.pairElim v1' v2 z hv1'_pe_ext hv2_pe_ext hv1'v2_ne hz_pe_ext rfl
      h_w2_eq body_cast
  by_cases h_col_v2 : xv.1 = v2.1
  · -- Collision on v2.
    have hxv_ne_v1 : xv.1 ≠ v1.1 := h_col_v1
    let avoid_v2 : Finset VarSymb :=
      VarCtx_to_VarSymbs pe_V ∪ {xv.1, v1.1, z} ∪ WFF.boundVars body
    let v2'_sym : VarSymb := VarSymb.fresh avoid_v2
    have hv2'_avoid : v2'_sym ∉ avoid_v2 := VarSymb.fresh_not_mem _
    have hv2'_pe_V : v2'_sym ∉ VarCtx_to_VarSymbs pe_V := fun h =>
      hv2'_avoid (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hv2'_xv : v2'_sym ≠ xv.1 := fun h => hv2'_avoid
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_insert.mpr (Or.inl h))))
    have hv2'_v1 : v2'_sym ≠ v1.1 := fun h => hv2'_avoid
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h)))))
    have hv2'_body : v2'_sym ∉ WFF.boundVars body := fun h =>
      hv2'_avoid (Finset.mem_union_right _ h)
    have hv2_V_v1 : v2.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v1 pe_V hv1) :=
      not_mem_VarSymbs_insert (fun h => hv1v2 h.symm) hv2
    have hv2'_V_v1 : v2'_sym ∉ VarCtx_to_VarSymbs
        (VarCtx_insert v1 pe_V hv1) :=
      not_mem_VarSymbs_insert hv2'_v1 hv2'_pe_V
    have hWdef2 : pe_W₁ = VarCtx_insert ⟨v2.1, v2.2⟩
        (VarCtx_insert v1 pe_V hv1) hv2_V_v1 := by
      apply VarCtx_ext
      change pe_W₁.1 = insert v2 (insert v1 pe_V.1)
      have hfst : pe_W₁.1 = insert v1 (insert v2 pe_V.1) :=
        (congrArg PSigma.fst w1eq).symm
      rw [hfst, Finset.insert_comm]
    let body2 : WFF σ (VarCtx_insert ⟨v2'_sym, v2.2⟩
        (VarCtx_insert v1 pe_V hv1) hv2'_V_v1) :=
      WFF.rename v2.1 v2'_sym v2.2 (VarCtx_insert v1 pe_V hv1) pe_W₁
        hv2_V_v1 hv2'_V_v1 hWdef2 body hv2'_body
    let v2' : VarSymb × VarType := ⟨v2'_sym, v2.2⟩
    have hv2'_pe_V' : v2'.1 ∉ VarCtx_to_VarSymbs pe_V := hv2'_pe_V
    have hv1v2'_ne : v1.1 ≠ v2'.1 := fun h => hv2'_v1 h.symm
    let new_pe_W₁ : VarCtx :=
      VarCtx_insert_twice v1 v2' pe_V hv1 hv2'_pe_V' hv1v2'_ne
    have h_body2_cast :
        VarCtx_insert ⟨v2'_sym, v2.2⟩ (VarCtx_insert v1 pe_V hv1) hv2'_V_v1 =
        new_pe_W₁ := by
      apply VarCtx_ext
      change insert (⟨v2'_sym, v2.2⟩ : VarSymb × VarType) (insert v1 pe_V.1)
           = insert v1 (insert (⟨v2'_sym, v2.2⟩ : VarSymb × VarType) pe_V.1)
      exact Finset.insert_comm _ _ _
    let body2_cast : WFF σ new_pe_W₁ := h_body2_cast ▸ body2
    have hxv_new_pe_W₁ : xv.1 ∉ VarCtx_to_VarSymbs new_pe_W₁ := by
      intro h
      obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h
      change q ∈ insert v1 (insert v2' pe_V.1) at hq_in
      rcases Finset.mem_insert.mp hq_in with h_v1 | hq_in'
      · subst h_v1; exact hxv_ne_v1 hq_eq.symm
      · rcases Finset.mem_insert.mp hq_in' with h_v2 | h_pe
        · subst h_v2; exact hv2'_xv hq_eq
        · exact hxv_pe_V (Finset.mem_image.mpr ⟨q, h_pe, hq_eq⟩)
    let body_ext := WFF.ctx_ext xv hxv_new_pe_W₁ body2_cast
    have hv1_pe_ext : v1.1 ∉ VarCtx_to_VarSymbs
        (VarCtx_insert xv pe_V hxv_pe_V) :=
      not_mem_VarSymbs_insert (fun h => hxv_ne_v1 h.symm) hv1
    have hv2'_pe_ext : v2'.1 ∉ VarCtx_to_VarSymbs
        (VarCtx_insert xv pe_V hxv_pe_V) :=
      not_mem_VarSymbs_insert hv2'_xv hv2'_pe_V'
    have hz_pe_ext : z ∉ VarCtx_to_VarSymbs
        (VarCtx_insert xv pe_V hxv_pe_V) :=
      not_mem_VarSymbs_insert (fun h => hxv_ne_z h.symm) hz
    have h_ctx_eq :
        VarCtx_insert xv new_pe_W₁ hxv_new_pe_W₁ =
        VarCtx_insert_twice v1 v2' (VarCtx_insert xv pe_V hxv_pe_V)
          hv1_pe_ext hv2'_pe_ext hv1v2'_ne := by
      apply VarCtx_ext
      change insert xv (insert v1 (insert v2' pe_V.1))
           = insert v1 (insert v2' (insert xv pe_V.1))
      rw [Finset.insert_comm xv v1, Finset.insert_comm xv v2']
    let body_cast : WFF σ (VarCtx_insert_twice v1 v2'
        (VarCtx_insert xv pe_V hxv_pe_V) hv1_pe_ext hv2'_pe_ext hv1v2'_ne) :=
      h_ctx_eq ▸ body_ext
    have h_w2_eq :
        VarCtx_insert ⟨z, .VTypeProd v1.2 v2'.2⟩
          (VarCtx_insert xv pe_V hxv_pe_V) hz_pe_ext =
        VarCtx_insert xv V hxv := by
      apply VarCtx_ext
      have hfst : V.1 = insert (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType) pe_V.1 :=
        (congrArg PSigma.fst w2eq).symm
      change insert (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType)
               (insert xv pe_V.1) = insert xv V.1
      rw [hfst, Finset.insert_comm]
    exact WFF.pairElim v1 v2' z hv1_pe_ext hv2'_pe_ext hv1v2'_ne hz_pe_ext rfl
      h_w2_eq body_cast
  -- No collision.
  have hxv_ne_v1 : xv.1 ≠ v1.1 := h_col_v1
  have hxv_ne_v2 : xv.1 ≠ v2.1 := h_col_v2
  have hxv_pe_W₁ : xv.1 ∉ VarCtx_to_VarSymbs pe_W₁ := by
    intro h
    rw [← w1eq] at h
    obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h
    change q ∈ insert v1 (insert v2 pe_V.1) at hq_in
    rcases Finset.mem_insert.mp hq_in with h_v1 | hq_in'
    · exact hxv_ne_v1 (h_v1 ▸ hq_eq).symm
    · rcases Finset.mem_insert.mp hq_in' with h_v2 | h_pe
      · exact hxv_ne_v2 (h_v2 ▸ hq_eq).symm
      · exact hxv_pe_V (Finset.mem_image.mpr ⟨q, h_pe, hq_eq⟩)
  let body_ext := WFF.ctx_ext xv hxv_pe_W₁ body
  have hv1_pe_ext : v1.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv pe_V hxv_pe_V) :=
    not_mem_VarSymbs_insert (fun h => hxv_ne_v1 h.symm) hv1
  have hv2_pe_ext : v2.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv pe_V hxv_pe_V) :=
    not_mem_VarSymbs_insert (fun h => hxv_ne_v2 h.symm) hv2
  have hz_pe_ext : z ∉ VarCtx_to_VarSymbs (VarCtx_insert xv pe_V hxv_pe_V) :=
    not_mem_VarSymbs_insert (fun h => hxv_ne_z h.symm) hz
  have h_ctx_eq :
      VarCtx_insert xv pe_W₁ hxv_pe_W₁ =
      VarCtx_insert_twice v1 v2 (VarCtx_insert xv pe_V hxv_pe_V)
        hv1_pe_ext hv2_pe_ext hv1v2 := by
    apply VarCtx_ext
    have hfst : pe_W₁.1 = insert v1 (insert v2 pe_V.1) :=
      (congrArg PSigma.fst w1eq).symm
    change insert xv pe_W₁.1
         = insert v1 (insert v2 (insert xv pe_V.1))
    rw [hfst, Finset.insert_comm xv v1, Finset.insert_comm xv v2]
  let body_cast : WFF σ
      (VarCtx_insert_twice v1 v2 (VarCtx_insert xv pe_V hxv_pe_V)
        hv1_pe_ext hv2_pe_ext hv1v2) := h_ctx_eq ▸ body_ext
  have h_w2_eq :
      VarCtx_insert ⟨z, .VTypeProd v1.2 v2.2⟩
        (VarCtx_insert xv pe_V hxv_pe_V) hz_pe_ext =
      VarCtx_insert xv V hxv := by
    apply VarCtx_ext
    have hfst : V.1 = insert (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType) pe_V.1 :=
      (congrArg PSigma.fst w2eq).symm
    change insert (⟨z, .VTypeProd v1.2 v2.2⟩ : VarSymb × VarType)
             (insert xv pe_V.1)
         = insert xv V.1
    rw [hfst, Finset.insert_comm]
  exact WFF.pairElim v1 v2 z hv1_pe_ext hv2_pe_ext hv1v2 hz_pe_ext rfl
    h_w2_eq body_cast
termination_by (sizeOf xv.2, 1 + WFF.numNodes body, 0)
decreasing_by
  all_goals (refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
             try simp only [WFF.numNodes_rename, WFF.numNodes_ctx_cast]
             omega)

end

-- Freshness helper for the `.dia` arm of `WFF.diaCount_ctx_ext` and similar
-- lemmas: from `xv.1 ∉ V` and `dia_subset V_inner ⊆ V`, derive that xv.1 is
-- fresh in (insert x_t V_inner), so it can be used as the ctx_ext target.
private lemma WFF.dia_hxv_outer {V V_inner : VarCtx}
    {xv x_t : VarSymb × VarType}
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (hx_t : x_t.1 ∉ VarCtx_to_VarSymbs V_inner)
    (hsub : (VarCtx_dia x_t V_inner hx_t).1 ⊆ V.1) :
    xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x_t V_inner hx_t) := by
  have hxv_inner : xv.1 ∉ VarCtx_to_VarSymbs V_inner := by
    intro h_in_inner
    apply hxv
    obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
    cases q with
    | mk qv qT =>
      have hbox_in_inner : (⟨qv, qT.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
        Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩
      have hbox_in_dia : (⟨qv, qT.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
        rw [VarCtx_dia_fst]
        exact Finset.mem_insert_of_mem hbox_in_inner
      exact Finset.mem_image.mpr ⟨_, hsub hbox_in_dia, hq_eq⟩
  have hxv_ne_x_t : xv.1 ≠ x_t.1 := by
    intro h_eq
    apply hxv
    have hdia_in : (⟨x_t.1, x_t.2.VTypeDia⟩ : VarSymb × VarType)
                    ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
      rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
    exact Finset.mem_image.mpr ⟨_, hsub hdia_in, h_eq.symm⟩
  exact not_mem_VarSymbs_insert hxv_ne_x_t hxv_inner

-- `WFF.ctx_ext` preserves `diaCount`.  2-member mutual block: the dispatcher
-- inlines every arm (no further helper dispatch) and the only mutual
-- companion is `WFF.diaCount_ctx_ext_pe_arm`, which mirrors
-- `WFF.ctx_ext_pe_arm`'s 3-branch structure (collision on v1, collision on v2,
-- no collision).  Earlier attempts with 5+ member mutual blocks crashed the
-- elaborator with 0xC0000005; inlining keeps the mutual block tractable.
-- Termination: lex `(sizeOf xv.2, WFF.numNodes φ, phase)`, mirror of
-- `WFF.ctx_ext` (phase 1) + `WFF.ctx_ext_pe_arm` (phase 0).
mutual

theorem WFF.diaCount_ctx_ext {σ : Signature} {V : VarCtx}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ V) :
    WFF.diaCount (WFF.ctx_ext xv hxv φ) = WFF.diaCount φ := by
  match φ with
  | .atom R =>
      have ih := Rel.diaCount_ctx_ext xv hxv R
      unfold WFF.ctx_ext
      simp only [WFF.diaCount]
      exact ih
  | .top => unfold WFF.ctx_ext; rfl
  | .bot => unfold WFF.ctx_ext; rfl
  | .and φ' ψ =>
      have ih1 := WFF.diaCount_ctx_ext xv hxv φ'
      have ih2 := WFF.diaCount_ctx_ext xv hxv ψ
      unfold WFF.ctx_ext
      simp only [WFF.diaCount]
      omega
  | .or φ' ψ =>
      have ih1 := WFF.diaCount_ctx_ext xv hxv φ'
      have ih2 := WFF.diaCount_ctx_ext xv hxv ψ
      unfold WFF.ctx_ext
      simp only [WFF.diaCount]
      omega
  | .imp φ' ψ =>
      have ih1 := WFF.diaCount_ctx_ext xv hxv φ'
      have ih2 := WFF.diaCount_ctx_ext xv hxv ψ
      unfold WFF.ctx_ext
      simp only [WFF.diaCount]
      omega
  | .eq s t =>
      have ih_s := Term.diaCount_ctx_ext xv hxv s
      have ih_t := Term.diaCount_ctx_ext xv hxv t
      unfold WFF.ctx_ext
      simp only [WFF.diaCount]
      omega
  | @WFF.all _ _ x hx ψ =>
      unfold WFF.ctx_ext
      split_ifs with h_col
      · simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
        rw [WFF.diaCount_ctx_ext]
        exact WFF.diaCount_rename _ _ _ _ _ _ _ _ ψ _
      · simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
        exact WFF.diaCount_ctx_ext xv _ ψ
  | @WFF.ex _ _ x hx ψ =>
      unfold WFF.ctx_ext
      split_ifs with h_col
      · simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
        rw [WFF.diaCount_ctx_ext]
        exact WFF.diaCount_rename _ _ _ _ _ _ _ _ ψ _
      · simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
        exact WFF.diaCount_ctx_ext xv _ ψ
  | .box ψ hsub h_no_extras =>
      rename_i V_inner
      unfold WFF.ctx_ext
      split
      · rename_i U' h_xv2
        have h_sz : sizeOf U' < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        simp only [WFF.diaCount]
        exact WFF.diaCount_ctx_ext ⟨xv.1, U'⟩ _ ψ
      · rfl
      · rfl
      · rfl
      · rename_i a b h_xv2
        have h_a_sz : sizeOf a < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        have h_b_sz : sizeOf b < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        rw [WFF.diaCount_ctx_cast, WFF.diaCount_pairElim_gen,
            WFF.diaCount_ctx_cast]
        rw [WFF.diaCount_ctx_ext ⟨_, b⟩ _ _]
        exact WFF.diaCount_ctx_ext ⟨_, a⟩ _ _
  | .dia x_t hx_t ψ hsub h_no_extras =>
      rename_i V_inner
      have hxv_outer := WFF.dia_hxv_outer hxv hx_t hsub
      unfold WFF.ctx_ext
      split
      · rename_i U' h_xv2
        have h_sz : sizeOf U' < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
        have ih := WFF.diaCount_ctx_ext ⟨xv.1, U'⟩ hxv_outer ψ
        omega
      · rfl
      · rfl
      · rfl
      · rename_i a b h_xv2
        have h_a_sz : sizeOf a < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        have h_b_sz : sizeOf b < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        rw [WFF.diaCount_ctx_cast, WFF.diaCount_pairElim_gen,
            WFF.diaCount_ctx_cast]
        rw [WFF.diaCount_ctx_ext ⟨_, b⟩ _ _]
        exact WFF.diaCount_ctx_ext ⟨_, a⟩ _ _
  | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body =>
      rename_i pe_V pe_W₁
      exact WFF.diaCount_ctx_ext_pe_arm xv hxv
        v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body
termination_by (sizeOf xv.2, WFF.numNodes φ, 1)
decreasing_by
  all_goals first
    | (refine Prod.Lex.right _ (Prod.Lex.right _ ?_); decide)
    | (refine Prod.Lex.left _ _ ?_; assumption)
    | (refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
       try simp only [WFF.numNodes, WFF.numNodes_rename, WFF.numNodes_ctx_cast]
       omega)

theorem WFF.diaCount_ctx_ext_pe_arm {σ : Signature} {V pe_V pe_W₁ : VarCtx}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (v1 v2 : VarSymb × VarType) (z : VarSymb)
    (hv1 : v1.1 ∉ VarCtx_to_VarSymbs pe_V) (hv2 : v2.1 ∉ VarCtx_to_VarSymbs pe_V)
    (hv1v2 : v1.1 ≠ v2.1) (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w1eq : VarCtx_insert_twice v1 v2 pe_V hv1 hv2 hv1v2 = pe_W₁)
    (w2eq : VarCtx_insert ⟨z, .VTypeProd v1.2 v2.2⟩ pe_V hz = V)
    (body : WFF σ pe_W₁) :
    WFF.diaCount (WFF.ctx_ext xv hxv
        (@WFF.pair_elim σ pe_V pe_W₁ V v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body))
      = WFF.diaCount (@WFF.pair_elim σ pe_V pe_W₁ V
            v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body) := by
  unfold WFF.ctx_ext
  unfold WFF.ctx_ext_pe_arm
  split_ifs with h_col_v1 h_col_v2
  · simp only [WFF.diaCount_pairElim_gen, WFF.diaCount_ctx_cast, WFF.diaCount]
    rw [WFF.diaCount_ctx_ext]
    try simp only [WFF.diaCount_ctx_cast]
    exact WFF.diaCount_rename _ _ _ _ _ _ _ _ body _
  · simp only [WFF.diaCount_pairElim_gen, WFF.diaCount_ctx_cast, WFF.diaCount]
    rw [WFF.diaCount_ctx_ext]
    try simp only [WFF.diaCount_ctx_cast]
    exact WFF.diaCount_rename _ _ _ _ _ _ _ _ body _
  · simp only [WFF.diaCount_pairElim_gen, WFF.diaCount_ctx_cast, WFF.diaCount]
    exact WFF.diaCount_ctx_ext _ _ _
termination_by (sizeOf xv.2, 1 + WFF.numNodes body, 0)
decreasing_by
  all_goals (refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
             try simp only [WFF.numNodes_rename, WFF.numNodes_ctx_cast]
             omega)

end

-- `WFF.ctx_ext` preserves `binderPairDepth`.  Same 2-member mutual block
-- structure as `WFF.diaCount_ctx_ext`: dispatcher inlines every arm and the
-- only mutual companion is `_pe_arm`.  Differences from `diaCount_ctx_ext`:
--   * `.atom`/`.eq`: binderPairDepth = 0 (no Rel/Term-level lemma needed).
--   * `.all`/`.ex`/`.dia`: binderPairDepth adds `x.2.pairDepth` instead of `1`.
mutual

theorem WFF.binderPairDepth_ctx_ext {σ : Signature} {V : VarCtx}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ V) :
    WFF.binderPairDepth (WFF.ctx_ext xv hxv φ) = WFF.binderPairDepth φ := by
  match φ with
  | .atom _ =>
      unfold WFF.ctx_ext
      simp only [WFF.binderPairDepth]
  | .top => unfold WFF.ctx_ext; rfl
  | .bot => unfold WFF.ctx_ext; rfl
  | .and φ' ψ =>
      have ih1 := WFF.binderPairDepth_ctx_ext xv hxv φ'
      have ih2 := WFF.binderPairDepth_ctx_ext xv hxv ψ
      unfold WFF.ctx_ext
      simp only [WFF.binderPairDepth]
      omega
  | .or φ' ψ =>
      have ih1 := WFF.binderPairDepth_ctx_ext xv hxv φ'
      have ih2 := WFF.binderPairDepth_ctx_ext xv hxv ψ
      unfold WFF.ctx_ext
      simp only [WFF.binderPairDepth]
      omega
  | .imp φ' ψ =>
      have ih1 := WFF.binderPairDepth_ctx_ext xv hxv φ'
      have ih2 := WFF.binderPairDepth_ctx_ext xv hxv ψ
      unfold WFF.ctx_ext
      simp only [WFF.binderPairDepth]
      omega
  | .eq _ _ =>
      unfold WFF.ctx_ext
      simp only [WFF.binderPairDepth]
  | @WFF.all _ _ x hx ψ =>
      unfold WFF.ctx_ext
      split_ifs with h_col
      · simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
        congr 1
        rw [WFF.binderPairDepth_ctx_ext]
        exact WFF.binderPairDepth_rename _ _ _ _ _ _ _ _ ψ _
      · simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
        congr 1
        exact WFF.binderPairDepth_ctx_ext xv _ ψ
  | @WFF.ex _ _ x hx ψ =>
      unfold WFF.ctx_ext
      split_ifs with h_col
      · simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
        congr 1
        rw [WFF.binderPairDepth_ctx_ext]
        exact WFF.binderPairDepth_rename _ _ _ _ _ _ _ _ ψ _
      · simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
        congr 1
        exact WFF.binderPairDepth_ctx_ext xv _ ψ
  | .box ψ hsub h_no_extras =>
      rename_i V_inner
      unfold WFF.ctx_ext
      split
      · rename_i U' h_xv2
        have h_sz : sizeOf U' < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        simp only [WFF.binderPairDepth]
        exact WFF.binderPairDepth_ctx_ext ⟨xv.1, U'⟩ _ ψ
      · rfl
      · rfl
      · rfl
      · rename_i a b h_xv2
        have h_a_sz : sizeOf a < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        have h_b_sz : sizeOf b < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_pairElim_gen,
            WFF.binderPairDepth_ctx_cast]
        rw [WFF.binderPairDepth_ctx_ext ⟨_, b⟩ _ _]
        exact WFF.binderPairDepth_ctx_ext ⟨_, a⟩ _ _
  | .dia x_t hx_t ψ hsub h_no_extras =>
      rename_i V_inner
      have hxv_outer := WFF.dia_hxv_outer hxv hx_t hsub
      unfold WFF.ctx_ext
      split
      · rename_i U' h_xv2
        have h_sz : sizeOf U' < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
        have ih := WFF.binderPairDepth_ctx_ext ⟨xv.1, U'⟩ hxv_outer ψ
        omega
      · rfl
      · rfl
      · rfl
      · rename_i a b h_xv2
        have h_a_sz : sizeOf a < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        have h_b_sz : sizeOf b < sizeOf xv.2 := by rw [h_xv2]; simp +arith
        rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_pairElim_gen,
            WFF.binderPairDepth_ctx_cast]
        rw [WFF.binderPairDepth_ctx_ext ⟨_, b⟩ _ _]
        exact WFF.binderPairDepth_ctx_ext ⟨_, a⟩ _ _
  | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body =>
      rename_i pe_V pe_W₁
      exact WFF.binderPairDepth_ctx_ext_pe_arm xv hxv
        v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body
termination_by (sizeOf xv.2, WFF.numNodes φ, 1)
decreasing_by
  all_goals first
    | (refine Prod.Lex.right _ (Prod.Lex.right _ ?_); decide)
    | (refine Prod.Lex.left _ _ ?_; assumption)
    | (refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
       try simp only [WFF.numNodes, WFF.numNodes_rename, WFF.numNodes_ctx_cast]
       omega)

theorem WFF.binderPairDepth_ctx_ext_pe_arm {σ : Signature}
    {V pe_V pe_W₁ : VarCtx}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (v1 v2 : VarSymb × VarType) (z : VarSymb)
    (hv1 : v1.1 ∉ VarCtx_to_VarSymbs pe_V) (hv2 : v2.1 ∉ VarCtx_to_VarSymbs pe_V)
    (hv1v2 : v1.1 ≠ v2.1) (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w1eq : VarCtx_insert_twice v1 v2 pe_V hv1 hv2 hv1v2 = pe_W₁)
    (w2eq : VarCtx_insert ⟨z, .VTypeProd v1.2 v2.2⟩ pe_V hz = V)
    (body : WFF σ pe_W₁) :
    WFF.binderPairDepth (WFF.ctx_ext xv hxv
        (@WFF.pair_elim σ pe_V pe_W₁ V v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body))
      = WFF.binderPairDepth (@WFF.pair_elim σ pe_V pe_W₁ V
            v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body) := by
  unfold WFF.ctx_ext
  unfold WFF.ctx_ext_pe_arm
  split_ifs with h_col_v1 h_col_v2
  · simp only [WFF.binderPairDepth_pairElim_gen, WFF.binderPairDepth_ctx_cast,
      WFF.binderPairDepth]
    rw [WFF.binderPairDepth_ctx_ext]
    try simp only [WFF.binderPairDepth_ctx_cast]
    exact WFF.binderPairDepth_rename _ _ _ _ _ _ _ _ body _
  · simp only [WFF.binderPairDepth_pairElim_gen, WFF.binderPairDepth_ctx_cast,
      WFF.binderPairDepth]
    rw [WFF.binderPairDepth_ctx_ext]
    try simp only [WFF.binderPairDepth_ctx_cast]
    exact WFF.binderPairDepth_rename _ _ _ _ _ _ _ _ body _
  · simp only [WFF.binderPairDepth_pairElim_gen, WFF.binderPairDepth_ctx_cast,
      WFF.binderPairDepth]
    exact WFF.binderPairDepth_ctx_ext _ _ _
termination_by (sizeOf xv.2, 1 + WFF.numNodes body, 0)
decreasing_by
  all_goals (refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
             try simp only [WFF.numNodes_rename, WFF.numNodes_ctx_cast]
             omega)

end

-- The finset version of context extension, for use with contexts
def WFF.ctx_ext_Finset {σ : Signature} {V : VarCtx}
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V)
    (Γ : Finset (WFF σ V)) : Finset (WFF σ (VarCtx_insert xv V hxv)) :=
  Finset.image (WFF.ctx_ext xv hxv) Γ

/-! ### Unpair -/

-- Translate a WFF from a "joined" context `W₁ = V + ⟨z, V1×V2⟩` to a "split"
-- Case A helper for `WFF.unpair`'s `.pair_elim` arm.  Mirrors
-- `Term.unpair_pe_caseA`: extracts the `subst z'` / `subst pe_V` / `obtain
-- ⟨rfl, rfl⟩` chain into a standalone function so that `WFF.unpair` itself
-- remains eq-lemma-compatible.
def WFF.unpair_pe_caseA {σ : Signature}
    (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
    (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (pe_V pe_W₁ : VarCtx)
    (v₁ v₂ : VarSymb × VarType) (z' : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs pe_V)
    (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs pe_V)
    (hv₁v₂_inner : v₁.1 ≠ v₂.1)
    (hz' : z' ∉ VarCtx_to_VarSymbs pe_V)
    (w₁_eq : VarCtx_insert_twice v₁ v₂ pe_V hv₁ hv₂ hv₁v₂_inner = pe_W₁)
    (w₂_eq : VarCtx_insert ⟨z', v₁.2.VTypeProd v₂.2⟩ pe_V hz' = W₁)
    (inner_wff : WFF σ pe_W₁)
    (h_v1_nb_inner : v1 ∉ WFF.boundVars inner_wff)
    (h_v2_nb_inner : v2 ∉ WFF.boundVars inner_wff)
    (_h1 : v1 ∉ (insert v₁.1 (insert v₂.1 (insert z' (WFF.boundVars inner_wff)))))
    (_h2 : v2 ∉ (insert v₁.1 (insert v₂.1 (insert z' (WFF.boundVars inner_wff)))))
    (h_case : (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩)
    : { t : WFF σ W₂ // WFF.diaCount t = WFF.diaCount inner_wff ∧
                         WFF.binderPairDepth t = WFF.binderPairDepth inner_wff } := by
  have h_z'_eq : z' = z := congrArg Prod.fst h_case
  have h_type_eq : (VarType.VTypeProd v₁.2 v₂.2) = V1.VTypeProd V2 :=
    congrArg Prod.snd h_case
  subst z'
  obtain ⟨rfl, rfl⟩ := VarType.VTypeProd.inj h_type_eq
  have h_pe_V_eq_V : pe_V = V := by
    apply VarCtx_ext
    have h_W_eq : insert (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) pe_V.1
               = insert ⟨z, v₁.2.VTypeProd v₂.2⟩ V.1 :=
      congrArg PSigma.fst (w₂_eq.trans W₁def)
    have h_not_in_pe : (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∉ pe_V.1 :=
      fun h => hz' (Finset.mem_image.mpr ⟨_, h, rfl⟩)
    have h_not_in_V : (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∉ V.1 :=
      fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
    change pe_V.1 = V.1
    rw [← Finset.erase_insert h_not_in_pe, h_W_eq, Finset.erase_insert h_not_in_V]
  subst pe_V
  have h_v1_ne_v₂_1 : v1 ≠ v₂.1 := fun heq =>
    _h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
  have h_v2_ne_v₁_1 : v2 ≠ v₁.1 := fun heq =>
    _h2 (Finset.mem_insert.mpr (Or.inl heq))
  have h_v1_fresh_in_iv₂ :
      v1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂) :=
    not_mem_VarSymbs_insert h_v1_ne_v₂_1 hv1
  have h_v₁1_fresh_in_iv₂ :
      v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂) :=
    not_mem_VarSymbs_insert hv₁v₂_inner hv₁
  have w₁_decomp : pe_W₁ =
      VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) h_v₁1_fresh_in_iv₂ :=
    w₁_eq.symm.trans (VarCtx_ext _ _ rfl)
  let renamed_1 := WFF.rename v₁.1 v1 v₁.2 (VarCtx_insert v₂ V hv₂) pe_W₁
                     h_v₁1_fresh_in_iv₂ h_v1_fresh_in_iv₂ w₁_decomp
                     inner_wff h_v1_nb_inner
  have h_v2_fresh_in_iv1 :
      v2 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) :=
    not_mem_VarSymbs_insert hv1v2.symm hv2
  have h_v₂1_fresh_in_iv1 :
      v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) :=
    not_mem_VarSymbs_insert h_v1_ne_v₂_1.symm hv₂
  have ctx_swap_1 :
      VarCtx_insert ⟨v1, v₁.2⟩ (VarCtx_insert v₂ V hv₂) h_v1_fresh_in_iv₂ =
      VarCtx_insert v₂ (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) h_v₂1_fresh_in_iv1 :=
    VarCtx_insert_comm h_v1_fresh_in_iv₂ h_v₂1_fresh_in_iv1
  have h_v2_nb_renamed_1 : v2 ∉ WFF.boundVars renamed_1 := fun hmem => by
    have h_sub := WFF.boundVars_rename_subset v₁.1 v1 v₁.2
      (VarCtx_insert v₂ V hv₂) pe_W₁
      h_v₁1_fresh_in_iv₂ h_v1_fresh_in_iv₂ w₁_decomp
      inner_wff h_v1_nb_inner
    rcases Finset.mem_insert.mp (h_sub hmem) with heq | hin
    · exact hv1v2.symm heq
    · exact h_v2_nb_inner hin
  let renamed_2 := WFF.rename v₂.1 v2 v₂.2 (VarCtx_insert ⟨v1, v₁.2⟩ V hv1)
                     (VarCtx_insert ⟨v1, v₁.2⟩ (VarCtx_insert v₂ V hv₂) h_v1_fresh_in_iv₂)
                     h_v₂1_fresh_in_iv1 h_v2_fresh_in_iv1 ctx_swap_1
                     renamed_1 h_v2_nb_renamed_1
  have ctx_final :
      VarCtx_insert ⟨v2, v₂.2⟩ (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) h_v2_fresh_in_iv1 =
      VarCtx_insert_twice ⟨v1, v₁.2⟩ ⟨v2, v₂.2⟩ V hv1 hv2 hv1v2 :=
    VarCtx_ext _ _ (by
      change insert ⟨v2, v₂.2⟩ (insert (⟨v1, v₁.2⟩ : VarSymb × VarType) V.1) =
             insert ⟨v1, v₁.2⟩ (insert ⟨v2, v₂.2⟩ V.1)
      exact Finset.insert_comm _ _ _)
  refine ⟨W₂def ▸ ctx_final ▸ renamed_2, ?_, ?_⟩
  · rw [WFF.diaCount_ctx_cast, WFF.diaCount_ctx_cast,
        WFF.diaCount_rename, WFF.diaCount_rename]
  · rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_cast,
        WFF.binderPairDepth_rename, WFF.binderPairDepth_rename]

-- context `W₂ = V + {v1, v2}` (with v1 : V1, v2 : V2).  Mirrors `Term.unpair`:
-- structural recursion through WFF constructors, delegating to `Rel.unpair`
-- for atomic relations and `Term.unpair` for equality terms.  `z` cannot
-- appear inside `.box`/`.dia` modal bodies (z's type is `.VTypeProd`, but
-- `VarCtx_box`/`VarCtx_dia` images only contain `.VTypeBox`/`.VTypeDia`
-- entries), so those arms are pass-through.  The `.pair_elim` arm has two
-- sub-cases (Case A: `z' = z`, drop the constructor and rename inner v₁,
-- v₂ to v1, v2; Case B: recurse on inner) — same pattern as `Term.unpair`.
def WFF.unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
    (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (input : WFF σ W₁)
    (h_v1_nb : v1 ∉ WFF.boundVars input)
    (h_v2_nb : v2 ∉ WFF.boundVars input)
    : WFF σ W₂ := by
  match input, h_v1_nb, h_v2_nb with
  | .atom R, h1, h2 =>
      exact .atom
        (Rel.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def R h1 h2)
  | .top, _, _ => exact .top
  | .bot, _, _ => exact .bot
  | .and φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      exact .and
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ)
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ)
  | .or φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      exact .or
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ)
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ)
  | .imp φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      exact .imp
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ)
        (WFF.unpair z V1 V2 v1 v2 V W₁ W₂ hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ)
  | .eq s t, h1, h2 =>
      have h1_s : v1 ∉ Term.boundVars s :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_t : v1 ∉ Term.boundVars t :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_s : v2 ∉ Term.boundVars s :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_t : v2 ∉ Term.boundVars t :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      exact .eq
        (Term.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def s h1_s h2_s)
        (Term.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def t h1_t h2_t)
  | @WFF.all _ _ x hx ψ, h1, h2 =>
      -- Recurse on ψ at the extended context (insert x V, insert x W₁, insert x W₂).
      have h_v1_ne_x : v1 ≠ x.1 := fun heq =>
        h1 (Finset.mem_insert.mpr (Or.inl heq))
      have h_v2_ne_x : v2 ≠ x.1 := fun heq =>
        h2 (Finset.mem_insert.mpr (Or.inl heq))
      have h_v1_nb_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_insert_of_mem hmem)
      have h_v2_nb_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_insert_of_mem hmem)
      -- x.1 ∉ symbols V (from hx via W₁def: W₁ = insert ⟨z, _⟩ V; hx says x.1 ∉ W₁).
      have hx_W₁ : x.1 ∉ VarCtx_to_VarSymbs W₁ := hx
      have h_x_ne_z : x.1 ≠ z := by
        intro heq
        apply hx_W₁
        rw [W₁def]
        have h_z_in : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
                        ∈ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz).1 :=
          Finset.mem_insert_self _ _
        exact Finset.mem_image.mpr ⟨_, h_z_in, heq.symm⟩
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := by
        intro hmem
        apply hx_W₁
        rw [W₁def]
        rcases Finset.mem_image.mp hmem with ⟨q, hq_in, hq_eq⟩
        exact Finset.mem_image.mpr ⟨q, Finset.mem_insert_of_mem hq_in, hq_eq⟩
      have hz_inner : z ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => h_x_ne_z h.symm) hz
      have hv1_inner : v1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert h_v1_ne_x hv1
      have hv2_inner : v2 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert h_v2_ne_x hv2
      let W₁_inner : VarCtx := VarCtx_insert ⟨z, V1.VTypeProd V2⟩
        (VarCtx_insert x V hx_V) hz_inner
      let W₂_inner : VarCtx := VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
        (VarCtx_insert x V hx_V) hv1_inner hv2_inner hv1v2
      -- ψ lives at insert x W₁ = insert x (insert ⟨z, _⟩ V), which equals W₁_inner.
      have h_ψ_ctx : VarCtx_insert x W₁ hx = W₁_inner := by
        apply VarCtx_ext
        change insert x W₁.1 = insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) (insert x V.1)
        rw [W₁def]
        change insert x (insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) V.1) = _
        exact Finset.insert_comm _ _ _
      let ψ_cast : WFF σ W₁_inner := h_ψ_ctx ▸ ψ
      have h_v1_nb_ψ_cast : v1 ∉ WFF.boundVars ψ_cast := by
        show v1 ∉ WFF.boundVars (h_ψ_ctx ▸ ψ)
        rw [WFF.boundVars_ctx_cast]; exact h_v1_nb_ψ
      have h_v2_nb_ψ_cast : v2 ∉ WFF.boundVars ψ_cast := by
        show v2 ∉ WFF.boundVars (h_ψ_ctx ▸ ψ)
        rw [WFF.boundVars_ctx_cast]; exact h_v2_nb_ψ
      let ψ_unpaired : WFF σ W₂_inner :=
        WFF.unpair z V1 V2 v1 v2 (VarCtx_insert x V hx_V) W₁_inner W₂_inner
          hz_inner hv1_inner hv2_inner hv1v2 rfl rfl ψ_cast
          h_v1_nb_ψ_cast h_v2_nb_ψ_cast
      -- Now swap inserts so x appears outermost: W₂_inner = insert x W₂.
      have hx_W₂ : x.1 ∉ VarCtx_to_VarSymbs W₂ := by
        rw [W₂def]
        exact not_mem_VarSymbs_insert_twice
          (fun h => h_v1_ne_x h.symm) (fun h => h_v2_ne_x h.symm) hx_V
      have h_swap_ctx : W₂_inner = VarCtx_insert x W₂ hx_W₂ := by
        apply VarCtx_ext
        change insert (⟨v1, V1⟩ : VarSymb × VarType)
                 (insert ⟨v2, V2⟩ (insert x V.1)) =
               insert x W₂.1
        rw [W₂def]
        change _ = insert x (insert (⟨v1, V1⟩ : VarSymb × VarType) (insert ⟨v2, V2⟩ V.1))
        rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) x,
            Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) x]
      exact .all x (hx := hx_W₂) (h_swap_ctx ▸ ψ_unpaired)
  | @WFF.ex _ _ x hx ψ, h1, h2 =>
      -- Symmetric to .all.
      have h_v1_ne_x : v1 ≠ x.1 := fun heq =>
        h1 (Finset.mem_insert.mpr (Or.inl heq))
      have h_v2_ne_x : v2 ≠ x.1 := fun heq =>
        h2 (Finset.mem_insert.mpr (Or.inl heq))
      have h_v1_nb_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_insert_of_mem hmem)
      have h_v2_nb_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_insert_of_mem hmem)
      have hx_W₁ : x.1 ∉ VarCtx_to_VarSymbs W₁ := hx
      have h_x_ne_z : x.1 ≠ z := by
        intro heq
        apply hx_W₁
        rw [W₁def]
        have h_z_in : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
                        ∈ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz).1 :=
          Finset.mem_insert_self _ _
        exact Finset.mem_image.mpr ⟨_, h_z_in, heq.symm⟩
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := by
        intro hmem
        apply hx_W₁
        rw [W₁def]
        rcases Finset.mem_image.mp hmem with ⟨q, hq_in, hq_eq⟩
        exact Finset.mem_image.mpr ⟨q, Finset.mem_insert_of_mem hq_in, hq_eq⟩
      have hz_inner : z ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => h_x_ne_z h.symm) hz
      have hv1_inner : v1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert h_v1_ne_x hv1
      have hv2_inner : v2 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert h_v2_ne_x hv2
      let W₁_inner : VarCtx := VarCtx_insert ⟨z, V1.VTypeProd V2⟩
        (VarCtx_insert x V hx_V) hz_inner
      let W₂_inner : VarCtx := VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
        (VarCtx_insert x V hx_V) hv1_inner hv2_inner hv1v2
      have h_ψ_ctx : VarCtx_insert x W₁ hx = W₁_inner := by
        apply VarCtx_ext
        change insert x W₁.1 = insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) (insert x V.1)
        rw [W₁def]
        change insert x (insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) V.1) = _
        exact Finset.insert_comm _ _ _
      let ψ_cast : WFF σ W₁_inner := h_ψ_ctx ▸ ψ
      have h_v1_nb_ψ_cast : v1 ∉ WFF.boundVars ψ_cast := by
        show v1 ∉ WFF.boundVars (h_ψ_ctx ▸ ψ)
        rw [WFF.boundVars_ctx_cast]; exact h_v1_nb_ψ
      have h_v2_nb_ψ_cast : v2 ∉ WFF.boundVars ψ_cast := by
        show v2 ∉ WFF.boundVars (h_ψ_ctx ▸ ψ)
        rw [WFF.boundVars_ctx_cast]; exact h_v2_nb_ψ
      let ψ_unpaired : WFF σ W₂_inner :=
        WFF.unpair z V1 V2 v1 v2 (VarCtx_insert x V hx_V) W₁_inner W₂_inner
          hz_inner hv1_inner hv2_inner hv1v2 rfl rfl ψ_cast
          h_v1_nb_ψ_cast h_v2_nb_ψ_cast
      have hx_W₂ : x.1 ∉ VarCtx_to_VarSymbs W₂ := by
        rw [W₂def]
        exact not_mem_VarSymbs_insert_twice
          (fun h => h_v1_ne_x h.symm) (fun h => h_v2_ne_x h.symm) hx_V
      have h_swap_ctx : W₂_inner = VarCtx_insert x W₂ hx_W₂ := by
        apply VarCtx_ext
        change insert (⟨v1, V1⟩ : VarSymb × VarType)
                 (insert ⟨v2, V2⟩ (insert x V.1)) =
               insert x W₂.1
        rw [W₂def]
        change _ = insert x (insert (⟨v1, V1⟩ : VarSymb × VarType) (insert ⟨v2, V2⟩ V.1))
        rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) x,
            Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) x]
      exact .ex x (hx := hx_W₂) (h_swap_ctx ▸ ψ_unpaired)
  | .box ψ hsub h_no_box_extras, _, _ =>
      -- `z` is `.VTypeProd`-typed in W₁; `VarCtx_box V_inner` only has
      -- `.VTypeBox`-outer entries.  If V1 or V2 is box-typed, then under
      -- recursive `isBox`, `(V1.VTypeProd V2).isBox = true`, so
      -- `h_no_box_extras` on the original W₁ forces `⟨z, V1×V2⟩` into
      -- `VarCtx_box V_inner` — impossible by constructor mismatch.
      rename_i V_inner
      refine .box ψ ?_ (by
        intro p hp h_box
        rw [W₂def] at hp
        rcases Finset.mem_insert.mp hp with h_eq | hp'
        · subst h_eq
          exfalso
          have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [W₁def]; exact Finset.mem_insert_self _ _
          have hz_box : (V1.VTypeProd V2).isBox = true := by
            simp [VarType.isBox, h_box]
          have hz_in_box := h_no_box_extras _ hz_in_W1 hz_box
          rcases Finset.mem_image.mp hz_in_box with ⟨⟨_, _⟩, _, hveq⟩
          simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
        · rcases Finset.mem_insert.mp hp' with h_eq2 | hp_V
          · subst h_eq2
            exfalso
            have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_self _ _
            have hz_box : (V1.VTypeProd V2).isBox = true := by
              simp [VarType.isBox, h_box]
            have hz_in_box := h_no_box_extras _ hz_in_W1 hz_box
            rcases Finset.mem_image.mp hz_in_box with ⟨⟨_, _⟩, _, hveq⟩
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
          · have hp_W1 : p ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_of_mem hp_V
            exact h_no_box_extras p hp_W1 h_box)
      intro y hy
      rw [W₂def]
      have hy_W : y ∈ W₁.1 := hsub hy
      rw [W₁def] at hy_W
      rcases Finset.mem_insert.mp hy_W with hyz | hyV
      · subst hyz
        rcases Finset.mem_image.mp hy with ⟨_, _, hweq⟩
        simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hweq
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hyV)
  | .dia x hx ψ hsub h_no_box_extras, _, _ =>
      -- Same argument as .box: under recursive `isBox`, V1×V2 box-detected if
      -- V1 or V2 is box; h_no_box_extras then forces ⟨z, V1×V2⟩ into
      -- VarCtx_dia, but neither the x-binder (VTypeDia-outer) nor the
      -- VarCtx_box rest (VTypeBox-outer) entries match VTypeProd.
      rename_i V_inner
      refine .dia x hx ψ ?_ (by
        intro p hp h_box
        rw [W₂def] at hp
        rcases Finset.mem_insert.mp hp with h_eq | hp'
        · subst h_eq
          exfalso
          have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [W₁def]; exact Finset.mem_insert_self _ _
          have hz_box : (V1.VTypeProd V2).isBox = true := by
            simp [VarType.isBox, h_box]
          have hz_in_dia := h_no_box_extras _ hz_in_W1 hz_box
          rcases Finset.mem_insert.mp hz_in_dia with hxeq | hbox
          · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
          · rcases Finset.mem_image.mp hbox with ⟨⟨_, _⟩, _, hveq⟩
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
        · rcases Finset.mem_insert.mp hp' with h_eq2 | hp_V
          · subst h_eq2
            exfalso
            have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_self _ _
            have hz_box : (V1.VTypeProd V2).isBox = true := by
              simp [VarType.isBox, h_box]
            have hz_in_dia := h_no_box_extras _ hz_in_W1 hz_box
            rcases Finset.mem_insert.mp hz_in_dia with hxeq | hbox
            · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
            · rcases Finset.mem_image.mp hbox with ⟨⟨_, _⟩, _, hveq⟩
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
          · have hp_W1 : p ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_of_mem hp_V
            exact h_no_box_extras p hp_W1 h_box)
      intro y hy
      rw [W₂def]
      have hy_W : y ∈ W₁.1 := hsub hy
      rw [W₁def] at hy_W
      rcases Finset.mem_insert.mp hy_W with hyz | hyV
      · subst hyz
        rcases Finset.mem_insert.mp hy with hxeq | hbox
        · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
        · rcases Finset.mem_image.mp hbox with ⟨_, _, hweq⟩
          simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hweq
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hyV)
  | .pair_elim v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff, h1, h2 =>
      rename_i pe_V pe_W₁
      -- Extract freshness conditions from h1/h2.
      have h_v1_nb_inner : v1 ∉ WFF.boundVars inner_wff := fun hmem =>
        h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      have h_v2_nb_inner : v2 ∉ WFF.boundVars inner_wff := fun hmem =>
        h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      by_cases h_case :
          (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩
      · -- Case A: delegate to `WFF.unpair_pe_caseA` helper (subtype return).
        exact (WFF.unpair_pe_caseA z V1 V2 v1 v2 V W₁ W₂
          hz hv1 hv2 hv1v2 W₁def W₂def pe_V pe_W₁ v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner
          hz' w₁_eq w₂_eq inner_wff h_v1_nb_inner h_v2_nb_inner h1 h2 h_case).val
      · -- Case B: ⟨z, V1.VTypeProd V2⟩ must lie in pe_V.  Recurse on inner_wff.
        have h_z_in_pe_V :
            (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ pe_V.1 := by
          have h_z_in_W₁ : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [W₁def]; exact Finset.mem_insert_self _ _
          rw [← w₂_eq] at h_z_in_W₁
          rcases Finset.mem_insert.mp h_z_in_W₁ with h_eq | h_pe_V
          · exact absurd h_eq.symm h_case
          · exact h_pe_V
        let pe_V' := VarCtx_erase pe_V ⟨z, V1.VTypeProd V2⟩
        have hz_pe_V' : z ∉ VarCtx_to_VarSymbs pe_V' :=
          VarCtx_erase_fresh h_z_in_pe_V
        have hv₁_pe_V' : v₁.1 ∉ VarCtx_to_VarSymbs pe_V' :=
          fun hmem => hv₁ (VarCtx_to_VarSymbs_erase_subset hmem)
        have hv₂_pe_V' : v₂.1 ∉ VarCtx_to_VarSymbs pe_V' :=
          fun hmem => hv₂ (VarCtx_to_VarSymbs_erase_subset hmem)
        have h_z_ne_v₁_1 : z ≠ v₁.1 := fun heq =>
          hv₁ (heq ▸ Finset.mem_image.mpr ⟨_, h_z_in_pe_V, rfl⟩)
        have h_z_ne_v₂_1 : z ≠ v₂.1 := fun heq =>
          hv₂ (heq ▸ Finset.mem_image.mpr ⟨_, h_z_in_pe_V, rfl⟩)
        let V_inner_pe :=
          VarCtx_insert_twice v₁ v₂ pe_V' hv₁_pe_V' hv₂_pe_V' hv₁v₂_inner
        have hz_V_inner : z ∉ VarCtx_to_VarSymbs V_inner_pe :=
          not_mem_VarSymbs_insert_twice h_z_ne_v₁_1 h_z_ne_v₂_1 hz_pe_V'
        have h_v1_ne_v₁_1 : v1 ≠ v₁.1 := fun heq =>
          h1 (Finset.mem_insert.mpr (Or.inl heq))
        have h_v1_ne_v₂_1 : v1 ≠ v₂.1 := fun heq =>
          h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
        have h_v2_ne_v₁_1 : v2 ≠ v₁.1 := fun heq =>
          h2 (Finset.mem_insert.mpr (Or.inl heq))
        have h_v2_ne_v₂_1 : v2 ≠ v₂.1 := fun heq =>
          h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
        have h_v1_pe_V' : v1 ∉ VarCtx_to_VarSymbs pe_V' := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨⟨v, S'⟩, hvin', hveq⟩
          have hvin_W₁ : (⟨v, S'⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [← w₂_eq]
            exact Finset.mem_insert_of_mem (Finset.erase_subset _ _ hvin')
          rw [W₁def] at hvin_W₁
          rcases Finset.mem_insert.mp hvin_W₁ with h_eq | h_inV
          · exact (Finset.mem_erase.mp hvin').1 h_eq
          · exact hv1 (Finset.mem_image.mpr ⟨⟨v, S'⟩, h_inV, hveq⟩)
        have h_v2_pe_V' : v2 ∉ VarCtx_to_VarSymbs pe_V' := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨⟨v, S'⟩, hvin', hveq⟩
          have hvin_W₁ : (⟨v, S'⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [← w₂_eq]
            exact Finset.mem_insert_of_mem (Finset.erase_subset _ _ hvin')
          rw [W₁def] at hvin_W₁
          rcases Finset.mem_insert.mp hvin_W₁ with h_eq | h_inV
          · exact (Finset.mem_erase.mp hvin').1 h_eq
          · exact hv2 (Finset.mem_image.mpr ⟨⟨v, S'⟩, h_inV, hveq⟩)
        have hv1_V_inner : v1 ∉ VarCtx_to_VarSymbs V_inner_pe :=
          not_mem_VarSymbs_insert_twice h_v1_ne_v₁_1 h_v1_ne_v₂_1 h_v1_pe_V'
        have hv2_V_inner : v2 ∉ VarCtx_to_VarSymbs V_inner_pe :=
          not_mem_VarSymbs_insert_twice h_v2_ne_v₁_1 h_v2_ne_v₂_1 h_v2_pe_V'
        have W₁_inner_def : pe_W₁ =
            VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_inner_pe hz_V_inner := by
          apply VarCtx_ext
          rw [← w₁_eq]
          change insert v₁ (insert v₂ pe_V.1) =
                 insert ⟨z, V1.VTypeProd V2⟩ (insert v₁ (insert v₂ pe_V'.1))
          rw [← Finset.insert_erase h_z_in_pe_V,
              Finset.insert_comm v₂ ⟨z, V1.VTypeProd V2⟩,
              Finset.insert_comm v₁ ⟨z, V1.VTypeProd V2⟩]
          rfl
        let W₂_inner_pe :=
          VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_inner_pe hv1_V_inner hv2_V_inner hv1v2
        have h_v1_nb_inner_cast : v1 ∉ WFF.boundVars (W₁_inner_def ▸ inner_wff) := by
          rw [WFF.boundVars_ctx_cast]; exact h_v1_nb_inner
        have h_v2_nb_inner_cast : v2 ∉ WFF.boundVars (W₁_inner_def ▸ inner_wff) := by
          rw [WFF.boundVars_ctx_cast]; exact h_v2_nb_inner
        let recursed := WFF.unpair z V1 V2 v1 v2 V_inner_pe
                          (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_inner_pe hz_V_inner)
                          W₂_inner_pe
                          hz_V_inner hv1_V_inner hv2_V_inner hv1v2
                          rfl rfl (W₁_inner_def ▸ inner_wff)
                          h_v1_nb_inner_cast h_v2_nb_inner_cast
        let pe_V_new :=
          VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ pe_V' h_v1_pe_V' h_v2_pe_V' hv1v2
        have hv₁_new : v₁.1 ∉ VarCtx_to_VarSymbs pe_V_new :=
          not_mem_VarSymbs_insert_twice h_v1_ne_v₁_1.symm h_v2_ne_v₁_1.symm hv₁_pe_V'
        have hv₂_new : v₂.1 ∉ VarCtx_to_VarSymbs pe_V_new :=
          not_mem_VarSymbs_insert_twice h_v1_ne_v₂_1.symm h_v2_ne_v₂_1.symm hv₂_pe_V'
        have hz'_new : z' ∉ VarCtx_to_VarSymbs pe_V_new := by
          have h_z'_in_V : (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ V.1 := by
            have h_z'_in_W₁ : (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [← w₂_eq]; exact Finset.mem_insert_self _ _
            rw [W₁def] at h_z'_in_W₁
            rcases Finset.mem_insert.mp h_z'_in_W₁ with h_eq | h_inV
            · exact absurd h_eq h_case
            · exact h_inV
          have h_z'_ne_v1 : z' ≠ v1 := fun heq =>
            hv1 (heq ▸ Finset.mem_image.mpr ⟨_, h_z'_in_V, rfl⟩)
          have h_z'_ne_v2 : z' ≠ v2 := fun heq =>
            hv2 (heq ▸ Finset.mem_image.mpr ⟨_, h_z'_in_V, rfl⟩)
          have h_z'_pe_V' : z' ∉ VarCtx_to_VarSymbs pe_V' :=
            fun hmem => hz' (VarCtx_to_VarSymbs_erase_subset hmem)
          exact not_mem_VarSymbs_insert_twice h_z'_ne_v1 h_z'_ne_v2 h_z'_pe_V'
        have ctx_eq : W₂_inner_pe =
            VarCtx_insert_twice v₁ v₂ pe_V_new hv₁_new hv₂_new hv₁v₂_inner :=
          VarCtx_ext _ _ (by
            change insert (⟨v1, V1⟩ : VarSymb × VarType)
                     (insert ⟨v2, V2⟩ (insert v₁ (insert v₂ pe_V'.1))) =
                   insert v₁ (insert v₂ (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ pe_V'.1)))
            rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) v₁,
                Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) v₁,
                Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) v₂,
                Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) v₂])
        have w₂_eq_new :
            VarCtx_insert ⟨z', .VTypeProd v₁.2 v₂.2⟩ pe_V_new hz'_new = W₂ := by
          rw [W₂def]
          apply VarCtx_ext
          change insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                   (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ pe_V'.1)) =
                 insert (⟨v1, V1⟩ : VarSymb × VarType) (insert ⟨v2, V2⟩ V.1)
          have h_W_set : insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V.1
                       = insert ⟨z, V1.VTypeProd V2⟩ V.1 :=
            congrArg PSigma.fst (w₂_eq.trans W₁def)
          have h_V_eq : V.1 = insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V'.1 := by
            have step :
                (insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V.1).erase
                  ⟨z, V1.VTypeProd V2⟩ = V.1 := by
              rw [h_W_set, Finset.erase_insert
                (fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩))]
            rw [Finset.erase_insert_of_ne h_case] at step
            exact step.symm
          rw [h_V_eq,
              Finset.insert_comm
                (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                (⟨v1, V1⟩ : VarSymb × VarType),
              Finset.insert_comm
                (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                (⟨v2, V2⟩ : VarSymb × VarType)]
        exact w₂_eq_new ▸ .pair_elim v₁ v₂ z' hv₁_new hv₂_new hv₁v₂_inner hz'_new
                                     rfl rfl (ctx_eq ▸ recursed)
termination_by WFF.numNodes input
decreasing_by
  all_goals (first
    | (simp only [WFF.numNodes_ctx_cast, WFF.numNodes]; omega)
    | (simp only [WFF.numNodes]; omega))

-- Probe: does `WFF.unpair` now generate equational theorems?
private theorem WFF.unpair_eq_lemma_probe {σ : Signature}
    (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
    (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (h1 : v1 ∉ WFF.boundVars (.top : WFF σ W₁))
    (h2 : v2 ∉ WFF.boundVars (.top : WFF σ W₁)) :
    WFF.unpair z V1 V2 v1 v2 V W₁ W₂
      hz hv1 hv2 hv1v2 W₁def W₂def
      (.top : WFF σ W₁) h1 h2
      = .top := by
  unfold WFF.unpair
  rfl

-- `WFF.unpair` preserves `diaCount`.  Structural cases recurse via IH;
-- `.box`/`.dia` bodies pass through (z has pair type, can't appear in
-- box/dia inner context); `.pair_elim` Case A uses the helper subtype's
-- diaCount preservation, Case B recurses via `apply`.
theorem WFF.diaCount_unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType)
    (v1 v2 : VarSymb) (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (input : WFF σ W₁)
    (h_v1_nb : v1 ∉ WFF.boundVars input)
    (h_v2_nb : v2 ∉ WFF.boundVars input) :
    WFF.diaCount (WFF.unpair z V1 V2 v1 v2 V W₁ W₂
                    hz hv1 hv2 hv1v2 W₁def W₂def input h_v1_nb h_v2_nb)
      = WFF.diaCount input := by
  match input, h_v1_nb, h_v2_nb with
  | .atom R, h1, h2 =>
      have ih := Rel.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂ _
        hz hv1 hv2 hv1v2 W₁def W₂def R h1 h2
      unfold WFF.unpair
      simp only [WFF.diaCount]
      exact ih
  | .top, _, _ =>
      unfold WFF.unpair; rfl
  | .bot, _, _ =>
      unfold WFF.unpair; rfl
  | .and φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.diaCount]
      omega
  | .or φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.diaCount]
      omega
  | .imp φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.diaCount]
      omega
  | .eq s t, h1, h2 =>
      have h1_s : v1 ∉ Term.boundVars s :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_t : v1 ∉ Term.boundVars t :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_s : v2 ∉ Term.boundVars s :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_t : v2 ∉ Term.boundVars t :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_s := Term.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂ _
        hz hv1 hv2 hv1v2 W₁def W₂def s h1_s h2_s
      have ih_t := Term.diaCount_unpair z V1 V2 v1 v2 V W₁ W₂ _
        hz hv1 hv2 hv1v2 W₁def W₂def t h1_t h2_t
      unfold WFF.unpair
      simp only [WFF.diaCount]
      omega
  | @WFF.all _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
      rw [WFF.diaCount_unpair, WFF.diaCount_ctx_cast]
  | @WFF.ex _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      simp only [WFF.diaCount, WFF.diaCount_ctx_cast]
      rw [WFF.diaCount_unpair, WFF.diaCount_ctx_cast]
  | .box _ _ _, _, _ =>
      unfold WFF.unpair
      rfl
  | .dia _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      rfl
  | .pair_elim v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff, h1, h2 =>
      rename_i pe_V pe_W₁
      have h_v1_nb_inner : v1 ∉ WFF.boundVars inner_wff := fun hmem =>
        h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      have h_v2_nb_inner : v2 ∉ WFF.boundVars inner_wff := fun hmem =>
        h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      unfold WFF.unpair
      by_cases h_case :
          (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩
      · rw [dif_pos h_case]
        exact (WFF.unpair_pe_caseA z V1 V2 v1 v2 V W₁ W₂
          hz hv1 hv2 hv1v2 W₁def W₂def pe_V pe_W₁ v₁ v₂ z' hv₁ hv₂
          hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff h_v1_nb_inner h_v2_nb_inner
          h1 h2 h_case).property.1
      · rw [dif_neg h_case]
        simp only [WFF.diaCount_ctx_cast, WFF.diaCount]
        rw [WFF.diaCount_unpair, WFF.diaCount_ctx_cast]
termination_by WFF.numNodes input
decreasing_by
  all_goals (first
    | (simp only [WFF.numNodes_ctx_cast, WFF.numNodes]; omega)
    | (simp only [WFF.numNodes]; omega))

-- `WFF.unpair` preserves `binderPairDepth`.  Same structure as
-- `WFF.diaCount_unpair`: unpair only shuffles free variables, doesn't add or
-- remove modal/quantifier binders.
theorem WFF.binderPairDepth_unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType)
    (v1 v2 : VarSymb) (V W₁ W₂ : VarCtx)
    (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2)
    (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
    (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
    (input : WFF σ W₁)
    (h_v1_nb : v1 ∉ WFF.boundVars input)
    (h_v2_nb : v2 ∉ WFF.boundVars input) :
    WFF.binderPairDepth (WFF.unpair z V1 V2 v1 v2 V W₁ W₂
                           hz hv1 hv2 hv1v2 W₁def W₂def input h_v1_nb h_v2_nb)
      = WFF.binderPairDepth input := by
  match input, h_v1_nb, h_v2_nb with
  | .atom _, _, _ =>
      unfold WFF.unpair; rfl
  | .top, _, _ =>
      unfold WFF.unpair; rfl
  | .bot, _, _ =>
      unfold WFF.unpair; rfl
  | .and φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.binderPairDepth]
      omega
  | .or φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.binderPairDepth]
      omega
  | .imp φ ψ, h1, h2 =>
      have h1_φ : v1 ∉ WFF.boundVars φ :=
        fun hmem => h1 (Finset.mem_union_left _ hmem)
      have h1_ψ : v1 ∉ WFF.boundVars ψ :=
        fun hmem => h1 (Finset.mem_union_right _ hmem)
      have h2_φ : v2 ∉ WFF.boundVars φ :=
        fun hmem => h2 (Finset.mem_union_left _ hmem)
      have h2_ψ : v2 ∉ WFF.boundVars ψ :=
        fun hmem => h2 (Finset.mem_union_right _ hmem)
      have ih_φ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def φ h1_φ h2_φ
      have ih_ψ := WFF.binderPairDepth_unpair z V1 V2 v1 v2 V W₁ W₂
        hz hv1 hv2 hv1v2 W₁def W₂def ψ h1_ψ h2_ψ
      unfold WFF.unpair
      simp only [WFF.binderPairDepth]
      omega
  | .eq _ _, _, _ =>
      unfold WFF.unpair; rfl
  | @WFF.all _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
      rw [WFF.binderPairDepth_unpair, WFF.binderPairDepth_ctx_cast]
  | @WFF.ex _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      simp only [WFF.binderPairDepth, WFF.binderPairDepth_ctx_cast]
      rw [WFF.binderPairDepth_unpair, WFF.binderPairDepth_ctx_cast]
  | .box _ _ _, _, _ =>
      unfold WFF.unpair
      rfl
  | .dia _ _ _ _ _, _, _ =>
      unfold WFF.unpair
      rfl
  | .pair_elim v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff, h1, h2 =>
      rename_i pe_V pe_W₁
      have h_v1_nb_inner : v1 ∉ WFF.boundVars inner_wff := fun hmem =>
        h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      have h_v2_nb_inner : v2 ∉ WFF.boundVars inner_wff := fun hmem =>
        h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
      unfold WFF.unpair
      by_cases h_case :
          (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩
      · rw [dif_pos h_case]
        exact (WFF.unpair_pe_caseA z V1 V2 v1 v2 V W₁ W₂
          hz hv1 hv2 hv1v2 W₁def W₂def pe_V pe_W₁ v₁ v₂ z' hv₁ hv₂
          hv₁v₂_inner hz' w₁_eq w₂_eq inner_wff h_v1_nb_inner h_v2_nb_inner
          h1 h2 h_case).property.2
      · rw [dif_neg h_case]
        simp only [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth]
        rw [WFF.binderPairDepth_unpair, WFF.binderPairDepth_ctx_cast]
termination_by WFF.numNodes input
decreasing_by
  all_goals (first
    | (simp only [WFF.numNodes_ctx_cast, WFF.numNodes]; omega)
    | (simp only [WFF.numNodes]; omega))

/-! ### Context Restriction -/

-- Substitute the variable `⟨x, S⟩` with the term `s` inside `φ`.  Mirrors
-- `Term.ctx_rest` + `Term.ctx_rest_MU`: `WFF.ctx_rest` is the structural
-- pass requiring `V_ext.firstPairVar = none` (no pair binders in the
-- extended context); `WFF.ctx_rest_MU` is the user-facing wrapper that
-- preprocesses pair binders via `WFF.unpair` / `Term.unpair` before
-- delegating.
--
-- TODO: full implementations.  Currently both are skeleton stubs (returning
-- a placeholder `.top` for the non-trivial arms) so the mutual structure
-- compiles.  The .pair_elim arm of `WFF.ctx_rest` is properly exfalso via
-- `h_pf`; the other binder arms (.all/.ex/.box/.dia) are stubs to fill in.

-- Case-3 (modal beta) reorder helper for `WFF.ctx_rest_dia_arm`.  Extracted
-- outside the ctx_rest mutual block to keep dia_arm's Case 3 body compact and
-- avoid elaborator memory pressure (which caused BSODs on inline attempts).
--
-- Given ψ living in (insert xv V_inner) with xv.1 = x and a separate binder
-- xv_s : VarSymb × VarType with xv_s.1 ∉ V_inner (and xv.1 ≠ xv_s.1), this
-- helper produces the reordered/reformed WFF living in
--   (insert ⟨x, xv.2⟩ (insert xv_s V_inner))
-- ready for the MU substitution step at x.  Preserves `binderPairDepth` and
-- `diaCount` (both are stable under ctx_ext and under VarCtx-equality casts).
def WFF.dia_arm_case3_reorder {σ : Signature} {V_inner : VarCtx}
    (xv xv_s : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (hxv_s : xv_s.1 ∉ VarCtx_to_VarSymbs V_inner)
    (h_xv_ne_xv_s : xv.1 ≠ xv_s.1)
    {x : VarSymb} (h_xv_eq_x : xv.1 = x)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    : Σ' (h_x_inner : x ∉ VarCtx_to_VarSymbs
                          (VarCtx_insert xv_s V_inner hxv_s)),
        { ψ' : WFF σ (VarCtx_insert (⟨x, xv.2⟩ : VarSymb × VarType)
                        (VarCtx_insert xv_s V_inner hxv_s) h_x_inner) //
            WFF.binderPairDepth ψ' = WFF.binderPairDepth ψ ∧
            WFF.diaCount ψ' = WFF.diaCount ψ } := by
  -- Step 1: lift ψ past xv_s.
  have hxv_s_outer : xv_s.1 ∉ VarCtx_to_VarSymbs
      (VarCtx_insert xv V_inner hxv) := by
    apply not_mem_VarSymbs_insert
    · exact fun h => h_xv_ne_xv_s h.symm
    · exact hxv_s
  let ψ_lifted : WFF σ (VarCtx_insert xv_s
      (VarCtx_insert xv V_inner hxv) hxv_s_outer) :=
    WFF.ctx_ext xv_s hxv_s_outer ψ
  -- Step 2: reorder to swap xv_s and xv.
  have hxv_xv_s_outer : xv.1 ∉ VarCtx_to_VarSymbs
      (VarCtx_insert xv_s V_inner hxv_s) :=
    not_mem_VarSymbs_insert h_xv_ne_xv_s hxv
  have h_reorder :
      VarCtx_insert xv_s (VarCtx_insert xv V_inner hxv) hxv_s_outer =
      VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer := by
    apply VarCtx_ext
    change insert xv_s (insert xv V_inner.1) =
           insert xv (insert xv_s V_inner.1)
    exact Finset.insert_comm _ _ _
  let ψ_reordered : WFF σ (VarCtx_insert xv
      (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer) :=
    h_reorder ▸ ψ_lifted
  -- Step 3: reform binder as ⟨x, xv.2⟩ via h_xv_eq_x.
  have hxv_form : xv = (⟨x, xv.2⟩ : VarSymb × VarType) :=
    Prod.ext h_xv_eq_x rfl
  have h_x_inner : x ∉ VarCtx_to_VarSymbs
      (VarCtx_insert xv_s V_inner hxv_s) :=
    h_xv_eq_x ▸ hxv_xv_s_outer
  have h_reform :
      VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer =
      VarCtx_insert (⟨x, xv.2⟩ : VarSymb × VarType)
        (VarCtx_insert xv_s V_inner hxv_s) h_x_inner := by
    apply VarCtx_ext
    change insert xv _ = insert (⟨x, xv.2⟩ : VarSymb × VarType) _
    rw [hxv_form]
  let ψ_for_sub : WFF σ (VarCtx_insert (⟨x, xv.2⟩ : VarSymb × VarType)
      (VarCtx_insert xv_s V_inner hxv_s) h_x_inner) :=
    h_reform ▸ ψ_reordered
  refine ⟨h_x_inner, ⟨ψ_for_sub, ?_, ?_⟩⟩
  · -- binderPairDepth preserved.
    show WFF.binderPairDepth (h_reform ▸ h_reorder ▸
              WFF.ctx_ext xv_s hxv_s_outer ψ) = _
    rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_cast,
        WFF.binderPairDepth_ctx_ext]
  · -- diaCount preserved.
    show WFF.diaCount (h_reform ▸ h_reorder ▸
              WFF.ctx_ext xv_s hxv_s_outer ψ) = _
    rw [WFF.diaCount_ctx_cast, WFF.diaCount_ctx_cast,
        WFF.diaCount_ctx_ext]

mutual

def WFF.ctx_rest {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    {ψ' : WFF σ V // WFF.binderPairDepth ψ' ≤ WFF.binderPairDepth φ} := by
  match φ with
  | .atom R => exact ⟨.atom (Rel.ctx_rest hx h_pf s R), Nat.zero_le _⟩
  | .top => exact ⟨.top, Nat.zero_le _⟩
  | .bot => exact ⟨.bot, Nat.zero_le _⟩
  | .and φ' ψ =>
      let r1 := WFF.ctx_rest hx h_pf s φ'
      let r2 := WFF.ctx_rest hx h_pf s ψ
      exact ⟨.and r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .or φ' ψ =>
      let r1 := WFF.ctx_rest hx h_pf s φ'
      let r2 := WFF.ctx_rest hx h_pf s ψ
      exact ⟨.or r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .imp φ' ψ =>
      let r1 := WFF.ctx_rest hx h_pf s φ'
      let r2 := WFF.ctx_rest hx h_pf s ψ
      exact ⟨.imp r1.val r2.val, by
        simp only [WFF.binderPairDepth]
        exact Nat.add_le_add r1.property r2.property⟩
  | .eq s' t =>
      exact ⟨.eq (Term.ctx_rest hx h_pf s s') (Term.ctx_rest hx h_pf s t),
             Nat.zero_le _⟩
  | @WFF.all _ _ x_a hx_a ψ =>
      let r := WFF.ctx_rest_quant_arm hx h_pf s false x_a hx_a ψ
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | @WFF.ex _ _ x_a hx_a ψ =>
      let r := WFF.ctx_rest_quant_arm hx h_pf s true x_a hx_a ψ
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | .box ψ hsub h_no_extras =>
      let r := WFF.ctx_rest_box_arm hx h_pf s ψ hsub h_no_extras
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | .dia xv hxv ψ hsub h_no_extras =>
      let r := WFF.ctx_rest_dia_arm hx h_pf s xv hxv ψ hsub h_no_extras
      exact ⟨r.val, by
        simp only [WFF.binderPairDepth]
        exact r.property⟩
  | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq _ =>
      -- Unreachable: V_ext contains ⟨z, V1×V2⟩ via w2eq, but h_pf says
      -- V_ext.firstPairVar = none.  Contradiction.
      exfalso
      have h_z_in : (⟨z, v1.2.VTypeProd v2.2⟩ : VarSymb × VarType) ∈
          (VarCtx_insert ⟨x, S⟩ V hx).1 := by
        rw [← w2eq]; exact Finset.mem_insert_self _ _
      exact VarCtx.firstPairVar_none_no_pair h_pf h_z_in
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ,
                WFF.diaCount φ, WFF.numNodes φ, 1)
decreasing_by
  -- 10 recursive call sites — per-site bullets with `by_cases` on the
  -- "other" subformula's bpd (0 vs > 0) and dC (0 vs > 0) for and/or/imp;
  -- binder dispatches go directly to phase-strict.
  -- New 4-tuple structure: `(V_ext.pd + bpd, dC, numNodes, phase)`.
  -- Structural recursion cases: if bpd(other) > 0, new comp 1 strict; else if
  -- dC(other) > 0, comp 1 eq + comp 2 strict; else all comps eq, comp 3 strict.
  · -- 1. and on φ' (other = ψ)
    by_cases hb : WFF.binderPairDepth ψ = 0
    · by_cases hd : WFF.diaCount ψ = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- 2. and on ψ (other = φ')
    by_cases hb : WFF.binderPairDepth φ' = 0
    · by_cases hd : WFF.diaCount φ' = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- 3. or on φ' (other = ψ)
    by_cases hb : WFF.binderPairDepth ψ = 0
    · by_cases hd : WFF.diaCount ψ = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- 4. or on ψ (other = φ')
    by_cases hb : WFF.binderPairDepth φ' = 0
    · by_cases hd : WFF.diaCount φ' = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- 5. imp on φ' (other = ψ)
    by_cases hb : WFF.binderPairDepth ψ = 0
    · by_cases hd : WFF.diaCount ψ = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- 6. imp on ψ (other = φ')
    by_cases hb : WFF.binderPairDepth φ' = 0
    · by_cases hd : WFF.diaCount φ' = 0
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · right; refine ⟨?_, ?_⟩
          · simp only [WFF.diaCount]; omega
          · left; simp only [WFF.numNodes]; omega
      · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
        refine ⟨?_, ?_⟩
        · simp only [WFF.binderPairDepth]; omega
        · left; simp only [WFF.diaCount]; omega
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [WFF.binderPairDepth]; omega
  · -- 7. all → quant_arm (comps 1, 2, 3 equal, phase strict)
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- 8. ex → quant_arm
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- 9. box → box_arm
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide
  · -- 10. dia → dia_arm
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth]; try omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount]; try omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.numNodes]; try omega
        · decide

def WFF.ctx_rest_MU {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    {ψ' : WFF σ V // WFF.binderPairDepth ψ' ≤ WFF.binderPairDepth φ} := by
  match h_pv : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar with
  | none =>
      exact WFF.ctx_rest hx h_pv s φ
  | some ⟨(z, V1, V2), hzmem⟩ =>
      by_cases h_z_eq_x : z = x
      · -- Case A: z = x, so S = V1×V2.  Under the Σ' design the second
        -- recursive MU call's termination reads the FIRST call's bpd bound
        -- (h_r1_bpd, from result1.property + unpair/cast preservation) —
        -- this was the circularity that blocked the plain-return design.
        have h_S_eq : S = V1.VTypeProd V2 := by
          rcases Finset.mem_insert.mp hzmem with h_eq | h_in_V
          · exact ((Prod.mk.inj h_eq).2).symm
          · exfalso
            exact hx (Finset.mem_image.mpr ⟨_, h_in_V, h_z_eq_x⟩)
        have hVE_eq : VarCtx_insert ⟨x, S⟩ V hx =
                      VarCtx_insert ⟨x, V1.VTypeProd V2⟩ V hx := by
          apply VarCtx_ext
          change insert (⟨x, S⟩ : VarSymb × VarType) V.1
               = insert (⟨x, V1.VTypeProd V2⟩ : VarSymb × VarType) V.1
          rw [h_S_eq]
        let s_pair : Term σ V (V1.VTypeProd V2) := h_S_eq ▸ s
        let φ_pair : WFF σ (VarCtx_insert ⟨x, V1.VTypeProd V2⟩ V hx) :=
          hVE_eq ▸ φ
        match s_pair with
        | .pair s1 s2 =>
            let avoid : Finset VarSymb :=
              VarCtx_to_VarSymbs V ∪ {x} ∪ WFF.boundVars φ_pair
                ∪ Term.boundVars s1 ∪ Term.boundVars s2
            let v1 : VarSymb := VarSymb.fresh avoid
            have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem avoid
            let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
            have hv2_avoid_v1 : v2 ∉ insert v1 avoid :=
              VarSymb.fresh_not_mem (insert v1 avoid)
            have hv2_avoid : v2 ∉ avoid :=
              fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
            have hv1v2_ne : v1 ≠ v2 :=
              fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
            have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun y h =>
              Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
            have h_avoid_φ : WFF.boundVars φ_pair ⊆ avoid := fun y h =>
              Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_right _ h))
            have hv1_V : v1 ∉ VarCtx_to_VarSymbs V :=
              fun h => hv1_avoid (h_avoid_V h)
            have hv2_V : v2 ∉ VarCtx_to_VarSymbs V :=
              fun h => hv2_avoid (h_avoid_V h)
            have hv1_nb_φ : v1 ∉ WFF.boundVars φ_pair :=
              fun h => hv1_avoid (h_avoid_φ h)
            have hv2_nb_φ : v2 ∉ WFF.boundVars φ_pair :=
              fun h => hv2_avoid (h_avoid_φ h)
            -- Unpair φ_pair at x.
            let V_v1v2 : VarCtx :=
              VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1_V hv2_V hv1v2_ne
            let φ' : WFF σ V_v1v2 :=
              WFF.unpair x V1 V2 v1 v2 V _ V_v1v2
                hx hv1_V hv2_V hv1v2_ne rfl rfl φ_pair hv1_nb_φ hv2_nb_φ
            have hv2_V_only : v2 ∉ VarCtx_to_VarSymbs V := hv2_V
            have hv1_V_plus_v2 : v1 ∉ VarCtx_to_VarSymbs
                (VarCtx_insert ⟨v2, V2⟩ V hv2_V_only) :=
              not_mem_VarSymbs_insert hv1v2_ne hv1_V
            have h_V_v1v2_eq :
                V_v1v2 = VarCtx_insert ⟨v1, V1⟩
                  (VarCtx_insert ⟨v2, V2⟩ V hv2_V_only) hv1_V_plus_v2 := by
              apply VarCtx_ext; rfl
            let φ'_cast : WFF σ (VarCtx_insert ⟨v1, V1⟩
                (VarCtx_insert ⟨v2, V2⟩ V hv2_V_only) hv1_V_plus_v2) :=
              h_V_v1v2_eq ▸ φ'
            -- Weaken s1 : V → V + v2; substitute v1 ↦ s1_weakened.
            let s1_weakened : Term σ (VarCtx_insert ⟨v2, V2⟩ V hv2_V_only) V1 :=
              Term.ctx_ext ⟨v2, V2⟩ hv2_V_only s1
            have h_in_bpd : WFF.binderPairDepth φ'_cast
                = WFF.binderPairDepth φ := by
              simp only [φ'_cast, φ', φ_pair, WFF.binderPairDepth_ctx_cast,
                         WFF.binderPairDepth_unpair]
            let result1 := WFF.ctx_rest_MU hv1_V_plus_v2 s1_weakened φ'_cast
            have h_r1_bpd : WFF.binderPairDepth result1.val
                ≤ WFF.binderPairDepth φ :=
              le_trans result1.property (le_of_eq h_in_bpd)
            -- Substitute v2 ↦ s2.
            let result2 := WFF.ctx_rest_MU hv2_V_only s2 result1.val
            exact ⟨result2.val, le_trans result2.property h_r1_bpd⟩
        | @Term.pair_elim _ pe_V _ _ _ sv1 sv2 sz hsv1 hsv2 hsv1sv2 hsz
            sw1eq sw2eq sbody =>
            -- s is itself .pair_elim with binder sz: lock-step unpair φ and
            -- s at sz using fresh v1, v2; recurse; re-wrap WFF.pairElim.
            have hsz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                ∈ V.1 := by
              rw [← sw2eq]; exact Finset.mem_insert_self _ _
            let avoid : Finset VarSymb :=
              VarCtx_to_VarSymbs V ∪ {x} ∪ Term.boundVars s_pair
                ∪ WFF.boundVars φ_pair
            let v1 : VarSymb := VarSymb.fresh avoid
            have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem _
            let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
            have hv2_avoid_v1 : v2 ∉ insert v1 avoid := VarSymb.fresh_not_mem _
            have hv2_avoid : v2 ∉ avoid :=
              fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
            have hv1v2_ne : v1 ≠ v2 :=
              fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
            have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun y h =>
              Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ h))
            have h_avoid_x : x ∈ avoid :=
              Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)))
            have h_avoid_s : Term.boundVars s_pair ⊆ avoid := fun y h =>
              Finset.mem_union_left _ (Finset.mem_union_right _ h)
            have h_avoid_φ : WFF.boundVars φ_pair ⊆ avoid :=
              fun y h => Finset.mem_union_right _ h
            have hv1_V : v1 ∉ VarCtx_to_VarSymbs V :=
              fun h => hv1_avoid (h_avoid_V h)
            have hv2_V : v2 ∉ VarCtx_to_VarSymbs V :=
              fun h => hv2_avoid (h_avoid_V h)
            have hv1_x_ne : v1 ≠ x := fun h => hv1_avoid (h ▸ h_avoid_x)
            have hv2_x_ne : v2 ≠ x := fun h => hv2_avoid (h ▸ h_avoid_x)
            have hv1_nb_s : v1 ∉ Term.boundVars s_pair :=
              fun h => hv1_avoid (h_avoid_s h)
            have hv2_nb_s : v2 ∉ Term.boundVars s_pair :=
              fun h => hv2_avoid (h_avoid_s h)
            have hv1_nb_φ : v1 ∉ WFF.boundVars φ_pair :=
              fun h => hv1_avoid (h_avoid_φ h)
            have hv2_nb_φ : v2 ∉ WFF.boundVars φ_pair :=
              fun h => hv2_avoid (h_avoid_φ h)
            have h_peV_subset_V : VarCtx_to_VarSymbs pe_V ⊆
                VarCtx_to_VarSymbs V := fun y h => by
              obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h
              refine Finset.mem_image.mpr ⟨q, ?_, hq_eq⟩
              rw [← sw2eq]; exact Finset.mem_insert_of_mem hq_in
            have hv1_peV : v1 ∉ VarCtx_to_VarSymbs pe_V :=
              fun h => hv1_V (h_peV_subset_V h)
            have hv2_peV : v2 ∉ VarCtx_to_VarSymbs pe_V :=
              fun h => hv2_V (h_peV_subset_V h)
            -- Unpair s_pair at sz → s' in (pe_V + v1 + v2), type V1×V2.
            let peV_v1v2 : VarCtx :=
              VarCtx_insert_twice ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩ pe_V
                hv1_peV hv2_peV hv1v2_ne
            let s' : Term σ peV_v1v2 (V1.VTypeProd V2) :=
              Term.unpair sz sv1.2 sv2.2 v1 v2 pe_V _ peV_v1v2 _
                hsz hv1_peV hv2_peV hv1v2_ne sw2eq.symm rfl s_pair
                hv1_nb_s hv2_nb_s
            -- Unpair φ_pair at sz: first re-express its context as
            -- ((pe_V + ⟨x, V1×V2⟩) + sz).
            have hx_peV : x ∉ VarCtx_to_VarSymbs pe_V :=
              fun h => hx (h_peV_subset_V h)
            let peV_x : VarCtx := VarCtx_insert ⟨x, V1.VTypeProd V2⟩ pe_V hx_peV
            have hsz_ne_x : sz ≠ x := fun h =>
              hx (Finset.mem_image.mpr
                ⟨⟨sz, sv1.2.VTypeProd sv2.2⟩, hsz_in_V, h⟩)
            have hsz_peV_x : sz ∉ VarCtx_to_VarSymbs peV_x :=
              not_mem_VarSymbs_insert hsz_ne_x hsz
            have h_cast_φA :
                VarCtx_insert ⟨x, V1.VTypeProd V2⟩ V hx =
                VarCtx_insert ⟨sz, sv1.2.VTypeProd sv2.2⟩ peV_x hsz_peV_x := by
              apply VarCtx_ext
              change insert (⟨x, V1.VTypeProd V2⟩ : VarSymb × VarType) V.1 =
                   insert (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                     (insert ⟨x, V1.VTypeProd V2⟩ pe_V.1)
              rw [show V.1 = insert (⟨sz, sv1.2.VTypeProd sv2.2⟩ :
                              VarSymb × VarType) pe_V.1
                    from (congrArg PSigma.fst sw2eq).symm]
              exact Finset.insert_comm _ _ _
            let φ_castA : WFF σ (VarCtx_insert ⟨sz, sv1.2.VTypeProd sv2.2⟩
                peV_x hsz_peV_x) :=
              h_cast_φA ▸ φ_pair
            have hv1_peV_x : v1 ∉ VarCtx_to_VarSymbs peV_x :=
              not_mem_VarSymbs_insert hv1_x_ne hv1_peV
            have hv2_peV_x : v2 ∉ VarCtx_to_VarSymbs peV_x :=
              not_mem_VarSymbs_insert hv2_x_ne hv2_peV
            let peV_x_v1v2 : VarCtx :=
              VarCtx_insert_twice ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩ peV_x
                hv1_peV_x hv2_peV_x hv1v2_ne
            have hv1_nb_φ_castA : v1 ∉ WFF.boundVars φ_castA := by
              change v1 ∉ WFF.boundVars (h_cast_φA ▸ φ_pair)
              rw [WFF.boundVars_ctx_cast]; exact hv1_nb_φ
            have hv2_nb_φ_castA : v2 ∉ WFF.boundVars φ_castA := by
              change v2 ∉ WFF.boundVars (h_cast_φA ▸ φ_pair)
              rw [WFF.boundVars_ctx_cast]; exact hv2_nb_φ
            let φ'A : WFF σ peV_x_v1v2 :=
              WFF.unpair sz sv1.2 sv2.2 v1 v2 peV_x _ peV_x_v1v2
                hsz_peV_x hv1_peV_x hv2_peV_x hv1v2_ne rfl rfl φ_castA
                hv1_nb_φ_castA hv2_nb_φ_castA
            -- Re-arrange φ'A to (peV_v1v2 + ⟨x, V1×V2⟩) form.
            have hx_peV_v1v2 : x ∉ VarCtx_to_VarSymbs peV_v1v2 :=
              not_mem_VarSymbs_insert_twice
                (fun h => hv1_x_ne h.symm)
                (fun h => hv2_x_ne h.symm)
                hx_peV
            have h_cast_φ'A :
                peV_x_v1v2 = VarCtx_insert ⟨x, V1.VTypeProd V2⟩
                  peV_v1v2 hx_peV_v1v2 := by
              apply VarCtx_ext
              change insert (⟨v1, sv1.2⟩ : VarSymb × VarType)
                     (insert ⟨v2, sv2.2⟩ (insert ⟨x, V1.VTypeProd V2⟩ pe_V.1)) =
                   insert (⟨x, V1.VTypeProd V2⟩ : VarSymb × VarType)
                     (insert ⟨v1, sv1.2⟩ (insert ⟨v2, sv2.2⟩ pe_V.1))
              rw [Finset.insert_comm (⟨v2, sv2.2⟩ : VarSymb × VarType)
                  ⟨x, V1.VTypeProd V2⟩,
                  Finset.insert_comm (⟨v1, sv1.2⟩ : VarSymb × VarType)
                  ⟨x, V1.VTypeProd V2⟩]
            let φ'A_cast : WFF σ
                (VarCtx_insert ⟨x, V1.VTypeProd V2⟩ peV_v1v2 hx_peV_v1v2) :=
              h_cast_φ'A ▸ φ'A
            -- bpd of the recursion input equals bpd φ (hoisted for the
            -- decreasing bullet).
            have h_in_bpdA : WFF.binderPairDepth φ'A_cast
                = WFF.binderPairDepth φ := by
              simp only [φ'A_cast, φ'A, φ_castA, φ_pair,
                         WFF.binderPairDepth_ctx_cast,
                         WFF.binderPairDepth_unpair]
            -- comp-1 pd strictness (hoisted).
            have h_measure_lt : (V1.VTypeProd V2).pairDepth
                  + peV_v1v2.pairDepth
                < S.pairDepth + V.pairDepth := by
              have h_peV_erase : pe_V = VarCtx_erase V
                  ⟨sz, sv1.2.VTypeProd sv2.2⟩ := by
                apply VarCtx_ext
                change pe_V.1 = V.1.erase ⟨sz, sv1.2.VTypeProd sv2.2⟩
                rw [show V.1 = insert (⟨sz, sv1.2.VTypeProd sv2.2⟩ :
                                VarSymb × VarType) pe_V.1
                      from (congrArg PSigma.fst sw2eq).symm]
                exact (Finset.erase_insert
                  (fun h => hsz (Finset.mem_image.mpr ⟨_, h, rfl⟩))).symm
              have hv1_Vmsz : v1 ∉ VarCtx_to_VarSymbs
                  (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩) := by
                rw [← h_peV_erase]; exact hv1_peV
              have hv2_Vmsz : v2 ∉ VarCtx_to_VarSymbs
                  (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩) := by
                rw [← h_peV_erase]; exact hv2_peV
              have h_lt : (VarCtx_insert_twice ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩
                  (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩)
                  hv1_Vmsz hv2_Vmsz hv1v2_ne).pairDepth < V.pairDepth :=
                VarCtx.pairDepth_unpair_lt hsz_in_V hv1_Vmsz hv2_Vmsz hv1v2_ne
              have h_peV_v1v2_eq : peV_v1v2 =
                  VarCtx_insert_twice ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩
                    (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩)
                    hv1_Vmsz hv2_Vmsz hv1v2_ne := by
                apply VarCtx_ext
                change insert (⟨v1, sv1.2⟩ : VarSymb × VarType)
                    (insert ⟨v2, sv2.2⟩ pe_V.1)
                  = insert ⟨v1, sv1.2⟩ (insert ⟨v2, sv2.2⟩
                      (VarCtx_erase V ⟨sz, sv1.2.VTypeProd sv2.2⟩).1)
                rw [h_peV_erase]
              have hS_pd : S.pairDepth = 1 + V1.pairDepth + V2.pairDepth := by
                rw [h_S_eq]; rfl
              have hprod : (V1.VTypeProd V2).pairDepth
                  = 1 + V1.pairDepth + V2.pairDepth := rfl
              rw [h_peV_v1v2_eq]
              omega
            let result := WFF.ctx_rest_MU hx_peV_v1v2 s' φ'A_cast
            exact ⟨WFF.pairElim ⟨v1, sv1.2⟩ ⟨v2, sv2.2⟩ sz
                hv1_peV hv2_peV hv1v2_ne hsz rfl sw2eq result.val, by
              rw [WFF.binderPairDepth_pairElim_gen]
              exact le_trans result.property (le_of_eq h_in_bpdA)⟩
      · -- Case B: z ≠ x, so z ∈ V.  Pick fresh v1, v2; lock-step unpair
        -- Term.unpair s and WFF.unpair φ at z; recurse on smaller context.
        have hzmem_V : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1 := by
          rcases Finset.mem_insert.mp hzmem with h_eq | h_in_V
          · exact absurd (Prod.mk.inj h_eq).1 h_z_eq_x
          · exact h_in_V
        let V_minus_z := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩
        have hz_fresh : z ∉ VarCtx_to_VarSymbs V_minus_z :=
          VarCtx_erase_fresh hzmem_V
        have V_eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z hz_fresh = V :=
          VarCtx_insert_erase hzmem_V hz_fresh
        let avoid : Finset VarSymb :=
          VarCtx_to_VarSymbs V ∪ {x} ∪ Term.boundVars s ∪ WFF.boundVars φ
        let v1 : VarSymb := VarSymb.fresh avoid
        have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem avoid
        let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
        have hv2_avoid_v1 : v2 ∉ insert v1 avoid :=
          VarSymb.fresh_not_mem (insert v1 avoid)
        have hv2_avoid : v2 ∉ avoid :=
          fun h => hv2_avoid_v1 (Finset.mem_insert_of_mem h)
        have hv1v2_ne : v1 ≠ v2 :=
          fun h => hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
        have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun y h =>
          Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have h_avoid_φ : WFF.boundVars φ ⊆ avoid :=
          fun y h => Finset.mem_union_right _ h
        have h_avoid_s : Term.boundVars s ⊆ avoid := fun y h =>
          Finset.mem_union_left _ (Finset.mem_union_right _ h)
        have h_avoid_x : x ∈ avoid := Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_singleton.mpr rfl)))
        have hv1_V : v1 ∉ VarCtx_to_VarSymbs V := fun h => hv1_avoid (h_avoid_V h)
        have hv2_V : v2 ∉ VarCtx_to_VarSymbs V := fun h => hv2_avoid (h_avoid_V h)
        have hv1_Vmz : v1 ∉ VarCtx_to_VarSymbs V_minus_z := fun h =>
          hv1_V (VarCtx_to_VarSymbs_erase_subset h)
        have hv2_Vmz : v2 ∉ VarCtx_to_VarSymbs V_minus_z := fun h =>
          hv2_V (VarCtx_to_VarSymbs_erase_subset h)
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
          not_mem_VarSymbs_insert h_z_eq_x hz_fresh
        have h_cast_φ :
            VarCtx_insert ⟨x, S⟩ V hx =
            VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z_x hz_Vmz_x := by
          apply VarCtx_ext
          change insert (⟨x, S⟩ : VarSymb × VarType) V.1 =
               insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType)
                 (insert ⟨x, S⟩ V_minus_z.1)
          rw [show V.1 = insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) V_minus_z.1
                from (Finset.insert_erase hzmem_V).symm]
          exact Finset.insert_comm _ _ _
        let φ_cast :
            WFF σ (VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z_x hz_Vmz_x) :=
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
            (fun h => hv1_x_ne h.symm)
            (fun h => hv2_x_ne h.symm)
            hx_Vmz
        have h_cast_φ' :
            V_minus_z_x_v1v2 =
            VarCtx_insert ⟨x, S⟩ V_minus_z_v1v2 hx_Vmz_v1v2 := by
          apply VarCtx_ext
          change insert (⟨v1, V1⟩ : VarSymb × VarType)
                 (insert ⟨v2, V2⟩ (insert ⟨x, S⟩ V_minus_z.1)) =
               insert ⟨x, S⟩
                 (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ V_minus_z.1))
          rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) ⟨x, S⟩,
              Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) ⟨x, S⟩]
        let φ'_cast : WFF σ (VarCtx_insert ⟨x, S⟩ V_minus_z_v1v2 hx_Vmz_v1v2) :=
          h_cast_φ' ▸ φ'
        let result := WFF.ctx_rest_MU hx_Vmz_v1v2 s' φ'_cast
        exact ⟨V_eq ▸ WFF.pairElim ⟨v1, V1⟩ ⟨v2, V2⟩ z
                 hv1_Vmz hv2_Vmz hv1v2_ne hz_fresh rfl rfl result.val, by
          simp only [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_pairElim]
          refine le_trans result.property ?_
          simp only [φ'_cast, φ', φ_cast, WFF.binderPairDepth_ctx_cast,
                     WFF.binderPairDepth_unpair]
          exact le_refl _⟩
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ,
                WFF.diaCount φ, WFF.numNodes φ, 2)
decreasing_by
  · -- None branch: delegate to ctx_rest.  4-tuple: comp 1, 2, 3 equal; phase strict.
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt
    right; refine ⟨rfl, ?_⟩
    right; refine ⟨rfl, ?_⟩
    right; exact ⟨rfl, by decide⟩
  · -- Case A, first MU call: comp 1 strict — V_ext.pd drops by 1 + V1.pd
    -- (S = V1×V2 opened to v1:V1, v2:V2) while bpd is preserved by
    -- unpair/casts.
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    simp only [VarCtx.pairDepth_insert]
    have hS_pd : S.pairDepth = 1 + V1.pairDepth + V2.pairDepth := by
      rw [h_S_eq]; rfl
    change V1.pairDepth + (V2.pairDepth + V.pairDepth)
             + WFF.binderPairDepth φ'_cast
         < S.pairDepth + V.pairDepth + WFF.binderPairDepth φ
    omega
  · -- Case A, second MU call: comp 1 strict — V_ext.pd drops by 1 + V1.pd
    -- and bpd(result1.val) ≤ bpd φ via h_r1_bpd (the Σ' payoff).
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    simp only [VarCtx.pairDepth_insert]
    have hS_pd : S.pairDepth = 1 + V1.pairDepth + V2.pairDepth := by
      rw [h_S_eq]; rfl
    change V2.pairDepth + V.pairDepth + WFF.binderPairDepth result1.val
         < S.pairDepth + V.pairDepth + WFF.binderPairDepth φ
    omega
  · -- Case A .pair_elim MU call: comp 1 strict via h_measure_lt (hoisted
    -- pd arithmetic) + h_in_bpdA (bpd preserved through unpair/casts).
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    simp only [VarCtx.pairDepth_insert]
    change (V1.VTypeProd V2).pairDepth + peV_v1v2.pairDepth
             + WFF.binderPairDepth φ'A_cast
         < S.pairDepth + V.pairDepth + WFF.binderPairDepth φ
    omega
  · -- Case B MU call: comp 1 (V_ext.pd + bpd) strict via unpair_lt + bpd
    -- preserved.  4-tuple structure: use `left` at the outer.
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
    have h_pd_lt : V_minus_z_v1v2.pairDepth < V.pairDepth :=
      VarCtx.pairDepth_unpair_lt hzmem_V hv1_Vmz hv2_Vmz hv1v2_ne
    have h_bpd_eq :
        WFF.binderPairDepth φ'_cast = WFF.binderPairDepth φ := by
      show WFF.binderPairDepth (h_cast_φ' ▸ φ') = _
      rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_unpair,
          WFF.binderPairDepth_ctx_cast]
    rw [VarCtx.pairDepth_insert, VarCtx.pairDepth_insert]
    show (⟨x, S⟩ : VarSymb × VarType).2.pairDepth + V_minus_z_v1v2.pairDepth
           + WFF.binderPairDepth φ'_cast
         < (⟨x, S⟩ : VarSymb × VarType).2.pairDepth + V.pairDepth
           + WFF.binderPairDepth φ
    rw [h_bpd_eq]
    omega

-- Helper for `WFF.ctx_rest`'s `.all`/`.ex` arms.
def WFF.ctx_rest_quant_arm {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (_h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (is_ex : Bool)
    (x_a : VarSymb × VarType)
    (hx_a : x_a.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨x, S⟩ V hx))
    (ψ : WFF σ (VarCtx_insert x_a (VarCtx_insert ⟨x, S⟩ V hx) hx_a))
    : {res : WFF σ V // WFF.binderPairDepth res
         ≤ x_a.2.pairDepth + WFF.binderPairDepth ψ} := by
  have hxa_V : x_a.1 ∉ VarCtx_to_VarSymbs V := by
    intro h; apply hx_a
    rw [VarCtx_to_VarSymbs_insert]
    exact Finset.mem_insert_of_mem h
  have hxa_ne_x : x_a.1 ≠ x := by
    intro heq; apply hx_a
    rw [VarCtx_to_VarSymbs_insert]
    exact Finset.mem_insert.mpr (Or.inl heq)
  have hx_xaV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert x_a V hxa_V) :=
    not_mem_VarSymbs_insert (fun h => hxa_ne_x h.symm) hx
  have h_ψ_ctx :
      VarCtx_insert x_a (VarCtx_insert ⟨x, S⟩ V hx) hx_a =
      VarCtx_insert ⟨x, S⟩ (VarCtx_insert x_a V hxa_V) hx_xaV :=
    VarCtx_ext _ _ (Finset.insert_comm _ _ _)
  let result := WFF.ctx_rest_MU hx_xaV (Term.ctx_ext x_a hxa_V s) (h_ψ_ctx ▸ ψ)
  refine ⟨bif is_ex then .ex x_a (hx := hxa_V) result.val
                    else .all x_a (hx := hxa_V) result.val, ?_⟩
  cases is_ex
  · simp only [Bool.cond_false, WFF.binderPairDepth]
    refine Nat.add_le_add_left ?_ _
    refine le_trans result.property ?_
    rw [WFF.binderPairDepth_ctx_cast]
  · simp only [Bool.cond_true, WFF.binderPairDepth]
    refine Nat.add_le_add_left ?_ _
    refine le_trans result.property ?_
    rw [WFF.binderPairDepth_ctx_cast]
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + x_a.2.pairDepth
                  + WFF.binderPairDepth ψ,
                WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  -- quant_arm → MU: comp 1 (V_ext.pd + bpd) equal, comp 2 (dC) equal, comp 3
  -- (numNodes) strict.  4-tuple structure.
  all_goals (
    apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt
    right
    refine ⟨?_, ?_⟩
    · simp only [WFF.binderPairDepth_ctx_cast, VarCtx.pairDepth_insert]; omega
    · right; refine ⟨?_, ?_⟩
      · simp only [WFF.diaCount_ctx_cast]
      · left; simp only [WFF.numNodes_ctx_cast]; omega)

-- Helper for `WFF.ctx_rest`'s `.box` arm.  Mirrors `Term.ctx_rest`'s
-- `.boxterm` arm: case-analyse on whether x ∈ V_inner.  If yes, force
-- S = T.VTypeBox, match s as `.boxterm`, recurse via WFF.ctx_rest_MU
-- on ψ at the smaller V_inner_minus_x context.  If no, trivial passthrough.
def WFF.ctx_rest_box_arm {σ : Signature} {V : VarCtx} {V_inner : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (ψ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (h_no_extras : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
                   VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    : {res : WFF σ V // WFF.binderPairDepth res ≤ WFF.binderPairDepth ψ} := by
  by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
  · -- x ∈ V_inner: forces S = T.VTypeBox.  Match s as `.boxterm`; recurse.
    cases S with
    | Var =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeOne =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeDia _ =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeProd _ _ =>
        exfalso
        obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
        simp only at hx'_eq; subst hx'_eq
        have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                          ∈ (VarCtx_box V_inner).1 :=
          Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
        rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    | VTypeBox T =>
        by_cases hxT_in : (⟨x, T⟩ : VarSymb × VarType) ∈ V_inner.1
        · let V_inner_minus_x : VarCtx := VarCtx_erase V_inner ⟨x, T⟩
          have hx_minus : x ∉ VarCtx_to_VarSymbs V_inner_minus_x :=
            VarCtx_erase_fresh hxT_in
          have h_V_inner_eq :
              V_inner = VarCtx_insert ⟨x, T⟩ V_inner_minus_x hx_minus :=
            (VarCtx_insert_erase hxT_in hx_minus).symm
          match s with
          | @Term.boxterm _ V_s _ _ s_inner s_hsub s_h_no_extras =>
              have h_V_eq : V_s = V_inner_minus_x :=
                ctx_rest_box_V_s_eq hxT_in hsub h_no_extras
                  s_hsub s_h_no_extras
              subst h_V_eq
              let ψ_cast : WFF σ
                  (VarCtx_insert ⟨x, T⟩ V_inner_minus_x hx_minus) :=
                h_V_inner_eq ▸ ψ
              let ψ_new := WFF.ctx_rest_MU hx_minus s_inner ψ_cast
              exact ⟨.box ψ_new.val s_hsub s_h_no_extras, by
                refine le_trans ψ_new.property ?_
                simp only [ψ_cast, WFF.binderPairDepth_ctx_cast]
                exact le_refl _⟩
          | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
              exfalso
              have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                  ∈ V.1 := by
                rw [← sw2eq]; exact Finset.mem_insert_self _ _
              have h_sz_in_Vext :
                  (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈
                  (VarCtx_insert ⟨x, T.VTypeBox⟩ V hx).1 :=
                Finset.mem_insert_of_mem h_sz_in_V
              exact VarCtx.firstPairVar_none_no_pair h_pf h_sz_in_Vext
        · exfalso
          obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
          simp only at hx'_eq; subst hx'_eq
          have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
          rcases Finset.mem_insert.mp (hsub hx'box_in) with h_eq | h_in_V
          · have : T'.VTypeBox = T.VTypeBox := (Prod.mk.inj h_eq).2
            have hT_eq : T' = T := VarType.VTypeBox.inj this
            subst hT_eq
            exact hxT_in hx'T'
          · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
  · -- x ∉ V_inner: trivial passthrough.
    have hsub' : (VarCtx_box V_inner).1 ⊆ V.1 := by
      intro p hp
      rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
      · subst h_eq
        exfalso
        rcases Finset.mem_image.mp hp with ⟨w, hw, hweq⟩
        exact h_x_in
          (Finset.mem_image.mpr ⟨w, hw, (Prod.mk.inj hweq).1⟩)
      · exact h_V
    have h_no_extras' :
        ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1 :=
      fun p hp h_box => h_no_extras p (Finset.mem_insert_of_mem hp) h_box
    exact ⟨.box ψ hsub' h_no_extras', Nat.le_refl _⟩
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth ψ,
                WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  -- box_arm Case 2 → MU: comp 1 ≥ (by hsub), comp 3 (numNodes) STRICT when equal.
  -- 4-tuple: (V_ext.pd + bpd, dC, numNodes, phase).
  all_goals (
    have hS_eq : S = T.VTypeBox := ‹S = T.VTypeBox›
    subst hS_eq
    have h_le := VarCtx.pairDepth_le_of_box_subset hsub
    have h_V_inner_pd : V_inner.pairDepth =
        T.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := by
      conv_lhs => rw [h_V_inner_eq]
      exact VarCtx.pairDepth_insert _ _ _
    have h_v_min_unfold :
        V_inner_minus_x.pairDepth = (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := rfl
    have h_ext_pd : (VarCtx_insert ⟨x, T.VTypeBox⟩ V hx).pairDepth
                    = T.pairDepth + V.pairDepth := by
      rw [VarCtx.pairDepth_insert]
      rfl
    have h_key : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth ≤ V.pairDepth := by
      rw [h_ext_pd] at h_le
      omega
    by_cases h_lt : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth < V.pairDepth
    · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
      simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
      show T.pairDepth + _ + _ < T.pairDepth + _ + _
      omega
    · have h_eq : (VarCtx_erase V_inner ⟨x, T⟩).pairDepth = V.pairDepth := by omega
      apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
      refine ⟨?_, ?_⟩
      · simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
        show T.pairDepth + _ + _ = T.pairDepth + _ + _
        omega
      · right; refine ⟨?_, ?_⟩
        · simp only [WFF.diaCount_ctx_cast]
        · left; simp only [WFF.numNodes_ctx_cast]; omega)

-- Helper for `WFF.ctx_rest`'s `.dia` arm.  Mirrors `Term.ctx_rest`'s
-- `.diaterm` arm.  Three cases:
--   1. xv.1 = x: modal beta (TODO: currently stub).
--   2. xv.1 ≠ x AND x ∈ V_inner: recurse into ψ via MU after lifting s.
--   3. xv.1 ≠ x AND x ∉ V_inner: trivial passthrough.
def WFF.ctx_rest_dia_arm {σ : Signature} {V : VarCtx} {V_inner : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (h_no_extras : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1,
                   VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1)
    : {res : WFF σ V // WFF.binderPairDepth res ≤ WFF.binderPairDepth ψ} := by
  by_cases h_xv_eq_x : xv.1 = x
  · -- Case 3: xv.1 = x. Modal-beta reduction. Step 0-1: uniqueness + destructure s.
    have hxv_in_Vext : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈
        (VarCtx_insert ⟨x, S⟩ V hx).1 := by
      apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
    have h_S_eq : S = xv.2.VTypeDia := by
      rcases Finset.mem_insert.mp hxv_in_Vext with h_eq | h_in_V
      · exact ((Prod.mk.inj h_eq).2).symm
      · exfalso
        exact hx (Finset.mem_image.mpr ⟨_, h_in_V, h_xv_eq_x⟩)
    let s_dia : Term σ V xv.2.VTypeDia := h_S_eq ▸ s
    match s_dia with
    | @Term.diaterm _ V_inner_s _ _ xv_s hxv_s tt_s hsub_s h_no_extras_s =>
        -- Step 2: V_inner_s = V_inner via VarCtx_box_inj + no-extras.
        have h_V_inner_eq : V_inner_s = V_inner := by
          apply VarCtx_box_inj
          apply VarCtx_ext
          apply Finset.ext
          intro p
          constructor
          · intro hp_s
            have hp_V : p ∈ V.1 := by
              apply hsub_s
              rw [VarCtx_dia_fst]
              exact Finset.mem_insert_of_mem hp_s
            have hp_box : VarType.isBox p.2 = true := by
              rcases Finset.mem_image.mp hp_s with ⟨q, _, hq_eq⟩
              rw [← hq_eq]; simp [VarType.isBox]
            have hp_Vext : p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1 :=
              Finset.mem_insert_of_mem hp_V
            have hp_dia := h_no_extras p hp_Vext hp_box
            rw [VarCtx_dia_fst] at hp_dia
            rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
            · subst h_eq; simp [VarType.isBox] at hp_box
            · exact h_in_box
          · intro hp
            have hp_Vext : p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1 := by
              apply hsub
              rw [VarCtx_dia_fst]
              exact Finset.mem_insert_of_mem hp
            have hp_box : VarType.isBox p.2 = true := by
              rcases Finset.mem_image.mp hp with ⟨q, _, hq_eq⟩
              rw [← hq_eq]; simp [VarType.isBox]
            have hp_V : p ∈ V.1 := by
              rcases Finset.mem_insert.mp hp_Vext with h_eq | h_V
              · subst h_eq
                rw [h_S_eq] at hp_box
                simp [VarType.isBox] at hp_box
              · exact h_V
            have hp_dia := h_no_extras_s p hp_V hp_box
            rw [VarCtx_dia_fst] at hp_dia
            rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
            · subst h_eq; simp [VarType.isBox] at hp_box
            · exact h_in_box
        cases h_V_inner_eq
        -- Step 3: derive xv_s.1 ≠ x, i.e., xv.1 ≠ xv_s.1.
        have hxv_s_ne_x : xv_s.1 ≠ x := by
          intro h
          apply hx
          apply Finset.mem_image.mpr
          refine ⟨⟨xv_s.1, xv_s.2.VTypeDia⟩, ?_, h⟩
          apply hsub_s
          rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        have h_xv_ne_xv_s : xv.1 ≠ xv_s.1 :=
          fun h => hxv_s_ne_x (h ▸ h_xv_eq_x)
        -- Step 4: use reorder helper to produce ψ_for_sub in the target context.
        obtain ⟨h_x_inner, ψ_for_sub, h_bpd_eq, h_dC_eq⟩ :=
          WFF.dia_arm_case3_reorder xv xv_s hxv hxv_s h_xv_ne_xv_s h_xv_eq_x ψ
        -- Step 5: recursive MU substitution at x with witness tt_s.
        let result_sub := WFF.ctx_rest_MU h_x_inner tt_s ψ_for_sub
        -- Step 6: wrap in .dia xv_s producing WFF σ V via hsub_s / h_no_extras_s.
        exact ⟨.dia xv_s hxv_s result_sub.val hsub_s h_no_extras_s, by
          refine le_trans result_sub.property ?_
          exact le_of_eq h_bpd_eq⟩
    | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
        exfalso
        have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
            ∈ V.1 := by
          rw [← sw2eq]; exact Finset.mem_insert_self _ _
        exact VarCtx.firstPairVar_none_no_pair h_pf
          (Finset.mem_insert_of_mem h_sz_in_V)
  · by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
    · -- Case 2: xv.1 ≠ x AND x ∈ V_inner.  Mirrors box arm with hxv lift.
      cases S with
      | Var | VTypeOne | VTypeDia _ | VTypeProd _ _ =>
          exfalso
          obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
          simp only at hx'_eq; subst hx'_eq
          have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                            ∈ (VarCtx_box V_inner).1 :=
            Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
          have hx'box_in_dia : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hx'box_in
          rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
          all_goals first
            | exact VarType.noConfusion (Prod.mk.inj h_eq).2
            | exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
      | VTypeBox T =>
          by_cases hxT_in : (⟨x, T⟩ : VarSymb × VarType) ∈ V_inner.1
          · let V_inner_minus_x : VarCtx := VarCtx_erase V_inner ⟨x, T⟩
            have hx_minus : x ∉ VarCtx_to_VarSymbs V_inner_minus_x :=
              VarCtx_erase_fresh hxT_in
            have hxv_minus : xv.1 ∉ VarCtx_to_VarSymbs V_inner_minus_x :=
              fun h => hxv (VarCtx_to_VarSymbs_erase_subset h)
            match s with
            | @Term.boxterm _ V_s _ _ s_inner s_hsub s_h_no_extras =>
                have h_V_eq : V_s = V_inner_minus_x :=
                  ctx_rest_dia_V_s_eq hxT_in hsub h_no_extras s_hsub
                    s_h_no_extras
                subst h_V_eq
                let s_lifted :
                    Term σ (VarCtx_insert xv V_inner_minus_x hxv_minus) T :=
                  Term.ctx_ext xv hxv_minus s_inner
                have hx_in_outer :
                    x ∉ VarCtx_to_VarSymbs
                          (VarCtx_insert xv V_inner_minus_x hxv_minus) :=
                  not_mem_VarSymbs_insert
                    (fun h => h_xv_eq_x h.symm) hx_minus
                have h_combined :
                    VarCtx_insert xv V_inner hxv =
                    VarCtx_insert ⟨x, T⟩
                      (VarCtx_insert xv V_inner_minus_x hxv_minus)
                      hx_in_outer := by
                  apply VarCtx_ext
                  change insert xv V_inner.1 =
                       insert ⟨x, T⟩ (insert xv V_inner_minus_x.1)
                  rw [Finset.insert_comm]
                  congr 1
                  show V_inner.1 = insert ⟨x, T⟩ V_inner_minus_x.1
                  exact (Finset.insert_erase hxT_in).symm
                let ψ_cast : WFF σ
                    (VarCtx_insert ⟨x, T⟩
                      (VarCtx_insert xv V_inner_minus_x hxv_minus)
                      hx_in_outer) :=
                  h_combined ▸ ψ
                let ψ_new := WFF.ctx_rest_MU hx_in_outer s_lifted ψ_cast
                exact ⟨.dia xv hxv_minus ψ_new.val
                  (ctx_rest_dia_hsub_erase hxv_minus
                    (fun h => h_xv_eq_x h) hsub)
                  (ctx_rest_dia_h_no_extras_erase hxv_minus h_no_extras), by
                  refine le_trans ψ_new.property ?_
                  simp only [ψ_cast, WFF.binderPairDepth_ctx_cast]
                  exact le_refl _⟩
            | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
                exfalso
                have h_sz_in_V : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType)
                    ∈ V.1 := by
                  rw [← sw2eq]; exact Finset.mem_insert_self _ _
                have h_sz_in_Vext :
                    (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈
                    (VarCtx_insert ⟨x, T.VTypeBox⟩ V hx).1 :=
                  Finset.mem_insert_of_mem h_sz_in_V
                exact VarCtx.firstPairVar_none_no_pair h_pf h_sz_in_Vext
          · exfalso
            obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
            simp only at hx'_eq; subst hx'_eq
            have hx'box_in : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType)
                              ∈ (VarCtx_box V_inner).1 :=
              Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
            have hx'box_in_dia :
                (⟨x', T'.VTypeBox⟩ : VarSymb × VarType) ∈
                  (VarCtx_dia xv V_inner hxv).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hx'box_in
            rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
            · have hT_eq : T' = T :=
                VarType.VTypeBox.inj (Prod.mk.inj h_eq).2
              subst hT_eq
              exact hxT_in hx'T'
            · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
    · -- Case 1: xv.1 ≠ x AND x ∉ V_inner.  Trivial passthrough.
      have hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1 := by
        rw [VarCtx_dia_fst]
        intro p hp
        rcases Finset.mem_insert.mp hp with h_eq | hp_box
        · subst h_eq
          have hp_in_dia : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈
                            (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
          rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq' | h_in_V
          · exact absurd (Prod.mk.inj h_eq').1 h_xv_eq_x
          · exact h_in_V
        · have hp_in_dia : p ∈ (VarCtx_dia xv V_inner hxv).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_box
          rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq | h_in_V
          · subst h_eq
            exfalso
            apply h_x_in
            rcases Finset.mem_image.mp hp_box with ⟨q, hq_in, hq_eq⟩
            cases q with
            | mk qv qT =>
              refine Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, ?_⟩
              exact (Prod.mk.inj hq_eq).1
          · exact h_in_V
      have h_no_extras' :
          ∀ p ∈ V.1, VarType.isBox p.2 = true →
            p ∈ (VarCtx_dia xv V_inner hxv).1 :=
        fun p hp h_box => h_no_extras p (Finset.mem_insert_of_mem hp) h_box
      exact ⟨.dia xv hxv ψ hsub' h_no_extras', Nat.le_refl _⟩
termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth ψ,
                1 + WFF.diaCount ψ, 1 + WFF.numNodes ψ, 0)
decreasing_by
  -- dia_arm two recursive MU goals.  Since bpd's `.dia` clause no longer
  -- adds the binder's pairDepth, the measure drops its xv.2.pairDepth term
  -- (comp 1 = V_ext.pd + bpd ψ); comp 2 keeps the 1 + dC ψ gap.
  --  * Case 2 (S = T.VTypeBox): comp 1 ≤ via dia-subset; comp 2 STRICT via +1.
  --  * Case 3 (modal beta): comp 1 ≤ via dia-subset; comp 2 STRICT via +1.
  all_goals first
    | (-- Case 2
       have hS_eq : S = T.VTypeBox := by assumption
       subst hS_eq
       have h_le := VarCtx.pairDepth_le_of_dia_subset hsub
       have h_V_inner_pd : V_inner.pairDepth =
           T.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := by
         conv_lhs => rw [show V_inner = VarCtx_insert ⟨x, T⟩
           (VarCtx_erase V_inner ⟨x, T⟩) hx_minus from
           (VarCtx_insert_erase hxT_in hx_minus).symm]
         exact VarCtx.pairDepth_insert _ _ _
       have h_v_min_unfold :
           V_inner_minus_x.pairDepth = (VarCtx_erase V_inner ⟨x, T⟩).pairDepth := rfl
       have h_ext_pd : (VarCtx_insert ⟨x, T.VTypeBox⟩ V hx).pairDepth
                       = T.pairDepth + V.pairDepth := by
         rw [VarCtx.pairDepth_insert]
         rfl
       have h_le' : (VarCtx_insert xv V_inner hxv).pairDepth
                     ≤ T.pairDepth + V.pairDepth := by
         rw [h_ext_pd] at h_le; exact h_le
       have h_insert_xv_pd :
           (VarCtx_insert xv V_inner hxv).pairDepth
             = xv.2.pairDepth + V_inner.pairDepth :=
         VarCtx.pairDepth_insert _ _ _
       have h_key : xv.2.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth
                     ≤ V.pairDepth := by
         rw [h_insert_xv_pd, h_V_inner_pd] at h_le'
         omega
       -- comp 1: new = T.pd + (xv.2.pd + V_inner_minus_x.pd) + bpd ψ_cast;
       -- outer = T.pd + V.pd + bpd ψ.  Diff ≥ 0 via h_key.
       -- Split into new < outer (comp 1 strict) vs new = outer (comp 2 strict).
       by_cases h_c1_lt :
           xv.2.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth
             < V.pairDepth
       · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
         simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
         show T.pairDepth + _ + _ < T.pairDepth + _ + _
         omega
       · have h_c1_eq :
             xv.2.pairDepth + (VarCtx_erase V_inner ⟨x, T⟩).pairDepth
               = V.pairDepth := by omega
         apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
         refine ⟨?_, ?_⟩
         · simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth_ctx_cast]
           show T.pairDepth + _ + _ = T.pairDepth + _ + _
           omega
         · left; simp only [WFF.diaCount_ctx_cast]; omega)
    | (-- Case 3 (modal beta): MU call on ψ_for_sub / tt_s from reorder helper.
       have hS_eq : S = xv.2.VTypeDia := by assumption
       subst hS_eq
       have h_le := VarCtx.pairDepth_le_of_dia_subset hsub_s
       have h_le' : xv_s.2.pairDepth + V_inner.pairDepth ≤ V.pairDepth := by
         rw [VarCtx.pairDepth_insert] at h_le; exact h_le
       have h_VTypeDia_pd : xv.2.VTypeDia.pairDepth = xv.2.pairDepth := rfl
       -- comp 1: new = xv.2.pd + xv_s.2.pd + V_inner.pd + bpd (via h_bpd_eq)
       -- outer = xv.2.VTypeDia.pd + V.pd + bpd = xv.2.pd + V.pd + bpd.
       -- Diff = V.pd - xv_s.2.pd - V_inner.pd ≥ 0 via h_le'.
       -- comp 2: new = dC ψ_for_sub = dC ψ (via h_dC_eq); outer = 1 + dC ψ.  Strict.
       by_cases h_c1_lt :
           xv_s.2.pairDepth + V_inner.pairDepth < V.pairDepth
       · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; left
         simp only [VarCtx.pairDepth_insert, h_VTypeDia_pd, h_bpd_eq]
         omega
       · apply Prod.Lex.of_lt_or_eq_lt_or_eq_lt_or_eq_lt; right
         refine ⟨?_, ?_⟩
         · simp only [VarCtx.pairDepth_insert, h_VTypeDia_pd, h_bpd_eq]
           omega
         · left; simp only [h_dC_eq]; omega)

end

-- Preservation of `binderPairDepth` under the substitution machinery is now
-- carried by the Σ'-subtype returns of the functions themselves (each
-- returns `{res // bpd res ≤ bound}`; Case A .pair/.pair_elim are fully
-- implemented, using the first recursive call's `.property` for the second
-- call's termination).  The previous standalone mutual theorem block is
-- superseded by `.property` projections, kept as named lemmas:
theorem WFF.binderPairDepth_ctx_rest_MU_le {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.ctx_rest_MU hx s φ).val
      ≤ WFF.binderPairDepth φ :=
  (WFF.ctx_rest_MU hx s φ).property

theorem WFF.binderPairDepth_ctx_rest_le {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.ctx_rest hx h_pf s φ).val
      ≤ WFF.binderPairDepth φ :=
  (WFF.ctx_rest hx h_pf s φ).property

/-! ### Variable instantiation (public API) -/

-- Substitute the free variable `x : S` by the term `s : Term σ V S`
-- throughout `φ`, discharging `x` from the context: `φ` lives in `V + x`,
-- the result lives in `V`.  This is THE substitution operation the proof
-- system's quantifier/modal rules use (∀-elim, ∃-intro, modal beta).
--
-- Thin wrapper over the Σ'-subtype machinery: `WFF.ctx_rest_MU` handles
-- pair-typed variables (Case A), pair vars elsewhere in the context
-- (Case B), and the pair-free structural pass, and carries the
-- `binderPairDepth` bound intrinsically.
def WFF.substVar {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) : WFF σ V :=
  (WFF.ctx_rest_MU hx s φ).val

theorem WFF.binderPairDepth_substVar_le {σ : Signature} {V : VarCtx}
    {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (s : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.binderPairDepth (WFF.substVar hx s φ) ≤ WFF.binderPairDepth φ :=
  (WFF.ctx_rest_MU hx s φ).property

/-! ## Proof System (Natural Deduction) -/

/-! ### Modal context bridging lemmas

    Convert a `dia`-context side condition into the corresponding `box`-context
    one, so that `□Γ` and `◇ₓψ` can inhabit the same outer context `W` in the
    modal rules (`K_dia`, `Mlem`). -/

lemma in_box_of_in_dia {x : VarSymb × VarType} {V W : VarCtx} {hx : x.1 ∉ VarCtx_to_VarSymbs V}
    (in_dia : ∀ p ∈ W.1, p.2.isBox = true → p ∈ (VarCtx_dia x V hx).fst) :
    ∀ p ∈ W.1, p.2.isBox = true → p ∈ (VarCtx_box V).fst := by
  rintro p pmemW pbox
  have pmem := in_dia p pmemW pbox
  unfold VarCtx_dia at pmem
  simp only [Finset.mem_insert] at pmem
  rcases pmem with diacase | boxcase
  · exfalso
    have : p.2.isBox = false := by
      rw [diacase]
      exact Bool.eq_false_of_le_false fun a ↦ a
    rw [pbox] at this
    exact (Bool.true_eq_false_eq_False this)
  · exact boxcase


lemma box_subs_of_dia_subs {x : VarSymb × VarType} {V W : VarCtx} {hx : x.1 ∉ VarCtx_to_VarSymbs V}
    (dia_in_W : (VarCtx_dia x V hx).fst ⊆ W.fst) :
    (VarCtx_box V).fst ⊆ W.fst := by
  intros y ybox
  have : y ∈  (VarCtx_dia x V hx).fst := by
    unfold VarCtx_dia
    simp only [Finset.mem_insert]
    exact Or.inr ybox
  exact dia_in_W this

/-! ### Deduction rules

    `Proof σ V Γ φ` is the type of derivations of `φ` from hypotheses `Γ` in
    context `V`.  Classical natural deduction (structural, propositional,
    quantifier, and equality rules) plus Fitch-style modal K.  Freshness /
    eigenvariable side conditions are discharged by the context typing rather
    than carried as premises. -/

/-- A `pair_elim` body α-renamed `v₁ → n₁` and `v₂ → n₂` (to fresh names of the same type):
    outer rename of `v₁` (`rfl` `Wdef`), then inner rename of `v₂` (`VarCtx_insert_comm` `Wdef`).
    Result lands over the *commuted* context `insert ⟨n₂,·⟩ (insert ⟨n₁,·⟩ V)` — no final cast; the
    commute is absorbed into `pair_elim`'s free `w₁'eq`.  Factored out of `Proof.pair_elim_alpha`. -/
def Term.pairElimAlphaBody {σ : Signature} (v₁ v₂ : VarSymb × VarType) (n₁ n₂ : VarSymb)
    {V : VarCtx} (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V) (hn₁ : n₁ ∉ VarCtx_to_VarSymbs V)
    (hn₁n₂ : n₁ ≠ n₂)
    (hv₁_nest : v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂))
    (hn₁_nest : n₁ ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂))
    (hv₂_nest : v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁))
    (hn₂_nest : n₂ ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁))
    {S : VarType} (body : Term σ (VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest) S)
    (nnb₁ : n₁ ∉ Term.boundVars body) (nnb₂ : n₂ ∉ Term.boundVars body) :
    Term σ (VarCtx_insert ⟨n₂, v₂.2⟩ (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁) hn₂_nest) S :=
  Term.rename v₂.1 n₂ v₂.2 (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁)
    (VarCtx_insert ⟨n₁, v₁.2⟩ (VarCtx_insert v₂ V hv₂) hn₁_nest) S
    hv₂_nest hn₂_nest (VarCtx_insert_comm hn₁_nest hv₂_nest)
    (Term.rename v₁.1 n₁ v₁.2 (VarCtx_insert v₂ V hv₂)
      (VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest) S hv₁_nest hn₁_nest rfl body nnb₁)
    (fun h =>
      (Finset.mem_insert.mp (Term.boundVars_rename_subset v₁.1 n₁ v₁.2 (VarCtx_insert v₂ V hv₂)
          (VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest) S hv₁_nest hn₁_nest rfl body nnb₁ h)).elim
        (fun heq => hn₁n₂ heq.symm) nnb₂)

inductive Proof (σ : Signature) : (V : VarCtx) → Finset (WFF σ V) → WFF σ V → Type where
  -- Structural rules
  | ax       : φ ∈ (Γ : Finset (WFF σ V))
               → Proof σ V Γ φ
  | weak     : Proof σ V Γ φ
               → Proof σ V (Γ ∪ {ψ}) φ
  | weak_ctx : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
               → Proof σ V Γ φ
               → Proof σ (VarCtx_insert x V hx) (WFF.ctx_ext_Finset x hx Γ) (WFF.ctx_ext x hx φ)
  -- Conjunction
  | and_intro  : Proof σ V Γ φ → Proof σ V Γ ψ
                 → Proof σ V Γ (φ.and ψ)
  | and_elim_l : Proof σ V Γ (φ.and ψ) → Proof σ V Γ φ
  | and_elim_r : {φ : WFF σ V}
                 → Proof σ V Γ (φ.and ψ) → Proof σ V Γ ψ
  -- Disjunction
  | or_intro_l : Proof σ V Γ φ → Proof σ V Γ (φ.or ψ)
  | or_intro_r : {φ : WFF σ V}
                 → Proof σ V Γ ψ → Proof σ V Γ (φ.or ψ)
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
  | lem        : (φ : WFF σ V) →  Proof σ V Γ (φ.or (neg φ))
  -- Universal quantifier
  -- Introduction: prove φ in the extended context V ∪ {x}, with x fresh.
  | all_intro  : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert x V hx)}
                 → Proof σ (VarCtx_insert x V hx) (WFF.ctx_ext_Finset x hx Γ) φ
                 → Proof σ V Γ (.all x φ)
  -- Elimination: from ∀x.φ and a term t : Term σ V, get φ[t/x] back in context V.
  | all_elim   : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert x V hx)}
                 → (t : Term σ V x.2)
                 → Proof σ V Γ (.all x φ)
                 → Proof σ V Γ (WFF.substVar hx t φ)
  -- Existential quantifier
  -- Introduction: provide a witness t : Term σ V and a proof of φ[s/x].
  | ex_intro   : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert x V hx)}
                 → (t : Term σ V x.2)
                 → Proof σ V Γ (WFF.substVar hx t φ)
                 → Proof σ V Γ (.ex x φ)
  -- Elimination: from ∃x.φ, derive ψ given that ψ holds with x as a fresh variable.
  | ex_elim    : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {φ : WFF σ (VarCtx_insert x V hx)}
                 → Proof σ V Γ (.ex x φ)
                 → Proof σ (VarCtx_insert x V hx) ((WFF.ctx_ext_Finset x hx Γ) ∪ {φ}) (WFF.ctx_ext x hx ψ)
                 → Proof σ V Γ ψ
  -- Equality
  -- Introduction: given a term t, get t = t
  | eq_intro   : (t : Term σ V S) → Proof σ V Γ (WFF.eq t t)
  -- Elimination: given t = s, sub t for s
  | eq_elim : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
            → {φ : WFF σ (VarCtx_insert x V hx)} → (t s : Term σ V x.2)
            → Proof σ V Γ (WFF.eq t s)
            → Proof σ V Γ (WFF.substVar hx t φ)
            → Proof σ V Γ (WFF.substVar hx s φ)
  -- Pairing
  | pair_elim : (v₁ v₂ : VarSymb × VarType) → (z : VarSymb)
                 → (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) → (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
                 → (hv₁v₂ : v₁.1 ≠ v₂.1) → (hz : z ∉ VarCtx_to_VarSymbs V)
                 → (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
                 → (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
                 → Proof σ W₁ Γ φ
                 → Proof σ W₂ (WFF.pairElim_Finset v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq Γ)
                   (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ)
  -- Modal K rules
  -- K box rule
  | K_box : (hsub : (VarCtx_box V).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
                 → Proof σ V Γ φ
                 → Proof σ W (WFF.box_Finset hsub h_no_box_extras Γ)
                  (WFF.box φ hsub h_no_box_extras)
  -- General modal-`K` rule for `◇_x` (the multi-conclusion K rule, single-conclusion form): from
  -- `Γ, Δ, ψ ⊢ φ` conclude `□Γ, □_x Δ, ◇_x ψ ⊢ ◇_x φ`.  `Γ` is `x`-free (plain `□`); `Δ` may mention
  -- the witness `x` (witnessed box `□_x = ¬◇_x¬`).  Subsumes the old plain-`□`-only `K_dia`
  -- (`Δ = ∅`) and the witnessed-only `K_dia_x` (`Γ = ∅`); the `□`↔`◇_x` bridge (e.g. `□φ ⊢ □_x φ`)
  -- and the box_x-hypothesis transfer needed for canonical-model completeness both live here.
  | K_dia : (x : VarSymb × VarType)
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
  -- (A witness-only `K_dia_pure` — `□Γ ⊢ ◇_x φ` with no `◇`-formula hypothesis — was tried and
  -- removed: under the existential `◇` semantics `◇_x ⊤` asserts the possible object `x` is
  -- *nonempty*, which fails for the empty (impossible) possible object.  A possible object may be
  -- empty, so `⊤ ⊢ ◇_x⊤` is correctly not a theorem.)
  -- contradictions are not possible: this can be dropped in some intuitionistic versions
  | dia_bot : (x : VarSymb × VarType)
                 → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → {W : VarCtx}
                 → (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
                 → {Γ : Finset (WFF σ W)}
                 → Proof σ W Γ (WFF.dia x hx WFF.bot hsub h_no_box_extras)
                 → Proof σ W Γ WFF.bot
  -- (The "modal LEM" `Mlem` has been removed: with the object-witness `◇_x` it is a disguised
  -- coverage/Barcan axiom, unsound over general models.  The de-dicto version `□φ ∨ ◇' ¬φ`
  -- (using `WFF.dia'`) is just `lem` and is derivable.)
  -- World-extensionality (funext / Σ-ext): necessarily / possibly equal box / dia
  -- terms are equal.  Both conclusions are `necIntro` / `posIntro` of the equal
  -- section / witness the premise provides, so these are sound in *every* model
  -- (no `necEval` / `posEval` injectivity condition is required).
  | box_ext : {V W : VarCtx} → {S : VarType} → {Γ : Finset (WFF σ W)}
                 → (hsub : (VarCtx_box V).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1)
                 → (tt₁ tt₂ : Term σ V S)
                 → Proof σ W Γ (WFF.box (WFF.eq tt₁ tt₂) hsub h_no_box_extras)
                 → Proof σ W Γ (WFF.eq (Term.boxterm tt₁ hsub h_no_box_extras)
                  (Term.boxterm tt₂ hsub h_no_box_extras))
  | dia_ext : {V W : VarCtx} → {S : VarType} → {Γ : Finset (WFF σ W)}
                 → (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V)
                 → (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
                 → (h_no_box_extras :
                  ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
                 → (tt₁ tt₂ : Term σ (VarCtx_insert x V hx) S)
                 -- premise is `box_x (tt₁ ≐ tt₂)` = `¬◇_x¬(tt₁ ≐ tt₂)` = the terms agree at
                 -- *every* realization of `x` (existential `◇_x` gives only one — too weak).
                 → Proof σ W Γ (neg (WFF.dia x hx (neg (WFF.eq tt₁ tt₂)) hsub h_no_box_extras))
                 → Proof σ W Γ (WFF.eq (Term.diaterm x hx tt₁ hsub h_no_box_extras)
                  (Term.diaterm x hx tt₂ hsub h_no_box_extras))
  -- α-conversion for `pair_elim` — the ONLY term former with a genuine binder (`v₁`,`v₂` are
  -- consumed; `dia_x`'s `x` and `boxterm`'s variables are *promoted free* variables).  Renaming the
  -- bound variables to fresh `n₁,n₂` yields a provably-equal term.  NOT derivable: pair-β only fires
  -- on a *literal* pair, and there are no projections to η-expand a neutral `z` (projections are the
  -- *negative* product, commuting inward; `pair_elim` is *positive* and stays stuck outside).  So α
  -- among stuck `pair_elim`s is a primitive rule; soundness = α-invariance of `interpTerm`
  -- (= `interpTerm_rename`, twice, casts via `interpTerm_cast`).  The renamed body is `pairElimAlphaBody`
  -- (both indices; freshness side-conditions are the usual on-paper ones).
  | pair_elim_alpha :
      (v₁ v₂ : VarSymb × VarType) → (n₁ n₂ z : VarSymb)
      → (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) → (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
      → (hv₁v₂ : v₁.1 ≠ v₂.1) → (hz : z ∉ VarCtx_to_VarSymbs V)
      → (hn₁ : n₁ ∉ VarCtx_to_VarSymbs V) → (hn₂ : n₂ ∉ VarCtx_to_VarSymbs V)
      → (hn₁v₂ : n₁ ≠ v₂.1) → (hn₁n₂ : n₁ ≠ n₂)
      → (hv₁_nest : v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂))
      → (hn₁_nest : n₁ ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂))
      → (hv₂_nest : v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁))
      → (hn₂_nest : n₂ ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁))
      → (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂
                  = VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest)
      → (w₁'eq : VarCtx_insert_twice ⟨n₁, v₁.2⟩ ⟨n₂, v₂.2⟩ V hn₁ hn₂ hn₁n₂
                  = VarCtx_insert ⟨n₂, v₂.2⟩ (VarCtx_insert ⟨n₁, v₁.2⟩ V hn₁) hn₂_nest)
      → (w₂eq : VarCtx_insert ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
      → (body : Term σ (VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) hv₁_nest) S)
      → (nnb₁ : n₁ ∉ Term.boundVars body) → (nnb₂ : n₂ ∉ Term.boundVars body)
      → Proof σ W₂ Γ (WFF.eq
          (Term.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body)
          (Term.pair_elim ⟨n₁, v₁.2⟩ ⟨n₂, v₂.2⟩ z hn₁ hn₂ hn₁n₂ hz w₁'eq w₂eq
            (Term.pairElimAlphaBody v₁ v₂ n₁ n₂ hv₂ hn₁ hn₁n₂ hv₁_nest hn₁_nest hv₂_nest
              hn₂_nest body nnb₁ nnb₂)))


