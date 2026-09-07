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

/-! ### Pair-Elim Distribution (η-Normalisation) -/

/-! `WFF.pairElim`'s quantifier arms push the destructure *inside* the binder, α-renaming the
binder to a canonical fresh name.  Renaming unconditionally (rather than only on collision with
the new pair variable `z`) keeps the arm branch-free and makes the arm total on `all`/`ex`. -/

-- A binder fresh for `W₁ = V + v₁ + v₂` is automatically distinct from `v₁`/`v₂` and fresh for `V`.
theorem pairElim_binder_fresh {V W₁ : VarCtx} {v₁ v₂ : VarSymb × VarType}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1}
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    {y : VarSymb} (hy : y ∉ VarCtx_to_VarSymbs W₁) :
    y ≠ v₁.1 ∧ y ≠ v₂.1 ∧ y ∉ VarCtx_to_VarSymbs V := by
  subst w₁eq
  refine ⟨fun h => hy (Finset.mem_image.mpr ⟨v₁, Finset.mem_insert_self _ _, h.symm⟩),
          fun h => hy (Finset.mem_image.mpr
            ⟨v₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h.symm⟩),
          fun h => ?_⟩
  rcases Finset.mem_image.mp h with ⟨p, hp, hpeq⟩
  exact hy (Finset.mem_image.mpr
    ⟨p, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp), hpeq⟩)

theorem pairElim_quant_w₁eq {V W₁ : VarCtx} {v₁ v₂ : VarSymb × VarType}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1}
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    {y : VarSymb × VarType} (hyV : y.1 ∉ VarCtx_to_VarSymbs V)
    (hyW₁ : y.1 ∉ VarCtx_to_VarSymbs W₁)
    (hv₁y : v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert y V hyV))
    (hv₂y : v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert y V hyV)) :
    VarCtx_insert_twice v₁ v₂ (VarCtx_insert y V hyV) hv₁y hv₂y hv₁v₂
      = VarCtx_insert y W₁ hyW₁ := by
  subst w₁eq
  apply VarCtx_ext
  change insert v₁ (insert v₂ (insert y V.1)) = insert y (insert v₁ (insert v₂ V.1))
  rw [Finset.insert_comm v₂ y, Finset.insert_comm v₁ y]

theorem pairElim_quant_w₂eq {V W₂ : VarCtx} {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    {hz : z ∉ VarCtx_to_VarSymbs V}
    (w₂eq : VarCtx_insert ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    {y : VarSymb × VarType} (hyV : y.1 ∉ VarCtx_to_VarSymbs V)
    (hyW₂ : y.1 ∉ VarCtx_to_VarSymbs W₂)
    (hzy : z ∉ VarCtx_to_VarSymbs (VarCtx_insert y V hyV)) :
    VarCtx_insert ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ (VarCtx_insert y V hyV) hzy
      = VarCtx_insert y W₂ hyW₂ := by
  subst w₂eq
  exact VarCtx_insert_comm _ _

/-- The canonical fresh binder: avoids the new pair variable `z`, the ambient `W₁`, and the
    body's own binders (the last is `WFF.rename`'s capture-avoidance condition). -/
def pairElim_qy (z : VarSymb) (W₁ : VarCtx) (bv : Finset VarSymb) : VarSymb :=
  VarSymb.fresh (insert z (VarCtx_to_VarSymbs W₁ ∪ bv))

theorem pairElim_qy_spec (z : VarSymb) (W₁ : VarCtx) (bv : Finset VarSymb) :
    pairElim_qy z W₁ bv ∉ insert z (VarCtx_to_VarSymbs W₁ ∪ bv) := VarSymb.fresh_not_mem _

theorem pairElim_qy_ne_z (z : VarSymb) (W₁ : VarCtx) (bv : Finset VarSymb) :
    pairElim_qy z W₁ bv ≠ z :=
  fun h => pairElim_qy_spec z W₁ bv (Finset.mem_insert.mpr (Or.inl h))

theorem pairElim_qy_notin_W₁ (z : VarSymb) (W₁ : VarCtx) (bv : Finset VarSymb) :
    pairElim_qy z W₁ bv ∉ VarCtx_to_VarSymbs W₁ :=
  fun h => pairElim_qy_spec z W₁ bv (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))

theorem pairElim_qy_notin_bv (z : VarSymb) (W₁ : VarCtx) (bv : Finset VarSymb) :
    pairElim_qy z W₁ bv ∉ bv :=
  fun h => pairElim_qy_spec z W₁ bv (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))

theorem pairElim_qyV {V W₁ : VarCtx} {v₁ v₂ : VarSymb × VarType}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1}
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (z : VarSymb) (bv : Finset VarSymb) :
    pairElim_qy z W₁ bv ∉ VarCtx_to_VarSymbs V :=
  (pairElim_binder_fresh w₁eq (pairElim_qy_notin_W₁ z W₁ bv)).2.2

theorem pairElim_qyv₁ {V W₁ : VarCtx} {v₁ v₂ : VarSymb × VarType}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1}
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (z : VarSymb) (bv : Finset VarSymb) (T : VarType) :
    v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert
      (⟨pairElim_qy z W₁ bv, T⟩ : VarSymb × VarType) V (pairElim_qyV w₁eq z bv)) :=
  not_mem_VarSymbs_insert
    (Ne.symm (pairElim_binder_fresh w₁eq (pairElim_qy_notin_W₁ z W₁ bv)).1) hv₁

theorem pairElim_qyv₂ {V W₁ : VarCtx} {v₁ v₂ : VarSymb × VarType}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1}
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (z : VarSymb) (bv : Finset VarSymb) (T : VarType) :
    v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert
      (⟨pairElim_qy z W₁ bv, T⟩ : VarSymb × VarType) V (pairElim_qyV w₁eq z bv)) :=
  not_mem_VarSymbs_insert
    (Ne.symm (pairElim_binder_fresh w₁eq (pairElim_qy_notin_W₁ z W₁ bv)).2.1) hv₂

theorem pairElim_qyz {V W₁ : VarCtx} {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1} (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (bv : Finset VarSymb) (T : VarType) :
    z ∉ VarCtx_to_VarSymbs (VarCtx_insert
      (⟨pairElim_qy z W₁ bv, T⟩ : VarSymb × VarType) V (pairElim_qyV w₁eq z bv)) :=
  not_mem_VarSymbs_insert (Ne.symm (pairElim_qy_ne_z z W₁ bv)) hz

theorem pairElim_qyW₂ {V W₁ W₂ : VarCtx} {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1} {hz : z ∉ VarCtx_to_VarSymbs V}
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (bv : Finset VarSymb) :
    pairElim_qy z W₁ bv ∉ VarCtx_to_VarSymbs W₂ :=
  w₂eq ▸ not_mem_VarSymbs_insert (pairElim_qy_ne_z z W₁ bv) (pairElim_qyV w₁eq z bv)

-- `WFF.pairElim` distributes a `pair_elim` over the structure of a WFF.  Structural connectives
-- push the destructure inside.  QUANTIFIER binders also push inside, α-renaming the binder to
-- `pairElim_qy` (which avoids `z`, so the newly-freed pair variable is never captured).  Modal
-- binders (`box`, `dia`) and nested `pair_elim` remain STUCK, and structurally so: `isBox` of a
-- product is the disjunction of its components, so when either `v₁.2` or `v₂.2` is box-typed,
-- `⟨z, v₁.2 ×ᵥ v₂.2⟩ ∈ W₂` is a box-typed entry not of the form `□T`, making `h_no_box_extras`
-- unsatisfiable — no `box` can exist in `W₂` at all, so the pushed-in form does not typecheck.
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
  | @WFF.all _ _ x hx φ =>
      @WFF.all σ W₂ ⟨pairElim_qy z W₁ (WFF.boundVars φ), x.2⟩
        (pairElim_qyW₂ w₁eq w₂eq (WFF.boundVars φ))
        (WFF.pairElim
          (V := VarCtx_insert (⟨pairElim_qy z W₁ (WFF.boundVars φ), x.2⟩ : VarSymb × VarType) V
                  (pairElim_qyV w₁eq z (WFF.boundVars φ)))
          v₁ v₂ z
          (pairElim_qyv₁ w₁eq z (WFF.boundVars φ) x.2)
          (pairElim_qyv₂ w₁eq z (WFF.boundVars φ) x.2)
          hv₁v₂ (pairElim_qyz hz w₁eq (WFF.boundVars φ) x.2)
          (pairElim_quant_w₁eq w₁eq (pairElim_qyV w₁eq z (WFF.boundVars φ))
            (pairElim_qy_notin_W₁ z W₁ (WFF.boundVars φ))
            (pairElim_qyv₁ w₁eq z (WFF.boundVars φ) x.2)
            (pairElim_qyv₂ w₁eq z (WFF.boundVars φ) x.2))
          (pairElim_quant_w₂eq w₂eq (pairElim_qyV w₁eq z (WFF.boundVars φ))
            (pairElim_qyW₂ w₁eq w₂eq (WFF.boundVars φ))
            (pairElim_qyz hz w₁eq (WFF.boundVars φ) x.2))
          (WFF.rename x.1 (pairElim_qy z W₁ (WFF.boundVars φ)) x.2 W₁
            (VarCtx_insert x W₁ hx) hx (pairElim_qy_notin_W₁ z W₁ (WFF.boundVars φ)) rfl φ
            (pairElim_qy_notin_bv z W₁ (WFF.boundVars φ))))
  | @WFF.ex _ _ x hx φ =>
      @WFF.ex σ W₂ ⟨pairElim_qy z W₁ (WFF.boundVars φ), x.2⟩
        (pairElim_qyW₂ w₁eq w₂eq (WFF.boundVars φ))
        (WFF.pairElim
          (V := VarCtx_insert (⟨pairElim_qy z W₁ (WFF.boundVars φ), x.2⟩ : VarSymb × VarType) V
                  (pairElim_qyV w₁eq z (WFF.boundVars φ)))
          v₁ v₂ z
          (pairElim_qyv₁ w₁eq z (WFF.boundVars φ) x.2)
          (pairElim_qyv₂ w₁eq z (WFF.boundVars φ) x.2)
          hv₁v₂ (pairElim_qyz hz w₁eq (WFF.boundVars φ) x.2)
          (pairElim_quant_w₁eq w₁eq (pairElim_qyV w₁eq z (WFF.boundVars φ))
            (pairElim_qy_notin_W₁ z W₁ (WFF.boundVars φ))
            (pairElim_qyv₁ w₁eq z (WFF.boundVars φ) x.2)
            (pairElim_qyv₂ w₁eq z (WFF.boundVars φ) x.2))
          (pairElim_quant_w₂eq w₂eq (pairElim_qyV w₁eq z (WFF.boundVars φ))
            (pairElim_qyW₂ w₁eq w₂eq (WFF.boundVars φ))
            (pairElim_qyz hz w₁eq (WFF.boundVars φ) x.2))
          (WFF.rename x.1 (pairElim_qy z W₁ (WFF.boundVars φ)) x.2 W₁
            (VarCtx_insert x W₁ hx) hx (pairElim_qy_notin_W₁ z W₁ (WFF.boundVars φ)) rfl φ
            (pairElim_qy_notin_bv z W₁ (WFF.boundVars φ))))
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
termination_by φ => WFF.numNodes φ
decreasing_by
  all_goals
    simp only [WFF.numNodes]
    first
      | omega
      | (rw [WFF.numNodes_rename]; omega)

def WFF.pairElim_Finset {σ : Signature} {V W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂) :
    Finset (WFF σ W₁) → Finset (WFF σ W₂) :=
  fun Γ => Finset.image (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq) Γ

-- `WFF.pairElim` preserves `diaCount`.  Stated GENERALLY (arbitrary `W₁`/`W₂`) because the
-- quantifier arms hand the recursive call PERMUTED context equations, not `rfl`; the α-rename is
-- absorbed by `WFF.diaCount_rename`.
theorem WFF.diaCount_pairElim_gen {σ : Signature} {V W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (φ : WFF σ W₁) :
    WFF.diaCount (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ) = WFF.diaCount φ := by
  match φ with
  | .atom R =>
      simp only [WFF.pairElim, WFF.diaCount]
      exact Rel.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq R
  | .top => simp only [WFF.pairElim, WFF.diaCount]
  | .bot => simp only [WFF.pairElim, WFF.diaCount]
  | .and φ' ψ' =>
      simp only [WFF.pairElim, WFF.diaCount,
        WFF.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ',
        WFF.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ']
  | .or φ' ψ' =>
      simp only [WFF.pairElim, WFF.diaCount,
        WFF.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ',
        WFF.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ']
  | .imp φ' ψ' =>
      simp only [WFF.pairElim, WFF.diaCount,
        WFF.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ',
        WFF.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ']
  | .eq s t =>
      simp only [WFF.pairElim, WFF.diaCount,
        Term.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq s,
        Term.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t]
  | @WFF.all _ _ x hx φ' =>
      simp only [WFF.pairElim, WFF.diaCount,
        WFF.diaCount_pairElim_gen _ _ _ _ _ _ _ _ _
          (WFF.rename x.1 _ x.2 W₁ _ hx _ rfl φ' _),
        WFF.diaCount_rename]
  | @WFF.ex _ _ x hx φ' =>
      simp only [WFF.pairElim, WFF.diaCount,
        WFF.diaCount_pairElim_gen _ _ _ _ _ _ _ _ _
          (WFF.rename x.1 _ x.2 W₁ _ hx _ rfl φ' _),
        WFF.diaCount_rename]
  | .box _ _ _ => simp only [WFF.pairElim, WFF.diaCount]
  | .dia _ _ _ _ _ => simp only [WFF.pairElim, WFF.diaCount]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => simp only [WFF.pairElim, WFF.diaCount]
termination_by WFF.numNodes φ
decreasing_by
  all_goals
    simp only [WFF.numNodes]
    first
      | omega
      | (rw [WFF.numNodes_rename]; omega)

theorem WFF.diaCount_pairElim {σ : Signature} {V : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂)) :
    WFF.diaCount (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz rfl rfl φ) = WFF.diaCount φ :=
  WFF.diaCount_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz rfl rfl φ

-- Same for `binderPairDepth`.  The quantifier arms work because `WFF.rename` changes only the
-- binder's SYMBOL, not its type, and `binderPairDepth` reads only the type.
theorem WFF.binderPairDepth_pairElim_gen {σ : Signature} {V W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (φ : WFF σ W₁) :
    WFF.binderPairDepth (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ)
      = WFF.binderPairDepth φ := by
  match φ with
  | .atom _ => simp only [WFF.pairElim, WFF.binderPairDepth]
  | .top => simp only [WFF.pairElim, WFF.binderPairDepth]
  | .bot => simp only [WFF.pairElim, WFF.binderPairDepth]
  | .and φ' ψ' =>
      simp only [WFF.pairElim, WFF.binderPairDepth,
        WFF.binderPairDepth_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ',
        WFF.binderPairDepth_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ']
  | .or φ' ψ' =>
      simp only [WFF.pairElim, WFF.binderPairDepth,
        WFF.binderPairDepth_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ',
        WFF.binderPairDepth_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ']
  | .imp φ' ψ' =>
      simp only [WFF.pairElim, WFF.binderPairDepth,
        WFF.binderPairDepth_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ',
        WFF.binderPairDepth_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ']
  | .eq _ _ => simp only [WFF.pairElim, WFF.binderPairDepth]
  | @WFF.all _ _ x hx φ' =>
      simp only [WFF.pairElim, WFF.binderPairDepth,
        WFF.binderPairDepth_pairElim_gen _ _ _ _ _ _ _ _ _
          (WFF.rename x.1 _ x.2 W₁ _ hx _ rfl φ' _),
        WFF.binderPairDepth_rename]
  | @WFF.ex _ _ x hx φ' =>
      simp only [WFF.pairElim, WFF.binderPairDepth,
        WFF.binderPairDepth_pairElim_gen _ _ _ _ _ _ _ _ _
          (WFF.rename x.1 _ x.2 W₁ _ hx _ rfl φ' _),
        WFF.binderPairDepth_rename]
  | .box _ _ _ => simp only [WFF.pairElim, WFF.binderPairDepth]
  | .dia _ _ _ _ _ => simp only [WFF.pairElim, WFF.binderPairDepth]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => simp only [WFF.pairElim, WFF.binderPairDepth]
termination_by WFF.numNodes φ
decreasing_by
  all_goals
    simp only [WFF.numNodes]
    first
      | omega
      | (rw [WFF.numNodes_rename]; omega)

theorem WFF.binderPairDepth_pairElim {σ : Signature} {V : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂)) :
    WFF.binderPairDepth (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz rfl rfl φ)
      = WFF.binderPairDepth φ :=
  WFF.binderPairDepth_pairElim_gen v₁ v₂ z hv₁ hv₂ hv₁v₂ hz rfl rfl φ

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

