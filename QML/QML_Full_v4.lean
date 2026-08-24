import Mathlib

/-!
# Quantified Modal Logic: Natural Deduction (v4)

Redesign from v3. Key changes:

  · `VarCtx` changed from `List (VarSymb × VarType)` to `Finset (VarSymb × VarType)`.
    The `exch` structural rule is thereby eliminated (Finset context has no ordering).
    `wk` remains as a Term constructor; it is needed because modal context changes
    (boxterm/diaterm) produce specific Finset shapes that may need to be enlarged.

  · `GlobalTerm σ τ` is a new context-free term type indexed by `VarType`.
    `Term.toGlobal` maps any term to its global representative, making `wk`
    transparent. `DecidableEq (GlobalTerm σ τ)` derives trivially and is the basis
    for term equality in substitution and equality elimination.
    α-equivalence for `pair_elim` binders is handled by `GlobalTerm.AlphaEq`.
    The `pair_elim` scrutinee is a `GlobalTerm σ (.VTypeProd v₁.2 v₂.2)`, enforcing
    that only pair-typed terms can be destructured.

  · `DecidableEq (Term σ V S)` is dropped. Term equality uses `Term.toGlobal`.

  · `box_VarCtx` and `dia_VarCtx` are now Finset operations:
        box_VarCtx V  = V.image (fun ⟨v,S⟩ => ⟨v, S.VTypeBox⟩)
        dia_VarCtx x V = insert ⟨x.1, x.2.VTypeDia⟩ (box_VarCtx V)

  · Modal terms are formed exclusively via `boxterm` and `diaterm`:
        boxterm : Term σ V S             → Term σ (box_VarCtx V) (VTypeBox S)
        diaterm : Term σ (insert x V) S  → Term σ (dia_VarCtx x V) (VTypeDia S)
-/

/-! ## Modalities (kept for documentation; not used in core v4 definitions) -/

inductive Modality : Type where
  | box : Modality
  | dia : Modality
  deriving DecidableEq

/-! ## Signature -/

structure Signature where
  FuncSyms  : Type
  RelSyms   : Type
  funcArity : FuncSyms → ℕ
  relArity  : RelSyms  → ℕ
  [decEqF   : DecidableEq FuncSyms]
  [decEqR   : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

/-! ## Variable Types -/

inductive VarType where
  | Var     : VarType
  | VTypeBox  : VarType → VarType
  | VTypeDia  : VarType → VarType
  | VTypeOne  : VarType                      -- nullary product / trivial dia witness
  | VTypeProd : VarType → VarType → VarType  -- binary product
  deriving DecidableEq

/-! ## Variable Symbols -/

inductive VarSymb : Type where
  | mk : ℕ → VarSymb
  deriving DecidableEq

/-! ## Variable Contexts -/

abbrev VarCtx := Finset (VarSymb × VarType)

-- Wrap every variable's type in VTypeBox
def box_VarCtx (V : VarCtx) : VarCtx :=
  V.image fun ⟨v, S⟩ => ⟨v, S.VTypeBox⟩

-- One designated witness gets VTypeDia; everything else gets VTypeBox
def dia_VarCtx (x : VarSymb × VarType) (V : VarCtx) : VarCtx :=
  insert ⟨x.1, x.2.VTypeDia⟩ (box_VarCtx V)

/-! ## Terms -/

mutual
  inductive Func (σ : Signature) : VarCtx → ℕ → Type where
    | F    : {f : σ.FuncSyms // σ.funcArity f = n} → Func σ V n
    | eval : Func σ V (Nat.succ n) → Term σ V .Var → Func σ V n
    deriving DecidableEq

-- `Term σ V S`: a term of VarType S with free variables drawn from VarCtx V.
  inductive Term (σ : Signature) : VarCtx → VarType → Type where
    | var       : {v : VarSymb // ⟨v, S⟩ ∈ V} → Term σ V S
    | func      : Func σ V 0 → Term σ V .Var
    | boxterm   : Term σ V S → ((box_VarCtx V) ⊆ W) → Term σ W S.VTypeBox
    | diaterm   : (x : VarSymb × VarType) → x ∉ V →
                  Term σ (insert x V) S → ((dia_VarCtx x V) ⊆ W) → Term σ W S.VTypeDia
    | unit      : Term σ V .VTypeOne
    | pair      : Term σ V S → Term σ V T → Term σ V (.VTypeProd S T)
    | pair_elim : (v₁ v₂ : VarSymb × VarType) → (z : VarSymb) →
                  ⟨z, .VTypeProd v₁.2 v₂.2⟩ ∉ V →
                  insert v₁ (insert v₂ V) = W₁ →
                  insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V = W₂ →
                  Term σ W₁ S →
                  Term σ W₂ S
  deriving DecidableEq
end

-- Rename a variable symbol to another variable symbol inside a function/term
mutual
  def Func.rename {σ : Signature} (old : VarSymb × VarType) (new : VarSymb) (V W : VarCtx) (N : Nat)
      (old_fresh : old ∉ V) (new_fresh : (⟨new, old.2⟩ ∉ V)) (Wdef : W = insert old V)
      : Func σ W N → Func σ (insert ⟨new, old.2⟩ V) N := by
    intro f
    match f with
    | .F h => exact .F h
    | .eval g t => exact .eval (Func.rename _ _ _ _ _ old_fresh new_fresh Wdef g) (Term.rename _ _ _ _ _ old_fresh new_fresh Wdef t)

  def Term.rename {σ : Signature} (old : VarSymb × VarType) (new : VarSymb) (V W : VarCtx) (S : VarType)
      (old_fresh : old ∉ V) (new_fresh : (⟨new, old.2⟩ ∉ V)) (Wdef : W = insert old V)
      : Term σ W S → Term σ (insert ⟨new, old.2⟩ V) S := by
    intro old_term
    match old_term with
    | .var ⟨v, veq⟩ =>
      if h : ⟨v, S⟩ = old then
        exact .var ⟨new, (Prod.eq_iff_fst_eq_snd_eq.mp h).2 ▸ Finset.mem_insert_self (new, old.2) V⟩
      else
        refine .var ⟨v, ?_⟩
        rcases Finset.mem_insert.mp (Wdef ▸ veq) with tr | fa
        · exact absurd tr h
        · exact Finset.mem_insert_of_mem fa
    | .func f => exact .func (Func.rename _ _ _ _ _ old_fresh new_fresh Wdef f)
    | .boxterm inner_t box_context_sub =>
        rcases old with ⟨old1, old2⟩
        rename_i inner_ctx inner_termtype
        rcases old2 with _ | innertype | _ | _ | ⟨_, _⟩
        · -- Var
          refine .boxterm inner_t ?_
          have : box_VarCtx inner_ctx ⊆ V := by
            intro x x_in_box_inner
            rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub x_in_box_inner) with xold | xV
            · rcases xold ▸ Finset.mem_image.mp x_in_box_inner with ⟨w, weq⟩
              have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
              simp only [reduceCtorEq, and_false] at this
            · exact xV
          exact (Finset.subset_insert_iff_of_notMem fun a ↦ new_fresh (this a)).mpr this
        · -- VTypeBox: recurse into inner_t if old1 is bound in inner_ctx, else pass through
          if h : ⟨old1, innertype⟩ ∈ inner_ctx then
            let innerCtx' := inner_ctx.erase ⟨old1, innertype⟩
            have innerCtx_eq : inner_ctx = insert ⟨old1, innertype⟩ innerCtx' :=
              (Finset.insert_erase h).symm
            have oldinner_fresh : ⟨old1, innertype⟩ ∉ innerCtx' := fun hmem =>
              (Finset.mem_erase.mp hmem).1 rfl
            have hbox_sub : box_VarCtx innerCtx' ⊆ V := by
              intro x hx
              have hx_inner : x ∈ box_VarCtx inner_ctx := by
                rcases Finset.mem_image.mp hx with ⟨⟨v, S⟩, hvin, hveq⟩
                exact Finset.mem_image.mpr ⟨⟨v, S⟩, Finset.erase_subset _ _ hvin, hveq⟩
              rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub hx_inner) with rfl | hV
              · rcases Finset.mem_image.mp hx with ⟨⟨v, S⟩, hvin, hveq⟩
                simp only [Prod.mk.injEq] at hveq
                exact absurd (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin) oldinner_fresh
              · exact hV
            have newinner_fresh : ⟨new, innertype⟩ ∉ innerCtx' := fun hmem =>
              new_fresh (hbox_sub (Finset.mem_image.mpr ⟨⟨new, innertype⟩, hmem, rfl⟩))
            let renamed_t := Term.rename ⟨old1, innertype⟩ new innerCtx' inner_ctx inner_termtype
                                         oldinner_fresh newinner_fresh innerCtx_eq inner_t
            refine .boxterm renamed_t ?_
            rw [show box_VarCtx (insert ⟨new, innertype⟩ innerCtx') =
                     insert ⟨new, innertype.VTypeBox⟩ (box_VarCtx innerCtx') from
                  by simp [box_VarCtx, Finset.image_insert]]
            exact Finset.insert_subset_insert _ hbox_sub
          else
            refine .boxterm inner_t ?_
            have hbox_old_not : ⟨old1, innertype.VTypeBox⟩ ∉ box_VarCtx inner_ctx := by
              intro hmem
              rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin)
            have hsub : box_VarCtx inner_ctx ⊆ V :=
              (Finset.subset_insert_iff_of_notMem hbox_old_not).mp (Wdef ▸ box_context_sub)
            exact Finset.Subset.trans hsub (Finset.subset_insert _ _)
        -- remaining cases are all the same: VTypeDia, VTyprProd and VTypeOne
        all_goals refine .boxterm inner_t ?_
        all_goals have : box_VarCtx inner_ctx ⊆ V := by
          { intro x x_in_box_inner
            rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub x_in_box_inner) with xold | xV
            · rcases xold ▸ Finset.mem_image.mp x_in_box_inner with ⟨w, weq⟩
              have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
              simp only [reduceCtorEq, and_false] at this
            · exact xV
          }
        all_goals exact (Finset.subset_insert_iff_of_notMem fun a ↦ new_fresh (this a)).mpr this
    | .diaterm x xfresh inner_t dia_context_sub =>
        rcases old with ⟨old1, old2⟩
        rename_i inner_ctx inner_termtype
        rcases old2 with _ | innertype | _ | _ | ⟨_, _⟩
        · -- Var case
          refine .diaterm x xfresh inner_t ?_
          have : dia_VarCtx x inner_ctx ⊆ V := by
            intro y y_in_dia_inner
            rcases Finset.mem_insert.mp (Wdef ▸ dia_context_sub y_in_dia_inner) with xold | xV
            · rcases xold ▸ Finset.mem_insert.mp y_in_dia_inner with dia_case | box_case
              · have := (Prod.eq_iff_fst_eq_snd_eq.mp dia_case).2
                simp only [reduceCtorEq] at this
              · rcases Finset.mem_image.mp box_case with ⟨⟨v, T⟩, _, hveq⟩
                simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
            · exact xV
          exact Finset.Subset.trans this (Finset.subset_insert _ _)
        · -- VTypeBox case
          if h : ⟨old1, innertype⟩ ∈ inner_ctx then
            have : insert ⟨new, innertype⟩ V = sorry
            refine .diaterm x xfresh (Term.rename   )

            · -- Var
    | .unit => exact .unit
    | .pair _ _ => _
    | .pair_elim v₁ v₂ z _ _ _ _ => _
end

/-! ## Global Terms -/

-- Context-free terms for equality comparison. No VarCtx parameter, no `wk`.
-- Mirrors the QML_FOL.lean pattern: a mutual inductive with a `GlobalFunc σ n`
-- spine avoids function-type fields, allowing `deriving DecidableEq` on both types.
--
-- `GlobalFunc σ n` is an n-ary function symbol, possibly partially applied.
-- `GlobalTerm σ` is a fully-applied (0-ary) function, variable, or compound term.
--
-- Term equality for substitution: a ≈ b ↔ a.toGlobal = b.toGlobal.
-- α-equivalence for `pair_elim` binders is handled by `GlobalTerm.AlphaEq`.
mutual
  inductive GlobalFunc (σ : Signature) : ℕ → Type where
    | F    : {f : σ.FuncSyms // σ.funcArity f = n} → GlobalFunc σ n
    | eval : GlobalFunc σ (Nat.succ n) → GlobalTerm σ .Var → GlobalFunc σ n
    deriving DecidableEq

  inductive GlobalTerm (σ : Signature) : VarType → Type where
    | var       : VarSymb → (τ : VarType) → GlobalTerm σ τ
    | func      : GlobalFunc σ 0 → GlobalTerm σ .Var
    | boxterm   : GlobalTerm σ S → GlobalTerm σ S.VTypeBox
    | diaterm   : GlobalTerm σ S → GlobalTerm σ S.VTypeDia
    | unit      : GlobalTerm σ .VTypeOne
    | pair      : GlobalTerm σ S → GlobalTerm σ T → GlobalTerm σ (.VTypeProd S T)
    | pair_elim : (v₁ v₂ : VarSymb × VarType) →
                  GlobalTerm σ (.VTypeProd v₁.2 v₂.2) →
                  GlobalTerm σ τ → GlobalTerm σ τ
    deriving DecidableEq
end

-- Build a fully-applied GlobalFunc from a function symbol and its arguments.
private def applyGlobalArgs {σ : Signature} :
    {n : ℕ} → GlobalFunc σ n → (Fin n → GlobalTerm σ .Var) → GlobalFunc σ 0
  | 0,   g, _ => g
  | _+1, g, k => applyGlobalArgs (.eval g (k 0)) (fun i => k i.succ)

-- Map a term to its global representative.
-- `wk` is transparent: `toGlobal (wk v t) = toGlobal t`.
-- The variable's VarType index S is recorded in the `var` case (from the implicit index).
def Term.toGlobal {σ : Signature} {V : VarCtx} {S : VarType} : Term σ V S → GlobalTerm σ S
  | .var ⟨v, _⟩              => .var v S
  | .func f k                => .func (applyGlobalArgs (.F ⟨f, rfl⟩) (fun i => (k i).toGlobal))
  | .boxterm t _             => .boxterm t.toGlobal
  | .diaterm _ _ t _         => .diaterm t.toGlobal
  | .unit                    => .unit
  | .pair t₁ t₂              => .pair t₁.toGlobal t₂.toGlobal
  | .pair_elim v₁ v₂ z _ b => .pair_elim v₁ v₂ (.var z (.VTypeProd v₁.2 v₂.2)) b.toGlobal

/-! ## Variable Renaming on GlobalTerm -/

-- Rename all occurrences of `old` to `⟨new_sym, old.2⟩`, stopping at pair_elim binders
-- that shadow `old`. Type-preserving: the renamed variable keeps its type. Correct under
-- the Barendregt convention.
mutual
  def GlobalTerm.rename {σ : Signature} (old : VarSymb × VarType) (new_sym : VarSymb) :
      GlobalTerm σ τ → GlobalTerm σ τ
    | .var v τ_v  => .var (if (v, τ_v) = old then new_sym else v) τ_v
    | .func g     => .func (GlobalFunc.rename old new_sym g)
    | .boxterm t  => .boxterm (t.rename old new_sym)
    | .diaterm t  => .diaterm (t.rename old new_sym)
    | .unit       => .unit
    | .pair t₁ t₂ => .pair (t₁.rename old new_sym) (t₂.rename old new_sym)
    | .pair_elim v₁ v₂ t b =>
        let t' := t.rename old new_sym
        if old = v₁ ∨ old = v₂ then .pair_elim v₁ v₂ t' b
        else .pair_elim v₁ v₂ t' (b.rename old new_sym)

  def GlobalFunc.rename {σ : Signature} {n : ℕ} (old : VarSymb × VarType) (new_sym : VarSymb) :
      GlobalFunc σ n → GlobalFunc σ n
    | .F f      => .F f
    | .eval g t => .eval (g.rename old new_sym) (t.rename old new_sym)
end

/-! ## Substitution -/

-- Internal implementation on GlobalTerm, used by Term.substTerm and pair_β.
-- At each node: if the whole term equals `target` (checked after a type-index equality
-- test), return `replacement`; otherwise recurse into subterms. Variables are atomic.
-- Under the Barendregt convention no binder-shadowing check is needed.
mutual
  def GlobalTerm.substTerm {σ : Signature} {τ τ_body : VarType}
      (t : GlobalTerm σ τ_body)
      (target : GlobalTerm σ τ) (replacement : GlobalTerm σ τ) :
      GlobalTerm σ τ_body :=
    if h : τ_body = τ then
      if h ▸ t = target then h.symm ▸ replacement
      else match t with
        | .var v τ_v          => .var v τ_v
        | .func g             => .func (g.substTerm target replacement)
        | .boxterm t'         => .boxterm (t'.substTerm target replacement)
        | .diaterm t'         => .diaterm (t'.substTerm target replacement)
        | .unit               => .unit
        | .pair t₁ t₂         => .pair (t₁.substTerm target replacement)
                                       (t₂.substTerm target replacement)
        | .pair_elim v₁ v₂ scrut b =>
            .pair_elim v₁ v₂ (scrut.substTerm target replacement)
                              (b.substTerm target replacement)
    else match t with
      | .var v τ_v            => .var v τ_v
      | .func g               => .func (g.substTerm target replacement)
      | .boxterm t'           => .boxterm (t'.substTerm target replacement)
      | .diaterm t'           => .diaterm (t'.substTerm target replacement)
      | .unit                 => .unit
      | .pair t₁ t₂           => .pair (t₁.substTerm target replacement)
                                       (t₂.substTerm target replacement)
      | .pair_elim v₁ v₂ scrut b =>
          .pair_elim v₁ v₂ (scrut.substTerm target replacement)
                            (b.substTerm target replacement)

  def GlobalFunc.substTerm {σ : Signature} {n : ℕ} {τ : VarType}
      (g : GlobalFunc σ n) (target : GlobalTerm σ τ) (replacement : GlobalTerm σ τ) :
      GlobalFunc σ n :=
    match g with
    | .F f       => .F f
    | .eval g' t => .eval (g'.substTerm target replacement) (t.substTerm target replacement)
end

-- Replaces a product-typed variable `z_sym : v₁.2 × v₂.2` in a term with the
-- pair of component variables `(v₁, v₂)`, threading the context change.
-- Two cases matter: `.wk ⟨z_sym,_⟩ t'` → `.wk v₁ (.wk v₂ t')`;
-- `.var ⟨z_sym,_⟩` → `.pair (.var v₁) (.var v₂)`. Box/dia contexts never
-- contain VTypeProd-typed variables (box_VarCtx maps all types to VTypeBox),
-- so those arms are vacuous; pair_elim scrutinee case is a semantic no-op
-- (GlobalTerm.pair_elim always has variable scrutinees, so no subterm of the
-- body's toGlobal can ever equal x'.toGlobal there).
def Term.substPairVar {σ : Signature} {V : VarCtx} {S : VarType}
    (z_sym : VarSymb) (v₁ v₂ : VarSymb × VarType)
    (t : Term σ (insert ⟨z_sym, .VTypeProd v₁.2 v₂.2⟩ V) S)
    : Term σ (insert v₁ (insert v₂ V)) S := by
  match t with
  | .var ⟨v, hv⟩ =>
      if heq : (⟨v, S⟩ : VarSymb × VarType) = ⟨z_sym, .VTypeProd v₁.2 v₂.2⟩ then
        have hS : S = .VTypeProd v₁.2 v₂.2 := congrArg Prod.snd heq
        exact hS ▸ .pair (.var ⟨v₁.1, Finset.mem_insert_self _ _⟩)
                          (.var ⟨v₂.1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩)
      else
        exact .var ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                        ((Finset.mem_insert.mp hv).resolve_left heq))⟩
  | .func f k   => exact .func f (fun i => (k i).substPairVar z_sym v₁ v₂)
  | .unit       => exact .unit
  | .pair t₁ t₂ => exact .pair (t₁.substPairVar z_sym v₁ v₂) (t₂.substPairVar z_sym v₁ v₂)
  | .pair_elim w₁ w₂ z _ W₁eq _ t_unpaired => if zeq : z = z_sym ∧ w₁.2 = v₁.2 ∧ w₂.2 = v₂.2
                                then
                                zeq.2.2 ▸ (W₁eq.symm ▸ t_unpaired)
                                else
  | .boxterm _  => sorry
    -- simp_all [box_VarCtx, Finset.ext_iff, Finset.mem_insert, Finset.mem_image]
  | .diaterm _ _ _ => sorry
    --simp_all [dia_VarCtx, box_VarCtx, Finset.ext_iff,
                                  Finset.mem_insert, Finset.mem_image]

-- Public API: `t.substTerm x y` replaces every subterm of `t` whose global
-- representative equals `x.toGlobal` with `y`. All three are Terms in the same
-- context; equality is decided by mapping to GlobalTerm. Variable substitution
-- is the special case `x = Term.var v`.
def Term.substTerm {σ : Signature} {V : VarCtx} {S S' : VarType}
    (t : Term σ V S) (x : Term σ V S') (y : Term σ V S') : Term σ V S :=
  if h : S = S' then
    if h ▸ t.toGlobal = x.toGlobal then h.symm ▸ y
    else match t with
      | .var v                   => .var v
      | .func f k                => .func f (fun i => (k i).substTerm x y)
      | .boxterm t'              => .boxterm t'
      | .diaterm xv hx t'        => .diaterm xv hx t'
      | .unit                    => .unit
      | .pair t₁ t₂              => .pair (t₁.substTerm x y) (t₂.substTerm x y)
      | .pair_elim v₁ v₂ z hz b  =>
          .pair_elim v₁ v₂ z hz (b.substTerm (.wk v₁ (.wk v₂ x)) (.wk v₁ (.wk v₂ y)))
      | .wk v t'                 => .wk v t'
  else match t with
    | .var v                   => .var v
    | .func f k                => .func f (fun i => (k i).substTerm x y)
    | .boxterm t'              => .boxterm t'
    | .diaterm xv hx t'        => .diaterm xv hx t'
    | .unit                    => .unit
    | .pair t₁ t₂              => .pair (t₁.substTerm x y) (t₂.substTerm x y)
    | .pair_elim v₁ v₂ z hz b  =>
          .pair_elim v₁ v₂ z hz (b.substTerm (.wk v₁ (.wk v₂ x)) (.wk v₁ (.wk v₂ y)))
    | .wk v t'                 => .wk v t'

/-! ## α-Equivalence on GlobalTerm -/

-- α-equivalence: structural congruence everywhere; pair_elim binders (v₁, v₂)
-- may differ by a consistent renaming of the body, and scrutinees must be α-equivalent.
-- Sound under the Barendregt convention.
mutual
  inductive GlobalTerm.AlphaEq {σ : Signature} :
      {τ : VarType} → GlobalTerm σ τ → GlobalTerm σ τ → Prop where
    | var (v : VarSymb) (τ : VarType) :
        GlobalTerm.AlphaEq (.var v τ) (.var v τ)
    | func {g₁ g₂ : GlobalFunc σ 0} :
        GlobalFunc.AlphaEq g₁ g₂ → GlobalTerm.AlphaEq (.func g₁) (.func g₂)
    | boxterm {S : VarType} {t₁ t₂ : GlobalTerm σ S} :
        GlobalTerm.AlphaEq t₁ t₂ → GlobalTerm.AlphaEq (.boxterm t₁) (.boxterm t₂)
    | diaterm {S : VarType} {t₁ t₂ : GlobalTerm σ S} :
        GlobalTerm.AlphaEq t₁ t₂ → GlobalTerm.AlphaEq (.diaterm t₁) (.diaterm t₂)
    | unit : GlobalTerm.AlphaEq .unit .unit
    | pair {S T : VarType} {s₁ s₂ : GlobalTerm σ S} {t₁ t₂ : GlobalTerm σ T} :
        GlobalTerm.AlphaEq s₁ s₂ → GlobalTerm.AlphaEq t₁ t₂ →
        GlobalTerm.AlphaEq (.pair s₁ t₁) (.pair s₂ t₂)
    | pair_elim
        {v₁ v₂ v₁' v₂' : VarSymb × VarType} {τ : VarType}
        {t  : GlobalTerm σ (.VTypeProd v₁.2  v₂.2 )}
        {t' : GlobalTerm σ (.VTypeProd v₁'.2 v₂'.2)}
        {b b' : GlobalTerm σ τ} :
        (h₁ : v₁.2 = v₁'.2) → (h₂ : v₂.2 = v₂'.2) →
        GlobalTerm.AlphaEq (h₁ ▸ h₂ ▸ t) t' →
        GlobalTerm.AlphaEq (b.rename v₁ v₁'.1 |>.rename v₂ v₂'.1) b' →
        GlobalTerm.AlphaEq (.pair_elim v₁ v₂ t b) (.pair_elim v₁' v₂' t' b')

  inductive GlobalFunc.AlphaEq {σ : Signature} :
      {n : ℕ} → GlobalFunc σ n → GlobalFunc σ n → Prop where
    | F {n : ℕ} (f : {f : σ.FuncSyms // σ.funcArity f = n}) :
        GlobalFunc.AlphaEq (.F f) (.F f)
    | eval {n : ℕ} {g₁ g₂ : GlobalFunc σ (n + 1)} {t₁ t₂ : GlobalTerm σ .Var} :
        GlobalFunc.AlphaEq g₁ g₂ → GlobalTerm.AlphaEq t₁ t₂ →
        GlobalFunc.AlphaEq (.eval g₁ t₁) (.eval g₂ t₂)
end

/-! ## Term Conversion -/

-- `GlobalTerm.Conv s t`: the least congruence on global terms containing the β/η rules.
--
-- β/η rules:
--   unit_η           : any term of type VTypeOne converts to .unit
--   pair_β           : "let (v₁,v₂) = (s,t) in b" reduces to b[v₁:=s][v₂:=t]
--   pair_η           : "let (v₁,v₂) = t in (v₁,v₂)" is just t (for any pair-typed t)
--   pair_elim_cong   : congruence under the body of a pair_elim
--   pair_elim_t_cong : congruence under the scrutinee of a pair_elim
mutual
  inductive GlobalTerm.Conv {σ : Signature} :
      {τ : VarType} → GlobalTerm σ τ → GlobalTerm σ τ → Prop where
    | unit_η           : GlobalTerm.Conv t .unit
    | pair_β           {v₁ v₂ : VarSymb × VarType} {τ : VarType}
                       {s : GlobalTerm σ v₁.2} {t : GlobalTerm σ v₂.2} {b : GlobalTerm σ τ} :
                       GlobalTerm.Conv (.pair_elim v₁ v₂ (.pair s t) b)
                                       (b.substTerm (.var v₁.1 v₁.2) s
                                          |>.substTerm (.var v₂.1 v₂.2) t)
    | pair_η           : GlobalTerm.Conv
                           (.pair_elim v₁ v₂ t (.pair (.var v₁.1 v₁.2) (.var v₂.1 v₂.2)))
                           t
    | func_cong        : GlobalFunc.Conv g₁ g₂ →
                         GlobalTerm.Conv (.func g₁) (.func g₂)
    | boxterm_cong     : GlobalTerm.Conv t₁ t₂ →
                         GlobalTerm.Conv (.boxterm t₁) (.boxterm t₂)
    | diaterm_cong     : GlobalTerm.Conv t₁ t₂ →
                         GlobalTerm.Conv (.diaterm t₁) (.diaterm t₂)
    | pair_l           : GlobalTerm.Conv s s' →
                         GlobalTerm.Conv (.pair s t) (.pair s' t)
    | pair_r           : GlobalTerm.Conv t t' →
                         GlobalTerm.Conv (.pair s t) (.pair s t')
    | pair_elim_cong   : GlobalTerm.Conv b b' →
                         GlobalTerm.Conv (.pair_elim v₁ v₂ t b) (.pair_elim v₁ v₂ t b')
    | pair_elim_t_cong {v₁ v₂ : VarSymb × VarType} {τ : VarType}
                       {t t' : GlobalTerm σ (.VTypeProd v₁.2 v₂.2)} {b : GlobalTerm σ τ} :
                       GlobalTerm.Conv t t' →
                       GlobalTerm.Conv (.pair_elim v₁ v₂ t b) (.pair_elim v₁ v₂ t' b)
    | refl  : GlobalTerm.Conv t t
    | symm  : GlobalTerm.Conv s t → GlobalTerm.Conv t s
    | trans : GlobalTerm.Conv s t → GlobalTerm.Conv t u → GlobalTerm.Conv s u

  inductive GlobalFunc.Conv {σ : Signature} :
      {n : ℕ} → GlobalFunc σ n → GlobalFunc σ n → Prop where
    | F    : GlobalFunc.Conv (.F f) (.F f)
    | eval : GlobalFunc.Conv g₁ g₂ → GlobalTerm.Conv t₁ t₂ →
             GlobalFunc.Conv (.eval g₁ t₁) (.eval g₂ t₂)
    | refl  : GlobalFunc.Conv g g
    | symm  : GlobalFunc.Conv g₁ g₂ → GlobalFunc.Conv g₂ g₁
    | trans : GlobalFunc.Conv g₁ g₂ → GlobalFunc.Conv g₂ g₃ → GlobalFunc.Conv g₁ g₃
end

-- Two terms are convertible when their global representatives are convertible.
def Term.Conv {σ : Signature} {V : VarCtx} {S : VarType} (t₁ t₂ : Term σ V S) : Prop :=
  GlobalTerm.Conv t₁.toGlobal t₂.toGlobal

/-! ## Relation Symbols -/

-- `RelSymb σ V n`: an n-ary relation symbol, partially applied to terms over V.
-- DecidableEq is not derived here; it will be handled via GlobalTerm-based equality
-- once the overall equality design is settled.
inductive RelSymb (σ : Signature) (V : VarCtx) : ℕ → Type where
  | R    : {r : σ.RelSyms // σ.relArity r = n} → RelSymb σ V n
  | eval : RelSymb σ V (Nat.succ n) → (S : VarType) → Term σ V S → RelSymb σ V n

-- Two relation symbols are convertible when they share the same function symbol
-- and all term arguments are pairwise convertible (at the same VarType).
inductive RelSymb.Conv {σ : Signature} {V : VarCtx} :
    {n : ℕ} → RelSymb σ V n → RelSymb σ V n → Prop where
  | R    : RelSymb.Conv (.R f) (.R f)
  | eval {n : ℕ} {p q : RelSymb σ V (n+1)} {S : VarType} {t s : Term σ V S} :
           RelSymb.Conv p q → Term.Conv t s →
           RelSymb.Conv (.eval p S t) (.eval q S s)
  | refl  : RelSymb.Conv r r
  | symm  : RelSymb.Conv p q → RelSymb.Conv q p
  | trans : RelSymb.Conv p q → RelSymb.Conv q r → RelSymb.Conv p r

/-! ## Well-Formed Formulas -/

-- `WFF σ V`: a formula whose free variables lie in V.
--
-- `box φ` : □φ.  φ lives in V; the result lives in box_VarCtx V.
-- `dia x φ`: ◇(∃x.φ).  φ lives in insert x V; the result lives in dia_VarCtx x V.
--   Use x.2 = VTypeOne for the propositional case (trivial witness).
-- `wk v φ` : weakening.  φ lives in V; the result lives in insert v V.
--
-- DecidableEq is not derived here pending the GlobalTerm-based equality design.
inductive WFF (σ : Signature) : VarCtx → Type where
  | atom : RelSymb σ V 0 → WFF σ V
  | top  : WFF σ V
  | bot  : WFF σ V
  | and  : WFF σ V → WFF σ V → WFF σ V
  | or   : WFF σ V → WFF σ V → WFF σ V
  | imp  : WFF σ V → WFF σ V → WFF σ V
  | all  : (x : VarSymb × VarType) → WFF σ (insert x V) → WFF σ V
  | ex   : (x : VarSymb × VarType) → WFF σ (insert x V) → WFF σ V
  | eq   : Term σ V S → Term σ V S → WFF σ V
  | box  : WFF σ V → WFF σ (box_VarCtx V)
  | dia  : (x : VarSymb × VarType) → x ∉ V → WFF σ (insert x V) → WFF σ (dia_VarCtx x V)
  | wk   : (v : VarSymb × VarType) → WFF σ V → WFF σ (insert v V)

namespace WFF

variable {σ : Signature}

def neg (φ : WFF σ V) : WFF σ V := imp φ bot

/-! ## Notation -/

infixr:35 " →ₘ "  => WFF.imp
infixl:65 " ∧ₘ "  => WFF.and
infixl:60 " ∨ₘ "  => WFF.or
prefix:75 "¬ₘ "   => WFF.neg
notation  "⊤ₘ"    => WFF.top
notation  "⊥ₘ"    => WFF.bot
notation  "∀ₘ"    => WFF.all
notation  "∃ₘ"    => WFF.ex
prefix:80 "□ₘ "   => WFF.box
-- ◇ₘ takes an explicit witness: ◇ₘ x φ
notation  "◇ₘ"    => WFF.dia

/-! ## Well-Scopedness -/

-- A formula is Scoped if every quantifier and dia witness binds a variable that
-- is not already present in the relevant context at the point of binding.
def Scoped : WFF σ V → Prop
  | .atom _ | .top | .bot | .eq _ _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ   => φ.Scoped ∧ ψ.Scoped
  | .all x φ                        => x ∉ V ∧ φ.Scoped
  | .ex  x φ                        => x ∉ V ∧ φ.Scoped
  | .box φ                          => φ.Scoped
  | .dia _ _ φ                      => φ.Scoped
  | .wk _ φ                         => φ.Scoped

/-! ## Formula Depth (termination measure) -/

def depth : WFF σ V → ℕ
  | .atom _ | .top | .bot | .eq _ _ => 0
  | .and φ ψ | .or φ ψ | .imp φ ψ   => φ.depth + ψ.depth + 1
  | .all _ φ | .ex _ φ              => φ.depth + 1
  | .box φ   | .dia _ _ φ | .wk _ φ  => φ.depth + 1

lemma depth_cast {V W : VarCtx} (h : V = W) (φ : WFF σ V) :
    depth (h ▸ φ) = depth φ := by subst h; rfl

lemma Scoped_cast {V W : VarCtx} (h : V = W) (φ : WFF σ V) :
    Scoped (h ▸ φ) = Scoped φ := by subst h; rfl

/-! ## Formula Conversion -/

-- The least congruence on formulas that lifts `Term.Conv`.
inductive Conv : {V : VarCtx} → WFF σ V → WFF σ V → Prop where
  | atom  : RelSymb.Conv p q → Conv (.atom p) (.atom q)
  | and_l : Conv φ φ' → Conv (.and φ ψ) (.and φ' ψ)
  | and_r : Conv ψ ψ' → Conv (.and φ ψ) (.and φ  ψ')
  | or_l  : Conv φ φ' → Conv (.or  φ ψ) (.or  φ' ψ)
  | or_r  : Conv ψ ψ' → Conv (.or  φ ψ) (.or  φ  ψ')
  | imp_l : Conv φ φ' → Conv (.imp φ ψ) (.imp φ' ψ)
  | imp_r : Conv ψ ψ' → Conv (.imp φ ψ) (.imp φ  ψ')
  | eq_l  : Term.Conv s s' → Conv (.eq s t) (.eq s' t)
  | eq_r  : Term.Conv t t' → Conv (.eq s t) (.eq s  t')
  | all   {x : VarSymb × VarType} {φ ψ : WFF σ (insert x V)} :
      Conv φ ψ → Conv (.all x φ) (.all x ψ)
  | ex    {x : VarSymb × VarType} {φ ψ : WFF σ (insert x V)} :
      Conv φ ψ → Conv (.ex  x φ) (.ex  x ψ)
  | box   {V' : VarCtx} {φ ψ : WFF σ V'} :
      Conv φ ψ → Conv (V := box_VarCtx V') (.box φ) (.box ψ)
  | dia   {V' : VarCtx} {x : VarSymb × VarType} {h : x ∉ V'} {φ ψ : WFF σ (insert x V')} :
      Conv φ ψ → Conv (V := dia_VarCtx x V') (.dia x h φ) (.dia x h ψ)
  | wk    {V' : VarCtx} {v : VarSymb × VarType} {φ ψ : WFF σ V'} :
      Conv φ ψ → Conv (V := insert v V') (.wk v φ) (.wk v ψ)
  | refl  : Conv φ φ
  | symm  : Conv φ ψ → Conv ψ φ
  | trans : Conv φ ψ → Conv ψ χ → Conv φ χ

end WFF

/-!
## Still to port from v2/v3

  · Term weakening as an admissible function (Term.weaken : V ⊆ W → Term σ V S → Term σ W S)
  · Substitution (subst source target φ — replace toGlobal(source) by target in φ)
  · Pair β via substitution: when a term of the form `pair s t` is substituted for a
    product variable z, any `pair_elim v₁ v₂ z b` in scope should reduce to `b` with
    v₁ and v₂ replaced by the appropriate components. This requires general term
    substitution (GlobalTerm.subst) and a corresponding Conv or proof rule.
  · Context extension / restriction helpers
  · Proof system (natural deduction):
      - Classical propositional rules (ax, weak, conv, and/or/imp/top/bot/lem)
      - Equality rules (eq_intro, eq_elim)
      - Quantifier rules (all_intro, all_elim, ex_intro, ex_elim)
      - Modal rules:
          K_box : Proof σ V Γ φ
                  → Proof σ (box_VarCtx V) (Γ.image (□ₘ ∘ box_lift)) (□ₘ (box_lift φ))
          K_dia : analogous rule for ◇ₘ, one witness at a time
-/
