import QML.QML_v11_OpenBinder

/-!
# QML v11 — substituting a variable for a variable is renaming (LEMMA B, WIP)

LEMMA B finishes `congAll`: after LEMMA A the formula `all_elim` substitutes into is
`ctx_extU u (rename u↦y φ)` (reordered), and substituting `var u` for `y` must give back `φ`.
It splits into

* **B1** (this file) — substituting `var u` for `y` in `ctx_extU u χ` is `rename y↦u χ`;
* **B2** — `rename y↦u (rename u↦y φ) = φ`: the involution `WFF.rename_rename`, already proved.

⚠️The reordering `(B+y)+u = (B+u)+y` is stated as `mapCtx` along `CtxBij.idOfEq`, not as a cast:
`mapCtx_var` then produces the variable's name syntactically, which the `substCore` `var` rules
need.  `mapCtx_idOfEq` converts back to the cast when B is assembled.

⚠️**WIP**: `Term` level only, `T = .Var` only; `boxterm`/`diaterm` arms are `sorry`.
Nothing imports this file.
-/

/-! ## `Term.substCore` computation rules not yet available -/

theorem Term.substCore_var_ne {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) {v : VarSymb}
    (hv : (⟨v, .Var⟩ : VarSymb × VarType) ∈ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : (⟨v, VarType.Var⟩ : VarSymb × VarType) ≠ ⟨x, S⟩) :
    Term.substCore hx h_pf s (Term.var ⟨v, hv⟩)
      = Term.var ⟨v, (Finset.mem_insert.mp hv).resolve_left hne⟩ := by
  conv_lhs => unfold Term.substCore
  rw [dif_neg hne]

theorem Term.substCore_func {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) (fn : Func σ (VarCtx_insert ⟨x, S⟩ V hx) 0) :
    Term.substCore hx h_pf s (Term.func fn) = Term.func (Func.substCore hx h_pf s fn) := by
  conv_lhs => unfold Term.substCore

theorem Term.substCore_unit {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) :
    Term.substCore hx h_pf s (Term.unit : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .VTypeOne)
      = Term.unit := by
  conv_lhs => unfold Term.substCore

theorem Term.substCore_pair {σ : Signature} {V : VarCtx} {x : VarSymb} {S A B : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V) (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) (a : Term σ (VarCtx_insert ⟨x, S⟩ V hx) A)
    (b : Term σ (VarCtx_insert ⟨x, S⟩ V hx) B) :
    Term.substCore hx h_pf s (Term.pair a b)
      = Term.pair (Term.substCore hx h_pf s a) (Term.substCore hx h_pf s b) := by
  conv_lhs => unfold Term.substCore

theorem Func.substCore_F {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType} {N : ℕ}
    (hx : x ∉ VarCtx_to_VarSymbs V) (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) (hr : {f // σ.funcArity f = N}) :
    Func.substCore hx h_pf s (Func.F hr : Func σ (VarCtx_insert ⟨x, S⟩ V hx) N) = Func.F hr := by
  conv_lhs => unfold Func.substCore

theorem Func.substCore_eval {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType} {N : ℕ}
    (hx : x ∉ VarCtx_to_VarSymbs V) (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
    (s : Term σ V S) (g : Func σ (VarCtx_insert ⟨x, S⟩ V hx) (N + 1))
    (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) .Var) :
    Func.substCore hx h_pf s (Func.eval g t)
      = Func.eval (Func.substCore hx h_pf s g) (Term.substCore hx h_pf s t) := by
  conv_lhs => unfold Func.substCore

/-! ## LEMMA B1 for `Term` / `Func` (WIP) -/

mutual
theorem Term.substCore_var_ctx_extU {σ : Signature} {B : VarCtx} (u : UserSymb) {y : VarSymb}
    (hyB : y ∉ VarCtx_to_VarSymbs B) (huB : u.toVar ∉ VarCtx_to_VarSymbs B)
    (hu_y : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨y, .Var⟩ B hyB))
    (hy_u : y ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, .Var⟩ B huB))
    (hreord : VarCtx_insert ⟨u.toVar, .Var⟩ (VarCtx_insert ⟨y, .Var⟩ B hyB) hu_y
                = VarCtx_insert ⟨y, .Var⟩ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB) hy_u)
    (h_pf : (VarCtx_insert ⟨y, .Var⟩ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB) hy_u).PairFree)
    (hmem : (⟨u.toVar, .Var⟩ : VarSymb × VarType)
      ∈ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB).1) :
    ∀ (S : VarType) (t : Term σ (VarCtx_insert ⟨y, .Var⟩ B hyB) S),
      Term.substCore hy_u h_pf (Term.var ⟨u.toVar, hmem⟩)
          (Term.mapCtx (CtxBij.idOfEq hreord) (Term.ctx_extU u .Var hu_y t))
        = Term.mapCtx (CtxBij.renameOne y u.toVar .Var hyB huB) t
  | _, .var ⟨w, hw⟩ => by
      rw [Term.ctx_extU_var, Term.mapCtx_var (CtxBij.idOfEq hreord) _
            ((CtxBij.idOfEq hreord).toCtxMap.maps _ (Finset.mem_insert_of_mem hw)),
          Term.mapCtx_var (CtxBij.renameOne y u.toVar .Var hyB huB) hw
            ((CtxBij.renameOne y u.toVar .Var hyB huB).toCtxMap.maps _ hw)]
      simp only [CtxBij.idOfEq_f, id]
      by_cases hwy : w = y
      · subst hwy
        rw [Term.substCore_var_self]
        congr 1
        apply Subtype.ext
        change u.toVar = VarSymb.update id w u.toVar w
        simp [VarSymb.update]
      · have hne : (⟨w, VarType.Var⟩ : VarSymb × VarType) ≠ ⟨y, VarType.Var⟩ :=
          fun h => hwy (congrArg Prod.fst h)
        rw [Term.substCore_var_ne hy_u h_pf _ _ hne]
        congr 1
        apply Subtype.ext
        change w = VarSymb.update id y u.toVar w
        simp [VarSymb.update, hwy]
  | _, .func fn => by
      rw [Term.ctx_extU_func, Term.mapCtx_func, Term.substCore_func, Term.mapCtx_func,
          Func.substCore_var_ctx_extU u hyB huB hu_y hy_u hreord h_pf hmem _ fn]
  | _, .unit => by
      rw [Term.ctx_extU_unit, Term.mapCtx_unit, Term.substCore_unit, Term.mapCtx_unit]
  | _, .pair a b => by
      rw [Term.ctx_extU_pair, Term.mapCtx_pair, Term.substCore_pair, Term.mapCtx_pair,
          Term.substCore_var_ctx_extU u hyB huB hu_y hy_u hreord h_pf hmem _ a,
          Term.substCore_var_ctx_extU u hyB huB hu_y hy_u hreord h_pf hmem _ b]
  | _, .boxterm tt hsub hne => by
      sorry
  | _, .diaterm x hx tt hsub hne => by
      sorry
  | _, .pair_elim T₁ T₂ z hz w₁eq w₂eq body => by
      -- vacuous: a pair variable of `B + y` lies in `B` (y is `Var`-typed), contradicting `h_pf`.
      exfalso
      have hmemBy : (⟨z, T₁.VTypeProd T₂⟩ : VarSymb × VarType)
          ∈ (VarCtx_insert ⟨y, .Var⟩ B hyB).1 := by
        rw [← w₂eq]; exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp hmemBy with h | hB
      · exact VarType.noConfusion (congrArg Prod.snd h)
      · exact h_pf z T₁ T₂ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hB))
  termination_by _ t => sizeOf t

theorem Func.substCore_var_ctx_extU {σ : Signature} {B : VarCtx} (u : UserSymb) {y : VarSymb}
    (hyB : y ∉ VarCtx_to_VarSymbs B) (huB : u.toVar ∉ VarCtx_to_VarSymbs B)
    (hu_y : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨y, .Var⟩ B hyB))
    (hy_u : y ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, .Var⟩ B huB))
    (hreord : VarCtx_insert ⟨u.toVar, .Var⟩ (VarCtx_insert ⟨y, .Var⟩ B hyB) hu_y
                = VarCtx_insert ⟨y, .Var⟩ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB) hy_u)
    (h_pf : (VarCtx_insert ⟨y, .Var⟩ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB) hy_u).PairFree)
    (hmem : (⟨u.toVar, .Var⟩ : VarSymb × VarType)
      ∈ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB).1) :
    ∀ (N : ℕ) (fn : Func σ (VarCtx_insert ⟨y, .Var⟩ B hyB) N),
      Func.substCore hy_u h_pf (Term.var ⟨u.toVar, hmem⟩)
          (Func.mapCtx (CtxBij.idOfEq hreord) (Func.ctx_extU u .Var hu_y fn))
        = Func.mapCtx (CtxBij.renameOne y u.toVar .Var hyB huB) fn
  | _, .F hr => by
      rw [Func.ctx_extU_F, Func.mapCtx_F, Func.substCore_F, Func.mapCtx_F]
  | _, .eval g t => by
      rw [Func.ctx_extU_eval, Func.mapCtx_eval, Func.substCore_eval, Func.mapCtx_eval,
          Func.substCore_var_ctx_extU u hyB huB hu_y hy_u hreord h_pf hmem _ g,
          Term.substCore_var_ctx_extU u hyB huB hu_y hy_u hreord h_pf hmem _ t]
  termination_by _ fn => sizeOf fn
end
