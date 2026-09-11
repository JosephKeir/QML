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

The `boxterm`/`diaterm` arms need no IH: the `Var`-typed `y` can be neither a modal node's witness
nor in its inner context, so `substCore` passes through, and off `y` the identity and `renameOne`
agree (`imageCtx_congr` + `mapCtx_congr`, as in A1's modal arms).

⚠️**WIP**: `Term`/`Func` level only (sorry-free), `T = .Var` only.  Nothing imports this file.
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

/-- The `boxterm` pass-through: the substituted variable does not occur inside the box. -/
theorem Term.substCore_boxterm_out {σ : Signature} {V V_inner : VarCtx} {x : VarSymb}
    {S A : VarType} (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree) (s : Term σ V S) (tt : Term σ V_inner A)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1, VarType.isBox p.2 = true
             → p ∈ (VarCtx_box V_inner).1)
    (h_x_out : x ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_box V_inner).1 ⊆ V.1)
    (hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    Term.substCore hx h_pf s (Term.boxterm tt hsub hne) = Term.boxterm tt hsub' hne' := by
  conv_lhs => unfold Term.substCore
  simp only [dif_neg h_x_out]

/-- The `diaterm` pass-through: neither the witness nor the interior is the substituted variable. -/
theorem Term.substCore_diaterm_out {σ : Signature} {V V_inner : VarCtx} {x : VarSymb}
    {S A : VarType} (hx : x ∉ VarCtx_to_VarSymbs V)
    (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree) (s : Term σ V S)
    {xv : VarSymb × VarType} (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (tt : Term σ (VarCtx_insert xv V_inner hxv) A)
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hne : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1, VarType.isBox p.2 = true
             → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (h_xv_ne : ¬ (xv.1 = x)) (h_x_out : x ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1)
    (hne' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    Term.substCore hx h_pf s (Term.diaterm xv hxv tt hsub hne)
      = Term.diaterm xv hxv tt hsub' hne' := by
  conv_lhs => unfold Term.substCore
  simp only [dif_neg h_xv_ne, dif_neg h_x_out]

/-! ## A `Var`-typed entry is invisible to modal nodes

`VarCtx_box`/`VarCtx_dia` contain only box- and dia-typed entries, so a `Var`-typed variable `y` is
neither in a modal node's inner context nor its witness, and side conditions stated against
`W + ⟨y, Var⟩` transfer to `W`. -/

theorem VarCtx.box_entry_ne_Var {U : VarCtx} : ∀ p ∈ (VarCtx_box U).1, p.2 ≠ .Var := by
  intro p hp h
  rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
  cases h

theorem VarCtx.dia_entry_ne_Var {U : VarCtx} {xv : VarSymb × VarType}
    {hxv : xv.1 ∉ VarCtx_to_VarSymbs U} : ∀ p ∈ (VarCtx_dia xv U hxv).1, p.2 ≠ .Var := by
  intro p hp
  rw [VarCtx_dia_fst] at hp
  rcases Finset.mem_insert.mp hp with rfl | hp'
  · intro h; cases h
  · exact VarCtx.box_entry_ne_Var p hp'

theorem VarCtx.sub_of_sub_insert_Var {P : Finset (VarSymb × VarType)} {W : VarCtx} {y : VarSymb}
    {hy : y ∉ VarCtx_to_VarSymbs W} (hP : ∀ p ∈ P, p.2 ≠ .Var)
    (h : P ⊆ (VarCtx_insert ⟨y, .Var⟩ W hy).1) : P ⊆ W.1 := by
  intro p hp
  rcases Finset.mem_insert.mp (h hp) with rfl | hW
  · exact (hP _ hp rfl).elim
  · exact hW

theorem VarCtx.notMem_inner_of_box_sub_Var {U W : VarCtx} {y : VarSymb}
    (hy : y ∉ VarCtx_to_VarSymbs W)
    (hsub : (VarCtx_box U).1 ⊆ (VarCtx_insert ⟨y, .Var⟩ W hy).1) :
    y ∉ VarCtx_to_VarSymbs U := by
  intro hyU
  rcases Finset.mem_image.mp hyU with ⟨p, hp, hpy⟩
  have hbox : (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ∈ (VarCtx_box U).1 :=
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  rcases Finset.mem_insert.mp (hsub hbox) with h | h
  · exact VarType.noConfusion (congrArg Prod.snd h)
  · exact hy (Finset.mem_image.mpr ⟨_, h, hpy⟩)

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
      -- no IH: `y` is not inside the box, and off `y` the two maps agree
      rename_i V_inner _
      have hyE : y ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, .Var⟩
          (VarCtx_insert ⟨y, .Var⟩ B hyB) hu_y) :=
        Finset.mem_image.mpr ⟨⟨y, .Var⟩, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), rfl⟩
      have hy_in : y ∉ VarCtx_to_VarSymbs V_inner := VarCtx.notMem_inner_of_box_sub_Var hyB hsub
      have hfY : ∀ v, v ≠ y → (CtxBij.idOfEq hreord).toCtxMap.f v
          = (CtxBij.renameOne y u.toVar .Var hyB huB).toCtxMap.f v := by
        intro v hv
        change v = VarSymb.update id y u.toVar v
        simp [VarSymb.update, hv]
      -- the weakened side
      have hsubE := box_sub_insert_pass (u := u) (T := .Var) (hu := hu_y) hsub
      have hneE := box_extras_insert_pass (u := u) (hu := hu_y)
        (rfl : VarType.Var.isBox = false) hne
      have hUE := VarCtx.symbs_of_box_sub hsubE
      have hsubI := CtxBij.box_sub_image (CtxBij.idOfEq hreord) hsubE hUE
      have hneI := CtxBij.box_extras_image (CtxBij.idOfEq hreord) hneE hUE
      have hyI : y ∉ VarCtx_to_VarSymbs ((CtxBij.idOfEq hreord).imageCtx V_inner hUE) :=
        CtxBij.notMem_imageCtx (CtxBij.idOfEq hreord) hUE hyE hy_in
      -- the renamed side
      have hU := VarCtx.symbs_of_box_sub hsub
      have hI : (CtxBij.idOfEq hreord).imageCtx V_inner hUE
          = (CtxBij.renameOne y u.toVar .Var hyB huB).imageCtx V_inner hU :=
        CtxBij.imageCtx_congr _ _ V_inner hUE hU (fun v hv => hfY v (fun h => hy_in (h ▸ hv)))
      have hX := Term.mapCtx_congr ((CtxBij.idOfEq hreord).toImage V_inner hUE)
        ((CtxBij.renameOne y u.toVar .Var hyB huB).toImage V_inner hU) hI
        (fun v hv => hfY v (fun h => hy_in (h ▸ hv))) tt
      rw [Term.ctx_extU_boxterm_pass u .Var rfl rfl hu_y tt hsub hne hsubE hneE,
          Term.mapCtx_boxterm (CtxBij.idOfEq hreord) tt hsubE hneE hUE hsubI hneI,
          Term.substCore_boxterm_out hy_u h_pf _ _ hsubI hneI hyI
            (VarCtx.sub_of_sub_insert_Var VarCtx.box_entry_ne_Var hsubI)
            (fun p hp hb => hneI p (Finset.mem_insert_of_mem hp) hb),
          Term.mapCtx_boxterm (CtxBij.renameOne y u.toVar .Var hyB huB) tt hsub hne hU
            (CtxBij.box_sub_image _ hsub hU) (CtxBij.box_extras_image _ hne hU)]
      exact Term.boxterm_congr' hI _ _ hX _ _ _ _
  | _, .diaterm xv hxv tt hsub hne => by
      -- no IH: `y` is neither the witness nor inside, and off `y` the two maps agree
      rename_i V_inner _
      have hyE : y ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, .Var⟩
          (VarCtx_insert ⟨y, .Var⟩ B hyB) hu_y) :=
        Finset.mem_image.mpr ⟨⟨y, .Var⟩, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), rfl⟩
      have hy_in : y ∉ VarCtx_to_VarSymbs V_inner :=
        VarCtx.notMem_inner_of_box_sub_Var hyB
          (fun p hp => hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp))
      have hxv_ne : xv.1 ≠ y := by
        intro h
        rcases Finset.mem_insert.mp (VarCtx.dia_witness_mem hsub) with h' | h'
        · exact VarType.noConfusion (congrArg Prod.snd h')
        · exact hyB (Finset.mem_image.mpr ⟨_, h', h⟩)
      have hfY : ∀ v, v ≠ y → (CtxBij.idOfEq hreord).toCtxMap.f v
          = (CtxBij.renameOne y u.toVar .Var hyB huB).toCtxMap.f v := by
        intro v hv
        change v = VarSymb.update id y u.toVar v
        simp [VarSymb.update, hv]
      -- the weakened side
      have hsubE := dia_sub_insert_pass (u := u) (T := .Var) (hu := hu_y) hsub
      have hneE := dia_extras_insert_pass (u := u) (hu := hu_y)
        (rfl : VarType.Var.isBox = false) hne
      have hUE := VarCtx.symbs_of_dia_sub hsubE
      have hxVE : xv.1 ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, .Var⟩
          (VarCtx_insert ⟨y, .Var⟩ B hyB) hu_y) :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsubE, rfl⟩
      have hx'I := CtxBij.notMem_imageCtx (CtxBij.idOfEq hreord) hUE hxVE hxv
      have hsubI := CtxBij.dia_sub_image (CtxBij.idOfEq hreord) hsubE hUE hx'I
      have hneI := CtxBij.dia_extras_image (CtxBij.idOfEq hreord) hneE hUE hx'I
      have hyI : y ∉ VarCtx_to_VarSymbs ((CtxBij.idOfEq hreord).imageCtx V_inner hUE) :=
        CtxBij.notMem_imageCtx (CtxBij.idOfEq hreord) hUE hyE hy_in
      -- the renamed side
      have hU := VarCtx.symbs_of_dia_sub hsub
      have hxV : xv.1 ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨y, .Var⟩ B hyB) :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub, rfl⟩
      have hx'R := CtxBij.notMem_imageCtx (CtxBij.renameOne y u.toVar .Var hyB huB) hU hxV hxv
      have hxx : (⟨(CtxBij.idOfEq hreord).toCtxMap.f xv.1, xv.2⟩ : VarSymb × VarType)
          = ⟨(CtxBij.renameOne y u.toVar .Var hyB huB).toCtxMap.f xv.1, xv.2⟩ := by
        rw [hfY xv.1 hxv_ne]
      have hI : (CtxBij.idOfEq hreord).imageCtx V_inner hUE
          = (CtxBij.renameOne y u.toVar .Var hyB huB).imageCtx V_inner hU :=
        CtxBij.imageCtx_congr _ _ V_inner hUE hU (fun v hv => hfY v (fun h => hy_in (h ▸ hv)))
      have hCtx : VarCtx_insert (⟨(CtxBij.idOfEq hreord).toCtxMap.f xv.1, xv.2⟩
            : VarSymb × VarType) ((CtxBij.idOfEq hreord).imageCtx V_inner hUE) hx'I
          = VarCtx_insert ⟨(CtxBij.renameOne y u.toVar .Var hyB huB).toCtxMap.f xv.1, xv.2⟩
              ((CtxBij.renameOne y u.toVar .Var hyB huB).imageCtx V_inner hU) hx'R := by
        refine VarCtx_ext _ _ ?_
        change insert (⟨(CtxBij.idOfEq hreord).toCtxMap.f xv.1, xv.2⟩ : VarSymb × VarType)
              ((CtxBij.idOfEq hreord).imageCtx V_inner hUE).1
            = insert (⟨(CtxBij.renameOne y u.toVar .Var hyB huB).toCtxMap.f xv.1, xv.2⟩
                : VarSymb × VarType)
                ((CtxBij.renameOne y u.toVar .Var hyB huB).imageCtx V_inner hU).1
        rw [hxx, hI]
      have hf' : ∀ v ∈ VarCtx_to_VarSymbs (VarCtx_insert xv V_inner hxv),
          ((CtxBij.idOfEq hreord).extendPoint V_inner hUE xv hxVE hxv hx'I).toCtxMap.f v
            = ((CtxBij.renameOne y u.toVar .Var hyB huB).extendPoint V_inner hU xv hxV hxv
                hx'R).toCtxMap.f v := by
        intro v hv
        rw [VarCtx_to_VarSymbs_insert] at hv
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact hfY _ hxv_ne
        · exact hfY v (fun h => hy_in (h ▸ hv'))
      have hX := Term.mapCtx_congr
        ((CtxBij.idOfEq hreord).extendPoint V_inner hUE xv hxVE hxv hx'I)
        ((CtxBij.renameOne y u.toVar .Var hyB huB).extendPoint V_inner hU xv hxV hxv hx'R)
        hCtx hf' tt
      rw [Term.ctx_extU_diaterm_pass u .Var rfl rfl hu_y hxv tt hsub hne hsubE hneE,
          Term.mapCtx_diaterm (CtxBij.idOfEq hreord) hxv tt hsubE hneE hUE hxVE hx'I hsubI hneI,
          -- ⚠️the witness must be given: left implicit, `id` unfolds and it is inferred as `xv`
          Term.substCore_diaterm_out
            (xv := (⟨(CtxBij.idOfEq hreord).toCtxMap.f xv.1, xv.2⟩ : VarSymb × VarType))
            hy_u h_pf _ hx'I _ hsubI hneI hxv_ne hyI
            (VarCtx.sub_of_sub_insert_Var VarCtx.dia_entry_ne_Var hsubI)
            (fun p hp hb => hneI p (Finset.mem_insert_of_mem hp) hb),
          Term.mapCtx_diaterm (CtxBij.renameOne y u.toVar .Var hyB huB) hxv tt hsub hne hU hxV
            hx'R (CtxBij.dia_sub_image _ hsub hU hx'R) (CtxBij.dia_extras_image _ hne hU hx'R)]
      exact Term.diaterm_congr' hxx hI _ _ hCtx hX _ _ _ _
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

/-! ## LEMMA B1 for `Rel` -/

theorem Rel.substCore_var_ctx_extU {σ : Signature} {B : VarCtx} (u : UserSymb) {y : VarSymb}
    (hyB : y ∉ VarCtx_to_VarSymbs B) (huB : u.toVar ∉ VarCtx_to_VarSymbs B)
    (hu_y : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨y, .Var⟩ B hyB))
    (hy_u : y ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, .Var⟩ B huB))
    (hreord : VarCtx_insert ⟨u.toVar, .Var⟩ (VarCtx_insert ⟨y, .Var⟩ B hyB) hu_y
                = VarCtx_insert ⟨y, .Var⟩ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB) hy_u)
    (h_pf : (VarCtx_insert ⟨y, .Var⟩ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB) hy_u).PairFree)
    (hmem : (⟨u.toVar, .Var⟩ : VarSymb × VarType)
      ∈ (VarCtx_insert ⟨u.toVar, .Var⟩ B huB).1) :
    ∀ {n : ℕ} (R : Rel σ (VarCtx_insert ⟨y, .Var⟩ B hyB) n),
      Rel.substCore hy_u h_pf (Term.var ⟨u.toVar, hmem⟩)
          (Rel.mapCtx (CtxBij.idOfEq hreord) (Rel.ctx_extU u .Var hu_y R))
        = Rel.mapCtx (CtxBij.renameOne y u.toVar .Var hyB huB) R
  | _, .R _ => rfl
  | _, .eval R' t => by
      rw [Rel.ctx_extU_eval, Rel.mapCtx_eval, Rel.mapCtx_eval]
      simp only [Rel.substCore,
        Rel.substCore_var_ctx_extU u hyB huB hu_y hy_u hreord h_pf hmem R',
        Term.substCore_var_ctx_extU u hyB huB hu_y hy_u hreord h_pf hmem _ t]
