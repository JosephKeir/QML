import QML.QML_v11_Symbols

/-!
# QML v11 — Terms

The v11 `Term`, differing from v10 in exactly one constructor: `pair_elim`.

## Which variables are genuinely BOUND

Only `pair_elim`'s two components.  Everything modal keeps user-supplied names, because those
variables stay FREE:

* `boxterm` promotes every variable of the inner context with `□`; all of them remain free and
  referenceable in the result.
* `diaterm x` takes an object in a context `Γ` containing `x`, and produces one in a context where
  every variable of `Γ` *except* `x` is promoted with `□`, `x` itself is promoted with `◇`, and
  the context may be weakened provided no boxed variable is added.  So `x` is a *promoted free*
  variable, not a binder — it is still there afterwards, at type `x.2.VTypeDia`.
* `pair_elim v₁ v₂ z`'s `z` is likewise free: it is the pair variable being destructured, live in
  the output context `W₂`.  Only `v₁, v₂` are consumed.

So `v₁, v₂` are the only genuine binders here, and in v11 they are no longer named: they take the
canonical slots `VarCtx.insertBnd2`, which are functions of the context alone.  The constructor
therefore loses its two symbol arguments, both freshness hypotheses, and the distinctness
hypothesis — all of which are now theorems rather than data.

Consequences: α-variants of a `pair_elim` cannot be *expressed*, so `Proof.pair_elim_alpha` has
nothing left to say and becomes retirable; and since `v₁, v₂` can never be user symbols, a user
variable can never be captured, so `new ∉ Term.boundVars t` side conditions are vacuous for user
renamings.
-/

/-! ## Signature (unchanged from v10) -/

structure Signature where
  FuncSyms : Type
  RelSyms : Type
  funcArity : FuncSyms → ℕ
  relArity  : RelSyms  → ℕ
  [decEqF   : DecidableEq FuncSyms]
  [decEqR   : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

/-! ## Terms -/

mutual
  inductive Func (σ : Signature) : VarCtx → ℕ → Type where
    | F    : {f : σ.FuncSyms // σ.funcArity f = n} → Func σ V n
    | eval : Func σ V (Nat.succ n) → Term σ V .Var → Func σ V n
    deriving DecidableEq

  /-- `Term σ V S`: a term of `VarType` `S` with free variables drawn from `VarCtx` `V`. -/
  inductive Term (σ : Signature) : VarCtx → VarType → Type where
    -- `.var` only produces basic (Var-typed) terms; modal / pair / unit terms must be built via
    -- the dedicated constructors, which removes the syntactic ambiguity where `.var x : T.VTypeBox`
    -- and `.boxterm (.var x) …` would be two forms for the same semantic value.
    | var       : {v : VarSymb // ⟨v, .Var⟩ ∈ V.1} → Term σ V .Var
    | func      : Func σ V 0 → Term σ V .Var
    | boxterm   : Term σ V S → (hsub : (VarCtx_box V).1 ⊆ W.1) →
                  (h_no_box_extras :
                    ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V).1) →
                  Term σ W S.VTypeBox
    -- `x` is a PROMOTED FREE variable, not a binder: it survives into `W` at type `x.2.VTypeDia`.
    | diaterm   : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V) →
                  Term σ (VarCtx_insert x V hx) S →
                  (hsub : (VarCtx_dia x V hx).1 ⊆ W.1) →
                  (h_no_box_extras :
                    ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1) →
                  Term σ W S.VTypeDia
    | unit      : Term σ V .VTypeOne
    | pair      : Term σ V S → Term σ V T → Term σ V (.VTypeProd S T)
    -- ⭐v11: the two components are BOUND, so they are canonical slots rather than names.  Only
    -- the destructured pair variable `z` is user-supplied, because it stays free in `W₂`.
    | pair_elim : (T₁ T₂ : VarType) → (z : VarSymb) →
                  (hz : z ∉ VarCtx_to_VarSymbs V) →
                  (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁) →
                  (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) →
                  Term σ W₁ S →
                  Term σ W₂ S
  deriving DecidableEq
end

/-! ## Renaming

`Term.rename old new` replaces a FREE variable.  In v11 both `old` and `new` are user symbols, so:

* **no capture-avoidance side condition.**  v10 carried `new ∉ Term.boundVars old_term` at every
  call; here `new` is a `.mk` and every binder is a `.bnd`, so capture is impossible by
  construction and the hypothesis is dropped outright.  `Term.boundVars` is not needed.
* **binders are untouched.**  A `pair_elim`'s slots are canonical, and renaming a user variable in
  the context leaves `nextBnd` fixed (`VarCtx.nextBnd_insert_user`), so the slots of the rebuilt
  node are literally the same ones.
-/

mutual
  def Func.rename {σ : Signature} (old new : VarSymb) (repl_type : VarType)
      (V W : VarCtx) (N : ℕ)
      (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
      (hold : old.isUsr = true) (hnew : new.isUsr = true)
      (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
      (old_func : Func σ W N)
      : Func σ (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) N := by
    match old_func with
    | .F fs => exact .F fs
    | .eval g t =>
        exact .eval (Func.rename old new repl_type V W _ old_fresh new_fresh hold hnew Wdef g)
                    (Term.rename old new repl_type V W _ old_fresh new_fresh hold hnew Wdef t)

  def Term.rename {σ : Signature} (old new : VarSymb) (repl_type : VarType)
      (V W : VarCtx) (S : VarType)
      (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
      (hold : old.isUsr = true) (hnew : new.isUsr = true)
      (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
      (old_term : Term σ W S)
      : Term σ (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) S := by
    match old_term with
    | .var ⟨v, veq⟩ =>
      if h_v_old : v = old then
        have old_in_W : ⟨old, repl_type⟩ ∈ W.1 := by rw [Wdef]; exact Finset.mem_insert_self _ _
        have hVar : VarType.Var = repl_type :=
          W.2 ⟨v, .Var⟩ veq ⟨old, repl_type⟩ old_in_W h_v_old
        exact .var ⟨new, hVar ▸ Finset.mem_insert_self _ _⟩
      else
        have hv_V : ⟨v, .Var⟩ ∈ V.1 := by
          rw [Wdef] at veq
          rcases Finset.mem_insert.mp veq with heq | hv
          · exact absurd (congrArg Prod.fst heq) h_v_old
          · exact hv
        exact .var ⟨v, Finset.mem_insert_of_mem hv_V⟩
    | .func f =>
        exact .func (Func.rename old new repl_type V W _ old_fresh new_fresh hold hnew Wdef f)
    | .unit => exact .unit
    | .pair t1 t2 =>
        exact .pair (Term.rename old new repl_type V W _ old_fresh new_fresh hold hnew Wdef t1)
                    (Term.rename old new repl_type V W _ old_fresh new_fresh hold hnew Wdef t2)
    | .boxterm inner_t box_context_sub h_box_no_extras =>
        rename_i inner_ctx inner_termtype
        rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩
        · -- Var
          refine .boxterm inner_t ?_ (by
            -- New W = insert ⟨new, .Var⟩ V; the added entry is non-box, so the
            -- predicate transfers from the original W via Wdef.
            intro p hp h_box
            rcases Finset.mem_insert.mp hp with h_eq | hp_V
            · subst h_eq; simp [VarType.isBox] at h_box
            · exact h_box_no_extras p (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V)
                h_box)
          have : (VarCtx_box inner_ctx).1 ⊆ V.1 := by
            intro x x_in_box_inner
            rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub x_in_box_inner) with xold | xV
            · rcases xold ▸ Finset.mem_image.mp x_in_box_inner with ⟨w, weq⟩
              have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
              simp only [reduceCtorEq, and_false] at this
            · exact xV
          exact (Finset.subset_insert_iff_of_notMem fun a ↦
            new_fresh (Finset.mem_image.mpr ⟨_, this a, rfl⟩)).mpr this
        · -- VTypeBox: recurse into inner_t if old is bound in inner_ctx, else pass through
          if h : ⟨old, innertype⟩ ∈ inner_ctx.1 then
            let innerCtx' := VarCtx_erase inner_ctx ⟨old, innertype⟩
            have oldinner_fresh : old ∉ VarCtx_to_VarSymbs innerCtx' := VarCtx_erase_fresh h
            have innerCtx_eq : inner_ctx =
                VarCtx_insert ⟨old, innertype⟩ innerCtx' oldinner_fresh :=
              (VarCtx_insert_erase h oldinner_fresh).symm
            have hbox_sub : (VarCtx_box innerCtx').1 ⊆ V.1 := by
              intro y hy
              have hy_inner : y ∈ (VarCtx_box inner_ctx).1 := by
                rcases Finset.mem_image.mp hy with ⟨w, hvin, hveq⟩
                exact Finset.mem_image.mpr ⟨w, Finset.erase_subset _ _ hvin, hveq⟩
              rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub hy_inner) with rfl | hV
              · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, hvin, hveq⟩
                simp only [Prod.mk.injEq] at hveq
                exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, innertype⟩,
                  hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin, rfl⟩)).elim
              · exact hV
            have newinner_fresh : new ∉ VarCtx_to_VarSymbs innerCtx' := fun hmem => by
              rcases Finset.mem_image.mp hmem with ⟨w, hvin, hveq⟩
              exact new_fresh (Finset.mem_image.mpr ⟨⟨w.1, w.2.VTypeBox⟩,
                hbox_sub (Finset.mem_image.mpr ⟨w, hvin, rfl⟩), hveq⟩)
            let renamed_t := Term.rename old new innertype innerCtx' inner_ctx inner_termtype
                                         oldinner_fresh newinner_fresh hold hnew innerCtx_eq inner_t
            refine .boxterm renamed_t ?_ (by
              -- New W has ⟨new, innertype.VTypeBox⟩ as the only added box-typed
              -- entry, and that exact entry is in VarCtx_box (insert ⟨new, innertype⟩ innerCtx').
              -- Other box-typed entries in V transfer from VarCtx_box inner_ctx via
              -- h_box_no_extras (after erasing the now-renamed ⟨old, innertype⟩).
              intro p hp h_box
              rw [VarCtx_box_fst_insert]
              rcases Finset.mem_insert.mp hp with h_eq | hp_V
              · subst h_eq
                exact Finset.mem_insert_self _ _
              · have hp1_ne_old : p.1 ≠ old := fun h_eq =>
                  old_fresh (Finset.mem_image.mpr ⟨p, hp_V, h_eq⟩)
                have hp_W : p ∈ W.1 := by
                  rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
                have hp_box_inner : p ∈ (VarCtx_box inner_ctx).1 :=
                  h_box_no_extras p hp_W h_box
                rcases Finset.mem_image.mp hp_box_inner with ⟨⟨v, S⟩, hvS_in, hvS_eq⟩
                have hp_eq_v : p.1 = v := (Prod.mk.inj hvS_eq).1.symm
                have hv_ne_old : v ≠ old := hp_eq_v ▸ hp1_ne_old
                apply Finset.mem_insert_of_mem
                refine Finset.mem_image.mpr ⟨⟨v, S⟩, ?_, hvS_eq⟩
                change ⟨v, S⟩ ∈ (inner_ctx.1.erase _)
                exact Finset.mem_erase.mpr ⟨fun h_eq => hv_ne_old (Prod.mk.inj h_eq).1, hvS_in⟩)
            rw [VarCtx_box_fst_insert]
            exact Finset.insert_subset_insert _ hbox_sub
          else
            -- Under the new no-box-extras constraint, this branch is impossible
            -- (the original W contains ⟨old, .VTypeBox innertype⟩, forcing
            -- ⟨old, innertype⟩ ∈ inner_ctx via h_box_no_extras). We still build
            -- a syntactic boxterm so that downstream `boundVars` reduces; the
            -- impossibility is discharged into the h_no_box_extras proof obligation.
            refine .boxterm inner_t ?_ (by
              exfalso
              have h_old_in_W : (⟨old, innertype.VTypeBox⟩ : VarSymb × VarType) ∈ W.1 := by
                rw [Wdef]; exact Finset.mem_insert_self _ _
              have h_in_box : (⟨old, innertype.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (VarCtx_box inner_ctx).1 :=
                h_box_no_extras _ h_old_in_W rfl
              rcases Finset.mem_image.mp h_in_box with ⟨⟨v, S⟩, hvin, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin))
            have hbox_old_not : ⟨old, innertype.VTypeBox⟩ ∉ (VarCtx_box inner_ctx).1 := by
              intro hmem
              rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin)
            have hsub : (VarCtx_box inner_ctx).1 ⊆ V.1 := by
              intro y hy
              rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub hy) with rfl | hV
              · exact absurd hy hbox_old_not
              · exact hV
            exact Finset.Subset.trans hsub (Finset.subset_insert _ _)
        -- remaining cases are all the same: VTypeDia, VTyprProd and VTypeOne
        -- For h_no_box_extras: .VTypeDia/.VTypeOne discharge via simp (isBox=false).
        -- .VTypeProd may have isBox=true via recursion through box components;
        -- in that case use h_box_no_extras on ⟨old, repl_type⟩ for contradiction
        -- (VarCtx_box inner_ctx has only .VTypeBox-outer entries).
        all_goals refine .boxterm inner_t ?_ (by
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
        all_goals have : (VarCtx_box inner_ctx).1 ⊆ V.1 := by
          { intro x x_in_box_inner
            rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub x_in_box_inner) with xold | xV
            · rcases xold ▸ Finset.mem_image.mp x_in_box_inner with ⟨w, weq⟩
              have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
              simp only [reduceCtorEq, and_false] at this
            · exact xV
          }
        all_goals exact (Finset.subset_insert_iff_of_notMem fun a ↦
          new_fresh (Finset.mem_image.mpr ⟨_, this a, rfl⟩)).mpr this
    | .diaterm x hx inner_t dia_ctx_sub h_dia_no_extras =>
        rename_i inner_ctx inner_type
        match repl_type with
        | .Var | .VTypeOne | .VTypeProd _ _ =>
            -- repl_type is none of VTypeBox/VTypeDia, so ⟨old, repl_type⟩ can't appear
            -- in VarCtx_dia; everything else in VarCtx_dia lies in V.
            refine .diaterm x hx inner_t ?_ (by
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
            -- VTypeBox: recurse into inner_t if old is bound in inner_ctx, else pass through
            if h : ⟨old, repl_inner_type⟩ ∈ inner_ctx.1 then
              let innerCtx' := VarCtx_erase inner_ctx ⟨old, repl_inner_type⟩
              have oldinner_fresh : old ∉ VarCtx_to_VarSymbs innerCtx' :=
                VarCtx_erase_fresh h
              have hx_ne_old : x.1 ≠ old := fun heq =>
                hx (Finset.mem_image.mpr ⟨⟨old, repl_inner_type⟩, h, heq.symm⟩)
              have hx' : x.1 ∉ VarCtx_to_VarSymbs innerCtx' :=
                fun hmem => hx (VarCtx_to_VarSymbs_erase_subset hmem)
              have hbox_sub : (VarCtx_box innerCtx').1 ⊆ V.1 := by
                intro y hy
                have hy_inner_box : y ∈ (VarCtx_box inner_ctx).1 := by
                  rcases Finset.mem_image.mp hy with ⟨w, hvin, hveq⟩
                  exact Finset.mem_image.mpr ⟨w, Finset.erase_subset _ _ hvin, hveq⟩
                have hy_dia : y ∈ (VarCtx_dia x inner_ctx hx).1 :=
                  Finset.mem_insert_of_mem hy_inner_box
                rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy_dia) with rfl | hV
                · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, hvin, hveq⟩
                  simp only [Prod.mk.injEq] at hveq
                  exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, repl_inner_type⟩,
                    hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin, rfl⟩)).elim
                · exact hV
              have hx1_in_V : ⟨x.1, x.2.VTypeDia⟩ ∈ V.1 := by
                have hx_in_dia : ⟨x.1, x.2.VTypeDia⟩ ∈ (VarCtx_dia x inner_ctx hx).1 :=
                  Finset.mem_insert_self _ _
                rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hx_in_dia) with heq | hV
                · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
                · exact hV
              have hnew_ne_x : new ≠ x.1 := fun heq =>
                new_fresh (Finset.mem_image.mpr
                  ⟨⟨x.1, x.2.VTypeDia⟩, hx1_in_V, heq.symm⟩)
              have newinner_fresh : new ∉ VarCtx_to_VarSymbs innerCtx' := fun hmem => by
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
              have innerCtx_eq : VarCtx_insert x inner_ctx hx =
                  VarCtx_insert ⟨old, repl_inner_type⟩
                                (VarCtx_insert x innerCtx' hx') oldinnerX_fresh :=
                VarCtx_ext _ _ <| by
                  change insert x inner_ctx.1 =
                       insert ⟨old, repl_inner_type⟩ (insert x innerCtx'.1)
                  rw [← Finset.insert_erase h]; exact Finset.insert_comm _ _ _
              let renamed_t := Term.rename old new repl_inner_type
                                 (VarCtx_insert x innerCtx' hx')
                                 (VarCtx_insert x inner_ctx hx)
                                 inner_type
                                 oldinnerX_fresh newinnerX_fresh hold hnew innerCtx_eq inner_t
              have ctx_swap :
                  VarCtx_insert ⟨new, repl_inner_type⟩
                                (VarCtx_insert x innerCtx' hx') newinnerX_fresh =
                  VarCtx_insert x
                    (VarCtx_insert ⟨new, repl_inner_type⟩ innerCtx' newinner_fresh)
                    hx_target :=
                VarCtx_insert_comm _ _
              refine .diaterm x hx_target (ctx_swap ▸ renamed_t) ?_ (by
                intro p hp h_box
                rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
                rcases Finset.mem_insert.mp hp with h_eq | hp_V
                · subst h_eq
                  exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                · have hp1_ne_old : p.1 ≠ old := fun h_eq =>
                    old_fresh (Finset.mem_image.mpr ⟨p, hp_V, h_eq⟩)
                  have hp_W : p ∈ W.1 := by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
                  have hp_dia_inner : p ∈ (VarCtx_dia x inner_ctx hx).1 :=
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
                    change ⟨v, S⟩ ∈ inner_ctx.1.erase _
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
              -- Impossible under no-box-extras: ⟨old, .VTypeBox repl_inner_type⟩ ∈ W
              -- is box-typed, so h_dia_no_extras forces it into VarCtx_dia; it can't
              -- be the dia binder (wrong type), so it's in VarCtx_box inner_ctx, i.e.
              -- ⟨old, repl_inner_type⟩ ∈ inner_ctx — contradicting `h`.
              refine .diaterm x hx inner_t ?_ (by
                exfalso
                have h_old_in_W : (⟨old, repl_inner_type.VTypeBox⟩ : VarSymb × VarType) ∈ W.1 := by
                  rw [Wdef]; exact Finset.mem_insert_self _ _
                have h_in_dia : (⟨old, repl_inner_type.VTypeBox⟩ : VarSymb × VarType)
                                  ∈ (VarCtx_dia x inner_ctx hx).1 :=
                  h_dia_no_extras _ h_old_in_W rfl
                rcases Finset.mem_insert.mp h_in_dia with hxeq | hbox
                · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
                · rcases Finset.mem_image.mp hbox with ⟨⟨v, S⟩, hvin, hveq⟩
                  simp only [Prod.mk.injEq] at hveq
                  exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin))
              have hdia_old_not :
                  ⟨old, repl_inner_type.VTypeBox⟩ ∉ (VarCtx_dia x inner_ctx hx).1 := by
                intro hmem
                rcases Finset.mem_insert.mp hmem with heq | hbox
                · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
                · rcases Finset.mem_image.mp hbox with ⟨⟨v, S⟩, hvin, hveq⟩
                  simp only [Prod.mk.injEq] at hveq
                  exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin)
              have hsub : (VarCtx_dia x inner_ctx hx).1 ⊆ V.1 := by
                intro y hy
                rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy) with rfl | hV
                · exact absurd hy hdia_old_not
                · exact hV
              exact Finset.Subset.trans hsub (Finset.subset_insert _ _)
        | .VTypeDia repl_inner_type =>
            -- VTypeDia: if x is the bound variable being renamed, rebind to ⟨new, repl_inner_type⟩
            -- and rename inside inner_t; otherwise pass through.
            if h_x : x = ⟨old, repl_inner_type⟩ then
              -- Avoid `subst h_x` so the recursive call still sees `inner_t` as a
              -- structural sub-term of `old_term`.
              have hx_eq_old : x.1 = old := congrArg Prod.fst h_x
              have hx_old : old ∉ VarCtx_to_VarSymbs inner_ctx := hx_eq_old ▸ hx
              have hbox_sub : (VarCtx_box inner_ctx).1 ⊆ V.1 := by
                intro y hy
                have hy_dia : y ∈ (VarCtx_dia x inner_ctx hx).1 :=
                  Finset.mem_insert_of_mem hy
                rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy_dia) with rfl | hV
                · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, _, hveq⟩
                  simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
                · exact hV
              have hnew_fresh_inner : new ∉ VarCtx_to_VarSymbs inner_ctx := fun hmem => by
                rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
                exact new_fresh (Finset.mem_image.mpr ⟨⟨v, S.VTypeBox⟩,
                  hbox_sub (Finset.mem_image.mpr ⟨⟨v, S⟩, hvin, rfl⟩), hveq⟩)
              have Wdef_inner : VarCtx_insert x inner_ctx hx =
                  VarCtx_insert ⟨old, repl_inner_type⟩ inner_ctx hx_old :=
                VarCtx_ext _ _ (by
                  change insert x inner_ctx.1 = insert ⟨old, repl_inner_type⟩ inner_ctx.1
                  rw [h_x])
              let renamed_t := Term.rename old new repl_inner_type
                                 inner_ctx
                                 (VarCtx_insert x inner_ctx hx)
                                 inner_type
                                 hx_old hnew_fresh_inner hold hnew Wdef_inner inner_t
              refine .diaterm ⟨new, repl_inner_type⟩ hnew_fresh_inner renamed_t ?_ (by
                -- New W adds ⟨new, repl_inner_type.VTypeDia⟩ which is non-box.
                -- Box-typed entries in V transfer from h_dia_no_extras (and the
                -- single dia entry there is also non-box).
                intro p hp h_box
                rw [VarCtx_dia_fst]
                rcases Finset.mem_insert.mp hp with h_eq | hp_V
                · subst h_eq; simp [VarType.isBox] at h_box
                · have hp_W : p ∈ W.1 := by
                    rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
                  have hp_dia_inner : p ∈ (VarCtx_dia x inner_ctx hx).1 :=
                    h_dia_no_extras p hp_W h_box
                  rw [VarCtx_dia_fst] at hp_dia_inner
                  rcases Finset.mem_insert.mp hp_dia_inner with hpx | hp_box
                  · subst hpx; simp [VarType.isBox] at h_box
                  · exact Finset.mem_insert_of_mem hp_box)
              rw [VarCtx_dia_fst]
              exact Finset.insert_subset_insert _ hbox_sub
            else
              refine .diaterm x hx inner_t ?_ (by
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
    | .pair_elim T₁ T₂ z hz w₁_eq w₂_eq inner_term =>
        rename_i pe_V pe_W₁
        by_cases h_case : (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
        · -- Case A: the destructured pair variable IS the one being renamed.  `inner_term` lives
          -- in `insertBnd2 T₁ T₂ pe_V`, whose slots depend on `pe_V = V` only — so unlike v10
          -- there is nothing to transport and the body is reused verbatim.
          have h_repl_eq : (VarType.VTypeProd T₁ T₂) = repl_type := congrArg Prod.snd h_case
          have h_pe_V_eq_V : pe_V = V := by
            apply VarCtx_ext
            have h_not_in_pe : (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∉ pe_V.1 :=
              fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            have h_not_in_V_old : (⟨old, repl_type⟩ : VarSymb × VarType) ∉ V.1 :=
              fun h => old_fresh (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            have h_not_in_V : (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∉ V.1 :=
              h_case ▸ h_not_in_V_old
            have h_set : insert (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) pe_V.1
                       = insert (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) V.1 := by
              have orig : insert (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) pe_V.1
                        = insert (⟨old, repl_type⟩ : VarSymb × VarType) V.1 :=
                congrArg PSigma.fst (w₂_eq.trans Wdef)
              rw [← h_case] at orig
              exact orig
            change pe_V.1 = V.1
            rw [← Finset.erase_insert h_not_in_pe, h_set, Finset.erase_insert h_not_in_V]
          have w₁_eq_V : VarCtx.insertBnd2 T₁ T₂ V = pe_W₁ := h_pe_V_eq_V ▸ w₁_eq
          have w₂_eq_V : VarCtx_insert ⟨new, .VTypeProd T₁ T₂⟩ V new_fresh
              = VarCtx_insert ⟨new, repl_type⟩ V new_fresh :=
            congrArg (fun T => VarCtx_insert ⟨new, T⟩ V new_fresh) h_repl_eq
          exact .pair_elim T₁ T₂ new new_fresh w₁_eq_V w₂_eq_V inner_term
        · -- Case B: `⟨old, repl_type⟩` lives inside `pe_V`.  Erase it, rename inside the body,
          -- and rebuild.  The binder slots are IDENTICAL before and after, by
          -- `insertBnd2_comm_insert` — a user insert does not move `nextBnd`.  v10 had to
          -- transport `hv₁`/`hv₂` freshness proofs here; in v11 there is nothing to transport.
          have h_old_in_pe_V : (⟨old, repl_type⟩ : VarSymb × VarType) ∈ pe_V.1 := by
            have h_old_in_W : (⟨old, repl_type⟩ : VarSymb × VarType) ∈ W.1 := by
              rw [Wdef]; exact Finset.mem_insert_self _ _
            rw [← w₂_eq] at h_old_in_W
            rcases Finset.mem_insert.mp h_old_in_W with h_eq | h_pe_V
            · exact absurd h_eq.symm h_case
            · exact h_pe_V
          have h_old_not_in_V : (⟨old, repl_type⟩ : VarSymb × VarType) ∉ V.1 :=
            fun h => old_fresh (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          have old_fresh_pe_V' : old ∉ VarCtx_to_VarSymbs (VarCtx_erase pe_V ⟨old, repl_type⟩) :=
            VarCtx_erase_fresh h_old_in_pe_V
          have hz' : z ∉ VarCtx_to_VarSymbs (VarCtx_erase pe_V ⟨old, repl_type⟩) :=
            fun hmem => hz (VarCtx_to_VarSymbs_erase_subset hmem)
          -- `insert ⟨z,_⟩ pe_V' = V`, obtained by erasing `⟨old,repl_type⟩` from both
          -- decompositions of `W`.
          have h_erased : insert (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType)
                            (VarCtx_erase pe_V ⟨old, repl_type⟩).1 = V.1 := by
            have h_W_set : insert (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) pe_V.1
                         = insert (⟨old, repl_type⟩ : VarSymb × VarType) V.1 :=
              congrArg PSigma.fst (w₂_eq.trans Wdef)
            have step : (insert (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) pe_V.1).erase
                          ⟨old, repl_type⟩ = V.1 := by
              rw [h_W_set, Finset.erase_insert h_old_not_in_V]
            rwa [Finset.erase_insert_of_ne h_case] at step
          have h_z_ne_new : z ≠ new := fun heq => new_fresh
            (Finset.mem_image.mpr ⟨⟨z, .VTypeProd T₁ T₂⟩,
              h_erased ▸ Finset.mem_insert_self _ _, heq⟩)
          have new_fresh_pe_V' : new ∉ VarCtx_to_VarSymbs (VarCtx_erase pe_V ⟨old, repl_type⟩) := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
            exact new_fresh (Finset.mem_image.mpr ⟨⟨v, S⟩,
              h_erased ▸ Finset.mem_insert_of_mem hvin, hveq⟩)
          have old_fresh_inner : old ∉ VarCtx_to_VarSymbs
              (VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase pe_V ⟨old, repl_type⟩)) :=
            VarCtx.notMem_insertBnd_of_isUsr hold T₂
              (VarCtx.notMem_insertBnd_of_isUsr hold T₁ old_fresh_pe_V')
          have new_fresh_inner : new ∉ VarCtx_to_VarSymbs
              (VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase pe_V ⟨old, repl_type⟩)) :=
            VarCtx.notMem_insertBnd_of_isUsr hnew T₂
              (VarCtx.notMem_insertBnd_of_isUsr hnew T₁ new_fresh_pe_V')
          have Wdef_inner : pe_W₁ = VarCtx_insert ⟨old, repl_type⟩
              (VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase pe_V ⟨old, repl_type⟩)) old_fresh_inner := by
            rw [← w₁_eq]
            conv_lhs => rw [← VarCtx_insert_erase h_old_in_pe_V old_fresh_pe_V']
            exact VarCtx.insertBnd2_comm_insert ⟨old, repl_type⟩ _ old_fresh_pe_V' hold T₁ T₂
              old_fresh_inner
          have ctx_swap : VarCtx_insert ⟨new, repl_type⟩
                (VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase pe_V ⟨old, repl_type⟩)) new_fresh_inner
              = VarCtx.insertBnd2 T₁ T₂
                  (VarCtx_insert ⟨new, repl_type⟩ (VarCtx_erase pe_V ⟨old, repl_type⟩)
                    new_fresh_pe_V') :=
            (VarCtx.insertBnd2_comm_insert ⟨new, repl_type⟩ _ new_fresh_pe_V' hnew T₁ T₂
              new_fresh_inner).symm
          have hz_new : z ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨new, repl_type⟩
              (VarCtx_erase pe_V ⟨old, repl_type⟩) new_fresh_pe_V') :=
            not_mem_VarSymbs_insert h_z_ne_new hz'
          have w₂_eq_new : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩
                (VarCtx_insert ⟨new, repl_type⟩ (VarCtx_erase pe_V ⟨old, repl_type⟩)
                  new_fresh_pe_V') hz_new
              = VarCtx_insert ⟨new, repl_type⟩ V new_fresh := by
            apply VarCtx_ext
            change insert (⟨z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType)
                     (insert (⟨new, repl_type⟩ : VarSymb × VarType)
                       (VarCtx_erase pe_V ⟨old, repl_type⟩).1)
                 = insert (⟨new, repl_type⟩ : VarSymb × VarType) V.1
            rw [← h_erased, Finset.insert_comm]
          exact .pair_elim T₁ T₂ z hz_new rfl w₂_eq_new
            (ctx_swap ▸ Term.rename old new repl_type
              (VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase pe_V ⟨old, repl_type⟩)) pe_W₁ S
              old_fresh_inner new_fresh_inner hold hnew Wdef_inner inner_term)
end


/-! ## Rebuilding along a context bijection

`mapCtx` is the single traversal that renaming, shifting and lifting all reduce to.  At a binder it
uses `CtxBij.extendBnd`, which sends the OLD slot to the NEW one — so slots are RECOMPUTED from the
target context rather than transported, which is what makes the result canonical. -/

mutual
  def Func.mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {N : ℕ}
      (fn : Func σ V N) : Func σ V' N := by
    match fn with
    | .F fs => exact .F fs
    | .eval g t => exact .eval (Func.mapCtx m g) (Term.mapCtx m t)
  termination_by sizeOf fn

  def Term.mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {S : VarType}
      (t : Term σ V S) : Term σ V' S := by
    match t with
    | .var ⟨v, veq⟩ => exact .var ⟨m.toCtxMap.f v, m.toCtxMap.maps ⟨v, .Var⟩ veq⟩
    | .func fn => exact .func (Func.mapCtx m fn)
    | .unit => exact .unit
    | .pair t1 t2 => exact .pair (Term.mapCtx m t1) (Term.mapCtx m t2)
    | .boxterm inner hsub h =>
        rename_i V_inner _
        have hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
          VarCtx.symbs_of_box_sub hsub
        refine .boxterm (Term.mapCtx (m.toImage V_inner hU) inner) ?_ ?_
        · -- the image's box-wrap lands in `V'`
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
          rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
          exact m.toCtxMap.maps ⟨r.1, r.2.VTypeBox⟩
            (hsub (Finset.mem_image.mpr ⟨r, hr, rfl⟩))
        · -- ⭐`onto` is exactly what this needs: every box-typed entry of `V'` comes from one of
          -- `V`, which `h` places in the source inner context, hence in its image.
          intro p hp hbox
          obtain ⟨q, hq, rfl⟩ := m.onto p hp
          have hqbox : VarType.isBox q.2 = true := hbox
          have hqin := h q hq hqbox
          rcases Finset.mem_image.mp hqin with ⟨r, hr, hreq⟩
          refine Finset.mem_image.mpr
            ⟨⟨m.toCtxMap.f r.1, r.2⟩, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
          simp only
          obtain ⟨h1, h2⟩ := Prod.mk.inj hreq
          rw [h1, h2]
    | .diaterm x hx inner hsub h =>
        rename_i V_inner _
        -- `x` is a PROMOTED FREE variable: it sits in `V` as `⟨x.1, ◇x.2⟩`.
        have hxdia : (⟨x.1, x.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
          apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        have hxV : x.1 ∈ VarCtx_to_VarSymbs V :=
          Finset.mem_image.mpr ⟨⟨x.1, x.2.VTypeDia⟩, hxdia, rfl⟩
        have hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V := by
          intro v hv
          rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
          refine Finset.mem_image.mpr ⟨⟨p.1, p.2.VTypeBox⟩, hsub ?_, rfl⟩
          rw [VarCtx_dia_fst]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
        have hx' : m.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m.imageCtx V_inner hU) := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨p, hp, hpeq⟩
          rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
          apply hx
          have : m.toCtxMap.f q.1 = m.toCtxMap.f x.1 := hpeq
          have hq1 : q.1 = x.1 :=
            m.toCtxMap.inj q.1 (hU _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)) x.1 hxV this
          exact hq1 ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩
        refine .diaterm ⟨m.toCtxMap.f x.1, x.2⟩ hx'
          (Term.mapCtx (m.extendPoint V_inner hU x hxV hx hx') inner) ?_ ?_
        · intro p hp
          rw [VarCtx_dia_fst] at hp
          rcases Finset.mem_insert.mp hp with rfl | hbox
          · exact m.toCtxMap.maps ⟨x.1, x.2.VTypeDia⟩ hxdia
          · rcases Finset.mem_image.mp hbox with ⟨q, hq, rfl⟩
            rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
            refine m.toCtxMap.maps ⟨r.1, r.2.VTypeBox⟩ (hsub ?_)
            rw [VarCtx_dia_fst]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
        · intro p hp hbox
          obtain ⟨q, hq, rfl⟩ := m.onto p hp
          have hqin := h q hq hbox
          rw [VarCtx_dia_fst] at hqin ⊢
          rcases Finset.mem_insert.mp hqin with rfl | hqbox
          · exact Finset.mem_insert_self _ _
          · rcases Finset.mem_image.mp hqbox with ⟨r, hr, hreq⟩
            refine Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨⟨m.toCtxMap.f r.1, r.2⟩, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩)
            simp only
            obtain ⟨h1, h2⟩ := Prod.mk.inj hreq
            rw [h1, h2]
    | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
        rename_i pe_V pe_W₁
        subst w₂eq
        have hzV' : (⟨m.toCtxMap.f z, .VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∈ V'.1 :=
          m.toCtxMap.maps _ (Finset.mem_insert_self _ _)
        -- Restrict to the node's base contexts, then extend past BOTH slots.  The slots are
        -- RECOMPUTED from the target base, which is why no level hypothesis appears here — the
        -- difficulty that sank the fixed-offset design simply does not arise.
        -- NOTE: transport `w₁eq` on the MAP, not on `body`; substituting `body` would break the
        -- `sizeOf` relationship the termination proof needs.
        exact .pair_elim T₁ T₂ (m.toCtxMap.f z) (VarCtx_erase_fresh hzV') rfl
          (VarCtx_insert_erase hzV' (VarCtx_erase_fresh hzV'))
          (Term.mapCtx (w₁eq ▸ ((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂) body)
  termination_by sizeOf t
end

/-! ## Renaming, as `mapCtx` along a bijection

⭐This is the intended REPLACEMENT for `Term.rename` above.  Compare the two:

* `Term.rename` is a ~570-line traversal with a case analysis at every constructor, and carries
  `isUsr` hypotheses on both symbols — needed there because renaming had to leave binder slots
  FIXED, which only works for user variables.
* `Term.rename'` is one line.  `mapCtx` RECOMPUTES slots from the target context, so no
  slot-preservation constraint arises and the `isUsr` hypotheses disappear — making it strictly
  more general: it renames bound symbols too.

`Term.rename` is kept (and still compiles) until the migration is done and the equivalence of the
two has been checked; nothing depends on it. -/

/-- Rename one free variable, by rebuilding along the swap bijection. -/
def Term.rename' {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    {S : VarType} (t : Term σ (VarCtx_insert ⟨old, T⟩ V hold) S) :
    Term σ (VarCtx_insert ⟨new, T⟩ V hnew) S :=
  Term.mapCtx (CtxBij.renameOne old new T hold hnew) t

/-- The same for `Func`. -/
def Func.rename' {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    {N : ℕ} (fn : Func σ (VarCtx_insert ⟨old, T⟩ V hold) N) :
    Func σ (VarCtx_insert ⟨new, T⟩ V hnew) N :=
  Func.mapCtx (CtxBij.renameOne old new T hold hnew) fn
