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

/-! ## Measures

`numNodes` and `diaCount` are the termination measures the substitution machinery uses.  Both drop
the `pair_elim` binder arguments, which are no longer data.

⭐Note what is ABSENT: v10 also carries `Term.boundVars` / `Func.boundVars`, used solely to state
capture-avoidance side conditions.  Those conditions are vacuous in v11 (a user variable cannot be
captured, and a bound one is never renamed by hand), so the whole `boundVars` family is gone. -/

mutual
  def Func.numNodes {σ : Signature} {V : VarCtx} {N : ℕ} : Func σ V N → ℕ
    | .F _      => 1
    | .eval g t => 1 + Func.numNodes g + Term.numNodes t

  def Term.numNodes {σ : Signature} {V : VarCtx} {S : VarType} : Term σ V S → ℕ
    | .var _                   => 1
    | .func f                  => 1 + Func.numNodes f
    | .boxterm inner_t _ _     => 1 + Term.numNodes inner_t
    | .diaterm _ _ inner_t _ _ => 1 + Term.numNodes inner_t
    | .unit                    => 1
    | .pair t1 t2              => 1 + Term.numNodes t1 + Term.numNodes t2
    | .pair_elim _ _ _ _ _ _ b => 1 + Term.numNodes b
end

mutual
  def Func.diaCount {σ : Signature} {V : VarCtx} {N : ℕ} : Func σ V N → ℕ
    | .F _      => 0
    | .eval g t => Func.diaCount g + Term.diaCount t

  def Term.diaCount {σ : Signature} {V : VarCtx} {S : VarType} : Term σ V S → ℕ
    | .var _                   => 0
    | .func f                  => Func.diaCount f
    | .boxterm inner_t _ _     => Term.diaCount inner_t
    | .diaterm _ _ inner_t _ _ => 1 + Term.diaCount inner_t
    | .unit                    => 0
    | .pair t1 t2              => Term.diaCount t1 + Term.diaCount t2
    | .pair_elim _ _ _ _ _ _ b => Term.diaCount b
end

-- `mapCtx` is a pure rebuild: it never creates or destroys a `◇`-node.
mutual
  theorem Func.diaCount_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {N : ℕ}
      (fn : Func σ V N) : Func.diaCount (Func.mapCtx m fn) = Func.diaCount fn := by
    match fn with
    | .F _ => rw [Func.mapCtx]; rfl
    | .eval g t =>
        rw [Func.mapCtx]
        simp only [Func.diaCount]
        rw [Func.diaCount_mapCtx m g, Term.diaCount_mapCtx m t]
  termination_by sizeOf fn

  theorem Term.diaCount_mapCtx {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') {S : VarType}
      (t : Term σ V S) : Term.diaCount (Term.mapCtx m t) = Term.diaCount t := by
    match t with
    | .var _ => rw [Term.mapCtx]; rfl
    | .unit => rw [Term.mapCtx]; rfl
    | .func fn =>
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Func.diaCount_mapCtx m fn]
    | .pair t1 t2 =>
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Term.diaCount_mapCtx m t1, Term.diaCount_mapCtx m t2]
    | .boxterm inner hsub h =>
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Term.diaCount_mapCtx _ inner]
    | .diaterm xv hxv inner hsub h =>
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Term.diaCount_mapCtx _ inner]
    | .pair_elim T1 T2 z hz w1eq w2eq body =>
        rename_i pe_V pe_W1
        subst w2eq
        rw [Term.mapCtx]
        simp only [Term.diaCount]
        rw [Term.diaCount_mapCtx _ body]
  termination_by sizeOf t
end

/-! ## Pair-elim distribution

`pairElim` moves a term from the SPLIT context `V + two slots` to the JOINED one `V + ⟨z, T₁×T₂⟩`.
It is needed by `ctx_ext`: weakening by a pair-typed variable proceeds by weakening by the two
components and re-pairing.

`Rel.pairElim`/`Term.pairElim` never get genuinely stuck the way `WFF.pairElim` does — `eval` only
takes `Var`-typed terms — but the modal and nested-`pair_elim` arms still wrap rather than descend.
In v11 the two components are the canonical slots of `V`, so they are not arguments. -/

mutual
  def Func.pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
      (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
      (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
      (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) {N : ℕ} :
      Func σ W₁ N → Func σ W₂ N
    | .F h => .F h
    | .eval g t =>
        .eval (Func.pairElim T₁ T₂ z hz w₁eq w₂eq g)
              (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t)

  def Term.pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
      (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
      (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
      (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) {S : VarType} :
      Term σ W₁ S → Term σ W₂ S
    | .unit => .unit
    | .var ⟨w, hw⟩ =>
        have hb₁ : (⟨V.nextBnd, T₁⟩ : VarSymb × VarType) ∈ W₁.1 := by
          rw [← w₁eq]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        have hb₂ : (⟨(VarCtx.insertBnd T₁ V).nextBnd, T₂⟩ : VarSymb × VarType) ∈ W₁.1 := by
          rw [← w₁eq]
          exact Finset.mem_insert_self _ _
        if h₁ : w = V.nextBnd then
          have hT₁ : T₁ = .Var := W₁.2 _ hb₁ ⟨w, .Var⟩ hw h₁.symm
          Term.pair_elim T₁ T₂ z hz w₁eq w₂eq
            (.var ⟨V.nextBnd, by rw [← hT₁]; exact hb₁⟩)
        else if h₂ : w = (VarCtx.insertBnd T₁ V).nextBnd then
          have hT₂ : T₂ = .Var := W₁.2 _ hb₂ ⟨w, .Var⟩ hw h₂.symm
          Term.pair_elim T₁ T₂ z hz w₁eq w₂eq
            (.var ⟨(VarCtx.insertBnd T₁ V).nextBnd, by rw [← hT₂]; exact hb₂⟩)
        else
          have hw_V : (⟨w, .Var⟩ : VarSymb × VarType) ∈ V.1 := by
            have hw_W : (⟨w, .Var⟩ : VarSymb × VarType) ∈ W₁.1 := hw
            rw [← w₁eq] at hw_W
            rcases Finset.mem_insert.mp hw_W with h_eq | h_rest
            · exact absurd (congrArg Prod.fst h_eq) h₂
            · rcases Finset.mem_insert.mp h_rest with h_eq | h_in
              · exact absurd (congrArg Prod.fst h_eq) h₁
              · exact h_in
          .var ⟨w, by rw [← w₂eq]; exact Finset.mem_insert_of_mem hw_V⟩
    | .func f => .func (Func.pairElim T₁ T₂ z hz w₁eq w₂eq f)
    | .pair t₁ t₂ =>
        .pair (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t₁)
              (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t₂)
    | .boxterm tt hsub hne =>
        Term.pair_elim T₁ T₂ z hz w₁eq w₂eq (.boxterm tt hsub hne)
    | .diaterm xv hxv tt hsub hne =>
        Term.pair_elim T₁ T₂ z hz w₁eq w₂eq (.diaterm xv hxv tt hsub hne)
    | .pair_elim T₁' T₂' z' hz' w₁eq' w₂eq' body =>
        Term.pair_elim T₁ T₂ z hz w₁eq w₂eq
          (.pair_elim T₁' T₂' z' hz' w₁eq' w₂eq' body)
end

-- `pairElim` only ever wraps or descends; it never creates or destroys a `◇`-node.
mutual
  theorem Func.diaCount_pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
      (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
      (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
      (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) {N : ℕ} (fn : Func σ W₁ N) :
      Func.diaCount (Func.pairElim T₁ T₂ z hz w₁eq w₂eq fn) = Func.diaCount fn := by
    match fn with
    | .F _ => rfl
    | .eval g t =>
        rw [Func.pairElim]
        simp only [Func.diaCount]
        rw [Func.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq g,
            Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq t]
  termination_by sizeOf fn

  theorem Term.diaCount_pairElim {σ : Signature} {V W₁ W₂ : VarCtx}
      (T₁ T₂ : VarType) (z : VarSymb) (hz : z ∉ VarCtx_to_VarSymbs V)
      (w₁eq : VarCtx.insertBnd2 T₁ T₂ V = W₁)
      (w₂eq : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz = W₂) {S : VarType} (t : Term σ W₁ S) :
      Term.diaCount (Term.pairElim T₁ T₂ z hz w₁eq w₂eq t) = Term.diaCount t := by
    match t with
    | .unit => rfl
    | .var ⟨w, hw⟩ =>
        rw [Term.pairElim]
        split_ifs <;> rfl
    | .func f =>
        rw [Term.pairElim]
        simp only [Term.diaCount]
        rw [Func.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq f]
    | .pair t₁ t₂ =>
        rw [Term.pairElim]
        simp only [Term.diaCount]
        rw [Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq t₁,
            Term.diaCount_pairElim T₁ T₂ z hz w₁eq w₂eq t₂]
    | .boxterm _ _ _ => rfl
    | .diaterm _ _ _ _ _ => rfl
    | .pair_elim _ _ _ _ _ _ _ => rfl
  termination_by sizeOf t
end

/-! ## Weakening by a user variable

Weakening is NOT a `CtxBij` (it is not onto), so it needs its own traversal.  This is the
user-variable case — the only one the proof rules ever need, since the variable being added is
always an eigenvariable.  It takes a `UserSymb` directly, so there is no predicate to carry.

⭐The binder arms are trivial here: `VarCtx.nextBnd_insert_isUsr` says a user insert does not move
the canonical slot, so a `pair_elim`'s components are the SAME before and after — no renaming, no
recomputation.  (Weakening by a BOUND slot does move them; that case belongs with the substitution
machinery, which is where it is needed.) -/

mutual
  def Func.ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
      (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {N : ℕ} (fn : Func σ V N) :
      Func σ (VarCtx_insert ⟨u.toVar, T⟩ V hu) N := by
    match fn with
    | .F fs => exact .F fs
    | .eval g t => exact .eval (Func.ctx_extU u T hu g) (Term.ctx_extU u T hu t)
  termination_by (sizeOf T, sizeOf fn)

  def Term.ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
      (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S) :
      Term σ (VarCtx_insert ⟨u.toVar, T⟩ V hu) S := by
    match t with
    | .var ⟨w, hw⟩ => exact .var ⟨w, Finset.mem_insert_of_mem hw⟩
    | .func fn => exact .func (Func.ctx_extU u T hu fn)
    | .unit => exact .unit
    | .pair t1 t2 => exact .pair (Term.ctx_extU u T hu t1) (Term.ctx_extU u T hu t2)
    | .boxterm tt hsub hne =>
        rename_i V_inner S_inner
        have hu_inner : u.toVar ∉ VarCtx_to_VarSymbs V_inner := by
          intro h_in
          apply hu
          obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in
          exact Finset.mem_image.mpr ⟨⟨q.1, q.2.VTypeBox⟩,
            hsub (Finset.mem_image.mpr ⟨q, hq_in, rfl⟩), hq_eq⟩
        match h_T : T with
        | .VTypeBox U' =>
            -- Box-typed: the inner context gains `⟨u, U'⟩`; recurse into `tt` at the SMALLER type.
            subst h_T
            refine .boxterm (Term.ctx_extU u U' hu_inner tt) ?_ ?_
            · rw [VarCtx_box_fst_insert]
              intro p hp
              rcases Finset.mem_insert.mp hp with rfl | hp_box
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hsub hp_box)
            · intro p hp h_box
              rw [VarCtx_box_fst_insert]
              rcases Finset.mem_insert.mp hp with rfl | hp_V
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hne p hp_V h_box)
        | .VTypeProd a b =>
            -- ⭐Pair-typed: weaken by the two COMPONENTS under fresh USER names, rename each to
            -- its canonical slot, then re-pair.  v10 needs `Term.boundVars` in its avoid set here;
            -- capture is impossible in v11, so the CONTEXT alone suffices.
            subst h_T
            have hw1 : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar ∉ VarCtx_to_VarSymbs V :=
              UserSymb.fresh_not_mem _
            have hw2 : (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))).toVar
                ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd a V) := UserSymb.fresh_not_mem _
            exact Term.pairElim a b u.toVar hu rfl rfl
              (Term.rename' _ (VarCtx.insertBnd a V).nextBnd b hw2 (VarCtx.nextBnd_not_mem _)
                (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))) b hw2
                  (Term.rename' _ V.nextBnd a hw1 (VarCtx.nextBnd_not_mem V)
                    (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) a hw1
                      (.boxterm tt hsub hne)))))
        | .Var | .VTypeOne | .VTypeDia _ =>
            -- Not box-typed and not a pair: the inner context is untouched, and the added entry
            -- cannot be box-typed, so `h_no_box_extras` transfers unchanged.
            all_goals
              subst h_T
              refine .boxterm tt (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
              intro p hp h_box
              rcases Finset.mem_insert.mp hp with rfl | hp_V
              · simp [VarType.isBox] at h_box
              · exact hne p hp_V h_box
    | .diaterm x hx inner hsub hne =>
        rename_i V_inner S_inner
        have hu_inner : u.toVar ∉ VarCtx_to_VarSymbs V_inner := by
          intro h_in
          apply hu
          obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in
          refine Finset.mem_image.mpr ⟨⟨q.1, q.2.VTypeBox⟩, hsub ?_, hq_eq⟩
          rw [VarCtx_dia_fst]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, hq_in, rfl⟩)
        -- The witness `x` is FREE in `V` (as `⟨x.1, ◇x.2⟩`), so it differs from the new variable.
        have hu_ne_x : u.toVar ≠ x.1 := by
          intro h_eq
          apply hu
          refine Finset.mem_image.mpr ⟨⟨x.1, x.2.VTypeDia⟩, hsub ?_, h_eq.symm⟩
          rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        have hu_outer : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert x V_inner hx) :=
          not_mem_VarSymbs_insert hu_ne_x hu_inner
        match h_T : T with
        | .VTypeBox U' =>
            -- Recurse into the inner term, then swap the inserts so the ◇-witness stays outermost.
            subst h_T
            have hx_ext : x.1 ∉ VarCtx_to_VarSymbs
                (VarCtx_insert ⟨u.toVar, U'⟩ V_inner hu_inner) :=
              not_mem_VarSymbs_insert (Ne.symm hu_ne_x) hx
            have h_swap : VarCtx_insert ⟨u.toVar, U'⟩ (VarCtx_insert x V_inner hx) hu_outer
                = VarCtx_insert x (VarCtx_insert ⟨u.toVar, U'⟩ V_inner hu_inner) hx_ext :=
              VarCtx_insert_comm hu_outer hx_ext
            refine .diaterm x hx_ext
              (h_swap ▸ Term.ctx_extU u U' hu_outer inner) ?_ ?_
            · rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
              intro p hp
              rcases Finset.mem_insert.mp hp with rfl | hp1
              · refine Finset.mem_insert_of_mem (hsub ?_)
                rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
              · rcases Finset.mem_insert.mp hp1 with rfl | hp_box
                · exact Finset.mem_insert_self _ _
                · refine Finset.mem_insert_of_mem (hsub ?_)
                  rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_box
            · intro p hp h_box
              rw [VarCtx_dia_fst, VarCtx_box_fst_insert]
              rcases Finset.mem_insert.mp hp with rfl | hp_V
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              · have := hne p hp_V h_box
                rw [VarCtx_dia_fst] at this
                rcases Finset.mem_insert.mp this with rfl | hp_box
                · exact Finset.mem_insert_self _ _
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp_box)
        | .VTypeProd a b =>
            -- Same peel as `boxterm`: weaken by the two components under fresh USER names,
            -- rename each to its canonical slot, then re-pair.
            subst h_T
            have hw1 : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar ∉ VarCtx_to_VarSymbs V :=
              UserSymb.fresh_not_mem _
            have hw2 : (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))).toVar
                ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd a V) := UserSymb.fresh_not_mem _
            exact Term.pairElim a b u.toVar hu rfl rfl
              (Term.rename' _ (VarCtx.insertBnd a V).nextBnd b hw2 (VarCtx.nextBnd_not_mem _)
                (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs (VarCtx.insertBnd a V))) b hw2
                  (Term.rename' _ V.nextBnd a hw1 (VarCtx.nextBnd_not_mem V)
                    (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) a hw1
                      (.diaterm x hx inner hsub hne)))))
        | .Var | .VTypeOne | .VTypeDia _ =>
            all_goals
              subst h_T
              refine .diaterm x hx inner (fun p hp => Finset.mem_insert_of_mem (hsub hp)) ?_
              intro p hp h_box
              rcases Finset.mem_insert.mp hp with rfl | hp_V
              · simp [VarType.isBox] at h_box
              · exact hne p hp_V h_box
    | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
        rename_i pe_V pe_W₁
        subst w₂eq
        have hu_pe : u.toVar ∉ VarCtx_to_VarSymbs pe_V := by
          intro hm
          exact hu (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem hm)
        have hz_ne : z ≠ u.toVar := by
          intro h
          refine hu ?_
          rw [VarCtx_to_VarSymbs_insert, ← h]
          exact Finset.mem_insert_self _ _
        have hz' : z ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe) :=
          not_mem_VarSymbs_insert hz_ne hz
        have hu_bnd2 : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd2 T₁ T₂ pe_V) :=
          VarCtx.notMem_insertBnd_of_isUsr rfl T₂
            (VarCtx.notMem_insertBnd_of_isUsr rfl T₁ hu_pe)
        have hu_W₁ : u.toVar ∉ VarCtx_to_VarSymbs pe_W₁ := w₁eq ▸ hu_bnd2
        -- ⭐The slots do not move: a user insert leaves `nextBnd` alone, so the rebuilt node's
        -- components are literally the same ones.  Target the BODY's context so `body` is passed
        -- untouched (transporting it would break the `sizeOf` relation termination needs).
        have w₁eq' : VarCtx.insertBnd2 T₁ T₂ (VarCtx_insert ⟨u.toVar, T⟩ pe_V hu_pe)
            = VarCtx_insert ⟨u.toVar, T⟩ pe_W₁ hu_W₁ := by
          rw [VarCtx.insertBnd2_comm_insert ⟨u.toVar, T⟩ pe_V hu_pe rfl T₁ T₂ hu_bnd2]
          apply VarCtx_ext
          change insert (⟨u.toVar, T⟩ : VarSymb × VarType) (VarCtx.insertBnd2 T₁ T₂ pe_V).1
               = insert (⟨u.toVar, T⟩ : VarSymb × VarType) pe_W₁.1
          rw [w₁eq]
        exact .pair_elim T₁ T₂ z hz' w₁eq'
          (VarCtx_insert_comm hz' (not_mem_VarSymbs_insert (Ne.symm hz_ne) hu_pe))
          (Term.ctx_extU u T hu_W₁ body)
  termination_by (sizeOf T, sizeOf t)
end

/-! ## Cast invariance of the measures (ported from v10) -/

-- Term.numNodes is invariant under VarCtx-equality casts.
lemma Term.numNodes_ctx_cast {σ : Signature} {V V' : VarCtx} {S : VarType}
    (h : V = V') (t : Term σ V S) :
    Term.numNodes (h ▸ t) = Term.numNodes t := by
  cases h; rfl

-- Term.sizeOf is invariant under VarCtx-equality casts.
lemma Term.sizeOf_ctx_cast {σ : Signature} {V V' : VarCtx} {S : VarType}
    (h : V = V') (t : Term σ V S) :
    sizeOf (h ▸ t) = sizeOf t := by
  cases h; rfl

-- Term.diaCount is invariant under VarCtx-equality casts.
lemma Term.diaCount_ctx_cast {σ : Signature} {V V' : VarCtx} {S : VarType}
    (h : V = V') (t : Term σ V S) :
    Term.diaCount (h ▸ t) = Term.diaCount t := by
  cases h; rfl

-- Func.diaCount is invariant under VarCtx-equality casts.
lemma Func.diaCount_ctx_cast {σ : Signature} {V V' : VarCtx} {N : ℕ}
    (h : V = V') (f : Func σ V N) :
    Func.diaCount (h ▸ f) = Func.diaCount f := by
  cases h; rfl
/-! ## Weakening by an ARBITRARY symbol, and its `diaCount` invariance

`ctx_extU` only covers user symbols, because inserting one leaves `nextBnd` alone.  Weakening by a
BOUND slot does move the canonical slots — but that is exactly what `mapCtx` recomputes, so the
general case is `ctx_extU` under a fresh user name followed by `rename'` onto the wanted symbol.

The `diaCount` invariance is what the modal-β arm of `substCore` needs: there the recursion target
is a LIFTED subterm, so `sizeOf` is no help and the measure counts `◇`-nodes instead. -/

/-- `rename'` preserves `diaCount` (it is `mapCtx`). -/
theorem Term.diaCount_rename' {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    {S : VarType} (t : Term σ (VarCtx_insert ⟨old, T⟩ V hold) S) :
    Term.diaCount (Term.rename' old new T hold hnew t) = Term.diaCount t :=
  Term.diaCount_mapCtx _ t

mutual
  theorem Func.diaCount_ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
      (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {N : ℕ} (fn : Func σ V N) :
      Func.diaCount (Func.ctx_extU u T hu fn) = Func.diaCount fn := by
    match fn with
    | .F _ => rw [Func.ctx_extU]; rfl
    | .eval g t =>
        rw [Func.ctx_extU]
        simp only [Func.diaCount]
        rw [Func.diaCount_ctx_extU u T hu g, Term.diaCount_ctx_extU u T hu t]
  termination_by (sizeOf T, sizeOf fn)

  theorem Term.diaCount_ctx_extU {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
      (hu : u.toVar ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S) :
      Term.diaCount (Term.ctx_extU u T hu t) = Term.diaCount t := by
    match t with
    | .var _ => rw [Term.ctx_extU]; rfl
    | .unit => rw [Term.ctx_extU]; rfl
    | .func fn =>
        rw [Term.ctx_extU]
        simp only [Term.diaCount]
        rw [Func.diaCount_ctx_extU u T hu fn]
    | .pair t1 t2 =>
        rw [Term.ctx_extU]
        simp only [Term.diaCount]
        rw [Term.diaCount_ctx_extU u T hu t1, Term.diaCount_ctx_extU u T hu t2]
    | .boxterm tt hsub hne =>
        match h_T : T with
        | .VTypeBox U' =>
            subst h_T
            rw [Term.ctx_extU]
            simp only [Term.diaCount]
            rw [Term.diaCount_ctx_extU u U' _ tt]
        | .VTypeProd a b =>
            subst h_T
            rw [Term.ctx_extU, Term.diaCount_pairElim, Term.diaCount_rename',
                Term.diaCount_ctx_extU _ b, Term.diaCount_rename',
                Term.diaCount_ctx_extU _ a]
        | .Var => subst h_T; rw [Term.ctx_extU]; rfl
        | .VTypeOne => subst h_T; rw [Term.ctx_extU]; rfl
        | .VTypeDia _ => subst h_T; rw [Term.ctx_extU]; rfl
    | .diaterm xv hxv inner hsub hne =>
        match h_T : T with
        | .VTypeBox U' =>
            subst h_T
            rw [Term.ctx_extU]
            simp only [Term.diaCount]
            rw [Term.diaCount_ctx_cast, Term.diaCount_ctx_extU u U' _ inner]
        | .VTypeProd a b =>
            subst h_T
            rw [Term.ctx_extU, Term.diaCount_pairElim, Term.diaCount_rename',
                Term.diaCount_ctx_extU _ b, Term.diaCount_rename',
                Term.diaCount_ctx_extU _ a]
        | .Var => subst h_T; rw [Term.ctx_extU]; rfl
        | .VTypeOne => subst h_T; rw [Term.ctx_extU]; rfl
        | .VTypeDia _ => subst h_T; rw [Term.ctx_extU]; rfl
    | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
        rename_i pe_V pe_W₁
        subst w₂eq
        rw [Term.ctx_extU]
        simp only [Term.diaCount]
        rw [Term.diaCount_ctx_extU u T _ body]
  termination_by (sizeOf T, sizeOf t)
end

/-- Weakening by an ARBITRARY symbol: weaken under a fresh user name, then rename onto `v`.
    `mapCtx` recomputes the canonical slots, so this is correct even when `v` is a slot. -/
def Term.ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S) :
    Term σ (VarCtx_insert xv V hv) S :=
  Term.rename' (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar xv.1 xv.2
    (UserSymb.fresh_not_mem _) hv
    (Term.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) xv.2 (UserSymb.fresh_not_mem _) t)

theorem Term.diaCount_ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S) :
    Term.diaCount (Term.ctx_ext xv hv t) = Term.diaCount t := by
  rw [Term.ctx_ext, Term.diaCount_rename', Term.diaCount_ctx_extU]


-- Bound-vars preservation for renaming: every binder of `Term.rename ... t` is

/-! ## Unpairing

`unpair` is the INVERSE of `pairElim`: it moves a term from the JOINED context `V + ⟨z, T₁×T₂⟩` to
the SPLIT one `insertBnd2 T₁ T₂ V`.  `substVar` uses it to remove a pair variable from the context
before the structural pass runs.

Two things make it work in v11:

* **`z` is never a `.var`.**  `.var` is `Var`-typed only, so a pair-typed symbol can occur in a term
  ONLY as a `pair_elim` binder.  Unpairing therefore deletes exactly those nodes and touches
  nothing else — there is no term-level replacement to perform.
* **`z` is required to be USER-named** (`hzu`).  A user insert does not move `nextBnd`, which is
  what lets the nested node's slots be recomputed.  Call sites α-rename first — free, since
  `rename'` is `mapCtx`.

The modal arms pass straight through.  If either component were box-typed then `⟨z, T₁×T₂⟩` would
itself be box-DETECTED (`isBox` recurses through `VTypeProd`), and `h_no_box_extras` would place a
`VTypeProd`-headed entry inside a `VarCtx_box` image — impossible.  So neither new slot is
box-typed either, and the "no extras" condition transfers unchanged. -/

/-- Membership in a base context transfers to the split one. -/
theorem VarCtx.mem_insertBnd2_of_mem {V : VarCtx} {T₁ T₂ : VarType} {p : VarSymb × VarType}
    (hp : p ∈ V.1) : p ∈ (VarCtx.insertBnd2 T₁ T₂ V).1 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp)

/-- Case analysis on the split context: the two new slots, or an original entry. -/
theorem VarCtx.mem_insertBnd2 {V : VarCtx} {T₁ T₂ : VarType} {p : VarSymb × VarType}
    (hp : p ∈ (VarCtx.insertBnd2 T₁ T₂ V).1) :
    p = (⟨VarSymb.bnd (VarCtx.bndLevel V + 1), T₂⟩ : VarSymb × VarType)
      ∨ p = (⟨VarSymb.bnd (VarCtx.bndLevel V), T₁⟩ : VarSymb × VarType) ∨ p ∈ V.1 := by
  rw [VarCtx.insertBnd2_fst] at hp
  rcases Finset.mem_insert.mp hp with h | h1
  · exact Or.inl h
  · rcases Finset.mem_insert.mp h1 with h | h2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h2)

mutual
  def Func.unpair {σ : Signature} {V : VarCtx} (T₁ T₂ : VarType) (z : VarSymb)
      (hzu : z.isUsr = true) (hz : z ∉ VarCtx_to_VarSymbs V) {N : ℕ}
      (fn : Func σ (VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz) N) :
      Func σ (VarCtx.insertBnd2 T₁ T₂ V) N := by
    match fn with
    | .F fs => exact .F fs
    | .eval g t =>
        exact .eval (Func.unpair T₁ T₂ z hzu hz g) (Term.unpair T₁ T₂ z hzu hz t)
  termination_by sizeOf fn

  def Term.unpair {σ : Signature} {V : VarCtx} (T₁ T₂ : VarType) (z : VarSymb)
      (hzu : z.isUsr = true) (hz : z ∉ VarCtx_to_VarSymbs V) {S : VarType}
      (t : Term σ (VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz) S) :
      Term σ (VarCtx.insertBnd2 T₁ T₂ V) S := by
    match t with
    | .unit => exact .unit
    | .var ⟨w, hw⟩ =>
        refine .var ⟨w, VarCtx.mem_insertBnd2_of_mem ?_⟩
        rcases Finset.mem_insert.mp hw with h_eq | hw_V
        · exact VarType.noConfusion (Prod.mk.inj h_eq).2
        · exact hw_V
    | .func fn => exact .func (Func.unpair T₁ T₂ z hzu hz fn)
    | .pair t1 t2 =>
        exact .pair (Term.unpair T₁ T₂ z hzu hz t1) (Term.unpair T₁ T₂ z hzu hz t2)
    | .boxterm inner hsub hne =>
        rename_i V_inner S_inner
        have hnb : ¬ ((VarType.VTypeProd T₁ T₂).isBox = true) := by
          intro hbox
          obtain ⟨q, _, hqeq⟩ := Finset.mem_image.mp
            (hne ⟨z, .VTypeProd T₁ T₂⟩ (Finset.mem_insert_self _ _) hbox)
          exact VarType.noConfusion (Prod.mk.inj hqeq).2
        have h1 : ¬ (T₁.isBox = true) := fun h => hnb (by simp [VarType.isBox, h])
        have h2 : ¬ (T₂.isBox = true) := fun h => hnb (by simp [VarType.isBox, h])
        refine .boxterm inner ?_ ?_
        · intro p hp
          rcases Finset.mem_insert.mp (hsub hp) with h_eq | hp_V
          · exfalso
            subst h_eq
            obtain ⟨q, _, hqeq⟩ := Finset.mem_image.mp hp
            exact VarType.noConfusion (Prod.mk.inj hqeq).2
          · exact VarCtx.mem_insertBnd2_of_mem hp_V
        · intro p hp h_box
          rcases VarCtx.mem_insertBnd2 hp with rfl | rfl | hp_V
          · exact absurd h_box h2
          · exact absurd h_box h1
          · exact hne p (Finset.mem_insert_of_mem hp_V) h_box
    | .diaterm xv hxv inner hsub hne =>
        rename_i V_inner S_inner
        have hnb : ¬ ((VarType.VTypeProd T₁ T₂).isBox = true) := by
          intro hbox
          have hin := hne ⟨z, .VTypeProd T₁ T₂⟩ (Finset.mem_insert_self _ _) hbox
          rw [VarCtx_dia_fst] at hin
          rcases Finset.mem_insert.mp hin with h_eq | h_box
          · exact VarType.noConfusion (Prod.mk.inj h_eq).2
          · obtain ⟨q, _, hqeq⟩ := Finset.mem_image.mp h_box
            exact VarType.noConfusion (Prod.mk.inj hqeq).2
        have h1 : ¬ (T₁.isBox = true) := fun h => hnb (by simp [VarType.isBox, h])
        have h2 : ¬ (T₂.isBox = true) := fun h => hnb (by simp [VarType.isBox, h])
        refine .diaterm xv hxv inner ?_ ?_
        · intro p hp
          rcases Finset.mem_insert.mp (hsub hp) with h_eq | hp_V
          · exfalso
            subst h_eq
            rw [VarCtx_dia_fst] at hp
            rcases Finset.mem_insert.mp hp with h_eq' | h_box
            · exact VarType.noConfusion (Prod.mk.inj h_eq').2
            · obtain ⟨q, _, hqeq⟩ := Finset.mem_image.mp h_box
              exact VarType.noConfusion (Prod.mk.inj hqeq).2
          · exact VarCtx.mem_insertBnd2_of_mem hp_V
        · intro p hp h_box
          rcases VarCtx.mem_insertBnd2 hp with rfl | rfl | hp_V
          · exact absurd h_box h2
          · exact absurd h_box h1
          · exact hne p (Finset.mem_insert_of_mem hp_V) h_box
    | .pair_elim T₁' T₂' z' hz' w₁eq w₂eq body =>
        rename_i pe_V pe_W₁
        by_cases hzz : z' = z
        · -- ⭐The node eliminates exactly the variable being unpaired: its body ALREADY lives in
          -- the split context, so the node simply disappears.
          subst hzz
          have hmem' : (⟨z', T₁'.VTypeProd T₂'⟩ : VarSymb × VarType)
              ∈ (VarCtx_insert ⟨z', .VTypeProd T₁ T₂⟩ V hz).1 := by
            rw [← w₂eq]; exact Finset.mem_insert_self _ _
          have hTeq : (T₁'.VTypeProd T₂') = VarType.VTypeProd T₁ T₂ :=
            (VarCtx_insert ⟨z', .VTypeProd T₁ T₂⟩ V hz).2
              ⟨z', T₁'.VTypeProd T₂'⟩ hmem'
              ⟨z', .VTypeProd T₁ T₂⟩ (Finset.mem_insert_self _ _) rfl
          have hT₁ : T₁' = T₁ := (VarType.VTypeProd.inj hTeq).1
          have hT₂ : T₂' = T₂ := (VarType.VTypeProd.inj hTeq).2
          subst hT₁; subst hT₂
          have hpe_not : (⟨z', VarType.VTypeProd T₁' T₂'⟩ : VarSymb × VarType) ∉ pe_V.1 :=
            fun h => hz' (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          have hV_not : (⟨z', VarType.VTypeProd T₁' T₂'⟩ : VarSymb × VarType) ∉ V.1 :=
            fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          have hpeV : pe_V = V := by
            refine VarCtx_ext _ _ ?_
            have h : insert (⟨z', VarType.VTypeProd T₁' T₂'⟩ : VarSymb × VarType) pe_V.1
                = insert (⟨z', VarType.VTypeProd T₁' T₂'⟩ : VarSymb × VarType) V.1 :=
              congrArg (fun (W : VarCtx) => W.1) w₂eq
            have h1 := congrArg
              (fun (s : Finset (VarSymb × VarType)) =>
                s.erase (⟨z', VarType.VTypeProd T₁' T₂'⟩ : VarSymb × VarType)) h
            simp only at h1
            rwa [Finset.erase_insert hpe_not, Finset.erase_insert hV_not] at h1
          subst hpeV
          exact w₁eq ▸ body
        · -- ⭐The node eliminates a DIFFERENT variable, so `z` sits in its base context.  Unpair
          -- under the binder and rebuild — which needs the four-slot swap, because the two slot
          -- pairs come out in the opposite order (and possibly at a different level).
          have hz_pe : (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∈ pe_V.1 := by
            have hin : (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType)
                ∈ (VarCtx_insert ⟨z', T₁'.VTypeProd T₂'⟩ pe_V hz').1 := by
              rw [w₂eq]; exact Finset.mem_insert_self _ _
            rcases Finset.mem_insert.mp hin with h | h
            · exact absurd (Prod.mk.inj h).1.symm hzz
            · exact h
          have hzU : z ∉ VarCtx_to_VarSymbs (VarCtx_erase pe_V ⟨z, .VTypeProd T₁ T₂⟩) :=
            VarCtx_erase_fresh hz_pe
          have hpeU : VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩
              (VarCtx_erase pe_V ⟨z, .VTypeProd T₁ T₂⟩) hzU = pe_V :=
            VarCtx_insert_erase hz_pe hzU
          have hz'U : z' ∉ VarCtx_to_VarSymbs (VarCtx_erase pe_V ⟨z, .VTypeProd T₁ T₂⟩) :=
            fun h => hz' (VarCtx_to_VarSymbs_erase_subset h)
          have hVU : VarCtx_insert ⟨z', T₁'.VTypeProd T₂'⟩
              (VarCtx_erase pe_V ⟨z, .VTypeProd T₁ T₂⟩) hz'U = V := by
            refine VarCtx_ext _ _ ?_
            have h : insert (⟨z', T₁'.VTypeProd T₂'⟩ : VarSymb × VarType) pe_V.1
                = insert (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) V.1 :=
              congrArg (fun (W : VarCtx) => W.1) w₂eq
            have hne' : (⟨z', T₁'.VTypeProd T₂'⟩ : VarSymb × VarType)
                ≠ (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) :=
              fun hc => hzz (Prod.mk.inj hc).1
            have hV_not : (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∉ V.1 :=
              fun hm => hz (Finset.mem_image.mpr ⟨_, hm, rfl⟩)
            have h1 := congrArg
              (fun (s : Finset (VarSymb × VarType)) =>
                s.erase (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType)) h
            simp only at h1
            rw [Finset.erase_insert_of_ne hne', Finset.erase_insert hV_not] at h1
            exact h1
          have hz_P : z ∉ VarCtx_to_VarSymbs
              (VarCtx.insertBnd2 T₁' T₂' (VarCtx_erase pe_V ⟨z, .VTypeProd T₁ T₂⟩)) :=
            VarCtx.notMem_insertBnd_of_isUsr hzu T₂'
              (VarCtx.notMem_insertBnd_of_isUsr hzu T₁' hzU)
          have hsplit : VarCtx.insertBnd2 T₁' T₂' pe_V
              = VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩
                  (VarCtx.insertBnd2 T₁' T₂' (VarCtx_erase pe_V ⟨z, .VTypeProd T₁ T₂⟩)) hz_P := by
            conv_lhs => rw [← hpeU]
            exact VarCtx.insertBnd2_comm_insert ⟨z, .VTypeProd T₁ T₂⟩ _ hzU hzu T₁' T₂' hz_P
          have hz'_tgt : (⟨z', T₁'.VTypeProd T₂'⟩ : VarSymb × VarType)
              ∈ (VarCtx.insertBnd2 T₁ T₂ V).1 :=
            VarCtx.mem_insertBnd2_of_mem (by rw [← hVU]; exact Finset.mem_insert_self _ _)
          have hbij : CtxBij
              (VarCtx.insertBnd2 T₁ T₂
                (VarCtx.insertBnd2 T₁' T₂' (VarCtx_erase pe_V ⟨z, .VTypeProd T₁ T₂⟩)))
              (VarCtx.insertBnd2 T₁' T₂'
                (VarCtx_erase (VarCtx.insertBnd2 T₁ T₂ V) ⟨z', T₁'.VTypeProd T₂'⟩)) :=
            CtxBij.swap4At _ _ T₁' T₂' T₁ T₂ (VarCtx_erase pe_V ⟨z, .VTypeProd T₁ T₂⟩) _ _
              rfl (VarCtx.unpair_level_le hVU)
              (VarCtx.unpair_srcCtx T₁' T₂' T₁ T₂ _)
              (VarCtx.unpair_tgtCtx T₁' T₂' T₁ T₂ hVU)
          refine .pair_elim T₁' T₂' z' (VarCtx_erase_fresh hz'_tgt) rfl
            (VarCtx_insert_erase hz'_tgt (VarCtx_erase_fresh hz'_tgt)) ?_
          exact Term.mapCtx hbij (Term.unpair T₁ T₂ z hzu hz_P (hsplit ▸ (w₁eq ▸ body)))
  termination_by sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (rw [Term.sizeOf_ctx_cast, Term.sizeOf_ctx_cast]; decreasing_tactic)
end

/-! ## Substitution

`substCore` is the structural pass: it replaces the TOP context entry `⟨x, S⟩` by a term `s`.
It requires the extended context to be pair-free, which makes the `pair_elim` arm unreachable —
a `pair_elim`'s output context holds `⟨z, T₁×ᵥT₂⟩`.  The dispatcher (`substVar`, below) unpairs
first when the context does hold a pair variable.

⭐Note the erasure is always of the TOP entry, so it can never leave a GAP in the slot numbering:
if that entry is a slot it is the highest one, and if it is a user symbol the slots are untouched.
(Gaps would revive the α-equivalence problem — see `VarCtx.bndLevel`.) -/

/-! ### The termination measure

Four components, lexicographically:

1. `pairDepth` of the extended context — strictly drops when `substVar` unpairs.
2. `diaCount` of the term — strictly drops at a `◇`-node, which is what the two interior calls
   need: their recursion target is a LIFTED subterm, so `sizeOf` says nothing about it.
3. `sizeOf` of the term — the ordinary structural component.
4. A TAG separating the two functions: `substVar` (1) may call `substCore` (0) at the same
   context and term.

`lex4_intro` states the order arithmetically; the three wrappers below are the only shapes the
`decreasing_by` blocks actually use. -/

theorem lex4_intro {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (h : a₁ < a₂ ∨ (a₁ = a₂ ∧ (b₁ < b₂ ∨ (b₁ = b₂ ∧ (c₁ < c₂ ∨ (c₁ = c₂ ∧ d₁ < d₂)))))) :
    Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
      (Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
        (Prod.Lex (fun x1 x2 : ℕ => x1 < x2) (fun x1 x2 : ℕ => x1 < x2)))
      (a₁, b₁, c₁, d₁) (a₂, b₂, c₂, d₂) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · refine Prod.Lex.right _ ?_
    rcases h with h | ⟨rfl, h⟩
    · exact Prod.Lex.left _ _ h
    · refine Prod.Lex.right _ ?_
      rcases h with h | ⟨rfl, h⟩
      · exact Prod.Lex.left _ _ h
      · exact Prod.Lex.right _ h

/-- Structural shape: context no bigger, no more `◇`s, strictly smaller term. -/
theorem lex4_le {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hc : c₁ < c₂) :
    Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
      (Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
        (Prod.Lex (fun x1 x2 : ℕ => x1 < x2) (fun x1 x2 : ℕ => x1 < x2)))
      (a₁, b₁, c₁, d₁) (a₂, b₂, c₂, d₂) :=
  lex4_intro (by omega)

/-- Modal shape: context no bigger, strictly fewer `◇`s (the term itself may have grown). -/
theorem lex4_lt {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (ha : a₁ ≤ a₂) (hb : b₁ < b₂) :
    Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
      (Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
        (Prod.Lex (fun x1 x2 : ℕ => x1 < x2) (fun x1 x2 : ℕ => x1 < x2)))
      (a₁, b₁, c₁, d₁) (a₂, b₂, c₂, d₂) :=
  lex4_intro (by omega)

/-- Pair shape: the context strictly loses `pairDepth` (an unpairing step). -/
theorem lex4_pd {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ} (ha : a₁ < a₂) :
    Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
      (Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
        (Prod.Lex (fun x1 x2 : ℕ => x1 < x2) (fun x1 x2 : ℕ => x1 < x2)))
      (a₁, b₁, c₁, d₁) (a₂, b₂, c₂, d₂) :=
  lex4_intro (Or.inl ha)

/-- Dispatch shape: everything equal but the tag (`substVar` handing off to `substCore`). -/
theorem lex4_tag {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hc : c₁ ≤ c₂) (hd : d₁ < d₂) :
    Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
      (Prod.Lex (fun x1 x2 : ℕ => x1 < x2)
        (Prod.Lex (fun x1 x2 : ℕ => x1 < x2) (fun x1 x2 : ℕ => x1 < x2)))
      (a₁, b₁, c₁, d₁) (a₂, b₂, c₂, d₂) :=
  lex4_intro (by omega)

mutual
  def Func.substCore {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
      (hx : x ∉ VarCtx_to_VarSymbs V)
      (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
      (s : Term σ V S) {N : ℕ}
      (fn : Func σ (VarCtx_insert ⟨x, S⟩ V hx) N) : Func σ V N := by
    match fn with
    | .F fs => exact .F fs
    | .eval g t =>
        exact .eval (Func.substCore hx h_pf s g) (Term.substCore hx h_pf s t)
  termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth, Func.diaCount fn, sizeOf fn, 0)
  decreasing_by
    all_goals
      refine lex4_le (le_refl _) ?_ ?_
      · simp only [Func.diaCount]; omega
      · decreasing_tactic

  def Term.substCore {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
      (hx : x ∉ VarCtx_to_VarSymbs V)
      (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
      (s : Term σ V S) {S' : VarType}
      (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S') : Term σ V S' := by
    match t with
    | .var ⟨w, hw⟩ =>
        by_cases h_eq : (⟨w, .Var⟩ : VarSymb × VarType) = ⟨x, S⟩
        · -- the substituted variable itself
          have hS : S = .Var := (Prod.mk.inj h_eq).2.symm
          subst hS
          exact s
        · exact .var ⟨w, (Finset.mem_insert.mp hw).resolve_left h_eq⟩
    | .func fn => exact .func (Func.substCore hx h_pf s fn)
    | .unit => exact .unit
    | .pair t1 t2 =>
        exact .pair (Term.substCore hx h_pf s t1) (Term.substCore hx h_pf s t2)
    | .boxterm tt hsub hne =>
        rename_i V_inner S_inner
        by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
        · -- `x` occurs inside the box, so its ambient type must be a BOX type.
          -- `boxterm_subst_type` discharges the four impossible shapes in one line each
          -- (v10 spends ~10 lines on each).
          cases S with
          | Var =>
              exact absurd (boxterm_subst_type hsub h_x_in)
                (by rintro ⟨T, hT⟩; exact VarType.noConfusion hT)
          | VTypeOne =>
              exact absurd (boxterm_subst_type hsub h_x_in)
                (by rintro ⟨T, hT⟩; exact VarType.noConfusion hT)
          | VTypeDia _ =>
              exact absurd (boxterm_subst_type hsub h_x_in)
                (by rintro ⟨T, hT⟩; exact VarType.noConfusion hT)
          | VTypeProd _ _ =>
              exact absurd (boxterm_subst_type hsub h_x_in)
                (by rintro ⟨T, hT⟩; exact VarType.noConfusion hT)
          | VTypeBox T =>
              by_cases hxT_in : (⟨x, T⟩ : VarSymb × VarType) ∈ V_inner.1
              · match s with
                | .boxterm s_inner s_hsub s_hne =>
                    have hx_minus : x ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨x, T⟩) :=
                      VarCtx_erase_fresh hxT_in
                    have h_V_eq : _ = VarCtx_erase V_inner ⟨x, T⟩ :=
                      ctx_rest_box_V_s_eq hxT_in hsub hne s_hsub s_hne
                    subst h_V_eq
                    exact .boxterm
                      (Term.substVar hx_minus s_inner
                        ((VarCtx_insert_erase hxT_in hx_minus).symm ▸ tt))
                      s_hsub s_hne
                | .pair_elim sT₁ sT₂ sz _ _ sw₂eq _ =>
                    -- Impossible: `s`'s context `V` would hold `⟨sz, sT₁×ᵥsT₂⟩`, but `h_pf` says
                    -- the extended context — hence `V` — is pair-free.
                    exact absurd
                      (Finset.mem_insert_of_mem
                        (by rw [← sw₂eq]; exact Finset.mem_insert_self _ _))
                      (h_pf sz sT₁ sT₂)
              · -- `x` has SOME type in `V_inner`; uniqueness forces it to be `T`.
                exfalso
                obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
                simp only at hx'_eq; subst hx'_eq
                have hbox : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType) ∈ (VarCtx_box V_inner).1 :=
                  Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
                rcases Finset.mem_insert.mp (hsub hbox) with h_eq | h_in_V
                · exact hxT_in (VarType.VTypeBox.inj (Prod.mk.inj h_eq).2 ▸ hx'T')
                · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
        · -- `x` does not occur inside the box: pass straight through.
          refine .boxterm tt ?_ (fun p hp h_box => hne p (Finset.mem_insert_of_mem hp) h_box)
          intro p hp
          rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
          · exfalso
            subst h_eq
            rcases Finset.mem_image.mp hp with ⟨w, hw, hweq⟩
            exact h_x_in (Finset.mem_image.mpr ⟨w, hw, (Prod.mk.inj hweq).1⟩)
          · exact h_V
    | .diaterm xv hxv tt hsub hne =>
        rename_i V_inner S_inner
        by_cases h_xv_eq_x : xv.1 = x
        · -- ⭐Case 3 — MODAL β.  The ◇-witness IS the substituted variable, so `s` must itself be a
          -- `◇`-term, and substitution reduces the redex.
          have hxv_in_Vext : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈
              (VarCtx_insert ⟨x, S⟩ V hx).1 := by
            apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
          have h_S_eq : S = xv.2.VTypeDia := by
            rcases Finset.mem_insert.mp hxv_in_Vext with h_eq | h_in_V
            · exact ((Prod.mk.inj h_eq).2).symm
            · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, h_xv_eq_x⟩) hx
          match (h_S_eq ▸ s : Term σ V xv.2.VTypeDia) with
          | @Term.diaterm _ V_inner_s _ _ xv_s hxv_s tt_s hsub_s hne_s =>
              -- The two ◇-nodes see the SAME box-context: `⟨x, ◇xv.2⟩` is not box-typed, so it
              -- contributes nothing, and `VarCtx_box` is injective.
              have h_V_inner_eq : V_inner_s = V_inner := by
                refine VarCtx_box_inj (VarCtx_ext _ _ (Finset.ext (fun p => ⟨?_, ?_⟩)))
                · intro hp_s
                  have hp_box : VarType.isBox p.2 = true := by
                    rcases Finset.mem_image.mp hp_s with ⟨q, _, hq_eq⟩
                    rw [← hq_eq]; simp [VarType.isBox]
                  have hp_V : p ∈ V.1 := by
                    apply hsub_s; rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_s
                  have hp_dia := hne p (Finset.mem_insert_of_mem hp_V) hp_box
                  rw [VarCtx_dia_fst] at hp_dia
                  rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
                  · subst h_eq; simp [VarType.isBox] at hp_box
                  · exact h_in_box
                · intro hp
                  have hp_box : VarType.isBox p.2 = true := by
                    rcases Finset.mem_image.mp hp with ⟨q, _, hq_eq⟩
                    rw [← hq_eq]; simp [VarType.isBox]
                  have hp_Vext : p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1 := by
                    apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp
                  have hp_V : p ∈ V.1 := by
                    rcases Finset.mem_insert.mp hp_Vext with h_eq | h_V
                    · subst h_eq; rw [h_S_eq] at hp_box; simp [VarType.isBox] at hp_box
                    · exact h_V
                  have hp_dia := hne_s p hp_V hp_box
                  rw [VarCtx_dia_fst] at hp_dia
                  rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
                  · subst h_eq; simp [VarType.isBox] at hp_box
                  · exact h_in_box
              cases h_V_inner_eq
              -- `xv_s.1` is free in `V`, so it is not `x`.
              have hxv_s_ne_x : xv_s.1 ≠ x := by
                intro h
                refine hx (Finset.mem_image.mpr ⟨⟨xv_s.1, xv_s.2.VTypeDia⟩, ?_, h⟩)
                apply hsub_s; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
              have hxv_s_outer : xv_s.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv V_inner hxv) :=
                not_mem_VarSymbs_insert (fun h => hxv_s_ne_x (h.trans h_xv_eq_x)) hxv_s
              have hxv_xv_s_outer :
                  xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s) :=
                not_mem_VarSymbs_insert (fun h => hxv_s_ne_x (h ▸ h_xv_eq_x)) hxv
              have h_x_inner : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s) :=
                not_mem_VarSymbs_insert (fun h => hxv_s_ne_x h.symm) (h_xv_eq_x ▸ hxv)
              -- Lift `tt` past the NEW witness, reorder so `x` is outermost, and substitute.
              -- ⭐`ctx_ext` is the general (arbitrary-symbol) weakening: `xv_s.1` may be a slot,
              -- and the `mapCtx` inside it recomputes any binder slots that moved.
              have h_reorder :
                  VarCtx_insert xv_s (VarCtx_insert xv V_inner hxv) hxv_s_outer
                    = VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer :=
                VarCtx_insert_comm hxv_s_outer hxv_xv_s_outer
              have h_reform :
                  VarCtx_insert xv (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer
                    = VarCtx_insert (⟨x, xv.2⟩ : VarSymb × VarType)
                        (VarCtx_insert xv_s V_inner hxv_s) h_x_inner := by
                refine VarCtx_ext _ _ ?_
                change insert xv (VarCtx_insert xv_s V_inner hxv_s).1
                     = insert (⟨x, xv.2⟩ : VarSymb × VarType) (VarCtx_insert xv_s V_inner hxv_s).1
                rw [show xv = (⟨x, xv.2⟩ : VarSymb × VarType) from Prod.ext h_xv_eq_x rfl]
              exact .diaterm xv_s hxv_s
                (Term.substVar h_x_inner tt_s
                  (h_reform ▸ h_reorder ▸ Term.ctx_ext xv_s hxv_s_outer tt))
                hsub_s hne_s
          | .pair_elim sT₁ sT₂ sz _ _ sw₂eq _ =>
              -- Impossible: `s`'s context `V` would hold a pair variable, but `h_pf` says the
              -- extended context — hence `V` — is pair-free.
              exact absurd
                (Finset.mem_insert_of_mem
                  (by rw [← sw₂eq]; exact Finset.mem_insert_self _ _))
                (h_pf sz sT₁ sT₂)
        · by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
          · -- Case 2: the witness differs from `x`, but `x` occurs INSIDE the ◇.  As for `boxterm`,
            -- `x`'s ambient type must then be a BOX type.
            cases S with
            | Var | VTypeOne | VTypeDia _ | VTypeProd _ _ =>
                exfalso
                obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
                simp only at hx'_eq; subst hx'_eq
                have hx'box_in_dia : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType) ∈
                    (VarCtx_dia xv V_inner hxv).1 := by
                  rw [VarCtx_dia_fst]
                  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩)
                rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
                all_goals first
                  | exact VarType.noConfusion (Prod.mk.inj h_eq).2
                  | exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
            | VTypeBox T =>
                by_cases hxT_in : (⟨x, T⟩ : VarSymb × VarType) ∈ V_inner.1
                · have hx_minus : x ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨x, T⟩) :=
                    VarCtx_erase_fresh hxT_in
                  have hxv_minus : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨x, T⟩) :=
                    fun h => hxv (VarCtx_to_VarSymbs_erase_subset h)
                  match s with
                  | .boxterm s_inner s_hsub s_hne =>
                      have h_V_eq : _ = VarCtx_erase V_inner ⟨x, T⟩ :=
                        ctx_rest_dia_V_s_eq hxT_in hsub hne s_hsub s_hne
                      subst h_V_eq
                      have hx_in_outer : x ∉ VarCtx_to_VarSymbs
                          (VarCtx_insert xv (VarCtx_erase V_inner ⟨x, T⟩) hxv_minus) :=
                        not_mem_VarSymbs_insert (fun h => h_xv_eq_x h.symm) hx_minus
                      have h_combined : VarCtx_insert xv V_inner hxv
                          = VarCtx_insert (⟨x, T⟩ : VarSymb × VarType)
                              (VarCtx_insert xv (VarCtx_erase V_inner ⟨x, T⟩) hxv_minus)
                              hx_in_outer := by
                        refine VarCtx_ext _ _ ?_
                        change insert xv V_inner.1
                             = insert (⟨x, T⟩ : VarSymb × VarType)
                                 (insert xv (VarCtx_erase V_inner ⟨x, T⟩).1)
                        rw [Finset.insert_comm]
                        congr 1
                        exact (Finset.insert_erase hxT_in).symm
                      exact .diaterm xv hxv_minus
                        (Term.substVar hx_in_outer
                          (Term.ctx_ext xv hxv_minus s_inner) (h_combined ▸ tt))
                        (ctx_rest_dia_hsub_erase hxv_minus h_xv_eq_x hsub)
                        (ctx_rest_dia_h_no_extras_erase hxv_minus hne)
                  | .pair_elim sT₁ sT₂ sz _ _ sw₂eq _ =>
                      exact absurd
                        (Finset.mem_insert_of_mem
                          (by rw [← sw₂eq]; exact Finset.mem_insert_self _ _))
                        (h_pf sz sT₁ sT₂)
                · -- `x` has SOME type in `V_inner`; uniqueness forces it to be `T`.
                  exfalso
                  obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
                  simp only at hx'_eq; subst hx'_eq
                  have hx'box_in_dia : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType) ∈
                      (VarCtx_dia xv V_inner hxv).1 := by
                    rw [VarCtx_dia_fst]
                    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩)
                  rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
                  · exact hxT_in (VarType.VTypeBox.inj (Prod.mk.inj h_eq).2 ▸ hx'T')
                  · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
          · -- Case 1: neither the witness nor the interior mentions `x` — pass straight through.
            refine .diaterm xv hxv tt ?_
              (fun p hp h_box => hne p (Finset.mem_insert_of_mem hp) h_box)
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
              · exfalso
                subst h_eq
                rcases Finset.mem_image.mp hp_box with ⟨q, hq_in, hq_eq⟩
                exact h_x_in (Finset.mem_image.mpr ⟨q, hq_in, (Prod.mk.inj hq_eq).1⟩)
              · exact h_in_V
    | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
        -- Unreachable: the node's output context holds `⟨z, T₁ ×ᵥ T₂⟩`, contradicting `h_pf`.
        exact absurd
          (show (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∈ _ from by
            rw [← w₂eq]; exact Finset.mem_insert_self _ _)
          (h_pf z T₁ T₂)
  termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth, Term.diaCount t, sizeOf t, 0)
  decreasing_by
    all_goals first
      -- structural: same context, no new `◇`s, smaller term
      | (refine lex4_le (le_refl _) ?_ ?_
         · simp only [Term.diaCount]; omega
         · decreasing_tactic)
      -- interior call at a `boxterm`'s inner context: `pairDepth` cannot grow, `diaCount` is
      -- untouched (a box adds none), and the recursion target is a cast of the subterm.
      | (have hS : S = T.VTypeBox := by assumption
         subst hS
         refine lex4_le ?_ ?_ ?_
         · have h_le := VarCtx.pairDepth_le_of_box_subset hsub
           rw [VarCtx.pairDepth_insert, ← VarCtx_insert_erase hxT_in hx_minus,
               VarCtx.pairDepth_insert ⟨x, T⟩ _ hx_minus] at h_le
           rw [VarCtx.pairDepth_insert, VarCtx.pairDepth_insert]
           exact h_le
         · rw [Term.diaCount_ctx_cast]
           simp only [Term.diaCount]
           omega
         · rw [Term.sizeOf_ctx_cast]
           decreasing_tactic)
      | skip
    -- Two goals remain, in order: `diaterm` Case 3 (modal β), then `diaterm` Case 2.
    · -- ⭐Case 3 (modal β): the recursion target is a LIFTED subterm, so only `diaCount` —
      -- which `ctx_ext` preserves — can see the decrease.
      refine lex4_lt ?_ ?_
      · have h_le := VarCtx.pairDepth_le_of_dia_subset hsub_s
        have hSpd : S.pairDepth = xv.2.pairDepth := by
          simp only [h_S_eq, VarType.pairDepth]
        simp only [VarCtx.pairDepth_insert] at h_le ⊢
        omega
      · rw [Term.diaCount_ctx_cast, Term.diaCount_ctx_cast, Term.diaCount_ctx_ext]
        simp only [Term.diaCount]
        omega
    · -- ⭐Case 2: `pairDepth` cannot grow, and the `◇`-node just consumed makes `diaCount`
      -- STRICTLY smaller — which is the whole reason it is in the measure.
      have hS : S = T.VTypeBox := by assumption
      subst hS
      refine lex4_lt ?_ ?_
      · have h_le := VarCtx.pairDepth_le_of_dia_subset hsub
        have h_V_inner := VarCtx.pairDepth_insert (⟨x, T⟩ : VarSymb × VarType) _ hx_minus
        rw [VarCtx_insert_erase hxT_in hx_minus] at h_V_inner
        simp only [VarCtx.pairDepth_insert, VarType.pairDepth] at h_le h_V_inner ⊢
        omega
      · rw [Term.diaCount_ctx_cast]
        simp only [Term.diaCount]
        omega

  /-- ⭐The dispatcher.  Three cases, keyed on the BASE context `V` rather than the extended one:

      * **B** — `V` holds a pair variable `z`.  Unpair `s` and `t` at `z`, recurse in the split
        context (strictly smaller `pairDepth`), and re-pair with `pairElim`.
      * **A** — `V` is pair-free but `x` ITSELF is pair-typed.  Then `s` cannot be a `pair_elim`
        (that would put a pair variable in `V`), so it is a literal `.pair s₁ s₂`.  Unpair `t` at
        `x` and substitute the two components into the two canonical slots in turn.
      * otherwise the extended context is pair-free and the structural pass applies.

      Both cases α-rename to a fresh USER symbol first: `unpair` needs a user-named binder so that
      a nested node's slots can be recomputed, and `insertBnd2` only commutes past a user insert.
      Renaming is free — `rename'` is `mapCtx`. -/
  def Term.substVar {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
      (hx : x ∉ VarCtx_to_VarSymbs V)
      (s : Term σ V S) {S' : VarType}
      (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S') : Term σ V S' := by
    match h_pv : V.firstPairVar with
    | some ⟨(z, V1, V2), hzmem⟩ =>
        -- ⭐Case B.  `U` is `V` without `z`.
        have hzV : z ∈ VarCtx_to_VarSymbs V := Finset.mem_image.mpr ⟨_, hzmem, rfl⟩
        have hzU : z ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) :=
          VarCtx_erase_fresh hzmem
        have hVU : VarCtx_insert ⟨z, .VTypeProd V1 V2⟩
            (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hzU = V :=
          VarCtx_insert_erase hzmem hzU
        -- `u` renames the substituted variable, `w` the pair variable; both fresh and USER.
        have hu : (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar
            ∉ VarCtx_to_VarSymbs V := fun h =>
          UserSymb.fresh_not_mem _ (Finset.mem_insert_of_mem h)
        have hu_U : (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar
            ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) := fun h =>
          hu (VarCtx_to_VarSymbs_erase_subset h)
        have hw_V : (UserSymb.fresh
            (insert (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar
              (VarCtx_to_VarSymbs V))).toVar ∉ VarCtx_to_VarSymbs V := fun h =>
          UserSymb.fresh_not_mem _ (Finset.mem_insert_of_mem h)
        have hw_ne_u : (UserSymb.fresh
            (insert (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar
              (VarCtx_to_VarSymbs V))).toVar
            ≠ (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar := fun h =>
          UserSymb.fresh_not_mem _ (by rw [h]; exact Finset.mem_insert_self _ _)
        have hw_U : (UserSymb.fresh
            (insert (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar
              (VarCtx_to_VarSymbs V))).toVar
            ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) := fun h =>
          hw_V (VarCtx_to_VarSymbs_erase_subset h)
        have hu_US : (UserSymb.fresh
            (insert (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar
              (VarCtx_to_VarSymbs V))).toVar
            ∉ VarCtx_to_VarSymbs (VarCtx_insert
                ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
                (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hu_U) :=
          not_mem_VarSymbs_insert hw_ne_u hw_U
        have hz_ne_u : z ≠ (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar := by
          intro h
          exact hu (h ▸ hzV)
        have hz_US : z ∉ VarCtx_to_VarSymbs (VarCtx_insert
            ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
            (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hu_U) :=
          not_mem_VarSymbs_insert hz_ne_u hzU
        have hu_bnd : (UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar
            ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd2 V1 V2
                (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩)) :=
          VarCtx.notMem_insertBnd_of_isUsr rfl V2 (VarCtx.notMem_insertBnd_of_isUsr rfl V1 hu_U)
        have hVfst : V.1 = insert (⟨z, VarType.VTypeProd V1 V2⟩ : VarSymb × VarType)
            (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩).1 :=
          (congrArg (fun (W : VarCtx) => W.1) hVU).symm
        -- Move `z` outermost in `t`'s context, so it can be renamed and then unpaired.
        have hcomm : VarCtx_insert
            ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩ V hu
            = VarCtx_insert ⟨z, .VTypeProd V1 V2⟩ (VarCtx_insert
                ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
                (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hu_U) hz_US := by
          refine VarCtx_ext _ _ ?_
          change insert
              (⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩ :
                VarSymb × VarType) V.1
            = insert (⟨z, VarType.VTypeProd V1 V2⟩ : VarSymb × VarType)
                (insert (⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩ :
                  VarSymb × VarType) (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩).1)
          rw [hVfst, Finset.insert_comm]
        -- and the same on the split side.
        have hcomm2 : VarCtx.insertBnd2 V1 V2 (VarCtx_insert
              ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
              (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hu_U)
            = VarCtx_insert ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
                (VarCtx.insertBnd2 V1 V2 (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩)) hu_bnd :=
          VarCtx.insertBnd2_comm_insert _ _ hu_U rfl V1 V2 hu_bnd
        have hdecB : (VarCtx_insert ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
              (VarCtx.insertBnd2 V1 V2 (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩)) hu_bnd).pairDepth
            < (VarCtx_insert ⟨x, S⟩ V hx).pairDepth := by
          have hVd := VarCtx.pairDepth_insert (⟨z, VarType.VTypeProd V1 V2⟩ : VarSymb × VarType)
            (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hzU
          rw [hVU] at hVd
          simp only [VarCtx.insertBnd2, VarCtx.insertBnd, VarCtx.pairDepth_insert,
            VarType.pairDepth] at hVd ⊢
          omega
        have hsEq : Term σ (VarCtx_insert ⟨z, .VTypeProd V1 V2⟩
            (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hzU) S = Term σ V S := by rw [hVU]
        exact Term.pairElim V1 V2 z hzU rfl hVU
          (Term.substVar hu_bnd
            (Term.unpair V1 V2 _ rfl hw_U
              (Term.rename' z _ (.VTypeProd V1 V2) hzU hw_U
                (cast hsEq.symm s)))
            (hcomm2 ▸ Term.unpair V1 V2 _ rfl hu_US
              (Term.rename' z _ (.VTypeProd V1 V2) hz_US hu_US
                (hcomm ▸ Term.rename' x _ S hx hu t))))
    | none =>
        have hVfree : V.PairFree := VarCtx.pairFree_of_firstPairVar_none h_pv
        match hSp : S.isPair with
        | false =>
            -- Not a pair type, so the EXTENDED context is pair-free too.
            exact Term.substCore hx
              (VarCtx.pairFree_insert hx hVfree (fun T₁ T₂ h => by
                subst h; simp [VarType.isPair] at hSp)) s t
        | true =>
            cases S with
            | VTypeProd V1 V2 =>
                -- ⭐Case A.  `s` is a literal pair: a `pair_elim` would need a pair variable in `V`.
                match s with
                | .pair s1 s2 =>
                    have hufresh : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar
                        ∉ VarCtx_to_VarSymbs V := UserSymb.fresh_not_mem _
                    have hdecA1 : (VarCtx_insert ⟨V.nextBnd, V1⟩ V
                          (VarCtx.nextBnd_not_mem V)).pairDepth
                        < (VarCtx_insert ⟨x, VarType.VTypeProd V1 V2⟩ V hx).pairDepth := by
                      simp only [VarCtx.pairDepth_insert, VarType.pairDepth]; omega
                    have hdecA2 : (VarCtx_insert ⟨(VarCtx.insertBnd V1 V).nextBnd, V2⟩
                          (VarCtx.insertBnd V1 V) (VarCtx.nextBnd_not_mem _)).pairDepth
                        < (VarCtx_insert ⟨x, VarType.VTypeProd V1 V2⟩ V hx).pairDepth := by
                      simp only [VarCtx.insertBnd, VarCtx.pairDepth_insert, VarType.pairDepth]
                      omega
                    exact Term.substVar (VarCtx.nextBnd_not_mem V) s1
                      (Term.substVar (VarCtx.nextBnd_not_mem (VarCtx.insertBnd V1 V))
                        (Term.ctx_ext ⟨V.nextBnd, V1⟩ (VarCtx.nextBnd_not_mem V) s2)
                        (Term.unpair V1 V2 _ rfl hufresh
                          (Term.rename' x _ (.VTypeProd V1 V2) hx hufresh t)))
                | .pair_elim sT₁ sT₂ sz _ _ sw₂eq _ =>
                    exact absurd
                      (show (⟨sz, VarType.VTypeProd sT₁ sT₂⟩ : VarSymb × VarType) ∈ V.1 from by
                        rw [← sw₂eq]; exact Finset.mem_insert_self _ _)
                      (hVfree sz sT₁ sT₂)
            | Var => exact absurd hSp (by simp [VarType.isPair])
            | VTypeOne => exact absurd hSp (by simp [VarType.isPair])
            | VTypeBox T => exact absurd hSp (by simp [VarType.isPair])
            | VTypeDia T => exact absurd hSp (by simp [VarType.isPair])
  termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth, Term.diaCount t, sizeOf t, 1)
  decreasing_by
    -- The two shapes: the hand-off to the structural pass keeps everything but the tag, and both
    -- unpairing steps strictly drop `pairDepth` (proved in place, where the names are still bound).
    all_goals (try subst_vars)
    all_goals first
      | exact lex4_tag (le_refl _) (le_refl _) (le_refl _) (by omega)
      | exact lex4_pd (by assumption)
end
