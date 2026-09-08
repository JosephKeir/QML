import QML.QML_v11_Terms

/-!
# QML v11 — Term substitution

The second half of the term layer: everything that CHANGES a context rather than merely renaming
inside one.  Split out from `QML_v11_Terms.lean` because it is where the elaboration cost lives —
the core term file rebuilds in seconds, this one in minutes.

The three operations, in dependency order:

* **`Term.ctx_ext`** — weakening by an ARBITRARY symbol.  `ctx_extU` (previous file) only covers
  USER symbols, because it relies on a user insert leaving `nextBnd` alone; the general case is
  `ctx_extU` under a fresh user name followed by `rename'`, since `mapCtx` recomputes the slots.
* **`Term.unpair`** — the inverse of `pairElim`: `V + ⟨z, T₁×T₂⟩ → insertBnd2 T₁ T₂ V`.
* **`Term.substCore` / `Term.substVar`** — substitution proper.  `substCore` is the structural pass
  and needs a pair-free context; `substVar` is the dispatcher that gets it there by unpairing.

`diaCount` invariance under all of the above lives here too: it is the measure component that the
modal-β arm of `substCore` turns on, since there the recursion target is a LIFTED subterm and
`sizeOf` says nothing about it.
-/

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
