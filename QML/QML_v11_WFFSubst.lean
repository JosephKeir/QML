import QML.QML_v11_WFF

/-!
# QML v11 — WFF substitution

The formula-level mirror of `QML_v11_TermSubst.lean`, and split off for the same reason.  Read that
file first: every construction here has the same shape, with two extra arms (`all` / `ex`) that are
uniformly cheap because the binders are nameless.

* **`WFF.ctx_ext`** — weakening by an ARBITRARY symbol: `ctx_extU` under a fresh user name followed
  by `rename`.
* **`WFF.unpair`** — the inverse of `pairElim`: `V + ⟨z, T₁×T₂⟩ → insertBnd2 T₁ T₂ V`.
* **`WFF.substCore` / `WFF.substVar`** — substitution proper.
-/

/-! ## Splitting a product type at the PROP level

`substVar` needs the two components of a pair-typed `S`, but it must NOT `cases S`: that
re-introduces the formula parameter as a fresh variable and the termination goals then compare
`binderPairDepth` of two unrelated atoms.  These total projections plus a `Prop`-level equation
give the components without touching any data. -/

def VarType.pfst : VarType → VarType
  | .VTypeProd a _ => a
  | T              => T

def VarType.psnd : VarType → VarType
  | .VTypeProd _ b => b
  | T              => T

/-! ## Weakening by an arbitrary symbol -/

/-- Weakening by an ARBITRARY symbol.  `ctx_extU` only covers USER symbols (it relies on a user
    insert leaving `nextBnd` alone); the general case is `ctx_extU` under a fresh user name
    followed by `rename`, since `mapCtx` recomputes the slots. -/
def WFF.ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) :
    WFF σ (VarCtx_insert xv V hv) :=
  WFF.rename (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar xv.1 xv.2
    (UserSymb.fresh_not_mem _) hv
    (WFF.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) xv.2 (UserSymb.fresh_not_mem _) φ)

theorem WFF.diaCount_ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) :
    WFF.diaCount (WFF.ctx_ext xv hv φ) = WFF.diaCount φ := by
  rw [WFF.ctx_ext, WFF.diaCount_rename, WFF.diaCount_ctx_extU]

/-! ## Unpairing

Exactly `Term.unpair`, plus the two quantifier arms.  The same two facts carry it:

* a pair-typed symbol can only occur as a `pair_elim` BINDER, so unpairing deletes precisely those
  nodes and touches nothing else;
* the modal arms pass straight through, because a box-typed component would make `⟨z, T₁×T₂⟩`
  box-DETECTED and `h_no_box_extras` would then force a `VTypeProd`-headed entry into a
  `VarCtx_box` image.

`z` must be USER-named, for the same reason as at term level — and here also so that the binder
slot of a `∀` commutes past it. -/

def WFF.unpair {σ : Signature} {V : VarCtx} (T₁ T₂ : VarType) (z : VarSymb)
    (hzu : z.isUsr = true) (hz : z ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz)) :
    WFF σ (VarCtx.insertBnd2 T₁ T₂ V) := by
  match φ with
  | .atom R  => exact .atom (Rel.unpair T₁ T₂ z hzu hz R)
  | .top     => exact .top
  | .bot     => exact .bot
  | .and φ ψ => exact .and (WFF.unpair T₁ T₂ z hzu hz φ) (WFF.unpair T₁ T₂ z hzu hz ψ)
  | .or φ ψ  => exact .or (WFF.unpair T₁ T₂ z hzu hz φ) (WFF.unpair T₁ T₂ z hzu hz ψ)
  | .imp φ ψ => exact .imp (WFF.unpair T₁ T₂ z hzu hz φ) (WFF.unpair T₁ T₂ z hzu hz ψ)
  | .eq s t  => exact .eq (Term.unpair T₁ T₂ z hzu hz s) (Term.unpair T₁ T₂ z hzu hz t)
  | .all T ψ =>
      -- ⭐The binder slot commutes past the (user-named) pair variable, so the recursion is at
      -- `insertBnd T V`; the result then needs the three-slot rotation undone.
      exact .all T (WFF.mapCtx (CtxBij.quantRotInv T₁ T₂ T V)
        (WFF.unpair T₁ T₂ z hzu (VarCtx.notMem_insertBnd_of_isUsr hzu T hz)
          (VarCtx.insertBnd_comm_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz hzu T
            (VarCtx.notMem_insertBnd_of_isUsr hzu T hz) ▸ ψ)))
  | .ex T ψ =>
      exact .ex T (WFF.mapCtx (CtxBij.quantRotInv T₁ T₂ T V)
        (WFF.unpair T₁ T₂ z hzu (VarCtx.notMem_insertBnd_of_isUsr hzu T hz)
          (VarCtx.insertBnd_comm_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz hzu T
            (VarCtx.notMem_insertBnd_of_isUsr hzu T hz) ▸ ψ)))
  | .box inner hsub hne =>
      rename_i V_inner
      have hnb : ¬ ((VarType.VTypeProd T₁ T₂).isBox = true) := by
        intro hbox
        obtain ⟨q, _, hqeq⟩ := Finset.mem_image.mp
          (hne ⟨z, .VTypeProd T₁ T₂⟩ (Finset.mem_insert_self _ _) hbox)
        exact VarType.noConfusion (Prod.mk.inj hqeq).2
      have h1 : ¬ (T₁.isBox = true) := fun h => hnb (by simp [VarType.isBox, h])
      have h2 : ¬ (T₂.isBox = true) := fun h => hnb (by simp [VarType.isBox, h])
      refine .box inner ?_ ?_
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
  | .dia x hx inner hsub hne =>
      rename_i V_inner
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
      refine .dia x hx inner ?_ ?_
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
      · -- ⭐The node eliminates exactly the variable being unpaired: its body already lives in the
        -- split context, so the node simply disappears.  ⚠️Everything below is done WITHOUT
        -- `subst`, so the branch reduces to a single `▸` and `binderPairDepth_unpair` can mirror
        -- it with one `binderPairDepth_ctx_cast`.
        have hmem' : (⟨z', T₁'.VTypeProd T₂'⟩ : VarSymb × VarType)
            ∈ (VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz).1 := by
          rw [← w₂eq]; exact Finset.mem_insert_self _ _
        have hTeq : (T₁'.VTypeProd T₂') = VarType.VTypeProd T₁ T₂ :=
          (VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz).2
            ⟨z', T₁'.VTypeProd T₂'⟩ hmem'
            ⟨z, .VTypeProd T₁ T₂⟩ (Finset.mem_insert_self _ _) hzz
        have haeq : (⟨z', T₁'.VTypeProd T₂'⟩ : VarSymb × VarType)
            = ⟨z, .VTypeProd T₁ T₂⟩ := Prod.ext hzz hTeq
        have hpe_not : (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∉ pe_V.1 := by
          intro hm
          exact hz' (hzz ▸ Finset.mem_image.mpr
            ⟨(⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType), hm, rfl⟩)
        have hV_not : (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∉ V.1 :=
          fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
        have hpeV : pe_V = V := by
          refine VarCtx_ext _ _ ?_
          have h0 : insert (⟨z', T₁'.VTypeProd T₂'⟩ : VarSymb × VarType) pe_V.1
              = insert (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) V.1 :=
            congrArg (fun (W : VarCtx) => W.1) w₂eq
          rw [haeq] at h0
          have h1 := congrArg
            (fun (s : Finset (VarSymb × VarType)) =>
              s.erase (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType)) h0
          simp only at h1
          rwa [Finset.erase_insert hpe_not, Finset.erase_insert hV_not] at h1
        have hVeq : pe_W₁ = VarCtx.insertBnd2 T₁ T₂ V := by
          rw [← w₁eq, (VarType.VTypeProd.inj hTeq).1, (VarType.VTypeProd.inj hTeq).2, hpeV]
        exact hVeq ▸ body
      · -- ⭐A DIFFERENT variable, so `z` sits in its base context: unpair under the binder and
        -- rebuild along the four-slot swap.
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
        exact WFF.mapCtx hbij (WFF.unpair T₁ T₂ z hzu hz_P (hsplit ▸ (w₁eq ▸ body)))
  termination_by sizeOf φ
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (rw [WFF.sizeOf_ctx_cast]; decreasing_tactic)

theorem WFF.binderPairDepth_ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) :
    WFF.binderPairDepth (WFF.ctx_ext xv hv φ) = WFF.binderPairDepth φ := by
  rw [WFF.ctx_ext, WFF.binderPairDepth_rename, WFF.binderPairDepth_ctx_extU]

/-- ⭐Unpairing does not touch quantifier binders, so it leaves `binderPairDepth` alone.  This is
    what makes `substVar`'s unpairing cases strictly decrease the measure. -/
theorem WFF.binderPairDepth_unpair {σ : Signature} {V : VarCtx} (T₁ T₂ : VarType) (z : VarSymb)
    (hzu : z.isUsr = true) (hz : z ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨z, .VTypeProd T₁ T₂⟩ V hz)) :
    WFF.binderPairDepth (WFF.unpair T₁ T₂ z hzu hz φ) = WFF.binderPairDepth φ := by
  match φ with
  | .atom R => rw [WFF.unpair]; rfl
  | .top => rw [WFF.unpair]; rfl
  | .bot => rw [WFF.unpair]; rfl
  | .and φ ψ =>
      rw [WFF.unpair]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_unpair T₁ T₂ z hzu hz φ,
          WFF.binderPairDepth_unpair T₁ T₂ z hzu hz ψ]
  | .or φ ψ =>
      rw [WFF.unpair]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_unpair T₁ T₂ z hzu hz φ,
          WFF.binderPairDepth_unpair T₁ T₂ z hzu hz ψ]
  | .imp φ ψ =>
      rw [WFF.unpair]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_unpair T₁ T₂ z hzu hz φ,
          WFF.binderPairDepth_unpair T₁ T₂ z hzu hz ψ]
  | .eq s t => rw [WFF.unpair]; rfl
  | .all T ψ =>
      rw [WFF.unpair]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_mapCtx, WFF.binderPairDepth_unpair T₁ T₂ z hzu _ _,
          WFF.binderPairDepth_ctx_cast]
  | .ex T ψ =>
      rw [WFF.unpair]; simp only [WFF.binderPairDepth]
      rw [WFF.binderPairDepth_mapCtx, WFF.binderPairDepth_unpair T₁ T₂ z hzu _ _,
          WFF.binderPairDepth_ctx_cast]
  | .box inner hsub hne => rw [WFF.unpair]; rfl
  | .dia x hx inner hsub hne => rw [WFF.unpair]; rfl
  | .pair_elim T₁' T₂' z' hz' w₁eq w₂eq body =>
      rename_i pe_V pe_W₁
      rw [WFF.unpair]
      split
      · rw [WFF.binderPairDepth_ctx_cast]
        simp only [WFF.binderPairDepth]
      · simp only [WFF.binderPairDepth]
        rw [WFF.binderPairDepth_mapCtx, WFF.binderPairDepth_unpair T₁ T₂ z hzu _ _,
            WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_cast]
  termination_by WFF.numNodes φ
  decreasing_by
    all_goals first
      | (simp only [WFF.numNodes]; omega)
      | (simp only [WFF.numNodes_ctx_cast, WFF.numNodes]; omega)

theorem WFF.numNodes_rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨old, T⟩ V hold)) :
    WFF.numNodes (WFF.rename old new T hold hnew φ) = WFF.numNodes φ :=
  WFF.numNodes_mapCtx _ φ

/-! ## Substitution

The formula-level `substCore` / `substVar` pair.  Two differences from the term level:

* **The result carries a `binderPairDepth` bound.**  `substVar`'s Case A performs two substitutions
  in sequence, and the second one's measure mentions the FIRST one's output — so the recursion only
  terminates if the output's `binderPairDepth` is known not to have grown.  It never does
  (substitution puts TERMS in, and terms have no quantifiers), but that has to be part of the
  definition rather than a lemma about it.  v10 reached the same conclusion.
* **The measure's first component is `pairDepth + binderPairDepth`.**  Descending into `.all T ψ`
  moves `T.pairDepth` out of the formula and into the context, so the sum is invariant while
  `pairDepth` alone grows.  Full measure: `(pairDepth + bpd, diaCount, numNodes, tag)`.

`substCore` additionally requires `x` to be USER-named: it descends under quantifiers, and only a
user insert commutes past a binder slot.  `substVar` α-renames before handing off, which is free. -/

mutual
  def WFF.substCore {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
      (hxu : x.isUsr = true)
      (hx : x ∉ VarCtx_to_VarSymbs V)
      (h_pf : (VarCtx_insert ⟨x, S⟩ V hx).PairFree)
      (s : Term σ V S)
      (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
      { ψ : WFF σ V // WFF.binderPairDepth ψ ≤ WFF.binderPairDepth φ } := by
    match φ with
    | .atom R => exact ⟨.atom (Rel.substCore hx h_pf s R), le_refl _⟩
    | .top => exact ⟨.top, le_refl _⟩
    | .bot => exact ⟨.bot, le_refl _⟩
    | .and φ' ψ' =>
        have a := WFF.substCore hxu hx h_pf s φ'
        have b := WFF.substCore hxu hx h_pf s ψ'
        exact ⟨.and a.val b.val, Nat.add_le_add a.property b.property⟩
    | .or φ' ψ' =>
        have a := WFF.substCore hxu hx h_pf s φ'
        have b := WFF.substCore hxu hx h_pf s ψ'
        exact ⟨.or a.val b.val, Nat.add_le_add a.property b.property⟩
    | .imp φ' ψ' =>
        have a := WFF.substCore hxu hx h_pf s φ'
        have b := WFF.substCore hxu hx h_pf s ψ'
        exact ⟨.imp a.val b.val, Nat.add_le_add a.property b.property⟩
    | .eq s' t' =>
        exact ⟨.eq (Term.substCore hx h_pf s s') (Term.substCore hx h_pf s t'), le_refl _⟩
    | .all T ψ =>
        -- ⭐The binder slot commutes past the (user-named) `x`, so the recursion is at
        -- `insertBnd T V` and the measure's first component is UNCHANGED.
        have hx_bnd : x ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T V) :=
          VarCtx.notMem_insertBnd_of_isUsr hxu T hx
        have hcomm : VarCtx.insertBnd T (VarCtx_insert ⟨x, S⟩ V hx)
            = VarCtx_insert ⟨x, S⟩ (VarCtx.insertBnd T V) hx_bnd :=
          VarCtx.insertBnd_comm_insert ⟨x, S⟩ V hx hxu T hx_bnd
        have r := WFF.substVar hx_bnd
          (Term.ctx_ext ⟨V.nextBnd, T⟩ (VarCtx.nextBnd_not_mem V) s) (hcomm ▸ ψ)
        refine ⟨.all T r.val, ?_⟩
        simp only [WFF.binderPairDepth]
        have hb : WFF.binderPairDepth r.val ≤ WFF.binderPairDepth ψ :=
          le_trans r.property (le_of_eq (WFF.binderPairDepth_ctx_cast hcomm ψ))
        omega
    | .ex T ψ =>
        have hx_bnd : x ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T V) :=
          VarCtx.notMem_insertBnd_of_isUsr hxu T hx
        have hcomm : VarCtx.insertBnd T (VarCtx_insert ⟨x, S⟩ V hx)
            = VarCtx_insert ⟨x, S⟩ (VarCtx.insertBnd T V) hx_bnd :=
          VarCtx.insertBnd_comm_insert ⟨x, S⟩ V hx hxu T hx_bnd
        have r := WFF.substVar hx_bnd
          (Term.ctx_ext ⟨V.nextBnd, T⟩ (VarCtx.nextBnd_not_mem V) s) (hcomm ▸ ψ)
        refine ⟨.ex T r.val, ?_⟩
        simp only [WFF.binderPairDepth]
        have hb : WFF.binderPairDepth r.val ≤ WFF.binderPairDepth ψ :=
          le_trans r.property (le_of_eq (WFF.binderPairDepth_ctx_cast hcomm ψ))
        omega
    | .box inner hsub hne =>
        rename_i V_inner
        by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
        · cases S with
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
                      substCore_box_V_s_eq hxT_in hsub hne s_hsub s_hne
                    subst h_V_eq
                    have r := WFF.substVar hx_minus s_inner
                      ((VarCtx_insert_erase hxT_in hx_minus).symm ▸ inner)
                    refine ⟨.box r.val s_hsub s_hne, ?_⟩
                    simp only [WFF.binderPairDepth]
                    exact le_trans r.property
                      (le_of_eq (WFF.binderPairDepth_ctx_cast _ inner))
                | .pair_elim sT₁ sT₂ sz _ _ sw₂eq _ =>
                    exact absurd
                      (Finset.mem_insert_of_mem
                        (by rw [← sw₂eq]; exact Finset.mem_insert_self _ _))
                      (h_pf sz sT₁ sT₂)
              · exfalso
                obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
                simp only at hx'_eq; subst hx'_eq
                have hbox : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType) ∈ (VarCtx_box V_inner).1 :=
                  Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩
                rcases Finset.mem_insert.mp (hsub hbox) with h_eq | h_in_V
                · exact hxT_in (VarType.VTypeBox.inj (Prod.mk.inj h_eq).2 ▸ hx'T')
                · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
        · refine ⟨.box inner ?_ (fun p hp h_box => hne p (Finset.mem_insert_of_mem hp) h_box),
            ?_⟩
          · intro p hp
            rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
            · exfalso
              subst h_eq
              rcases Finset.mem_image.mp hp with ⟨w, hw, hweq⟩
              exact h_x_in (Finset.mem_image.mpr ⟨w, hw, (Prod.mk.inj hweq).1⟩)
            · exact h_V
          · exact le_refl _
    | .dia xv hxv inner hsub hne =>
        rename_i V_inner
        by_cases h_xv_eq_x : xv.1 = x
        · -- ⭐MODAL β.
          have hxv_in_Vext : (⟨xv.1, xv.2.VTypeDia⟩ : VarSymb × VarType) ∈
              (VarCtx_insert ⟨x, S⟩ V hx).1 := by
            apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
          have h_S_eq : S = xv.2.VTypeDia := by
            rcases Finset.mem_insert.mp hxv_in_Vext with h_eq | h_in_V
            · exact ((Prod.mk.inj h_eq).2).symm
            · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, h_xv_eq_x⟩) hx
          match (h_S_eq ▸ s : Term σ V xv.2.VTypeDia) with
          | @Term.diaterm _ V_inner_s _ _ xv_s hxv_s tt_s hsub_s hne_s =>
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
              have r := WFF.substVar h_x_inner tt_s
                (h_reform ▸ h_reorder ▸ WFF.ctx_ext xv_s hxv_s_outer inner)
              have hb : WFF.binderPairDepth
                  (h_reform ▸ h_reorder ▸ WFF.ctx_ext xv_s hxv_s_outer inner)
                  = WFF.binderPairDepth inner := by
                rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_cast,
                    WFF.binderPairDepth_ctx_ext]
              refine ⟨.dia xv_s hxv_s r.val hsub_s hne_s, ?_⟩
              simp only [WFF.binderPairDepth]
              exact le_trans r.property (le_of_eq hb)
          | .pair_elim sT₁ sT₂ sz _ _ sw₂eq _ =>
              exact absurd
                (Finset.mem_insert_of_mem
                  (by rw [← sw₂eq]; exact Finset.mem_insert_self _ _))
                (h_pf sz sT₁ sT₂)
        · by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
          · cases S with
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
                        substCore_dia_V_s_eq hxT_in hsub hne s_hsub s_hne
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
                      have r := WFF.substVar hx_in_outer
                        (Term.ctx_ext xv hxv_minus s_inner) (h_combined ▸ inner)
                      refine ⟨.dia xv hxv_minus r.val
                        (substCore_dia_hsub_erase hxv_minus h_xv_eq_x hsub)
                        (substCore_dia_h_no_extras_erase hxv_minus hne), ?_⟩
                      simp only [WFF.binderPairDepth]
                      exact le_trans r.property
                        (le_of_eq (WFF.binderPairDepth_ctx_cast _ inner))
                  | .pair_elim sT₁ sT₂ sz _ _ sw₂eq _ =>
                      exact absurd
                        (Finset.mem_insert_of_mem
                          (by rw [← sw₂eq]; exact Finset.mem_insert_self _ _))
                        (h_pf sz sT₁ sT₂)
                · exfalso
                  obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
                  simp only at hx'_eq; subst hx'_eq
                  have hx'box_in_dia : (⟨x', T'.VTypeBox⟩ : VarSymb × VarType) ∈
                      (VarCtx_dia xv V_inner hxv).1 := by
                    rw [VarCtx_dia_fst]
                    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩)
                  rcases Finset.mem_insert.mp (hsub hx'box_in_dia) with h_eq | h_in_V
                  · exact hxT_in (VarType.VTypeBox.inj (Prod.mk.inj h_eq).2 ▸ hx'T')
                  · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
          · refine ⟨.dia xv hxv inner ?_
              (fun p hp h_box => hne p (Finset.mem_insert_of_mem hp) h_box), ?_⟩
            · rw [VarCtx_dia_fst]
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
            · exact le_refl _
    | .pair_elim T₁ T₂ z hz w₁eq w₂eq body =>
        exact absurd
          (show (⟨z, VarType.VTypeProd T₁ T₂⟩ : VarSymb × VarType) ∈ _ from by
            rw [← w₂eq]; exact Finset.mem_insert_self _ _)
          (h_pf z T₁ T₂)
  termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ,
                  WFF.diaCount φ, WFF.numNodes φ, 0)
  -- ⭐Five recursion shapes, each alternative self-contained so their ORDER does not matter
  -- (`first` backtracks on any failure inside an alternative, and the `·` bullets force each
  -- component goal to be closed).  ⚠️Every cast rewrite is `try`ed: whether Lean leaves a visible
  -- `▸` in the recursion argument depends on how the arm was elaborated.  ⚠️And every hypothesis
  -- an alternative reaches for is fetched by `assumption`, never by name: an unknown identifier
  -- is a hard elaboration error that `first` cannot backtrack out of.
  decreasing_by
    all_goals first
      -- structural: the connective arms.  Same context, so component 1 compares `bpd` alone.
      | (refine lex4_le ?_ ?_ ?_
         · simp only [WFF.binderPairDepth]; try omega
         · simp only [WFF.diaCount]; try omega
         · simp only [WFF.numNodes]; try omega)
      -- ⭐quantifier descent: `T.pairDepth` moves from the formula into the context, so
      -- component 1 is EQUAL and `numNodes` carries the decrease.
      | (refine lex4_le ?_ ?_ ?_
         · try rw [WFF.binderPairDepth_ctx_cast]
           simp only [VarCtx.insertBnd, VarCtx.pairDepth_insert, WFF.binderPairDepth]
           try omega
         · try rw [WFF.diaCount_ctx_cast]
           simp only [WFF.diaCount]; try omega
         · try rw [WFF.numNodes_ctx_cast]
           simp only [WFF.numNodes]; try omega)
      -- interior call at a `box`'s inner context: `diaCount` is untouched, `numNodes` decreases
      | (have hS : S = T.VTypeBox := by assumption
         subst hS
         refine lex4_le ?_ ?_ ?_
         · have h_le := VarCtx.pairDepth_le_of_box_subset hsub
           have hVi := VarCtx.pairDepth_insert (⟨x, T⟩ : VarSymb × VarType) _ hx_minus
           rw [VarCtx_insert_erase hxT_in hx_minus] at hVi
           try rw [WFF.binderPairDepth_ctx_cast]
           simp only [VarCtx.pairDepth_insert, VarType.pairDepth, WFF.binderPairDepth]
             at h_le hVi ⊢
           try omega
         · try rw [WFF.diaCount_ctx_cast]
           simp only [WFF.diaCount]; try omega
         · try rw [WFF.numNodes_ctx_cast]
           simp only [WFF.numNodes]; try omega)
      -- interior call at a `dia`'s inner context: the `◇`-node just consumed makes `diaCount`
      -- STRICTLY smaller, which is the whole reason it is in the measure
      | (have hS : S = T.VTypeBox := by assumption
         subst hS
         refine lex4_lt ?_ ?_
         · have h_le := VarCtx.pairDepth_le_of_dia_subset hsub
           have hVi := VarCtx.pairDepth_insert (⟨x, T⟩ : VarSymb × VarType) _ hx_minus
           rw [VarCtx_insert_erase hxT_in hx_minus] at hVi
           try rw [WFF.binderPairDepth_ctx_cast]
           simp only [VarCtx.pairDepth_insert, VarType.pairDepth, WFF.binderPairDepth]
             at h_le hVi ⊢
           try omega
         · try rw [WFF.diaCount_ctx_cast]
           simp only [WFF.diaCount]
           try omega)
      -- ⭐modal β: the target is a LIFTED subformula, so only `diaCount` sees the decrease
      | (refine lex4_lt ?_ ?_
         · have h_le := VarCtx.pairDepth_le_of_dia_subset hsub_s
           have hSpd : S.pairDepth = xv.2.pairDepth := by
             simp only [h_S_eq, VarType.pairDepth]
           try rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_ctx_cast]
           try rw [WFF.binderPairDepth_ctx_ext]
           simp only [VarCtx.pairDepth_insert, WFF.binderPairDepth] at h_le ⊢
           try omega
         · try rw [WFF.diaCount_ctx_cast, WFF.diaCount_ctx_cast]
           try rw [WFF.diaCount_ctx_ext]
           simp only [WFF.diaCount]
           try omega)

  /-- ⭐The dispatcher, keyed on the BASE context `V` exactly as `Term.substVar` is.

      * **B** — `V` holds a pair variable: unpair `s`'s side and the formula there, recurse, and
        re-pair.  ⚠️Re-pairing uses the raw `.pair_elim` constructor rather than `WFF.pairElim`:
        the smart constructor descends under quantifiers and so needs a USER-named binder, which
        a `firstPairVar` witness need not be.
      * **A** — `V` pair-free but `x` pair-typed: `s` is then a literal `.pair`, so unpair the
        formula at `x` and substitute the components into the two slots in turn.
      * otherwise α-rename `x` to a fresh user symbol and hand off to `substCore`. -/
  def WFF.substVar {σ : Signature} {V : VarCtx} {x : VarSymb} {S : VarType}
      (hx : x ∉ VarCtx_to_VarSymbs V)
      (s : Term σ V S)
      (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
      { ψ : WFF σ V // WFF.binderPairDepth ψ ≤ WFF.binderPairDepth φ } := by
    match h_pv : V.firstPairVar with
    | some ⟨(z, V1, V2), hzmem⟩ =>
        -- ⭐Case B.
        have hzV : z ∈ VarCtx_to_VarSymbs V := Finset.mem_image.mpr ⟨_, hzmem, rfl⟩
        have hzU : z ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) :=
          VarCtx_erase_fresh hzmem
        have hVU : VarCtx_insert ⟨z, .VTypeProd V1 V2⟩
            (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hzU = V :=
          VarCtx_insert_erase hzmem hzU
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
        have hcomm2 : VarCtx.insertBnd2 V1 V2 (VarCtx_insert
              ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
              (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hu_U)
            = VarCtx_insert ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
                (VarCtx.insertBnd2 V1 V2 (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩)) hu_bnd :=
          VarCtx.insertBnd2_comm_insert _ _ hu_U rfl V1 V2 hu_bnd
        have hsEq : Term σ (VarCtx_insert ⟨z, .VTypeProd V1 V2⟩
            (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hzU) S = Term σ V S := by rw [hVU]
        -- `bpd` survives the whole rename / unpair / recast chain.
        have hbpd : WFF.binderPairDepth (hcomm2 ▸ WFF.unpair V1 V2 _ rfl hu_US
              (WFF.rename z _ (.VTypeProd V1 V2) hz_US hu_US
                (hcomm ▸ WFF.rename x _ S hx hu φ)))
            = WFF.binderPairDepth φ := by
          rw [WFF.binderPairDepth_ctx_cast, WFF.binderPairDepth_unpair,
              WFF.binderPairDepth_rename, WFF.binderPairDepth_ctx_cast,
              WFF.binderPairDepth_rename]
        have hdecB : (VarCtx_insert ⟨(UserSymb.fresh (insert x (VarCtx_to_VarSymbs V))).toVar, S⟩
              (VarCtx.insertBnd2 V1 V2 (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩)) hu_bnd).pairDepth
              + WFF.binderPairDepth (hcomm2 ▸ WFF.unpair V1 V2 _ rfl hu_US
                  (WFF.rename z _ (.VTypeProd V1 V2) hz_US hu_US
                    (hcomm ▸ WFF.rename x _ S hx hu φ)))
            < (VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ := by
          have hVd := VarCtx.pairDepth_insert (⟨z, VarType.VTypeProd V1 V2⟩ : VarSymb × VarType)
            (VarCtx_erase V ⟨z, .VTypeProd V1 V2⟩) hzU
          rw [hVU] at hVd
          rw [hbpd]
          simp only [VarCtx.insertBnd2, VarCtx.insertBnd, VarCtx.pairDepth_insert,
            VarType.pairDepth] at hVd ⊢
          omega
        have r := WFF.substVar hu_bnd
          (Term.unpair V1 V2 _ rfl hw_U
            (Term.rename z _ (.VTypeProd V1 V2) hzU hw_U (cast hsEq.symm s)))
          (hcomm2 ▸ WFF.unpair V1 V2 _ rfl hu_US
            (WFF.rename z _ (.VTypeProd V1 V2) hz_US hu_US
              (hcomm ▸ WFF.rename x _ S hx hu φ)))
        exact ⟨.pair_elim V1 V2 z hzU rfl hVU r.val,
          le_trans r.property (le_of_eq hbpd)⟩
    | none =>
        have hVfree : V.PairFree := VarCtx.pairFree_of_firstPairVar_none h_pv
        match hSp : S.isPair with
        | false =>
            match hxu : x.isUsr with
            | true =>
                -- ⭐`x` is ALREADY user-named — which is the only case the proof system ever
                -- produces, since `Proof.eq_elim`'s eigenvariable is a `UserSymb`.  Hand straight
                -- off to the structural pass: the α-rename below exists solely to manufacture the
                -- `isUsr` that `substCore`'s quantifier arms need, so here it is pure overhead,
                -- and skipping it is what makes the reduction lemmas (`WFF.subst_eq` and friends
                -- in `QML_v11_SubstLemmas`) reachable at all.
                exact WFF.substCore hxu hx
                  (VarCtx.pairFree_insert hx hVfree (fun T₁ T₂ h => by
                    subst h; simp [VarType.isPair] at hSp)) s φ
            | false =>
                -- α-rename `x` to a fresh USER symbol, then hand off to the structural pass.
                have hu : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar
                    ∉ VarCtx_to_VarSymbs V := UserSymb.fresh_not_mem _
                have r := WFF.substCore (x := (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar)
                  rfl hu
                  (VarCtx.pairFree_insert hu hVfree (fun T₁ T₂ h => by
                    subst h; simp [VarType.isPair] at hSp)) s
                  (WFF.rename x _ S hx hu φ)
                exact ⟨r.val, le_trans r.property
                  (le_of_eq (WFF.binderPairDepth_rename x _ S hx hu φ))⟩
        | true =>
            -- ⚠️NO `cases S` here.  Casing the TYPE re-introduces the formula `φ` as a fresh
            -- variable, and the termination goals then compare `binderPairDepth` of two unrelated
            -- atoms (the arm's `φ` and the parameter's).  Split `S` at the PROP level instead and
            -- cast `φ` ONCE along a VarCtx equality, which `binderPairDepth_ctx_cast` sees through.
            have hSeq : S = VarType.VTypeProd S.pfst S.psnd := by
              revert hSp
              cases S <;> simp [VarType.isPair, VarType.pfst, VarType.psnd]
            have hctx : VarCtx_insert ⟨x, S⟩ V hx
                = VarCtx_insert ⟨x, VarType.VTypeProd S.pfst S.psnd⟩ V hx := by
              rw [← hSeq]
            have hSpd : S.pairDepth = 1 + S.pfst.pairDepth + S.psnd.pairDepth := by
              conv_lhs => rw [hSeq]
              simp only [VarType.pairDepth]
            -- ⭐Case A.  `s` is a literal pair: a `pair_elim` would need a pair variable in `V`.
            match (hSeq ▸ s : Term σ V (VarType.VTypeProd S.pfst S.psnd)) with
            | .pair s1 s2 =>
                have hufresh : (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar
                    ∉ VarCtx_to_VarSymbs V := UserSymb.fresh_not_mem _
                have hbpd : WFF.binderPairDepth
                    (WFF.unpair S.pfst S.psnd _ rfl hufresh
                      (WFF.rename x _ (.VTypeProd S.pfst S.psnd) hx hufresh (hctx ▸ φ)))
                    = WFF.binderPairDepth φ := by
                  rw [WFF.binderPairDepth_unpair, WFF.binderPairDepth_rename,
                      WFF.binderPairDepth_ctx_cast]
                -- ⚠️DESTRUCTURE rather than `have r1 := …`: a data-valued `have` does not survive
                -- into the termination goals, so its bound would be unavailable there — and that
                -- bound is exactly what the SECOND call needs.
                obtain ⟨r1v, r1p⟩ := WFF.substVar
                  (VarCtx.nextBnd_not_mem (VarCtx.insertBnd S.pfst V))
                  (Term.ctx_ext ⟨V.nextBnd, S.pfst⟩ (VarCtx.nextBnd_not_mem V) s2)
                  (WFF.unpair S.pfst S.psnd _ rfl hufresh
                    (WFF.rename x _ (.VTypeProd S.pfst S.psnd) hx hufresh (hctx ▸ φ)))
                obtain ⟨r2v, r2p⟩ := WFF.substVar (VarCtx.nextBnd_not_mem V) s1 r1v
                exact ⟨r2v, le_trans r2p (le_trans r1p (le_of_eq hbpd))⟩
            | .pair_elim sT₁ sT₂ sz _ _ sw₂eq _ =>
                exact absurd
                  (show (⟨sz, VarType.VTypeProd sT₁ sT₂⟩ : VarSymb × VarType) ∈ V.1 from by
                    rw [← sw₂eq]; exact Finset.mem_insert_self _ _)
                  (hVfree sz sT₁ sT₂)
  termination_by ((VarCtx_insert ⟨x, S⟩ V hx).pairDepth + WFF.binderPairDepth φ,
                  WFF.diaCount φ, WFF.numNodes φ, 1)
  -- ⚠️No `subst_vars` here: substituting `S := V1 ×ᵥ V2` re-introduces the formula parameter as a
  -- FRESH variable, so the in-arm `have`s stop matching the goal.  Feed `omega` the arithmetic
  -- consequence of `S = V1 ×ᵥ V2` instead — that `rw` lives inside a `have` about `ℕ`, so it has
  -- no motive to compute.
  decreasing_by
    all_goals first
      -- hand-off to the structural pass at an ALREADY user-named `x`: nothing moves but the tag.
      | exact lex4_tag (le_refl _) (le_refl _) (le_refl _) (by omega)
      -- hand-off to the structural pass: the α-rename leaves all three measures alone,
      -- so only the tag moves.
      | exact lex4_tag
          (by rw [VarCtx.pairDepth_insert, VarCtx.pairDepth_insert, WFF.binderPairDepth_rename])
          (by rw [WFF.diaCount_rename])
          (by rw [WFF.numNodes_rename])
          (by omega)
      -- Case B: the `have` in the arm states the decrease directly.
      | exact lex4_pd (by assumption)
      -- Case A, both calls: unpairing replaces the pair variable by two slots, dropping
      -- `pairDepth` by one; `binderPairDepth` is preserved by `unpair`/`rename` (`hbpd`) and
      -- bounded by `r1p` for the second call.  `hSpd` supplies `S.pairDepth`.
      | (refine lex4_pd ?_
         try rw [WFF.binderPairDepth_unpair, WFF.binderPairDepth_rename,
                 WFF.binderPairDepth_ctx_cast]
         simp only [VarCtx.insertBnd, VarCtx.pairDepth_insert, VarType.pairDepth]
         omega)
end
