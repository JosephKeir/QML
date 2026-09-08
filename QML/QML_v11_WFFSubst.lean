import QML.QML_v11_WFF

/-!
# QML v11 — WFF substitution

The formula-level mirror of `QML_v11_TermSubst.lean`, and split off for the same reason.  Read that
file first: every construction here has the same shape, with two extra arms (`all` / `ex`) that are
uniformly cheap because the binders are nameless.

* **`WFF.ctx_ext`** — weakening by an ARBITRARY symbol: `ctx_extU` under a fresh user name followed
  by `rename'`.
* **`WFF.unpair`** — the inverse of `pairElim`: `V + ⟨z, T₁×T₂⟩ → insertBnd2 T₁ T₂ V`.
* **`WFF.substCore` / `WFF.substVar`** — substitution proper.
-/

/-! ## Weakening by an arbitrary symbol -/

/-- Weakening by an ARBITRARY symbol.  `ctx_extU` only covers USER symbols (it relies on a user
    insert leaving `nextBnd` alone); the general case is `ctx_extU` under a fresh user name
    followed by `rename'`, since `mapCtx` recomputes the slots. -/
def WFF.ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) :
    WFF σ (VarCtx_insert xv V hv) :=
  WFF.rename' (UserSymb.fresh (VarCtx_to_VarSymbs V)).toVar xv.1 xv.2
    (UserSymb.fresh_not_mem _) hv
    (WFF.ctx_extU (UserSymb.fresh (VarCtx_to_VarSymbs V)) xv.2 (UserSymb.fresh_not_mem _) φ)

theorem WFF.diaCount_ctx_ext {σ : Signature} {V : VarCtx} (xv : VarSymb × VarType)
    (hv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) :
    WFF.diaCount (WFF.ctx_ext xv hv φ) = WFF.diaCount φ := by
  rw [WFF.ctx_ext, WFF.diaCount_rename', WFF.diaCount_ctx_extU]

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
        -- split context, so the node simply disappears.
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
