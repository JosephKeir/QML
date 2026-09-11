import QML.QML_v11_CtxExtMapCtxWFF

/-!
# QML v11 — opening a weakened, closed binder (LEMMA A)

In `congAll`, `Proof.all_intro` closes `φ` over the user eigenvariable `u` into the body
`rename u↦slot φ`; the hypothesis is then weakened by `u` (`ctx_extU`); and `Proof.all_elim` OPENS
it again, which `WFF.subst` does by renaming the slot to a fresh user name `y` before substituting.
So the formula `all_elim` actually substitutes into is

    rename slot↦y (ctx_extU u (rename u↦slot φ))

and LEMMA A says this is `ctx_extU u (rename u↦y φ)`, up to reordering `⟨u,T⟩` and `⟨y,T⟩` in the
context.  (LEMMA B then substitutes `var u` back for `y`.)

⚠️**Why it is not a direct application of A1.**  A1 moves `ctx_extU u` past a `mapCtx` whose SOURCE
is fresh for `u` — but the inner rename's source is `V + u`, which contains `u`.  So A1 is used on
the OUTER rename instead, run backwards:

1. push the cast onto the outer map, which becomes `renameOne slot↦y` at base `V + u`;
2. that map has the same function as `(renameOne slot↦y at base V).extendUser u`
   (`update` at `u` fixes `u` anyway) and lands in the reordered context — `mapCtx_congr`;
3. A1 backwards: `mapCtx (m.extendUser u) (ctx_extU u χ) = ctx_extU u (mapCtx m χ)`;
4. A2: `rename slot↦y ∘ rename u↦slot = rename u↦y`.

The steps are chained with `calc`, so each is checked up to definitional equality rather than by
syntactic rewriting — `rename` and `mapCtx renameOne`, and `insertBnd T V` and its unfolding, are
equal only definitionally.
-/

theorem WFF.open_weaken_close {σ : Signature} {V : VarCtx} (u : UserSymb) (T : VarType)
    (hTb : T.isBox = false) (hTp : T.isPair = false)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨u.toVar, T⟩ V hu))
    (hu_bnd : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T V))
    (hc : VarCtx.insertBnd T (VarCtx_insert ⟨u.toVar, T⟩ V hu)
            = VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T V) hu_bnd)
    (y : VarSymb)
    (hyW : y ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨u.toVar, T⟩ V hu))
    (hyV : y ∉ VarCtx_to_VarSymbs V)
    (hu_y : u.toVar ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨y, T⟩ V hyV))
    (hreord : VarCtx_insert ⟨u.toVar, T⟩ (VarCtx_insert ⟨y, T⟩ V hyV) hu_y
                = VarCtx_insert ⟨y, T⟩ (VarCtx_insert ⟨u.toVar, T⟩ V hu) hyW) :
    WFF.rename (VarCtx_insert ⟨u.toVar, T⟩ V hu).nextBnd y T (VarCtx.nextBnd_not_mem _) hyW
        (hc ▸ WFF.ctx_extU u T hu_bnd
          (WFF.rename u.toVar V.nextBnd T hu (VarCtx.nextBnd_not_mem V) φ)
          : WFF σ (VarCtx.insertBnd T (VarCtx_insert ⟨u.toVar, T⟩ V hu)))
      = hreord ▸ WFF.ctx_extU u T hu_y (WFF.rename u.toVar y T hu hyV φ) := by
  -- the outer rename, typed at the `insertBnd` form of its source
  let R₂ : CtxBij (VarCtx.insertBnd T (VarCtx_insert ⟨u.toVar, T⟩ V hu))
      (VarCtx_insert ⟨y, T⟩ (VarCtx_insert ⟨u.toVar, T⟩ V hu) hyW) :=
    CtxBij.renameOne (VarCtx_insert ⟨u.toVar, T⟩ V hu).nextBnd y T (VarCtx.nextBnd_not_mem _) hyW
  -- the slot-to-`y` rename at base `V`
  let m : CtxBij (VarCtx.insertBnd T V) (VarCtx_insert ⟨y, T⟩ V hyV) :=
    CtxBij.renameOne V.nextBnd y T (VarCtx.nextBnd_not_mem V) hyV
  have hf : ∀ v ∈ VarCtx_to_VarSymbs
        (VarCtx_insert ⟨u.toVar, T⟩ (VarCtx.insertBnd T V) hu_bnd),
      (m.extendUser u.toVar T hu_bnd hu_y).toCtxMap.f v
        = (CtxBij.ofEq hc.symm R₂).toCtxMap.f v := by
    intro v _
    have hne : u.toVar ≠ V.nextBnd := VarCtx.ne_nextBnd_of_isUsr rfl V
    simp only [CtxBij.extendUser_f, CtxBij.ofEq_f]
    change VarSymb.update (VarSymb.update id V.nextBnd y) u.toVar u.toVar v
      = VarSymb.update id (VarCtx_insert ⟨u.toVar, T⟩ V hu).nextBnd y v
    rw [VarCtx.nextBnd_insert_isUsr ⟨u.toVar, T⟩ V hu rfl]
    simp only [VarSymb.update]
    split_ifs <;> simp_all
  calc WFF.rename (VarCtx_insert ⟨u.toVar, T⟩ V hu).nextBnd y T (VarCtx.nextBnd_not_mem _) hyW
          (hc ▸ WFF.ctx_extU u T hu_bnd
            (WFF.rename u.toVar V.nextBnd T hu (VarCtx.nextBnd_not_mem V) φ)
            : WFF σ (VarCtx.insertBnd T (VarCtx_insert ⟨u.toVar, T⟩ V hu)))
        = WFF.mapCtx (CtxBij.ofEq hc.symm R₂)
            (WFF.ctx_extU u T hu_bnd
              (WFF.rename u.toVar V.nextBnd T hu (VarCtx.nextBnd_not_mem V) φ)) :=
          WFF.mapCtx_cast' hc R₂ (CtxBij.ofEq hc.symm R₂) (CtxBij.cast_ofEq' hc R₂) _
      _ = hreord ▸ WFF.mapCtx (m.extendUser u.toVar T hu_bnd hu_y)
            (WFF.ctx_extU u T hu_bnd
              (WFF.rename u.toVar V.nextBnd T hu (VarCtx.nextBnd_not_mem V) φ)) :=
          (WFF.mapCtx_congr _ _ hreord hf _).symm
      _ = hreord ▸ WFF.ctx_extU u T hu_y (WFF.mapCtx m
            (WFF.rename u.toVar V.nextBnd T hu (VarCtx.nextBnd_not_mem V) φ)) :=
          -- ⚠️The lambdas need explicit binder AND result types: untyped, `hreord ▸ X` leaves `X`'s
          -- type a metavariable and the cast cannot find its motive.
          congrArg (fun X : WFF σ (VarCtx_insert ⟨u.toVar, T⟩ (VarCtx_insert ⟨y, T⟩ V hyV) hu_y) =>
              (hreord ▸ X : WFF σ (VarCtx_insert ⟨y, T⟩ (VarCtx_insert ⟨u.toVar, T⟩ V hu) hyW)))
            (WFF.ctx_extU_mapCtx u T hTb hTp _ _ m hu_bnd hu_y
              (WFF.rename u.toVar V.nextBnd T hu (VarCtx.nextBnd_not_mem V) φ)).symm
      _ = hreord ▸ WFF.ctx_extU u T hu_y (WFF.rename u.toVar y T hu hyV φ) :=
          congrArg (fun X : WFF σ (VarCtx_insert ⟨y, T⟩ V hyV) =>
              (hreord ▸ WFF.ctx_extU u T hu_y X
                : WFF σ (VarCtx_insert ⟨y, T⟩ (VarCtx_insert ⟨u.toVar, T⟩ V hu) hyW)))
            (WFF.rename_comp u.toVar V.nextBnd y T hu (VarCtx.nextBnd_not_mem V) hyV φ)
