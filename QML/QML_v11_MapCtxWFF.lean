import QML.QML_v11_MapCtx

/-!
# QML v11 — the `mapCtx` round trip for `Rel` and `WFF`

`QML_v11_MapCtx` proves the round trip for `Term`/`Func`.  This file lifts it.

`WFF.mapCtx` is `Term.mapCtx` arm for arm: `box`/`dia`/`pair_elim` are `boxterm`/`diaterm`/
`pair_elim` again (same side conditions, same casts), `eq`/`atom` delegate to `Term`/`Rel`, and the
propositional arms are plain recursion.  ⭐The quantifier arms are ONE `extendBnd` layer, which
`CtxBij.extendBnd_id` closes against `insertBnd T` of the ambient equation — no name, no freshness,
no context algebra.  That is the canonical-binder design paying off: the arm that would be the
hardest with named binders is the easiest one here.
-/

/-! ## `Rel` -/

theorem Rel.cast_R {σ : Signature} {A B : VarCtx} {n : ℕ} (h : A = B)
    (hr : {r // σ.relArity r = n}) :
    (h ▸ (Rel.R hr : Rel σ A n)) = Rel.R hr := by subst h; rfl

theorem Rel.cast_eval {σ : Signature} {A B : VarCtx} {n : ℕ} (h : A = B)
    (R' : Rel σ A (n + 1)) (t : Term σ A .Var) :
    (h ▸ (Rel.eval R' t : Rel σ A n)) = Rel.eval (h ▸ R') (h ▸ t) := by subst h; rfl

theorem Rel.mapCtx_R {σ : Signature} {V V' : VarCtx} {n : ℕ} (m : CtxBij V V')
    (hr : {r // σ.relArity r = n}) :
    Rel.mapCtx m (Rel.R hr : Rel σ V n) = Rel.R hr := rfl

theorem Rel.mapCtx_eval {σ : Signature} {V V' : VarCtx} {n : ℕ} (m : CtxBij V V')
    (R' : Rel σ V (n + 1)) (t : Term σ V .Var) :
    Rel.mapCtx m (Rel.eval R' t) = Rel.eval (Rel.mapCtx m R') (Term.mapCtx m t) := rfl

theorem Rel.mapCtx_roundtrip {σ : Signature} {V V' V'' : VarCtx} (m₁ : CtxBij V V')
    (m₂ : CtxBij V' V'') (hVV : V'' = V)
    (hid : ∀ v ∈ VarCtx_to_VarSymbs V, m₂.toCtxMap.f (m₁.toCtxMap.f v) = v) :
    ∀ {n : ℕ} (R : Rel σ V n), hVV ▸ (Rel.mapCtx m₂ (Rel.mapCtx m₁ R)) = R
  | _, .R hr => by rw [Rel.mapCtx_R, Rel.mapCtx_R, Rel.cast_R]
  | _, .eval R' t => by
      rw [Rel.mapCtx_eval, Rel.mapCtx_eval, Rel.cast_eval,
          Rel.mapCtx_roundtrip m₁ m₂ hVV hid R',
          Term.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid _ t]

/-! ## `WFF`: constructor casts and congruences -/

theorem WFF.cast_atom {σ : Signature} {A B : VarCtx} (h : A = B) (R : Rel σ A 0) :
    (h ▸ (WFF.atom R : WFF σ A)) = WFF.atom (h ▸ R) := by subst h; rfl

theorem WFF.cast_top {σ : Signature} {A B : VarCtx} (h : A = B) :
    (h ▸ (WFF.top : WFF σ A)) = WFF.top := by subst h; rfl

theorem WFF.cast_bot {σ : Signature} {A B : VarCtx} (h : A = B) :
    (h ▸ (WFF.bot : WFF σ A)) = WFF.bot := by subst h; rfl

theorem WFF.cast_and {σ : Signature} {A B : VarCtx} (h : A = B) (φ ψ : WFF σ A) :
    (h ▸ (WFF.and φ ψ : WFF σ A)) = WFF.and (h ▸ φ) (h ▸ ψ) := by subst h; rfl

theorem WFF.cast_or {σ : Signature} {A B : VarCtx} (h : A = B) (φ ψ : WFF σ A) :
    (h ▸ (WFF.or φ ψ : WFF σ A)) = WFF.or (h ▸ φ) (h ▸ ψ) := by subst h; rfl

theorem WFF.cast_imp {σ : Signature} {A B : VarCtx} (h : A = B) (φ ψ : WFF σ A) :
    (h ▸ (WFF.imp φ ψ : WFF σ A)) = WFF.imp (h ▸ φ) (h ▸ ψ) := by subst h; rfl

theorem WFF.cast_eq {σ : Signature} {A B : VarCtx} (h : A = B) (s t : Term σ A .Var) :
    (h ▸ (WFF.eq s t : WFF σ A)) = WFF.eq (h ▸ s) (h ▸ t) := by subst h; rfl

theorem WFF.cast_all {σ : Signature} {A B : VarCtx} (h : A = B) (T : VarType)
    (ψ : WFF σ (VarCtx.insertBnd T A)) :
    (h ▸ (WFF.all T ψ : WFF σ A)) = WFF.all T (congrArg (VarCtx.insertBnd T) h ▸ ψ) := by
  subst h; rfl

theorem WFF.cast_ex {σ : Signature} {A B : VarCtx} (h : A = B) (T : VarType)
    (ψ : WFF σ (VarCtx.insertBnd T A)) :
    (h ▸ (WFF.ex T ψ : WFF σ A)) = WFF.ex T (congrArg (VarCtx.insertBnd T) h ▸ ψ) := by
  subst h; rfl

theorem WFF.cast_box {σ : Signature} {W W' V_inner : VarCtx} (h : W = W') (χ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    (h ▸ (WFF.box χ hsub hne : WFF σ W)) = WFF.box χ (h ▸ hsub) (h ▸ hne) := by subst h; rfl

theorem WFF.cast_dia {σ : Signature} {W W' V_inner : VarCtx}
    (h : W = W') (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (χ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    (h ▸ (WFF.dia xv hxv χ hsub hne : WFF σ W)) = WFF.dia xv hxv χ (h ▸ hsub) (h ▸ hne) := by
  subst h; rfl

theorem WFF.cast_pair_elim {σ : Signature} {pe_V W₁ W₂ W₂' : VarCtx} {T₁ T₂ : VarType}
    {z : VarSymb} (h : W₂ = W₂') (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ pe_V = W₁)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂) (body : WFF σ W₁) :
    (h ▸ (WFF.pair_elim T₁ T₂ z hz w₁eq w₂eq body : WFF σ W₂))
      = WFF.pair_elim T₁ T₂ z hz w₁eq (w₂eq.trans h) body := by subst h; rfl

theorem WFF.box_congr' {σ : Signature} {W V_inner V_inner' : VarCtx}
    (hI : V_inner' = V_inner) (X : WFF σ V_inner') (χ : WFF σ V_inner) (hX : hI ▸ X = χ)
    (P : (VarCtx_box V_inner').1 ⊆ W.1)
    (Q : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner').1)
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    (WFF.box X P Q : WFF σ W) = WFF.box χ hsub hne := by
  subst hI; subst hX; rfl

theorem WFF.dia_congr' {σ : Signature} {W V_inner V_inner' : VarCtx}
    {x x' : VarSymb × VarType}
    {hx' : x'.1 ∉ VarCtx_to_VarSymbs V_inner'} {hx : x.1 ∉ VarCtx_to_VarSymbs V_inner}
    (hxx : x' = x) (hI : V_inner' = V_inner)
    (X : WFF σ (VarCtx_insert x' V_inner' hx')) (χ : WFF σ (VarCtx_insert x V_inner hx))
    (hCtx : VarCtx_insert x' V_inner' hx' = VarCtx_insert x V_inner hx)
    (hX : hCtx ▸ X = χ)
    (P : (VarCtx_dia x' V_inner' hx').1 ⊆ W.1)
    (Q : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x' V_inner' hx').1)
    (hsub : (VarCtx_dia x V_inner hx).1 ⊆ W.1)
    (hne : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V_inner hx).1) :
    (WFF.dia x' hx' X P Q : WFF σ W) = WFF.dia x hx χ hsub hne := by
  subst hxx; subst hI; subst hX; rfl

theorem WFF.pair_elim_congr' {σ : Signature} {pe_V pe_V' W₁ W₁' W₂ : VarCtx}
    {T₁ T₂ : VarType} {z z' : VarSymb}
    {hz' : z' ∉ VarCtx_to_VarSymbs pe_V'} {hz : z ∉ VarCtx_to_VarSymbs pe_V}
    (hzz : z' = z) (hB : pe_V' = pe_V) (hW : W₁' = W₁)
    (w₁eq' : VarCtx.insertBnd2 T₁ T₂ pe_V' = W₁')
    (w₁eq : VarCtx.insertBnd2 T₁ T₂ pe_V = W₁)
    (w₂eq' : VarCtx_insert ⟨z', T₁.VTypeProd T₂⟩ pe_V' hz' = W₂)
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂)
    (X : WFF σ W₁') (body : WFF σ W₁) (hX : hW ▸ X = body) :
    (WFF.pair_elim T₁ T₂ z' hz' w₁eq' w₂eq' X : WFF σ W₂)
      = WFF.pair_elim T₁ T₂ z hz w₁eq w₂eq body := by
  subst hzz; subst hB; subst hW; subst hX; rfl

theorem WFF.pair_elim_as_cast {σ : Signature} {pe_V W₂ : VarCtx} {T₁ T₂ : VarType}
    {z : VarSymb} (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (X : WFF σ (VarCtx.insertBnd2 T₁ T₂ pe_V))
    (w₂eq : VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz = W₂) :
    (WFF.pair_elim T₁ T₂ z hz rfl w₂eq X : WFF σ W₂)
      = w₂eq ▸ (WFF.pair_elim T₁ T₂ z hz rfl rfl X) := by subst w₂eq; rfl

theorem WFF.mapCtx_cast {σ : Signature} {A B V' : VarCtx} (h : A = B)
    (m : CtxBij B V') (m' : CtxBij A V') (hm : h ▸ m' = m) (φ : WFF σ A) :
    WFF.mapCtx m (h ▸ φ) = WFF.mapCtx m' φ := by
  subst h; subst hm; rfl

/-! ## `WFF.mapCtx` computation rules -/

theorem WFF.mapCtx_atom {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (R : Rel σ V 0) :
    WFF.mapCtx m (WFF.atom R) = WFF.atom (Rel.mapCtx m R) := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_top {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') :
    WFF.mapCtx m (WFF.top : WFF σ V) = WFF.top := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_bot {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') :
    WFF.mapCtx m (WFF.bot : WFF σ V) = WFF.bot := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_and {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (φ ψ : WFF σ V) :
    WFF.mapCtx m (WFF.and φ ψ) = WFF.and (WFF.mapCtx m φ) (WFF.mapCtx m ψ) := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_or {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (φ ψ : WFF σ V) :
    WFF.mapCtx m (WFF.or φ ψ) = WFF.or (WFF.mapCtx m φ) (WFF.mapCtx m ψ) := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_imp {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (φ ψ : WFF σ V) :
    WFF.mapCtx m (WFF.imp φ ψ) = WFF.imp (WFF.mapCtx m φ) (WFF.mapCtx m ψ) := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_eq {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (s t : Term σ V .Var) :
    WFF.mapCtx m (WFF.eq s t) = WFF.eq (Term.mapCtx m s) (Term.mapCtx m t) := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_all {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (T : VarType)
    (ψ : WFF σ (VarCtx.insertBnd T V)) :
    WFF.mapCtx m (WFF.all T ψ) = WFF.all T (WFF.mapCtx (m.extendBnd T) ψ) := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_ex {σ : Signature} {V V' : VarCtx} (m : CtxBij V V') (T : VarType)
    (ψ : WFF σ (VarCtx.insertBnd T V)) :
    WFF.mapCtx m (WFF.ex T ψ) = WFF.ex T (WFF.mapCtx (m.extendBnd T) ψ) := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_box {σ : Signature} {V V' V_inner : VarCtx}
    (m : CtxBij V V') (χ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V)
    (hsub' : (VarCtx_box (m.imageCtx V_inner hU)).1 ⊆ V'.1)
    (hne' : ∀ p ∈ V'.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box (m.imageCtx V_inner hU)).1) :
    WFF.mapCtx m (WFF.box χ hsub hne)
      = WFF.box (WFF.mapCtx (m.toImage V_inner hU) χ) hsub' hne' := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_dia {σ : Signature} {V V' V_inner : VarCtx}
    (m : CtxBij V V') {x : VarSymb × VarType} (hx : x.1 ∉ VarCtx_to_VarSymbs V_inner)
    (χ : WFF σ (VarCtx_insert x V_inner hx))
    (hsub : (VarCtx_dia x V_inner hx).1 ⊆ V.1)
    (hne : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V_inner hx).1)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V)
    (hxV : x.1 ∈ VarCtx_to_VarSymbs V)
    (hx' : m.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m.imageCtx V_inner hU))
    (hsub' : (VarCtx_dia (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType)
                (m.imageCtx V_inner hU) hx').1 ⊆ V'.1)
    (hne' : ∀ p ∈ V'.1, VarType.isBox p.2 = true
              → p ∈ (VarCtx_dia (⟨m.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType)
                      (m.imageCtx V_inner hU) hx').1) :
    WFF.mapCtx m (WFF.dia x hx χ hsub hne)
      = WFF.dia ⟨m.toCtxMap.f x.1, x.2⟩ hx'
          (WFF.mapCtx (m.extendPoint V_inner hU x hxV hx hx') χ) hsub' hne' := by
  conv_lhs => unfold WFF.mapCtx

theorem WFF.mapCtx_pair_elim {σ : Signature} {pe_V V' : VarCtx} {T₁ T₂ : VarType}
    {z : VarSymb} (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (body : WFF σ (VarCtx.insertBnd2 T₁ T₂ pe_V))
    (m : CtxBij (VarCtx_insert ⟨z, T₁.VTypeProd T₂⟩ pe_V hz) V')
    (hz' : m.toCtxMap.f z ∉ VarCtx_to_VarSymbs
             (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩))
    (w₂eq' : VarCtx_insert ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩
               (VarCtx_erase V' ⟨m.toCtxMap.f z, T₁.VTypeProd T₂⟩) hz' = V') :
    WFF.mapCtx m (WFF.pair_elim T₁ T₂ z hz rfl rfl body)
      = WFF.pair_elim T₁ T₂ (m.toCtxMap.f z) hz' rfl w₂eq'
          (WFF.mapCtx (((CtxBij.restrictInsert hz m).extendBnd T₁).extendBnd T₂) body) := by
  conv_lhs => unfold WFF.mapCtx

/-! ## The `WFF` round trip -/

theorem WFF.mapCtx_roundtrip {σ : Signature} :
    ∀ (V V' V'' : VarCtx) (m₁ : CtxBij V V') (m₂ : CtxBij V' V'') (hVV : V'' = V)
      (_hid : ∀ v ∈ VarCtx_to_VarSymbs V, m₂.toCtxMap.f (m₁.toCtxMap.f v) = v)
      (φ : WFF σ V),
      hVV ▸ (WFF.mapCtx m₂ (WFF.mapCtx m₁ φ)) = φ
  | V, V', V'', m₁, m₂, hVV, hid, .atom R => by
      rw [WFF.mapCtx_atom, WFF.mapCtx_atom, WFF.cast_atom, Rel.mapCtx_roundtrip m₁ m₂ hVV hid R]
  | _, _, _, _, _, hVV, _, .top => by
      rw [WFF.mapCtx_top, WFF.mapCtx_top, WFF.cast_top]
  | _, _, _, _, _, hVV, _, .bot => by
      rw [WFF.mapCtx_bot, WFF.mapCtx_bot, WFF.cast_bot]
  | V, V', V'', m₁, m₂, hVV, hid, .and φ ψ => by
      rw [WFF.mapCtx_and, WFF.mapCtx_and, WFF.cast_and,
          WFF.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid φ,
          WFF.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid ψ]
  | V, V', V'', m₁, m₂, hVV, hid, .or φ ψ => by
      rw [WFF.mapCtx_or, WFF.mapCtx_or, WFF.cast_or,
          WFF.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid φ,
          WFF.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid ψ]
  | V, V', V'', m₁, m₂, hVV, hid, .imp φ ψ => by
      rw [WFF.mapCtx_imp, WFF.mapCtx_imp, WFF.cast_imp,
          WFF.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid φ,
          WFF.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid ψ]
  | V, V', V'', m₁, m₂, hVV, hid, .eq s t => by
      rw [WFF.mapCtx_eq, WFF.mapCtx_eq, WFF.cast_eq,
          Term.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid _ s,
          Term.mapCtx_roundtrip V V' V'' m₁ m₂ hVV hid _ t]
  -- ⭐The quantifier arms: one `extendBnd` layer.
  | _, _, _, m₁, m₂, hVV, hid, .all T ψ => by
      have IH := WFF.mapCtx_roundtrip _ _ _ (m₁.extendBnd T) (m₂.extendBnd T)
        (congrArg (VarCtx.insertBnd T) hVV) (CtxBij.extendBnd_id m₁ m₂ hVV hid T) ψ
      rw [WFF.mapCtx_all, WFF.mapCtx_all, WFF.cast_all]
      exact congrArg (WFF.all T) IH
  | _, _, _, m₁, m₂, hVV, hid, .ex T ψ => by
      have IH := WFF.mapCtx_roundtrip _ _ _ (m₁.extendBnd T) (m₂.extendBnd T)
        (congrArg (VarCtx.insertBnd T) hVV) (CtxBij.extendBnd_id m₁ m₂ hVV hid T) ψ
      rw [WFF.mapCtx_ex, WFF.mapCtx_ex, WFF.cast_ex]
      exact congrArg (WFF.ex T) IH
  | V, V', V'', m₁, m₂, hVV, hid, .box inner hsub hne => by
      rename_i V_inner
      have hU₁ : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_box_sub hsub
      have hsub₁ : (VarCtx_box (m₁.imageCtx V_inner hU₁)).1 ⊆ V'.1 :=
        CtxBij.box_sub_image m₁ hsub hU₁
      have hne₁ : ∀ p ∈ V'.1, VarType.isBox p.2 = true
          → p ∈ (VarCtx_box (m₁.imageCtx V_inner hU₁)).1 :=
        CtxBij.box_extras_image m₁ hne hU₁
      have hU₂ : ∀ v ∈ VarCtx_to_VarSymbs (m₁.imageCtx V_inner hU₁),
          v ∈ VarCtx_to_VarSymbs V' := VarCtx.symbs_of_box_sub hsub₁
      have hid' : ∀ v ∈ VarCtx_to_VarSymbs V_inner,
          m₂.toCtxMap.f (m₁.toCtxMap.f v) = v := fun v hv => hid v (hU₁ v hv)
      have hI : m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂ = V_inner :=
        CtxBij.imageCtx_roundtrip m₁ m₂ V_inner hU₁ hU₂ hid'
      have hIH := WFF.mapCtx_roundtrip V_inner (m₁.imageCtx V_inner hU₁)
        (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂)
        (m₁.toImage V_inner hU₁) (m₂.toImage (m₁.imageCtx V_inner hU₁) hU₂) hI hid' inner
      rw [WFF.mapCtx_box m₁ inner hsub hne hU₁ hsub₁ hne₁,
          WFF.mapCtx_box m₂ _ hsub₁ hne₁ hU₂
            (CtxBij.box_sub_image m₂ hsub₁ hU₂) (CtxBij.box_extras_image m₂ hne₁ hU₂),
          WFF.cast_box]
      exact WFF.box_congr' hI _ inner hIH _ _ _ _
  | V, V', V'', m₁, m₂, hVV, hid, .dia x hx χ hsub hne => by
      rename_i V_inner
      have hxV : x.1 ∈ VarCtx_to_VarSymbs V :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub, rfl⟩
      have hU₁ : ∀ v ∈ VarCtx_to_VarSymbs V_inner, v ∈ VarCtx_to_VarSymbs V :=
        VarCtx.symbs_of_dia_sub hsub
      have hx'₁ : m₁.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m₁.imageCtx V_inner hU₁) :=
        CtxBij.notMem_imageCtx m₁ hU₁ hxV hx
      have hsub₁ := CtxBij.dia_sub_image m₁ hsub hU₁ hx'₁
      have hne₁ := CtxBij.dia_extras_image m₁ hne hU₁ hx'₁
      have hxV' : m₁.toCtxMap.f x.1 ∈ VarCtx_to_VarSymbs V' :=
        Finset.mem_image.mpr ⟨_, VarCtx.dia_witness_mem hsub₁, rfl⟩
      have hU₂ : ∀ v ∈ VarCtx_to_VarSymbs (m₁.imageCtx V_inner hU₁),
          v ∈ VarCtx_to_VarSymbs V' := VarCtx.symbs_of_dia_sub hsub₁
      have hx'₂ := CtxBij.notMem_imageCtx m₂ hU₂ hxV' hx'₁
      have hsub₂ := CtxBij.dia_sub_image m₂ hsub₁ hU₂ hx'₂
      have hne₂ := CtxBij.dia_extras_image m₂ hne₁ hU₂ hx'₂
      have hxeq : m₂.toCtxMap.f (m₁.toCtxMap.f x.1) = x.1 := hid x.1 hxV
      have hI : m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂ = V_inner :=
        CtxBij.imageCtx_roundtrip m₁ m₂ V_inner hU₁ hU₂ (fun v hv => hid v (hU₁ v hv))
      have hxx : (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType) = x := by
        rw [hxeq]
      have hCtx : VarCtx_insert
            (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType)
            (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂) hx'₂
          = VarCtx_insert x V_inner hx := by
        refine VarCtx_ext _ _ ?_
        change insert (⟨m₂.toCtxMap.f (m₁.toCtxMap.f x.1), x.2⟩ : VarSymb × VarType)
              (m₂.imageCtx (m₁.imageCtx V_inner hU₁) hU₂).1
            = insert x V_inner.1
        rw [hxx, hI]
      have hid'' : ∀ v ∈ VarCtx_to_VarSymbs (VarCtx_insert x V_inner hx),
          m₂.toCtxMap.f (m₁.toCtxMap.f v) = v := by
        intro v hv
        rw [VarCtx_to_VarSymbs_insert] at hv
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact hxeq
        · exact hid v (hU₁ v hv')
      have hIH := WFF.mapCtx_roundtrip _ _ _
        (m₁.extendPoint V_inner hU₁ x hxV hx hx'₁)
        (m₂.extendPoint (m₁.imageCtx V_inner hU₁) hU₂
          (⟨m₁.toCtxMap.f x.1, x.2⟩ : VarSymb × VarType) hxV' hx'₁ hx'₂)
        hCtx hid'' χ
      rw [WFF.mapCtx_dia m₁ hx χ hsub hne hU₁ hxV hx'₁ hsub₁ hne₁,
          WFF.mapCtx_dia m₂ hx'₁ _ hsub₁ hne₁ hU₂ hxV' hx'₂ hsub₂ hne₂,
          WFF.cast_dia]
      exact WFF.dia_congr' hxx hI _ χ hCtx hIH _ _ _ _
  | V, V', V'', m₁, m₂, hVV, hid, .pair_elim T₁ T₂ z hz w₁eq w₂eq body => by
      rename_i pe_V pe_W₁
      -- IH before any `subst` (see `Term.mapCtx_roundtrip`'s `pair_elim` arm).
      have IH : ∀ (A B : VarCtx) (M₁ : CtxBij pe_W₁ A) (M₂ : CtxBij A B) (h : B = pe_W₁)
          (hid' : ∀ v ∈ VarCtx_to_VarSymbs pe_W₁, M₂.toCtxMap.f (M₁.toCtxMap.f v) = v),
          h ▸ (WFF.mapCtx M₂ (WFF.mapCtx M₁ body)) = body :=
        fun A B M₁ M₂ h hid' => WFF.mapCtx_roundtrip pe_W₁ A B M₁ M₂ h hid' body
      subst w₂eq
      subst w₁eq
      have hzV₁ : (⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩ : VarSymb × VarType) ∈ V'.1 :=
        m₁.toCtxMap.maps _ (Finset.mem_insert_self _ _)
      have hz₁ : m₁.toCtxMap.f z
          ∉ VarCtx_to_VarSymbs (VarCtx_erase V' ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩) :=
        VarCtx_erase_fresh hzV₁
      have w₂eq₁ : VarCtx_insert ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩
          (VarCtx_erase V' ⟨m₁.toCtxMap.f z, T₁.VTypeProd T₂⟩) hz₁ = V' :=
        VarCtx_insert_erase hzV₁ hz₁
      have hzV₂ : (⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩
          : VarSymb × VarType) ∈ V''.1 :=
        (CtxBij.ofEq w₂eq₁ m₂).toCtxMap.maps _ (Finset.mem_insert_self _ _)
      have hz₂ : (CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z)
          ∉ VarCtx_to_VarSymbs (VarCtx_erase V''
              ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩) :=
        VarCtx_erase_fresh hzV₂
      have w₂eq₂ : VarCtx_insert
          ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩
          (VarCtx_erase V''
            ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩) hz₂ = V'' :=
        VarCtx_insert_erase hzV₂ hz₂
      rw [WFF.mapCtx_pair_elim hz body m₁ hz₁ w₂eq₁,
          WFF.pair_elim_as_cast hz₁ _ w₂eq₁,
          WFF.mapCtx_cast w₂eq₁ m₂ (CtxBij.ofEq w₂eq₁ m₂) (CtxBij.cast_ofEq w₂eq₁ m₂),
          WFF.mapCtx_pair_elim hz₁ _ (CtxBij.ofEq w₂eq₁ m₂) hz₂ w₂eq₂,
          WFF.cast_pair_elim]
      have hzz : (CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z) = z :=
        hid z (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_self _ _)
      have hB : VarCtx_erase V''
          ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩ = pe_V := by
        rw [hzz, hVV]
        refine VarCtx_ext _ _ ?_
        change (insert (⟨z, T₁.VTypeProd T₂⟩ : VarSymb × VarType) pe_V.1).erase
            ⟨z, T₁.VTypeProd T₂⟩ = pe_V.1
        exact Finset.erase_insert (fun hmem => hz (Finset.mem_image.mpr ⟨_, hmem, rfl⟩))
      have hW : VarCtx.insertBnd2 T₁ T₂ (VarCtx_erase V''
          ⟨(CtxBij.ofEq w₂eq₁ m₂).toCtxMap.f (m₁.toCtxMap.f z), T₁.VTypeProd T₂⟩)
          = VarCtx.insertBnd2 T₁ T₂ pe_V := by rw [hB]
      have hid₀ : ∀ v ∈ VarCtx_to_VarSymbs pe_V,
          (CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).toCtxMap.f
            ((CtxBij.restrictInsert hz m₁).toCtxMap.f v) = v := fun v hv =>
        hid v (by rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem hv)
      have hid₁ := CtxBij.extendBnd_id (CtxBij.restrictInsert hz m₁)
        (CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)) hB hid₀ T₁
      have hidB := CtxBij.extendBnd_id ((CtxBij.restrictInsert hz m₁).extendBnd T₁)
        ((CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).extendBnd T₁) (by rw [hB]) hid₁ T₂
      have hIH := IH _ _
        (((CtxBij.restrictInsert hz m₁).extendBnd T₁).extendBnd T₂)
        (((CtxBij.restrictInsert hz₁ (CtxBij.ofEq w₂eq₁ m₂)).extendBnd T₁).extendBnd T₂)
        hW hidB
      exact WFF.pair_elim_congr' hzz hB hW _ _ _ _ _ body hIH
  termination_by _ _ _ _ _ _ _ φ => sizeOf φ

/-! ## ⭐The rename involution

Renaming is `mapCtx` along `CtxBij.renameOne`, and renaming back lands in the SAME context on the
nose, so the round trip's context equation is `rfl`.  The side condition is that the two
`VarSymb.update`s cancel on every symbol of the context, which needs exactly that `old` and `new`
are both fresh for the base — the "fresh name must not collide" condition. -/

theorem CtxBij.renameOne_roundtrip_id {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V) :
    ∀ v ∈ VarCtx_to_VarSymbs (VarCtx_insert ⟨old, T⟩ V hold),
      (CtxBij.renameOne new old T hnew hold).toCtxMap.f
        ((CtxBij.renameOne old new T hold hnew).toCtxMap.f v) = v := by
  intro v hv
  rw [VarCtx_to_VarSymbs_insert] at hv
  change VarSymb.update id new old (VarSymb.update id old new v) = v
  rcases Finset.mem_insert.mp hv with rfl | hv'
  · simp [VarSymb.update]
  · have h1 : v ≠ old := fun h => hold (h ▸ hv')
    have h2 : v ≠ new := fun h => hnew (h ▸ hv')
    simp [VarSymb.update, h1, h2]

theorem Term.rename_rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V) {S : VarType}
    (t : Term σ (VarCtx_insert ⟨old, T⟩ V hold) S) :
    Term.rename new old T hnew hold (Term.rename old new T hold hnew t) = t :=
  Term.mapCtx_roundtrip _ _ _ (CtxBij.renameOne old new T hold hnew)
    (CtxBij.renameOne new old T hnew hold) rfl
    (CtxBij.renameOne_roundtrip_id old new T hold hnew) S t

theorem Rel.rename_rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V) {n : ℕ}
    (R : Rel σ (VarCtx_insert ⟨old, T⟩ V hold) n) :
    Rel.rename new old T hnew hold (Rel.rename old new T hold hnew R) = R :=
  Rel.mapCtx_roundtrip (CtxBij.renameOne old new T hold hnew)
    (CtxBij.renameOne new old T hnew hold) rfl
    (CtxBij.renameOne_roundtrip_id old new T hold hnew) R

theorem WFF.rename_rename {σ : Signature} {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V)
    (φ : WFF σ (VarCtx_insert ⟨old, T⟩ V hold)) :
    WFF.rename new old T hnew hold (WFF.rename old new T hold hnew φ) = φ :=
  WFF.mapCtx_roundtrip _ _ _ (CtxBij.renameOne old new T hold hnew)
    (CtxBij.renameOne new old T hnew hold) rfl
    (CtxBij.renameOne_roundtrip_id old new T hold hnew) φ
