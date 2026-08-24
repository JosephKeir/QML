import QML.SemanticsRealB
import QML.SubstitutionLemmas9

/-!
# Soundness for the "real" model `RModel` (in progress)

This is the RModel analogue of `Soundness2.lean` (which targets `GModel`).  The plan is to retire
`GModel` once this is complete; `GModel` was a stopgap while the target model structure was unclear.

Key semantic difference from `GModel`: `RModel` has **no** total `necIntro`/`posIntro` (and no
`nec_beta`/`pos_beta`).  Box/dia objects come from the applicative `map`/`zip`/`mapPos` structure,
are read out by the **injective** `necEval`/`posEval`.  So the `◇` proposition is interpreted via
membership in the realization *set* `posEval` (rather than `posMem`), and the modal reasoning uses
`mapPos_eval`/`nec_inj`/`pos_inj` in place of the `β`-laws.  The substitution/context plumbing
(`Env`, `Env.extend`, `Env.boxPush`) is *identical* to `GModel`, so those parts port verbatim.

**Status: the pair-free soundness port is COMPLETE** — full parity with `Soundness2.lean`'s GModel
proof.  `interpTerm/Func/Rel_{ctx_ext,rename,substVar}`, `interpWFF_{ctx_ext,rename,substVar}`
(with collision branches), and the full `soundness` induction over `Proof` are all proven; every
remaining `sorry` is the pair sector (`VTypeProd` arms / `pair_elim` / pair-ful `firstPairVar`
branches), exactly as in GModel.  The GModel→RModel β-swaps used throughout: `nec_beta` ⇒
`interpTerm_boxterm` + `necEval_interpTermNec` after `nec_inj`; `pos_beta`/`posMem` ⇒
`mapPos_eval`/`∈ posEval` after `pos_inj`; `congrArg necIntro` (`box_ext`) ⇒ `nec_inj`.
-/

universe u

namespace RModel

variable {σ : Signature}


/-- Relation interpretation (ordinary FOL recursion).  Identical shape to `GModel.interpRel`. -/
def interpRel (M : RModel σ) : {V : VarCtx} → {n : ℕ} →
    Rel σ V n → (w : M.W) → M.Env V w → (Fin n → M.D w) → Prop
  | _, _, .R hr,      w, _,   args => M.relInterp hr.1 w (hr.2.symm ▸ args)
  | _, _, .eval R' t, w, env, args => M.interpRel R' w env (Fin.cons (M.interpTerm t w env) args)

/-! ### Environment / `boxPush` / cast foundation lemmas

These are pure `Env`/`Env.boxPush`/context-cast manipulation — `RModel.Env` is *identical* to
`GModel.Env`, so they port verbatim from `Soundness2.lean` (only `GModel` → `RModel`). -/

/-- Extending the env by a **not-box**-typed variable leaves `boxPush` unchanged. -/
theorem boxPush_extend_notBox (M : RModel σ) {V_inner W : VarCtx} {w : M.W}
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hsub' : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert xv W hxv).1)
    (env : M.Env W w) (a : M.interp xv.2 w) (hxvBox : xv.2.isBox = false)
    (w' : {w' : M.W // M.R w w'}) :
    Env.boxPush hsub' (env.extend xv hxv a) w' = Env.boxPush hsub env w' := by
  funext p hp
  have hne : (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ≠ xv := by
    rintro rfl; simp [VarType.isBox] at hxvBox
  simp only [Env.boxPush, Env.extend, dif_neg hne]

/-- Shape-based variant of `boxPush_extend_notBox`: a `boxPush` read key is always
    `⟨_, _.VTypeBox⟩`, so only the constructor SHAPE of `xv.2` matters.  This also covers
    product types, which may have `isBox = true` (when a component is a box) yet are never
    `VTypeBox`-shaped. -/
theorem boxPush_extend_notBoxShape (M : RModel σ) {V_inner W : VarCtx} {w : M.W}
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hsub' : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert xv W hxv).1)
    (env : M.Env W w) (a : M.interp xv.2 w)
    (hshape : ∀ U : VarType, xv.2 ≠ VarType.VTypeBox U)
    (w' : {w' : M.W // M.R w w'}) :
    Env.boxPush hsub' (env.extend xv hxv a) w' = Env.boxPush hsub env w' := by
  funext p hp
  have hne : (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ≠ xv := by
    rintro rfl; exact hshape p.2 rfl
  simp only [Env.boxPush, Env.extend, dif_neg hne]

/-- Extending by a **box**-typed variable pushes to extending the inner `boxPush` env by its
    `necEval`'d value. -/
theorem boxPush_extend_box (M : RModel σ) {V_inner W : VarCtx} {w : M.W}
    {xs : VarSymb} {U' : VarType} {hxs : xs ∉ VarCtx_to_VarSymbs W}
    (hxs_inner : xs ∉ VarCtx_to_VarSymbs V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hsub' : (VarCtx_box (VarCtx_insert ⟨xs, U'⟩ V_inner hxs_inner)).1
             ⊆ (VarCtx_insert ⟨xs, U'.VTypeBox⟩ W hxs).1)
    (env : M.Env W w) (a : M.interp U'.VTypeBox w) (w' : {w' : M.W // M.R w w'}) :
    Env.boxPush hsub' (env.extend ⟨xs, U'.VTypeBox⟩ hxs a) w'
      = (Env.boxPush hsub env w').extend ⟨xs, U'⟩ hxs_inner (M.necEval a w') := by
  funext p hp
  simp only [Env.boxPush, Env.extend]
  by_cases hpeq : p = (⟨xs, U'⟩ : VarSymb × VarType)
  · subst hpeq; rw [dif_pos rfl, dif_pos rfl]
  · obtain ⟨pv, pT⟩ := p
    have hne : (⟨pv, pT.VTypeBox⟩ : VarSymb × VarType) ≠ ⟨xs, U'.VTypeBox⟩ := by
      intro h; rw [Prod.mk.injEq] at h
      exact hpeq (Prod.ext_iff.mpr ⟨h.1, VarType.VTypeBox.inj h.2⟩)
    rw [dif_neg hne, dif_neg hpeq]

/-- Extending the env by a variable whose symbol is **not in `V_inner`** leaves `boxPush`
    unchanged (regardless of the variable's type) — the boxed lookups `⟨p.1, p.2.VTypeBox⟩`
    have `p.1 ∈ V_inner`, so never equal `xv`. -/
theorem boxPush_extend_notin (M : RModel σ) {V_inner W : VarCtx} {w : M.W}
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hsub' : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert xv W hxv).1)
    (env : M.Env W w) (a : M.interp xv.2 w) (hnotin : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (w' : {w' : M.W // M.R w w'}) :
    Env.boxPush hsub' (env.extend xv hxv a) w' = Env.boxPush hsub env w' := by
  funext p hp
  have hne : (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ≠ xv := by
    intro h
    rw [Prod.mk.injEq] at h
    exact hnotin (h.1 ▸ Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  simp only [Env.boxPush, Env.extend, dif_neg hne]

/-- Looking up a variable already in `V` in an extended environment ignores the extension. -/
theorem Env.extend_apply_ne {M : RModel σ} {V : VarCtx} {w : M.W} (env : M.Env V w)
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs V} (aa : M.interp xv.2 w)
    {q : VarSymb × VarType} (hq : q ∈ (VarCtx_insert xv V hxv).1) (hqV : q ∈ V.1) :
    (env.extend xv hxv aa) q hq = env q hqV := by
  have hne : q ≠ xv := fun h => hxv (h ▸ Finset.mem_image.mpr ⟨q, hqV, rfl⟩)
  simp only [Env.extend, dif_neg hne]

/-- Cast on the term alone: transport the environment the other way. -/
theorem interpTerm_cast_term (M : RModel σ) {W1 W2 : VarCtx} (h : W1 = W2) {S : VarType}
    (t : Term σ W1 S) (w : M.W) (env : M.Env W2 w) :
    M.interpTerm (h ▸ t) w env = M.interpTerm t w (h.symm ▸ env) := by subst h; rfl

/-- Two independent `Env.extend`s commute (across the `insert_comm` context cast). -/
theorem Env.extend_comm {M : RModel σ} {V : VarCtx} {w : M.W} (env : M.Env V w)
    {a b : VarSymb × VarType}
    (ha : a.1 ∉ VarCtx_to_VarSymbs V) (hb : b.1 ∉ VarCtx_to_VarSymbs V)
    (hb' : b.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert a V ha))
    (ha' : a.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert b V hb))
    (va : M.interp a.2 w) (vb : M.interp b.2 w)
    (h : VarCtx_insert b (VarCtx_insert a V ha) hb' = VarCtx_insert a (VarCtx_insert b V hb) ha') :
    h ▸ ((env.extend a ha va).extend b hb' vb) = (env.extend b hb vb).extend a ha' va := by
  funext p hp
  rw [Env_transport_apply]
  simp only [Env.extend]
  by_cases hpa : p = a
  · subst hpa
    have hpb : ¬ (p = b) := by
      rintro rfl; exact hb' (Finset.mem_image.mpr ⟨_, Finset.mem_insert_self _ _, rfl⟩)
    simp [hpb]
  · by_cases hpb : p = b
    · subst hpb; simp [hpa]
    · simp [hpa, hpb]

/-! ### Pair-elim distribution is semantics-preserving

`Term.pairElim` (the η-normaliser that distributes a `pair_elim` inward through the term structure,
stopping at modal boundaries) denotes the same as the `Term.pair_elim` *constructor* (the direct
product recursor).  This is THE linchpin: it unlocks the `VTypeProd` cases of `ctx_ext`/`rename`
(where `Term.ctx_ext`/`rename` of a modal term over a product-typed variable produces a `pairElim`),
and the `Proof.pair_elim` soundness rule. -/
mutual
theorem interpTerm_pairElim (M : RModel σ) {V W₁ W₂ : VarCtx} {S : VarType}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (body : Term σ W₁ S) (w : M.W) (env : M.Env W₂ w) :
    M.interpTerm (Term.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body) w env
      = M.interpTerm (Term.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body) w env := by
  -- The RHS is (by the `interpTerm.pair_elim` clause) `interpTerm body (w₁eq ▸ unpairEnv env)`.
  rw [show M.interpTerm (Term.pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body) w env
        = M.interpTerm body w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) from by
        simp only [RModel.interpTerm]]
  match body with
  | .unit => simp only [Term.pairElim, RModel.interpTerm]
  | .var ⟨ww, hw⟩ =>
      have hv₁W₁ : v₁ ∈ W₁.1 := by rw [← w₁eq]; exact Finset.mem_insert_self _ _
      have hv₂W₁ : v₂ ∈ W₁.1 := by
        rw [← w₁eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      simp only [RModel.interpTerm]
      rw [Env_transport_apply]
      by_cases h1 : ww = v₁.1
      · have hv₁2 : v₁.2 = VarType.Var := W₁.2 v₁ hv₁W₁ ⟨ww, .Var⟩ hw h1.symm
        simp [Term.pairElim, dif_pos h1, RModel.interpTerm, Env_transport_apply,
          Env.unpairEnv, h1, hv₁2, Prod.ext_iff]
      · by_cases h2 : ww = v₂.1
        · have hv₂2 : v₂.2 = VarType.Var := W₁.2 v₂ hv₂W₁ ⟨ww, .Var⟩ hw h2.symm
          have hne : ¬ (v₂.1 = v₁.1) := fun h => hv₁v₂ h.symm
          simp [Term.pairElim, dif_neg h1, dif_pos h2, RModel.interpTerm, Env_transport_apply,
            Env.unpairEnv, h2, hv₂2, hne, Prod.ext_iff]
        · simp [Term.pairElim, dif_neg h1, dif_neg h2, RModel.interpTerm, Env_transport_apply,
            Env.unpairEnv, h1, h2, Prod.ext_iff]
  | .func f =>
      simp only [Term.pairElim, RModel.interpTerm]
      exact interpFunc_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq f w env Fin.elim0
  | .pair t₁ t₂ =>
      simp only [Term.pairElim, RModel.interpTerm]
      rw [interpTerm_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t₁ w env,
          interpTerm_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t₂ w env]
      simp only [RModel.interpTerm]
  | .boxterm tt hsub hnbe => simp only [Term.pairElim, RModel.interpTerm]
  | .diaterm x hx tt hsub hnbe => simp only [Term.pairElim, RModel.interpTerm]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => simp only [Term.pairElim, RModel.interpTerm]

theorem interpFunc_pairElim (M : RModel σ) {V W₁ W₂ : VarCtx} {n : ℕ}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (f : Func σ W₁ n) (w : M.W) (env : M.Env W₂ w) (args : Fin n → M.D w) :
    M.interpFunc (Func.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq f) w env args
      = M.interpFunc f w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) args := by
  match f with
  | .F hr => simp only [Func.pairElim, RModel.interpFunc]
  | .eval g t =>
      simp only [Func.pairElim, RModel.interpFunc]
      rw [interpFunc_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq g w env,
          show M.interpTerm (Term.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t) w env
            = M.interpTerm t w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) from by
            rw [interpTerm_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t w env];
            simp only [RModel.interpTerm]]
end

/-- Relation-level pair-elim distribution (base for the `atom` WFF case; via `interpTerm_pairElim`). -/
theorem interpRel_pairElim (M : RModel σ) {V W₁ W₂ : VarCtx} {n : ℕ}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (R : Rel σ W₁ n) (w : M.W) (env : M.Env W₂ w) (args : Fin n → M.D w) :
    M.interpRel (Rel.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq R) w env args
      = M.interpRel R w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) args := by
  induction R with
  | R hr => simp only [Rel.pairElim, RModel.interpRel]
  | eval R' t ih =>
      simp only [Rel.pairElim, RModel.interpRel]
      rw [show M.interpTerm (Term.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t) w env
            = M.interpTerm t w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) from by
            rw [interpTerm_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t w env];
            simp only [RModel.interpTerm]]
      exact ih _

/-- A `VarCtx` is a `PSigma` with a `Prop` coherence field, so equality follows from equality of the
    underlying `Finset` (public re-derivation of the private `VarCtx_ext`). -/
theorem VarCtx_ext' {V W : VarCtx} (h : V.1 = W.1) : V = W := by
  obtain ⟨V1, V2⟩ := V; obtain ⟨W1, W2⟩ := W; simp only at h; subst h; rfl

/-- The env-level content of the product-`pair_elim` peel: `unpairEnv` splitting the env at a
    product var `z = ⟨a1,a2⟩` (and re-transported to the nested-`insert` order) *is* the two
    successive `extend`s by the components.  Used to close the `VTypeProd`-modal `ctx_ext`/`rename`
    arms (whose `Term.ctx_ext`/`rename` re-pairs the split via `Term.pairElim`). -/
theorem unpairEnv_transport_eq (M : RModel σ) {V : VarCtx} {w : M.W}
    {v₁ v₂ : VarSymb × VarType} {z : VarSymb}
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (hv₂' : v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₁ V hv₁))
    (h_swap : VarCtx_insert v₂ (VarCtx_insert v₁ V hv₁) hv₂'
             = VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂)
    (env : M.Env V w) (a1 : M.interp v₁.2 w) (a2 : M.interp v₂.2 w) :
    (h_swap.symm ▸ Env.unpairEnv hv₁v₂
          (rfl : VarCtx_insert ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ V hz = _)
          (env.extend ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ hz (a1, a2)))
      = (env.extend v₁ hv₁ a1).extend v₂ hv₂' a2 := by
  have hzs : (⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
      ∈ (VarCtx_insert ⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ V hz).1 := Finset.mem_insert_self _ _
  have hv₁ne : ¬ (v₁ = v₂) := fun h => hv₁v₂ (congrArg Prod.fst h)
  funext p hp
  rw [Env_transport_apply]
  by_cases h2 : p = v₂
  · subst h2
    rw [Env.unpairEnv_apply_v₂ (hzs := hzs)]
    simp [Env.extend]
  · by_cases h1 : p = v₁
    · subst h1
      rw [Env.unpairEnv_apply_v₁ (hzs := hzs)]
      simp [Env.extend, hv₁ne]
    · have hpV : p ∈ V.1 := by
        rcases Finset.mem_insert.mp hp with h | h
        · exact absurd h h2
        · exact (Finset.mem_insert.mp h).resolve_left h1
      have hpz : p ≠ (⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) := by
        rintro rfl; exact hz (Finset.mem_image.mpr ⟨_, hpV, rfl⟩)
      rw [Env.unpairEnv_apply_other (h1 := h1) (h2 := h2)
            (hqW := Finset.mem_insert_of_mem hpV)]
      simp only [Env.extend, dif_neg h1, dif_neg h2, dif_neg hpz]

/-! ### Term/Func/Rel-level `ctx_ext` invariance (base for the `eq`/`atom` WFF cases)

Non-modal cases port verbatim from `Soundness2.lean` (only `GModel` → `RModel`).  The modal cases
(`boxterm`/`diaterm`) go through `nec_inj` + box-β (`necEval_interpTermNec`) / `mapPos`-congruence
rather than GModel's `necIntro`.

⭐TERMINATION (the `_fuel` parameter): the VTypeProd arms peel `ctx_ext ⟨w2,B⟩ (ctx_ext ⟨w1,A⟩ t)`,
whose `numNodes` GROWS — only the weakening type shrinks (`A,B < A×B`).  A measure mentioning
`sizeOf xv.2` cannot survive the `obtain ⟨xs,xt⟩ := xv` the proof bodies need (the measure is
elaborated outside the tactic block, so `cases` never refines it), and keeping `xv` abstract makes
`Term.ctx_ext` irreducible (`simp` loops).  Fix: an explicit fuel bound `k` with
`hk : sizeOf xv.2 ≤ k` and measure `(k, numNodes)` — `k` is a plain variable the measure sees
directly, while `hk` IS refined by `cases` and supplies the arithmetic (`sizeOf A ≤ k-1`, `0 < k`)
that `decreasing_by`'s `omega` needs.  Public wrappers instantiate `k := sizeOf xv.2`. -/
mutual
theorem interpTerm_ctx_ext_fuel (M : RModel σ) (k : ℕ) {V : VarCtx} (xv : VarSymb × VarType)
    (hk : sizeOf xv.2 ≤ k) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S)
    (w : M.W) (env : M.Env V w) (a : M.interp xv.2 w) :
    M.interpTerm (Term.ctx_ext xv hxv t) w (env.extend xv hxv a) = M.interpTerm t w env := by
  match t with
  | .var ⟨v, hv⟩ =>
      have hne : (⟨v, VarType.Var⟩ : VarSymb × VarType) ≠ xv := by
        rintro rfl; exact hxv (Finset.mem_image.mpr ⟨_, hv, rfl⟩)
      simp only [Term.ctx_ext, RModel.interpTerm, Env.extend, dif_neg hne]
  | .func f =>
      simp only [Term.ctx_ext, RModel.interpTerm]
      exact interpFunc_ctx_ext_fuel M k xv hk hxv f w env a Fin.elim0
  | .unit => simp only [Term.ctx_ext, RModel.interpTerm]
  | .pair t1 t2 =>
      simp only [Term.ctx_ext, RModel.interpTerm]
      rw [interpTerm_ctx_ext_fuel M k xv hk hxv t1 w env a,
          interpTerm_ctx_ext_fuel M k xv hk hxv t2 w env a]
  | @Term.boxterm _ V_inner S_inner _ tt hsub hnbe =>
      -- `obtain`+`cases xt` reduces `ctx_ext` cleanly (xt concrete ⇒ no simp loop); the measure
      -- `(k, numNodes)` is untouched by the destructuring, and `hk` is refined per branch.  See the
      -- mutual's doc comment for why the fuel decouples the measure from `xv`.
      obtain ⟨xs, xt⟩ := xv
      cases xt with
      | Var | VTypeOne | VTypeDia _ =>
          -- non-box `xv`: `ctx_ext` leaves `tt` unchanged, so both sides are the same box-lift over
          -- environments agreeing on the box-variables (`extend` by a non-box var is invisible).
          simp only [Term.ctx_ext, RModel.interpTerm]
          refine interpTermNecStk_congr M (.box .hole) _ _ tt w _ env (fun p hp => ?_)
          exact Env.extend_apply_ne env a _ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
      | VTypeBox U' =>
          -- box `xv = ⟨xs, U'.box⟩`: `ctx_ext` weakens the inner `tt` by `⟨xs, U'⟩`.
          have hkU' : sizeOf U' ≤ k := by
            have h : sizeOf (VarType.VTypeBox U') ≤ k := hk
            simp +arith at h; omega
          have hxv_inner : xs ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in_inner
            apply hxv
            obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
            cases q with
            | mk qv qT =>
              exact Finset.mem_image.mpr
                ⟨_, hsub (Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩), hq_eq⟩
          simp only [Term.ctx_ext]
          rw [interpTerm_boxterm, interpTerm_boxterm]
          apply M.nec_inj
          funext w'
          rw [necEval_interpTermNec, necEval_interpTermNec,
              boxPush_extend_box M hxv_inner hsub _ env a w']
          exact interpTerm_ctx_ext_fuel M k ⟨xs, U'⟩ hkU' hxv_inner tt w'.1
            (Env.boxPush hsub env w') (M.necEval a w')
      | VTypeProd A B =>
          -- `Term.ctx_ext ⟨xs,A×B⟩ boxterm` splits the product into fresh `⟨w1,A⟩,⟨w2,B⟩`,
          -- ctx_ext's by each, and re-pairs via `Term.pairElim`; reduce (unfold+dsimp), send the
          -- pairElim through `interpTerm_pairElim` to the `unpairEnv`, then peel the two weakenings
          -- at fuel `k-1` (their terms' numNodes GREW, but `sizeOf A, sizeOf B ≤ k-1` from `hk`).
          have hAB : sizeOf A + sizeOf B + 1 ≤ k := by
            have h : sizeOf (VarType.VTypeProd A B) ≤ k := hk
            simp +arith at h; omega
          have hkA : sizeOf A ≤ k - 1 := by omega
          have hkB : sizeOf B ≤ k - 1 := by omega
          have hkpos : 0 < k := by omega
          obtain ⟨a1, a2⟩ := a
          unfold Term.ctx_ext
          dsimp only
          set av := VarCtx_to_VarSymbs V ∪ {xs} ∪ (tt.boxterm hsub hnbe).boundVars with havdef
          set w1 := VarSymb.fresh av with hw1def
          set w2 := VarSymb.fresh (insert w1 av) with hw2def
          have hw1_V : w1 ∉ VarCtx_to_VarSymbs V := fun h =>
            VarSymb.fresh_not_mem av (Finset.mem_union_left _ (Finset.mem_union_left _ h))
          have hw2_iav : w2 ∉ insert w1 av := VarSymb.fresh_not_mem (insert w1 av)
          have hw2_V : w2 ∉ VarCtx_to_VarSymbs V := fun h =>
            hw2_iav (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
          have hw1w2 : w1 ≠ w2 := fun h => hw2_iav (h ▸ Finset.mem_insert_self _ _)
          have hw2_V1 : w2 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨w1, A⟩ V hw1_V) :=
            not_mem_VarSymbs_insert (fun h => hw1w2 h.symm) hw2_V
          have h_swap : VarCtx_insert ⟨w2, B⟩ (VarCtx_insert ⟨w1, A⟩ V hw1_V) hw2_V1
              = VarCtx_insert_twice ⟨w1, A⟩ ⟨w2, B⟩ V hw1_V hw2_V hw1w2 := by
            apply VarCtx_ext'
            change insert (⟨w2, B⟩ : VarSymb × VarType) (insert ⟨w1, A⟩ V.1)
                = insert ⟨w1, A⟩ (insert ⟨w2, B⟩ V.1)
            exact Finset.insert_comm _ _ _
          rw [interpTerm_pairElim M]
          simp only [RModel.interpTerm]
          rw [interpTerm_cast_term,
              unpairEnv_transport_eq M hw1_V hw2_V hw1w2 hxv hw2_V1 h_swap env a1 a2,
              interpTerm_ctx_ext_fuel M (k - 1) ⟨w2, B⟩ hkB hw2_V1 _ w
                (env.extend ⟨w1, A⟩ hw1_V a1) a2,
              interpTerm_ctx_ext_fuel M (k - 1) ⟨w1, A⟩ hkA hw1_V (tt.boxterm hsub hnbe)
                w env a1]
          simp only [RModel.interpTerm]
  | @Term.diaterm _ V_inner S_inner _ xv_t hxv_t tt hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      cases xt with
      | Var | VTypeOne | VTypeDia _ =>
          -- non-box `xv`: `ctx_ext` leaves the diaterm's `tt`/witness unchanged, so both sides are
          -- the same `mapPos` — fibre function equal via `boxPush_extend_notBox`, witness via
          -- `Env.extend_apply_ne`.
          simp only [Term.ctx_ext, RModel.interpTerm]
          congr 1
          · funext w' v
            rw [boxPush_extend_notBox M (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _
                  env a rfl]
          · exact Env.extend_apply_ne env a _ (hsub (Finset.mem_insert_self _ _))
      | VTypeBox U' =>
          have hkU' : sizeOf U' ≤ k := by
            have h : sizeOf (VarType.VTypeBox U') ≤ k := hk
            simp +arith at h; omega
          have hxv_inner : xs ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in_inner; apply hxv
            obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
            cases q with
            | mk qv qT =>
              have hbox_in_dia : (⟨qv, qT.VTypeBox⟩ : VarSymb × VarType)
                  ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
                rw [VarCtx_dia_fst]
                exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩)
              exact Finset.mem_image.mpr ⟨_, hsub hbox_in_dia, hq_eq⟩
          have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 :=
            hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)
          have hxv_ne : xs ≠ xv_t.1 := by
            intro h; apply hxv; rw [h]; exact Finset.mem_image.mpr ⟨_, hwit, rfl⟩
          have hxv_outer : xs ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_t V_inner hxv_t) :=
            not_mem_VarSymbs_insert hxv_ne hxv_inner
          simp only [Term.ctx_ext, RModel.interpTerm]
          congr 1
          · funext w' v
            rw [boxPush_extend_box M hxv_inner
                  (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a,
                interpTerm_cast_term, Env.extend_comm,
                interpTerm_ctx_ext_fuel M k ⟨xs, U'⟩ hkU' hxv_outer tt _ _ _]
          · exact Env.extend_apply_ne env a _ hwit
      | VTypeProd A B =>
          -- Identical shape to the boxterm-VTypeProd arm (v8 marks the syntactic branches
          -- "identical"): reduce, distribute via `interpTerm_pairElim`, rewrite the env via
          -- `unpairEnv_transport_eq`, peel the two weakenings at fuel `k-1`.
          have hAB : sizeOf A + sizeOf B + 1 ≤ k := by
            have h : sizeOf (VarType.VTypeProd A B) ≤ k := hk
            simp +arith at h; omega
          have hkA : sizeOf A ≤ k - 1 := by omega
          have hkB : sizeOf B ≤ k - 1 := by omega
          have hkpos : 0 < k := by omega
          obtain ⟨a1, a2⟩ := a
          unfold Term.ctx_ext
          dsimp only
          set av := VarCtx_to_VarSymbs V ∪ {xs}
              ∪ (Term.diaterm xv_t hxv_t tt hsub hnbe).boundVars with havdef
          set w1 := VarSymb.fresh av with hw1def
          set w2 := VarSymb.fresh (insert w1 av) with hw2def
          have hw1_V : w1 ∉ VarCtx_to_VarSymbs V := fun h =>
            VarSymb.fresh_not_mem av (Finset.mem_union_left _ (Finset.mem_union_left _ h))
          have hw2_iav : w2 ∉ insert w1 av := VarSymb.fresh_not_mem (insert w1 av)
          have hw2_V : w2 ∉ VarCtx_to_VarSymbs V := fun h =>
            hw2_iav (Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
          have hw1w2 : w1 ≠ w2 := fun h => hw2_iav (h ▸ Finset.mem_insert_self _ _)
          have hw2_V1 : w2 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨w1, A⟩ V hw1_V) :=
            not_mem_VarSymbs_insert (fun h => hw1w2 h.symm) hw2_V
          have h_swap : VarCtx_insert ⟨w2, B⟩ (VarCtx_insert ⟨w1, A⟩ V hw1_V) hw2_V1
              = VarCtx_insert_twice ⟨w1, A⟩ ⟨w2, B⟩ V hw1_V hw2_V hw1w2 := by
            apply VarCtx_ext'
            change insert (⟨w2, B⟩ : VarSymb × VarType) (insert ⟨w1, A⟩ V.1)
                = insert ⟨w1, A⟩ (insert ⟨w2, B⟩ V.1)
            exact Finset.insert_comm _ _ _
          rw [interpTerm_pairElim M]
          simp only [RModel.interpTerm]
          rw [interpTerm_cast_term,
              unpairEnv_transport_eq M hw1_V hw2_V hw1w2 hxv hw2_V1 h_swap env a1 a2,
              interpTerm_ctx_ext_fuel M (k - 1) ⟨w2, B⟩ hkB hw2_V1 _ w
                (env.extend ⟨w1, A⟩ hw1_V a1) a2,
              interpTerm_ctx_ext_fuel M (k - 1) ⟨w1, A⟩ hkA hw1_V
                (Term.diaterm xv_t hxv_t tt hsub hnbe) w env a1]
          simp only [RModel.interpTerm]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => sorry
termination_by (k, t.numNodes)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; (try simp only [Term.numNodes, Func.numNodes]); omega)
    | (apply Prod.Lex.left; omega)

theorem interpFunc_ctx_ext_fuel (M : RModel σ) (k : ℕ) {V : VarCtx} (xv : VarSymb × VarType)
    (hk : sizeOf xv.2 ≤ k) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {n : ℕ} (f : Func σ V n)
    (w : M.W) (env : M.Env V w) (a : M.interp xv.2 w) (args : Fin n → M.D w) :
    M.interpFunc (Func.ctx_ext xv hxv f) w (env.extend xv hxv a) args
      = M.interpFunc f w env args := by
  match f with
  | .F hr => simp only [Func.ctx_ext, RModel.interpFunc]
  | .eval g t =>
      simp only [Func.ctx_ext, RModel.interpFunc]
      rw [interpTerm_ctx_ext_fuel M k xv hk hxv t w env a]
      exact interpFunc_ctx_ext_fuel M k xv hk hxv g w env a _
termination_by (k, f.numNodes)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; (try simp only [Term.numNodes, Func.numNodes]); omega)
end

/-- `ctx_ext` invariance (public form — instantiates the fuel at `sizeOf xv.2`). -/
theorem interpTerm_ctx_ext (M : RModel σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S)
    (w : M.W) (env : M.Env V w) (a : M.interp xv.2 w) :
    M.interpTerm (Term.ctx_ext xv hxv t) w (env.extend xv hxv a) = M.interpTerm t w env :=
  interpTerm_ctx_ext_fuel M (sizeOf xv.2) xv le_rfl hxv t w env a

/-- `ctx_ext` invariance for `Func` (public form). -/
theorem interpFunc_ctx_ext (M : RModel σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {n : ℕ} (f : Func σ V n)
    (w : M.W) (env : M.Env V w) (a : M.interp xv.2 w) (args : Fin n → M.D w) :
    M.interpFunc (Func.ctx_ext xv hxv f) w (env.extend xv hxv a) args
      = M.interpFunc f w env args :=
  interpFunc_ctx_ext_fuel M (sizeOf xv.2) xv le_rfl hxv f w env a args

/-- Relation-level `ctx_ext` invariance (base for the `atom` case; via `interpTerm_ctx_ext`). -/
theorem interpRel_ctx_ext (M : RModel σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {n : ℕ} (R : Rel σ V n)
    (w : M.W) (env : M.Env V w) (a : M.interp xv.2 w) (args : Fin n → M.D w) :
    M.interpRel (Rel.ctx_ext xv hxv R) w (env.extend xv hxv a) args
      = M.interpRel R w env args := by
  induction R with
  | R hr => simp only [Rel.ctx_ext, RModel.interpRel]
  | eval R' t ih =>
      simp only [Rel.ctx_ext, RModel.interpRel]
      rw [interpTerm_ctx_ext M xv hxv t w env a]
      exact ih _

/-! ### Term/Func/Rel-level α-rename invariance (base for the `all`/`ex` collision WFF cases)

Non-modal cases port verbatim from `Soundness2.lean`.  Modal cases (`boxterm`/`diaterm` with a
box-typed `repl_type`, and the `diaterm` witness rebind) are COMPLETE — the `erase`/`insert`
context gymnastics port verbatim with the `nec_inj`+box-β / `pos_inj`+`mapPos_eval` swaps;
the rebind case delays its local `subst` until after the recursive call is emitted (see inline
note).  Only the pair sector is deferred (`sorry`). -/
mutual
theorem interpTerm_rename (M : RModel σ) {old new : VarSymb} {repl_type : VarType}
    {V W : VarCtx} {S : VarType}
    (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (t : Term σ W S) (new_not_bound : new ∉ Term.boundVars t)
    (w : M.W) (env : M.Env V w) (val : M.interp repl_type w) :
    M.interpTerm (Term.rename old new repl_type V W S
        old_fresh new_fresh Wdef t new_not_bound) w (env.extend ⟨new, repl_type⟩ new_fresh val)
      = M.interpTerm t w (Wdef ▸ (env.extend ⟨old, repl_type⟩ old_fresh val)) := by
  match t, new_not_bound with
  | .var ⟨v, veq⟩, _ =>
      subst Wdef
      by_cases h_v_old : v = old
      · subst h_v_old
        have hrepl : repl_type = .Var := by
          rcases Finset.mem_insert.mp veq with heq | hin
          · exact (Prod.mk.inj heq).2.symm
          · exact absurd (Finset.mem_image.mpr ⟨_, hin, rfl⟩) old_fresh
        subst hrepl
        simp [Term.rename, RModel.interpTerm, Env.extend]
      · have hv_V : (⟨v, .Var⟩ : VarSymb × VarType) ∈ V.1 := by
          rcases Finset.mem_insert.mp veq with heq | hin
          · exact absurd (congrArg Prod.fst heq) h_v_old
          · exact hin
        have hv_new : v ≠ new :=
          fun h => new_fresh (h ▸ Finset.mem_image.mpr ⟨_, hv_V, rfl⟩)
        have hne_new : (⟨v, .Var⟩ : VarSymb × VarType) ≠ ⟨new, repl_type⟩ :=
          fun h => hv_new (congrArg Prod.fst h)
        have hne_old : (⟨v, .Var⟩ : VarSymb × VarType) ≠ ⟨old, repl_type⟩ :=
          fun h => h_v_old (congrArg Prod.fst h)
        simp only [Term.rename, dif_neg h_v_old, RModel.interpTerm, Env.extend,
          dif_neg hne_new, dif_neg hne_old]
  | .func f, nnb =>
      simp only [Term.rename, RModel.interpTerm]
      exact interpFunc_rename M old_fresh new_fresh Wdef f nnb w env val Fin.elim0
  | .unit, _ => subst Wdef; simp only [Term.rename, RModel.interpTerm]
  | .pair t1 t2, nnb =>
      have h1 : new ∉ Term.boundVars t1 := fun h => nnb (Finset.mem_union_left _ h)
      have h2 : new ∉ Term.boundVars t2 := fun h => nnb (Finset.mem_union_right _ h)
      simp only [Term.rename, RModel.interpTerm]
      rw [interpTerm_rename M old_fresh new_fresh Wdef t1 h1 w env val,
          interpTerm_rename M old_fresh new_fresh Wdef t2 h2 w env val]
  | @Term.boxterm _ V_inner S_inner _ tt hsub hnbe, nnb =>
      subst Wdef
      rcases repl_type with _ | innertype | diatype | _ | ⟨A, B⟩
      case VTypeBox =>
          -- box `repl_type = innertype.box`: `hnbe` forces `⟨old, innertype⟩ ∈ V_inner`, so
          -- `Term.rename` recurses into `tt`; box β + `nec_inj` drop to `interpTerm`, then the IH
          -- (`interpTerm_rename`) over the `erase` context, and an old-side env reconciliation.
          have h : (⟨old, innertype⟩ : VarSymb × VarType) ∈ V_inner.1 := by
            have hmem := hnbe ⟨old, innertype.VTypeBox⟩ (Finset.mem_insert_self _ _) rfl
            rcases Finset.mem_image.mp hmem with ⟨⟨v, Sv⟩, hv, hveq⟩
            simp only [Prod.mk.injEq] at hveq
            obtain ⟨rfl, hSeq⟩ := hveq
            rwa [VarType.VTypeBox.inj hSeq] at hv
          have oldinner_fresh : old ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) :=
            VarCtx_erase_fresh h
          have hsubV : (VarCtx_box (VarCtx_erase V_inner ⟨old, innertype⟩)).1 ⊆ V.1 := by
            intro y hy
            have hy_inner : y ∈ (VarCtx_box V_inner).1 := by
              rcases Finset.mem_image.mp hy with ⟨w0, hvin, hveq⟩
              exact Finset.mem_image.mpr ⟨w0, Finset.erase_subset _ _ hvin, hveq⟩
            rcases Finset.mem_insert.mp (hsub hy_inner) with rfl | hV
            · rcases Finset.mem_image.mp hy with ⟨⟨v, Sv⟩, hvin, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              obtain ⟨hv_eq, hSv⟩ := hveq
              rw [hv_eq, VarType.VTypeBox.inj hSv] at hvin
              exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, innertype⟩, hvin, rfl⟩)).elim
            · exact hV
          have newinner_fresh : new ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨w0, hvin, hveq⟩
            exact new_fresh (Finset.mem_image.mpr ⟨⟨w0.1, w0.2.VTypeBox⟩,
              hsubV (Finset.mem_image.mpr ⟨w0, hvin, rfl⟩), hveq⟩)
          have innerCtx_eq : V_inner
              = VarCtx_insert ⟨old, innertype⟩ (VarCtx_erase V_inner ⟨old, innertype⟩)
                  oldinner_fresh :=
            (VarCtx_insert_erase h oldinner_fresh).symm
          simp only [Term.rename, dif_pos h]
          rw [interpTerm_boxterm, interpTerm_boxterm]
          apply M.nec_inj
          funext w'
          rw [necEval_interpTermNec, necEval_interpTermNec,
              boxPush_extend_box M (xs := new) (U' := innertype) newinner_fresh hsubV _ env val w',
              interpTerm_rename M oldinner_fresh newinner_fresh innerCtx_eq tt nnb w'.1
                (Env.boxPush hsubV env w') (M.necEval val w')]
          congr 1
          funext p hp
          rw [Env_transport_apply]
          simp only [Env.boxPush, Env.extend]
          by_cases hpo : p = (⟨old, innertype⟩ : VarSymb × VarType)
          · subst hpo
            rw [dif_pos rfl, dif_pos rfl]
          · obtain ⟨pv, pT⟩ := p
            have hne : (⟨pv, pT.VTypeBox⟩ : VarSymb × VarType) ≠ ⟨old, innertype.VTypeBox⟩ := by
              intro heq
              rw [Prod.mk.injEq] at heq
              exact hpo (Prod.ext heq.1 (VarType.VTypeBox.inj heq.2))
            rw [dif_neg hne, dif_neg hpo]
      case VTypeProd =>
          -- product `repl_type = A×B`: `Term.rename` passes `tt` through — a product-typed var is
          -- never `VTypeBox`-SHAPED, so `boxPush` ignores it on both sides (via the shape-based
          -- lemma: products CONTAINING boxes have `isBox = true`, so the `isBox = false` variant
          -- does not apply; `hnbe` in fact excludes those, but the shape argument needs neither).
          have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro x x_in
            rcases Finset.mem_insert.mp (hsub x_in) with xeq | xV
            · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
              rw [← hveq] at xeq
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
            · exact xV
          simp only [Term.rename]
          rw [interpTerm_boxterm, interpTerm_boxterm]
          apply M.nec_inj
          funext w'
          rw [necEval_interpTermNec, necEval_interpTermNec]
          congr 1
          refine (boxPush_extend_notBoxShape (xv := ⟨new, _⟩) M hsubV _ env val
              (fun _ h => VarType.noConfusion h) w').trans
            (boxPush_extend_notBoxShape (xv := ⟨old, _⟩) M hsubV _ env val
              (fun _ h => VarType.noConfusion h) w').symm
      all_goals
        -- non-box `repl_type`: `Term.rename` passes `tt` through; box β + `nec_inj` drop to
        -- `interpTerm`, and the renamed non-box variable is invisible to `boxPush` on both sides.
        have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
          intro x x_in
          rcases Finset.mem_insert.mp (hsub x_in) with xeq | xV
          · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
            rw [← hveq] at xeq
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
          · exact xV
        simp only [Term.rename]
        rw [interpTerm_boxterm, interpTerm_boxterm]
        apply M.nec_inj
        funext w'
        rw [necEval_interpTermNec, necEval_interpTermNec]
        congr 1
        refine (boxPush_extend_notBox (xv := ⟨new, _⟩) M hsubV _ env val ?_ w').trans
          (boxPush_extend_notBox (xv := ⟨old, _⟩) M hsubV _ env val ?_ w').symm
        · rfl
        · rfl
  | @Term.diaterm _ V_inner S_inner _ xv_t hxv_t tt hsub hnbe, nnb =>
      subst Wdef
      rcases repl_type with _ | innertype | diatype | _ | ⟨A, B⟩
      case VTypeBox =>
          have h : (⟨old, innertype⟩ : VarSymb × VarType) ∈ V_inner.1 := by
            have hmem := hnbe ⟨old, innertype.VTypeBox⟩ (Finset.mem_insert_self _ _) rfl
            rw [VarCtx_dia_fst] at hmem
            rcases Finset.mem_insert.mp hmem with heq | hbox
            · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
            · rcases Finset.mem_image.mp hbox with ⟨⟨v, Sv⟩, hv, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              obtain ⟨rfl, hSeq⟩ := hveq
              rwa [VarType.VTypeBox.inj hSeq] at hv
          have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
            rcases Finset.mem_insert.mp
              (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)) with heq | hV
            · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
            · exact hV
          have oldinner_fresh : old ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) :=
            VarCtx_erase_fresh h
          have hx_ne_old : xv_t.1 ≠ old := fun heq =>
            hxv_t (Finset.mem_image.mpr ⟨⟨old, innertype⟩, h, heq.symm⟩)
          have hx' : xv_t.1 ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) :=
            fun hmem => hxv_t (VarCtx_to_VarSymbs_erase_subset hmem)
          have hsubV : (VarCtx_box (VarCtx_erase V_inner ⟨old, innertype⟩)).1 ⊆ V.1 := by
            intro y hy
            have hy_inner : y ∈ (VarCtx_box V_inner).1 := by
              rcases Finset.mem_image.mp hy with ⟨w0, hvin, hveq⟩
              exact Finset.mem_image.mpr ⟨w0, Finset.erase_subset _ _ hvin, hveq⟩
            have hy_dia : y ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hy_inner
            rcases Finset.mem_insert.mp (hsub hy_dia) with rfl | hV
            · rcases Finset.mem_image.mp hy with ⟨⟨v, Sv⟩, hvin, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              obtain ⟨hv_eq, hSv⟩ := hveq
              rw [hv_eq, VarType.VTypeBox.inj hSv] at hvin
              exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, innertype⟩, hvin, rfl⟩)).elim
            · exact hV
          have hnew_ne_x : new ≠ xv_t.1 := fun heq =>
            new_fresh (Finset.mem_image.mpr ⟨⟨xv_t.1, xv_t.2.VTypeDia⟩, hwit, heq.symm⟩)
          have newinner_fresh : new ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨w0, hvin, hveq⟩
            exact new_fresh (Finset.mem_image.mpr ⟨⟨w0.1, w0.2.VTypeBox⟩,
              hsubV (Finset.mem_image.mpr ⟨w0, hvin, rfl⟩), hveq⟩)
          have oldinnerX_fresh :=
            not_mem_VarSymbs_insert (x := xv_t) (hx := hx') hx_ne_old.symm oldinner_fresh
          have newinnerX_fresh :=
            not_mem_VarSymbs_insert (x := xv_t) (hx := hx') hnew_ne_x newinner_fresh
          have hx_target :=
            not_mem_VarSymbs_insert (x := (⟨new, innertype⟩ : VarSymb × VarType))
              (hx := newinner_fresh) hnew_ne_x.symm hx'
          have innerCtx_eq : VarCtx_insert xv_t V_inner hxv_t
              = VarCtx_insert ⟨old, innertype⟩
                  (VarCtx_insert xv_t (VarCtx_erase V_inner ⟨old, innertype⟩) hx') oldinnerX_fresh := by
            apply VarCtx_ext'
            change insert xv_t V_inner.1
                = insert ⟨old, innertype⟩ (insert xv_t (VarCtx_erase V_inner ⟨old, innertype⟩).1)
            rw [← Finset.insert_erase h]
            exact Finset.insert_comm _ _ _
          have ctx_swap : VarCtx_insert ⟨new, innertype⟩
                (VarCtx_insert xv_t (VarCtx_erase V_inner ⟨old, innertype⟩) hx') newinnerX_fresh
              = VarCtx_insert xv_t
                (VarCtx_insert ⟨new, innertype⟩ (VarCtx_erase V_inner ⟨old, innertype⟩) newinner_fresh)
                hx_target :=
            VarCtx_insert_comm _ _
          have h_nb_inner : new ∉ Term.boundVars tt :=
            fun hmem => nnb (Finset.mem_insert_of_mem hmem)
          simp only [Term.rename, dif_pos h, RModel.interpTerm]
          congr 1
          · funext w' v
            rw [boxPush_extend_box M (xs := new) (U' := innertype) newinner_fresh hsubV _ env val w',
                interpTerm_cast_term,
                Env.extend_comm (Env.boxPush hsubV env w') newinner_fresh hx' hx_target
                  newinnerX_fresh (M.necEval val w') v ctx_swap.symm,
                interpTerm_rename M oldinnerX_fresh newinnerX_fresh innerCtx_eq tt h_nb_inner w'.1
                  ((Env.boxPush hsubV env w').extend xv_t hx' v) (M.necEval val w')]
            congr 1
            funext p hp
            rw [Env_transport_apply]
            simp only [Env.boxPush, Env.extend]
            split_ifs with h1 h2 h3 <;>
              first
              | (subst_vars; rfl)
              | (exfalso; apply hx_ne_old; simp_all [Prod.ext_iff])
          · rw [Env.extend_apply_ne (xv := ⟨new, _⟩) env val
                  (q := ⟨xv_t.1, xv_t.2.VTypeDia⟩) (hqV := hwit),
                Env.extend_apply_ne (xv := ⟨old, _⟩) env val
                  (q := ⟨xv_t.1, xv_t.2.VTypeDia⟩) (hqV := hwit)]
      case VTypeDia =>
          by_cases h_x : xv_t = (⟨old, diatype⟩ : VarSymb × VarType)
          · -- rebind: the ◇-witness IS the renamed var (⟨old,diatype⟩ → ⟨new,diatype⟩).  Mirrors
            -- GModel's `Soundness2.lean:542-599` (`cast` across the `xv_t.2 = diatype` gap), but
            -- through `pos_inj`+`mapPos_eval` instead of GModel's concrete `∃`-unfolding.  `subst h_x`
            -- is used only *locally*, inside already-`rintro`'d leaf goals, AFTER the recursive
            -- `interpTerm_rename tt` call has been emitted — so the shared `decreasing_by` still sees
            -- the untouched pattern-bound `tt` at the call site (the earlier top-level-`subst` attempt
            -- broke termination by duplicating `tt`; this ordering avoids that).
            have hx_old : old ∉ VarCtx_to_VarSymbs V_inner := by
              have hxt1 : xv_t.1 = old := congrArg Prod.fst h_x
              rw [← hxt1]; exact hxv_t
            have Wdef_inner : VarCtx_insert xv_t V_inner hxv_t
                = VarCtx_insert ⟨old, diatype⟩ V_inner hx_old := by
              apply VarCtx_ext'
              change insert xv_t V_inner.1 = insert (⟨old, diatype⟩ : VarSymb × VarType) V_inner.1
              rw [h_x]
            have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
              intro x x_in
              have hx_dia : x ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := Finset.mem_insert_of_mem x_in
              rcases Finset.mem_insert.mp (hsub hx_dia) with xeq | xV
              · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
                rw [← hveq] at xeq
                simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
              · exact xV
            have hnew_fresh_inner : new ∉ VarCtx_to_VarSymbs V_inner := by
              intro hmem
              rcases Finset.mem_image.mp hmem with ⟨⟨av, aS⟩, hav, hveq⟩
              exact new_fresh (Finset.mem_image.mpr ⟨⟨av, aS.VTypeBox⟩,
                hsubV (Finset.mem_image.mpr ⟨⟨av, aS⟩, hav, rfl⟩), hveq⟩)
            have h_nb_inner : new ∉ Term.boundVars tt := fun hmem => nnb (Finset.mem_insert_of_mem hmem)
            have hqkey : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
                = (⟨old, diatype.VTypeDia⟩ : VarSymb × VarType) := by rw [h_x]
            simp only [Term.rename, dif_pos h_x, RModel.interpTerm]
            apply M.pos_inj
            ext ru
            rw [M.mapPos_eval _ _ ru, M.mapPos_eval _ _ ru,
                show (env.extend (⟨new, diatype.VTypeDia⟩ : VarSymb × VarType) new_fresh val)
                    (⟨new, diatype.VTypeDia⟩ : VarSymb × VarType) (Finset.mem_insert_self _ _) = val
                  by simp only [Env.extend]; rw [dif_pos trivial]]
            have hMIeq : M.interp diatype ru.1.1 = M.interp xv_t.2 ru.1.1 := by
              rw [show xv_t.2 = diatype from congrArg Prod.snd h_x]
            constructor
            · rintro ⟨v, hp, heq⟩
              refine ⟨cast hMIeq v, ?_, ?_⟩
              · have hXold : (env.extend (⟨old, diatype.VTypeDia⟩ : VarSymb × VarType) old_fresh val)
                    (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
                    (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _))
                    = hqkey ▸ val := by simp only [Env.extend, dif_pos hqkey]
                rw [hXold]
                subst h_x
                simpa only [cast_eq] using hp
              · rw [boxPush_extend_notBox (xv := (⟨new, _⟩ : VarSymb × VarType)) M hsubV _ env val
                      rfl ru.1,
                    interpTerm_rename M hx_old hnew_fresh_inner Wdef_inner tt h_nb_inner ru.1.1
                      (Env.boxPush hsubV env ru.1) v] at heq
                rw [boxPush_extend_notBox (xv := (⟨old, _⟩ : VarSymb × VarType)) M hsubV _ env val
                      rfl ru.1, ← heq]
                congr 1
                subst h_x
                simp
            · rintro ⟨v, hp, heq⟩
              have hXold : (env.extend (⟨old, diatype.VTypeDia⟩ : VarSymb × VarType) old_fresh val)
                  (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
                  (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _))
                  = hqkey ▸ val := by simp only [Env.extend, dif_pos hqkey]
              rw [hXold] at hp
              refine ⟨cast hMIeq.symm v, ?_, ?_⟩
              · subst h_x
                simpa only [cast_eq] using hp
              · rw [boxPush_extend_notBox (xv := (⟨new, _⟩ : VarSymb × VarType)) M hsubV _ env val
                      rfl ru.1,
                    interpTerm_rename M hx_old hnew_fresh_inner Wdef_inner tt h_nb_inner ru.1.1
                      (Env.boxPush hsubV env ru.1) (cast hMIeq.symm v)]
                rw [boxPush_extend_notBox (xv := (⟨old, _⟩ : VarSymb × VarType)) M hsubV _ env val
                      rfl ru.1] at heq
                rw [← heq]
                congr 1
                subst h_x
                simp
          · -- passthrough: witness ≠ renamed var; both witness and boxPush ignore it.
            have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
              rcases Finset.mem_insert.mp
                (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)) with heq | hV
              · rw [Prod.mk.injEq] at heq
                exact absurd (Prod.ext heq.1 (VarType.VTypeDia.inj heq.2)) h_x
              · exact hV
            have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
              intro x x_in
              have hx_dia : x ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
                rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem x_in
              rcases Finset.mem_insert.mp (hsub hx_dia) with xeq | xV
              · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
                rw [← hveq] at xeq
                simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
              · exact xV
            simp only [Term.rename, dif_neg h_x, RModel.interpTerm]
            congr 1
            · funext w' v
              congr 2
              refine (boxPush_extend_notBox (xv := ⟨new, _⟩) M hsubV _ env val ?_ w').trans
                (boxPush_extend_notBox (xv := ⟨old, _⟩) M hsubV _ env val ?_ w').symm
              · rfl
              · rfl
            · rw [Env.extend_apply_ne (xv := ⟨new, _⟩) env val
                    (q := ⟨xv_t.1, xv_t.2.VTypeDia⟩) (hqV := hwit),
                  Env.extend_apply_ne (xv := ⟨old, _⟩) env val
                    (q := ⟨xv_t.1, xv_t.2.VTypeDia⟩) (hqV := hwit)]
      case VTypeProd =>
          -- product `repl_type = A×B`: passthrough (like Var/VTypeOne), but the product var is only
          -- non-`VTypeBox`-SHAPED (its `isBox` may be true), so use `boxPush_extend_notBoxShape`.
          have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
            rcases Finset.mem_insert.mp
              (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)) with heq | hV
            · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
            · exact hV
          have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro x x_in
            have hx_dia : x ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem x_in
            rcases Finset.mem_insert.mp (hsub hx_dia) with xeq | xV
            · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
              rw [← hveq] at xeq
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
            · exact xV
          simp only [Term.rename, RModel.interpTerm]
          congr 1
          · funext w' v
            congr 2
            refine (boxPush_extend_notBoxShape (xv := ⟨new, _⟩) M hsubV _ env val
                (fun _ h => VarType.noConfusion h) w').trans
              (boxPush_extend_notBoxShape (xv := ⟨old, _⟩) M hsubV _ env val
                (fun _ h => VarType.noConfusion h) w').symm
          · rw [Env.extend_apply_ne (xv := ⟨new, _⟩) env val
                  (q := ⟨xv_t.1, xv_t.2.VTypeDia⟩) (hqV := hwit),
                Env.extend_apply_ne (xv := ⟨old, _⟩) env val
                  (q := ⟨xv_t.1, xv_t.2.VTypeDia⟩) (hqV := hwit)]
      all_goals
        -- Var / VTypeOne passthrough
        have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
          rcases Finset.mem_insert.mp
            (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)) with heq | hV
          · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
          · exact hV
        have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
          intro x x_in
          have hx_dia : x ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem x_in
          rcases Finset.mem_insert.mp (hsub hx_dia) with xeq | xV
          · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
            rw [← hveq] at xeq
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
          · exact xV
        simp only [Term.rename, RModel.interpTerm]
        congr 1
        · funext w' v
          congr 2
          refine (boxPush_extend_notBox (xv := ⟨new, _⟩) M hsubV _ env val ?_ w').trans
            (boxPush_extend_notBox (xv := ⟨old, _⟩) M hsubV _ env val ?_ w').symm
          · rfl
          · rfl
        · rw [Env.extend_apply_ne (xv := ⟨new, _⟩) env val
                (q := ⟨xv_t.1, xv_t.2.VTypeDia⟩) (hqV := hwit),
              Env.extend_apply_ne (xv := ⟨old, _⟩) env val
                (q := ⟨xv_t.1, xv_t.2.VTypeDia⟩) (hqV := hwit)]
  | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁_eq w₂_eq inner_term, h_nb =>
      -- `Term.rename` on a `pair_elim` node (v9 syntax L1291) is 3-way.  ⭐Reduction (VERIFIED):
      -- `by_cases h_case : ⟨z,V₁×V₂⟩ = ⟨old,repl_type⟩` mirrors the def; `simp only [Term.rename,
      -- dif_pos/neg h_case, RModel.interpTerm]` reduces BOTH sides (via the `interpTerm.pair_elim`
      -- clause) to `interpTerm inner_term w <unpaired env>`, so `congr 1` leaves an ENV-EQUALITY.
      -- • Case A (h_case, z IS the renamed var): rebind z→new, `inner_term` untouched; both envs are
      --   `unpairEnv (extend ⟨new/z⟩ val)` reading the SAME `val` at the pair slot (old=z, repl=V₁×V₂).
      -- • Recurse case: rename inside `inner_term` ⇒ needs the IH `interpTerm_rename inner_term` +
      --   an `unpairEnv`/`extend` commutation.
      -- ⏳TODO: the env-transport `funext` (push outer `▸` via `Env_transport_apply`, then
      -- `by_cases p=v₁/v₂/else` + `Env.unpairEnv_apply_v₁/v₂/other`; cf. `unpairEnv_transport_eq`).
      rename_i pe_V pe_W₁
      by_cases h_case : (⟨z, VarType.VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
      · -- Case A: the pair binder `z` IS the renamed var; rebind z→new, `inner_term` intact.
        -- ⭐VERIFIED so far: `simp [Term.rename, dif_pos h_case, RModel.interpTerm]` reduces both
        -- sides to `interpTerm inner_term w <unpaired env>`; `congr 1` leaves a CLEAN env-eq (no HEq)
        -- `ENV_L = ENV_R` : Env pe_W₁ w; `funext p hp; rw [Env_transport_apply, Env_transport_apply]`
        -- pushes the outer `▸`; `by_cases p=v₁/v₂/else; subst` then reduces each to a pair-slot read
        -- `= val.1/val.2` (LHS reads `extend ⟨new,repl_type⟩ val` at ⟨new,V₁×V₂⟩; RHS reads
        -- `Wdef▸extend ⟨old,repl_type⟩ val` at ⟨z,V₁×V₂⟩ — both = val, using h_case: z=old,repl=V₁×V₂).
        -- ⏳TODO: the per-var `unpairEnv_apply_v₁/v₂/other` + extend-at-key + `Env_transport_apply` for
        -- the inner `Wdef▸`.  (Reduction confirmed; only the pair-slot bookkeeping remains.)
        obtain ⟨hz_old, hrepl⟩ := Prod.mk.inj h_case
        simp only [Term.rename, dif_pos h_case, RModel.interpTerm]
        subst hrepl
        subst hz_old
        -- The pair's inner context `pe_V` equals the outer `V` (both = `W` minus `⟨z,V₁×V₂⟩`).
        have hVV : pe_V = V := by
          apply VarCtx_ext'
          have hzpe : (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∉ pe_V.1 :=
            fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          have hzV : (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∉ V.1 :=
            fun h => old_fresh (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          have hset : insert (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) pe_V.1
                    = insert ⟨z, v₁.2.VTypeProd v₂.2⟩ V.1 :=
            congrArg PSigma.fst (w₂_eq.trans Wdef)
          change pe_V.1 = V.1
          rw [← Finset.erase_insert hzpe, hset, Finset.erase_insert hzV]
        congr 1
        funext p hp
        rw [Env_transport_apply, Env_transport_apply]
        by_cases h1 : p = v₁
        · subst h1
          rw [Env.unpairEnv_apply_v₁ (hzs := Finset.mem_insert_self _ _),
              Env.unpairEnv_apply_v₁ (hzs := by rw [Wdef]; exact Finset.mem_insert_self _ _),
              Env_transport_apply]
          simp only [Env.extend, dif_pos rfl, dite_true]
        · by_cases h2 : p = v₂
          · subst h2
            rw [Env.unpairEnv_apply_v₂ (hzs := Finset.mem_insert_self _ _),
                Env.unpairEnv_apply_v₂ (hzs := by rw [Wdef]; exact Finset.mem_insert_self _ _),
                Env_transport_apply]
            simp only [Env.extend, dif_pos rfl, dite_true]
          · -- else: `p ∈ V`, both `unpairEnv`s pass `env p` through (the extends miss `p`).
            have hpV : p ∈ V.1 := by
              have hp2 : p ∈ (VarCtx_insert_twice v₁ v₂ pe_V hv₁ hv₂ hv₁v₂).1 := by
                rw [w₁_eq]; exact hp
              have hpV_pe : p ∈ pe_V.1 := by
                rcases Finset.mem_insert.mp hp2 with h | h
                · exact absurd h h1
                · rcases Finset.mem_insert.mp h with h' | h'
                  · exact absurd h' h2
                  · exact h'
              exact hVV ▸ hpV_pe
            rw [Env.unpairEnv_apply_other (h1 := h1) (h2 := h2)
                  (hqW := Finset.mem_insert_of_mem hpV),
                Env.unpairEnv_apply_other (h1 := h1) (h2 := h2)
                  (hqW := by rw [Wdef]; exact Finset.mem_insert_of_mem hpV),
                Env_transport_apply]
            have hpnew : p ≠ (⟨new, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) := by
              rintro rfl; exact new_fresh (Finset.mem_image.mpr ⟨_, hpV, rfl⟩)
            have hpz : p ≠ (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) := by
              rintro rfl; exact old_fresh (Finset.mem_image.mpr ⟨_, hpV, rfl⟩)
            simp only [Env.extend, dif_neg hpnew, dif_neg hpz]
      · -- Recurse case: `old` is free inside `inner_term`; rename it there.  ⭐Reduction VERIFIED
        -- (below): `simp [Term.rename, dif_neg h_case, RModel.interpTerm]` + `interpTerm_cast_term`
        -- gives `interpTerm (rename old new … inner_term) w (unpairEnv (extend ⟨new,repl⟩ val)) =
        -- interpTerm inner_term w (w₁_eq ▸ unpairEnv w₂_eq (Wdef ▸ extend ⟨old,repl⟩ val))`.
        -- ⏳TODO: (1) a NEW helper `unpairEnv_extend_comm` — `unpairEnv (env.extend ⟨s,T⟩ val) =
        -- (unpairEnv env).extend ⟨s,T⟩ val` for `s ∉ {z,v₁,v₂}` (funext + apply-lemmas, like Case A);
        -- rewrite the LHS's `unpairEnv (extend ⟨new⟩)` to `(unpairEnv env).extend ⟨new⟩` so the IH
        -- `interpTerm_rename inner_term` (over `pe_W₁_inner = insert_twice v₁ v₂ (erase pe_V ⟨old⟩)`,
        -- env `unpairEnv env`) fires; (2) match the resulting `Wdef_i ▸ (unpairEnv env).extend ⟨old⟩`
        -- against RHS via the same commutation on the `⟨old⟩` side.
        simp only [Term.rename, dif_neg h_case, RModel.interpTerm]
        rw [interpTerm_cast_term]
        sorry
termination_by Term.numNodes t
decreasing_by all_goals (simp_wf; simp only [Term.numNodes, Func.numNodes]; omega)

theorem interpFunc_rename (M : RModel σ) {old new : VarSymb} {repl_type : VarType}
    {V W : VarCtx} {n : ℕ}
    (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (f : Func σ W n) (new_not_bound : new ∉ Func.boundVars f)
    (w : M.W) (env : M.Env V w) (val : M.interp repl_type w) (args : Fin n → M.D w) :
    M.interpFunc (Func.rename old new repl_type V W n
        old_fresh new_fresh Wdef f new_not_bound) w (env.extend ⟨new, repl_type⟩ new_fresh val) args
      = M.interpFunc f w (Wdef ▸ (env.extend ⟨old, repl_type⟩ old_fresh val)) args := by
  match f, new_not_bound with
  | .F h, _ => subst Wdef; simp only [Func.rename, RModel.interpFunc]
  | .eval g t, nnb =>
      have h_nb_g : new ∉ Func.boundVars g := fun hmem => nnb (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t := fun hmem => nnb (Finset.mem_union_right _ hmem)
      simp only [Func.rename, RModel.interpFunc]
      rw [interpTerm_rename M old_fresh new_fresh Wdef t h_nb_t w env val]
      exact interpFunc_rename M old_fresh new_fresh Wdef g h_nb_g w env val _
termination_by Func.numNodes f
decreasing_by all_goals (simp_wf; simp only [Term.numNodes, Func.numNodes]; omega)
end

/-- Relation-level α-rename invariance (base for the `atom` case; via `interpTerm_rename`). -/
theorem interpRel_rename (M : RModel σ) {old new : VarSymb} {repl_type : VarType}
    {V : VarCtx} {n : ℕ}
    (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (R : Rel σ (VarCtx_insert ⟨old, repl_type⟩ V old_fresh) n)
    (new_not_bound : new ∉ Rel.boundVars R)
    (w : M.W) (env : M.Env V w) (val : M.interp repl_type w) (args : Fin n → M.D w) :
    M.interpRel (Rel.rename old new repl_type V (VarCtx_insert ⟨old, repl_type⟩ V old_fresh) n
        old_fresh new_fresh rfl R new_not_bound) w (env.extend ⟨new, repl_type⟩ new_fresh val) args
      = M.interpRel R w (env.extend ⟨old, repl_type⟩ old_fresh val) args := by
  match R, new_not_bound with
  | .R hr, _ => simp only [Rel.rename, RModel.interpRel]
  | .eval R' t, nnb =>
      have h_nb_R : new ∉ Rel.boundVars R' := fun hmem => nnb (Finset.mem_union_left _ hmem)
      have h_nb_t : new ∉ Term.boundVars t := fun hmem => nnb (Finset.mem_union_right _ hmem)
      simp only [Rel.rename, RModel.interpRel]
      rw [interpTerm_rename M old_fresh new_fresh rfl t h_nb_t w env val]
      exact interpRel_rename M old_fresh new_fresh R' h_nb_R w env val _

/-- **Satisfaction of formulas.**  Propositional/quantifier/`box` cases are identical to
    `GModel.interpWFF`; the `◇` case reads the witness out of the realization set `posEval`
    (RModel's `Pos`-object *is* its realization set, `pos_inj`), in place of `GModel`'s `posMem`. -/
def interpWFF (M : RModel σ) : {V : VarCtx} → WFF σ V → (w : M.W) → M.Env V w → Prop
  | _, .atom R,     w, env => M.interpRel R w env Fin.elim0
  | _, .top,        _, _   => True
  | _, .bot,        _, _   => False
  | _, .and φ ψ,    w, env => M.interpWFF φ w env ∧ M.interpWFF ψ w env
  | _, .or φ ψ,     w, env => M.interpWFF φ w env ∨ M.interpWFF ψ w env
  | _, .imp φ ψ,    w, env => M.interpWFF φ w env → M.interpWFF ψ w env
  | _, .eq s t,     w, env => M.interpTerm s w env = M.interpTerm t w env
  | _, @WFF.all _ _ x hx φ, w, env => ∀ a : M.interp x.2 w, M.interpWFF φ w (env.extend x hx a)
  | _, @WFF.ex _ _ x hx φ,  w, env => ∃ a : M.interp x.2 w, M.interpWFF φ w (env.extend x hx a)
  | _, .box φ hsub _, w, env =>
      ∀ w' : {w' : M.W // M.R w w'}, M.interpWFF φ w'.1 (Env.boxPush hsub env w')
  | _, .dia x hx φ hsub _, w, env =>
      -- `◇_x φ` = *some* realization of the `◇`-variable makes `φ` hold at its world.
      ∃ dv : Σ' w' : {w' : M.W // M.R w w'}, M.interp x.2 w'.1,
        dv ∈ M.posEval (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))) ∧
        M.interpWFF φ dv.1.1
          ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2)
  | _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz W₁eq W₂eq body, w, env =>
      -- The product recursor at the formula level: bind `v₁,v₂` to `z`'s projections.
      M.interpWFF body w (W₁eq ▸ Env.unpairEnv hv₁v₂ W₂eq env)

/-- Interpretation commutes with a context-equality cast on the formula (transport the env). -/
theorem interpWFF_cast_term (M : RModel σ) {W1 W2 : VarCtx} (h : W1 = W2)
    (φ : WFF σ W1) (w : M.W) (env : M.Env W2 w) :
    M.interpWFF (h ▸ φ) w env = M.interpWFF φ w (h.symm ▸ env) := by subst h; rfl

/-- **Formula-level pair-elim distribution is semantics-preserving.**  The `WFF.pairElim`
    η-normaliser (push a `pair_elim` inward through the connectives, stopping at quantifier/modal
    binders) denotes the same as the direct product recursor `WFF.pair_elim`.  Base for the
    `Proof.pair_elim` rule and the WFF `VTypeProd` cases of `ctx_ext`/`rename`. -/
theorem interpWFF_pairElim (M : RModel σ) {V W₁ W₂ : VarCtx}
    (v₁ v₂ : VarSymb × VarType) (z : VarSymb)
    (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) (hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V)
    (hv₁v₂ : v₁.1 ≠ v₂.1) (hz : z ∉ VarCtx_to_VarSymbs V)
    (w₁eq : VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁)
    (w₂eq : VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂)
    (φ : WFF σ W₁) (w : M.W) (env : M.Env W₂ w) :
    M.interpWFF (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ) w env
      = M.interpWFF φ w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) := by
  match φ with
  | .atom R =>
      simp only [WFF.pairElim, RModel.interpWFF]
      exact interpRel_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq R w env Fin.elim0
  | .top => simp only [WFF.pairElim, RModel.interpWFF]
  | .bot => simp only [WFF.pairElim, RModel.interpWFF]
  | .and φ ψ =>
      simp only [WFF.pairElim, RModel.interpWFF]
      rw [interpWFF_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ w env,
          interpWFF_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ w env]
  | .or φ ψ =>
      simp only [WFF.pairElim, RModel.interpWFF]
      rw [interpWFF_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ w env,
          interpWFF_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ w env]
  | .imp φ ψ =>
      simp only [WFF.pairElim, RModel.interpWFF]
      rw [interpWFF_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq φ w env,
          interpWFF_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ w env]
  | .eq s t =>
      simp only [WFF.pairElim, RModel.interpWFF]
      rw [show M.interpTerm (Term.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq s) w env
            = M.interpTerm s w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) from by
            rw [interpTerm_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq s w env];
            simp only [RModel.interpTerm],
          show M.interpTerm (Term.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t) w env
            = M.interpTerm t w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) from by
            rw [interpTerm_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq t w env];
            simp only [RModel.interpTerm]]
  | .all x φ => simp only [WFF.pairElim, RModel.interpWFF]
  | .ex x φ => simp only [WFF.pairElim, RModel.interpWFF]
  | .box φ hsub hnbe => simp only [WFF.pairElim, RModel.interpWFF]
  | .dia x hx φ hsub hnbe => simp only [WFF.pairElim, RModel.interpWFF]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => simp only [WFF.pairElim, RModel.interpWFF]

/-- Semantic entailment over `RModel`s. -/
def Entails {V : VarCtx} (Γ : Finset (WFF σ V)) (φ : WFF σ V) : Prop :=
  ∀ (M : RModel.{u} σ) (w : M.W) (env : M.Env V w),
    (∀ ψ ∈ Γ, M.interpWFF ψ w env) → M.interpWFF φ w env

@[inherit_doc] scoped notation:50 Γ " ⊨ᵣ " φ => Entails Γ φ

/-- **Formula-level α-rename invariance.**  All cases port verbatim from `Soundness2.lean` —
    including the modal `box`/`dia` cases (Props, so `propext` + `forall_congr'`/`exists_congr`
    suffice; no `nec_inj`/`pos_inj` needed at the WFF level).  Only the pair sector is
    deferred (`sorry`). -/
theorem interpWFF_rename (M : RModel σ) {old new : VarSymb} {repl_type : VarType}
    {V W : VarCtx}
    (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (φ : WFF σ W) (new_not_bound : new ∉ WFF.boundVars φ)
    (w : M.W) (env : M.Env V w) (val : M.interp repl_type w) :
    M.interpWFF (WFF.rename old new repl_type V W old_fresh new_fresh Wdef φ new_not_bound) w
        (env.extend ⟨new, repl_type⟩ new_fresh val)
      = M.interpWFF φ w (Wdef.symm ▸ env.extend ⟨old, repl_type⟩ old_fresh val) := by
  match φ, new_not_bound with
  | .atom R, nnb =>
      subst Wdef
      simp only [WFF.rename, RModel.interpWFF]
      exact interpRel_rename M old_fresh new_fresh R nnb w env val Fin.elim0
  | .top, _ => simp only [WFF.rename, RModel.interpWFF]
  | .bot, _ => simp only [WFF.rename, RModel.interpWFF]
  | .and a b, nnb =>
      have h1 : new ∉ WFF.boundVars a := fun h => nnb (Finset.mem_union_left _ h)
      have h2 : new ∉ WFF.boundVars b := fun h => nnb (Finset.mem_union_right _ h)
      simp only [WFF.rename, RModel.interpWFF]
      rw [interpWFF_rename M old_fresh new_fresh Wdef a h1 w env val,
          interpWFF_rename M old_fresh new_fresh Wdef b h2 w env val]
  | .or a b, nnb =>
      have h1 : new ∉ WFF.boundVars a := fun h => nnb (Finset.mem_union_left _ h)
      have h2 : new ∉ WFF.boundVars b := fun h => nnb (Finset.mem_union_right _ h)
      simp only [WFF.rename, RModel.interpWFF]
      rw [interpWFF_rename M old_fresh new_fresh Wdef a h1 w env val,
          interpWFF_rename M old_fresh new_fresh Wdef b h2 w env val]
  | .imp a b, nnb =>
      have h1 : new ∉ WFF.boundVars a := fun h => nnb (Finset.mem_union_left _ h)
      have h2 : new ∉ WFF.boundVars b := fun h => nnb (Finset.mem_union_right _ h)
      simp only [WFF.rename, RModel.interpWFF]
      rw [interpWFF_rename M old_fresh new_fresh Wdef a h1 w env val,
          interpWFF_rename M old_fresh new_fresh Wdef b h2 w env val]
  | .eq s t, nnb =>
      subst Wdef
      have h_s : new ∉ Term.boundVars s := fun h => nnb (Finset.mem_union_left _ h)
      have h_t : new ∉ Term.boundVars t := fun h => nnb (Finset.mem_union_right _ h)
      simp only [WFF.rename, RModel.interpWFF]
      rw [interpTerm_rename M old_fresh new_fresh rfl s h_s w env val,
          interpTerm_rename M old_fresh new_fresh rfl t h_t w env val]
  | @WFF.all _ _ x hx ψ, nnb =>
      have h_W_symbols : VarCtx_to_VarSymbs W = insert old (VarCtx_to_VarSymbs V) := by
        rw [Wdef]; exact VarCtx_to_VarSymbs_insert _ _ _
      have hx_ne_old : x.1 ≠ old := fun h_eq =>
        hx (h_W_symbols ▸ Finset.mem_insert.mpr (Or.inl h_eq))
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := fun h_in =>
        hx (h_W_symbols ▸ Finset.mem_insert_of_mem h_in)
      have hx_ne_new : x.1 ≠ new := fun h_eq => nnb (Finset.mem_insert.mpr (Or.inl h_eq.symm))
      have h_nb_ψ : new ∉ WFF.boundVars ψ := fun hmem => nnb (Finset.mem_insert_of_mem hmem)
      have hold_V_x : old ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_old h.symm) old_fresh
      have hnew_V_x : new ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_new h.symm) new_fresh
      have Wdef_inner : VarCtx_insert x W hx
          = VarCtx_insert ⟨old, repl_type⟩ (VarCtx_insert x V hx_V) hold_V_x := by
        apply VarCtx_ext'
        change insert x W.1 = insert ⟨old, repl_type⟩ (insert x V.1)
        rw [Wdef]
        change insert x (insert ⟨old, repl_type⟩ V.1) = _
        exact Finset.insert_comm _ _ _
      simp only [WFF.rename, RModel.interpWFF]
      apply propext; apply forall_congr'; intro a
      rw [interpWFF_cast_term, Env.extend_comm,
          interpWFF_rename M hold_V_x hnew_V_x Wdef_inner ψ h_nb_ψ w (env.extend x hx_V a) val]
      subst Wdef
      rw [Env.extend_comm]
  | @WFF.ex _ _ x hx ψ, nnb =>
      have h_W_symbols : VarCtx_to_VarSymbs W = insert old (VarCtx_to_VarSymbs V) := by
        rw [Wdef]; exact VarCtx_to_VarSymbs_insert _ _ _
      have hx_ne_old : x.1 ≠ old := fun h_eq =>
        hx (h_W_symbols ▸ Finset.mem_insert.mpr (Or.inl h_eq))
      have hx_V : x.1 ∉ VarCtx_to_VarSymbs V := fun h_in =>
        hx (h_W_symbols ▸ Finset.mem_insert_of_mem h_in)
      have hx_ne_new : x.1 ≠ new := fun h_eq => nnb (Finset.mem_insert.mpr (Or.inl h_eq.symm))
      have h_nb_ψ : new ∉ WFF.boundVars ψ := fun hmem => nnb (Finset.mem_insert_of_mem hmem)
      have hold_V_x : old ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_old h.symm) old_fresh
      have hnew_V_x : new ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx_V) :=
        not_mem_VarSymbs_insert (fun h => hx_ne_new h.symm) new_fresh
      have Wdef_inner : VarCtx_insert x W hx
          = VarCtx_insert ⟨old, repl_type⟩ (VarCtx_insert x V hx_V) hold_V_x := by
        apply VarCtx_ext'
        change insert x W.1 = insert ⟨old, repl_type⟩ (insert x V.1)
        rw [Wdef]
        change insert x (insert ⟨old, repl_type⟩ V.1) = _
        exact Finset.insert_comm _ _ _
      simp only [WFF.rename, RModel.interpWFF]
      apply propext; apply exists_congr; intro a
      rw [interpWFF_cast_term, Env.extend_comm,
          interpWFF_rename M hold_V_x hnew_V_x Wdef_inner ψ h_nb_ψ w (env.extend x hx_V a) val]
      subst Wdef
      rw [Env.extend_comm]
  | @WFF.box _ V_inner _ ψ hsub hnbe, nnb =>
      rcases repl_type with _ | innertype | diatype | _ | ⟨A, B⟩
      · -- repl_type = Var: passthrough (renamed var is non-box, never in the box context)
        subst Wdef
        have hsub_V : (VarCtx_box V_inner).1 ⊆ V.1 := by
          intro y hy
          rcases Finset.mem_insert.mp (hsub hy) with yold | yV
          · rcases Finset.mem_image.mp hy with ⟨q, _, qeq⟩
            exact VarType.noConfusion (Prod.mk.inj (qeq.trans yold)).2
          · exact yV
        simp only [WFF.rename, RModel.interpWFF]
        apply propext; apply forall_congr'; intro w'
        rw [boxPush_extend_notBox (xv := (⟨new, VarType.Var⟩ : VarSymb × VarType))
              M hsub_V _ env val rfl w',
            boxPush_extend_notBox M hsub_V hsub env val rfl w']
      · -- repl_type = VTypeBox: recurse into ψ over `VarCtx_erase V_inner ⟨old,innertype⟩`
        subst Wdef
        have h : (⟨old, innertype⟩ : VarSymb × VarType) ∈ V_inner.1 := by
          have hmem := hnbe ⟨old, innertype.VTypeBox⟩ (Finset.mem_insert_self _ _) rfl
          rcases Finset.mem_image.mp hmem with ⟨⟨v, Sv⟩, hv, hveq⟩
          simp only [Prod.mk.injEq] at hveq
          obtain ⟨rfl, hSeq⟩ := hveq
          rwa [VarType.VTypeBox.inj hSeq] at hv
        simp only [WFF.rename, dif_pos h, RModel.interpWFF]
        have oldinner_fresh : old ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) :=
          VarCtx_erase_fresh h
        have hsubV : (VarCtx_box (VarCtx_erase V_inner ⟨old, innertype⟩)).1 ⊆ V.1 := by
          intro y hy
          have hy_inner : y ∈ (VarCtx_box V_inner).1 := by
            rcases Finset.mem_image.mp hy with ⟨w0, hvin, hveq⟩
            exact Finset.mem_image.mpr ⟨w0, Finset.erase_subset _ _ hvin, hveq⟩
          rcases Finset.mem_insert.mp (hsub hy_inner) with rfl | hV
          · rcases Finset.mem_image.mp hy with ⟨⟨v, Sv⟩, hvin, hveq⟩
            simp only [Prod.mk.injEq] at hveq
            obtain ⟨hv_eq, hSv⟩ := hveq
            rw [hv_eq, VarType.VTypeBox.inj hSv] at hvin
            exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, innertype⟩, hvin, rfl⟩)).elim
          · exact hV
        have newinner_fresh : new ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨w0, hvin, hveq⟩
          exact new_fresh (Finset.mem_image.mpr ⟨⟨w0.1, w0.2.VTypeBox⟩,
            hsubV (Finset.mem_image.mpr ⟨w0, hvin, rfl⟩), hveq⟩)
        have innerCtx_eq : V_inner
            = VarCtx_insert ⟨old, innertype⟩ (VarCtx_erase V_inner ⟨old, innertype⟩) oldinner_fresh :=
          (VarCtx_insert_erase h oldinner_fresh).symm
        apply propext; apply forall_congr'; intro w'
        rw [boxPush_extend_box M (xs := new) (U' := innertype) newinner_fresh hsubV _ env val w',
            interpWFF_rename M oldinner_fresh newinner_fresh innerCtx_eq ψ nnb w'.1
              (Env.boxPush hsubV env w') (M.necEval val w')]
        have henv : innerCtx_eq.symm ▸ ((Env.boxPush hsubV env w').extend ⟨old, innertype⟩
              oldinner_fresh (M.necEval val w'))
            = Env.boxPush hsub (env.extend ⟨old, innertype.VTypeBox⟩ old_fresh val) w' := by
          funext p hp
          rw [Env_transport_apply]
          simp only [Env.boxPush, Env.extend]
          by_cases hpo : p = (⟨old, innertype⟩ : VarSymb × VarType)
          · subst hpo
            rw [dif_pos rfl, dif_pos rfl]
          · obtain ⟨pv, pT⟩ := p
            have hne : (⟨pv, pT.VTypeBox⟩ : VarSymb × VarType) ≠ ⟨old, innertype.VTypeBox⟩ := by
              intro heq
              rw [Prod.mk.injEq] at heq
              exact hpo (Prod.ext heq.1 (VarType.VTypeBox.inj heq.2))
            rw [dif_neg hne, dif_neg hpo]
        rw [henv]
      · -- repl_type = VTypeDia: passthrough
        subst Wdef
        have hsub_V : (VarCtx_box V_inner).1 ⊆ V.1 := by
          intro y hy
          rcases Finset.mem_insert.mp (hsub hy) with yold | yV
          · rcases Finset.mem_image.mp hy with ⟨q, _, qeq⟩
            exact VarType.noConfusion (Prod.mk.inj (qeq.trans yold)).2
          · exact yV
        simp only [WFF.rename, RModel.interpWFF]
        apply propext; apply forall_congr'; intro w'
        rw [boxPush_extend_notBox (xv := (⟨new, VarType.VTypeDia diatype⟩ : VarSymb × VarType))
              M hsub_V _ env val rfl w',
            boxPush_extend_notBox M hsub_V hsub env val rfl w']
      · -- repl_type = VTypeOne: passthrough
        subst Wdef
        have hsub_V : (VarCtx_box V_inner).1 ⊆ V.1 := by
          intro y hy
          rcases Finset.mem_insert.mp (hsub hy) with yold | yV
          · rcases Finset.mem_image.mp hy with ⟨q, _, qeq⟩
            exact VarType.noConfusion (Prod.mk.inj (qeq.trans yold)).2
          · exact yV
        simp only [WFF.rename, RModel.interpWFF]
        apply propext; apply forall_congr'; intro w'
        rw [boxPush_extend_notBox (xv := (⟨new, VarType.VTypeOne⟩ : VarSymb × VarType))
              M hsub_V _ env val rfl w',
            boxPush_extend_notBox M hsub_V hsub env val rfl w']
      · -- repl_type = VTypeProd: passthrough (product var is never VTypeBox-SHAPED, so `boxPush`
        -- ignores it on both sides — via the shape-based lemma, since `isBox (A×B)` may be true).
        subst Wdef
        have hsub_V : (VarCtx_box V_inner).1 ⊆ V.1 := by
          intro y hy
          rcases Finset.mem_insert.mp (hsub hy) with yold | yV
          · rcases Finset.mem_image.mp hy with ⟨q, _, qeq⟩
            exact VarType.noConfusion (Prod.mk.inj (qeq.trans yold)).2
          · exact yV
        simp only [WFF.rename, RModel.interpWFF]
        apply propext; apply forall_congr'; intro w'
        rw [boxPush_extend_notBoxShape (xv := (⟨new, VarType.VTypeProd A B⟩ : VarSymb × VarType))
              M hsub_V _ env val (fun _ h => VarType.noConfusion h) w',
            boxPush_extend_notBoxShape M hsub_V hsub env val (fun _ h => VarType.noConfusion h) w']
  | @WFF.dia _ V_inner _ x_t hx_t ψ hsub hnbe, nnb =>
      -- Ports Soundness2:929-1135 verbatim (GModel→RModel): the WFF-level `◇` is a native `∃`
      -- Prop (`dv ∈ posEval …`), so no `pos_inj`/`mapPos_eval` — the env-rewrites act on the
      -- witness lookup and `boxPush` arguments directly, as in GModel.
      subst Wdef
      rcases repl_type with _ | innertype | diatype | _ | ⟨A, B⟩
      case VTypeBox =>
        have h : (⟨old, innertype⟩ : VarSymb × VarType) ∈ V_inner.1 := by
          have hmem := hnbe ⟨old, innertype.VTypeBox⟩ (Finset.mem_insert_self _ _) rfl
          rw [VarCtx_dia_fst] at hmem
          rcases Finset.mem_insert.mp hmem with heq | hbox
          · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
          · rcases Finset.mem_image.mp hbox with ⟨⟨v, Sv⟩, hv, hveq⟩
            simp only [Prod.mk.injEq] at hveq
            obtain ⟨rfl, hSeq⟩ := hveq
            rwa [VarType.VTypeBox.inj hSeq] at hv
        simp only [WFF.rename, dif_pos h, RModel.interpWFF]
        have hwit : (⟨x_t.1, x_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
          rcases Finset.mem_insert.mp
            (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)) with heq | hV
          · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
          · exact hV
        apply propext
        apply exists_congr
        intro dv
        rw [Env.extend_apply_ne (xv := (⟨new, _⟩ : VarSymb × VarType)) env val
              (q := ⟨x_t.1, x_t.2.VTypeDia⟩) (hqV := hwit),
            Env.extend_apply_ne (xv := (⟨old, _⟩ : VarSymb × VarType)) env val
              (q := ⟨x_t.1, x_t.2.VTypeDia⟩) (hqV := hwit)]
        have oldinner_fresh : old ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) :=
          VarCtx_erase_fresh h
        have hx_ne_old : x_t.1 ≠ old := fun heq =>
          hx_t (Finset.mem_image.mpr ⟨⟨old, innertype⟩, h, heq.symm⟩)
        have hx' : x_t.1 ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) :=
          fun hmem => hx_t (VarCtx_to_VarSymbs_erase_subset hmem)
        have hsubV : (VarCtx_box (VarCtx_erase V_inner ⟨old, innertype⟩)).1 ⊆ V.1 := by
          intro y hy
          have hy_inner : y ∈ (VarCtx_box V_inner).1 := by
            rcases Finset.mem_image.mp hy with ⟨w0, hvin, hveq⟩
            exact Finset.mem_image.mpr ⟨w0, Finset.erase_subset _ _ hvin, hveq⟩
          have hy_dia : y ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hy_inner
          rcases Finset.mem_insert.mp (hsub hy_dia) with rfl | hV
          · rcases Finset.mem_image.mp hy with ⟨⟨v, Sv⟩, hvin, hveq⟩
            simp only [Prod.mk.injEq] at hveq
            obtain ⟨hv_eq, hSv⟩ := hveq
            rw [hv_eq, VarType.VTypeBox.inj hSv] at hvin
            exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, innertype⟩, hvin, rfl⟩)).elim
          · exact hV
        have hnew_ne_x : new ≠ x_t.1 := fun heq =>
          new_fresh (Finset.mem_image.mpr ⟨⟨x_t.1, x_t.2.VTypeDia⟩, hwit, heq.symm⟩)
        have newinner_fresh : new ∉ VarCtx_to_VarSymbs (VarCtx_erase V_inner ⟨old, innertype⟩) := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨w0, hvin, hveq⟩
          exact new_fresh (Finset.mem_image.mpr ⟨⟨w0.1, w0.2.VTypeBox⟩,
            hsubV (Finset.mem_image.mpr ⟨w0, hvin, rfl⟩), hveq⟩)
        have oldinnerX_fresh :=
          not_mem_VarSymbs_insert (x := x_t) (hx := hx') hx_ne_old.symm oldinner_fresh
        have newinnerX_fresh :=
          not_mem_VarSymbs_insert (x := x_t) (hx := hx') hnew_ne_x newinner_fresh
        have hx_target :=
          not_mem_VarSymbs_insert (x := (⟨new, innertype⟩ : VarSymb × VarType))
            (hx := newinner_fresh) hnew_ne_x.symm hx'
        have innerCtx_eq : VarCtx_insert x_t V_inner hx_t
            = VarCtx_insert ⟨old, innertype⟩
              (VarCtx_insert x_t (VarCtx_erase V_inner ⟨old, innertype⟩) hx') oldinnerX_fresh := by
          apply VarCtx_ext'
          change insert x_t V_inner.1
              = insert ⟨old, innertype⟩ (insert x_t (VarCtx_erase V_inner ⟨old, innertype⟩).1)
          rw [← Finset.insert_erase h]
          exact Finset.insert_comm _ _ _
        have ctx_swap : VarCtx_insert ⟨new, innertype⟩
              (VarCtx_insert x_t (VarCtx_erase V_inner ⟨old, innertype⟩) hx') newinnerX_fresh
            = VarCtx_insert x_t
            (VarCtx_insert ⟨new, innertype⟩ (VarCtx_erase V_inner ⟨old, innertype⟩) newinner_fresh)
            hx_target :=
          VarCtx_insert_comm _ _
        have h_nb_inner : new ∉ WFF.boundVars ψ := fun hmem => nnb (Finset.mem_insert_of_mem hmem)
        apply and_congr_right; intro _
        rw [boxPush_extend_box M (xs := new) (U' := innertype) newinner_fresh hsubV _ env val
              dv.fst,
            interpWFF_cast_term,
            Env.extend_comm (Env.boxPush hsubV env dv.fst) newinner_fresh hx' hx_target
              newinnerX_fresh (M.necEval val dv.fst) dv.snd ctx_swap.symm,
            interpWFF_rename M oldinnerX_fresh newinnerX_fresh innerCtx_eq ψ h_nb_inner (↑dv.fst)
              ((Env.boxPush hsubV env dv.fst).extend x_t hx' dv.snd) (M.necEval val dv.fst)]
        refine Iff.of_eq (congrArg (fun e => M.interpWFF ψ (↑dv.fst) e) ?_)
        funext p hp
        rw [Env_transport_apply]
        simp only [Env.boxPush, Env.extend]
        split_ifs with h1 h2 h3 <;>
          first
          | (subst_vars; rfl)
          | (exfalso; apply hx_ne_old; simp_all [Prod.ext_iff])
      case VTypeDia =>
        by_cases h_x : x_t = (⟨old, diatype⟩ : VarSymb × VarType)
        · -- rebind: the dia's witness IS the renamed var (⟨old,diatype⟩ → ⟨new,diatype⟩).
          simp only [WFF.rename, dif_pos h_x, RModel.interpWFF]
          have hx_old : old ∉ VarCtx_to_VarSymbs V_inner := by
            have hxt1 : x_t.1 = old := congrArg Prod.fst h_x
            rw [← hxt1]; exact hx_t
          have Wdef_inner : VarCtx_insert x_t V_inner hx_t
              = VarCtx_insert ⟨old, diatype⟩ V_inner hx_old := by
            apply VarCtx_ext'
            change insert x_t V_inner.1 = insert (⟨old, diatype⟩ : VarSymb × VarType) V_inner.1
            rw [h_x]
          have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro x x_in
            have hx_dia : x ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem x_in
            rcases Finset.mem_insert.mp (hsub hx_dia) with xeq | xV
            · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
              rw [← hveq] at xeq
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
            · exact xV
          have hnew_fresh_inner : new ∉ VarCtx_to_VarSymbs V_inner := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨⟨av, aS⟩, hav, hveq⟩
            exact new_fresh (Finset.mem_image.mpr ⟨⟨av, aS.VTypeBox⟩,
              hsubV (Finset.mem_image.mpr ⟨⟨av, aS⟩, hav, rfl⟩), hveq⟩)
          have h_nb_inner : new ∉ WFF.boundVars ψ := fun hmem => nnb (Finset.mem_insert_of_mem hmem)
          apply propext
          constructor
          · rintro ⟨⟨dw, dval⟩, hp, heq⟩
            have hMIeq : M.interp x_t.2 ↑dw = M.interp diatype ↑dw := by
              rw [show x_t.2 = diatype from congrArg Prod.snd h_x]
            refine ⟨⟨dw, cast hMIeq.symm dval⟩, ?_, ?_⟩
            · subst h_x
              simpa only [Env.extend, dif_pos, cast_eq] using hp
            · rw [boxPush_extend_notBox (xv := (⟨new, _⟩ : VarSymb × VarType)) M hsubV _ env val
                    rfl dw,
                  interpWFF_rename M hx_old hnew_fresh_inner Wdef_inner ψ h_nb_inner ↑dw
                    (Env.boxPush hsubV env dw) dval] at heq
              rw [boxPush_extend_notBox (xv := (⟨old, _⟩ : VarSymb × VarType)) M hsubV _ env val
                    rfl dw]
              convert heq using 2
              subst h_x
              simp
          · rintro ⟨⟨dw, dval⟩, hp, heq⟩
            have hMIeq : M.interp x_t.2 ↑dw = M.interp diatype ↑dw := by
              rw [show x_t.2 = diatype from congrArg Prod.snd h_x]
            refine ⟨⟨dw, cast hMIeq dval⟩, ?_, ?_⟩
            · subst h_x
              simpa only [Env.extend, dif_pos, cast_eq] using hp
            · rw [boxPush_extend_notBox (xv := (⟨new, _⟩ : VarSymb × VarType)) M hsubV _ env val
                    rfl dw,
                  interpWFF_rename M hx_old hnew_fresh_inner Wdef_inner ψ h_nb_inner ↑dw
                    (Env.boxPush hsubV env dw) (cast hMIeq dval)]
              rw [boxPush_extend_notBox (xv := (⟨old, _⟩ : VarSymb × VarType)) M hsubV _ env val
                    rfl dw] at heq
              convert heq using 2
              subst h_x
              simp
        · -- passthrough: witness ≠ renamed var; both witness lookup and boxPush ignore it
          simp only [WFF.rename, dif_neg h_x, RModel.interpWFF]
          apply propext
          apply exists_congr
          intro dv
          have hwit : (⟨x_t.1, x_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
            rcases Finset.mem_insert.mp
              (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)) with heq | hV
            · rw [Prod.mk.injEq] at heq
              exact absurd (Prod.ext heq.1 (VarType.VTypeDia.inj heq.2)) h_x
            · exact hV
          have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro x x_in
            have hx_dia : x ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem x_in
            rcases Finset.mem_insert.mp (hsub hx_dia) with xeq | xV
            · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
              rw [← hveq] at xeq
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
            · exact xV
          rw [Env.extend_apply_ne (xv := (⟨new, _⟩ : VarSymb × VarType)) env val
                (q := ⟨x_t.1, x_t.2.VTypeDia⟩) (hqV := hwit),
              Env.extend_apply_ne (xv := (⟨old, _⟩ : VarSymb × VarType)) env val
                (q := ⟨x_t.1, x_t.2.VTypeDia⟩) (hqV := hwit),
              boxPush_extend_notBox (xv := (⟨new, _⟩ : VarSymb × VarType)) M hsubV _ env val
                rfl dv.fst,
              boxPush_extend_notBox (xv := (⟨old, _⟩ : VarSymb × VarType)) M hsubV _ env val
                rfl dv.fst]
      case VTypeProd =>
          -- product `repl_type = A×B`: passthrough (like Var/VTypeOne), shape-based `boxPush`.
          simp only [WFF.rename, RModel.interpWFF]
          apply propext
          apply exists_congr
          intro dv
          have hwit : (⟨x_t.1, x_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
            rcases Finset.mem_insert.mp
              (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)) with heq | hV
            · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
            · exact hV
          have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro x x_in
            have hx_dia : x ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem x_in
            rcases Finset.mem_insert.mp (hsub hx_dia) with xeq | xV
            · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
              rw [← hveq] at xeq
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
            · exact xV
          rw [Env.extend_apply_ne (xv := (⟨new, _⟩ : VarSymb × VarType)) env val
                (q := ⟨x_t.1, x_t.2.VTypeDia⟩) (hqV := hwit),
              Env.extend_apply_ne (xv := (⟨old, _⟩ : VarSymb × VarType)) env val
                (q := ⟨x_t.1, x_t.2.VTypeDia⟩) (hqV := hwit),
              boxPush_extend_notBoxShape (xv := (⟨new, _⟩ : VarSymb × VarType)) M hsubV _ env val
                (fun _ h => VarType.noConfusion h) dv.fst,
              boxPush_extend_notBoxShape (xv := (⟨old, _⟩ : VarSymb × VarType)) M hsubV _ env val
                (fun _ h => VarType.noConfusion h) dv.fst]
      -- Var / VTypeOne: `WFF.rename` passthrough; witness lookup + boxPush ignore the renamed var.
      all_goals
        simp only [WFF.rename, RModel.interpWFF]
        apply propext
        apply exists_congr
        intro dv
        have hwit : (⟨x_t.1, x_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
          rcases Finset.mem_insert.mp
            (hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)) with heq | hV
          · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
          · exact hV
        have hsubV : (VarCtx_box V_inner).1 ⊆ V.1 := by
          intro x x_in
          have hx_dia : x ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
            rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem x_in
          rcases Finset.mem_insert.mp (hsub hx_dia) with xeq | xV
          · rcases Finset.mem_image.mp x_in with ⟨⟨av, aS⟩, hav, hveq⟩
            rw [← hveq] at xeq
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at xeq
          · exact xV
        rw [Env.extend_apply_ne (xv := (⟨new, _⟩ : VarSymb × VarType)) env val
              (q := ⟨x_t.1, x_t.2.VTypeDia⟩) (hqV := hwit),
            Env.extend_apply_ne (xv := (⟨old, _⟩ : VarSymb × VarType)) env val
              (q := ⟨x_t.1, x_t.2.VTypeDia⟩) (hqV := hwit),
            boxPush_extend_notBox (xv := (⟨new, _⟩ : VarSymb × VarType)) M hsubV _ env val
              rfl dv.fst,
            boxPush_extend_notBox (xv := (⟨old, _⟩ : VarSymb × VarType)) M hsubV _ env val
              rfl dv.fst]
  | .pair_elim _ _ _ _ _ _ _ _ _ _, _ => sorry

/-- **Context-extension invariance** — a formula weakened by an unused variable interprets the same.
    All cases port from GModel: propositional/`box`/`dia`/non-collision quantifiers verbatim (the
    `◇` case's `posEval` is transparent to the env-rewrites); `atom`/`eq` via the term-level
    `interpTerm_ctx_ext`; the `all`/`ex` **collision** branches α-rename the bound var to a fresh
    symbol via `interpWFF_rename` (hence the `numNodes` termination measure).  Only the pair
    sector is deferred (`sorry`). -/
theorem interpWFF_ctx_ext_fuel (M : RModel σ) (k : ℕ) {V : VarCtx} (xv : VarSymb × VarType)
    (hk : sizeOf xv.2 ≤ k) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) (w : M.W)
    (env : M.Env V w) (a : M.interp xv.2 w) :
    M.interpWFF (WFF.ctx_ext xv hxv φ) w (env.extend xv hxv a) = M.interpWFF φ w env := by
  match φ with
  | .atom R =>
      simp only [WFF.ctx_ext, RModel.interpWFF]
      exact interpRel_ctx_ext M xv hxv R w env a Fin.elim0
  | .top => simp only [WFF.ctx_ext, RModel.interpWFF]
  | .bot => simp only [WFF.ctx_ext, RModel.interpWFF]
  | .and φ ψ =>
      simp only [WFF.ctx_ext, RModel.interpWFF]
      rw [interpWFF_ctx_ext_fuel M k xv hk hxv φ w env a,
          interpWFF_ctx_ext_fuel M k xv hk hxv ψ w env a]
  | .or φ ψ =>
      simp only [WFF.ctx_ext, RModel.interpWFF]
      rw [interpWFF_ctx_ext_fuel M k xv hk hxv φ w env a,
          interpWFF_ctx_ext_fuel M k xv hk hxv ψ w env a]
  | .imp φ ψ =>
      simp only [WFF.ctx_ext, RModel.interpWFF]
      rw [interpWFF_ctx_ext_fuel M k xv hk hxv φ w env a,
          interpWFF_ctx_ext_fuel M k xv hk hxv ψ w env a]
  | .eq s t =>
      simp only [WFF.ctx_ext, RModel.interpWFF]
      rw [interpTerm_ctx_ext M xv hxv s w env a, interpTerm_ctx_ext M xv hxv t w env a]
  | @WFF.box _ V_inner _ ψ hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      cases xt with
      | Var | VTypeOne | VTypeDia _ =>
          simp only [WFF.ctx_ext, RModel.interpWFF, boxPush_extend_notBox M hsub _ env a rfl]
      | VTypeBox U' =>
          have hkU' : sizeOf U' ≤ k := by
            have h : sizeOf (VarType.VTypeBox U') ≤ k := hk
            simp +arith at h; omega
          have hxv_inner : xs ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in_inner
            apply hxv
            obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
            cases q with
            | mk qv qT =>
              exact Finset.mem_image.mpr
                ⟨_, hsub (Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩), hq_eq⟩
          simp only [WFF.ctx_ext, RModel.interpWFF]
          apply propext
          apply forall_congr'
          intro w'
          rw [boxPush_extend_box M hxv_inner hsub _ env a w']
          exact iff_of_eq (interpWFF_ctx_ext_fuel M k ⟨xs, U'⟩ hkU' hxv_inner ψ w'.1
            (Env.boxPush hsub env w') (M.necEval a w'))
      | VTypeProd A B =>
          -- `WFF.ctx_ext ⟨xs,A×B⟩ (box ψ)` splits the product into fresh `⟨w1,A⟩,⟨w2,B⟩`, ctx_ext's
          -- by each, and re-pairs via `WFF.pairElim`; mirror the term-level boxterm-VTypeProd arm:
          -- reduce, distribute via `interpWFF_pairElim`, rewrite env, peel at fuel `k-1`.
          have hAB : sizeOf A + sizeOf B + 1 ≤ k := by
            have h : sizeOf (VarType.VTypeProd A B) ≤ k := hk
            simp +arith at h; omega
          have hkA : sizeOf A ≤ k - 1 := by omega
          have hkB : sizeOf B ≤ k - 1 := by omega
          have hkpos : 0 < k := by omega
          obtain ⟨a1, a2⟩ := a
          unfold WFF.ctx_ext
          dsimp only
          set av := VarCtx_to_VarSymbs V ∪ {xs} ∪ WFF.boundVars (WFF.box ψ hsub hnbe) with havdef
          set w1 := VarSymb.fresh av with hw1def
          set w2 := VarSymb.fresh (insert w1 av) with hw2def
          have hw1_V : w1 ∉ VarCtx_to_VarSymbs V := fun h =>
            VarSymb.fresh_not_mem av (Finset.mem_union_left _ (Finset.mem_union_left _ h))
          have hw2_iav : w2 ∉ insert w1 av := VarSymb.fresh_not_mem (insert w1 av)
          have hw2_V : w2 ∉ VarCtx_to_VarSymbs V := fun h =>
            hw2_iav (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
          have hw1w2 : w1 ≠ w2 := fun h => hw2_iav (h ▸ Finset.mem_insert_self _ _)
          have hw2_V1 : w2 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨w1, A⟩ V hw1_V) :=
            not_mem_VarSymbs_insert (fun h => hw1w2 h.symm) hw2_V
          have h_swap : VarCtx_insert ⟨w2, B⟩ (VarCtx_insert ⟨w1, A⟩ V hw1_V) hw2_V1
              = VarCtx_insert_twice ⟨w1, A⟩ ⟨w2, B⟩ V hw1_V hw2_V hw1w2 := by
            apply VarCtx_ext'
            change insert (⟨w2, B⟩ : VarSymb × VarType) (insert ⟨w1, A⟩ V.1)
                = insert ⟨w1, A⟩ (insert ⟨w2, B⟩ V.1)
            exact Finset.insert_comm _ _ _
          rw [interpWFF_pairElim M]
          simp only [RModel.interpWFF]
          rw [interpWFF_cast_term,
              unpairEnv_transport_eq M hw1_V hw2_V hw1w2 hxv hw2_V1 h_swap env a1 a2,
              interpWFF_ctx_ext_fuel M (k - 1) ⟨w2, B⟩ hkB hw2_V1 _ w
                (env.extend ⟨w1, A⟩ hw1_V a1) a2,
              interpWFF_ctx_ext_fuel M (k - 1) ⟨w1, A⟩ hkA hw1_V (WFF.box ψ hsub hnbe)
                w env a1]
          simp only [RModel.interpWFF]
  | @WFF.dia _ V_inner _ x_t hx_t ψ hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      have hwit := hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)
      cases xt with
      | Var | VTypeOne | VTypeDia _ =>
          simp only [WFF.ctx_ext, RModel.interpWFF]
          apply propext; apply exists_congr; intro dv
          rw [Env.extend_apply_ne env a _ hwit,
            boxPush_extend_notBox M (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a rfl]
      | VTypeBox U' =>
          have hkU' : sizeOf U' ≤ k := by
            have h : sizeOf (VarType.VTypeBox U') ≤ k := hk
            simp +arith at h; omega
          have hxv_inner : xs ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in_inner; apply hxv
            obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
            cases q with
            | mk qv qT =>
              have hbox_in_dia : (⟨qv, qT.VTypeBox⟩ : VarSymb × VarType)
                  ∈ (VarCtx_dia x_t V_inner hx_t).1 := by
                rw [VarCtx_dia_fst]
                exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩)
              exact Finset.mem_image.mpr ⟨_, hsub hbox_in_dia, hq_eq⟩
          have hxv_ne : xs ≠ x_t.1 := by
            intro h; apply hxv; rw [h]; exact Finset.mem_image.mpr ⟨_, hwit, rfl⟩
          have hxv_outer : xs ∉ VarCtx_to_VarSymbs (VarCtx_insert x_t V_inner hx_t) :=
            not_mem_VarSymbs_insert hxv_ne hxv_inner
          simp only [WFF.ctx_ext, RModel.interpWFF]
          apply propext; apply exists_congr; intro dv
          rw [Env.extend_apply_ne env a _ hwit,
              boxPush_extend_box M hxv_inner (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a,
              interpWFF_cast_term, Env.extend_comm,
              interpWFF_ctx_ext_fuel M k ⟨xs, U'⟩ hkU' hxv_outer ψ _ _ _]
      | VTypeProd A B =>
          -- product-typed extended var: split into fresh `⟨w1,A⟩,⟨w2,B⟩`, re-pair via `WFF.pairElim`
          -- (mirrors the box-VTypeProd arm; `pe_t = dia x_t hx_t ψ hsub hnbe`).
          have hAB : sizeOf A + sizeOf B + 1 ≤ k := by
            have h : sizeOf (VarType.VTypeProd A B) ≤ k := hk
            simp +arith at h; omega
          have hkA : sizeOf A ≤ k - 1 := by omega
          have hkB : sizeOf B ≤ k - 1 := by omega
          have hkpos : 0 < k := by omega
          obtain ⟨a1, a2⟩ := a
          unfold WFF.ctx_ext
          dsimp only
          set av := VarCtx_to_VarSymbs V ∪ {xs}
              ∪ WFF.boundVars (WFF.dia x_t hx_t ψ hsub hnbe) with havdef
          set w1 := VarSymb.fresh av with hw1def
          set w2 := VarSymb.fresh (insert w1 av) with hw2def
          have hw1_V : w1 ∉ VarCtx_to_VarSymbs V := fun h =>
            VarSymb.fresh_not_mem av (Finset.mem_union_left _ (Finset.mem_union_left _ h))
          have hw2_iav : w2 ∉ insert w1 av := VarSymb.fresh_not_mem (insert w1 av)
          have hw2_V : w2 ∉ VarCtx_to_VarSymbs V := fun h =>
            hw2_iav (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
          have hw1w2 : w1 ≠ w2 := fun h => hw2_iav (h ▸ Finset.mem_insert_self _ _)
          have hw2_V1 : w2 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨w1, A⟩ V hw1_V) :=
            not_mem_VarSymbs_insert (fun h => hw1w2 h.symm) hw2_V
          have h_swap : VarCtx_insert ⟨w2, B⟩ (VarCtx_insert ⟨w1, A⟩ V hw1_V) hw2_V1
              = VarCtx_insert_twice ⟨w1, A⟩ ⟨w2, B⟩ V hw1_V hw2_V hw1w2 := by
            apply VarCtx_ext'
            change insert (⟨w2, B⟩ : VarSymb × VarType) (insert ⟨w1, A⟩ V.1)
                = insert ⟨w1, A⟩ (insert ⟨w2, B⟩ V.1)
            exact Finset.insert_comm _ _ _
          rw [interpWFF_pairElim M]
          simp only [RModel.interpWFF]
          rw [interpWFF_cast_term,
              unpairEnv_transport_eq M hw1_V hw2_V hw1w2 hxv hw2_V1 h_swap env a1 a2,
              interpWFF_ctx_ext_fuel M (k - 1) ⟨w2, B⟩ hkB hw2_V1 _ w
                (env.extend ⟨w1, A⟩ hw1_V a1) a2,
              interpWFF_ctx_ext_fuel M (k - 1) ⟨w1, A⟩ hkA hw1_V
                (WFF.dia x_t hx_t ψ hsub hnbe) w env a1]
          simp only [RModel.interpWFF]
  | @WFF.all _ _ x hx ψ =>
      by_cases h_col : xv.1 = x.1
      · -- Collision: `ctx_ext` α-renames the bound var `x.1 → fresh`; peel
        -- `h_swap ▸` (cast_term), commute `xv` out (extend_comm), strip `ctx_ext`, strip the rename.
        simp only [WFF.ctx_ext, dif_pos h_col]
        set avoid : Finset VarSymb := VarCtx_to_VarSymbs V ∪ {xv.1} ∪ WFF.boundVars ψ with havoid
        set x'_sym : VarSymb := VarSymb.fresh avoid with hx'sym
        have hx'_avoid : x'_sym ∉ avoid := VarSymb.fresh_not_mem _
        have hx'_V : x'_sym ∉ VarCtx_to_VarSymbs V := fun h =>
          hx'_avoid (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have hx'_ne_xv : x'_sym ≠ xv.1 := fun h =>
          hx'_avoid (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
        have hx'_nb_ψ : x'_sym ∉ WFF.boundVars ψ := fun h => hx'_avoid (Finset.mem_union_right _ h)
        have hWdef : VarCtx_insert x V hx
            = VarCtx_insert (⟨x.1, x.2⟩ : VarSymb × VarType) V hx := rfl
        have hxv_x' : xv.1 ∉ VarCtx_to_VarSymbs
            (VarCtx_insert (⟨x'_sym, x.2⟩ : VarSymb × VarType) V hx'_V) :=
          not_mem_VarSymbs_insert (fun h => hx'_ne_xv h.symm) hxv
        apply propext
        apply forall_congr'
        intro val
        rw [interpWFF_cast_term, Env.extend_comm,
            interpWFF_ctx_ext_fuel M k xv hk hxv_x'
              (WFF.rename x.1 x'_sym x.2 V (VarCtx_insert x V hx) hx hx'_V hWdef ψ hx'_nb_ψ) _ _ _,
            interpWFF_rename M hx hx'_V hWdef ψ hx'_nb_ψ w env val]
      · have hxv_x : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) :=
          not_mem_VarSymbs_insert h_col hxv
        simp only [WFF.ctx_ext, RModel.interpWFF, dif_neg h_col]
        apply propext
        apply forall_congr'
        intro val
        rw [interpWFF_cast_term, Env.extend_comm, interpWFF_ctx_ext_fuel M k xv hk hxv_x ψ _ _ _]
  | @WFF.ex _ _ x hx ψ =>
      by_cases h_col : xv.1 = x.1
      · -- Collision: symmetric to `.all`; α-rename the bound var, then peel the same chain.
        simp only [WFF.ctx_ext, dif_pos h_col]
        set avoid : Finset VarSymb := VarCtx_to_VarSymbs V ∪ {xv.1} ∪ WFF.boundVars ψ with havoid
        set x'_sym : VarSymb := VarSymb.fresh avoid with hx'sym
        have hx'_avoid : x'_sym ∉ avoid := VarSymb.fresh_not_mem _
        have hx'_V : x'_sym ∉ VarCtx_to_VarSymbs V := fun h =>
          hx'_avoid (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have hx'_ne_xv : x'_sym ≠ xv.1 := fun h =>
          hx'_avoid (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
        have hx'_nb_ψ : x'_sym ∉ WFF.boundVars ψ := fun h => hx'_avoid (Finset.mem_union_right _ h)
        have hWdef : VarCtx_insert x V hx
            = VarCtx_insert (⟨x.1, x.2⟩ : VarSymb × VarType) V hx := rfl
        have hxv_x' : xv.1 ∉ VarCtx_to_VarSymbs
            (VarCtx_insert (⟨x'_sym, x.2⟩ : VarSymb × VarType) V hx'_V) :=
          not_mem_VarSymbs_insert (fun h => hx'_ne_xv h.symm) hxv
        apply propext
        apply exists_congr
        intro val
        rw [interpWFF_cast_term, Env.extend_comm,
            interpWFF_ctx_ext_fuel M k xv hk hxv_x'
              (WFF.rename x.1 x'_sym x.2 V (VarCtx_insert x V hx) hx hx'_V hWdef ψ hx'_nb_ψ) _ _ _,
            interpWFF_rename M hx hx'_V hWdef ψ hx'_nb_ψ w env val]
      · have hxv_x : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) :=
          not_mem_VarSymbs_insert h_col hxv
        simp only [WFF.ctx_ext, RModel.interpWFF, dif_neg h_col]
        apply propext
        apply exists_congr
        intro val
        rw [interpWFF_cast_term, Env.extend_comm, interpWFF_ctx_ext_fuel M k xv hk hxv_x ψ _ _ _]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => sorry
termination_by (k, WFF.numNodes φ)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; simp only [WFF.numNodes, WFF.numNodes_rename]; omega)
    | (apply Prod.Lex.left; omega)

/-- **Context-extension invariance** (public form — instantiates the fuel at `sizeOf xv.2`). -/
theorem interpWFF_ctx_ext (M : RModel σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) (w : M.W) (env : M.Env V w)
    (a : M.interp xv.2 w) :
    M.interpWFF (WFF.ctx_ext xv hxv φ) w (env.extend xv hxv a) = M.interpWFF φ w env :=
  interpWFF_ctx_ext_fuel M (sizeOf xv.2) xv le_rfl hxv φ w env a

/-- **Soundness of `K_dia`** (the `◇`-elimination / K-rule for `◇`).  End-to-end spike: given the
    sub-derivation's entailment `ih`, the `K_dia` conclusion is `RModel`-valid.  Ports the GModel
    proof verbatim, with `dv ∈ posEval …` in place of `posMem … dv`. -/
theorem K_dia_sound {V W : VarCtx} (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V)
    (hsub : (VarCtx_dia x V hx).1 ⊆ W.1)
    (hnbe : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x V hx).1)
    {φ ψ : WFF σ (VarCtx_insert x V hx)} {Γ : Finset (WFF σ V)}
    (ih : Entails.{u} (WFF.ctx_ext_Finset x hx Γ ∪ {ψ}) φ) :
    Entails.{u} (WFF.box_Finset (box_subs_of_dia_subs hsub) (in_box_of_in_dia hnbe) Γ
        ∪ {WFF.dia x hx ψ hsub hnbe})
      (WFF.dia x hx φ hsub hnbe) := by
  intro M w env hΓ
  obtain ⟨dv, hposEval, hψ⟩ := hΓ (WFF.dia x hx ψ hsub hnbe)
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  refine ⟨dv, hposEval, ih M dv.1.1 _ (fun χ hχ => ?_)⟩
  rcases Finset.mem_union.mp hχ with hχΓ | hχψ
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hχΓ
    rw [interpWFF_ctx_ext M x hx γ]
    exact hΓ (WFF.box γ _ _)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)) dv.1
  · rw [Finset.mem_singleton] at hχψ
    subst hχψ
    exact hψ

/-! ### Semantic substitution (`substVar`) — term level

Ports `Soundness2.lean:1287-1655` (GModel→RModel).  The GModel β-laws are swapped for the RModel
levers: `nec_beta` ⇒ `interpTerm_boxterm` + `necEval_interpTermNec` (box-β the theorem) after a
`nec_inj` reduction to sections; `pos_beta`/`posMem` ⇒ `mapPos_eval`/`∈ posEval` after a `pos_inj`
reduction to realization sets.  All context gymnastics / `Env` plumbing is verbatim. -/

/-- Cast a `boxterm`'s **inner** context (model-free; verbatim from `Soundness2`). -/
theorem boxterm_inner_cast {V_inner V_inner' W : VarCtx} {S : VarType}
    (h : V_inner = V_inner') (tt : Term σ V_inner S)
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hnbe : ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    Term.boxterm (h ▸ tt) (h ▸ hsub) (h ▸ hnbe) = Term.boxterm tt hsub hnbe := by
  subst h; rfl

/-- In the pair-free branch `Term.substVar = Term.ctx_rest` (model-free; verbatim). -/
theorem substVar_eq_ctx_rest' {V : VarCtx} {x : VarSymb} {S S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S) (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S') :
    Term.substVar hx s t = Term.ctx_rest hx hpf s t := by
  simp only [Term.substVar]
  conv_lhs => unfold Term.ctx_rest_MU
  split
  · rfl
  · exfalso; rename_i z V1 V2 hzmem heq; rw [hpf] at heq; simp at heq

mutual
/-- **Term-level semantic substitution** (base for `interpWFF_substVar`; pair-free). -/
theorem interpTerm_substVar (M : RModel σ) {V : VarCtx} {x : VarSymb} {S S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S) (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S') (w : M.W) (env : M.Env V w) :
    M.interpTerm (Term.substVar hx s t) w env
      = M.interpTerm t w (env.extend ⟨x, S⟩ hx (M.interpTerm s w env)) := by
  match t with
  | .var ⟨v, hv⟩ =>
      rw [Term.substVar_var hx s hpf v hv]
      split_ifs with h_eq
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
        simp [RModel.interpTerm, Env.extend]
      · simp only [RModel.interpTerm, Env.extend, dif_neg h_eq]
  | .unit => rw [Term.substVar_unit hx s hpf]; simp only [RModel.interpTerm]
  | .func f =>
      rw [Term.substVar_func hx s hpf f]
      simp only [RModel.interpTerm]
      exact interpFunc_substVar M hx hpf s f w env Fin.elim0
  | .pair a b =>
      rw [Term.substVar_pair hx s hpf a b]
      simp only [RModel.interpTerm]
      rw [interpTerm_substVar M hx hpf s a w env, interpTerm_substVar M hx hpf s b w env]
  | @Term.boxterm _ V_inner S_inner _ tt hsub hnbe =>
      cases S with
      | Var | VTypeOne | VTypeDia _ =>
          -- Non-box `S`: passthrough (`x` cannot reach the all-box inner context).
          have hx_notin : x ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in
            obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_in
            simp only at hx'_eq; subst hx'_eq
            rcases Finset.mem_insert.mp (hsub (Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩))
              with h_eq | h_in_V
            · exact VarType.noConfusion (Prod.mk.inj h_eq).2
            · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
          rw [substVar_eq_ctx_rest' hx hpf s (Term.boxterm tt hsub hnbe)]
          simp only [Term.ctx_rest, dif_neg hx_notin]
          rw [interpTerm_boxterm, interpTerm_boxterm]
          apply M.nec_inj
          funext w'
          rw [necEval_interpTermNec, necEval_interpTermNec]
          congr 1
          exact (boxPush_extend_notBox M _ hsub env (M.interpTerm s w env) rfl w').symm
      | VTypeBox U =>
          by_cases hx_in : x ∈ VarCtx_to_VarSymbs V_inner
          · have hxU_in : (⟨x, U⟩ : VarSymb × VarType) ∈ V_inner.1 := by
              obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp hx_in
              simp only at hx'_eq; rw [hx'_eq] at hx'T'
              rcases Finset.mem_insert.mp
                  (hsub (Finset.mem_image.mpr ⟨⟨x, T'⟩, hx'T', rfl⟩)) with h_eq | h_in_V
              · have hT : T' = U := VarType.VTypeBox.inj (Prod.mk.inj h_eq).2
                subst hT; exact hx'T'
              · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩) hx
            match s with
            | @Term.boxterm _ V_s _ _ s_inner s_hsub s_hnbe =>
                have hV_s : V_s = VarCtx_erase V_inner ⟨x, U⟩ :=
                  ctx_rest_box_V_s_eq hxU_in hsub hnbe s_hsub s_hnbe
                have hx_s : x ∉ VarCtx_to_VarSymbs V_s := by
                  rw [hV_s]; exact VarCtx_erase_fresh hxU_in
                have h_V_inner_eq : V_inner = VarCtx_insert ⟨x, U⟩ V_s hx_s := by
                  subst hV_s; exact (VarCtx_insert_erase hxU_in hx_s).symm
                subst h_V_inner_eq
                have hred : Term.substVar hx (Term.boxterm s_inner s_hsub s_hnbe)
                      (Term.boxterm tt hsub hnbe)
                    = Term.boxterm (Term.substVar hx_s s_inner tt) s_hsub s_hnbe :=
                  Term.substVar_boxterm hx_s hx s_hsub s_hnbe hpf s_inner tt
                rw [hred]
                set VAL := M.interpTerm (Term.boxterm s_inner s_hsub s_hnbe) w env with hVAL
                rw [interpTerm_boxterm, interpTerm_boxterm]
                apply M.nec_inj
                funext w'
                rw [necEval_interpTermNec, necEval_interpTermNec]
                by_cases hpf_m : (VarCtx_insert ⟨x, U⟩ V_s hx_s).firstPairVar = none
                · rw [interpTerm_substVar M hx_s hpf_m s_inner tt w'.1 (Env.boxPush s_hsub env w'),
                      boxPush_extend_box M hx_s s_hsub hsub env VAL w', hVAL,
                      interpTerm_boxterm, necEval_interpTermNec]
                · sorry  -- inner pair-ful context: pair splitting-translation plug-in
            | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
                exfalso
                have h_sz : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈ V.1 := by
                  rw [← sw2eq]; exact Finset.mem_insert_self _ _
                exact VarCtx.firstPairVar_none_no_pair hpf (Finset.mem_insert_of_mem h_sz)
          · rw [substVar_eq_ctx_rest' hx hpf s (Term.boxterm tt hsub hnbe)]
            simp only [Term.ctx_rest, dif_neg hx_in]
            rw [interpTerm_boxterm, interpTerm_boxterm]
            apply M.nec_inj
            funext w'
            rw [necEval_interpTermNec, necEval_interpTermNec]
            congr 1
            funext p hp
            have hne : (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ≠ ⟨x, U.VTypeBox⟩ := by
              intro h
              rw [Prod.mk.injEq] at h
              exact hx_in (h.1 ▸ Finset.mem_image.mpr ⟨p, hp, rfl⟩)
            simp only [Env.boxPush, Env.extend, dif_neg hne]
      | VTypeProd A B => sorry
  | @Term.diaterm _ V_inner S_inner _ xv_t hxv_t tt hsub hnbe =>
      by_cases h_xv_eq_x : xv_t.1 = x
      · -- modal-beta: the dia witness IS the substituted variable ⟹ `S = xv_t.2.dia`.
        have hxv_in_Vext : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
            ∈ (VarCtx_insert ⟨x, S⟩ V hx).1 := by
          apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        have h_S_eq : S = xv_t.2.VTypeDia := by
          rcases Finset.mem_insert.mp hxv_in_Vext with h_eq | h_in_V
          · exact ((Prod.mk.inj h_eq).2).symm
          · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, h_xv_eq_x⟩) hx
        subst h_S_eq
        subst h_xv_eq_x
        match s with
        | @Term.diaterm _ V_inner_s _ _ xv_s hxv_s tt_s hsub_s h_no_extras_s =>
            have h_V_inner_eq : V_inner_s = V_inner := by
              apply VarCtx_box_inj; apply VarCtx_ext'; apply Finset.ext; intro p
              constructor
              · intro hp_s
                have hp_V : p ∈ V.1 := by
                  apply hsub_s; rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_s
                have hp_box : VarType.isBox p.2 = true := by
                  rcases Finset.mem_image.mp hp_s with ⟨q, _, hq_eq⟩
                  rw [← hq_eq]; simp [VarType.isBox]
                have hp_dia := hnbe p (Finset.mem_insert_of_mem hp_V) hp_box
                rw [VarCtx_dia_fst] at hp_dia
                rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
                · subst h_eq; simp [VarType.isBox] at hp_box
                · exact h_in_box
              · intro hp
                have hp_Vext : p ∈ (VarCtx_insert ⟨xv_t.1, xv_t.2.VTypeDia⟩ V hx).1 := by
                  apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp
                have hp_box : VarType.isBox p.2 = true := by
                  rcases Finset.mem_image.mp hp with ⟨q, _, hq_eq⟩
                  rw [← hq_eq]; simp [VarType.isBox]
                have hp_V : p ∈ V.1 := by
                  rcases Finset.mem_insert.mp hp_Vext with h_eq | h_V
                  · subst h_eq; simp [VarType.isBox] at hp_box
                  · exact h_V
                have hp_dia := h_no_extras_s p hp_V hp_box
                rw [VarCtx_dia_fst] at hp_dia
                rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
                · subst h_eq; simp [VarType.isBox] at hp_box
                · exact h_in_box
            cases h_V_inner_eq
            have h_xv_ne_xv_s : xv_t.1 ≠ xv_s.1 := fun h => hx
              (Finset.mem_image.mpr ⟨⟨xv_s.1, xv_s.2.VTypeDia⟩,
                hsub_s (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _), h.symm⟩)
            have hxv_s_outer : xv_s.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_t V_inner hxv_t) :=
              not_mem_VarSymbs_insert (fun h => h_xv_ne_xv_s h.symm) hxv_s
            have hxv_xv_s_outer : xv_t.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s) :=
              not_mem_VarSymbs_insert h_xv_ne_xv_s hxv_t
            have h_reorder : VarCtx_insert xv_s (VarCtx_insert xv_t V_inner hxv_t) hxv_s_outer
                = VarCtx_insert xv_t (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer := by
              apply VarCtx_ext'; exact Finset.insert_comm _ _ _
            have h_reform : VarCtx_insert xv_t (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer
                = VarCtx_insert (⟨xv_t.1, xv_t.2⟩ : VarSymb × VarType)
                    (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer := rfl
            rw [Term.substVar_diaterm_modal_beta xv_t hxv_t hx xv_s hxv_s h_xv_ne_xv_s tt hsub hnbe
                tt_s hsub_s h_no_extras_s hpf hxv_s_outer hxv_xv_s_outer hxv_xv_s_outer
                h_reorder h_reform]
            -- ◇◇-composition: `pos_inj` + `mapPos_eval` (twice — the inner one replaces GModel's
            -- `pos_beta`); the reordered body reduces via `interpTerm_substVar` + cast-strip +
            -- drop `xv_s`.  (Pair-free branch.)
            simp only [RModel.interpTerm]
            by_cases hpf'' : (VarCtx_insert (⟨xv_t.1, xv_t.2⟩ : VarSymb × VarType)
                (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer).firstPairVar = none
            · apply M.pos_inj
              ext ru
              rw [M.mapPos_eval _ _ ru, M.mapPos_eval _ _ ru]
              constructor
              · rintro ⟨v, hmem_v, hbody_v⟩
                rw [interpTerm_substVar M hxv_xv_s_outer hpf'' tt_s,
                    interpTerm_cast_term, Env.extend_comm,
                    interpTerm_ctx_ext M xv_s hxv_s_outer tt] at hbody_v
                refine ⟨M.interpTerm tt_s ↑ru.fst
                    ((Env.boxPush (fun p hp => hsub_s (Finset.mem_insert_of_mem hp)) env ru.fst).extend
                      xv_s hxv_s v), ?_, ?_⟩
                · simp only [Env.extend, dif_pos]
                  rw [M.mapPos_eval]
                  exact ⟨v, hmem_v, rfl⟩
                · rw [boxPush_extend_notBox (xv := (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)) M
                      (fun p hp => hsub_s (Finset.mem_insert_of_mem hp)) _ env _
                      rfl ru.fst]
                  exact hbody_v
              · rintro ⟨a, hmem_a, hbody_a⟩
                simp only [Env.extend, dif_pos] at hmem_a
                rw [M.mapPos_eval] at hmem_a
                obtain ⟨v', hmem', htt'⟩ := hmem_a
                refine ⟨v', hmem', ?_⟩
                rw [interpTerm_substVar M hxv_xv_s_outer hpf'' tt_s,
                    interpTerm_cast_term, Env.extend_comm,
                    interpTerm_ctx_ext M xv_s hxv_s_outer tt, htt']
                rw [boxPush_extend_notBox (xv := (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)) M
                    (fun p hp => hsub_s (Finset.mem_insert_of_mem hp)) _ env _
                    rfl ru.fst] at hbody_a
                exact hbody_a
            · sorry  -- pair-ful reordered context (deferred with the pair track)
        | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
            exfalso
            have h_sz : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈ V.1 := by
              rw [← sw2eq]; exact Finset.mem_insert_self _ _
            exact VarCtx.firstPairVar_none_no_pair hpf (Finset.mem_insert_of_mem h_sz)
      · by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
        · cases S with
          | Var | VTypeOne | VTypeDia _ | VTypeProd _ _ =>
              exfalso
              obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
              simp only at hx'_eq; rw [hx'_eq] at hx'T'
              have hbox : (⟨x, T'.VTypeBox⟩ : VarSymb × VarType)
                  ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
                rw [VarCtx_dia_fst]
                exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨x, T'⟩, hx'T', rfl⟩)
              rcases Finset.mem_insert.mp (hsub hbox) with h_eq | h_in_V
              · exact VarType.noConfusion (Prod.mk.inj h_eq).2
              · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
          | VTypeBox U =>
              have hxU_in : (⟨x, U⟩ : VarSymb × VarType) ∈ V_inner.1 := by
                obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
                simp only at hx'_eq; rw [hx'_eq] at hx'T'
                have hbox : (⟨x, T'.VTypeBox⟩ : VarSymb × VarType)
                    ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
                  rw [VarCtx_dia_fst]
                  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨x, T'⟩, hx'T', rfl⟩)
                rcases Finset.mem_insert.mp (hsub hbox) with h_eq | h_in_V
                · have hT : T' = U := VarType.VTypeBox.inj (Prod.mk.inj h_eq).2
                  subst hT; exact hx'T'
                · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩) hx
              match s with
              | @Term.boxterm _ V_s _ _ s_inner s_hsub s_hnbe =>
                  have hV_s : V_s = VarCtx_erase V_inner ⟨x, U⟩ :=
                    ctx_rest_dia_V_s_eq hxU_in hsub hnbe s_hsub s_hnbe
                  have hx_s : x ∉ VarCtx_to_VarSymbs V_s := by
                    rw [hV_s]; exact VarCtx_erase_fresh hxU_in
                  have hxv_V : xv_t.1 ∉ VarCtx_to_VarSymbs V_s := by
                    rw [hV_s]; exact fun h => hxv_t (VarCtx_to_VarSymbs_erase_subset h)
                  have h_V_inner_eq : V_inner = VarCtx_insert ⟨x, U⟩ V_s hx_s := by
                    subst hV_s; exact (VarCtx_insert_erase hxU_in hx_s).symm
                  subst h_V_inner_eq
                  have hx_out : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_t V_s hxv_V) :=
                    not_mem_VarSymbs_insert (fun h => h_xv_eq_x h.symm) hx_s
                  have h_reorder : VarCtx_insert xv_t (VarCtx_insert ⟨x, U⟩ V_s hx_s) hxv_t
                      = VarCtx_insert ⟨x, U⟩ (VarCtx_insert xv_t V_s hxv_V) hx_out :=
                    VarCtx_insert_comm hxv_t hx_out
                  have P' : (VarCtx_dia xv_t V_s hxv_V).1 ⊆ V.1 := by
                    intro q hq
                    rw [VarCtx_dia_fst] at hq
                    rcases Finset.mem_insert.mp hq with h_eq | h_box
                    · have hq_dia : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
                          ∈ (VarCtx_dia xv_t (VarCtx_insert ⟨x, U⟩ V_s hx_s) hxv_t).1 := by
                        rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
                      rcases Finset.mem_insert.mp (hsub hq_dia) with h_eq2 | h_V
                      · exact absurd (congrArg Prod.fst h_eq2) h_xv_eq_x
                      · rw [h_eq]; exact h_V
                    · exact s_hsub h_box
                  have Q' : ∀ p ∈ V.1, VarType.isBox p.2 = true
                      → p ∈ (VarCtx_dia xv_t V_s hxv_V).1 := by
                    intro p hp hp_box
                    have hin := hnbe p (Finset.mem_insert_of_mem hp) hp_box
                    rw [VarCtx_dia_fst, VarCtx_box_fst_insert] at hin
                    rw [VarCtx_dia_fst]
                    rcases Finset.mem_insert.mp hin with h_dia | h_rest
                    · exact Finset.mem_insert.mpr (Or.inl h_dia)
                    · rcases Finset.mem_insert.mp h_rest with h_xU | h_box
                      · exact absurd (Finset.mem_image.mpr ⟨p, hp, congrArg Prod.fst h_xU⟩) hx
                      · exact Finset.mem_insert_of_mem h_box
                  rw [Term.substVar_diaterm_base hx_s hx s_hsub s_hnbe hpf s_inner xv_t
                      h_xv_eq_x hxv_V hxv_t hx_out h_reorder tt hsub hnbe P' Q']
                  have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 :=
                    P' (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)
                  set VAL := M.interpTerm (Term.boxterm s_inner s_hsub s_hnbe) w env with hVAL
                  simp only [RModel.interpTerm]
                  apply M.pos_inj
                  ext ru
                  rw [M.mapPos_eval _ _ ru, M.mapPos_eval _ _ ru]
                  apply exists_congr; intro v
                  by_cases hpf_m :
                      (VarCtx_insert ⟨x, U⟩ (VarCtx_insert xv_t V_s hxv_V) hx_out).firstPairVar = none
                  · rw [interpTerm_substVar M hx_out hpf_m,
                        interpTerm_ctx_ext M xv_t hxv_V s_inner ru.1.1
                          (Env.boxPush (fun p hp => P' (Finset.mem_insert_of_mem hp)) env ru.1) v,
                        interpTerm_cast_term,
                        Env.extend_comm
                          (Env.boxPush (fun p hp => P' (Finset.mem_insert_of_mem hp)) env ru.1)
                          hxv_V hx_s hx_out hxv_t v _ h_reorder.symm,
                        Env.extend_apply_ne (xv := (⟨x, U.VTypeBox⟩ : VarSymb × VarType)) env VAL _ hwit,
                        boxPush_extend_box M hx_s s_hsub
                          (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env VAL ru.1,
                        hVAL, interpTerm_boxterm, necEval_interpTermNec]
                  · sorry  -- inner pair-ful context: pair splitting-translation plug-in
              | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
                  exfalso
                  have h_sz : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈ V.1 := by
                    rw [← sw2eq]; exact Finset.mem_insert_self _ _
                  exact VarCtx.firstPairVar_none_no_pair hpf (Finset.mem_insert_of_mem h_sz)
        · rw [substVar_eq_ctx_rest' hx hpf s (Term.diaterm xv_t hxv_t tt hsub hnbe)]
          simp only [Term.ctx_rest, dif_neg h_xv_eq_x, dif_neg h_x_in, RModel.interpTerm]
          have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 := by
            have hins := hsub (show (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
                ∈ (VarCtx_dia xv_t V_inner hxv_t).1 from by
                  rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)
            rcases Finset.mem_insert.mp hins with h_eq | h_V
            · exact absurd (congrArg Prod.fst h_eq) h_xv_eq_x
            · exact h_V
          have hsub_base : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro q hq
            have hq_dia : q ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hq
            rcases Finset.mem_insert.mp (hsub hq_dia) with h_eq | h_V
            · exfalso
              rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
              exact h_x_in ((Prod.mk.inj (hpq.trans h_eq)).1 ▸ Finset.mem_image.mpr ⟨p, hp, rfl⟩)
            · exact h_V
          congr 1
          · funext ru v
            congr 2
            exact (boxPush_extend_notin M hsub_base
                (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env
                (M.interpTerm s w env) h_x_in ru).symm
          · rw [Env.extend_apply_ne (xv := (⟨x, S⟩ : VarSymb × VarType)) env
                (M.interpTerm s w env) _ hwit]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => sorry

/-- Companion of `interpTerm_substVar` for the `func` case (over `Func.ctx_rest`). -/
theorem interpFunc_substVar (M : RModel σ) {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S) {N : ℕ} (f : Func σ (VarCtx_insert ⟨x, S⟩ V hx) N)
    (w : M.W) (env : M.Env V w) (args : Fin N → M.D w) :
    M.interpFunc (Func.ctx_rest hx hpf s f) w env args
      = M.interpFunc f w (env.extend ⟨x, S⟩ hx (M.interpTerm s w env)) args := by
  match f with
  | .F h => simp only [Func.ctx_rest, RModel.interpFunc]
  | .eval g t =>
      simp only [Func.ctx_rest, RModel.interpFunc]
      rw [← substVar_eq_ctx_rest' hx hpf s t, interpTerm_substVar M hx hpf s t w env]
      exact interpFunc_substVar M hx hpf s g w env _
end

/-- Relation-level `substVar` invariance (base for the `atom` case; via `interpTerm_substVar`). -/
theorem interpRel_substVar (M : RModel σ) {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S) {n : ℕ} (R : Rel σ (VarCtx_insert ⟨x, S⟩ V hx) n)
    (w : M.W) (env : M.Env V w) (args : Fin n → M.D w) :
    M.interpRel (Rel.ctx_rest hx hpf s R) w env args
      = M.interpRel R w (env.extend ⟨x, S⟩ hx (M.interpTerm s w env)) args := by
  induction R with
  | R hr => simp only [Rel.ctx_rest, RModel.interpRel]
  | eval R' t ih =>
      simp only [Rel.ctx_rest, RModel.interpRel]
      rw [← substVar_eq_ctx_rest' hx hpf s t, interpTerm_substVar M hx hpf s t w env]
      exact ih _

/-! ### Semantic substitution — WFF level (ports `Soundness2.lean:1657-2197`) -/

/-- `WFF.numNodes` is context-invariant, so it is preserved by a context-equality cast
    (used in the `interpWFF_substVar` termination measure). -/
private theorem WFF_numNodes_cast {A B : VarCtx} (h : A = B) (ψ : WFF σ A) :
    WFF.numNodes (h ▸ ψ) = WFF.numNodes ψ := by subst h; rfl

/-- `WFF.substVar` unfolds to `WFF.ctx_rest` in the pair-free branch. -/
theorem WFF_substVar_eq_ctx_rest' {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S) (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) :
    WFF.substVar hx s φ = WFF.ctx_rest hx hpf s φ := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · rfl
  · exfalso; rename_i z V1 V2 hzmem heq; rw [hpf] at heq; simp at heq

/-- Passthrough for `substVar` into a `box`: when `x ∉ V_inner`, substitution never reaches the
    box body (side-conditions proof-irrelevant). -/
theorem WFF_substVar_box_notin {V V_inner : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (t : Term σ V S) (ψ : WFF σ V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hnbe : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1, VarType.isBox p.2 = true
              → p ∈ (VarCtx_box V_inner).1)
    (hx_notin : x ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_box V_inner).1 ⊆ V.1)
    (h_no_extras' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1) :
    WFF.substVar hx t (WFF.box ψ hsub hnbe) = WFF.box ψ hsub' h_no_extras' := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_box_arm]
    rw [dif_neg hx_notin]
  · exfalso; rename_i z V1 V2 hzmem heq; rw [hpf] at heq; simp at heq

/-- Passthrough for `substVar` into a `dia`: when `xv.1 ≠ x` and `x ∉ V_inner`, substitution
    never reaches the diamond body. -/
theorem WFF_substVar_dia_notin {V V_inner : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (t : Term σ V S) (xv : VarSymb × VarType) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V_inner)
    (ψ : WFF σ (VarCtx_insert xv V_inner hxv))
    (hsub : (VarCtx_dia xv V_inner hxv).1 ⊆ (VarCtx_insert ⟨x, S⟩ V hx).1)
    (hnbe : ∀ p ∈ (VarCtx_insert ⟨x, S⟩ V hx).1, VarType.isBox p.2 = true
              → p ∈ (VarCtx_dia xv V_inner hxv).1)
    (h_xv_ne_x : xv.1 ≠ x) (hx_notin : x ∉ VarCtx_to_VarSymbs V_inner)
    (hsub' : (VarCtx_dia xv V_inner hxv).1 ⊆ V.1)
    (h_no_extras' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia xv V_inner hxv).1) :
    WFF.substVar hx t (WFF.dia xv hxv ψ hsub hnbe) = WFF.dia xv hxv ψ hsub' h_no_extras' := by
  simp only [WFF.substVar]
  conv_lhs => unfold WFF.ctx_rest_MU
  split
  · conv_lhs => unfold WFF.ctx_rest
    dsimp only
    simp only [WFF.ctx_rest_dia_arm]
    rw [dif_neg h_xv_ne_x, dif_neg hx_notin]
  · exfalso; rename_i z V1 V2 hzmem heq; rw [hpf] at heq; simp at heq

/-- Lexicographic step for the `(diaCount, numNodes)` termination measure. -/
private theorem lex_of_le_lt {a₁ a₂ b₁ b₂ : ℕ} (h1 : a₁ ≤ b₁) (h2 : a₂ < b₂) :
    Prod.Lex (· < ·) (· < ·) (a₁, a₂) (b₁, b₂) := by
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ h2

/-- **Semantic substitution.**  Interpreting `φ[t/x]` = interpreting `φ` in the environment
    extended by `t`'s value (pair-free fragment). -/
theorem interpWFF_substVar (M : RModel σ) {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (t : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) (w : M.W) (env : M.Env V w) :
    M.interpWFF (WFF.substVar hx t φ) w env
      = M.interpWFF φ w (env.extend ⟨x, S⟩ hx (M.interpTerm t w env)) := by
  match φ with
  | .top => rw [WFF.substVar_top hx t hpf]; simp only [RModel.interpWFF]
  | .bot => rw [WFF.substVar_bot hx t hpf]; simp only [RModel.interpWFF]
  | .and φ ψ =>
      rw [WFF.substVar_and hx t hpf φ ψ]
      simp only [RModel.interpWFF]
      rw [interpWFF_substVar M hx hpf t φ w env, interpWFF_substVar M hx hpf t ψ w env]
  | .or φ ψ =>
      rw [WFF.substVar_or hx t hpf φ ψ]
      simp only [RModel.interpWFF]
      rw [interpWFF_substVar M hx hpf t φ w env, interpWFF_substVar M hx hpf t ψ w env]
  | .imp φ ψ =>
      rw [WFF.substVar_imp hx t hpf φ ψ]
      simp only [RModel.interpWFF]
      rw [interpWFF_substVar M hx hpf t φ w env, interpWFF_substVar M hx hpf t ψ w env]
  | .eq t1 t2 =>
      rw [WFF.substVar_eq hx t hpf t1 t2]
      simp only [RModel.interpWFF]
      rw [interpTerm_substVar M hx hpf t t1 w env, interpTerm_substVar M hx hpf t t2 w env]
  | .atom R =>
      rw [WFF.substVar_atom hx t hpf R]
      simp only [RModel.interpWFF]
      exact interpRel_substVar M hx hpf t R w env Fin.elim0
  | @WFF.all _ _ y hy ψ =>
      have hy_ne : y.1 ≠ x := fun h => hy (by
        rw [VarCtx_to_VarSymbs_insert, h]; exact Finset.mem_insert_self _ _)
      have hxa_V : y.1 ∉ VarCtx_to_VarSymbs V := fun h => hy (by
        rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem h)
      have hx_xaV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert y V hxa_V) :=
        not_mem_VarSymbs_insert (fun h => hy_ne h.symm) hx
      have h_reorder : VarCtx_insert y (VarCtx_insert ⟨x, S⟩ V hx) hy
          = VarCtx_insert ⟨x, S⟩ (VarCtx_insert y V hxa_V) hx_xaV :=
        VarCtx_insert_comm hy hx_xaV
      rw [WFF.substVar_all hx t hpf y hy hxa_V hx_xaV h_reorder ψ]
      simp only [RModel.interpWFF]
      apply propext; apply forall_congr'; intro a
      by_cases hpf_m :
          (VarCtx_insert ⟨x, S⟩ (VarCtx_insert y V hxa_V) hx_xaV).firstPairVar = none
      · rw [interpWFF_substVar M hx_xaV hpf_m, interpTerm_ctx_ext M y hxa_V t w env a,
            interpWFF_cast_term, Env.extend_comm]
      · sorry  -- pair-ful reordered context (deferred with the pair track)
  | @WFF.ex _ _ y hy ψ =>
      have hy_ne : y.1 ≠ x := fun h => hy (by
        rw [VarCtx_to_VarSymbs_insert, h]; exact Finset.mem_insert_self _ _)
      have hxa_V : y.1 ∉ VarCtx_to_VarSymbs V := fun h => hy (by
        rw [VarCtx_to_VarSymbs_insert]; exact Finset.mem_insert_of_mem h)
      have hx_xaV : x ∉ VarCtx_to_VarSymbs (VarCtx_insert y V hxa_V) :=
        not_mem_VarSymbs_insert (fun h => hy_ne h.symm) hx
      have h_reorder : VarCtx_insert y (VarCtx_insert ⟨x, S⟩ V hx) hy
          = VarCtx_insert ⟨x, S⟩ (VarCtx_insert y V hxa_V) hx_xaV :=
        VarCtx_insert_comm hy hx_xaV
      rw [WFF.substVar_ex hx t hpf y hy hxa_V hx_xaV h_reorder ψ]
      simp only [RModel.interpWFF]
      apply propext; apply exists_congr; intro a
      by_cases hpf_m :
          (VarCtx_insert ⟨x, S⟩ (VarCtx_insert y V hxa_V) hx_xaV).firstPairVar = none
      · rw [interpWFF_substVar M hx_xaV hpf_m, interpTerm_ctx_ext M y hxa_V t w env a,
            interpWFF_cast_term, Env.extend_comm]
      · sorry  -- pair-ful reordered context (deferred with the pair track)
  | @WFF.box _ V_inner _ ψ hsub hnbe =>
      cases S with
      | Var | VTypeOne | VTypeDia _ =>
          -- Non-box `S`: `x` cannot reach the (all-box) inner context, so this is a passthrough.
          have hx_notin : x ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in
            obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_in
            simp only at hx'_eq; subst hx'_eq
            rcases Finset.mem_insert.mp (hsub (Finset.mem_image.mpr ⟨⟨x', T'⟩, hx'T', rfl⟩))
              with h_eq | h_in_V
            · exact VarType.noConfusion (Prod.mk.inj h_eq).2
            · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
          have hsub' : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro p hp
            rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
            · exfalso; rcases Finset.mem_image.mp hp with ⟨q, hq, hqeq⟩
              exact hx_notin (Finset.mem_image.mpr ⟨q, hq, (Prod.mk.inj (hqeq.trans h_eq)).1⟩)
            · exact h_V
          have h_no_extras' : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_box V_inner).1 :=
            fun p hp h_box => hnbe p (Finset.mem_insert_of_mem hp) h_box
          rw [WFF_substVar_box_notin hx hpf t ψ hsub hnbe hx_notin hsub' h_no_extras']
          simp only [RModel.interpWFF,
            boxPush_extend_notin M hsub' hsub env (M.interpTerm t w env) hx_notin]
      | VTypeBox U =>
          by_cases hx_in : x ∈ VarCtx_to_VarSymbs V_inner
          · have hxU_in : (⟨x, U⟩ : VarSymb × VarType) ∈ V_inner.1 := by
              obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp hx_in
              simp only at hx'_eq; rw [hx'_eq] at hx'T'
              rcases Finset.mem_insert.mp
                  (hsub (Finset.mem_image.mpr ⟨⟨x, T'⟩, hx'T', rfl⟩)) with h_eq | h_in_V
              · have hT : T' = U := VarType.VTypeBox.inj (Prod.mk.inj h_eq).2
                subst hT; exact hx'T'
              · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩) hx
            match t with
            | @Term.boxterm _ V_s _ _ t_inner t_hsub t_hnbe =>
                have hV_s : V_s = VarCtx_erase V_inner ⟨x, U⟩ :=
                  ctx_rest_box_V_s_eq hxU_in hsub hnbe t_hsub t_hnbe
                have hx_s : x ∉ VarCtx_to_VarSymbs V_s := by
                  rw [hV_s]; exact VarCtx_erase_fresh hxU_in
                have h_V_inner_eq : V_inner = VarCtx_insert ⟨x, U⟩ V_s hx_s := by
                  subst hV_s; exact (VarCtx_insert_erase hxU_in hx_s).symm
                -- Cast to the `insert ⟨x,U⟩ V_s` form WITHOUT `subst` (keeps `ψ` structurally the
                -- box body ⇒ the `numNodes` WF measure survives via `WFF_numNodes_cast`).
                have hbox_cast : WFF.box ψ hsub hnbe
                    = WFF.box (h_V_inner_eq ▸ ψ) (h_V_inner_eq ▸ hsub) (h_V_inner_eq ▸ hnbe) := by
                  cases h_V_inner_eq; rfl
                rw [hbox_cast]
                have hred : WFF.substVar hx (Term.boxterm t_inner t_hsub t_hnbe)
                      (WFF.box (h_V_inner_eq ▸ ψ) (h_V_inner_eq ▸ hsub) (h_V_inner_eq ▸ hnbe))
                    = WFF.box (WFF.substVar hx_s t_inner (h_V_inner_eq ▸ ψ)) t_hsub t_hnbe :=
                  WFF.substVar_boxterm_box_gen_base hx_s hx t_hsub t_hnbe hpf t_inner
                    (h_V_inner_eq ▸ ψ)
                rw [hred]
                set VAL := M.interpTerm (Term.boxterm t_inner t_hsub t_hnbe) w env with hVAL
                simp only [RModel.interpWFF]
                apply propext; apply forall_congr'; intro w'
                by_cases hpf_m : (VarCtx_insert ⟨x, U⟩ V_s hx_s).firstPairVar = none
                · rw [interpWFF_substVar M hx_s hpf_m t_inner (h_V_inner_eq ▸ ψ) w'.1
                        (Env.boxPush t_hsub env w'),
                      boxPush_extend_box M hx_s t_hsub (h_V_inner_eq ▸ hsub) env VAL w', hVAL,
                      interpTerm_boxterm, necEval_interpTermNec]
                · sorry  -- inner pair-ful context: pair splitting-translation plug-in
            | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
                exfalso
                have h_sz : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈ V.1 := by
                  rw [← sw2eq]; exact Finset.mem_insert_self _ _
                exact VarCtx.firstPairVar_none_no_pair hpf (Finset.mem_insert_of_mem h_sz)
          · have hsub' : (VarCtx_box V_inner).1 ⊆ V.1 := by
              intro p hp
              rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
              · exfalso; rcases Finset.mem_image.mp hp with ⟨q, hq, hqeq⟩
                exact hx_in (Finset.mem_image.mpr ⟨q, hq, (Prod.mk.inj (hqeq.trans h_eq)).1⟩)
              · exact h_V
            have h_no_extras' : ∀ p ∈ V.1, VarType.isBox p.2 = true
                → p ∈ (VarCtx_box V_inner).1 :=
              fun p hp h_box => hnbe p (Finset.mem_insert_of_mem hp) h_box
            rw [WFF_substVar_box_notin hx hpf t ψ hsub hnbe hx_in hsub' h_no_extras']
            simp only [RModel.interpWFF,
              boxPush_extend_notin M hsub' hsub env (M.interpTerm t w env) hx_in]
      | VTypeProd A B => sorry
  | @WFF.dia _ V_inner _ xv_t hxv_t ψ hsub hnbe =>
      by_cases h_xv_eq_x : xv_t.1 = x
      · -- modal-beta: the dia witness IS the substituted variable ⟹ `S = xv_t.2.dia`.
        have hxv_in_Vext : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
            ∈ (VarCtx_insert ⟨x, S⟩ V hx).1 := by
          apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
        have h_S_eq : S = xv_t.2.VTypeDia := by
          rcases Finset.mem_insert.mp hxv_in_Vext with h_eq | h_in_V
          · exact ((Prod.mk.inj h_eq).2).symm
          · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, h_xv_eq_x⟩) hx
        subst h_S_eq
        subst h_xv_eq_x  -- identify the theorem's `x` with the dia witness `xv_t.1`
        match t with
        | @Term.diaterm _ V_inner_s _ _ xv_s hxv_s tt_s hsub_s h_no_extras_s =>
            -- Step: the value's inner context = the dia's inner context (VarCtx_box_inj).
            have h_V_inner_eq : V_inner_s = V_inner := by
              apply VarCtx_box_inj; apply VarCtx_ext'; apply Finset.ext; intro p
              constructor
              · intro hp_s
                have hp_V : p ∈ V.1 := by
                  apply hsub_s; rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_s
                have hp_box : VarType.isBox p.2 = true := by
                  rcases Finset.mem_image.mp hp_s with ⟨q, _, hq_eq⟩
                  rw [← hq_eq]; simp [VarType.isBox]
                have hp_dia := hnbe p (Finset.mem_insert_of_mem hp_V) hp_box
                rw [VarCtx_dia_fst] at hp_dia
                rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
                · subst h_eq; simp [VarType.isBox] at hp_box
                · exact h_in_box
              · intro hp
                have hp_Vext : p ∈ (VarCtx_insert ⟨xv_t.1, xv_t.2.VTypeDia⟩ V hx).1 := by
                  apply hsub; rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp
                have hp_box : VarType.isBox p.2 = true := by
                  rcases Finset.mem_image.mp hp with ⟨q, _, hq_eq⟩
                  rw [← hq_eq]; simp [VarType.isBox]
                have hp_V : p ∈ V.1 := by
                  rcases Finset.mem_insert.mp hp_Vext with h_eq | h_V
                  · subst h_eq; simp [VarType.isBox] at hp_box
                  · exact h_V
                have hp_dia := h_no_extras_s p hp_V hp_box
                rw [VarCtx_dia_fst] at hp_dia
                rcases Finset.mem_insert.mp hp_dia with h_eq | h_in_box
                · subst h_eq; simp [VarType.isBox] at hp_box
                · exact h_in_box
            cases h_V_inner_eq
            have h_xv_ne_xv_s : xv_t.1 ≠ xv_s.1 := fun h => hx
              (Finset.mem_image.mpr ⟨⟨xv_s.1, xv_s.2.VTypeDia⟩,
                hsub_s (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _), h.symm⟩)
            rw [WFF.substVar_diaterm_dia_gen_base xv_t hxv_t hx xv_s hxv_s h_xv_ne_xv_s tt_s
                hsub_s h_no_extras_s hpf ψ hsub hnbe]
            -- ◇◇-composition: the LHS `◇_{xv_s}` realization `dv_s` corresponds to the RHS
            -- `◇_{xv_t}` realization `⟨dv_s.1, ⟦tt_s⟧⟩` with the inner witness `v := dv_s.2`.
            simp only [RModel.interpWFF, RModel.interpTerm]
            apply propext
            constructor
            · rintro ⟨dv_s, hmem_s, hbody_s⟩
              refine ⟨⟨dv_s.1, M.interpTerm tt_s dv_s.1.1
                  ((Env.boxPush (fun p hp => hsub_s (Finset.mem_insert_of_mem hp)) env dv_s.1).extend
                    xv_s hxv_s dv_s.2)⟩, ?_, ?_⟩
              · -- membership: self-lookup collapses `env.extend … VAL` to `VAL`, then `mapPos_eval`.
                simp only [Env.extend, dif_pos]
                rw [M.mapPos_eval]
                exact ⟨dv_s.2, hmem_s, rfl⟩
              · -- interpWFF ψ body: rewrite the substituted body via `interpWFF_substVar`
                -- (the reordered body `↑R.snd` is `ctx_ext xv_s ψ` up to casts), then relate to `ψ`.
                set R := WFF.dia_arm_case3_reorder xv_t xv_s hxv_t hxv_s h_xv_ne_xv_s rfl ψ with hR
                by_cases hpf' : (VarCtx_insert (⟨xv_t.1, xv_t.2⟩ : VarSymb × VarType)
                    (VarCtx_insert xv_s V_inner hxv_s) R.fst).firstPairVar = none
                · rw [show (↑(WFF.ctx_rest_MU R.fst tt_s ↑R.snd)
                            : WFF σ (VarCtx_insert xv_s V_inner hxv_s))
                          = WFF.substVar R.fst tt_s ↑R.snd from rfl,
                      interpWFF_substVar M R.fst hpf' tt_s (↑R.snd)] at hbody_s
                  have hxv_s_outer : xv_s.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_t V_inner hxv_t) :=
                    not_mem_VarSymbs_insert (fun h => h_xv_ne_xv_s h.symm) hxv_s
                  have hxv_xv_s_outer :
                      xv_t.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s) :=
                    not_mem_VarSymbs_insert h_xv_ne_xv_s hxv_t
                  have h_reorder : VarCtx_insert xv_s (VarCtx_insert xv_t V_inner hxv_t) hxv_s_outer
                      = VarCtx_insert xv_t (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer := by
                    apply VarCtx_ext'; exact Finset.insert_comm _ _ _
                  have h_reform : VarCtx_insert xv_t (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer
                      = VarCtx_insert (⟨xv_t.1, xv_t.2⟩ : VarSymb × VarType)
                          (VarCtx_insert xv_s V_inner hxv_s) R.fst := rfl
                  have hReq : (↑R.snd : WFF σ (VarCtx_insert (⟨xv_t.1, xv_t.2⟩ : VarSymb × VarType)
                        (VarCtx_insert xv_s V_inner hxv_s) R.fst))
                      = h_reform ▸ h_reorder ▸ WFF.ctx_ext xv_s hxv_s_outer ψ := rfl
                  rw [hReq, interpWFF_cast_term] at hbody_s
                  rw [Env.extend_comm, interpWFF_ctx_ext M xv_s hxv_s_outer ψ] at hbody_s
                  rw [boxPush_extend_notBox (xv := (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)) M
                      (fun p hp => hsub_s (Finset.mem_insert_of_mem hp)) _ env _
                      rfl dv_s.fst]
                  exact hbody_s
                · sorry  -- pair-ful reordered context (deferred with the pair track)
            · rintro ⟨dv_t, hmem_t, hbody_t⟩
              simp only [Env.extend, dif_pos] at hmem_t
              rw [M.mapPos_eval] at hmem_t
              obtain ⟨v, hmem_v, htt⟩ := hmem_t
              refine ⟨⟨dv_t.1, v⟩, hmem_v, ?_⟩
              -- Mirror of the `mp` body, but transforming the goal; `htt` rewrites `⟦tt_s⟧ = dv_t.snd`.
              set R := WFF.dia_arm_case3_reorder xv_t xv_s hxv_t hxv_s h_xv_ne_xv_s rfl ψ with hR
              have hxv_s_outer : xv_s.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_t V_inner hxv_t) :=
                not_mem_VarSymbs_insert (fun h => h_xv_ne_xv_s h.symm) hxv_s
              have hxv_xv_s_outer : xv_t.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_s V_inner hxv_s) :=
                not_mem_VarSymbs_insert h_xv_ne_xv_s hxv_t
              have h_reorder : VarCtx_insert xv_s (VarCtx_insert xv_t V_inner hxv_t) hxv_s_outer
                  = VarCtx_insert xv_t (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer := by
                apply VarCtx_ext'; exact Finset.insert_comm _ _ _
              have h_reform : VarCtx_insert xv_t (VarCtx_insert xv_s V_inner hxv_s) hxv_xv_s_outer
                  = VarCtx_insert (⟨xv_t.1, xv_t.2⟩ : VarSymb × VarType)
                      (VarCtx_insert xv_s V_inner hxv_s) R.fst := rfl
              have hReq : (↑R.snd : WFF σ (VarCtx_insert (⟨xv_t.1, xv_t.2⟩ : VarSymb × VarType)
                    (VarCtx_insert xv_s V_inner hxv_s) R.fst))
                  = h_reform ▸ h_reorder ▸ WFF.ctx_ext xv_s hxv_s_outer ψ := rfl
              by_cases hpf' : (VarCtx_insert (⟨xv_t.1, xv_t.2⟩ : VarSymb × VarType)
                  (VarCtx_insert xv_s V_inner hxv_s) R.fst).firstPairVar = none
              · rw [show (↑(WFF.ctx_rest_MU R.fst tt_s ↑R.snd)
                          : WFF σ (VarCtx_insert xv_s V_inner hxv_s))
                        = WFF.substVar R.fst tt_s ↑R.snd from rfl,
                    interpWFF_substVar M R.fst hpf' tt_s (↑R.snd),
                    hReq, interpWFF_cast_term,
                    Env.extend_comm, interpWFF_ctx_ext M xv_s hxv_s_outer ψ, htt]
                rw [boxPush_extend_notBox (xv := (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)) M
                    (fun p hp => hsub_s (Finset.mem_insert_of_mem hp)) _ env _
                    rfl dv_t.fst] at hbody_t
                exact hbody_t
              · sorry  -- pair-ful reordered context (deferred with the pair track)
        | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
            exfalso
            have h_sz : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈ V.1 := by
              rw [← sw2eq]; exact Finset.mem_insert_self _ _
            exact VarCtx.firstPairVar_none_no_pair hpf (Finset.mem_insert_of_mem h_sz)
      · by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
        · cases S with
          | Var | VTypeOne | VTypeDia _ | VTypeProd _ _ =>
              exfalso
              obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
              simp only at hx'_eq; rw [hx'_eq] at hx'T'
              have hbox : (⟨x, T'.VTypeBox⟩ : VarSymb × VarType)
                  ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
                rw [VarCtx_dia_fst]
                exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨x, T'⟩, hx'T', rfl⟩)
              rcases Finset.mem_insert.mp (hsub hbox) with h_eq | h_in_V
              · exact VarType.noConfusion (Prod.mk.inj h_eq).2
              · exact hx (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩)
          | VTypeBox U =>
              -- Generalized IH with an explicit `numNodes` bound, taken BEFORE the `subst`
              -- below: the WF-termination obligation fires HERE, where `ψ` is still the
              -- measure's `ψ`, and is closed by `omega` from the guard `hle`.
              have IH : ∀ (V' : VarCtx) (S' : VarType) (hx' : x ∉ VarCtx_to_VarSymbs V')
                  (hpf' : (VarCtx_insert ⟨x, S'⟩ V' hx').firstPairVar = none)
                  (t' : Term σ V' S') (φ' : WFF σ (VarCtx_insert ⟨x, S'⟩ V' hx'))
                  (w' : M.W) (env' : M.Env V' w'),
                  WFF.diaCount φ' ≤ WFF.diaCount ψ →
                  WFF.numNodes φ' ≤ WFF.numNodes ψ →
                  M.interpWFF (WFF.substVar hx' t' φ') w' env'
                    = M.interpWFF φ' w'
                        (env'.extend ⟨x, S'⟩ hx' (M.interpTerm t' w' env')) :=
                fun V' S' hx' hpf' t' φ' w' env' hle_dia hle =>
                  interpWFF_substVar M hx' hpf' t' φ' w' env'
              have hxU_in : (⟨x, U⟩ : VarSymb × VarType) ∈ V_inner.1 := by
                obtain ⟨⟨x', T'⟩, hx'T', hx'_eq⟩ := Finset.mem_image.mp h_x_in
                simp only at hx'_eq; rw [hx'_eq] at hx'T'
                have hbox : (⟨x, T'.VTypeBox⟩ : VarSymb × VarType)
                    ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
                  rw [VarCtx_dia_fst]
                  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨x, T'⟩, hx'T', rfl⟩)
                rcases Finset.mem_insert.mp (hsub hbox) with h_eq | h_in_V
                · have hT : T' = U := VarType.VTypeBox.inj (Prod.mk.inj h_eq).2
                  subst hT; exact hx'T'
                · exact absurd (Finset.mem_image.mpr ⟨_, h_in_V, rfl⟩) hx
              match t with
              | @Term.boxterm _ V_s _ _ t_inner t_hsub t_hnbe =>
                  have hV_s : V_s = VarCtx_erase V_inner ⟨x, U⟩ :=
                    ctx_rest_dia_V_s_eq hxU_in hsub hnbe t_hsub t_hnbe
                  have hx_s : x ∉ VarCtx_to_VarSymbs V_s := by
                    rw [hV_s]; exact VarCtx_erase_fresh hxU_in
                  have hxv_V : xv_t.1 ∉ VarCtx_to_VarSymbs V_s := by
                    rw [hV_s]; exact fun h => hxv_t (VarCtx_to_VarSymbs_erase_subset h)
                  have h_V_inner_eq : V_inner = VarCtx_insert ⟨x, U⟩ V_s hx_s := by
                    subst hV_s; exact (VarCtx_insert_erase hxU_in hx_s).symm
                  subst h_V_inner_eq
                  have hx_out : x ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_t V_s hxv_V) :=
                    not_mem_VarSymbs_insert (fun h => h_xv_eq_x h.symm) hx_s
                  have h_reorder : VarCtx_insert xv_t (VarCtx_insert ⟨x, U⟩ V_s hx_s) hxv_t
                      = VarCtx_insert ⟨x, U⟩ (VarCtx_insert xv_t V_s hxv_V) hx_out :=
                    VarCtx_insert_comm hxv_t hx_out
                  have P' : (VarCtx_dia xv_t V_s hxv_V).1 ⊆ V.1 := by
                    intro q hq
                    rw [VarCtx_dia_fst] at hq
                    rcases Finset.mem_insert.mp hq with h_eq | h_box
                    · have hq_dia : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
                          ∈ (VarCtx_dia xv_t (VarCtx_insert ⟨x, U⟩ V_s hx_s) hxv_t).1 := by
                        rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
                      rcases Finset.mem_insert.mp (hsub hq_dia) with h_eq2 | h_V
                      · exact absurd (congrArg Prod.fst h_eq2) h_xv_eq_x
                      · rw [h_eq]; exact h_V
                    · exact t_hsub h_box
                  have Q' : ∀ p ∈ V.1, VarType.isBox p.2 = true
                      → p ∈ (VarCtx_dia xv_t V_s hxv_V).1 := by
                    intro p hp hp_box
                    have hin := hnbe p (Finset.mem_insert_of_mem hp) hp_box
                    rw [VarCtx_dia_fst, VarCtx_box_fst_insert] at hin
                    rw [VarCtx_dia_fst]
                    rcases Finset.mem_insert.mp hin with h_dia | h_rest
                    · exact Finset.mem_insert.mpr (Or.inl h_dia)
                    · rcases Finset.mem_insert.mp h_rest with h_xU | h_box
                      · exact absurd (Finset.mem_image.mpr ⟨p, hp, congrArg Prod.fst h_xU⟩) hx
                      · exact Finset.mem_insert_of_mem h_box
                  rw [WFF.substVar_boxterm_dia_gen_base hx_s hx t_hsub t_hnbe hpf t_inner xv_t
                      h_xv_eq_x hxv_V hxv_t hx_out h_reorder ψ hsub hnbe P' Q']
                  have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 :=
                    P' (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)
                  set VAL := M.interpTerm (Term.boxterm t_inner t_hsub t_hnbe) w env with hVAL
                  simp only [RModel.interpWFF]
                  apply propext; apply exists_congr; intro dv
                  by_cases hpf_m :
                      (VarCtx_insert ⟨x, U⟩ (VarCtx_insert xv_t V_s hxv_V) hx_out).firstPairVar
                        = none
                  · rw [IH _ _ hx_out hpf_m]
                    all_goals first
                      | exact le_of_eq (WFF.diaCount_ctx_cast _ _)
                      | exact le_of_eq (WFF_numNodes_cast _ _)
                      | (rw [interpTerm_ctx_ext M xv_t hxv_V t_inner dv.1.1
                               (Env.boxPush (fun p hp => P' (Finset.mem_insert_of_mem hp))
                                 env dv.1) dv.2,
                             interpWFF_cast_term,
                             Env.extend_comm
                               (Env.boxPush (fun p hp => P' (Finset.mem_insert_of_mem hp))
                                 env dv.1)
                               hxv_V hx_s hx_out hxv_t dv.2 _ h_reorder.symm,
                             Env.extend_apply_ne (xv := (⟨x, U.VTypeBox⟩ : VarSymb × VarType))
                               env VAL _ hwit,
                             boxPush_extend_box M hx_s t_hsub
                               (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env VAL dv.1,
                             hVAL, interpTerm_boxterm, necEval_interpTermNec])
                  · sorry  -- inner pair-ful context: pair splitting-translation plug-in
              | .pair_elim sv1 sv2 sz _ _ _ _ _ sw2eq _ =>
                  exfalso
                  have h_sz : (⟨sz, sv1.2.VTypeProd sv2.2⟩ : VarSymb × VarType) ∈ V.1 := by
                    rw [← sw2eq]; exact Finset.mem_insert_self _ _
                  exact VarCtx.firstPairVar_none_no_pair hpf (Finset.mem_insert_of_mem h_sz)
        · have hsub' : (VarCtx_dia xv_t V_inner hxv_t).1 ⊆ V.1 := by
            rw [VarCtx_dia_fst]; intro p hp
            rcases Finset.mem_insert.mp hp with h_eq | hp_box
            · subst h_eq
              have hp_in_dia : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType)
                  ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
                rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _
              rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq' | h_in_V
              · exact absurd (Prod.mk.inj h_eq').1 h_xv_eq_x
              · exact h_in_V
            · have hp_in_dia : p ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
                rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hp_box
              rcases Finset.mem_insert.mp (hsub hp_in_dia) with h_eq | h_in_V
              · subst h_eq; exfalso; apply h_x_in
                rcases Finset.mem_image.mp hp_box with ⟨q, hq_in, hq_eq⟩
                exact Finset.mem_image.mpr ⟨q, hq_in, (Prod.mk.inj hq_eq).1⟩
              · exact h_in_V
          have h_no_extras' : ∀ p ∈ V.1, VarType.isBox p.2 = true
              → p ∈ (VarCtx_dia xv_t V_inner hxv_t).1 :=
            fun p hp h_box => hnbe p (Finset.mem_insert_of_mem hp) h_box
          have hsub_base : (VarCtx_box V_inner).1 ⊆ V.1 := by
            intro q hq
            have hq_dia : q ∈ (VarCtx_dia xv_t V_inner hxv_t).1 := by
              rw [VarCtx_dia_fst]; exact Finset.mem_insert_of_mem hq
            rcases Finset.mem_insert.mp (hsub hq_dia) with h_eq | h_V
            · exfalso; rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
              exact h_x_in ((Prod.mk.inj (hpq.trans h_eq)).1 ▸ Finset.mem_image.mpr ⟨p, hp, rfl⟩)
            · exact h_V
          rw [WFF_substVar_dia_notin hx hpf t xv_t hxv_t ψ hsub hnbe h_xv_eq_x h_x_in
                hsub' h_no_extras']
          simp only [RModel.interpWFF]
          apply propext; apply exists_congr; intro dv
          have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 :=
            hsub' (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)
          rw [Env.extend_apply_ne (xv := (⟨x, S⟩ : VarSymb × VarType)) env
                (M.interpTerm t w env) _ hwit,
              boxPush_extend_notin M hsub_base (fun p hp => hsub (Finset.mem_insert_of_mem hp))
                env (M.interpTerm t w env) h_x_in dv.1]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => sorry
termination_by (WFF.diaCount φ, WFF.numNodes φ)
decreasing_by
  all_goals
    first
    | (apply lex_of_le_lt
       · first
           | (simp only [WFF.diaCount, WFF.diaCount_ctx_cast, WFF.diaCount_rename] <;> omega)
           | omega
           | (rw [WFF.diaCount_ctx_cast]; simp only [WFF.diaCount] <;> omega)
       · first
           | (simp only [WFF.numNodes, WFF_numNodes_cast]; omega)
           | (rw [WFF_numNodes_cast]; simp only [WFF.numNodes]; omega))
    | -- modal-β recursion: `diaCount` drops strictly (the reorder preserves `diaCount`).
      (apply Prod.Lex.left
       have h := (WFF.dia_arm_case3_reorder xv_t xv_s hxv_t hxv_s h_xv_ne_xv_s rfl ψ).snd.property.2
       simp only [WFF.diaCount]
       omega)

/-! ### The soundness theorem (ports `Soundness2.lean:2199-2327`) -/

/-- Extend a satisfied hypothesis set by one more satisfied formula (`Γ ∪ {ψ}`). -/
theorem sat_union_singleton {M : RModel σ} {V : VarCtx} {Γ : Finset (WFF σ V)}
    {ψ : WFF σ V} {w : M.W} {env : M.Env V w}
    (hΓ : ∀ χ ∈ Γ, M.interpWFF χ w env) (hψ : M.interpWFF ψ w env) :
    ∀ χ ∈ Γ ∪ {ψ}, M.interpWFF χ w env :=
  fun χ hχ => (Finset.mem_union.mp hχ).elim (hΓ χ)
    (fun h => by rw [Finset.mem_singleton.mp h]; exact hψ)

/-- Restrict a satisfied hypothesis set to a subset (here `Γ ⊆ Γ ∪ {ψ}`). -/
theorem sat_of_union_left {M : RModel σ} {V : VarCtx} {Γ : Finset (WFF σ V)}
    {ψ : WFF σ V} {w : M.W} {env : M.Env V w}
    (hΓ : ∀ χ ∈ Γ ∪ {ψ}, M.interpWFF χ w env) :
    ∀ χ ∈ Γ, M.interpWFF χ w env :=
  fun χ hχ => hΓ χ (Finset.mem_union_left _ hχ)

/-- `Finset` corollary of `interpWFF_ctx_ext`: the extended hypothesis set is satisfied by the
    extended environment iff the original set is satisfied by the original. -/
theorem sat_ctx_ext_Finset (M : RModel σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (Γ : Finset (WFF σ V)) (w : M.W) (env : M.Env V w)
    (a : M.interp xv.2 w) :
    (∀ ψ ∈ WFF.ctx_ext_Finset xv hxv Γ, M.interpWFF ψ w (env.extend xv hxv a))
      ↔ (∀ χ ∈ Γ, M.interpWFF χ w env) := by
  constructor
  · intro h χ hχ
    have hh := h (WFF.ctx_ext xv hxv χ) (Finset.mem_image.mpr ⟨χ, hχ, rfl⟩)
    rwa [interpWFF_ctx_ext M xv hxv χ] at hh
  · intro h ψ hψ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hψ
    rw [interpWFF_ctx_ext M xv hxv χ]
    exact h χ hχ

/-- **Soundness**: provability implies `RModel`-entailment.  By structural recursion on the
    derivation.  The `box_ext`/`dia_ext` rules are where RModel's *injective* eval maps earn
    their keep: sections/realization-sets agree ⇒ the objects agree, by `nec_inj`/`pos_inj`
    (GModel instead rebuilt both sides with `necIntro`/`posIntro`). -/
theorem soundness {V : VarCtx} {Γ : Finset (WFF σ V)} {φ : WFF σ V} :
    Proof σ V Γ φ → (Γ ⊨ᵣ φ)
  -- Structural
  | .ax hmem => fun _ _ env hΓ => hΓ _ hmem
  | .weak h => fun M w env hΓ => soundness h M w env (sat_of_union_left hΓ)
  | .weak_ctx x hx h => fun M w env hΓ => by
      set a : M.interp x.2 w := env x (Finset.mem_insert_self _ _) with ha
      set env' : M.Env _ w := fun p hp => env p (Finset.mem_insert_of_mem hp) with henv'
      have heq : env = env'.extend x hx a := by
        funext p hp
        by_cases hpx : p = x
        · subst hpx; simp [Env.extend, henv', ha]
        · simp only [Env.extend, dif_neg hpx, henv']
      rw [heq] at hΓ ⊢
      rw [interpWFF_ctx_ext M x hx _ w env' a]
      exact soundness h M w env' ((sat_ctx_ext_Finset M x hx _ w env' a).mp hΓ)
  -- Conjunction
  | .and_intro h₁ h₂ => fun M w env hΓ => ⟨soundness h₁ M w env hΓ, soundness h₂ M w env hΓ⟩
  | .and_elim_l h => fun M w env hΓ => (soundness h M w env hΓ).1
  | .and_elim_r h => fun M w env hΓ => (soundness h M w env hΓ).2
  -- Disjunction
  | .or_intro_l h => fun M w env hΓ => Or.inl (soundness h M w env hΓ)
  | .or_intro_r h => fun M w env hΓ => Or.inr (soundness h M w env hΓ)
  | .or_elim h hl hr => fun M w env hΓ =>
      (soundness h M w env hΓ).elim
        (fun hφ => soundness hl M w env (sat_union_singleton hΓ hφ))
        (fun hψ => soundness hr M w env (sat_union_singleton hΓ hψ))
  -- Implication
  | .imp_intro h => fun M w env hΓ hφ => soundness h M w env (sat_union_singleton hΓ hφ)
  | .imp_elim h₁ h₂ => fun M w env hΓ => (soundness h₁ M w env hΓ) (soundness h₂ M w env hΓ)
  -- Truth / falsity
  | .top_intro => fun _ _ _ _ => trivial
  | .bot_elim h => fun M w env hΓ => (soundness h M w env hΓ).elim
  -- Classical
  | .lem p => fun M w env _ => Classical.em (M.interpWFF p w env)
  -- Quantifiers
  | .all_intro x hx h => fun M w env hΓ a =>
      soundness h M w (env.extend x hx a) ((sat_ctx_ext_Finset M x hx _ w env a).mpr hΓ)
  | .all_elim x hx t h => fun M w env hΓ => by
      by_cases hpf : (VarCtx_insert ⟨x.1, x.2⟩ V hx).firstPairVar = none
      · rw [interpWFF_substVar M hx hpf t _ w env]
        exact soundness h M w env hΓ (M.interpTerm t w env)
      · sorry  -- pair-ful context: handled by the pair splitting-translation
  | .ex_intro x hx t h => fun M w env hΓ => by
      by_cases hpf : (VarCtx_insert ⟨x.1, x.2⟩ V hx).firstPairVar = none
      · exact ⟨M.interpTerm t w env,
          (interpWFF_substVar M hx hpf t _ w env) ▸ soundness h M w env hΓ⟩
      · sorry  -- pair-ful context: handled by the pair splitting-translation
  | .ex_elim x hx h₁ h₂ => fun M w env hΓ => by
      obtain ⟨a, hφa⟩ := soundness h₁ M w env hΓ
      have hh := soundness h₂ M w (env.extend x hx a)
        (sat_union_singleton ((sat_ctx_ext_Finset M x hx _ w env a).mpr hΓ) hφa)
      rwa [interpWFF_ctx_ext M x hx _ w env a] at hh
  -- Equality
  | .eq_intro _ => fun _ _ _ _ => rfl
  | .eq_elim x hx t s h₁ h₂ => fun M w env hΓ => by
      by_cases hpf : (VarCtx_insert ⟨x.1, x.2⟩ V hx).firstPairVar = none
      · rw [interpWFF_substVar M hx hpf s _ w env]
        have heq : M.interpTerm t w env = M.interpTerm s w env := soundness h₁ M w env hΓ
        rw [← heq, ← interpWFF_substVar M hx hpf t _ w env]
        exact soundness h₂ M w env hΓ
      · sorry  -- pair-ful context: handled by the pair splitting-translation
  -- Pairing: distribution is semantics-preserving (`interpWFF_pairElim`), so the eliminated
  -- derivation transports to the split (`unpairEnv`) environment.
  | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq h => fun M w env hΓ => by
      rw [interpWFF_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq _ w env]
      refine soundness h M w (w₁eq ▸ Env.unpairEnv hv₁v₂ w₂eq env) (fun ψ hψ => ?_)
      have hmem := hΓ (WFF.pairElim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ)
        (Finset.mem_image.mpr ⟨ψ, hψ, rfl⟩)
      rwa [interpWFF_pairElim M v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq ψ w env] at hmem
  | .pair_elim_alpha .. => by sorry
  -- Modal
  | .K_box hsub hnbe h => fun M w env hΓ w' =>
      soundness h M w'.1 (Env.boxPush hsub env w')
        (fun γ hγ => hΓ (WFF.box γ hsub hnbe) (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩) w')
  | .K_dia x hx hsub hnbe h => fun M w env hΓ => by
      -- General modal-`K` rule.  Skeleton = the old plain-`□` proof (grab the `◇_x ψ` witness `dv`,
      -- run `soundness h` at `dv.1.1`).  Premise antecedent = `ctx_ext_Finset Γ ∪ Δ ∪ {ψ}`:
      -- • `Γ` (x-free, `□`-hyps): unchanged — `interpWFF_ctx_ext` + the `box γ` hypothesis at `dv.1`.
      -- • `Δ` (x-dependent, `□_x`-hyps): NEW — `box_x δ = ¬◇_x¬δ` holds at `w`, so read `δ` at the
      --   SAME realization `dv` (`◇_x ψ` and `box_x δ` share the one `posEval` set); by-contradiction
      --   feeds `⟨dv, hposEval, ¬δ@dv⟩` to `box_x δ`.
      obtain ⟨dv, hposEval, hψ⟩ := hΓ (WFF.dia x hx _ hsub hnbe)
        (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      refine ⟨dv, hposEval, soundness h M dv.1.1 _ (fun χ hχ => ?_)⟩
      rcases Finset.mem_union.mp hχ with hχΓΔ | hχψ
      · rcases Finset.mem_union.mp hχΓΔ with hχΓ | hχΔ
        · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hχΓ
          rw [interpWFF_ctx_ext M x hx γ]
          exact hΓ (WFF.box γ _ _)
            (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩))) dv.1
        · by_contra hneg
          exact hΓ (WFF.box_x x hx hsub hnbe χ)
            (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨χ, hχΔ, rfl⟩)))
            ⟨dv, hposEval, hneg⟩
      · rw [Finset.mem_singleton] at hχψ
        subst hχψ
        exact hψ
  | .dia_bot _ _ _ _ h => fun M w env hΓ => (soundness h M w env hΓ).elim (fun _ hdv => hdv.2)
  -- World-extensionality: sections agree ⇒ the box objects agree, by `nec_inj` + box-β.
  -- (THE rule `nec_inj` exists for — GModel needed `necIntro` here instead.)
  | .box_ext _ _ _ _ h => fun M w env hΓ => by
      show M.interpTerm (Term.boxterm _ _ _) w env = M.interpTerm (Term.boxterm _ _ _) w env
      rw [interpTerm_boxterm, interpTerm_boxterm]
      apply M.nec_inj
      funext w'
      rw [necEval_interpTermNec, necEval_interpTermNec]
      exact soundness h M w env hΓ w'
  | .dia_ext x hx hsub hnbe tt₁ tt₂ h => fun M w env hΓ => by
      -- `box_x (tt₁ ≐ tt₂)` ⇒ the two terms agree at every realization of `x`; then the two
      -- `mapPos` images have the same realization set (`mapPos_eval`), so `pos_inj` closes.
      have hagree : ∀ dv : Σ' w' : {w' : M.W // M.R w w'}, M.interp x.2 w'.1,
          dv ∈ M.posEval (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))) →
          M.interpTerm tt₁ dv.1.1
              ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2)
            = M.interpTerm tt₂ dv.1.1
              ((Env.boxPush (fun p hp => hsub (Finset.mem_insert_of_mem hp)) env dv.1).extend x hx dv.2) := by
        intro dv hposmem
        by_contra hne
        exact soundness h M w env hΓ ⟨dv, hposmem, hne⟩
      show M.interpTerm (Term.diaterm x hx tt₁ hsub hnbe) w env
         = M.interpTerm (Term.diaterm x hx tt₂ hsub hnbe) w env
      simp only [RModel.interpTerm]
      apply M.pos_inj
      ext ru
      rw [M.mapPos_eval _ _ ru, M.mapPos_eval _ _ ru]
      constructor
      · rintro ⟨v, hmem, heq⟩; exact ⟨v, hmem, (hagree ⟨ru.1, v⟩ hmem).symm.trans heq⟩
      · rintro ⟨v, hmem, heq⟩; exact ⟨v, hmem, (hagree ⟨ru.1, v⟩ hmem).trans heq⟩

end RModel
