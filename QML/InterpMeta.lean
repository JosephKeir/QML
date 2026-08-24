import QML.InterpWFF

/-!
# Interpreter metatheory (shared) — `InterpMeta`

Multi-purpose lemmas about the `RModelB` interpreter (`interpTerm` / `interpWFF`, from `InterpWFF`)
that **both** the soundness and completeness developments consume: substitution, context-extension,
and α-renaming.  Collected in one importable file (rather than duplicated), and kept small so it
builds once and stays cached.

These statements are the shared *contract*.  They are ported from `SoundnessRealB` (which proved the
same facts for the **predecessor** `RModel`); the port rewrites `M.W → M.frame.W`,
`M.interp → M.frame.interp`, `M.Env → Env M`, and `interpTerm`'s argument order.  The foundational
env/cast lemmas below port directly.

**The big three (`ctx_ext`/`substVar`/`rename`) need *re-proofs*, not copies.**  `SoundnessRealB`'s
proofs are built on the *predecessor* interpreter (a level-0 `interpTerm` with a `sizeOf`-fuel trick
and helpers like `interpTerm_boxterm`/`necEval_interpTermNec`).  The live interpreter is the
level-generic `termToNecLvl` with `box-β` (`termToNecLvl_necEvalLvl`) and the `necEvalLvl`/
`posLiftStkLvl` machinery, so each needs a **level-generic** `termToNecLvl_*` helper (mirroring how
`box-β` is stated over `interpN _ k`, not `interp`), whose `k = 0` instance gives the `interpTerm`
version, feeding the `interpWFF` version.  The old proofs guide the *case structure*; the modal
cases are redone against the new closures.  **Statements are the contract; proofs `sorry` for now.**
-/

namespace RModel

variable {σ : Signature}

/-! ### Foundational env / cast lemmas (ported from `SoundnessRealB`; used by the big three). -/

/-- Looking up a variable already in `V` in an extended environment ignores the extension. -/
theorem Env.extend_apply_ne {M : RModel σ} {V : VarCtx} {w : M.frame.W} (env : Env M V w)
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs V} (aa : M.frame.interp xv.2 w)
    {q : VarSymb × VarType} (hq : q ∈ (VarCtx_insert xv V hxv).1) (hqV : q ∈ V.1) :
    (env.extend xv hxv aa) q hq = env q hqV := by
  have hne : q ≠ xv := fun h => hxv (h ▸ Finset.mem_image.mpr ⟨q, hqV, rfl⟩)
  simp only [Env.extend, dif_neg hne]

/-- Cast on the term alone: transport the environment the other way. -/
theorem interpTerm_cast_term (M : RModel σ) {W1 W2 : VarCtx} (h : W1 = W2) {S : VarType}
    (t : Term σ W1 S) (w : M.frame.W) (env : Env M W2 w) :
    M.interpTerm w env (h ▸ t) = M.interpTerm w (h.symm ▸ env) t := by subst h; rfl

/-- Cast on the formula alone: transport the environment the other way. -/
theorem interpWFF_cast_term (M : RModel σ) {W1 W2 : VarCtx} (h : W1 = W2)
    (φ : WFF σ W1) (w : M.frame.W) (env : Env M W2 w) :
    M.interpWFF (h ▸ φ) w env = M.interpWFF φ w (h.symm ▸ env) := by subst h; rfl

/-! ### Congruence: the interpreter depends only on the environment's values on the free variables.
    (New-style port of `SoundnessRealB`'s `interpTermNecStk_congr`; foundational for the big three.) -/

/-- `bundleNecLvl` depends only on the `necOf` values, pointwise. -/
theorem bundleNecLvl_congr (M : RModel σ) (k : ℕ) {w : M.frame.W} :
    (l : List (VarSymb × VarType)) →
    (f g : (p : VarSymb × VarType) → p ∈ l → M.frame.interpN p.2 (k + 1) w) →
    (∀ p hp, f p hp = g p hp) → M.bundleNecLvl k l f = M.bundleNecLvl k l g
  | [],        _, _, _ => rfl
  | q :: rest, f, g, h => by
      simp only [bundleNecLvl]
      rw [bundleNecLvl_congr M k rest (fun p hp => f p (List.mem_cons.mpr (Or.inr hp)))
            (fun p hp => g p (List.mem_cons.mpr (Or.inr hp))) (fun p hp => h p _),
          h q (List.mem_cons.mpr (Or.inl rfl))]

mutual

/-- **Congruence for `termToNecLvl`**: two environments agreeing on `V`'s variables interpret any
    term equally.  (Induction on the term; `boxterm`/`diaterm` push the agreement through the boxed
    environment / bundled necessary context.) -/
theorem termToNecLvl_congr (M : RModel σ) (k : ℕ) {w : M.frame.W} : {V : VarCtx} →
    (env₁ env₂ : (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 k w) →
    (∀ p hp, env₁ p hp = env₂ p hp) → {S : VarType} → (t : Term σ V S) →
    M.termToNecLvl k env₁ t = M.termToNecLvl k env₂ t
  | _, env₁, env₂, h, _, .var ⟨v, hv⟩ => h ⟨v, .Var⟩ hv
  | _, env₁, env₂, h, _, .func ff => by
      simp only [RModel.termToNecLvl]
      exact funcToNecLvl_congr M k env₁ env₂ h ff Fin.elim0 Fin.elim0 (fun i => i.elim0)
  | _, _, _, _, _, .unit => rfl
  | _, env₁, env₂, h, _, .pair a b => by
      simp only [RModel.termToNecLvl,
        termToNecLvl_congr M k env₁ env₂ h a, termToNecLvl_congr M k env₁ env₂ h b]
  | _, env₁, env₂, h, _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body => by
      simp only [RModel.termToNecLvl]
      apply termToNecLvl_congr M k _ _ _ body
      intro p hp
      simp only [peLookup]
      by_cases hpv1 : p = v₁
      · simp only [dif_pos hpv1]; rw [h]
      · by_cases hpv2 : p = v₂
        · simp only [dif_neg hpv1, dif_pos hpv2]; rw [h]
        · simp only [dif_neg hpv1, dif_neg hpv2]; rw [h]
  | _, env₁, env₂, h, _, .boxterm s hsub _ => by
      simp only [RModel.termToNecLvl]
      exact termToNecLvl_congr M (k + 1) _ _
        (fun p hp => h ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))) s
  | _, env₁, env₂, h, _, @Term.diaterm _ V_dia _ _ x hx tt hsub _ => by
      simp only [RModel.termToNecLvl]
      rw [bundleNecLvl_congr M k V_dia.1.toList _ _ (fun p hp =>
            h ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨p, Finset.mem_toList.mp hp, rfl⟩)))),
          h ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))]

theorem funcToNecLvl_congr (M : RModel σ) (k : ℕ) {w : M.frame.W} : {V : VarCtx} →
    (env₁ env₂ : (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 k w) →
    (∀ p hp, env₁ p hp = env₂ p hp) → {n : ℕ} → (ff : Func σ V n) →
    (args₁ args₂ : Fin n → M.frame.interpN VarType.Var k w) → (∀ i, args₁ i = args₂ i) →
    M.funcToNecLvl k env₁ ff args₁ = M.funcToNecLvl k env₂ ff args₂
  | _, _, _, _, _, .F ⟨f, hf⟩, args₁, args₂, hargs => by
      subst hf; simp only [RModel.funcToNecLvl]; congr 1; funext i; exact hargs i
  | _, env₁, env₂, h, _, .eval g t, args₁, args₂, hargs => by
      simp only [RModel.funcToNecLvl]
      refine funcToNecLvl_congr M k env₁ env₂ h g _ _ ?_
      intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]; exact termToNecLvl_congr M k env₁ env₂ h t
      · intro j; simp only [Fin.cons_succ]; exact hargs j

end

/-- Term congruence at level 0 (`interpTerm`). -/
theorem interpTerm_congr (M : RModel σ) {V : VarCtx} (w : M.frame.W)
    (env₁ env₂ : Env M V w) (h : ∀ p hp, env₁ p hp = env₂ p hp) {S : VarType} (t : Term σ V S) :
    M.interpTerm w env₁ t = M.interpTerm w env₂ t := by
  simp only [RModel.interpTerm]; exact M.termToNecLvl_congr 0 env₁ env₂ h t

/-- Relation-application congruence. -/
theorem interpRel_congr (M : RModel σ) {V : VarCtx} (w : M.frame.W)
    (env₁ env₂ : Env M V w) (h : ∀ p hp, env₁ p hp = env₂ p hp) :
    {n : ℕ} → (R : Rel σ V n) → (args : Fin n → M.frame.D w) →
    M.interpRel R w env₁ args = M.interpRel R w env₂ args
  | _, .R hr,      _    => by simp only [RModel.interpRel]
  | _, .eval R' t, args => by
      simp only [RModel.interpRel]
      rw [interpTerm_congr M w env₁ env₂ h t]
      exact interpRel_congr M w env₁ env₂ h R' _

/-- Agreeing environments stay agreeing after `Env.extend` by the same value. -/
theorem Env.extend_congr {M : RModel σ} {V : VarCtx} {w : M.frame.W} {env₁ env₂ : Env M V w}
    (h : ∀ p hp, env₁ p hp = env₂ p hp) (x : VarSymb × VarType)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (a : M.frame.interp x.2 w) :
    ∀ p hp, (env₁.extend x hx a) p hp = (env₂.extend x hx a) p hp := by
  intro p hp; simp only [Env.extend]
  by_cases hpx : p = x
  · simp only [dif_pos hpx]
  · simp only [dif_neg hpx]; exact h p _

/-- Agreeing environments stay agreeing after `Env.boxPush` to an accessible world. -/
theorem Env.boxPush_congr {M : RModel σ} {V W : VarCtx} {w : M.frame.W}
    (hsub : (VarCtx_box V).1 ⊆ W.1) {env₁ env₂ : Env M W w}
    (h : ∀ p hp, env₁ p hp = env₂ p hp) (w' : {w' : M.frame.W // M.frame.R w w'}) :
    ∀ p hp, (Env.boxPush hsub env₁ w') p hp = (Env.boxPush hsub env₂ w') p hp := by
  intro p hp; simp only [Env.boxPush]; rw [h]

/-- **Congruence for `interpWFF`**: agreeing environments satisfy the same formulas.  Foundational for
    the Truth Lemma (which manipulates the environment across worlds) and for the big three. -/
theorem interpWFF_congr (M : RModel σ) : {V : VarCtx} → (φ : WFF σ V) → (w : M.frame.W) →
    (env₁ env₂ : Env M V w) → (∀ p hp, env₁ p hp = env₂ p hp) →
    (M.interpWFF φ w env₁ ↔ M.interpWFF φ w env₂)
  | _, .atom R, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]; exact Iff.of_eq (interpRel_congr M w env₁ env₂ h R Fin.elim0)
  | _, .top, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _ => Iff.rfl
  | _, .and φ ψ, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      exact and_congr (interpWFF_congr M φ w env₁ env₂ h) (interpWFF_congr M ψ w env₁ env₂ h)
  | _, .or φ ψ, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      exact or_congr (interpWFF_congr M φ w env₁ env₂ h) (interpWFF_congr M ψ w env₁ env₂ h)
  | _, .imp φ ψ, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      exact imp_congr (interpWFF_congr M φ w env₁ env₂ h) (interpWFF_congr M ψ w env₁ env₂ h)
  | _, .eq s t, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      rw [interpTerm_congr M w env₁ env₂ h s, interpTerm_congr M w env₁ env₂ h t]
  | _, @WFF.all _ _ x hx φ, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      exact forall_congr' (fun a => interpWFF_congr M φ w _ _ (Env.extend_congr h x hx a))
  | _, @WFF.ex _ _ x hx φ, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      exact exists_congr (fun a => interpWFF_congr M φ w _ _ (Env.extend_congr h x hx a))
  | _, .box φ hsub _, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      exact forall_congr' (fun w' =>
        interpWFF_congr M φ w'.1 _ _ (Env.boxPush_congr hsub h w'))
  | _, .dia x hx φ hsub _, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      refine exists_congr (fun dv => and_congr (Iff.of_eq ?_) ?_)
      · rw [h ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))]
      · exact interpWFF_congr M φ dv.1.1 _ _
          (Env.extend_congr (Env.boxPush_congr _ h dv.1) x hx dv.2)
  | _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body, w, env₁, env₂, h => by
      simp only [RModel.interpWFF]
      refine interpWFF_congr M body w _ _ (fun p hp => ?_)
      simp only [peLookup]
      by_cases hpv1 : p = v₁
      · simp only [dif_pos hpv1]; rw [h]
      · by_cases hpv2 : p = v₂
        · simp only [dif_neg hpv1, dif_pos hpv2]; rw [h]
        · simp only [dif_neg hpv1, dif_neg hpv2]; rw [h]

/-! ### `termToGFunc` congruence (GFunc analog of `termToNecLvl_congr`).

The definable-map compiler depends only on the projection assignment's values on the free variables.
Foundational for a future `termToGFunc` weakening lemma (which the `diaterm`-over-box `ctx_ext` case
needs).  `boxterm`/`diaterm` reduce entirely through `boxCtx_congr` (the projections are absorbed into
the `boxCtx`), so no recursive `termToGFunc_congr` call is needed there. -/

/-- `boxCtx` depends only on its projection family, pointwise. -/
theorem boxCtx_congr {σ : Signature} {ctxType : VarType} :
    (l : List (VarSymb × VarType)) →
    (bp₁ bp₂ : (q : VarSymb × VarType) → q ∈ l → GFunc σ ctxType q.2.VTypeBox) →
    (∀ q hq, bp₁ q hq = bp₂ q hq) → boxCtx l bp₁ = boxCtx l bp₂
  | [], _, _, _ => rfl
  | q :: rest, bp₁, bp₂, h => by
      have hR := boxCtx_congr rest (fun p hp => bp₁ p (List.mem_cons.mpr (Or.inr hp)))
                   (fun p hp => bp₂ p (List.mem_cons.mpr (Or.inr hp)))
                   (fun p hp => h p (List.mem_cons.mpr (Or.inr hp)))
      simp only [boxCtx]
      rw [hR, h q (List.mem_cons.mpr (Or.inl rfl))]

mutual
theorem termToGFunc_congr {σ : Signature} {ctxType : VarType} : {V : VarCtx} →
    (proj₁ proj₂ : Proj σ ctxType V) → (∀ p hp, proj₁ p hp = proj₂ p hp) →
    {S : VarType} → (t : Term σ V S) → termToGFunc proj₁ t = termToGFunc proj₂ t
  | _, proj₁, proj₂, h, _, .var ⟨v, hv⟩ => h ⟨v, .Var⟩ hv
  | _, proj₁, proj₂, h, _, .func ff => by
      simp only [termToGFunc]
      exact funcToGFunc_congr proj₁ proj₂ h ff GFunc.unit GFunc.unit rfl
  | _, _, _, _, _, .unit => rfl
  | _, proj₁, proj₂, h, _, .pair a b => by
      simp only [termToGFunc, termToGFunc_congr proj₁ proj₂ h a, termToGFunc_congr proj₁ proj₂ h b]
  | _, proj₁, proj₂, h, _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body => by
      simp only [termToGFunc]
      apply termToGFunc_congr _ _ (fun p hp => ?_) body
      simp only [peLookup]
      by_cases hpv1 : p = v₁
      · simp only [dif_pos hpv1]; rw [h]
      · by_cases hpv2 : p = v₂
        · simp only [dif_neg hpv1, dif_pos hpv2]; rw [h]
        · simp only [dif_neg hpv1, dif_neg hpv2]; rw [h]
  | _, proj₁, proj₂, h, _, @Term.boxterm _ Vin _ _ s hsub _ => by
      simp only [termToGFunc]
      rw [boxCtx_congr Vin.1.toList _ _ (fun q hq =>
            h ⟨q.1, q.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨q, Finset.mem_toList.mp hq, rfl⟩)))]
  | _, proj₁, proj₂, h, _, @Term.diaterm _ Vdia _ _ x hx tt hsub _ => by
      simp only [termToGFunc]
      rw [boxCtx_congr Vdia.1.toList _ _ (fun q hq =>
            h ⟨q.1, q.2.VTypeBox⟩ (hsub (Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨q, Finset.mem_toList.mp hq, rfl⟩)))),
          h ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _))]
theorem funcToGFunc_congr {σ : Signature} {ctxType : VarType} : {V : VarCtx} →
    (proj₁ proj₂ : Proj σ ctxType V) → (∀ p hp, proj₁ p hp = proj₂ p hp) →
    {n : ℕ} → (ff : Func σ V n) → (args₁ args₂ : GFunc σ ctxType (VarPow n)) → args₁ = args₂ →
    funcToGFunc proj₁ ff args₁ = funcToGFunc proj₂ ff args₂
  | _, _, _, _, _, .F ⟨f, hf⟩, args₁, args₂, hargs => by
      subst hf; simp only [funcToGFunc]; rw [hargs]
  | _, proj₁, proj₂, h, _, .eval g t, args₁, args₂, hargs => by
      simp only [funcToGFunc]
      exact funcToGFunc_congr proj₁ proj₂ h g _ _
        (by rw [termToGFunc_congr proj₁ proj₂ h t, hargs])
end

/-! ### `termToGFunc` faithfulness: evaluating the compiled definable map = interpreting the term.

`gEvalN m (termToGFunc proj tt) arg = termToNecLvl m (env-from-proj) tt`, where each variable's env
value is `gEvalN m (proj p) arg`.  Level-generic (the `boxterm` case recurses `gEvalN m → m+1`).  This
is THE lemma that unblocks the `diaterm` modal cases: via `posLift_eval`/`posStrength_eval` +
`pos_inj`, a `diaterm` value's realization set is expressed through `GFunc.eval` of the compiled body,
and faithfulness rewrites that back to `interpTerm`, so the old `mapPos`+congr+`boxPush` argument
applies.  All cases proved: `func` via the `toVecN`/`funcNecStkLvl` plumbing, `boxterm` via
`boxCtx_eval`, `diaterm` via `bundleNecLvl_eq_boxCtx` (+ `boxCtx_eval`). -/
/-- **`boxCtx` faithfulness**: assembling the boxed projections into `□Γ` (via `boxProd`/`boxUnit`)
    and then projecting the `q`-component back out (at level `m+1`) recovers the original boxed
    projection `bp q` (evaluated at level `m`).  The `boxProd`/`boxUnit` evals are the identity, so
    this is a clean induction on the list. -/
theorem boxCtx_eval (M : RModel σ) {ctxType : VarType} (w : M.frame.W) (m : ℕ)
    (arg : M.frame.interpN ctxType m w) :
    (l : List (VarSymb × VarType)) →
    (bp : (q : VarSymb × VarType) → q ∈ l → GFunc σ ctxType q.2.VTypeBox) →
    (q : VarSymb × VarType) → (hq : q ∈ l) →
    M.frame.gEvalN M.gOps w (m + 1) ((boxCtx l bp).2.2 q hq)
        (M.frame.gEvalN M.gOps w m (boxCtx l bp).2.1 arg)
      = M.frame.gEvalN M.gOps w m (bp q hq) arg
  | [],       _,  _, hq => by simp at hq
  | q₀ :: rest, bp, q, hq => by
      by_cases hpq : q = q₀
      · subst hpq
        simp only [boxCtx, RFrame.gEvalN, GFunc.gpair, dif_pos]
      · simp only [boxCtx, RFrame.gEvalN, GFunc.gpair, dif_neg hpq]
        exact boxCtx_eval M w m arg rest
          (fun p hp => bp p (List.mem_cons.mpr (Or.inr hp))) q ((List.mem_cons.mp hq).resolve_left hpq)

/-- **`bundleNecLvl` = `boxCtx` (packaged)**: the interpreter's value-bundle equals the compiler's
    `boxCtx` with its box-context `GFunc` *evaluated*.  Packaging `Γ` in the `PSigma` makes this
    well-typed with no cast; `rw [IH]` substitutes the whole rest-structure, aligning `.1`/`.2.1`/`.2.2`
    at once.  This is what lets the `diaterm` faithfulness case rewrite the interpreter's bundle into
    the compiler's `boxCtx` form (so the two `termToGFunc` bodies coincide). -/
theorem bundleNecLvl_eq_boxCtx (M : RModel σ) {ctxType : VarType} (w : M.frame.W) (m : ℕ)
    (arg : M.frame.interpN ctxType m w) :
    (l : List (VarSymb × VarType)) →
    (bp : (q : VarSymb × VarType) → q ∈ l → GFunc σ ctxType q.2.VTypeBox) →
    (necOf : (p : VarSymb × VarType) → p ∈ l → M.frame.interpN p.2 (m + 1) w) →
    (∀ p hp, necOf p hp = M.frame.gEvalN M.gOps w m (bp p hp) arg) →
    M.bundleNecLvl m l necOf
      = ⟨(boxCtx l bp).1, M.frame.gEvalN M.gOps w m (boxCtx l bp).2.1 arg, (boxCtx l bp).2.2⟩
  | [],        _,  _,     _ => by simp only [RModel.bundleNecLvl, boxCtx, RFrame.gEvalN]
  | q :: rest, bp, necOf, h => by
      simp only [RModel.bundleNecLvl, boxCtx, RFrame.gEvalN, GFunc.gpair]
      rw [bundleNecLvl_eq_boxCtx M w m arg rest (fun p hp => bp p (List.mem_cons.mpr (Or.inr hp)))
            (fun p hp => necOf p (List.mem_cons.mpr (Or.inr hp)))
            (fun p hp => h p (List.mem_cons.mpr (Or.inr hp))),
          h q (List.mem_cons.mpr (Or.inl rfl))]

mutual
theorem termToGFunc_gEvalN (M : RModel σ) {ctxType : VarType} (w : M.frame.W) : {V : VarCtx} →
    (proj : Proj σ ctxType V) → (m : ℕ) → (arg : M.frame.interpN ctxType m w) →
    {S : VarType} → (tt : Term σ V S) →
    M.frame.gEvalN M.gOps w m (termToGFunc proj tt) arg
      = M.termToNecLvl m (fun p hp => M.frame.gEvalN M.gOps w m (proj p hp) arg) tt
  | _, proj, m, arg, _, .var ⟨v, hv⟩ => by
      simp only [termToGFunc, RModel.termToNecLvl]
  | _, proj, m, arg, _, .func ff => by
      simp only [termToGFunc, RModel.termToNecLvl]
      rw [funcToGFunc_gEvalN M w proj m arg ff GFunc.unit]
      simp only [RFrame.gEvalN, RFrame.toVecN]
  | _, proj, m, arg, _, .unit => by
      simp only [termToGFunc, RModel.termToNecLvl, RFrame.gEvalN]
  | _, proj, m, arg, _, .pair a b => by
      simp only [termToGFunc, RModel.termToNecLvl, GFunc.gpair, RFrame.gEvalN]
      rw [termToGFunc_gEvalN M w proj m arg a, termToGFunc_gEvalN M w proj m arg b]
  | _, proj, m, arg, _, .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq body => by
      simp only [termToGFunc, RModel.termToNecLvl]
      rw [termToGFunc_gEvalN M w _ m arg body]
      refine termToNecLvl_congr M m _ _ (fun p hp => ?_) body
      exact peLookup_natural
        (fun {A B} g => GFunc.comp (GFunc.fst : GFunc σ (A.VTypeProd B) A) g)
        (fun {A B} g => GFunc.comp (GFunc.snd : GFunc σ (A.VTypeProd B) B) g)
        (fun {A B} x => (x : M.frame.interpN A m w × M.frame.interpN B m w).1)
        (fun {A B} x => (x : M.frame.interpN A m w × M.frame.interpN B m w).2)
        (fun g => M.frame.gEvalN M.gOps w m g arg)
        (fun _ => rfl) (fun _ => rfl) v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁eq w₂eq proj p hp
  | _, proj, m, arg, _, @Term.boxterm _ Vin _ _ s hsub _ => by
      simp only [termToGFunc, RModel.termToNecLvl, RFrame.gEvalN]
      rw [termToGFunc_gEvalN M w _ (m + 1) _ s]
      refine termToNecLvl_congr M (m + 1) _ _ (fun p hp => ?_) s
      exact boxCtx_eval M w m arg Vin.1.toList
        (fun q hq => proj ⟨q.1, q.2.VTypeBox⟩
          (hsub (Finset.mem_image.mpr ⟨q, Finset.mem_toList.mp hq, rfl⟩)))
        p (Finset.mem_toList.mpr hp)
  | _, proj, m, arg, _, @Term.diaterm _ Vdia _ _ x hx tt hsub _ => by
      simp only [termToGFunc, RModel.termToNecLvl]
      rw [bundleNecLvl_eq_boxCtx M w m arg Vdia.1.toList
            (fun q hq => proj ⟨q.1, q.2.VTypeBox⟩
              (hsub (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, Finset.mem_toList.mp hq, rfl⟩))))
            _ (fun p hp => rfl)]
      simp only [RFrame.gEvalN, GFunc.gpair, RModel.posLiftStkLvl, RModel.posStrengthStkLvl,
        RModel.gOps]

theorem funcToGFunc_gEvalN (M : RModel σ) {ctxType : VarType} (w : M.frame.W) : {V : VarCtx} →
    (proj : Proj σ ctxType V) → (m : ℕ) → (arg : M.frame.interpN ctxType m w) →
    {n : ℕ} → (ff : Func σ V n) → (gargs : GFunc σ ctxType (VarPow n)) →
    M.frame.gEvalN M.gOps w m (funcToGFunc proj ff gargs) arg
      = M.funcToNecLvl m (fun p hp => M.frame.gEvalN M.gOps w m (proj p hp) arg) ff
          (M.frame.toVecN m _ (M.frame.gEvalN M.gOps w m gargs arg))
  | _, proj, m, arg, _, .F ⟨f, hf⟩, gargs => by
      subst hf
      simp only [funcToGFunc, RFrame.gEvalN, RModel.funcToNecLvl, RModel.funcNecStkLvl, RModel.gOps]
  | _, proj, m, arg, _, .eval g t, gargs => by
      simp only [funcToGFunc, RModel.funcToNecLvl]
      rw [funcToGFunc_gEvalN M w proj m arg g (GFunc.gpair (termToGFunc proj t) gargs)]
      congr 1
      simp only [GFunc.gpair, RFrame.gEvalN, RFrame.toVecN]
      rw [termToGFunc_gEvalN M w proj m arg t]
end

/-! ### Level-0 faithfulness (`GFunc.eval`), via a `GFunc.eval = gEvalN 0` bridge.

`posLift_eval`/`posStrength_eval` characterise `posEval` through `GFunc.eval` (not `gEvalN`), so the
diaterm `posEval` argument needs faithfulness for `GFunc.eval`.  Since `GFunc.eval ≠ gEvalN 0` defeq
(they differ at `sym`/`diaLift`/`diaStrength`), bridge them via the `*_hole` laws (the `interp_boxes`
casts at level 0 are identity by proof-irrelevance of `Eq`), then reuse `termToGFunc_gEvalN` at `m=0`. -/

/-- `toVecN` at level 0 is `toVec`. -/
theorem toVecN_zero (M : RFrame σ) : (n : ℕ) → {w : M.W} → (a : M.interpN (VarPow n) 0 w) →
    M.toVecN 0 n a = M.toVec n a
  | 0,     _, _ => rfl
  | n + 1, _, p => by simp only [RFrame.toVecN, RFrame.toVec, toVecN_zero M n p.2]

/-- **Bridge**: `GFunc.eval` = `gEvalN` at box-depth 0 (via the `*_hole` laws for the modal leaves). -/
theorem GFunc_eval_eq_gEvalN0 (M : RModel σ) (w : M.frame.W) :
    {A B : VarType} → (G : GFunc σ A B) → (a : M.frame.interp A w) →
    RFrame.GFunc.eval M.frame M.gOps w G a = M.frame.gEvalN M.gOps w 0 G a
  | _, _, .sym f, a => by
      simp only [RFrame.GFunc.eval, RFrame.gEvalN, RModel.gOps, Stk.boxes, toVecN_zero]
      rw [M.funcNecStk_hole]
  | _, _, .idm,      _ => rfl
  | _, _, .comp g h, a => by
      simp only [RFrame.GFunc.eval, RFrame.gEvalN]
      rw [GFunc_eval_eq_gEvalN0 M w h a, GFunc_eval_eq_gEvalN0 M w g _]
  | _, _, .prod g h, p => by
      simp only [RFrame.GFunc.eval, RFrame.gEvalN]
      rw [GFunc_eval_eq_gEvalN0 M w g p.1, GFunc_eval_eq_gEvalN0 M w h p.2]
  | _, _, .diag,     _ => rfl
  | _, _, .fst,      _ => rfl
  | _, _, .snd,      _ => rfl
  | _, _, .unit,     _ => rfl
  | _, _, .boxLift φ, _ => rfl
  | _, _, .boxProd,  _ => rfl
  | _, _, .boxUnit,  _ => rfl
  | _, _, .diaLift φ, a => by
      simp only [RFrame.GFunc.eval, RFrame.gEvalN, RModel.gOps, Stk.boxes]
      rw [M.posLiftStk_hole]
  | _, _, .diaStrength, p => by
      simp only [RFrame.GFunc.eval, RFrame.gEvalN, RModel.gOps, Stk.boxes]
      rw [M.posStrengthStk_hole]

/-- **Level-0 faithfulness**: evaluating the compiled definable map (`GFunc.eval`) = interpreting the
    term (`interpTerm`), env = `GFunc.eval ∘ proj`.  Immediate from the bridge + `termToGFunc_gEvalN`. -/
theorem termToGFunc_eval (M : RModel σ) {ctxType : VarType} {V : VarCtx} (w : M.frame.W)
    (proj : Proj σ ctxType V) (arg : M.frame.interp ctxType w) {S : VarType} (tt : Term σ V S) :
    RFrame.GFunc.eval M.frame M.gOps w (termToGFunc proj tt) arg
      = M.interpTerm w (fun p hp => RFrame.GFunc.eval M.frame M.gOps w (proj p hp) arg) tt := by
  simp only [RModel.interpTerm]
  rw [GFunc_eval_eq_gEvalN0 M w (termToGFunc proj tt) arg, termToGFunc_gEvalN M w proj 0 arg tt]
  exact termToNecLvl_congr M 0 _ _
    (fun p hp => (GFunc_eval_eq_gEvalN0 M w (proj p hp) arg).symm) tt

/-! ### Diaterm `posEval` characterization (the tool for the diaterm modal cases).

At level 0 the interpreter's `posLiftStkLvl 0`/`posStrengthStkLvl 0` reduce to `posLift`/`posStrength`
(via the `*_hole` laws + level-0 cast collapse), so the diaterm value = `posLift (termToGFunc body)
(posStrength bundle witness)`.  Then `posLift_eval` + `posStrength_eval` + `termToGFunc_eval`
characterise its realization set through `interpTerm` of the body. -/

/-- `posLiftStkLvl` at box-depth 0 is `posLift`. -/
theorem posLiftStkLvl_zero (M : RModel σ) {A B : VarType} {w : M.frame.W} (φ : GFunc σ A B)
    (x : M.frame.interpN A.VTypeDia 0 w) :
    M.posLiftStkLvl 0 φ x = M.posLift φ x := by
  simp only [RModel.posLiftStkLvl, Stk.boxes]; rw [M.posLiftStk_hole]

/-- `posStrengthStkLvl` at box-depth 0 is `posStrength`. -/
theorem posStrengthStkLvl_zero (M : RModel σ) {A B : VarType} {w : M.frame.W}
    (n : M.frame.interpN A.VTypeBox 0 w) (x : M.frame.interpN B.VTypeDia 0 w) :
    M.posStrengthStkLvl 0 n x = M.posStrength n x := by
  simp only [RModel.posStrengthStkLvl, Stk.boxes]; rw [M.posStrengthStk_hole]

/-- **Bundle-at-realization**: evaluating the bundle's `p`-projection at the `necEval`'d bundle value
    recovers the `necEval` of the `p`-th necessary object (`= boxPush` on that variable).  Induction on
    the list, using `necEval_prod` (necEval distributes over the bundle's product). -/
theorem bundle_proj_necEval (M : RModel σ) {w : M.frame.W}
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
    (l : List (VarSymb × VarType)) →
    (necOf : (p : VarSymb × VarType) → p ∈ l → M.frame.interpN p.2 1 w) →
    (p : VarSymb × VarType) → (hp : p ∈ l) →
    RFrame.GFunc.eval M.frame M.gOps w'.1 ((M.bundleNecLvl 0 l necOf).2.2 p hp)
        (M.necEval (M.bundleNecLvl 0 l necOf).2.1 w')
      = M.necEval (necOf p hp) w'
  | [],        _,     _, hq => by simp at hq
  | q₀ :: rest, necOf, p, hp => by
      by_cases hpq : p = q₀
      · subst hpq
        simp only [RModel.bundleNecLvl, RFrame.GFunc.eval, M.necEval_prod, ↓reduceDIte]
      · simp only [RModel.bundleNecLvl, RFrame.GFunc.eval, dif_neg hpq, M.necEval_prod]
        exact bundle_proj_necEval M w' rest
          (fun p hp => necOf p (List.mem_cons.mpr (Or.inr hp))) p
          ((List.mem_cons.mp hp).resolve_left hpq)

/-- **Diaterm `posEval` characterization** (the reusable tool): a diaterm value's realization set is
    exactly the old-interpreter `mapPos` set — *some* realization `v` of the ◇-variable, with the body
    interpreted at the realization world under the `boxPush`+`extend` environment.  Assembled from the
    level-0 reductions + `posLift_eval` + `posStrength_eval` + `termToGFunc_eval` + `bundle_proj_necEval`. -/
theorem posEval_interpTerm_diaterm (M : RModel σ) {V Vdia : VarCtx} (x : VarSymb × VarType)
    (hx : x.1 ∉ VarCtx_to_VarSymbs Vdia) {S : VarType} (tt : Term σ (VarCtx_insert x Vdia hx) S)
    (hsub : (VarCtx_dia x Vdia hx).1 ⊆ V.1)
    (hnbe : ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (VarCtx_dia x Vdia hx).1)
    (w : M.frame.W) (env : Env M V w)
    (ru : Σ' w' : {w' : M.frame.W // M.frame.R w w'}, M.frame.interp S w'.1) :
    ru ∈ M.posEval (M.interpTerm w env (Term.diaterm x hx tt hsub hnbe)) ↔
      ∃ v : M.frame.interp x.2 ru.1.1,
        (⟨ru.1, v⟩ : Σ' w' : {w' : M.frame.W // M.frame.R w w'}, M.frame.interp x.2 w'.1)
            ∈ M.posEval (env ⟨x.1, x.2.VTypeDia⟩ (hsub (Finset.mem_insert_self _ _)))
          ∧ M.interpTerm ru.1.1
              ((Env.boxPush (fun _ hp => hsub (Finset.mem_insert_of_mem hp)) env ru.1).extend x hx v)
              tt
            = ru.2 := by
  simp only [RModel.interpTerm, RModel.termToNecLvl]
  rw [posLiftStkLvl_zero, posStrengthStkLvl_zero, M.posLift_eval]
  simp only [M.posStrength_eval]
  constructor
  · rintro ⟨a, ⟨hmem, ha1⟩, hbody⟩
    refine ⟨a.2, hmem, Eq.trans (termToNecLvl_congr M 0 _ _ (fun p hp => ?_) tt)
      ((termToGFunc_eval M ru.fst.1 _ a tt).symm.trans hbody)⟩
    by_cases hpx : p = x
    · subst hpx
      simp only [Env.extend, ↓reduceDIte, RFrame.GFunc.eval, eqRec_eq_cast, cast_eq]
    · simp only [Env.extend, Env.boxPush, dif_neg hpx, RFrame.GFunc.eval]
      rw [ha1, bundle_proj_necEval M ru.fst Vdia.1.toList _ p
        (Finset.mem_toList.mpr ((Finset.mem_insert.mp hp).resolve_left hpx))]
  · rintro ⟨v, hmem, hbody⟩
    refine ⟨⟨_, v⟩, ⟨hmem, rfl⟩,
      (termToGFunc_eval M ru.fst.1 _ _ tt).trans
        (Eq.trans (termToNecLvl_congr M 0 _ _ (fun p hp => ?_) tt) hbody)⟩
    by_cases hpx : p = x
    · subst hpx
      simp only [Env.extend, ↓reduceDIte, RFrame.GFunc.eval, eqRec_eq_cast, cast_eq]
    · simp only [Env.extend, Env.boxPush, dif_neg hpx, RFrame.GFunc.eval]
      rw [bundle_proj_necEval M ru.fst Vdia.1.toList _ p
        (Finset.mem_toList.mpr ((Finset.mem_insert.mp hp).resolve_left hpx))]

/-- **`necEvalLvl` injectivity**: a level-`(j+1)` object is determined by its `necEvalLvl` peels (via
    `necEvalLvl_eq_necEval` + `nec_inj`).  Lets the diaterm-over-box `ctx_ext` case peel to level 0. -/
theorem necEvalLvl_inj (M : RModel σ) (S : VarType) (j : ℕ) {w : M.frame.W}
    {L R : M.frame.interpN S (j + 1) w}
    (h : ∀ w' : {w' : M.frame.W // M.frame.R w w'},
        M.necEvalLvl S j w L w' = M.necEvalLvl S j w R w') : L = R := by
  have hcast : (M.frame.interp_boxes S (j + 1) w).symm ▸ L
             = (M.frame.interp_boxes S (j + 1) w).symm ▸ R := by
    apply M.nec_inj
    funext w'
    have hw := h w'
    rw [M.necEvalLvl_eq_necEval S, M.necEvalLvl_eq_necEval S, eqRec_eq_cast, eqRec_eq_cast] at hw
    exact (cast_inj _).mp hw
  rw [eqRec_eq_cast, eqRec_eq_cast] at hcast
  exact (cast_inj _).mp hcast

/-! ### Env / boxPush plumbing (verbatim ports; `Env.boxPush`/`Env.extend` are model-agnostic).
    Placed here (before the fuel lemma) since the diaterm-over-box `ctx_ext` base case uses them. -/

/-- Transporting an environment along a context equality commutes with lookup. -/
theorem Env_transport_apply {M : RModel σ} {W1 W2 : VarCtx} {w : M.frame.W} (h : W1 = W2)
    (F : Env M W1 w) (p : VarSymb × VarType) (hp : p ∈ W2.1) :
    (h ▸ F) p hp = F p (h ▸ hp) := by subst h; rfl

/-- Extending the env by a **not-box**-typed variable leaves `boxPush` unchanged. -/
theorem boxPush_extend_notBox (M : RModel σ) {V_inner W : VarCtx} {w : M.frame.W}
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hsub' : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert xv W hxv).1)
    (env : Env M W w) (a : M.frame.interp xv.2 w) (hxvBox : xv.2.isBox = false)
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
    Env.boxPush hsub' (env.extend xv hxv a) w' = Env.boxPush hsub env w' := by
  funext p hp
  have hne : (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ≠ xv := by
    rintro rfl; simp [VarType.isBox] at hxvBox
  simp only [Env.boxPush, Env.extend, dif_neg hne]

/-- Extending by a **box**-typed variable pushes to extending the inner `boxPush` env by its
    `necEval`'d value. -/
theorem boxPush_extend_box (M : RModel σ) {V_inner W : VarCtx} {w : M.frame.W}
    {xs : VarSymb} {U' : VarType} {hxs : xs ∉ VarCtx_to_VarSymbs W}
    (hxs_inner : xs ∉ VarCtx_to_VarSymbs V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hsub' : (VarCtx_box (VarCtx_insert ⟨xs, U'⟩ V_inner hxs_inner)).1
             ⊆ (VarCtx_insert ⟨xs, U'.VTypeBox⟩ W hxs).1)
    (env : Env M W w) (a : M.frame.interp U'.VTypeBox w)
    (w' : {w' : M.frame.W // M.frame.R w w'}) :
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

/-- Two independent `Env.extend`s commute (across the `insert_comm` context cast). -/
theorem Env.extend_comm {M : RModel σ} {V : VarCtx} {w : M.frame.W} (env : Env M V w)
    {a b : VarSymb × VarType}
    (ha : a.1 ∉ VarCtx_to_VarSymbs V) (hb : b.1 ∉ VarCtx_to_VarSymbs V)
    (hb' : b.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert a V ha))
    (ha' : a.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert b V hb))
    (va : M.frame.interp a.2 w) (vb : M.frame.interp b.2 w)
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

/-! ### Context extension (`ctx_ext`) — term level, via a `sizeOf xv.2` fuel.

The syntactic `Term.ctx_ext` recurses on `xv.2` (peeling `□`/`×`), so the semantic lemma is not
structural in `t` alone; we thread a `fuel` bounding `sizeOf xv.2` and measure `(fuel, numNodes t)`.
Unlike the predecessor interpreter, the `boxterm` case here is *directly recursive at level `k+1`*
(no `necEval`/`nec_inj`): since `interpN (□U) k = interpN U (k+1)` definitionally, the extension
value `a` is reused verbatim one level up. -/

/-- Extend a level-`k` environment with a value for a fresh variable (level-`k` `Env.extend`). -/
noncomputable def extendN (M : RModel σ) (k : ℕ) {V : VarCtx} {w : M.frame.W}
    (env : (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 k w)
    (x : VarSymb × VarType) (hx : x.1 ∉ VarCtx_to_VarSymbs V) (a : M.frame.interpN x.2 k w) :
    (p : VarSymb × VarType) → p ∈ (VarCtx_insert x V hx).1 → M.frame.interpN p.2 k w :=
  fun p hp =>
    if hpx : p = x then (congrArg Prod.snd hpx).symm ▸ a
    else env p ((Finset.mem_insert.mp hp).resolve_left hpx)

/-- Level-`k` analog of `Env.extend_apply_ne`: looking up an already-present variable ignores the
    `extendN`. -/
theorem extendN_apply_ne (M : RModel σ) (k : ℕ) {V : VarCtx} {w : M.frame.W}
    (env : (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 k w)
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs V} (a : M.frame.interpN xv.2 k w)
    {q : VarSymb × VarType} (hq : q ∈ (VarCtx_insert xv V hxv).1) (hqV : q ∈ V.1) :
    (M.extendN k env xv hxv a) q hq = env q hqV := by
  have hne : q ≠ xv := fun h => hxv (h ▸ Finset.mem_image.mpr ⟨q, hqV, rfl⟩)
  simp only [extendN, dif_neg hne]

mutual
/-- Term-level context extension, fuel-indexed.  `var`/`func`/`unit`/`pair` and the `boxterm`
    (non-product) cases are proved; `boxterm`-over-product, `diaterm`, and `pair_elim` remain (the
    product/`pair_elim` cases need the `pairElim`/`unpairEnv` transport lemmas re-derived for the new
    interpreter, and `diaterm` needs a fresh proof against `posLiftStkLvl`/`bundleNecLvl`). -/
theorem termToNecLvl_ctx_ext_fuel (M : RModel σ) (fuel : ℕ) {V : VarCtx}
    (xv : VarSymb × VarType) (hfuel : sizeOf xv.2 ≤ fuel)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (k : ℕ) {w : M.frame.W}
    (env : (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 k w)
    (a : M.frame.interpN xv.2 k w) {S : VarType} (t : Term σ V S) :
    M.termToNecLvl k (M.extendN k env xv hxv a) (Term.ctx_ext xv hxv t)
      = M.termToNecLvl k env t := by
  match t with
  | .var ⟨v, hv⟩ =>
      have hne : (⟨v, VarType.Var⟩ : VarSymb × VarType) ≠ xv := by
        rintro rfl; exact hxv (Finset.mem_image.mpr ⟨_, hv, rfl⟩)
      simp only [Term.ctx_ext, RModel.termToNecLvl, extendN, dif_neg hne]
  | .func f =>
      simp only [Term.ctx_ext, RModel.termToNecLvl]
      exact funcToNecLvl_ctx_ext_fuel M fuel xv hfuel hxv k env a f Fin.elim0
  | .unit => simp only [Term.ctx_ext, RModel.termToNecLvl]
  | .pair t1 t2 =>
      simp only [Term.ctx_ext, RModel.termToNecLvl]
      rw [termToNecLvl_ctx_ext_fuel M fuel xv hfuel hxv k env a t1,
          termToNecLvl_ctx_ext_fuel M fuel xv hfuel hxv k env a t2]
  | @Term.boxterm _ V_inner S_inner _ tt hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      cases xt with
      | Var | VTypeOne | VTypeDia _ =>
          simp only [Term.ctx_ext, RModel.termToNecLvl]
          refine termToNecLvl_congr M (k + 1) _ _ (fun p hp => ?_) tt
          simp only [extendN]
          exact dif_neg (fun h => VarType.noConfusion (congrArg Prod.snd h))
      | VTypeBox U' =>
          have hfuelU' : sizeOf U' ≤ fuel := by
            have h : sizeOf (VarType.VTypeBox U') ≤ fuel := hfuel
            simp +arith at h; omega
          have hxv_inner : xs ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in; apply hxv
            obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in
            exact Finset.mem_image.mpr
              ⟨_, hsub (Finset.mem_image.mpr ⟨q, hq_in, rfl⟩), hq_eq⟩
          simp only [Term.ctx_ext, RModel.termToNecLvl]
          refine Eq.trans (termToNecLvl_congr M (k + 1) _
              (M.extendN (k + 1) (fun p hp =>
                  env ⟨p.1, p.2.VTypeBox⟩ (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
                ⟨xs, U'⟩ hxv_inner a) (fun p hp => ?_) (Term.ctx_ext ⟨xs, U'⟩ hxv_inner tt))
            (termToNecLvl_ctx_ext_fuel M fuel ⟨xs, U'⟩ hfuelU' hxv_inner (k + 1) _ a tt)
          obtain ⟨pv, pT⟩ := p
          simp only [extendN]
          by_cases hpx : (⟨pv, pT⟩ : VarSymb × VarType) = ⟨xs, U'⟩
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpx
            rw [dif_pos rfl, dif_pos rfl]
          · rw [dif_neg hpx]
            exact dif_neg (fun h => hpx (by
              obtain ⟨e1, e2⟩ := Prod.mk.inj h
              have e3 := VarType.VTypeBox.inj e2
              subst e1; subst e3; rfl))
      | VTypeProd A B => sorry
  | @Term.diaterm _ V_dia _ _ x hx tt hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      cases xt with
      | Var | VTypeOne | VTypeDia _ =>
          simp only [Term.ctx_ext, RModel.termToNecLvl]
          rw [bundleNecLvl_congr M k V_dia.1.toList _
                (fun p hp => env ⟨p.1, p.2.VTypeBox⟩
                  (hsub (Finset.mem_insert_of_mem
                    (Finset.mem_image.mpr ⟨p, Finset.mem_toList.mp hp, rfl⟩))))
                (fun p hp => M.extendN_apply_ne k env a _
                  (hsub (Finset.mem_insert_of_mem
                    (Finset.mem_image.mpr ⟨p, Finset.mem_toList.mp hp, rfl⟩)))),
              M.extendN_apply_ne k env a _ (hsub (Finset.mem_insert_self _ _))]
      | VTypeBox U' =>
          cases k with
          | zero =>
              show M.interpTerm w (Env.extend env ⟨xs, U'.VTypeBox⟩ hxv a)
                    (Term.ctx_ext ⟨xs, U'.VTypeBox⟩ hxv (Term.diaterm x hx tt hsub hnbe))
                  = M.interpTerm w env (Term.diaterm x hx tt hsub hnbe)
              apply M.pos_inj
              apply Set.ext
              intro ru
              simp only [Term.ctx_ext]
              rw [posEval_interpTerm_diaterm, posEval_interpTerm_diaterm]
              have hxv_inner : xs ∉ VarCtx_to_VarSymbs V_dia := by
                intro h_in; apply hxv
                obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in
                obtain ⟨qv, qT⟩ := q
                have hbox_in_dia : (⟨qv, qT.VTypeBox⟩ : VarSymb × VarType)
                    ∈ (VarCtx_dia x V_dia hx).1 := by
                  rw [VarCtx_dia_fst]
                  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩)
                exact Finset.mem_image.mpr ⟨_, hsub hbox_in_dia, hq_eq⟩
              have hwit : (⟨x.1, x.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 :=
                hsub (Finset.mem_insert_self _ _)
              have hxv_ne : xs ≠ x.1 := fun h => hxv (h ▸ Finset.mem_image.mpr ⟨_, hwit, rfl⟩)
              have hxv_outer : xs ∉ VarCtx_to_VarSymbs (VarCtx_insert x V_dia hx) :=
                not_mem_VarSymbs_insert hxv_ne hxv_inner
              apply exists_congr
              intro v
              rw [Env.extend_apply_ne env a _ hwit,
                  boxPush_extend_box M hxv_inner (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _
                    env a,
                  interpTerm_cast_term, Env.extend_comm]
              -- reduce `ctx_ext ⟨xs,U'⟩ tt` on the body via the fuel lemma at level 0
              -- (`interpTerm_ctx_ext` is unavailable here — defined after this mutual).
              have hfuelU' : sizeOf U' ≤ fuel := by
                have h : sizeOf (VarType.VTypeBox U') ≤ fuel := hfuel
                simp +arith at h; omega
              have hbody : M.interpTerm ru.fst.1
                    (Env.extend
                      ((Env.boxPush (fun _ hp => hsub (Finset.mem_insert_of_mem hp)) env ru.fst).extend
                        x hx v) ⟨xs, U'⟩ hxv_outer (M.necEval a ru.fst))
                    (Term.ctx_ext ⟨xs, U'⟩ hxv_outer tt)
                  = M.interpTerm ru.fst.1
                      ((Env.boxPush (fun _ hp => hsub (Finset.mem_insert_of_mem hp)) env ru.fst).extend
                        x hx v) tt :=
                termToNecLvl_ctx_ext_fuel M fuel ⟨xs, U'⟩ hfuelU' hxv_outer 0 _ (M.necEval a ru.fst) tt
              rw [hbody]
          | succ j =>
              apply necEvalLvl_inj M _ j
              intro w'
              rw [M.termToNecLvl_necEvalLvl, M.termToNecLvl_necEvalLvl]
              refine Eq.trans (termToNecLvl_congr M j _
                  (M.extendN j (fun p hp => M.necEvalLvl p.2 j w (env p hp) w')
                    ⟨xs, U'.VTypeBox⟩ hxv (M.necEvalLvl U'.VTypeBox j w a w'))
                  (fun p hp => ?_)
                  (Term.ctx_ext ⟨xs, U'.VTypeBox⟩ hxv (Term.diaterm x hx tt hsub hnbe)))
                (termToNecLvl_ctx_ext_fuel M fuel ⟨xs, U'.VTypeBox⟩ hfuel hxv j
                  (fun p hp => M.necEvalLvl p.2 j w (env p hp) w')
                  (M.necEvalLvl U'.VTypeBox j w a w') (Term.diaterm x hx tt hsub hnbe))
              by_cases hpxv : p = ⟨xs, U'.VTypeBox⟩
              · subst hpxv; simp only [extendN, ↓reduceDIte]
              · simp only [extendN, dif_neg hpxv]
      | VTypeProd A B => sorry
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => sorry
termination_by (fuel, t.numNodes, k)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.left; (try simp only [Term.numNodes, Func.numNodes]); omega)
    | (apply Prod.Lex.right; apply Prod.Lex.right; omega)

/-- Function-level context extension, fuel-indexed (feeds the `.func` case above). -/
theorem funcToNecLvl_ctx_ext_fuel (M : RModel σ) (fuel : ℕ) {V : VarCtx}
    (xv : VarSymb × VarType) (hfuel : sizeOf xv.2 ≤ fuel)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (k : ℕ) {w : M.frame.W}
    (env : (p : VarSymb × VarType) → p ∈ V.1 → M.frame.interpN p.2 k w)
    (a : M.frame.interpN xv.2 k w) {n : ℕ} (f : Func σ V n)
    (args : Fin n → M.frame.interpN VarType.Var k w) :
    M.funcToNecLvl k (M.extendN k env xv hxv a) (Func.ctx_ext xv hxv f) args
      = M.funcToNecLvl k env f args := by
  match f with
  | .F hr => simp only [Func.ctx_ext, RModel.funcToNecLvl]
  | .eval g t =>
      simp only [Func.ctx_ext, RModel.funcToNecLvl]
      rw [termToNecLvl_ctx_ext_fuel M fuel xv hfuel hxv k env a t]
      exact funcToNecLvl_ctx_ext_fuel M fuel xv hfuel hxv k env a g _
termination_by (fuel, f.numNodes, k)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; apply Prod.Lex.left; simp only [Term.numNodes, Func.numNodes]; omega)
end

/-- `ctx_ext` invariance at level 0 (`interpTerm`) — instantiates the fuel at `sizeOf xv.2`. -/
theorem interpTerm_ctx_ext (M : RModel σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S)
    (w : M.frame.W) (env : Env M V w) (a : M.frame.interp xv.2 w) :
    M.interpTerm w (env.extend xv hxv a) (Term.ctx_ext xv hxv t) = M.interpTerm w env t := by
  simp only [RModel.interpTerm]
  exact termToNecLvl_ctx_ext_fuel M (sizeOf xv.2) xv le_rfl hxv 0 env a t

/-! ### Rel plumbing for the `interpWFF` `atom` case. -/

/-- Relation-application context extension (feeds the `atom` WFF case). -/
theorem interpRel_ctx_ext (M : RModel σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {n : ℕ} (R : Rel σ V n)
    (w : M.frame.W) (env : Env M V w) (a : M.frame.interp xv.2 w) (args : Fin n → M.frame.D w) :
    M.interpRel (Rel.ctx_ext xv hxv R) w (env.extend xv hxv a) args
      = M.interpRel R w env args := by
  induction R with
  | R hr => simp only [Rel.ctx_ext, RModel.interpRel]
  | eval R' t ih =>
      simp only [Rel.ctx_ext, RModel.interpRel]
      rw [interpTerm_ctx_ext M xv hxv t w env a]
      exact ih _

/-- WFF-level context extension, fuel-indexed.  Non-modal, `eq`, `box`/`dia` (non-box + `VTypeBox`),
    and `all`/`ex` (non-collision) cases are proved via the ported plumbing; the `VTypeProd` cases
    (need `interpWFF_pairElim`/`unpairEnv_transport_eq`), the `all`/`ex` **collision** cases (need
    `interpWFF_rename`), and `pair_elim` remain `sorry`. -/
theorem interpWFF_ctx_ext_fuel (M : RModel σ) (k : ℕ) {V : VarCtx} (xv : VarSymb × VarType)
    (hk : sizeOf xv.2 ≤ k) (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) (w : M.frame.W)
    (env : Env M V w) (a : M.frame.interp xv.2 w) :
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
            intro h_in_inner; apply hxv
            obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
            exact Finset.mem_image.mpr
              ⟨_, hsub (Finset.mem_image.mpr ⟨q, hq_in, rfl⟩), hq_eq⟩
          simp only [WFF.ctx_ext, RModel.interpWFF]
          apply propext; apply forall_congr'; intro w'
          rw [boxPush_extend_box M hxv_inner hsub _ env a w']
          exact iff_of_eq (interpWFF_ctx_ext_fuel M k ⟨xs, U'⟩ hkU' hxv_inner ψ w'.1
            (Env.boxPush hsub env w') (M.necEval a w'))
      | VTypeProd A B => sorry
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
      | VTypeProd A B => sorry
  | @WFF.all _ _ x hx ψ =>
      by_cases h_col : xv.1 = x.1
      · sorry
      · have hxv_x : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) :=
          not_mem_VarSymbs_insert h_col hxv
        simp only [WFF.ctx_ext, RModel.interpWFF, dif_neg h_col]
        apply propext; apply forall_congr'; intro val
        rw [interpWFF_cast_term, Env.extend_comm, interpWFF_ctx_ext_fuel M k xv hk hxv_x ψ _ _ _]
  | @WFF.ex _ _ x hx ψ =>
      by_cases h_col : xv.1 = x.1
      · sorry
      · have hxv_x : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) :=
          not_mem_VarSymbs_insert h_col hxv
        simp only [WFF.ctx_ext, RModel.interpWFF, dif_neg h_col]
        apply propext; apply exists_congr; intro val
        rw [interpWFF_cast_term, Env.extend_comm, interpWFF_ctx_ext_fuel M k xv hk hxv_x ψ _ _ _]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => sorry
termination_by (k, WFF.numNodes φ)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; simp only [WFF.numNodes, WFF.numNodes_rename]; omega)
    | (apply Prod.Lex.left; omega)

/-- **Context extension**: interpreting under a fresh, unused variable `xv` ignores its value.
    (Weakening — needed wherever an induction step adds a bound variable.)
    Port of `SoundnessRealB.interpWFF_ctx_ext`. -/
theorem interpWFF_ctx_ext (M : RModel σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) (w : M.frame.W) (env : Env M V w)
    (a : M.frame.interp xv.2 w) :
    M.interpWFF (WFF.ctx_ext xv hxv φ) w (env.extend xv hxv a) = M.interpWFF φ w env :=
  interpWFF_ctx_ext_fuel M (sizeOf xv.2) xv le_rfl hxv φ w env a

/-- **Substitution**: substituting a term for a variable equals extending the environment with the
    term's value.  The `∀`/`∃` cases of soundness *and* of the completeness Truth Lemma both need
    this.  Port of `SoundnessRealB.interpWFF_substVar`. -/
theorem interpWFF_substVar (M : RModel σ) {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (t : Term σ V S) (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) (w : M.frame.W) (env : Env M V w) :
    M.interpWFF (WFF.substVar hx t φ) w env
      = M.interpWFF φ w (env.extend ⟨x, S⟩ hx (M.interpTerm w env t)) := by
  sorry

/-- **α-renaming**: renaming a variable that is bound nowhere in `φ` preserves interpretation
    (capture-avoidance for the `◇`/`∃` witness cases).  Port of `SoundnessRealB.interpWFF_rename`. -/
theorem interpWFF_rename (M : RModel σ) {old new : VarSymb} {repl_type : VarType} {V W : VarCtx}
    (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (φ : WFF σ W) (new_not_bound : new ∉ WFF.boundVars φ)
    (w : M.frame.W) (env : Env M V w) (val : M.frame.interp repl_type w) :
    M.interpWFF (WFF.rename old new repl_type V W old_fresh new_fresh Wdef φ new_not_bound) w
        (env.extend ⟨new, repl_type⟩ new_fresh val)
      = M.interpWFF φ w (Wdef.symm ▸ env.extend ⟨old, repl_type⟩ old_fresh val) := by
  sorry

end RModel
