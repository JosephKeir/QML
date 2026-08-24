import QML.SemanticsGeneral
import QML.SubstitutionLemmas

/-!
# Soundness — skeleton and plan

Goal: `Proof σ V Γ φ → (Γ ⊨ φ)`, i.e. every provable sequent is satisfied in every `GModel`
under every world/environment satisfying the hypotheses.  `GModel` here has total
`necIntro`/`posIntro` (the full-sections/full-witnesses class), so `interpTerm`/`interpWFF`
are total and everything is interpretable — this is the honest "check we're on the right
track" class; the proof uses only `necEval`/`posEval` and the `_beta` laws (and those only on
the denotable sections boxterms produce), so it retargets to the faithful denotable-containing
general class unchanged.

Equality is **primitive/intensional** here: `interpWFF.eq` is plain domain-equality, and the
model class carries *no* extensionality or path-independence obligations (those were dropped as
optional collapses).  So `eq_intro`/`eq_elim` are just `rfl` + Leibniz on domain-equality — no
world-extensionality lemma is needed, and nothing in the induction has to discharge a coherence.

## Plan (induction on `Proof`)

Trivial / propositional (pure `interpWFF` unfolding + logic):
  `ax, and_intro, and_elim_l/r, or_intro_l/r, or_elim, imp_intro, imp_elim, top_intro,
   bot_elim, lem`.

Structural context moves — need small `Env` lemmas:
  `weak` (Γ ⊆ Γ'), `weak_ctx` (context extension: an `Env` for the bigger context restricts;
   interpretation is invariant under the extra unused variable — a *weakening/vacuous-env*
   lemma, semantic mirror of the syntactic `ctx_ext`/vacuous-subst work).

Quantifiers — need the **semantic substitution lemma** (the real workhorse):
  `all_intro/ex_intro` : `∀/∃ a, interpWFF φ w (env.extend x hx a)` — direct from `interpWFF`'s
     `all`/`ex` clauses; `all_intro` needs the eigenvariable freshness (env-invariance again).
  `all_elim/ex_elim`   : instantiating at a witness term `t`.  Requires
     **`interpTerm (φ[x:=t]) = interpWFF φ (env.extend x (interpTerm t))`** — interpreting a
     substitution = extending the environment by the term's value.  Prove by induction on the
     term/formula (mirrors `SubstitutionLemmas.lean`).  THIS is the lemma to build first.
  `eq_intro` (`rfl`), `eq_elim` (Leibniz — same substitution lemma + `interpWFF.eq`).

Products: `pair_elim` — needs the product interpretation (currently `sorry` in `interpWFF`);
  defer until `pair_elim`/product clauses are filled.

Modal — the payoff, uses the destructors:
  `K_box`  : `interpWFF.box` = "∀ accessible w', … (boxPush)"; `K` distributes because
     `boxPush` is applied uniformly.  Needs: `interpWFF (□(φ→ψ)) → interpWFF (□φ) → interpWFF (□ψ)`
     pointwise over `w'`, i.e. `boxPush` commutes with the connective (it does, definitionally).
  `K_dia`, `dia_bot` : `interpWFF.dia` = the Skolem witness via `posEval`; distribute/absurd at
     the witness world.
  `Mlem` and any remaining modal axioms: unfold at the witness / over accessible worlds.

## Key lemmas to prove first (in order)
  1. `Env`-invariance under an unused/extra variable (weakening).            [`weak_ctx`, `all_intro`]
  2. **Semantic substitution**: `interpTerm/interpWFF (·[x:=t]) = ·.extend x (interpTerm t)`.  [`all_elim`,`ex_elim`,`eq_elim`]
  3. `boxPush` commutes with the connectives (mostly definitional).           [`K_box`]
-/

namespace GModel

universe u
variable {σ : Signature}

/-- Semantic entailment: in every model, every world/environment satisfying all hypotheses in
    `Γ` satisfies `φ`. -/
def Entails {V : VarCtx} (Γ : Finset (WFF σ V)) (φ : WFF σ V) : Prop :=
  ∀ (M : GModel.{u} σ) (w : M.W) (env : Env M V w),
    (∀ ψ ∈ Γ, M.interpWFF ψ w env) → M.interpWFF φ w env

@[inherit_doc] scoped notation:50 Γ " ⊨ " φ => Entails Γ φ

/-! ### Small hypothesis-set helper -/

/-- Extend a satisfied hypothesis set by one more satisfied formula (`Γ ∪ {ψ}`). -/
theorem sat_union_singleton {M : GModel.{u} σ} {V : VarCtx} {Γ : Finset (WFF σ V)}
    {ψ : WFF σ V} {w : M.W} {env : Env M V w}
    (hΓ : ∀ χ ∈ Γ, M.interpWFF χ w env) (hψ : M.interpWFF ψ w env) :
    ∀ χ ∈ Γ ∪ {ψ}, M.interpWFF χ w env :=
  fun χ hχ => (Finset.mem_union.mp hχ).elim (hΓ χ)
    (fun h => by rw [Finset.mem_singleton.mp h]; exact hψ)

/-- Restrict a satisfied hypothesis set to a subset (here `Γ ⊆ Γ ∪ {ψ}`). -/
theorem sat_of_union_left {M : GModel.{u} σ} {V : VarCtx} {Γ : Finset (WFF σ V)}
    {ψ : WFF σ V} {w : M.W} {env : Env M V w}
    (hΓ : ∀ χ ∈ Γ ∪ {ψ}, M.interpWFF χ w env) :
    ∀ χ ∈ Γ, M.interpWFF χ w env :=
  fun χ hχ => hΓ χ (Finset.mem_union_left _ hχ)

/-! ### The two workhorse semantic lemmas (to prove — see plan above)

`interpWFF_substVar` handles the quantifier/equality-elimination rules; `interpWFF_ctx_ext`
(with its `Finset` corollary) handles the eigenvariable / context-extension rules.

**Pair-free scope.**  The `SubstitutionLemmas.lean` computation rules (`Term.substVar_var/
func/unit/pair`, `WFF.substVar_and/or/imp/top/bot/eq/atom/all/ex`, and the modal
`substVar_boxterm_*`/`diaterm_*`) all carry `hpf : (VarCtx_insert ⟨x,S⟩ V hx).firstPairVar =
none` — the pair-free side condition.  So the semantic substitution lemma is stated with the
same `hpf`, and the soundness cases it feeds (`all_elim`, `ex_intro`, `eq_elim`) are for the
pair-free fragment — consistent with `pair_elim` already being deferred in `interpWFF`/
`interpTerm`.  Handling pairs is a later step tied to filling those `sorry`s.

Proof plan for `interpWFF_substVar`: induction on `φ` (generalizing `w`, `env`, and — for the
binder/modal cases — the context, since `all`/`ex`/`box`/`dia` recurse into an extended
context).  Propositional cases: rewrite by `WFF.substVar_*`, unfold `interpWFF`, apply the IH.
`eq`/`atom`: `WFF.substVar_eq`/`atom` + the term-level `interpTerm_substVar`.  Binder/modal
cases: the hard part — variable-reordering casts and `boxPush`/`env.extend` interaction. -/

/-- **Term-level semantic substitution** (base for `interpWFF_substVar`; pair-free). -/
theorem interpTerm_substVar (M : GModel.{u} σ) {V : VarCtx} {x : VarSymb} {S S' : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (s : Term σ V S) (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S') (w : M.W) (env : Env M V w) :
    M.interpTerm (Term.substVar hx s t) w env
      = M.interpTerm t w (env.extend ⟨x, S⟩ hx (M.interpTerm s w env)) := by
  sorry

/-- **Semantic substitution.**  Interpreting `φ[t/x]` = interpreting `φ` in the environment
    extended by `t`'s value (pair-free fragment; see the note above). -/
theorem interpWFF_substVar (M : GModel.{u} σ) {V : VarCtx} {x : VarSymb} {S : VarType}
    (hx : x ∉ VarCtx_to_VarSymbs V)
    (hpf : (VarCtx_insert ⟨x, S⟩ V hx).firstPairVar = none)
    (t : Term σ V S)
    (φ : WFF σ (VarCtx_insert ⟨x, S⟩ V hx)) (w : M.W) (env : Env M V w) :
    M.interpWFF (WFF.substVar hx t φ) w env
      = M.interpWFF φ w (env.extend ⟨x, S⟩ hx (M.interpTerm t w env)) := by
  sorry

/-- Extending an environment by a **non-box** variable leaves `boxPush` unchanged: the boxed
    lookups `⟨p.1, p.2.VTypeBox⟩` are box-typed, hence never equal to a non-box `xv`. -/
theorem boxPush_extend_notBox (M : GModel.{u} σ) {V_inner W : VarCtx} {w : M.W}
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs W}
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hsub' : (VarCtx_box V_inner).1 ⊆ (VarCtx_insert xv W hxv).1)
    (env : Env M W w) (a : M.interp xv.2 w) (hxvBox : xv.2.isBox = false)
    (w' : {w' : M.W // M.R w w'}) :
    Env.boxPush hsub' (env.extend xv hxv a) w' = Env.boxPush hsub env w' := by
  funext p hp
  have hne : (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType) ≠ xv := by
    rintro rfl; simp [VarType.isBox] at hxvBox
  simp only [Env.boxPush, Env.extend, dif_neg hne]

/-- Extending the env by a **box**-typed variable `⟨xs, U'.VTypeBox⟩` pushes, under a box, to
    extending the inner `boxPush` env by that variable's `necEval`'d value at `w'`. -/
theorem boxPush_extend_box (M : GModel.{u} σ) {V_inner W : VarCtx} {w : M.W}
    {xs : VarSymb} {U' : VarType} {hxs : xs ∉ VarCtx_to_VarSymbs W}
    (hxs_inner : xs ∉ VarCtx_to_VarSymbs V_inner)
    (hsub : (VarCtx_box V_inner).1 ⊆ W.1)
    (hsub' : (VarCtx_box (VarCtx_insert ⟨xs, U'⟩ V_inner hxs_inner)).1
             ⊆ (VarCtx_insert ⟨xs, U'.VTypeBox⟩ W hxs).1)
    (env : Env M W w) (a : M.interp U'.VTypeBox w) (w' : {w' : M.W // M.R w w'}) :
    Env.boxPush hsub' (env.extend ⟨xs, U'.VTypeBox⟩ hxs a) w'
      = (Env.boxPush hsub env w').extend ⟨xs, U'⟩ hxs_inner (M.necEval a w') := by
  funext p hp
  simp only [Env.boxPush, Env.extend]
  by_cases hpeq : p = (⟨xs, U'⟩ : VarSymb × VarType)
  · subst hpeq
    rw [dif_pos rfl, dif_pos rfl]
  · obtain ⟨pv, pT⟩ := p
    have hne : (⟨pv, pT.VTypeBox⟩ : VarSymb × VarType) ≠ ⟨xs, U'.VTypeBox⟩ := by
      intro h
      rw [Prod.mk.injEq] at h
      exact hpeq (Prod.ext_iff.mpr ⟨h.1, VarType.VTypeBox.inj h.2⟩)
    rw [dif_neg hne, dif_neg hpeq]

/-- Looking up a variable already in `V` in an extended environment ignores the extension. -/
theorem Env.extend_apply_ne {M : GModel.{u} σ} {V : VarCtx} {w : M.W} (env : Env M V w)
    {xv : VarSymb × VarType} {hxv : xv.1 ∉ VarCtx_to_VarSymbs V} (aa : M.interp xv.2 w)
    {q : VarSymb × VarType} (hq : q ∈ (VarCtx_insert xv V hxv).1) (hqV : q ∈ V.1) :
    (env.extend xv hxv aa) q hq = env q hqV := by
  have hne : q ≠ xv := fun h => hxv (h ▸ Finset.mem_image.mpr ⟨q, hqV, rfl⟩)
  simp only [Env.extend, dif_neg hne]

/-- Interpretation commutes with a context-equality cast (both `t` and `env` transported). -/
theorem interpTerm_cast (M : GModel.{u} σ) {W1 W2 : VarCtx} (h : W1 = W2) {S : VarType}
    (t : Term σ W1 S) (w : M.W) (env : Env M W1 w) :
    M.interpTerm (h ▸ t) w (h ▸ env) = M.interpTerm t w env := by
  subst h; rfl

/-- Cast on the term alone: transport the environment the other way. -/
theorem interpTerm_cast_term (M : GModel.{u} σ) {W1 W2 : VarCtx} (h : W1 = W2) {S : VarType}
    (t : Term σ W1 S) (w : M.W) (env : Env M W2 w) :
    M.interpTerm (h ▸ t) w env = M.interpTerm t w (h.symm ▸ env) := by
  subst h; rfl

/-- Applying a context-transported environment reindexes the membership proof. -/
theorem Env_transport_apply {M : GModel.{u} σ} {W1 W2 : VarCtx} {w : M.W} (h : W1 = W2)
    (F : Env M W1 w) (p : VarSymb × VarType) (hp : p ∈ W2.1) :
    (h ▸ F) p hp = F p (h ▸ hp) := by subst h; rfl

/-- Two independent `Env.extend`s commute (across the `insert_comm` context cast). -/
theorem Env.extend_comm {M : GModel.{u} σ} {V : VarCtx} {w : M.W} (env : Env M V w)
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

/-! Term/Func-level `ctx_ext` invariance (mutual; base for the `eq`/`atom` WFF cases).  Non-modal
    cases proved; modal (`boxterm`/`diaterm`, which recurse only when `xv.2` is box-typed) and
    `pair_elim` deferred. -/
mutual
theorem interpTerm_ctx_ext (M : GModel.{u} σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {S : VarType} (t : Term σ V S)
    (w : M.W) (env : Env M V w) (a : M.interp xv.2 w) :
    M.interpTerm (Term.ctx_ext xv hxv t) w (env.extend xv hxv a) = M.interpTerm t w env := by
  match t with
  | .var ⟨v, hv⟩ =>
      have hne : (⟨v, VarType.Var⟩ : VarSymb × VarType) ≠ xv := by
        rintro rfl; exact hxv (Finset.mem_image.mpr ⟨_, hv, rfl⟩)
      simp only [Term.ctx_ext, GModel.interpTerm, Env.extend, dif_neg hne]
  | .func f =>
      simp only [Term.ctx_ext, GModel.interpTerm]
      exact interpFunc_ctx_ext M xv hxv f w env a Fin.elim0
  | .unit => simp only [Term.ctx_ext, GModel.interpTerm]
  | .pair t1 t2 =>
      simp only [Term.ctx_ext, GModel.interpTerm]
      rw [interpTerm_ctx_ext M xv hxv t1 w env a, interpTerm_ctx_ext M xv hxv t2 w env a]
  | @Term.boxterm _ V_inner S_inner _ tt hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      cases xt with
      | Var =>
          simp only [Term.ctx_ext, GModel.interpTerm]
          congr 1
          funext w'
          congr 1
          exact boxPush_extend_notBox M hsub _ env a rfl w'
      | VTypeOne =>
          simp only [Term.ctx_ext, GModel.interpTerm]
          congr 1
          funext w'
          congr 1
          exact boxPush_extend_notBox M hsub _ env a rfl w'
      | VTypeDia U' =>
          simp only [Term.ctx_ext, GModel.interpTerm]
          congr 1
          funext w'
          congr 1
          exact boxPush_extend_notBox M hsub _ env a rfl w'
      | VTypeBox U' =>
          have hxv_inner : xs ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in_inner
            apply hxv
            obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
            cases q with
            | mk qv qT =>
              exact Finset.mem_image.mpr
                ⟨_, hsub (Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩), hq_eq⟩
          simp only [Term.ctx_ext, GModel.interpTerm]
          congr 1
          funext w'
          rw [boxPush_extend_box M hxv_inner hsub _ env a w']
          exact interpTerm_ctx_ext M ⟨xs, U'⟩ hxv_inner tt w'.1
            (Env.boxPush hsub env w') (M.necEval a w')
      | VTypeProd A B => sorry
  | @Term.diaterm _ V_inner S_inner _ xv_t hxv_t tt hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      have hwit : (⟨xv_t.1, xv_t.2.VTypeDia⟩ : VarSymb × VarType) ∈ V.1 :=
        hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)
      cases xt with
      | Var =>
          simp only [Term.ctx_ext, GModel.interpTerm]
          rw [Env.extend_apply_ne env a _ hwit,
              boxPush_extend_notBox M (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a rfl]
      | VTypeOne =>
          simp only [Term.ctx_ext, GModel.interpTerm]
          rw [Env.extend_apply_ne env a _ hwit,
              boxPush_extend_notBox M (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a rfl]
      | VTypeDia U' =>
          simp only [Term.ctx_ext, GModel.interpTerm]
          rw [Env.extend_apply_ne env a _ hwit,
              boxPush_extend_notBox M (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a rfl]
      | VTypeBox U' =>
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
          have hxv_ne : xs ≠ xv_t.1 := by
            intro h; apply hxv; rw [h]; exact Finset.mem_image.mpr ⟨_, hwit, rfl⟩
          have hxv_outer : xs ∉ VarCtx_to_VarSymbs (VarCtx_insert xv_t V_inner hxv_t) :=
            not_mem_VarSymbs_insert hxv_ne hxv_inner
          simp only [Term.ctx_ext, GModel.interpTerm]
          rw [Env.extend_apply_ne env a _ hwit]
          congr 1
          rw [boxPush_extend_box M hxv_inner (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a]
          rw [interpTerm_cast_term, Env.extend_comm,
              interpTerm_ctx_ext M ⟨xs, U'⟩ hxv_outer tt _ _ _]
      | VTypeProd A B => sorry
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => sorry

theorem interpFunc_ctx_ext (M : GModel.{u} σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {n : ℕ} (f : Func σ V n)
    (w : M.W) (env : Env M V w) (a : M.interp xv.2 w) (args : Fin n → M.D w) :
    M.interpFunc (Func.ctx_ext xv hxv f) w (env.extend xv hxv a) args
      = M.interpFunc f w env args := by
  match f with
  | .F hr => simp only [Func.ctx_ext, GModel.interpFunc]
  | .eval g t =>
      simp only [Func.ctx_ext, GModel.interpFunc]
      rw [interpTerm_ctx_ext M xv hxv t w env a]
      exact interpFunc_ctx_ext M xv hxv g w env a _
end

/-- Relation-level `ctx_ext` invariance (base for the `atom` case; via `interpTerm_ctx_ext`). -/
theorem interpRel_ctx_ext (M : GModel.{u} σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) {n : ℕ} (R : Rel σ V n)
    (w : M.W) (env : Env M V w) (a : M.interp xv.2 w) (args : Fin n → M.D w) :
    M.interpRel (Rel.ctx_ext xv hxv R) w (env.extend xv hxv a) args
      = M.interpRel R w env args := by
  induction R with
  | R hr => simp only [Rel.ctx_ext, GModel.interpRel]
  | eval R' t ih =>
      simp only [Rel.ctx_ext, GModel.interpRel]
      rw [interpTerm_ctx_ext M xv hxv t w env a]
      exact ih _

/-- Interpretation commutes with a context-equality cast (both `φ` and `env` transported). -/
theorem interpWFF_cast (M : GModel.{u} σ) {W1 W2 : VarCtx} (h : W1 = W2)
    (φ : WFF σ W1) (w : M.W) (env : Env M W1 w) :
    M.interpWFF (h ▸ φ) w (h ▸ env) = M.interpWFF φ w env := by
  subst h; rfl

/-- Cast on the formula alone: transport the environment the other way. -/
theorem interpWFF_cast_term (M : GModel.{u} σ) {W1 W2 : VarCtx} (h : W1 = W2)
    (φ : WFF σ W1) (w : M.W) (env : Env M W2 w) :
    M.interpWFF (h ▸ φ) w env = M.interpWFF φ w (h.symm ▸ env) := by
  subst h; rfl

/-- **α-rename invariance.**  Renaming the bound variable `old → new` interprets the same, with
    the environment relabelled accordingly.  (For the `all`/`ex` collision case of `ctx_ext`.) -/
theorem interpWFF_rename (M : GModel.{u} σ) {old new : VarSymb} {repl_type : VarType}
    {V W : VarCtx}
    (old_fresh : old ∉ VarCtx_to_VarSymbs V)
    (new_fresh : new ∉ VarCtx_to_VarSymbs V)
    (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
    (φ : WFF σ W) (new_not_bound : new ∉ WFF.boundVars φ)
    (w : M.W) (env : Env M V w) (val : M.interp repl_type w) :
    M.interpWFF (WFF.rename old new repl_type V W old_fresh new_fresh Wdef φ new_not_bound) w
        (env.extend ⟨new, repl_type⟩ new_fresh val)
      = M.interpWFF φ w (Wdef.symm ▸ env.extend ⟨old, repl_type⟩ old_fresh val) := by
  sorry

/-- **Context-extension invariance.**  A formula weakened by an unused variable interprets the
    same, in the environment extended by any value for that variable. -/
theorem interpWFF_ctx_ext (M : GModel.{u} σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (φ : WFF σ V) (w : M.W) (env : Env M V w)
    (a : M.interp xv.2 w) :
    M.interpWFF (WFF.ctx_ext xv hxv φ) w (env.extend xv hxv a) = M.interpWFF φ w env := by
  match φ with
  | .atom R =>
      simp only [WFF.ctx_ext, GModel.interpWFF]; exact interpRel_ctx_ext M xv hxv R w env a Fin.elim0
  | .top => simp only [WFF.ctx_ext, GModel.interpWFF]
  | .bot => simp only [WFF.ctx_ext, GModel.interpWFF]
  | .and φ ψ =>
      simp only [WFF.ctx_ext, GModel.interpWFF]
      rw [interpWFF_ctx_ext M xv hxv φ w env a, interpWFF_ctx_ext M xv hxv ψ w env a]
  | .or φ ψ =>
      simp only [WFF.ctx_ext, GModel.interpWFF]
      rw [interpWFF_ctx_ext M xv hxv φ w env a, interpWFF_ctx_ext M xv hxv ψ w env a]
  | .imp φ ψ =>
      simp only [WFF.ctx_ext, GModel.interpWFF]
      rw [interpWFF_ctx_ext M xv hxv φ w env a, interpWFF_ctx_ext M xv hxv ψ w env a]
  | .eq s t =>
      simp only [WFF.ctx_ext, GModel.interpWFF]
      rw [interpTerm_ctx_ext M xv hxv s w env a, interpTerm_ctx_ext M xv hxv t w env a]
  | @WFF.box _ V_inner _ ψ hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      cases xt with
      | Var =>
          simp only [WFF.ctx_ext, GModel.interpWFF, boxPush_extend_notBox M hsub _ env a rfl]
      | VTypeOne =>
          simp only [WFF.ctx_ext, GModel.interpWFF, boxPush_extend_notBox M hsub _ env a rfl]
      | VTypeDia U' =>
          simp only [WFF.ctx_ext, GModel.interpWFF, boxPush_extend_notBox M hsub _ env a rfl]
      | VTypeBox U' =>
          have hxv_inner : xs ∉ VarCtx_to_VarSymbs V_inner := by
            intro h_in_inner
            apply hxv
            obtain ⟨q, hq_in, hq_eq⟩ := Finset.mem_image.mp h_in_inner
            cases q with
            | mk qv qT =>
              exact Finset.mem_image.mpr
                ⟨_, hsub (Finset.mem_image.mpr ⟨⟨qv, qT⟩, hq_in, rfl⟩), hq_eq⟩
          simp only [WFF.ctx_ext, GModel.interpWFF]
          apply propext
          apply forall_congr'
          intro w'
          rw [boxPush_extend_box M hxv_inner hsub _ env a w']
          exact iff_of_eq (interpWFF_ctx_ext M ⟨xs, U'⟩ hxv_inner ψ w'.1
            (Env.boxPush hsub env w') (M.necEval a w'))
      | VTypeProd A B => sorry
  | @WFF.dia _ V_inner _ x_t hx_t ψ hsub hnbe =>
      obtain ⟨xs, xt⟩ := xv
      have hwit := hsub (by rw [VarCtx_dia_fst]; exact Finset.mem_insert_self _ _)
      cases xt with
      | Var =>
          simp only [WFF.ctx_ext, GModel.interpWFF]
          rw [Env.extend_apply_ne env a _ hwit,
            boxPush_extend_notBox M (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a rfl]
      | VTypeOne =>
          simp only [WFF.ctx_ext, GModel.interpWFF]
          rw [Env.extend_apply_ne env a _ hwit,
            boxPush_extend_notBox M (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a rfl]
      | VTypeDia U' =>
          simp only [WFF.ctx_ext, GModel.interpWFF]
          rw [Env.extend_apply_ne env a _ hwit,
            boxPush_extend_notBox M (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a rfl]
      | VTypeBox U' =>
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
          simp only [WFF.ctx_ext, GModel.interpWFF]
          rw [Env.extend_apply_ne env a _ hwit,
              boxPush_extend_box M hxv_inner (fun p hp => hsub (Finset.mem_insert_of_mem hp)) _ env a,
              interpWFF_cast_term, Env.extend_comm,
              interpWFF_ctx_ext M ⟨xs, U'⟩ hxv_outer ψ _ _ _]
      | VTypeProd A B => sorry
  | @WFF.all _ _ x hx ψ =>
      by_cases h_col : xv.1 = x.1
      · sorry
      · have hxv_x : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) :=
          not_mem_VarSymbs_insert h_col hxv
        simp only [WFF.ctx_ext, GModel.interpWFF, dif_neg h_col]
        apply propext
        apply forall_congr'
        intro val
        rw [interpWFF_cast_term, Env.extend_comm, interpWFF_ctx_ext M xv hxv_x ψ _ _ _]
  | @WFF.ex _ _ x hx ψ =>
      by_cases h_col : xv.1 = x.1
      · sorry
      · have hxv_x : xv.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) :=
          not_mem_VarSymbs_insert h_col hxv
        simp only [WFF.ctx_ext, GModel.interpWFF, dif_neg h_col]
        apply propext
        apply exists_congr
        intro val
        rw [interpWFF_cast_term, Env.extend_comm, interpWFF_ctx_ext M xv hxv_x ψ _ _ _]
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => sorry

/-- `Finset` corollary of `interpWFF_ctx_ext`: the extended hypothesis set is satisfied by the
    extended environment iff the original set is satisfied by the original. -/
theorem sat_ctx_ext_Finset (M : GModel.{u} σ) {V : VarCtx} (xv : VarSymb × VarType)
    (hxv : xv.1 ∉ VarCtx_to_VarSymbs V) (Γ : Finset (WFF σ V)) (w : M.W) (env : Env M V w)
    (a : M.interp xv.2 w) :
    (∀ ψ ∈ WFF.ctx_ext_Finset xv hxv Γ, M.interpWFF ψ w (env.extend xv hxv a))
      ↔ (∀ χ ∈ Γ, M.interpWFF χ w env) := by
  sorry

/-- **Soundness**: provability implies entailment.  By structural recursion on the derivation
    (which gives the induction hypothesis as a recursive call at the sub-derivation's context). -/
theorem soundness {V : VarCtx} {Γ : Finset (WFF σ V)} {φ : WFF σ V} :
    Proof σ V Γ φ → (Γ ⊨ φ)
  -- Structural
  | .ax hmem => fun _ _ env hΓ => hΓ _ hmem
  | .weak h => fun M w env hΓ => soundness h M w env (sat_of_union_left hΓ)
  | .weak_ctx _ _ _ => by sorry
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
  | .all_intro _ _ _ => by sorry
  | .all_elim _ _ _ _ => by sorry
  | .ex_intro _ _ _ _ => by sorry
  | .ex_elim _ _ _ _ => by sorry
  -- Equality
  | .eq_intro _ => fun _ _ _ _ => rfl
  | .eq_elim _ _ _ _ _ _ => by sorry
  -- Pairing
  | .pair_elim _ _ _ _ _ _ _ _ _ _ => by sorry
  -- Modal
  | .K_box hsub hnbe h => fun M w env hΓ w' =>
      soundness h M w'.1 (Env.boxPush hsub env w')
        (fun γ hγ => hΓ (WFF.box γ hsub hnbe) (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩) w')
  | .K_dia x hx hsub hnbe h => fun M w env hΓ => by
      simp only [GModel.interpWFF]
      refine soundness h M _ _ (fun χ hχ => ?_)
      rcases Finset.mem_union.mp hχ with hχΓ | hχψ
      · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hχΓ
        rw [interpWFF_ctx_ext M x hx γ]
        exact hΓ (WFF.box γ _ _)
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)) _
      · rw [Finset.mem_singleton] at hχψ
        subst hχψ
        exact hΓ (WFF.dia x hx _ hsub hnbe)
          (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  | .dia_bot _ _ _ _ h => fun M w env hΓ => soundness h M w env hΓ
  -- World-extensionality: sections/witnesses agree ⇒ the built `necIntro`/`posIntro`
  -- objects agree, by `congrArg` (funext for `□`).  No injectivity needed.
  | .box_ext _ _ _ _ h => fun M w env hΓ =>
      congrArg M.necIntro (funext (fun w' => soundness h M w env hΓ w'))
  | .dia_ext _ _ _ _ _ _ _ => by sorry

end GModel
