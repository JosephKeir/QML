# QML v12m: metatheory to do

Recorded 2026-09-16; items 4 and 5 added 2026-09-18; item 6 added 2026-09-18. These are general proof-theory jobs, not
modal-extension work. The agreed order is: finish the modal extensions (strong T, strong B, S5, D,
BF) and their completeness first, then the items here. Item 1 is close enough to done that it could
be taken at any time; items 4 and 5 are research questions rather than routine jobs.

**Two files (user, 2026-11-06).**  `QML_v12m_SemAdmissible.lean` holds rules shown admissible
**semantically**, through soundness and completeness across the cube (`provable_iff_validCube`):
quick, but only for the complete systems (not K5 or KD5), and they say nothing about the proofs.
`QML_v12m_ProofAdmissible.lean` holds **proof-theoretic** arguments, which hold for every flag
combination.  The semantic file is populated first; the proof-theoretic versions are item 7.

## 1. Strong completeness and compactness

**Status: ✅ DONE (2026-09-19)** — `QML_v12m_Compactness.lean`: `model_existence` (every
consistent set of formulas in a presented context is satisfiable), `strong_completeness` (a
semantic consequence of any set of premises is derivable from finitely many of them) and
`compactness` (a set is satisfiable if every finite subset is — the finite subsets' models may
live in any universe). All three hold for every combination of the flags, over a countable
signature; axioms `propext`, `Classical.choice`, `Quot.sound`. As predicted below, the completeness
proof went through with `S₀ := {⟨0, ψ⟩ | ψ ∈ S}`, and consistency is stated directly for sets
(`WFF.SetConsistent`: no finite list drawn from the set derives `⊥`) rather than through
`Theory.Derives`. The notes below are the plan as it was.

*Plan (to 2026-09-19):* **not stated, but the machinery is finitary and already supports it.**

What exists:
- `Theory.Derives S φ` = *some finite list* of members of `S` proves `φ`; `Theory.Consistent S` =
  `¬ Derives S ⊥`. So consistency of a set is already "every finite subset is consistent".
- `StageSys.Consistent T` = `Theory.Consistent` at every stage, and `World.ofHenkin` takes an
  arbitrary **set** of sentences with that property. Nothing in the Henkin construction wants a
  finite premise set.
- `completeness` / `provable_iff_valid` are stated for a `List` of hypotheses only.

What is missing (small):
- **Strong completeness.** For `S : Set (WFF σ Γ 0)` with `Γ` presented: if every model and
  environment satisfying `S` satisfies `φ`, then `Theory.Derives S φ`. The existing proof goes
  through verbatim with `S₀ := {⟨0, ψ⟩ | ψ ∈ S} ∪ {⟨0, φ.neg⟩}`: the consistency argument already
  extracts a finite list of hypotheses from a derivation, which is exactly what `Derives` wants.
- **Compactness.** Then a corollary: if every finite subset of `S` is satisfiable, so is `S`. (If
  `S` has no model then `S ⊨ ⊥`, so `Derives S ⊥`, so some finite subset proves `⊥`, which by
  soundness has no model.)
- Caveats carried over from `completeness`: countable signature, presented `Γ`, the
  `Γ.NoProjLast` side condition, and models in `Model.{0}`.

## 2. Generalisation on constants (`all_intro` by replacing a constant)

**Status: done for declared variables; open for constants (2026-11-06).**

*Done, for declared variables* — `QML_v12m_ProofAdmissible.lean` (proof-theoretic, every flag
combination): ⭐`Proof.genVar`, from `Δ ⊢ φ(c)` with `Δ` not mentioning the declared variable `c`,
`Δ ⊢ ∀x. φ(x)`, `c` declared anywhere at the top level and kept declared; ⭐`WFF.genV_inst`,
instantiating the bound formula at `c` gives `φ` back.  By `Proof.subst` (renaming `c` to the first
fresh name, `genS`) and `all_intro`.  (First built as "generalisation on constants"; the user
pointed out that a constant is a nullary function symbol, which is a different theorem.)

*Open, for constants (nullary function symbols).*  The user's statement: take `ψ(x)` with a declared
`x : □ᵏ Var` and a constant `f` occurring in neither `Δ` nor `ψ`, and promote `f` by `k` boxes so
the types match; from `Δ ⊢ ψ(□ᵏ f)` infer `Δ ⊢ ∀x. ψ(x)`.  All tokens of `f` are then at depth `k`.
* **It fails with T, 4 or strong B** (paper, 2026-11-06).  A function symbol is read per world, so
  `□ᵏ f`'s value at the end of a path depends only on the world the path ends at.  An arbitrary
  `x : □ᵏ Var` can depend on the whole path, and these systems can compare two paths to one world.
  With `x : □□Var`:
  * *T:* `ψ(x) := □(x.here.box = x.box.here)`.  The two sides read `x` along the paths
    `(1_w, a)` and `(a, 1_u)`, with different middle worlds.  T's laws only say how one object is
    read at the identity arrow; no composition is involved without 4.  Countermodel: `w R w`,
    `w R u`, `u R u`, `Var = {0, 1}`, full domains, `x` giving `0` along `(1_w, a)` and `1` along
    `(a, 1_u)`.  For `□□f` both sides are `f(u)`.
  * *4:* `ψ(x) := ∃n:□Var. □□(n.keep.box = x.box.box)`: `n := □f` for the constant; an `x`
    depending on the middle world has no such `n`.
  * *Strong B:* `ψ(x) := ∃y:Var. Back(x, y)`: `□□f` comes back as `f(w)` along every round trip;
    an arbitrary `x` need not.
  * *5* probably fails like 4 (side images carry contents between paths); not checked.
* **It should hold in K, D and weak B**, where nothing relates two paths to one world: no rule
  moves a symbol between depths, and weak B's closed rule cannot produce single-depth tokens.  A
  proof-theoretic argument: replace only the depth-`k` tokens of `f` in the proof by the matching
  address of a fresh `x`, leaving other depths as the promoted `f`, check rule by rule that nothing
  connects depth `k` with other depths, then bind `x` as `Proof.genVar` does.  The user has a
  proof-theoretic proof in mind for K.
* **Later (user, 2026-11-06):** look for a way to state "depends only on the end points", which
  would give the right type to generalise over in the other systems.  The language has no such type
  now; this is new design.

The notes below are the plan as it was.

**Goal.** A metatheorem: given a proof of `φ(c)` where `c` is a declared root of a fixed type,
replace every occurrence of `c` by a variable and conclude the universally quantified formula. The
point is to be able to take constants *out* of formulas, not only put them in (`all_elim`).

Notes before starting:
- Half of this may already exist. `Proof.subst` sends a proof along any substitution into a
  presented context, so renaming `c` to a fresh eigenvariable should be an instance of it, and
  `all_intro` then binds that eigenvariable (`WFF.bindFree`).
- **The declaration cannot be dropped.** There is no non-emptiness assumption on any domain, so
  declaring `c : T` proves `∃x:T. ⊤`. A proof in `Γ.insert (.free c) T` whose hypotheses and
  conclusion do not mention `c` therefore cannot in general be rebuilt in `Γ`: strengthening is
  *not* admissible. The conclusion has to keep the variable bound.
- So the statement to aim for is the "hypotheses do not mention `c`" version, matching the shape of
  `all_intro`, and the work is the induction that rewrites the proof.
- **The eigenvariable must have the same type as the constant**, and that is what keeps the
  renaming sound in modal positions. Roots are invisible inside `□` (`Ctx.boxIn` has only `u.box`
  and, under 4, `u.keep`), so a constant `c : Var` simply cannot occur under a modality: `□(y = c)`
  is not well-formed. A constant occurs under a modality only as an address built from its root —
  `c.box`, `c.here`, `c.keep`, or as the witness of `◇_c` with `c.dia` in its view — and each maps
  to the same address built from the eigenvariable. Renaming `c : □Var` to `x : □Var` sends
  `□(y = c.box)` to `□(y = x.box)`; renaming it to an `x : Var` does not typecheck.
- For a constant of `◇` type the annotation indices move too, since witnesses live in annotations.
  That is the map `ι` of `Subst.Coh`, which for a renaming is the same map on addresses. State this
  explicitly: it is where a careless version would go wrong.

## 3. Uniform substitution

**Status: done semantically for the cube (2026-11-07); proof-theoretic version is item 7.**
`QML_v12m_SemAdmissible.lean`: ⭐`usubstCube`, for every `[ModalSys.CubeSys]` system, from
`Δ ⊢ φ` infer `Δ[R := ψ] ⊢ φ[R := ψ]` (`WFF.usubst`), `ψ` a formula over the empty context with
one hole, the tuple of `R`'s arguments (`VarType.varTup`), so it uses only the atom's own indices,
as below.  The proof: `M.relSwap r ψ` is `M` with `R` read as `ψ`; ⭐`Model.sat_usubst` says it
satisfies `φ` exactly when `M` satisfies `φ[R := ψ]`, and it is a model proper when `M` is
(`indInvariant_relSwap`).  This needed `relInterp` moved from `Frame` to `Model`, so that the
swapped model keeps its frame (`Frame.Dom` is not definitional under a frame update).  Reading the
swapped model's operations as `M`'s needs smart unfolding off in those proofs: it won't unfold a
recursion stuck on a variable, so it never reaches the shared fields.

**Goal.** Replacing a relation symbol by a formula, uniformly through a proof: given `R` of arity
`n` and a formula `ψ` with `n` holes, every proof maps to a proof with each atom `R(t₁, …, tₙ)`
replaced by `ψ[t₁, …, tₙ]`.

Notes before starting:
- **The restriction the user flagged:** `ψ` may only use the indices that appear in the atom. In
  this system that means `ψ` lives over a context of just its `n` holes, with no other free
  addresses. Otherwise an occurrence of `R` inside `□` or `◇_x` would need addresses that are not
  reachable there.
- Given that, `ψ` can be instantiated at each occurrence's own context, and the induction should be
  routine. The cases worth checking first are the modal rules (`K_box`, `K_dia`, `T_box`,
  `four_box`, `T_dia`), since they move formulas between levels, and the equality rules, which
  instantiate a formula at a slot.

## 4. Cut elimination

**Status: ✅ CUT ELIMINATION FOR K, built (2026-11-07).**  ⭐`GK.provable_iff_der`
(`QML_v12m_GKToND.lean`): over a presented context, with every flag off (`ModalSys.IsK`), a sequent
is provable in natural deduction exactly when it has a **cut-free** GK derivation.  Sorry-free,
standard axioms.  About 2 200 lines in all (estimate was 4 500 to 7 000).
* `QML_v12m_GKEq.lean`: `ModalSys.IsK` (every flag off; instance for `ModalSys.K`); ⭐`GK.ident`
  (`φ ⇒ φ` for every formula, by weight, quantifiers opened with `openFree`); ⭐`GK.replace` (ND's
  `eq_elim` for any formula) from `GK.replaceGen`, stated for two substitutions agreeing except at
  the slot `bnd 0` (sent to `t` and `s`, one index map since a base term carries no indices):
  quantifiers by `bindFree_toFree`/`instantiate_toFree`, the `□`/`◇_x` views by
  `Subst.sim_box_of_agree`/`sim_dia_of_agree` (both sides the same formula), atoms by the hole
  formula `θ₁.under 0 0` (`instantiate_hole`, `Subst.coh_under_occ`); `GK.eq_symm`.
* `QML_v12m_GKFromND.lean`: `GK.Der` (single-conclusion derivability); every ND rule of K derived
  (`Der.and_elim_l`, `Der.K_dia` by `negRight`/`dropNeg`, …); ⭐`GK.ofProof`, the translation along
  any substitution into a presented context (as `Proof.subst`: `weak_ctx`, `pair_elim` have
  premises over contexts that need not be presented, and there they become a restriction and
  `θ.pairSplit`); non-K rules by their flags (`kflag`); ⭐`GK.Der.ofProof`.
* `QML_v12m_GKToND.lean`: ⭐`GK.toND` (`Δ ⇒ Θ` read as `Δ, ¬Θ ⊢ ⊥`, every system), `NDP` helpers,
  ⭐`GK.provable_iff_der`.
* **Subformula property, built (2026-11-07)**, `QML_v12m_GKSubform.lean`: ⭐`GK.subformula`, a
  cut-free derivation whose end sequent lies in `GSub E` has every sequent there (`GKS`, GK's rules
  with each conclusion in a family); ⭐`GK.subformula_of_provable`, every ND-provable sequent of K
  has such an analytic derivation.  `GSub E` is Gentzen's notion for predicate logic: the least
  family containing `E`, closed under immediate subformulas (the bodies of `□`/`◇_x` read in their
  views), a quantifier's body instantiated at any term or opened at an eigenvariable, weakening by a
  fresh variable, a `□` body moved into a `◇_x` view, and atoms (`ref`/`repl` introduce them, as in
  Negri and von Plato).  `GSub.weight_le`: every member is an atom or no heavier than a formula of
  `E`.  *Not done:* the sharper form "a single substitution instance of a syntactic subformula"
  (needs composing substitutions, for which the codebase has no `Ok`/`Coh` lemmas), and
  restricting the atoms to those built from the end sequent's terms.
* *Next:* interpolation (item 5).

*Earlier status:* cut admissible in GK, built (2026-11-07).
* `QML_v12m_GK.lean`: the calculus `GK σ n Γ Δ Θ` (a `Prop`, indexed by a height bound), `WFF.IsAtom`,
  `WFF.weight`; `GK.mono_height`; `GK.weaken` (weakening, exchange and contraction, by membership).
* `QML_v12m_GKSubst.lean`: ⭐`GK.subst`, height-preserving substitution into a presented context,
  each rule to itself by `Proof.subst`'s formula lemmas; `GK.monoCtx`.
* `QML_v12m_GKCut.lean`: ⭐`GK.cut` (and `GK.cut'` with separate contexts), over any presented
  context; `WFF.weight_subst`/`_instantiate`/`_mono`; `GK.instEigenR`/`instEigenL` (eigenvariable
  to term); `GK.LeftPrin` (the cut formula principal on the right, indexed by the formula so a case
  analysis keeps the matching rules) and `GK.permRight`; `GK.cut_step`, `GK.cutIH_all` (weight,
  then the sum of heights).  Sorry-free, standard axioms.  About 1 100 lines in all.
* GK is stated for any `[ModalSys]`: the formers K lacks have no rules, so they act as opaque
  formulas; the K restriction enters only in the equivalence with ND.
* *Next:* ND → GK + cut (left rules from eliminations; `eq_elim` over any formula by induction on
  it, the modal cases trivial; `K_dia`, `dia_bot`, `lem`, `weak_ctx` by `monoCtx`, `pair_elim` by
  `GK.subst` with `θ.pairSplit`), and GK → ND (semantically or by derived rules); then the
  subformula property and interpolation.

*The scope as agreed:*  The user's
aim: the subformula property and, from it, interpolation.  K only for now: the user is much less
confident for the other systems (the literature agrees for B and 5; T, D and 4 usually have
cut-free G3 calculi).  Of interest because cut elimination usually fails for QML.

### The calculus GK (agreed with the user)

Classical, two-sided, multi-succedent, G3-style; `◇` and `□_x` are notation (`¬□¬`, `¬◇_x¬`), as in
the paper.
* **Connectives and quantifiers:** G3c.  `∀R`/`∃L` with a fresh eigenvariable of any type;
  `∀L`/`∃R` at a term of any type, `□`- and `◇`-terms included.
* **Equality (user's decision):** Negri–von Plato's `Ref` and `Repl` on **atoms only**, at base
  type.  ND's `eq_elim` over an arbitrary `φ` is a corollary: `t = s, φ(t) ⇒ φ(s)` is cut-free
  derivable by induction on `φ`, with trivial modal cases (a `Var` slot is invisible in the `□` and
  `◇_x` views).  The general rule as primitive would need a right-replacement lemma and a second
  same-size cut against a derivation of unbounded height in the reduction where the cut formula is
  used by `Repl`; atoms are never principal in a logical right rule, so cuts on them go up the left
  derivation to an axiom.  Equivalent, awkward for writing proofs, but proofs are not the point.
* **Modal rules (the user's, symmetric):**
  * from `Δ ⇒ φ, Θ` infer `□Δ ⇒ □φ, ◇Θ`, all variables promoted to necessary ones (the premise in
    the `□` view);
  * from `x : E; Δ, φ ⇒ Θ` infer `x : ◇E; □Δ, ◇_x φ ⇒ ◇_x Θ`, every variable but `x` promoted (the
    premise in the `◇_x` view, `x : E` its content).
  With `◇` defined these are derivable from the one-sided forms `□R` (from `Δ ⇒ φ` in the `□` view,
  `□Δ ⇒ □φ`) and `◇_xL` (from `ψ, Δ ⇒ Θ` in the `◇_x` view, `◇_x ψ, □Δ ⇒ ◇_x Θ`) by `¬L`/`¬R`, and
  back.  If `◇` were primitive, the `◇_x` rule would also need `◇Θ'` on the right (`◇_x φ ⇒ ◇φ`
  is valid, extents lie inside the accessible worlds); with `◇` notation it is derivable.  Not to
  be added: `◇_x` on the right of the `□` rule (`□Δ ⇒ □φ, ◇_x χ` is invalid: the extent may be
  empty).  ND's `K_dia` (`□_x Δ₂` on the left is `◇_x ¬Δ₂` on the right) and `dia_bot` (`Θ` empty)
  are instances.
* **Not primitive:** `pair_elim` (a substitution, as `Proof.subst` already treats it:
  `θ.pairSplit`) and `weak_ctx` (`mono`).

### Why QML usually fails, and why K here may not

1. *Barcan / constant domains*, the usual failure: a world-level object is invisible under `□`, so
   the Barcan formula can only be stated with necessary objects, `∀x:□Var. □φ(x.box) → □∀y φ(y)`,
   which is not valid (comprehension, kept apart from the cube).
2. *Identity under modalities:* replacement never passes into a modal context (item above).
   Equality at `□`/`◇` types is the defined `eqRec`, contents under one modality and one witness.
3. *Terms of modal type:* instantiation is a term substitution (`◇_z χ` at `z := diatm x bd` is
   `◇_x χ[bd]`), so it preserves the **weight** (connective count), which the induction needs.

### The reductions, checked on paper

Lean-friendly form: **Kleene's G3 with principal formulas retained** and membership-based contexts
(`φ ∧ ψ ∈ Δ` and `φ :: ψ :: Δ ⇒ Θ` give `Δ ⇒ Θ`).  Weakening, exchange and contraction are then
free, and cut elimination needs **no inversion or contraction lemmas**: in a principal case one
first cuts the original formula against the premises (smaller height), then the components
(smaller weight).  Induction on (weight of the cut formula, sum of heights).
* **∀ (and ∃) principal:** cut the `∀R` conclusion against the `∀L` premise (smaller height) to get
  `φ[t], Δ ⇒ Θ`; substitute `u := t` in the `∀R` premise (height-preserving substitution) to get
  `Δ ⇒ Θ, φ[t]`; cut on `φ[t]` (smaller weight).  For `u : ◇A`, `t := diatm y bd`, a `◇_uL`
  instance becomes a `◇_yL` instance in `Γ.diaIn y` with `u.dia ↦ bd`; for `u : □A`, `t := boxtm s`,
  `u.box ↦ s` in the `□` view.  Exactly what `Proof.subst`'s `K_box`/`K_dia` cases do.
* **`□φ` principal on both sides:** right rule `□R`: cut on `φ` in the `□` view, then `□R`.  Right
  rule `◇_xL` with `□φ` among its `□Δ`: move the left premise from `Γ.boxIn` to `Γ.diaIn x`
  (`mono` along `Ctx.le_boxIn_diaIn`), cut on `φ` there, then `◇_xL`.
* **`◇_x φ` principal on both sides:** the right rule is `◇_xL` with the same `x` (formula equality
  forces it); cut on `φ` in the `◇_x` view, then `◇_xL`.  Different witnesses never meet.
* **Cut formula in a modal rule's weakening context:** the cut vanishes (conclusion contexts are
  arbitrary); otherwise permute upward (`∀R`/`∃L` need `mono` into the eigenvariable's context).
* **Atoms:** go up the left derivation (an atom on the right is principal only in an axiom); at an
  axiom `P ∈ Δ`, so the conclusion is the right derivation weakened.  `Repl` and `Ref` permute.
No case found that fails.

### Plan and cost

* `GK` (an inductive with the K formers; `here`/`back`/`ret`/`link` are uninhabited under
  `ModalSys.K`), weight, height: 400 lines.
* Height-preserving weakening (easy, membership-based) and **substitution**: reuse the formula-level
  lemmas of `ProofSubst` (`subst_instantiate`, `subst_bindFree`, the view substitutions
  `θ.box`/`θ.dia`); only the ~15 rule cases are new.  `mono` and `pair_elim` as instances.
  800 to 1 500 lines.
* Cut admissibility: 1 500 to 2 500 lines.
* ND → GK + cut (general replacement by induction on `φ`, `K_dia`, `lem`, ...): 800 to 1 200.
  GK → ND: semantically (each rule preserves validity, then `provable_iff_validCube` at K) or
  syntactically; 500 to 1 000.
* Total about 4 500 to 7 000 lines.  Then the subformula property (up to term instances) and
  interpolation (item 5).

*The notes before scoping:*

**Goal.** A sequent calculus equivalent to the natural-deduction system, with cut admissible.

Notes before starting:
- The user already has a picture of the appropriate sequent calculus. The ND system is close to a
  sequent system already — `Proof σ Γ Δ φ` carries an explicit hypothesis list, and the structural
  rules (`weak`, `contr`, `exch`) are explicit — so the equivalence proof should be comparatively
  direct: left rules from the elimination rules via `cut` (which is `Proof.cut`, derived from
  `imp_intro`/`imp_elim`), right rules from the introduction rules.
- Scope is genuinely open. It may hold only for K. The extensions add rules that move formulas
  between levels (`T_box` collapses, `four_box` shifts, `T_dia` introduces an eigenvariable with
  view hypotheses), and each needs a cut-reduction case. Known background: cut-free sequent calculi
  for propositional K, T and S4 are standard; S5 notoriously needs a richer structure (hypersequents,
  labelled or nested sequents). How the address/view machinery changes this is part of the question.
- Equality needs care: `eq_elim` rewrites under an arbitrary formula context, which is the usual
  obstacle to cut elimination with identity.

## 5. Craig interpolation

**Goal.** If `φ ⊢ ψ`, there is `θ` using only the non-logical symbols common to `φ` and `ψ` with
`φ ⊢ θ` and `θ ⊢ ψ`.

Notes before starting:
- **Why it would be interesting.** Interpolation holds for the standard *propositional* normal modal
  logics (K, T, S4, S5), but fails for many *quantified* ones: Fine (1979) showed first-order S5 with
  constant domains lacks it, and the failure recurs across quantified modal logics. The usual culprit
  is that the classical interpolant would have to quantify over something the object language cannot
  express. This system makes more of that expressible — possible objects are first-class, witnesses
  are named in `◇_x`, and quantifiers range over modal types — so it is a reasonable hope that
  interpolation holds here where it fails classically. A positive result would be a good selling
  point; a failure would be informative about where the extra expressiveness stops.
- The standard route is via cut elimination (Maehara's method on a cut-free sequent calculus), so
  item 4 is likely a prerequisite. A semantic route through the canonical model (amalgamation or a
  Robinson-consistency argument) is the alternative if cut elimination only holds for K.
- Decide early what "common language" means: relation and function symbols only, or also the
  witness addresses and modal types occurring in the formulas.

## 6. Strong T: `T_dia∀` is equivalent to the positive-Φ rule

**Status: set aside (user, 2026-11-07).**  The point was to show that an unnatural-looking rule,
`T_dia∀` with its list of parameterised hypotheses, is equivalent to a natural one.  `T_dia∀` is
no longer the rule: `Proof.T_dia` hands over the single atom `Here(c, t)`, and `here_intro` /
`here_elim` read it, which is natural in itself (and gives every `T_dia∀` hypothesis by
`here_intro`, `imp_intro` and `all_intro`).  If it is ever revived, the question is the current
atom rule against the positive-Φ rule, and `Φ⟨x := t⟩` says nothing about a `Here(x, t)` atom, so
first decide whether the paper rule stands in for `T_dia` alone (with `here_intro`/`here_elim`
kept) or for all three.  The notes below are the plan as it was.

**Goal.** Prove in Lean that the implemented rule `T_dia∀` and the rule the paper will state are
interderivable (added 2026-09-18, after completeness for strong T):

  from `Γ;Δ ⊢ Φ⟨x := t⟩` and `Γ, c:◇A ; Φ(c), Δ ⊢ φ` infer `Γ;Δ ⊢ φ`,

with `c` fresh for `Γ, Δ, φ` and `Φ` positive in `x`. It reads as ∃-elimination generalised to a
witness that no term can name.

Notes before starting:
- Paper sketch in `docs/v12-modal-extensions.md` (strong T, "Equivalence with the
  positive-polarity schema"): monotonicity `Φ⟨x:=t⟩ → Φ(c)` by induction on positive `Φ`, from
  `T_dia∀` hypotheses, one per `◇_x` atom, with the variables bound above the atom as parameter
  (a product if several); conversely `Φ(x) := ∀y. (ψ↓(t,y) → ◇_x ψ↑(y))` makes the first premise
  trivial.
- New syntax needed: the substitution `Φ⟨x := t⟩` (each atom `◇_x χ` becomes `χ↓(t)`, i.e.
  `hereRead`), and a positivity predicate on formulas. Slot renumbering under the binders above an
  atom is where the effort goes.
- Positivity is necessary, not a convenience: with `Φ(x) = ¬◇_x ψ` the rule would yield `□_c ¬ψ`
  from `¬ψ↓`, which fails when the extent of `c` holds more than the realised object.
- Why ordinary ∃-elimination needs no such generalisation: its premise `∃x.ψ(x)` already allows any
  `ψ`, quantifiers included, and `Φ(t) ⊢ ∃x.Φ(x)` is plain ∃-introduction because `t` is itself a
  value for `x`. Here `t : A` is not a value of `◇A`, so the witness is manufactured, and it is
  pinned down only one way (it realises `t`, but may not be the only object there).
- A bare `◇_c ψ↑` hypothesis (no quantifiers around it) is equivalent only to the unparameterised
  `T_dia` (`∀y ∃c`), not to `T_dia∀` (`∃c ∀y`).

## 7. Proof-theoretic versions of the semantic corollaries *(added 2026-11-06)*

Also: **generalisation on constants** for K, D and weak B, and the "depends only on the end points" type for the other systems (item 2's notes).

**Status: to do.**  Each holds semantically in every cube system (`QML_v12m_SemAdmissible`:
`leibnizCube` and `usubstCube`, done 2026-11-07); the
proof-theoretic version would hold for every flag combination, K5 and KD5 included, and is the
proof theory proper.  Go into `QML_v12m_ProofAdmissible.lean`.

- **Leibniz at every type.**  From `eqRec T t s` and `φ[t]`, `φ[s]`.  The K-only system has it
  (`QML_v12_LeibnizMain.lean`: `Proof.substEq`, `Proof.leibniz`, by provably equal substitutions,
  `SubE.EqE`); `QML_v12m_Leibniz*` hold the generalised infrastructure but not the theorem.  What
  stopped the port (`QML_v12m_LeibnizSpine`'s note): under T the `here` component of a necessary
  entry needs the equality read at the current world, which T proves but which is not among the
  hypotheses, so the bookkeeping must carry those collapsed equalities too.  Then the formers K
  lacks: `keep` (4), `here` (T), the links (5), `Back` and the returning possibility (strong B).
  An induction over formulas, not proofs.  Estimate 2 000 to 4 000 lines.
- **Uniform substitution.**  Every atom `R(t̄)` replaced by `ψ(t̄)`, `ψ` closed apart from the tuple
  of arguments (`WFF.usubst`, defined in the semantic file).  An induction over all the proof
  rules, each needing the substitution to commute with the rule's operations (`mono`, `subst`,
  `instantiate`, `bindFree`, `collapse`, `shift`, `holeAt`, `bodyRepl`, the closed formulas of U
  and `five_reflL`).  Sized like `Proof.subst`: 3 000 to 5 000 lines.
- *Done proof-theoretically already:* **generalisation on declared variables** (item 2,
  `Proof.genVar`, `WFF.genV_inst`, for declared variables).
