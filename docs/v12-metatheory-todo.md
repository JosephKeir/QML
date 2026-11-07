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

**Status: ✅ CUT ELIMINATION FOR K, KD, K4 AND KD4, built (2026-11-07; K first, then KD and K4
by extending GK, see "K4 and KD built" below).**  ⭐`GK.provable_iff_der`
(`QML_v12m_GKToND.lean`): over a presented context, with weak D and weak 4 either way and every
other flag off (`ModalSys.GKSys`; it replaced `ModalSys.IsK`), a sequent
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
  `E`.
* **Both sharpenings, built (2026-11-07).**  (1) `GSub`'s atoms are only those `ref` and `repl`
  introduce: `t = t`, and `P(s)` from members `t = s` and `P(t)`.  (2) `QML_v12m_GKSubSharp.lean`:
  ⭐`GK.subformula_sharp_of_provable`, every ND-provable sequent of K has a cut-free derivation in
  which every formula is a **single substitution instance of a syntactic subformula** of the end
  sequent (`WFF.SubF`, `SharpSub.inst`) or such an atom; ⭐`GSub.sharp` (`GSub ⊆ SharpSub`).  No
  composition of substitutions was needed: instantiating after `θ.under` is substituting along
  `θ.set (bnd d) t` (`WFF.instantiate_subst_under`, from the existing `Subst.set`); opening at an
  eigenvariable is `θ.toFree` (`bindFree_toFree`, `openFree_bindFree`, which moved from
  `BBackTruth` to `QML_v12m_Open`); weakening is `WFF.mono_subst`/`WFF.mono_instantiate`.
  *Not done:* Negri–von Plato's subterm property (`ref` only at terms of the end sequent); the
  quantifier rules instantiate at arbitrary terms anyway.
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

### Other systems: priorities and the K4 paper check (2026-11-07)

*The user's priority:* systems people care about, some version of 4 or T; cut elimination is not
expected everywhere (it fails for some propositional systems already).  Assessment:
* **KD** (weak D): one more modal rule, from `Δ₁ ⇒` (empty) in the `□` view infer `□Δ₁ ⇒`,
  equivalent to `D_box`; one new principal case.  Cheap.
* **K4** (weak 4): paper check below, passes.
* **KT** (weak T): `T_box` alone is standard (a left rule adding the collapsed body; collapse is a
  substitution, `WFF.collapse_subst`).  But the T flag brings `Here` with six rules: `here_intro`
  becomes one right rule for `◇_x` (`here_elim` follows from it classically), whose reduction against
  `◇_xL` reads a view derivation at the current world (by substitution); `here_beta` and `here_name`
  look like Negri's geometric rules (atoms; an eigenvariable); `here_subst` and `here_eq` are
  replacement over arbitrary formulas, the likeliest place for a failure.  Needs its own paper check.
* **S4**: later (`here_keep`, views exposing only `keep`).

**K4 paper check (weak 4: K plus `four_box`, `four_dia`; `keep_lift` needs the strong flags,
`five_refl` needs 5).**  Under 4 the `□` view also has `u.keep : □A` and `x.keep : ◇X`, and
`shift` (`u.box ↦ u.keep.box`, `u.keep ↦ u.keep.keep`, `x.dia ↦ x.keep.dia`) carries a view one
level further in; it is a renaming substitution (`WFF.subst_shift`), so `GK.subst` shifts
derivations.
* **Rules.**  `□R⁴`: from `Δ₁, □(shift Δ₁) ⇒ φ, ◇_{y.keep}(shift Θ_y)` in the `□` view, infer
  `□Δ₁ ⇒ □φ, ◇_y Θ_y` (for any witnesses `y`).  `◇_xL⁴`: from `ψ, Δ₁↑, □(shift Δ₁)↑ ⇒ Θ_x,
  ◇_{y.keep}(shift Θ_y)↑` in the `◇_x` view, infer `◇_x ψ, □Δ₁ ⇒ ◇_x Θ_x, ◇_y Θ_y` (`y = x`
  allowed: then both `Θ_x` and `◇_{x.keep}(shift Θ_x)`).  New against textbook K4: the
  right-hand `◇_y` part — invalid in K (an extent may be empty), valid with 4 through `y.keep`,
  whose extent lies inside `y`'s.  Sound by transitivity and restriction.
* **ND into GK4.**  `four_box`: `□R⁴` with `L_Δ = [□φ]`, premise `φ, □shift φ ⇒ □shift φ`.
  `four_dia` (`□_x φ ⊢ □□_{x.keep}(shift φ)`): `□_x φ` on the left is `◇_x ¬φ` on the right, so
  `□R⁴` with `L_Θ = [◇_x ¬φ]` and premise `⇒ □_{x.keep}(shift φ), ◇_{x.keep}(shift ¬φ)`, an
  identity.  **GK4 into ND**: `□R⁴` from `K_box` with `four_box`, `four_dia`.
* **Cut, principal cases**, by the standard K4 argument: the cut formula's own 4-copy (`□(shift φ)`,
  `◇_{x.keep}(shift θ)`) appears in a premise, at the same weight; it is cut against **the other
  side's conclusion re-derived inside the view**, by shifting that side's premise (`GK.subst`) and
  applying the 4-rule one level in; that re-derivation's height is the other side's, the premise's
  smaller, so the induction on height applies; the components are cut at smaller weight.
  - `□R⁴` against `□R⁴` (`□φ` among the boxed hypotheses): cut `□shift φ`, then `φ`.
  - `□R⁴` against `◇_xL⁴`: the same, moved into the `◇_x` view (`monoCtx`).
  - `◇_x θ` from a 4-part (`□R⁴`'s `Θ_x`, or `◇_yL⁴`'s) against `◇_xL⁴`: cut `◇_{x.keep}(shift θ)`
    against the right conclusion shifted into the view (the `◇_x` view shifts into the
    `◇_{x.keep}` view, `Ctx.shifts_diaIn_keep`); with `y = x`, also `θ` itself.
  - Non-principal: the modal rules keep no context, so the cut vanishes.
  No case found that fails.
* **Lemmas needed:** shift commutes with itself where the 4-copy is re-shifted
  (`shift₁ ∘ shift₀ = shift₀ ∘ shift₀` on the reachable addresses: checked on `u.box`, `u.keep`);
  the inclusion of the shifted `□` view into the `◇_x` view's `□` view; weight kept by shift.
* **Design question:** extend GK with flag-gated 4-rules (K the special case; every GK proof gains
  two cases) or a separate calculus.  Estimate 2 000 to 3 000 lines; interpolation for K4 afterwards
  (Maehara is known to work for propositional K4).

### K4 and KD built (2026-11-07)

Decided: **GK extended**, flag-gated (the copies `cp4`, `kp4` are empty without 4; `serial` needs
`D`).  About 1 300 lines added; sorry-free.
* `QML_v12m_GK.lean`: `cp4`, `kp4` (`WFF.keepDia`); `boxR` and `diaL` with the copies and a list `L`
  of conclusions whose `◇` copies the premise gets; `serial` (D).
* `QML_v12m_GKShift.lean`: `Ctx.Leveled` (every declared address `L r` levels below its root;
  presented contexts are leveled, `Ctx.Presented.leveled`), `Subst.coh_atShiftL`, ⭐`GK.shiftD`
  (shifting a derivation one view in, height kept, by `GK.subst`), `WFF.shift_mono`,
  `WFF.weight_shift`, `shift_cp4`/`shift_kp4` (from `WFF.shift_shift_same`).
* `QML_v12m_GKCut.lean`: `GK.Into` (the `□` view itself or a `◇_x` view), ⭐`GK.boxCut` (`□φ`
  principal: cut its copy `□(shift φ)` against the left conclusion re-derived in the view, then
  `φ`), ⭐`GK.copyCut` (a `◇_y θ`'s copy cut against the right conclusion re-derived in the view,
  `diaL` at `y.keep`), `boxPrin`, `diaPrin*`, `left*`; `permRight` with the new rules.  The paper
  check held exactly: no case failed.
* Equivalence: `GKSys` with instances for `ModalSys.K`, `KD`, `K4`, `KD4` (new presets);
  `Der.D_box`, `Der.four_box`, `Der.four_dia`; `keep_lift` excluded since no type is liftable
  (`ModalSys.GKSys.liftableR`); `NDP.box_neg_keep` and `NDP.boxes_ok` for `toND`.
* **Subformula property** for all four (`GSub.box_keep`, `GSub.dia_keep`: the copies;
  `GSub.view_dia`).  **Sharp form for all four** (`GK.subformula_sharp_of_provable`): every formula
  is a single substitution instance of a **subformula up to copies** (`WFF.SubC`: syntactic
  subformulas, closed under subformulas and the two keep-shifts; without 4 exactly the syntactic
  ones, `WFF.SubC.subF`).  The copy of an instance `θ(□χ)` is the instance `θ.box` of `□(shift χ)`
  (`WFF.shift_subst` with `Subst.shiftCorr_box_box`; `shiftCorr_dia_keep` for `◇`).
* **Craig interpolation** for all four (`GK.craig`): the copies split with their originals and keep
  their relation symbols (`WFF.occ_shift`); `serial` has interpolant `◇χ'` with `□R` on its right.
* `QML_v12m_GKEq.lean`'s `hole` renamed `holeF` (clash with `LeibnizSpine.hole` through the new
  imports).
* Next candidates: KT (paper check of the `Here` rules first); S4; S5 (see below).

### KT paper check (2026-11-07)

Weak T: `T = true`, `TStrong = false` (so no `T_dia`); 4, B, 5 off.  The T rules are `T_box` and the
six `Here` rules (`here_elim`, `here_intro`, `here_beta`, `here_name`, `here_subst`, `here_eq`);
`Here` atoms have weight 0.  Proposed GKT = GK plus:
* **TL** (`T_box`): `□φ ∈ Δ`; premise `collapse φ, Δ ⇒ Θ`.  Principal cut against `□R`: cut `□φ`
  into TL's premise (height), then `collapse φ` (lighter) against the `□R` premise **collapsed**
  (collapse is a substitution: a `GK.shiftD`-style `collapseD`), whose hypotheses
  `collapse Δ₁` come back by TL from `□Δ₁`.  Standard (Ohnishi–Matsumoto's G3 for KT).  **Fine.**
* **◇R_T** (`here_intro`): `Here(⟨x;bd⟩, t) ∈ Δ`, `◇_x(viewReadTm bd ψ) ∈ Θ`; premise
  `Δ ⇒ hereRead t ψ, Θ`.  `here_elim` is derivable from it classically (`□_x = ¬◇_x¬`, and both
  readings commute with `¬`).  Principal cut against `◇_xL`: the `◇_x` view's derivation must be
  read at this world.  `here_name` gives a content `c` of `x` here only existentially, so the
  reduction takes `c` as an eigenvariable, reads the view derivation at `x.dia := c`,
  `u.box := u.here` (a substitution), and matches `bd[c]` with `t` by `here_beta` and functionality.
  **Fine if functionality (below) is.**
* **HB** (`here_beta`) and **HN** (`here_name`): Negri-style geometric rules (atoms in, atoms out;
  HN with an eigenvariable, its conclusion being `∃c. Here(…, c)`).  `Here` atoms are never
  introduced on the right except in axioms, so, like `repl`, they need no reductions of their own.
  **Fine.**
* **HS** (`here_subst`, functionality) and **HE** (`here_eq`): replacement.  K's `repl` is atomic
  because a base-type slot is invisible in every view, so `GK.replaceGen` passes views untouched.
  A content of any type can be visible in views, so atomising needs more:
  - *Contents without `◇` (`Var`, `𝟙`, products, `□`):* two contents of one subject are equal
    (`here_fun` is an instance of `here_subst`), so HS reduces to replacement along `eqRec`, and
    Leibniz along `eqRec` at every type is admissible by induction on the formula, carrying
    `eqRec A t.unbox t'.unbox` into `□` views (the equality at `□A` is itself `□(…)`).  The atomic
    case at a `Here` atom is HE.  HE's side formula `eqRec A t t'` is not atomic at compound `A`; at
    `□A` it can be made a **modal rule** (`Here(s, box u), □Δ₁ ⇒ …` with a `□`-view premise
    `Δ₁ ⇒ eqRec u u'`), whose cuts are those of `□R` against a boxed hypothesis; at `◇X` (one
    witness, `eqRec = □_x(…)`) a `◇_x`-view premise.  **Plausible; to check.**
  - ⚠️**Contents with `◇`: HS is not atomisable.**  Two contents `⟨y;b⟩`, `⟨y';b'⟩` of one subject
    may stand over different witnesses, and HS at the formula `◇_{hole} χ` transfers `◇_y χ(b)` to
    `◇_{y'} χ(b')`: a cross-fibre identification, which by design (§10.3, §10.10, the decision of
    2026-10-01) has no formula, only the rule schema.  For cut elimination a non-atomic side formula
    `φ(t)` of HS needs right-replacement to be height-preserving admissible (from `Δ ⇒ φ(t), Θ` and
    the two `Here` atoms, `Δ ⇒ φ(t'), Θ`), proved by induction on the derivation; the induction
    fails exactly where `◇_y χ(b)` is introduced by `◇_yL`, whose premise lives in the `◇_y` view and
    cannot be moved to the `◇_{y'}` view (no term map between the fibres).  Treating HS as a
    general rule in both polarities does not help: the cut on `φ(t')` then has the same weight and no
    smaller height.  It is not derivable from the other `Here` rules either (functionality is why it
    is primitive: `here_intro`/`here_elim` relate the content to `◇_z`/`□_z` of the subject's
    witness, not to *this* world as a point of the extent).
* **Verdict:** KT's cut elimination goes through on paper **except at `here_subst` for contents
  containing `◇`**, where the calculus meets the cross-fibre gap the semantics settled by a model law
  (`Ind`).  Options: (a) a structural way for a sequent to say "this world, as a point of `z`'s
  extent" (hybrid-like, a label), so that two `Here`-linked contents can be compared in one view;
  (b) reformulate functionality so its cross-fibre content is carried by the subject's view rather
  than by a schema over formulas; (c) a counterexample search: a cut-free-underivable instance would
  show KT, as ruled, has no cut elimination.  Restricting `Here` to `◇`-free contents is the kind of
  restriction the user has rejected before (memory: "no ◇-free restrictions").  **Decision needed.**

**Option (c) tried (2026-11-07): a counterexample.**  `s : ◇◇Var`, `y, y' : ◇Var`, unary function
symbols `f`, `h`, unary relations `P, Q, R`; `t = ⟨y; f(y.dia)⟩`, `t' = ⟨y'; h(y'.dia)⟩`.
  `S :  Here(s,t), Here(s,t'), ◇_y P(y.dia), □_y(P(y.dia) → Q(f(y.dia))),
        □_{y'}(Q(h(y'.dia)) → R(y'.dia))  ⇒  ◇_{y'} R(y'.dia)`
* *ND-provable, with a cut:* K gives `◇_y Q(f(y.dia))`; `here_subst` at `φ(z) = ◇_z Q(z.dia)` moves it
  to `◇_{y'} Q(h(y'.dia))`; K with the `□_{y'}` hypothesis gives the goal.
* *No cut-free GKT derivation, even with `here_subst` in both polarities:* the goal needs a `◇_{y'}`
  formula on the left (`◇_{y'}L`) or a `Here` atom whose subject is over `y'` (`◇R_T`).  The `Here`
  rules only produce subjects over `s`'s witness; `here_subst` produces `◇_{y'}` formulas only from
  formulas `φ(t)` whose dependence on `y`'s content goes through `f(y.dia)` alone, and none is in the
  sequent (`◇_y P(y.dia)`, `◇_y ¬(P → Q f)` read `y.dia` through `P`; symmetrically for `t'`, `R`).
  Within the `y` fibre, `◇_yL` needs `Q(f(y.dia)) ⇒ ⊥`.
* **Conclusion:** with `here_subst` the only cross-fibre link, every proof of `S` passes through a
  transfer formula such as `◇_y Q(f(y.dia))`, which is not a subformula of `S` (it is `◇` of a view
  subformula: an almost analytic cut).  **KT as ruled has no derivations with the subformula
  property**, whatever the calculus, as long as the fibres are linked only by formula transfer.
  `◇`-contents only; for `Var` contents functionality is equality and stays atomic.
* **Diagnosis:** `here_subst` links two possibilities without pairing them, against the principle
  that linking two possibilities must go through a paired one (memory, "joint possibility goes
  through pairing").  A functionality rule over a paired possibility could give the joint view `S`
  needs.  Next, if the user agrees: a paper check of that (soundness, `S` cut-free, the canonical
  model); optionally `S` in Lean's ND.

**Option (b), paired functionality, checked (2026-11-07): unsound under `Ind`.**  `Here` at
`◇`-content reads `Ind`, Henkin-style indistinguishability (same slot formulas), not identity
(modal-extensions §10.23).  Two `Ind`-related possible objects may stand over disjoint extents that
no formula separates; no joint possibility, no world with both contents.  So a functionality rule
producing a paired possibility is unsound for `Ind`-models, and making it sound means reading `Here`
at `◇`-content as a join of witnesses: exactly the reading §10.23 rejected ("a joint possibility
that did not come from pairing"; it broke the canonical model).  `here_subst` is unpaired by design.

**The obstruction is the semantics, not the rule format.**  `Ind` is invariance under formulas, so
every use of it in a proof transfers a formula, and the formula acts as an interpolant between the
two fibres.  Refined counterexample `S₂`: as `S`, with `□_y(P → A(f y.dia))`, `□_y(P → B(f y.dia))`
and `□_{y'}(A(h y'.dia) → (B(h y'.dia) → R(y'.dia)))`.  Transferring `◇_y A(b)` and `◇_y B(b)`
separately gives two `y'` worlds; the proof must transfer `◇_y(A(b) ∧ B(b))`, which is not `◇` of a
subformula.  So analytic cut fails too; a linked-component (hypersequent) calculus is not expected to
help (components are worlds, `Ind` matches extents only by formulas).

**Remaining options:** (1) cut elimination and interpolation for the **`Here`-free fragment** of KT
and S4 (GK + TL, standard), with a conservativity check (do `Here`-free ND theorems need the `Here`
rules?), via completeness of the fragment for K+T(+4) models; (2) revisit `Here` at `◇`-content
(§10.23); (3) record as a finding: `Here` with indistinguishability buys T's expressiveness at the
price of analyticity.  Recommended: (1), with (3) in the paper.  Awaiting the user.

**Witness equality: not pursued (user, 2026-11-07).**  Tried before in some form; judged unworkable.

**Bounded transfer (2026-11-07): refuted.**  Conjecture: GKT cut-free except a transfer rule
`Tr` (`Here(s,t), Here(s,t')`; `Δ ⇒ ◇_t χ, Θ` and `◇_{t'} χ, Δ ⇒ Θ` give `Δ ⇒ Θ`) with `χ` a
conjunction of literals over the subformulas closed under swapping linked contents.  (Unbounded
`Tr` says nothing: with `t = t'` it is cut.)  Counterexample `S₄` (`t = ⟨y; f(y.dia)⟩`,
`t' = ⟨y'; h(y'.dia)⟩`):
  `Here(s,t), Here(s,t'), ◇_y ∃v A(y.dia,v), □_y ∀v(A(y.dia,v) → B(v)),
   □_{y'} R(y'.dia), □_{y'} ∀v(R(y'.dia) → ¬B(v)) ⇒`
ND-provable by transferring `◇_y ∃v B(v)`; no closed shared closure formula exists, so only `⊤`/`⊥`
are available.  The transfer formula is an interpolant between the fibres (a modal variant `S₃`
needs `□B` likewise).  Only "shared-language formulas of bounded rank" survives: finite up to
equivalence, but useless for search.

**Proposal: merged (joint) views.**  Strengthen `◇L`: when `◇_y φ` opens a view and
`Here(s,⟨y;b⟩)`, `Here(s,⟨y';b'⟩)` are present, the premise is a *joint view* holding `φ`, the
`□_y` and `□_{y'}` contents, the `◇_y` and `◇_{y'}` right formulas, and a fresh shared content `e`
with `b = e`, `b' = e` (one-sided equations, for Maehara).  A proof device, not a formula: the
language never asserts a joint possibility (a proof-level pairing made only from a `Here` link).
* *Subformula property:* `S`, `S₂`, `S₄` close in one joint view; `here_subst` should be
  admissible (its old failure, a right `◇_y` formula not reaching the `y'` view, is gone).
* *Soundness via interpolation:* a closed joint view splits at `e` (`y`-side `⊢ I(e)`, `y'`-side
  refutes it); outside, `◇_t I`, `here_subst` to `◇_{t'} I`, refuted.  Merge's Maehara case:
  interpolant `∃u(Here(s,u) ∧ ◇_u I(u.dia))` (or its dual by partition), only logical symbols
  added.  So soundness and Craig interpolation for KT are one induction.
* *Corrects* the earlier remark that a linked-component calculus would not help (it assumed
  components must be worlds of an `Ind`-model).
* *To check:* (i) interpolation at `◇R_T` (`here_intro`) and `here_name`'s eigenvariable;
  (ii) contents whose type contains `◇` (`b = e` is no `eqRec`; recursive merging of inner
  witnesses); (iii) completeness (cut elimination with `here_subst` admissible, or failed search
  giving a joint countermodel, `Ind = Eq` there, proper by `indInvariant_of_eq`); (iv) Lean cost:
  a joint view is a new `Ctx` view, unprecedented.

**Check (i), interpolation at the `Here` rules (2026-11-07).**  Interpolants restrict relation
symbols only (`GK.Itp`); variables, function symbols, `Here` and `eqRec` are free.
* *`Here` atoms cross the split for free:* if `H` (symbol-free) is on the left and `χ₀`
  interpolates with `H` copied to the right, `H ∧ χ₀` interpolates; on the right, `H → χ₀`.  So
  every rule with `Here` side atoms (`◇R_T`, `here_beta`, `here_eq`) has its atoms on both sides.
  `◇R_T` with the atom and the `◇_x` formula on opposite sides: `χ = I ∧ Here(…)` or
  `Here(…) → I`.  **Fine.**
* *`here_name`'s eigenvariable `c`:* principal atom on the left, `χ = ∃c I(c)`; on the right,
  `χ = ∀c I(c)` (quantifiers exist at every type).  **Fine.**  `TL`: one-sided, needs only
  `Occ (collapse φ) = Occ φ`.  **Fine.**
* ⚠️*The merge rule:* the joint view's interpolant may mention both contents `c = y.dia` and
  `c' = y'.dia`, and no formula outside can say that (a joint possibility).  Examples decompose
  (`◇_y γ ∨ ◇_{y'} δ`, possibly importing the other side's formulas), but in general they do not:

**⚠️Craig interpolation fails for KT with `Here` at `◇`-content (paper, 2026-11-07).**
`s : ◇◇Var`, `y, y' : ◇Var`, `t = ⟨y; f(y.dia)⟩`, `t' = ⟨y'; h(y'.dia)⟩`; `S` binary, `P`, `N`
unary.
  `φ = Here(s,t) ∧ Here(s,t') ∧ ◇_y P(y.dia) ∧ □_{y'} ∀v(P(v) → S(v, y'.dia))`
  `ψ = ◇_y ∃w(S(y.dia,w) ∧ ¬N(w)) ∨ ◇_{y'} N(y'.dia)`
* `φ ⊢ ψ`: from `¬ψ`, `◇_y K` for `K = ∃v(P(v) ∧ ∀w(S(v,w) → N(w)))`; `here_subst` at
  `◇_z K` gives `◇_{y'} K`; there `S(v₀, y'.dia)`, so `N(y'.dia)`.  The transferred `K` is a
  *joint property* (`P` from the left, `N` from the right): Fine's mechanism, here caused by
  identification by indiscernibility.
* No interpolant in `{S}`: worlds `w₀, a, b` (self-arrows, `w₀ → a, b`), `ext y = {a}`,
  `ext y' = {b}`; `a` and `b` both the random graph `G`; `f`, `h` constantly `o`; `y.dia = p`;
  the only necessary object constantly `o`; `Ind` least: `⟨a↦o⟩ ~ ⟨b↦o⟩`, the content of `s`.
  `M₁`: `P = {p}` at `a` and `b`, `y'.dia = q₁ ∈ nbhd(p)`, so `M₁ ⊨ φ`.  `M₂`:
  `N = nbhd(p)` at `a` and `b`, `y'.dia = q₂ ∉ nbhd(p)`, so `M₂ ⊨ ¬ψ`.  Choose `q₁`, `q₂` with
  the same adjacency to `o`; an automorphism `π` of `(G, o)` with `π q₁ = q₂`, applied at `b` only,
  is an isomorphism of the `{S}`-reducts (it fixes `o`, so the carriers, `Ind`, `f`, `h`).  Both
  are models proper: `a`, `b` carry identical structure and the only visible parameter is `o`.
* *To verify:* the models against the T model laws (carriers, realisation at self-arrows); the
  extension to S4 and S5 (S5's frames join `a`, `b`, `w₀`).  `Here` at `◇`-free content is not
  affected (two realised witnesses share the actual world; no indiscernibility transfer).

**Consequences.**
* *Merge soundness is easy:* `K(e) = ∃v(⋀Y(v) ∧ b(v) = e)` (the whole `y` side, `c` quantified)
  is transferred by `here_subst`.  The joint view is `Γ.diaIn y` with `y'.dia` inserted as a fresh
  variable, `□_{y'}` contents read through a substitution: probably no new `Ctx` view (to check).
  `◇`-typed contents (no `b(v) = e`) stay open.  So a cut-free KT with the subformula property is
  still plausible, without Craig: as for first-order S5 (cut-free hypersequents, no Craig; check
  the reference).
* ⭐*The `Here`-free fragment of weak KT is GK + TL:* replacing every `Here` atom by `⊥` maps ND
  proofs to ND proofs (every `Here` rule has a `Here` premise, now `⊥`; `hereEx` becomes `∃c ⊥`;
  the rest is schematic) and fixes `Here`-free formulas.  So conservativity is a syntactic
  translation, and cut elimination, the sharp subformula property and Craig for `Here`-free
  sequents follow the K4 route (TL's principal cut via a `collapseD` mirroring `GK.shiftD`).  Same
  for weak S4.  Weak T only (strong T's `T_dia` realises without a `Here` premise).
* *Proposal:* build GK + TL for KT and S4 on the `Here`-free fragment; record the Craig failure
  (optionally `φ ⊢ ψ` in Lean); the merged calculus as later research.

**Would witness equality repair Craig? (2026-11-07, paper.)**  *Not by itself.*  The
counterexample survives the strongest identification, literal identity (the join reading §10.23
rejected): let `y` and `y'` share the one-world extent `{a}`, `y.dia = p`, `y'.dia = q₁` (M₁) or
`q₂` (M₂).  Every view sees one content, so an `{S}`-formula sees `(G,o,p)` and `(G,o,qᵢ)`
separately, and an automorphism of `(G,o)` per view gives the same `{S}`-theories; `φ ⊨ ψ` still
holds.  The `{S}`-interpolant would be the joint `S(y.dia, y'.dia)` at a common point, which no
formula can state.
* *Diagnosis:* completeness needs the identification only to be **respected** (truth invariant under
  `Ind`), interpolation needs it to be **expressible**.  The T pattern (identification as a model
  law, the language only substitutes) is exactly the first, so it is structurally at odds with Craig.
  Same shape as Fine 1979 (QS5 etc. lack interpolation); the known repair is expressive, not a
  change of identity criterion: Areces, Blackburn and Marx, *Repairing the interpolation theorem in
  quantified modal logic* (APAL 2003): quantified *hybrid* logics have interpolation.
* *Our analogue (option (a) of the KT check):* an operator inside a view, `at z as v. χ`: the current
  arrow is in `z`'s extent and `v` is `z`'s content there (a `↓`/`@`-like binder for extents).
  Interpolant here: `◇_y (at y' as v. S(y.dia, v))`.  Witness equality becomes *definable*
  (`□_y at y' ⊤`, `□_{y'} at y ⊤`, content `□_y (at y' as v. eqRec b v)`), not primitive.  Each earlier
  failure loses its cause: §10.9 (no view has both contents: `at` supplies one), §10.23 (a child for
  `z` cannot name `x`'s content: now its language can), §10.25 (comparison across contexts
  ill-defined: `at` is the map).  Not a join from a link (pairing principle): like `◇(p ∧ q)`, never
  inferred from `◇_y`, `◇_{y'}` separately.
* *Costs:* `Here` at `◇`-content back to identity (extents equal, `Ind` dropped); a new formula
  former and view; children for sets of witnesses (B's network, `kd`, the precedent); completeness
  redone across the cube.  Open: the vacuous case (empty extents identified across inner
  annotations, §10.24–10.25), and whether Maehara closes (the merge interpolant is now a formula).

**The arrow atom `In`: paper check done (2026-11-07)** — `docs/v12-modal-extensions.md` §12.
`In(u↑, t)`: the arrow just taken is in `u`'s extent with content `t` ("`Here` along the arrow").
Soundness easy (`Ind := Eq`, shapes dropped); tree completeness closes on paper; cut elimination
and Craig for K/KT look plausible (the counterexample's interpolant is `◇_y ∃e(In(y'↑,e) ∧
S(y.dia,e))`).  Needs the user's decision: identity (sharing forced) vs indiscernibility.

### S5: prospects (discussed 2026-11-07)

Fine 1979 (JSL 44): interpolation fails for every constant-domain first-order modal logic
between K and S5, and for first-order S5.  Fitting 2002 (JSL 67) restores S5 interpolation by
adding propositional quantifiers (the interpolant may need them); Areces, Blackburn and Marx
restore it with nominals.  The failure looks like an expressive gap (the interpolant must bind an
individual of another world), which our `◇X`-typed variables with `◇_c` may supply, so S5
interpolation in our language would be a Fitting-style result with an independently motivated
language; Fine's theorem itself (base-language interpolants) stands.  Our K-family results do not
contradict known theorems (no Barcan, varying domains).

**Step (1) done (2026-11-07): Fine's counterexample has an interpolant in our language**
(`QML_v12m_FineExample.lean`, sorry-free).  Fine's valid entailment (varying domains, no Barcan)
is `p ∧ □∀x□(p → Fx) ⊢ q → □∀x◇(q ∧ Fx)`.  Its classical validity predicates `F` at the actual
world of objects of other worlds, possibly non-existent there.  In our language an object of `v`
is read at a further world only through a modal type, so `x : □Var`, read as `x.keep.here` (T + 4
expose only `keep`).  Translated so, `Fine.interpolant`: with T, 4 and B, `φ ⊢ χ` and `χ ⊢ ψ` for
`χ = ∀y:□Var. F(y.here)` (every necessary object, as realised here, is `F`), whose only relation
symbol `F` occurs in both; `Fine.interpolant_S5` for `ModalSys.S5`.  `φ ⊢ χ`: `T_box` twice.
`χ ⊢ ψ`: `B_box` on the closed `q ∧ χ`, then in the `◇` view `χ` instantiated at `x.keep`
(`SubE.proj_here_eta`).  The interpolant is of the kind Fitting's propositional quantifiers and
the hybrid repairs supply, from the language's own means.  **Pinned (user, 2026-11-07):** S5 cut
elimination and interpolation wait; KT and S4 first.  Plan: (1) translate Fine's counterexample
and look for an interpolant by hand (needs the paper; the user may have it); (2) hypersequents,
not analytic cut (cut formulas mix languages, so Maehara fails with analytic cut), components as
views of the cluster, the paper check aimed at quantifier rules with an eigenvariable in another
component; (3) prerequisites KT (Here rules), then weak S5, then the strong forms.

## 5. Craig interpolation

**Goal.** If `φ ⊢ ψ`, there is `θ` using only the non-logical symbols common to `φ` and `ψ` with
`φ ⊢ θ` and `θ ⊢ ψ`.

**Status: ✅ DONE FOR K, relation symbols (2026-11-07).**  `QML_v12m_GKInterp.lean`: ⭐`GK.interp`,
every split `Δ₁ ; Θ₁ | Δ₂ ; Θ₂` of a GK-derivable sequent has an interpolant `χ` (`Δ₁ ⇒ Θ₁, χ` and
`χ, Δ₂ ⇒ Θ₂` cut-free derivable, every relation symbol of `χ` on both sides: `Itp`); ⭐`GK.craig`,
for ND in K over a presented context: from `φ ⊢ ψ`, `χ` with `φ ⊢ χ`, `χ ⊢ ψ` and every relation
symbol of `χ` in both `φ` and `ψ`.  Sorry-free, standard axioms; about 700 lines.  Maehara's
method on cut-free GK, no paper surprises:
* axioms give `⊥`, `⊤`, `P` or `¬P`; two-premise rules the disjunction of the premises'
  interpolants (principal formula in the first part; the second part by `Itp.swap`, the negation of
  the swapped split's interpolant);
* an eigenvariable rule (`∀R`, `∃L`) binds the eigenvariable in the interpolant, `∃u χ'`;
* `□R`: the boxed hypotheses split by side (`List.filter`); the interpolant is `◇χ'` (`¬□¬χ'`), or
  `□χ'` by the swap;
* `◇_xL`: hypotheses and conclusions split by side; `◇_x χ'`, or `□_x χ'` by the swap; the witness
  `x` is a variable of the shared context;
* `repl` with `t = s` and `P(t)` on different sides: `t = s → χ'` (equality is logical).

*"Common language" as decided:* relation symbols only; equality logical; function symbols, the
declared variables and the witness addresses unrestricted (both sides share the context).

*Possible to-do, not urgent (user, 2026-11-07): the function-symbol condition.*  Foreign function
symbols enter the interpolant through instantiation terms and `repl`'s `t = s → χ'`.  First-order
logic abstracts them by a variable quantified at the top; here that fails, since a term like
`f(x.dia)` inside `◇_x` cannot be named by any outer variable (only `x`'s own content is visible in
its view).  Two routes: (a) Maehara with the abstraction done *inside* views (`◇_x ∃z R(z)`),
plausible because function symbols are read per world (occurrences at different worlds are
unrelated, those in one world merge into one scope); needs a term-abstraction operation and an
anti-substitution lemma for GK, and a paper check that side 2 survives the local abstraction where
`◇_xL` meets `□_x` hypotheses; (b) graphs `R_f` with totality and functionality axioms, which must
hold at every world (hypotheses `□ᵏ Ax` up to the modal depth), plus signature extension.
Estimate 2 000 to 4 000 lines.  Also open: the other systems of the cube (cut elimination is only
proved for K).

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
