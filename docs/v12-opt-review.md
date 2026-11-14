# The `Opt` programme: a high-level review *(2026-11-14)*

A review of the whole plan of roadmap Milestone 5: the new modal operators (`◇⁰`, `◇⁰ᵀ`, then
`⟪back⟫` and a side view), every primitive relation replaced by such an operator plus `≡`, and
soundness, completeness, cut elimination and Craig interpolation for the result.  Paper judgement
only; nothing here is checked in Lean.  Sources: roadmap M5, `v12-modal-extensions.md` §12,
`v12-metatheory-todo.md` items 4–5.

## Verdict

| Part | Soundness, completeness | Cut elimination, Craig | Judgement |
|---|---|---|---|
| K, D (M1) | built | GK needs `optL`, `reopenR`, the folded `□R` | **will work** |
| KT (M2, M3) | sound; tree to build | TL + collapse of derivations | **likely** |
| K4, KD4 (M4a) | no new rule on paper | 4-copies shift `◇⁰_y` to `◇⁰_{y.keep}` | **likely** |
| S4 | `keepOnly` naming to settle | as KT and K4 together | **probable, one design point** |
| B (M4b) | plausible, large | **open research** | **uncertain** |
| 5 (M4c, M4d) | redesign open; K5/KD5 are gaps today | **open research** | **uncertain** |
| Shapes, `Ind`, `Ret` deleted | needs B and S5 redone first | — | **only if all of the above land** |

The tree systems (K, D, T, 4) should go through, and they contain the result that motivated the
work: Craig for KT, which fails with `Here` and `Ind`.  B and 5 are a different kind of project:
there the operators are a hypothesis about what an analytic calculus could look like, not a
checked design.  The full end state (no shapes anywhere) depends on the uncertain half.

**So the main recommendation is about order and stopping points, not design** (§1 below).

## 1. Order of work: test the gate before paying for the tree

* **The gate is M3, and it does not depend on completeness.**  Cut elimination and Maehara are
  syntactic.  M2's remaining steps (NecT, the KT tree at 2 000–4 000 lines) come before M3 in the
  roadmap, but none of them is needed to learn whether GK with `◇⁰` has cut elimination and Craig.
* **Recommended order:** finish step 4 (the derived `Here` rules), then **GK with `◇⁰` for K and D**
  (extend `QML_v12m_GK*`: `optL`, `reopenR`, the folded `□R`/`◇_uL`, weight `◇_u χ = χ + 2`), then
  **TL and `◇⁰ᵀ` for KT**, and only then the KT tree.  If Maehara's `◇⁰` case fails, the tree would
  have been built for a logic without the property it was built for.
* *Why I expect M3 to pass* (checked by hand for this review):
  * `optL` principal on the left part: interpolant `◇⁰_y I`; on the right part: `□⁰_y I`.  Both
    halves close with `optL` and `reopenR` alone.
  * The folded `□R`: the standard `◇I` / `□I`, the folded `◇⁰_u χ` splitting with their `◇_u χ`.
  * TL is a one-premise rule and keeps the interpolant.
  * There is no equality at higher types to replace: function symbols take `Var` arguments only,
    so a `◇`-typed term occurs only as a substitution entry, where it dissolves (`◇_x` becomes
    `◇_z` with the body substituted).  `≡` is a defined formula.  GK needs no Leibniz rule and no
    naming rule; `opt_name` and Leibniz are ND-derived and so admissible.  This is the plan's best
    structural feature: the old KT obstacle (`here_subst` not atomisable) has nothing to stand on.
* *Where M3 needs care:*
  * **Collapse of derivations** (`GK.collapseD`, height-preserving), for the `□R`/TL principal
    cut, and a second collapse `diaIn x → optInT x` for `◇_xL` against T's `◇_xR` at the identity
    arrow.  Both rely on the collapse being a homomorphism, which (S) secured.
  * **The measure with folding.**  `◇_u χ` weighs `χ + 2`, `◇⁰_u χ` and `◇⁰ᵀ_u χ` weigh `χ + 1`,
    and `collapse`, `shift`, `subst` and `mono` must all keep the weight, including across the two
    witness kinds.
  * **The KT counterexample `S`** must be derived cut-free in the built calculus, not only on
    paper with `In` (§12.7).  Do it as soon as GKT exists; it is the cheapest real test.

## 2. Decide before the KT tree: the model class with `Opt` on

* With `Opt` on, `ModalSys.shaped` is still `T || BStrong`, so a KT model must still supply shapes
  and prove `IndInvariant`.
* `IndInvariant.inv` quantifies over **every** slot formula, and the language now contains `◇⁰`,
  `◇⁰ᵀ` and `≡`.  A canonical `Ind` other than equality would need its invariance re-proved for the
  richer language; the old `Interch` machinery does not cover it.
* **So the KT tree should not carry shapes at all:** `Ind := Eq` (`Model.indInvariant_of_eq`, as
  M1's tree and the cone use), shapes off with `Opt` (`shaped := (T || BStrong) && !Opt`), and
  `pos_inj` in its extensional form.  Soundness for that class is already proved, since it is a
  subclass.  Completeness for a subclass is the stronger statement.
* This also settles two recorded loose ends: `IndInvariant.inv` against `OpenedT` (uniform
  substitution, §12.30), since with `Ind := Eq` `inv` is trivial; and whether `OpenedT` should be
  structural (it stops mattering for `inv`).
* *Cost:* `shaped` is read in about 100 files.  The change is to its definition, with the `Opt`
  side refuted everywhere the old code runs (`NoOpt`).  Do it as its own step, with the strict
  build, before any tree code.

## 3. Scope of "cut elimination": weak forms only, unless decided otherwise

* GK today excludes every strong form (`GKSys`: `TStrong`, `DStrong`, `FourStrong`, … off).  The
  strong forms are existence laws: a fresh object with a **compound** hypothesis (`T_dia`'s
  `◇⁰ᵀ_c (c.at ≡ t)`, with `≡` unfolding into `□` and nested `◇⁰` at higher types).
* Such a rule is not geometric in Negri's sense (atoms in, atoms and `∃` out), so the standard
  route to cut elimination with axioms does not apply directly.  §12.18 met the same problem for
  `opt_name` and avoided it with `opt_reopen`; the strong forms have no such escape, because they
  assert existence.
* **State the target explicitly:** cut elimination and Craig for the weak cube first.  Treat each
  strong form as a separate question, on paper, before promising it.  A possible route for strong
  T: bind the fresh witness's identity content to `t` in the *context* (a view whose `c.at` is
  `t` by substitution) instead of asserting `c.at ≡ t` as a formula.  Unchecked.
* *Related:* strong B and `BStrongW` are domain-covering laws (□-BF, ◇-BF).  That is the zone of
  Fine's failures.  Our varying domains and first-class possible objects may well avoid them
  (`FineExample`), but nothing proves it.  Try to transplant Fine's and the KT counterexample into
  each strong system on paper before building its calculus.

**Correction (2026-11-14, same day; user's question).**  The above is too pessimistic.  A strong
form in the shape "fresh object plus a hypothesis" (`T_dia` with `Opt`: from
`(Γ, c); Δ, ◇⁰ᵀ_c (c.at ≡ t) ⇒ Θ` infer `Δ ⇒ Θ`) has **no principal formula in its conclusion**,
as `serial` has none.  A cut never meets it principally and permutes into its premise.  Negri's
atom condition concerns rules with principal formulas.
* *Cut admissibility:* expected to hold.  The rule must commute with `collapseD` and `shiftD` (the
  collapse of an instance is an instance).
* *Subformula property:* only up to the naming formulas `◇⁰ᵀ_c (c.at ≡ t)`, which have no relation
  symbols.
* *Craig:* as an eigenvariable rule.  With the naming formula `N` in the left part and premise
  interpolant `I`, take `∃c:◇A. (N ∧ I)`; both halves close (checked by hand).
* The same holds for NecT (`u : □A`, `u.here ≡ t`; at base type the hypothesis is an atom),
  strong D, and strong B's existence rules once phrased with `⟪back⟫`.  Strong 4's lifts are
  different: the object lives at the start and depends on one further in, so it is a rule, not a
  formula on either side; unchecked.
* **Agreed target (user, 2026-11-14):** cut elimination and Craig for the weak forms is an
  acceptable result; the strong forms are a bonus, "analytic up to naming formulas".
* **Decided (user, 2026-11-14):** one `T_dia` rule whose premise dispatches on `Opt`.

**One picture for the operators (user's question, 2026-11-14).**  Each axiom has a canonical arrow
built from the arrows taken, and an operator reading the start's objects along it: T the identity
(`◇⁰ᵀ_y`), K the arrow (`◇⁰_y`), 4 the composite (`◇⁰²_y`, which **is** `◇⁰_{y.keep}`, since
`y.keep`'s extent is the second arrows whose composite lies in `y`'s), B the way home (`⟪back⟫`),
5 the side arrow.  4's operator is definable because the composite factors through its last step;
B's and 5's do not.  The weak rules of T and 4 are the two homomorphisms (collapse, shift).  D has
no canonical arrow; its operator is `◇_c`, and strong D says a name exists.  For the writeup:
`◇⁰²` as defined notation; `keep` stays in the Lean.

## 4. B: the operator is plausible; the analytic calculus is not established

* *Semantics and completeness:* `⟪back⟫` read at the far world is sound on paper (§12.29), and the
  classical B argument covers the canonical network (§12.12 (2)).  The costs are the ones already
  listed there: labels decided by theories, the compactness argument over label sets, and strong
  B's invariants without `sep` (unchecked).
* *Infrastructure:* the back view needs the far context to remember the **whole** parent context,
  and the environment the whole parent environment, and the substitution its parent substitution.
  That is a recursive `Ctx`/`Env`/`Subst`, a larger change than `wit` was.
  * **Design it once.**  `wit` is already an instance of "the view remembers something of its
    parent" (the parent's `◇`-addresses).  `⟪back⟫` remembers everything; the side view remembers
    the parent as seen from a sibling.  A single `home` component, from which `wit` is derived,
    would serve all three.  Three separate mechanisms would triple the ripple (each new view former
    has so far touched about 50 files).
* *Cut elimination:* **§12.31's hope is stronger than what is known.**
  * Having the converse modality in the formulas does not give a cut-free calculus: tense logic
    `Kt` has it, and its cut-free calculi are nested or display calculi, not ordinary sequents.
  * What the plan really proposes is a nested sequent with a parent pointer, written with formulas:
    `□R`'s premise would carry each parent formula `ψ` as `⟪back⟫ψ`, and a rule entering the back
    view would have to carry the child's sequent home as a formula.  That can probably be made to
    work, but the measure, the form of the subformula property (up to the wrapping), and the
    Maehara cases are all unchecked, and this is where symmetric logics are hard.
  * Propositional KB has interpolation (nested sequents: Fitting and Kuznets).  The quantified
    case with these objects is new.
* **Treat M4b as two milestones:** (i) `⟪back⟫` with soundness, completeness and the relations
  `Back`/`ret` defined away, which is valuable on its own (the relations go, the redundancy sweep
  becomes moot); (ii) the analytic calculus, a research question with a paper check first and a
  real chance of "no".

## 5. 5: keep expectations low until the paper design exists

* Weak K5 and KD5 are incomplete today, and 5 without 4 has only the link relations.  The side
  view is a sketch.  F2's obstruction must be rechecked first (§12.29).
* With 4 (K45, KD45, S5) there is no relation atom and no `Ind` transfer, so the question is only
  the calculus.  The standard tools are hypersequents (S5) and grafted hypersequents (K5, KD5,
  K45, KD45: Kuznets and Lellmann).  A formula-level counterpart is not known to me.
* The existing 5 development is the largest in the repository (the cluster, hub, loop and cone
  files).  The end state replaces it.  **Do not start M4d until M4c's paper design has passed the
  same four checks every other design here has** (rules sound, closed under substitution, truth
  lemma, cut reductions).

## 6. The end state is conditional: define the fallbacks now

* Shapes can be deleted only when **every** shaped system runs with `Opt`: T on the tree, T with 4,
  strong B on the network, strong B on S5's cluster.  That is most of the completeness work of the
  cube again, in the new language.
* If B or 5 stalls, the repository holds two languages for good.  That is acceptable if it is
  planned:
  * **Fallback A (tree systems):** K, D, T, 4 with `Opt`: sound, complete, cut-free, Craig.  The
    old language stays for B and 5, with the old results.  This alone carries the paper's main
    point (the repair of interpolation by an operator and `≡`).
  * **Fallback B:** A plus B with `⟪back⟫` (relations gone, completeness), without an analytic
    calculus.
* The gating that makes this possible is in place (`NoOpt`, `NoT`, `WFF.here`'s `hO`).  Keep it
  honest:
  * **Watch for vacuity.**  A lemma that gains `[NoOpt]` to compile says nothing about `Opt`
    systems; one that gains `[NoT]` says nothing about T.  M1's files must never take `NoOpt`
    (checked once, 2026-11-13; check again after any automatic fixing).
  * **Keep one table** of what is proved with `Opt` on, per system (sound, complete, cut-free,
    Craig), in the roadmap.  `CubeSys` extends `NoOpt`, so none of the cube's headline theorems
    speak about `Opt` systems.

## 7. Smaller points that need care

* **S4 and `keepOnly`.**  Under T + 4 the views expose only `keep`, and §12.12 makes the arrow
  witness definable there (`◇⁰_u` as `◇⁰ᵀ_{u.keep}`).  So S4 has two candidate primitives for one
  notion.  Decide which is primitive, and prove the other equivalent, before M4a touches T + 4.
* **4's shift of a witness.**  `shift (◇⁰_y χ)` must be `◇⁰_{y.keep} (shift χ)`: the composite
  arrow lies in `y`'s extent exactly when the second arrow lies in `y.keep`'s.  `Ctx.Shifts`
  refutes its `optx` case by `optStage` today, as `Collapses` did before step 3.  Expect the same
  amount of work as the collapse (`CorrW` and its lemmas) again.
* **Impossible objects.**  All possible objects of one type with empty extent are identified
  (§12.11, accepted).  The new logic is therefore a proper extension of the old one even on
  `◇⁰`-free formulas.  Say so wherever old and new results are stated side by side.
* **What Craig says.**  `GK.interp` restricts relation symbols only; function symbols and free
  variables are shared through the context.  With witnesses, an interpolant from inside a view
  mentions the view's witnesses and leaves as `◇⁰_y I`.  A stronger theorem (function symbols,
  constants) would need eigen-witnesses handled like eigenvariables.  Not planned; do not promise
  it by accident.
* **Strong T with `Opt`.**  `T_dia` is gated off; one rule whose premise dispatches on `Opt` is
  proposed (§12.32).  It needs soundness and a substitution case at `hereO`, and it is exactly the
  rule §3 says has no cut-free form yet.
* **Automatic fixing.**  The flag drop and the gate were done by scripts that add instance
  arguments where the build fails.  They are effective and they can over-reach (the file-wide
  `NoOpt` on `CanonFunc` broke M1 and was reverted).  After each such pass, list what gained
  which class.

## What I would do next, in order

1. Finish step 4 part 2 (the derived `Here` rules; strong T's rule last).
2. The model class with `Opt` on (§2).
3. GK with `◇⁰` for K and D: cut elimination, subformula property, Craig.
4. GKT: TL, `◇⁰ᵀ`, the collapse of derivations; the counterexample `S` cut-free; Craig for KT.
5. Only then the KT tree and NecT.
6. 4 on the tree (and S4's design point).
7. B, in the two milestones of §4, the paper check of the calculus first.
8. 5, when its paper design exists.
