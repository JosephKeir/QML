# QML v12: modal extensions (design)

Status: 2026-09-14. **Weak T and weak 4 are implemented**, with soundness and completeness for
every combination (K, T, 4, and T + 4 = S4); files `QML/QML_v12m_*.lean`, namespace `V12M`.
Everything else is design. Claims marked *(sketch)* come
from paper arguments that have not been checked in Lean.

## 1. Goals and constraints

- Extend the v12 system (K, with soundness and completeness proved) by D, T, B, 4 and 5, which
  generate the 15 systems of the modal cube, and by the Barcan formulas.
- Users choose combinations. Every axiom comes in a **weak** and a **strong** version.
- The K build stays untouched. The extensions live in separate, generalised files; once they are
  finished, the K-only files can be retired in favour of the generalised ones with every flag off.
- Presented contexts (`Ctx.Presented`) are the real contexts; metatheorems are stated for them.
- Prefer admissible metatheory to new proof rules. The axioms themselves still need rules.

## 2. Vocabulary

- **Weak version** of an axiom: only the laws stated with `□` and the unwitnessed `◇ = ¬□¬`.
  Their duals come for free.
- **Strong version**: adds the witnessed-`◇` laws (those involving `◇_x`, possible objects).
- **Carrier maps.** Each frame condition gives maps between carriers at related worlds.
  - *Inward*: an object at `w` is used at the same world, or inside a modality (at `v ∈ R(w)`).
    It can be **named**: a context principle (an existing address becomes visible in a view) or a
    term former.
  - *Outward*: an object living at an inner world `v` is wanted at `w`. Which object it is depends
    on `v`, which `w` cannot name, so it needs an **existential** rule.
- **Link.** A formula, at some level, relating an outward witness chosen at `w` to the inner
  object at `v`. With a link, completeness can use the Barcan-style successor construction
  (Hughes–Cresswell): build `v` while keeping `◇_x ∃ȳ. ⋀S ∈ T_w`, and pick each witness from
  `w`'s language. Without one, every witness would have to realise an infinite type, which a
  Henkin construction does not provide. **We know no method for outward maps without a link.**
- **Name it iff it is unique.** An object determined by current-level data (by extensionality,
  `nec_inj`/`pos_inj`) should be a term or an address, not an existential.

## 2a. Witness combinations and components *(sketch)*

**Contraposition pairs the two-operator forms**, so each slogan pair is one principle:

| Axiom | Unwitnessed | Same witness |
|---|---|---|
| 4 | `□φ → □□φ` ⟺ `◇◇ψ → ◇ψ` | `□_x`/`◇_x` forms likewise |
| B | `φ → □◇φ` ⟺ `◇□ψ → ψ` | |
| 5 | `◇φ → □◇φ` ⟺ `◇□ψ → □ψ` | `◇_x φ → □◇_x φ` ⟺ `◇□_x ψ → □_x ψ` |

For example, "possibly necessary ⇒ necessary" and "possible ⇒ necessarily possible" are the same
axiom. Neither is easier than the other.

**Decorating the operators does not generate new principles.** Take `◇φ → □◇φ`, whose premise `◇`,
conclusion `□` and conclusion `◇` can each carry a witness:

| Decoration | Status |
|---|---|
| conclusion `□_x` | weaker; follows from the plain form by `□ψ ⊢ □_x ψ` |
| premise `◇_x` only | follows from the plain form by `◇_x φ ⊢ ◇φ` |
| plain premise, conclusion `◇_z` | asserts that possible objects exist: a comprehension principle (§8.5), not part of 5 |
| same witness on both `◇`s | the named inward principle (strong 5) |
| different witnesses | unrelated, not a principle |

**What matters is where the objects live.** Objects of the outer world pushed inward can be named.
Objects born at an inner world and pulled outward depend on that world, so they need an
existential. The existential lives on the "possibly necessary ⇒ necessary" side for 5, even
though the restriction map itself is a total function. So every axiom has up to three
**components**:

1. the frame schema (closed formulas);
2. an inward, named carrier map (a context principle);
3. an outward, existential carrier map.

| Axiom | Inward, named | Outward, existential |
|---|---|---|
| 4 | `Nec(w)→Nec(v)` restriction: `□`-items visible deeper, `□φ ⊢ □□φ` | `Pos(v)→Pos(w)` lift: `◇_x◇_{x.dia}θ ⊢ ∃z:◇A. ◇_z θ(z.dia)` |
| B | `D(w)→Pos(v)` singletons: `φ(z) ⊢ □◇_{z↑}φ(z↑.dia)` | `Nec(v)→D(w)` value at origin: `◇∃u:□A. □φ(u.box) ⊢ ∃a:A. φ(a)` |
| 5 | `Pos(w)→Pos(v)`: `◇`-items visible under `□`, `◇_x φ ⊢ □◇_x φ` | `Nec(v)→Nec(w)` restriction: `◇∃c:□B. □χ(c.box) ⊢ ∃c:□B. □χ(c.box)` |

The weak/strong labels of §3 put the `Nec`-side component in *weak* and add the `Pos`-side
component in *strong*. For 4 the weak component is the named one. For B and 5 it is the existential
one, so the nesting weak ⊂ strong puts the open part inside strong B and strong 5.

**Components as flags, or bundles.**
- Semantically the components look independent. For example, 5's `Pos` map does not force euclidean
  frames or the `Nec` restriction. A flag per component would describe the systems more finely than
  weak/strong.
- Completeness may not respect that independence. An outward component needs a link, and every link
  known so far comes from another component:
  - weak B's link is strong B's singleton;
  - weak 5's link is 4's visibility;
  - strong 4's lift has a link only with strong 5.
- The frame schema of B and 5 probably also needs the outward component, because the canonical
  proof carries an inner world's necessities through the outer world.
- So some components may only be completable in **bundles** (e.g. weak B only together with strong
  B). Inward-only systems are the tractable kind and may be complete alone.
- Plan: keep components as separate flags where the syntax allows it. Treat "which flag sets are
  complete" as a feasibility question beside the closure question of §4, settled case by case.

## 3. The flags

`R` is the accessibility relation. `Nec`/`Pos` are the carriers, `ext`/`cont` the extent and
content of a possible object.

### D (seriality)
- Frame: `R(w)` nonempty.
- **Weak**: rule `□⊥ ⊢ ⊥`. Canonical seriality is the usual successor for `◇⊤`.
- **Strong**: axiom `⊢ ∃x:◇𝟙. ◇_x ⊤`. Carrier condition: some possible object has nonempty extent.
  Same level, not unique ⇒ existential. A Henkin witness satisfies it directly.

### T (reflexivity)
- Frame: `w R w`.
- **Weak (inward, named): extract `□A → A`.**
  - Context principle: a new projection step `here`. `u.here : A` is readable at the current level
    whenever `u : □A` is (`VarType.step (□A) here`, gated by the flag). It must differ from `box`:
    for `u : □□C`, inside a `□` the address `u.here.box` is `u(w)(v)` while `u.box.here` is
    `u(v)(v)`. As a projection it needs no context entry; `Ctx.ref`, `Env.ref` (evaluate at `w`
    itself), `Subst.at` and `Term.bases` treat it like `fst`/`snd`.
  - Moving syntax from the `□` view to the current level is **collapsing**
    (`VarSymb.collapse k`: the level step with exactly `k` level steps after it becomes `here`),
    with `Term.collapse`/`WFF.collapse` along `Ctx.Collapses k Γ₁ Γ₂`. The `here` component of a
    term entry `□t` is `t` collapsed. Collapsing commutes with weakening, with collapsing at another
    level, and with substitution (`Subst.Corr`).
  - Canonical forms and address witnesses survive. Binding is by root, so `x.here` is bound
    together with `x`.
  - Semantics: an `extract` operation on `Nec` with law `extract n = necEval n ⟨w, refl⟩`, and a
    matching `GFunc` constructor for compiled bodies.
  - Rule `T_box`: `□φ ⊢ φ`, with φ over `Γ.boxIn` collapsed onto `Γ` (`WFF.collapse`).
  - *Implemented.* Soundness via `sat_boxHere` (environments agree across the collapse,
    `Env.CollapseAgree`). The general Leibniz principle of K (`SubE.EqE`, equalities tracked by
    membership among hypotheses) is not carried over: a `here` component needs the collapsed
    equality, which is provable but not a hypothesis. Completeness only needs argument spines
    (`LeibnizSpine`), and gives Leibniz back.
  - *Canonical model (implemented).* Proper accessibility `Acc'` additionally requires the
    successor to be one level deeper, so a world is never its own proper successor. The frame
    relation is `R w v := Acc' w v ∨ (T ∧ v = w)`; a successor at the same depth is the world itself
    (`Succ.self`). Raw necessary objects range over all of `R(w)`. `rden (□t)` at a proper
    successor is `rden t` there, and at `w` itself it is `rden` of `t` collapsed. Collapsing keeps
    the type, so `rden` recurses on the type. Extents contain only proper successors. `applyG`
    sends `extract` to collapsing, which commutes with application (`applyG_collapse`). The
    term truth lemma uses induction on term size. In the `□` truth case, the self-successor goes
    through `sat_boxHere` and `T_box`; the proper successors go through `exists_box_fail` as in K.
- **Strong (inward, UNNAMED): a possible object realised here (decided 2026-09-17).**
  - **Semantics.** A model operation `posRet : Dom A w → Pos A w` whose extent contains `w` with
    the object as its content there. Stated existentially — `∃ (h : R w w), ⟨w, h⟩ ∈ extent ∧
    content = a` — so it needs no reflexivity hypothesis and implies `R w w` wherever a domain is
    inhabited. **No uniqueness and no naturality**: the object need not be a singleton, and nothing
    relates `posRet (f a)` to `posRet a`.
  - **Rule (Henkin-style, with a fresh witness `c : ◇A`).** From
    `Δ, θ₁↓(t) → ◇_c θ₁, …, θₙ↓(t) → ◇_c θₙ ⊢ φ`, with `c` fresh and not in `Δ` or `φ`, conclude
    `Δ ⊢ φ`. Here `θ↓(t)` reads the view formula `θ` at the current world: `c.dia ↦ t`,
    `u.box ↦ u.here` (weak T), `u.keep ↦ u` (4). That is an ordinary substitution into `Γ`, so
    `WFF.subst` states it and `sat_subst` proves it sound; the agreement lemma is the `◇` analogue
    of `Env.collapseAgree_self`, namely `diaPush` at the self-world.
  - **No polarity condition is needed.** Only the one direction `θ↓(t) → ◇_c θ` is ever available,
    so `◇_c` can only be used positively. The user's axiom "from `P` infer `∃x:◇A. ◇_x P†`" is the
    one-instance case: modus ponens, then `ex_intro` at `c`, then discharge `c`.
  - **Why finitely many instances suffice.** The canonical construction adds one witness constant
    per term with all instances as axioms; consistency of that extension is exactly this rule with
    the finitely many instances of a hypothetical derivation of `⊥`. Stronger consequences, such as
    `∃x ∀y …`, follow from completeness rather than from the rule.
  - No new term formers, so `◇` canonical forms, `eqRec` and the address-witness design are
    untouched.
  - *Rejected: named singletons (`unitT t`).* A new `◇` canonical form and annotation, with the
    collapse `◇_z φ [z ↦ unitT t] = φ[z.dia ↦ t, u.box ↦ u.here]` living in substitution. Clean and
    complete-able, but it forces every possible object realised here to be a singleton, and every
    witness use then reduces to a statement about the object.
  - *Rejected: naming the unnamed object (`y.ret`).* Substituting a compound term for `y` has no
    address to name `ret(t)`; requiring one (naturality) plus projections forces a single extent per
    world and homomorphic counterpart maps. Uniqueness of the realised-here object forces the same.
  - *Rejected: the positive-polarity schema `Φ⟨x := t⟩ ⊢ ∃x. Φ(x)`.* Same strength, but it needs a
    new formula transformation with polarity tracking and slot renumbering. The Henkin rule reuses
    `WFF.subst` instead.

### 4 (transitivity)
- Frame: `R(v) ⊆ R(w)` for `v ∈ R(w)`.
- **Weak (inward, named): restriction `Nec(w) → Nec(v)`.**
  - Context principle: `□`-items stay visible deeper; `Γ.boxIn` also contains `u : □A`.
  - Rule: `□φ ⊢ □□φ`.
  - Semantics: a restriction map with `necEval (restrict n v) s = necEval n s`.
  - *Implementation (done).*
    - **Addresses.** A new LEVEL step `keep`, visible in `Γ.boxIn` (and so in `Γ.diaIn x`) when the
      flag is on: `u.keep : □A` for `u : □A`, the restriction of `u`. At each level an address
      records whether the object was evaluated (`box`) or kept (`keep`), so addresses are unique:
      at depth 2, `u.keep.box = u(s)`, `u.box.keep = u(v)|R(s)`, `u.keep.keep = u|R(s)`.
    - **Rejected: a projection `u.dup : □□A`.** It would need no change to `boxIn`, but it names
      the same object twice (`u.dup.dup.box = u.dup.box.dup` by coassociativity). Completeness
      would then need equations between variables.
    - **Shifting** (`VarSymb.shift k`, the counterpart of `collapse`) inserts `keep` before the
      level step with exactly `k` level steps after it. It moves syntax one view further in:
      `Ctx.Shifts 0 Γ.boxIn Γ.boxIn.boxIn` (`u.box ↦ u.keep.box`, `u.keep ↦ u.keep.keep`).
    - **Rule** `four_box`: `□φ ⊢ □□(shift φ)`.
    - **Semantics.** `□` becomes a comonad: T is the counit (`extract`), 4 the comultiplication
      (`GFunc.dup : □A → □□A`). The law is `necEval (necEval (dup n) v) s = necEval n s` (by
      transitivity), and `boxPush` reads `u.keep` at `v` as `necEval (dup u) v`. Soundness goes
      through a `ShiftAgree` analogue of `CollapseAgree`.
    - **Collapse under T + 4:** `u.keep` collapses to `u`, which removes the step.
    - **Canonical model (implemented).** Accessibility is a chain of proper steps (`Chain`), of
      length 0 only under T (the world itself) and of length at least 2 only under 4. So it is
      reflexive under T and transitive under 4, and a successor's depth difference is the length
      of its chain.
      - `rden (□t)` at a successor `d + 1` levels deeper is `rden` of `t` shifted `d` times
        (`Term.shiftIter`, in the iterated view `Ctx.boxIter`); shifting keeps the type. The
        iterates are **inner-first** (`boxIter (n+1) Γ = boxIter n Γ.boxIn`), so a far denotation
        is definitionally what `□(shift t)` gives from the first proper step
        (`rden_boxtm_step`), and proofs go by induction on the distance with one-step lemmas.
      - `dup` is raw evaluation at the composite successor. Its closure law (`rden_dup`) uses
        `collapse_shift_self`, `shift_shift_same` and, under T + 4, `Term.collapse_shift_same`:
        shifting then collapsing one level undoes itself because views have only kept entries.
        That identity is exactly what the T + 4 naming decision below makes true.
      - Truth lemma for terms at far successors: `interp_box_far`, via `interp_shift` and
        `shiftAgree_twoBox`. For formulas: `four_box`, the necessary contents of the first step,
        and `sat_shift_twoBox`, by induction on the distance.
      - `completeness` and `provable_iff_valid` hold for every flag combination (the temporary
        `ModalSys.NoFour` is gone); axioms `propext`, `Classical.choice`, `Quot.sound`.
    - *Implemented.* Syntax (`keep`, `shift`, `Ctx.Shifts`), substitution (`keepE`, `ShiftSubst`:
      shifting commutes with substitution, collapse and weakening), models (`Frame.trans`,
      `GFunc.dup`, `necDup_eval`), semantics (`SemShift`), the rule `four_box`, and soundness and
      completeness for every flag combination.
    - **Finding: T + 4 (S4) breaks address uniqueness.** With both flags, `u.keep.here` (`u` kept
      at `v`, read at `v`) and `u.box` name the same object, by the comonad law
      `extract ∘ dup = id`. T alone and 4 alone have no such coincidence.
      - *Rejected: no `here` directly after `keep`* (collapse `p.keep.box ↦ p.box`). Names become
        unique, but a view still has both `u.box` and `u.keep` as entries, and the syntax now
        identifies one with the other read here. Soundness then fails for arbitrary environments
        on view contexts, which are presented. In `Γ = (x : □A).boxIn`, `T_box` derives
        `□P(x.keep.box) ⊢ P(x.box)`; an environment giving `x.box` and `x.keep` unrelated values
        falsifies it on a one-world reflexive frame. Rescuing it would restrict validity to
        "coherent" environments.
      - *Rejected: an equational rule.* It would have to be stated from outside the view,
        `□(u.keep.here = u.box)`, since the unboxed equation has the same counterexample. It adds a
        rule and gives up normal forms.
      - **Principle adopted:** names are unique *and the entries of every view are independent*.
        Anything derivable from other entries is notation (a smart constructor), not an entry.
    - **Implemented: under T + 4 a view shows only kept objects.** `ModalSys.keepOnly := T ∧ Four`.
      - `Ctx.boxIn` has no `u.box` entries under `keepOnly`; the contents of `u` are `u.keep.here`.
        The smart constructor `VarSymb.inner u` is `u.box` or `u.keep.here`. `Term.eta`, `Ann.eta`
        and `SubE.unbox` use it, and `Ctx.ref_inner` gives `u.inner : A` in the view for `u : □A`.
      - Collapse and shift are unchanged: `u.keep.here` collapses to `u.here` and shifts to
        `u.keep.keep.here` (`VarSymb.inner_collapse_zero/succ`, `inner_shift_zero/succ`).
      - Semantics: `Env.ref_inner` (the pushed environment at `u.inner` holds `u` evaluated at the
        accessible world; under `keepOnly` by `necDup_eval`).
      - Lemmas about `box` entries (`idxAlong_unbox`, `unbox_comp`, `ref_boxIn_of`) take
        `keepOnly = false`, which any visible `box` entry provides (`Ctx.boxIn_box`).
      - Environments and substitutions need no side condition; soundness and completeness keep
        their statements. All v12m files build; axioms `propext`, `Classical.choice`,
        `Quot.sound`.
      - The issue should recur for B and 5: a singleton view returns to an earlier world, so which
        entries are redundant depends on the view, not only on the flags. Decide per flag when it
        is designed, with boxed equations as the fallback.
- **Strong (outward): lift `Pos(v) → Pos(w)`.**
  - Rule, matching the path condition "for `x : ◇◇A` and `v ∈ ext(x)`, the lift of `cont(x)(v)`
    is in `Pos(w)`": `◇_x ◇_{x.dia} θ ⊢ ∃z:◇A. ◇_z θ(z.dia)`. Sound.
  - **Open.** No link without strong 5: `w`'s `◇`-items are invisible at `v`, and `v`'s objects are
    invisible at `w`.
  - Naming a join `◇◇A → ◇A` fails with world extents (overlapping inner extents disagree), and
    with world-*path* extents (concatenation loses the split point). It would need extents that
    record nested hop structure, a substantial redesign of `Pos`.
  - Omitting the lift is coherent: it is a comprehension principle, like the export
    `◇_x ∃y. φ(y) ⊢ ∃x'. ◇_{x'} φ(x'.dia)`, which K also lacks. Plain `◇◇φ → ◇φ` still holds.

### B (symmetry)
- Frame: `v R w` for `v ∈ R(w)`.
- **Strong (inward, named): singletons at the origin `D(w) → Pos(v)`.**
  - Context principle: inside a modality, current items `z : A` are visible as singleton addresses
    `z↑ : ◇A` with extent `{w}`. The address-level form is still to be designed.
  - Round trips must reduce: going out along `u↑` and back along `y↑` normalises to `u.box`. This
    is needed for parameterised instances of the ◇-BF derivation (§5).
  - Rules: `φ(z) ⊢ □◇_{z↑} φ(z↑.dia)` and `◇◇_{z↑} φ ⊢ φ(z)` (and the `□_{z↑}` forms).
- **Weak (outward): value at the origin `Nec(v) → D(w)`.**
  - Forced by the frame (`necEval` lands in `Dom A w`), so canonical symmetry needs it.
  - Rule: closed `B` (`ψ ⊢ □◇ψ`). The parameter-free export `◇∃u:□A. □φ(u.box) ⊢ ∃a:A. φ(a)` is
    derivable from it *(sketch)*.
  - **Open alone.** Its link is strong B's singleton, `◇_{a↑}(a↑.dia = u.box)`.

### 5 (euclidean)
- Frame: `R(w) ⊆ R(v)` for `v ∈ R(w)`.
- **Strong (inward, named): `Pos(w) → Pos(v)`.** Context principle: `◇`-items stay visible inside
  `□` (and inside `◇_y`). Rule: `◇_x φ ⊢ □◇_x φ`.
- **Weak (outward): restriction `Nec(v) → Nec(w)`.** Rule: `◇φ ⊢ □◇φ`; with free `□`-parameters it
  is only statable when 4's visibility is present. The carrier principle that completeness needs
  is the existential `◇∃c:□B. □χ(c.box) ⊢ ∃c:□B. □χ(c.box)` (§2a). **Open without 4**; with 4
  the link is `□(c.box = u.box)`.
- The two halves are contrapositive-paired with the slogans the other way round from 4 (§2a):
  "possible ⇒ necessarily possible" with its witness kept is the named half; "possibly necessary ⇒
  necessary" for objects born inside is the existential half.

### □-BF and ◇-BF
Base variables are invisible under `□`, so each Barcan formula pairs a concept quantifier outside
with a base quantifier inside.

| | Rule | Status |
|---|---|---|
| □-CBF | `□∀y:A. φ(y) ⊢ ∀x:□A. □φ(x.box)` | K theorem (`ConverseBarcan_v12`) |
| ◇-CBF | `∃x:◇A. ◇_x φ(x.dia) ⊢ ◇∃y:A. φ(y)` | K theorem |
| □-BF | `∀x:□A. □φ(x.box) ⊢ □∀y:A. φ(y)` | flag; necessary objects at `w` cover each successor's domain |
| ◇-BF | `◇∃y:A. φ(y) ⊢ ∃x:◇A. ◇_x φ(x.dia)` | flag; possible objects at `w` cover each successor's domain |

- **□-BF** is independent of every flag *(sketch countermodel: two worlds, universal `R`,
  `D(v) = {b₁, b₂}`, one necessary object missing `b₂`, full possible objects)*. It spreads
  non-emptiness. It has a link already in K (all box contents are visible together at a successor),
  so the textbook BF completeness argument should adapt: successors reuse the parent's box contents
  as witnesses.
- **◇-BF** follows from strong B, and from strong T + strong 4, hence from strong S5. Weak flags
  never give it. **Alone it is open**: a successor sits inside only one `◇_x` at a time, so several
  witnesses cannot be linked jointly.

## 4. Combinations

- **Closure.** Formula axioms derive each other (T+5 ⊢ 4, B; B+4 ⊢ 5), but context principles do not.
  A chosen flag set must therefore be closed under what its frame and carrier conditions imply.
  Otherwise the syntax lacks principles its own models validate.
- **Every edge has two levels**: *semantic* (conditions imply conditions) and *syntactic* (rules
  derive rules). A mismatch signals a missing rule or a mis-stated flag. Completeness for each flag
  set is what makes the levels agree.

Known edges *(all sketch)*:

| Edge | Semantic | Syntactic |
|---|---|---|
| strong X ⇒ weak X | by definition | by definition |
| T ⇒ D (weak and strong) | ✓ | strong: `∃`-intro at `unitT` |
| T + 5 ⇒ B, 4 (frames) | ✓ | propositional ✓; object level via closure |
| B + 4 ⇒ 5 (frames) | ✓ | propositional ✓; object level via closure |
| strong T + strong 5 ⇒ strong B, strong 4 | ✓ (symmetry turns 5's inclusion around) | ? |
| strong B ⇒ ◇-BF | ✓ | parameter-free ✓; parameters need round-trip reduction |
| strong T + strong 4 ⇒ ◇-BF | ✓ | ? |
| anything ⇒ □-BF | ✗ (countermodel) | ✗ |

## 5. Expected status of the modal cube

✓ = expected tractable, ✗ = open (no known link), ? = unclear.

| System | weak | strong | Obstacle |
|---|---|---|---|
| K | done | done | |
| KD | ✓ | ✓ | |
| T | ✓ | ✓ | |
| KB | ✗ | ✓ | weak B |
| K4 | ✓ | ✗ | lift |
| K5 | ✗ | ✗ | 5's box half without 4 |
| KD4 | ✓ | ✗ | lift |
| KD5 | ✗ | ✗ | 5's box half without 4 |
| KDB | ✗ | ✓ | weak B |
| KTB | ✗ | ✓ | weak B |
| S4 | ✓ | ✗ | lift |
| KB5 (= KB4) | ? | ✓ | weak B's link without T |
| K45 | ✓ | ✓ | |
| KD45 | ✓ | ✓ | |
| S5 | ✓ | ✓ | weak: B's link via T + 4 + 5's restriction |

Smallest instance of the no-link problem: **weak B** (base values only, no extents). Attack it first
if we try to resolve the open cases.

## 6. Impact by layer

| Layer (K file) | Weak T | Strong T | Weak 4 | Strong B / 5 | Barcan |
|---|---|---|---|---|---|
| Symbols (`Ctx.ref`, `boxIn`, `diaIn`) | `here` projection step | new `Ann` | `□`-items in `boxIn` | new views/addresses | |
| Terms, WFF, `eqRec` | | `unitT`, `eqRec` case | | | |
| Subst (`SubE.proj/unbox/diaBody`, `WFF.subst`) | box projection | collapse | | round trips | |
| Proof | T rule | | 4 rule | B/5 rules | BF rules |
| Model, Interp (`Ops`, `GFunc`) | reflexive, extract | posUnit | transitive, restrict | symmetric/euclidean, inclusions | coverage |
| Canonical (`Acc'`, `extent`) | reflexive up to translation | singleton denotation | transitive | symmetric, Barcan successors | Barcan successors |

Canonical accessibility is the shared redesign.
- Today `Acc'` requires `BoxView`: the child's base context *equals* the parent's view. That is
  never reflexive, symmetric or transitive.
- `BoxContents` already quantifies over arbitrary `Ctx.Le` embeddings. So the planned change is to
  replace view equality by view **inclusion** (or a translation), making `w` its own successor
  under T and making successors compose under 4.
- *For T this was not needed*: the world itself is added to the frame relation beside the proper
  successors (tagged by depth), and denotations at it are computed by collapsing (§3, T). Whether
  4 can use the same trick (adding composites of proper successors) is the next question.

## 7. Implementation plan

- **Fork.** `Ctx.boxIn` sits at the root of the dependency graph, so every downstream file depends
  on it. The generalised development is therefore a full fork, threaded with a parameter
  `S : ModalSys` (flags plus closure). Naming convention: to be decided.
- **Regression check.** With every flag off, the generalised definitions should agree with K,
  definitionally where possible (e.g. `boxInS K Γ = boxIn Γ` by `rfl`), so K results transfer.
- **Order**: each step adds one new kind of difficulty.
  1. Weak T: views, extract, reflexive canonical accessibility.
  2. Weak 4: composition of flags, transitivity.
  3. Strong T: a new canonical form, collapse in substitution.
  4. Strong B: the Barcan-style successor construction.
  5. S5.
  6. D and □-BF along the way.

## 8. Open questions

1. Strong 4 (lift) without strong 5 — and whether it exists at all.
2. Weak B without strong B; weak 5 without 4; ◇-BF alone; KB5 weak.
3. The address-level design of B's singleton addresses and of the round-trip reduction.
4. How closure of flag sets is computed. (Flags are carried by a typeclass `ModalSys`, with
   `ModalSys.K` all flags off.)
5. Later axis: comprehension principles for carriers (modal choice
   `□∃y. φ(y) ⊢ ∃u:□B. □φ(u.box)`, the `◇`-export). They hold in full models only.
6. Other frame conditions (.2, .3, density, functionality) and GL/Grz are out of scope.
7. Flags per component (§2a) or per weak/strong version? Which components are complete alone, and
   which only in bundles (e.g. weak B with strong B)? Are inward-only systems (5's `Pos` map
   without the euclidean schema) complete?
