# QML v12: modal extensions (design)

Status: 2026-09-19. **Weak and strong D, weak and strong T, and weak 4 are implemented**, with
soundness *and* completeness for every combination of the flags; files `QML/QML_v12m_*.lean`,
namespace `V12M`.
`V12M.completeness` and `V12M.provable_iff_valid` now hold under a bare `[ModalSys]`: the scaffold
`ModalSys.NoTStrong` has been **removed**, and `QML_v12m_*` as a whole contains no `sorry` and
builds without warnings. Everything else is design. Claims marked *(sketch)* come from paper
arguments that have not been checked in Lean.

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

**⭐Weak and strong: whether new objects are required (2026-09-19).** A **weak** component requires
no new objects: it is purely propositional, or it uses *determinate maps on existing objects*
(evaluation here, `u.here`; restriction down chains, `u.keep`; value at the origin). A **strong**
component asserts that objects exist which no existing object determines — which is why strong
components come out existential in the syntax.

| Flag | weak (no new objects) | strong (new objects) |
|---|---|---|
| D | propositional `□⊥ ⊢ ⊥` | a possible object with nonempty extent |
| T | evaluation here (`u.here`) | a possible object for each object, realised here (`T_dia`); *also* a necessary object for each object (§3 T, candidate) |
| 4 | restriction down chains (`u.keep`) | the lift `Pos(v) → Pos(w)`: no determinate join |
| B | propositional `φ ⊢ □◇φ`, with the value at the origin | two: a `□□`-object with a constant round trip, and possible objects reaching back (§3 B) |
| 5 | *to be re-sorted*: both components below are determinate maps | ? |

This replaces the earlier rule, "the `Nec`-side component is weak and the `Pos`-side strong". The
two agree on T, D and 4. For B the new rule makes the outward half and propositional B weak, and
finds two strong components rather than one. For **5** both components in the components table above
are determinate — restriction `Nec(v) → Nec(w)`, and re-use of a witness `Pos(w) → Pos(v)` — so by this
criterion both are *weak*, and a strong 5 would be something else, or nothing. That affects the S5
plan and has to be settled before 5 is designed.

*Superseded (to 2026-09-18):* the weak/strong labels of §3 put the `Nec`-side component in *weak*
and add the `Pos`-side component in *strong*. For 4 the weak component is the named one. For B and
5 it is the existential one, so the nesting weak ⊂ strong puts the open part inside strong B and
strong 5.

### 2b. How to state a carrier map *(2026-09-18, after strong T)*

**Nameable is not the same as named.** The classification above says *where* an object lives, and
that settles whether an existential is **forced**: an object born at an inner world cannot be named
from outside. It does **not** settle how the carrier map is *written*. Strong T is the worked case:
its object `t` lives at the outer world and is pushed inward (to `w` itself), so by the criterion
above it is nameable — and it shipped as an **existential** anyway, `T_dia` with a Henkin witness
and `posRet_exists` as the carrier condition, the canonical model naming the realisation as *data
on `World`* (`real`) rather than as a syntactic address.

That was a cost decision, and the costs apply to every remaining axiom. A new address former must
be stable under `mono`, `collapse`, `shift` and `subst`, and must keep view entries independent —
weak 4's single `keep` step is what forced the whole `keepOnly` redesign. An existential needs no
new address: it reuses `∃`, a Henkin constant, and a carrier condition of `posRet_exists` shape,
all of which now have a worked precedent. A new *term* former is dearer still **in the syntax**:
new cases in `Term.mono`, `collapse`, `shift`, `subst`, `rden`, `interp`, `size` and every
congruence lemma. It can repay that in the canonical model, though, so this is a default and not a
rule — see the term-former option kept open under §3 T.
**So the default is: state a carrier map existentially, and let the canonical model name the
witness as data.**

**⭐What decides the form: scope inside the witness's view.** A carrier map relates a source object
to an asserted target. To state that relation as an **equation** — the strongest and most useful
form — both sides must be in scope in one context, and for a possible object `x` that context can
only be `Γ.diaIn x`, since `x.dia` exists nowhere else. What is in scope there is exactly `x.dia`
together with `Γ.boxIn`, and `Γ.boxIn` consists of exactly `.step u .box` and `.step u .keep`
(`Ctx.le_boxIn_diaIn`; every root case is absurd). Hence:

> **The equation form is available exactly when the source object is a `□`-item and its type is
> `◇`-free.** Base items of `Γ` do not survive into the view; and equality at a `◇`-type compares
> two possible objects only on one shared witness (`eqRec` needs equal annotations, and `Ann.eta`
> records the witness), so it cannot compare an object reached through one witness with one reached
> through another. *(The type condition added 2026-09-19, found implementing strong D.)*

**When the source is in scope, the schema pins its own witness.** A schema
`□φ(u.box) ⊢ ∃x. ◇_x φ(x.dia)` whose `φ` may mention `u.box` has the instance
`φ(z) := (z = u.box)`, which is the equation form, and so a witness uniform in every formula and
parameter. The per-formula weakness of a schema — the reason strong T needed its parameter, its
Henkin form and the packing — arises only when the source is **out of** scope. *(2026-09-19; an
earlier note under §3 D rejected D's schema as too weak, wrongly.)*

Note what the obstruction is *not*. The content of a possible object is perfectly available inside
the view — it is `x.dia`. The problem is that the thing one wants to compare it against has left
scope. It is a scope problem, not a missing elimination form. Three routes follow, and the
criterion says which are *available*, not which is cheapest:

| Route | When | Cost | Instances |
|---|---|---|---|
| **Same witness**, nothing to compare | the identical `◇`-object is asserted at the new world | extends the view with `◇`-items — the expensive named route | strong 5 (`◇_x φ ⊢ □◇_x φ`) |
| **Equation** | source is a `□`-item, so both sides are in scope | uniform witness, no new entries | the `Nec→Pos` map of §3 D (derived there from a closed axiom via `strength`) |
| **Schematic** (forced) | source is a base object of `Γ`, or a possible object's content | `realiseAt`-style substitution; constrains the content only through view-expressible `φ` | strong T *(done)*, strong B inward, strong 4's lift |

**Two consequences worth acting on.**
- **Strong B's inward half is schematic, with strong T.** Its source is `a ∈ D(w)`, a base object,
  and the comparison would sit in `v`'s view two steps out, where `Γ`'s roots are gone. So B
  inherits not only `realiseAt`'s recipe but its **compensation**: because the syntax
  underdetermines the content, the canonical world must *name* the realisation as data, a
  `World.real` analogue. That was the most surprising thing about strong T — it is why
  `Classical.choice` was not enough for `posRet_exists` — and it is not a T-specific hack but the
  standing price of the schematic route. Plan for it at the start of B, not at the `posRet_exists`
  stage.
- **Strong 4's lift is open for a different reason from "hard".** It is schematic too, but the
  compensation is unavailable: naming it as data would need `Pos` to hold something it cannot,
  extents recording nested hop structure. So "schematic, hard, done" (strong T) and "schematic, and
  the carrier cannot hold the witness" (4's lift) are different failures, recorded as one
  undifferentiated "no link" in §5. Only the second is evidence that the principle may not exist.

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

## 2c. From propositional rules to object-level maps *(2026-09-25, paper)*

The object-level principles are the propositional ones read as **maps between carriers, in the same
direction as the implication**.  Enumerating them systematically says how many variants a flag has,
which are free, and — in two cases — why a principle cannot be stated at all.

**Axis 1: duality.**  Each propositional rule can be written two ways (§2a); some are self-dual.
Each way gives one map:

| Flag | propositional | object-level map | grade and status |
|---|---|---|---|
| T | `□φ → φ` | `□A → A` | function: `necExtract` *(done, weak)* |
| | `φ → ◇φ` | `A → ◇A` | existence: `posRet_exists` *(done, strong T)*; named: `Here` (§3 T) |
| D | `□φ → ◇φ` *(self-dual)* | `□A → ◇A` | existence at `𝟙` + strength: `D_ex` *(done, strong D)* |
| 4 | `□φ → □□φ` | `□A → □□A` | function: `necDup` *(done, weak)* |
| | `◇◇φ → ◇φ` | `◇◇A → ◇A` | **missing** — the join; see §3 4 |
| B | `φ → □◇φ` | `A → □◇A` | (ii) gathered, carrier `□◇A` |
| | `◇□φ → φ` | `◇□A → A` | (i)'s inward dual; named: `Back` (§3 B) |
| 5 | `◇φ → □◇φ` | `◇A → □◇A` | function (determinate transport) |
| | `◇□φ → □φ` | `◇□A → □A` | existence: §3 5's carrier principle |

So D, being self-dual, has **one** object-level map — which is why it was the cheapest flag. T, 4, B
and 5 have two each, and they are not interderivable: they concern different carriers.

**Axis 2: grade.**  Each map can be asserted at three strengths, and which is appropriate depends on
whether the value is **canonically determined**:

| grade | form | when |
|---|---|---|
| function | an `Ops` field with an evaluation law | the value is determinate — evaluate at the identity arrow (T), at the composite (4) |
| relation | a primitive naming the value, choice-free | the value exists but is not canonical: `Here`, `Back` |
| existence | `∃` in the object language | only that *some* value exists: `D_ex`, `posRet_exists`, 5's carrier principle |

This is not a free choice.  `necExtract` and `necDup` are functions because their arrows are
canonical; strong D, strong T and 5's outward half are existential because theirs are not.  The
relation grade sits between: it pins one value without choosing a canonical one, which is what makes
`Here` and `Back` an improvement on their per-formula predecessors (§3 T, §3 B).

**Axis 3: witnessed or not.**  Each `◇` in a map may range over all arrows or over a named object's
extent, so an `n`-diamond map has up to `2ⁿ` variants, with the carrier changing accordingly (§3 B
tabulates B's four).  §2a's "decorating the operators does not generate new principles" holds
**propositionally**, where the decorated forms follow by `□ψ ⊢ □_x ψ` and `◇_x φ ⊢ ◇φ`.  At the object
level it fails, because the carrier's type is part of the principle: witnessing a `∀` leg weakens,
witnessing an `∃` leg strengthens.

**⭐Axis 4: can it be named at all?  Names travel inward.**  A context principle adds names to
*inner* contexts (`u.keep` inside `Γ.boxIn`; `x` staying visible under `□`).  Nothing adds an inner
object's name to the outer context.  So:

| map | direction | statable as |
|---|---|---|
| weak 4, `Nec(w) → Nec(v)` | inward | context principle (`keep`) ✓ |
| 5's `Pos(w) → Pos(v)` | inward | context principle (`◇`-items stay visible) ✓ |
| T's `A → ◇A`, B's round trip | **returns to the origin** | a relation at `w`, both arguments in scope ✓ |
| 4's lift `Nec(v) → Nec(w)` | outward, no return | ✗ — but by **quantifier order**, not scope: see below |
| 4's `Pos(v) → Pos(w)` | outward, no return | ✗ per arrow; gathering gives the join, at a cost (§3 4) |
| 5's `Nec(v) → Nec(w)` | outward, no return | ✗ pinned; hence its existential carrier principle |

This subsumes the earlier "the pinned form is statable exactly when the route returns to the origin":
a returning route is what puts a modal object and a local object in one scope.  It also explains the
open status of 4's lift and of 5's outward half structurally, rather than as a difficulty of proof.

**Correction (2026-09-25): 4's lift is blocked by quantifier order, not by scope.**  Inside the view
`m.keep` names `m`'s restriction and an object `n` of `v` is in scope too, so the relation "`m`
restricted is `n`" *is* statable there.  What fails is the nesting: `n` ranges inside `□` and `m` must
be found outside, so the principle needs `∃m` outside a `∀n` inside — the `□∀ ⊢ ∃□` swap, modal
choice.  One gets either `∃m. □∀n. (…)`, which is far too strong (one `m` for every `v` and every
`n`), or the schematic form §2b records.  5's outward half is blocked differently, by scope proper.
So the two open cases are open for different reasons.

**Axis 5: surjectivity or injectivity.**  Each free map has two natural strengthenings, and they are
two different kinds of principle:

| strengthening | what it asserts | kind |
|---|---|---|
| **surjective** | every object at the target comes from one at the source | existence — the **strong** principle |
| **injective** | the map loses nothing, so the source embeds in the target | no new objects — an **extensionality / converse** principle |

Surjectivity gives the strong flags; injectivity gives the **converse axioms**, with their own frame
conditions *(paper)*:

| free map | surjective | injective |
|---|---|---|
| T's `necExtract : Nec A w → Dom A w` | NecT: every object is some necessary object's value here | `φ → □φ`, i.e. `R(w) ⊆ {w}` — T's converse |
| 4's restriction `Nec A w → Nec A v` | **the lift = strong 4**: no *new* necessary objects deeper | **density** `□□φ → □φ` (`R ⊆ R∘R`) — 4's converse, and what makes the `□`-domains **grow** |
| 4's transport `Pos A v → Pos A w` | every possible object here comes from a successor — not wanted | the `◇`-domains **shrink** going deeper; automatic in a relational frame, and in an arrow frame when composition is injective |

So "the `□`-domains grow and the `◇`-domains shrink" is exactly *injectivity* of the two maps of 4 —
free on the `◇` side, and on the `□` side the extra condition of density.  Note that the lift, being
surjectivity of the restriction, says the `□`-domains do **not** grow: `Nec A v` is then precisely the
image.  So the lift and the growth expectation pull in opposite directions, and 4 with both is
`R = R∘R`.

**A consequence worth following up.** D's rejected graph form
`∀u:□A. ∃x:◇A. ◇_x(x.dia = u.box)` (§2b) was rejected because object-language equality at `◇`-types
is witness-relative, so it typechecks only at `◇`-free types.  At the **relation** grade — "`x`'s
content along its route is `u`'s value there" — it escapes that, since the relation's semantics uses
equality in the model, as `Here` and `Back` do.  Whether that makes §8.5's comprehension flag worth
revisiting is open.

## 2d. The `◇`-types have quantification but no equality *(2026-09-25)*

**The defect.**  `Ann.dia` carries a witness, so an *annotated* `◇`-type is a fibre: `Ann (.VTypeDia
A)` is `.dia x a`, indexed by `x`.  `eqRec`'s `◇` clause is `.boxx x hx (eqRec A t s)` and needs both
sides to carry the **same** annotation, so it is equality *within* the fibre over `x`.  There is no
`Term.var` at `◇`-type, so a `◇`-typed variable appears only as a witness index or as its own
η-expansion, whose annotation is its own address.  Meanwhile `all_elim`/`ex_intro` instantiate at
terms of any annotation, so quantifiers range over all of `Pos A w`.  **Quantification separates
more than equality can.**  This is §2b's witness-relative equality problem stated as a defect of the
type rather than of a proof, and it is what blocks compound `Here` at `◇`-content (§3 T), `pair_elim`
in the equality reform, and the inward statements of 4's join and strong B's `Back`, each of which
has to say "that possible object is this one".

**What the fibre-wise equality already gets right.**  `eqRec (.VTypeDia A) (diatm x bd) (diatm x bd')`
is `□_x (eqRec A bd bd')`, and `□_x ⊥ ⊢ □_x ψ` for every `ψ` by monotonicity of `◇_x` (`K_dia` with
empty hypothesis lists; or explosion inside the view, then `K_dia`).  So an empty witness already
identifies all of *its own* terms, derivably, with no new machinery.  The cross-fibre rule below is
that same fact one level up: it says the fibres over two empty witnesses are one fibre.

**The proposal: a primitive `≐` on witnesses.**  Introduction is **reflexivity** (`⊢ x ≐ x`, matching
`eq_intro`); elimination is **Leibniz**, and substituting `y` for `x` as a witness index inside a
view *is* a renaming, so the `Subst`/`renameRoot` machinery already does it — modulo the usual
Σ-bookkeeping, since annotations mention the witness.  Symmetry and transitivity follow as for base
equality.

**Implemented: the syntax, the rules, soundness and substitution (2026-09-25).**

* ⭐`WFF.diaEq`: two `◇`-terms of the same **type**, annotations free to differ.  Its subjects are
  *terms*, not addresses — the same lesson as `WFF.here`: a substitution sends a `◇`-typed address to
  a `◇`-term, so an address-level equality would not survive substitution.  `WFF.diaEq_congr` and
  `diaEq_congr'` are the congruence helpers (Σ-valued and plain), and the ~20 recursions over `WFF`
  each take one line, exactly as for `here`.
* Semantics: `sat env (diaEq s s') := interp env s = interp env s'`, so `≐` *is* equality in the
  carrier — which is what reflexivity plus Leibniz force anyway (a reflexive relation inside the
  diagonal is the diagonal).
* Rules, mirroring `eq_intro`/`eq_elim` exactly: ⭐`Proof.diaEq_intro` (`⊢ s ≐ s`) and
  ⭐`Proof.diaEq_elim` (Leibniz through a hole formula `φ : WFF σ (Γ.insert (.bnd 0) (◇A)) 1`).  The
  hole takes a term of **any** annotation, which is the whole point: `WFF.instantiate` was already
  annotation-blind, so Leibniz across witnesses needs no new substitution machinery.  Symmetry and
  transitivity follow as for base equality.
* Soundness is two lines each (`rfl`; `sat_instantiate` with the equality rewritten), and
  `Proof.subst` follows `eq_elim`'s case verbatim with `.VTypeDia A` in place of `.Var`, so
  `Proof.mono` comes free.

**Still to do for the package:** the canonical model — the extent taken up to provable `≐`, the
congruences that the content function is well defined on that union, the `¬HereOnly` construction
trigger, and the two degenerate right-rules (which are needed only for the truth lemma, not for
soundness).  The truth lemma's `diaEq` case is the one hole this adds, alongside `here`'s.

**The model half, started (2026-09-26).**  In the canonical model the relation is between
**addresses**, since a comparison across witnesses is what it is for: ⭐`Canon.World.PEq w i hx hy`
says `η x ≐ η y` is in the world's theory at stage `i` (`QML_v12m_CanonDiaEq.lean`).  It is an
equivalence relation on the `◇`-typed addresses of a stage (`PEq.refl`, `PEq.symm`, `PEq.trans`, from
`diaEq_intro` and the derived `eqRec_symm`/`eqRec_trans` plus closure of a maximal consistent
theory), and it does not depend on the stage it is read at (`PEq.lift`, `PEq.of_lift`, by
`Term.mono_eta`).  `World.mem_lift` and `World.mem_of_provable` moved up from `QML_v12m_CanonDom` so
that this file precedes `rden`, which is where the extent is consumed.

The renaming, the extent and the transfer are done (2026-09-26).  `Canon.extent` is not a syntactic
tagging but the *semantic* condition `DiaView x w w' ∧ BoxxContents x w w'`, and of the two only
`DiaView` — the child's language *being* the `x`-view — is tied to the name.  So a child tagged `y`
can serve `x`, at the price of reading an `x`-view body in the `y`-view; that reading is a renaming
of the content address, and it needed no new recursion family:

* `QML_v12m_ViewRen.lean`: ⭐`VarSymb.reView x y` (the prefix `x.dia` becomes `y.dia`, with
  `reView_ext_dia` below the prefix and `reView_eq_self` elsewhere), ⭐`Subst.viewRen` with its `Ok`
  and `Coh`, and ⭐`Term.reView` / `WFF.reView` as `Term.subst` / `WFF.subst` along it, with the
  self-renaming laws.  `Coh` needs `Ctx.ViewClean Γ x` — nothing under the symbol `x.dia` is declared
  in the outer context — since otherwise one symbol would be both the view's content and a
  `□`-component and no address map could serve both.  Discharging `ViewClean` for the canonical
  model's contexts is the one obligation left open here.
* `QML_v12m_CanonDiaEq.lean`: ⭐`World.PEqW` (the identification read at whatever stage declares both
  addresses, an equivalence relation, stage-free because `rden` must be), ⭐`extentUpTo` with
  ⭐`extentUpTo_congr` (identified addresses have *one* extent) and the reading lemmas
  (`extentUpTo_proper`/`_self`/`_le`, each handing back the tag), and ⭐`DiaView.inj`: a child has only
  **one** tag, which is what makes the content function on the union well defined — no choice, no
  independence side condition.
* `QML_v12m_ViewEq.lean`: ⭐`WFF.reViewSlot` (the body of Leibniz's hole formula: `φ` read in the
  *slot's* view one depth up, in a single substitution, since `WFF.subst` may change the depth),
  ⭐`WFF.instantiate_reViewSlot` (filling the slot with `η z` gives `φ` read in the `z`-view — two
  substitutions collapsing by `WFF.subst_comp`, the composite agreeing with the renaming up to η:
  `.tm (η (z.dia))` against `.ren (z.dia)`, which is `SubE.Sim.eta_ren`), and ⭐`Proof.boxx_reView`,
  **the transfer**: `x ≐ y, □_x φ ⊢ □_y (φ read in the y-view)`.  Its theory-level form is
  ⭐`World.boxx_mem_reView`.

**Flatness: `Ctx.ViewClean` discharged (2026-09-27).**  The renaming's side condition is now a theorem
about the contexts the model uses, not a hypothesis to carry.  The clean formulation is
⭐`Ctx.LevelFlat`: *no declared address sits strictly below a declared one along a level step*
(`box`, `dia`, `keep`).  It implies cleanliness at every declared `◇`-address
(⭐`Ctx.LevelFlat.viewClean`) — a box-visible address is a level step below something declared, so
either it lies below `x.dia`, or `x` lies below it, and flatness forbids both.

* Address combinatorics (`QML_v12m_ViewRen.lean`): `VarSymb.eq_of_path` (an address is its root plus
  its steps), `VarSymb.ext_dichotomy` (two addresses with a common extension are prefix-comparable),
  and the splitting layer `AllProj` / `exists_split_last` / `split_unique` / ⭐`VarSymb.split_eq` — a
  level step followed by projections is written that way only once.  That last one is what makes the
  propagation arguments short.
* Propagation: ⭐`Ctx.LevelFlat.view` (a view of a flat context is flat, given only that its entries
  are level steps below declared addresses and that it declares no root), hence `.boxIn` and
  `.diaIn`; and `.insert` for a **fresh** root, hence ⭐`Ctx.LevelFlat.stage`.  In
  `QML_v12m_ViewFlat.lean`: ⭐`WorldLang.flatCtx`, so every stage context of every world language is
  flat and the renaming is available at each of its `◇`-addresses.
* ⭐**Non-shadowing is part of being presented (2026-09-26).**  `Ctx.Presented` now carries a third
  field, `fresh : expr.Fresh`, where `CtxExpr.Fresh` is *the* non-shadowing condition: each
  declaration's name unused in its own prefix.  That is the locally nameless discipline's own
  obligation on the user and the only one, so it belongs to what "presented" means rather than
  travelling as a side condition.  ⭐`Ctx.Presented.levelFlat` then derives `Ctx.LevelFlat` from the
  instance, `WorldLang.flatCtx` reads it off at every stage, and **nothing states flatness**: the
  `flat` field of `Canon.World` is gone, `World.ofHenkin` no longer asks for it, and ⭐`completeness`,
  `provable_iff_valid`, `model_existence`, `strong_completeness` and `compactness` need only
  `[Γ.Presented]`.
  * The cost is that declaring a name is no longer an unconditional instance:
    `Ctx.Presented.insertFree` takes the rule's own freshness side condition, and the one instance
    left covers the eigenvariable pattern `Γ.insert (.free (Ctx.Presented.bound Γ)) T`.  Every site
    that declares a variable already had the freshness proof one line away —
    `Ctx.stagePresented` (from `ρ_inj` and `WorldLang.fresh`), `WorldLang.presL` (from
    `ctxL_fresh`), `BArrow.presented_ctxOf` (from `ctxOf_fresh`), `Chain.insertRoot`,
    `Ctx.presentedOfDecls` (from distinct names, so `by decide`).  `Ctx.Presented.fresh` is now the
    field, so the name-generation lemma is `Ctx.Presented.fresh_bound`.
  * The arrow track takes a presentation apart constructor by constructor, so it needs one thing
    more: each view at a declared witness, `CtxExpr.Views`.  That is not a freshness condition — it
    is the `◇`-rule's own side condition — and `CtxExpr.Wf = Fresh ∧ Views` is what
    `completenessB_presented`, `model_existenceB`, `strong_completenessB` and `compactnessB` ask
    for.  The staged track never takes a presentation apart, so it asks for nothing.
  * `Ctx.LevelFlat` survives as the internal notion (it is what `Ctx.ViewClean`, hence `rden`,
    actually needs) and is genuinely weaker than non-shadowing: shadowing can be harmless —
    `(empty.insertFree 0 (□Var)).boxIn.insertFree 0 (◇Var)` is not flat, yet its only `◇`-address has
    an empty `.dia`-subtree, so `Ctx.ViewClean` holds there and the renaming exists.  Nobody needs
    that generality, and no one has to know it exists.
* ⭐`Term.reView_mono`: the renaming commutes with weakening (every entry is a renaming), which is
  what will make `rden`'s reading of a `◇`-body independent of the stage it is read at.

**The tagged reading is in the model (2026-09-27).**  `Canon.extent` now *is* the union — its proper
part, at least — and everything below the truth lemma has been carried through it.  What a member of
an extent hands back is its **tag** (`tagOf`, `peqw_tagOf`, `diaView_tagOf`, `boxxContents_tagOf`),
and a body written in the `x`-view is read there renamed:

* ⭐`tagBody` (terms) and ⭐`tagWFF` (formulas): move to a stage declaring both witnesses
  (`World.PEqW.st`, with `refXs`/`refYs`/`clean` reading off the declarations and cleanliness there)
  and rename along `x ↦ y`.  Laws: `tagBody_mono`, ⭐`tagBody_stage` (the stage move, via
  `Term.reView_mono`), `tagBody_pair`, ⭐`tagBody_mono_boxIn` (the `□`-part is untouched — the
  renaming only moves the content address, `Term.reView_mono_boxIn`), and `applyG_tagBody` (the
  function algebra commutes, both being substitutions).
* `rden`'s `.diatm` clause reads the body through `tagBody`; `rden_diatm_acc`/`acc'` hand back the
  tag, and stage-independence is ⭐`rden_tagBody_congr` with `rden_realisedTerm_congr` beside it
  (both taking `rden_congr`'s induction hypothesis at the body's type as a parameter, as
  `interp_box_far` does).
* ⭐`diaPush_agree_canon` is the semantic side: pushing the canonical environment into `◇_x` agrees
  with the successor's *read through the renaming* — `Model.substEnv` of `Subst.viewRen`.  The `◇`
  case of `interp_canon` then goes `Model.interp_mono` → `Model.interp_subst` → `Term.mono_subst` →
  the induction hypothesis, and the truth lemma's `dia` case goes the same way with `Model.sat_mono`
  → `Model.sat_subst` → `WFF.mono_subst`.  Its `→` half moves the `□_x` fact to the tag with
  ⭐`World.boxx_mem_reView` and reads it off `BoxxContents`; its `←` half builds an `x`-tagged child
  (`exists_dia`) and uses `DiaView.inj` plus ⭐`mem_tagWFF_of_tag_eq` to see that the renaming is
  then the identity.
* Supporting: ⭐`Subst.isRen_viewRen` and ⭐`Term.reView_eta_dia` (the renaming sends the content
  address's η-expansion to the tag's), which is what makes the environment agreement come out.

**The self part stays un-unioned, and that is entangled with `Here`.**  `World.real` is chosen by the
Henkin chain's `IsRet` bookkeeping, so realisedness is not invariant under `≐`: if the self part were
unioned, the content at the world itself would be *a* realised address's realising term, and its
independence of that choice is not available.  So `extent`'s self clause is still `w.Realised x`, and
`extent_congr` takes the invariance as a hypothesis (`w.Realised x ↔ w.Realised y`).  That hypothesis
is exactly what the **`Here`-driven `real`** of §3 T delivers — from `Here x t` and `x ≐ y`, Leibniz
gives `Here y t` — so the `diaEq` truth lemma needs Stage 3 first.  The order that falls out:
proper-part union (done) → naming at `◇`-types → `real` from `Here` (Stage 3) → self-part union →
both truth-lemma cases.

What remains for the `diaEq` case, then: Stage 3, then the self part, then the `⟹` direction's
collision analysis below — the `¬HereOnly` construction trigger and the two degenerate right-rules.

**`eqRec` is now annotation-free at every type (done, 2026-09-25).**  `eqRec T t s` takes two terms
sharing only their *type*: `Var` and `𝟙` as before, `×` componentwise, `□` inside a `□`, and `◇` the
primitive `diaEq` (`eqRec_dia`).  This is why the reform reaches so far: an annotation of a fixed
type varies only in its `.dia` indices, so annotation-freeness at `◇` *is* annotation-freeness
everywhere.  `sat_eqRec` became annotation-free with it (its `◇` case is definitional), and
`eqRec_refl`/`eqRec_symm`/`eqRec_trans` hold at any two or three annotations.

### What the reform unblocks *(2026-09-25)*

Each of these was blocked by the same thing — an equation whose two sides have different witnesses —
and each is now at least *statable*.  They are things to do, in roughly this order.

1. **Naming by an address, at every type.**  `eqRec A (Term.eta b A hb) t` — "the fresh constant `b`
   denotes `t`" — now typechecks at *every* `A`, where before only flat types took it.  Its semantics
   is right (`interp_eta` makes it `env.ref b = interp t`), and consistency for fresh `b` is the
   standard argument: were `T ∪ {b = t}` inconsistent, generalisation gives `T ⊢ ∀z:A. ¬(z = t)` —
   whose hole formula is itself an annotation-free equation — and instantiating at `t` contradicts
   `eqRec_refl`.  **But it is not what strong T needs**, and route γ should not be revived on the
   strength of it: naming is only *semantically faithful* when the canonical model identifies the two
   denotations, `rden (η b) = rden t`, and at `◇`-content that identification is precisely the
   extent-up-to-`≐` work of this section — so γ at compound content would be gated on the model half,
   where §3 T's base-typed route is not gated at all.  What the statability is good for is the items
   below, and any axiom a *user* wants to write naming an object.
2. **Compound `Here` at every content type — done (2026-09-26), and as the *primitive*, not a
   recursion.**  The plan had been to define `hereRec` by recursion on the content type (`Var`
   primitive, `𝟙` the extent condition, `×` componentwise, `□` inside a `□`, `◇` by `diaEq`).  That
   cannot be a definition: at `𝟙` the content carries no information, so the clause is the **extent
   condition alone** — the *reflexive* arrow lies in the extent — and that is expressible only
   *relative to a base term of the view*: `∃a. Here (diatm x hx bd) a` says it for any base-typed
   body `bd`, and a view is the content address plus `Γ.boxIn`, so with no base entry in scope and no
   constant in the signature there is no such `bd`.  `◇_x ⊤` says only that the extent is non-empty,
   and the realisation reading (`□_x χ → realiseAt χ unit`) characterises it only as a schema over
   `χ`.  So the `𝟙` clause has to be primitive, and once one clause is, the honest form is to
   generalise `WFF.here` itself.
   * **The old base-type restriction had two grounds; the second is now an obligation, not a
     refutation.**  The first — the value's own annotation, against an equality that compared only
     like-annotated terms — is exactly what the reform killed.  The second was that *the canonical
     model could not decide* a compound-content `Here`, and that is not discharged: the truth
     lemma's `here` case must now hold at every content type, and its `⟹` half needs model-equality
     of compound objects to imply provable `eqRec` — the same collision analysis `diaEq`'s `⟹` needs
     (`¬HereOnly`, the two degenerate right-rules).  `WFF.diaEq` has been primitive at every type
     since the reform, so that obligation was already taken on; generalising `here` adds instances of
     it, not a new kind.  If the collision analysis were to fail at some type, both would be hit
     together.
   * ⭐`WFF.here` now takes `{A : VarType} {b : Ann (.VTypeDia A)} {a : Ann A}`, its two sides
     carrying **unrelated** annotations.  `Model.Realised` was always stated at any content type, so
     satisfaction needed no change at all; the whole substitution/collapse/shift stack took the new
     constructor with four one-token fixes, each replacing a base-only lemma by its general (or
     `Sigma`-valued) counterpart.  `WFF.here_congr` now takes a `Sigma` equation on the value side
     too, and `WFF.code` records the type and both annotations, as `diaEq`'s does.
   * ⭐**`Proof.here_fun` at every content type** is what the reform paid for: two realisations of
     one possible object carry unrelated annotations, so the conclusion is `eqRec A t t'`, the
     annotation-free equality.  Sound (`Model.sat_here_fun` via `sat_eqRec`) and substitutable (the
     new ⭐`WFF.subst_eqRec`: substitution commutes with equality at every type).
   * `here_elim` and `here_intro` generalise unchanged — `WFF.viewReadTm`, `WFF.hereRead` and the
     bridge `Model.sat_viewReadTm` were already general in the content type.
   * ⭐`here_beta` is general in the content type **and the value type** (2026-09-26).  Its
     substitution case needed the two term lemmas as `Sigma` equations, since substitution moves the
     hole term's annotation: ⭐`Term.subst_single_tm_sig` (from `Term.subst_comp_sig`, the two
     `Subst.Sim` obligations unchanged), then ⭐`Term.subst_hereRead_sig` (fill the slot, then
     `Term.collapse_subst`) and ⭐`Term.subst_viewReadTm_sig` (fill the slot, then `subst_mono` /
     `mono_subst` and `Term.subst_congr`).  The base-typed forms are now one-line corollaries
     (`eq_of_heq (Sigma.mk.inj …).2`), and the new `sig_subst` moves such an equation under a
     substitution.  `WFF.here_congr` with `sig_diatm` absorbs both sides in the rule's case.
   * The pinned forms `Proof.here_elimAt` and `here_introAt` are general in the content type too —
     every supporting lemma (`WFF.realiseAt`, `diaAbs`, `viewReadAt_diaAbs`, `viewReadTm_eta`) was
     already general, so it was `.Var ↦ A`.  `Canon.spec_of_here` and `RealDatum` stay base-typed,
     instantiating them at `.Var`.
   * ⭐*Nothing introduces a `Here`, and that is a hole in the **outward** rule (tested
     2026-09-26).*  `here_elim`, `here_intro`, `here_beta`, `here_fun` and both pinned forms each
     *consume* a `Here` premise, so `Here` facts arrive only as hypotheses.  And `T_dia` does not
     supply one: it hands the continuation `WFF.retHyp` — `∀b. ∀y. hereRead t ψ → ◇_c (viewRead ψ)`,
     which is `here_intro`'s conclusion *schematically over the hole formula* — and no finite set of
     schema instances yields the atom, that step being an ω-rule.  So `∃x:◇A. Here x t` is **not
     derivable**.
     * But it is **valid**, at every content type: ⭐`Model.sat_here_ex` proves it straight from
       `Model.posRet_exists`, which says literally that every object has a possible object whose
       extent contains the reflexive arrow and whose content there is that object.
     * And it is not optional.  A realised witness's `RealDatum` makes `Here (η c) t₀` *true* in the
       canonical model, so a theory that lacked the atom would be maximal consistent while the model
       satisfied it, and the truth lemma's `here` case would fail.  **The chain must witness this
       existential** — which is exactly what "`real` driven by `Here`" (§3 T, Stage 3) requires.
     * ⭐*Done (2026-09-27), as a replacement rather than an addition:* `T_dia` takes the single
       hypothesis `Here (η c) t` in place of the `retHyp` schema, its soundness being
       `sat_here_ex`, and each old `retHyp` instance follows from the atom by `here_intro`, so the
       rule is simpler and nothing is lost.  Substitution needed one new device, `Subst.renameTm`:
       the eigenvariable now occurs as a *term*, its η-expansion, and sending it to the new
       eigenvariable's η-expansion makes the entry a **term**, read off pointwise by
       `Term.subst_eta_tm` — `Subst.rename`'s address entry would have wanted the global
       `Subst.IsRen`.  The chain follows: `WorldLang.retSet` is that atom, `Canon.spec_of_here` is
       general in the content type, and ⭐`RealDatum.spec` is a derivation (`retSpec`), which
       retires `spec_of_retHyps` and its `stageSkip` / `laterList` / `retHole` / `packType`
       apparatus along with `WFF.retHyp` and its five transports.
   * ⭐*The componentwise laws: **⟹** done, **⟸** not wanted (2026-09-27).*  ⭐`Proof.here_fst` and
     `Proof.here_snd` are instances of `here_beta` at the hole term built from the slot's own `.fst`
     address (`Term.eta (.step (.root (.bnd 0)) .fst)`), which reads `Here (diatm x bd) t` down to
     its first component.  The substitution machinery does it, the slot's entry being a *term*:
     `Subst.at_single_fst` (a pair entry projects by `SubE.proj`), then
     `Term.viewReadTm_eta_fst` inside the view and `Term.hereRead_eta_fst` here, the latter through
     `Term.collapse_eta` and `Term.subst_eta_tm`; `WFF.here_congr` with `sig_diatm` absorbs the
     `Sigma`s.  A hole term of *compound* value type — so this is what generalising `here_beta`'s
     value type was for.
     * The **⟸** half is not an instance, and is not wanted: nothing introduces a `Here` except
       `T_dia`, so component facts cannot be assembled into one about the pair — and nothing needs
       them to be, since the chain hands over a compound `Here` directly at the witness's full
       content type.
     * The `□` clause would go the same way, with `η (slot.here)` as the hole term: `SubE.proj` of a
       `.tm (.boxtm _)` entry along `.here` is the collapse under T, so the law reads a boxed content
       down to its value here.  It needs a `ref` lemma for the `.here` step of an inserted
       `□`-typed slot.
   * Now statable off base type: strong T's inward `∃x:◇A. Here x t`, and the `≐`-invariance of
     realisedness that the self part of the extent needs (below).
3. **General Leibniz, annotation-free.**  v12m has Leibniz at exactly two places, both primitive
   one-hole rules: `eq_elim` at `.Var`, and `diaEq_elim` at `◇A` for any `A`, annotations free on
   both sides.  There is no v12m principle at arbitrary type — the `QML_v12m_Leibniz*` files hold
   only infrastructure, and `LeibnizSpine`'s header records why: K's proof tracks equalities by
   membership among the hypotheses, which is what carries them under `□` and `◇_x`, and under T the
   `here` component of a necessary entry needs a collapsed equality that T proves but that is not a
   hypothesis.  K's own `V12.Proof.leibniz` is at every type but at a *single* annotation
   (`{a : Ann T} {t s : Term σ Γ T a}`) — exactly the restriction to drop when it is ported.  Two
   routes: recursion on the type from the two primitives, or an annotation-free port of `substEq`.
   The `×` clause of the recursion is the old `pair_elim` difficulty (a formula with one pair-slot
   must become one with two slots), and it is the one old blocker the reform does *not* obviously
   clear.
4. **Saying "that one" elsewhere.**  Strong B's `Back u t` coherence and 4's witnessed join both
   equate a possible object with a given one across witnesses, so both can be stated as equations
   rather than schemas; and `RealDatum`'s content type is no longer forced to be flat.
5. **Quantified identity over `◇A`** — uniqueness claims, "exactly one impossible object", definite
   descriptions — the original complaint of this section, now sayable.

**Which witnesses the canonical model cannot separate.**  Children are *tagged*: each child world is
built by `diaChild x` and its language declares **x's** content root, so a child of `x` lies in `y`'s
extent only when the theory says `x ≐ y`.  Hence witnesses that are indiscernible but not provably
equal still get different extents, and **no general extensionality rule is needed** — the collapse I
first feared does not happen.  Collisions arise exactly where there are no children to tag:

* **empty extent** — and here identification is *correct*: an extensional model has exactly one empty
  possible object, so a rule identifying empty witnesses states a truth rather than patching a
  defect;
* **under T, extent = exactly the identity arrow** with a given content — the **point object**, the
  unit `pt : A → ◇A`.  Note `posRet_exists` only asks for an object whose extent *contains* the
  identity, so the point object need not exist even under strong T.
  * *Two readings to keep apart (asked and answered 2026-09-27).*  The "under T" is **weak** T: it is
    what puts the arrow there at all (`Frame.refl : ModalSys.T = true → ∀ w, R w w`, packaged as
    `Frame.reflAcc`), so without T the shape is not even describable.  And this is **not** the extent
    of a strong T witness: `posRet_exists` asks only `reflAcc ∈ (posEval p).1`, *membership*, and in
    the canonical model a realised witness also picks up a proper child for each `◇_x χ` the theory
    asserts.  The point object is the extreme shape where nothing but the identity arrow is in the
    extent; strong T neither produces one nor needs one.  So the two rows are complementary: empty =
    no children and not realised, point = realised with no *proper* children.  What they share is
    that neither has anything to **tag**, which is what otherwise keeps unequal witnesses apart.

**`HereOnly x t`: the predicate-grade point object** — ⭐*agreed as the design, 2026-09-27.*
"Possible *only* here, with value `t`", the
partner of `Here s t` = "possible here, with value `t`".  A predicate, not a term former, so it
commits to no existence — the same reason `Here` is a predicate and `t_dia` (§3 T) was not taken, and
the same reason strong B's route back is a relation.  Avoid calling it *rigid*: rigidity is sameness
across worlds, which is not this notion; "settled" or "exhausted" are better prose words.  Its
**elimination** is the collapse of possibility onto the realisation, the converse of `here_intro`:

```
HereOnly x t,  ◇_x ψ⟨bd⟩  ⊢  ψ⟨t⟩
```

and it needs **no finitary introduction rule**: the canonical model honours `¬HereOnly x t` by
*building* a proper child for `x`, whose `□_x`-contents are consistent whenever `□_x ⊥ ∉ T`.  That is
the Henkin pattern already in `World` as `exW`/`allW`, so the obligation is discharged by a
construction trigger, not by an ω-rule.

**The two identifications are primitive right-rules, not admissible.**

```
□_x ⊥, □_y ⊥               ⊢ x ≐ y
HereOnly x t, HereOnly y t ⊢ x ≐ y
```

Neither is derivable, and the reason is worth keeping: with `≐` primitive the language gains a new
**leaf**, an `≐`-atom, which no induction on formulas can crack — equality no longer bottoms out at
base type only, since it now bottoms out at `◇`-types too.  There is also a direct independence
argument: read `≐` as *literal identity of witness addresses*; reflexivity holds, Leibniz holds
trivially, every other rule is untouched, and `□_x ⊥, □_y ⊥ ⊢ x ≐ y` fails.  So they are genuine
primitives.  (An earlier draft of this section claimed they were admissible; that was wrong.)

**But they behave, which is what cut elimination needs.**  Read them as *additional right-rules* for
`≐` — reflexivity being the third — and check that each reduces against Leibniz.  From `□_x ⊥`,
`□_y ⊥` and `φ(x)`, derive `φ(y)` by cases on `φ`: a `◇_x ψ` contradicts `□_x ⊥`, so explosion; a
`□_x ψ` has its image provable outright from `□_y ⊥`; `Here`-about-`x` is refutable (`here_intro` at
`ψ := ⊤` gives `◇_x ⊤`); `eqRec`-at-`◇` over `x` *is* a `□_x` form, so as above; and the new leaf
`x ≐ z` is handled by Leibniz on `□_x ⊥`, giving `□_z ⊥`, then the **same rule** on `□_y ⊥`, `□_z ⊥`.
The `HereOnly` version is the same with `◇_x ψ ↔ ψ⟨t⟩` in place of explosion.  Re-applying the rule
is fine for a reduction — it is not an attempt to show the rule redundant, and it is exactly why the
rule cannot be dropped.

Two mitigations are worth recording.  Each rule is **conditional on degenerate premises**, so neither
can act as a general-purpose identity generator.  And the empty one is *forced*: given `pos_inj` the
empty possible object is unique, so rejecting the rule means rejecting that.  The `HereOnly` one, by
contrast, is contingent on the model class — under the multi-loop change below it becomes derivable,
leaving exactly one primitive.

**Rejected: identity as a judgement rather than a proposition.**  The cheapest variant is to identify
witnesses in the *context* (quotienting addresses there) instead of adding a formula.  It is
axiom-free — nothing in the language can deny an identity the model imposes, so both right-rules and
the whole truth-lemma obligation disappear.  But it fails most of what the equality was wanted for:
compound `Here` at `◇`-content needs the identity as a **subformula** of a defined formula, and a
judgement cannot occur inside a formula; `eqRec` is still not total, so the original defect —
quantification without an equality predicate — remains; and quantified identity (uniqueness, "exactly
one impossible object", definite descriptions of possible objects) stays unsayable.  It would serve
only the strong principles, and only in rule shape, by extending the context with an identified
witness in the eigenvariable style `T_dia` already uses.  Cheap because it does much less.

**Canonical-model cost.**  Define the extent *up to provable `≐`* (`w'` is in `x`'s extent when it is
in the extent of some `x'` with `x ≐ x'` in the theory), add the congruences that the content
function is well defined on that union, and add the `¬HereOnly` construction trigger.  **No rebuild
of `diaChild`**: the earlier estimate of "the size of the B canonical model" assumed a quotient
inside the construction and was wrong.


#### ⭐The reform is withdrawn: equality stays inside the fibre *(2026-09-28)*

Everything from here to the end of this section is the record of a decision **reversed**.  The `◇`-type
equality of `7c9fe29` is gone; `eqRec`'s `◇` clause is again `□_x` within one fibre, and `WFF.diaEq`
with `diaEq_intro` / `diaEq_elim` is deleted.  What follows is why, since the reasoning is worth more
than the code that was written for it.

**The reform did two things, and only one of them was ever needed — neither, as it turned out.**  It
made `eqRec` annotation-free, and it made the `◇` clause a primitive atom on arbitrary terms.  The
first looked like the fix for a real defect and is *vacuous*: `Ann T` branches only at `.dia`, so an
annotation of a fixed type carries **nothing but the witness at each `◇` position** — "same
annotation" already *is* "same witness skeleton", and at a `◇`-free type the annotation is unique
(⭐`Ann.eq_of_diaFree`).  The motivating example, comparing the two components of a pair-typed witness
(`diatm p (view.fst)` against `diatm p (view.snd)`), was always statable, since with base-typed
components both annotations are `.dia p .var`.  So the single-annotation index was never the
restriction it was taken for.

**And the second is the defect.**  A primitive atom on arbitrary `◇`-terms lets a maximal theory
assert that two possibilities coincide when **nothing has joined them**, and the canonical extent
reads a *witness*.  Honouring such a sentence therefore needs two witnesses the theory does not
identify to share an extent, and each route to that was rejected on principle:

* *A joint view (`◇_{u,v}`) in the syntax.*  Against the whole design: propositional modal logic
  promotes exactly **one** formula to possible and the rest to necessary, because possibilities do
  not combine — only *joint* possibilities do, and the joining belongs to the syntax.  For formulas
  that is a connective; for terms it is **pairing**, which the product types already provide.  §3's
  `◇`-BF entry had recorded the same fact from the other side: "a successor sits inside only one
  `◇_x` at a time, so several witnesses cannot be linked jointly."
* *A pairing comprehension* — `diatm u b ≐ diatm v b' ⊢ ∃p. η u ≐ diatm p .fst ∧ η v ≐ diatm p .snd`,
  with a partial `posPair` law in `Model` (there is `necPair` for `□` and `posStrength` for
  `Nec × Pos`, and deliberately no pairing of two `Pos`, since it is meaningful only for co-extensive
  objects).  Also against the design: a modal domain should be free to have elements or to lack them,
  the only standing requirement being that the term algebra lifts to it, and flags should add only the
  modal analogues of the propositional rules.  "Co-extensive possible objects are the components of
  one" is wanted in the *other* direction only — a possible pair *has* co-extensive components — and
  wanting it as a hypothesis is wanting a co-extensivity predicate, which duplicates what pairing is
  for.

**What was actually blocked without it was one construct.**  Of the items this section listed:
`Back` needs no `eqRec` at all ("its semantics uses equality in the model, so `◇`-types are
unproblematic", §3 B); 4's witnessed join is blocked by `Pos`'s extent structure, not by equality;
`pair_elim` was never cleared by the reform; naming at compound content was not delivered by it
either.  The one load-bearing item was **compound `Here` at `◇`-content** — and that is *exactly* the
construct that combines two unjoined possibilities: `Here s t` with a possible object as its value
says `s`'s content here **is** that object, and two such atoms about one subject, over unidentified
witnesses, are each innocuous but jointly force the co-extension.  So the old base-typed restriction
on `Here` was **principled, not a limitation of the truth lemma**, and the honest form of "uniform
over content types" is *uniform over `◇`-free content types*, with `◇`-content reached by joining.

**What joining gives back.**  Comparing two possibilities means presenting them as components of one
witness, after which they stand over the one name and the fibre-wise equality applies:
`□_p (eqRec V (view.fst) (view.snd))`.  Uniqueness claims are then statable in joined form, and the
degenerate identification is **derivable with no new rule** — `□_x ⊥ ⊢ □_x ψ` by monotonicity of
`◇_x`, so a joined pair of empty possibilities is identified outright.  `WFF.hereOnly`, the
`¬HereOnly` construction trigger and both degenerate right-rules are therefore unnecessary.

**What it costs.**  `Here` and `posRet_exists` at `◇`-content; identity claims between possibilities
that have *not* been joined; and naming at `◇`-content (route γ), so `hstage` and the stage component
of `interp_canon`'s measure stay.  Strong T at `◇`-free content is unaffected, which is where the
uniformity that matters lives.

**Landed (2026-09-28).**  ⭐`VarType.diaFree` with ⭐`Ann.eq_of_diaFree`; `eqRec` back to one
annotation with the `□_x` clause; `Proof.here_fun` at one annotation and at `◇`-free content;
`WFF.diaEq`, `Proof.diaEq_intro`, `Proof.diaEq_elim` and `WFF.subst_eqRec`'s `◇` case deleted;
`QML_v12m_CanonDiaEq`, `QML_v12m_ViewEq` and `QML_v12m_EqDia` deleted with `World.PEq`/`PEqW`, the
extent up to `≐`, the child tags (`tagOf`, `peqw_tagOf`, `tagBody`, `tagWFF`) and `Proof.boxx_reView`;
`Canon.extent` is again the single-witness one, back in `QML_v12m_CanonWorld`.  The whole module list
builds with **one** error, the truth lemma's `here` alternative, and no sorries — where before the
withdrawal there were two, `here` and `diaEq`.

**Rejected for now: separating the point objects in the models.**  Reflexivity and Leibniz force `≐`
to *be* carrier equality (a reflexive relation inside the diagonal is the diagonal), so separation
has to change the carrier or the arrows.  Dropping `pos_inj` would do it and costs too much: the
η-laws go (`Model.interp_eta` is proved by `pos_inj`/`nec_inj`, and the pinned form of `Here` depends
on it) and so does `sat_eqRec`, i.e. the semantics of equality-by-extensionality.  The arrow-side
alternative is better: let a world carry **many loops** under T, with a coherence law that all loops
agree on necessary data (`necEval u ρ = necEval u (refl hT w)`), and let realisation be along the
witness's own loop.  That separates point objects with `pos_inj` intact, and it is the same device as
`Frame.R` being `Sort v`-valued for B and 5.  Not taken now: it touches the T core
(`refl`/`reflAcc`, `Model.Realised`, `Env.collapseAgree_self`, every T rule's soundness) and blurs
the pinned form into "at `x`'s own loop".  Revisit if 5 or strong B forces richer loop structure
anyway — then `HereOnly` becomes derivable rather than primitive.  The empty extent is not separable
this way, and should not be.

**Decision: no forced empty term (2026-09-25).**  Naming `∅ : ◇A` would commit every model to having
an empty possible object: `Pos A w` is an abstract carrier, and the canonical one holds only
**denotable** objects, so the construction would have to reserve and declare `∅` in every world's
language.  As a term former it also needs an `Ann (.VTypeDia A)` with no witness index, i.e. a new
`Ann` constructor and a pass over `mapIdx`/`collapse`/`shift`/`code`/`Subst.Coh`/the views/`rden`;
the reserved-root variant changes `Root` and `Ctx` instead.  With `≐` in the language a user can
simply *define* the empty object inside a theory, which is where it belongs.  Record beside the
`t_dia` note (§3 T) as the other half of the same choice: naming `∅` alone would be an asymmetry
needing its own justification, so if closed `◇`-terms are ever wanted, weigh `∅` and the point object
together.

## 3. The flags

`R` is the accessibility relation. `Nec`/`Pos` are the carriers, `ext`/`cont` the extent and
content of a possible object.

### D (seriality)
- Frame: `R(w)` nonempty.
- *Route (§2c)*: one leg, no return.  D's content is route-**existence**, so there is no value to
  relate and no pinned form to want; "strong" and "witnessed" coincide, which is why strong D is a
  witness at `𝟙` with no carrier.
- **Weak**: rule `□⊥ ⊢ ⊥`. Canonical seriality is the usual successor for `◇⊤`.
  - *Implemented (2026-09-19).* Flag `ModalSys.D`; frame condition `Frame.serial`; rule
    `Proof.D_box` (`□⊥ ⊢ ⊥`), with `Proof.D_dia` deriving `□φ ⊢ ◇φ` and `Proof.D_box_of_dia` the
    converse. Substitution and soundness are one line each: the formula is closed, and `□⊥`
    fails at any world with a successor. Canonically, `Canon.exists_succ`: the rule refutes `□⊥`,
    so it is not in the theory, and a failing `□` has a successor (`exists_box_fail`).
  - *Layout change.* The canonical frame now proves its own seriality, and a successor is a
    Henkin construction, so `Canon.frame` and everything after it take
    `[Countable σ.FuncSyms] [Countable σ.RelSyms]` — the setting of completeness anyway.
    `QML_v12m_CanonExist` never used the canonical model, so it now imports `CanonDom` and
    `HenkinRet` and sits *before* `CanonModel`. Unlike T and 4, whose frame conditions hold of
    the canonical `R` by definition, D needs a construction; any later flag whose frame
    condition needs new worlds will too, so this order is the one to keep.
  - Flags stay independent: under T the rule is derivable (`T_box` on `□⊥`), but D is not
    switched on by T.
- **Strong: implemented (2026-09-19).** Flag `ModalSys.DStrong`. Rule `Proof.D_ex`, the closed
  axiom `⊢ ∃x:◇𝟙. ◇_x ⊤` (`WFF.somePoss`). Model condition `Model.posSerial`: some possible object
  of type `𝟙` has a nonempty extent.
  - *What strong D says* is the map `Nec(w) → Pos(w)`: every necessary object has a possible
    counterpart whose content is its value. In the syntax that is the schema
    `□φ(u.box) ⊢ ∃x:◇A. ◇_x φ(x.dia)`, **derived** from the axiom in K and proved in Lean
    (`Proof.D_schema`, `QML_v12m_StrongD`). The axiom is primitive only because it is cheapest:
    closed, so substitution leaves it as it is **definitionally** (its `ProofSubst` case is
    `.D_ex hDS`).
  - **The map is already in K, given one witness.** Semantically, `posStrength_eval` gives
    `posMap fst (posStrength n p₀)` the extent of `p₀` and content `necEval n` throughout — so the
    model condition is stated at `𝟙`, and every model satisfying it has the map at every type, the
    whole extent included. Syntactically, `diatm z _ (u.box)` puts `u`'s value on an existing
    witness `z`, legitimately because `u.box` is a `□`-item and so in scope in `z`'s view.
  - *The derivation.* `ex_elim` on the axiom gives `z` with `◇_z ⊤`; `ex_intro` at
    `diatm z _ (u.box)`; `K_dia` carries `□φ(u.box)` into `◇_z φ(u.box)`. The one real lemma is
    `WFF.instantiate_exDia`: instantiating `∃x:◇A. ◇_x φ(x.dia)` at that term is `◇_z` of the
    premise's body carried into `z`'s view. Its proof is `subst_mono`, then `subst_comp` against
    the hole's substitution weakened into the view, then `subst_mono_eq`; the pointwise `Sim` is
    modal β at the witness (`SubE.diaBody_diatm_self`) for the hole and the identity on `□`-items.
    Binding the axiom's witness for `ex_elim` is not definitional (the renaming's `if` on
    `free z = free z` is stuck on a variable), hence `WFF.dia_top_congr`. `Proof.D_schema'` picks
    the eigenvariable for a presented context. No `Classical.choice`.
  - *Canonically*: the axiom's Henkin witness gives a `◇_z` in the theory — instantiating the
    witness reduces to it definitionally, so it is never named — and `exists_dia` a successor in
    `z`'s extent (`Canon.exists_extent`); the possible object is `diatm z _ unit`, whose raw
    extent is `extent w z` by `rden`'s definition (`posSerial_canon`).
  - **Three forms, equivalent in K** (2026-09-19; corrects two notes of 2026-09-18, below):

    | Form | Types | Derivation |
    |---|---|---|
    | (a) `⊢ ∃x:◇𝟙. ◇_x ⊤` — *the rule* | — | (c) at `A = 𝟙`, `φ := ⊤`, with `□⊤` a theorem |
    | (b) graph `∀u:□A. ∃x:◇A. ◇_x (x.dia = u.box)` | `◇`-free only | (c) at `φ(z) := (z = u.box)`, premise by reflexivity |
    | (c) schema `□φ(u.box) ⊢ ∃x:◇A. ◇_x φ(x.dia)` — *presented* | all | (a) by `Proof.D_schema` |

    (a) and (c) are the ones that matter — (a) for the implementation, (c) as the natural rule
    generalising propositional D to the witnessed case — and both are in Lean. (b) is deliberately
    not proved (decided 2026-09-19); it is a short `K_dia` + reflexivity argument if ever needed.
  - **(b) needs `◇`-free types.** `eqRec` compares two terms only at the **same annotation**, and
    `Ann.eta` records the witness address at every `◇` in a type, so `x.dia = u.box` typechecks
    exactly when `A` has no `◇` (under `□` and in products included). This is not a technicality:
    equality at `◇A` is `□_x` of equality of contents *on one witness*, so equality of possible
    objects is witness-relative, and two witnesses' extents cannot be compared — an extent is only
    reached by entering its own `◇`, and inside `◇_{x.dia}` the other object has left scope. At
    `◇`-types only the schematic form is statable — which, derived from (a), is enough.
  - *Corrected: "the map is a comprehension principle beside D, not a reading of it."* Wrong: the
    comprehension half is K's `strength`, and the only new content is seriality with a witness —
    so the map **is** strong D, as first suggested. The mistake was missing that `diatm` can re-use
    a witness with new content.
  - *Corrected: "the schematic form is too weak as an axiom: it binds the witness per formula."*
    Wrong for D: because `u.box` is in scope in the view, the schema can state the pinning
    equation as one of its own instances, `φ(z) := (z = u.box)`, and thereby a uniform witness.
    Per-formula weakness is real only where the source is **out of** scope — strong T, whose `t`
    is a base object, and which therefore needed the parameter `y`, the Henkin form and the packing.
    So it is the §2b criterion again. The schema was not made primitive only because, as a rule,
    it needs a hole read two ways and closure under substitution — the work that cost strong T its
    packing — whereas (a) is closed.
  - The witness's content type is `𝟙` in (a) because the axiom's `x` is a pure world-selector; at
    a general `A` a closed `∃x:◇A. ◇_x ⊤` would add domain non-emptiness, which (a) with strength
    does *not* give (strength only transports necessary objects' values).
  - **Not** as a term former `u ↦ u↓ : □A → ◇A` (§2b).

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
  - **Semantics.** A model axiom `posRet_exists`: every object has *some* possible object whose
    extent contains `w`, with the object as its content there — `∃ p, ∃ (h : R w w),
    ⟨w, h⟩ ∈ extent p ∧ content = a`. It needs no reflexivity hypothesis and implies `R w w`
    wherever a domain is inhabited.
  - **Not an operation on `Frame.Ops`** (changed 2026-09-17). Strong T adds no term former, so
    nothing interprets a map from objects to possible objects, and none is intended. **No
    uniqueness and no naturality**: the object need not be a singleton, and nothing relates the
    witness for `f a` to the witness for `a`. Demanding an operation would force the canonical
    model to choose one — and if naturality were ever wanted the choices would have to cohere,
    which is what sank `y.ret`. Existentially, the canonical model just `obtain`s a term from
    `Definable` inside an existential goal, with no choice principle at all.
  - **Rule (Henkin-style, with a fresh witness `c : ◇A`).** From
    `Δ, ψ₁↓(t) → ◇_c ψ₁↑, …, ψₙ↓(t) → ◇_c ψₙ↑ ⊢ φ`, with `c` fresh and not in `Δ` or `φ`, conclude
    `Δ ⊢ φ`.
  - **Both readings are existing operations**, because the rule is parameterised by a `□`-view
    formula *with a hole*, `ψ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1`:
    - `ψ↓(t)` (at the current world) is `WFF.collapse` — weak T's operation, extended over the hole
      by `Collapses.insert` — followed by `WFF.instantiate` at `t`;
    - `ψ↑` (in the view) is `WFF.renameRoot`, weakening into `(Γ.insert c ◇A).diaIn c` and filling
      the hole with the *address* `c.dia`. Not `instantiate` at a term: `Term.var` builds only
      base-typed terms, so the hole has to be filled by an address rather than via `Term.eta`.
    This is fully general: a view formula cannot mention `c` except as `c.dia`, since roots are
    invisible in views.
  - *Why not a substitution.* Reading a view at the current world maps annotation indices the way
    `collapse` does, which is depth-sensitive, and `Subst.Coh`'s index map `ι` is a plain function
    on addresses. Writing it as a substitution would need a bespoke operation with its own
    annotation theory; the hole formulation avoids that entirely.
  - Soundness: `sat_instantiate` and `sat_collapse` on the `↓` side, and on the `↑` side the `◇`
    analogue of `Env.collapseAgree_self` — `diaPush` at the world the object is realised at.
  - *Implemented (2026-09-17), sorry-free.* The `posRet_exists` axiom
    (`QML_v12m_Model`); `WFF.hereRead`, `WFF.viewRead` and the rule `T_dia` (`QML_v12m_Proof`);
    `Env.diaPush_ret` and `sat_ret` (`QML_v12m_SemStrongT`), where `sat_ret` takes the possible
    object and its realisation facts as hypotheses; the `T_dia` soundness case
    (`QML_v12m_Soundness`), which obtains the eigenvariable's value from `posRet_exists`.
  - *Substitution: done.* `Proof.subst`'s `T_dia` case is complete, with the eigenvariable renamed
    as in `all_intro`/`ex_elim`. `WFF.subst_hereRead` is `subst_instantiate` followed by
    `collapse_subst`, with a `Corr` from `corr_under` and `corr_box_self`.
    `WFF.subst_diaViewRead` splits in two. Its witness index is handled by `WFF.subst_dia`, which
    states the `.dia` arm of `WFF.subst` with the target address as a *variable* and the right-hand
    side's side conditions as hypotheses, so `subst` rewrites uniformly — including through the
    types of the `ok_dia`/`coh_dia` arguments, which is what defeats `rw` and `generalize` in
    place. Its body is the `◇` counterpart of `WFF.subst_bindFree`: a `WFF.subst_comp` on each side
    against `(θ.box.mono _).set (.bnd 0) (.ren (c'.dia))`, the two `Subst.Sim` obligations going
    through `dia_eq_box_mono` (with `at_eq_mono_of` plus freshness of `c` relating `θ.rename`'s
    entries to `θ`'s) and `under_eq_mono` respectively.
  - *Canonical model: **done** (2026-09-18); `ModalSys.NoTStrong` is gone.* What follows records
    why it was needed. **`posRet_exists` was false in the original canonical model**, not merely
    unproved:
    every definable possible object has extent `extent w x`, which requires
    `w'.depth = w.depth + 1`, so no extent contains the self-successor. Admitting it needs a
    *content* at `w`, and neither the syntax nor the theory determines one — the axioms
    `ψ↓(t) → ◇_{c_t} ψ↑` constrain the content only through view-expressible `ψ`, and an arbitrary
    `t` at `w` is not expressible in the `◇_{c_t}` view. So the association must be carried by the
    construction (design A, decided 2026-09-17): a witness-to-term field on `World`, an `extent`
    disjunct for the self-successor, a depth split in `rden`'s `.diatm` case, repairs at the
    `extent_dist`/`extent_le` sites, the Henkin stage, then the discharge.
  - *Realisation (`QML_v12m_Realise`) — **done**; builds clean, no sorries, imported by nothing.*

    **Rejected vehicle: a substitution.** `Subst.realise` (`x.dia ↦ t₀`, `u.box ↦ u.here`,
    `u.keep ↦ u`) with `Subst.ok_realise` is kept only for the typing facts. `Term.subst` needs
    `Subst.Coh ι`, and `coh_of` forces `ι ((.step u .box).ext p) = (.step u .here).ext p` — a map
    acting on the level step the view introduced, which is *not* a function of the address
    (`(.step u .box).ext [.box]` and `(.step (.step u .box) .box).ext []` coincide with different
    intended images). The existing combinators dodge this: `coh_box`/`coh_dia` keep the same `ι`,
    `setIdx`/`singleIdx` discriminate on the root.

    **Chosen vehicle: a dedicated recursion over an address map**, following weak T's actual
    pattern — `Term.collapse` threads an explicit level `k` rather than being a substitution, which
    is exactly why it has no such ambiguity. The extra simplification is to let the canonical
    model *name* the realised content by a constant `d` in the world's language (as the Henkin
    construction already names `∃`-witnesses). Realisation is then a pure **address** map, so
    `Term.realise` mirrors `Term.collapse` instead of threading `SubE` entries across view
    boundaries. This is a model-level device only: no term former, no equation, no congruence, and
    nothing for substitution to commute with, so the `y.ret` objection (substituting a compound term
    leaves no address for the witness) does not arise.

    *Built and verified.* `VarSymb.belowDia` (strip the inner prefix `x.dia`) with `belowDia_self`
    and `belowDia_dia_ext`; `ext_snoc`; `VarSymb.realiseAddr` with `realiseAddr_proj`,
    `realiseAddr_level` and `realiseAddr_dia_ne`; `Ann.realise`; `Ctx.Realises` (exactly
    `Ctx.Collapses`' shape with `collapse k` replaced by `realiseAddr x d k`) with
    `Realises.of_raw`, `Realises.boxIn` and `Realises.diaIn`; and the mutual
    `Term.realise` / `Func.realise`, a near-copy of `Term.collapse`: `k` threaded, `var` by
    `realiseAddr`, result annotation `Ann.realise`. The recursion additionally threads
    `Γ₁.ref (.root r) = none`, preserved at each descent by `Ctx.ref_root_boxIn` /
    `Ctx.ref_root_diaIn`, which is what discharges `Realises.diaIn`'s side condition.

    *The `diaIn` side condition (diagnosed and confirmed, 2026-09-17).* `Realises.diaIn` will read
    `Realises (k+1) x d (Γ₁.diaIn y) (Γ₂.diaIn (realiseAddr x d k y))`, which is false when `y = x`:
    the entry `.step x .dia` then maps to `d`, a constant of `Γ₂` rather than an address of the
    view. This would be **unsound**, not merely unprovable — an inner witness spelled `x` would have
    its content collide, under `belowDia`, with the outer realised content, though the two denote
    different objects (addresses are relative to their context).

    An earlier note claimed this is vacuous because "a view never contains the outer address `x`".
    **That claim is false.** If `x` is a level-step address `u.box`, then `(Γ.diaIn x).ref x` is
    `Γ.boxIn x`, which is `◇`-typed whenever `Γ.ref u = some (□◇_)`. Attempts to build such a
    context push the root one level deeper each time without bottoming out, so vacuity for general
    `x` would need a regress argument.

    The cheap and correct condition is the one that actually holds in the canonical model, where
    witnesses are Henkin **constants**: require `x` to be a *root*. Roots are never entries of a
    view, so `Γ₁.ref x = none` at every depth and `y ≠ x` is immediate. Confirmed in Lean by
    `Ctx.ref_root_boxIn` and `Ctx.ref_root_diaIn` (both `rfl`), with corollaries
    `Ctx.ne_root_of_ref_boxIn` and `Ctx.ne_root_of_ref_diaIn`. `Realises.diaIn` accordingly carries
    `y ≠ x`, which `Term.realise` discharges from the threaded freshness hypothesis — and with that
    the recursion goes through.
  - *Plan revision (2026-09-18): no association field on `World`.* The content at the world itself
    need not be named by a constant of the world's language. Realise the body with a transient bound
    root `d` (`Term.realise`), then substitute the witness's term `t` for `d` with `Subst.single` —
    a root substitution, so its index map is unproblematic. Every non-`Var` term is in canonical
    form (`var`/`func` build only `Var`), so no equality at higher types is needed. The world then
    needs only a *property*, like `exW`/`allW`: a root `x` is **realised by `t`** when `T` holds
    every instance `hereRead t ψ → ◇_x viewRead ψ`; `extent w x` admits the world itself iff `x` is
    realised, and the content there uses a chosen such `t`. Any choice works — each direction of the
    truth lemma uses only the chosen `t`'s instances (for `□_x χ`: if `χ` failed here, `¬χ` holds
    here and the instance gives `◇_x ¬χ`).
  - *Open problem (2026-09-18, analysis, not checked in Lean): later constants.* The Henkin chain
    enumerates formulas, and terms of non-`Var` type never occur inside a formula, so strong-T
    witnesses must come from a separate enumeration of terms (they are countable). But the truth
    lemma needs a witness `c` realised for **all** formulas, including ones mentioning constants
    declared *after* `c`, while `T_dia` only justifies instances when `c` is fresh for the rest of
    the theory — and later sentences may mention `c` (e.g. the witness of `∃y. P(y, c)`).
    Where it bites: a hole formula lives in a `□` view, which exposes only constants of
    `□`-reaching type (`u.box`, `u.keep`, through projections). So (a) a new strong-T witness, of
    type `◇A`, never appears in another witness's instances, and adding one is safe by `T_dia`;
    but (b) a later `∃`/`¬∀` witness of `□`-reaching type needs instances mentioning its `.box`,
    which do not follow from instances over the earlier language — quantifying inside the view
    (`∀z. ψ(z, hole)`) gives the right conclusion but too strong a premise, and pinning `z` to the
    new constant needs equality at higher types.
    **Candidate fix:** let the rule's instances carry universally quantified parameters,
    `∀ȳ:B. (hereRead t ψ(ȳ) → ◇_c viewRead ψ(ȳ))` with `c` outside the quantifier, so later
    constants are covered by `all_elim`. Soundness should extend easily (the `posRet` witness
    depends only on `t`'s value, not on `ȳ`), but it does not seem derivable from the current rule:
    applying `T_dia` under `∀ȳ` yields a different witness for each `ȳ`. This changes the proof
    rule, so it needs the user's decision. The alternative — a chain keeping "theory plus all
    current instances" consistent at every step — has no known argument for case (b).
  - **Decision (2026-09-18): the rule becomes `T_dia∀`.** From
    `Γ, c:◇A ; { ∀y:B. (ψ↓(t) → ◇_c ψ↑) | (B, ψ) ∈ Ψ }, Δ ⊢ φ` infer `Γ ; Δ ⊢ φ`, with `c` fresh
    for `Γ, Δ, φ` and each `ψ` over `(Γ, y:B).boxIn` plus a hole of type `A`. `B` = unit is the old
    rule; several parameters pack into a product. On paper the user states the positive-polarity
    schema, justified by the sketch below.
    *Implemented (2026-09-18), sorry-free.* `WFF.retHyp` builds one hypothesis:
    `WFF.all B (WFF.bindFree y …)` around the old implication taken over `Γ, y:B`, moved into
    place along `Ctx.insert_swap_le` (the rule declares `c` before `y`). The rule `T_dia` now takes
    `c y`, freshness for both, `y ≠ c`, and `Ψ : List (Σ B, hole formula)`. Soundness:
    `sat_retHyp` reduces to `sat_ret` for each parameter value, with `Env.extend_swap_agree` for
    the swap — the witness is chosen from `t`'s value before the parameter, which is what makes
    `∃x ∀y` sound. Substitution: `WFF.subst_retHyp` renames `c ↦ c'` and `y ↦ y'`
    (`c' = bound Γ'`, `y' = bound Γ' + 1`) via `subst_bindFree`, then `subst_mono_eq` for the swap
    (a `Sim` check that renaming `c` then `y` agrees with `y` then `c`), then the old argument over
    `Γ, y:B`. `Term.subst` annotates by the index map, so the weakened term is compared as a
    dependent pair (`Term.subst_mono_rename_sigma`, `WFF.hereRead_congr`).
  - *Equivalence with the positive-polarity schema (paper sketch, not checked in Lean).* A root `x`
    is invisible in every view, and `◇`-typed terms cannot sit inside `=` or function arguments, so
    `x` occurs in a formula only as the witness of a top-level `◇_x χ`. A `Φ` positive in `x` is
    built from such atoms and `x`-free formulas by `∧`, `∨`, `∃`, `∀`, and `θ → A` with `θ`
    `x`-free. **Monotonicity:** given, for each atom `α(z̄)` with `z̄` the variables bound above it,
    the hypothesis `∀z̄. (α↓(z̄) → α(z̄))`, we get `Φ⟨x := t⟩ → Φ(c)` by induction — the `∨` case by
    `or_elim`/`or_intro`, the `∃z` case by `ex_elim`/`ex_intro` from `∀z. (A↓(z) → A(z))`. The
    hypotheses are `∀`-quantified whether the binder in `Φ` is `∀` or `∃`, which is exactly what the
    parameter supplies. **Schema from `T_dia∀`:** from `⊢ Φ⟨x := t⟩`, apply `T_dia∀` with one
    hypothesis per atom, get `Φ(c)`, then `ex_intro` at `c`; the goal does not mention `c`.
    **Converse:** with `Φ(x) := ∀y. (ψ↓(t,y) → ◇_x ψ↑(y))` (conjoined over hypotheses) the
    premise is trivial, so the schema gives `∃x. Φ(x)`, and `ex_elim` with a fresh `c` recovers
    `T_dia∀`. **Corollary:** the unparameterised `T_dia` handles exactly the `Φ` in which no bound
    variable of `□`-reaching type sits above an atom — the same condition that broke the canonical
    model.
  - **No polarity condition is needed.** Only the one direction `θ↓(t) → ◇_c θ` is ever available,
    so `◇_c` can only be used positively. The user's axiom "from `P` infer `∃x:◇A. ◇_x P†`" is the
    one-instance case: modus ponens, then `ex_intro` at `c`, then discharge `c`.
  - **Why finitely many instances suffice.** The canonical construction adds one witness constant
    per term with all instances as axioms; consistency of that extension is exactly this rule with
    the finitely many instances of a hypothetical derivation of `⊥`. ~~Stronger consequences, such
    as `∃x ∀y …`, follow from completeness rather than from the rule.~~ **Wrong (corrected
    2026-09-18):** this was circular. The canonical construction itself needs the uniform `∃x ∀y`
    strength (a witness must also serve formulas mentioning later constants), so completeness does
    not supply it — see "Open problem: later constants" below.
  - No new term formers, so `◇` canonical forms, `eqRec` and the address-witness design are
    untouched.
  - **Canonical model: realisation needs no new recursion (2026-09-18, in Lean).** The note above
    (and `QML_v12m_Realise`) assumed the model would need a `Term.realise` recursion, level-threaded
    like `Term.collapse`, because `Subst.realise` fails `Subst.Coh`.  It does not.  Split the job:
    *abstraction* sends the view `Γ.diaIn c` back to a hole formula (`c.dia ↦ bnd 0`, every `u.box`
    and `u.keep` fixed), and that changes **no levels**, so its address map is a function of the
    address and `Coh` holds — it is an ordinary substitution (`Subst.diaAbs`).  Realisation is then
    abstraction followed by the existing `hereRead`: `WFF.realiseAt`, `Term.realiseAt`.  The round
    trip `WFF.viewReadAt_diaAbs` turns the theory's `retHyp` instances, which are stated for hole
    formulas, into instances for an arbitrary formula of the view.
  - *Semantics (done).* `Model.sat_viewRead_ret` is `sat_ret` as an equivalence at the realised
    world; `Env.substEnv_diaAbs` identifies the environment abstraction induces there with the one
    pushed into the witness's `◇` view, and gives `interp_realiseAt` and `sat_realiseAt` at any
    context where the witness is a declared root — the shape a world's contexts actually have.
  - *The model (in progress).* `World.RealData` is the evidence that an address is a realised
    witness: the root, its type, the realising term `t₀`, and the theory's instances.  `extent w x`
    gains the world itself when `x` is realised, and `rden` gives the content there as the body
    realised by `t₀`.  The function algebra commutes with realisation (`applyG_subst`,
    `applyG_realiseAt`), and reading the witness's own content back gives `t₀` (`realiseAt_eta`,
    from `Term.subst_eta_ren` and `Term.subst_eta_tm`).
  - **Why `RealData` records the stage (2026-09-18).** `interp_canon` — a term's value in any
    environment agreeing with the canonical one is its denotation — is proved by induction on term
    size.  At the world itself the content is read off `t₀`, so the case needs `interp_canon` at
    `t₀`, whose size is unrelated.  There is no circle: in the chain the witness declared at step
    `n` realises the term enumerated at step `n` and is declared only from own stage `n + 1` on, so
    the realising term always comes from a strictly earlier own stage.  `RealData.hstage` records
    that, and the induction becomes lexicographic in (own stage, term size): the `□` and proper `◇`
    cases go to a successor at own stage `0` with a smaller term, the realised case recurses at
    `t₀` (earlier stage) and at the realised body (same stage, smaller term).  `interp_box_far`'s
    induction hypothesis accordingly asks for the stage it is used at.
  - **The world names its realisations (2026-09-18).** `Realised x` was `Nonempty (RealData x)`,
    with the realising term recovered by `Classical.choice`. That cannot work: `Model.posRet_exists`
    demands a possible object whose content *at the world itself* is a **given** object, and that
    content is read off the realising term, so the model must control which term the address
    carries — a choice function on a `Nonempty` returns an unknowable element of a type that has
    several. So `World` gained a field `real : ∀ c, Option (RealDatum σ L T c)`: the world chooses,
    once, the realisation of each of its roots, `Realised x` is `(w.realAt x).isSome`, and
    `Realised.data` is `Option.get` — determined, and no choice. `RealDatum` is the old `RealData`
    without the address; `RealData` keeps the old projections, so nothing downstream changed.
  - **Packing later constants into the parameter (`QML_v12m_Pack.lean`, 2026-09-18).** `spec` must
    serve formulas of *every* stage past the witness's, which mention the constants declared after
    it, while the chain's `retHyp` instances only have hole formulas over the stage where the
    witness was declared. This is what `T_dia`'s parameter `y : B` is for (its docstring: "several
    parameters pack into a product type"). `VarType.pack` is the right-nested product of a list of
    types, `Subst.pack` the renaming sending each listed root to its component `y.snd…snd.fst`,
    `Term.tuple` the tuple of the roots themselves, and ⭐`WFF.subst_pack_single` the round trip:
    packing and then instantiating the parameter at that tuple leaves a formula unchanged. Since
    packing is a renaming (projections are level steps-free) `Subst.Coh` is automatic, and the
    composite is `Subst.Sim` to the identity — `SubE.proj` on a `pair` entry is the pair-β, and the
    residual `.tm (eta v)` versus `.ren v` is exactly `SubE.Sim.ren_eta`.
  - **Using a hypothesis at a later stage (`QML_v12m_RetUse.lean`, 2026-09-18).** Once the
    parameter is bound the name is gone, so a later stage may declare that name itself and the
    instance may be taken at a term the declaring stage could not write
    (`WFF.instantiate_mono_bindFree`). ⭐`WFF.instantiate_mono_retBody` then says what comes out of
    weakening a hypothesis and instantiating its `∀`: the implication with the term substituted for
    the parameter. Both readings keep their hole formula over the later context *without* the
    witness, because the antecedent stays in the weakened form `WFF.retHyp` gives it —
    `WFF.subst_mono_eq` with `Subst.sim_rename_mono` pulls the weakening out, and then
    `WFF.subst_hereRead` and `WFF.subst_diaViewRead` handle a side each. The second applies only
    because the parameter substitution *is* the rename that keeps the witness
    (`Subst.single_eq_rename`). Specialised to the packing, ⭐`WFF.instantiate_mono_retBody_pack`
    gives exactly `RealDatum.spec`'s implication `WFF.realiseAt … χ → ◇_c χ`, for an arbitrary `χ`
    of the witness's view at an arbitrary later stage.
  - **The witness must be declared outermost (`QML_v12m_StageSkip.lean`).** `WFF.subst_diaViewRead`
    works in `Δ.insert c (◇A)`, and a world's contexts declare the witness in the middle. A context
    is a function, so declarations commute: `Ctx.stage_eq_skip_insert` rewrites the stage as the
    stage without the witness with the witness on top, and `Ctx.stageSkip_cases` gives what its raw
    entries are, which is what the packing's side conditions ask for.
  - **The specification, from the chain's hypotheses (`QML_v12m_HenkinRet.lean`).**
    ⭐`WorldLang.spec_of_retHyps` is `RealDatum.spec` for a witness declared with its `retSet`
    instances: at any later stage, everything the realising term satisfies there, the witness
    satisfies in its `◇` view. It takes the instance for the packed abstraction of the formula at
    that stage's base, reads off what instantiating its `∀` at the tuple gives
    (`WFF.instantiate_mono_retBody_pack`), and finishes by `∀`-elimination and modus ponens inside
    the maximal consistent theory. The stage of the formula is the witness's stage with the witness
    declared last, and since those contexts are *equal*, weakening carries everything across and
    the round trip collapses by `WFF.mono_mono` and `WFF.mono_refl`. `laterList` is the packing and
    its side conditions follow from what a raw entry of a stage can be.
  - **The chain's witnesses are realised (2026-09-18).** `hhyp_of_isRet` bridges the chain's own
    `retSet` membership to that hypothesis. Two things had to cross, both of them equalities that
    `rw` and `simp` cannot use because they sit inside types: the step's declaration (reached
    through `(chain (n+1)).l`) is carried by `step_ret`, which transports the *membership* as a
    statement about that declaration with an explicit motive; and the chain's `ρ l.length` over
    `ctxL m l` versus the model's `ρ n` over `final.ctx (m, n)` are carried by
    `WFF.retHyp_transport`, which takes context, both names and target as equalities and collapses
    every weakening at once. `retDatum` then assembles the `RealDatum`, and ⭐`chainReal` is what a
    world names at each root: the realisation of the step that declared that constant, if one did —
    a choice in name only, since `ρ` is injective. `World.ofHenkin` passes it. Without strong T the
    condition is unsatisfiable, so nothing is realised and the K/T/4/S4 proof is untouched.
  - **Every term of a Henkin world is realised (2026-09-18).** `World.realW`: under T and strong T,
    every term at every stage is the realising term of some root, with the datum the world names
    there. `ofHenkin` supplies it — `exists_isRet_term` finds the step that enumerates the term and
    reads `⊤`, which therefore declares a witness (`isRet_of_top`: neither `⊤` nor its negation
    calls for a witness of its own), and `chainReal_ret` says that is what the world names there.
    `Model.posRet_exists` now asks for weak T as well as strong T — which `Proof.T_dia` carries
    anyway, and without which the chain declares no witnesses at all, so nothing would be realised.
  - **The content half of `posRet_exists` (2026-09-18).** `rden_realisedTerm_eta`: reading a
    realised witness's content off its own η-expansion, at the world itself, gives what the
    realising term denotes. Like the other `realisedTerm` lemmas it is stated purely in terms of
    `hr.data`.
  - **⭐`posRet_exists` (2026-09-18).** `posRet_exists_canon`: the possible object is the witness
    the world realises by a term denoting the given object, `self_mem_extent` puts the world in its
    extent, and its content there is what the realising term denotes. The canonical model proves
    the field instead of discharging it from `ModalSys.NoTStrong`.
  - **The API that made it work.** The world's chosen datum `hr.data` is only *propositionally* the
    datum a construction hands over — `w.real c = some d` is a hypothesis, so `Option.get` does not
    reduce — and every use of it inside `realisedTerm` is a dependent position that neither `rw` nor
    `simp` can carry the identification through (the content's type is `hr.data.A` where the goal
    wants `A`). Fighting that at the use site does not work. Instead: `World.realAt_of_real`,
    `realised_of_real`, `data_of_real` read off what a world names at a root; `rden_eta_realised`
    states the content purely in terms of `hr.data`; and `rden_eta_realised_of_eq` takes the datum
    as a **variable** with an equation, which turns the identification into a `subst`.
    `rden_eta_of_real` is the form callers use. Worth remembering as the general move: to cross an
    equation that sits in dependent positions, bind the thing as a variable in a lemma and `subst`
    it there.
  - **⭐`ModalSys.NoTStrong` dropped (2026-09-18).** The class, `ModalSys.NoTStrong.absurd` and
    `World.Realised.elim` are deleted; nothing in `QML_v12m_*` assumes the flag any more. What was
    behind it was exactly two cases, and each needed the right measure.
    - **The measure of the truth lemma for terms is `(i.2, VarType.tsize A, t.size)`** — own stage
      first, then the type, then the size. The realised case of `.diatm x hx t` recurses twice: at
      the realising term `dat.t₀`, of an *unrelated* type, justified only by `hstage`'s
      `dat.i₀.2 < i.2`; and at the whole realisation `Term.realiseAt … (Term.mono … t)`, which is
      far larger than `t` but has type `A`, one `tsize` below `◇A`, at stage `i ⊔ dat.i₀` whose own
      component is `i.2` again. Entering a modality drops the own component to `0`
      (`childStage i = (max i.1 i.2, 0)`), so those calls are covered by the first component
      whenever `i.2 > 0` and by the type otherwise; `interp_box_far`'s `i.2 = 0` hypothesis is
      what the checker uses there. `decreasing_by` needs `Prod.lex_def` and `true_and` in the simp
      set before `omega`: `omega` treats an unreduced `Prod.Lex` — or a stray `True ∧ _` — as an
      atom and fails with an unhelpful counterexample.
    - **`interp_dia_self`** does the case, with both recursive calls taken as hypotheses (as
      `interp_box_far` does). It goes through `Model.interp_realiseAt`, whose `hcont` obligation —
      the witness's content at the world itself — is `rden_eta_of_real`, and whose conclusion is
      matched to the goal by `Model.Env.diaPush_agree` against `canonEnv_le` (the canonical
      environment is stage-independent). The address is a variable there, so the lemma takes the
      datum's root `c`, the equation `x = .root (.free c)` and the `RealDatum` as *separate*
      arguments: that makes `subst` legal, where `hr.data.hx` alone is circular (`hr.data.c`
      mentions `x`). `World.real_of_realised` is what turns a `Realised` back into the world's
      naming at the use site.
    - **The truth lemma's `◇` case at the world itself** is `dia_mem_of_sat_self`: satisfaction in
      the witness's view transfers to the realisation by `Model.sat_realiseAt`, the induction
      hypothesis turns that into theoryhood, `RealDatum.spec` turns it into `◇_c`, and
      `World.mem_mono_congr` brings the stage back down. This works only because **`WFF.size`
      counts connectives and ignores terms**, so `WFF.size_realiseAt` gives
      `(WFF.realiseAt … χ).size = χ.size` — the formula grows but its logical structure does not,
      and the existing induction on size goes through untouched.
    - **State the self-case lemmas at the self element.** A lemma about an arbitrary successor `w'`
      with `w'.depth - w.depth = 0` puts the content at `w'.1.1` where the caller wants `w`; the
      equation `w'.1.1 = w` then has to be carried through a dependent position. Stating them at
      `⟨⟨w, R.refl …⟩, self_mem_extent hr⟩` avoids it — the same move as the realisation API above.
  - *Rejected: reaching later stages by induction on the stage.* Take `spec` at stage `j` for
    `∀z. χ[ρ_j := z]` and eliminate the `∀` inside the `◇_c` view by monotonicity. Unsound: the
    premise needs `realiseAt (∀z. χ[z])` from `realiseAt χ[ρ_j]`, i.e. generalisation on a Henkin
    constant, which the theory does not admit. The parameter is on the *hypothesis* side, so
    packing instantiates rather than generalises.
  - *Rejected: named singletons (`unitT t`).* A new `◇` canonical form and annotation, with the
    collapse `◇_z φ [z ↦ unitT t] = φ[z.dia ↦ t, u.box ↦ u.here]` living in substitution. Clean and
    complete-able, but it forces every possible object realised here to be a singleton, and every
    witness use then reduces to a statement about the object.
  - *Rejected: naming the unnamed object (`y.ret`).* Substituting a compound term for `y` has no
    address to name `ret(t)`; requiring one (naturality) plus projections forces a single extent per
    world and homomorphic counterpart maps. Uniqueness of the realised-here object forces the same.
  - *Rejected: the positive-polarity schema `Φ⟨x := t⟩ ⊢ ∃x. Φ(x)`.* It needs a new formula
    transformation with polarity tracking and slot renumbering; the Henkin rule reuses `WFF.subst`
    instead. ~~Same strength.~~ **Not the same strength (corrected 2026-09-18).** `Φ` may put
    quantifiers around `◇_x`: with `Φ(x) = ∀y. (ψ↓(t,y) → ◇_x ψ↑(y))` the premise is trivial and
    the schema yields the uniform `∃x ∀y` witness, whereas `T_dia`'s hypotheses are bare
    implications and give only `∀y ∃x`. The parameterised rule proposed under "Open problem: later
    constants" restores that strength in Henkin form.
  - **⭐Kept open, and possibly the *right* shape: strong T inwards, via a realisation predicate
    (2026-09-24).** What we have is sound and complete, but it states T's `◇` half as an *outward*
    map — from an object of `A`, a possible object of `◇A` — and per formula. The inward reading
    may be the better primitive: read off the actual value of a possible object that is instantiated
    here.
    - *The inward map is semantically free.* Given `p : Pos A w` with `reflAcc hT w ∈ (posEval p).1`,
      the value `(posEval p).2 ⟨reflAcc hT w, _⟩ : Dom A w` needs no frame condition.  And
      `posRet_exists` (`QML_v12m_Model`) says exactly that **this map is surjective**.  So inward and
      outward are not alternatives: outward = inward + surjectivity.  Replacing one by the other
      loses the existential content; what changes is where that content sits and how it is stated.
    - *Name the realisation: a binary primitive.* Make the new formula `Here x t` — "`t` is `x`'s
      realisation here" — rather than a unary `Actual x`, which is then `∃a:A. Here x a`.  Sketch:

      ```lean
      | here {Γ : Ctx} {d : ℕ} {A : VarType} (hT : ModalSys.T = true) (x : VarSymb)
          (hx : Γ.ref x = some (.VTypeDia A)) {a : Ann A} (t : Term σ Γ A a) : WFF σ Γ d
      ```

      with `sat env (Here x t) := ∃ hm : reflAcc hT w ∈ (posEval (env.ref x hx)).1,
      (posEval (env.ref x hx)).2 ⟨reflAcc hT w, hm⟩ = interp env t`.  The semantics uses equality in
      the **model**, not `eqRec`, so the witness-relative equality problem at `◇`-types (§2b) does
      not arise.  This is what lets one say: `x : ◇Person` is Kripke as a possible object, `Here x k`
      says `k` is his realisation at the actual world; properties of the possible object go through
      `◇_x`/`□_x`, properties of the man through `k`.
    - *Rules.*  With the name, both halves of T are statable, and the right-hand sides already exist:
      `WFF.realiseAt = hereRead ∘ diaAbs` is literally "abstract the witness, read at `@` with `t`
      in the slot", so `Model.sat_realiseAt` should give soundness directly.

      ```
      Here x t,  □_x φ(x.dia)  ⊢  φ(t)          -- instantiate the extent-universal at @
      Here x t,  φ(t)          ⊢  ◇_x φ(x.dia)  -- @ witnesses the existential
      ```

      Uniqueness `Here x a, Here x b ⊢ a = b` is sound, statable at `◇`-free `A`; elsewhere use the
      Leibniz form `Here x a, Here x b, φ(a) ⊢ φ(b)`.
    - *`Here` must pin the **identity** arrow, not merely some loop.*  The `◇_x` half would survive
      an arbitrary loop, but the reading of the box-view items would not: `u.box` along a loop is
      `necEval u loop`, while the rule reads it as `u.here = necEval u (reflAcc)`.  Same point as the
      note on `posRet_exists`: with several loops only the identity one is sound for `T_dia`.  Hence
      the `hT` field.
    - *No new type, no new proof modality.*  A `◇A` object already *is* a witness variable plus
      content (`Term.diatm x _ body`, which is how `D_schema` builds its `◇A` objects), so
      "possible-and-actual object" = a `◇A` term whose witness is actual — no `◇⁺A` type former, and
      so no new cases in `Ann`, `Dom`/`RDom`, `bc`, `step`, `collapse`/`shift`, `rden`.  At the
      formula level `◇⁺_x ψ` is not a modality either: it is ψ read at `@` (`realiseAt`), so
      `◇⁺P ⊢ P` is definitional unfolding.  Quantification over actual witnesses comes free, as
      `∃x:◇A. Actual x ∧ …`.  A K`◇`-shaped introduction rule should come out **admissible** —
      reading a whole derivation at `@` is a congruence over `realiseAt` — and making it primitive
      would duplicate weak T.
    - *Why it might pay.*  The canonical model already carries `World.real : ℕ → Option RealDatum`:
      per world, which witness constants are realised *there* and by which term.  That is precisely
      `Here c t` as metatheory.  Internalising it means the theory says it, and the world's separate
      realisation structure becomes a consequence of MCS closure.  Cheap test before committing: add
      `Here` and the elimination rule, check soundness falls out of `Model.sat_realiseAt`, and see
      whether `Canon.dia_mem_of_sat_self` — the messy self case of the truth lemma — collapses.
    - *Costs.*  One `WFF` constructor, so a case in `mono`, `subst`, `collapse`, `shift`, `size`,
      `sat`, `DecidableEq`, and the canonical model.  The witness argument follows `dia`'s pattern,
      the term argument follows `atom`/`eq`'s.  Wrinkle: `WFF` has `deriving DecidableEq` and `Term`
      is indexed by `Ann T`, so comparing two `Here` formulas needs the indices compared first; if
      the derive handler balks, store `⟨A, a, t⟩` as a `Σ`, as the codebase does elsewhere.  This is
      plausibly why `WFF.eq` was kept at base type with the fixed annotation `.var`.
    - *Still needs the existential.*  `Here` alone is weak (a projection).  See §2c for the route
      idiom this instantiates, and §3 B for its two-leg counterpart.  The strong content
      remains "actual witnesses exist carrying any object", which factors as in §2b: the `◇`-side
      axiom at `𝟙`, plus NecT for arbitrary objects, plus strength.  So the inward reading
      **relocates** the strong content from the `◇` side to the `□` side — which is the side the
      Henkin tree already handles with ordinary box children and no extents to realise.
    - *Stage 1 done: the constructor propagates (branch `here-experiment`, 2026-09-25).*  The
      sketch above needed one change: **the subject is a term of `◇`-type, not an address.**  With
      an address, `WFF.here` does not survive substitution — a substitution may send the witness to
      a `diatm` term whose recorded index has a different content type, and nothing ties the
      formula's `A` to it.  As a term the subject substitutes like `atom`/`eq`'s terms, and the
      pinned form is recovered as `Here (Term.eta x (.VTypeDia A) hx) t`; the general form
      `Here (diatm x hx s) t` is the extra expressive power, and by `dia_beta` it says "`x` is
      realised here, and the here-reading of `s` is `t`".

      ```lean
      | here {Γ : Ctx} {d : ℕ} {A : VarType} (hT : ModalSys.T = true) {b : Ann (.VTypeDia A)}
          (s : Term σ Γ (.VTypeDia A) b) {a : Ann A} (t : Term σ Γ A a) : WFF σ Γ d
      ```

      `deriving DecidableEq` accepted it; `sat` reads through the named predicate
      `Model.Realised hT p o` (the dependent `∃` kept out of congruence proofs, so the rewriting in
      `sat_mono`/`sat_shift`/`sat_collapse`/`sat_subst` is `congrArg` on arguments).  The ~30
      recursions over `WFF` each take one line, with two congruence helpers `WFF.here_congr`
      (Σ-valued term lemmas) and `WFF.here_congr'` (plain equalities).
    - *One genuine theorem fell out.*  `WFF.subst_comp`'s new case needs substituting twice at the
      subject's type, and `Term.subst_comp` was **`Var`-only**: `Sim` is η-agreement, and at higher
      types the annotation moves with the index map, so the statement has to be Σ-valued.
      `Term.subst_comp_sig` now proves it at every type (`unit`/`pair`/`boxtm` structurally,
      `diatm` by the same generalise-then-`subst` trick as `WFF.subst_comp`'s `dia` case, the
      witness travelling by `Subst.idx_comp`).  The old `Var` version is a corollary.
    - *What is left, exactly.*  Everything up to `QML_v12m_CanonTerm` is green; the one hole is the
      truth lemma's `here` case, which is Stage 2 (the rules) plus Stage 3 (the canonical model).
      In the canonical model the case is forced: by `dia_beta`, `extent_self` and
      `dia_realised_self`,
      `sat (Here (diatm x s) t)` ⟺ `w.Realised x` ∧ `cls (realiseAt t₀ s) = cls t`, so the theory
      side needs (i) the pinned rules above, (ii) a β-rule taking `Here (η x) t₀` to
      `Here (diatm x s) (realiseAt t₀ s)` with Leibniz for the value, and (iii) the converse
      obligation `Here (diatm x s) t ∈ T → w.Realised x`, which is a *construction* condition: the
      world must give `x` a datum when a `Here` formula about it enters the theory.
    - *The collapse is confirmed, in advance of (iii).*  `RealDatum.spec` — "everything `t₀`
      satisfies at a stage, the witness satisfies in its view" — is exactly the intro rule
      specialised to `t₀`.  With `Here (η c) t₀` in the world's theory it follows from MCS closure,
      so the field goes and `Canon.dia_mem_of_sat_self` loses its `dat.spec` step.
    - *Stage 2 done: the rules, sound and substitutable (2026-09-25).*  The pinned form
      `Here x t, □_x χ ⊢ χ(t)` is **not closed under substitution**, and the reason is instructive: a
      substitution sends a `◇`-typed address to a `◇`-**term** `diatm y bd`, and inside the view it
      sends the content `x.dia` to that term's body `bd` (`Subst.dia_eq_box_mono` is the `□`-part of
      the same fact).  So the image of the pinned premise says "`bd`'s value here is `t`", which does
      *not* pin `y`'s own content — and the image of the pinned rule would be invalid if the `□`
      premise still spoke of `y.dia`.  Both sides move together: the rules are stated at a `◇`-term
      and at a **hole formula** read twice, inside the view with the body in the hole
      (`WFF.viewReadTm`, new) and here with the realising term in it (`WFF.hereRead`, which already
      existed for `retHyp`):

      ```
      Here (diatm x bd) t,  □_x ψ⟨bd⟩  ⊢  ψ⟨t⟩        -- Proof.here_elim
      Here (diatm x bd) t,  ψ⟨t⟩       ⊢  ◇_x ψ⟨bd⟩   -- Proof.here_intro
      ```

      This is the same discipline as `T_dia`'s `retHyp`, for the same reason, and it is what the
      term subject was for.  Soundness is `Model.sat_viewReadTm`, the two readings agreeing at the
      identity arrow, split by polarity: the `□` part of the view is read at that arrow either way
      (`Env.diaPush_boxIn`, `Env.collapseAgree_self`) and the hole gets the same object.  The pinned
      rules come back as `Proof.here_elimAt` / `Proof.here_introAt`, derived: `WFF.viewReadTm` at the
      η-expansion of `x.dia` is `WFF.viewReadAt` (`WFF.viewReadTm_eta` — the two substitutions differ
      only by `SubE.Sim.eta_ren`, which is what `Sim` is for), and every view formula is its
      abstraction read back.
    - *Two lemmas the semantics owed us.*  `Model.interp_eta`: an address's η-expansion denotes the
      address — needed because the pinned form's subject *is* that η-expansion.  Every case is a
      coherence already in the model (`stepObj` for projections, `Env.ref_inner` and `nec_inj` for
      `□`, `dia_beta` and `pos_inj` for `◇`), so it is short; it is also the model-side statement
      that an environment is determined by its components.  `WFF.subst_viewReadTm`: substitution
      commutes with the new reading, which is what `Proof.subst` needs; `WFF.subst_hereRead` was
      already there.  Weakening (`Proof.mono`) comes free from `Proof.subst`.
    - *Where the `hereRead` machinery now lives.*  `WFF.hereRead`, `viewRead` and `retHyp` moved from
      `QML_v12m_Proof` to `QML_v12m_DiaAbs`, and `Proof` now imports `DiaAbs` instead of the reverse:
      the rules' conclusions are `WFF.realiseAt`, so the proof system has to see it.
    - *Stage 3, first half: the predicate is base-typed, and there are four rules (2026-09-25).*
      The truth lemma forces `WFF.here` to **base type**, for exactly the reason `WFF.eq` is
      primitive there.  In the canonical model the `Here` case must decide an *object equality* —
      the content at the identity arrow is `t`'s value — and object equality is formula-level only
      through `eqRec`, which compares terms of the *same* annotation (`Model.sat_eqRec`).  The value
      names the content, so the two annotations differ, and at a compound content type no formula
      says "the content is `t`".  At base type `Ann .Var` is a singleton, the comparison is
      `WFF.eq`, and `cls_eq_iff` turns it into membership.  Compound `Here` can later be *defined*
      by extensionality, as `eqRec` defines compound equality; that is the same staging equality
      went through.
    - *The four rules.*  `here_elim` and `here_intro` as in Stage 2, plus two the canonical model
      needs: ⭐`here_beta`, `Here (diatm x bd) t ⊢ Here (diatm x bd⟨s⟩) (hereRead t s)` — the term
      counterpart of the hole-formula discipline, with `Term.viewReadTm` reading a hole *term* in
      the view — and ⭐`here_fun`, `Here s t, Here s t' ⊢ t = t'`, which is an equation only because
      the value is base-typed.  All four are sound (`Model.interp_viewReadTm` is β's bridge) and
      survive substitution; `Term.subst_single_tm`, `Term.subst_hereRead` and
      `Term.subst_viewReadTm` are the term-level lemmas that took, mirroring the `WFF` ones.
    - *What the canonical model still needs, and the one real obstacle.*  With `Here (η c) t₀` in a
      world's theory, `RealDatum.spec` is a derivation (`Proof.here_elimAt`/`here_introAt`), so the
      field goes.  The truth lemma's case then reads: `sat (Here (diatm x bd) t)` iff `w.Realised x`
      and `cls (realiseAt t₀ bd) = cls t`, the first by `extent_self`, the second by
      `dia_realised_self` and `cls_eq_iff`; the theory side is `here_beta` then `eq_elim` one way
      and `here_beta` then `here_fun` the other.  What is left is *which* roots the world realises.
      `RealDatum.hstage` demands the realising term live at a **strictly earlier** own stage than
      any stage declaring the witness, while a `Here`-driven datum arrives the other way round: the
      root is there first and the theory then names its content (by `exW` on
      `∃a. Here (η c) a`).  Two ways out, to be decided next:
      * relax `hstage`.  It exists to make `realisedDecl` available and `interp_canon` well founded;
        now that the content is base-typed, `rden` of the realising term is a *class of a base term*
        and recurses through nothing, so the ordering may be replaceable by monotonicity of
        declarations.
      * keep the order and change the strong-T step: have it add the pinned `Here (η c) t` for the
        term `t` it has just enumerated (a local change to `QML_v12m_HenkinRet`, replacing the
        `retHyp` family), and get the realisation of *other* roots from a strong-T **axiom**
        `⊢ ∃x:◇Var. Here x t`.  That axiom is the inward form of strong T, it makes `realW`
        immediate, and `T_dia` becomes derivable from it — at which point `retHyp`, `viewRead` and
        `T_dia` can all go.
    - *Stage 3, second half: the collapse is proven, and the ordering has a fix (2026-09-25).*
      ⭐`Canon.spec_of_here` derives `RealDatum.spec` from one sentence being in the theory —
      `Here (η c) t₀` at every later stage — by `Proof.here_introAt` and closure of a maximal
      consistent theory under provability.  So `spec` is no longer data the construction has to
      arrange, and the field can go once the datum carries the sentence instead.
    - *The ordering obstacle, precisely.*  `interp_canon`'s measure leads with the own stage because
      the realised `◇` case makes **two** recursive calls, not one: at the realising term `dat.t₀`
      (arbitrary type, so only the stage justifies it) and at the body's realisation, which lives at
      `i ⊔ dat.i₀` and so needs `dat.i₀.2 ≤ i.2`.  Base-typing removes the *first* — that is what
      `interp_canon_base` is for — but not the second, and re-leading the measure with the type fixes
      the second while breaking the first for legacy `T_dia` data.  `interp_dia_self` is now split so
      this is visible in the types: `interp_dia_self_core` asks only for the declaration's type at
      `i`, the single equation for `dat.t₀`'s value, and `dat.i₀.2 ≤ i.2`; `interp_dia_self` is the
      wrapper that supplies all three from the stage-led induction.  `RealDatum.declType` likewise
      isolates the *type* of the declaration from the stage order.
    - *The fix: a reserved partner constant declared before the witness.*  A `Here`-driven datum needs
      its realising term no later than the witness, which the Henkin order does not give — the
      witness is declared first and the theory names its content later, by `exW` on
      `∃a. Here (η c) a`, whose witness is a *later* constant.  Reserving an earlier partner does not
      work naively either, since by the time the `∃` is decided the partner is no longer fresh.  What
      does work is to commit at declaration time: when the chain declares a `◇`-typed own constant
      `c`, declare a base-typed partner `b` immediately **before** it and add the implication

      ```
      (∃a. Here (η c) a) → Here (η c) b
      ```

      which is consistent exactly when `b` is fresh, i.e. at that moment: were it not, the theory
      would prove `∃a. Here (η c) a` together with `¬Here (η c) b` for a fresh `b`, hence
      `∀y. ¬Here (η c) y` by generalisation on `b`.  Afterwards, a maximal theory that says `c` is
      realised contains `Here (η c) b` with `b` declared strictly earlier, so `hstage` holds, both
      induction calls are justified, and no measure changes.  Reserved names are already the staged
      construction's idiom (`QML_v12m_BCompactness`'s docstring contrasts the network with it on just
      that point).
    - *The declaration-time implication is blocked; the ordering has to go, not be satisfied
      (2026-09-25).*  Two findings, the second decisive.
      * **Freshness forces paired declarations.**  Adding `(∃a. Here (η c) a) → Here (η c) b` at the
        step that declares `c` is consistent only when `b` is fresh *at that moment* — otherwise the
        theory may already say that nothing is realised by `b`.  The chain declares exactly one own
        constant per step (`HState.l`, `Henkin.step`), so a fresh partner would mean two declarations
        per step, and the stage arithmetic (`length_chain`, `decJ_le`, `final_ctx`, `IsRet`) is keyed
        to one.  Invasive, and ~150 references to `L.chain` to re-check.
      * **It cannot work at all for the context's own witnesses.**  `RealDatum.hstage` demands the
        realising term live at a *strictly earlier* own stage than any stage declaring the witness.  A
        `◇`-typed variable of the presented context is declared at own stage 0, so no term can be
        strictly earlier: such a witness can *never* be realised under `hstage`, whatever the chain
        does.  Since a theory may perfectly well say `Here x t` for a context variable `x`, the truth
        lemma would fail there.  So the ordering requirement has to be removed, not satisfied.
    - *Experiment: the measure can lose its stage component, and exactly one call objects.*  Changing
      `interp_canon`'s `termination_by` from `(i.2, tsize A, t.size)` to `(tsize A, t.size)` leaves a
      **single** failing goal — the call at the realising term `dat.t₀`, whose type is unrelated to
      the term being interpreted.  Every other call decreases the type: the body's realisation
      (`A < ◇A`), `pair`, the `boxtm` collapse, the `diatm` proper branch, and `interp_box_far`, which
      already takes its hypothesis with a size bound rather than a stage one.  So the stage component
      exists *only* to justify that one call.
    - *Consequence: make realisation base-typed, and the ordering problem disappears at the root.*  If
      `RealDatum`'s content type is always `.Var` — matching `WFF.here`, which is base-typed for its
      own reasons — then `dat.t₀` is a base term, its value comes from `interp_canon_base` instead of
      the induction, the measure drops the stage, `hstage` goes, and a `Here`-driven datum may name its
      realisation at *any* stage.  No chain changes, no partner constants.  The work is then:
      * `RealDatum` base-typed, `World.realW` base-only, and the accessors and uses in
        `QML_v12m_CanonDom`, `QML_v12m_CanonTerm`, `QML_v12m_HenkinRet` and `QML_v12m_Completeness`
        adjusted;
      * ⭐re-prove `posRet_exists_canon` at every type from base realisation: given `a : Dom A w`, take
        a base-realised witness `c` and use `diatm c (body)` where the body is a term denoting `a`
        lifted into the view, which reads back at the identity arrow — so the compound content comes
        from the *body*, not from the datum.  This needs a small lemma that lifting then realising is
        the identity;
      * a **reserved individual**, or some guarantee that the base domain is non-empty: with base-only
        realisation and no base object at all (empty signature, empty context) there is no realised
        witness to hang compound contents on, and `posRet_exists` at `𝟙` would fail.  One reserved
        base-typed own constant fixes it and is worth having anyway;
      * then the measure change, `hstage` deleted, the `Here`-driven `real`, and the truth lemma's
        `here` case.
    - *Refuted: base-only realisation cannot serve `posRet_exists` at compound types (2026-09-26).*
      A view sees almost nothing: `Ctx.diaIn Γ x` is `x`'s content address together with `Γ.boxIn`,
      so the world's **own** entries — in particular its base constants — are not visible inside
      `◇_x`.  Hence a view body is built only from the content address, the necessary entries and the
      function symbols, and `Term.realiseAt` substitutes `t₀` for the content address: the contents a
      witness can have at the world itself are exactly the denotations of terms built from `t₀` and
      the values-at-here of necessary objects.  With `t₀` base-typed those never include, say,
      `rden (boxtm s)` for an arbitrary `s`, or a pair of two unrelated objects.  So "hang the
      compound content on the body" does not work, and the canonical model needs realisation data at
      compound content after all — which is what `World.realW` and the chain's enumeration already
      give it, with `hstage` to justify interpreting `t₀`.
    - *Where that leaves the ordering (2026-09-26).*  `RealDatum` must stay compound-typed, so
      `dat.t₀` at compound content must be interpretable without the induction — the two ways being a
      strictly earlier stage (`hstage`, which a `Here`-driven datum cannot have) or an address
      (route γ, faithful at `◇`-content only once §2d's model half is done).  Three routes, and the
      `diaEq` case of the truth lemma decides between them: it needs §2d's model half regardless, so
      nothing is saved by avoiding it.
      * **Base-only strong T.**  Restrict `T_dia` and `Model.posRet_exists` to base content.  Cheapest,
        and unblocks `here` at once, but it weakens the logic and changes the model class.
      * **§2d's model half, then γ.**  Extent up to provable `≐` makes naming faithful at every type;
        then every datum is address-named, `hstage` is deleted, the measure loses its stage, and a
        `Here`-driven datum may name its realisation at any stage.  Full strength, and the `diaEq`
        case comes with it.
      * **Paired declarations, keeping `hstage` with `≤` for base data.**  Since `interp_canon_base`
        gives `dat.t₀`'s value when the content is base-typed, a base datum needs only
        `dat.i₀.2 ≤ i.2` — and *that* the reserved-partner scheme above can supply, its decisive
        objection having been the *strict* inequality a context variable at own stage 0 can never
        satisfy.  What remains of the objection is the cost: two declarations per chain step, against
        stage arithmetic keyed to one.  Keeps full strength without §2d, but leaves `hstage` in the
        design permanently.
  - **Kept open: a term former `t_dia : ◇A` for `t : A` (2026-09-19).** Not taken, and there is no
    plan to redo strong T this way. It is recorded so that we remember strong T *could* be redone
    if the option starts to look right — for instance if other rules come to want term formers, or
    cut elimination needs uniform, syntactic witnesses.
    - *Same logic.* `T_dia` is `ex_intro` at `t_dia` with the term forgotten, and the canonical
      model already builds `t_dia`: `World.realW` gives each term a realising root `c_t`, and
      `RealDatum.spec` says `c_t` satisfies everything `t` does. That is a Skolem function for
      `T_dia` kept in the model. The option moves it into the syntax.
    - *What it would save* — most of steps 3–4: `posRet_exists` becomes immediate, with no `realW`
      and no chain enumeration of a `⊤` step; `rden` of `t_dia` at the world itself reads the
      subterm `t`, so there is no `hstage` and no stage-first measure; and probably the packing,
      since `t_dia` substitutes to `(θt)_dia` rather than being a constant fixed before later
      constants exist. The witness would also be uniform across formulas in the syntax, not only
      through `spec`.
    - *What it would not save.* `◇_x` is indexed by addresses (`WFF.dia` takes a `VarSymb`), so
      reading `◇_{t_dia} φ` means putting a term in a witness position, which substitution cannot
      do directly; it is `realiseAt` again. The scope criterion of §2b is unchanged: `t` is still
      out of scope in the view, so the rule stays schematic. (This differs from the rejected
      `y.ret` above, which asked for an *address* naming `ret(t)`.)
    - *What it would cost.* The term former, with its cases everywhere and in Leibniz; a new `Ann`
      constructor, since `eqRec` at `◇A` is defined only between terms sharing a witness
      annotation; and a `SubE` case for a term in a witness position.
    - *The trap: fix the extent.* With extent exactly `{w}`, `□_{t_dia}` and `◇_{t_dia}` agree and
      `P(t) ⊢ ∃x. □_x P(x.dia)` becomes provable — strictly stronger than `T_dia`, and the
      singleton design rejected for B (§3 B) coming back in. The extent must be left unspecified
      beyond containing `w`, with a model operation `Dom A w → Pos A w` (§6's `posUnit`); then the
      logic is `T_dia`'s.
    - *Balance.* Extra syntax against the model-side work that was the bulk of steps 3–4:
      comparable at least, possibly cheaper. The same choice will face strong B's inward half,
      which is schematic like T's (§2b): a `World.real` analogue, or this term former.
  - **Candidate: necessary-object strong T (2026-09-19).** A third T principle, Barcan-like —
    everything is the here-value of a necessary object:

    ```
    NecT:   P(a) ⊢ ∃u:□A. P(u.here)
    ```

    Carrier condition: every `a ∈ D(w)` is `necExtract n` for some `n ∈ Nec A w`. It requires new
    objects, so it is *strong* by §2a's criterion, and it is independent of `T_dia`: `T_dia`
    produces possible objects, not necessary ones. Both ends of T's loop are the same world, so `P`
    may mention anything in scope at `w` — including `a` itself and quantifiers over parameters —
    and NecT needs no packing. State it schematically, not as the equation `∃u. u.here = a`, which
    is statable only at `◇`-free types (§2b).
  - **⭐`T_dia` factorises through NecT (checked on paper, not in Lean).** To derive
    `∃x:◇A. ∀y. (ψ↓(t,y) → ◇_x ψ(x.dia, y))`:
    1. NecT at `P(z) := ∀y. (ψ↓(t,y) → ψ↓(z,y))`, whose instance `P(t)` is a tautology, gives
       `u : □A` with `∀y. (ψ↓(t,y) → ψ↓(u.here,y))`, chosen before `y`.
    2. `T_dia` at `𝟙` for `χ(y) := ψ(u.box, y)` — a `□`-view formula, since `u.box` is a
       `□`-item — gives `z : ◇𝟙` with `∀y. (ψ↓(u.here,y) → ◇_z ψ(u.box,y))`; reading here
       collapses `u.box` to `u.here`.
    3. Strength: `x := diatm z _ (u.box)` turns `◇_z ψ(u.box,y)` into `◇_x ψ(x.dia,y)` — the
       `instantiate_exDia` identity of `QML_v12m_StrongD`, under `∀y` and `→`.

    So `T_dia` at `A` ⟸ `T_dia` at `𝟙` + NecT + strength, uniformly in `y`. This is the uniform
    pattern:

    > A possible-object strong principle at type `A` = its instance at `𝟙` (a bare witness) + its
    > necessary-object version (which brings the object into scope as a `□`-item) + strength.

    | | witness at `𝟙` | necessary-object version | object already a `□`-item? |
    |---|---|---|---|
    | D | `⊢ ∃x:◇𝟙. ◇_x ⊤` | not needed | yes |
    | T | `T_dia` at `𝟙` | NecT | no |
    | B | (ii) at `𝟙` (§3 B) | (i) (§3 B) | no |

    Strong T is not being rebuilt this way for now. On the canonical side the work moves rather than
    shrinks: `T_dia` at `𝟙` becomes much simpler (unit content, no stage-first measure), but NecT
    needs its own "the world names its realisations" machinery for `□`-constants read here — which
    is exactly what the realisation predicate above would internalise, so the two notes should be
    read together if strong T is ever revisited.

### 4 (transitivity)
- Frame: `R(v) ⊆ R(w)` for `v ∈ R(w)`.
- *Route (§2c)*: the composite `w → v → s`, which does not return.  The restriction's value law is
  **definitional** (the comonad law, built into how `keep` evaluates), so no axiom states it.  The
  lift's source is an object of `v` and its carrier an object of `w`, and no scope holds both, so its
  pinned form cannot be written at all — a structural reason for its open status, not just a
  difficulty of proof.
- **⭐The `◇` side of 4, missing until now (2026-09-25, paper).**  §2c reads each propositional rule
  as two maps; 4's are `□A → □□A` (`necDup`, done) and its dual `◇◇A → ◇A`.  The second was never
  considered: `Frame.Ops` has `necExtract` for T and `necDup` for 4, and on the `Pos` side only
  `posMap` and `posStrength` — **no flag-guarded operation at all**.  `GFunc` likewise has `dup` and
  no dual.
  - *The per-arrow transport is free.*  For `a : w → v` and `q : Pos A v`, composing `a` with the
    arrows of `q`'s extent gives a set of arrows out of `w` with the **same values at the same
    targets**.  So `Pos A v → Pos A w` invents nothing, and along a chain the possible objects can
    only shrink: each deeper world's appear here as images.  This is the exact dual of weak 4's
    restriction, and it is **not** the lift — the lift is `Nec(v) → Nec(w)`, which must invent values
    at the arrows in `R(w) \ R(v)`.
  - *But it cannot be named per arrow*, since the name would have to mention `v` (§2c, axis 4: names
    travel inward, and this map goes outward).
  - *Gathering over the arrows gives the join* `◇◇A → ◇A`, whose extent is the set of composites.
    **Catch:** two different intermediate worlds may reach the same world with different contents, so
    the value function need not be well defined — and since `posEval` is injective, an object *is* its
    extent-and-values, so in that case there is no such object.  In an **arrow** frame composites are
    distinct arrows and the join exists; in a **relational** frame it may collide.
  - *Consequences.*  By §2a's criterion the gathered form is **strong**, not weak: where routes
    collide a value must be chosen, and choosing asserts a new object.  And it would be sound on
    arrow frames but not on arbitrary relational ones, which makes it the first candidate principle
    that **separates the two model classes** — see `v12-arrow-canonical.md` §4, whose unravelling
    argument assumes they do not come apart.  Both points want checking before any flag is added.
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
- **Weak B: implemented (2026-09-19), sound; complete without T and 4 for contexts of declared
  variables (2026-09-19, `BArrow.completenessB`, `QML_v12m_BCompleteness`).** Flag `ModalSys.B`; frame
  condition `Frame.symm` (every arrow `w → v` has *some* arrow `v → w`; existence only). Rule
  `Proof.B_dia`: `◇□ψ ⊢ ψ` for closed `ψ` (`WFF.closed`, weakened from `Ctx.empty`; `WFF.diaBox`
  is `¬□¬□`). `Proof.B_box` derives the familiar `ψ ⊢ □◇ψ`, and `Proof.B_dia_of_box` goes back,
  so the two forms are interderivable in K. The rule's form is the one the canonical check already
  used (`QML_v12m_ArrowCheck`).
  - *Substitution*: `ψ` is closed, so it crosses any substitution unchanged
    (`WFF.subst_mono_empty`, moved from `ArrowCheck` to `ProofSubst`, which now imports
    `SubstId`); `WFF.diaBox_closed` makes `◇□ψ` itself closed.
  - *Soundness*: a closed formula's truth depends only on the world (`Model.sat_closed`); `◇□ψ`
    gives an arrow `w → v` after which `ψ` holds everywhere, and `symm` gives one back to `w`.
  - *The staged canonical model excludes it*: its frame cannot satisfy `symm`, so `Canon.frame`
    and everything after it (completeness, strong completeness, compactness) assume
    `[ModalSys.NoB]` (the pattern `ModalSys.NoTStrong` used before strong T was complete).
  - *Completeness* comes from the arrow-based canonical model instead
    (`docs/v12-arrow-canonical.md` §6a), with `[ModalSys.NoFour]` (4 off; T and D
    may be on, in either strength) and for contexts of declared variables: a world language `ctxOf l₀`, or
    ⭐**every presented context** whose presentation is fresh (`completenessB_presented`,
    `QML_v12m_BFlat`), via chains of atomic pairs; the special cases are also stated directly
    (`completenessB_ofDecls`, `completenessB_boxIn`, `completenessB_diaIn`,
    `completenessB_boxInN`). ⭐Strong completeness and compactness too (`strong_completenessB`,
    `compactnessB`, `model_existenceB`, `QML_v12m_BCompactness`). Open: B with T or 4.
  - *Not yet*: the two strong Bs below.
- **Redesigned 2026-09-19** around necessary objects, and sorted by §2a's criterion (weak = no new
  objects, strong = new objects). One weak B and **two** strong Bs. `P` below is a formula closed
  apart from its hole, since it is read both at the origin and two views in; several parameters
  are packed into the hole with a tuple, as for strong T.

  | | new objects | principle |
  |---|---|---|
  | **weak** | none | propositional `φ ⊢ □◇φ` |
  | **strong, necessary** | a `□□`-object whose round trip `w → v → w` returns `a` from *every* `v` | (i) `P(a) ⊢ ∃u:□□A. □◇P(u.box.box)` |
  | **strong, possible** | a possible object at each `v` reaching back with content `a` | (ii) `P(a) ⊢ □∃x:◇A. ◇_x P(x.dia)` |

  - The outward forms — value at the origin, which is evaluation and so asserts nothing new — are
    **theorems of weak B**: `◇□P(u.box.box) ⊢ ∃x:A. P(x)` for `u : □□A`, its witnessed variant
    `◇_y □P(y.dia.box) ⊢ ∃x:A. P(x)` for `y : ◇□A`, and the born-inside export
    `◇∃c:□A. □P(c.box) ⊢ ∃x:A. P(x)`. Each takes `ψ := ∃x.P(x)`, which is closed, and B's
    contrapositive `◇□ψ ⊢ ψ`. *(Paper only.)*
  - (i) is strictly stronger than weak B, which gives only `□◇∃x.P(x)`: it moves the `∃` outside,
    one `u` for every `v`. For B's full strength the round trip must return `a` from *every*
    accessible `v`; from only some `v` it would give `φ → ◇◇φ`.
  - (i) and (ii) look independent. (ii) does not give (i): gathering one possible object per `v`
    into a single `□□`-object is a `□∃ ⊢ ∃□` step, which is modal choice. (i) does not give (ii):
    it produces no possible objects. (ii) at type `A` follows from (ii) at `𝟙` plus (i) plus
    strength — the uniform pattern of §3 T. *(Paper only.)*
  - (i) is to B what necessary-object strong T (§3 T) is to T, with T's loop `w → w` replaced by
    the round trip `w → v → w`.
- **⭐The relational form (2026-09-25, paper only).** Both principles above are *outward* and
  *per-formula*, the shape §3 T's realisation-predicate note criticises — and here the per-formula
  weakness is forced, not incidental. §2b's pinning trick (take the instance `φ(z) := (z = u.box)`)
  needs the source in scope; for (i) the source `a` is a base object of `w`, invisible two views in,
  so `u.box.box = a` is not even a formula and nothing pins `u`.  That is §2b's "object already a
  `□`-item? — no" row for B.  Consequently (i) as stated is strictly weaker than its own intended
  reading: "for every `v`, some continuation where `P` holds of the value" only approximates "the
  round trip returns `a`", since formulas closed apart from their hole cannot express identity with a
  particular object of `w`.

  **The fix is a primitive relation, as for T.** Where T names the value at its identity loop
  (`Here x t`), B names the value around its round trip:

  ```
  Back u t  :=  ∀ (a₁ : w → v),  ∃ (a₂ : v → w),  u(a₁)(a₂) = t
  ```

  for `u : □□A` and `t : A` at `w` — "from every `v`, *some* homeward arrow returns `t`".  Its
  semantics uses equality in the model, so nothing needs `eqRec` and `◇`-types are unproblematic.

  **The quantifiers are forced, not chosen.** `φ(t)` is a statement at `w`, so soundness needs one
  round trip that returns to `w`, carries `t`, and satisfies `φ`; that fixes which predicate pairs
  with which premise *(paper)*:

  | predicate | premise | sound? | matching introduction gives |
  |---|---|---|---|
  | `∃a₁ ∃a₂` returning, value `t` | `□□φ` | ✓ | only `◇◇φ` — too weak (cf. the `φ → ◇◇φ` remark above) |
  | `∃a₁ ∃a₂` returning, value `t` | `◇□φ` | ✗ the two `∃a₁` need not agree | — |
  | **`∀a₁ ∃a₂` returning, value `t`** | **`◇□φ`** | **✓** | **`□◇φ`** — exactly (i) |
  | `∀a₁ ∀a₂` | `□□φ` | ✓ but overkill | `□◇φ` |

  So the predicate is `∀`(out) `∃`(back) — not every round trip, and not merely some — and one
  predicate serves both directions:

  ```
  Back u t,  ◇□φ(u.box.box)  ⊢  φ(t)           -- elimination
  Back u t,  φ(t)            ⊢  □◇φ(u.box.box)  -- introduction
  ```

  with the strong axiom as surjectivity, `∀a:A. ∃u:□□A. Back u a`.  Then **(i) is derivable**, and
  the per-formula `P` with its tuple-packing goes away.

  - *This is not §4's round-trip coherence.*  Coherence asks all round trips `a ≫ a⁻` to agree — the
    hard condition where 4 meets B.  `Back` asks for one homeward route per `v` carrying the same
    value, leaving the others free.  In the network that is a *per-child* obligation, the shape a
    scheduled operation already has.
  - *No D needed.*  With `◇□` the premise supplies the outgoing arrow.  The `□□` variant would need
    `◇⊤` or D, since at a dead end both premise and predicate are vacuous.
  - *The `∃`-form is already free.*  The outward bullet above records `◇□P(u.box.box) ⊢ ∃x:A. P(x)`
    as a theorem of weak B.  So `Back` does for B exactly what `Here` does for T: the projection is
    free, the **naming** is the new expressive power, and the axiom is its surjectivity.

  **Witnessed variants: one per leg.**  Each leg may quantify over all arrows or over a named
  extent, which fixes the carrier and the address of the round-trip value *(paper)*:

  | out leg | back leg | carrier | value at | premises |
  |---|---|---|---|---|
  | `□` | `□`/`◇` | `□□A` | `u.box.box` | `◇□φ` / `□◇φ` |
  | `◇_y` (`y : ◇□A`) | `□`/`◇` | `◇□A` | `y.dia.box` | `◇_y □φ` / `□_y ◇φ` |
  | `□` | `◇_{c.box}` (`c : □◇A`) | `□◇A` | `c.box.dia` | `◇ □_{c.box} φ` / `□ ◇_{c.box} φ` |
  | `◇_y` | `◇_{y.dia}` | `◇◇A` | `y.dia.dia` | `◇_y □_{y.dia} φ` / `□_y ◇_{y.dia} φ` |

  Since the predicate is `∀`(out) `∃`(back), **witnessing the out leg weakens it** (only a named
  extent must be covered) and **witnessing the back leg strengthens it** (the homeward arrow must lie
  in a named extent).  Two of the four are already here: `◇_y □P(y.dia.box)` for `y : ◇□A` appears
  among the outward theorems of weak B, and (ii) is the witnessed-back form with its witness
  existentially quantified inside `□` rather than carried by a `□◇`-object — the two differing by the
  `□∃ ⊢ ∃□` modal-choice step noted above.

  **The witnessed-back variant is the one to look at first for the metatheory.**  Weak B's
  completeness problem (below) is that "from `v` nothing singles out the origin among its
  successors"; a witnessed back leg is exactly a name for the route home:

  ```
  BackW c t  :=  ∀ (a₁ : w → v),  ∃ a₂ ∈ extent (c(a₁)),  a₂ returns to w  ∧  c(a₁)(a₂) = t
  ```

  reading "every successor has a *named* way home, carrying `t`".  Whether its per-child obligation
  is schedulable in the network the way weak B's are is open, and is the thing to settle before
  choosing which variant to build.
- **⚠ No return-path collapse.** An earlier note here proposed reading a formula of `Γ.boxIn.boxIn`
  back at the origin by a collapse `Γ.boxIn.boxIn ⟶ Γ`. That is **ill-defined**: `u.box.box` read
  at the origin is `u(v)(w)`, which depends on the intermediate `v`, so there is no address at `w`
  for it. T's collapse works only because its loop is unique. The formulation above never reads a
  double-box item back at `w`; its two ends meet only through the hole.
- **Weak B's completeness problem** (2026-09-19). In the Henkin tree, B makes the parent `w`
  accessible from the child `v` — against the order of construction. Every **modal** object of
  `v` (its necessary objects, inherited or born, and its possible objects whose extent can reach
  `w`) then has a value at `w`, which the canonical model must realise by one `w`-term per object,
  respecting the whole type the child's theory gives it. Weak B realises each *finite* piece of such
  a type, but nothing pins one term for the whole: from `w` the equation `z = c.box` is out of
  scope, and from `v` nothing singles out the origin among its successors (which is what the
  rejected singleton addresses provided). T and 4 never meet this: T's loop returns to the same
  world, and 4's chains only go down. Propositional B avoids it by having no objects; classical
  quantified B by constant domains (B + CBF ⊢ BF), which our semantics does not have. Neither
  strong B addresses it, since both concern objects going *out* from `w`. **The proposed way
  forward is `docs/v12-arrow-canonical.md`**: a canonical model with no construction order, arrows
  carrying translations, and B's reverse arrows built back-and-forth.
- *Superseded: the existential strong-B design of 2026-09-18* (`φ↓(t) ⊢ □∃x:◇A. ◇_x φ`, with a
  `realiseAt`-style reading at the origin). Its possible-object content survives as (ii); its
  reading back at the origin relied on the ill-defined collapse above.
- *Rejected: singleton addresses `z↑ : ◇A` with extent `{w}`* (the design to 2026-09-17). It needed
  a new address former, a context principle putting current items inside every modality, and a
  round-trip normalisation (out along `u↑`, back along `y↑`, reducing to `u.box`) — a confluence
  problem on addresses that exists only because the addresses do — and would have met the
  entry-independence problem that `keep` met.

### 5 (euclidean)
- Frame: `R(w) ⊆ R(v)` for `v ∈ R(w)`.
- *Route (§2c)*: out and over, `w → v` and `w → s` giving `v → s`.  Like 4's lift and unlike T and
  B, it does not return to the origin, so no pinned relation is available; both components below are
  transport maps rather than value statements.
- **⚠ To be re-sorted (2026-09-19).** By §2a's new criterion both components below are *weak*: each
  is a determinate map on existing objects (re-use of a witness, restriction), so neither requires
  new objects. The labels below are the old ones. What a new-objects strong 5 would be, if any, is
  open. The canonical model also needs arrows between siblings, which the tree cannot give
  (`docs/v12-arrow-canonical.md`, open question 3).
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
| B + 4 ⇒ 5 (frames) | ✓ | propositional ✓; object level via closure — the component `◇□χ(u.keep.box) ⊢ □χ(u.box)`, valid on B+4 frames but not derivable from closed B + weak 4; conjecturally what makes the canonical round trips coherent (`v12-arrow-canonical.md` §4) |
| strong T + strong 5 ⇒ strong B, strong 4 | ✓ (symmetry turns 5's inclusion around) | ? |
| strong B ⇒ ◇-BF | ✓ | parameter-free ✓; parameterised: open (the return-path collapse once proposed here is ill-defined, §3 B) |
| strong T + strong 4 ⇒ ◇-BF | ✓ | ? |
| anything ⇒ □-BF | ✗ (countermodel) | ✗ |

## 5. Expected status of the modal cube

✓ = expected tractable, ✗ = open (no known link), ? = unclear.

| System | weak | strong | Obstacle |
|---|---|---|---|
| K | done | done | |
| KD | done | done | |
| T | ✓ | ✓ | |
| KB | done (closed) | ✓ | |
| K4 | ✓ | ✗ | lift |
| K5 | ✗ | ✗ | 5's box half without 4 |
| KD4 | done | ✗ | lift |
| KD5 | ✗ | ✗ | 5's box half without 4 |
| KDB | done (closed) | ✓ | |
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
  *(Answered: it could; 4 is implemented with chains of proper steps.)*
- **For B and 5 the tree cannot work** (2026-09-19): B makes the parent accessible from the child,
  against the order of construction, and 5 needs arrows between siblings. The proposed replacement
  is **`docs/v12-arrow-canonical.md`**: every world at once, with arrows carrying a translation
  that is a `Subst` from the source's `□` view into the target's context. The tree is the special
  case `θ = idS`.

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
   - *⭐A lead, not yet acted on (2026-09-28, the user's).*  Composing possibilities may be the same
     mistake §2d's withdrawal found in compound `Here`: a lift that takes `◇` of something to `◇◇`,
     or reads a possibility inside a possibility, is **composing two possibilities nothing has
     joined**.  The rule to look for would therefore take *joint* possibility as its hypothesis —
     one pair-typed witness whose components are the two possibilities, as pairing already provides
     — and only then let the composite be made sense of.  That is exactly the shape the `Here`
     reform failed for, and it is why the base-typed/`◇`-free restriction turned out to be
     principled rather than a limitation.  See §2d's closing subsection and the memory note
     "joint possibility goes through pairing".
2. Weak B without strong B; weak 5 without 4; ◇-BF alone; KB5 weak.
3. Whether B's return path `Γ.boxIn.boxIn ⟶ Γ` is an instance of `Ctx.Collapses` or needs a
   variant (§3 B). This replaces the old question about singleton addresses and round-trip
   reduction, which the existential design removes.
4. How closure of flag sets is computed. (Flags are carried by a typeclass `ModalSys`, with
   `ModalSys.K` all flags off.)
5. Later axis: comprehension principles for carriers (modal choice
   `□∃y. φ(y) ⊢ ∃u:□B. □φ(u.box)`, the `◇`-export). They hold in full models only.
6. Other frame conditions (.2, .3, density, functionality) and GL/Grz are out of scope.
7. Flags per component (§2a) or per weak/strong version? Which components are complete alone, and
   which only in bundles (e.g. weak B with strong B)? Are inward-only systems (5's `Pos` map
   without the euclidean schema) complete?

## 9. Status and work plan *(2026-09-25)*

Organised by axiom and, inside each, by the axes of §2c: the two dual sides of the propositional
rule, then the object-level map inward and outward, then witnessed or not.  This supersedes the
ordering of §7; §5's expected-status table still says what we expect to hold.

**The reading that now drives the design.** `Model.posRet_exists` *is* the statement that the inward
map — the value of a possible object at the identity arrow — is **surjective**.  So outward = inward
+ surjectivity: the inward map needs no frame condition, the strong flag is the surjectivity, and
where the inward map has no canonical value the statement has to be existential.  That last point is
also where the two model classes can come apart: a relational frame has at most one arrow per pair,
so every "which arrow" or "which witness" question collapses there and nowhere else.

### Where each axiom stands

**K** — done.  `K_box`, `K_dia`, `dia_bot`, with `□_x = ¬◇_x¬`; at the object level `necMap`,
`necPair`, `necUnit`, `posMap`, and the one mixing map `posStrength : □A × ◇B → ◇(A × B)`, which is
what lets `D_schema` re-use a witness with new content.

**T** — ✅ **finished** (2026-10-03, §10.41): every cell below is sound and complete, at every
content type.
* weak, `□`-side: `T_box` ✓ — open formulas, via the collapse `Ctx.collapses_boxIn_self`.
* weak, `◇`-side, unwitnessed: derivable in K by duality, **not named** (cheap).
* weak, `◇`-side, witnessed: `Proof.here_elimAt`, `Here x t, □_x χ ⊢ χ(t)` ✓ — weak T relativised
  to the witness.
* object, `□`-side, inward: `extract : □A → A` ✓ (`necExtract_eval`).
* object, `□`-side, outward: does not exist and should not — `A → □A` says everything is necessary.
  The asymmetry is real, and it is why T's two sides look so different.
* object, `◇`-side, outward: `TStrong`, `T_dia`, `posRet_exists` ✓ at **every** content type
  (§10.41: no `hA`; the frame condition reads `Ind`).  `T_dia` hands over the `Here` atom; the
  atom's existential `∃x:◇A. Here x t` is valid but not derivable (`Model.sat_here_ex`), so the
  chain adds it for every term (`World.retW`).
* object, `◇`-side, inward: `WFF.here` at every content type, read as indistinguishability
  (`Ind`); rules `here_elim`, `here_intro`, `here_beta`, `here_name`, `here_subst`, `here_eq` ✓;
  truth lemma `here` case ✓ (§10.40).
* functionality: `here_subst` at any content type and any two annotations ✓; its equational
  instance `Proof.here_fun` is `◇`-free, which is the shape of `eqRec` (one annotation), not a gap.
* tidying left: §10.18 (narrow `here_beta` to its pinned instance).  Combinations: KTB is open
  only because the B canonical model has no T machinery (see §9 B).

**4** — two open maps, and they are not the same axiom.
* weak, `□`-side: `four_box` ✓ — open formulas, via the shift `Ctx.shifts_boxIn_boxIn`.
* weak, `◇`-side, unwitnessed: derivable by duality, **not named** (cheap).
* weak, `◇`-side, witnessed — the join `◇_x ◇_y φ ⊢ ◇_z φ`: **open**.  Transport along a single
  arrow is free; the join needs a composite witness, and it is the likeliest thing to separate
  arrow from relational models.
* object, `□`-side, outward: `dup : □A → □□A` ✓ (`necDup_eval`), with `keep`/`keepOnly`/`GFunc.keep`
  as the witnessed plumbing (under T+4 views expose only `keep`).
* object, `□`-side, inward — `□□A → □A`, bunching the necessary objects: **open**, and its
  propositional shadow is **density**, not 4.  In the axis-5 reading it is *injectivity* of the
  outward map, not surjectivity, so it belongs to the converse axiom; without T it needs the arrow
  to factor, which is why it may only make sense in arrow models.  Decide which direction earns the
  name `FourStrong` before implementing either.

**D** — the self-dual case, so one weak rule and one strong axiom rather than two of each.
* weak: `D_box` (`□⊥ ⊢ ⊥`) ✓ and `D_dia` (`□φ ⊢ ◇φ`) ✓, interderivable in K both ways ✓.
* strong, witnessed: `D_ex` (`⊢ ∃x:◇𝟙. ◇_x ⊤`) ✓, `D_schema`/`D_schema'` at every type ✓,
  frame side `posSerial` ✓.
* inward / graph form as a relation: **open**.

**B** — weak done and complete; strong is the next real piece.
* weak, `◇`-side: `B_dia`, `◇□ψ ⊢ ψ` for closed ψ ✓; `□`-side `B_box`, `ψ ⊢ □◇ψ` ✓,
  interderivable ✓.
* metatheory: complete for every presented context, with strong completeness and compactness, under
  `NoFour` (4 off; T and D in either strength) ✓ (`BArrow.completenessB_presented`, 2026-10-03).
  **B with 4 is open.**
* strong B: **open**, and the decision is taken — see below.

**5** — nothing: no flag, no rules, no frame condition, no canonical model.  The arrow canonical
model (`docs/v12-arrow-canonical.md`) is the intended route, after B.

### Decision: strong B goes the relational route *(2026-09-25)*

Of the two designs in §3 B — a fifth network operation per formula, or the relation `Back u t` —
take the **relational** one.  It fits what the weak-B work actually produced: the canonical model
for weak B came out relational, with no unravelling needed, so the route back is already a relation
between an object at the origin and a value after the round trip, and the forced ∀out/∃back pairing
is the honest shape of "some round trip returns to `t`".  It also matches the inward reading above:
`Back` is a predicate because the returned value has no canonical name, exactly as `Here` is.

### Is `B_dia`'s closedness restriction the right one?

It is the odd one out, and for a principled reason rather than an accident.

* Every other weak rule comes with a **context translation**: T collapses `Γ.boxIn` onto `Γ`, 4
  shifts `Γ.boxIn` one view further in, D needs none.  B would need a translation
  `Γ.boxIn.boxIn ⟶ Γ`, and there is none: `Frame.symm` asserts only that *some* arrow comes back,
  and no law relates a value read two levels in and back to the value at the origin.  An
  open-formula form would therefore be unsound, not merely unprovable.
* It is not an artefact of the proof: weak B **is complete** for every presented context with the
  closed rule.  So no sound open-formula strengthening is missing.  Anything stronger has to add a
  frame condition — which is precisely strong B, and why `Back u t`'s content is "the route returns
  *to* `t`".
* Where the restriction is mis-*shaped* rather than mis-sized: "closed" is a syntactic proxy for
  **route-independent**.  The back-arrow returns to the very same world, so world-dependent data is
  fine — a closed formula may use any function and relation symbols of the signature, since
  `funcInterp`/`relInterp` are read at the world we return to.  What closedness excludes is exactly
  the addresses, i.e. the data read through views, which is what the round trip cannot carry.  If a
  route-free fragment (or rigid constants) is ever wanted, the restriction can be widened to exactly
  that; the general answer remains strong B.

### Order of work

> **Superseded (2026-10-03)** by `docs/v12-roadmap.md`; this list and the "START HERE" block
> below predate §10.23–10.41 and describe the retired `◇`-equality package.

1. **Stage 3 for `Here`**, second half: the truth lemma's `here` case.  The rules are in place
   (`here_elim`, `here_intro`, `here_beta`, `here_fun`, all sound and substitutable).  What remains is
   `real` driven by the `Here` sentence (`Canon.spec_of_here` already derives `spec` from it) and the
   interpretation of a realising term that the Henkin order supplies *late* — and the route for that
   is the open decision of §3 T (2026-09-26): base-only strong T, §2d's model half then naming, or
   paired declarations with `hstage` weakened to `≤`.  Base-only realisation is **refuted** (a view
   sees only `Γ.boxIn` and the content address, so compound contents cannot be hung on the body), and
   since the truth lemma's `diaEq` case needs §2d's model half anyway, avoiding it saves nothing.
   Done already: ⭐`interp_dia_self_core` takes whatever the induction asks of its stages as a
   parameter (`StageOK`), and ⭐`interp_dia_self_base` is the realised case at base content — no
   `IHt₀` and no stage condition, `interp_canon_base` supplying the realising term's value
   (`interp_canon_base_of`, at a type only provably `Var`).  Both are what any of the three routes
   needs for a base-typed datum.
2. **Cheap naming gaps**: the `◇`-duals of `T_box` and `four_box` as named lemmas; `Actual s` as
   `∃a. Here s a` (functionality is now the rule `here_fun`).
3. **B with T and/or 4**: the missing completeness combinations.
4. **The `◇`-equality package** (§2d) — **agreed as the direction (2026-09-25)**, and the thing the
   build waits on, `here` with it.  *Syntax half done*: `WFF.diaEq`, `diaEq_intro`/`diaEq_elim`,
   soundness, `Proof.subst`, `eqRec` annotation-free at every type.  *Model half, done
   (2026-09-26/27)*: the view renaming (`VarSymb.reView`, `Subst.viewRen`, `Term`/`WFF.reView`,
   `reView_mono`, `reView_mono_boxIn`, `reView_eta_dia`), flatness discharging its side condition
   (`Ctx.LevelFlat`, off `Ctx.Presented`), the identification and the extent up to it on its **proper**
   part (`World.PEqW`, `extent`, `extent_congr`, `DiaView.inj`, `tagOf`), the transfer
   (`Proof.boxx_reView`, `World.boxx_mem_reView`), the tagged reading through `rden` and
   `interp_canon` (`tagBody`, `tagWFF`, `tagBody_stage`, `rden_tagBody_congr`,
   `diaPush_agree_canon`), and the truth lemma's `dia` case.  *What remains*: the **self** part of
   the extent, which needs realisedness to be `≐`-invariant and so waits on `real` being driven by
   `Here` (§3 T, Stage 3, itself waiting on naming at `◇`-types); then the `¬HereOnly` construction
   trigger and the two degenerate right-rules with their cut reductions; then the `diaEq` case.
   Then its dependents, in order: `hereRec` (compound `Here`), annotation-free general Leibniz, and
   the "that one" statements of 4's join and strong B's `Back` (§2d, "What the reform unblocks").
5. **Strong B**, relationally (`Back u t`), with its witnessed variants.
6. **4's two open maps**: the witnessed join, and the inward/density direction.  Settling the join
   also settles whether the official model class is arrow-indexed.
7. **5**, then the general metatheory of `docs/v12-metatheory-todo.md`: generalisation on constants,
   uniform substitution, cut elimination, Craig interpolation, `T_dia∀ ⇔` positive-Φ.

### ⭐START HERE next session *(rewritten 2026-09-28, after steps 1–3)*

**State of the build.**  The whole `QML_v12m_*` module list builds with **one error**:
`Completeness.lean:273`, the truth lemma's `here` alternative.  No sorries, no warnings.
`Compactness` and the B track import `Completeness`, so they wait on that case.

*Build the **whole module list**, not a target:*
`lake build $(ls QML/QML_v12m_*.lean | sed 's|QML/|QML.|; s|\.lean$||')`.

**The design, settled** (§2d's closing subsection — read it before touching the Canon layer).
Equality of `◇`-terms lives inside one fibre; to compare two possibilities you **join** them by
pairing.  `Here`, `Proof.here_fun`, `T_dia`, `RealDatum`, `World.realW` and `Model.posRet_exists` are
uniform over **`◇`-free** content types (`VarType.diaFree`, `Ann.eq_of_diaFree`).

**Landed since the withdrawal**

1. **Step 1** (`a1599ff`): the `◇`-free restriction, including the chain — the term enumeration went
   `◇`-free, `retStep`'s condition gained that conjunct, `RealDatum` the field `hA`.
2. **`WFF.size`** (`544e137`): `.here` now has size `A.eqRecSize + 1` (⭐`VarType.eqRecSize`,
   ⭐`WFF.size_eqRec`), so the truth lemma's `here` case may appeal to **its own** induction
   hypothesis at the equation `here_fun` concludes — faithfulness for free, inside the induction.
3. **Faithfulness** (`9687a35`): ⭐`Canon.rden_eqRec` — at a `◇`-free type, two terms the theory
   equates denote alike.  `□` at a proper successor is ⭐`rden_eqRec_far`, recursing on the distance
   as `interp_box_far` does.  Transports: ⭐`eqRec_collapse`, ⭐`eqRec_shift`.
4. **Naming** (`17d53b6`): ⭐`Canon.exists_name` — every `◇`-free-typed term is denoted by some
   declared root's η-expansion.  No new chain machinery: the equation instantiates a *provable*
   existential (⭐`Proof.exists_eqRec_eta`, ⭐`WFF.instantiate_eqRec_slot`), and `World.exW` now gives
   its witness **at a declared root** (the old form is `World.exW_term`).  Annotation bookkeeping:
   ⭐`Term.castAnn`, ⭐`Term.sigma_castAnn`, ⭐`Canon.rden_castAnn`, ⭐`eqRec_congr`.
5. **⭐Step 3 — the datum's content is an address, and the measure loses its stage.**  Done as one
   change, since the three moves are coupled.  What landed:
   * **The chain reads an address, not a term.**  ⭐`enumAF` enumerates pairs (a `◇`-free type, a
     `VarSymb`) — no context, so ⭐`WorldLang.addrQ n = enumAF (decKT n)` is a plain function of the
     step, and `enumT`/`termQ`/`termQ_chain`/`enumT_mono_congr` are gone.  `retStep`'s guard is now
     "the address is declared at the step's own stage at that type", and the term it declares a
     witness for is ⭐`WorldLang.retTerm` = that address's η-expansion.  `IsRet` carries the guard as
     its third conjunct, and ⭐`exists_isRet_addr` replaces `exists_isRet_term`: *every declared
     address at every stage* is some strong T step's.
   * **`RealDatum`**: `a₀`/`t₀` are gone as fields — the field is ⭐`b₀ : VarSymb` with
     `hb₀ : (L.ctx i₀).ref b₀ = some A`, and `a₀`/`t₀` are `@[reducible]` defs (`Ann.eta`,
     `Term.eta`), so every consumer of `d.t₀` still works.  `hstage` is **deleted**.  `hdecl` stayed
     in its stage form (`i₀.2 < i.2 → declared at ◇A`) and the *type-uniqueness* form is now the
     derived ⭐`RealDatum.hdeclOf` (= `declType`): contexts grow, so a declaration at `◇Y` and the one
     past `i₀` meet at a common stage.  That is the honest reading — `hdecl` has to assert the
     witness *is* declared somewhere (`posRet_exists_canon` needs a stage where it is), and
     uniqueness is a consequence, not an extra assumption.  `CanonDom.realisedLt` is deleted.
   * **`World.realW`** is now: every **declared address** of a `◇`-free type is the content of some
     realised root — three *non-dependent* equations (`d.A = A`, `d.b₀ = v`, `i ≤ d.i₀`), since the
     content no longer depends on the stage.  `posRet_exists_canon` brings an arbitrary term into
     that form with `Canon.exists_name` and `rden_eta_le` (moved to `CanonDom`).
   * **The measure**: `interp_canon`'s `termination_by` is now `(VarType.tsize A, t.size)` — no
     stage.  `interp_dia_self` takes the declaration at `i` instead of a stage inequality and reads
     the content by the lookup `interp_canon_eta`, not a recursive call; `dia_mem_of_sat_self` the
     same, through `hdeclOf`.

6. **⭐Step 4 — realisedness is read off the theory.**  `World` no longer has a `real` field: a
   `RealDatum` is now exactly one stage's worth of facts about the language and the theory (the root
   declared at `◇A`, its content address declared at `A`, and the `Here` atom linking them — field
   `hd₀` and a single-sentence `hhere`, with `hdeclOf` and ⭐`RealDatum.hhereAt` derived), so
   ⭐`Canon.World.real c` is *defined* as "some datum exists, pick one" and `World.Realised x` means
   the theory says so.  `World.realised_of_datum` is the only way realisedness is established.
   * **Why the choice is harmless, and why steps 2–3 had to come first**: ⭐`Canon.rden_here_wd` and
     ⭐`Canon.rden_datum_wd` — two `Here` atoms about one root have the same content type and their
     contents *denote alike*, by `Proof.here_fun` (functionality, an equation because the content
     type is `◇`-free) and `rden_eqRec` (faithfulness).  So the model's pick changes nothing that
     the model can see.  Bridges: ⭐`rden_data_wd`, ⭐`rden_eta_realised_wd`.
   * `World.realW` survives as a field, now purely existential (`∃ c d, d.A = A ∧ d.b₀ = v ∧
     i ≤ d.i₀`); `ofHenkin` supplies it from `exists_isRet_addr` and `retDatum` directly, and
     `chainReal`, `chainReal_ret`, `retDatum_fields` are deleted.

**Then**: 7. `realW` from the *rule* instead of the chain: `T_dia` gives `⊢ ∃x:◇A. Here x (η v)`, so
a witnessed MCS contains the atom at a declared root (`World.exW`), which is a datum — that would
let the chain's `retStep`/`retSet`/`IsRet` apparatus go, and `exW` would have to hand over its
witness's `hfr` as well; 8. the truth lemma's `here` case, which then closes, and with it
`Compactness` and the B track; 9. the metatheory list (`docs/v12-metatheory-todo.md`).

**Superseded — the record of the non-root problem and its solution** *(the four passes below are
history; steps 1–4 of 2026-09-28 solved it: `Ctx.LevelDepth`/`Ctx.ViewFresh` propagate from
`Ctx.Presented`, so no presented context re-exposes its own witness, and the abstraction, the pinned
rules, the semantics and the whole model layer now stand at an arbitrary address — `Subst.diaAbsA`,
`Proof.here_elimAtA`/`here_introAtA`, `Model.sat_realiseAtA`, `Canon.RealDatum` indexed by a
`VarSymb`.  Read it only for why `coh-weaken` was abandoned.)*

**⭐Open, and the decision the `here` case now waits on: realisedness at a non-root address.**
A `RealDatum` is indexed by a **root**, and `World.Realised` is `False` at every other address.  But
`WFF.here`'s subject is an arbitrary `◇`-typed term, and every such term is `Term.diatm x hx s` for
some declared address `x` (the constructors give no other way to build one), so the truth lemma's
`here` case has to say something about each `x` — and the model side of `Here` is membership in
`extent w x` at the world itself, i.e. exactly `w.Realised x`.

*Why non-root subjects are not avoidable.*  A child world's base is `(w.ctx (m, m)).boxIn`, so its
context declares addresses of the form `.step u .box`, at `◇A` when `u : □◇A`.  A parent theory may
contain `□ (Here y t)` for such a `y` — a formula of `(w.ctx i).boxIn`, which is where `□`'s body
lives — and then the child's theory contains `Here y t` about a box-shaped address.  Nothing
refutes such an atom, so the `here` case cannot dismiss it.

*Why the machinery stops at roots.*  `Term.realise` — which computes a witness's content at the
world itself, and which `rden`'s `◇`-at-this-world case goes through (`realisedTerm`,
`Term.realiseAt`) — is keyed to `.root r` with the hypothesis `Γ₁.ref (.root r) = none` in the view.
It is used in exactly one place, the `.diatm y hy t` case, to know `y ≠ .root r`; and it is needed,
because `realiseAddr` matches the *syntactic* address `.step x .dia` and inside the view of an inner
witness `y = x` that address means the **inner** content.  For a root, and for projections of a root,
the hypothesis is free (`Ctx.boxIn` is `none` at a root); for `.step u .box` it fails — such an `x`
is visible in its own view.  Note the *proof system* has no such restriction: `here_elim` and
`here_intro` are stated at an arbitrary `x` because they read hole formulas (`WFF.viewReadTm`,
`WFF.hereRead`), not this substitution.  Three routes:

*Scoped, with a compiling experiment (2026-09-28).*  Restricting `WFF.here`'s subject to a root is
**out**: `□` has to act on all formulas, so `□ (Here y t)` must be statable.  Of the other two, the
"hole formulas in the model" route is not independent — `Term.realiseAt` *is* the hole route already
(`realiseAt = hereRead ∘ diaAbs`), and `diaAbs` is the root-keyed **substitution**, so it meets the
same wall.  What the experiment established, by rebuilding `Subst.diaAbs`/`diaAbsIdx` at an arbitrary
`x` with the `VarSymb.belowDia` API of `QML_v12m_Realise` (which is already stated at an arbitrary
`x`) and re-proving `Subst.Ok` and `Subst.Coh`:

* **the generalisation is mechanical, with no level threading**, because the index map's "not below
  `x.dia`" branch is the identity: `diaAbsIdx x v = match belowDia x v with | some p => (bnd 0).ext p
  | none => v`, `diaAbsIdx_dia` becomes `belowDia_dia_ext`, and `diaAbsIdx_of_rt_ne` becomes
  "`belowDia x v = none` ⇒ the map fixes `v`".  The two `Coh` cases go through unchanged in shape.
* **the one new obligation** is: extending a *visible* address that is not below `x.dia` never lands
  below it.  It fails exactly when some **prefix of `x.dia` is visible in `Γ.diaIn x`** — i.e. when
  `x` itself is a view entry — because then the single address `x.dia` would need two images (the
  outer slot, and the inner content of an inner witness `y = x`).  That is the `coh_of` ambiguity
  `QML_v12m_Realise`'s header already describes, in the abstraction direction.

*And 4 does not avoid it* (the earlier claim here was wrong).  Two corrections.  First, non-rootness
starts at depth 0 and at every flag setting: a context variable `p : (◇A) × B` makes `p.fst : ◇A`
(`Ctx.ref` projects through products), and a `◇_z`-child's context declares `.step z .dia : ◇A` when
`z : ◇◇A`.  Both are *benign* (no prefix of `x.dia` is visible), so the cheap generalisation covers
them.  Second, the *shadowed* case is not a `¬4` phenomenon either: with 4 the view exposes contents
as `u.keep.here` (`VarSymb.inner`, `.here` being a projection step with `(□A).step .here = some A`
under T), so `x = .step (.step u .keep) .here` is `◇`-typed exactly when `u : □◇C` — the same
two-level stack as `.step u .box` without 4.  Nothing here touches reflexivity; the two settings
differ only in the *shape* of the exposure.

*Which direction has to be rebuilt, and what the shadowing actually is (2026-09-28, second pass).*
Only the **abstraction** does.  `Term.realiseAt = Term.hereRead ∘ Term.diaAbs`, and `hereRead`
substitutes at the slot **root** `.bnd 0`, which is unambiguous at any `x`; so realisation comes free
once abstraction does, and the semantic bridges (`Model.sat_realiseAt`, `interp_realiseAt`) keep
their proofs, needing only the recursion's analogue of `Env.substEnv_diaAbs`.

And the shadowing is *not* "stop recursing".  Inside `◇_x` where `x` is itself a view entry, the view
`Γ₁.diaIn x` does not conflate — it **shadows**: `x.dia` there is the *inner* content (the `.dia`
branch of `Ctx.diaIn` wins), while the outer content's readings survive one level in, as `Γ₁.boxIn`
entries `.step (x.dia) .box` — visible because `Γ₁.ref (x.dia)` is the *outer* content's type.  So
below `x.dia` the two readings separate by whether the remaining path crosses a **level** step:
projections stay inner, a level step reads it outside.  Nested `◇_x` views stack this.  Hence the
address map must count levels, and the shape to build is

```
absAddr x k v := match belowDia x v with
  | some p => if k ≤ Step.levels p then (VarSymb.root (.bnd 0)).ext p else v
  | none   => v
```

with `k` the number of `◇_x` views entered (incremented only in the `.diatm y` case when `y = x`;
a `□` view needs no increment, since the level step it crosses is already part of the address and so
is counted by `Step.levels p`).  At a **root** `x` this degenerates to today's `Subst.diaAbsIdx`: a
root is never a view entry, so `k` stays `0` and the test always holds.  `QML_v12m_Realise`'s
`VarSymb.realiseAddr` has no such test — it is unused so far, and only ever applied at a root, where
the question does not arise; the level-aware "below" test is new work there too.

*⭐A cheaper route, found while building the recursion (2026-09-28, third pass): `Subst.Coh` is
stronger than the machinery needs.*  `Coh ι Γ θ` demands `(θ.at v).idxAlong p = ι (v.ext p)` for
**every** visible `v` and **every** path `p`.  But `Term.subst` consumes it in exactly *one* place —
the `.diatm x hx t` case, as `hc x _ hX []`, i.e. at a `◇`-**typed** address along the **empty**
path — and everything else only passes it down, rebuilt by `coh_box`, `coh_dia`, `coh_under`.  The
output annotation is `a.mapIdx ι`, whose indices are exactly the `◇`-nodes.  So the load-bearing
statement is

```
Coh ι Γ θ  :=  ∀ v T, Γ.ref v = some T → ∀ p X, (T along p) = some (◇X) →
                 (θ.at v).idxAlong p = ι (v.ext p)
```

— agreement only at paths that **land on a `◇`-type** — which is still preserved by `box`, `dia`,
`keep` and `under` (each prefixes a step to `p`, and the landing type is unchanged).

Under that reading the abstraction at an **arbitrary** address needs no recursion and no levels at
all.  The conflict the experiment found was at `v = x`, `p = [.dia]`: the entry for the view's copy of
`x` sends `x.dia` to `x.dia`, while `ι` sends it to the slot.  That path lands on the *content* type,
which is `◇`-free (§2d) and so never a `◇`-type — so the weakened `Coh` does not ask about it.  Paths
further below the content land inside a `◇`-free type, so they never ask either; and a path from a
*prefix* of `x` that lands on `x`'s own type `◇A` asks only that `ι x = x`, which holds.  So
`Subst.diaAbs`/`diaAbsIdx` generalise to any `x` whose view has the two properties the experiment
already used, with `Ctx.DiaFreeBelow` supplying the rest.

*⭐Tried, and abandoned — the wall is intrinsic (2026-09-28, fourth pass; branch `coh-weaken`,
commits `87088c8` and its successor, not merged).*  The weakening itself works: `VarType.stepAny`,
`VarType.along`, the weakened `Coh`, and `coh_of`/`coh_box`/`coh_dia`/`coh_under`/`coh_single` with
the `Term.subst`/`WFF.subst` uses and the `coh_*` sites across the tree all build.  But one layer up,
`Subst.IsRen` — which `Term.subst_eta_ren` needs, and so the round-trip the pinned rules rest on —
asks the index map to be **structural on visible addresses**, `ι (u.ext p) = (ι u).ext p`, and at a
shadowed subject `ι (x.ext [.dia]) = slot` while `(ι x).ext [.dia] = x.dia`.  Weakening *that* too
does not help, because the reason is not infrastructural:

> In the shadow case the view's own copy of `x` is a `◇`-typed entry whose content sits at
> `.step x .dia` — the very address the abstraction sends to the slot.  So the term `η x` has **no
> image** in a hole formula over `Γ.boxIn.insert (.bnd 0) A`: that context declares the copy of `x`
> but not a content address for it, the slot having taken its place.  The view's copy of the witness
> is *inexpressible* in the hole language.

So no weakening of `Coh`, `IsRen` or `Ctx.Abstracts` — and no level-threaded recursion either — can
give `realiseAt` at an address that its own view re-exposes.  `WFF.here` at such a subject cannot be
handled by realisation at all.  Two routes remain, and both are design choices:

* **Let the canonical theories deny it.**  The model side is *already* `False` there (`World.Realised`
  holds only where a datum exists), so if the construction can consistently add
  `¬ Here (diatm x bd) t` for every such `x` — and `¬ □ (Here y t)` in the parent, since that is how
  such an atom reaches a child — then both sides of the `here` case are `False` and it closes.  The
  syntax is untouched, so `□` still acts on every formula.  The obligation is a proof-theoretic
  inversion: nothing derives a positive `Here` at a shadowed subject from premises that do not
  contain one.  Cheapest, if that inversion is provable.
* **Stop a view re-exposing its own witness.**  `Ctx.diaIn x` inherits `Ctx.boxIn` wholesale, and it
  is only that inheritance which puts `x` back inside `◇_x` (as `.step u .box` without 4, as
  `u.keep.here` with it).  Hiding exactly that entry restores the principle the `□` view already
  obeys — a view exposes the outer objects' *values*, never the outer objects — at the cost of not
  being able to say, inside `◇_x`, what `u`'s value is at the successor.  Narrow but real, and the
  same loss already exists for the copy's own content, whose address is taken by the outer content.

*Cost of the weakening, for the record*: `Coh` is mentioned in ~34 `QML_v12m_*` files, almost all
of them *proving* a `coh_*` for a
particular substitution; each such proof needs two extra binders and the landing fact, and the five
places that *use* a `Coh` hypothesis need the same.  Broad but shallow, and it removes the need for
the level-threaded recursion entirely — `VarSymb.absAddr`, `Ann.abs` and `Ctx.Abstracts` (commits
`f1c3c0a`, `0287aad`, `a5e2151`) would become unused, though `Ctx.DiaFreeBelow` is still the reason
the weakening is sound here.

*The alternative, if that breadth is unwanted*: realisation and abstraction as
**dedicated recursions carrying the level `k`**, not substitutions, with the `.diatm y hy t` case
split on `y = x` and dispatching to `Term.collapse` when they are equal (the outer content is
shadowed there, and collapse is exactly the rest of the map).  Every piece has a weak-T template:
`Term.collapse`/`Ann.collapse`/`Ctx.Collapses` for the recursions, `Model.interp_collapse` and
`Model.Env.collapseAgree_self` for the semantic bridge.  `Term.realise` already exists in that shape
(root-keyed, typing only).  The sub-question to settle before starting: whether `spec_of_here` and
the pinned rules `here_elimAt`/`here_introAt` need the abstraction direction as well — they currently
go through `WFF.diaAbs` and `viewReadAt_diaAbs` ("every view formula is its abstraction read back"),
and if that is unavoidable the recursion has to be built both ways.

### ⭐Step 5, scoped: what the truth lemma's `here` case needs *(2026-09-28)*

Steps 1–4 landed, so realisedness, the rules, the semantics and the model layer all stand at an
arbitrary address (`feba402`).  The remaining error is the `here` alternative itself, and scoping it
turned up **two obligations that are about the theory, not the machinery**.  Neither is a gap in the
address generalisation; both were hidden behind it.

The model side of `Here (diatm x hx bd) t` is `Model.sat_here_diatm`: the **self arrow** lies in
`extent w x`, and the body's value there is `t`'s.  `Canon.extent`'s self case is
`w'.1 = w ∧ w.Realised x`, and `World.Realised x` means *the theory hands over a `RealDatum` at `x`* —
a pinned atom `Here (η x) (η b₀)` naming `x`'s content by a declared address.  So the `⟸` direction
must get that datum out of an arbitrary atom about `x`.

**(1) At a `◇`-free declared content type the pinned atom is not derivable: the logic needs one more
rule.**  From `Here (diatm x bd) t ∈ T`, `Proof.here_beta` reaches exactly the bodies *built from*
`bd` (`Term.viewReadTm bd s`), and `η x.dia` is of that form only when `bd` already is it — the β rule
moves away from the pinned form, never towards it.  `here_elim` with the hole formula
`∃z. Here (η x.keep) z` would do it, but its premise is `□_x (∃z. Here (η x.keep) z)`, i.e. extent
reflexivity *inside* the view — the strong 4 difficulty of §8.1, not available.  And `ex_intro` needs a
term for the content, which is the very thing missing.

The missing principle is valid and independent:

> **A realised possible object's witness has a content here.**
> `Here (diatm x hx bd) t ⊢ ∃z:X. Here (η x) z`, where `X` is `x`'s **declared** content type
> (`Γ.ref x = some (◇X)`, `X.diaFree`).

Soundness is immediate and, unlike `T_dia`, needs no `posRet_exists`: by `Model.dia_beta` the subject
has `x`'s extent, so the premise puts the self arrow there, and the content of `η x` at that arrow
(`Model.interp_eta`, `Env.ref_dia`) is an element of the domain — which is all the `∃` asks
(`Model.sat_hereAt_extend` is the shape to instantiate).  And it is exactly what closes the case:
`World.mem_of_provable` puts the `∃` in the theory, `World.exW` gives its witness **at a declared
root** with `(L.ctx i').ref (.root (.free c)) = some X` — the datum's `b₀`/`hb₀` — and the
instantiated body is the `hhere` field.  So a `RealDatum`, hence `World.Realised x`, hence
self-membership.

*Note what this does to the chain.*  With this rule the datum comes from the theory for **every**
realised address, so it also subsumes the planned step 7: `retStep`/`retSet`/`IsRet` exist only to
manufacture `realW`, and `T_dia` + this rule + `exW` give both `realW` and realisedness directly.

**(2) At a non-`◇`-free declared content type a datum cannot exist, so the extent's self condition
must stop asking for one.**  Nothing restricts the *witness's* declared type: with `x : ◇◇A`,
`Here (diatm x hx unit) unit` is a formula — the `𝟙` case the `WFF.here` docstring itself describes,
"the extent condition alone, relative to a base term of the view".  But `RealDatum` carries
`hA : A.diaFree` (its pinned atom is a `WFF.here` at content type `X`, and that constructor asks for
`◇`-freeness), so `World.Realised x` is unconditionally `False` there while the theory may assert the
atom — the truth lemma is false as currently set up.  Restricting `WFF.here`'s witness to a `◇`-free
declared type is **not** an option: substitution sends `x` to a `◇`-term over another witness, whose
declared type is unconstrained, so the restriction does not survive it.

The way through is that at such an `x` the content is **invisible to the bodies**: the only address
`Ctx.ref` reaches below `x` in `Γ.diaIn x` is `x.dia : ◇A'` (`VarType.step (◇A') p = none` for every
projection, `.here` included), and a `◇`-typed address occurs in a term only as a `diatm` witness,
which makes that term `◇`-typed — so a body of `◇`-free type cannot mention it at all.  Hence the
content of `diatm x bd` at the self arrow does not depend on `x`'s content: it is `bd`'s `Γ.boxIn`
part read here.  So:

* the extent's self condition becomes the theory's own assertion — `Canon.SelfIn w x`, "`w.T`
  contains some `Here` atom about `x`" — with the datum kept for the content;
* `rden`'s self case splits on `X.diaFree`: as today (`realiseAtA` at the named content) when it
  holds, and a **strengthening** when it does not;
* the one new lemma family is that strengthening: at a `◇`-free type, a term (and a formula) over a
  context does not use its non-`◇`-free-typed addresses, so it comes from the context without them.
  By induction — the `diatm` case never arises, since every subterm of a `◇`-free-typed term is
  `◇`-free-typed — and the same argument gives `here_beta`'s reach in that case, so the theory does
  decide every body's value there too.

**Order of work.**  (1) first: the rule, its soundness case, and the `here` alternative for a
`◇`-free declared content type — which is every atom the construction itself produces, so it closes
the case for the completeness theorem's own contexts as long as they declare no nested `◇`.  Then (2),
which is what makes the truth lemma hold for an arbitrary presented `Γ`.

## 10. The identification at `◇`-type — design pass *(2026-09-28)*

Written while scoping step 5 (the truth lemma's `here` case).  The question this section settles is
whether `Here` can drop its `◇`-free side condition on the content type — equivalently whether a
witness whose *declared* content type is itself `◇`-typed can be handled — and what that costs.
Nothing here is implemented; the recommendation is at the end.

### 10.1 Why the question arises at all

The model side of `Here (diatm x hx bd) t` (`Model.sat_here_diatm`) puts the **self arrow** in
`extent w x`; `Canon.extent`'s self case is `w'.1 = w ∧ w.Realised x`, and `World.Realised x` means
the theory hands over a `RealDatum` — a pinned atom `Here (η x) (η b₀)` naming `x`'s content by a
declared address.  Two facts then force the question:

* **"`x` is realised here" is expressible at every declared content type**, and derivable from any
  atom about `x`: `Dom .VTypeOne w = PUnit` (`QML_v12m_Model.lean:84`), so
  `Here (diatm x hx unit) unit` has a vacuous content clause and says exactly that the reflexive
  arrow lies in the extent; and `here_beta` at `s := Term.unit` produces it from
  `Here (diatm x bd) t`.  So an MCS may assert realisedness of an `x : ◇◇A'`, where a pinned atom is
  not even a formula.
* **The content is observable at the self arrow even when no term can mention it.**  A `◇`-free-typed
  *term* over the view cannot mention `x.dia` when `x.dia` is `◇`-typed (the only address `Ctx.ref`
  reaches below `x` is `x.dia`, `VarType.step (◇A') p = none` for every projection, and a `◇`-typed
  address occurs in a term only as a `diatm` witness, which makes that term `◇`-typed).  But a
  *formula* can: `χ = ◇_{x.dia} ψ` is a formula of `Γ.diaIn x`, and the truth lemma's `dia` case at
  the self arrow realises `χ` by substituting a **term** for `x.dia` (`WFF.realiseAtA`).  So the
  model needs `x`'s content named whenever the self arrow is in the extent — at every type.

### 10.2 What is already there: within-fibre `◇`-equality

`WFF.eqRec` is defined at **every** type, `◇` included:

```
eqRec (◇A) (diatm x _ t) (diatm x _ s) = boxx x hx (eqRec A t s)      -- QML_v12m_WFF.lean:103
```

The shared annotation `.dia x _` forces **one witness**, and the clause then says the bodies agree
throughout that witness's extent — extensionality, exactly as at `□`.  `eqRec_refl`/`symm`/`trans`
cover it (`QML_v12m_Eq.lean`), via `K_dia`/`dia_bot`.  So the fibre-internal row is complete.

What the canonical model needs, and what is missing, is the **cross-fibre** case: two names for one
content over *different* witnesses.

### 10.3 The cross-fibre identification is a rule schema, not a formula

Suppose `Here (η x) (η y)` and `Here (η x) (η y')` with `y ≠ y'`.  Both atoms are at the **self
arrow**, so they say `x`'s content here *is* `y`'s object and *is* `y'`'s object: an identity of two
elements of `Dom (◇A') w`, not agreement somewhere.  Equal possible objects have the same extent and
the same content function, so the identification has two halves, and they are of different kinds:

* **(C1) the extents interchange** — for every `χ`, `◇_y χ ⊢ ◇_{y'} (χ renamed along y.dia ↦ y'.dia)`.
  A set equality; *schematic*, because "the same extent" quantifies over formulas.  Sound: the two
  objects are equal, so `Model.sat`'s `dia` clause reads one and the same `posEval`.
* **(C2) the contents agree** — `⊢ □_y (eqRec A' bd (bd' renamed))` for the two bodies.  A single
  formula when `A'` is `◇`-free; when `A'` is itself `◇`-typed it unfolds, by 10.2, into a `□_y` of a
  cross-fibre identification one level in — so (C2) is **recursive in the type**, and at each level
  its extent half is again schematic.

Hence there is no formula expressing "these two possible objects are equal" across fibres, and none
can be added without a new formula former: the notion is a rule schema.  This is the precise content
of §2d's "equality lives inside the fibre", and it is why `WFF.here` carries `hA`.

### 10.4 What the canonical model would need

`RDom (◇A) w = Σ E : Set (Succ w), (w' : E) → RDom A w'.1.1` (`QML_v12m_CanonDom.lean:162`), and
`rden (diatm y hy bd) = ⟨extent w y, …⟩` — the extent component is **literally the address's**.
`Dom (◇A) w` is the definable part of that (`Canon.toDom`/`fromDom`), so elements are `rden`s of
`◇`-terms and distinct witnesses give distinct elements unless both components coincide.  Therefore:

* the theory's chosen name (`World.real`) fixes the model's content; a *second* name in the theory is
  a second Sigma value, and the truth lemma fails at the atom carrying it;
* so the domains must be **quotiented** by co-realisation: `extent w ⟦y⟧ = ⋃_{y' ≈ y} extent w y'`,
  with `≈` the equivalence generated by "some declared `x` has both as its content here";
* set equality then holds by construction, and (C1) is what makes the union coherent — the extent's
  conditions are `DiaView`/`BoxxContents`, built from `□_y`/`◇_y` facts;
* the **content function** must be well defined on the union: for `w'` in `extent y ∩ extent y'` the
  two candidate values are `bd` and `bd'` pushed to `w'`, and they agree because `BoxxContents`
  carries (C2)'s `□_y`-equation into `w'.T`, where faithfulness (`rden_eqRec`) applies.  So (C2) is
  not optional: it is what makes `rden` a function at all under the quotient.

A cheaper-looking variant — keep extents per address, choose a representative, transport the other
atoms along (C1) — does **not** avoid (C2): the transport has to identify the two Sigma values, and
their content components differ exactly by (C2).

### 10.5 Naming: what can and cannot be named

This is the part that most constrains the design, and it is worth stating separately.

* **N1 — a `◇`-typed object cannot be named by a fresh root.**  `Canon.exists_name` works by
  instantiating a *provable* existential `∃z. eqRec T (η z) t` (`Proof.exists_eqRec_eta`).  At `◇`
  that formula is not formable unless `z`'s annotation already matches `t`'s, i.e. unless the name's
  witness *is* `t`'s witness.  So "name this possible object" is only ever available as "name the
  address whose content it is" — which is what `here_name` does, through `Here`, not through `eqRec`.
  A `◇`-typed name carries a witness, and the witness must already be in the context: forced, not
  merely natural.
* **N2 — the Henkin witness of a `◇`-typed `∃` is fine.**  `World.exW` gives a *declared root* `b₀`
  with `(L.ctx i').ref b₀ = some X` at any `X`, and `η b₀ = diatm b₀ (η b₀.dia)` — witness and body
  both supplied.  So `here_name`'s conclusion `∃z:X. Here (η x) z` is witnessed without N1.
* **N3 — a reserved partner does not make the name unique.**  Installing, per address, a fresh
  `p_x : X` with the conditional `Here (diatm x unit) unit → Here (η x) (η p_x)` (consistent, the
  standard conditional-Henkin move) gives the model a canonical name, but an MCS may still assert a
  *second* name over another witness, and nothing derives that the two agree — cross-fibre again.  So
  naming discipline cannot substitute for the identification.
* **N4 — strong T's model condition is `◇`-free by design.**  `Model.posRet_exists` carries
  `_hA : A.diaFree = true` (`QML_v12m_Model.lean:204`), so no model is ever *required* to have a
  realised witness for a `◇`-typed value, and `World.realW`/`posRet_exists_canon`/`exists_name` stay
  at `◇`-free types whatever is decided here.  Dropping `hA` from `WFF.here` would therefore widen
  what theories may *assert* without widening what models must *provide* — which is precisely why
  the canonical model, and not soundness, is where the cost lands.
* **N5 — the chain is unaffected.**  `addrQ`/`enumAF` enumerate `{A // A.diaFree} × VarSymb` because
  `retStep` witnesses `∃x:◇A. Here x (η b)`; that serves `realW`, which by N4 stays `◇`-free.

### 10.6 The measure, for the record

`WFF.size` gives `.here` the budget `A.eqRecSize + 1` so that the truth lemma's `here` case may
appeal to its own induction hypothesis at the equation `here_fun` concludes.  At a `◇`-typed content
the conclusion of functionality is not an `eqRec` but (C1)+(C2), whose formula part is a `□_y` of an
`eqRec` *inside the view* — a formula of a different context, so the budget has to be re-derived
rather than adjusted.  Secondary to 10.3–10.5, but it should be settled on paper before any code.

### 10.7 Verdict

Filling the `◇` row is coherent and is the principled treatment: co-realisation through a common
address *is* the join that §2d asks for before two possibilities may be compared, so the
identification is legitimate exactly where the canonical model needs it.  But it is not a small
addition: it is a schematic congruence (C1), a type-recursive equation (C2), a quotient of `RDom`,
`extent` and `rden`, faithfulness at `◇` types, and a new measure — i.e. a restricted reinstatement
of the withdrawn `◇`-equality-by-extensionality reform (§2d), with the restriction being what makes
it sound to attempt.

The alternatives keep `hA` and differ only in what completeness claims:

1. **`◇` over `◇`-free types only** (a side condition on the type former, or on `Ctx.Presented`):
   every declared content type is `◇`-free, `here_name` is unconditional because the condition is
   vacuous, and step 5 closes with the machinery in hand.  `◇(A × B)` and nested `◇`-*formulas* are
   unaffected; `◇◇A` as a *type* goes.
2. **Keep `◇◇A` and restrict the metatheorem**: completeness for presented contexts whose declared
   types have no nested `◇`.  Nothing in the logic changes, the build goes green, and 10.3–10.6 stay
   open as the upgrade path.

### 10.8 Solutions to risks 1–3 *(2026-09-29; risk 3 WITHDRAWN — see 10.9)*

Scoped after §10.7, on the ruling that a version of strong T with side conditions is not worth
having: the earlier `∃`/positive-polarity formulation was already green and unconditional, so the
`Here` approach has to end up at least as clean.  Each of the three risks has a solution, and
together they remove `hA` from `WFF.here` entirely.  The shape of all three is the same: **an arrow
serves a whole co-naming class of witnesses, each member of the class through a renaming of content
addresses.**

#### The equivalence

`y ≈ y'` at a world `w`: the equivalence generated by "some declared `x` has both as its content
here", i.e. by `∃ i bd bd', ⟨i, Here (diatm x _ bd) (…)⟩`-style co-naming — concretely, by

```
∃ x i (s : Term … (◇A) _) (s' : …), ⟨i, Here (η x) s⟩ ∈ w.T ∧ ⟨i, Here (η x) s'⟩ ∈ w.T
       with s, s' the ◇-terms over y, y'
```

closed reflexively, symmetrically and transitively.  It is a relation on `VarSymb`, defined from the
world's own (final) theory, so it is fixed per world and needs no stage bookkeeping.

#### Risk 1 — `rden` on the class, via renaming *(solved, and `DiaView` need not change)*

`DiaView x w w'` is a **literal** equality of contexts, `∀ m, w'.L.base m = (w.L.ctx (m,m)).diaIn x`
(`CanonWorld.lean:349`), so a child is built for exactly one witness and two witnesses can never
share one by weakening that equality.  They do not have to: let the child keep its own witness `y''`,
and let every **other** member of the class reach it through the canonical renaming of content
addresses, `y.dia ↦ y''.dia` (identity on the `boxIn` part, which the two views share).  Then

* `extent w y := {w' | w' is a child built for some y'' ≈ y, with □_y-contents transported **along
  that renaming**} ∪ {self, when y is realised}`;
* `rden (diatm y hy bd)`'s content at such an arrow is `rden` at the child of `bd` renamed to `y''`;
* for `y ≈ y'` the two extents are the *same set* — the condition quantifies over the class, which is
  shared — so `rden`'s two Sigma values agree in their first component with no quotient type, no
  choice of representative, and no merging of worlds;
* y's own content at an arrow built for `y''` is *defined* as `y''`'s content there, which is exactly
  how the theory treats it: `BoxxContents` transports `□_y χ` along the same renaming.  Model and
  theory therefore agree by construction rather than by an extra lemma.

What this costs is uniform and mechanical rather than deep: the consumers of `DiaView` currently take
a context inclusion (`DiaView.le`, `extent_le`, `Acc'.boxIn_le`) and move formulas with `WFF.mono`;
they become renamings and move formulas with `WFF.subst` along a `Subst.IsRen`.  `Subst.IsRen`,
`Term.subst_eta_ren` and the B track's `QML_v12m_BRename.lean` are the templates.  The chain is
untouched.

#### Risk 2 — faithfulness at `◇`, with no circularity *(solved)*

`rden_eqRec` (`CanonDom.lean:583`) recurses on the **type**, and that is what breaks the apparent
circularity at the self arrow.  For `eqDia (◇A) s s'` (below) the proof splits by arrow:

* **proper arrows**: the `□_y`-form of the premise is transported into the child by
  `BoxxContents` (along the renaming of risk 1), and faithfulness **at `A`** — a smaller type —
  applies there;
* **the self arrow**: the content is computed through the datum, and the premise is a `□_y`-formula,
  so `Proof.here_elimAtA` (`Here (η y) t₀, □_y χ ⊢ realiseAtA y t₀ χ`) turns it into an equation
  *here*, between the two realised bodies; one new transport lemma — realisation commutes with the
  equality former, the analogue of the existing `eqRec_collapse`/`eqRec_shift` — puts it in the form
  faithfulness at `A` consumes.

So the datum is used only through `here_elimAtA`, never through faithfulness at `◇A`, and the
recursion is well founded on the type as it already is.

#### Risk 3 — the content half is a formula; the extent half is a rule, and needs no recursion *(solved)*

Generalise the equality former at `◇` to two annotations, by renaming:

```
eqDia (◇A) (diatm y _ bd) (diatm y' _ bd') :=
  boxx y  (eqDia A bd (bd' renamed y'.dia ↦ y.dia))
∧ boxx y' (eqDia A (bd renamed y.dia ↦ y'.dia) bd')
```

with the other clauses as in `WFF.eqRec`.  The recursion is on the type and **closes**, because the
`◇` clause no longer requires the two witnesses to agree — which is exactly why the present `eqRec`
could not state it (its `◇` clause matches one annotation `.dia x _`, `WFF.lean:103`).  At equal
annotations it is `eqRec` up to the duplicated conjunct.  Then:

* **functionality** becomes unconditional: `here_fun` concludes `eqDia A t t'` at **every** content
  type, so `WFF.here` loses `hA`, and with it `RealDatum.hA`, `spec_of_here`'s `hA`, and the
  `◇`-free conditions on `here_name` and on the chain's enumeration;
* `eqDia` is what `BoxxContents` transports, so it is the half that has to pass between levels — and
  it does, being a formula;
* the **extent half** stays a rule: from the two *pinned* names `Here (η x) (η y)` and
  `Here (η x) (η y')`, infer `◇_y χ ⊢ ◇_{y'} (χ renamed)`.  Pinnedness is what makes it sound —
  with general bodies the premises equate the *terms'* contents, not the witnesses' own, and the rule
  would be false — and pinned names are what `World.exW` produces, so nothing is lost.
* **the rule needs no recursion**: deeper levels are handled by their own worlds, each with its own
  theory, its own `≈` and the same rules.  Only `eqDia` crosses levels.

#### What is left uncertain

1. The breadth of the `mono → subst`-along-a-renaming change in the Canon layer (risk 1).  Every
   `DiaView`-derived inclusion and the `diaPush` agreement lemmas are touched; none of it is deep,
   but it is the bulk of the work.
2. `≈` must be shown to be an equivalence whose class is *stable under the stage order* — the theory
   is fixed per world, so this should be immediate, but the extent's monotonicity lemmas are where it
   would show up.
3. Whether the extent-half rule wants a primitive form or can be derived from a `□`-version of
   itself under `K_dia`; the canonical model only needs the top-level form.
4. `WFF.size` for `.here` must be re-derived against `eqDia` rather than `eqRec` (§10.6), including
   `eqDia`'s own size, which contains two `boxx`-copies of the smaller comparison.

#### Verdict, revised

With the above there are **no side conditions**: `Here` at every content type, `here_name`
unconditional, nested `◇` witnesses handled, functionality total.  The cost is one new formula former
(`eqDia`, a generalisation of `eqRec`), one new rule (the extent half), one relaxed rule
(`here_fun`), and a renaming-based rewrite of `extent`/`rden`/`BoxxContents` and their consumers —
with the chain, the soundness cases for everything else, and the whole `Abs`/`AbsRules`/`SemAbs`
layer untouched, the last because realisation never needed `◇`-freeness in the first place.

### 10.9 Correction to 10.8: `eqDia` is degenerate, and what that shows *(2026-09-29; its pessimistic verdict is superseded by 10.10)*

**`eqDia` as defined in 10.8 is wrong and is withdrawn.**  Its `◇` clause renames one body into the
other's view, so on pinned terms it degenerates: for any two witnesses `x`, `y`,

```
eqDia (◇A) (η x) (η y)
  = boxx x (eqDia A (η x.dia) ((η y.dia) renamed y.dia ↦ x.dia))  ∧  boxx y (…)
  = boxx x (eqDia A (η x.dia) (η x.dia))                          ∧  boxx y (…)
```

— reflexivity twice, provable whatever `x` and `y` are, and in particular with no extent in common.
The renaming identifies the two content addresses, which is precisely the difference the comparison
was meant to detect.

**What the failure shows.**  Comparing the contents of two possible objects means evaluating both
bodies at **one** arrow with **both** content addresses in scope.  No single view has both: `Γ.diaIn y`
declares `y.dia` only.  So the content half needs a *joint* view — a `◇` over a pair — which is §2d's
pairing principle, in the one place 10.8 assumed it could be sidestepped.  There is no formula, and
no renaming trick, that expresses cross-fibre content agreement.

**And it reaches the model as well.**  If the theory forces two witnesses to be co-extensive, every
arrow of the common extent must carry content addresses for *both*, because both witnesses' `□_·`
facts have to be evaluable there — and `DiaView` makes a child's base one witness's view
(`CanonWorld.lean:349`).  Defining one witness's content at another's child by renaming (10.8's
recipe) is sound only when their **own** contents agree, which co-naming of *terms* over them does not
give.  So the irreducible requirement is that **an arrow carry content addresses for a set of
witnesses**, not one — the labelling the B track's network already does (`kd`, `QML_v12m_BNet*`,
docs/v12-arrow-canonical.md).

**What survives of 10.8.**

* **Risk 2 in full**: faithfulness at `◇` recurses on the type, proper arrows by `BoxxContents`, the
  self arrow by `Proof.here_elimAtA` plus a realisation/equality transport.  No circularity.  This is
  independent of the rest.
* **Risk 1, half**: the extent as a union over the co-naming class removes the need for a quotient
  type and for merging *worlds*; what it does not survive is the content recipe, per above.
* **Within-fibre well-definedness needs nothing new**: two names over the *same* witness are compared
  by the existing `eqRec` (`□_z (eqRec A' bd₁ bd₂)`, one annotation), which `here_fun` already gives
  and `BoxxContents` already transports.  It is only across witnesses that the wall stands.

**Position for the next session.**  Either (a) `Here` stays `◇`-free in its content type and the
metatheorem is stated accordingly (§10.7 alternatives 1–2), or (b) strong T with `◇`-typed contents is
built on an arrow-labelled canonical model where an arrow serves a set of witnesses.  (b) is the
principled route and now has a definite shape rather than a hope, but it is a new canonical
construction, not an extension of the tree one.  Nothing in the syntax layer is wrong: `Here`,
`here_beta`, `here_fun`, `here_name`, the abstraction and the realisation are all type-generic
already — the obstruction is entirely in how the tree construction builds arrows.

### 10.10 ⭐The resolution: interchangeability, not equality *(2026-09-29, supersedes 10.9's verdict)*

*(The rule named `here_swap` below is superseded by `here_subst` in 10.11 — same purpose, substitutional form, and it also absorbs `here_fun`.)*

Two rulings from the user, and the second one dissolves the obstruction.

**Nested modal types are intended.**  `◇◇A` is the term counterpart of `◇◇φ`: ordinary propositional
modal logic has nested diamonds and no way to join two diamond formulas into one — to get *joint*
possibility one first conjoins and then applies `◇`.  Terms are the same, with pairing in place of
conjunction: `◇(A × B)`, never a join of two separate `◇`s.  So restricting the type former (10.7
alternative 1) is out, and so is restricting the metatheorem (alternative 2).

**We never needed equality at `◇`-type.**  The rule of 10.8 does not equate anything; it says two
co-named witnesses *prove the same things, inside a diamond, after substitution*.  That is all the
canonical model needs, because canonical objects are built out of what the theory proves.

#### The construction

For a `◇`-term `s = diatm y hy bd`, define its **interchangeability class**: `s ≈ s'` iff for every
hole formula `ψ` over `Γ.boxIn.insert (.bnd 0) A'`,

```
⟨i, ◇_y  (viewReadTm bd  ψ)⟩ ∈ w.T   ⟺   ⟨i, ◇_{y'} (viewReadTm bd' ψ)⟩ ∈ w.T
```

(terms lifted to a common stage, as elsewhere).  This is the `here_elim`/`here_intro`/`here_beta`
idiom — facts about a possible object are hole formulas read with its body — so it needs no new
machinery.  Then the canonical object of `s` is

* **extent** = the union, over the class members, of **their own** witnesses' children (`DiaView` and
  `BoxxContents` unchanged, just quantified over the class), plus the self arrow when realised;
* **content** at an arrow contributed by the member `⟨z, b⟩` = the value of **that member's own body**
  `b` there.

The content clause is what 10.8/10.9 got wrong: no renaming of one witness's content address into
another's view is needed, because each part of the extent is read through the term that contributed
it, and `b` lives in `z`'s view, which already embeds into that child's language.  So the objection of
10.9 — that an arrow would have to carry content addresses for several witnesses — does not arise, and
**the tree construction survives untouched**: children stay one-witness, the chain is unchanged.

#### Well-definedness, by Leibniz rather than by equality

Two members over the *same* witness `z` must denote alike at their shared children.  Take the hole
formula `ψ := eqRec A' (η slot) (b' weakened)`.  Its `b'`-instance is `eqRec A' b' b'`, in the child's
theory by reflexivity; interchangeability therefore puts its `b`-instance `eqRec A' b b'` there too,
and faithfulness (`rden_eqRec`) turns that into equal denotations.  At `◇`-free `A'` that is the whole
argument.  At `◇`-typed `A'` it closes **definitionally**: contraposing the rule at `ψ := ¬ψ₀` (using
that `viewReadTm` commutes with `¬`) gives the `□`-dual, `BoxxContents` carries it into the child, and
what arrives there is exactly interchangeability of `b` and `b'` *at the child* — i.e. membership in
one class there.  The recursion is on the type, as `rden` and `rden_eqRec` already are.

#### The rule, and why it is the load-bearing one

```
here_swap (hT) (x) (hx : ∃X, Γ.ref x = some (◇X)) {A'} …
  (y)  (hy)  (bd  : Term σ (Γ.diaIn y)  A' _)
  (y') (hy') (bd' : Term σ (Γ.diaIn y') A' _)
  (ψ : hole formula) :
    Here (η x) (diatm y hy bd) → Here (η x) (diatm y' hy' bd') →
    ◇_y (viewReadTm bd ψ) → ◇_{y'} (viewReadTm bd' ψ)
```

Sound: both premises say `x`'s content **here** *is* the respective object, so the objects are equal;
each conclusion quantifies over that one extent with the hole taking that object's content at the
arrow.  Note it is stated at *general* bodies and is still sound, because the hole formulas speak of
the objects' contents, not of the witnesses' own — which is what the 10.8 formulation got wrong when
it spoke of `◇_y χ` directly.

Its job is to make **co-naming imply interchangeability**, which is what the truth lemma's `here` case
needs: a second name for `x`'s content must land in the datum's class.  The `dia` case then goes
through the same relation in the other direction — an arrow contributed by `⟨z,b⟩` gives
`◇_z (viewReadTm b ψ)` ∈ T by the existing argument, and interchangeability transports it to
`◇_y χ` ∈ T, with `χ = viewReadTm (η y.dia) ψ` by the abstraction round trip
(`WFF.viewReadAtA_diaAbsA`).

#### Rule set, and what changes

Rules: the four existing `here_*`, plus `here_name` (§10.8, unconditional), plus `here_swap`.  No
`eqDia`, no new formula former, no cross-fibre equality, no side conditions — `hA` leaves `WFF.here`,
`RealDatum`, `spec_of_here` and the chain's enumeration.

Canon layer: `extent` becomes a function of a `◇`-**term** (`extentTm w s`) via the class; `rden`'s
`.diatm` clause reads the contributing member's body; `canonEnv_extent`, `extent_le`,
`diaPush_agree_canon`, `dia_mem_of_sat_self` follow the same rewrite.  Faithfulness gains its `◇`
case (10.8 risk 2, unchanged: recursion on the type, self arrow via `here_elimAtA`).  `WFF.size` for
`.here` is re-derived against the `◇`-free `eqRec` it already uses, so §10.6 is no longer a worry.

#### Still to check before coding

1. `≈` is an equivalence, and its class is stable under the stage order (the theory is fixed per
   world, so this should be routine; it shows up in the extent's monotonicity lemmas).
2. The union's arrows come with the member that contributed them; if one arrow is contributed by two
   members over *different* witnesses, the contents must agree — same Leibniz argument, but the hole
   formula lives in two different views, so check whether the pair is possible at all (a child's base
   fixes its witness, so it should not be).
3. Soundness of `here_swap` in the `Model` layer: `Model.sat_here_diatm` twice plus `dia_beta`.
4. Whether `here_name` is still needed once `here_swap` is present (it is: `here_swap` relates two
   names, `here_name` produces the first one).

### 10.11 The rule set, settled: `here_subst` replaces `here_fun` *(2026-09-29)*

Two corrections to 10.10, both from the user, both simplifications.

**`here_swap` is wrong shape; the rule is substitutional functionality.**  A `◇`-typed term occurs in
a formula only inside a `here` atom — as its subject, or inside its content term — and `WFF.dia`/`boxx`
take an *address*, not a term.  So a Leibniz-shaped rule must be stated as substitution for a **slot**,
and the `◇`-fact transfer of 10.10 is then one of its instances: with `φ := ◇_{.bnd 0} ψ`,

```
(◇_{.bnd 0} ψ)[.bnd 0 := diatm y hy bd]  =  ◇_y (WFF.viewReadTm bd ψ)
```

because substituting a `◇`-term for a witness address is exactly `Subst.dia`/`SubE.diaBody` — which is
also why `here_elim`/`here_intro`/`here_beta` are phrased with `viewReadTm`.  The instances 10.10's
`here_swap` missed are the **content positions**, e.g. `Here s₀ (pair t₁ s')`: once the model
identifies `s` with `s'` it satisfies that atom, so the truth lemma's ⟹ direction needs it in the MCS.
Hence:

```
here_subst (hT) {A} {b} (s : Term σ Γ (.VTypeDia A) b)
    {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
    (φ : WFF σ (Γ.insert (.bnd 0) A) 1) :
  Proof σ Γ Δ (WFF.here hT s t) → Proof σ Γ Δ (WFF.here hT s t') →
  Proof σ Γ Δ (WFF.instantiate _ t φ) → Proof σ Γ Δ (WFF.instantiate _ t' φ)
```

— any subject, any content type, **any two annotations**.  Soundness: the premises give
`interp t = interp t'` (`Model.Realised` reads the content at one arrow — the existing
`Model.sat_here_fun` proof), then `Model.sat_instantiate` twice.

**`here_fun` becomes derivable, so it stops being primitive.**  Take
`φ := eqRec A (t weakened) (η slot)`; then `φ[slot := t] = eqRec A t t` is `eqRec_refl`, and
`φ[slot := t'] = eqRec A t t'` is `here_fun`'s conclusion.  One step, no symmetry.  Existing users
(`rden_here_wd`, `rden_datum_wd`) keep working against the derived `def`.

*Not recovered, and not needed*: at a `◇`-typed content with a **shared** annotation `eqRec A t t'` is
formable but not derivable this way — `eqRec A (t weakened) (η slot)` does not typecheck there, since
`η slot`'s annotation names the slot while `t`'s names its own witness.  §10.10's well-definedness uses
substitutivity directly, and its `eqRec`-shaped hole formula sits at the *body* type inside the child.

**Primitive set after this**: `T_dia`, `here_elim`, `here_intro`, `here_beta`, `here_subst`,
`here_name`.  Derived: `here_fun`, `here_elimAtA`, `here_introAtA`, the realisedness atom
(`here_beta` at `s := Term.unit`).  Dropping `hA` from the `WFF.here` constructor frees `here_elim`,
`here_intro`, `here_beta` (both `hA` and `hB`) and `here_subst` automatically, since each inherits it
from the constructor.

### 10.12 ~~Open~~ Settled (§10.41, `hA` dropped): should `T_dia` keep `hA`? *(2026-09-29)*

`T_dia`'s `hA` is **not** a syntactic necessity — the rule is formable at any `A` once `WFF.here` loses
`hA`.  What carries the restriction is the frame condition `Model.posRet_exists`
(`Model.lean:204`, `_hA : A.diaFree = true`).  Three observations.

1. **Keeping it contradicts the nested-modality reading.**  At base type `T_dia` says an actual object
   is trivially possible, this world witnessing it; at `◇A'` it is the same principle one level up —
   the object counterpart of `φ → ◇φ` at every depth.  Keeping `hA` makes the dual of T apply to
   objects but not to possible objects, the very asymmetry rejected for types in 10.10.
2. **Soundness is a choice, not a risk.**  The condition stays existential: no operation on
   `Frame.Ops`, no uniqueness, no naturality — the reasons the `y.ret` design sank are untouched.
3. **The cost is the naming wall (§10.5 N1).**  `Canon.posRet_exists_canon` routes through
   `Canon.exists_name`, which has no `◇`-type analogue, since `Proof.exists_eqRec_eta` needs the
   term's annotation to *be* the slot's.  So the chain would have to witness `∃x:◇A. Here (η x) t` for
   enumerated **terms** at `◇`-typed `A` instead of enumerated addresses — partially undoing step 3,
   including the measure argument that motivated it.  Likely shape: the address-indexed step for
   `◇`-free content, a term-indexed step above it.

**Orthogonal to the `here` case**: the truth lemma's `here` and `dia` cases go through the datum, and
`World.realW` feeds only `posRet_exists_canon`.  So land the `here` case with `T_dia` as it stands,
then take this up.

### 10.13 ⭐The diagnosis, stated properly: a naming gap, not a comparison gap *(2026-09-29, user)*

The clearest way to see what all of §10 is about.  `WFF.here` strips the leading `◇`: the subject is
`s : Term σ Γ (◇A) b` and the content is `t : Term σ Γ A a`.  Take a **nested** subject,

```
s = diatm x hx (diatm y' hy' bd')  :  ◇(◇A')
```

The atom must then be completed by some `t : Term σ Γ (◇A')`, and a `◇`-term over `Γ` has its witness
**declared in `Γ`**.  But what the atom is about is the inner object `diatm y' bd'`, whose witness `y'`
is an address of the **view** `Γ.diaIn x`.  So there is no candidate `t` until the view-level witness
is *evaluated at the identity arrow* and named here.  That — not any failure of comparison — is why
`◇`-typed content types were blocked.

**Evaluating a view witness at the identity arrow is `Term.realiseAtA`, and the cases are exhaustive.**
`Ctx.diaIn x` is `x.dia` together with `Γ.boxIn`, so a `◇`-typed address of the view is one of:

* `u.box`, or `u.keep.here` under T+4, with `u : □(◇A')` in `Γ` — T's collapse sends it to `u`, a `Γ`
  address.  `Term.collapse`'s `diatm` clause already does exactly this (`Collapse.lean:328`: the
  witness goes through `VarSymb.collapse`, the body recurses), and `eqRec_collapse` has its `◇` clause.
  **No datum needed.**
* a projection of one of those (`(u.box).fst` when `u : □(◇A' × B)`) — likewise, projections of a
  collapsed address are `Γ` addresses.
* `x.dia` itself, when `x : ◇(◇A')` — the only case needing anything, and what it needs is a `Γ`-level
  `◇`-term naming `x`'s content.  That is exactly **`here_name`**.

So with `here_name` every nested content is nameable, by induction on the nesting, and `here_beta`
delivers the atom already in the right shape: from the datum `Here (η x) t₀` and the hole term
abstracting `diatm y' bd'`,

```
Here (diatm x hx (diatm y' hy' bd'))  (Term.realiseAtA hT x hxA t₀ (diatm y' hy' bd'))
```

the content's witness being `t₀`'s in the `x.dia` case and the collapsed `u` in the box-image case.
The cross-fibre business of 10.3–10.10 arose only from the *second* question — what if the theory
supplies **two** such names — which `here_subst` (10.11) settles without any equality.

**What to build first, therefore.**  Hole terms of `◇` type never arose before (`here_beta` carried
`hB : B.diaFree = true`), so the untested position is `hereRead`'s *substitution* half: a `◇`-typed
slot used as a **witness**, which goes through `Subst.dia`/`SubE.diaBody` and is the one place
`Subst.Coh` does real work.  `here_subst`'s soundness leans on the same mechanism, so a single check
covers both — do it before anything else.

### 10.14 ✅Checked: realisation at a `◇`-typed content type already works *(2026-09-29)*

The position 10.13 singles out as untested — a `◇`-typed slot used as a **witness** — was checked
against the built tree, and it is already general.  Two kinds of evidence.

**From the signatures.**  Nothing in the realisation stack constrains the content type:
`Term/WFF.realiseAtA`, `Term.hereRead`, `Term.viewReadTm`, `Subst.ok_diaAbsA`/`coh_diaAbsA`,
`Subst.ok_single`/`coh_single`, and on the semantic side `Model.Env.substEnv_diaAbsA`,
`Model.interp_realiseAtA`, `Model.sat_realiseAtA` (`QML_v12m_SemAbs.lean`) — none takes
`A.diaFree = true`.  `Term.subst`'s `.diatm` case with a `.tm` entry is `SubE.diaBody`
(`Subst.lean:70`), whose positive branch (`if h : y = ιx`) is exactly what `Subst.Coh` justifies, and
⭐`Term.realiseAtA_eta` (`Abs.lean:639`) — the pinned round trip — is *proven* at an arbitrary `A`,
which at a `◇`-typed `A` means `Term.eta (.root (.bnd 0)) A` is itself a `diatm` with the slot as its
witness.  So the case is not merely permitted, it is already discharged.

**By a concrete instance** (scratch module, built against `QML.QML_v12m_Abs`, then deleted).  Under
`ModalSys := ⟨T := true, Four := false, TStrong := true, …⟩`, with `Γ` declaring `x : ◇◇Var`,
`y : ◇Var` and `u : □◇Var`, all of the following elaborate and hold **by `rfl`**:

| # | statement | outcome |
|---|---|---|
| 1 | `Term.realiseAtA rfl x hx t₀ tv` for `tv = diatm (x.dia) ⟨Var,hd⟩ cst` | elaborates |
| 2 | the resulting annotation is `Ann.dia y .var` | `rfl` |
| 3 | `realiseAtA … tv = diatm y ⟨Var,hy⟩ cst` — the witness became `t₀`'s | `rfl` |
| 4 | `realiseAtA … (η x.dia) = t₀` at a `◇`-typed content type | `Term.realiseAtA_eta` |
| 5 | `Term.hereRead rfl t₀' sbox = diatm (u.here) ⟨Var,huh⟩ cst` for `sbox = diatm (u.box) … cst` | `rfl` |

Rows 3 and 5 are the two branches of 10.13's case analysis, and they compute to exactly "the view
witness evaluated at the identity arrow": the content address goes to the realising term's witness,
and a box-image `u.box` goes to `u.here`, `u`'s value here under T (`VarSymb.collapse` at level 0,
`Collapse.lean:231`).

**Consequence for the build order.**  The feared first step is done; nothing in `Abs`/`SemAbs` needs
touching.  So start instead at the syntax edge:

1. drop `hA` from the `WFF.here` constructor and let `here_elim`/`here_intro`/`here_beta`
   (`hA`, `hB`)/`here_subst` follow; fix the fallout in `WFF.size`, `Countable`, `DecidableEq` and the
   soundness case list;
2. `here_name` and `here_subst` with soundness (`Model.sat_here_diatm` + `Model.sat_instantiate`);
   re-derive `here_fun`;
3. Canon layer: indiscernibility classes, `extentTm`, faithfulness's `◇` case;
4. the `here` alternative in `truth_lt`.

### 10.15 The two directions, and why `here_name` is existential *(2026-09-29, user's question)*

**`T_dia` does not ask for a witness; it introduces one.**  It is eigenvariable-shaped, like
`ex_elim`: given `t : Term σ Γ A a` it hands the subproof a fresh root `c : ◇A` with
`WFF.hereAt hT (.root (.free c)) … t` as a hypothesis, and the conclusion may not mention `c`.  At a
`◇`-valued `t` (`A = ◇A'`, `c : ◇◇A'`) nothing has to be named: any inner witness is already carried
by `t`, which is a term the user wrote.  So the two directions never meet —

* **up**: `T_dia`, from a value to a witness realised by it.  No reading of contents, hence no
  naming; the object comes from `Model.posRet_exists`, which is why generalising it is §10.12.
* **down**: `here_name` and realisation, from a witness to its content.  This is the direction that
  needs the view witness *evaluated at the identity arrow* (§10.13, checked in §10.14).

**The existential is usable, by `ex_elim` (`Proof.lean:92`), whose type argument is arbitrary.**
Eliminating `here_name`'s `∃z:X. Here (η x) z` gives a fresh declared root `z : X` together with
`Here (η x) (η z)` as a hypothesis, and from there `z` is an honest term: it can be fed to `T_dia`, to
`Term.realiseAtA`, to `here_beta`.  The eigenvariable restriction — `z` not in the conclusion — is the
honest reflection of the fact that `x`'s content has no name in `Γ`.  A term former for "the content
of `x` here" would be the `y.ret` design, rejected for having no uniqueness and no naturality
(`Model.posRet_exists`'s docstring).

**Why existential rather than eigenvariable is the right primitive.**  In the canonical model the
theory is a witnessed MCS, so `∃z:X. Here (η x) z ∈ T` plus `World.exW` gives the atom
`Here (η x) (η b₀)` **at a declared root** — literally the `RealDatum`, with no eigenvariable
bookkeeping and no chain step.  An eigenvariable-shaped `here_nameE` would be interderivable in the
proof system but useless to the model: its conclusion is an arbitrary `φ`, so there is no sentence to
put in `T`.  Same argument as the `T_dia` docstring's, for the atom over the positive-Φ schema
(`Proof.lean:150–162`).

**Corollary for §10.12.**  If `T_dia` is generalised to `◇`-typed `A`, the chain witnesses
`∃x:◇A. Here (η x) t` for enumerated **terms** `t`; a writable `◇`-term carries its own witness, so no
new naming problem arises there either.  N1/N2 again: a possible object is nameable only through an
address already in the context.

### 10.16 ✅Step 1 landed: `WFF.here` is general in its content type *(2026-09-29)*

`hA` is gone from the `WFF.here` constructor, and with it from `WFF.here_congr`/`here_congr'`,
`WFF.hereAt`, `Proof.here_elim`, `Proof.here_intro`, `Proof.here_beta` (both `hA` and `hB`), the
pinned `here_elimAt`/`here_introAt`/`here_elimAtA`/`here_introAtA`, `WFF.mono_hereAt`/
`mono_hereAt_of_le`, `WFF.hereAt_transport`, `WFF.subst_hereAt_renameTm`, `Proof.here_fst`/
`here_snd`, and the `Model.sat_hereAt`/`sat_here_diatm`/`sat_here_fun`/`sat_here_beta`/
`sat_here_elim`/`sat_here_intro`/`sat_hereAt_extend` family.

**`Proof.here_fun` keeps its `hA`, and must.**  Its `Proof.subst` case goes through
`WFF.subst_eqRec`, which carries `T.diaFree = true` (`Subst.lean:656`) — substitution moves
annotations, and `eqRec` compares at one annotation.  That is exactly §10.11's reason for making
functionality *substitutional*: `here_subst` arrives in step 2 and `here_fun` becomes a derived `def`,
keeping its `◇`-free form where `eqRec` is formable.  Also keeping `hA`, correctly: `T_dia` and
`Model.sat_here_ex`/`posRet_exists` (the `◇`-free model condition, §10.12), `Canon.exists_name`,
`rden_castAnn`, `rden_here_wd`, `WFF.instantiate_eqRec_slot`, `Proof.exists_eqRec_eta` (annotation
uniqueness, §10.5 N1/N4), and `WorldLang.retSet`'s parameter (renamed `_hA`, the chain being
`◇`-free while `T_dia` is).

**Neither friction predicted for step 1 materialised.**  `WFF.size` needed no redefinition —
`VarType.eqRecSize` was already total, `.VTypeDia A => A.eqRecSize + 3` — and `Countable` needed none
either, `WFF.code` already encoding the type and both annotations while ignoring the proof fields.
Both took only the pattern change (one `_` fewer).

**State of the build**: the whole `QML_v12m_*` list, **one error** —
`Completeness.lean:286`, `Alternative 'here' has not been provided`, the truth lemma's `here`
alternative — with **zero warnings and zero sorries**.  That is the same single error as before step 1,
so the generalisation is regression-free.  (A `declaration uses sorry` warning seen mid-sweep at
`CanonDom:714` was Lean's error-recovery cascade from a then-broken `rden_here_wd`, not a real
`sorry`.)

The constructor's docstring already said what is true again — "the constructor takes any `A`, but
functionality … is stated at `◇`-free `A` only" — so it needed no edit; the pointer to §10.11/§10.13
rides along with step 2, which touches the file anyway, rather than paying a second full-tree rebuild.

**Next**: step 2 — `here_name` and `here_subst` with their soundness cases
(`Model.sat_here_diatm` + `Model.sat_instantiate`), then `here_fun` re-derived.

### 10.17 ✅Step 2 landed: `here_name` and `here_subst` *(2026-09-29)*

Both rules are in, with soundness and substitution, and `here_fun` is no longer primitive.

**`Proof.here_subst`** — functionality, substitutionally: at any subject, any content type and **any
two annotations**,

```
Here s t → Here s t' → φ[slot := t] → φ[slot := t']
```

Soundness is ⭐`Model.sat_here_subst`: `Realised` reads the content at one arrow, so `interp t =
interp t'`, then `Model.sat_instantiate` twice.  Its `Proof.subst` case is `all_elim`'s, through
`WFF.subst_instantiate`.

**`Proof.here_fun` is now derived** (`ProofSubst`): `here_subst` at the hole formula
`eqRec A (η slot) t`, whose `t`-instance is `Proof.eqRec_refl` and whose `t'`-instance is the
equation, read back by `WFF.instantiate_eqRec_slot` and turned round by `Proof.eqRec_symm`.  It keeps
`hA`, and that is the shape of the statement rather than a restriction — `eqRec` compares at one
annotation, which `Ann.eq_of_diaFree` makes automatic at a `◇`-free type.  Existing users
(`Canon.rden_here_wd`) are unchanged.

**`Proof.here_name`** — a realised witness has a content:

```
Here (diatm x hx unit) unit → WFF.hereEx hT (diatm x hx bd)
```

with ⭐`WFF.hereEx hT s := ∃z:B. Here s z` (`DiaAbs`), the subject weakened past the slot.  Soundness
is ⭐`Model.sat_here_name`: a `Pos`-object's content function is total on its extent, so the content at
the reflexive arrow *is* the witness — the totality half of the pair whose surjectivity half is
`posRet_exists`/`T_dia` (§10.15).  No condition on the type.

*Why the body is arbitrary.*  At the pinned subject alone the conclusion would not survive
substitution (§10.11: the pinned form is not substitution-closed).  With `bd` arbitrary the image of
the conclusion is the rule's own conclusion at the substituted body, so the `Proof.subst` case is a
constructor application.  The pinned instance `bd := η x.dia` is what the canonical model consumes.

**Two transport lemmas were needed, and both are reusable.**

* ⭐`Term.subst_eta_renAt` (`SubstEta`): the η-expansion of an address whose **entry** is a renaming
  substitutes to the η-expansion of the renamed address — pointwise, as `Term.subst_eta_tm` is for a
  term entry.  Unlike `Term.subst_eta_ren` it needs no global `Subst.IsRen`, which is what makes it
  usable at a slot under `Subst.under`: the entry's shape propagates by itself, to projections by
  `Subst.at`, to `□` by `SubE.unbox`/`keepE`, to `◇` by `SubE.diaBody`, with the witness index from
  `Subst.Coh`.
* ⭐`Term.subst_under_mono` (`ProofSubst`): substituting under a slot, on a term weakened from below
  it, is the weakening of the substituted term — `Subst.under` agrees with `θ` weakened past the slot
  on everything `Γ` declares (`Subst.sim_of`, `Term.subst_congr`), and weakening then commutes with
  substitution (`Term.mono_subst`).

Together they give ⭐`WFF.subst_hereEx`, the conclusion's transport.  For the model side,
⭐`WFF.instantiate_here_slot` fills the slot back: a witnessed theory containing `WFF.hereEx hT s`
contains `Here s (η b₀)` at a declared root, which is what `Canon.RealDatum` is made of.

**State of the build**: the whole `QML_v12m_*` list, **one error** — `Completeness.lean:286`, the
truth lemma's `here` alternative — zero warnings, zero sorries.

**Primitive rule set now**: `T_dia`, `here_elim`, `here_intro`, `here_beta`, `here_name`,
`here_subst`.  Derived: `here_fun`, `here_elimAtA`/`here_introAtA`, and realisedness itself
(`here_beta` at `s := Term.unit`).

**Next**: step 3, the Canon layer — indiscernibility classes, `extentTm`, faithfulness's `◇` case —
then step 4, the `here` alternative in `truth_lt`.

### 10.18 ~~Open~~ Decided — keep: could `here_beta` be narrowed to its pinned instance? *(2026-09-29, user)*

The observation: elsewhere in this development β-reduction is *automatic* rather than a rule.  Why
not here, and how far could it be pushed?

**Why this β is not a computation.**  Hole-filling is a function (`Term.subst`), so `s[z↦b]` computes;
the semantic β laws (`Model.dia_beta`, `Model.box_beta`) are theorems; and the term syntax has no
projection former at all — projections are *addresses* — so there is no projection-β to state.
`Proof.here_beta` is different in kind: both sides are irreducible **atoms**, and the rule says the
predicate *commutes* with hole-filling.  Computing the content of `⟨x ; b⟩` at `id_w` would mean
reading the view back into `Γ`, i.e. `Term.realiseAtA`, which needs a **name** `t₀` for `x`'s content
(§10.13).  Without one there is nothing to substitute, so the content cannot be calculated from `b` —
only related to other atoms' contents, which is what β does.

**But given a name, β *is* composition.**  So the primitive could be the pinned instance alone,

```
Here (η x) t₀  ⊢  Here (diatm x bd) (realiseAtA x t₀ bd)
```

with the general form derived:

1. `here_name` gives a content name — `∃z. Here (η x) z` — and `ex_elim` a root `z` for it;
2. pinned-β gives the atom for **every** body, in particular for `bd` and for `viewReadTm bd s`;
3. `here_subst` interchanges `realiseAtA x z bd` with the given `t`;
4. and `realiseAtA x z (viewReadTm bd s) = hereRead z (…) = (hereRead t s)` after that interchange,
   by composition of substitutions — *automatic*, no rule.

The eigenvariable does not occur in the conclusion, so `ex_elim` applies.  `Canon.spec_of_here` is
already the model-side shadow of this: `RealDatum.spec` is *derived* from one atom rather than
assumed.

**One ordering detail.**  Today the `𝟙`-atom (realisedness) comes from an arbitrary atom *by* β at
`s := Term.unit`.  Under the narrowed design that is unavailable before a name exists, so
`here_name`'s premise must be weakened to an arbitrary atom about `x` — otherwise the two rules are
circular.  That is a small change and it makes the dependency honest.

**Verdict.**  Worth doing, but after the truth lemma closes.  The primitive count does not drop (six
either way); what drops is β's strength, and the price is eigenvariable bookkeeping plus another pass
over `Proof.subst`.  Better spent once the `here` case stands.

**Decision (2026-10-03, user and Claude): keep `here_beta` as it is.**  Re-examined once the truth
lemma closed.  No primitive is saved (six either way); the pinned form is not closed under
substitution (as for `here_name`, §10.11), so `Proof.subst` would have to re-derive the general
form inside its own case; the pinned rule would need `realiseAtA` and hence `[Γ.Presented]`, where
the rules otherwise need only `NoSlots`; and soundness and the canonical model already use the
general form, so nothing downstream gets simpler.  The insight — given a name, β is composition —
could be recorded as a derivability theorem without changing the system, but is not needed.

### 10.19 Step 3 begun: the relation and the class-keyed extent *(2026-09-29)*

**Landed** (`QML_v12m_CanonInterch.lean`, builds clean):

* ⭐`Canon.Interch w s s'` — two `◇`-terms at one stage and one content type are *interchangeable*
  when every formula with a slot of that type has the same status at both.  The annotations need not
  agree, which is the point.  `refl`/`symm`/`trans`.
* ⭐`Canon.interch_of_coname` — **co-naming implies it**: from `Here p s` and `Here p s'` in the
  theory, `Proof.here_subst` plus `World.mem_of_provable` gives interchangeability.  This is the only
  source of the relation, and it is the pairing principle in force (the two possibilities are joined
  by the address whose content they both are).
* ⭐`Canon.extentTm w s` — the extent of a `◇`-**term**: proper arrows are the children built for the
  witness of *any* class member, and the world itself is there when a member's witness is realised.
  With ⭐`extentTm_congr` (interchangeable terms have **the same set**), `extent_subset_extentTm` and
  `extentTm_cases`.

`extentTm_congr` is the property the `here` atoms demand: two names of one content must denote
objects whose first components agree as sets, which address-keyed extents never do.  And the reason
this does not disturb anything else — the point §10.9 missed — is that a term the theory says nothing
about has a **singleton class**, hence exactly the arrows `Canon.extent` gives it today, so no
object's body ever has to be read at another witness's child.

### 10.20 ⭐The remaining design question, answered: the class must be stage-invariant

Found while writing `extentTm`, and it must be settled before `rden` can use it.

`rden` is stage-indexed and `Canon.rden_mono` says the denotation does not depend on the stage a term
is read at.  So `extentTm` must be stage-invariant.  But `Interch` as defined quantifies over the
formulas of **one** stage, and a later stage has more of them, so:

* interchangeability at a **larger** stage implies it at a smaller one (lift each test formula by
  `WFF.mono` and `World.mem_lift`) — the relation is *contravariant* in the stage;
* therefore the class can **shrink** as the stage grows, and `extentTm` as it stands is not
  stage-invariant.

The fix is to take the relation at *all* stages from the term's own upwards:

```
InterchAll w s s'  :=  ∀ j, i ≤ j → Interch w (s lifted to j) (s' lifted to j)
```

which **is** stage-invariant: `InterchAll` at `j ≥ i` gives every instance at `k ≥ i` by the
contravariance above, so lifting a term does not change its class.  The members quantified in
`extentTm` then range over terms at any stage `≥ i`, and lifting `s` leaves the set alone.

So the order of work for the rest of step 3 is:

1. `InterchAll` (stage-invariant) with `refl`/`symm`/`trans`, the contravariance lemma
   (`Interch` at `j` implies `Interch` at `i`, needing `WFF.mono_instantiate` and `World.mem_lift`),
   and `interch_of_coname` lifted to it;
2. `extentTm` restated over `InterchAll` with members at any stage, plus `extentTm_mono` (the
   stage-invariance) — the lemma `rden_mono` will need;
3. the `rden` switch: the `.diatm` clause takes `extentTm` for its first component, and its content at
   an arrow is read from **the member that contributed it** (a choice function, `rden` being already
   noncomputable), with the self arrow as today through the datum;
4. the `rden` congruence/monotonicity family in `CanonDom`/`CanonFunc`/`CanonTerm` re-proved against
   the new clause — the bulk of the work;
5. faithfulness's `◇` case (`rden_eqRec`'s analogue for `InterchAll`), by the Leibniz trick: the hole
   formula `eqRec A' (η slot) (b' weakened)` has `b'`-instance reflexivity, hence `b`-instance in the
   theory, hence equal denotations at the smaller type;
6. then step 4, the `here` alternative in `truth_lt`.

Nothing above is blocked; item 3 is where the tree goes red for a while, so it wants a session of its
own.

### 10.21 Blocker check before the `rden` switch *(2026-09-29)*

Cheap checks on everything the rest of step 3 assumes, plus an honest read on what could still bite.

**Checked, and present in the needed form.**

| assumption | verdict |
|---|---|
| `WFF.mono_instantiate` — lifting a test formula (`RetMono:86`) | ✅ exactly the shape §10.20 needs |
| `World.mem_lift` — stage lifting of membership (`CanonWorld:328`) | ✅ an **iff**, so contravariance goes both ways |
| `Canon.Definable` = "is the denotation of a term" (`CanonDom:455`) | ✅ trivially preserved by any change to `rden` |
| `◇`-slot substitution computes (the `here_name`/`dia` idiom) | ✅ verified by `rfl` in §10.14, rows 3 and 5 |

So the contravariance lemma is ~10 lines: `mem_lift` down, `mono_instantiate` across, `Interch`-at-`j`
at the lifted test formula, back up.

**Missing, and now a definite to-do.**  There is no formula-level lemma for `WFF.instantiate` at a
`◇`-typed slot used as a **witness** — the identity that turns an `Interch` instance at
`φ = ◇_{.bnd 0} ψ` into `◇_y (WFF.viewReadTm bd ψ)`.  The term-level analogue computes (§10.14), and
the proof route is `WFF.subst`'s `.dia` clause with `Subst.single`'s slot entry and `SubE.diaBody`, so
this is work rather than doubt.  It lands in the truth lemma's `dia` case.

**The risk I would actually bet on: choice-dependence couples items 4 and 5.**  The content of a
class-keyed object at an arrow is read from *a* contributing member, and the member has to be obtained
by choice — `RDom (◇A)`'s second component is a function of the subtype `{a // a ∈ E}`, whose elements
are equal whatever their membership proofs, so the definition cannot read the member off the proof.
Hence `rden`'s value is choice-dependent, and the equalities `rden_mono`/`rden_congr` will need the
**well-definedness** lemma — any two members' bodies agree at a shared arrow — which is item 5's
faithfulness argument.  So the plan should be reordered: prove well-definedness *before* the
congruence family, not after.

**Scope of the congruence family**, for planning: about twenty lemmas touch `rden` at `.diatm` or
`extent` — `rden` itself, `rden_diatm_acc`/`acc'`/`self`, `rden_mono`, `rden_congr`,
`definable_dia_apply`, `rden_eqRec_far` (`CanonDom`); the `applyG_*` and `rden_eta_realised*` family
(`CanonFunc`); `canonEnv_extent`, `diaPush_agree_canon`, `interp_dia_self*` (`CanonTerm`).
`rden_mono` and `rden_congr` are the two big recursive ones.

**Confidence.**  Higher than at any earlier point in this work, and for reasons that are specific
rather than general:

* the two things that killed the earlier attempts are *gone* — the naming gap (closed by `here_name`,
  now proven sound and substitution-stable) and §10.9's "one arrow would have to carry several
  witnesses' contents", which dissolved once extents are keyed to term classes: a term the theory says
  nothing about has a singleton class and keeps exactly today's arrows;
* every rule the model needs now exists and is sound, so **no further logic-level additions are
  expected** — what remains is bookkeeping inside one layer, which is a different kind of risk;
* the design-level question that sank the earlier tries — can the theory force something the model
  cannot represent — is answered: the only forcing is through `here` atoms, and the class construction
  represents exactly those.

What could still go wrong is *size*, not soundness: the three risks above (choice-dependence, the
missing `instantiate`-at-a-`◇`-slot lemma, and the stage bookkeeping of `InterchAll`) are all "more
Lean than expected" rather than "the design is wrong".  If one of them forces a change it would be
local — most likely making `rden`'s `◇` clause take the contributing member as data rather than by
choice, which would mean carrying the class as a structure instead of a relation.

### 10.22 Step 3, continued: the missing lemma, the stage-free class, and no well-definedness lemma *(2026-10-01)*

**Landed** (builds clean, no warnings):

* ⭐`WFF.diaSlot ψ` and ⭐`WFF.instantiate_diaSlot` (`ProofSubst`) — the lemma §10.21 flagged as
  missing.  Instantiating the slot of `◇_{bnd 0} (ψ read in the slot's view)` with `diatm y bd` gives
  `◇_y (WFF.viewReadTm bd ψ)`.  Proof: `WFF.subst_dia` peels the `◇` node (its witness index reduces
  because the slot is the numeral `bnd 0`), then one `WFF.subst_comp` against `single (bnd 0) (tm bd)`
  with `WFF.subst_mono` on `viewReadTm`'s side; the `Subst.Sim` is `SubE.diaBody` at the slot and
  `Subst.dia_eq_box_mono` + `Subst.single_at_ne` on the box part.  Axioms: `propext`, `Quot.sound`.
* ⭐`Canon.Interch.dia_iff` — **interchangeable terms have the same `◇`-facts**, read at the test
  formula `WFF.diaSlot ψ`.  This is the end-to-end check that the lemma does the job: it is exactly
  the transfer the truth lemma's `dia` case needs at an arrow contributed by another class member.
* ⭐`Canon.Interch.of_lift` — contravariance in the stage (`World.mem_lift` + `WFF.mono_instantiate`).
* ⭐`Canon.DTerm` (a `◇`-term with its stage) and ⭐`DTerm.Rel` — **interchangeable at every stage
  both reach**.  An equivalence (`trans` compares at a stage all three reach and descends by
  `of_lift`); ⭐`rel_lift` — a term and its lift are one class; ⭐`rel_of_coname`.
* `Canon.extentTm` **restated over `DTerm`**, members at any stage, with `extentTm_congr`,
  ⭐`extentTm_lift` (the stage-invariance `rden_mono` needs), `extent_subset_extentTm`,
  `extentTm_cases`.  §10.20's items 1 and 2 are done.

**The design refinement: the content is chosen per class, so no well-definedness lemma is needed.**

§10.21 expected `rden`'s new clause to need a lemma that any two members' bodies agree at a shared
arrow.  Working it through, that lemma would *not* be provable: two co-named bodies over one witness
`z` agree at every arrow of `z`'s extent semantically, but the slot formulas `Interch` quantifies over
cannot say "at the same arrow" across two separately substituted formulas — that needs
`□_z (b = b')`, i.e. functionality at a `◇`-typed content, which `here_subst` does not give.  So the
design must not need it, and it doesn't:

1. **Choose by class, not by term.**  The member whose body supplies the content at an arrow is
   chosen as a function of the term's *class* and the arrow alone.  Related terms have equal classes,
   so they get **literally the same** content function — equality of the two elements, which is all a
   pair of `Here` atoms forces, is then automatic.
2. **Prefer the pinned member.**  At a child of `z`, if `η z` is in the class, choose it.  The only
   objects whose contents at proper children are *observed* are address objects (`rden (η y)`, via
   `◇_y`/`□_y`), and for those this makes the content `y`'s own — which is what the theory's `◇_y`
   facts are about.  A term's object is otherwise observed only at the self arrow (`Here`) or through
   element equality, and (1) covers both.
3. **The `dia` case uses the chosen member and `Interch.dia_iff`** — no agreement between members
   needed: an arrow contributed by `diatm z b` satisfies the pushed formula iff the child's theory
   contains `viewReadTm b ψ`, iff `◇_z (viewReadTm b ψ) ∈ T`, iff `◇_y χ ∈ T`.

So the order of work is now: the class as a **set** (`cls s`, with `Rel → cls` equal) and the
per-class selector with its spec; then the `rden` switch; then the congruence family, where
`rden_mono`/`rden_congr` follow from `extentTm_lift` and class equality rather than from a
well-definedness argument; then the truth lemma.

### 10.23 ⚠️`dia_beta` refutes the class-keyed extent; `Here` at `◇`-content must mean *indistinguishable* *(2026-10-01)*

**The finding.**  `Model.dia_beta` (`InterpLemmas`) holds in every model:
`posEval ⟦diatm x t⟧ = ⟨ext ⟦x⟧, w' ↦ ⟦t⟧_{x̌ ↦ cont_x w'}⟩` — the body never touches the extent.
The canonical model must satisfy it (`interp_canon`), so **canonical extents are keyed to the
witness**, and `extentTm` (§10.10, §10.19–10.22), which gives `diatm x t` the extent of its
interchangeability class, is not a model.  §10.10 should have been checked against `dia_beta`.

**Why witness-keyed extents bring back §10.9.**  Under the present clause `Here` is *equality of
elements* (`Model.Realised`: `cont_p(id_w) = ⟦t⟧`).  So `Here(p, ⟨x;b⟩)` and `Here(p, ⟨z;c⟩)` give
`⟦⟨x;b⟩⟧ = ⟦⟨z;c⟩⟧`, hence equal `posEval`, hence (by `dia_beta`) `ext(x) = ext(z)`.  Pinned co-naming
is harmless (the witnesses' contents then agree, and `Interch.dia_iff` transfers facts), but
non-pinned co-naming makes `x` and `z` co-extensive with contents linked only through `b`, `c`: a
child built for `z` must still give `x` a content satisfying its `□_x`-facts, which that child's
language (`diaIn z`) cannot name.  `Here`-as-equality at `◇`-content is a **join** of the two
witnesses' possibilities — a joint possibility that did not come from pairing.

**The decision (user, 2026-10-01): `Here` at `◇`-typed content makes objects *indistinguishable*,
not identical.**  The syntax cannot identify possible objects over distinct witnesses, even when a
model happens to make them extensionally equal — `eqRec` compares only terms of one annotation, i.e.
over one witness (`WFF.lean`) — and the only thing it does with two names of one content is
substitute one for the other (`here_subst`).  So `Here(p, t)` should read: `id_w ∈ ext p` and
`cont_p(id_w) ≈ ⟦t⟧`, where `≈` is equality at `◇`-free types.  This is the semantic twin of
`Canon.Interch`.

**What `≈` should be.**

* *A structural bisimulation* would have to match arrows of `x`'s extent with arrows of `z`'s whose
  targets are equivalent — an isomorphism with *identical* targets is not enough, because canonically
  `x`- and `z`-children are different worlds (different base languages).  That is a back-and-forth
  over (world, object, environment), domains included: heavy.  It is at least *available*: canonical
  extents are **all** depth-`+1` worlds with `DiaView x`/`BoxxContents x` (`Canon.extent`), not one
  child per formula, so a `z`-child realising the full type of `b(x̌)` at an `x`-child as the type of
  `c(ž)` exists by Lindenbaum on a set-valued `diaStart` (finite pieces from `Interch.dia_iff`, and
  every formula of an `x`-child is `◇_x`-possible by `BoxxContents`).
* *Model data, Henkin-style* (preferred): the model supplies `Ind` at `◇`-types, reflexive, with
  the condition that `Ind`-related objects satisfy the same slot formulas.  `here_subst` is then
  sound outright (reflexivity covers `T_dia`/`here_name`).  Canonically `Ind := DTerm.Rel`, and the
  truth lemma's `here` case is two lines: `Here(p,s) ∈ T` and `Here(p,s₀) ∈ T` give `Rel s₀ s`
  (`rel_of_coname`); conversely `Rel s₀ s` applied to the slot formula `Here(p, ·)` gives
  `Here(p,s) ∈ T`.  The invariance condition is checked after the truth lemma, through it.  No
  cross-witness children, no bisimulation.

**⚠️The second obstacle: extensional `◇`-carriers.**  `Model.pos_inj` makes a possible object
*determined* by its extent and content.  Two witnesses with empty extents then denote **the same
object**, and no clause for `Here` — equality or `Ind` — can tell them apart:
`□_x⊥ ∧ □_z⊥ ∧ Here(q, η x) → Here(q, η z)` is valid, and (as far as I can see) not derivable,
since no rule produces a `Here` atom about `z` from these premises.  So the truth lemma fails for
the consistent theory `{□_x⊥, □_z⊥, Here(q, η x), ¬Here(q, η z)}`.  This was already latent in the
equality reading.  The principle above has to reach the carriers too:

* **Frame-level possibilities.**  Give the frame a set `Poss w` of possibilities, each with an
  extent, and make `Pos A w ≅ Σ π : Poss w, (ext π → Dom A)` — extensional *within* a possibility,
  so `eqRec`/`pos_inj`-style arguments over one witness survive, while distinct possibilities with
  equal extents stay distinct.  `dia_beta` becomes "the possibility of `⟦⟨x;t⟩⟧` is `x`'s";
  canonically the possibility is the witness address and `Canon.extent` stays as it is.
* **Residual vacuous case.**  Over *one* possibility with empty extent, `⟨x;b⟩` and `⟨x;b'⟩` with `b`,
  `b'` over different inner witnesses still coincide (empty content functions), but `eqRec` cannot
  compare them (two annotations).  Either carriers are intensional within a fibre too (then the
  `pos_inj` uses in `SemLemmas`/`SemShift`/`SemSubst`/`SemCollapse`/`SemHere` — `interp_eta`,
  `interp_mono`, the substitution lemmas — must come from strong-functor laws on `posMap`/
  `posStrength` instead), or the logic gets the principle that makes the vacuous case derivable (a
  heterogeneous `eqRec` that is `⊥` at mismatched inner witnesses, and `□_x(…)` over one outer
  witness — sound under possibility carriers).  Undecided.

**What survives.**  `instantiate_diaSlot`, `Interch` (`dia_iff`, `of_lift`), `DTerm.Rel` and
`rel_of_coname` are exactly what the `Ind` reading needs canonically.  `extentTm` and its four
lemmas are now dead and should be removed with the `rden` work; nothing uses them yet.

**Next.**  Settle the carrier question (possibilities, and the vacuous case), then: `Model` gets
`Ind` and possibilities; `Realised` uses `Ind` at `◇`-content; soundness of the `here_*` rules and
the lemmas that used `pos_inj`; the B-track canonical model (`BCanonModel`) and the T-track one
re-proved against the new `Model`; then the truth lemma's `here` case as above.

### 10.24 Weakening `pos_inj` to "one possibility": the laws, the canonical model, and a missing rule *(2026-10-01)*

**The proposal (user).**  Injectivity only where the witness is the same, with no witnesses in the
semantics.  Read the witness off the object itself: its **underlying possibility** `posMap unit p :
Pos 𝟙 w`.  Weakened `pos_inj`: `p ↦ (posMap unit p, posEval p)` is injective.  At `𝟙` this is
vacuous, so pure possibilities have no identity criterion beyond themselves.  A finer variant uses
the **skeleton** `posMap skel p : Pos (skel A) w` (`skel` keeps `◇`, `□`, `×`, sends `Var` to `𝟙`) —
the semantic counterpart of an annotation, so identity is exactly what `eqRec` can compare.

**Laws, from the use sites.**  Every `pos_inj` use (`interp_mono`, `interp_collapse`, `interp_shift`,
`interp_subst`, `interp_eta`, `SemHere`, `sat_eqRec`) compares two `diatm` denotations whose witness
objects are equal, or (`interp_subst`, `.tm` entry) a witness `⟦y⟧` with `⟦⟨y;d⟩⟧`.

* *Possibility variant*: two laws suffice — `posMap unit (posMap f p) = posMap unit p` and
  `posMap unit (posStrength n p) = posMap unit p`.  Then the possibility of `⟦⟨x;t⟩⟧` is that of
  `⟦x⟧`, and the existing proofs go through with the extra conjunct.  Canonically trivial: a carrier
  is ⟨possibility, content⟩ (possibility = the witness address, or an anonymous extent), `posMap`
  and `posStrength` act on the content only, and fibrewise injectivity is `Sigma.ext`.
* *Skeleton variant*: at skeleton types there is no injectivity at all, so e.g. `interp_eta` at
  `◇◇𝟙` must be proven equationally — functor laws, "`posMap` depends only on the function", strength
  naturality and unit.  Canonically the carriers must remember the content's annotation even when the
  extent is empty (a tag), and the "depends only on the function" law is where that can fail.
  Heavier, unchecked.

**⚠️The check exposed a missing rule, independent of the variant.**  Any injectivity — even within one
possibility — makes `Here(q, ⟨x;b⟩) ∧ □_x(b = b') → Here(q, ⟨x;b'⟩)` valid.  The rules do not derive
it: a `Here` atom's content moves only by `here_subst`, which needs a second atom, and `eqRec` has
`refl`/`symm`/`trans` but no Leibniz beyond base type (`eq_elim`); the Leibniz notes record that under
T the general principle is not derived and "completeness gives it back" — now circular.  Canonically
it is `Ind`'s reflexivity: the truth lemma needs *equal denotation ⇒ interchangeable*, and the only
argument for that runs through the truth lemma at the same `Here` formula.

The gap is not specific to `◇`-content.  `WFF.size` gives `here` at content `A` size
`A.eqRecSize + 1`, i.e. the truth lemma was meant to decide `Here(s,t)` by recursing on
`eqRec t₀ t` — which needs `eqRec t₀ t, Here s t₀ ⊢ Here s t`.  At `Var` that is `eq_elim`; at `□B`,
products or `◇B` no derivation exists.

**Two coherent ways out.**

* **(A) A content-congruence rule** `here_eq`: `Here s t, eqRec t t' ⊢ Here s t'` at any content type.
  It is Leibniz for `Here`'s content — the `here` component the T-Leibniz bookkeeping lacks (so it may
  make Leibniz under T derivable; to check).  With it, fibrewise injectivity is sound and complete,
  and the `here` case runs as the measure intends: `rden u = rden s₀ ⇒ eqRec ∈ T` (smaller) `⇒` the
  atom transfers.  With the possibility variant, the vacuous case (one witness, empty extent, bodies
  over different inner witnesses) is still identified and `eqRec` cannot compare it — that needs a
  heterogeneous `eqRec` (`⊥` at mismatched inner witnesses, sound under fibrewise injectivity, and
  `□_x⊥` proves it vacuously).  With the skeleton variant it is not identified and `eqRec` is enough.
* **(B) Fully intensional carriers**: no injectivity, no new rule.  Canonical carriers carry their
  `Rel`-class, so `Ind` is reflexive by construction and the `here` case is §10.23's two lines.  The
  cost moves to soundness: every `pos_inj` use becomes an equational argument from strong-functor laws,
  and "depends only on the function" cannot be stated extensionally (that reintroduces the
  identification), so it must be a syntactic equational theory on `GFunc` that the canonical model
  meets on classes.  `eqRec` at `◇` then means extensional equality, and Leibniz into `Here` contents
  fails semantically — consistent with having no `here_eq`.

### 10.25 Checking `here_eq` *(2026-10-01)*

`here_eq : Here s t, eqRec t t' ⊢ Here s t'`, any content type.  The user's diagnosis of why it was
missing: without `Here`, a possible object is used only inside a `◇` with its own witness, which is
what lets equality recurse down to base type; `Here` relates a possible object directly to an object
one level down, a cross-level relation of the kind K never has, so Leibniz in its K form cannot see
it.  Strong T's rules mix the levels, and an equality rule for the mixing is the price.

**Soundness.**  Immediate from the `⇒` half of `sat_eqRec` (`eqRec` true ⇒ equal denotations), since
`Realised`/`Ind` then receives the same object.  At `◇` that half needs the weakened injectivity:
same skeleton (resp. possibility) and same section.  For the skeleton variant this needs the lemma
*same annotation ⇒ same skeleton of the denotation*, by induction on the term from `posMap`
composition, strength naturality and "`posMap` respects pointwise-equal maps".

**Closure under substitution.**  The `Proof.subst` case needs `WFF.subst_eqRec` at `◇` types; today it
is `◇`-free only (`Subst.lean:654`).  The `◇` clause is `subst (□_x eqRec t s) = □_{ιx} (…)` with the
body under `θ.dia x (ιx)` — the witness-index bookkeeping `WFF.subst_dia` already does (as in
`instantiate_diaSlot`).  Work, not doubt.  (With a heterogeneous `eqRec` it can only be an
implication, `subst (eqHet t t') ⊢ eqHet tθ t'θ`, because substitution can merge two witnesses and
turn a `⊥` clause into a `□_z(…)`; that is the harmless direction.)

**Leibniz under T becomes derivable, as far as checked.**  The new case is a `Here` atom with the
equated term inside it.
* In the content: `here_eq` plus term congruence.
* In the subject (`Here(⟨x;b₁⟩,u)`, `□_x(b₁ = b₂)` ⊢ `Here(⟨x;b₂⟩,u)`): derived.  `here_beta` turns
  the atom into realisedness of `x`; `here_name` + `ex_elim` names `x`'s content `c`; `here_beta` gives
  `Here(⟨x;b_i⟩, b_i[c])`; `here_elim` at the pinned subject turns `□_x(b₁ = b₂)` into
  `eqRec b₁[c] b₂[c]`; `here_eq` gives `Here(⟨x;b₂⟩, b₁[c])`; `here_subst` against
  `Here(⟨x;b₁⟩, u)` moves the content to `u`.
* Still to look at: the necessary-entry `here` component the `LeibnizSpine` note mentions.

**The canonical `here` case**, as the size measure intends.  Canonical `Ind(o,o')` := `o = o'`, or
`o = rden u`, `o' = rden u'` with `Rel u u'`.  `Here(p,s) ∈ T` ⇒ `Rel s₀ s` (`rel_of_coname`) ⇒ `Ind`.
Conversely, `rden u = rden s₀` ⇒ `eqRec s₀ u ∈ T` (truth lemma at `eqRec`, size `A.eqRecSize` <
`A.eqRecSize + 1`) ⇒ `Here(p,u)` by `here_eq`; then `Rel u u'` at `Here(p,·)` gives `Here(p,u')`, and
`rden u' = rden s` gives `Here(p,s)` by `here_eq` again.  This needs *equal denotation ⇒ same
annotation* canonically — true by construction with skeleton tags.  With bare possibilities it holds
because distinct view addresses are distinct possibilities at every proper child, and a realised
witness always has proper children (`exists_dia` builds one for `◇_x ⊤`); the empty extent is the
vacuous case, where `□_x⊥` proves the heterogeneous equation.

**Costs found, common to both variants.**
1. `Ind`'s invariance is a model condition over *all* environments, so the canonical model must
   verify it beyond `canonEnv`.  Canonical domains are definable (`toDom … Definable`), so the route
   is: every definable environment is `substEnv θ canonEnv` for a term substitution `θ`, then
   `sat_subst` + truth lemma + `Rel`.  That lemma is new.
2. `subst_eqRec` at `◇` (above).

**Specific to the skeleton variant.**  At skeleton types there is no injectivity, so `interp_eta` and
the substitution lemmas need "`posMap` respects pointwise-equal maps" (or a syntactic equational
theory on `GFunc` plus `compile` lemmas).  Canonically carriers carry an annotation tag even on an
empty extent, and the law asks that two maps agreeing on every *definable* object transport tags
alike.  An empty-extent tag is seen by no evaluation, so this needs an argument, e.g. that tag
transport is label-parametric and every tag shape is realised.  **This is the open risk.**  The
possibility variant has no such law (two preservation laws only), at the price of the heterogeneous
`eqRec`.

**Decision (user, 2026-10-01): no heterogeneous `eqRec`; the skeleton variant.**  Comparing two
possible objects over different witnesses means comparing bodies that live in different contexts
(`diaIn y`, `diaIn y'`), and without a map between the contexts that comparison is *ill-defined*,
not false.  So the syntax has equality only within one annotation, which is `eqRec` as it stands.
The semantics must match: identity only within one skeleton, the semantic counterpart of an
annotation.  The possibility variant is out, because it identifies empty-extent objects across
inner annotations, which only `eqHet` could express.  Plan: weakened `pos_inj` over the skeleton,
`here_eq` with plain `eqRec`, `Ind` for `Here` at `◇`-content.  Next: settle the skeleton variant's
open risk (canonical tag transport against the pointwise law).

### 10.26 The skeleton variant's risk, checked: the extensional law fails, the equational one costs the interp layer *(2026-10-01)*

**Canonical carriers.**  A canonical possible object becomes `⟨x, α, c⟩`: witness address `x`, the
body's annotation `α` (labels are addresses of the view `diaIn x`), and the contents
`c : extent w x → RDom`.  The canonical operations act on tags by structural recursion on `GFunc`:
`posMap f ⟨x,α,c⟩ = ⟨x, f_*α, eval f ∘ c⟩`.  Here `f_*` relabels: identity for `fst`/`snd`/`pair`/
`diaMap`, `.var` for `func`, the T-collapse (`u.box ↦ u.here`) for `extract`, the 4-shift for `dup`.
`posStrength` pairs in the necessary argument's tag.  Under T that tag is recoverable from the value
at the reflexive successor, because the collapse is injective on box-view addresses, so `nec_inj` can
stay.  Skeleton-injectivity holds canonically: `skel_*` keeps every `◇` label, so it is injective on
tags, and the skeleton carries `x`.

**The extensional law ("`posMap f = posMap g` when `f`, `g` agree pointwise") cannot be established.**
When `x`'s extent is nonempty, `α` is literally the tag of `c v` at each child (`DiaView` makes the
child's base the view, address for address), so pointwise agreement there forces `f_*α = g_*α`.  When
the extent is empty, `α` is seen by no evaluation anywhere: its labels (`x.dia…`) are declared at no
world.  Pointwise agreement then says nothing about it.  Closing the gap would need a realisability
argument — tag transport is label-parametric, and every tag *shape* is realised with distinct labels
by some definable object somewhere — which depends on which witnesses each system's languages
supply.  Not robust; I would not build on it.

**The equational law works canonically, by inspection.**  State it as: `posMap` respects a syntactic
equational theory `E` on `GFunc` — category laws, product β/η, terminal η, functoriality of
`boxMap`/`diaMap`, strength naturality and unit, naturality of `extract`/`dup`.  Each equation
transports tags alike by inspection, and `eval` respects `E` by induction on depth.

**But soundness then pays.**  At skeleton types there is no injectivity, so every `diatm` case of the
interp layer needs an *equation*, not an evaluation:
* the skeleton of `⟦t⟧` is determined by `t`'s annotation — `skel ⟦t⟧ = ⟦annTerm (ann t)⟧`, where
  `annTerm` is the canonical skeleton-typed term with that annotation;
* `interp_mono`/`collapse`/`shift`/`subst`/`eta` restricted to skeleton-typed terms, proven as
  "`compile` commutes with the operation, modulo `E`" plus strength associativity/naturality for
  bundle alignment.

The skeleton fragment has no function symbols, base variables or `Here`, but it has pairs, `boxtm`,
`diatm` and variables, so this is most of the `compile` layer redone equationally.  True beyond
reasonable doubt; large.

**An idea considered and set aside: intension as content off the extent.**  Give a possible object
contents at *every* accessible arrow, with the extent marking where it really is, and keep full
`pos_inj` on these total sections.  Then nothing is forced across witnesses or inner annotations — the
off-extent "junk" can always differ — and no new laws are needed.  But `eqRec` at `◇` (`□_x`, on the
extent only) stops being identity, so `here_eq` fails at `◇`-content.  And the canonical junk at an
arrow outside `x`'s extent must be a *definable* object of a world whose language has no `x.dia`,
which reintroduces tags in a worse place.

### 10.27 ⭐The alternative: the skeleton as data, not as a possible object *(2026-10-02)*

**Why §10.26 needed equations.**  There the skeleton of `p` was `posMap skel p`, itself an element of an
intensional carrier `Pos (skel A) w`.  Comparing two skeletons was therefore comparing possible objects
with no injectivity to fall back on, and the only remaining tool was a `GFunc` equational theory.

**The alternative: make the skeleton plain data — a *semantic annotation*.**  Under T the model also
supplies:

* a set `Root w` of root possibilities, and `base : Pos A w → Root w`;
* `shape : Pos A w → SemAnn A w`.  This is a tree over `A`'s `◇` positions, like `Ann A`, whose labels
  are **semantic sources**: either *(root, path)* — the possibility at that path inside a root's
  content — or the possibility-part of a necessary object (`necMap (diaMap unit ∘ proj) n`, a
  `Nec (◇𝟙)`-object, compared by `nec_inj`).

The laws are **equalities of data**: `base (posMap f p) = base p`, `base (posStrength n p) = base p`,
`shape (posMap f p) = f_* (shape p)`, and `shape (posStrength n p) = (leaves of n, shape p)`.  Here
`f_*` is the fixed label-tree transport defined by recursion on `GFunc` — the same one the canonical
tags use.  Weakened injectivity: `p ↦ (base p, shape p, posEval p)` is injective.

This is the user's "map into `PosSec` via the witness" made precise.  `posEval` factors through what
the witness *determines semantically* — its root and the sources at each `◇` position — with no
variables in the semantics.

**Soundness without an equational layer.**  One lemma by induction on terms:
`shape ⟦t⟧_env = ⟦ann t⟧_env`, where each annotation label `r.steps` is interpreted through `env`.
Labels through a `◇`-root are looked up in `shape (env r)`; labels through a `□`-root become the
possibility-part of `env r`.  Then each `diatm` case of the interp layer gets its shape equality from
the **annotation identities the syntax already has** (`Term.mono` keeps the annotation; `subst`,
`collapse` and `shift` have annotation functions in their types).  Leaves are compared by existing
extensionality: `nec_inj`, and possibility equality (= base equality, by injectivity at `𝟙`).  In
`interp_subst` a `□`-label `u.box` with `u ↦ boxtm ⟨v.box; d⟩` becomes `v.box`.  The two leaves are
the possibility-parts of `⟦boxtm ⟨v.box;d⟩⟧` and of `env v`, equal at every successor because
`posMap` preserves the base.  This is why leaves are possibilities, not possible objects.

**Canonical.**  `Root w` = witness addresses, `base ⟨x,α,c⟩ = x`, and `shape` = the tag `α` with labels
interpreted.  The laws hold by construction, since canonical `posMap` transports tags by the same
`f_*`.  Injectivity: `(x, π)` labels determine `x.dia.π`, and a `□`-label's possibility-part
determines `u` because there is always a successor (T gives the reflexive one), where distinct `u`
give distinct addresses.

**Gating.**  Shapes and the weakened injectivity are needed only where `Here` exists, i.e. under T.
Without T the model keeps full `pos_inj`.  The B track (weak B without T) is untouched.

**Risks to check before building.**  (1) Labels under 4 (`keep`/`dup` steps): `f_*` for `dup` and the
interpretation of keep-labels must agree with `VarSymb.inner`/`keepOnly`.  (2) `SemAnn` is a
dependent tree over the type, with leaves at different "levels" (paths through boxes).  Defining it so
that `Ann`-level operations map over cleanly needs care, but it is data design, not proof risk.
(3) The interp layer's `diatm` cases must thread the shape equality alongside the section equality;
that adds a conjunct, not a new argument.

### 10.28 Risk 1 checked: 4 (`keep`/`dup`) fits, and the leaves take their final form *(2026-10-02)*

**Two structural facts from the syntax do most of the work.**

1. *Collapse and shift only ever rewrite a label's context prefix.*  A label of a `◇`-node at nesting
   depth `j` inside a term is an address of a view `j` levels in.  So it is a context address
   followed by a suffix with exactly `j` level steps.  `Ann.collapse k`/`Ann.shift k` act at `k + j`
   (`Ann.collapse`'s `.dia`/`.box` clauses), i.e. on the level step with `k + j` level steps after it,
   which lies in the prefix.  The suffix is never touched.
2. *Every object has one address per flag combination.*  Under T+4 views show only `u.keep`
   (`keepOnly`), so `u.box` and `u.keep.here` never both occur.  Without T there is no `here`, and
   without 4 no `keep`.  So labels need no quotienting.

**Interpreting a label.**  Evaluate the context prefix through the environment (the existing
`Env.ref`/`CollapseAgree`/`ShiftAgree` machinery), giving a world-`w` object `o`, then follow the
suffix structurally.  This yields **two kinds of leaf**, as one inductive family over worlds:

```
Leaf w ::= root (r : Root w) (p : List Step)        -- a root possibility, and a syntactic path in its content
         | fam  (f : (s : Acc w) → Leaf s.1)         -- one leaf per arrow out of w
```

* A suffix step `dia` on a possible object `o`: look up `shape o` along the rest of the path.  Inside a
  possible object's content the leaf stays *syntactic*: `root (base …, path)`.  This is what survives
  an empty extent.
* A suffix step `box` on a necessary object `n`: `fam (s ↦ leaf of necEval n s along the rest)`, over
  *all* arrows out of `w`.  Under T the reflexive arrow keeps it informative.
* `keep`: `fam` of the kept object, i.e. by `necDup_eval` the family reindexed by composite arrows.
  `here`: evaluate at the reflexive arrow (`necExtract_eval`).

**Transport `f_*` for the `T`/`4` maps mirrors `Ann.idxAt`.**  For `dup`: `root` leaves get their path
shifted (`VarSymb.shift`, inserting `keep`), `fam` leaves are reindexed by `trans`.  For `extract`:
`root` paths are collapsed (`VarSymb.collapse`: `box ↦ here`, `keep` disappears), `fam` leaves are
evaluated at `refl`.  These are exactly `Ann.idxAt`'s `here`/`keep` clauses, which already describe
how an address's witness is found through a necessary object.  The semantic and syntactic sides
agree by the existing laws: `necDup_eval`, `necExtract_eval`, and for "a kept object read where it
was kept is the object" the frame's T+4 unit law for `trans` with `refl`.

**What is checked by this, and what remains.**
* `interp_collapse`/`interp_shift`, shape part: immediate by fact 1.  The prefix values agree by the
  existing agreement lemmas; the suffixes are identical.
* The `diatm` case of the shape lemma needs "`compile` of an address transports shapes the way
  `Ann.idxAt` looks them up".  It is a lemma per address form (projections, `here`, `keep`), with the
  same case split the syntax already does in `SubE.proj_here_eq`/`ref_here_of`.  Work, not risk.
* Canonical injectivity: `root` leaves carry the witness address; `fam` leaves at the reflexive arrow
  carry `u.here`'s address, so distinct `u` give distinct leaves.  Holds under T, which is where shapes
  are required.

### 10.29 Step 1 landed on branch `sem-annotations`: shapes in `Model` *(2026-10-02)*

Checkpoint before the change: tag `checkpoint-before-semann` (commit `c51d3bd` on `self-part-union`).

**In `Model.lean`.**
* `Shp L A` — an annotation tree over `A` with labels in `L`, the same structure as `Ann`; accessors
  `fst`/`snd`/`inner`/`label`/`body`, and `map`.
* ⭐`Frame.Leaf F RootPoss w`: `root (r : RootPoss w) (p : VarSymb)` | `fam (f : (s : Acc w) → Leaf s.1)`.
  `Frame.Leaf.collapse hT i` / `shift hF i` act on the level `i` steps from the anchor: a family is
  read at `refl`, or reindexed by `trans`; a root path goes through `VarSymb.collapse`/`shift`.
* ⭐`GFunc.shp f j` — how a definable map moves a shape.  It rearranges positions as the map
  rearranges components, keeps labels, and lets `extract`/`dup` collapse/shift the level `j` they act
  at (§10.28).
* `Frame.transposeShp` (a family of shapes as one shape with family leaves) and `Frame.domShape`
  (the shape of any object, from the shapes of possible objects).
* `Model` fields: `RootPoss` and `shape : T = true → Pos A w → Shp (Leaf RootPoss w) (◇A)`.
  `pos_inj` is now *same section and, under T, same shape ⇒ equal*.  The laws are `shape_posMap`
  (label kept, body by `f.shp 1`) and `shape_posStrength` (body paired with the transposed shapes
  of the necessary object's values).
* (The field is `RootPoss`, not `Root`: inside `namespace Model` the latter shadows the syntax's
  `Root`.)

**Instances.**  `BCanonModel` (no T): the shape fields are vacuous via `noT`.  `CanonModel` (T track):
~~TEMPORARY `sorry`~~ (✅ removed in §10.37) in `shape`, `shape_posMap`, `shape_posStrength`.  These
needed step 5's tagged carriers; the current carriers are fully extensional, so `pos_inj` holds outright.  To be removed in
step 5.  `CanonTerm`/`BCanonTerm` now prove equality of canonical possible objects with the
canonical `posEval_injective` directly, not `Model.pos_inj`.

**Build.**  `Model`, `Env`, `Interp`, `InterpLemmas` build.  `SemLemmas` fails at its two `pos_inj`
uses (unsolved shape goal), so everything downstream waits for step 2: the shape lemma and the
shape conjunct in `interp_mono`/`interp_eta`/`sat_eqRec`, then `SemCollapse`/`SemShift`/`SemSubst`/
`SemHere`.

### 10.30 Step 2: the shape layer, and a T+4 normal-form problem at η *(2026-10-02)*

**Landed (builds, no warnings), new file `QML_v12m_SemShape.lean` plus additions to `SemCollapse`,
`SemShift`, `SemSubst`, `SemLemmas`.**  Shapes are computed symbolically:
* `ShEnv` (a shape per visible address, anchored at the current world), `ShEnv.ref`/`boxPush`/
  `diaPush`, `termShp ρ j t`.
* ⭐S1 `termShp_compile` (counterpart of `compile_eval`); ⭐`shp_transpose` (every map's transport
  commutes with transposition); ⭐T `termShp_transpose`; ⭐S2 `domSh_interp`: **the shape of a value is
  its symbolic shape** — the `◇` case does not even recurse.
* ⭐`termShp_mono`, ⭐`termShp_ann` (*the annotation determines the shape* — the semantic side of `eqRec`),
  `termShp_collapse`, `termShp_shift`, ⭐`termShp_subst` (with `entryShp`, `substShEnv`, and the shape
  counterparts of `collapseAgree_self`/`shiftAgree_twoBox`).
* Root paths are now `List Step` with front-indexed `Step.collapseAt`/`shiftAt` (not `VarSymb` with
  `levels - 1 - i`): the simplicial identities between them are clean list inductions
  (`Step.collapseAt_collapseAt`, …, `Frame.Leaf.collapse_collapse`, …, `shift_shift_self`).
* `interp_mono`, `sat_eqRec`, `interp_collapse`, `interp_shift`, `interp_subst` have their shape
  conjuncts.  Build: everything through `SemSubst` green.

**⚠️The problem (at `interp_eta`, `SemHere`).**  Under T+4 the contents of `u : □A` in a view are
`u.keep.here` (`keepOnly`).  Compiled, that is `dup` then `extract`, so on shapes `collapse (j+1) ∘
shift j`.  On families this is the identity (`trans_refl`).  On a **root** leaf it is the identity
only when the path's step at that level is `keep`: for `[…, box, …]` it gives `[…, keep, here, …]`.
That is the same possibility under T+4 but a different path.  A model may give a possible object of type
`◇(□◇C)` a shape whose inner leaf has the path `[dia, box]`.  Then `⟦⟨x; η x.dia⟩⟧` has a different
shape from `⟦x⟧`, so **the η-law is false in such a model**: a genuine gap in the model class, not
a proof gap.

**Options.**
1. *Normalise in the operation* (recommended): `Step.collapseAt` at a level step `s ≠ keep` whose
   immediate predecessor is a `keep` deletes that `keep` and leaves `s`.  This is "kept, then read
   where kept, is read", which is valid under T+4.  Then `collapse (j+1) ∘ shift j = id` on **every**
   path.  It agrees with `VarSymb.collapse` on every T+4-normal path (no `box`, no `keep` before a
   `dia`), so the canonical tags are unaffected.  Cost: re-prove the list identities with the
   look-behind case (mechanical; spot checks pass).
2. *Model condition*: under T+4 every root path is T+4-normal and well-typed for its root.  That
   needs a typing predicate on paths and its preservation; heavier, and it puts syntax-like
   well-formedness into the model.

### 10.31 ✅Step 2 done: option 1 adopted, η restored *(2026-10-03)*

**The rule.**  `Step.collapseAt` collapses a level step that comes right after a `keep` by deleting
the `keep` ("kept, then read where it was kept, is read"); otherwise it behaves as before.  Checked
first by brute force (every path of length ≤ 5, all seven identities), then proved:
`Step.collapseAt_shiftAt_succ` (the second counit, new), `collapseAt_shiftAt_self`,
`collapseAt_collapseAt`, `shiftAt_collapseAt`, `collapseAt_shiftAt`, `shiftAt_shiftAt`,
`shiftAt_shiftAt_self`.  The new case only ever fires at index 1 with a `keep` at the head, and closes
with "a leading level step survives a collapse at a positive index" (`headLvl_collapseAt_succ`).  The
leaf identities needed no change.  ⭐`Frame.Leaf.collapse_shift_succ` is new: families by
`trans_refl`, root paths by the list lemma.

**η.**  ⭐`ShEnv.ref_inner` (contents one view in = contents of the shape; under T+4 through
`u.keep.here`, i.e. the second counit) and ⭐`termShp_eta`.  `interp_eta` has its shape conjunct.

**Build.**  The whole `QML_v12m_*` list builds except `Completeness.lean:286` (the truth lemma's
`here` alternative, as before), with no new warnings.  The only `sorry`s are the three recorded
temporary ones in `CanonModel` (§10.29).  So **soundness holds over the new model class**: every
rule, including the `here_*` rules (still read with equality at `◇`-content; `Ind` is step 4).

**Next: step 3**, `here_eq` with its soundness and `subst_eqRec` at `◇`; then step 4, `Here` at
`◇`-content reads `Ind`; then step 5, the canonical model (tags, laws, removing the `sorry`s).

### 10.32 ✅Step 3 done: `here_eq` *(2026-10-03)*

* `Proof.here_eq : Here s t, eqRec t t' ⊢ Here s t'` — any content type, one annotation (`eqRec`).
* Soundness `Model.sat_here_eq`: `sat_eqRec` makes the two contents one object.  Under the current
  `Realised` (equality) this is immediate; under `Ind` (step 4) it stays immediate, since `Ind`
  receives the same object.
* `Proof.subst` case via ⭐`WFF.subst_eqRec_gen`: substitution commutes with `eqRec` at **every**
  type.  At `◇` both sides are `□_{ιx}` of the bodies under `θ.dia x (ιx)`, so the case is the
  inductive hypothesis; `WFF.subst`'s `.dia` arm builds the node at `ι x` definitionally, so a
  `congrArg` closes it.  The old `◇`-free `WFF.subst_eqRec` is now a special case (left in place for
  its callers).
* No other function recurses over `Proof` exhaustively, so nothing else needed a case.  Whole tree:
  same single error (`Completeness.lean:286`), same three recorded `CanonModel` sorries.

**Step 4 design note.**  `Ind`'s invariance ("related objects satisfy the same slot formulas")
mentions `sat`, which is defined *from* the model, so it cannot be a `Model` field.  The plan is a
field `Ind` with only structural conditions (reflexive, equality at `◇`-free types), plus a
predicate `Model.IndInvariant` stated after `sat`.  Soundness takes it as a hypothesis, and the
canonical model proves it.  Validity is then over the models satisfying it.

### 10.33 ✅Step 4 done: `Here` reads indistinguishability; models proper *(2026-10-03)*

**The decision (user).**  Not B ("same extent, indistinguishable contents"): indistinguishable does
not mean sharing worlds — identifying them should be consistent, not forced — and B would break
"a child's language is read off the parent plus the witness".  Not A (a bisimulation): bisimilarity
is strictly stronger than indistinguishability outside saturated models, so it says more than the
syntax.  **C**, read as a two-stage definition: the structure carries `Ind`, satisfaction is defined
over it, and a **model proper** is one whose `Ind` is invariant.  The condition is exactly the
semantic content of `here_subst`, and it cannot be a field, because truth depends on `Here`, `Here`
on indistinguishability, and indistinguishability on truth.

**In the code.**
* `Model.Ind` (any type) with `Ind_refl`; ⭐`Model.IndInvariant` (in `SemHere`): `Ind`-related
  objects satisfy the same formulas in any environment (`env.extend r o` vs `env.extend r o'`).
  `Model.indInvariant_of_eq`: a model whose `Ind` is equality is proper.
* `Model.Realised` reads `M.Ind (content at the identity arrow) o`.
* `SemHere`: `sat_here_name`, the strong-T existential and the `T_dia` case construct by `Ind_refl`.
  `sat_here_subst`, `sat_here_elim`, `sat_here_intro` and `sat_here_beta` consume via
  `IndInvariant`.  The bridge `sat_viewReadTm` takes `Ind` (not equality) between the body's value
  and `t`.  ⭐β uses its own new subject: `⟨x; viewReadTm bd s⟩` is realised with content `s`
  read with `c` in the hole, so the atom "`Here`(that subject, `s` read with the hole)" holds at `c`
  by reflexivity, and invariance carries it to `t`'s value.  New helpers `interp_viewReadTm`
  (generalised) and `interp_hereRead`.  `sat_here_fun` is removed (unused; `here_fun` is derived).
* `Model.soundness` quantifies over models proper (`M.IndInvariant →`).  Validity in `completeness`,
  `provable_iff_valid`, `strong_completeness`, `compactness`, `WFF.SetSatisfiable` and the B-track
  counterparts likewise.  Both canonical models have `Ind := Eq` for now, so they are proper by
  `indInvariant_of_eq`.  The T-track one switches to `DTerm.Rel` in step 5.

**Build.**  Same single error (`Completeness.lean:286`) and the same three recorded `CanonModel`
sorries.  `Compactness` is downstream of `Completeness`, so its edits are checked only once the
truth lemma closes.

### 10.34 Scoping step 5: the canonical model with shapes and `Ind` *(2026-10-03)*

**What the canonical model owes.**  (1) `RootPoss` and `shape` satisfying `shape_posMap` and
`shape_posStrength` (the three temporary `sorry`s); (2) weakened `pos_inj`; (3) `Ind := ` the
interchangeability of representatives; (4) `IndInvariant` — after the truth lemma, since it is no
longer a field; (5) the truth lemma's `here` case (step 6).

**Why the carriers need tags.**  The carriers are definable raw objects: a possible object is
`⟨extent, contents⟩`.  The laws demand, e.g., `shape (posStrength n p)` built from the shapes of `n`'s
values at **all** arrows, while the raw object only remembers `n` on `p`'s extent.  Two different `n`
agreeing on that extent give one raw object and two demanded shapes, so no shape *function* exists.
The object must carry its shape.

**The design: store the shape.**
* `RootPoss w := VarSymb` (the witness addresses).
* `RDom (◇A) w := (Σ E, contents) × Shp (Leaf w) (◇A)`: the section, and the shape as a tag.
  `shape p := p.tag`.
* `rawEval` transports tags exactly as the laws say (`diaMap g`: label kept, body by `g.shp 1`;
  `strength`: the transposed shapes of the necessary values).  **The laws then hold by
  definition**, and weakened `pos_inj` is `Prod.ext` — no argument at all.
* `rden`'s tag for `⟨x; t⟩` is the term's symbolic shape (`termShp`) in the **canonical shape
  environment**.  ◇-addresses `x` get the identity shape: label `root x []`, and at position `π`
  of the content `root x (dia :: π)`.  □-addresses get the transposition of their values' shapes at
  the successors, by recursion on the type.

**Work items.**
1. *Lift the shape layer from `Model` to `(Frame, RootPoss)`.*  `ShEnv`, `termShp` and S1 use the
   model only for their types, but the canonical construction needs them before the model exists.
   Mechanical: re-parameterise the first part of `SemShape`, keeping the `Model` names as
   specialisations.
2. *Tags in `RDom`/`rden`/`rawEval`*, and the tag half of the `rden` family (`rden_mono`,
   `rden_congr`, `rden_eqRec`, …).  The tag of `rden t` is `termShp`, which is stage- and
   weakening-invariant (`termShp_mono`).
3. *`definable_rawEval` with tags*: `termShp (applyG g t) = GFunc.shp g j (termShp t)`, by induction
   on `g` — the `applyG` analogue of S1.
4. *`interp_canon` with tags*: from S2 (`domSh_interp`) and `termShp_eta`, provided the canonical
   environment's shapes are the canonical shape environment, which holds by construction.
5. *`Interch`/`DTerm.Rel` at every type* (now `◇`-typed only), then `Ind o o' := ∃ representatives
   related by `Rel``.  Reflexive because every canonical object is definable.
6. *Step 6, the truth lemma's `here` case*: membership ⇒ `Rel` (`rel_of_coname`) ⇒ `Ind`.
   Conversely, from `Ind`: equal denotations ⇒ same annotation (**tags determine annotations**:
   root labels carry addresses, family leaves at the reflexive successor carry `u.here`'s address)
   ⇒ `eqRec` by the truth lemma at a smaller formula ⇒ `here_eq`.  Then `Rel` moves the atom.
7. *Canonical `IndInvariant`*: every definable environment is a substitution instance of the
   canonical one, then `sat_subst`, the truth lemma, and `Rel`.

**Risks.**  Item 1 is a refactor of a file that already builds — low risk, some churn.  Items 2–3
touch the largest canonical files (`CanonDom`, `CanonFunc`).  Their proofs are mostly by `rfl` on
sections, so the tag halves should follow the same shape, but this is where the size is.  Item 6's
"tags determine annotations" is the one genuinely new canonical fact.  It needs the reflexive
successor, so it holds under T, which is the only place `Here` exists.

### 10.35 A possible object is extent + content + shape: one evaluation map *(2026-10-03)*

**The decision (user).**  Mathematically this changes nothing: `posEval` and `shape` were already
jointly injective.  But the shape now belongs to the evaluation itself, gated by T: a possible
object *is* its extent, its contents and its shape.

* `Model.posFull : Pos A w → PosSec A w × (T = true → Shp (Leaf RootPoss w) (◇A))`, with
  `posFull_inj` plain injectivity.
* The laws `posMap_full` / `posStrength_full` each state the whole evaluation: section and shape.
* `Model.posEval` and `Model.shape` are now `abbrev`s for the two components.  `Model.pos_inj` (two
  hypotheses), `posMap_eval`, `posStrength_eval`, `shape_posMap` and `shape_posStrength` are
  theorems, so no use site changed.
* Both canonical models give `posFull := (section, shape)`.  The T-track one keeps its recorded
  temporary `sorry`s, now in the shape component of `posFull` and the shape halves of the two laws,
  until step 5's tags.

**An example of what the shape adds.**  With `x : ◇(◇Var × ◇Var)`, the terms `⟨x; x.dia.fst⟩` and
`⟨x; x.dia.snd⟩` have shapes `dia (root r []) (dia (root r [dia, fst]) var)` and
`dia (root r []) (dia (root r [dia, snd]) var)`.  If `x` is impossible their sections coincide
(empty extent, vacuous content).  Even with a nonempty extent they coincide whenever the two
components happen to agree at every arrow.  The shapes keep them apart, matching the syntax, where
their annotations differ and `eqRec` cannot compare them.

### 10.36 Step 5, item 1: the shape layer at frame level *(2026-10-03)*

`SemShape`'s definitions and lemmas — `Shape`, `ShEnv` and its pushes, `termShp`, S1
(`termShp_compile`), transposition (T), `termShp_mono`, `termShp_ann`, the map/collapse/shift
commutations — are now parameterised by a frame and a family of roots, `{F : Frame σ}
{Root : F.W → Type u}`.  `Shape F Root w T` and `ShEnv F Root Γ w` take them explicitly.  Only the
model link (S2: `domSh`, `envShape`, `domSh_interp`, and the bundle lemmas) still mentions a
`Model`; it sits in a `ModelShapes` section at the end.  The model-level files write
`ShEnv M.frame M.RootPoss`.  Lemma names are unchanged, so no proof changed.  This lets the
canonical construction compute its tags with `termShp` before the canonical model exists.
Build unchanged.

### 10.37 ✅Step 5, items 2–4: the canonical tags; the temporary `sorry`s are gone *(2026-10-03)*

**A circularity, and the split that removes it.**  A shape's type, `Shp (Leaf … w) (◇A)`, depended on
the whole `Frame`.  The canonical frame's `Pos` carriers are built from the tagged raw objects, so the
tags could not be typed.  A leaf only ever uses worlds, arrows, `refl`, `trans` and their laws.  These
are now a structure **`Arrows σ`**, and `Frame σ extends Arrows σ`.  The signature is a phantom
parameter, there so that `GFunc.shp` can read `σ` off the arrows as it read it off the frame.
`Arrows.Leaf`, `Arrows.transposeShp` and the whole frame-level shape layer take `{F : Arrows σ}`.
This covers `ShEnv`, `termShp`, the collapse/shift/mono/subst/η lemmas, `termShp_collapse_self` and
`termShp_shift_twoBox`.  The model-level files write `ShEnv M.arrows M.RootPoss`, with
`Model.arrows := M.frame.toArrows`.

**The canonical shapes (`QML_v12m_CanonShape.lean`, new).**
* `Canon.arrows σ N₀`: worlds and chains.  The canonical frame is `{ toArrows := arrows σ N₀, … }`.
* `canonSh w v T`, by recursion on `T`.  A `◇` address is a root: label `root v []`, and each `◇`
  position of its content is `root v π` (`rootSh`; since §10.39 the path is written as the address of
  the position is, `inner`-style, not with the shape's own `box`).  A `□` address has, at each successor `s`, the
  shape of `succAddr w s v.inner`: collapsed at the world itself, shifted `d` times `d + 1` levels
  deeper, exactly as `rden` moves a `□` body.
* `canonEnvF Γ w f` reads each address through `f`.  When `f` commutes with projections, every
  reachable address reads canonically (`canonEnvF_ref`).  `cEnv := canonEnvF · · id` does not depend
  on the context, so stage changes and weakening leave shapes alone.
* ⭐`cEnv_boxPush`: `cEnv` pushed into `□` is the transposed family `s ↦ canonEnvF Γ.boxIn s
  (succAddr w s)`.  The `keep` entries need one address identity over composite arrows,
  `succAddr_keep` (`shiftIter`/`keepIter` arithmetic; under T+4 the `keepOnly` contents `u.keep.here`).

**Tags (`CanonDom`, `CanonFunc`).**
* `RDom (◇A) w := RPos w A …`, a structure with fields `E`, `c` and `tag : T = true → CShape w (◇A)`.
  `.1`/`.2` keep their meaning, so most proofs were untouched.  **The tag is gated by T**, as
  `Model.posFull` is: without T two raw objects with one section must be one object, which an
  ungated tag would break.
* `rden`'s tag for `⟨x; t⟩` is `termShp (cEnv Γ w) 0 ⟨x; t⟩`.  Only `rden_mono` (by `termShp_mono`)
  and `rden_congr` (`rfl`) needed a tag half.
* `rawShape hT : RDom A w → CShape w A`, the raw `Frame.domShape`.  ⭐`rawShape_rden`: *the stored
  shape is the symbolic one*.  A `◇` term holds by definition.  A `□` term goes by `cEnv_boxPush` +
  `termShp_transpose`, then `termShp_collapse_cEnv` at the world itself or `termShp_shiftIter_cEnv`
  further on.  The recursion is on the type, as `rden`'s is.
* `rawEval` transports tags as the laws say.  ⭐`termShp_applyG`: `termShp (applyG g t) =
  g.shp (termShp t)`, for any arrows and any shape environment (the `applyG` analogue of S1).  With
  `rawShape_rden` for `strength`, it gives the tag halves of `rden_applyG`, so `definable_rawEval`
  is unchanged.

**The model (`CanonModel`, `CanonTerm`).**  `RootPoss _ := VarSymb` and `posFull p := (posEval p, p.1.3)`.
`posFull_injective` replaces `posEval_injective`.  `posMap_full`'s shape half is `rfl`, and
`posStrength_full`'s goes through `domShape_toDom`: a frame object's `domShape` is its raw object's
`rawShape`.  In `interp_canon`, `◇` now uses `Model.pos_inj`.  The shape half is S2
(`domSh_interp`) plus `envShape_canon`: the shapes of an environment agreeing with the canonical
one are `cEnv` (`domShape_toDom`, `rawShape_rden`, `termShp_eta`).

**State.**  The whole list builds with only `Completeness.lean:286` (the `here` alternative).
`QML_v12m_*` has no `sorry` (source scan); the three temporary ones of §10.29/§10.35 are gone.
Remaining in step 5: items 5 and 7 (`Interch`/`DTerm.Rel` at every type, canonical
`Ind := Rel` of representatives, canonical `IndInvariant`).  The canonical model still has
`Ind := Eq`.  Then step 6, the truth lemma's `here` case.

### 10.38 Step 5, items 5 and 7 begun: `Rel` at every type, the general datum, models proper over finite contexts *(2026-10-03)*

**Done.**
* `CanonInterch`: `Interch`, `DTerm`, `DTerm.Rel`, `interch_of_coname` and `rel_of_coname` are now
  stated at **every** type (they were `◇`-only), since `Here`'s content may have any type.  The
  `◇` transfer `Interch.dia_iff` is the instance at `◇A`.  The dead `extentTm` section is removed.
* `RealDatum` drops `hS` and `hA` (§10.10's plan).  A witness is realised whenever the theory says so,
  under weak T too, at any content type.  Only `rden_here_wd`/`rden_datum_wd`, which are about
  `◇`-free contents, take `◇`-freeness as a hypothesis.  `Realised.TStrong` is gone.
* ⭐**Models proper are now required to be invariant only over finite contexts, and only at slot
  formulas** (user decision, 2026-10-03: presented contexts are the ones proofs use).
  `Model.IndInvariant` quantifies over `Γ` with `[Γ.NoSlots]`, `Γ.Fin` and `Γ.NoProjLast`, and
  formulas `WFF σ (Γ.insert (.bnd 0) A) 1` — exactly the shape of `here_subst` and of `Rel`.
  *Why finite rather than presented*: `Proof.weak_ctx`'s premise lives in the smaller context, and
  presentedness does not pass downwards; finiteness does.  New file `QML_v12m_CtxFin.lean`:
  `Ctx.Fin` (finitely many declared addresses), closure under `Le` (downwards), `insert`, `boxIn`,
  `diaIn`, `Ctx.Fin.reach` (finitely many reachable addresses), and `Ctx.Presented.fin`.
  `Model.soundness` now takes `Γ.Fin` and carries it like `NoProjLast`, and its presented callers
  supply `Ctx.Presented.fin`.  The statements of `completeness`/`provable_iff_valid` are unchanged.

**Why finiteness is needed (item 7).**  Canonical `IndInvariant` has to speak about an *arbitrary*
environment.  The route is to name each of its values by a term at one stage, i.e. to write the
environment as a substitution of the canonical one, then use the truth lemma and `Rel`.  Over a
context with infinitely many addresses there may be no common stage.

**Open: "tags determine annotations" (item 6) is a real development.**  The `here` case's
truth-to-membership direction needs (F): canonical terms with equal denotations carry `Here` facts
across.  Reflexivity of `Ind` forces (F) for any choice of canonical `Ind`.  The planned route is:
equal tags ⇒ equal annotations, then `eqRec` (truth lemma at a smaller formula) and `here_eq`.  But
canonical leaves are root+path inside `◇`-contents and families at `□` positions, and views, `here`
(collapse) and `keep` (shift) transform them differently, so it needs a full characterization of
the leaf each view address gets.  Example of what it must see: under T, `u.here.box` and
`u.box.here` (for `u : □□X`) are different syntax and semantically different in general
(`n(w)(s)` vs `n(s)(s)`); their canonical shapes agree at the reflexive arrow and differ only at
proper successors.  Every canonical world has one under T (`T_box` refutes `□⊥`, then
`exists_box_fail`), but a general T model need not.  A possible simplification: label positions
inside `◇`-contents by their full address with an empty path, so that `here`/`keep` leave those
labels alone.  `rawShape_rden` and the laws do not depend on that convention.  Decision pending.

### 10.39 ⭐One labelling convention: a leaf is a label address, cut at the anchor's level *(2026-10-03, user)*

**Why step back.**  §10.38's "tags determine annotations" looked like a separate characterization
per view, per `here` and per `keep`.  The user's diagnosis: if addresses, roots, paths, families,
annotations and shapes all follow one convention, it should not bite.  An inventory bore this out:
one real mismatch and one unstated principle.

**What is written how.**
* An address is a root and steps, innermost last.  Level steps (`box`, `keep`, `dia`) enter a view;
  projections (`fst`, `snd`, `here`) stay at their level.  The contents of `u : □A` one view in are
  `u.inner` (`u.box`, or `u.keep.here` under T+4).
* An annotation label is the witness address of a `◇` node, a full address in that node's view,
  `inner`-style (`Ann.eta`).
* A shape is the type's tree with a leaf at each `◇` node; its positions are tree positions,
  separate from the labels.
* Leaves count levels from the anchor, while addresses count them from the label's own view.  This
  is not a mismatch: both count from the term's context, read from opposite ends, and
  `Step.collapseAt`/`shiftAt` (keep-absorbing) agree with `VarSymb.collapse`/`shift` on every
  T+4-normal path.

**The principle, now explicit.**  *A leaf records a label address by cutting it where it leaves the
anchor's level.*  If the first level step after the cut is a `□` step (`box`/`keep`), that level is
crossed semantically: a family over the anchor's successors, each entry the leaf of the same
address seen from that successor (`succAddr`).  If it is `dia`, the rest is kept syntactically, as
the path from the root possibility.  Families are forced at `□` levels: the strength law puts a
necessary object's values under one label.  A path is forced inside a content, because the extent
may be empty.

**The mismatch, fixed.**  `rootSh` wrote a `□` position inside a content as `box`, while every
address and annotation writes it `inner`, i.e. `keep.here` under T+4.  The leaf operations already
respect the address convention: shift then collapse (the second counit) on `[dia, keep, here]` gives
back `[dia, keep, here]`.  Only the canonical starting point broke it.  Now
`rootSh … (□A) = .box (rootSh … (π ++ Step.innerPath) A)`, with `Step.innerPath` the steps
`VarSymb.inner` appends (`VarSymb.inner_ext`).  Nothing proved depended on the old choice: the
whole list builds unchanged.

**What it buys (plan).**  Define `leafOf` (the principle as a function: world, depth, address ↦
leaf) and `canonSh w v T := Ann.eta v T` with labels read by `leafOf`.  The key lemma then reads:
*a term's canonical shape is its annotation, relabelled by `leafOf`*.  Its cases are the shape
layer's, plus `leafOf` commuting with collapse and shift, which is address arithmetic of the
`succAddr_keep` kind.  "Tags determine annotations" becomes injectivity of `leafOf`.  The decoder,
its left inverse, follows every family along a proper successor (where `succAddr` is the identity;
under T every canonical world has one) and reassembles root and path: the label address itself.
`u.box.here` and `u.here.box` decode to themselves, since the decoder never uses the reflexive
arrow.

### 10.40 ✅Step 5 done: tags determine annotations, the `here` case, canonical `Ind`, models proper *(2026-10-03)*

The truth lemma's `here` case is closed and the canonical model is a model proper, so the
semantic-annotation plan is complete.  `completeness`, `provable_iff_valid`, compactness and the
B track all build, sorry-free with no warnings.  Their statements are unchanged: they have quantified
over models proper since step 4.  What changed is the canonical witness: `Ind` was equality
(`indInvariant_of_eq`) and is now related representatives.

**The leaf calculus (`QML_v12m_CanonLeaf.lean`)** carries out §10.39's plan.
* *Address layer.*
  * `VarSymb.splitAt` cuts an address where it leaves a given level.
  * `Step.OK`/`VarSymb.OK`/`Ctx.DeclOK` are the T+4-normal addresses; every presented context is
    `DeclOK` (`Ctx.Presented.declOK`).
  * `VarSymb.collapse_agree`/`shift_agree` let front-indexed `collapseAt`/`shiftAt` act on an `OK`
    address exactly as `collapse`/`shift` do.
  * `succAddrK` is `succAddr` iterated over a depth.
* *Leaves.*
  * `leafOf w m y` is the principle as a function.
  * `annShp w j a` relabels an annotation by `leafOf`.
  * `rootSh_eq`/`canonSh_eq` show the canonical shape of a declared address is `annShp` of
    `Ann.eta`.
* *The calculus.*
  * `leafOf_collapse`/`leafOf_shift`: leaves commute with the shape layer's operations.
  * `Canonical` is the invariant "every leaf is `leafOf` of its label".
  * ⭐`termShp_canonical`: *a term's canonical shape is its annotation, relabelled*.
* *The decoder.*
  * `dec` follows every family along a proper successor (`properSucc`: under T `T_box` refutes
    `□⊥`, so `exists_box_fail` gives one; `exists_acc`) and reassembles root and path.
  * `dec_leafOf` makes `dec` a left inverse, so `annShp_injective`.
  * ⭐`ann_eq_of_rden`: two terms with one denotation (hence one tag, `rawShape_rden`) have one
    annotation.

**The `here` case (`QML_v12m_CanonHere.lean`).**
* `realised_of_here`: a `Here` atom in the theory makes its witness realised.  It goes through
  `here_beta` at unit, `here_name` and `exW`, which gives a `RealDatum`.
* `mem_here_realised`: the realised body is co-named with the possibility's content.
* ⭐`here_transfer` is (F) of §10.38.  Equal denotations carry a `Here` atom across: annotations
  agree by `ann_eq_of_rden`, `eqRec` holds by the truth lemma at a smaller formula
  (`WFF.size_eqRec`), and `Proof.here_eq` moves the atom.
* ⭐`here_truth`.  Canonical `Ind` relates two objects when they have representatives `s`, `s'`
  (`DTerm`s denoting them) with `s.Rel s'`.
  * *Membership ⇒ truth*: the related representatives are the realised body and `t`
    (`DTerm.rel_of_coname`).
  * *Truth ⇒ membership*: carry the atom from the realised body to `u`, across `Rel` to `u'` (at
    the slot formula `Here(S, ·)`, via `WFF.instantiate_here_slot`), then to `t`.
  * The `here` alternative of `truth_lt` only dispatches the `diatm` subject to `here_truth`.
  * The B track's `truth_lt` discharges `here` by `noT`, since `Here` needs T.

**Models proper over tame contexts.**  Representing an environment as a substitution needs
coherent witness indices.  Each declared address must be the only one that a given address extends
(`Ctx.decomp_unique`).  That holds when every root has one view depth (`Ctx.LevelDepth`).
`IndInvariant` therefore now asks for `Ctx.Tame Γ := Γ.Fin ∧ ∃ d, Γ.LevelDepth d` instead of
`Γ.Fin` (§10.38).  `Tame` is closed under `Le` (downwards), `insert`, `boxIn` and `diaIn`, and every
presented context is tame (`Ctx.Presented.tame`).  Soundness carries `Γ.Tame` as it carried
`Γ.Fin`.

**Canonical `IndInvariant` (`QML_v12m_CanonInd.lean`, `Canon.indInvariant` in `Completeness`).**
1. Every value has a representative term (`rep`, by definability).
2. Finitely many addresses give one stage above all of them (`repSup`).
3. The substitution `repSubst` sends each address to its representative there.  It is coherent by
   `decomp_unique` (`repSubst_coh`).
4. ⭐`substEnv_repSubst`: the canonical environment read through it is the given environment.

So `sat (env.extend o) φ` becomes membership of the substituted slot formula, instantiated at a
representative of `o`.  The chain is `substEnv_under`, `sat_subst`, `sat_mono`, `sat_instantiate`
and then the truth lemma.  `Rel` between the representatives of related objects makes the two
memberships agree.

**Knock-on changes.**  The B wrappers had not been updated when models proper arrived in step 4
(`completenessB` took `M.IndInvariant`, its callers did not), so `BRename` and `BFlat` failed to
build at `17e4035`.  The fixes are signature-only:
* `completenessB_rename`, `completenessB_ofDecls` and `completenessB_flat`;
* `completenessB_boxIn`/`diaIn`/`boxInN`/`presented`;
* the `RenameExample` validity hypotheses, which take `M.IndInvariant`.

Their proofs pass it through.

### 10.41 ✅`T_dia` without `hA`: strong T at every content type, and T is finished *(2026-10-03)*

§10.12's question, settled the way it argued for: `T_dia` is the object counterpart of `φ → ◇φ`
at every depth, so it now holds at `◇`-typed contents too.  Whole v12m list green, no `sorry`.

**Semantics: the frame condition reads `Ind`.**  `Model.posRet_exists` drops `_hA` and asks for a
possible object whose content at the world itself is `Ind`-related to the object, not equal to it.
The field moved below `Ind` (a structure field can only mention earlier ones).  This weakens the
condition (`Ind_refl` gives the old one) and is exactly what `T_dia`'s soundness uses, since `Here`
reads `Ind` (§10.33).  `Model.sat_here_ex` loses `hA` likewise.

**Proof theory.**  `Proof.T_dia` drops `(hA : A.diaFree = true)`; its substitution case and the
chain's consistency lemma (`consistent_grow_ret`, `retSet`) follow.

**The canonical model: no naming.**  The only real use of `hA` was `posRet_exists_canon`, which
named the object by an address (`exists_name`, `◇`-free only).  Now:
1. the object is some term `t`'s denotation (definability);
2. the theory has `Here(η y, t)` for some witness `y` (`World.retW`, below);
3. that atom makes `y` realised (`realised_of_here`, moved from `CanonHere` into `CanonModel`) —
   the datum's content is still an **address**, from `here_name` and the witnessed theory, so
   `interp_canon`'s measure is untouched;
4. `y`'s η-expansion has the world in its extent with the datum's content there
   (`rden_eta_realised`), and that content and `t` are co-named — the datum's atom and the
   chain's, at one stage — so their representatives are related (`DTerm.rel_of_coname`): `Ind`.

**The chain reads terms again.**  `World.realW` (every `◇`-free declared address is some realised
witness's content) is replaced by `World.retW`: every term, of any type, at every stage, has a
`Here` atom about some declared witness at a later stage.  The query is
`WorldLang.RetQ L σ m := Σ l' A a, Term σ (L.ctxL m l') A a` — a term over the base at stage `m`
and a list of own variables — enumerated by `enumRQ` and read as `termQ n`.  Carrying `l'` makes
the query independent of the construction so far (as the address was); a step uses it when
`ctxL m l' ≤ ctxL m l`, the analogue of the old "address declared" guard (`IsRet`).
`exists_retW` picks the step that enumerates the term and reads `⊤`; `retW_of_step` is stated for
any query equal to the step's so that the equation can be `subst`ed.

**Removed as dead:** `enumAF`/`addrQ`, `exists_isRet_addr`, `retDatum`, `retLt`, `retFr`,
`Canon.exists_name`, `rden_castAnn`, `rden_here_wd`, `rden_datum_wd`, `rden_eta_realised_wd`.
`Proof.exists_eqRec_eta` stays as a derived rule.

**Where T stands** (§9 updated): every cell sound and complete at every content type.  Left:
§10.18 (narrow `here_beta`, tidying only) and KTB (the B canonical model lacks the T machinery).

## 11. Strong B: the `Back` family — design pass *(2026-10-03, paper only)*

Roadmap milestone 2.  This settles the shape of strong B on top of §3 B ("The relational form",
"Witnessed variants") and the decision of §9 (relational route), with what `Here` taught (§10).
Nothing here is implemented yet.

### 11.1 Four predicates, one definition

A round trip `w → v → w` has two legs.  Each leg ranges over all arrows or over a named possible
object's extent; the witnessing fixes the carrier and where the round-trip value sits:

| row | out leg | back leg | carrier | value at |
|---|---|---|---|---|
| 1 | all arrows (`□`) | all arrows home | `□□A` | `u.box.box` |
| 2 | `y`'s extent, `y : ◇□A` | all arrows home | `◇□A` | `y.dia.box` |
| 3 | all arrows | `c(a₁)`'s extent, `c : □◇A` | `□◇A` | `c.box.dia` |
| 4 | `y`'s extent | `y(a₁)`'s extent, `y : ◇◇A` | `◇◇A` | `y.dia.dia` |

**One definition, parameterised by the legs.**  For a carrier object `c` and `t : A` at `w`, with
`Out` the out leg's arrows and `Home(a₁)` the back leg's arrows from `a₁.1` that end at `w`:

```
Back c t  :=  (∃ a₁ ∈ Out)  ∧  ∀ a₁ ∈ Out, ∃ a₂ ∈ Home(a₁),  Ind (c(a₁)(a₂)) t
```

* **∀ out, ∃ back** (§3 B, forced by soundness of elimination and introduction together).
* **The out leg is nonempty** — *decision 2026-10-03 (user)*: `Back` asserts that its round trip
  exists, as `Here` asserts that the identity arrow is in the extent.  So a `Back` atom is never
  vacuously true, and functionality (below) needs no premise; the condition moves to surjectivity.
* **Up to `Ind`**, as `Here`: the canonical model will only co-name the returned value with `t`.
* **Not an evaluation map.**  `u(a₁)(a₂)` depends on the intermediate world in general; `Back u t`
  holds only for carriers whose round trip is the same, `t`, from every out arrow, and for no `t`
  otherwise.  The dependence on the intermediate world is what the witnessed out leg (rows 2, 4)
  localises: a named extent stands in for "the chosen world", which the language cannot name.

Row 1 is §3 B's `Back`; row 3 is its `BackW`.  B's two object-level maps (§2c axis 1) sit at
different rows: `◇□A → A` at row 2, `A → □◇A` at row 3 (whose choice-free existential form is
§3 B's (ii)).

### 11.2 Rules, stated once for the family

Hole formulas are **closed apart from the hole**: `ψ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1`,
weakened wherever it is read.  The round trip carries no addresses — there is no return collapse
(§3 B) — so the two ends meet only through the hole, as weak B's closedness requires.  Several
parameters are packed into the hole with a tuple: joint round trips go through pairing.

Subjects are **terms, not addresses** (§10.11): every term of type `□□A` is
`boxtm (boxtm bd)`, of `◇□A` `diatm y (boxtm bd)`, and so on, so the rules are stated at the body
`bd` and a substitution's image of a rule instance is an instance.  Below, `ψ⟨bd⟩` is `ψ` read two
views in with the body in its hole, `ψ(t)` read at the origin; `Out◇`/`Out□` and `Home□`/`Home◇`
are the leg's modalities (`◇`/`□`, or `◇_y`/`□_y`, `◇_{c.box}`/`□_{c.box}`).

| rule | statement | analogue | soundness *(paper)* |
|---|---|---|---|
| `back_elim` | `Back c t`, `Out◇ Home□ ψ⟨bd⟩` ⊢ `ψ(t)` | `here_elim` | the premise picks `a₁ ∈ Out`; `Back` gives `a₂ ∈ Home(a₁)` returning a value `Ind` to `t`; `IndInvariant` |
| `back_intro` | `Back c t`, `ψ(t)` ⊢ `Out□ Home◇ ψ⟨bd⟩` | `here_intro` | for each `a₁ ∈ Out` the returning `a₂` witnesses `Home◇`; `IndInvariant` |
| `back_ne` | `Back c t` ⊢ `Out◇ ⊤` | (`here_name`'s premise) | the existence clause |
| `back_beta` | `Back c t` ⊢ `Back (c mapped by s) (s(t))`, `s` a hole term closed apart from its hole | `here_beta` | as `sat_here_beta`: `IndInvariant` at a `Back` atom with a slot |
| `back_fun` | `Back c t`, `Back c t'`, `φ(t)` ⊢ `φ(t')` (substitutional) | `here_subst` | **relational return arrows**: the arrow `a₁.1 → w` is unique, so both values are `Ind` to one object; `IndInvariant` twice |
| `back_eq` | `Back c t`, `t = t'` ⊢ `Back c t'` (one annotation, `eqRec`) | `here_eq` | equality in the model |
| `B_strong` (row `r`) | `Out◇ ⊤` and, for a fresh carrier variable `c`, `Back (η c) t ⊢ φ`, give `⊢ φ` | `T_dia` | the frame condition below |

`B_strong` in elimination form makes `Out◇ ⊤ ⊢ ∃c. Back c t` a theorem, so the network's Henkin
witnessing supplies the atoms with no new construction step, exactly as `Proof.retEx` did for strong
T (`v12-arrow-canonical.md` §9.12).

### 11.3 Semantics

* **No new model data** for the predicate: `Back` is defined from the frame, `necEval`/`posEval`
  and `Ind`.
* **Surjectivity**, one existential field per row, gated by its flag and stated after `Ind` (as
  `posRet_exists`): every object at `w`, where the out leg is nonempty, is returned by some carrier
  object.
* **`back_fun` needs unique return arrows.**  `Frame.R : W → W → Sort v` allows several arrows
  `v → w`, along which one carrier can return different values; then `Back c t` and `Back c t'`
  both hold.  Option (a) of the discussion, chosen with the user: require `Subsingleton (R v w)`
  where strong B is on — relational frames, the intended semantics of
  `v12-arrow-canonical.md` §4 — so the canonical network can stay relational.  (The alternative,
  non-functional `Back` over arrow frames with several reverse arrows per network edge, is recorded
  and not pursued.)
* Under T or D, `Out◇ ⊤` is provable for the unwitnessed out leg, so its premise disappears.

### 11.4 Open, to settle on paper before building

1. **The negative atom in the canonical model — the main risk.**  The truth lemma's `Back` case
   needs, besides "an atom makes every child's way home return a value co-named with `t`" (a
   per-child obligation on the reverse translations), the converse: if `¬Back c t ∈ M w` and the out
   leg is nonempty, then **some child's** way home returns a value *not* related to `t`.  Nothing in
   §11.2 produces such a child; it is a new existence obligation, like `ex` for `□`, but stated about
   the reverse edge, whose translation the network chooses.  Whether it is schedulable — and whether
   a rule is missing that would make it so — decides whether this family is complete.  §3 B already
   names this ("whether its per-child obligation is schedulable … is the thing to settle"); row 3,
   whose back leg is a named witness arrow, is the natural first test.
2. **Which surjectivity axioms imply which.**  Witnessing the out leg weakens the predicate,
   witnessing the back leg strengthens it, but the carriers differ, so implications between the
   axioms go through `strength`.  Decide the flags (one per row, or bundles) once known.
3. **The frame restriction.**  How `Subsingleton (R v w)` enters `Frame` (a field gated by the
   flags, or a separate predicate on models) and that soundness of everything else is untouched.
4. **Interaction with T and 4.**  Under T the own arrow is one of the out arrows and of the arrows
   home.  With 4, `Back` asks one homeward route per child to agree, not all round trips (§4's
   coherence): strong B does **not** obviously yield 5's object-level component, contrary to a
   first guess (2026-10-03).

**Proposed order**: (1) on paper for row 3, then for the family; then the predicate, rules and
soundness for all four rows at once; then the canonical model.

### 11.5 The canonical model's obligations, on paper *(2026-10-03)*

How the B network (`BData`: relational `R`, one reverse edge per edge, a witness label
`kd s t : Option (VarSymb × VarType)` per directed edge) would satisfy `Back` atoms, and what the
logic must then prove.  The return of a carrier along a child `v`'s edge home is a `w`-term `r_v`,
chosen by the construction of the reverse translation; the truth lemma needs
`Back c t ∈ M w ⟺ every child's r_v is related (DTerm.Rel) to t`.

**(1) Rows 3 and 4: the witnesses share the edge home, and the logic needs an n-ary elimination.**
A witnessed back leg asks the edge home `v → w` to lie in `c(v)`'s extent.  Relationally there is
one such edge, so every row-3 atom at `w` claims **the same arrow** for its own witness, and
surjectivity makes such atoms exist for every `t`.  Relationally valid, therefore:
```
Back c₁ t₁, …, Back cₙ tₙ,
  ◇ ∃d̄. (□_{c₁.box} χ₁(c₁.box.dia, d̄.box) ∧ … ∧ □_{cₙ.box} χₙ(cₙ.box.dia, d̄.box))
    ⊢ ∃x̄. χ₁(t₁, x̄) ∧ … ∧ χₙ(tₙ, x̄)
```
No rule of §11.2 derives it (each elimination takes one atom), and the carriers cannot be paired
(no term joins possible objects over different witnesses).
* *Why it is sound — a common translation (user, 2026-10-03).*  At `v` the views `□_{cᵢ(v)}` share
  everything but their own witness content.  All of them are read at the one edge home, so each
  translates into `w`'s context — `cᵢ(v).dia ↦ tᵢ`, as its atom says, and `v`'s box items to their
  values at `w` along that edge, **the same in every translation**.  The `∃x̄` is the image of the
  shared part, `v`'s born items, which have no name at `w`.  Every `χᵢ` lives in one witness view,
  so the premise needs no joint view.
* *Not a breach of the pairing principle.*  The link between the possibilities comes from atoms
  that each name the same arrow, not from bare `◇`s happening to meet — as `Here x s, Here y s'`
  combine `□_x φ` and `□_y ψ` at T's identity arrow into `φ(s) ∧ ψ(s')`.  B's version differs by the
  intermediate world, whose born items are the shared part.
* *The rule:* `back_joint`, the display above, for a list of atoms of **any** rows (an unwitnessed
  back leg contributes `□` in place of `□_{cᵢ.box}`).  Sound for unique ways home, as
  `back_fun`.  Where pairing is available (rows 1–2) it is equivalent to `back_pair` below, so one
  joint rule could serve the family.
* *The network:* the edge home must lie in every row-3 carrier's extent at once, so `kd` becomes a
  **set of labels** per edge, each with its content and its `trX` obligation.  A local change to the
  weak-B construction; the consistency of a child's joint commitments is what `back_joint` supplies.
* Rows 1 and 2 need neither: their back leg is "any arrow home", which carries no witness, and
  `□A × □B ≅ □(A × B)` pairs their carriers.

**(2) Rows 1 and 2, positive atoms: one more rule, `back_pair`.**  Two atoms `Back u t`,
`Back u' t'` constrain one child jointly (`□χ(u.box.box, u'.box.box)` at `v` must give `χ(t, t')`).
With unique return arrows the pair returns the pair:
```
back_pair:  Back u t, Back u' t'  ⊢  Back ⟨u, u'⟩ ⟨t, t'⟩          (necPair on the carriers)
```
sound for relational frames, not derivable from §11.2 (surjectivity's carrier for `⟨t, t'⟩` is
unrelated to `u`, `u'`).  This is "joint possibility goes through pairing" in its positive form, and
then every joint obligation is one elimination at a paired carrier.  Born parameters are packed by
`∃`-introduction inside the view, so hole formulas closed apart from the hole suffice.

**(3) Rows 1 and 2, negative atoms: an introduction rule, `back_def`.**  If `¬Back u t ∈ M w` (and
`◇⊤`), some child must return a value not related to `t`.  At a base type, with `Θ` the closed hole
formulas that define `t` uniquely at `w` (`∀z. θ(z) → z = t`), a child containing `◇¬θ(u.box.box)`
for every `θ ∈ Θ` leaves its return free to differ from `t` (compactness).  Such a child is
consistent unless `M w ⊢ □(□θ₁(u.bb) ∨ … ∨ □θₙ(u.bb))` for some `θᵢ ∈ Θ`, and then, `θ := ⋁θᵢ`
also defining `t`, every child returns `t`.  So completeness needs exactly
```
back_def:  ◇⊤,  □□θ(u.box.box),  ∀z. θ(z) → z = t  ⊢  Back u t      (θ closed apart from its hole)
```
sound (every return satisfies `θ`, hence is `t`).  It is not derivable: nothing else produces a
`Back` atom about a given `u`.  With positive atoms present the defining formula may use returns
already known — `θ(z, t')` with `Back u' t'`, i.e. `back_def` at the paired carrier `⟨u, u'⟩` — so
the rule should be stated with such parameters (or derived from the base form with `back_pair`).
* Negative atoms are then met by one child each, scheduled like `ex`.
* **At `◇`-content types** "uniquely defines `t`" has no formula: there is no equality, and
  interchangeability is a schema.  So `back_def` is stated for `◇`-free `A` first; whether `Ind`
  (as for `Here`, §10.41) lets the general case through is open.  (Cf. the standing lesson: when an
  operation strips a `◇`, restrict to `◇`-free and nest.)

**(4) Under T, one more positive obligation: `back_here`.**  The own arrow is an out arrow, and the
arrow home from `w` is again the identity (relationally unique), so the round trip along it returns
`u.here.here`:
```
back_here (T):  Back u t, φ(t)  ⊢  φ(u.here.here)                  (substitutional, any slot φ)
```
sound, not derivable from §11.2 (`back_intro` only yields `◇`-statements).  Row 2 under T meets
`Here` the same way: if the own arrow is in `y`'s extent, `y`'s content there returns `t`
(`Back y t, Here y s ⊢` `s.here` interchangeable with `t`).

**Revised proposal.**  All four rows, with §11.2's rules plus `back_joint` (or `back_pair` where
pairing is available), `back_def` (◇-free contents first) and, under T, `back_here`.  Build rows 1
and 2 first — no multi-labelled edges, binary pairing — then rows 3 and 4 in the same milestone.
Still to check on paper: that weak B's reverse-translation construction can absorb the positive
obligations of all atoms (it commits one variable at a time; `back_joint` should make each
commitment a finite-piece step) — the analogue of the step-1 finite-piece lemma.

### 11.6 The finite-piece check: an obstacle for the relational design *(2026-10-03, paper)*

**How weak B builds a way home** (`BLocal`, `BNet*`): along the edge `v → w` the child's variables
are committed **one at a time, in `v`'s declaration order**, each to a **fresh** `w`-variable, a
Henkin witness of what `v` necessitates about it and the older committed ones
(`realise_consistent`).  The new image adapts to the old ones; `w` never constrains an image
beforehand, so nothing can go wrong.

**What `Back` changes.**  A positive atom `Back u t ∈ M w` fixes the return of `u`'s item along
**every** child: the image of `z.box`, where `z` is `u.box`'s image in `v`, must be (related to) `t`.
That image can no longer adapt — and it must still agree with the images of the child's other items
along the same edge.

**The obstacle.**  Let `u : □□Var` with `Back u t₀`, and `v` a child created **before** `u` was
declared in `w`.  Then `u.box`'s image `z` enters `v` late (the forward arrow commits `w`'s later
variables later), after some item `d` born at `v`, whose return `d'` is already a fresh `w`-variable.
If `v` comes to necessitate `□(d.box = z.box)`, then `z` must return `d'` and also `t₀`, so
`M w` must contain `d' = t₀`.  But nothing in `w`'s language ties `d'` to the child it came from —
`d'` is "some object with these properties" — so the Lindenbaum steps of `w` may well have put
`d' ≠ t₀` into `M w` before `u` existed.  Then neither choice for `z`'s image works.
* `back_pair`/`back_joint` do not help: they combine atoms about `w`'s carriers, and `d` is born at
  `v`, with no carrier in `w`.
* Committing out of order cannot help either: `z` exists only after `d` is committed.
* So this is an obstacle to the **construction**, not (yet) evidence of incompleteness: `w` would
  need to say "these returns come back along one child", and its language cannot name a child.

**Two ways forward.**
1. *Relational, with names for round trips.*  Give `w` a handle on each child's round trip — e.g. a
   possible object declared at the child's creation whose extent is that child, with returns
   stated relative to it (a witnessed out leg, row 2) — so that `w`'s theory can constrain all of a
   child's returns jointly.  New construction machinery; unclear yet whether the handle's type can
   keep up with a child whose items grow.
2. *Arrow semantics for strong B.*  Let each atom take **its own** way home: every child gets a
   dedicated back arrow per atom, whose translation fixes that atom's carrier and lets everything
   else adapt (fresh), exactly as weak B's commitments do.  Joint obligations disappear —
   `back_fun`, `back_pair`/`back_joint` become unsound and unnecessary, and rows 3–4 no longer need
   multi-labelled edges (each witness gets its own arrow).  The price: the canonical model is no
   longer relational, so strong B is complete over arrow frames only — against the 2026-09-19
   direction (`v12-arrow-canonical.md` §4), though weak B's relational result stands.
   Negative atoms still need `back_def`-style children (one per `(u, t)`).

Not decided; to be put to the user.

### 11.7 Option 1's crux: the born-item principle `P` *(2026-10-03, paper)*

**Option 1 restated.**  The logic already anticipates future carriers: surjectivity is a theorem
schema from the start, so `w`'s theory constrains its children by every carrier it could acquire.
(Example: a child necessitating `∀z:□A. □(d.box = z.box)` is refuted at `w` as soon as `w` has two
distinct objects — surjectivity, `back_pair`, instantiate `z` at both carriers' items, elimination.)
The construction would then need (i) **commit at birth**: a `Back`-carrier's item gets its return
fixed when it enters the child, and (ii) an **extended back-transfer** carrying a child's facts
quantified over its `□`-objects to `w` as facts quantified over `w`'s carriers:
```
v ⊨ ∀z:□A. (χ(z) → □ψ(d.box, z.box))   ⟹   w ⊨ ∀u ∀t. (Back u t ∧ □χ(u.box) → ψ(d', t))
```
Committing a born item's return `d'` as a fresh witness then needs, in its consistency step:
```
P:  ◇∃d:□A. (□Σ(d.box) ∧ ∀z:□A. (χ(z) → □ψ(d.box, z.box)))
       ⊢  ∃y. (Σ(y) ∧ ∀u ∀t. (Back u t ∧ □χ(u.box) → ψ(y, t)))
```
valid relationally (`y` := `d`'s return along the edge home), **not** valid over arrow frames
(`d` and the carriers may come home along different arrows).

**The parameter-free core is derivable.**  `◇∀z:□A. □ψ(z.box) ⊢ ∀t. ψ(t)` (`ψ` closed apart from
its hole): fix `t`; surjectivity gives a fresh `u` with `Back u t`; inside `◇` instantiate `z := u.box`
to get `◇□ψ(u.box.box)`; `back_elim` gives `ψ(t)`.  This is the Barcan-type consequence of strong B
recorded in §4 ("strong B ⇒ ◇-BF, parameter-free ✓").

**With the born parameter `d` every route fails at the same point.**  The conclusion needs one `y`
for **all** carriers (`∃y ∀u`), and `y` must be `d`'s own return; but no rule says anything about the
return of an item born at the child:
* *via `y`'s carrier* (surjectivity gives `c` with `Back c y`): elimination at the pair `⟨c, u⟩` needs
  `□ψ(c(v).box, u(v).box)` at the child, but `c(v)` and `d` agree only along the edge home, so the
  child's fact about `d` does not transfer to `c(v)`;
* *via weak B on the refutation* (the negation of `P`'s conclusion is closed, so it holds `□◇` at
  the child): the successor it lands on is "some successor", and the step back needs the same
  `c(v)`-versus-`d` link;
* *via compactness*: it yields `∀u ∃y`, never `∃y ∀u`;
* *via a new carrier `e` with `e(v) = d`* ("name each born item by a carrier"): the existence of such
  an `e` is a gluing principle for necessary objects across children, which the general (non-full)
  models do not satisfy.

Every rule of §11 speaks only of `w`'s carriers and their returns; `P` speaks of a child's own items
coming home jointly with them.  So the conjecture: **`P` is not derivable from §11's rules**, and
option 1 needs `P` (or an equivalent) **as an axiom** — a parameterised, Barcan-strength principle,
relationally valid, characteristic of unique ways home.  This is §4's open "strong B ⇒ ◇-BF,
parameterised", met from the completeness side.

**Where that leaves the choice.**
* Option 1 = relational strong B **with `P` (or a cleaner equivalent) added**: completeness looks
  reachable along the lines above, at the price of a heavy new axiom whose simplest form is not yet
  known (a parameterised Barcan formula for necessary contents, `∀z:□A. □ψ(z.box, p̄) ⊢ □∀y. ψ(y, p̄)`,
  is valid relationally but does not obviously give `P`'s conditional form).
* Option 2 = arrow semantics: no `P`, no joint rules; the dedicated-arrow construction of §11.6.

### 11.8 The strong-T analogy: `P` is strong B's `T_dia∀` *(2026-10-03, paper; user's observation)*

Strong T met the same wall (§3 T, "Open problem: later constants"): the per-formula existential gave
`∀y ∃c` — a witness per formula — where the canonical model needs one witness for everything,
`∃c ∀y`.  Two ways out were found: **`T_dia∀`**, ∃-elimination for a manufactured witness whose
hypotheses carry `∀`-quantified parameters (equivalently the positive-polarity schema "from
`Φ⟨x := t⟩` infer `∃x. Φ(x)`, `Φ` positive in `x`"), and the **relational `Here` atom**, from which all
instances follow and which the canonical model reads its datum off.

`P` has exactly `T_dia∀`'s shape: a manufactured value (the return `y` of an item born at a child —
for T it was a possible object `c` realising `t`) with the uniform quantifier order `∃y ∀u`.  So:

* **The `T_dia∀` route: an export schema.**  Read a child's formula along the way home:
  ```
  from ◇Φ infer Φ↓        (Φ positive)
  ```
  where `↓` translates the child's formula at the world we return to: `□χ ↦ χ` (home is a
  successor); an item of `w` read two views in, `u.box.box ↦ t` given `Back u t` (row 3:
  `□_{c.box} χ(c.box.dia) ↦ χ(t)` given `Back c t`); an item born at the child, `∃d. … d.box …` ↦
  `∃y. … y …`; a quantifier over the child's `□`-objects `∀z:□A. … z.box …` ↦ a quantifier over `w`'s
  carriers `∀u ∀t. Back u t → … t …` (their images are among the child's `□`-objects).  Instances:
  **weak B** (`Φ := □ψ`, `ψ` closed: `◇□ψ ⊢ ψ`), **`back_elim`** (`Φ := □ψ(u.box.box)`),
  **`back_joint`** (a conjunction of such atoms, read at one home — so the joint rules become
  instances, not extra principles), and **`P`**.  It is exactly "a child's facts hold along the
  unique way home", which is what the relational semantics says; positivity is needed for the same
  reason as for T (`◇` and negation at the child do not speak about home).  Precedent: `T_dia∀` was
  accepted (2026-09-18) for precisely this reason.
* **The `Here` route: a relational atom for born items.**  The born item would have to be an
  argument at `w`, i.e. packed into a possible object `x : ◇□A` (row 2's carrier); then one atom
  `Back x y` would serve all carriers at once, through cross-row `back_joint`, as `Here` did for T.
  But packing `◇∃d. Φ(d) ⊢ ∃x:◇□A. ◇_x Φ(x.dia)` is a comprehension principle for possible objects
  that the general models do not satisfy (it is why strong D is an axiom).  For T the possible object
  was already the subject; here it is not.  So this route needs an extra axiom too, and a less
  natural one.

**Proposal.**  Take the export schema as strong B's characteristic rule, with `Back` (the four rows)
supplying the translation of returning carriers.  To check on paper before building: soundness of
the schema over relational frames; that `back_fun`, `back_pair` and `back_joint` are instances; that
the canonical construction of §11.6–11.7 goes through with it (commit at birth, the extended
back-transfer, `P` for born items); and its `T_dia∀`-style form with explicit hypotheses, which is
what an implementation would state.

### 11.9 ⭐Decision: the hybrid — relational where both ends can be named *(2026-10-03, user)*
> **Revised by §11.14:** born items get a relational form too (the returning possibility
> `◇[d ↦ t]`), so the line is simply *does the route return?* — all of T and strong B relational, 4's
> lift and 5 existential.

**The decision.**  Strong principles are **relational** (atoms) where a route returns to the origin
and both ends can be named there, and **existential** (∃-elimination rules for a manufactured
witness) where an object is born somewhere the origin cannot name.

| relational (atoms, `Here`-style) | existential (∃-elimination, `T_dia∀`-style) |
|---|---|
| T: `Here`, with `T_dia` (the witness is introduced at the origin with its atom) — **kept as is** | B: items **born at a child**, coming home (`B_ret`, §11.10) |
| B: `Back` (all four rows), optionally `Home`, for what the origin can name | 4's lift; 5's carrier principle; `◇-BF` (§3 4, §3 5) |

*Why this line.*  It is §2c's axis 4 ("names travel inward"): a pinned relation needs both arguments
in one scope, which a returning route gives for the origin's own objects and nothing gives for
objects born elsewhere.  4 and 5 never return, so a uniformly relational treatment is impossible;
uniformly schematic would throw away `Here`, which is better for examples and for a philosophical
audience.  The existential rules carry **no positivity condition**, as `T_dia∀` did not; positivity
appears only in the metatheory (the construction's invariant, and any equivalence with a one-line
schema).  Semantically the existential rule asserts only that a value of `w` with certain properties
exists (the item's return, always there), not that a new possible object exists, so no comprehension
principle is needed.

**Rejected:** uniform schemas (reverting T to `T_dia∀`); `Home` plus a comprehension principle for
possible objects (`◇∃d. Φ(d) ⊢ ∃x:◇□A. □_x Φ(x.dia)`, not valid in general models) for born items;
arrow semantics for strong B (§11.6 option 2).

### 11.10 The born-item rule `B_ret`, checked on paper *(2026-10-03)*
> **Superseded by §11.14** (`B_ret` replaced by the returning possibility); the soundness, `P` and
> construction arguments carry over.

**The rule.**  `Φ` a formula of the `□` view with one bound `d : □A` (the child's item); the `χ`s
closed apart from their holes:
```
B_ret:   Γ ; Δ ⊢ ◇∃d:□A. Φ(d)
         Γ, y:A ; H_{χ₁}(y), …, H_{χₙ}(y), Δ ⊢ φ          (y fresh for Γ, Δ, φ)
         ───────────────────────────────────────────
         Γ ; Δ ⊢ φ

H_χ(y)  :=  ∀ū:□□B̄ ∀t̄:B̄.  (Back ū t̄ ∧ χ(y, t̄))  →  ◇∃d. (Φ(d) ∧ ◇χ(d.box, ū.box.box))
```
"Introduce `y`, the value `d` comes home with: whatever holds of it, jointly with returning carriers,
is possible along a successor of a `Φ`-child."  The carriers `ū` are **bound in the hypothesis**, not
taken from `Γ`.  The shape is `T_dia∀`'s (`ψ↓(t) → ◇_c ψ↑`): a fact at the origin implies its reading
possible out there; nothing restricts `χ`'s polarity.

**(1) Soundness — ✓ on relational frames (unique way home), models proper.**  Let `v₀`, `d₀` witness
the premise, `r` the arrow `v₀ → w`, and `y := d₀.box` read along `r`.  Given `Back ūᵢ tᵢ` and
`χ(y, t̄)`: each `Back` returns along *some* arrow `v₀ → w`, which is `r`, so `ūᵢ.box.box` read along
`r` is `Ind` to `tᵢ`; `IndInvariant` turns `χ(y, t̄)` into `χ` of the values along `r`; so `v₀`, `d₀`
and `r` witness the consequent.  On arrow frames the carriers may come home along other arrows than
`d₀`'s, and the rule fails — it is the relational content, as expected.

**(2) Substitution — ✓ by construction.**  The `ū`, `t̄` are bound in `H_χ` and the `χ`s are closed
apart from their holes, so a substitution touches only `Φ` (uniformly, in the premise and in every
`H_χ`) and renames the fresh `y` as `T_dia∀` renamed `c`.  No case beyond `Subst.under` for the
binders.

**(3) `P` is derivable.**  Take `Φ(d) := □Σ(d.box) ∧ ∀z:□A.(ρ(z) → □ψ(d.box, z.box))`.  Under
`B_ret`'s hypotheses: if `¬Σ(y)`, `H_{¬Σ}` gives a `Φ`-child with `◇¬Σ(d.box)`, against
`□Σ(d.box)`; if `Back u t`, `□ρ(u.box)` and `¬ψ(y, t)`, `H_{¬ψ}` gives a `Φ`-child with
`◇¬ψ(d.box, u.box.box)`, while `Φ` at `z := u.box` (with `ρ(u.box)` from `□ρ(u.box)`) gives
`□ψ(d.box, u.box.box)`.  So `Σ(y) ∧ ∀u ∀t. (Back u t ∧ □ρ(u.box) → ψ(y, t))`; `∃`-introduction, and
`B_ret` discharges `y`.  One `y` serves every `u`: `∃y ∀u`.

**(4) The canonical construction — ✓ in outline.**  The *home reading* `Θ↓` of a **positive** child
formula `Θ` about an edge's committed items `ā` (images `ā'` in `w`): `□ψ ↦ ψ`; `ā.box ↦ ā'`; a
carrier's item `u.box.box ↦ t` under `Back u t`; `∀z:□C.(ρ(z) → …z.box…)` ↦
`∀u ∀t.(Back u t ∧ □ρ(u.box) → …t…)`; `∃d` (born) ↦ `∃x`; `∧`, `∨` homomorphically.
* **Invariant** (the extended back-transfer): along every edge `v → w`, every positive `Θ` true at `v`
  has `Θ↓ ∈ M w`.  It quantifies over **all** carriers of `w`, present and future, so late arrivals
  are covered in advance — this dissolves §11.6's obstacle.
* **Child creation.**  `v`'s seed plus `{¬Θ : ¬Θ↓ ∈ M w}` is consistent: otherwise the seed derives a
  positive `Θ`, so `◇Θ ∈ M w`, and the **export** `◇Θ ⊢ Θ↓` refutes `¬Θ↓`.  Export for positive `Θ` is
  derived by induction on `Θ`: `back_elim`/`back_joint` for `□ψ` atoms with carriers, `B_ret` for a
  top-level `∃d` (an `∃` below a `∀z` is per carrier and needs only `back_elim` with `∃` in the hole),
  `◇` distributing over `∨`, weak B for the closed part.
* **Committing an item `b`** (born, or an image without a `Back` value) to a fresh `b'`: a finite set
  of positive formulas about `ā, b` true at `v` gives `∃b. ⋀Θ`, positive about `ā`, so the invariant
  puts `∃x. ⋀Θ↓[x]` into `M w`; a Henkin witness realises the finite piece, and compactness gives the
  whole type — `realise_consistent` with `↓` in place of plain transfer.
* **Committing a carrier at birth** (a forward image `z` of `u` with `Back u t₀`, `t₀` the root from
  `exW`): `z.box ↦ t₀` at once.  `v`'s extension by `z` plus `{¬□ψ(ā.box, z.box) : ¬ψ(ā', t₀) ∈ M w}` is
  consistent: otherwise `v ⊢ ρ_u(z) → □ψ(ā.box, z.box)` for the forward facts `ρ_u`, with `z` fresh, so
  the positive `∀z.(ρ_u(z) → □ψ(ā.box, z.box))` holds at `v`; the invariant puts
  `∀u ∀t.(Back u t ∧ □ρ_u(u.box) → ψ(ā', t))` into `M w`, and `u, t₀` refute `¬ψ(ā', t₀)`.  Joint
  obligations between carriers are the same argument with several `z`s, which is where `back_joint`
  is used.
* **Negative atoms** (`¬Back u t`, `◇⊤`): a child whose return of `u` avoids `t`, by `back_def`'s
  argument (§11.5 (3)); `back_def` stays a rule (a `Back`-introduction; `◇`-free contents first).

**Still unchecked** (paper, before Lean): the home reading for every kind of item a child's formula
can mention (forward images of non-carrier items, `◇`-items, rows 3–4's witnessed back legs, where
`□_{c.box} χ ↦ χ` under a row-3 `Back`); the own arrow under T (the way home is the identity, where
`back_here` applies); `◇`-typed contents (`back_def` and the `Ind` side of `↓`); whether `back_fun`
is needed by the construction or only by the truth lemma.

**Rule set for strong B, as of now:** `Back` (four rows) with `back_elim`, `back_intro`, `back_ne`,
`back_beta`, `back_eq`, `back_fun`, `back_joint` (or `back_pair` for rows 1–2), `back_here` (T),
`back_def`, surjectivity `B_strong` per row, and `B_ret`.  Frames: unique ways home.

### 11.11 The unchecked items of §11.10 *(2026-10-03, paper)*

**(a) The home reading, item by item.**  Only what a child's `□` view sees can come home, and only
under a `□` (the way home is one of the child's successors).  So the positive class is built from
atoms `□ψ` (and, at a witness, `□_{c.box} ψ`), and `ψ`'s free items are contents of the child's
`□`-objects (or, for rows 3–4, of its possible objects along their witness arrows).  By kind:
* *Images of `w`'s carriers with a constant round trip*, `u.box.box` for `u : □□C` with `Back u t`:
  `↦ t` (row 1).  If `C` is itself modal, `ψ`'s deeper items `u.box.box.box…` follow by `unbox` of
  the substituted term, so the reading is a substitution of terms of `w` and nothing more.
* *Images of carriers without a constant round trip*: treated as born items —
  `◇Θ(u.box) ⊢ ◇∃d. Θ(d)` by `∃`-introduction inside `◇`, then `B_ret`.
* *Born `□`-objects* (`∃d`): `B_ret`.
* *Quantifiers over the child's `□`-objects* (`∀z:□C.(ρ(z) → …)`): over `w`'s carriers with `Back`,
  `ρ` read under `□` at `w`; sound because carriers' images are among the child's `□`-objects.
* *Contents of possible objects* (rows 3–4): `□_{c.box} χ(c.box.dia) ↦ χ(t)` under row-3
  `Back c t`; at a witnessed out leg (`◇_x Θ`, rows 2 and 4), `x.dia.box ↦ t` under row-2
  `Back x t`.  **New requirement:** `B_ret` needs a **witnessed variant** — premise `◇_x ∃d. Φ(d)`,
  hypotheses with `◇_x ∃d. (Φ(d) ∧ ◇χ(…))` — so that born items under a witnessed out leg come home
  too.  Best stated leg-parameterised, like `Back`.
* *Everything else is invisible or not in the class*: base objects of the child (`u.box : C` for base
  `C`, `x.dia` of non-`□` type) are not under a `□` and have no home value; `w`'s own `◇`-items are not
  visible in `□` views; a child-level `◇` (not `□`) says nothing about home and is excluded by
  positivity, which lives only in the construction's invariant, never in a rule.

**(b) The own arrow under T — ✓.**  The own arrow is one of the out arrows, and its way home is the
identity (relationally the unique arrow `w → w`).
* Soundness of `B_ret` is unchanged: if the premise is witnessed by `w` itself, `y := d₀` read at the
  identity, and every `Back` returns along the identity.
* In the construction the own arrow is not an edge; the invariant's case for it is "positive `Θ`
  true at `w` as its own successor gives `Θ↓`", which is the collapse — `T_box` for `□ψ ↦ ψ`,
  `u.box ↦ u.here` — plus **`back_here`** (`Back u t` makes `u.here.here` interchangeable with `t`).
  Both are rules; nothing new is needed.

**(c) `◇`-typed contents — open; restrict first.**  Positive atoms are fine at every type (`Ind`,
`IndInvariant`, as for `Here`).  The **negative** atom is the problem: a carrier `u` with no constant
round trip needs a child whose return is **not related** (`DTerm.Rel`) to a given `t`.  At a
`◇`-free type "not related" is one formula (`z ≠ t`), so a finite-piece argument works and its failure
is exactly `back_def`'s premise.  At a `◇`-typed type it is "some slot formula separates them" — an
infinitary disjunction, and no finitary `Back`-introduction is known that replaces `back_def`.
**Plan:** state `Back`'s content type `◇`-free (nesting `◇`s inside, per the standing lesson), as
`T_dia` was until §10.41; revisit with the `Ind` technique that lifted T's restriction.

**(d) `back_fun` — needed, and derivable from `back_joint`.**
* *Needed by the truth lemma* (and by the theory's coherence): with commit at birth every child
  returns `t₀` (the `exW` root of `∃t. Back u t`), so `Back u t` is true exactly when `t ~ t₀`; the
  direction "`Back u t ∈ M` ⇒ `t ~ t₀`" is functionality.  Without it a theory could hold `Back u t`
  and `Back u t₀` for unrelated `t`, `t₀`, which no relational model satisfies.
* *Derivable:* `back_joint` on `Back u t`, `Back u t₀` (the pair `⟨u, u⟩`) with the hole formula
  `φ(z₁) ↔ φ(z₂)`, after packing `φ`'s parameters into the hole through their own carriers
  (surjectivity), gives `φ(t) ↔ φ(t₀)`; at a `◇`-free type `z₁ = z₂` already gives `t = t₀`.  So
  `back_fun` can be a derived rule once `back_joint` is in place (under strong B, which supplies the
  parameters' carriers).

**Rule set after this pass:** `Back` (four rows, `◇`-free contents) with `back_elim`, `back_intro`,
`back_ne`, `back_beta`, `back_eq`, `back_joint`, `back_here` (T), `back_def`, `B_strong` per row,
and `B_ret` (leg-parameterised: plain and witnessed out leg).  `back_fun` derived.  Frames: unique
ways home.

**What remains before Lean:** the leg-parameterised `B_ret` written out with its soundness; the
export lemma's induction stated precisely over the positive class (the construction's invariant);
and a decision on how many rows to build first (rows 1–2 still need neither multi-labelled edges nor
row-3 `Back`).

### 11.12 ⭐Plan for `◇`-typed contents: a finer canonical `Ind`, and shapes under strong B *(2026-10-03, user)*

Settles how §11.11 (c) will be lifted; the first build stays `◇`-free.

**Why "build every consistent world" is not enough on its own.**  For a carrier `u` with no constant
round trip, the network does build a child whose return is separated from `t` whenever some slot
formula separates them (this is `back_def`'s compactness argument, phrased as "every consistent child
gets built").  What remains is the case where **no formula separates** the returns from `t` while
the theory denies `Back u t`.  Such a theory is satisfiable — models proper need only
`Ind ⊆ interchangeability`, so distinct, formula-indistinguishable, non-`Ind` returns are allowed —
but the canonical model with `Ind := DTerm.Rel` (all-formula interchangeability) identifies them and
cannot satisfy `¬Back u t`.  At `◇`-free types this cannot happen (`=` is a formula; `back_def`).

**Decision 1: canonical `Ind` generated by the atoms.**  Replace `Ind := DTerm.Rel` by the
equivalence **generated by the atoms**: co-naming through `Here` (`rel_of_coname`) and co-returning
through `Back` (two values returned by one carrier).
* Still `IndInvariant`: each generating atom implies interchangeability (`here_subst`, the derived
  `back_fun`), so the generated `Ind` is contained in `Rel`.
* T's proofs survive (on paper): `here_truth` and `posRet_exists_canon` use `Ind` only for co-named
  pairs; `indInvariant` needs only `Ind ⊆ Rel`.
* The negative `Back` atom becomes automatic: a carrier with no `Back` value has fresh return roots at
  its children, related to `t` by no atom, so not `Ind` to it.

**Decision 2: shapes gated by `T ∨ strong B`, not by T.**  Possible objects carry their shapes
(§10.27) whenever T **or** strong B is on.
* *It removes the coincidences.*  Without shapes, two fresh return roots can denote one possible
  object (same extent, same sections — e.g. both with empty extent), and equality then forces `Back`,
  which would need a `back_def` for formula-pinned possible objects.  A root possibility's shape
  records its root, so distinct roots are distinct objects, as under T.
* *It is needed anyway.*  The truth lemma's `Back` case at `◇`-contents turns "the return is `Ind` to
  `t`" into equal denotations, and from there into `eqRec` at one annotation — the step `Here` took
  with "tags determine annotations" (`ann_eq_of_rden`), which needs the tags.  Shapes are justified by
  the `◇`-content relations, `Here` under T and `Back` under strong B, not by T as such.
* *Cost:* every lemma taking `hT : T = true` only to reach the tags (`posFull`, `domShape`,
  `envShape`, `termShp`, `rawShape`, both canonical shape layers) takes the new condition instead —
  mechanical but wide.  K's and weak systems' models are unchanged.
* *The leaf calculus without T.*  The network decoder used the own arrow (roots, cut position)
  together with one network arrow (§9.10).  Without T it must use network arrows alone: **typed
  injectivity** of `arrowIdx` (without T it is a root renaming dropping the box; the label's type
  fixes where the box was), **injective images** (`imgInj`, avoided under T; expected by construction,
  commitments going to fresh roots), and a network successor — absent only at dead ends, where every
  `Back` atom is false and nothing needs decoding.

**Order.**  First build: `◇`-free contents, shapes unchanged.  Then, to lift the restriction:
regate shapes, refine canonical `Ind` (T track and network), the T-free decoder, and `Back` at all
content types.
### 11.13 `B_ret` leg-parameterised, and the export over a precise class *(2026-10-03, paper)*

> **`B_ret` superseded by §11.14**; the class `𝒞` and its sufficiency for the construction stand,
> and the export over `𝒞` now follows from the returning possibility.

**`B_ret`, leg-parameterised.**  The out leg `O` is either plain (`◇`, the child seen in `Γ.boxIn`) or
witnessed by a possible object `x : ◇Y` of `Γ` (`◇_x`, the child seen in `Γ.diaIn x`).  Write
`O∃d. Φ(d)` for `◇∃d. Φ(d)` resp. `◇_x ∃d. Φ(d)`, with `d : □A` bound in that view.
```
B_ret_O:   Γ ; Δ ⊢ O∃d:□A. Φ(d)
           Γ, y:A ; H_{χ₁}(y), …, H_{χₙ}(y), Δ ⊢ φ          (y fresh for Γ, Δ, φ)
           ─────────────────────────────────────────────
           Γ ; Δ ⊢ φ

H_χ(y)  :=  ∀ū ∀t̄. (Back ū t̄ ∧ χ(y, t̄))  →  O∃d. (Φ(d) ∧ ◇χ(d.box, val ū))
```
* `ū` are bound carriers whose values the view can see: row-1 carriers `u : □□B` (value
  `val u = u.box.box`) for either leg; for the witnessed leg also `x` itself under row 2
  (`x : ◇□B`, `val x = x.dia.box`), which is the only row-2 carrier whose content is in scope.  Rows
  3–4 carriers (contents behind their own witness views) are left to the rows-3–4 build; their
  joint use goes through per-witness components as in `back_joint`.
* `d` may be a tuple (several born items: pair them, `□A × □A' ≅ □(A × A')`).
* *Soundness* (relational frames, unique way home, models proper): let the premise be witnessed by
  an arrow `a₀` (in `ext x` for the witnessed leg), its target `v₀`, `d₀`, and `r : v₀ → w`; set
  `y := d₀.box` read along `r`.  Every `Back` among the `ū` — row 1 over all out arrows, row 2 over
  `ext x ∋ a₀` — returns along *some* arrow `v₀ → w`, which is `r`; so `val ū` read along `r` is `Ind`
  to `t̄`, and `IndInvariant` gives `χ` of the values along `r`.  So `a₀`, `d₀`, `r` witness `H_χ`.
  The argument is the same for both legs, which is why one rule with a leg parameter suffices.
* *Substitution:* unchanged from §11.10 (carriers bound in `H_χ`, `χ` closed apart from its holes,
  `x` substituted by `Subst.dia` as everywhere else).

**The class the construction needs.**  Let `𝒞` (over a view, with committed items `ā` as
parameters) be the formulas
```
Θ  =  ∃d̄. ∀z̄. (ρ̄(z̄) → M)
```
* `d̄` one block of born `□`-objects; `z̄` one block of quantifiers over the child's `□`-objects (any
  `∀z`s of a positive formula can be prenexed past `∧`, `∨` and the `ρ`s);
* `ρ̄` arbitrary formulas of the view (they are read under `□` at `w`, so no polarity matters);
* `M` a positive combination (`∧`, `∨`) of atoms `□ψ`, `ψ` a formula of the next view whose free
  items are `ā.box`, `d̄.box`, `z̄.box` and carriers' `u.box.box`; `ψ` itself is unrestricted (in
  particular `∃` over base values may sit inside it).

**Home reading on `𝒞`:**
`Θ↓ := ∃ȳ. ∀ū ∀t̄. (Back ū t̄ ∧ □ρ̄(ū.box) → M↓)`, where `M↓` replaces each `□ψ` by `ψ` with
`ā.box ↦ ā'`, `d̄.box ↦ ȳ`, `z̄.box ↦ t̄`, a carrier's `u.box.box ↦ t_u` (under its `Back`).

**Export on `𝒞`:** `Γ ; Back hypotheses ⊢ O Θ → Θ↓`.  Proof: `B_ret_O` on the born block gives
`ȳ`; `∀`-introduce `ū, t̄` with `Back ū t̄` and `□ρ̄(ū.box)`; prove `M↓` by contradiction with
`χ := ¬M↓` (its holes are `ȳ`, `t̄` and the carriers' values — no carrier quantifier inside): `H_χ`
gives an `O`-child with `Φ(d̄)` and `◇¬M↓(d̄.box, z̄ := ū.box, …)`, while `Φ` at `z̄ := ū.box`, with
`ρ̄(ū.box)` from `□ρ̄(ū.box)`, gives `M`, hence `□M↓`-at-the-child (each `□ψ` true, `□` over `∨` is
`□(ψ₁ ∨ ψ₂)`).  This is §11.10's derivation of `P`, done for the whole class.

**`𝒞` is enough for the construction.**  Its three uses:
* *the invariant itself*, stated for `𝒞`: along every edge, `Θ ∈ 𝒞` true at the child gives
  `Θ↓ ∈ M w`;
* *child creation*: the seed plus `{¬Θ : Θ ∈ 𝒞, ¬Θ↓ ∈ M w}` is consistent by export on `𝒞` (`𝒞` is
  closed under finite `∨`, which the compactness step forms);
* *committing an item `b`*: `∃b. ⋀Θ` for finitely many `Θ ∈ 𝒞` about `ā, b` is again in `𝒞` (merge
  `b` into the born block, prenex the carrier blocks); *committing a carrier at birth* uses
  `∀z.(ρ_u(z) → □ψ(ā.box, z.box))`, in `𝒞`.

**What `𝒞` deliberately excludes:** a born item **under** a carrier quantifier that shares an outer
born item — `∃d ∀z ∃d' ∀z' …`, with home reading `∃y ∀u ∃y' ∀u' …`.  Exporting it would need, inside
`H_χ`, quantifiers over the *successor's* carriers, i.e. the parameterised push
`∀z.(ρ(z) → □ψ(d.box, z.box)) ⊢ □∀u ∀t.(Back u t ∧ □ρ(u.box) → ψ(d.box, t))` — the parameterised
Barcan form of §11.7, valid but not derivable.  The construction never forms such formulas: born
items enter one block at a time, and committed ones become parameters.  (A born item under a carrier
quantifier *without* an outer born item, `∀z ∃d' …`, is per carrier and is `B_ret` again, with the
premise instantiated at `z := u.box`.)

**First build: rows 1 and 2.**  Rows 1–2 need neither multi-labelled edges nor per-witness
components; `B_ret` with both legs covers their born items; the class `𝒞` covers the construction.
Rows 3–4 follow in the same milestone, with multi-labelled edges and row-3/4 carriers in `H_χ`.

### 11.14 ⭐The returning possibility `◇[d ↦ t] Φ(d)` — replaces `B_ret` *(2026-10-03, user + paper)*

`B_ret` (§11.10, §11.13) manufactured the home value `y` of an item born at a child and then had to
say, through the hypothesis schema `H_χ`, what `y` was related to — because the born item cannot be
named at `w`.  But something at `w` *can* stand for it: the **possibility itself**.  Make it the
subject of a relation, as `Here` makes a possible object the subject.

**The formula former.**  For `t : A` a term of `Γ` and `Φ(d)` a formula of the `□` view with
`d : □A` bound:
```
◇[d ↦ t] Φ(d)     "possibly some necessary object d is such that Φ(d), and its content comes back
                   here as t"
```
Semantics: some out arrow `a : w → v` and `d ∈ Nec_v(A)` with `Φ(d)` at `v`, and `d`'s value along the
way home `r : v → w` is `Ind` to `t`.  Well defined because the way home is unique (relational
frames).  Both ends are in scope at `w`: `t` directly, `d` under its binder — `Here`'s shape with a
possibility as subject instead of a possible object, so **no comprehension principle** is needed.
`d` may be a tuple `d̄ ↦ t̄` (several items of one child).

**Rules.**
* **Existence** (the analogue of `here_name`), in extension form — one more item of the same child:
  ```
  ◇[ā ↦ ā'] ∃b. Φ(ā, b)   ⊢   ∃t. ◇[ā, b ↦ ā', t] Φ(ā, b)
  ```
  (`ā` empty: `◇∃d. Φ(d) ⊢ ∃t. ◇[d ↦ t] Φ(d)`.)  Sound: the premise's child and `b`, `t` := `b`'s
  value along the same way home.
* **Elimination** (with carriers; the work-horse):
  ```
  ◇[d̄ ↦ ȳ] ∀z̄.(ρ̄(z̄) → □ψ(d̄.box, z̄.box)),   Back ū t̄,   □ρ̄(ū.box)   ⊢   ψ(ȳ, t̄)
  ```
  `ψ` closed apart from its holes; no carriers gives `◇[d ↦ y] □ψ(d.box) ⊢ ψ(y)` — "what is necessary
  of `d` out there holds of its value here".  Sound: take the atom's child and `d̄`, instantiate
  `z̄ := ū`'s images there (`ρ̄` from `□ρ̄(ū.box)`), read `□ψ` along the way home `r`; each `Back` returns
  along some arrow home, which is `r`; `IndInvariant`.
* **β** (terms built from returned items return as the same terms): `◇[d̄ ↦ ȳ] Φ(s(d̄)) ⊢
  ◇[e ↦ s↓(ȳ)] Φ(e)`, with `s↓` the term `s` read at home (its items `d̄.box ↦ ȳ`).
* **Monotonicity**: `◇[d̄ ↦ t̄] Φ`, `□∀d̄.(Φ → Φ')` ⊢ `◇[d̄ ↦ t̄] Φ'`; and `◇[d̄ ↦ t̄] Φ ⊢ ◇∃d̄. Φ`.
* **Leibniz in `t`**, as `here_eq`.
* **Under T** (the own arrow, whose way home is the identity): `Φ↓(s) ⊢ ◇[d ↦ s.here] Φ(d)`, with
  `Φ↓` the collapse — the counterpart of `back_here`.

**What it replaces.**  `B_ret` and its `H_χ` are gone.  `P` is existence then elimination, once per
carrier — one atom, so `∃y ∀u` for free, as `Here` gave T its uniformity.  The export over the class `𝒞`
of §11.13 follows the same way (a positive matrix `M` gives `□M♭`, `M♭` = `M` with its boxes
stripped).  No positivity condition anywhere in the rules.

**The dividing line, refined (revises §11.9).**  Relational **exactly when the route returns to the
origin**, with the subject an object (`Here`: a possible object; `Back`: a carrier) or a possibility
(`◇[d ↦ t]`); existential only where the route does not return.  That is §2c's axis 4 with no special
case: all of T and all of strong B are relational; what stays existential is 4's lift and 5.
*Reminder — 4's lift:* by transitivity, a possible object found at a possible world should give a
possible object here reaching those worlds directly with the same contents,
`◇_x ◇_{x.dia} θ ⊢ ∃z:◇A. ◇_z θ(z.dia)` (`Pos(v) → Pos(w)`, §3 4; §2c also uses "lift" for the
`Nec(v) → Nec(w)` direction, "no new necessary objects deeper") — the route `w → v → s` never comes
back, so no relation at `w` can hold both ends.

**Check 1: substitution — ✓.**  `t` is a term of `Γ`, substituted as `Here`'s argument is; `Φ` is
substituted by `θ.box` under the binder for `d̄` (`Subst.under`), as `◇` and `∃` are.  Rules are stated
at terms, not addresses (§10.11): a carrier is given as its body `s : Term σ Γ.boxIn (□C)` (every
`□□C` term is `boxtm s`), `z̄ := s` instantiates inside the view, and `z̄.box ↦ s`'s body in the next
view; a substitution sends an instance to an instance.  Existence and β bind `t`/`e` at `w`
(`under`), monotonicity and Leibniz are structural.  Nothing beyond what `here_*` and `◇∃` already
need.

**Check 2: the canonical truth-lemma case — ✓ in outline, and it simplifies the construction.**  The
extended back-transfer of §11.10–11.13 becomes an **atom invariant**:
> along every edge `v → w`, for every finite `Θ` true at `v` of the committed items `ā` (images `ā'`):
> `◇[ā ↦ ā'] Θ(ā) ∈ M w`.
Everything about home readings and carriers then follows from the atoms by elimination.
* *Base case* (nothing committed): `◇Θ ∈ M w` for `Θ` true at `v` — forward transfer, as now.
* *Committing `b`* (born, or an image without a `Back` value): `∃b. ⋀Θ(ā, b)` is true at `v`, so by
  the invariant `◇[ā ↦ ā'] ∃b. ⋀Θ ∈ M w`, so existence gives `∃t. ◇[ā, b ↦ ā', t] ⋀Θ`; its Henkin
  witness is `b'`.  Compactness gives all `Θ` at once — **committing a born item is Henkin
  witnessing**, as `retW` came from `exW` in step 6.
* *Committing a carrier at birth* (`Back u t₀`): its item's image is `t₀`; the joint obligations are
  elimination with the carriers in `ū`.
* *Membership ⇒ truth*: an atom `◇[d ↦ t] Φ ∈ M w` gets a child, as `exX` gives one to `◇_x`: the seed
  `Φ(d)` with `d` declared fresh in the child and **committed at birth** to `t`; its consistency is
  elimination (and monotonicity) from the atom — a failure would put some `Θ` with `¬Θ↓(t)` into
  `□∀d.(Φ → Θ)`, and the atom then yields `Θ↓(t)`.
* *Truth ⇒ membership*: a child `v` and a canonical object `d = rden s` with `Φ(d)` and home value `Ind`
  to `t`.  `s` is built from `v`'s committed items `b̄` (fairness), so the invariant gives
  `◇[b̄ ↦ b̄'] Φ(s(b̄)) ∈ M w`; **β** gives `◇[e ↦ s↓(b̄')] Φ(e)`; `s↓(b̄')` is `d`'s home value, `Ind` to
  `t`, so Leibniz (through `Ind`) gives the atom.  At the own arrow under T: the T-rule.

**Check 3: is `back_joint` still needed? — yes, in its carrier form, but smaller.**  The elimination
rule takes several carriers with **separate** `Back` atoms, which covers every joint *use* (`P`, the
export, commit at birth), so the n-ary `back_joint` is no longer a separate rule.  What remains is
**`back_pair`** — `Back u t, Back u' t' ⊢ Back ⟨u, u'⟩ ⟨t, t'⟩` — needed by the truth lemma for `Back`
atoms at compound carriers (a pair of carriers is a term, and the theory must contain its atom).  It
is about all children at once (∀ over the out leg), which the returning possibility (∃, one child)
cannot supply.  Rows 3–4's per-witness components carry over to elimination the same way.

**Rule set for strong B now:** `Back` (four rows; first build rows 1–2, `◇`-free contents) with
`back_elim`, `back_intro`, `back_ne`, `back_beta`, `back_eq`, `back_pair`, `back_here` (T),
`back_def`, surjectivity per row; the returning possibility `◇[d ↦ t]` with existence, elimination,
β, monotonicity, Leibniz, and its T-rule.  `back_fun` derived.  Frames: unique ways home.

### 11.15 ⭐`◇`-typed contents cannot wait: the network commits them *(2026-10-04, user)*

**The obstacle (found mapping step 5 onto the network).**  The network commits **every** variable
of a node along each arrow, at its box-contents type `bc`; and `bc (□◇D) = ◇D`.  Committing one
more `◇`-free item `b` along `k → p` asks its image `c` for two things at once:
* *transfer* — `ψ'(ō', c)` at `p` for every `□ψ(ō, b)` at `k`, where `ō` may include items with
  `◇`-typed contents, already committed to `ō'`;
* *the atom invariant* — `◇[ā, b ↦ ā', c] Θ` at `p` for every `Θ` at `k` about the `◇`-free items.
Each family is satisfiable alone (the existing realisation lemma; `ret_ext`), but jointly they need a
returning possibility whose body speaks of `ō`, i.e. binds `d : □◇D`.  Ordering does not help (a
node's theory is complete at every stage, so the mixed facts are decided when `b` is committed), and
the `◇`-content items cannot be dropped (the `□` case of the truth lemma needs their transfer).

**Decision (user, 2026-10-04): go straight to the general case** — the `◇`-free restriction was to
make things easier, and here it makes them harder.

**What the general case needs, rule by rule.**  At `◇`-free contents `Ind` to a named value is
equality (`Model.eq_of_ind`); at `◇`-typed contents it is not, so:
* *two congruence laws on `Ind`*, as conditions of a model proper beside `IndInvariant` (they
  mention terms, so they cannot be `Model` fields): preservation by closed hole-term maps
  (`back_beta`, `ret_beta`) and by pairing (`back_pair`, `ret_ext`, `ret_back`);
* `back_here` substitutional (`Back u t, φ(t) ⊢ φ(u.here.here)`), as `here_subst`;
* `back_def` stays `◇`-free — at `◇`-types the negative atom is §11.12's decision 1 instead;
* everything else (`elim`, `intro`, `ne`, `eq`, `ret_elim`/`mono`/`dia`/`eq`/`here`/`bridge`,
  `B_strong`) goes through at every type as it is.

**Phases.**
* **L1 — soundness side.**  Drop `A.diaFree` from `WFF.back`/`WFF.ret`; the two laws in "model
  proper"; the rules at every type; both canonical models prove the laws, from congruence of
  interchangeability (`Interch` under a hole-term map and under pairing — a slot formula composed
  with the map, then transitivity).
* **L2 — canonical `Ind` generated by the atoms** (§11.12, decision 1), as the *congruence* they
  generate, so the laws hold by construction and `IndInvariant` follows from `Ind ⊆ Rel` (L1's
  lemmas).  Check T's proofs on the tree and the network.
* **L3 — shapes gated by `T ∨ strong B`** (§11.12, decision 2), with the T-free leaf decoder.
* **L4 — the network** (step 5): the atom invariant at every type, commit at birth, a child per
  `ret` atom, `backRet_exists_canon`, the truth lemma's `back`/`ret` cases.

**L1 done (2026-10-04).**  `WFF.back`/`WFF.ret` take every content type.  A model proper
(`Model.IndInvariant`) is now a structure: invariance (`inv`) and the two congruence laws (`map`
for a closed hole term, `pair`).  Every rule is stated at every type except `back_def`, which stays
`◇`-free; `back_here` is substitutional; `ret_back` (which needed an equation between the carrier's
image and a component) is replaced by **elimination with a carrier**, `ret_elimC`:
`◇[d ↦ y] □ψ(d.box, ū), Back u t ⊢ ψ(y, t)`, the body naming the carrier's image `ū` directly — the
form §11.14's construction uses.  Both canonical models prove the laws from congruence of
interchangeability: `Canon.Interch.subst_slot` (the test formula with its slot replaced by the term,
`WFF.instantiate_bodyRepl`), with `Interch.holeAt`, `Interch.pair` and their stage-free
`DTerm.Rel` forms; the model-level step is that a hole term (or a pair) of representatives
represents the mapped (or paired) object (`Canon.rden_holeAt`, `BData.rden_holeAt`).

**L3, model side, done (2026-10-04).**  `ModalSys.shaped := T || BStrong` gates the shape:
`Model.posFull`'s second component, `Model.shape`, `pos_inj`, `shape_posMap`/`shape_posStrength`,
and on the soundness side every lemma that reaches tags only to compare shapes (`domSh`,
`envShape`, `domSh_interp`, `Env.CollapseAgree.shape`, `Env.ShiftAgree.shape`, `envShape_substEnv`,
…).  Where T is used as T — `extract`'s collapse and `Leaf.collapse`, which read a family at the
identity arrow — `hT` stays, and nothing needed `shaped_of_T`: every T-rule's shape argument already
went through the gate-agnostic lemmas.  Both canonical models keep their stored tags gated by T
(`RPos.tag`) and convert at the instance, `shaped ↔ T` holding there (`ModalSys.NoB.T_of_shaped`,
`ModalSys.NoFour.T_of_shaped`, the latter through the temporary `noBStrong`).  **Moved to L4:** the
network's tags gated by `shaped` and built without T — the T-free leaf decoder (typed `arrowIdx`
injectivity, `imgInj`, the network successor).  It is only needed once the network admits strong B,
and it removes `NoFour.T_of_shaped` together with `noBStrong`.

### 11.16 ⭐The negative `Back` atom at `◇`-typed contents: `Ind` attested, not generated *(2026-10-04, user + paper)*

**The gap in §11.12's decision 1.**  Canonical `Ind` generated by the atoms (co-naming through
`Here`, co-returning through `Back`) was to make the negative atom automatic: a carrier `u` with no
constant round trip has fresh return roots `c_k` at its children, "related to `t` by no atom".  Not
so, as decision 1 stated it.  The home theory is maximal, so it decides `Here y c_k` for a witness `y`
of `t` (strong T gives one) and may say yes at every child; elimination with a carrier can even force
such a link.  Without T, the same through co-returning (`Back u'_k c_k`, `Back u'_k t`).  Then every
return is linked to `t`, the model says `Back u t`, the theory `¬Back u t`.

**Withdrawn: an object-level `z ≈ z'`** (`Ind` as a formula, reflexive and substitutive, with a
`◇`-type `back_def` built on it).  *User's objection, accepted:* reflexivity plus substitution is
Leibniz equality, so `≈` is the cross-witness equality §10.3 rejected; comparing two `◇`-terms over
different witnesses needs comparing their bodies in *different* inner contexts, which is only
meaningful along a map from one to the other — such as the arrow a `Back` atom goes along.

**The diagnosis that follows from it.**  Each atom already carries its map: `Here x c` relates `x`'s
content here to `c` through `x`'s view at the own arrow; `Back u c` relates each return of `u` to
`c` through the round trip.  The counterexample linked `c_k` to `t` through a **middle object** — two
links composed, which is exactly comparing `c_k` with `t` with no map between their inner contexts.
The error was making canonical `Ind` an *equivalence*: its transitivity smuggled the cross-witness
comparison back in.

**Decision (user, 2026-10-04): canonical `Ind` is what a single atom attests.**  No new formula, no
new rule.  `Ind o o'` holds in the network model when
* `o = o'` (reflexivity), or
* `o` is a realised witness's content here and `o'` the value of `c`, with `Here x c` in the theory, or
* `o` is a return (along some arrow and its way home) of the carrier denoted by `u`, and `o'` the
  value of `c`, with `Back u c` in the theory (the returns computed in the frame, so a carrier term
  and any other term denoting the same carrier attest alike),
* closed under L1's congruences (hole terms, pairing), which soundness uses.

Not symmetric, not transitive — and nothing asks it to be: a model proper asks reflexivity,
invariance and the two congruences.  `IndInvariant` holds because each attesting atom yields
interchangeability in the theory (`here_subst`, `back_fun`); interchangeability is transitive, but it
is a relation of *formulas*, not of objects.

**The truth lemma.**
* *`Back`, positive:* a carrier with a value is committed at birth to its root `t₀`; `Back u t` in
  the theory attests every return of `u` to `t`.
* *`Back`, negative:* a carrier with no value returns a **fresh root** at each child, and no single
  atom mentions that root with `t`.  The construction adds **one fresh child per negative atom**
  (`¬Back u t` with `◇⊤`; with `◇_y⊤` for row 2), so a return that is not `t` always exists — a
  network with one child would otherwise make `Back u c₁` true of its only return.
* *`Here`:* attested by `Here` directly; attested by `Back` (the content is a returned `t₀`) gives
  `t₀` and `t` interchangeable (`back_fun`), then `here_subst`; attested through a congruence, the
  hole term carries interchangeability (`Interch.holeAt`, `Interch.pair`).

**Risks, scoped (paper, 2026-10-04).**
1. **Distinct roots must be distinct objects** — the hinge.  It needs L3 (shapes under `T ∨ strong
   B`: two fresh `◇`-roots with empty extents are otherwise one object, `posFull_inj`) and injective
   commitments (`imgInj`).  L3 is wide (every lemma reaching tags through `hT`) and needs a T-free
   leaf decoder (§11.12); this is the largest single risk.
2. **`◇`-free components are not automatic.**  At a `◇`-free type `Ind` to a named object is
   equality, and the theory may prove the fresh child's return equal to `t`.  There the negative
   atom still needs `back_def`'s separating child (§11.5 (3)).  Mixed types (`D × ◇E`) are covered by
   the `◇` component's freshness alone; a purely `◇`-free content by `back_def`.  Two mechanisms, to
   be kept straight in the construction.
3. **The congruence closure must not reach fresh roots.**  A closed hole term of `◇`-type builds its
   possible objects over the *slot's* witness, so `h(a)` carries `a`'s root, never a fresh `c_k` —
   checked on paper for `◇`-typed results; `◇`-free results are risk 2.
4. **Carriers sharing images.**  Two carriers whose images coincide at one child share that child's
   return, and a `Back` atom about one then attests it; harmless because the fresh child of the
   negative atom keeps distinct variables apart (distinct by risk 1).  To re-check against commit at
   birth when one carrier has a value and the other not.
5. **T's proofs on the network change their `Ind`.**  `BCanonModel` and `BHere` use
   `DTerm.Rel.trans` and `rel_lift` (stage lifting, representative independence); with attested `Ind`
   these become existential over representatives and stages.  Rework, not redesign; the tree keeps
   `Ind := DTerm.Rel` (no strong B there).
6. **`exW` need not give fresh roots** (`BWorld.exW` returns any declared root witnessing `∃`), so
   commit-at-birth values may be old roots.  Harmless for positive atoms (one root for all children);
   for injectivity only back-images of carriers *without* a value must be fresh — the realisation step
   already makes them so.

**L2 done (2026-10-05).**  On the network, `BData.Ind o o'` says that `o` and `o'` have
representatives related by `BData.Att`, an inductive relation on `DTerm`s with four constructors:
`refl`; `here` (a `Here x c` atom relates `x`'s realisation `realTerm`, read at the stage above
both, to `c`); `holeAt`; and `pair`.  The old relation is kept as `IndRel` (related
representatives, the tree's `Canon.Ind`).  `Att.rel` shows that attested representatives are
interchangeable: `here` by co-naming with the realisation (`mem_here_real`, `rel_of_coname`), the
congruences by `DTerm.Rel.holeAt`/`pair`.  So `indInvariant`'s `inv` goes through `Ind.rel` and the
old proof, and `map`/`pair` hold by construction.  Risk 5 turned out smaller than scoped:
* `posRet_exists_canon` uses `Att.here` directly, on `retW`'s atom (no `Rel.trans`, no stage
  lifting);
* `here_truth` takes membership to truth by `Att.here`, and truth to membership through `Att.rel`
  (the old argument).

The tree is unchanged.  **Left for L4:** a `back` constructor (a `Back u c` atom attests every
return of `u`'s carrier and `c`), with `Att.rel` from `back_fun`.
