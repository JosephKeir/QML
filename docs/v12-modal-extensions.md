# QML v12: modal extensions (design)

Status: design pass, 2026-09-13. **Weak T is implemented** (soundness and completeness, files
`QML/QML_v12m_*.lean`, namespace `V12M`); everything else is design. Claims marked *(sketch)* come
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
- **Strong (inward, named): unit `A → ◇A` (`unitT`).**
  - New canonical form of `◇`-terms, `unitT t`, beside `diatm x _ t`. It needs a new annotation
    (`Ann.dia` currently records the witness address).
  - `eqRec` case: `unitT t = unitT s` is `eqRec A t s`. Mixed annotations are never compared.
  - **Collapse lives in substitution**: `◇_z φ [z ↦ unitT t] = φ [z.dia ↦ t, u.box ↦ u.here]` and
    `diatm z s [z ↦ unitT t] = unitT (s[z.dia ↦ t, …])`. `SubE` entries for `◇`-addresses become
    "address or unitT", and `WFF.subst` at `.dia z` collapses in the unitT case. This type-checks
    only because of weak T's context principle.
  - No new rule: the singleton principle is ordinary `∃`-intro/`∀`-elim at `unitT t`.
  - Semantics: `posUnit : Dom A w → Pos A w` with extent `{w}` and content the object.
  - `Proof.subst` needs `K_dia`/`dia_bot` cases that use T's `□`-elimination.
  - Rejected alternative: an existential rule `Φ⟨x := t⟩ ⊢ ∃x:◇A. Φ(x)` with positive `◇_x` only
    (extent *contains* `w`). It is complete-able only with a chain invariant and one Henkin constant
    per term, and it makes proofs non-modular.

### 4 (transitivity)
- Frame: `R(v) ⊆ R(w)` for `v ∈ R(w)`.
- **Weak (inward, named): restriction `Nec(w) → Nec(v)`.**
  - Context principle: `□`-items stay visible deeper; `Γ.boxIn` also contains `u : □A`.
  - Rule: `□φ ⊢ □□φ`.
  - Semantics: a restriction map with `necEval (restrict n v) s = necEval n s`.
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
  is only statable when 4's visibility is present. **Open without 4**; with 4 the link is
  `□(c.box = u.box)`.

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
