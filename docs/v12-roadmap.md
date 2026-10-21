# QML v12m: roadmap *(2026-10-03; status table 2026-10-18)*

This supersedes the "Order of work" and "START HERE" blocks of `v12-modal-extensions.md` §9, which
predate the semantic-annotation work (§10.23–10.41) and still describe the retired `◇`-equality
package.  Design detail stays in `v12-modal-extensions.md` (per axiom) and `v12-arrow-canonical.md`
(the network/arrow canonical model); this file only orders the work.

## Where things stand

| Flags | Sound | Complete | Canonical model |
|---|---|---|---|
| K, T (weak, strong), D (weak, strong), 4 (weak), any combination without B | ✓ | ✓ (+ strong completeness, compactness) | the tree (`Canon.*`) |
| weak B with any of T, D (both strengths), without 4 (`NoFour`) | ✓ | ✓ (+ strong completeness, compactness; every presented context) | the network (`BArrow.*`) |
| strong B, rows 1–2 (carriers `□□A`, `◇_y□A`), with T and D in either strength, 4 off | ✓ | ✓ (+ strong completeness, compactness; every presented context; T added 2026-10-20, `v12-modal-extensions.md` §11.21) | the network, strong chain (`bdataS`) |
| strong B, rows 3–4 (carriers `□◇A`, `◇◇A`) | not yet stated | — (§11.23: decided, paper-checked; row 3 under way: flag `BStrongW`, two-leg `Back`, named back witnesses in the returning possibility and its rules (stages 1–2); next the row-3 counit rules (stage 3), then the network) | — |
| B with 4, S5 | ✓ | **open** | — |
| 5, 4's open maps | not yet stated | — | — |

`here_beta` stays general: §10.18 is decided (keep).

T is finished (§10.41): every component is sound and complete at every content type.

## The two canonical models

Everything ahead turns on this.  The **tree** (`QML_v12m_Canon*`) is staged by depth; successors are
worlds one deeper, and a successor sees `u.box` at an address (`succAddr`).  The **network**
(`QML_v12m_B*`) is a fair ω-chain of worlds whose languages are root-only (`ctxOf l`); an arrow is a
renaming of roots (`img`, `stg`), and pushing the canonical environment along an arrow is reading
the target's canonical environment through a substitution (`boxPush_canon`).  The tree cannot do B
(no route back); the network now does weak T too (milestone 1).

## Milestone 1 — B with T (KTB)  ← next

**Why weak T is not the cheap half.**  `WFF.here` and all six `Here` rules are gated by weak T alone
(`hT : ModalSys.T = true`); only `T_dia` needs `TStrong`.  So the network model has to host the whole
`Here` layer even for weak T — extents containing the identity arrow, realisation read off the
theory, shape tags, `Ind`, models proper.  Strong T then adds one thing: the chain's term query
(`World.retW`).  Weak and strong T with B are therefore one milestone in two steps, and most of the
cost is in the first.

**1a. Scoping — done** (`v12-arrow-canonical.md` §9, 2026-10-03).  Findings:
* the `□` case at the identity arrow is easy (`sat_boxHere`; collapse need not be a substitution);
* **the real new work is syntactic**: under T, `u.here` is a projection, so a root-only box view
  contains `r.here.q.box` too, and `VarType.bc`/`arrowS`/`arrowIdx` need a T-aware form
  (`bc(□A) = A × bc(A)`) across the B syntax layer;
* `Here` layer: **share** the theory level (restate over `StageSys`, adapter for `BWorld`),
  **port** the model level (`rden`'s `◇` clause, shapes by arrow images, a decoder that inverts
  arrows — needs a new `imgInj` from the construction); no migration.

**1b. Weak T + B**, in the order of `v12-arrow-canonical.md` §9.4:
1. ✅ **Syntax** (2026-10-03, `v12-arrow-canonical.md` §9.5): T-aware `bc` (`bcB`), `itemAt`, `here`
   in projection paths; everything up to `BData` now needs only 4 off (`ModalSys.NoFour`).
   `imgInj` moves to step 4.
2. ✅ **Theory-level `Here` layer over `StageSys`** (2026-10-03, `v12-arrow-canonical.md` §9.6):
   shared by both models; `BWorld` adapter (`QML_v12m_BStaged`), root-form `BWorld.exW`.
3. ✅ **Model, below the instance** (2026-10-03, `v12-arrow-canonical.md` §9.7): own arrows (`RT`,
   `irrefl`), extents with the own arrow, `rden` and `extract` there, the frame.  The `□` case moves
   to step 4: the `Model` instance needs shapes under T.
4. ✅ **Shapes on the network** — 4a ✅ (§9.8: shape layer, tags, `Model` instance under weak T);
   4b ✅ (§9.9: canonical environment and `interp_canon` under weak T); 4c ✅ (2026-10-03, §9.10:
   leaves by arrow images under exact levels, decoding by the own arrow and a network arrow
   together — no `imgInj` needed — tags determine annotations; `Ind := Rel`; the truth lemma's
   `□`/`◇` (own arrow) and `here` cases; canonical `IndInvariant`).  The truth lemma and models
   proper now hold under `NoFourNoTS`.
5. ✅ **Statements** (2026-10-03, `v12-arrow-canonical.md` §9.11): `NoFourNoTS` (4 off, strong T
   off) replaces `NoTFour`, which is gone; completeness, strong completeness, compactness, every
   presented context.  Nothing beyond the flag class had to change.

**1c. ✅ Strong T + B** (2026-10-03, `v12-arrow-canonical.md` §9.12).  No new operation: strong T's
existential `∃y:◇A. Here y t` is a theorem (`Proof.retEx`, by `T_dia` and `∃`-introduction), so the
network's Henkin witnessing gives `retW`; `posRet_exists` then as in §10.41.  The flag class is
just `NoFour`.

**Milestone 1 is done.**

*Done when:* completeness, strong completeness and compactness for every 4-free flag set
(K, T, D, B, both strengths of T and D).

## Milestone 2 — strong B

Next while B is in mind (user, 2026-10-03), and the closest relative of what milestone 1 builds.
The design is decided: **relational**, a predicate `Back u t` — "some round trip returns `u` to
`t`" — with the forced ∀-out/∃-back pairing (`v12-modal-extensions.md` §9, decision of
2026-09-25).  What `Here` taught that should carry over:
* *a predicate, not an equation*: the returned value has no canonical name, exactly as `Here`'s
  content has none — so read it up to indistinguishability (`Ind`), not identity (§10.23, §10.33);
* *atoms in the theory*: if `∃t. Back u t` (or its analogue) is valid but not derivable, the chain
  must add the atom, as it does `Here` for strong T (`Model.sat_here_ex`, `World.retW`), and the
  canonical model reads the datum off the atom (`realised_of_here`);
* *rules about the predicate, not computations*: elimination/introduction across two readings, a
  β-like commutation with hole-filling, and Leibniz for its content (`here_eq`), each checked for
  closure under `Proof.subst` from the start (§10.11);
* *shapes*: whether the frame condition needs shape tags, as `Here` did, is the first thing to check.

Start by writing the frame condition and the rules, then check them against the model's β-laws
before building on them (the lesson of §10.10).

**Design pass done (2026-10-03, `v12-modal-extensions.md` §11):** all four witnessed/unwitnessed
rows as one leg-parameterised predicate; `Back` asserts its out leg is nonempty (so functionality is
unconditional and surjectivity takes `◇⊤`); unique return arrows (relational frames) for
functionality.

**Decided (2026-10-03, `v12-modal-extensions.md` §11.9): the hybrid.**  Relational atoms (`Here`,
`Back`) where both ends of a route can be named at the origin; ∃-elimination rules, with no
positivity condition, for objects born elsewhere — strong B's `B_ret` for a child's items coming
home, and later 4's lift and 5's carrier principle.  T stays relational.  `B_ret` checked on paper
(§11.10): sound on relational frames, closed under substitution, derives `P`, and the canonical
construction goes through in outline (extended back-transfer, commit at birth).  The remaining
paper items are settled in §11.11: the home reading by item kind (`B_ret` needs a witnessed,
leg-parameterised form), the own arrow under T (collapse plus `back_here`), `back_fun` derived from
`back_joint`.  **`◇`-typed contents** (§11.12, decided with the user): first build `◇`-free; then lift
by making canonical `Ind` the equivalence generated by the atoms (`Here` co-naming, `Back`
co-returning) and gating shapes by `T ∨ strong B` instead of T, with a T-free leaf decoder (typed
`arrowIdx` injectivity, `imgInj`).

**Revised (2026-10-03, §11.14): the returning possibility replaces `B_ret`.**  A formula former
`◇[d ↦ t] Φ(d)` — "possibly a necessary object `d` with `Φ(d)` whose content comes back here as
`t`" — with existence, elimination (with carriers), β, monotonicity, Leibniz and a T-rule.  Born items
are then relational too, so the dividing line is just *does the route return?*: all of T and strong
B relational, 4's lift and 5 existential.  Checked on paper: substitution, the canonical truth-lemma
case (the construction's invariant becomes an atom invariant, and committing a born item becomes
Henkin witnessing), and `back_joint` reduces to `back_pair`.

**Implementation plan (2026-10-03, draft).**  Scope of the first build: rows 1–2 (carriers `□□A` and
`◇□A`; out leg plain or witnessed), `◇`-free contents, frames with unique ways home.  Steps in the
style of milestone 1, each ending green and committed:
1. **Flags and frames.**  `ModalSys.BStrong` (requiring `B`); a frame law
   `homeUnique : BStrong = true → ∀ {v w}, Subsingleton (R v w)`.  Every existing canonical frame is
   relational (`Prop`-valued), so the law holds by `Subsingleton` of proofs; soundness of existing
   rules does not use it.
2. **Syntax.**  Two `WFF` constructors, gated by `BStrong` as `here` is by T:
   `back (L : Leg) (s : Term σ Γ (L.carrier A) b) (t : Term σ Γ A a)` and
   `ret (L : Leg) (t : Term σ Γ A a) (Φ : body in the out leg's view with d : □A bound)`, where `Leg`
   is an inductive with the plain and witnessed out legs (`nec`, `pos x`), to be extended with
   witnessed back legs for rows 3–4 without touching `WFF` again.  Content type restricted to
   `◇`-free in the constructors (lifted later, §11.12).  Then the mechanical ripple through every
   recursion on `WFF` (mono, subst, collapse, shift, size, instantiate, countability, decidable
   equality, …) — some thirty files, mirroring how `here` threads through them (§10.16).
   *Done (2026-10-03), as built:* `BLeg` is `nec | pos` with `BLeg.carrier` giving `□□A` or
   `◇□A` (the witnessed leg's witness is the carrier itself, so no variable in the leg); `ret` has
   no leg — it ranges over every successor, and the witnessed form comes from the bridging rule
   `Back x s, ◇_x Θ(x.dia) ⊢ ◇[d ↦ s] Θ(d)` (step 4).  `sat` is in already (`Model.Backs`), so step
   3 is the model law and the soundness lemmas.  `ModalSys.NoB` now also turns strong B off (it
   needs weak B), which dismisses both formers in the tree's truth lemma.  **Temporary:** B's
   network does not build strong B's worlds until step 5, so for now `ModalSys.NoFour` (which
   every B completeness theorem assumes) also turned strong B off (`noBStrong`); step 6 replaced
   it by `noTStrong` (strong B ⇒ T off).
3. **Semantics and soundness.**  `sat` clauses (`Back`: out leg nonempty, ∀ out ∃ home, `Ind`;
   `ret`: ∃ out, ∃ `d`, `Φ(d)`, home value `Ind t`); a `Model` field `backRet_exists` per row
   (surjectivity, after `Ind`); a `SemBack` file with one soundness lemma per rule, using
   `homeUnique` and `IndInvariant`.
   *Done (2026-10-03), as built:* **one** law, `Model.backRet_exists` (row 1, `◇`-free contents,
   given a way out); row 2's carriers come from row 1's by strength over a nonempty extent, so it
   has no field (to be checked when row 2's `B_strong` is stated in step 4).  `QML_v12m_SemBack`
   proves the rules at the level of values over a generic out leg (`Model.RoundTrip`), to which
   both rows' carriers unfold (`backs_nec_boxtm`, `backs_pos_diatm`): `ne`, `elim`, `intro`,
   `of_def` (weak B), `map` (β), `pair` (`homeUnique`), `own` (T), `ret_exists` (weak B),
   `ret_counit` (no carriers), and surjectivity at a fresh carrier (`sat_back_ex`).  Hole formulas
   are `WFF.holeRead` / `Model.holeSat`.  **No congruence law on `Ind` is needed:** in a model
   proper, `Ind` to a *named* object at a `◇`-free type is equality (`Model.eq_of_ind`, the slot
   formula `z = t`), so β, pairing and the own arrow are equations.  Left to step 4, where the
   syntax is fixed: the WFF-level forms of each lemma (the readings `◇□ψ⟨bd⟩`, the mapped and
   paired carriers, `u.here.here` by collapse), `back_eq` (immediate from `sat_eqRec`), and the
   returning possibility's extension form, carriers in elimination, β, monotonicity, Leibniz and
   T-rule.
4. **Proof rules.**  `back_counit`, `back_unit`, `back_ne`, `back_beta`, `back_eq`, `back_pair`,
   `back_here` (T), `back_def`, `B_strong` (∃-elimination per row, as `T_dia`); `ret_exists`
   (extension form), `ret_counit` (with carriers), `ret_beta`, `ret_mono`, `ret_eq`, `ret_here` (T);
   `Proof.subst` cases; soundness assembled.  `back_fun` as a derived rule.
   *`Back` half done (2026-10-04):* the nine `Back` rules are in `Proof`, with `Proof.subst` cases
   and soundness.  They are stated once over the out leg — `OutLeg` (`QML_v12m_BackSyntax`): `nec`
   or a witness `pos y`, with its view, `◇`/`□` (`OutLeg.dia`, `OutLeg.box`) and the atom of a
   carrier given by its body (`OutLeg.back`), all of which substitution acts on definitionally.
   Hole formulas and terms are `WFF.holeRead`, `Term.holeRead`.  `back_eq` is stated at any carrier
   term and leg; `back_here` concludes the equation `u.here.here = t` (two collapses, `◇`-free);
   `back_def` takes its definability premise as one formula `∀z. θ(z) → z = t`; `B_strong` is row 1
   only, with the premise `◇⊤`.
   *Returning-possibility half done (2026-10-04):* ten `ret_*` rules, with `Proof.subst` cases and
   soundness.  Design (a), chosen with the user: `ret` keeps its **single** binder `d : □A`, several
   items being one paired item, and two body substitutions move between forms — `WFF.bodyRepl`
   (the item becomes a term over a new one) and `WFF.bodySplit` (two items become the components
   `Term.boxFst`/`boxSnd` of one); hole readings inside a body use `WFF.holeAt`/`Term.holeAt`
   (any depth).  The rules: `ret_new` and `ret_ext` (existence, as `∃`-eliminations with a fresh
   value; `ret_ext` adds a companion item, its subproof's hypothesis a weakening so `Proof.subst`
   goes as for `T_dia`), `ret_counit`, `ret_back` (a carrier joins the item — with elimination and
   monotonicity this is elimination with carriers), `ret_mono`, `ret_dia`, `ret_beta`, `ret_eq`,
   `ret_here` (T) and `ret_bridge` (a `Back` atom plus a possibility, either out leg).  Each body
   substitution commutes with an outer substitution by `WFF.subst_comp` (`WFF.subst_bodyRepl`,
   `subst_bodySplit`).  **Not done:** `back_fun` as a derived rule (needed only in step 5).
   *Lifted to every content type (2026-10-04, `v12-modal-extensions.md` §11.15, phase L1):* step 5
   found that the network commits items with `◇`-typed contents, so the `◇`-free first build could
   not be finished; with the user's agreement strong B now works at every type.  A model proper
   gains two congruence laws on `Ind`; `back_here` is substitutional; `ret_back` became
   elimination with a carrier, `ret_counitC`; `back_def` stays `◇`-free.  L3's model side is done:
   shapes are gated by `ModalSys.shaped` (`T ∨ strong B`); the network's T-free leaf decoder moved
   to L4.  L2 is done: the network's `Ind` is attested by single atoms (`BData.Att`, §11.16),
   and the tree is unchanged.  Next: L4 (the network, step 5 proper, with `Att`'s `back`
   constructor and the T-free decoder).
5. **The canonical network.**  The hard step:
   * the **atom invariant** replaces the back arrows' necessity transfer (`Transfer` becomes a
     consequence), and committing a born item becomes Henkin witnessing of `ret_exists` (in `BLocal`,
     `BNet*`);
   * **commit at birth** for `Back`-carriers (`∃t. Back u t` decided at `u`'s stage, image the `exW`
     root);
   * a new network operation giving every `ret` atom a child, as `exX` does for `◇_x`, with fairness;
   * `backRet_exists_canon` by Henkin witnessing (as step 6 of milestone 1); `BTruth`'s `back` and
     `ret` cases; canonical `Ind` unchanged at `◇`-free types.

   *Status (2026-10-09), built for strong B **without T** (T is combined afterwards, §11.20):*
   L4a–e are done (`v12-modal-extensions.md` §11.17, §11.20).  The invariants (`RetInv`,
   `RetInvW`, `RetInvX`, `RetInvWD`; `RetData`, `GoodS`), the realisation steps, aliases, the four
   returning successors (`mkRet`, `mkRetX`, `mkRetD`, `mkRetXD`, with the K-laws `ret_K`, `retx_K`,
   `retD_K`, `retxD_K` derived; the fourth needed the rule `ret_unitWD`) and a kind on back arrows
   (`bkind`, content `bcx`) are in; the chain is `netS` with the fair schedule `schedS`
   (`QML_v12m_BNetS`: `goodS_netS`, `ext_netS`).  Commit at birth for `Back` carriers turned out
   unnecessary, and `back_def` was replaced by `back_ret` (user, 2026-10-09; `Back` as the definite
   description of `ret`).  **Decided (user, 2026-10-10, §11.20):** at `◇`-typed contents `Back`
   reads a model primitive `Ret` ("comes back as", keyed on round-trip data, laws in models
   proper), as `Ind` is; built (semantics, soundness, the rule `back_eqC`).  **L4f so far:**
   aliases persist (`packRoots`, `alias_interch`), canonical `Ind` = related representatives, the
   T-free decoder with injective images (`ImgInj`), the pair law on carriers' data, back-witness
   arrows in extents and the strong chain (`StrongChain`, E1 steps 1–2), and the fourth returning
   successor (§11.20), the returning invariants at the limit (E1 step 3, `lretAt`), and canonical
   `Ret` with its laws (step 4; `ret_counitC` now leg-indexed; `Ret_fwd` from `bdataS`'s
   `backRel`/`backRelX`, `QML_v12m_BBackTail`).  Step 5 begun: sizes, `back` membership ⇒ truth,
   `back` truth ⇒ membership on both legs at every content type (`QML_v12m_BBackTruth`,
   `QML_v12m_BBackLimit`; new `BData` field `unl`), plan in §11.20.
   `ret` truth ⇒ membership for all four forms (both legs, every shape;
   `QML_v12m_BRetTruth`, `QML_v12m_BRetTruthW`; `ret_eq` generalised to `ret_eqS`, and β on
   the possible part `ret_mapD` added after an audit of necessary vs possible parts, §11.20).
   `ret` membership ⇒ truth for all four forms (both legs, every shape; `QML_v12m_BRetOut`).
   The cases are wired into the truth lemma (`BData.StrongTruth`, `bdataS_strongTruth`), and
   the canonical `Ret` is a congruence (`BData.retCongr`, `bdataS_indInvariant`).  **Done.**
6. **Statements (done, 2026-10-11).**  `NoFour.noBStrong` is replaced by `noTStrong` (strong B ⇒
   T off, for now); `exists_canonB` picks the strong limit under strong B, so completeness
   (every presented context), strong completeness and compactness hold for strong B with T off,
   rows 1–2, at every content type.
7. **Strong B with T** (`v12-modal-extensions.md` §11.21, planned 2026-10-11).
   * *Back commitments under T*: a born root's `here` items must come back, coherently with the
     object.  An equation works only when `□` contents are `◇`-free.  In general: a new shape
     `boxT` (value = the whole image `bc(□A)`), an existence rule and a `ShapeMap` `packT`;
     the user decides.
   * *The own arrow in the truth cases*: products are derivable; witnessed shapes, the `◇_x` leg
     and `Back` row 2 are not.  Proposed: `ret_hereS` (every shape and leg) and `back_here` on
     the leg; the user decides.
   * *One name per leg under T*: resolved on paper (`here_intro` at `⊤`).
   * *Then*: flag-generic obligations, pull-backs and births; `hT` dropped from the network and
     the limit; `NoFour.noTStrong` removed.
   * **Done (2026-10-20).**  `NoFour` is 4 off only; `bdataS` takes no `hT`, and completeness,
     strong completeness and compactness hold for strong B with T.
Then rows 3–4 (multi-labelled edges, per-witness components) and `◇`-typed contents (§11.12).
**Main risks:** step 5's refactor of the back arrows (the invariant changes shape); step 2's ripple
is large but mechanical.

## Milestone 3 — B with 4, and S5 (5 itself)

The open question is **round-trip coherence** (`v12-arrow-canonical.md` §4, §8 q. 1): with 4 and B,
every out-and-back route through different successors must return the same value.  Conjecture:
coherence is the shadow of flag closure, supplied by 5's object-level component
`◇□χ(u.keep.box) ⊢ □χ(u.box)`.  So this milestone starts with **designing 5** (no flag, rules or
frame condition exist yet) and testing the conjecture; if coherence fails, these systems are
complete only over arrow frames, which is a decision about the intended semantics.  Strong B's
`Back` (milestone 2) is likely to be what states the coherence.

## Milestone 4 — the remaining strong forms, completing the cube

* **4's two open maps**: the witnessed join `◇_x ◇_y φ ⊢ ◇_z φ`, and the inward map `□□A → □A`
  (whose shadow is density, not 4).  Decide which earns the name `FourStrong` first.
* **D's** inward / graph form (low priority).

*Done when:* every flag combination of the cube (T, D, B, 4, 5, weak and strong) is sound and
complete, or the exceptions are understood and recorded.

## Afterwards — general metatheory (`v12-metatheory-todo.md`)

Generalisation on constants, uniform substitution, cut elimination (scope open beyond K), Craig
interpolation, `T_dia∀ ⇔` the positive-Φ rule.  Deferred until the cube is finished (user,
2026-10-03): each result should then be stated once, for every system.

## Small items, any time

* Named `◇`-duals of `T_box` and `four_box`; `Actual s := ∃a. Here s a`.
* Retire the K-only `QML_v12_*` files once nothing depends on them.
