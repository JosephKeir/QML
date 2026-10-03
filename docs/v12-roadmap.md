# QML v12m: roadmap *(2026-10-03)*

This supersedes the "Order of work" and "START HERE" blocks of `v12-modal-extensions.md` §9, which
predate the semantic-annotation work (§10.23–10.41) and still describe the retired `◇`-equality
package.  Design detail stays in `v12-modal-extensions.md` (per axiom) and `v12-arrow-canonical.md`
(the network/arrow canonical model); this file only orders the work.

## Where things stand

| Flags | Sound | Complete | Canonical model |
|---|---|---|---|
| K, T (weak, strong), D (weak, strong), 4 (weak), any combination without B | ✓ | ✓ (+ strong completeness, compactness) | the tree (`Canon.*`) |
| weak B with any of T, D (both strengths), without 4 (`NoFour`) | ✓ | ✓ (+ strong completeness, compactness; every presented context) | the network (`BArrow.*`) |
| B with 4, S5 | ✓ | **open** | — |
| strong B, 5, 4's open maps | not yet stated | — | — |

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
Henkin witnessing), and `back_joint` reduces to `back_pair`.  **Next:** an implementation plan,
rows 1–2 and `◇`-free contents first.

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
