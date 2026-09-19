# QML v12: an arrow-based canonical model (design draft)

Status: 2026-09-19. **Design only — nothing here is implemented.** It is meant to be settled on
paper before any Lean is written. Motivation: B and 5, for which the current staged canonical model
cannot work. Background on the flags is in `v12-modal-extensions.md` (§2a/§2b for the criteria,
§3 B for the rules).

## 1. Why the staged construction cannot give B or 5

The current canonical model (`QML_v12m_Canon*`) is a **Henkin tree**. A child world is built after
its parent, from the parent's necessary truths; its context is literally the parent's `□` view
(or `◇_x` view) plus fresh constants of its own. Accessibility is a chain of such steps, of length
0 only under T and of length at least 2 only under 4. Both T and 4 point *with* the order of
construction: the world itself, or worlds further down.

- **B** makes the parent accessible from the child — *against* the order of construction. Every
  modal object of the child then has a value at the parent: its necessary objects (inherited or
  born there, and compound ones), and its possible objects whose extent can reach the parent. The
  frame puts these values in the parent's domain (`necEval` lands in `Dom A w`), so in the canonical
  model each must be the denotation of a parent term — one term realising the whole **type** of the
  value, i.e. every `χ` with `□χ(c.box)` in the child's theory. That type is fixed by the child's
  freely extended theory, built after the parent was complete. Only the child's *base* objects
  escape: with varying domains they need not exist at the parent.
- **5** needs arrows between *siblings*, whose contexts were both built from the parent's view and
  not from each other's.

**How the classical cases avoid this.** Propositional B has no objects, and its canonical model has
every maximal consistent set as a world with accessibility defined between theories; symmetry is
then a two-line consequence of the axiom (if `w R v`, `□φ ∈ v` and `φ ∉ w`, then `¬φ ∈ w`, so
`□◇¬φ ∈ w`, so `◇¬φ ∈ v`). Classical quantified B pays with **constant domains**: B together with
the converse Barcan formula yields the Barcan formula, and the canonical construction uses one
language for every world. Our semantics keeps domains varying under B — necessary objects tie the
domains together without equating them, and our converse Barcan formula is concept-quantified, so
the classical derivation of the Barcan formula does not go through — so neither route is open.

## 2. Arrows carry translations, and translations are substitutions

Names are local: each world's environment (its context) carries its own. What a successor must
supply is, for each `□A`-item of the source's environment, an item of type `A` in its own. That is
exactly a **substitution** in the existing sense:

```
θ : Subst σ Γ_v      with      Subst.Ok (Γ_w.boxIn) θ,   Subst.Coh ι (Γ_w.boxIn) θ
```

An **arrow** `w → v` is a target world together with such a `θ`, subject to **necessity transfer**:

```
□ψ ∈ T_w   ⟹   WFF.subst θ ψ ∈ T_v          (ψ in the □ view of w's context at some stage)
```

A **witness arrow** for `◇_x` is the same with the source `Γ_w.diaIn x`: `x.dia` goes to a content
term, the `□`-entries as for a `□`-arrow — the shape of `Subst.dia`.

Most of the arrow algebra already exists:

| | as a substitution | existing machinery |
|---|---|---|
| the tree's child steps | `θ = idS`: the homophonic translation | `Subst.idS`, `WFF.subst_id` |
| T's self-arrow | `u.box ↦ u.here`, `u.keep ↦ u` | `Ctx.Collapses`; see §8 on stating collapse as a `Subst` |
| 4's composite arrows | `θ₁` then `θ₂` | `Subst.comp`, `WFF.subst_comp` |
| action on environments | assigns each `u.box` its value at the target | `Env.boxPush` |

So the present construction becomes the special case in which every arrow is the identity
substitution, and agreement lemmas like `boxPush_agree_canon` should hold by definition of an
arrow's `θ`.

## 3. Worlds

A world keeps what a world has now — a world language (a context at each stage), a maximal
consistent theory, and its Henkin witnesses (`exW`, `allW`), and under strong T its named
realisations (`real`) — but loses everything that places it in a tree: its depth, the naming of its
constants by depth (`hρ`, `hfresh` in their current form), its parent. **Stages stay within a
world** (the Henkin construction needs them); **there are no stages between worlds**. The canonical
`W` is
the type of all such worlds, or of those with some saturation property if one is needed (§6).

## 4. The frame, indexed by arrows

`Frame.Acc w` becomes a type of arrows with a target, instead of the subtype `{v // R w v}`.
`NecSec` and `PosSec` are already functions on `Acc w`, so sections are reindexed, not reshaped;
extents become sets of arrows.

Frame conditions per flag. T and 4 need their arrows as **operations**, because their evaluation
laws name a particular arrow (`necExtract_eval` evaluates at `⟨w, frame.refl hT w⟩`, `necDup_eval`
at `⟨s.1, frame.trans hF v.2 s.2⟩`); the others need only existence:

| Flag | condition | kind |
|---|---|---|
| T | an identity arrow `idA w : w → w` | operation |
| 4 | a composite `a ≫ b : w → s` for `a : w → v`, `b : v → s` | operation |
| D | some arrow out of every world | existence |
| B | for each `a : w → v`, some arrow `v → w` | existence (coherence: §6) |
| 5 | for `a : w → v` and `b : w → s`, some arrow `v → s` | existence |

No category laws are imposed unless a soundness proof turns out to need one.

**⚠ This changes the class of models.** A relational frame is the special case with at most one
arrow per pair, so every current model is still a model and soundness should survive the
reindexing. But completeness would then be proved relative to arrow-frames, a *weaker* result than
relative to relational frames unless every arrow-model we need can be turned into a relational
one. Quantified modal logics complete for functor semantics but not for Kripke semantics are known
to exist (Ghilardi), so this has to be checked, not assumed.

**Turning an arrow-model into a relational one (2026-09-19, paper).** Copy worlds, and let each
relational edge take its values from one arrow; a copy then behaves exactly like the world it
copies, and "copies the same world" is a bisimulation, objects included, so truth is preserved.
What matters is how copies are indexed and how the frame conditions are restored.

- *One copy per arrow (the line graph) fails for 4, even with category laws.* For `b, b' : w → v`
  and `c : v → s`, transitivity demands a single edge from `w` to the copy for `c`, whose values
  would come from `b ≫ c` along one route and from `b' ≫ c` along the other — legitimately
  different arrows.
- *One copy per path (unravelling) fixes this*: `w·b·c` and `w·b'·c` are distinct, and a path
  determines its composite. Unravelling alone gives a tree, with no loops, transitivity or back
  edges, but they can be **restored by closure**, each added edge taking its values from an actual
  arrow: a loop `p → p` along the identity (T); `p → q` for every extension `q`, along the
  composite of the extension (4); a back edge `p·b → p` along a chosen reverse `b⁻` (B). An added
  edge duplicates a successor the arrow model already has, with the same values, so the
  bisimulation survives.
- *The one failure left*: two different routes in the closed frame reaching the same pair of
  copies through different composite arrows, so that one edge would need two values. When that
  happens depends on the flags:

  | Flags | conflicting routes | law needed (up to values) |
  |---|---|---|
  | T, D or B alone | none | none |
  | 4 | different bracketings of one path | associativity |
  | T + 4 | `p → p → p·c` against `p → p·c` | identity: `id ≫ c` gives `c`'s values |
  | B + 4, S5 | out along `a` and back along `a⁻`, against out along `c` and back along `c⁻`, both landing on `p` | round trips agree: every `a ≫ a⁻` gives the same value — `w`'s own, or the identity arrow's under T |

  "Up to values" means the two routes must give every object equal values, not literally be the
  same arrow.

So relationalising needs **no laws for T, D or B individually**, and **coherence laws exactly where
4 meets T, B or 5**. For the canonical model, associativity and identity look unproblematic:
composition is `subst_comp`, already stated up to `Sim`, and the identity is `idS` (or the collapse
under T). **Round trips are the real constraint**: every back-translation `a⁻` sends `u.box` to some
`w`-term, and coherence demands that every round trip `a ≫ a⁻` return the *same* object for `u`,
namely `u`'s value at `w`. Back-translations built independently for each successor will not do
that on their own, so the back-and-forth construction of §6 would have to make them agree across
all successors of `w`. That is **open question 1** (§8), and it ties it to open question 2:
plausibly exactly the extra difficulty S5 has over B. If the laws cannot be met, adopting arrows
for those combinations is a decision about the intended semantics, not only about the proof.

## 5. The canonical model on arrows

- **Canonical arrows** `w → v`: pairs `(v, θ)` with `θ` ok, coherent and satisfying necessity
  transfer; witness arrows likewise.
- **Canonical necessary objects** evaluate along an arrow by translation: the value of `u` at
  `(v, θ)` is the denotation at `v` of `θ(u.box)`, so `rden`'s `□` clause is reindexed by arrows
  rather than split by depth.
- **The truth lemma's `□` case.** One direction is necessity transfer together with the induction
  hypothesis. The other is an **existence lemma**: if `□φ` fails at `w`, there is an arrow
  `(v, θ)` with `¬φ[θ] ∈ T_v`. With `θ` the inclusion of `w`'s `□` view, this is today's
  `exists_box_fail`, unchanged.
- **T**: the identity arrow is `(w, collapse)`, so strong T's self-successor stops being a depth-0
  special case of `rden`, `extent` and the truth lemma. Whether that simplifies the strong-T
  machinery (`realisedTerm`, the stage-first measure) is worth checking before anything is built.
- **4**: composite arrows compose their substitutions (`subst_comp`); `interp_box_far`'s induction
  on distance should become unnecessary.

## 6. B in this setting

**Symmetry** asks that every canonical arrow `(v, θ) : w → v` have a reverse `(w, θ') : v → w`:

```
θ' : Subst σ Γ_w     with     Subst.Ok (Γ_v.boxIn) θ',    □χ ∈ T_v ⟹ WFF.subst θ' χ ∈ T_w
```

`θ'` sends each of `v`'s `□`-items to a term of `w`: the back-translation.

**⭐Finite-piece lemma — weak B suffices (checked on paper, not in Lean).** Take finitely many of
`v`'s `□`-items `c⃗` and one `χ` with `□χ(c⃗.box) ∈ T_v`. Then some `w`-terms `t⃗` satisfy
`χ(t⃗) ∈ T_w`.

1. `v`'s `□` view contains none of `v`'s base items, and `w`'s items appear in it only through
   their round trips, which are themselves among the `c⃗`. So `χ` is **closed apart from the
   `c⃗`**.
2. By `∃`-introduction at `v`, the closed formula `∃y⃗:□A⃗. □χ(y⃗.box)` is in `T_v`.
3. A closed formula is in every `□` view, and the contrapositive of necessity transfer gives
   `◇∃y⃗. □χ(y⃗.box) ∈ T_w`.
4. The outward B rule — a theorem of propositional B for formulas closed apart from their hole —
   gives `∃x⃗. χ(x⃗) ∈ T_w`, and `w`'s Henkin witnesses are the `t⃗`.

So no new *logical* principle is needed for any finite piece. It is small, and it is the evidence
that weak B alone might suffice, so it is the first thing to check in Lean.

**The whole type.** `θ'` fixes one term for each of `v`'s `□`-items, respecting every `χ` at once.
The type may have as many variables as `v` has `□`-items — at least as many as `w` has, since `θ`
is total on `w`'s `□` view.

- *Rejected: saturated worlds.* Asking every world to realise all such types needs models saturated
  in their own cardinality, with set-theoretic side conditions. Not something to formalise.
- *Proposed: build the successor together with its reverse* (back-and-forth). When the existence
  lemma builds `v`, it chooses each new `□`-item's back-image in `w` at the step that introduces
  the item, and makes only decisions at `v` consistent with the back-images chosen so far. The
  finite-piece lemma gives consistency for a single new item.

**Open question 2: the back-and-forth invariant.** State an invariant, about the finite part of
`v`'s theory built so far together with its back-images, that holds at the start, survives every
Lindenbaum and Henkin decision at `v`, and implies the reverse arrow in the limit — using weak B
alone. *Suspicion, not established:* stating it needs a way for `v` to refer to "back at the
origin", since `v`'s theory has to be constrained by facts about the back-images, which are `w`'s
base terms and out of scope at `v`. That is exactly what the dropped singleton design provided.
Strong B in its necessary-object form, `P(a) ⊢ ∃u:□□A. □◇P(u.box.box)`, carries `w`'s terms out as
round trips, but only reaching *some* successor of `v`, not the origin in particular. If the
suspicion is right, B needs an origin-pinning device, or a necessary-object strong B that pins its
successor, and weak B is complete only in a bundle.

**Coherence of reverse arrows.** Weak B's soundness needs only that a reverse exists, and so does
relationalising B alone (§4). Once B meets 4, relationalising needs every round trip `a ≫ a⁻` to
give the same values (§4, open question 1), so the back-and-forth construction must choose the
reverse arrows of *all* successors of `w` coherently, not one successor at a time.

## 7. What carries over, and what it costs

- **Kept:** the syntax, the proof system, the substitution library (it becomes the arrow algebra),
  the Henkin and Lindenbaum constructions within a world, `rden` (reindexed), and the truth lemma's
  skeleton.
- **Replaced:** depth and `childStage`; `Succ`, `Chain`, `R` and `extent` as depth-indexed notions;
  `boxWorld` and `diaWorld` (they become existence lemmas that produce arrows); the depth-0 special
  case for strong T; `interp_box_far`.
- **Staging the migration.** T, D and 4 are complete under the tree and could keep it, with arrows
  used only for the B and 5 systems. Or arrows replace the tree everywhere, if §5 shows them to be
  simpler. The first option leaves two canonical models to maintain, and the second risks the
  model-class change of §4 for systems that do not need it.

**Early checks, before any rebuild:**

1. The finite-piece lemma (§6), in the current Lean, as a statement about two theories and a
   substitution.
2. Collapse as a substitution: `WFF.collapse` for `Ctx.collapses_boxIn_self` equal to
   `WFF.subst` along `u.box ↦ u.here`, `u.keep ↦ u` (T's identity arrow).
3. A throwaway arrow-indexed `Frame`, to see how much of `Soundness` survives the reindexing
   unchanged.

## 8. Open questions

1. **Round-trip coherence.** Relationalising the canonical arrow model needs no laws for T, D or B
   alone, associativity and identity (which look unproblematic) where 4 meets T, and — the real
   constraint — agreement of all round trips `a ≫ a⁻` where 4 meets B or 5. Can the reverse
   arrows be built so that every round trip returns each necessary object's value at `w`? If not,
   completeness for those combinations holds only over arrow-frames. (§4)
2. The back-and-forth invariant for B's reverse arrows, with weak B alone. For B + 4 and S5 it must
   also give question 1's agreement across all successors of `w`. (§6)
3. 5's arrows between siblings: the same back-and-forth question with a different target, `v → s`
   for siblings `v`, `s`.
4. Whether any coherence beyond question 1's is needed for soundness or for strong B. (§6)
5. Whether the arrow model simplifies strong T enough to migrate T, D and 4 as well. (§5, §7)
