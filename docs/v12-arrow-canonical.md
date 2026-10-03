# QML v12: an arrow-based canonical model (design draft)

Status: 2026-09-19. **Design; the construction itself is not implemented**, but the arrow-indexed
`Frame` of §4 is (with category laws for T+4 and 4). Early checks of its
key steps are in Lean (`QML_v12m_ArrowCheck`, and `realise_type` in `QML_v12m_Compactness`); the
rest is to be settled on paper before the construction is written. Motivation: B and 5, for which
the current staged canonical model cannot work. Background on the flags is in
`v12-modal-extensions.md` (§2a/§2b for the criteria, §3 B for the rules).

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
`W` is the type of all such worlds, or of those with some saturation property if one is needed (§6).

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

**Implemented (2026-09-19, `QML_v12m_Model`).** `Frame.R : W → W → Sort v` (a relational frame is
the `Prop` instance), `Acc w := Σ w', PLift (R w w')`, and `Frame.reflAcc hT w` names the identity
arrow. Soundness *did* need laws, exactly the category laws, and only where both flags are on:
`refl_trans`, `trans_refl` (T+4: `SemCollapse`'s `keepOnly` cases compose a `keep` with the
identity) and `trans_assoc` (4: `SemShift`'s `keep`–`keep` case). Strong T's `posRet_exists` now
places the possible object at the identity arrow rather than at an arbitrary loop `R w w` — with
several loops only the identity one is sound for `T_dia`. The canonical model is unchanged: its
`Succ` is now literally `Σ w', PLift (R w w')` and the laws hold by `rfl`. Soundness, completeness,
strong completeness and compactness all build sorry-free, axioms `propext`/`choice`/`Quot.sound`.

**⚠ This changes the class of models.** A relational frame is the special case with at most one
arrow per pair, so every current model is still a model and soundness should survive the
reindexing. But completeness would then be proved relative to arrow-frames, a *weaker* result than
relative to relational frames unless every arrow-model we need can be turned into a relational
one. Quantified modal logics complete for functor semantics but not for Kripke semantics are known
to exist (Ghilardi), so this has to be checked, not assumed.


**⚠ A principle that may separate the two classes (2026-09-25, paper).**  Everything checked so far
says arrow models and relational models validate the same sequents: soundness is
universe-polymorphic, the canonical model for weak B came out relational, and §6a's unravelling was
not needed.  But 4's `◇`-side map `◇◇A → ◇A` (`v12-modal-extensions.md` §3 4) is sound on arrow
frames and **not** on arbitrary relational ones: its extent is the set of composites, and where two
intermediate worlds reach the same world with different contents the value function is not well
defined, so — `posEval` being injective — no such object exists.  Arrow frames keep the composites
apart; relational frames need not.  If that flag is ever wanted, the unravelling argument above has to
be revisited, since the copies it makes are per path and so would validate the join while the frame it
came from does not.

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

**⭐Coherence is the shadow of flag closure (2026-09-19, paper).** Round-trip agreement has a
syntactic counterpart. For `u : □A` at `w` and successors `v₁`, `v₂` in a relational B+4 frame,
`w` is accessible from both, and `u.keep` at either is `u` restricted, so its value at `w` is
`u(w)` from both sides. Hence

```
¬(◇□χ(u.keep.box) ∧ ◇□¬χ(u.keep.box))      is valid on B+4 frames.
```

It is *not* derivable from closed B plus weak 4: it has a parameter, which closed B cannot reach,
and an arrow model with disagreeing round trips satisfies closed B and weak 4 but refutes it.
What derives it is

```
◇□χ(u.keep.box) ⊢ □χ(u.box)
```

— valid on B+4 frames, since they are euclidean (`R(w) ⊆ R(v)`) — which is **5's
"possibly necessary ⇒ necessary" half with a kept parameter**, the object-level component that
modal-extensions §4 records as "B + 4 ⇒ 5: propositional ✓, object level via closure". So the
conjecture: *round-trip coherence is what the canonical model needs exactly when the flag set must
be closed under that component, and with the component the logic supplies what makes successors
agree about `u`'s value at `w`.* Open question 1 becomes "does adding 5's object-level component
make the canonical round trips coherent?", which ties B + 4 and S5 to the design of 5.

**⭐Direction: construction changes, semantics does not (2026-09-19).** Of the three options —
(1) arrow semantics for B and 5; (2) arrow-style constructions unravelled into relational models,
so only the canonical model changes; (3) no arrows at all — the evidence points to **(2)**:

- *B alone:* no coherence law is needed, so if the construction of §6 goes through, its
  unravelling is an ordinary relational model and completeness holds for the present semantics.
- *B + 4, S5:* (2) if the coherence conjecture above holds; (1) is the fallback only if coherence
  fails even with the closure.
- *(3) in its strong form* — the present tree, identity translations only — is ruled out for B.
  One could build the unravelled relational model directly, each canonical world carrying the
  translation it was reached by, with no arrow semantics anywhere; that is (2) with translations as
  bookkeeping inside a relational construction, not a different option.

So `Frame` keeps a relational `R`, soundness is untouched, and the work is entirely in the
canonical model.

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

**⭐Finite-piece lemma — weak B suffices. Checked in Lean (2026-09-19):
`Canon.finite_piece_closed` and `Canon.finite_piece` in `QML_v12m_ArrowCheck.lean`.** If `v` is
accessible from `w`, and `v`'s theory has `□χ(s)` for a formula `χ` closed apart from its hole and
any term `s` of `v`'s `□` view, then some `w`-term `t` has `χ(t)` in `w`'s theory. Finitely many of
`v`'s `□`-items are covered by taking `s` to be their tuple.

1. At `v`, push `∃x` *inside* the `□`: `□χ(s)` gives `□∃x.χ(x)` (`K_box` on `ex_intro`), a closed
   formula.
2. At `w`, `◇□∃x.χ(x)`: otherwise `□¬□∃x.χ(x)`, whose body, being closed, holds at `v` and
   contradicts step 1.
3. Weak B, `◇□ψ ⊢ ψ` for closed `ψ`, gives `∃x.χ(x)` at `w`.
4. Its Henkin witness is `t` (`World.exW`).

This is shorter than the paper sketch recorded here before, which went through
`∃y⃗:□A⃗. □χ(y⃗.box)`: no quantifier over `□A` is needed.

Two observations from the Lean:

- **The translation plays no part.** The only formula that has to cross from `w` to `v` is closed,
  so the lemma needs only accessibility on closed formulas (`finite_piece_closed`). The arrow
  version follows because substitution fixes closed formulas (`WFF.subst_mono_empty`, via
  `subst_mono_eq` and `subst_id`). The finite pieces of a back-type are therefore *propositional*
  information, and the translation matters only for realising a whole type at once — which is
  where open questions 1 and 2 sit.
- **What it assumes.** Weak B enters as closure of `w`'s theory under `◇□ψ ⊢ ψ` for closed `ψ`,
  not as a rule, and accessibility at a single pair of stages. It is stated for a formula `χ`
  already closed apart from its hole. That every formula of `v`'s `□` view has this form — its
  finitely many free `□`-items abstracted into a tuple — is purely syntactic and is not formalised.

So no new *logical* principle is needed for any finite piece.

**The whole type.** `θ'` fixes one term for each of `v`'s `□`-items, respecting every `χ` at once.
The type may have as many variables as `v` has `□`-items — at least as many as `w` has, since `θ`
is total on `w`'s `□` view.

- *Rejected: saturated worlds.* Asking every world to realise all such types needs models saturated
  in their own cardinality, with set-theoretic side conditions. Not something to formalise.
- *Proposed: build the successor together with its reverse* (back-and-forth). When the existence
  lemma builds `v`, it chooses each new `□`-item's back-image in `w` at the step that introduces
  the item, and makes only decisions at `v` consistent with the back-images chosen so far. The
  finite-piece lemma gives consistency for a single new item.

**Open question 2: the back-and-forth invariant — proposed answer (2026-09-19; key step checked
in Lean).** The invariant:

> **every committed back-image realises its item's complete back-type in the item's own
> language** (`Canon.RealisesBackType`): every formula closed apart from its hole that `v`
> necessitates of the item holds of the image at `w`.

It is stated in the metatheory — as the arrow's data — not in the object language, which is why
no reference to "back at the origin" is needed.

- *Why it survives later decisions (fix-then-extend).* Suppose `c ↦ t_c` is committed and `v`
  later gains an item `c'` with `□χ(c.box, c'.box)`. `∃`-introduction inside the `□` gives
  `□∃y. χ(c.box, y)`, a formula about `c` alone. It was decided when `c` was introduced, because
  `v`'s theory was then complete for `c`'s language, so it is part of `c`'s back-type, and `t_c`
  realises it: `∃y. χ(t_c, y)` holds at `w`. Finite conjunctions likewise, so the type of `c'` over
  `t_c` is finitely satisfiable, and a fresh constant realises it. **Checked in Lean:**
  `Canon.backType_extend` in `QML_v12m_ArrowCheck.lean`. Weak B is not used in this step; it
  enters only in the base case, the finite-piece lemma.
- *The construction this suggests: an ω-chain in which every world grows together.* At each step:
  (1) realise the new back-types of each world's successors, over the images already committed,
  by fresh constants; (2) complete and Henkin-saturate each world; (3) extend forward arrows to any
  new `□`-items — the K direction, where the same closed-formula argument gives consistency. Each
  world's theory is a chain of complete theories in growing languages, and the limit is complete
  and saturated.
- *The realisation step — checked in Lean (2026-09-19):* `realise_type` in
  `QML_v12m_Compactness.lean`. If a consistent set derives `∃y. χ₁(y) ∧ … ∧ χₙ(y)` for every finite
  part of a type, it stays consistent when one fresh variable is made to satisfy the whole type. It
  is proof-theoretic — no completeness, countability or presented context — as it must be, since
  the construction applies it in the B system, whose completeness is what is being built.
- **⭐Every local obligation of the chain is now checked in Lean (2026-09-19):**

  | Obligation | What discharges it | Lean |
  |---|---|---|
  | a successor's new item needs a back-image at `w` | finite pieces | `finite_piece_closed`, `finite_piece` |
  | …compatible with back-images already fixed | `∃`-projection onto fixed items | `backType_extend` |
  | an arrow's images satisfy the forward invariant | substitution commutes with filling a hole | `arrow_realises` (`WFF.subst_fill1`) |
  | a new `□`-item of `w` needs an image in each successor, compatible with images already fixed | the mirror: `□ψ(old, new)` gives `□∃y.ψ(old, y)` | `forward_extend` |
  | one fresh variable realises a whole type | compactness, proof-theoretically | `realise_type` |

  `forward_extend` is `backType_extend` with the worlds swapped: `RealisesBackType` states "whatever
  one world necessitates of an item, the other says of its image", which covers both directions.
  Two things that could have hidden a problem check out on paper: *joint obligations* (a world
  realising types for several successors at once, while its own new constants create new forward
  obligations) use disjoint fresh constants, so their finite pieces combine by conjunction with no
  cross-constraint; and *the limit* — every formula of the limit language lives at a finite stage,
  so with a fair enumeration each arrow condition holds eventually, and a union of complete
  theories is complete. This is the **step-by-step method** of modal logic (Burgess, Gabbay;
  Blackburn–de Rijke–Venema §4.6), with languages that grow along the chain.
- *Not yet checked:* the chain's bookkeeping — the fair enumeration of obligations, and Lindenbaum
  relative to an existing theory. That is the construction itself, not something isolated lemmas
  can test. `WorldLang` already grows a world's language by stages through a Henkin chain, so one
  global enumeration of all obligations feeding every world's stages may be enough.
- *Superseded suspicion (to 2026-09-19):* that stating the invariant needs a way for `v` to refer
  to "back at the origin", and so an origin-pinning device or a necessary-object strong B that
  pins its successor, leaving weak B complete only in a bundle. That assumed the invariant had to
  be stated in the object language.

Round-trip coherence for B + 4 and S5 (open question 1) is not addressed: the chain chooses each
world's back-images independently.

**Coherence of reverse arrows.** Weak B's soundness needs only that a reverse exists, and so does
relationalising B alone (§4). Once B meets 4, relationalising needs every round trip `a ≫ a⁻` to
give the same values (§4, open question 1), so the back-and-forth construction must choose the
reverse arrows of *all* successors of `w` coherently, not one successor at a time.

## 6a. Implemented: weak B without T and 4 (2026-09-19)

**⭐`BArrow.completenessB` (`QML_v12m_BCompleteness`): with `ModalSys.B` and
`[ModalSys.NoTFour]` (T and 4 off; D and strong D free), a sequent in a context of declared
variables (`ctxOf l₀`, the root world's starting language) valid in every model is provable.**
Sorry-free; axioms `propext`, `Classical.choice`, `Quot.sound`. The files, in dependency order:

| File | Content |
|---|---|
| `BSyntax`, `BAbs` | worlds' contexts `ctxOf l` (own variables `free n` only); arrows as renamings of roots (`arrowS`: `r.q.box ↦ z_r.q`, `z_r : bc(type r)`), witness arrows (`arrowXS`, also `x.dia ↦ cx`); abstraction of finitely many items into a tuple |
| `BLocal`, `BChild`, `BDia` | the local steps: realising one more variable along an arrow keeps consistency (`realise_consistent`, `realiseX_consistent`); new children for failing `□φ` and true `◇_x φ` (`child_consistent`, `childX_consistent`); weak B enters only here, as closed transfer back to the parent (`closed_back`) |
| `BNet*`, `BFair` | the network: a tree of nodes, each edge a forward and a back arrow with committed variables; four operations (Henkin witness, new child, extend forward arrow, extend back arrow) on a fair schedule; invariants (`Good`), monotonicity (`Ext`), fairness (`fwd_total`, `back_total`, `henk_ex`, `child_box`, `child_dia`) |
| `BCanonWorld`, `BCanonDom`, `BCanonFunc`, `BCanonModel` | the model from abstract data `BData`: raw objects, denotations `rden` translating along arrows, the function algebra, definable objects as domains |
| `BCanonTerm`, `BTruth` | pushing the canonical environment along an arrow *is* the target's canonical environment read through the arrow (`boxPush_canon`, `diaPush_canon`); so the modal cases of the truth lemma are `Model.sat_subst` plus transfer/existence |
| `BRename` | renaming the declared roots of a context: `renS` with its inverse (`subst_renS_renS`), so completeness transports from a world language `ctxOf l` to any root-only context the user writes (`completenessB_rename`); for `Ctx.ofDecls ds` with distinct names the renaming is read off the declarations (`completenessB_ofDecls`) |
| `BFlat` | `Flat σ Γ Δ`: provability backwards, truth forwards along a translation, composable; built from a cancelling pair of substitutions (`Flat.ofPair`).  `Pair` keeps that data so it can be pushed under a view (`Pair.box`, `Pair.dia`) or extended by a declared root (`Pair.insertRoot`).  `Chain` keeps the steps apart so those operations distribute over them, and the `CtxExpr` induction (`CtxExpr.chain`) flattens any well-formed presentation (`CtxExpr.Wf`) — ⭐`completenessB_presented` |
| `BCompactness` | ⭐`model_existenceB`, `strong_completenessB`, `compactnessB`: consistency travels along a flattening and satisfiability back, so a presented context reduces to a world language, where the canonical model over a maximal consistent extension satisfies the set at its root |
| `BLimitPre`, `BLimit` | `BData` from the chain's limit (`bdata`): worlds are the nodes ever born, stage `i` is round `birth + i`, images are the committed ones, and stage `i` goes to the first target stage where all its variables are committed |

What the design turned out to need, beyond §2–6:

- **No back-and-forth type realisation.** The ω-chain's fairness does the work §6 assigned to
  back-types: every source variable is eventually committed along each arrow (forward and back),
  each commitment extends a consistent theory (`realise_consistent`), and arrows are read at a
  stage of the target by which the source stage is committed. Round-trip coherence is not needed.
- **Arrows are used through their committed part** (`Transfer.apply`: any suffix of the committed
  variables, any image map agreeing on them). Along a witness arrow, plain necessities transfer
  too, by `□ψ ⊢ □_x ψ` (`TransferX.applyBox`).
- **The canonical model is not staged by depth.** `rden`'s `□` clause is the denotation at the
  target of the term translated along the arrow, and the truth lemma needs no self or far cases.
- **⭐The model built is relational, so no unravelling is needed** — §4's open question 1 does not
  arise for weak B. `BData.R` is `W → W → Prop` and `BData.frame : Frame.{0, 0} σ` (`Sort 0` is
  `Prop`), with `R` the tree's edges taken both ways, symmetric by construction. Parallel arrows
  never appear because each world *names* the objects it inherits as fresh roots: the translation
  lives in the construction's `img`/`stg` data, not in the frame. `completenessB` therefore reads
  "true in every relational model implies provable", and with soundness (universe-polymorphic) the
  arrow and relational model classes validate exactly the same sequents. Whether the same trick
  collapses B + 4 and 5 is open; that is where round-trip coherence would bite.

⭐**Every presented context is covered** (`completenessB_presented`), by way of root-only contexts
whatever their names (`completenessB_ofDecls`), single views and stacks of them
(`completenessB_boxIn`, `completenessB_diaIn`, `completenessB_boxInN`), and the chain construction
below.  Still open: strong completeness, and B with T or 4.


### Presented contexts: done (2026-09-24)

⭐`BArrow.completenessB_presented`: **weak B is complete in every presented context**.  Sorry-free,
axioms `propext`, `Classical.choice`, `Quot.sound`.

The hypothesis is `CtxExpr.Wf` (2026-09-26).  Non-shadowing — each declaration's name unused in its
own prefix, needed because `CtxExpr.insertFree` permits shadowing and a renaming cannot undo it — is
`CtxExpr.Fresh`, and it is no longer asked for: it is a field of `Ctx.Presented` itself (§2d of
`v12-modal-extensions.md`).  What is left is `CtxExpr.Views`, the `◇`-rule's own side condition that
each view be taken at a declared witness, which this track needs because it takes the presentation
apart constructor by constructor.

**What the earlier note called a blocker was a missing layer, not an obstruction.**  `Pair` cannot be
composed with `Pair`, because `Subst.Coh` for a composite substitution has no generic index map: the
junk convention in `Ann.idxAt` (it returns `.root (.free 0)` away from `◇`-nodes) pins a `Coh` index
map to the annotation's junk, so `ι₂ ∘ ι₁` is the wrong map.  The fix keeps the steps apart:

```lean
inductive Chain (σ) : Ctx → Ctx → Type
  | nil  (hΓ : Γ.Presented) : Chain σ Γ Γ
  | cons (hΓ : Γ.Presented) : Pair σ Γ Δ → Chain σ Δ E → Chain σ Γ E
```

`Chain.toFlat` folds with `Flat.comp`; `Chain.box`, `Chain.insertRoot` and `Chain.dia` distribute
over the links; `Chain.snoc` appends the child arrow at the far end.  Composition therefore happens
only at the level of translations, which is exactly what the network does — arrows stay atomic, facts
get chained.  Names for `insertRoot` are per **context**, not per link (`Ctx.Presented.bound`), so
adjacent links agree.

The `CtxExpr` induction then reads:

| case | step |
|---|---|
| `empty` | `Chain.nil` |
| `insertFree e u T` | `Chain.insertRoot`, target name `l.length`, so the target is `ctxOf (T :: l)` by `ctxOf_cons` |
| `boxIn e` | `Chain.box`, then `snoc (pairBox l)` |
| `diaIn e x` | `Chain.dia`, then `snoc (pairDia l hy)`; the witness travels by `Chain.diaIdx`, and `Chain.witness` keeps it a witness |

Two things made the view cases work.  `sim_box_of`/`sim_dia_of`: being similar to the identity
survives a view, proved pointwise through `Sim.unbox`/`Sim.diaBody` — needed because `Subst.Sim` is
**not transitive** (at `𝟙`, `Term.eta w 𝟙 h` is `.unit` whatever `w` is).  And `Pair.idx_dia`: a
pair's own data forces `ι' (ι x) = x` at a reachable `◇`-address (via `Subst.idx_comp`), which is
what lets the back substitution of `Pair.dia` land on `x` rather than on `ι' (ι x)`.

**Strong completeness and compactness: done (2026-09-24)**, in `QML_v12m_BCompactness` —
`model_existenceB`, `strong_completenessB`, `compactnessB`, for every fresh presentation.  They went
through unchanged from the staged development's shape, and needed no reserved names, since the
network makes its own; the only new pieces were that a translation fixes `⊥` (a `Flat` field) and
that a list of images has a list of preimages.

**Next, in order.** Strong B, whose witnesses fit the network as a fifth scheduled operation.  Then
5, where the sibling-arrow question decides whether the naming trick collapses it to a relation as it
did for B.

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

1. ~~The finite-piece lemma (§6), in the current Lean, as a statement about two theories and a
   substitution.~~ **Done** (`QML_v12m_ArrowCheck`); the substitution turned out to be
   unnecessary.
2. Collapse as a substitution: `WFF.collapse` for `Ctx.collapses_boxIn_self` equal to
   `WFF.subst` along `u.box ↦ u.here`, `u.keep ↦ u` (T's identity arrow).
3. A throwaway arrow-indexed `Frame`, to see how much of `Soundness` survives the reindexing
   unchanged.

## 8. Open questions

1. **Round-trip coherence.** Relationalising the canonical arrow model needs no laws for T, D or B
   alone, associativity and identity (which look unproblematic) where 4 meets T, and — the real
   constraint — agreement of all round trips `a ≫ a⁻` where 4 meets B or 5. *Conjecture* (§4):
   coherence is the shadow of flag closure, so the question is whether adding 5's object-level
   component, `◇□χ(u.keep.box) ⊢ □χ(u.box)`, makes the canonical round trips coherent. If not,
   completeness for those combinations holds only over arrow-frames. (§4)
2. ~~The back-and-forth invariant for B's reverse arrows, with weak B alone.~~ **Answered for weak
   B without T and 4 (§6a)**: a fair ω-chain committing one variable at a time, no back-types
   needed. For B + 4 and S5 the chain must also give question 1's agreement across all successors
   of `w`.
3. 5's arrows between siblings: the same back-and-forth question with a different target, `v → s`
   for siblings `v`, `s`.
4. Whether any coherence beyond question 1's is needed for soundness or for strong B. (§6)
5. Whether the arrow model simplifies strong T enough to migrate T, D and 4 as well. (§5, §7)

## 9. B with T: scoping *(2026-10-03, roadmap milestone 1a)*

What the network model needs in order to take T as well as B (4 stays off).  Read against the
code as of `11926df`.

### 9.1 What is easy

* **The `□` case at the identity arrow needs no new idea.**  The semantic lemma `sat_boxHere`
  (already used for `T_box`'s soundness) says truth at the identity successor is truth of the
  collapse here; then the truth lemma at the smaller formula (`WFF.size_collapse`) and `T_box`
  finish it.  So §7's early check 2 (collapse as a substitution) is **not needed**: the identity
  arrow does not have to be one more substitution.
* **Frame.**  Keep `BData.R` as the network's edges and let the frame's accessibility be its
  reflexive closure under T (decided classically, `R s t` or else `s = t`; the network has no
  loops).  Without 4 there is no composition, so no category law and no coherence.  `rden`'s
  `□` clause reads the collapse at the identity arrow, as the tree's `rden_boxtm_self` does.
* **`extract`**: its canonical denotation is the value at the identity arrow; `necExtract_eval`
  by definition.
* **Flags.**  Most `NoTFour` uses are really `keepOnly = false`, which holds whenever 4 is off
  (`keepOnly = T && Four`).  Only eight sites use `noT` (`BCanonFunc`, `BCanonModel`, `BTruth`,
  and the `here` step in `reach_ppath`, `BRename`, `BCanonTerm`).

### 9.2 What is not: the `here` projection changes the box view

Under T, `u.here : A` is a **projection** of `u : □A` (`VarType.step`).  So in a root-only language
a root `r : □A` reaches `r.here`, and the box view contains `r.here.q.box` as well as `r.q.box`.
The B syntax layer assumes projection paths are `fst`/`snd` only (`reach_ppath`, `PPath`) and
translates an item `r.q.box` to `z.q` by rerooting at one target variable `z : bc(type r)`
(`arrowS`, `arrowIdx`, `VarType.bc`).  Under T that cannot work: `r.box` at the target is `r(t)`,
while `r.here.box` is `r(s)` read at `t`, a different object, and both must be images.  The fix is
a T-aware box-contents type, e.g.

```
bc(□A) = A × bc(A)      (under T; = A without T)
```

with `r.box ↦ z.fst'`, `r.here.q.box ↦ z.snd'.q`, and the same for products componentwise.
Defining `bc` (and `arrowS`/`arrowIdx`) by cases on `ModalSys.T` keeps every current statement
true by `simp [noT]`.  This touches the whole B syntax layer (`BSyntax`, `BAbs`, `BChild`, `BDia`,
`BFlat`, `BRename`, ~2,500 lines), mostly path arithmetic.  The consistency arguments (children,
realisation, closed transfer back) are about `arrowS` abstractly and should carry over.  **This is
the first real piece of work, and it is independent of `Here`.**

### 9.3 The `Here` layer: share the theory, port the model

Under weak T the network must host all of `Here` (`v12-roadmap.md`, milestone 1): extents containing the identity
arrow, realisation read off the theory, shape tags, `Ind`, models proper.  Split by what it
depends on:

* **Theory level — share.**  `RealDatum`, `hdeclOf`, `hhereAt`, `spec_of_here` use only a staged
  system's `ctx`, `ctx_le` and sentences (`L.sys : StageSys`), not `WorldLang` itself.
  `realised_of_here`, `mem_here_realised`, `DTerm`/`Interch`/`Rel`/`rel_of_coname` and
  `here_transfer`'s syntactic half likewise only need a maximal consistent staged theory with
  witnesses.  Restate them over a `StageSys` (with the `exW` they use), and give `BWorld` an
  adapter to `StageSys ℕ` (`ctx i := ctxOf (l i)`, sentences `⟨i, φ⟩` with `φ ∈ M i`).  This is a
  refactor of ~500 lines of the tree's files, verifiable on the tree alone, and it saves
  maintaining two copies.
* **Model level — port.**  `rden`'s `◇` clause (the identity arrow in the extent when realised,
  with the realised content there), `interp_dia_self`, and the shape layer differ in substance:
  - *shapes*: a canonical leaf for a label address cut at a `□` step is a family over the
    successors.  In the tree an entry is the leaf of the address the successor sees
    (`succAddr`, shift arithmetic); in the network it is the leaf of the address's **image under
    the arrow's renaming** (and the collapse at the identity arrow).  Without 4 there is no shift,
    so the calculus should be simpler than `CanonLeaf`'s;
  - *the decoder* follows a proper successor (under T one exists: `T_box` refutes `□⊥`, and `ex`
    gives a network successor) and must **invert the arrow's renaming**.  `ImgOk` does not make
    `img` injective.  The network's images are fresh committed variables, so injectivity should
    be provable and added to `BData` (`imgInj`); this is the one new obligation on the
    construction found so far;
  - `Ind := Rel` and canonical `IndInvariant` follow the tree (`CanonInd`): an environment over a
    tame context is the canonical one read through a substitution, which the network already
    does for arrows (`boxPush_canon`).
* **Not migrating.**  Running the 4-free systems on the network would still leave the tree for 4,
  so two models remain either way; it can be reconsidered once B + 4 is understood (§8 q. 5).

### 9.4 Proposed order

1. **Syntax**: T-aware `bc`/`arrowS`/`arrowIdx`, `here` in projection paths, under 4 off; current
   B results unchanged.  Then the network construction under weak T (consistency lemmas with the
   new items), and `imgInj`.
2. **Theory-level `Here` layer over `StageSys`** (refactor, tree only), then the `BWorld` adapter.
3. **Model**: reflexive closure, `rden` at the identity arrow (`□` collapse, `◇` realised content),
   `extract`; the truth lemma's `□` case.
4. **Shapes on the network**: leaves by arrow images, the decoder, tags determine annotations;
   then the `here` case, `Ind`, `IndInvariant`.
5. **Statements**: a flag class "4 off, strong T off" replacing `NoTFour`; completeness, strong
   completeness, compactness, presented contexts.
6. **Strong T**: the term query in the network's fair schedule (`retW`), then `posRet_exists`.

Steps 1 and 2 are independent and can go in either order; 3 needs 1; 4 needs 2 and 3.

### 9.5 ✅ Step 1 done: the B syntax layer and the network take T *(2026-10-03)*

Everything up to and including `BData` (`BSyntax` … `BLimit`) now assumes only
`ModalSys.NoFour` (4 off) instead of `NoTFour`; the canonical model on top (`BCanonWorld`
onwards), flattening (`BFlat`, `BRename`) and the statements still assume `NoTFour`, and every
existing result is unchanged.  Whole v12m list green, no `sorry`, no warnings.

* **Box contents with a flag argument.**  `VarType.bcB (b : Bool)` with `bc := bcB ModalSys.T`;
  `bcB true (□A) = A × bcB true A`, `bcB false (□A) = A` (`cond`, with `b` a fixed parameter so
  that `bcB b (A × B)` reduces for a variable `b`).  Terms of a `bc` type are built by matching on
  the flag (`tupB u R b hb h`, `tup := tupB u R ModalSys.T rfl`) — no casts.
* **Where an item lands.**  `encPath` (projection path, `here ↦ snd` under T), `itemTail` (`[fst]`
  under T), `itemPath` (up to the first `box` encoded, the `box` replaced by `itemTail`), and
  ⭐`itemAt z u := z.(encPath u.path ++ itemTail)`, the image of the item `u.box` read from a root
  `z`.  Arrows use `itemImg img u := itemAt (img u.rt) u`, abstraction `itemAt (bnd 0) u`.
  Without T, `itemAt z u = u.reroot z` (`itemAt_noT`).  `ref_enc_bc`/`ref_item` type them.
* **Paths.**  `PPath` is now "every step a projection" (so it admits `here`), and `reach_ppath`
  needs no flag: a root-only context reaches only projection paths, whatever the flags.
* **Tuples.**  `proj_tupB` (projecting a tuple along an encoded step gives the tuple of the
  projected address — under T, a `□` component's second component is its `here` value's tuple),
  `at_item_of_tupB` (reading a substitution at an item's image gives the item), and their
  weakened forms; `at_single_tupB`, `at_pull_tup`, `at_pullX_tup` are inductions using them.
* **Not needed after all** in step 1: `imgInj`.  It belongs to the decoder (step 4).

So weak and strong T both reach `BData` with the construction unchanged; what T still needs is
the canonical model (steps 3–4) and, for strong T, the term query (step 6).

### 9.6 ✅ Step 2 done: the theory-level `Here` layer is shared *(2026-10-03)*

The theory-level `Here` layer is now stated for a **staged theory** — a stage system `S : StageSys I`
(directed) with a set `T` of its sentences, maximal consistency supplied as an instance
`[Fact (StageSys.IsMCS T)]` — and both canonical models instantiate it.  Whole v12m list green.

* `Canon.RealDatum σ S T x` with `a₀`, `t₀`, `hdeclOf` (directedness instead of the tree's `max`),
  `hhereAt`, `declType`, `spec_of_here`, `spec`.
* `CanonInterch`: `Interch T`, `DTerm S T A` (the theory a parameter only, so `s.Rel s'` reads it off
  the type), `DTerm.Rel` with `refl`/`symm`/`trans`/`rel_lift`, `interch_of_coname`,
  `rel_of_coname`, `Interch.of_lift`, `Interch.dia_iff`.
* New, generic: `RootWitnessed S T` (Henkin witnessing at a declared root); ⭐`datum_of_here` (a
  `Here` atom gives its witness a datum) and ⭐`mem_here_datum` (a datum's possible object has its
  realisation as content, at any stage above both) — with `Term.viewReadTm_eta_diaAbsA` moved
  alongside.  The tree's `realised_of_here` and `mem_here_realised` are now one-line instances.
* The tree instantiates at `S := w.L.sys`, `T := w.T` (`World.mcsFact`).  Lean accepts
  `w.L.sys.ctx i` for `w.L.ctx i` by unfolding, so no tree proof needed changing beyond a few
  `DTerm w.L.sys w.T A` signatures and two type ascriptions.
* The network: `BWorld.exW` now witnesses at a declared root (the Henkin step always declared a
  fresh variable; `henk_ex` now says so), with `BWorld.exW_term` the old form.  New file
  `QML_v12m_BStaged`: `BWorld.sys`, `BWorld.T`, ⭐`BWorld.mcsT` (maximal consistent as a staged
  theory), `BWorld.rootWitnessed`, and `BWorld.datum_of_here` checking that the generic layer
  applies.
* Left world-specific: the classical choice of a datum (`World.real`/`Realised`), a few lines the
  network's model will define for itself in step 3.

### 9.7 ✅ Step 3 done: the network model's own arrows, below the `Model` instance *(2026-10-03)*

Under T a `Model` must tag every possible object with a shape (`posFull`), and the network has no
shapes until step 4.  So step 3 makes everything **below** the `Model` instance T-aware, under
`ModalSys.NoFour`, while the instance itself, the canonical environment lemmas and the truth lemma
stay under `NoTFour` for now (they reach the new definitions through `R_of_RT` and
`kd_of_extent`, which hold when T is off).  The truth lemma's `□` case at the own arrow therefore
moves to step 4 with the instance.  Whole v12m list green.

* **Own arrows.**  `BData` gains `irrefl` (the network has no loops: `LR.irrefl`, an edge joins a
  node to its child).  The canonical accessibility is `RT s t := R s t ∨ (T ∧ s = t)`; `Acc` is
  indexed by it; `self_of_not_R` reads an arrow that is not the network's as the world's own.
* **Extents.**  `extent s x` is the network's witness arrows into `x`'s extent and, when the
  world's theory realises `x` (`BWorld.Realised`: a datum exists, `QML_v12m_BStaged`), its own
  arrow (`mem_extent_self`).
* **`rden`** (now classical): along the own arrow a necessary term denotes its body collapsed;
  a possible term's content there is the body realised by the datum (`realTerm`, the tree's
  `realisedTerm`), transported by the context inclusion `selfLe` rather than by casting the raw
  object.  Equation lemmas `rden_boxtm_net`/`_self`, `rden_diatm_net`/`_self`; `rden_mono` and
  `rden_congr` cover the new cases (the latter mirroring the tree's via `Term.mono_realiseAtA`);
  `rden_realTerm_pair`, `rden_realTerm_mono_boxIn` (a `□`-view term's realised content is its
  collapse).
* **Function algebra.**  `rawEval (.extract hT) o := o` at the own arrow; `rden_applyG` for every
  map including `strength` and `extract` at the own arrow (`applyG_realTerm`,
  `Canon.applyG_collapse`).
* **Frame.**  `R := RT`: reflexive under T by construction, symmetric, serial; the 4 laws are
  vacuous.

### 9.8 ✅ Step 4a: shapes on the network, and the `Model` instance under weak T *(2026-10-03)*

Step 4 is split: **4a** shapes and the instance; **4b** the truth lemma's `□`/`◇` cases at the
own arrow (`canonEnv`, `boxPush`/`diaPush`, `interp_canon` under T, mirroring the tree's
`envShape_canon` and `interp_dia_self`); **4c** the decoder, tags determine annotations, the `here`
case, `Ind := Rel` and `IndInvariant`.  4a is done; whole v12m list green, no warnings.

* **Shape layer** (`BCanonDom`, mirroring `QML_v12m_CanonShape`): `BData.arrows` (the worlds with
  `RT`; the frame is now built on it, `toArrows := B.arrows`, so canonical shapes are the model's),
  `CShape`/`CShEnv`, ⭐`succAddr` (through the arrow's index map `arrowIdx` along a network arrow,
  collapsed along the own arrow), `rootSh`, ⭐`canonSh`, `canonSh_proj`, `canonEnvF`/`cEnv`,
  `canonEnvF_ref` (projections need only commute on reachable addresses — `arrowIdx` encodes a
  `here` before the first `box`), `cEnv_boxPush`, `termShp_collapse_cEnv`, ⭐`termShp_arrow_cEnv`
  (a body translated along a network arrow has the shape of the body read through `arrowIdx`, by
  `Model.termShp_subst`).  `arrowIdx_item` moved to `BSyntax`.
* **Tags.**  `RDom (◇A)` is now `RPos` (extent, contents, and under T a stored shape), `rden`'s tag
  is `termShp (cEnv Γ s) 0 (◇_x t)`, `rawShape`, and ⭐`rawShape_rden` (stored = symbolic).
* **Function algebra.**  `rawEval` moves tags as `GFunc.shp` does (`diaMap`, `strength` with the
  necessary object's `rawShape`); `rden_applyG` checks them (`Canon.termShp_applyG`).
* **Model.**  `posFull` (section and stored shape), `posFull_injective` (replacing
  `posEval_injective`, which only holds without T), `domShape_toDom`, the laws `posMap_full` and
  `posStrength_full`, `necExtract` by `rawEval`.  The instance is built under the new class
  `ModalSys.NoFourNoTS` (4 off; strong T off whenever T is on — `NoTFour` gives it), with
  `RootPoss := VarSymb` and, for now, `Ind := (· = ·)` (4c replaces it).

### 9.9 ✅ Step 4b: the canonical environment under weak T *(2026-10-03)*

`BCanonTerm` now holds under `ModalSys.NoFourNoTS` (weak T allowed).  Whole v12m list green.

* `canonEnv_ref`'s `here` case: `u.here` reads the value at the own arrow, which is the collapse of
  `u`'s body (`rden_boxtm_self`, `Term.collapse_eta`, `VarSymb.inner_collapse_zero`).
* `boxPush_canon`/`diaPush_canon` now take the network-arrow hypothesis (`B.R s a.1`,
  resp. `∃ X, B.kd s a.1.1 = some (x, X)`); along the own arrow the push is semantic
  (`Model.Env.collapseAgree_self`, `Model.interp_realiseAtA`), not a substitution.
* `interp_canon_eta`, `envShape_canon` (an environment agreeing with the canonical one has the
  canonical shapes), `rden_eta_real` (a realised witness's content along the own arrow is its
  datum's), `rden_realTerm_eta` (`BCanonDom`).
* ⭐`interp_dia_self` (the tree's `interp_dia_self`): along the own arrow a possible term's value has
  the realised body as content.
* ⭐`interp_canon` under T: `□` along the own arrow via `Model.interp_collapse`; `◇` via
  `Model.pos_inj` — sections arrow by arrow (network arrows by substitution, the own arrow by
  `interp_dia_self`) and shapes by `envShape_canon`.

**The truth lemma moves to 4c.**  Its `here` case cannot be discharged under weak T until `Ind` is
the canonical relation, so `BTruth` (and with it the `□`/`◇` cases along the own arrow, which are
the tree's: `sat_boxHere` with `T_box`, and `interp_dia_self`) stays under `NoTFour` until then.

### 9.10 ✅ Step 4c: leaves, tags, `Ind`, the truth lemma under weak T *(2026-10-03)*

Step 4 is complete: the truth lemma and `IndInvariant` hold under `ModalSys.NoFourNoTS`.  Only the
statements (step 5) still assume `NoTFour`.  Whole B chain green (through `BCompactness`), no
sorries.

**The leaf calculus on the network** (`QML_v12m_BLeaf`) is the tree's with two changes.
* *Exact levels.*  The network's languages declare only roots, so an address reachable after `j`
  views has exactly `j` levels (`Ctx.Exact`, replacing the tree's `Ctx.Deep`; `Ann.Exact` for
  labels, `Term.ann_exact`).  A label's cut is therefore its *first* level step, a `box` (4 is off).
  That is exactly where `arrowIdx` cuts, so `succAddrK s a k` is `arrowIdx` along a network arrow
  (for every `k`) and `collapse k` along the own arrow.  With this, `annShp_eta_transpose`,
  `canonSh_eq` (for level-free addresses), `leafOf_collapse`, `annShp_eta_collapse`, `Canonical`
  and ⭐⭐`termShp_canonical` port line for line.  The new address lemmas are
  `collapse_ext_indep`/`splitAt_ext_indep` (collapsing and cutting inside a path ignore its
  prefix) and `arrowIdx_boxExt` (past the first `box`, `arrowIdx` keeps the path).
* *No one arrow decodes.*  The tree reads a family back along one proper successor, where reading
  is the identity.  On the network no single arrow is injective on labels.
  * The own arrow turns the cut `box` into a `here`, so `r.here.box` and `r.box.here` collapse
    alike.
  * A network arrow encodes the projections before the cut (`here ↦ snd`), so it identifies
    `r.here.…` with `r.snd.…`.
  * The two together do decode (`eq_of_here_enc`): where the paths first differ, one image has the
    cut's `here` against a projection that would have to encode to `fst`, and nothing does.
  * So ⭐`leafOf_inj` uses the own arrow (under T) and one network arrow.  `exists_net` gives one:
    `T_box` refutes `□⊥`, and `ex` builds the arrow.  The `imgInj` that §9 anticipated is not
    needed.

  Hence ⭐⭐`ann_eq_of_rden` / `ann_eq_of_rden_ctx`: under T, tags determine annotations, in any
  allowed, level-free context — in particular the worlds' own (`exact_ctxOf`).

**`Ind` and `Here`.**
* `BData.Ind` is the tree's `Canon.Ind`: related representatives (`DTerm.Rel` over `BWorld.sys`).
* `QML_v12m_BHere` holds `mem_here_real` (`Canon.mem_here_datum` at the realised term),
  `here_transfer` and ⭐⭐`here_truth`, all the tree's.

**The truth lemma** (`BTruth`, now under `NoFourNoTS`):
* `□` at the own arrow: `sat_boxHere` with `T_box`.
* `◇` at the own arrow, where the witness is realised: `dia_mem_of_sat_self` (`sat_realiseAtA`,
  `RealDatum.spec`).
* `here`: `here_truth`.

**Models proper** (`QML_v12m_BInd`): `rep`, `repSubst`, `substEnv_repSubst`, ⭐⭐`indInvariant`,
as in the tree.  `BCompleteness` and `BCompactness` use it in place of `indInvariant_of_eq`.
