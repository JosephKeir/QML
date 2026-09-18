# QML v12: modal extensions (design)

Status: 2026-09-17. **Weak T and weak 4 are implemented**, with soundness and completeness for
every combination (K, T, 4, and T + 4 = S4); files `QML/QML_v12m_*.lean`, namespace `V12M`.
**Strong T is implemented through soundness and substitution**: the flag, the model axiom, the rule
`T_dia`, its soundness case and substitution into it are all sorry-free, and `QML_v12m_*` as a whole
contains no `sorry`. Its canonical model is not started, so completeness does not yet cover strong T
(`ModalSys.NoTStrong` is still assumed there). Everything else is design. Claims marked *(sketch)*
come from paper arguments that have not been checked in Lean.

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
  - *Canonical model: barely started.* `ModalSys.NoTStrong` is still assumed in `QML_v12m_Canon*`
    and `QML_v12m_Completeness`. **`posRet_exists` is currently false there**, not merely unproved:
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
  - *Still to do for strong T's model*: the chain's list of later constants and the three packing
    side conditions; the `RealDatum` for each chain witness (`chainReal`), which `World.ofHenkin`
    then names; `posRet_exists`; and then dropping `ModalSys.NoTStrong`, at which point
    `interp_canon`'s realised case, `diaPush_agree_canon` and the truth lemma's `◇` case need their
    real proofs, on the lexicographic (own stage, term size) measure.
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
