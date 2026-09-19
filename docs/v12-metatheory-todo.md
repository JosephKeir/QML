# QML v12m: metatheory to do

Recorded 2026-09-16; items 4 and 5 added 2026-09-18; item 6 added 2026-09-18. These are general proof-theory jobs, not
modal-extension work. The agreed order is: finish the modal extensions (strong T, strong B, S5, D,
BF) and their completeness first, then the items here. Item 1 is close enough to done that it could
be taken at any time; items 4 and 5 are research questions rather than routine jobs.

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

## 5. Craig interpolation

**Goal.** If `φ ⊢ ψ`, there is `θ` using only the non-logical symbols common to `φ` and `ψ` with
`φ ⊢ θ` and `θ ⊢ ψ`.

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
