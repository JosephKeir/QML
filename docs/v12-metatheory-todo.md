# QML v12m: metatheory to do

Recorded 2026-09-16. These are general proof-theory jobs, not modal-extension work. The agreed
order is: finish the modal extensions (strong T, strong B, S5, D, BF) first, then items 2 and 3
here. Item 1 is close enough to done that it could be taken at any time.

## 1. Strong completeness and compactness

**Status: not stated, but the machinery is finitary and already supports it.**

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
  `four_box`), since they move formulas between levels, and the equality rules, which instantiate a
  formula at a slot.
