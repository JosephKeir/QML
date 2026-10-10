---
name: feedback-qml-cube-vs-barcan
description: "QML design principle — modal axioms are about accessibility first, object existence only in their strong forms; Barcan (comprehension of possible objects) stays separate from the cube"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-10-05T12:36:05.767Z
---

Each modal axiom's weak form is about the accessibility relation (frame conditions, transport of
formulas). Its strong form adds the existence of certain objects (naming routes or returns:
`T_dia`/`Here`, `B_strong`/`Back`/`◇[d ↦ t]`, `4_lift`, `5_lift`, strong D's `D_ex`). The Barcan
formula, in its possibilist form `◇∃y.φ(y) ⊢ ∃x:◇A.◇_xφ(x.dia)`, is a comprehension principle on
the model's possible objects (`D_name` at type 𝟙). It is not part of the cube, and the user counts
"Barcan separated from the cube" as a positive result (2026-10-05, docs §11.19).

**Why:** the user's view is that modal rules concern accessibility first, and only then the
existence of objects in the strong cases. Comprehension of possible objects is a separate,
philosophical choice.

**How to apply:** don't fold Barcan-like or comprehension principles (`D_name`, fullness of `Pos`)
into an axiom's flag. Keep them as separate, optional principles. Inward transport should be
designed as existence-plus-relation, and outward transport as terms or view items (see
[[project-qml-current-position]]).
