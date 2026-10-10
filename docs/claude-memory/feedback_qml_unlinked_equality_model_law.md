---
name: qml-unlinked-equality-model-law
description: "QML design principle — an equality-like relation between ◇-typed objects with no proper link becomes a model requirement (law), never an object-language rule"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-10-10T10:52:52.829Z
---

When something looks like an equality between `◇`-typed objects without a proper link (no map
between their witnesses' inner contexts), don't express it in the object language. Make it a
primitive of models, constrained by laws ("models proper"), as `Ind` was. Where equality does
exist (`◇`-free types), the primitive is *defined* (e.g. `Back` = round trip = definite
description via `back_ret`).

**Why:** user, 2026-10-10. Rule-based routes (§11.16's `≈`, `back_cases` and its family form)
keep adding ever more elaborate rules until a cross-witness equality seems needed, and that
equality brings insoluble problems (§10.3). The model-law route is known to work (`Ind`). Decided
for `Back` at `◇` contents (`Ret` primitive, docs §11.20).

**How to apply:** when a completeness gap at `◇` types seems to need a new rule comparing objects
over different witnesses, first ask whether the semantics can be loosened to a model primitive
with laws that make the existing rules sound. The canonical model then reads the primitive off
the theory's atoms. Related: [[qml-cube-vs-barcan]], [[qml-joint-possibility-pairing]],
[[project-qml-current-position]].
