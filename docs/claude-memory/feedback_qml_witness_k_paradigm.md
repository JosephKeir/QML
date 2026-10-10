---
name: feedback-qml-witness-k-paradigm
description: "QML design rule (user, 2026-10-10) — witnessed rules = unwitnessed rules + subscript, carrying the witness (a possible object) along with necessary objects, on the K rules' paradigm; applies to strong B now and to 4 and 5 later"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-10-09T09:04:57.978Z
---

**Witnessed/subscripted rules should be almost identical to their unwitnessed versions, with the
subscript added**: semantically they are the same rules restricted to the witness's extent.
**The K rules are the paradigm**: `K_box` carries necessary objects into the `□` view, `K_dia`
carries necessary objects *together with the witness's content* into the `◇_x` view.  So
unwitnessed constructions carry/return necessary objects; witnessed ones carry/return necessary
objects **and the witness** (a possible object).

**Why:** when a subscripted rule fails to behave like its plain version, the cause has been a
construct that can only carry necessary objects — e.g. strong B's `ret` bound only `d : □A`, so
the witnessed unit could not bring `x` back and the ∨ law along `x` was underivable.  The fix
(returnable binders with `◇` parts, `e ⇝ u`; docs §11.17) made witness children uniform with
plain ones.  The user said this should also be the pattern for 4 and 5.

**How to apply:** when designing or checking a witnessed rule, ask what the K pair does and make
the witnessed version carry the witness too.  If a derivation works on the plain leg but not along
`x`, look for a binder or hole that only admits necessary objects.  Related:
[[feedback-qml-joint-possibility-pairing]], [[project-qml-current-position]].
