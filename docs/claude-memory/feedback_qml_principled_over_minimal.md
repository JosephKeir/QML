---
name: feedback-qml-principled-over-minimal
description: QML engineering choices (user, 2026-10-10) — prefer the principled, generalisable design over the smaller patch when the piece may be reused (e.g. shape-level ret rules over an ad hoc "rest" parameter)
metadata:
  type: feedback
---

When an engineering choice is between a smaller targeted patch and a more principled,
generalisable construction, **prefer the principled one if the piece is potentially reusable or
generalisable** — the user expects it to save work in the long term.

**Why:** said when choosing how witness children hold `x` under strong B: the user picked
shape-level `ret_ext` plus a shape-level β (box `ret_ext` becoming derived) over an optional
"rest" parameter threaded through `RetInv`, though the latter was smaller.

**How to apply:** still present both options with costs, but recommend the principled one when it
will be reused (4 and 5 are coming), and reserve the minimal patch for genuinely one-off needs.
Related: [[feedback-qml-witness-k-paradigm]], [[feedback-qml-mirror-terms]].
