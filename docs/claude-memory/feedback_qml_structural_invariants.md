---
name: feedback-qml-structural-invariants
description: "QML — invariants that hold of everything a user can write and are preserved by every construction (Presented, OpenedT) should ideally be structural, not hypotheses; but don't polish forever"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-11-13T23:10:02.540Z
---

User (2026-11-13), on `Env.OpenedT` (environment respects its identity contents, threaded as a
hypothesis through soundness and a dozen semantic lemmas): it is like `Ctx.Presented` — required
of anything a user can actually write, then preserved by everything built. In the neatest
formulation all such conditions should be **structural**, but the user accepts this is not always
the easiest route and "we don't want to keep polishing forever".

**Why:** a hypothesis that every construction preserves is a property of the objects, not of the
theorem; carrying it by hand clutters statements (and broke `IndInvariant.inv` for uniform
substitution, which quantifies over all environments).

**How to apply:** when adding such an invariant, note the structural option (a bundled
environment / a field, as `CtxExpr.Fresh` became a field of `Presented`) and its cost; take the
hypothesis route mid-milestone if the structural one is expensive, but record it as a cleanup item
(docs §12.30 "To consider") rather than forgetting it. Don't propose polishing passes unprompted
between milestones. See [[feedback-qml-locally-nameless-obligations]],
[[feedback-qml-presented-contexts]], [[feedback-qml-principled-over-minimal]].
