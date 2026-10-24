---
name: feedback-qml-type-generality
description: "QML: restricting to ◇-free types and 'nesting' is a FAILED design principle (user, 2026-10-23 and 2026-10-25) — never propose it as a fix; only equality stays base-typed"
metadata:
  node_type: memory
  type: feedback
---

**Do not propose "restrict to `◇`-free types and nest" as a fix.**  It was tried and abandoned:
`Here` was restricted to `◇`-free content in 2026-09 and later generalised back to every content
type (`WFF.here` takes any `A`; `RealDatum`'s content is "any type, as `WFF.here`'s is"), and for
strong 4 the user rejected a `◇`-free restriction on 2026-10-23 ("Finding 1 came from the tree":
it was a *direction* problem of the construction, not a `◇`-type problem — docs §3 4,
"Correction (2026-10-23, user)").  On 2026-10-25 the user called it "a failed design principle"
when I offered it again (option (A) for T + strong 4 vs canonical shapes) and chose the general
fix instead.

**Why:** apparent `◇`-type obstacles have so far always been artefacts of a construction (order of
naming, what the canonical side records), and the general design worked once the construction
was fixed.  Restrictions cost the logic real reach.

**How to apply:** when a canonical construction fails at `◇`-typed contents, look for what the
construction fails to record or in which direction it names things, and design that general
fix.  Equality being base-typed is a separate, settled matter (still the case), not a licence
for further restrictions.  Related: [[feedback-qml-principled-over-minimal]],
[[feedback-qml-joint-possibility-pairing]].
