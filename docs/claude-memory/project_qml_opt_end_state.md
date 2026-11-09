---
name: project-qml-opt-end-state
description: "QML target end state for the box view of possible objects (Opt): shapes deleted, interpolation in every system, Opt a semi-independent flag required only where needed"
metadata:
  node_type: memory
  type: project
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-11-09T12:07:43.515Z
---

The user's target (2026-11-10) for the `wip/in-atom` line: **delete shapes** and have **Craig
interpolation in every case** (every system of the cube), if it can be done.  `Opt` (the box view
of possible objects, `◇⁰`/`In`) becomes a **semi-independent modal flag**: a requirement field
forces it on where a system needs it (as `CubeSys.strongB : BStrong → B` does), and elsewhere it is
an independent choice ("you can have this machinery if you want").

**Why:** `In` exists to repair interpolation (KT lacks Craig with `Here` at `◇`-content) and to
carry the identification principle, which is what lets shapes and `Ind` go.  K, D and 4 never
needed it: their completeness, GK, cut elimination and Craig hold with `Opt` off.

**How to apply:** decide which flag combinations require `Opt` by that target: T and strong B
certainly (no semantics once shapes go); weak B and 5 according to whether their interpolation
needs it.  Keep the Opt-off results for K, D, 4 as final.  Order: M1 (K with `Opt` on), M2 (KT),
M3 (GK with `In`), then 4, B, 5 and the requirement fields.  See [[project-qml-current-position]],
[[feedback-qml-principled-over-minimal]], [[project-qml-scope-cube]].
