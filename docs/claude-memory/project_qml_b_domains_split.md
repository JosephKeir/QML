---
name: project-qml-b-domains-split
description: "QML writeup framing the user liked (2026-11-10): B's three strengths split domains cleanly — frame only / necessary objects cover / possible objects cover — with □-BF and ◇-BF falling on the split"
metadata:
  node_type: memory
  type: project
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-11-09T20:56:51.003Z
---

The user called this "quite neat, a clean split" (2026-11-10) and wants it for the writeup:

1. **Weak B** (`Frame.symm` only): a frame condition; domains vary freely beyond K's inclusion
   (necessary objects' values land in successor domains).  □-BF fails (countermodel: a successor
   object no necessary object reaches).  The standard BF proof fails at the instance-and-return
   step: the outer eigenvariable is invisible under `□`, and `B_dia` only returns closed formulas.
2. **Strong B rows 1–2** (`homeUnique`, `backRet_exists`): each world's domain is exactly the
   values of a neighbour's necessary objects, both directions, every type, up to `Ind`.  The arrow
   analogue of constant domains, but many-one (sizes may differ; like total counterpart relations).
   □-BF valid with parameters, so derivable by completeness; the standard proof goes through with
   the variable replaced by its carrier (`B_strong`) and B by `back_counit`.  ◇-BF still fails.
3. **Strong B with witnessed ways home** (`BStrongW`, `posBack_exists`): possible objects cover the
   successors' domains too, arrow by arrow (no uniform carrier) — the possibilist ◇-BF, valid and so
   derivable.  So `BStrongW` is where comprehension of possible objects enters the cube (tension
   with [[feedback-qml-cube-vs-barcan]], flagged to the user, not yet decided).

**Why:** it shows weak = accessibility, strong = object existence, one kind of object at a time.
**How to apply:** use this framing for B in the writeup; docs §4's edge table was corrected to
match (strong B ⇒ □-BF ✓; ◇-BF only with `BStrongW`).  The two-world many-one example and the
counterpart comparison are paper reasoning, not checked in Lean.  See
[[project-qml-current-position]].

Generalised (2026-11-10) to every axiom: weak = frame + determined maps, strong = one existence law per object kind (necessary / possible), diagonal.  Empty cells: T necessary (NecT), 5 possible (◇-gather); both on the roadmap ('After the Opt refactor') as the next work after Opt.
