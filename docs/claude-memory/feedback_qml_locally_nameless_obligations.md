---
name: feedback-qml-locally-nameless-obligations
description: "QML design principle — the user's ONLY freshness obligation is that free variables they declare are not already in the context; bound-variable freshness is internal machinery"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-09-26T17:29:48.117Z
---

User (2026-09-26), stated as their basic philosophy for QML: one advantage of the locally nameless
approach is that **bound variables and their freshness conditions are handled internally**, while
the user's only obligation is to check that **free variables they declare are not already in the
context**. Any *additional* freshness obligation is a design smell.

**Why:** two reasons the user gave. (1) The user does not control bound-variable names, so an extra
freshness condition may be hard or impossible for them to satisfy. (2) It is the kind of thing the
locally nameless machinery should handle itself, not delegate to the user.

**How to apply:** when a construction needs a freshness/non-shadowing side condition, do not add it
as a hypothesis on the headline theorem — make it **structural**, carried by the object that is
already required. The 2026-09-26 fix: `CtxExpr.Fresh` (each declaration's name unused in its own
prefix) became a *field* of `Ctx.Presented`, so `Ctx.Presented.levelFlat` derives `Ctx.LevelFlat`
and `completeness`/`provable_iff_valid`/`model_existence`/`strong_completeness`/`compactness` need
only `[Γ.Presented]`. The user also dislikes having *several slightly different* non-shadowing
conditions in different places: keep one, and if a second is unavoidable, make sure it is genuinely
a different kind of condition (e.g. `CtxExpr.Views`, the ◇-rule's own side condition) and say so.
See [[feedback-qml-presented-contexts]], [[project-qml-current-position]].
