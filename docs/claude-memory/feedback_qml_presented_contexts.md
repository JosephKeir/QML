---
name: feedback-qml-presented-contexts
description: "QML v12 — presentable (finitely presented) contexts are the \"real\" contexts; generality over arbitrary function contexts is a bonus"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-09-12T17:57:25.009Z
---

User (2026-09-12): presentable contexts (`Ctx.Presented`, built from empty by free-variable
insertion and □/◇ views) are the "real" ones — the only ones that matter. Being able to say things
about non-presentable function contexts is a bonus, not a goal.

**Why:** function contexts are an implementation device kept "under the hood"; the logic is about
finite, presented contexts.

**How to apply:** state headline metatheorems (proof renaming/weakening admissibility, completeness)
for presented contexts; use Presented to discharge side conditions like fresh-name supply. Avoid
designs that need non-presentable (e.g. infinite limit) contexts — prefer staged constructions whose
every stage is presentable. See [[project-qml-v12-semantics]].
