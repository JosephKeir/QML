---
name: feedback_qml_operators_over_relations
description: QML design preference — express modal notions as modal operators (views/formers like ◇⁰) rather than primitive relations (Back, Ret, links, Here, Ind)
metadata:
  type: feedback
---
Prefer **modal operators** (view formers in the style of `◇⁰_y`, read along a canonical arrow) to
**primitive relations** (`Back`, the returning possibility's `Ret`, 5's links, `Here`, `Ind`).

**Why:** the user (2026-11-13) expects operators to help cut elimination/interpolation and to remove
primitives, giving a neater syntax. Concretely: `Here` becomes `◇⁰ᵀ` at the identity arrow (M2), and
for B the user proposed stating the round trip at the far world, where the way home of the arrow
just taken is canonical under strong B (docs §12.29).

**Goal (user, 2026-11-13, stronger):** *all* primitive relations should go — Here, Ind, Back/ret, links — "it is supposed to be modal logic after all". Paper check (docs §12.31): where the model reads `Ind` (Here, strong B's Back/ret at ◇-content) interpolation is at risk and operator + ≡ fixes it; weak B/5 need an analytic calculus, which ⟪back⟫/side views may supply.

**How to apply:** before adding `Opt` (or other machinery) to a system whose syntax has relation
primitives, first check on paper whether a far-world/arrow-indexed operator can define them
(roadmap M4b for B, M4c for 5). Don't dismiss an operator because "nothing names the arrow" or
"the far world can't see home objects" without checking whether a canonical arrow exists
(uniqueness laws) and whether the witness mechanism (`Ctx.wit`/`Env.wit` storing outer names and
their data) gets past it. Related: [[feedback_qml_principled_over_minimal]],
[[feedback_qml_unlinked_equality_model_law]], [[project_qml_opt_end_state]].
