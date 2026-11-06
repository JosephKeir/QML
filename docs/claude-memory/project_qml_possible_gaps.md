---
name: project_qml_possible_gaps
description: QML possible gaps and questions to review only once everything else is finished; so far KB5 with strong B, weak and strong K5/KD5 (no construction found; five_rigid missing; saturation route recorded), and whether other rule sets could take K_box/K_dia's shape
metadata:
  type: project
---

**KB5 with strong B: CLOSED as a recorded exception** (reviewed with the user, 2026-11-06): S5 with strong B or a dead end, not worth the T-off stack; not to be filled.  (Was a possible gap since 2026-11-01.)

**Why:** strong B makes arrows unique, so with D the frames are S5's (`Frame.exists_unit_of_serial`) and KDB5 with strong B is read as S5 with strong B.  KB5 with strong B is S5 with strong B or a dead end, so it adds little, while filling it takes the T-off stack: `back_self`, `back_own`, `back_leg`, a `Here` without T (a language extension), and about 9 500 lines redone.

**Also for the final review (user, 2026-11-06): could other rule sets have taken `K_box` and `K_dia`'s shape?**  The user is very sure those two shapes are right for what they do, and wondered whether other rule sets (e.g. the returning possibility's, the link rules of 5) could have been given that shape instead of the ones they have.  The links' K rules were given it (`link_K`, `linkx_K`).  **Reviewed (2026-11-06):** only the returning possibility deviates (`ret_monoS`); a `K_dia`-shaped `ret_K` is inter-derivable with it.  Decided: present `ret_K` in the write-up, `ret_monoS` derived; Lean change optional, low priority.

**Strong K5 and KD5 are possible gaps too** (user's decision, 2026-11-06).  Both strengths are incomplete as ruled (missing `five_rigid`, cluster rigidity of uniform formulas, plus its companion "5 for uniform formulas", both checked sound), and both meet the amalgamation obstruction: strong only at the root, whose necessary objects nothing names.  Most promising route: a saturation construction (decide every theory first, identify afterwards), which dissolves the obstruction but needs saturated models of one size (a set-theoretic hypothesis or monster models).  The user's view (2026-11-06): likely a lot of work, probably not worth it.  Details: `docs/v12-modal-extensions.md`, "5 without 4: a saturation construction, scoped" and the sections before it.

**Weak K5 and KD5 (5 without 4, strong 5 off) are possible gaps** (user's decision, 2026-11-06).  Their syntax, rules, soundness and substitution are built; completeness is not.  A construction by local steps meets an obstruction met by no other cell: necessary objects private to cluster worlds (weak 5 has no operation carrying them across arrows), possible objects shared across the cluster (side images), and theories completed one world at a time.  Six alternatives failed on paper.  Routes left: a global (labelled) calculus, or a reduction to K45 needing a conservativity theorem.  Incompleteness not ruled out.  Details: `docs/v12-modal-extensions.md`, "Weak K5 and KD5: alternative constructions, scoped".  Review at the end with the user; don't start before.

**How to apply:** keep it out of the next-steps list, but raise it at the final review.  The design is in `docs/v12-modal-extensions.md`, "Strong B on KB5 and KDB5", sections 2 to 8.  Related: [[project_qml_current_position]], [[project_qml_scope_cube]].
