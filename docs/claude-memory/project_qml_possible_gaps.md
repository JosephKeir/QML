---
name: project_qml_possible_gaps
description: QML possible gaps to review only once everything else is finished; so far KB5 with strong B
metadata:
  type: project
---

**KB5 with strong B is a possible gap** (user's decision, 2026-11-01).  Once everything else is finished, review it with the user and decide whether it needs filling or does not seem worthwhile.  Do not start on it before that review.

**Why:** strong B makes arrows unique, so with D the frames are S5's (`Frame.exists_unit_of_serial`) and KDB5 with strong B is read as S5 with strong B.  KB5 with strong B is S5 with strong B or a dead end, so it adds little, while filling it takes the T-off stack: `back_self`, `back_own`, `back_leg`, a `Here` without T (a language extension), and about 9 500 lines redone.

**How to apply:** keep it out of the next-steps list, but raise it at the final review.  The design is in `docs/v12-modal-extensions.md`, "Strong B on KB5 and KDB5", sections 2 to 8.  Related: [[project_qml_current_position]], [[project_qml_scope_cube]].
