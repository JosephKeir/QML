---
name: project-qml-legacy-tracks
description: "Pointers to memories about superseded QML tracks (v8–v10 files, GModel/RModel semantics, old canonical model, eq-by-extensionality prototype) and a stale tooling note — open only when the user asks about legacy work"
metadata:
  node_type: memory
  type: project
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-10-05T14:35:55.783Z
---

Superseded by the v12/v12m development (`QML/QML_v12m_*`, see [[project-qml-current-position]]).
These memories were moved out of the index on 2026-10-05 to save tokens at every session start.
The files are kept; open them only when the user asks about legacy work.

- [[QML Lean 4 project state]] (`project_qml_lean4.md`): `QML_Full_v8.lean`; converse Barcan
  proven in `InterestingTheorems.lean`; freshness tactic and cast library.
- [[project-qml-semantics]] (`project_qml_semantics.md`): `SemanticsGeneral.lean`/`GModel` (general,
  extensional, not full; BF fails) and `SemanticsEndpoint.lean`/`EModel` (full).
- [[project-qml-rmodel-port]] (`project_qml_rmodel_port.md`): the RModel soundness port in
  `InterpMeta.lean`; the faithfulness stack done; pair-sector `ctx_ext` sorries left.
- [[project-qml-canonical-model]] (`project_qml_canonical_model.md`): the old canonical-model track
  (finitary proofs, Lindenbaum via Zorn), before v12.
- [[reference-qml-eq-by-extensionality]] (`reference_qml_eq_by_extensionality.md`): a prototype
  defining equality via `box_ext`/`dia_ext` (`QML/EqProto.lean`); decision never taken.
  v12 keeps equality base-type only.
- [[qml-modal-axiom-term-rules]] (`project_qml_modal_axiom_term_rules.md`): early T/S4/S5 notes —
  `T` needs a term former and the dual does not.  Realised in v12m as `extract` and `T_dia`/`Here`.
- [[Claude Code VSCode extension rollback]] (`project_vscode_extension_rollback.md`): the user
  rolled back the extension on 2026-05-09 over a bug.  Possibly stale.
