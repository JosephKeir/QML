---
name: project-qml-opt-review
description: 2026-11-14 high-level review of the Opt programme — verdict per system, risks, recommended reordering (gate before tree); full text in docs/v12-opt-review.md
metadata:
  type: project
---

Review written 2026-11-14 at the user's request (docs/v12-opt-review.md). Verdict: K, D, T, 4 with
◇⁰/◇⁰ᵀ should work incl. cut elimination + Craig (relation symbols); B (⟪back⟫) and 5 (side view)
are open research on the calculus side; deleting shapes needs all of them.

Key points: (1) M3 (GK with ◇⁰: cut elim, Maehara) is the gate and is syntactic, so test it BEFORE
the KT tree — proposed order: Here rules → model class with Opt (Ind := Eq, shaped off with Opt) →
GK+◇⁰ for K/D → GKT → KT tree. (2) No higher-type equality rule needed in GK (◇-terms dissolve
under substitution; ≡ defined) — the plan's best feature. (3) Strong forms are non-geometric
existence rules: scope cut elimination to weak forms unless decided. (4) "Converse in the formulas"
does not by itself give B a cut-free calculus (Kt needs nested/display). (5) Design one `home`
mechanism for wit/⟪back⟫/side. (6) Define fallbacks (tree systems only; + B without calculus).
(7) Watch vacuity from NoOpt/NoT gating; keep a per-system table of Opt-on results.

**Why:** the user asked whether the whole plan will work and for risks in the notes.
**How to apply:** consult before planning M3–M4; the reordering was AGREED by the user 2026-11-14.
See [[project-qml-opt-end-state]], [[project-qml-current-position]], [[feedback-qml-operators-over-relations]].
