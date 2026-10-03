# QML — quantified modal logic in Lean 4

Lean 4 + Mathlib formalisation of a quantified modal logic with first-class possible objects
(`◇_x` with named witnesses) and modal types. Toolchain pinned in `lean-toolchain` (v4.28.0).

## Where things are

- **Current development: `QML/QML_v12m_*.lean`, namespace `V12M`.** Generalised over
  `class ModalSys` (flags `T`, `Four`, `TStrong`, `D`, `DStrong`, `B`, `BStrong`; used
  as `variable [ModalSys]`). Frames are arrow-indexed (`Frame.R : W → W → Sort v`; relational frames
  are the `Prop` case). Soundness holds for every flag; completeness, strong completeness and
  compactness for every flag combination without B (`[ModalSys.NoB]`). Weak B with 4 off
  (`[ModalSys.NoFour]`; T and D in either strength allowed; for now `NoFour` also
  turns strong B off) is complete for **every presented context** with a fresh presentation
  (`BArrow.completenessB_presented`), with strong completeness and compactness
  (`BArrow.strong_completenessB`, `BArrow.compactnessB`), via the arrow-based canonical model
  (`QML_v12m_B*.lean`: network construction, `BData`, truth lemma, `BFlat` for flattening a
  presentation).
- `QML/QML_v12_*.lean` (namespace `V12`) is the K-only version, kept untouched until the
  generalised files supersede it.
- Older files (`QML_Full_v8.lean`, `Soundness2.lean`, `SemanticsGeneral2.lean`, …) are legacy and
  carry their own sorries and warnings; ignore them unless asked.
- **Roadmap: `docs/v12-roadmap.md`** — what is done and the order of work; start there.
- Design notes: `docs/v12-modal-extensions.md` (per-axiom design, status, decisions and rejected
  alternatives — read before changing modal machinery), `docs/v12-arrow-canonical.md` (draft:
  the arrow-based canonical model proposed for B and 5) and `docs/v12-metatheory-todo.md`.

## Standing constraints

- **Never modify, stage or commit `QML/InterestingTheoremsv12.lean`** — it is the user's own
  untracked work.
- **Presented contexts are the real ones.** State metatheorems for `Ctx.Presented`; extra
  generality is a bonus, not a goal.
- **Prefer admissibility to new proof rules.** Add a rule only when an axiom genuinely needs one.
- Keep `QML_v12m_*` sorry-free. If a `sorry` is unavoidable mid-task, say so and record it in the
  docs; never leave one unreported.
- Commit only when asked. Commit messages end with
  `Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>`.

## Building

- Run `lake build <module>` (e.g. `lake build QML.QML_v12m_Soundness`) **from the repo directory**.
- **Never `lake --dir=...`**: elan picks the toolchain from the current directory, so from elsewhere
  it downloads the wrong Lean and recompiles dependencies into `.lake/packages`.
- A full `lake build` also rebuilds the noisy legacy files; prefer a targeted module. Background
  build logs can be truncated at the front — confirm v12m results with a targeted build, per-file
  diagnostics, or a source `grep` for `sorry`, not from a filtered log.

## Conventions

- Mirror an existing construction when building a parallel one (e.g. `Term.realise` follows
  `Term.collapse`; WFF machinery follows the `Term` version) — it avoids rediscovering the same
  termination and elaboration problems.
- Addresses (`VarSymb`) are a root plus steps, innermost step last; projections (`fst`, `snd`,
  `here`) versus level steps (`box`, `dia`, `keep`). Views: `Γ.boxIn`, `Γ.diaIn x`.
- Lines are limited to 100 characters (linter).
