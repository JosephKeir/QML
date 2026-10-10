---
name: qml-lake-cwd-and-toolchain
description: Run lake from the QML repo directory; never use lake --dir (elan takes the toolchain from cwd)
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-09-17T11:11:08.414Z
---

Since 2026-09-18 the user opens `C:\Users\Joseph Keir\Lean4Projects\QML` as the VS Code workspace,
so the session starts in the repo and plain `lake build <target>` works (verified: `lean --version`
resolves the pinned 4.28.0). Before that, sessions started in the home folder and the working
directory kept drifting there, which is why older notes prefix `Set-Location`. If a session ever
starts outside the repo again, `Set-Location` into it first and suggest reopening the folder as the
workspace — memories are keyed to the workspace, so a home-rooted session will not see these.

**Never use `lake --dir=<project>` as a substitute.** elan resolves the Lean toolchain from the
*current directory's* `lean-toolchain`, not lake's project root. From the home folder `--dir` ignored
the pin, resolved to v4.34.0, downloaded and installed it unprompted, and began recompiling
batteries/mathlib into `.lake/packages` before failing. A build from inside the repo repaired the
artefacts. An unwanted v4.34.0 toolchain may remain in `.elan`
(`elan toolchain uninstall leanprover--lean4---v4.34.0`) — ask before removing, other projects may use it.

**Why:** only the process's cwd controls elan's toolchain resolution.

**How to apply:** run lake from the repo; check `Get-Location` if a build behaves oddly. The old
home-keyed memory directory `C--Users-Joseph-Keir` is now a stale copy — write memories here.
