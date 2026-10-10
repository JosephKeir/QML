---
name: Don't poll build status
description: User dislikes frequent polling of long-running builds — wait for monitor notifications instead
type: feedback
originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
---
Don't repeatedly `tasklist`/`wc -l` a long-running Lean build every few seconds. Waste of the user's attention and my tool budget.

**Why:** Lean builds for `QML_Full_v7.lean` take 10+ minutes; the incremental checks reveal nothing actionable and just create noise.

**How to apply:** After starting a long-running build via `run_in_background` or `Monitor`, wait for the actual completion notification (monitor stream / task-done notification / ScheduleWakeup) before checking again.  If the wait feels long, use the time for planning, code reading, or memory updates — NOT status polling.
