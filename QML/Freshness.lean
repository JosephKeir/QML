import QML.QML_Full_v8

/-!
# `freshness` — automation for context-membership side conditions

Discharges the pervasive `v ∉ VarCtx_to_VarSymbs V` freshness side conditions
(on `VarCtx_insert` / `ctx_ext` / binders) with `aesop`:

* `not_mem_VarSymbs_insert` peels a `VarCtx_insert` layer
  (`v ∉ insert x V` ↦ `v ≠ x.1` and `v ∉ V`),
* `Ne.symm` closes `≠` subgoals that only match a hypothesis up to symmetry
  (the `fun h => hxy h.symm` case),
* `≠` and base goals are closed from local hypotheses.

Register your base-context freshness facts with an `aesop` tag so `freshness`
sees them, e.g. `attribute [aesop safe apply] not_in_empty_VarCtx`.
-/

/-- Discharge `v ∉ VarCtx_to_VarSymbs V` freshness side conditions. -/
macro "freshness" : tactic =>
  `(tactic| aesop (add safe apply not_mem_VarSymbs_insert, safe apply Ne.symm))
