---
name: reference-qml-dia-witness-ctxext
description: QML proof-theory fact — ◇_x formulas are not ctx_ext-form in their witness variable x (□/◇ = ∀/∃ asymmetry)
metadata: 
  node_type: memory
  type: reference
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
---

**QML design fact (correct behaviour, verified conceptually 2026-07-23):** In the `Proof`/WFF
calculus, `□` is universal (names no witness world) so `ctx_ext` commutes with it —
`ctx_ext (□φ) = □(ctx_ext φ)`. But `◇_x φ` (`WFF.dia x hx φ …`) names its witness world via the
variable `x`, which is *genuinely used* (`interpWFF (dia x …)` reads `env x`'s `posEval`
witness). So **`◇_x φ` is NOT `ctx_ext x ψ` for any `x`-free `ψ`** — a context extension adds an
*unused* variable, and `x` here is the witness.

Consequence for proofs (existential converse-Barcan `∃x ◇P(x) ⊢ ◇∃y P(y)`, i.e.
`∃x:◇Var, ◇_x P(x) ⊢ ∃z ◇_z ∃y P(y)` in [[project-qml-lean4]]'s InterestingTheorems.lean): after
`K_dia` you get `◇_x ∃y P(y)`, whose witness world is the *specific* one carried by the
hypothesis's possible-object `x`. To `ex_elim` that `∃x` you need an `x`-free conclusion, so you
must first `ex_intro` (witness `z := x`) to rebind the witness existentially, giving
`∃z ◇_z ∃y P(y)` (= `◇∃y P(y)`, since a "plain ◇" is spelled `∃(witness) ◇_witness`). This extra
`∃`-intro is REAL content ("this specific witness world" → "some witness world"), the modal
analogue of the `ex_elim` eigenvariable side condition — NOT a bug. The box side needs no such
step precisely because `□` has no witness variable. These "witnesses you must existentially
rebind" are the Henkin witnesses of the eventual completeness construction.

**HOW CBF is PROVED (2026-07-24, corrected): `K_dia` (SAME witness x both sides) then `ex_intro` (existentially generalize the witness).** `K_dia` picks ONE witness x appearing identically as `◇_x` in hyp AND conclusion — you can NEVER get different diamonds facing each other. CBF `∃x:◇Var, ◇_x P(x) ⊢ ∃z:◇Var, ◇_z ∃y P(y)`: (1) inner `x,P(x)⊢∃yP(y)`; (2) K_dia → `◇_x P(x) ⊢ ◇_x ∃yP(y)` (same x); (3) `ex_intro` witness:=x → `∃z:◇Var, ◇_z ∃yP(y)` since `(◇_z ∃yP(y))[z:=x]=◇_x ∃yP(y)` (subst renames witness); (4) ex_elim. The RHS `◇_z` is just `◇_x` with witness UN-FIXED (∃z), re-instantiated to x by ex_intro — a QUANTIFIER move, not modal. So `◇_x φ ⊢ ∃z:◇Var, ◇_z φ` (same type) IS provable; `◇_x φ ⊢ ◇_(specific other z) φ` is NOT (can only ∃-generalize the shared witness). Keep z:◇Var → witness is the bare variable x, NO forgetful map / ◇Unit needed (that's a red herring; ◇Unit would need `ex_intro` witness = compound `diaterm ⟨x.1,Var⟩ hx unit…`, strictly harder).

**SEMANTIC note (separate from provability): `R : W→W→Prop` is WORLD-FIXED, not context-relative** — never mentions VarCtx; `ctx_ext` extends the ENV not W/R/D. But the ENV that TRANSPORTS across a modal step is FILTERED: only □-necessary vars survive (via necEval/boxPush) + the ◇-witness gets its value; non-necessary vars of the current world don't exist at the accessible world. ("witness points at world where [boxed-ctx+witness] available" vs "R context-independent" = env-transport-filtered vs R-fixed, NOT contradictory.) World-fixed R makes the `◇Var→◇Unit` downgrade `posIntro ⟨(posEval x).1, unit⟩` sound IN THE FULL MODEL ONLY, but that's NOT how CBF is proved.

**CRITICAL (2026-07-24): the `◇Var→◇Unit` downgrade is NOT valid over GENERAL models — so correctly UNPROVABLE, NO incompleteness.** `∃x:◇Var, ◇_x P(x) ⊢ ∃z:◇Unit, ◇_z ∃yP(y)` is a COVERAGE/FULLNESS principle (cousin of BF): valid in the FULL model (posIntro total) but FALSE in general/faithful models. COUNTER-MODEL: worlds w→{w_x,w_y}; ∃yP(y) TRUE at w_x, FALSE at w_y; `Pos(Var) w` has an UNDENOTABLE x with posEval=⟨w_x,d⟩ (P(d) at w_x); `Pos(Unit) w` (independent designated domain, only denotables forced) contains only units at w_y. LHS holds (via x), RHS fails (no Pos(Unit) elt covers w_x). Since validity = over ALL general models, downgrade INVALID ⟹ unprovable is CORRECT. This VINDICATES general (non-full) models: full-model semantics would make it valid-but-unprovable = real incompleteness; dropping fullness realigns semantics with proof theory (K_dia = one witness). **Earlier "downgrade semantically valid" was WRONG (full-model reasoning).** The HONEST CBF keeps z:◇Var (z:=x, no downgrade) = valid AND provable.
