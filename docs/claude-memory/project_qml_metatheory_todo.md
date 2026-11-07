---
name: qml-metatheory-todo
description: "Metatheorems to prove after completeness work — strong completeness/compactness, generalisation on constants, uniform substitution, cut elimination, Craig interpolation"
metadata: 
  node_type: memory
  type: project
  originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
  modified: 2026-09-17T12:52:51.616Z
---

Theorems the user wants proved eventually, **after the entire modal cube is finished** (user,
2026-10-03: "most of the metatheory stuff can probably wait until the entire cube is finished"; strong
completeness and compactness are already done per system).  Order: docs/v12-roadmap.md. Full notes are in the repo at `docs/v12-metatheory-todo.md`; read that
before starting any of them.

1. **Strong completeness and compactness** — nearly free: `Theory.Derives` is already finitary and
   `World.ofHenkin` takes arbitrary sets.
2. **Generalisation on constants** (done for DECLARED VARIABLES 2026-11-06, `Proof.genVar`; for constants = nullary function symbols OPEN: generalising promoted `□ᵏ f` to `x : □ᵏ Var` FAILS with T, 4, strong B (counterexamples in the repo doc, item 2), should hold in K/D/weak B; user has a proof-theoretic proof in mind for K; later find a way to state 'depends only on the end points') — replace a declared constant by a same-typed eigenvariable and
   bind it; the declaration cannot be dropped (no non-empty domains).
3. **Uniform substitution** — the substituted formula may use only the atom's own indices.
4. **Cut elimination** (added 2026-09-18) — user already has the sequent calculus in mind; ND is close
   to a sequent system. May hold only for K; S5 classically needs hypersequents or similar.
5. **Craig interpolation** (added 2026-09-18) — holds for propositional K/T/S4/S5 but fails for many
   *quantified* modal logics (Fine 1979, first-order S5 with constant domains). Would be a notable
   result here because the system makes possible objects expressible. Likely needs item 4.
7. **Proof-theoretic versions of the semantic corollaries** (added 2026-11-06): Leibniz at every
   type and uniform substitution, done semantically for the cube in `QML_v12m_SemAdmissible`
   (`leibnizCube`, `usubstCube`, built 2026-11-07); the
   proof-theoretic versions (every flag, K5/KD5 included) go in `QML_v12m_ProofAdmissible`.
   Generalisation on declared variables is already proof-theoretic there (`Proof.genVar`).
4b. **Cut elimination for K: CUT ADMISSIBLE IN GK, BUILT 2026-11-07** (QML_v12m_GK, GKSubst, GKCut: GK.cut sorry-free; next the ND <-> GK equivalence, then subformula property, interpolation) (docs item 4): GK = G3c (Kleene style, principal formulas retained, membership contexts), equality Ref/Repl on ATOMS (user agreed), the user's symmetric K rules (◇ and □_x are notation), pair_elim/weak_ctx not primitive; all reductions checked on paper, none fails; 4 500-7 000 lines; next: build. User's aim: subformula property, then interpolation; K only.
6. **`T_dia∀` ⇔ positive-Φ rule** (added 2026-09-18; SET ASIDE by the user 2026-11-07: `T_dia∀` is no longer the rule, the `Here`-atom `T_dia` with `here_intro`/`here_elim` is natural itself, so the motivation is gone) — Lean keeps `T_dia∀`; the paper states "from
   `Φ⟨x:=t⟩` and `c:◇A; Φ(c) ⊢ φ` infer `φ`", `Φ` positive in `x`. Prove the equivalence in Lean
   once strong-T completeness is done.

**Why:** the user wants the system's proof theory, not just soundness/completeness, and these are the
selling points for a write-up.

**How to apply:** don't start these before the extension completeness work is done unless asked; when
one comes up, read the repo doc first and keep it updated rather than this file. See
[[qml-v12-semantics]] and [[qml-roadmap]].
