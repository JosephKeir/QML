# QML: quantified modal logic in Lean 4

A work-in-progress formalisation, in Lean 4 with Mathlib, of a quantified modal logic in which
possible objects are first-class: `◇_x φ` names a witness `x`, and there are modal types (`□A` for
necessary objects, `◇A` for possible ones).  The aim is soundness and completeness for the modal
cube (T, D, B, 4, 5, each in a weak and a strong form), with strong completeness and compactness.

## Status

All of this is research code and still changing.

* **Sound** for every combination of the flags implemented so far.
* **Complete**, with strong completeness and compactness:
  * for every system without B (K, T, D, 4 and 4's strong forms);
  * for B with T and D but without 4, including strong B.
* **Open:** B with 4, and 5 (and so S5).  5 is planned on paper but not yet built.

The current development is `QML/QML_v12m_*.lean` (namespace `V12M`).  Other files in `QML/` are
earlier versions, kept for reference; they contain `sorry`s and warnings.

## Where to look

* `docs/v12-roadmap.md`: what is done and what comes next.
* `docs/v12-modal-extensions.md`: the design, axiom by axiom, with decisions and rejected
  alternatives.
* `docs/v12-arrow-canonical.md`: the arrow-based canonical models.

## Building

The toolchain is pinned in `lean-toolchain`.  From the repository directory:

```
lake exe cache get
lake build QML.QML_v12m_NoBComplete QML.QML_v12m_BCompleteness
```

A plain `lake build` also builds the legacy files, which are noisy.
