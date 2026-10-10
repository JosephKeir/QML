---
name: feedback-qml-joint-possibility-pairing
description: "QML design rule: anything that asks for JOINT possibility must go through pairing (product types), typically as a hypothesis — if pairing cannot do it, the design is mistaken, not the mechanism"
metadata:
  node_type: memory
  type: feedback
---

In QML, **anything that looks like it is asking for joint possibility must go through pairing**, and
usually by taking a *paired* joint possibility as a **hypothesis** rather than by adding machinery.
Possibilities do not combine: only joint possibilities do, and the joining belongs to the syntax.
Propositional modal logic promotes exactly **one** formula to possible and the rest to necessary; for
formulas the joining device is a connective, and for terms it is the product type. If pairing cannot
express what a proposed principle needs, that is evidence the **principle or design is wrong**, not
that pairing needs supplementing.

**Why:** this is the project's founding analogy — mirror what propositional modal logic does for
formulas, for terms — and it is what made the system work. Devices that link two unjoined
possibilities are exactly what the design excludes: a joint view `◇_{u,v}` contradicts the
one-formula rule, and a pairing *comprehension* (`co-extensive objects are the components of one`)
contradicts the principle that modal domains are free to have elements or lack them, with the only
standing requirement being that the term algebra lifts. "Co-extensive objects are components of one"
is wanted in the **other** direction only: a possible pair *has* co-extensive components. Wanting it
as a hypothesis is wanting a co-extensivity predicate, which duplicates pairing's job.

**How to apply:** when a metatheorem seems to need two witnesses identified, co-extensive, or linked,
stop and ask what the *paired* form of the statement is, and take that as the hypothesis. Do not
reach for a joint modality, a co-extensivity predicate, a comprehension axiom, or a shared-children
construction. The 2026-09 `◇`-equality episode cost days by treating the symptom: a primitive
cross-witness `diaEq` let a maximal theory assert an identity between possibilities nothing had
joined, and every repair violated one of these principles until the atom itself was withdrawn
([[project-qml-current-position]]). Related: [[feedback-qml-type-generality]].
