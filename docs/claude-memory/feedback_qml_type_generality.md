---
name: feedback-qml-type-generality
description: "QML design rule: type-generality is desirable but not always right — equality is base-type-only and better for it; when an operation strips a ◇ from the type, restricting it to ◇-free types costs no expressiveness, because the right move is to NEST the operation"
metadata:
  node_type: memory
  type: feedback
---

**Type-generality is desirable in QML but is not automatically the right move.** Equality is
base-type-only, and that is *better and more elegant* than equality at every type. Before
generalising an operation over `VarType`, ask whether the restriction is a real expressive limit or
only a shape.

**Why:** when the operation itself **strips a `◇`** from the type of the terms it relates, a
restriction to `◇`-free types is not a limitation at all — the right thing is to **nest** the
operation (and to make sure everything is jointly possible in the right way, via pairing:
[[feedback-qml-joint-possibility-pairing]]). `Here s t` is the case in hand: `s : ◇A` and `t : A`, so
the operation peels one `◇`, and a `Here` whose *value* is itself a possible object is not a more
general `Here` — it is an unjoined combination of two possibilities. Talk about a possibility's
possible content *inside its view*, where the content is a witness in its own right, and the
recursion bottoms out at `◇`-free content.

**How to apply:** treat "make it general over all types" as a claim needing justification, not a
default. Check what the operation does to the type: if it descends one constructor, the natural
domain is the types without that constructor, and generality there buys ceremony rather than reach.
The 2026-09 `◇`-equality reform was launched to generalise `Here` to every content type; the single
load-bearing motivation turned out to be exactly the case that should not exist, and the old
base-typed restriction was **principled** rather than a defect of the truth lemma. `WFF.here` now
carries `A.diaFree = true` (with `VarType.diaFree`, `Ann.eq_of_diaFree`), and so do `here_fun`,
`T_dia`, `RealDatum`, `World.realW` and `Model.posRet_exists`
([[project-qml-current-position]]).
