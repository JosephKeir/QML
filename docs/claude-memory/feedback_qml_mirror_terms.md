---
name: QML — mirror Term work for WFF
description: When adding/refactoring WFF machinery, closely follow the Term equivalent. Difficulties solved for Term will repeat for WFF.
type: feedback
originSessionId: 82584446-806a-4407-a2ac-aca5e14b84dd
---
For QML (Lean 4 formalisation) work: WFF features should run in close parallel to Term features. The Term layer already solved many termination/elaboration problems; mirroring its structure (measures, mutual block layout, lemma sequences) saves significant iteration.

**Why:** User explicitly noted that "we should expect a close parallel with terms and WFFs throughout, and that means that difficulties which we already encountered and solved for terms will likely repeat for WFFs". When I propose a different design for WFF (e.g. dropping a Term lemma analog because "we might not need it"), I often hit the same wall later that the Term analog was built to handle.

**How to apply:**
- Before designing a WFF refactor, look at the Term version's `termination_by` measure, supporting lemmas, mutual block structure
- Plan the WFF analog as a direct mirror: same measure shape, same lemmas (`diaCount_ctx_ext`, `binderPairDepth_ctx_ext`, `_pairElim_gen`, etc.)
- The asymmetries to call out explicitly: WFF has `.all`/`.ex` quantifier binders that have no Term equivalent — these can introduce pair-typed bindings that Term's diaterm/boxterm wouldn't (because Term modal binders have an `hsub` constraint bounding the inner V). For these arms, factor extra work into helpers (`quant_arm`) — Term doesn't have such helpers because its inline layout works for the Term-specific cases.
- When a refactor seems "too big", check Term — if Term did the same scope refactor previously, it's almost certainly worth doing for WFF the same way rather than inventing a smaller scope that will likely fail later.
