import QML.QML_v12m_Presented

/-!
# QML v12m — a view never re-exposes its own addresses

`Ctx.diaIn x` inherits `Ctx.boxIn` wholesale, so if `x` were *itself* visible in `Γ.boxIn` the view
`Γ.diaIn x` would re-expose `x`, and then the one address `x.dia` would mean two things: the inner
content (the `.dia` branch of `Ctx.diaIn`) and — one level further in — the outer content, inherited
as a `□`-view entry.  That is a **co-naming**, not a co-extension: two addresses may perfectly well
denote the same object, but one address may not stand for two positions.  It is what blocks
abstracting a `◇` view at an arbitrary address (§2d, §9), and only an address of the shape
`VarSymb.inner u` for `u : □◇A` — a *necessarily possible* object's value one view in — can do it.

⭐`Ctx.ViewFresh` says it never happens: nothing visible in the `□` view, nor any extension of it, is
visible in the context.  The intent is that it be closed under exactly the operations a
**presentation** is built from (`CtxExpr`), so that the naming discipline the user already owes
(`Ctx.Presented`) is what rules the collision out, rather than a side condition travelling with the
metatheorems.
-/

namespace V12M

variable [ModalSys]

namespace Ctx

/-- Nothing is visible in the empty context. -/
theorem ref_empty : ∀ v : VarSymb, Ctx.empty.ref v = none
  | .root _ => rfl
  | .step v s => by
      change (if s.isProj then (Ctx.empty.ref v).bind (·.step s) else Ctx.empty (.step v s)) = none
      split_ifs with hs
      · rw [ref_empty v]
        rfl
      · rfl

/-- ⭐Nothing the `□` view makes visible is visible in the context, at any extension: an address
    belongs to one view depth only. -/
def ViewFresh (Γ : Ctx) : Prop :=
  ∀ (v : VarSymb) (p : List Step), Γ.boxIn.ref v ≠ none → Γ.ref (v.ext p) = none

/-- The case the abstraction of a `◇` view needs first: a declared address is not itself a view
    entry, so `Γ.diaIn x` does not re-expose `x`. -/
theorem ViewFresh.not_boxIn {Γ : Ctx} (h : Γ.ViewFresh) {v : VarSymb} {T : VarType}
    (hv : Γ.ref v = some T) : Γ.boxIn.ref v = none := by
  cases hb : Γ.boxIn.ref v with
  | none => rfl
  | some U =>
      exfalso
      have hnone := h v [] (by rw [hb]; exact fun hcon => by cases hcon)
      rw [show VarSymb.ext v [] = v from rfl, hv] at hnone
      cases hnone

/-- And the case `Subst.Coh` needs: no *prefix* of a declared address is a view entry either, so
    extending a view entry never reaches the content. -/
theorem ViewFresh.not_prefix {Γ : Ctx} (h : Γ.ViewFresh) {v w : VarSymb} {T : VarType}
    (p : List Step) (hvw : w = v.ext p) (hw : Γ.ref w = some T) : Γ.boxIn.ref v = none := by
  cases hb : Γ.boxIn.ref v with
  | none => rfl
  | some U =>
      exfalso
      have hnone := h v p (by rw [hb]; exact fun hcon => by cases hcon)
      rw [← hvw, hw] at hnone
      cases hnone

theorem viewFresh_empty : Ctx.ViewFresh Ctx.empty :=
  fun v p _ => ref_empty (v.ext p)

end Ctx

end V12M
