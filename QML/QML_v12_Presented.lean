import QML.QML_v12_Symbols

/-!
# QML v12 — presented contexts

Contexts are partial functions on addresses, which is what the machinery wants.  But a function
can declare infinitely many roots (no fresh eigenvariables), or make addresses visible that no
declaration produces.  A **presentation** rules both out: an expression built from the empty
context by declaring free variables and taking modal views, whose denotation is the context.

* `Ctx.Presented Γ` carries the expression as data, so fresh names are computed from it
  (`Ctx.Presented.bound`, `Ctx.Presented.fresh`).  It also gives `Ctx.NoSlots`.
* Instances follow the proof rules: the empty context, declaring a free variable, `□` and `◇_x`
  views.
* `Ctx.ofDecls` builds a context from a finite list of declarations `(u, T)`; the head of the list
  is declared last, so it wins on a repeated name.
-/

namespace V12

/-- How a proof context is built. -/
inductive CtxExpr where
  | empty
  | insertFree (e : CtxExpr) (u : ℕ) (T : VarType)
  | boxIn (e : CtxExpr)
  | diaIn (e : CtxExpr) (x : VarSymb)

namespace CtxExpr

def denote : CtxExpr → Ctx
  | .empty => Ctx.empty
  | .insertFree e u T => e.denote.insert (.free u) T
  | .boxIn e => e.denote.boxIn
  | .diaIn e x => e.denote.diaIn x

/-- Every free variable from here on is unused. -/
def freeBound : CtxExpr → ℕ
  | .empty => 0
  | .insertFree e u _ => max e.freeBound (u + 1)
  | .boxIn e => e.freeBound
  | .diaIn e _ => e.freeBound

theorem fresh : ∀ (e : CtxExpr) (n : ℕ), e.freeBound ≤ n → e.denote.RootFresh (.free n)
  | .empty, _, _ => Ctx.RootFresh.empty _
  | .insertFree e u T, n, hn =>
      (fresh e n (Nat.max_le.mp hn).1).insert_ne
        (fun he => by
          cases he
          exact absurd (Nat.max_le.mp hn).2 (Nat.not_succ_le_self _)) T
  | .boxIn e, n, hn => (fresh e n hn).boxIn
  | .diaIn e x, n, hn => (fresh e n hn).diaIn x

theorem slots : ∀ (e : CtxExpr), e.denote.SlotsFrom 0
  | .empty => fun _ _ _ _ => rfl
  | .insertFree e u T => (slots e).insertFree u T
  | .boxIn e => (slots e).boxIn
  | .diaIn e x => (slots e).diaIn x

end CtxExpr

/-- ⭐A presentation of the context: found by instance search. -/
class Ctx.Presented (Γ : Ctx) where
  expr : CtxExpr
  denote_eq : expr.denote = Γ

namespace Ctx.Presented

/-- The first free variable guaranteed unused. -/
def bound (Γ : Ctx) [h : Γ.Presented] : ℕ := h.expr.freeBound

theorem fresh {Γ : Ctx} [h : Γ.Presented] (n : ℕ) (hn : bound Γ ≤ n) :
    Γ.RootFresh (.free n) :=
  h.denote_eq ▸ h.expr.fresh n hn

end Ctx.Presented

instance : Ctx.empty.Presented := ⟨.empty, rfl⟩

instance {Γ : Ctx} [h : Γ.Presented] {u : ℕ} {T : VarType} :
    (Γ.insert (.free u) T).Presented :=
  ⟨.insertFree h.expr u T, congrArg (fun Δ => Ctx.insert Δ (.free u) T) h.denote_eq⟩

instance {Γ : Ctx} [h : Γ.Presented] : Γ.boxIn.Presented :=
  ⟨.boxIn h.expr, congrArg Ctx.boxIn h.denote_eq⟩

instance {Γ : Ctx} [h : Γ.Presented] {x : VarSymb} : (Γ.diaIn x).Presented :=
  ⟨.diaIn h.expr x, congrArg (fun Δ => Ctx.diaIn Δ x) h.denote_eq⟩

instance (priority := low) {Γ : Ctx} [h : Γ.Presented] : Γ.NoSlots :=
  ⟨h.denote_eq ▸ h.expr.slots⟩

/-! ## Contexts from finite declaration lists -/

/-- Declare the free variables of a finite list; the head is declared last. -/
def Ctx.ofDecls : List (ℕ × VarType) → Ctx
  | [] => Ctx.empty
  | (u, T) :: ds => (Ctx.ofDecls ds).insert (.free u) T

def CtxExpr.ofDecls : List (ℕ × VarType) → CtxExpr
  | [] => .empty
  | (u, T) :: ds => .insertFree (CtxExpr.ofDecls ds) u T

theorem CtxExpr.denote_ofDecls : ∀ ds, (CtxExpr.ofDecls ds).denote = Ctx.ofDecls ds
  | [] => rfl
  | (u, T) :: ds => congrArg (fun Δ => Ctx.insert Δ (.free u) T) (denote_ofDecls ds)

instance (ds : List (ℕ × VarType)) : (Ctx.ofDecls ds).Presented :=
  ⟨CtxExpr.ofDecls ds, CtxExpr.denote_ofDecls ds⟩

/-! ## Checks -/

example : (Ctx.ofDecls [(3, .Var), (0, .VTypeBox .Var)]).boxIn.NoSlots := inferInstance

example : Ctx.Presented.bound ((Ctx.ofDecls [(3, .Var), (0, .VTypeBox .Var)]).boxIn) = 4 := rfl

end V12
