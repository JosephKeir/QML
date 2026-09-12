import QML.QML_v12_Proof

/-!
# The converse Barcan formula, universal form, in v12

    □ ∀y:Var. P(y)   ⊢   ∀x:□Var. □ P(x.box)

A variable declared OUTSIDE a `□` is visible inside it only through its content: `x : □Var`
outside, its content `x.box : Var` inside.

`P` is a unary relation symbol of the signature, so it can be used in any context.
-/

namespace V12

namespace ConverseBarcan

variable {σ : Signature} (P : {r : σ.RelSyms // σ.relArity r = 1})

/-- The atom `P t`. -/
abbrev atomP {Γ : Ctx} {d : ℕ} (t : Term σ Γ .Var .var) : WFF σ Γ d := .atom (.eval (.R P) t)

/-- The hypothesis `□ ∀y:Var. P(y)`.  The bound `y` is the slot `bnd 0`, declared inside the `□`. -/
def hyp : WFF σ Ctx.empty 0 :=
  .box (.all .Var (atomP P (.var (.root (.bnd 0)) (by decide))))

/-- The conclusion `∀x:□Var. □ P(x.box)`.  The bound `x` is the slot `bnd 0`, declared outside
    the `□`, so inside it appears as its content `x.box`. -/
def conc : WFF σ Ctx.empty 0 :=
  .all (.VTypeBox .Var) (.box (atomP P (.var (.step (.root (.bnd 0)) .box) (by decide))))

/-- ⭐The derivation. -/
def converseBarcanUniversal : Proof σ Ctx.empty [hyp P] (conc P) := by
  -- ∀-introduction.  The eigenvariable is the free variable `u := free 0` of type `□Var`;
  -- the new goal is `□ P(u.box)` over the context `u : □Var`.
  refine Proof.all_intro 0 (.VTypeBox .Var) (by fresh)
    (φ := .box (atomP P (.var (.step (.root (.free 0)) .box) (by decide)))) ?_
  -- K□.  Strip the box from the hypothesis `□ ∀y. P(y)` and from the goal `□ P(u.box)`;
  -- inside, `u.box : Var` is visible.
  refine Proof.K_box (Δ := [.all .Var (atomP P (.var (.root (.bnd 0)) (by decide)))]) ?_
  -- ∀-elimination at `y := u.box`.
  exact Proof.all_elim (Γ := (Ctx.empty.insert (.free 0) (.VTypeBox .Var)).boxIn) .Var
    (.var (.step (.root (.free 0)) .box) (by decide)) (Proof.ax _)

end ConverseBarcan

end V12
