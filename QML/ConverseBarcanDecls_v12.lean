import QML.QML_v12_Proof

/-!
# Converse Barcan in a presented context

With a declared variable `y : □Var` (the free variable 0):

    y : □Var  ;  □ ∀x:Var. R(x, y.box)   ⊢   ∀x:□Var. □ R(x.box, y.box)

The context is given by a finite declaration list, so the eigenvariable's freshness is checked
from the presentation (`by fresh`).
-/

namespace V12

namespace ConverseBarcanDecls

variable {σ : Signature} (R : {r : σ.RelSyms // σ.relArity r = 2})

abbrev atomR {Γ : Ctx} {d : ℕ} (t₁ t₂ : Term σ Γ .Var .var) : WFF σ Γ d :=
  .atom (.eval (.eval (.R R) t₁) t₂)

/-- `y : □Var`. -/
abbrev Γy : Ctx := Ctx.ofDecls [(0, .VTypeBox .Var)]

def hyp : WFF σ Γy 0 :=
  .box (.all .Var (atomR R (.var (.root (.bnd 0)) (by decide))
    (.var (.step (.root (.free 0)) .box) (by decide))))

def conc : WFF σ Γy 0 :=
  .all (.VTypeBox .Var) (.box (atomR R (.var (.step (.root (.bnd 0)) .box) (by decide))
    (.var (.step (.root (.free 0)) .box) (by decide))))

def converseBarcan : Proof σ Γy [hyp R] (conc R) := by
  -- ∀-introduction with the eigenvariable `u := free 1`, fresh beyond the declarations.
  refine Proof.all_intro (Γ := Γy) 1 (.VTypeBox .Var) (by fresh)
    (φ := .box (atomR R (.var (.step (.root (.free 1)) .box) (by decide))
      (.var (.step (.root (.free 0)) .box) (by decide)))) ?_
  -- K□.
  refine Proof.K_box (Δ := [.all .Var (atomR R (.var (.root (.bnd 0)) (by decide))
    (.var (.step (.root (.free 0)) .box) (by decide)))]) ?_
  -- ∀-elimination at `x := u.box`.
  exact Proof.all_elim (Γ := (Γy.insert (.free 1) (.VTypeBox .Var)).boxIn) .Var
    (.var (.step (.root (.free 1)) .box) (by decide)) (Proof.ax _)

end ConverseBarcanDecls

end V12
