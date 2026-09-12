import QML.QML_v12_LeibnizMain

/-!
# Using Leibniz at a modal type

    x = y  (at □Var, i.e. □(x.box = y.box)),   □P(x.box)   ⊢   □P(y.box)

The formula with the hole is `□P(z.box)`, the hole `z` being the slot `bnd 0`.
-/

namespace V12

namespace LeibnizExample

variable {σ : Signature} (P : {r : σ.RelSyms // σ.relArity r = 1})

abbrev atomP {Γ : Ctx} {d : ℕ} (t : Term σ Γ .Var .var) : WFF σ Γ d := .atom (.eval (.R P) t)

/-- `x y : □Var`, as the free variables 0 and 1. -/
abbrev Γxy : Ctx :=
  (Ctx.empty.insert (.free 0) (.VTypeBox .Var)).insert (.free 1) (.VTypeBox .Var)

def tx : Term σ Γxy (.VTypeBox .Var) (.box .var) :=
  .boxtm (.var (.step (.root (.free 0)) .box) (by decide))

def ty : Term σ Γxy (.VTypeBox .Var) (.box .var) :=
  .boxtm (.var (.step (.root (.free 1)) .box) (by decide))

/-- `□P(z.box)`, the hole `z` at the slot. -/
def φ : WFF σ (Γxy.insert (.bnd 0) (.VTypeBox .Var)) 1 :=
  .box (atomP P (.var (.step (.root (.bnd 0)) .box) (by decide)))

/-- ⭐The derivation: one application of `Proof.leibniz`. -/
def boxLeibniz :
    Proof σ Γxy [eqRec (.VTypeBox .Var) tx ty,
        .box (atomP P (.var (.step (.root (.free 0)) .box) (by decide)))]
      (.box (atomP P (.var (.step (.root (.free 1)) .box) (by decide)))) :=
  Proof.leibniz (φ := φ P) (.VTypeBox .Var) (Proof.lookup List.mem_cons_self)
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))

end LeibnizExample

end V12
