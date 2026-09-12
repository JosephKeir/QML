import QML.QML_v12_Interp

/-!
# QML v12 — a model with an empty domain

No domain is required to be nonempty.  Here: one world, no accessible worlds, EMPTY base domain,
and a signature whose only function symbol is unary (so there are no closed base terms).  The
carriers are one-point types, their evaluation maps are forced (there are no accessible worlds),
and the closure laws hold vacuously.

Consequences, checked below: no environment can give a value to a base-typed variable at this
world; `∀y:Var. ⊥` holds there and `∃y:Var. ⊤` fails.
-/

namespace V12

namespace ModelExample

/-- One unary function symbol, no relation symbols. -/
def σ₁ : Signature :=
  { FuncSyms := Unit, RelSyms := Empty, funcArity := fun _ => 1, relArity := Empty.elim }

abbrev frame : Frame.{0} σ₁ where
  W := Unit
  actual := ()
  R := fun _ _ => False
  D := fun _ => Empty
  Nec := fun _ _ => PUnit
  Pos := fun _ _ => PUnit
  funcInterp := fun _ _ args => args ⟨0, Nat.zero_lt_one⟩
  relInterp := fun r => r.elim

abbrev model : Model.{0} σ₁ where
  frame := frame
  necEval := fun _ w' => w'.2.elim
  nec_inj := fun _ => rfl
  posEval := fun _ => ⟨∅, fun w' => w'.1.2.elim⟩
  pos_inj := fun _ => rfl
  ops :=
    { necMap := fun _ _ => PUnit.unit
      necPair := fun _ _ => PUnit.unit
      necUnit := PUnit.unit
      posMap := fun _ _ => PUnit.unit
      posStrength := fun _ _ => PUnit.unit }
  necMap_eval := fun _ _ w' => w'.2.elim
  necPair_eval := fun _ _ w' => w'.2.elim
  posMap_eval := fun _ _ => Sigma.ext rfl (heq_of_eq (funext fun w' => w'.1.2.elim))
  posStrength_eval := fun _ _ => Sigma.ext rfl (heq_of_eq (funext fun w' => w'.1.2.elim))

/-- No environment can give a base-typed variable a value here. -/
example {Γ : Ctx} {v : VarSymb} (h : Γ v = some .Var) (env : model.Env Γ ()) : False :=
  (env v .Var h).elim

/-- The empty context's environment. -/
def env₀ : model.Env Ctx.empty () := fun _ _ h => by cases h

/-- `∀y:Var. ⊥` holds. -/
example : model.sat env₀ (.all .Var .bot : WFF σ₁ Ctx.empty 0) := fun o => o.elim

/-- `∃y:Var. ⊤` fails. -/
example : ¬ model.sat env₀ (.ex .Var .top : WFF σ₁ Ctx.empty 0) := fun ⟨o, _⟩ => o.elim

end ModelExample

end V12
