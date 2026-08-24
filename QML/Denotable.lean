import QML.SemanticsEndpoint

/-!
# Denotable domains — the free (inductive) construction

The denotable objects at each modality, built by **closure over existing objects** — the
inductive core of the term model, and the "subdomain of denotable objects" a general model is
required to contain (`NecD ↪ Nec`).  This is *inclusive*-logic-native: a world with no closed
terms simply gets an empty denotable domain, no special-casing.

This file lays the base stone: the **`□Var` fragment** — denotable *necessary individuals*.
They are freely generated from
* **atoms** — the given generators (a `□Var`-variable's value, or an undenotable object we
  choose to include), each carrying its section; and
* the **function-symbol lifts** (`liftNec` of `funcInterp`, worldwise).

`necEval` reads a denotable necessary individual back to its section, by recursion.  The full
`NecD`/`PosD` extend this with the same shape at products, `◇` (`PosD`, witness-generated) and
nested modalities — more constructors, same `atoms + lifts + eval-by-recursion` skeleton, with
`D` (individuals) as the level-`Var` base already supplied by `funcInterp`'s totality.
-/

universe u

namespace EModel

variable {σ : Signature}

/-- Denotable necessary individuals over a frame, freely generated from a family of atoms by
    the function-symbol lifts.  (The `□Var` fragment of `NecD`.) -/
inductive NecInd (M : EModel σ) (Atom : M.W → Type u) : M.W → Type u where
  /-- A generator: a given necessary individual (a `□Var`-variable, or a chosen extra). -/
  | atom : {w : M.W} → Atom w → NecInd M Atom w
  /-- Lift a function symbol worldwise over already-built necessary individuals. -/
  | func : {w : M.W} → (f : σ.FuncSyms) →
      (Fin (σ.funcArity f) → NecInd M Atom w) → NecInd M Atom w

/-- Read a denotable necessary individual back to its section, given the atoms' sections.
    Functions are applied worldwise — `necEval` is a σ-homomorphism by construction. -/
def NecInd.necEval {M : EModel σ} {Atom : M.W → Type u}
    (atomEval : {w : M.W} → Atom w → (w' : {w' : M.W // M.R w w'}) → M.D w'.1)
    {w : M.W} : NecInd M Atom w → (w' : {w' : M.W // M.R w w'}) → M.D w'.1
  | .atom a,    w' => atomEval a w'
  | .func f ns, w' => M.funcInterp f w'.1 (fun i => NecInd.necEval atomEval (ns i) w')

/-- `necEval` really is a σ-homomorphism (the `func`-clause, made explicit). -/
theorem NecInd.necEval_func {M : EModel σ} {Atom : M.W → Type u}
    (atomEval : {w : M.W} → Atom w → (w' : {w' : M.W // M.R w w'}) → M.D w'.1)
    {w : M.W} (f : σ.FuncSyms) (ns : Fin (σ.funcArity f) → NecInd M Atom w)
    (w' : {w' : M.W // M.R w w'}) :
    NecInd.necEval atomEval (.func f ns) w'
      = M.funcInterp f w'.1 (fun i => NecInd.necEval atomEval (ns i) w') := rfl

end EModel
