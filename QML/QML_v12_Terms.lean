import QML.QML_v12_Symbols

/-!
# QML v12 — terms

Terms are typed intrinsically by a plain type and its witness annotation.  Only base-typed
addresses are terms; modal, pair and unit terms are built by their constructors.  Annotations are
plain constructor applications (`boxtm : … → Term σ Γ (□A) (.box a)`), so `DecidableEq` derives.
-/

namespace V12

structure Signature where
  FuncSyms : Type
  RelSyms : Type
  funcArity : FuncSyms → ℕ
  relArity : RelSyms → ℕ
  [decEqF : DecidableEq FuncSyms]
  [decEqR : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

mutual
  inductive Func (σ : Signature) : Ctx → ℕ → Type where
    | F {Γ : Ctx} {n : ℕ} (f : {f : σ.FuncSyms // σ.funcArity f = n}) : Func σ Γ n
    | eval {Γ : Ctx} {n : ℕ} : Func σ Γ (n + 1) → Term σ Γ .Var .var → Func σ Γ n
  deriving DecidableEq

  inductive Term (σ : Signature) : Ctx → (T : VarType) → Ann T → Type where
    | var {Γ : Ctx} (v : VarSymb) (h : Γ.ref v = some .Var) : Term σ Γ .Var .var
    | func {Γ : Ctx} : Func σ Γ 0 → Term σ Γ .Var .var
    | unit {Γ : Ctx} : Term σ Γ .VTypeOne .one
    | pair {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B} :
        Term σ Γ A a → Term σ Γ B b → Term σ Γ (.VTypeProd A B) (.prod a b)
    | boxtm {Γ : Ctx} {A : VarType} {a : Ann A} :
        Term σ Γ.boxIn A a → Term σ Γ (.VTypeBox A) (.box a)
    /-- `x` is the promoted witness: `x : ◇X` outside, its content `x.dia : X` inside. -/
    | diatm {Γ : Ctx} {A : VarType} {a : Ann A} (x : VarSymb)
        (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
        Term σ (Γ.diaIn x) A a → Term σ Γ (.VTypeDia A) (.dia x a)
  deriving DecidableEq
end

/-! ## Weakening -/

mutual
  def Func.mono {σ : Signature} : {Γ Γ' : Ctx} → Γ.Le Γ' → {n : ℕ} → Func σ Γ n → Func σ Γ' n
    | _, _, _, _, .F f => .F f
    | _, _, h, _, .eval g t => .eval (Func.mono h g) (Term.mono h t)

  /-- ⭐Moving to a context with more visible positions: annotations untouched. -/
  def Term.mono {σ : Signature} : {Γ Γ' : Ctx} → Γ.Le Γ' → {T : VarType} → {a : Ann T} →
      Term σ Γ T a → Term σ Γ' T a
    | _, _, h, _, _, .var v hv => .var v (h.ref hv)
    | _, _, h, _, _, .func f => .func (Func.mono h f)
    | _, _, _, _, _, .unit => .unit
    | _, _, h, _, _, .pair s t => .pair (Term.mono h s) (Term.mono h t)
    | _, _, h, _, _, .boxtm t => .boxtm (Term.mono h.boxIn t)
    | _, _, h, _, _, .diatm x hx t =>
        .diatm x (hx.imp fun _ hX => h.ref hX) (Term.mono (h.diaIn x) t)
end

/-- Weakening by a fresh root. -/
def Term.weaken {σ : Signature} {Γ : Ctx} {r : Root} (hr : Γ (.root r) = none) (T : VarType)
    {S : VarType} {a : Ann S} (t : Term σ Γ S a) : Term σ (Γ.insert r T) S a :=
  Term.mono (Ctx.le_insert hr T) t

end V12
