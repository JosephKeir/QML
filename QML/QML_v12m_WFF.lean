import QML.QML_v12m_Terms

/-!
# QML v12m — formulas

`WFF σ Γ d`: a formula over `Γ` at binder depth `d`.  A quantifier ranges over a plain type and
binds the slot `bnd d`.  Modal formulas use the pointwise views.  Base equality is primitive;
equality at every type is DEFINED by extensionality (`eqRec`), between terms of the same annotated
type — which forces the same witnesses and the same inner contexts, so no casts are needed.
-/

namespace V12M

variable [ModalSys]

set_option inductive.autoPromoteIndices false in
inductive Rel (σ : Signature) : Ctx → ℕ → Type where
  | R {Γ : Ctx} {n : ℕ} (r : {r : σ.RelSyms // σ.relArity r = n}) : Rel σ Γ n
  | eval {Γ : Ctx} {n : ℕ} : Rel σ Γ (n + 1) → Term σ Γ .Var .var → Rel σ Γ n
deriving DecidableEq

inductive WFF (σ : Signature) : Ctx → ℕ → Type where
  | atom {Γ : Ctx} {d : ℕ} : Rel σ Γ 0 → WFF σ Γ d
  | eq {Γ : Ctx} {d : ℕ} : Term σ Γ .Var .var → Term σ Γ .Var .var → WFF σ Γ d
  | top {Γ : Ctx} {d : ℕ} : WFF σ Γ d
  | bot {Γ : Ctx} {d : ℕ} : WFF σ Γ d
  | and {Γ : Ctx} {d : ℕ} : WFF σ Γ d → WFF σ Γ d → WFF σ Γ d
  | or {Γ : Ctx} {d : ℕ} : WFF σ Γ d → WFF σ Γ d → WFF σ Γ d
  | imp {Γ : Ctx} {d : ℕ} : WFF σ Γ d → WFF σ Γ d → WFF σ Γ d
  | all {Γ : Ctx} {d : ℕ} (T : VarType) : WFF σ (Γ.insert (.bnd d) T) (d + 1) → WFF σ Γ d
  | ex {Γ : Ctx} {d : ℕ} (T : VarType) : WFF σ (Γ.insert (.bnd d) T) (d + 1) → WFF σ Γ d
  | box {Γ : Ctx} {d : ℕ} : WFF σ Γ.boxIn d → WFF σ Γ d
  /-- `◇_x φ`: `x : ◇X` outside, its content `x.dia : X` inside. -/
  | dia {Γ : Ctx} {d : ℕ} (x : VarSymb) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
      WFF σ (Γ.diaIn x) d → WFF σ Γ d
deriving DecidableEq

abbrev WFF.neg {σ : Signature} {Γ : Ctx} {d : ℕ} (φ : WFF σ Γ d) : WFF σ Γ d := .imp φ .bot

/-- `□_x φ := ¬◇_x¬φ`. -/
abbrev WFF.boxx {σ : Signature} {Γ : Ctx} {d : ℕ} (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (φ : WFF σ (Γ.diaIn x) d) : WFF σ Γ d :=
  (WFF.dia x hx φ.neg).neg

/-- ⭐Equality at every type, by extensionality.  Same annotation ⇒ same witness and same inner
    context, definitionally: no casts, no unreachable branches. -/
def eqRec {σ : Signature} {d : ℕ} : {Γ : Ctx} → (T : VarType) → {a : Ann T} →
    Term σ Γ T a → Term σ Γ T a → WFF σ Γ d
  | _, .Var, .var, t, s => .eq t s
  | _, .VTypeOne, _, _, _ => .top
  | _, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => .and (eqRec A t₁ s₁) (eqRec B t₂ s₂)
  | _, .VTypeBox A, .box _, .boxtm t, .boxtm s => .box (eqRec A t s)
  | _, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s => .boxx x hx (eqRec A t s)

/-! ## Weakening -/

def Rel.mono {σ : Signature} {Γ Γ' : Ctx} (h : Γ.Le Γ') : {n : ℕ} → Rel σ Γ n → Rel σ Γ' n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.mono h ρ) (Term.mono h t)

def WFF.mono {σ : Signature} : {Γ Γ' : Ctx} → {d : ℕ} → Γ.Le Γ' → WFF σ Γ d → WFF σ Γ' d
  | _, _, _, h, .atom ρ => .atom (Rel.mono h ρ)
  | _, _, _, h, .eq t s => .eq (Term.mono h t) (Term.mono h s)
  | _, _, _, _, .top => .top
  | _, _, _, _, .bot => .bot
  | _, _, _, h, .and φ ψ => .and (WFF.mono h φ) (WFF.mono h ψ)
  | _, _, _, h, .or φ ψ => .or (WFF.mono h φ) (WFF.mono h ψ)
  | _, _, _, h, .imp φ ψ => .imp (WFF.mono h φ) (WFF.mono h ψ)
  | _, _, _, h, .all T φ => .all T (WFF.mono (h.insert _ T) φ)
  | _, _, _, h, .ex T φ => .ex T (WFF.mono (h.insert _ T) φ)
  | _, _, _, h, .box φ => .box (WFF.mono h.boxIn φ)
  | _, _, _, h, .dia x hx φ => .dia x (hx.imp fun _ hX => h.ref hX) (WFF.mono (h.diaIn x) φ)

/-- Weakening by a fresh root. -/
def WFF.weaken {σ : Signature} {Γ : Ctx} {d : ℕ} {r : Root} (hr : Γ (.root r) = none)
    (T : VarType) (φ : WFF σ Γ d) : WFF σ (Γ.insert r T) d :=
  WFF.mono (Ctx.le_insert hr T) φ

end V12M
