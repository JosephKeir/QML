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
  /-- `Here s t`: the possible object `s` is realised at this world, with value `t` (T only).

      Two restrictions, each for a reason:
      * its subject is a **term** of `◇`-type, not a witness address, so that substitution can act
        on it — sending a witness to a `diatm` term would otherwise break the tie between the
        term's type and the witness's content type;
      * it is primitive only at **base type**, as `WFF.eq` is.  The value names the content, so the
        two carry different annotations, and `eqRec` — equality at every type — compares only terms
        of the *same* annotation.  So at a compound content type there is no formula saying that the
        content is `t`, and the canonical model could not decide one. -/
  | here {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true) {b : Ann (.VTypeDia .Var)}
      (s : Term σ Γ (.VTypeDia .Var) b) (t : Term σ Γ .Var .var) : WFF σ Γ d
  /-- `s ≐ s'`: two `◇`-terms of the same **type** denote the same possible object — their
      annotations may differ, and that is the whole point.  An annotation of a fixed type can vary
      only in its `.dia` witness indices, everything else being forced by the type, so "same type,
      different annotation" *is* "different witness", and this is exactly the equality the `◇`-types
      lack (§2d).  Annotation-free equality at the other types is then definable from it: `×`
      componentwise, `□` inside a `□`, `Var`/`𝟙` as `eqRec` already does.

      Its subjects are **terms**, not addresses, for the reason `WFF.here`'s subject is: a
      substitution sends a `◇`-typed address to a `◇`-term, so an address-level equality would not
      survive substitution. -/
  | diaEq {Γ : Ctx} {d : ℕ} {A : VarType} {b b' : Ann (.VTypeDia A)}
      (s : Term σ Γ (.VTypeDia A) b) (s' : Term σ Γ (.VTypeDia A) b') : WFF σ Γ d
deriving DecidableEq



/-- Two `≐` formulas agree when their terms do, annotations included. -/
theorem WFF.diaEq_congr {σ : Signature} {Γ : Ctx} {d : ℕ} {A : VarType}
    {b b' c c' : Ann (.VTypeDia A)} {s : Term σ Γ (.VTypeDia A) b}
    {s' : Term σ Γ (.VTypeDia A) b'} {u : Term σ Γ (.VTypeDia A) c}
    {u' : Term σ Γ (.VTypeDia A) c'}
    (h : (⟨b, s⟩ : Σ e, Term σ Γ (.VTypeDia A) e) = ⟨c, u⟩)
    (h' : (⟨b', s'⟩ : Σ e, Term σ Γ (.VTypeDia A) e) = ⟨c', u'⟩) :
    (WFF.diaEq s s' : WFF σ Γ d) = WFF.diaEq u u' := by
  cases h
  cases h'
  rfl

/-- The same at equal annotations. -/
theorem WFF.diaEq_congr' {σ : Signature} {Γ : Ctx} {d : ℕ} {A : VarType}
    {b b' : Ann (.VTypeDia A)} {s u : Term σ Γ (.VTypeDia A) b}
    {s' u' : Term σ Γ (.VTypeDia A) b'} (h : s = u) (h' : s' = u') :
    (WFF.diaEq s s' : WFF σ Γ d) = WFF.diaEq u u' := by
  rw [h, h']
/-- Two `Here` formulas agree when their subjects do. -/
theorem WFF.here_congr' {σ : Signature} {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true)
    {b : Ann (.VTypeDia .Var)} {s s' : Term σ Γ (.VTypeDia .Var) b}
    {t t' : Term σ Γ .Var .var} (hs : s = s') (ht : t = t') :
    (WFF.here hT s t : WFF σ Γ d) = WFF.here hT s' t' := by
  rw [hs, ht]

/-- Two `Here` formulas agree when their subjects do, annotations included. -/
theorem WFF.here_congr {σ : Signature} {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true)
    {b b' : Ann (.VTypeDia .Var)} {s : Term σ Γ (.VTypeDia .Var) b}
    {s' : Term σ Γ (.VTypeDia .Var) b'} {t t' : Term σ Γ .Var .var}
    (hs : (⟨b, s⟩ : Σ b, Term σ Γ (.VTypeDia .Var) b) = ⟨b', s'⟩) (ht : t = t') :
    (WFF.here hT s t : WFF σ Γ d) = WFF.here hT s' t' := by
  cases hs
  cases ht
  rfl

abbrev WFF.neg {σ : Signature} {Γ : Ctx} {d : ℕ} (φ : WFF σ Γ d) : WFF σ Γ d := .imp φ .bot

/-- `□_x φ := ¬◇_x¬φ`. -/
abbrev WFF.boxx {σ : Signature} {Γ : Ctx} {d : ℕ} (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (φ : WFF σ (Γ.diaIn x) d) : WFF σ Γ d :=
  (WFF.dia x hx φ.neg).neg

/-- ⭐Equality at every type, by extensionality — and **annotation-free**: the two terms need only
    share their *type*.  At `◇` it is the primitive `WFF.diaEq`, which is exactly the comparison
    across witnesses that annotations otherwise block (§2d); every other clause is structural, so
    since an annotation of a fixed type varies only in its `.dia` indices, this is equality at every
    type between any two terms of that type. -/
def eqRec {σ : Signature} {d : ℕ} : {Γ : Ctx} → (T : VarType) → {a a' : Ann T} →
    Term σ Γ T a → Term σ Γ T a' → WFF σ Γ d
  | _, .Var, .var, .var, t, s => .eq t s
  | _, .VTypeOne, _, _, _, _ => .top
  | _, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ =>
      .and (eqRec A t₁ s₁) (eqRec B t₂ s₂)
  | _, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => .box (eqRec A t s)
  | _, .VTypeDia _, _, _, s, s' => .diaEq s s'

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
  | _, _, _, h, .here hT s t => .here hT (Term.mono h s) (Term.mono h t)
  | _, _, _, h, .diaEq s s' => .diaEq (Term.mono h s) (Term.mono h s')

/-- Weakening by a fresh root. -/
def WFF.weaken {σ : Signature} {Γ : Ctx} {d : ℕ} {r : Root} (hr : Γ (.root r) = none)
    (T : VarType) (φ : WFF σ Γ d) : WFF σ (Γ.insert r T) d :=
  WFF.mono (Ctx.le_insert hr T) φ

end V12M
