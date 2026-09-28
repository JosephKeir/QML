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
  /-- `Here s t`: the possible object `s` is realised at this world, with value `t` (T only).  Its
      subject is a **term** of `◇`-type, not a witness address, so that substitution can act on it:
      sending a witness to a `diatm` term would otherwise break the tie between the term's type
      and the witness's content type.

      *On the content type.*  The constructor takes any `A`, but functionality — `Proof.here_fun`,
      the rule that makes `Here` useful — is stated at `◇`-free `A` only, and so is strong T's
      `posRet_exists`.  The reason is the predicate's, not the equality's: `Here s t` with a
      possible object as its value asserts that `s`'s content here *is* that object, and two such
      atoms about one subject, over witnesses nothing has joined, are jointly satisfiable only if
      those witnesses share an extent — which the construction cannot arrange, and should not,
      since possibilities combine only when the syntax has joined them (§2d).  At `◇`-free `A` the
      annotation is unique (`Ann.eq_of_diaFree`), so functionality's `eqRec` needs no side
      condition there.

      The `𝟙` case is why this is primitive rather than a recursion on the content type: there the
      content carries no information, so the clause is the extent condition alone — the
      **reflexive** arrow lies in the extent — and that is expressible only *relative to a base
      term of the view* (`∃a. Here (diatm x hx bd) a` for a base-typed body `bd`), which need not
      exist: the view is the content address plus `Γ.boxIn`, so with no base entry in scope and no
      constant in the signature there is no such `bd`.  `◇_x ⊤` will not do — it says only that the
      extent is non-empty. -/
  | here {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true) {A : VarType} (hA : A.diaFree = true)
      {b : Ann (.VTypeDia A)} {a : Ann A} (s : Term σ Γ (.VTypeDia A) b) (t : Term σ Γ A a) :
      WFF σ Γ d
deriving DecidableEq
/-- Two `Here` formulas agree when their subjects do. -/
theorem WFF.here_congr' {σ : Signature} {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true)
    {A : VarType} (hA : A.diaFree = true) {b : Ann (.VTypeDia A)} {a : Ann A}
    {s s' : Term σ Γ (.VTypeDia A) b} {t t' : Term σ Γ A a} (hs : s = s') (ht : t = t') :
    (WFF.here hT hA s t : WFF σ Γ d) = WFF.here hT hA s' t' := by
  rw [hs, ht]

/-- Two `Here` formulas agree when their subjects do, annotations included on both sides. -/
theorem WFF.here_congr {σ : Signature} {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true)
    {A : VarType} (hA : A.diaFree = true) {b b' : Ann (.VTypeDia A)} {a a' : Ann A}
    {s : Term σ Γ (.VTypeDia A) b} {s' : Term σ Γ (.VTypeDia A) b'}
    {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    (hs : (⟨b, s⟩ : Σ b, Term σ Γ (.VTypeDia A) b) = ⟨b', s'⟩)
    (ht : (⟨a, t⟩ : Σ a, Term σ Γ A a) = ⟨a', t'⟩) :
    (WFF.here hT hA s t : WFF σ Γ d) = WFF.here hT hA s' t' := by
  cases hs
  cases ht
  rfl

abbrev WFF.neg {σ : Signature} {Γ : Ctx} {d : ℕ} (φ : WFF σ Γ d) : WFF σ Γ d := .imp φ .bot

/-- `□_x φ := ¬◇_x¬φ`. -/
abbrev WFF.boxx {σ : Signature} {Γ : Ctx} {d : ℕ} (x : VarSymb)
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (φ : WFF σ (Γ.diaIn x) d) : WFF σ Γ d :=
  (WFF.dia x hx φ.neg).neg

/-- ⭐Equality at every type, by extensionality, **within one fibre**: the two terms share their
    annotation.  An annotation of a fixed type varies only in its `.dia` witness indices, everything
    else being forced by the type, so sharing it means sharing the witness at every `◇` position —
    and the `◇` clause is then `□_x`, the equality of the two bodies at every arrow of the one
    witness's extent.  Terms over *different* witnesses are not compared, and that is the design:
    possibilities combine only when the syntax has joined them, which for terms is pairing, after
    which both components stand over the one witness and this equality applies (§2d).  At a `◇`-free
    type the annotation is unique (`Ann.eq_of_diaFree`), so there the restriction is vacuous. -/
def eqRec {σ : Signature} {d : ℕ} : {Γ : Ctx} → (T : VarType) → {a : Ann T} →
    Term σ Γ T a → Term σ Γ T a → WFF σ Γ d
  | _, .Var, .var, t, s => .eq t s
  | _, .VTypeOne, _, _, _ => .top
  | _, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ =>
      .and (eqRec A t₁ s₁) (eqRec B t₂ s₂)
  | _, .VTypeBox A, .box _, .boxtm t, .boxtm s => .box (eqRec A t s)
  | _, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s => .boxx x hx (eqRec A t s)


/-- At base type the defined equality is the primitive one: `eqRec`’s `.Var` clause, as a
    rewrite. -/
theorem eqRec_Var {σ : Signature} {Γ : Ctx} {d : ℕ} (t s : Term σ Γ .Var .var) :
    (eqRec .Var t s : WFF σ Γ d) = .eq t s := by
  cases t <;> cases s <;> rfl


/-- Two equalities agree when their sides do, annotations included — the `Sigma` form, since
    substitution moves annotations.  Both sides must land at one annotation, as `eqRec` compares
    within a fibre. -/
theorem eqRec_congr {σ : Signature} {Γ : Ctx} {d : ℕ} {A : VarType} {a a' : Ann A}
    {t s : Term σ Γ A a} {t' s' : Term σ Γ A a'}
    (ht : (⟨a, t⟩ : Σ b, Term σ Γ A b) = ⟨a', t'⟩)
    (hs : (⟨a, s⟩ : Σ b, Term σ Γ A b) = ⟨a', s'⟩) :
    (eqRec A t s : WFF σ Γ d) = eqRec A t' s' := by
  cases ht
  cases hs
  rfl

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
  | _, _, _, h, .here hT hA s t => .here hT hA (Term.mono h s) (Term.mono h t)

/-- Weakening by a fresh root. -/
def WFF.weaken {σ : Signature} {Γ : Ctx} {d : ℕ} {r : Root} (hr : Γ (.root r) = none)
    (T : VarType) (φ : WFF σ Γ d) : WFF σ (Γ.insert r T) d :=
  WFF.mono (Ctx.le_insert hr T) φ


/-- Weakening commutes with equality at every type. -/
theorem eqRec_mono {σ : Signature} {d : ℕ} : {Γ Γ' : Ctx} → (h : Γ.Le Γ') → (T : VarType) →
    {a : Ann T} → (t s : Term σ Γ T a) →
    WFF.mono h (eqRec T t s : WFF σ Γ d) = eqRec T (Term.mono h t) (Term.mono h s)
  | _, _, h, .Var, .var, t, s =>
      (congrArg (WFF.mono h) (eqRec_Var t s)).trans (eqRec_Var _ _).symm
  | _, _, _, .VTypeOne, .one, .unit, .unit => rfl
  | _, _, h, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change WFF.and (WFF.mono h (eqRec A t₁ s₁)) (WFF.mono h (eqRec B t₂ s₂)) = _
      rw [eqRec_mono h A, eqRec_mono h B]
      rfl
  | _, _, h, .VTypeBox A, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.mono h.boxIn (eqRec A t s)) = _
      rw [eqRec_mono h.boxIn A]
      rfl
  | _, _, h, .VTypeDia A, .dia x _, .diatm _ _ t, .diatm _ _ s => by
      change WFF.imp (WFF.dia x _ (WFF.imp (WFF.mono (h.diaIn x) (eqRec A t s)) .bot)) .bot = _
      rw [eqRec_mono (h.diaIn x) A]
      rfl

end V12M
