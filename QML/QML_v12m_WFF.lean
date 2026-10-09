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

/-- The out leg of a `Back` atom (strong B, `docs/v12-modal-extensions.md` §11): every successor
    (row 1) or the carrier's own extent (row 2).  Rows 3–4, with a witnessed way home, are to extend
    this type rather than `WFF`. -/
inductive BLeg where
  | nec
  | pos
deriving DecidableEq

/-- The carrier of a `Back` atom whose round trip returns an `A`: a necessary (row 1) or possible
    (row 2) object whose contents are necessary objects. -/
def BLeg.carrier : BLeg → VarType → VarType
  | .nec, A => .VTypeBox (.VTypeBox A)
  | .pos, A => .VTypeDia (.VTypeBox A)

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

      *On the content type.*  Any `A`, and every rule about `Here` — strong T's `T_dia` included
      (§10.41) — holds at every content type.  At a `◇`-typed content `Here s t` says the content
      is *indistinguishable* from `t`'s value (the model's `Ind`, §10.33), not identical to it: two
      names of one content may stand over witnesses nothing has joined, and possibilities combine
      only when the syntax has joined them (§2d).  So functionality is `here_subst`, at any two
      annotations; its equational instance `Proof.here_fun` is `◇`-free only because `eqRec`
      compares at one annotation (`Ann.eq_of_diaFree`).

      The `𝟙` case is why this is primitive rather than a recursion on the content type: there the
      content carries no information, so the clause is the extent condition alone — the
      **reflexive** arrow lies in the extent — and that is expressible only *relative to a base
      term of the view* (`∃a. Here (diatm x hx bd) a` for a base-typed body `bd`), which need not
      exist: the view is the content address plus `Γ.boxIn`, so with no base entry in scope and no
      constant in the signature there is no such `bd`.  `◇_x ⊤` will not do — it says only that the
      extent is non-empty. -/
  | here {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true) {A : VarType}
      {b : Ann (.VTypeDia A)} {a : Ann A} (s : Term σ Γ (.VTypeDia A) b) (t : Term σ Γ A a) :
      WFF σ Γ d
  /-- `Back s t` (strong B): the carrier `s` comes back as `t` — its out leg is nonempty and from
      every arrow of it the way home returns (a value indistinguishable from) `t`
      (`docs/v12-modal-extensions.md` §11.1).  The leg `L` fixes the carrier type: `□□A` (row 1,
      every successor) or `◇□A` (row 2, the carrier's extent).  Any content type (§11.15). -/
  | back {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true) (L : BLeg) {A : VarType}
      {b : Ann (L.carrier A)} {a : Ann A}
      (s : Term σ Γ (L.carrier A) b) (t : Term σ Γ A a) : WFF σ Γ d
  /-- `◇[e ↦ t] Φ(e)` (strong B), the **returning possibility**: possibly some necessary object
      `e : □A` is such that `Φ(e)`, and its content comes back here as `t`
      (`docs/v12-modal-extensions.md` §11.14).  The body is `□∃e:□A. Φ(e)`'s, so every recursion
      treats it as its `box` case followed by its `ex` case.  -/
  | ret {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true) {A : VarType}
      {a : Ann A} (t : Term σ Γ A a)
      (Φ : WFF σ (Γ.boxIn.insert (.bnd d) (.VTypeBox A)) (d + 1)) : WFF σ Γ d
  /-- `◇_y[e ↦ t] Φ(e)` (strong B), the **returning possibility along a witness**: some arrow of
      `y`'s extent reaches a necessary object `e : □A` with `Φ(e)` (read in `y`'s view, so `Φ` may
      speak of `y.dia`), and `e`'s content comes back here along that arrow's way home as `t`
      (`docs/v12-modal-extensions.md` §11.17).  `ret` is the same along every arrow. -/
  | retx {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true) (y : VarSymb)
      (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {A : VarType} {a : Ann A} (t : Term σ Γ A a)
      (Φ : WFF σ ((Γ.diaIn y).insert (.bnd d) (.VTypeBox A)) (d + 1)) : WFF σ Γ d
deriving DecidableEq
/-- Two `Here` formulas agree when their subjects do. -/
theorem WFF.here_congr' {σ : Signature} {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true)
    {A : VarType} {b : Ann (.VTypeDia A)} {a : Ann A}
    {s s' : Term σ Γ (.VTypeDia A) b} {t t' : Term σ Γ A a} (hs : s = s') (ht : t = t') :
    (WFF.here hT s t : WFF σ Γ d) = WFF.here hT s' t' := by
  rw [hs, ht]

/-- Two `Here` formulas agree when their subjects do, annotations included on both sides. -/
theorem WFF.here_congr {σ : Signature} {Γ : Ctx} {d : ℕ} (hT : ModalSys.T = true)
    {A : VarType} {b b' : Ann (.VTypeDia A)} {a a' : Ann A}
    {s : Term σ Γ (.VTypeDia A) b} {s' : Term σ Γ (.VTypeDia A) b'}
    {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    (hs : (⟨b, s⟩ : Σ b, Term σ Γ (.VTypeDia A) b) = ⟨b', s'⟩)
    (ht : (⟨a, t⟩ : Σ a, Term σ Γ A a) = ⟨a', t'⟩) :
    (WFF.here hT s t : WFF σ Γ d) = WFF.here hT s' t' := by
  cases hs
  cases ht
  rfl

/-- Two `Back` formulas agree when their carriers and values do, annotations included. -/
theorem WFF.back_congr {σ : Signature} {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true)
    (L : BLeg) {A : VarType} {b b' : Ann (L.carrier A)} {a a' : Ann A}
    {s : Term σ Γ (L.carrier A) b} {s' : Term σ Γ (L.carrier A) b'}
    {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    (hs : (⟨b, s⟩ : Σ b, Term σ Γ (L.carrier A) b) = ⟨b', s'⟩)
    (ht : (⟨a, t⟩ : Σ a, Term σ Γ A a) = ⟨a', t'⟩) :
    (WFF.back hB L s t : WFF σ Γ d) = WFF.back hB L s' t' := by
  cases hs
  cases ht
  rfl

/-- Two `Back` formulas agree when their carriers and values do, at one annotation each. -/
theorem WFF.back_congr' {σ : Signature} {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true)
    (L : BLeg) {A : VarType} {b : Ann (L.carrier A)} {a : Ann A}
    {s s' : Term σ Γ (L.carrier A) b} {t t' : Term σ Γ A a} (hs : s = s') (ht : t = t') :
    (WFF.back hB L s t : WFF σ Γ d) = WFF.back hB L s' t' := by
  rw [hs, ht]

/-- Two returning possibilities agree when their values and bodies do, at one annotation. -/
theorem WFF.ret_congr' {σ : Signature} {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true)
    {A : VarType} {a : Ann A} {t t' : Term σ Γ A a}
    {Φ Φ' : WFF σ (Γ.boxIn.insert (.bnd d) (.VTypeBox A)) (d + 1)} (ht : t = t') (hΦ : Φ = Φ') :
    (WFF.ret hB t Φ : WFF σ Γ d) = WFF.ret hB t' Φ' := by
  rw [ht, hΦ]

/-- Two returning possibilities agree when their values and bodies do. -/
theorem WFF.ret_congr {σ : Signature} {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true)
    {A : VarType} {a a' : Ann A} {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    {Φ Φ' : WFF σ (Γ.boxIn.insert (.bnd d) (.VTypeBox A)) (d + 1)}
    (ht : (⟨a, t⟩ : Σ a, Term σ Γ A a) = ⟨a', t'⟩) (hΦ : Φ = Φ') :
    (WFF.ret hB t Φ : WFF σ Γ d) = WFF.ret hB t' Φ' := by
  cases ht
  cases hΦ
  rfl

/-- Two returning possibilities along a witness agree when their values and bodies do, at one
    annotation. -/
theorem WFF.retx_congr' {σ : Signature} {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true)
    (y : VarSymb) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {A : VarType} {a : Ann A}
    {t t' : Term σ Γ A a} {Φ Φ' : WFF σ ((Γ.diaIn y).insert (.bnd d) (.VTypeBox A)) (d + 1)}
    (ht : t = t') (hΦ : Φ = Φ') :
    (WFF.retx hB y hy t Φ : WFF σ Γ d) = WFF.retx hB y hy t' Φ' := by
  rw [ht, hΦ]

/-- Two returning possibilities along a witness agree when their values and bodies do. -/
theorem WFF.retx_congr {σ : Signature} {Γ : Ctx} {d : ℕ} (hB : ModalSys.BStrong = true)
    (y : VarSymb) (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {A : VarType} {a a' : Ann A}
    {t : Term σ Γ A a} {t' : Term σ Γ A a'}
    {Φ Φ' : WFF σ ((Γ.diaIn y).insert (.bnd d) (.VTypeBox A)) (d + 1)}
    (ht : (⟨a, t⟩ : Σ a, Term σ Γ A a) = ⟨a', t'⟩) (hΦ : Φ = Φ') :
    (WFF.retx hB y hy t Φ : WFF σ Γ d) = WFF.retx hB y hy t' Φ' := by
  cases ht
  cases hΦ
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
  | _, _, _, h, .here hT s t => .here hT (Term.mono h s) (Term.mono h t)
  | _, _, _, h, .back hB L s t => .back hB L (Term.mono h s) (Term.mono h t)
  | _, _, _, h, .ret hB t Φ => .ret hB (Term.mono h t) (WFF.mono (h.boxIn.insert _ _) Φ)
  | _, _, _, h, .retx hB y hy t Φ =>
      .retx hB y (hy.imp fun _ hY => h.ref hY) (Term.mono h t) (WFF.mono ((h.diaIn y).insert _ _) Φ)

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
