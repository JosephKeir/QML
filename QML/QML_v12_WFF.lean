import QML.QML_v12_Terms

/-!
# QML v12 — formulas

Formulas follow the term scheme: modal nodes store their inner context Forded (`Ctx.boxIn`,
`Ctx.diaIn`), there is no pair-elimination node, and quantifiers range over PLAIN types, binding
the next slot `bnd depth` (`Ctx.insertBnd`).

Base equality is primitive; equality at every type is DEFINED by extensionality (`eqRec`).  It
compares terms of the same ANNOTATED type, so terms with different witnesses cannot even be
compared.
-/

namespace V12

-- ⚠️Keep the context an INDEX: promoted to a parameter, the heterogeneous `Rel.beq` below would
-- depend on `Quot.sound`.
set_option inductive.autoPromoteIndices false in
inductive Rel (σ : Signature) : Ctx → ℕ → Type where
  | R {Γ : Ctx} {n : ℕ} (r : {r : σ.RelSyms // σ.relArity r = n}) : Rel σ Γ n
  | eval {Γ : Ctx} {n : ℕ} : Rel σ Γ (n + 1) → Term σ Γ .Var .var → Rel σ Γ n

inductive WFF (σ : Signature) : Ctx → Type where
  | atom {Γ : Ctx} : Rel σ Γ 0 → WFF σ Γ
  | top {Γ : Ctx} : WFF σ Γ
  | bot {Γ : Ctx} : WFF σ Γ
  | and {Γ : Ctx} : WFF σ Γ → WFF σ Γ → WFF σ Γ
  | or {Γ : Ctx} : WFF σ Γ → WFF σ Γ → WFF σ Γ
  | imp {Γ : Ctx} : WFF σ Γ → WFF σ Γ → WFF σ Γ
  /-- The bound variable is the slot `Γ.nextBnd`; only its plain TYPE is data. -/
  | all {Γ : Ctx} (T : VarType) : WFF σ (Γ.insertBnd T) → WFF σ Γ
  | ex {Γ : Ctx} (T : VarType) : WFF σ (Γ.insertBnd T) → WFF σ Γ
  /-- Primitive only at base type; see `eqRec`. -/
  | eq {Γ : Ctx} : Term σ Γ .Var .var → Term σ Γ .Var .var → WFF σ Γ
  | box {Γ Δ : Ctx} (φ : WFF σ Δ) (hΔ : Δ = Γ.boxIn) : WFF σ Γ
  /-- `◇_x φ`: `x` has type `◇X` outside, `X` inside. -/
  | dia {Γ Δ : Ctx} (x : VarSymb) (X : VarType) (hx : Γ.refType x = some (.VTypeDia X))
      (φ : WFF σ Δ) (hΔ : Δ = Γ.diaIn x X) : WFF σ Γ

abbrev WFF.neg {σ : Signature} {Γ : Ctx} (φ : WFF σ Γ) : WFF σ Γ := .imp φ .bot

/-- `□_x φ := ¬◇_x¬φ`. -/
abbrev WFF.boxx {σ : Signature} {Γ Δ : Ctx} (x : VarSymb) (X : VarType)
    (hx : Γ.refType x = some (.VTypeDia X)) (φ : WFF σ Δ) (hΔ : Δ = Γ.diaIn x X) : WFF σ Γ :=
  (WFF.dia x X hx φ.neg hΔ).neg

/-! ## Decidable equality

As for terms: a structurally recursive boolean test on formulas over possibly different contexts,
sound by the recursor. -/

def Rel.beq {σ : Signature} : {Γ Γ' : Ctx} → {n n' : ℕ} → Rel σ Γ n → Rel σ Γ' n' → Bool
  | _, _, _, _, .R r, .R r' => decide (r.1 = r'.1)
  | _, _, _, _, .eval ρ t, .eval ρ' t' => Rel.beq ρ ρ' && Term.beq t t'
  | _, _, _, _, _, _ => false

theorem Rel.eq_of_beq {σ : Signature} : {Γ : Ctx} → {n : ℕ} → (R R' : Rel σ Γ n) →
    Rel.beq R R' = true → R = R'
  | _, _, .R r, .R r', h => by
      simp only [Rel.beq, decide_eq_true_eq] at h
      rw [Subtype.ext h]
  | _, _, .R _, .eval _ _, h => by simp [Rel.beq] at h
  | _, _, .eval _ _, .R _, h => by simp [Rel.beq] at h
  | _, _, .eval ρ t, .eval ρ' t', h => by
      simp only [Rel.beq, Bool.and_eq_true] at h
      rw [Rel.eq_of_beq ρ ρ' h.1, Term.eq_of_beq t t' h.2]

theorem Rel.beq_refl {σ : Signature} : {Γ : Ctx} → {n : ℕ} → (R : Rel σ Γ n) → Rel.beq R R = true
  | _, _, .R _ => by simp only [Rel.beq, decide_true]
  | _, _, .eval ρ t => by simp only [Rel.beq, Rel.beq_refl ρ, Term.beq_refl t, Bool.and_self]

instance {σ : Signature} {Γ : Ctx} {n : ℕ} : DecidableEq (Rel σ Γ n) :=
  fun R R' =>
    if h : Rel.beq R R' = true then isTrue (Rel.eq_of_beq R R' h)
    else isFalse (fun e => h (by subst e; exact Rel.beq_refl R))

def WFF.beq {σ : Signature} : {Γ Γ' : Ctx} → WFF σ Γ → WFF σ Γ' → Bool
  | _, _, .atom R, .atom R' => Rel.beq R R'
  | _, _, .top, .top => true
  | _, _, .bot, .bot => true
  | _, _, .and φ ψ, .and φ' ψ' => WFF.beq φ φ' && WFF.beq ψ ψ'
  | _, _, .or φ ψ, .or φ' ψ' => WFF.beq φ φ' && WFF.beq ψ ψ'
  | _, _, .imp φ ψ, .imp φ' ψ' => WFF.beq φ φ' && WFF.beq ψ ψ'
  | _, _, .all T φ, .all T' φ' => decide (T = T') && WFF.beq φ φ'
  | _, _, .ex T φ, .ex T' φ' => decide (T = T') && WFF.beq φ φ'
  | _, _, .eq t s, .eq t' s' => Term.beq t t' && Term.beq s s'
  | _, _, .box φ _hΔ, .box φ' _hΔ' => WFF.beq φ φ'
  | _, _, .dia x X _hx φ _hΔ, .dia x' X' _hx' φ' _hΔ' =>
      decide (x = x') && decide (X = X') && WFF.beq φ φ'
  | _, _, _, _ => false

theorem WFF.eq_of_beq {σ : Signature} {Γ : Ctx} (φ : WFF σ Γ) :
    ∀ ψ, WFF.beq φ ψ = true → φ = ψ := by
  refine WFF.rec (motive := fun Γ φ => ∀ ψ : WFF σ Γ, WFF.beq φ ψ = true → φ = ψ)
    ?hatom ?htop ?hbot ?hand ?hor ?himp ?hall ?hex ?heq ?hbox ?hdia φ
  case hatom =>
    intro Γ R ψ h
    cases ψ with
    | atom R' => simp only [WFF.beq] at h; rw [Rel.eq_of_beq R R' h]
    | _ => simp [WFF.beq] at h
  case htop =>
    intro Γ ψ h
    cases ψ with
    | top => rfl
    | _ => simp [WFF.beq] at h
  case hbot =>
    intro Γ ψ h
    cases ψ with
    | bot => rfl
    | _ => simp [WFF.beq] at h
  case hand =>
    intro Γ φ₁ φ₂ ih₁ ih₂ ψ h
    cases ψ with
    | and ψ₁ ψ₂ =>
        simp only [WFF.beq, Bool.and_eq_true] at h
        rw [ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [WFF.beq] at h
  case hor =>
    intro Γ φ₁ φ₂ ih₁ ih₂ ψ h
    cases ψ with
    | or ψ₁ ψ₂ =>
        simp only [WFF.beq, Bool.and_eq_true] at h
        rw [ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [WFF.beq] at h
  case himp =>
    intro Γ φ₁ φ₂ ih₁ ih₂ ψ h
    cases ψ with
    | imp ψ₁ ψ₂ =>
        simp only [WFF.beq, Bool.and_eq_true] at h
        rw [ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [WFF.beq] at h
  case hall =>
    intro Γ T φ ih ψ h
    cases ψ with
    | all T' ψ =>
        simp only [WFF.beq, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, h⟩ := h
        rw [ih ψ h]
    | _ => simp [WFF.beq] at h
  case hex =>
    intro Γ T φ ih ψ h
    cases ψ with
    | ex T' ψ =>
        simp only [WFF.beq, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, h⟩ := h
        rw [ih ψ h]
    | _ => simp [WFF.beq] at h
  case heq =>
    intro Γ t s ψ h
    cases ψ with
    | eq t' s' =>
        simp only [WFF.beq, Bool.and_eq_true] at h
        rw [Term.eq_of_beq t t' h.1, Term.eq_of_beq s s' h.2]
    | _ => simp [WFF.beq] at h
  case hbox =>
    intro Γ Δ φ hΔ ih ψ h
    cases ψ with
    | box ψ hΔ' =>
        simp only [WFF.beq] at h
        subst hΔ hΔ'
        rw [ih ψ h]
    | _ => simp [WFF.beq] at h
  case hdia =>
    intro Γ Δ x X hx φ hΔ ih ψ h
    cases ψ with
    | dia x' X' _hx' ψ hΔ' =>
        simp only [WFF.beq, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, rfl⟩, h⟩ := h
        subst hΔ hΔ'
        rw [ih ψ h]
    | _ => simp [WFF.beq] at h

theorem WFF.beq_refl {σ : Signature} : {Γ : Ctx} → (φ : WFF σ Γ) → WFF.beq φ φ = true
  | _, .atom R => Rel.beq_refl R
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and φ ψ => by simp only [WFF.beq, WFF.beq_refl φ, WFF.beq_refl ψ, Bool.and_self]
  | _, .or φ ψ => by simp only [WFF.beq, WFF.beq_refl φ, WFF.beq_refl ψ, Bool.and_self]
  | _, .imp φ ψ => by simp only [WFF.beq, WFF.beq_refl φ, WFF.beq_refl ψ, Bool.and_self]
  | _, .all _ φ => by simp only [WFF.beq, WFF.beq_refl φ, decide_true, Bool.and_self]
  | _, .ex _ φ => by simp only [WFF.beq, WFF.beq_refl φ, decide_true, Bool.and_self]
  | _, .eq t s => by simp only [WFF.beq, Term.beq_refl t, Term.beq_refl s, Bool.and_self]
  | _, .box φ _hΔ => by simp only [WFF.beq, WFF.beq_refl φ]
  | _, .dia _x _X _hx φ _hΔ => by
      simp only [WFF.beq, WFF.beq_refl φ, decide_true, Bool.and_self]

instance {σ : Signature} {Γ : Ctx} : DecidableEq (WFF σ Γ) :=
  fun φ ψ =>
    if h : WFF.beq φ ψ = true then isTrue (WFF.eq_of_beq φ ψ h)
    else isFalse (fun e => h (by subst e; exact WFF.beq_refl φ))

/-! ## Transport between similar contexts -/

def Rel.transport {σ : Signature} {Γ Γ' : Ctx} (h : Γ.Sim Γ') :
    {n : ℕ} → Rel σ Γ n → Rel σ Γ' n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.transport h ρ) (Term.transport h t)

theorem Rel.transport_transport {σ : Signature} {Γ Γ' Γ'' : Ctx} (h : Γ.Sim Γ')
    (h' : Γ'.Sim Γ'') : {n : ℕ} → (R : Rel σ Γ n) →
    Rel.transport h' (Rel.transport h R) = Rel.transport (h.trans h') R
  | _, .R _ => rfl
  | _, .eval ρ t => by
      simp only [Rel.transport, Rel.transport_transport h h' ρ, Term.transport_transport h h' t]

theorem Rel.transport_refl {σ : Signature} {Γ : Ctx} (h : Γ.Sim Γ) :
    {n : ℕ} → (R : Rel σ Γ n) → Rel.transport h R = R
  | _, .R _ => rfl
  | _, .eval ρ t => by simp only [Rel.transport, Rel.transport_refl h ρ, Term.transport_refl h t]

/-- ⭐Cast-free; enters quantifier bodies (hence `PSim`), never modal ones. -/
def WFF.transport {σ : Signature} : {Γ Γ' : Ctx} → Γ.PSim Γ' → WFF σ Γ → WFF σ Γ'
  | _, _, h, .atom R => .atom (R.transport h.toSim)
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, h, .and φ ψ => .and (WFF.transport h φ) (WFF.transport h ψ)
  | _, _, h, .or φ ψ => .or (WFF.transport h φ) (WFF.transport h ψ)
  | _, _, h, .imp φ ψ => .imp (WFF.transport h φ) (WFF.transport h ψ)
  | _, _, h, .all T φ => .all T (WFF.transport (h.insertBnd T) φ)
  | _, _, h, .ex T φ => .ex T (WFF.transport (h.insertBnd T) φ)
  | _, _, h, .eq t s => .eq (t.transport h.toSim) (s.transport h.toSim)
  | _, _, h, .box φ hΔ => .box φ (hΔ.trans h.toSim.box.symm)
  | _, _, h, .dia x X hx φ hΔ =>
      .dia x X (h.toSim.dia x X hx).1 φ (hΔ.trans (h.toSim.dia x X hx).2.symm)

theorem WFF.transport_transport {σ : Signature} : {Γ Γ' Γ'' : Ctx} → (h : Γ.PSim Γ') →
    (h' : Γ'.PSim Γ'') → (φ : WFF σ Γ) →
    WFF.transport h' (WFF.transport h φ) = WFF.transport (h.trans h') φ
  | _, _, _, h, h', .atom R => by
      simp only [WFF.transport, Rel.transport_transport h.toSim h'.toSim R]
  | _, _, _, _, _, .top => rfl
  | _, _, _, _, _, .bot => rfl
  | _, _, _, h, h', .and φ ψ => by
      simp only [WFF.transport, WFF.transport_transport h h' φ, WFF.transport_transport h h' ψ]
  | _, _, _, h, h', .or φ ψ => by
      simp only [WFF.transport, WFF.transport_transport h h' φ, WFF.transport_transport h h' ψ]
  | _, _, _, h, h', .imp φ ψ => by
      simp only [WFF.transport, WFF.transport_transport h h' φ, WFF.transport_transport h h' ψ]
  | _, _, _, h, h', .all T φ => by
      simp only [WFF.transport, WFF.transport_transport (h.insertBnd T) (h'.insertBnd T) φ]
  | _, _, _, h, h', .ex T φ => by
      simp only [WFF.transport, WFF.transport_transport (h.insertBnd T) (h'.insertBnd T) φ]
  | _, _, _, h, h', .eq t s => by
      simp only [WFF.transport, Term.transport_transport h.toSim h'.toSim t,
        Term.transport_transport h.toSim h'.toSim s]
  | _, _, _, _, _, .box _φ _hΔ => rfl
  | _, _, _, _, _, .dia _x _X _hx _φ _hΔ => rfl

theorem WFF.transport_refl {σ : Signature} : {Γ : Ctx} → (h : Γ.PSim Γ) → (φ : WFF σ Γ) →
    WFF.transport h φ = φ
  | _, h, .atom R => by simp only [WFF.transport, Rel.transport_refl h.toSim R]
  | _, _, .top => rfl
  | _, _, .bot => rfl
  | _, h, .and φ ψ => by simp only [WFF.transport, WFF.transport_refl h φ, WFF.transport_refl h ψ]
  | _, h, .or φ ψ => by simp only [WFF.transport, WFF.transport_refl h φ, WFF.transport_refl h ψ]
  | _, h, .imp φ ψ => by simp only [WFF.transport, WFF.transport_refl h φ, WFF.transport_refl h ψ]
  | _, h, .all T φ => by simp only [WFF.transport, WFF.transport_refl (h.insertBnd T) φ]
  | _, h, .ex T φ => by simp only [WFF.transport, WFF.transport_refl (h.insertBnd T) φ]
  | _, h, .eq t s => by
      simp only [WFF.transport, Term.transport_refl h.toSim t, Term.transport_refl h.toSim s]
  | _, _, .box _φ _hΔ => rfl
  | _, _, .dia _x _X _hx _φ _hΔ => rfl

/-! ## Splitting and unsplitting

⭐The whole of pair elimination on formulas: a formula over a split context IS a formula over the
unsplit one, up to replacing proofs.  This is what the `pair_elim` proof rule will use. -/

def WFF.unsplit {σ : Signature} {Γ : Ctx} (P : Root → Pat) : WFF σ (Γ.refine P) → WFF σ Γ :=
  WFF.transport (Γ.psim_refine_left P)

def WFF.split {σ : Signature} {Γ : Ctx} (P : Root → Pat) : WFF σ Γ → WFF σ (Γ.refine P) :=
  WFF.transport (Γ.psim_refine_right P)

@[simp] theorem WFF.unsplit_split {σ : Signature} {Γ : Ctx} (P : Root → Pat) (φ : WFF σ Γ) :
    (φ.split P).unsplit P = φ :=
  (WFF.transport_transport _ _ φ).trans (WFF.transport_refl _ φ)

@[simp] theorem WFF.split_unsplit {σ : Signature} {Γ : Ctx} (P : Root → Pat)
    (φ : WFF σ (Γ.refine P)) : (φ.unsplit P).split P = φ :=
  (WFF.transport_transport _ _ φ).trans (WFF.transport_refl _ φ)

/-! ## Equality at every type

DEFINED by extensionality, recursing on the plain type.  Both sides carry the same annotation, so
at a modal type their witnesses, inner contexts and body annotations agree; the `else` branches
are unreachable, and are there only because that agreement is propositional. -/

def eqRec {σ : Signature} : {Γ : Ctx} → (T : VarType) → {a : Ann T} →
    Term σ Γ T a → Term σ Γ T a → WFF σ Γ
  | _, .Var, .var, t, s => .eq t s
  | _, .VTypeOne, _, _, _ => .top
  | _, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => .and (eqRec A t₁ s₁) (eqRec B t₂ s₂)
  | _, .VTypeBox A, _, .boxtm (Δ := Δ₁) (a := a₁) t hΔ₁ _hb₁,
      .boxtm (Δ := Δ₂) (a := a₂) s hΔ₂ _hb₂ =>
      if ha : a₁ = a₂ then .box (eqRec A t (cast (by rw [hΔ₁, hΔ₂, ha]) s)) hΔ₁ else .bot
  | _, .VTypeDia A, _, .diatm (Δ := Δ₁) (a := a₁) x X hx t hΔ₁ _hb₁,
      .diatm (Δ := Δ₂) (a := a₂) x' X' _hx' s hΔ₂ _hb₂ =>
      if h : x = x' ∧ X = X' ∧ a₁ = a₂ then
        .boxx x X hx (eqRec A t (cast (by rw [hΔ₁, hΔ₂, h.1, h.2.1, h.2.2]) s)) hΔ₁
      else .bot

theorem eqRec_boxtm {σ : Signature} {Γ Δ : Ctx} {A : VarType} {a : Ann A}
    {b : Ann (.VTypeBox A)} (t s : Term σ Δ A a) (hΔ : Δ = Γ.boxIn)
    (hb hb' : b = .box (a.mapIdx Δ.boxOut)) :
    eqRec (.VTypeBox A) (Term.boxtm t hΔ hb) (Term.boxtm s hΔ hb') = .box (eqRec A t s) hΔ := by
  simp only [eqRec, dite_true, cast_eq]

theorem eqRec_diatm {σ : Signature} {Γ Δ : Ctx} {A : VarType} {a : Ann A}
    {b : Ann (.VTypeDia A)} (x : VarSymb) (X : VarType)
    (hx hx' : Γ.refType x = some (.VTypeDia X)) (t s : Term σ Δ A a) (hΔ : Δ = Γ.diaIn x X)
    (hb hb' : b = .dia x.toIdx (a.mapIdx (Δ.diaOut x))) :
    eqRec (.VTypeDia A) (Term.diatm x X hx t hΔ hb) (Term.diatm x X hx' s hΔ hb') =
      .boxx x X hx (eqRec A t s) hΔ := by
  simp only [eqRec, and_self, dite_true, cast_eq]

end V12
