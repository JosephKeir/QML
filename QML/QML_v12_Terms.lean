import QML.QML_v12_Symbols

/-!
# QML v12 — terms

Terms are typed INTRINSICALLY by a plain type together with its witness annotation:
`Term σ Γ T a` with `a : Ann T`.

* **No pair-elimination node.**  A pair component is referenced by its path name (`comp z fst`),
  looked up through any unsplit product (`Ctx.refType`).  A modal node applies the forced split of
  its context itself (`Ctx.boxIn`, `Ctx.diaIn`), which is exactly the normal form: the only place a
  split is ever needed.
* **Forded indices.**  Each modal constructor stores its inner context `Δ` and its annotation `b`
  as variables with defining equations.  Moving a term between similar contexts (`Ctx.Sim`) then
  only replaces those proofs: `Term.transport` is cast-free and never enters a modal body.
  Splitting and unsplitting are instances, and they are inverse.
* `DecidableEq` comes from a structurally recursive boolean comparison, so it reduces in the
  kernel and needs no `Classical.choice` (the derived handler cannot be used: it would try to
  compare the stored contexts, which are functions).
-/

namespace V12

structure Signature where
  FuncSyms : Type
  RelSyms : Type
  funcArity : FuncSyms → ℕ
  relArity  : RelSyms  → ℕ
  [decEqF   : DecidableEq FuncSyms]
  [decEqR   : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

mutual
  inductive Func (σ : Signature) : Ctx → ℕ → Type where
    | F {Γ : Ctx} {n : ℕ} (f : {f : σ.FuncSyms // σ.funcArity f = n}) : Func σ Γ n
    | eval {Γ : Ctx} {n : ℕ} : Func σ Γ (n + 1) → Term σ Γ .Var .var → Func σ Γ n

  /-- `Term σ Γ T a`: a term of plain type `T` and annotation `a` over the context `Γ`.  Only
      base-typed names are terms; modal, pair and unit terms are built by their constructors. -/
  inductive Term (σ : Signature) : Ctx → (T : VarType) → Ann T → Type where
    | var {Γ : Ctx} (v : VarSymb) (h : Γ.refType v = some .Var) : Term σ Γ .Var .var
    | func {Γ : Ctx} (f : Func σ Γ 0) : Term σ Γ .Var .var
    | unit {Γ : Ctx} : Term σ Γ .VTypeOne .one
    | pair {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B} :
        Term σ Γ A a → Term σ Γ B b → Term σ Γ (.VTypeProd A B) (.prod a b)
    | boxtm {Γ Δ : Ctx} {A : VarType} {a : Ann A} {b : Ann (.VTypeBox A)}
        (t : Term σ Δ A a) (hΔ : Δ = Γ.boxIn) (hb : b = .box (a.mapIdx Δ.boxOut)) :
        Term σ Γ (.VTypeBox A) b
    /-- `x` is the PROMOTED witness: a name of type `◇X` outside, `X` inside. -/
    | diatm {Γ Δ : Ctx} {A : VarType} {a : Ann A} {b : Ann (.VTypeDia A)}
        (x : VarSymb) (X : VarType) (hx : Γ.refType x = some (.VTypeDia X))
        (t : Term σ Δ A a) (hΔ : Δ = Γ.diaIn x X)
        (hb : b = .dia x.toIdx (a.mapIdx (Δ.diaOut x))) :
        Term σ Γ (.VTypeDia A) b
end

/-! ## Decidable equality

Terms are compared by a STRUCTURALLY recursive boolean test on terms over possibly different
contexts, so modal bodies are compared without any cast; it is shown sound by the recursor.  No
well-founded recursion is involved, so the instance reduces in the kernel and uses no
`Classical.choice`. -/

/-- Annotations of possibly different plain types, compared as one. -/
def Ann.heq {A B : VarType} (a : Ann A) (b : Ann B) : Bool :=
  decide ((⟨A, a⟩ : Σ T, Ann T) = ⟨B, b⟩)

mutual
  def Func.beq {σ : Signature} : {Γ Γ' : Ctx} → {n n' : ℕ} →
      Func σ Γ n → Func σ Γ' n' → Bool
    | _, _, _, _, .F f, .F g => decide (f.1 = g.1)
    | _, _, _, _, .F _, .eval _ _ => false
    | _, _, _, _, .eval _ _, .F _ => false
    | _, _, _, _, .eval f s, .eval g t => Func.beq f g && Term.beq s t

  def Term.beq {σ : Signature} : {Γ Γ' : Ctx} → {T T' : VarType} → {a : Ann T} → {a' : Ann T'} →
      Term σ Γ T a → Term σ Γ' T' a' → Bool
    | _, _, _, _, _, _, .var v _, .var w _ => decide (v = w)
    | _, _, _, _, _, _, .func f, .func g => Func.beq f g
    | _, _, _, _, _, _, .unit, .unit => true
    | _, _, _, _, _, _, .pair s₁ s₂, .pair t₁ t₂ => Term.beq s₁ t₁ && Term.beq s₂ t₂
    -- ⚠️the proof fields must be NAMED in these patterns: `_` fails to elaborate
    | _, _, _, _, _, _, .boxtm (a := a₁) t₁ _hΔ₁ _hb₁, .boxtm (a := a₂) t₂ _hΔ₂ _hb₂ =>
        Ann.heq a₁ a₂ && Term.beq t₁ t₂
    | _, _, _, _, _, _, .diatm (a := a₁) x₁ X₁ _hx₁ t₁ _hΔ₁ _hb₁,
      .diatm (a := a₂) x₂ X₂ _hx₂ t₂ _hΔ₂ _hb₂ =>
        decide (x₁ = x₂) && decide (X₁ = X₂) && Ann.heq a₁ a₂ && Term.beq t₁ t₂
    | _, _, _, _, _, _, _, _ => false
end

/-- Soundness of `beq`, by the recursor: its induction hypotheses are plain variables, so the
    context substitutions a modal case needs cannot disturb the recursion (a structural proof
    fails exactly there). -/
theorem Term.eq_of_beq {σ : Signature} {Γ : Ctx} {T : VarType} {a : Ann T} (s : Term σ Γ T a) :
    ∀ t, Term.beq s t = true → s = t := by
  refine Term.rec
    (motive_1 := fun Γ n f => ∀ g : Func σ Γ n, Func.beq f g = true → f = g)
    (motive_2 := fun Γ T a s => ∀ t : Term σ Γ T a, Term.beq s t = true → s = t)
    ?F ?eval ?var ?func ?unit ?pair ?boxtm ?diatm s
  case F =>
    intro Γ n f g h
    cases g with
    | F g => simp only [Func.beq, decide_eq_true_eq] at h; rw [Subtype.ext h]
    | eval _ _ => simp [Func.beq] at h
  case eval =>
    intro Γ n f s ihf ihs g h
    cases g with
    | F _ => simp [Func.beq] at h
    | eval g t =>
        simp only [Func.beq, Bool.and_eq_true] at h
        rw [ihf g h.1, ihs t h.2]
  case var =>
    intro Γ v hv t h
    cases t with
    | var w hw => simp only [Term.beq, decide_eq_true_eq] at h; subst h; rfl
    | func _ => simp [Term.beq] at h
  case func =>
    intro Γ f ih t h
    cases t with
    | var _ _ => simp [Term.beq] at h
    | func g => simp only [Term.beq] at h; rw [ih g h]
  case unit =>
    intro Γ t _
    cases t; rfl
  case pair =>
    intro Γ A B a b s₁ s₂ ih₁ ih₂ t h
    cases t with
    | pair t₁ t₂ =>
        simp only [Term.beq, Bool.and_eq_true] at h
        rw [ih₁ t₁ h.1, ih₂ t₂ h.2]
  case boxtm =>
    intro Γ Δ A a b t₁ hΔ₁ hb₁ ih t h
    cases t with
    | @boxtm _ Δ₂ _ a₂ _ t₂ hΔ₂ hb₂ =>
        simp only [Term.beq, Ann.heq, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨ha, ht⟩ := h
        have ha' : a = a₂ := eq_of_heq (Sigma.mk.inj ha).2
        subst ha' hΔ₁ hΔ₂
        rw [ih t₂ ht]
  case diatm =>
    intro Γ Δ A a b x X hx t₁ hΔ₁ hb₁ ih t h
    cases t with
    | @diatm _ Δ₂ _ a₂ _ x₂ X₂ hx₂ t₂ hΔ₂ hb₂ =>
        simp only [Term.beq, Ann.heq, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hxx, hXX⟩, ha⟩, ht⟩ := h
        have ha' : a = a₂ := eq_of_heq (Sigma.mk.inj ha).2
        subst hxx hXX ha' hΔ₁ hΔ₂
        rw [ih t₂ ht]

mutual
  theorem Func.beq_refl {σ : Signature} : {Γ : Ctx} → {n : ℕ} → (f : Func σ Γ n) →
      Func.beq f f = true
    | _, _, .F _ => decide_eq_true rfl
    | _, _, .eval f s => by
        simp only [Func.beq, Func.beq_refl f, Term.beq_refl s, Bool.and_self]

  theorem Term.beq_refl {σ : Signature} : {Γ : Ctx} → {T : VarType} → {a : Ann T} →
      (t : Term σ Γ T a) → Term.beq t t = true
    | _, _, _, .var _ _ => decide_eq_true rfl
    | _, _, _, .func f => Func.beq_refl f
    | _, _, _, .unit => rfl
    | _, _, _, .pair s t => by simp only [Term.beq, Term.beq_refl s, Term.beq_refl t, Bool.and_self]
    | _, _, _, .boxtm t _hΔ _hb => by
        simp only [Term.beq, Ann.heq, Term.beq_refl t, decide_true, Bool.and_self]
    | _, _, _, .diatm _x _X _hx t _hΔ _hb => by
        simp only [Term.beq, Ann.heq, Term.beq_refl t, decide_true, Bool.and_self]
end

instance {σ : Signature} {Γ : Ctx} {T : VarType} {a : Ann T} : DecidableEq (Term σ Γ T a) :=
  fun s t =>
    if h : Term.beq s t = true then isTrue (Term.eq_of_beq s t h)
    else isFalse (fun e => h (by subst e; exact Term.beq_refl s))

/-! ## Transport between similar contexts -/

mutual
  def Func.transport {σ : Signature} {Γ Γ' : Ctx} (h : Γ.Sim Γ') :
      {n : ℕ} → Func σ Γ n → Func σ Γ' n
    | _, .F f => .F f
    | _, .eval g t => .eval (Func.transport h g) (Term.transport h t)

  /-- ⭐Cast-free, and never enters a modal body: only the stored proofs change. -/
  def Term.transport {σ : Signature} {Γ Γ' : Ctx} (h : Γ.Sim Γ') :
      {T : VarType} → {a : Ann T} → Term σ Γ T a → Term σ Γ' T a
    | _, _, .var v hv => .var v (h.var v hv)
    | _, _, .func f => .func (Func.transport h f)
    | _, _, .unit => .unit
    | _, _, .pair s t => .pair (Term.transport h s) (Term.transport h t)
    | _, _, .boxtm t hΔ hb => .boxtm t (hΔ.trans h.box.symm) hb
    | _, _, .diatm x X hx t hΔ hb =>
        .diatm x X (h.dia x X hx).1 t (hΔ.trans (h.dia x X hx).2.symm) hb
end

mutual
  theorem Func.transport_transport {σ : Signature} {Γ Γ' Γ'' : Ctx} (h : Γ.Sim Γ')
      (h' : Γ'.Sim Γ'') : {n : ℕ} → (f : Func σ Γ n) →
      Func.transport h' (Func.transport h f) = Func.transport (h.trans h') f
    | _, .F _ => rfl
    | _, .eval g t => by
        simp only [Func.transport, Func.transport_transport h h' g,
          Term.transport_transport h h' t]

  theorem Term.transport_transport {σ : Signature} {Γ Γ' Γ'' : Ctx} (h : Γ.Sim Γ')
      (h' : Γ'.Sim Γ'') : {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) →
      Term.transport h' (Term.transport h t) = Term.transport (h.trans h') t
    | _, _, .var _ _ => rfl
    | _, _, .func f => by simp only [Term.transport, Func.transport_transport h h' f]
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        simp only [Term.transport, Term.transport_transport h h' s,
          Term.transport_transport h h' t]
    | _, _, .boxtm _ _ _ => rfl
    | _, _, .diatm _ _ _ _ _ _ => rfl
end

mutual
  theorem Func.transport_refl {σ : Signature} {Γ : Ctx} (h : Γ.Sim Γ) :
      {n : ℕ} → (f : Func σ Γ n) → Func.transport h f = f
    | _, .F _ => rfl
    | _, .eval g t => by
        simp only [Func.transport, Func.transport_refl h g, Term.transport_refl h t]

  theorem Term.transport_refl {σ : Signature} {Γ : Ctx} (h : Γ.Sim Γ) :
      {T : VarType} → {a : Ann T} → (t : Term σ Γ T a) → Term.transport h t = t
    | _, _, .var _ _ => rfl
    | _, _, .func f => by simp only [Term.transport, Func.transport_refl h f]
    | _, _, .unit => rfl
    | _, _, .pair s t => by
        simp only [Term.transport, Term.transport_refl h s, Term.transport_refl h t]
    | _, _, .boxtm _ _ _ => rfl
    | _, _, .diatm _ _ _ _ _ _ => rfl
end

/-! ## Splitting and unsplitting

⭐This is the whole of pair elimination on terms: a term over a split context IS a term over the
unsplit one, up to replacing proofs. -/

def Term.unsplit {σ : Signature} {Γ : Ctx} (P : Root → Pat) {T : VarType} {a : Ann T} :
    Term σ (Γ.refine P) T a → Term σ Γ T a :=
  Term.transport (Γ.sim_refine_left P)

def Term.split {σ : Signature} {Γ : Ctx} (P : Root → Pat) {T : VarType} {a : Ann T} :
    Term σ Γ T a → Term σ (Γ.refine P) T a :=
  Term.transport (Γ.sim_refine_right P)

@[simp] theorem Term.unsplit_split {σ : Signature} {Γ : Ctx} (P : Root → Pat) {T : VarType}
    {a : Ann T} (t : Term σ Γ T a) : (t.split P).unsplit P = t :=
  (Term.transport_transport _ _ t).trans (Term.transport_refl _ t)

@[simp] theorem Term.split_unsplit {σ : Signature} {Γ : Ctx} (P : Root → Pat) {T : VarType}
    {a : Ann T} (t : Term σ (Γ.refine P) T a) : (t.unsplit P).split P = t :=
  (Term.transport_transport _ _ t).trans (Term.transport_refl _ t)

end V12
