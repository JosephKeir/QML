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
* `DecidableEq` is written by hand: the stored contexts are functions, but both sides' contexts
  equal the same computed one, so they are substituted away rather than compared.
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

/-! ## Decidable equality -/

mutual
  def Func.decEq {σ : Signature} {Γ : Ctx} {n : ℕ} (f g : Func σ Γ n) : Decidable (f = g) :=
    match f, g with
    | .F f, .F g =>
        if h : f = g then isTrue (by subst h; rfl) else isFalse (fun e => by cases e; exact h rfl)
    | .F _, .eval _ _ => isFalse (fun e => by cases e)
    | .eval _ _, .F _ => isFalse (fun e => by cases e)
    | .eval f s, .eval g t =>
        match Func.decEq f g, Term.decEq s t with
        | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
        | isFalse h₁, _ => isFalse (fun e => by cases e; exact h₁ rfl)
        | _, isFalse h₂ => isFalse (fun e => by cases e; exact h₂ rfl)
  termination_by sizeOf f

  def Term.decEq {σ : Signature} {Γ : Ctx} {T : VarType} {b : Ann T} (s t : Term σ Γ T b) :
      Decidable (s = t) :=
    match s, t with
    | .var v _, .var w _ =>
        if h : v = w then isTrue (by subst h; rfl) else isFalse (fun e => by cases e; exact h rfl)
    | .var _ _, .func _ => isFalse (fun e => by cases e)
    | .func _, .var _ _ => isFalse (fun e => by cases e)
    | .func f, .func g =>
        match Func.decEq f g with
        | isTrue h => isTrue (by subst h; rfl)
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | .unit, .unit => isTrue rfl
    | .pair s₁ s₂, .pair t₁ t₂ =>
        match Term.decEq s₁ t₁, Term.decEq s₂ t₂ with
        | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
        | isFalse h₁, _ => isFalse (fun e => by cases e; exact h₁ rfl)
        | _, isFalse h₂ => isFalse (fun e => by cases e; exact h₂ rfl)
    | .boxtm (Δ := Δ₁) (a := a₁) t₁ hΔ₁ hb₁, .boxtm (Δ := Δ₂) (a := a₂) t₂ hΔ₂ hb₂ =>
        if ha : a₁ = a₂ then
          have hΔ : Δ₂ = Δ₁ := hΔ₂.trans hΔ₁.symm
          -- the recursion stays on `t₁`; only `t₂` is cast
          match Term.decEq t₁ (cast (by rw [hΔ, ha]) t₂) with
          | isTrue h => isTrue (by subst ha hΔ₁ hΔ₂; subst h; rfl)
          | isFalse h => isFalse (fun e => by subst ha hΔ₁ hΔ₂; cases e; exact h rfl)
        else isFalse (fun e => by cases e; exact ha rfl)
    | .diatm (Δ := Δ₁) (a := a₁) x₁ X₁ _ t₁ hΔ₁ hb₁,
      .diatm (Δ := Δ₂) (a := a₂) x₂ X₂ _ t₂ hΔ₂ hb₂ =>
        if hx : x₁ = x₂ then
          if hX : X₁ = X₂ then
            if ha : a₁ = a₂ then
              have hΔ : Δ₂ = Δ₁ := hΔ₂.trans (by subst hx hX; exact hΔ₁.symm)
              match Term.decEq t₁ (cast (by rw [hΔ, ha]) t₂) with
              | isTrue h => isTrue (by subst hx hX ha hΔ₁ hΔ₂; subst h; rfl)
              | isFalse h => isFalse (fun e => by subst hx hX ha hΔ₁ hΔ₂; cases e; exact h rfl)
            else isFalse (fun e => by cases e; exact ha rfl)
          else isFalse (fun e => by cases e; exact hX rfl)
        else isFalse (fun e => by cases e; exact hx rfl)
  termination_by sizeOf s
end

instance {σ : Signature} {Γ : Ctx} {n : ℕ} : DecidableEq (Func σ Γ n) := Func.decEq
instance {σ : Signature} {Γ : Ctx} {T : VarType} {b : Ann T} : DecidableEq (Term σ Γ T b) :=
  Term.decEq

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
