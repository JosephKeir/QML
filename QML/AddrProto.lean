import Mathlib.Tactic

/-!
# Address prototype: modal steps inside names

Names are ADDRESSES: a root and a path of steps `fst | snd | box | dia`.  Inside `□` the content
of `z : □A` is the name `z.box`; the witness of `◇_{z.box.fst}` is that name.  An annotation index
is an address, fixed where its root was declared, so it is the same at every modal level: there
are no out-maps.

A context is a partial function on addresses: the positions visible at the current level (roots,
and `….box` / `….dia` names).  Product components are always reached by projection (`Ctx.ref`).
Formulas carry their binder depth `d`; a quantifier binds the slot `bnd d`.
-/

namespace AddrProto

inductive VarType where
  | Var
  | VTypeOne
  | VTypeProd (A B : VarType)
  | VTypeBox (A : VarType)
  | VTypeDia (A : VarType)
deriving DecidableEq

inductive Step where
  | fst
  | snd
  | box
  | dia
deriving DecidableEq

inductive Root where
  | free (n : ℕ)
  | bnd (n : ℕ)
deriving DecidableEq

/-- An address: a root and steps, the innermost step LAST. -/
inductive Name where
  | root (r : Root)
  | step (v : Name) (s : Step)
deriving DecidableEq

def Name.rt : Name → Root
  | root r => r
  | step v _ => v.rt

/-- The steps, root-first. -/
def Name.path : Name → List Step
  | root _ => []
  | step v s => v.path ++ [s]

def Name.ext : Name → List Step → Name
  | v, [] => v
  | v, s :: p => Name.ext (.step v s) p

def Name.reroot (r' : Root) : Name → Name
  | root _ => root r'
  | step v s => step (v.reroot r') s

def Name.lastProd : Name → Bool
  | root _ => false
  | step _ s => match s with
    | .fst => true
    | .snd => true
    | _ => false

theorem Name.ext_rt : ∀ (v : Name) (p : List Step), (v.ext p).rt = v.rt
  | _, [] => rfl
  | v, s :: p => Name.ext_rt (.step v s) p

theorem Name.ext_path : ∀ (v : Name) (p : List Step), (v.ext p).path = v.path ++ p
  | v, [] => by simp [Name.ext]
  | v, s :: p => by
      change (Name.ext (.step v s) p).path = _
      rw [Name.ext_path]
      simp [Name.path]

theorem Name.reroot_ext (r' : Root) :
    ∀ (v : Name) (p : List Step), (v.ext p).reroot r' = (v.reroot r').ext p
  | _, [] => rfl
  | v, s :: p => Name.reroot_ext r' (.step v s) p

def VarType.step : VarType → Step → Option VarType
  | .VTypeProd A _, .fst => some A
  | .VTypeProd _ B, .snd => some B
  | .VTypeBox A, .box => some A
  | .VTypeDia A, .dia => some A
  | _, _ => none

def Step.isProd : Step → Bool
  | .fst => true
  | .snd => true
  | _ => false

/-! ## Contexts and their modal views -/

abbrev Ctx := Name → Option VarType

/-- The type reachable at a name: product steps project from the parent, modal steps must be
    visible. -/
def Ctx.ref (Γ : Ctx) : Name → Option VarType
  | .root r => Γ (.root r)
  | .step v s => if s.isProd then (Γ.ref v).bind (·.step s) else Γ (.step v s)

/-- Inside `□`: `v.box : A` exactly when `v : □A` is reachable. -/
def Ctx.boxIn (Γ : Ctx) : Ctx := fun v =>
  match v with
  | .step u .box =>
      match Γ.ref u with
      | some (.VTypeBox A) => some A
      | _ => none
  | _ => none

/-- Inside `◇_x`: the `□` view, and `x.dia : X` where `x : ◇X`. -/
def Ctx.diaIn (Γ : Ctx) (x : Name) : Ctx := fun v =>
  match v with
  | .step u .dia =>
      if u = x then
        match Γ.ref x with
        | some (.VTypeDia X) => some X
        | _ => none
      else none
  | v => Γ.boxIn v

def Ctx.insert (Γ : Ctx) (r : Root) (T : VarType) : Ctx :=
  fun v => if v = .root r then some T else Γ v

theorem Ctx.ref_nonprod (Γ : Ctx) : ∀ {v : Name}, v.lastProd = false → Γ.ref v = Γ v
  | .root _, _ => rfl
  | .step v s, h => by
      change (if s.isProd then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = _
      have hs : s.isProd = false := by cases s <;> first | rfl | cases h
      rw [if_neg (Bool.eq_false_iff.mp hs)]

theorem Ctx.ref_none_of_rootFresh {Γ : Ctx} {r : Root} (h : ∀ v, v.rt = r → Γ v = none) :
    ∀ v, v.rt = r → Γ.ref v = none := by
  intro v
  induction v with
  | root r' => intro hv; exact h _ hv
  | step v s ih =>
      intro hv
      simp only [Ctx.ref]
      split_ifs
      · simp only [ih hv, Option.bind_none]
      · exact h _ hv

/-! ## Signature, annotations, terms -/

structure Signature where
  FuncSyms : Type
  RelSyms : Type
  funcArity : FuncSyms → ℕ
  relArity : RelSyms → ℕ
  [decEqF : DecidableEq FuncSyms]
  [decEqR : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

inductive Ann : VarType → Type where
  | var : Ann .Var
  | one : Ann .VTypeOne
  | prod {A B : VarType} (a : Ann A) (b : Ann B) : Ann (.VTypeProd A B)
  | box {A : VarType} (a : Ann A) : Ann (.VTypeBox A)
  | dia {A : VarType} (i : Name) (a : Ann A) : Ann (.VTypeDia A)
deriving DecidableEq

def Ann.mapIdx (f : Name → Name) : {T : VarType} → Ann T → Ann T
  | _, .var => .var
  | _, .one => .one
  | _, .prod a b => .prod (a.mapIdx f) (b.mapIdx f)
  | _, .box a => .box (a.mapIdx f)
  | _, .dia i a => .dia (f i) (a.mapIdx f)

/-- The index at the `◇`-node a path reaches (junk otherwise). -/
def Ann.idxAt : {T : VarType} → Ann T → List Step → Name
  | _, .dia i _, [] => i
  | _, .prod a _, .fst :: p => a.idxAt p
  | _, .prod _ b, .snd :: p => b.idxAt p
  | _, .box a, .box :: p => a.idxAt p
  | _, .dia _ a, .dia :: p => a.idxAt p
  | _, _, _ => .root (.free 0)

mutual
  inductive Func (σ : Signature) : Ctx → ℕ → Type where
    | F {Γ : Ctx} {n : ℕ} (f : {f : σ.FuncSyms // σ.funcArity f = n}) : Func σ Γ n
    | eval {Γ : Ctx} {n : ℕ} : Func σ Γ (n + 1) → Term σ Γ .Var .var → Func σ Γ n
  deriving DecidableEq

  /-- ⭐Annotations are plain constructor applications: no out-maps, no Forded fields. -/
  inductive Term (σ : Signature) : Ctx → (T : VarType) → Ann T → Type where
    | var {Γ : Ctx} (v : Name) (h : Γ.ref v = some .Var) : Term σ Γ .Var .var
    | func {Γ : Ctx} : Func σ Γ 0 → Term σ Γ .Var .var
    | unit {Γ : Ctx} : Term σ Γ .VTypeOne .one
    | pair {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B} :
        Term σ Γ A a → Term σ Γ B b → Term σ Γ (.VTypeProd A B) (.prod a b)
    | boxtm {Γ : Ctx} {A : VarType} {a : Ann A} :
        Term σ Γ.boxIn A a → Term σ Γ (.VTypeBox A) (.box a)
    | diatm {Γ : Ctx} {A : VarType} {a : Ann A} (x : Name)
        (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
        Term σ (Γ.diaIn x) A a → Term σ Γ (.VTypeDia A) (.dia x a)
  deriving DecidableEq
end

set_option inductive.autoPromoteIndices false in
inductive Rel (σ : Signature) : Ctx → ℕ → Type where
  | R {Γ : Ctx} {n : ℕ} (r : {r : σ.RelSyms // σ.relArity r = n}) : Rel σ Γ n
  | eval {Γ : Ctx} {n : ℕ} : Rel σ Γ (n + 1) → Term σ Γ .Var .var → Rel σ Γ n
deriving DecidableEq

/-- Formulas over `Γ` at binder depth `d`: a quantifier binds the slot `bnd d`. -/
inductive Wff (σ : Signature) : Ctx → ℕ → Type where
  | atom {Γ : Ctx} {d : ℕ} : Rel σ Γ 0 → Wff σ Γ d
  | eq {Γ : Ctx} {d : ℕ} : Term σ Γ .Var .var → Term σ Γ .Var .var → Wff σ Γ d
  | top {Γ : Ctx} {d : ℕ} : Wff σ Γ d
  | bot {Γ : Ctx} {d : ℕ} : Wff σ Γ d
  | and {Γ : Ctx} {d : ℕ} : Wff σ Γ d → Wff σ Γ d → Wff σ Γ d
  | imp {Γ : Ctx} {d : ℕ} : Wff σ Γ d → Wff σ Γ d → Wff σ Γ d
  | all {Γ : Ctx} {d : ℕ} (T : VarType) : Wff σ (Γ.insert (.bnd d) T) (d + 1) → Wff σ Γ d
  | ex {Γ : Ctx} {d : ℕ} (T : VarType) : Wff σ (Γ.insert (.bnd d) T) (d + 1) → Wff σ Γ d
  | box {Γ : Ctx} {d : ℕ} : Wff σ Γ.boxIn d → Wff σ Γ d
  | dia {Γ : Ctx} {d : ℕ} (x : Name) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
      Wff σ (Γ.diaIn x) d → Wff σ Γ d
deriving DecidableEq

/-- ⭐Same annotation ⇒ same witness and same inner context, definitionally: no casts. -/
def eqRec {σ : Signature} {d : ℕ} : {Γ : Ctx} → (T : VarType) → {a : Ann T} →
    Term σ Γ T a → Term σ Γ T a → Wff σ Γ d
  | _, .Var, .var, t, s => .eq t s
  | _, .VTypeOne, _, _, _ => .top
  | _, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => .and (eqRec A t₁ s₁) (eqRec B t₂ s₂)
  | _, .VTypeBox A, .box _, .boxtm t, .boxtm s => .box (eqRec A t s)
  | _, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s =>
      .imp (.dia x hx (.imp (eqRec A t s) .bot)) .bot

/-! ## Weakening: more positions visible -/

def Ctx.Le (Γ Γ' : Ctx) : Prop := ∀ v T, Γ v = some T → Γ' v = some T

theorem Ctx.Le.refl (Γ : Ctx) : Γ.Le Γ := fun _ _ h => h

theorem Ctx.Le.ref {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ {v : Name} {T : VarType}, Γ.ref v = some T → Γ'.ref v = some T := by
  intro v
  induction v with
  | root r => intro T hv; exact h _ _ hv
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref] at hv ⊢
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [hU] at hv; rw [ih hU]; exact hv
      · exact h _ _ hv

theorem Ctx.Le.boxIn {Γ Γ' : Ctx} (h : Γ.Le Γ') : Γ.boxIn.Le Γ'.boxIn := by
  intro v T hv
  match v with
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      change (match Γ'.ref u with | some (.VTypeBox A) => some A | _ => none) = some T
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U => rw [hu] at hv; rw [h.ref hu]; exact hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

theorem Ctx.Le.diaIn {Γ Γ' : Ctx} (h : Γ.Le Γ') (x : Name) : (Γ.diaIn x).Le (Γ'.diaIn x) := by
  intro v T hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      change (if u = x then (match Γ'.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T
      split_ifs at hv ⊢ with hux
      · cases hx : Γ.ref x with
        | none => rw [hx] at hv; cases hv
        | some U => rw [hx] at hv; rw [h.ref hx]; exact hv
  | .step u .box => exact h.boxIn (.step u .box) T hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

theorem Ctx.Le.insert {Γ Γ' : Ctx} (h : Γ.Le Γ') (r : Root) (T : VarType) :
    (Γ.insert r T).Le (Γ'.insert r T) := by
  intro v U hv
  simp only [Ctx.insert] at hv ⊢
  split_ifs at hv ⊢
  · exact hv
  · exact h v U hv

theorem Ctx.le_boxIn_diaIn (Γ : Ctx) (x : Name) : Γ.boxIn.Le (Γ.diaIn x) := by
  intro v T hv
  match v with
  | .step u .box => exact hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

theorem Ctx.le_insert {Γ : Ctx} {r : Root} (hr : Γ (.root r) = none) (T : VarType) :
    Γ.Le (Γ.insert r T) := by
  intro v U hv
  simp only [Ctx.insert]
  split_ifs with h
  · subst h
    rw [hr] at hv
    cases hv
  · exact hv

mutual
  def Func.mono {σ : Signature} : {Γ Γ' : Ctx} → Γ.Le Γ' → {n : ℕ} → Func σ Γ n → Func σ Γ' n
    | _, _, _, _, .F f => .F f
    | _, _, h, _, .eval g t => .eval (Func.mono h g) (Term.mono h t)

  /-- ⭐Weakening: annotations untouched, no scoping needed. -/
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

def Rel.mono {σ : Signature} {Γ Γ' : Ctx} (h : Γ.Le Γ') : {n : ℕ} → Rel σ Γ n → Rel σ Γ' n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.mono h ρ) (Term.mono h t)

def Wff.mono {σ : Signature} : {Γ Γ' : Ctx} → {d : ℕ} → Γ.Le Γ' → Wff σ Γ d → Wff σ Γ' d
  | _, _, _, h, .atom ρ => .atom (Rel.mono h ρ)
  | _, _, _, h, .eq t s => .eq (Term.mono h t) (Term.mono h s)
  | _, _, _, _, .top => .top
  | _, _, _, _, .bot => .bot
  | _, _, _, h, .and φ ψ => .and (Wff.mono h φ) (Wff.mono h ψ)
  | _, _, _, h, .imp φ ψ => .imp (Wff.mono h φ) (Wff.mono h ψ)
  | _, _, _, h, .all T φ => .all T (Wff.mono (h.insert _ T) φ)
  | _, _, _, h, .ex T φ => .ex T (Wff.mono (h.insert _ T) φ)
  | _, _, _, h, .box φ => .box (Wff.mono h.boxIn φ)
  | _, _, _, h, .dia x hx φ => .dia x (hx.imp fun _ hX => h.ref hX) (Wff.mono (h.diaIn x) φ)

/-! ## Fresh quantifier slots -/

/-- No slot at or above `d` is visible. -/
def Ctx.SlotsFrom (Γ : Ctx) (d : ℕ) : Prop := ∀ v n, v.rt = .bnd n → d ≤ n → Γ v = none

theorem Ctx.SlotsFrom.root {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) : Γ (.root (.bnd d)) = none :=
  h _ d rfl le_rfl

theorem Ctx.SlotsFrom.insert {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (T : VarType) :
    (Γ.insert (.bnd d) T).SlotsFrom (d + 1) := by
  intro v n hv hn
  simp only [Ctx.insert]
  split_ifs with hvr
  · subst hvr
    cases hv
    omega
  · exact h v n hv (by omega)

theorem Ctx.SlotsFrom.insertFree {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (u : ℕ) (T : VarType) :
    (Γ.insert (.free u) T).SlotsFrom d := by
  intro v n hv hn
  simp only [Ctx.insert]
  split_ifs with hvr
  · subst hvr
    cases hv
  · exact h v n hv hn

theorem Ctx.SlotsFrom.boxIn {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) : Γ.boxIn.SlotsFrom d := by
  intro v n hv hn
  have hfresh : ∀ w, w.rt = .bnd n → Γ w = none := fun w hw => h w n hw hn
  match v with
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = none
      simp only [Ctx.ref_none_of_rootFresh hfresh u hv]
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .dia => rfl

theorem Ctx.SlotsFrom.diaIn {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (x : Name) :
    (Γ.diaIn x).SlotsFrom d := by
  intro v n hv hn
  have hfresh : ∀ w, w.rt = .bnd n → Γ w = none := fun w hw => h w n hw hn
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = none
      split_ifs with hux
      · rw [← hux]
        simp only [Ctx.ref_none_of_rootFresh hfresh u hv]
      · rfl
  | .step u .box => exact h.boxIn (.step u .box) n hv hn
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl

/-! ## Substitution entries

A substitution at some modal level sends each VISIBLE source name to an entry over the current
target: a name or a term.  Product components are reached by projection (`Subst.at`).  Under `□`,
`◇_x` and binders it is transformed pointwise.  Annotations are mapped by an address map `ι`;
`Subst.Coh` says the entries agree with it. -/

inductive SubE (σ : Signature) (Δ : Ctx) : Type where
  | hide
  | ren (w : Name)
  | tm {T : VarType} {a : Ann T} (s : Term σ Δ T a)

namespace SubE

variable {σ : Signature} {Δ : Ctx}

def proj : SubE σ Δ → Step → SubE σ Δ
  | .ren w, s => .ren (.step w s)
  | .tm (.pair s _), .fst => .tm s
  | .tm (.pair _ t), .snd => .tm t
  | _, _ => .hide

def unbox : SubE σ Δ → SubE σ Δ.boxIn
  | .ren w => .ren (.step w .box)
  | .tm (.boxtm t) => .tm t
  | _ => .hide

def mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) : SubE σ Δ₁ → SubE σ Δ₂
  | .hide => .hide
  | .ren w => .ren w
  | .tm s => .tm (Term.mono h s)

/-- The entry at the witness body, for the new witness `ιx` (modal β for a term entry). -/
def diaBody (ιx : Name) : SubE σ Δ → SubE σ (Δ.diaIn ιx)
  | .ren _ => .ren (.step ιx .dia)
  | .tm (.diatm y _hy u) =>
      if h : y = ιx then .tm (Term.mono (by subst h; exact Ctx.Le.refl _) u) else .hide
  | _ => .hide

def OkRef : SubE σ Δ → VarType → Prop
  | .ren w, T => Δ.ref w = some T
  | .tm (T := U) _, T => U = T
  | .hide, _ => False

def idxAlong : SubE σ Δ → List Step → Name
  | .ren w, p => w.ext p
  | .tm (a := a) _, p => a.idxAt p
  | .hide, _ => .root (.free 0)

def toVar : (e : SubE σ Δ) → e.OkRef .Var → Term σ Δ .Var .var
  | .ren w, h => .var w h
  | .tm (.var v hv), _ => .var v hv
  | .tm (.func f), _ => .func f
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _), h => nomatch h
  | .tm (.diatm _ _ _), h => nomatch h
  | .hide, h => False.elim h

theorem okRef_proj : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step}, e.OkRef U → s.isProd = true →
    U.step s = some T → (e.proj s).OkRef T
  | .ren w, U, T, s, he, hs, hst => by
      change (if s.isProd then (Δ.ref w).bind (·.step s) else Δ (.step w s)) = some T
      rw [if_pos hs, he]
      exact hst
  | .hide, _, _, _, he, _, _ => False.elim he
  | .tm (T := U') s₀, U, T, s, he, hs, hst => by
      have hU : U' = U := he
      subst hU
      cases s <;> (try cases hs) <;> cases s₀ <;> first | (cases hst; rfl) | cases hst

theorem idxAlong_proj : ∀ {e : SubE σ Δ} {U T : VarType} {s : Step} (p : List Step),
    e.OkRef U → s.isProd = true → U.step s = some T →
      (e.proj s).idxAlong p = e.idxAlong (s :: p)
  | .ren _, _, _, _, _, _, _, _ => rfl
  | .hide, _, _, _, _, he, _, _ => False.elim he
  | .tm (T := U') s₀, U, T, s, p, he, hs, hst => by
      have hU : U' = U := he
      subst hU
      cases s <;> (try cases hs) <;> cases s₀ <;> first | rfl | cases hst

theorem okRef_unbox : ∀ {e : SubE σ Δ} {A : VarType}, e.OkRef (.VTypeBox A) → e.unbox.OkRef A
  | .ren w, A, he => by
      change (match Δ.ref w with | some (.VTypeBox A) => some A | _ => none) = some A
      rw [he]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem idxAlong_unbox : ∀ {e : SubE σ Δ} {A : VarType} (p : List Step),
    e.OkRef (.VTypeBox A) → e.unbox.idxAlong p = e.idxAlong (.box :: p)
  | .ren _, _, _, _ => rfl
  | .hide, _, _, he => False.elim he
  | .tm (T := U) s, A, p, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem okRef_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ {e : SubE σ Δ₁} {T : VarType}, e.OkRef T → (e.mono h).OkRef T
  | .ren _, _, he => h.ref he
  | .tm _, _, he => he
  | .hide, _, he => False.elim he

theorem idxAlong_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ (e : SubE σ Δ₁) (p : List Step), (e.mono h).idxAlong p = e.idxAlong p
  | .ren _, _ => rfl
  | .tm _, _ => rfl
  | .hide, _ => rfl

theorem okRef_diaBody {ιx : Name} : ∀ {e : SubE σ Δ} {X : VarType},
    e.OkRef (.VTypeDia X) → e.idxAlong [] = ιx → (e.diaBody ιx).OkRef X
  | .ren w, X, he, hw => by
      have hw' : w = ιx := hw
      subst hw'
      change (if w = w then (match Δ.ref w with | some (.VTypeDia X) => some X | _ => none)
        else none) = some X
      rw [if_pos rfl, he]
  | .tm (.diatm y _hy u), X, he, hw => by
      have hw' : y = ιx := hw
      rw [show ((SubE.tm (Term.diatm y _hy u) : SubE σ Δ).diaBody ιx) =
        SubE.tm (Term.mono (by subst hw'; exact Ctx.Le.refl _) u) from dif_pos hw']
      exact VarType.VTypeDia.inj he
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

theorem idxAlong_diaBody {ιx : Name} : ∀ {e : SubE σ Δ} {X : VarType} (p : List Step),
    e.OkRef (.VTypeDia X) → e.idxAlong [] = ιx →
      (e.diaBody ιx).idxAlong p = e.idxAlong (.dia :: p)
  | .ren w, _, p, _, hw => by
      have hw' : w = ιx := hw
      subst hw'
      rfl
  | .tm (.diatm y _hy u), X, p, he, hw => by
      have hw' : y = ιx := hw
      rw [show ((SubE.tm (Term.diatm y _hy u) : SubE σ Δ).diaBody ιx) =
        SubE.tm (Term.mono (by subst hw'; exact Ctx.Le.refl _) u) from dif_pos hw']
      rfl
  | .tm (.var _ _), _, _, he, _ => nomatch he
  | .tm (.func _), _, _, he, _ => nomatch he
  | .tm .unit, _, _, he, _ => nomatch he
  | .tm (.pair _ _), _, _, he, _ => nomatch he
  | .tm (.boxtm _), _, _, he, _ => nomatch he
  | .hide, _, _, he, _ => False.elim he

theorem ref_witness {w : Name} : ∀ {e : SubE σ Δ} {X : VarType},
    e.OkRef (.VTypeDia X) → e.idxAlong [] = w → ∃ Y, Δ.ref w = some (.VTypeDia Y)
  | .ren w', X, he, hw => by
      have hw' : w' = w := hw
      subst hw'
      exact ⟨X, he⟩
  | .tm (.diatm y hy _), _, _, hw => by
      have hw' : y = w := hw
      subst hw'
      exact hy
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm (.func _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

end SubE

/-! ## Substitutions at a modal level -/

abbrev Subst (σ : Signature) (Δ : Ctx) := Name → SubE σ Δ

/-- Shift addresses under the slot `bnd d` to the slot `bnd d'`. -/
def Name.shiftSlot (ι : Name → Name) (d d' : ℕ) : Name → Name :=
  fun i => if i.rt = .bnd d then i.reroot (.bnd d') else ι i

namespace Subst

variable {σ : Signature} {Δ : Ctx}

/-- The entry reachable at a name: product components by projection. -/
def «at» (θ : Subst σ Δ) : Name → SubE σ Δ
  | .root r => θ (.root r)
  | .step v s => if s.isProd then (θ.at v).proj s else θ (.step v s)

def Ok (Γ : Ctx) (θ : Subst σ Δ) : Prop := ∀ v T, Γ v = some T → (θ v).OkRef T

def Coh (ι : Name → Name) (Γ : Ctx) (θ : Subst σ Δ) : Prop :=
  ∀ v T, Γ.ref v = some T → ∀ p, (θ.at v).idxAlong p = ι (v.ext p)

def box (θ : Subst σ Δ) : Subst σ Δ.boxIn := fun v =>
  match v with
  | .step u .box => (θ.at u).unbox
  | _ => .hide

def dia (θ : Subst σ Δ) (x ιx : Name) : Subst σ (Δ.diaIn ιx) := fun v =>
  match v with
  | .step u .dia => if u = x then (θ.at x).diaBody ιx else .hide
  | .step u .box => (θ.at u).unbox.mono (Ctx.le_boxIn_diaIn Δ ιx)
  | _ => .hide

/-- Under a binder: the source slot goes to the target slot; everything else is weakened. -/
def under (θ : Subst σ Δ) (d d' : ℕ) (T : VarType) (h : Δ (.root (.bnd d')) = none) :
    Subst σ (Δ.insert (.bnd d') T) := fun v =>
  if v = .root (.bnd d) then .ren (.root (.bnd d')) else (θ v).mono (Ctx.le_insert h T)

theorem at_nonprod (θ : Subst σ Δ) : ∀ {v : Name}, v.lastProd = false → θ.at v = θ v
  | .root _, _ => rfl
  | .step v s, h => by
      change (if s.isProd then (θ.at v).proj s else θ (.step v s)) = _
      have hs : s.isProd = false := by cases s <;> first | rfl | cases h
      rw [if_neg (Bool.eq_false_iff.mp hs)]

theorem okRef_at {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) :
    ∀ {v : Name} {T : VarType}, Γ.ref v = some T → (θ.at v).OkRef T := by
  intro v
  induction v with
  | root r => intro T hv; exact hθ _ _ hv
  | step v s ih =>
      intro T hv
      simp only [Ctx.ref, Subst.at] at hv ⊢
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            exact SubE.okRef_proj (ih hU) hs hv
      · exact hθ _ _ hv

/-- Coherence follows from coherence on the visible non-product names. -/
theorem coh_of {ι : Name → Name} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ)
    (hvis : ∀ v T, v.lastProd = false → Γ v = some T → ∀ p, (θ v).idxAlong p = ι (v.ext p)) :
    Coh ι Γ θ := by
  intro v
  induction v with
  | root r => intro T hv p; exact hvis _ _ rfl hv p
  | step v s ih =>
      intro T hv p
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            rw [SubE.idxAlong_proj p (okRef_at hθ hU) hs hv, ih U hU (s :: p)]
            rfl
      · have hlp : (Name.step v s).lastProd = false := by
          cases s <;> first | rfl | exact absurd rfl hs
        exact hvis _ _ hlp hv p

theorem ok_box {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) : Ok Γ.boxIn θ.box := by
  intro v T hv
  match v with
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [hu] at hv
          cases U <;> try cases hv
          exact SubE.okRef_unbox (okRef_at hθ hu)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

theorem coh_box {ι : Name → Name} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) (hc : Coh ι Γ θ) :
    Coh ι Γ.boxIn θ.box := by
  refine coh_of (ok_box hθ) ?_
  intro v T _ hv p
  match v with
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [hu] at hv
          cases U <;> try cases hv
          change ((θ.at u).unbox).idxAlong p = _
          rw [SubE.idxAlong_unbox p (okRef_at hθ hu), hc u _ hu (.box :: p)]
          rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

theorem ok_dia {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {x ιx : Name}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (hw : (θ.at x).idxAlong [] = ιx) :
    Ok (Γ.diaIn x) (θ.dia x ιx) := by
  obtain ⟨X, hx⟩ := hx
  intro v T hv
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · rw [hx] at hv
        cases hv
        change (if u = x then (θ.at x).diaBody ιx else SubE.hide).OkRef X
        rw [if_pos hux]
        exact SubE.okRef_diaBody (okRef_at hθ hx) hw
  | .step u .box => exact SubE.okRef_mono _ (ok_box hθ (.step u .box) T hv)
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

theorem coh_dia {ι : Name → Name} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) (hc : Coh ι Γ θ)
    {x : Name} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
    Coh ι (Γ.diaIn x) (θ.dia x (ι x)) := by
  have hw : (θ.at x).idxAlong [] = ι x := by
    obtain ⟨X, hX⟩ := hx
    exact hc x _ hX []
  refine coh_of (ok_dia hθ hx hw) ?_
  obtain ⟨X, hx⟩ := hx
  intro v T _ hv p
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with hux
      · subst hux
        change (if u = u then (θ.at u).diaBody (ι u) else SubE.hide).idxAlong p = _
        rw [if_pos rfl, SubE.idxAlong_diaBody p (okRef_at hθ hx) hw, hc u _ hx (.dia :: p)]
        rfl
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = some T at hv
      cases hu : Γ.ref u with
      | none => rw [hu] at hv; cases hv
      | some U =>
          rw [hu] at hv
          cases U <;> try cases hv
          change (((θ.at u).unbox).mono _).idxAlong p = _
          rw [SubE.idxAlong_mono, SubE.idxAlong_unbox p (okRef_at hθ hu), hc u _ hu (.box :: p)]
          rfl
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv

theorem ok_under {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) {d d' : ℕ} (T : VarType)
    (h : Δ (.root (.bnd d')) = none) : Ok (Γ.insert (.bnd d) T) (θ.under d d' T h) := by
  intro v U hv
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    have hTU : T = U := by simpa [Ctx.insert] using hv
    subst hTU
    rw [show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
    change (Δ.insert (.bnd d') T) (.root (.bnd d')) = some T
    simp [Ctx.insert]
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    rw [show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr]
    exact SubE.okRef_mono _ (hθ v U hv')

theorem coh_under {ι : Name → Name} {Γ : Ctx} {θ : Subst σ Δ} (hθ : Ok Γ θ) (hc : Coh ι Γ θ)
    {d d' : ℕ} (hΓ : Γ.SlotsFrom d) (T : VarType) (h : Δ (.root (.bnd d')) = none) :
    Coh (Name.shiftSlot ι d d') (Γ.insert (.bnd d) T) (θ.under d d' T h) := by
  refine coh_of (ok_under hθ T h) ?_
  intro v U hlp hv p
  by_cases hvr : v = .root (.bnd d)
  · subst hvr
    rw [show θ.under d d' T h (.root (.bnd d)) = .ren (.root (.bnd d')) from if_pos rfl]
    change (Name.root (.bnd d')).ext p =
      (if ((Name.root (.bnd d)).ext p).rt = .bnd d then ((Name.root (.bnd d)).ext p).reroot (.bnd d')
        else ι _)
    have hc0 : (Name.root (Root.bnd d)).rt = Root.bnd d := rfl
    rw [Name.ext_rt, if_pos hc0]
    exact (Name.reroot_ext (.bnd d') (.root (.bnd d)) p).symm
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hrt : v.rt ≠ .bnd d := fun he => by
      rw [hΓ v d he le_rfl] at hv'
      cases hv'
    rw [show θ.under d d' T h v = (θ v).mono (Ctx.le_insert h T) from if_neg hvr,
      SubE.idxAlong_mono, ← at_nonprod θ hlp, hc v U ((Ctx.ref_nonprod Γ hlp).trans hv') p]
    change ι (v.ext p) = if (v.ext p).rt = .bnd d then _ else ι (v.ext p)
    rw [Name.ext_rt, if_neg hrt]

end Subst

/-! ## Substitution in terms and formulas -/

mutual
  def Func.subst {σ : Signature} (ι : Name → Name) : {Γ Δ : Ctx} → (θ : Subst σ Δ) →
      Subst.Ok Γ θ → Subst.Coh ι Γ θ → {n : ℕ} → Func σ Γ n → Func σ Δ n
    | _, _, _, _, _, _, .F f => .F f
    | _, _, θ, hθ, hc, _, .eval g t => .eval (Func.subst ι θ hθ hc g) (Term.subst ι θ hθ hc t)

  /-- ⭐**Substitution**, intrinsically typed, annotations mapped by `ι`.  No casts, no out-map
      commutation: the `□` case is literally `boxtm` of the substituted body, and the `◇` case
      uses the new witness `ι x` directly. -/
  def Term.subst {σ : Signature} (ι : Name → Name) : {Γ Δ : Ctx} → (θ : Subst σ Δ) →
      Subst.Ok Γ θ → Subst.Coh ι Γ θ → {T : VarType} → {a : Ann T} →
      Term σ Γ T a → Term σ Δ T (a.mapIdx ι)
    | _, _, θ, hθ, _, _, _, .var _ hv => (θ.at _).toVar (Subst.okRef_at hθ hv)
    | _, _, θ, hθ, hc, _, _, .func f => .func (Func.subst ι θ hθ hc f)
    | _, _, _, _, _, _, _, .unit => .unit
    | _, _, θ, hθ, hc, _, _, .pair s t =>
        .pair (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
    | _, _, θ, hθ, hc, _, _, .boxtm t =>
        .boxtm (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) t)
    | _, _, θ, hθ, hc, _, _, .diatm x hx t =>
        have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
        .diatm (ι x) (hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw)
          (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) t)
end

def Rel.subst {σ : Signature} (ι : Name → Name) {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) : {n : ℕ} → Rel σ Γ n → Rel σ Δ n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.subst ι θ hθ hc ρ) (Term.subst ι θ hθ hc t)

/-- ⭐Substitution in formulas: under a binder the source slot `bnd d` goes to the target slot
    `bnd d'` and the address map is re-rooted there. -/
def Wff.subst {σ : Signature} : (ι : Name → Name) → {Γ Δ : Ctx} → {d d' : ℕ} →
    (θ : Subst σ Δ) → Subst.Ok Γ θ → Subst.Coh ι Γ θ → Γ.SlotsFrom d → Δ.SlotsFrom d' →
    Wff σ Γ d → Wff σ Δ d'
  | ι, _, _, _, _, θ, hθ, hc, _, _, .atom ρ => .atom (Rel.subst ι θ hθ hc ρ)
  | ι, _, _, _, _, θ, hθ, hc, _, _, .eq t s => .eq (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s)
  | _, _, _, _, _, _, _, _, _, _, .top => .top
  | _, _, _, _, _, _, _, _, _, _, .bot => .bot
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .and φ ψ =>
      .and (Wff.subst ι θ hθ hc hΓ hΔ φ) (Wff.subst ι θ hθ hc hΓ hΔ ψ)
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .imp φ ψ =>
      .imp (Wff.subst ι θ hθ hc hΓ hΔ φ) (Wff.subst ι θ hθ hc hΓ hΔ ψ)
  | ι, _, _, d, d', θ, hθ, hc, hΓ, hΔ, .all T φ =>
      .all T (Wff.subst (Name.shiftSlot ι d d') (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (hΓ.insert T) (hΔ.insert T) φ)
  | ι, _, _, d, d', θ, hθ, hc, hΓ, hΔ, .ex T φ =>
      .ex T (Wff.subst (Name.shiftSlot ι d d') (θ.under d d' T hΔ.root)
        (Subst.ok_under hθ T hΔ.root) (Subst.coh_under hθ hc hΓ T hΔ.root)
        (hΓ.insert T) (hΔ.insert T) φ)
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .box φ =>
      .box (Wff.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn φ)
  | ι, _, _, _, _, θ, hθ, hc, hΓ, hΔ, .dia x hx φ =>
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      .dia (ι x) (hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw)
        (Wff.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx)
          (hΓ.diaIn x) (hΔ.diaIn (ι x)) φ)

/-! ## Substitutions from a root assignment -/

/-- A top-level context shows only roots. -/
def Ctx.TopLevel (Γ : Ctx) : Prop := ∀ v T, Γ v = some T → ∃ r, v = .root r

theorem Ctx.TopLevel.insert {Γ : Ctx} (h : Γ.TopLevel) (r : Root) (T : VarType) :
    (Γ.insert r T).TopLevel := by
  intro v U hv
  simp only [Ctx.insert] at hv
  split_ifs at hv with hvr
  · exact ⟨r, hvr⟩
  · exact h v U hv

namespace Subst

variable {σ : Signature} {Δ : Ctx}

def ofRoots (ρ : Root → SubE σ Δ) : Subst σ Δ := fun v =>
  match v with
  | .root r => ρ r
  | _ => .hide

def idxOfRoots (ρ : Root → SubE σ Δ) : Name → Name := fun i => (ρ i.rt).idxAlong i.path

theorem ok_ofRoots {Γ : Ctx} {ρ : Root → SubE σ Δ} (hΓ : Γ.TopLevel)
    (hρ : ∀ r T, Γ (.root r) = some T → (ρ r).OkRef T) : Ok Γ (ofRoots ρ) := by
  intro v T hv
  obtain ⟨r, rfl⟩ := hΓ v T hv
  exact hρ r T hv

theorem coh_ofRoots {Γ : Ctx} {ρ : Root → SubE σ Δ} (hΓ : Γ.TopLevel)
    (hρ : ∀ r T, Γ (.root r) = some T → (ρ r).OkRef T) :
    Coh (idxOfRoots ρ) Γ (ofRoots ρ) := by
  refine coh_of (ok_ofRoots hΓ hρ) ?_
  intro v T _ hv p
  obtain ⟨r, rfl⟩ := hΓ v T hv
  change (ρ r).idxAlong p = (ρ ((Name.root r).ext p).rt).idxAlong ((Name.root r).ext p).path
  simp only [Name.ext_rt, Name.ext_path, Name.rt, Name.path, List.nil_append]

/-- `bnd d ↦ s`, every other root to itself. -/
def instRoots {Γ : Ctx} (d : ℕ) {T : VarType} {a : Ann T} (s : Term σ Γ T a) :
    Root → SubE σ Γ :=
  fun r => if r = .bnd d then .tm s else .ren (.root r)

/-- `free u ↦ bnd d`, every other root to itself. -/
def bindRoots (Δ : Ctx) (u d : ℕ) : Root → SubE σ Δ :=
  fun r => if r = .free u then .ren (.root (.bnd d)) else .ren (.root r)

end Subst

/-- ⭐Instantiation (for `∀`-elimination / `∃`-introduction). -/
def Wff.instantiate {σ : Signature} {Γ : Ctx} {d : ℕ} (hΓ : Γ.TopLevel) (hs : Γ.SlotsFrom d)
    {T : VarType} {a : Ann T} (s : Term σ Γ T a) (φ : Wff σ (Γ.insert (.bnd d) T) (d + 1)) :
    Wff σ Γ d :=
  have hρ : ∀ r U, (Γ.insert (.bnd d) T) (.root r) = some U →
      (Subst.instRoots d s r).OkRef U := by
    intro r U hU
    by_cases hr : r = .bnd d
    · subst hr
      have hTU : T = U := by simpa [Ctx.insert] using hU
      subst hTU
      rw [show Subst.instRoots _ s (.bnd _) = .tm s from if_pos rfl]
      rfl
    · have hU' : Γ (.root r) = some U := by simpa [Ctx.insert, hr] using hU
      rw [show Subst.instRoots d s r = .ren (.root r) from if_neg hr]
      exact hU'
  Wff.subst (Subst.idxOfRoots (Subst.instRoots d s)) (Subst.ofRoots (Subst.instRoots d s))
    (Subst.ok_ofRoots (hΓ.insert _ T) hρ) (Subst.coh_ofRoots (hΓ.insert _ T) hρ)
    (hs.insert T) hs φ

/-- ⭐Binding a free variable to the next slot (for `∀`-introduction / `∃`-elimination). -/
def Wff.bindFree {σ : Signature} {Γ : Ctx} {d : ℕ} (hΓ : Γ.TopLevel) (hs : Γ.SlotsFrom d)
    (u : ℕ) (T : VarType) (φ : Wff σ (Γ.insert (.free u) T) d) :
    Wff σ (Γ.insert (.bnd d) T) (d + 1) :=
  have hρ : ∀ r U, (Γ.insert (.free u) T) (.root r) = some U →
      (Subst.bindRoots (σ := σ) (Γ.insert (.bnd d) T) u d r).OkRef U := by
    intro r U hU
    by_cases hr : r = .free u
    · subst hr
      have hTU : T = U := by simpa [Ctx.insert] using hU
      subst hTU
      rw [show Subst.bindRoots (σ := σ) (Γ.insert (.bnd d) T) _ d (.free _) =
        .ren (.root (.bnd d)) from if_pos rfl]
      change (Γ.insert (.bnd d) T) (.root (.bnd d)) = some T
      simp [Ctx.insert]
    · have hU' : Γ (.root r) = some U := by simpa [Ctx.insert, hr] using hU
      have hrb : r ≠ .bnd d := fun he => by
        subst he
        rw [hs.root] at hU'
        cases hU'
      rw [show Subst.bindRoots (σ := σ) (Γ.insert (.bnd d) T) u d r = .ren (.root r)
        from if_neg hr]
      change (Γ.insert (.bnd d) T) (.root r) = some U
      simp [Ctx.insert, hrb, hU']
  Wff.subst (Subst.idxOfRoots (Subst.bindRoots (Γ.insert (.bnd d) T) u d))
    (Subst.ofRoots (Subst.bindRoots (Γ.insert (.bnd d) T) u d))
    (Subst.ok_ofRoots (hΓ.insert _ T) hρ) (Subst.coh_ofRoots (hΓ.insert _ T) hρ)
    (hs.insertFree u T) (hs.insert T) φ

/-! ## Sanity checks -/

def σ0 : Signature :=
  { FuncSyms := Empty, RelSyms := Empty, funcArity := Empty.elim, relArity := Empty.elim }

def y₂ : Name := .root (.free 2)
def b0 : Name := .root (.bnd 0)
def b1 : Name := .root (.bnd 1)

/-- `y : ◇Var`. -/
def Γ₂ : Ctx := fun v => if v = y₂ then some (.VTypeDia .Var) else none

theorem Γ₂_top : Γ₂.TopLevel := by
  intro v T h
  unfold Γ₂ at h
  split_ifs at h with hv
  exact ⟨_, hv⟩

theorem Γ₂_slots : Γ₂.SlotsFrom 0 := by
  intro v n hv _
  unfold Γ₂
  split_ifs with h
  · subst h
    cases hv
  · rfl

/-- `◇_y (y.dia)`. -/
def s₂ : Term σ0 Γ₂ (.VTypeDia .Var) (.dia y₂ .var) :=
  .diatm y₂ ⟨.Var, by decide⟩ (.var (.step y₂ .dia) (by decide))

/-- `◇_z (z.dia = z.dia) ∧ ∀w:Var. w = w`, with `z` the slot `bnd 0`. -/
def φ₂ : Wff σ0 (Γ₂.insert (.bnd 0) (.VTypeDia .Var)) 1 :=
  .and (.dia b0 ⟨.Var, by decide⟩ (.eq (.var (.step b0 .dia) (by decide))
      (.var (.step b0 .dia) (by decide))))
    (.all .Var (.eq (.var b1 (by decide)) (.var b1 (by decide))))

/-- Expected: `◇_y (y.dia = y.dia) ∧ ∀w:Var. w = w`, the inner slot shifted to `bnd 0`. -/
def expected₂ : Wff σ0 Γ₂ 0 :=
  .and (.dia y₂ ⟨.Var, by decide⟩ (.eq (.var (.step y₂ .dia) (by decide))
      (.var (.step y₂ .dia) (by decide))))
    (.all .Var (.eq (.var b0 (by decide)) (.var b0 (by decide))))

/-- ⭐Modal β and slot shifting, computed. -/
example : Wff.instantiate Γ₂_top Γ₂_slots s₂ φ₂ = expected₂ := by decide

end AddrProto
