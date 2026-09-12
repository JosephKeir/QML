import Mathlib.Tactic

/-!
# Address prototype: modal steps inside names

Names are ADDRESSES: a root and a path of steps `fst | snd | box | dia`.  Inside `□` the content
of `z : □A` is the name `z.box`; the witness of `◇_{z.box.fst}` is that name.  An annotation index
is an address, fixed where its root was declared, so it is the same at every modal level: there
are no out-maps.

A context is a partial function on addresses: the positions visible at the current level (roots,
and `….box` / `….dia` names).  Product components are always reached by projection (`Ctx.ref`).
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

def Name.ext : Name → List Step → Name
  | v, [] => v
  | v, s :: p => Name.ext (.step v s) p

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

/-! ## Annotations and terms -/

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

/-- ⭐Annotations are plain constructor applications: no out-maps, no Forded fields. -/
inductive Term : Ctx → (T : VarType) → Ann T → Type where
  | var {Γ : Ctx} (v : Name) (h : Γ.ref v = some .Var) : Term Γ .Var .var
  | unit {Γ : Ctx} : Term Γ .VTypeOne .one
  | pair {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B} :
      Term Γ A a → Term Γ B b → Term Γ (.VTypeProd A B) (.prod a b)
  | boxtm {Γ : Ctx} {A : VarType} {a : Ann A} : Term Γ.boxIn A a → Term Γ (.VTypeBox A) (.box a)
  | diatm {Γ : Ctx} {A : VarType} {a : Ann A} (x : Name)
      (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
      Term (Γ.diaIn x) A a → Term Γ (.VTypeDia A) (.dia x a)
deriving DecidableEq

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

theorem Ctx.le_boxIn_diaIn (Γ : Ctx) (x : Name) : Γ.boxIn.Le (Γ.diaIn x) := by
  intro v T hv
  match v with
  | .step u .box => exact hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

/-- ⭐Weakening: annotations untouched, no scoping needed. -/
def Term.mono : {Γ Γ' : Ctx} → Γ.Le Γ' → {T : VarType} → {a : Ann T} → Term Γ T a → Term Γ' T a
  | _, _, h, _, _, .var v hv => .var v (h.ref hv)
  | _, _, _, _, _, .unit => .unit
  | _, _, h, _, _, .pair s t => .pair (Term.mono h s) (Term.mono h t)
  | _, _, h, _, _, .boxtm t => .boxtm (Term.mono h.boxIn t)
  | _, _, h, _, _, .diatm x hx t =>
      .diatm x (hx.imp fun _ hX => h.ref hX) (Term.mono (h.diaIn x) t)

def Ctx.insert (Γ : Ctx) (r : Root) (T : VarType) : Ctx :=
  fun v => if v = .root r then some T else Γ v

theorem Ctx.le_insert {Γ : Ctx} {r : Root} (hr : Γ (.root r) = none) (T : VarType) :
    Γ.Le (Γ.insert r T) := by
  intro v U hv
  simp only [Ctx.insert]
  split_ifs with h
  · subst h
    rw [hr] at hv
    cases hv
  · exact hv

/-! ## Formulas and equality, without casts -/

inductive Wff : Ctx → Type where
  | eq {Γ : Ctx} : Term Γ .Var .var → Term Γ .Var .var → Wff Γ
  | top {Γ : Ctx} : Wff Γ
  | bot {Γ : Ctx} : Wff Γ
  | and {Γ : Ctx} : Wff Γ → Wff Γ → Wff Γ
  | imp {Γ : Ctx} : Wff Γ → Wff Γ → Wff Γ
  | box {Γ : Ctx} : Wff Γ.boxIn → Wff Γ
  | dia {Γ : Ctx} (x : Name) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) : Wff (Γ.diaIn x) → Wff Γ
deriving DecidableEq

/-- ⭐Same annotation ⇒ same witness and same inner context, definitionally: no casts, no
    unreachable branches. -/
def eqRec : {Γ : Ctx} → (T : VarType) → {a : Ann T} → Term Γ T a → Term Γ T a → Wff Γ
  | _, .Var, .var, t, s => .eq t s
  | _, .VTypeOne, _, _, _ => .top
  | _, .VTypeProd A B, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => .and (eqRec A t₁ s₁) (eqRec B t₂ s₂)
  | _, .VTypeBox A, .box _, .boxtm t, .boxtm s => .box (eqRec A t s)
  | _, .VTypeDia A, .dia x _, .diatm _ hx t, .diatm _ _ s =>
      .imp (.dia x hx (.imp (eqRec A t s) .bot)) .bot

/-! ## Substitution

A substitution at some modal level sends each VISIBLE source name to an entry over the current
target: a name or a term.  Product components are reached by projection (`Subst.at`).  Under `□`
and `◇_x` it is transformed pointwise (`Subst.box`, `Subst.dia`).  Annotations are mapped by ONE
global address map `ι`; `Subst.Coh` says the entries agree with it. -/

inductive SubE (Δ : Ctx) : Type where
  | hide
  | ren (w : Name)
  | tm {T : VarType} {a : Ann T} (s : Term Δ T a)

namespace SubE

variable {Δ : Ctx}

def proj : SubE Δ → Step → SubE Δ
  | .ren w, s => .ren (.step w s)
  | .tm (.pair s _), .fst => .tm s
  | .tm (.pair _ t), .snd => .tm t
  | _, _ => .hide

def unbox : SubE Δ → SubE Δ.boxIn
  | .ren w => .ren (.step w .box)
  | .tm (.boxtm t) => .tm t
  | _ => .hide

def mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) : SubE Δ₁ → SubE Δ₂
  | .hide => .hide
  | .ren w => .ren w
  | .tm s => .tm (Term.mono h s)

/-- The entry at the witness body, for the new witness `ιx` (modal β for a term entry). -/
def diaBody (ιx : Name) : SubE Δ → SubE (Δ.diaIn ιx)
  | .ren _ => .ren (.step ιx .dia)
  | .tm (.diatm y _hy u) =>
      if h : y = ιx then .tm (Term.mono (by subst h; exact Ctx.Le.refl _) u) else .hide
  | _ => .hide

def OkRef : SubE Δ → VarType → Prop
  | .ren w, T => Δ.ref w = some T
  | .tm (T := U) _, T => U = T
  | .hide, _ => False

def idxAlong : SubE Δ → List Step → Name
  | .ren w, p => w.ext p
  | .tm (a := a) _, p => a.idxAt p
  | .hide, _ => .root (.free 0)

def toVar : (e : SubE Δ) → e.OkRef .Var → Term Δ .Var .var
  | .ren w, h => .var w h
  | .tm (.var v hv), _ => .var v hv
  | .tm .unit, h => nomatch h
  | .tm (.pair _ _), h => nomatch h
  | .tm (.boxtm _), h => nomatch h
  | .tm (.diatm _ _ _), h => nomatch h
  | .hide, h => False.elim h

theorem okRef_proj : ∀ {e : SubE Δ} {U T : VarType} {s : Step}, e.OkRef U → s.isProd = true →
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

theorem idxAlong_proj : ∀ {e : SubE Δ} {U T : VarType} {s : Step} (p : List Step), e.OkRef U →
    s.isProd = true → U.step s = some T → (e.proj s).idxAlong p = e.idxAlong (s :: p)
  | .ren _, _, _, _, _, _, _, _ => rfl
  | .hide, _, _, _, _, he, _, _ => False.elim he
  | .tm (T := U') s₀, U, T, s, p, he, hs, hst => by
      have hU : U' = U := he
      subst hU
      cases s <;> (try cases hs) <;> cases s₀ <;> first | rfl | cases hst

theorem okRef_unbox : ∀ {e : SubE Δ} {A : VarType}, e.OkRef (.VTypeBox A) → e.unbox.OkRef A
  | .ren w, A, he => by
      change (match Δ.ref w with | some (.VTypeBox A) => some A | _ => none) = some A
      rw [he]
  | .hide, _, he => False.elim he
  | .tm (T := U) s, A, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem idxAlong_unbox : ∀ {e : SubE Δ} {A : VarType} (p : List Step), e.OkRef (.VTypeBox A) →
    e.unbox.idxAlong p = e.idxAlong (.box :: p)
  | .ren _, _, _, _ => rfl
  | .hide, _, _, he => False.elim he
  | .tm (T := U) s, A, p, he => by
      have hU : U = .VTypeBox A := he
      subst hU
      cases s
      rfl

theorem okRef_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ {e : SubE Δ₁} {T : VarType}, e.OkRef T → (e.mono h).OkRef T
  | .ren _, _, he => h.ref he
  | .tm _, _, he => he
  | .hide, _, he => False.elim he

theorem idxAlong_mono {Δ₁ Δ₂ : Ctx} (h : Δ₁.Le Δ₂) :
    ∀ (e : SubE Δ₁) (p : List Step), (e.mono h).idxAlong p = e.idxAlong p
  | .ren _, _ => rfl
  | .tm _, _ => rfl
  | .hide, _ => rfl

theorem okRef_diaBody {ιx : Name} : ∀ {e : SubE Δ} {X : VarType},
    e.OkRef (.VTypeDia X) → e.idxAlong [] = ιx → (e.diaBody ιx).OkRef X
  | .ren w, X, he, hw => by
      have hw' : w = ιx := hw
      subst hw'
      change (if w = w then (match Δ.ref w with | some (.VTypeDia X) => some X | _ => none)
        else none) = some X
      rw [if_pos rfl, he]
  | .tm (.diatm y _hy u), X, he, hw => by
      have hw' : y = ιx := hw
      rw [show ((SubE.tm (Term.diatm y _hy u) : SubE Δ).diaBody ιx) =
        SubE.tm (Term.mono (by subst hw'; exact Ctx.Le.refl _) u) from dif_pos hw']
      exact VarType.VTypeDia.inj he
  | .tm (.var _ _), _, he, _ => nomatch he
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

theorem idxAlong_diaBody {ιx : Name} : ∀ {e : SubE Δ} {X : VarType} (p : List Step),
    e.OkRef (.VTypeDia X) → e.idxAlong [] = ιx → (e.diaBody ιx).idxAlong p = e.idxAlong (.dia :: p)
  | .ren w, _, p, _, hw => by
      have hw' : w = ιx := hw
      subst hw'
      rfl
  | .tm (.diatm y _hy u), X, p, he, hw => by
      have hw' : y = ιx := hw
      rw [show ((SubE.tm (Term.diatm y _hy u) : SubE Δ).diaBody ιx) =
        SubE.tm (Term.mono (by subst hw'; exact Ctx.Le.refl _) u) from dif_pos hw']
      rfl
  | .tm (.var _ _), _, _, he, _ => nomatch he
  | .tm .unit, _, _, he, _ => nomatch he
  | .tm (.pair _ _), _, _, he, _ => nomatch he
  | .tm (.boxtm _), _, _, he, _ => nomatch he
  | .hide, _, _, he, _ => False.elim he

theorem ref_witness {w : Name} : ∀ {e : SubE Δ} {X : VarType},
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
  | .tm .unit, _, he, _ => nomatch he
  | .tm (.pair _ _), _, he, _ => nomatch he
  | .tm (.boxtm _), _, he, _ => nomatch he
  | .hide, _, he, _ => False.elim he

end SubE

abbrev Subst (Δ : Ctx) := Name → SubE Δ

namespace Subst

variable {Δ : Ctx}

/-- The entry reachable at a name: product components by projection. -/
def «at» (θ : Subst Δ) : Name → SubE Δ
  | .root r => θ (.root r)
  | .step v s => if s.isProd then (θ.at v).proj s else θ (.step v s)

def Ok (Γ : Ctx) (θ : Subst Δ) : Prop := ∀ v T, Γ v = some T → (θ v).OkRef T

def Coh (ι : Name → Name) (Γ : Ctx) (θ : Subst Δ) : Prop :=
  ∀ v T, Γ.ref v = some T → ∀ p, (θ.at v).idxAlong p = ι (v.ext p)

def box (θ : Subst Δ) : Subst Δ.boxIn := fun v =>
  match v with
  | .step u .box => (θ.at u).unbox
  | _ => .hide

def dia (θ : Subst Δ) (x ιx : Name) : Subst (Δ.diaIn ιx) := fun v =>
  match v with
  | .step u .dia => if u = x then (θ.at x).diaBody ιx else .hide
  | .step u .box => (θ.at u).unbox.mono (Ctx.le_boxIn_diaIn Δ ιx)
  | _ => .hide

theorem okRef_at {Γ : Ctx} {θ : Subst Δ} (hθ : Ok Γ θ) :
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

/-- Coherence follows from coherence on the visible names. -/
theorem coh_of {ι : Name → Name} {Γ : Ctx} {θ : Subst Δ} (hθ : Ok Γ θ)
    (hvis : ∀ v T, Γ v = some T → ∀ p, (θ v).idxAlong p = ι (v.ext p)) : Coh ι Γ θ := by
  intro v
  induction v with
  | root r => intro T hv p; exact hvis _ _ hv p
  | step v s ih =>
      intro T hv p
      have hv' := hv
      simp only [Ctx.ref] at hv
      simp only [Subst.at]
      split_ifs at hv ⊢ with hs
      · cases hU : Γ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U =>
            rw [hU] at hv
            rw [SubE.idxAlong_proj p (okRef_at hθ hU) hs hv, ih U hU (s :: p)]
            rfl
      · exact hvis _ _ hv p

theorem ok_box {Γ : Ctx} {θ : Subst Δ} (hθ : Ok Γ θ) : Ok Γ.boxIn θ.box := by
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

theorem coh_box {ι : Name → Name} {Γ : Ctx} {θ : Subst Δ} (hθ : Ok Γ θ) (hc : Coh ι Γ θ) :
    Coh ι Γ.boxIn θ.box := by
  refine coh_of (ok_box hθ) ?_
  intro v T hv p
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

theorem ok_dia {Γ : Ctx} {θ : Subst Δ} (hθ : Ok Γ θ) {x ιx : Name}
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

theorem coh_dia {ι : Name → Name} {Γ : Ctx} {θ : Subst Δ} (hθ : Ok Γ θ) (hc : Coh ι Γ θ)
    {x : Name} (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) :
    Coh ι (Γ.diaIn x) (θ.dia x (ι x)) := by
  have hw : (θ.at x).idxAlong [] = ι x := by
    obtain ⟨X, hX⟩ := hx
    exact hc x _ hX []
  refine coh_of (ok_dia hθ hx hw) ?_
  obtain ⟨X, hx⟩ := hx
  intro v T hv p
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

end Subst

/-- ⭐**Substitution**, intrinsically typed, annotations mapped by `ι`.  No casts, no out-map
    commutation: the `□` case is literally `boxtm` of the substituted body, and the `◇` case uses
    the new witness `ι x` directly. -/
def Term.subst (ι : Name → Name) : {Γ Δ : Ctx} → (θ : Subst Δ) → Subst.Ok Γ θ →
    Subst.Coh ι Γ θ → {T : VarType} → {a : Ann T} → Term Γ T a → Term Δ T (a.mapIdx ι)
  | _, _, θ, hθ, _, _, _, .var _ hv => (θ.at _).toVar (Subst.okRef_at hθ hv)
  | _, _, _, _, _, _, _, .unit => .unit
  | _, _, θ, hθ, hc, _, _, .pair s t => .pair (Term.subst ι θ hθ hc s) (Term.subst ι θ hθ hc t)
  | _, _, θ, hθ, hc, _, _, .boxtm t =>
      .boxtm (Term.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) t)
  | _, _, θ, hθ, hc, _, _, .diatm x hx t =>
      have hw : (θ.at x).idxAlong [] = ι x := hx.elim fun _ hX => hc x _ hX []
      .diatm (ι x) (hx.elim fun _ hX => SubE.ref_witness (Subst.okRef_at hθ hX) hw)
        (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) t)

/-! ## Sanity: the running example -/

def z : Root := .free 0

/-- `z : □(◇Var × Var)`. -/
def Γ₁ : Ctx := fun v => if v = .root z then some (.VTypeBox (.VTypeProd (.VTypeDia .Var) .Var))
  else none

def zbf : Name := .step (.step (.root z) .box) .fst

/-- `□ ◇_{z.box.fst} unit`, with its annotation exactly the witness address. -/
def ex : Term Γ₁ (.VTypeBox (.VTypeDia .VTypeOne)) (.box (.dia zbf .one)) :=
  .boxtm (.diatm zbf ⟨.Var, by decide⟩ .unit)

end AddrProto
