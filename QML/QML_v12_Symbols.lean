import Mathlib.Tactic

/-!
# QML v12 — foundations: types, addresses, contexts, annotations

* **Variable symbols are ADDRESSES**: a root (a free variable or a quantifier slot) and a path of
  steps `fst | snd | box | dia`.  Inside `□` the content of `z : □A` is `z.box`; inside `◇_x` the
  content of the witness is `x.dia`; product components are `z.fst`, `z.snd`.
* **Annotation indices are addresses**, fixed where their root was declared, so a witness has the
  same index at every modal level: there are no out-maps.
* **A context is a partial function on addresses**: the positions visible at the current level
  (roots, `….box`, `….dia`).  Product components are always reached by projection (`Ctx.ref`).
  The `□` and `◇_x` views are pointwise (`Ctx.boxIn`, `Ctx.diaIn`).
* Quantifier slots are roots `bnd d`; formulas record the binder depth `d` (see the formula file).
-/

namespace V12

/-! ## Types -/

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

/-! ## Addresses -/

inductive Root where
  | free (n : ℕ)
  | bnd (n : ℕ)
deriving DecidableEq

/-- A variable symbol: a root and steps, the innermost step LAST. -/
inductive VarSymb where
  | root (r : Root)
  | step (v : VarSymb) (s : Step)
deriving DecidableEq

namespace VarSymb

def rt : VarSymb → Root
  | root r => r
  | step v _ => v.rt

/-- The steps, root-first. -/
def path : VarSymb → List Step
  | root _ => []
  | step v s => v.path ++ [s]

def ext : VarSymb → List Step → VarSymb
  | v, [] => v
  | v, s :: p => ext (.step v s) p

def reroot (r' : Root) : VarSymb → VarSymb
  | root _ => root r'
  | step v s => step (v.reroot r') s

/-- The last step is a product step. -/
def lastProd : VarSymb → Bool
  | root _ => false
  | step _ s => s.isProd

theorem ext_rt : ∀ (v : VarSymb) (p : List Step), (v.ext p).rt = v.rt
  | _, [] => rfl
  | v, s :: p => ext_rt (.step v s) p

theorem ext_path : ∀ (v : VarSymb) (p : List Step), (v.ext p).path = v.path ++ p
  | v, [] => by simp [ext]
  | v, s :: p => by
      change (ext (.step v s) p).path = _
      rw [ext_path]
      simp [path]

theorem reroot_ext (r' : Root) :
    ∀ (v : VarSymb) (p : List Step), (v.ext p).reroot r' = (v.reroot r').ext p
  | _, [] => rfl
  | v, s :: p => reroot_ext r' (.step v s) p

/-- Shift the addresses under the slot `bnd d` to the slot `bnd d'`. -/
def shiftSlot (ι : VarSymb → VarSymb) (d d' : ℕ) : VarSymb → VarSymb :=
  fun i => if i.rt = .bnd d then i.reroot (.bnd d') else ι i

end VarSymb

/-! ## Contexts and their modal views -/

abbrev Ctx := VarSymb → Option VarType

namespace Ctx

/-- The type reachable at an address: product steps project from the parent, modal steps must be
    visible. -/
def ref (Γ : Ctx) : VarSymb → Option VarType
  | .root r => Γ (.root r)
  | .step v s => if s.isProd then (Γ.ref v).bind (·.step s) else Γ (.step v s)

/-- Inside `□`: `v.box : A` exactly when `v : □A` is reachable. -/
def boxIn (Γ : Ctx) : Ctx := fun v =>
  match v with
  | .step u .box =>
      match Γ.ref u with
      | some (.VTypeBox A) => some A
      | _ => none
  | _ => none

/-- Inside `◇_x`: the `□` view, and `x.dia : X` where `x : ◇X`. -/
def diaIn (Γ : Ctx) (x : VarSymb) : Ctx := fun v =>
  match v with
  | .step u .dia =>
      if u = x then
        match Γ.ref x with
        | some (.VTypeDia X) => some X
        | _ => none
      else none
  | v => Γ.boxIn v

/-- Declare a root. -/
def insert (Γ : Ctx) (r : Root) (T : VarType) : Ctx :=
  fun v => if v = .root r then some T else Γ v

theorem ref_nonprod (Γ : Ctx) : ∀ {v : VarSymb}, v.lastProd = false → Γ.ref v = Γ v
  | .root _, _ => rfl
  | .step v s, h => by
      change (if s.isProd then (Γ.ref v).bind (·.step s) else Γ (.step v s)) = _
      have hs : s.isProd = false := h
      rw [if_neg (Bool.eq_false_iff.mp hs)]

theorem ref_none_of_rootFresh {Γ : Ctx} {r : Root} (h : ∀ v, v.rt = r → Γ v = none) :
    ∀ v, v.rt = r → Γ.ref v = none := by
  intro v
  induction v with
  | root r' => intro hv; exact h _ hv
  | step v s ih =>
      intro hv
      simp only [ref]
      split_ifs
      · simp only [ih hv, Option.bind_none]
      · exact h _ hv

/-! ## Revealing more positions -/

def Le (Γ Γ' : Ctx) : Prop := ∀ v T, Γ v = some T → Γ' v = some T

theorem Le.refl (Γ : Ctx) : Γ.Le Γ := fun _ _ h => h

theorem Le.ref {Γ Γ' : Ctx} (h : Γ.Le Γ') :
    ∀ {v : VarSymb} {T : VarType}, Γ.ref v = some T → Γ'.ref v = some T := by
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

theorem Le.boxIn {Γ Γ' : Ctx} (h : Γ.Le Γ') : Γ.boxIn.Le Γ'.boxIn := by
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

theorem Le.diaIn {Γ Γ' : Ctx} (h : Γ.Le Γ') (x : VarSymb) : (Γ.diaIn x).Le (Γ'.diaIn x) := by
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

theorem Le.insert {Γ Γ' : Ctx} (h : Γ.Le Γ') (r : Root) (T : VarType) :
    (Γ.insert r T).Le (Γ'.insert r T) := by
  intro v U hv
  simp only [Ctx.insert] at hv ⊢
  split_ifs at hv ⊢
  · exact hv
  · exact h v U hv

theorem le_boxIn_diaIn (Γ : Ctx) (x : VarSymb) : Γ.boxIn.Le (Γ.diaIn x) := by
  intro v T hv
  match v with
  | .step u .box => exact hv
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv

/-- Weakening by a fresh root. -/
theorem le_insert {Γ : Ctx} {r : Root} (hr : Γ (.root r) = none) (T : VarType) :
    Γ.Le (Γ.insert r T) := by
  intro v U hv
  simp only [Ctx.insert]
  split_ifs with h
  · subst h
    rw [hr] at hv
    cases hv
  · exact hv

/-! ## Fresh quantifier slots; top-level contexts -/

/-- No slot at or above `d` is visible. -/
def SlotsFrom (Γ : Ctx) (d : ℕ) : Prop := ∀ v n, v.rt = .bnd n → d ≤ n → Γ v = none

theorem SlotsFrom.root {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) : Γ (.root (.bnd d)) = none :=
  h _ d rfl le_rfl

theorem SlotsFrom.insert {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (T : VarType) :
    (Γ.insert (.bnd d) T).SlotsFrom (d + 1) := by
  intro v n hv hn
  simp only [Ctx.insert]
  split_ifs with hvr
  · subst hvr
    cases hv
    omega
  · exact h v n hv (by omega)

theorem SlotsFrom.insertFree {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (u : ℕ) (T : VarType) :
    (Γ.insert (.free u) T).SlotsFrom d := by
  intro v n hv hn
  simp only [Ctx.insert]
  split_ifs with hvr
  · subst hvr
    cases hv
  · exact h v n hv hn

theorem SlotsFrom.boxIn {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) : Γ.boxIn.SlotsFrom d := by
  intro v n hv hn
  have hfresh : ∀ w, w.rt = .bnd n → Γ w = none := fun w hw => h w n hw hn
  match v with
  | .step u .box =>
      change (match Γ.ref u with | some (.VTypeBox A) => some A | _ => none) = none
      simp only [ref_none_of_rootFresh hfresh u hv]
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl
  | .step _ .dia => rfl

theorem SlotsFrom.diaIn {Γ : Ctx} {d : ℕ} (h : Γ.SlotsFrom d) (x : VarSymb) :
    (Γ.diaIn x).SlotsFrom d := by
  intro v n hv hn
  have hfresh : ∀ w, w.rt = .bnd n → Γ w = none := fun w hw => h w n hw hn
  match v with
  | .step u .dia =>
      change (if u = x then (match Γ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = none
      split_ifs with hux
      · rw [← hux]
        simp only [ref_none_of_rootFresh hfresh u hv]
      · rfl
  | .step u .box => exact h.boxIn (.step u .box) n hv hn
  | .root _ => rfl
  | .step _ .fst => rfl
  | .step _ .snd => rfl

/-- A top-level context shows only roots. -/
def TopLevel (Γ : Ctx) : Prop := ∀ v T, Γ v = some T → ∃ r, v = .root r

theorem TopLevel.insert {Γ : Ctx} (h : Γ.TopLevel) (r : Root) (T : VarType) :
    (Γ.insert r T).TopLevel := by
  intro v U hv
  simp only [Ctx.insert] at hv
  split_ifs at hv with hvr
  · exact ⟨r, hvr⟩
  · exact h v U hv

end Ctx

/-! ## Witness annotations -/

inductive Ann : VarType → Type where
  | var : Ann .Var
  | one : Ann .VTypeOne
  | prod {A B : VarType} (a : Ann A) (b : Ann B) : Ann (.VTypeProd A B)
  | box {A : VarType} (a : Ann A) : Ann (.VTypeBox A)
  | dia {A : VarType} (i : VarSymb) (a : Ann A) : Ann (.VTypeDia A)
deriving DecidableEq

def Ann.mapIdx (f : VarSymb → VarSymb) : {T : VarType} → Ann T → Ann T
  | _, .var => .var
  | _, .one => .one
  | _, .prod a b => .prod (a.mapIdx f) (b.mapIdx f)
  | _, .box a => .box (a.mapIdx f)
  | _, .dia i a => .dia (f i) (a.mapIdx f)

/-- The index at the `◇`-node a path reaches (junk otherwise). -/
def Ann.idxAt : {T : VarType} → Ann T → List Step → VarSymb
  | _, .dia i _, [] => i
  | _, .prod a _, .fst :: p => a.idxAt p
  | _, .prod _ b, .snd :: p => b.idxAt p
  | _, .box a, .box :: p => a.idxAt p
  | _, .dia _ a, .dia :: p => a.idxAt p
  | _, _, _ => .root (.free 0)

end V12
