import Mathlib.Tactic

/-!
# Prototype — the ◇-witness carried in the TYPE

Isolated (no QML imports).  Tests the design in which a `◇`-term records its witness in its type,
`◇_x t : ◇_x A`, with every variable SELF-indexed (`z : ◇Z` has type `◇_z Z`), and a type index
only ever arising from promotion of exactly one variable.

**Indices are access paths.**  An index `⟨v, p⟩` names the `◇`-node reached from variable `v` by the
steps `p` (`fst`/`snd` into products, `box`/`dia` into modal layers).  Promotions translate indices
outward by PREPENDING one step, which is what keeps the levels apart: `z : ◇◇W` has type
`◇_⟨z,[]⟩ ◇_⟨z,[dia]⟩ W`, and inside `◇_z` the realization value `z : ◇W` is `◇_⟨z,[]⟩ W` again.

Simplifications (orthogonal to the question):
* de Bruijn positions, and contexts are FUNCTIONS `Nat → Option Ty` — a promotion HIDES or
  REVEALS slots rather than shifting them, so positions are stable across modal layers;
* the box shadow is canonical (`unboxCtx`: box-typed slots unboxed, everything else hidden);
* `pelim p` binds the two components as fresh positions `0` (snd) and `1` (fst);
* only `.base`-typed variables are terms (faithful to the real grammar).
-/

namespace DiaIdx

/-! ## Types and indexed types -/

inductive Ty where
  | base | unit
  | prod (A B : Ty) | box (A : Ty) | dia (A : Ty)
deriving DecidableEq

inductive Step where
  | fst | snd | box | dia
deriving DecidableEq

/-- An access path: from variable `var`, follow `path` to a `◇`-node. -/
structure Idx where
  var : Nat
  path : List Step
deriving DecidableEq

def Idx.pre (s : Step) (i : Idx) : Idx := ⟨i.var, s :: i.path⟩

def Idx.strip (i : Idx) : Idx := ⟨i.var, i.path.tail⟩

def Idx.ren (ρ : Nat → Nat) (i : Idx) : Idx := ⟨ρ i.var, i.path⟩

@[simp] theorem Idx.strip_pre (s : Step) (i : Idx) : (i.pre s).strip = i := rfl

/-- Types whose `◇`-nodes carry their witness index. -/
inductive ITy where
  | base | unit
  | prod (A B : ITy) | box (A : ITy) | dia (i : Idx) (A : ITy)
deriving DecidableEq

namespace ITy

def erase : ITy → Ty
  | base => .base
  | unit => .unit
  | prod A B => .prod A.erase B.erase
  | box A => .box A.erase
  | dia _ A => .dia A.erase

def mapIdx (f : Idx → Idx) : ITy → ITy
  | base => base
  | unit => unit
  | prod A B => prod (A.mapIdx f) (B.mapIdx f)
  | box A => box (A.mapIdx f)
  | dia i A => dia (f i) (A.mapIdx f)

def idxs : ITy → List Idx
  | base => []
  | unit => []
  | prod A B => A.idxs ++ B.idxs
  | box A => A.idxs
  | dia i A => i :: A.idxs

/-- The index at the `◇`-node reached by a path (junk if the path does not lead to one). -/
def idxAt : ITy → List Step → Idx
  | dia i _, [] => i
  | prod A _, .fst :: p => A.idxAt p
  | prod _ B, .snd :: p => B.idxAt p
  | box A, .box :: p => A.idxAt p
  | dia _ A, .dia :: p => A.idxAt p
  | _, _ => ⟨0, []⟩

end ITy

/-- The path leads to a `◇`-node. -/
def Ty.DiaAt : Ty → List Step → Prop
  | .dia _, [] => True
  | .prod A _, .fst :: p => A.DiaAt p
  | .prod _ B, .snd :: p => B.DiaAt p
  | .box A, .box :: p => A.DiaAt p
  | .dia A, .dia :: p => A.DiaAt p
  | _, _ => False

namespace ITy

@[simp] theorem erase_mapIdx (f : Idx → Idx) (S : ITy) : (S.mapIdx f).erase = S.erase := by
  induction S with
  | base => rfl
  | unit => rfl
  | prod A B ihA ihB => simp [mapIdx, erase, ihA, ihB]
  | box A ih => simp [mapIdx, erase, ih]
  | dia i A ih => simp [mapIdx, erase, ih]

theorem mapIdx_mapIdx (f g : Idx → Idx) (S : ITy) :
    (S.mapIdx f).mapIdx g = S.mapIdx (g ∘ f) := by
  induction S with
  | base => rfl
  | unit => rfl
  | prod A B ihA ihB => simp [mapIdx, ihA, ihB]
  | box A ih => simp [mapIdx, ih]
  | dia i A ih => simp [mapIdx, ih]

@[simp] theorem mapIdx_id (S : ITy) : S.mapIdx id = S := by
  induction S with
  | base => rfl
  | unit => rfl
  | prod A B ihA ihB => simp [mapIdx, ihA, ihB]
  | box A ih => simp [mapIdx, ih]
  | dia i A ih => simp [mapIdx, ih]

theorem mapIdx_congr {f g : Idx → Idx} (S : ITy) (h : ∀ i ∈ S.idxs, f i = g i) :
    S.mapIdx f = S.mapIdx g := by
  induction S with
  | base => rfl
  | unit => rfl
  | prod A B ihA ihB =>
      simp only [mapIdx]
      rw [ihA (fun i hi => h i (by simp [idxs, hi])), ihB (fun i hi => h i (by simp [idxs, hi]))]
  | box A ih => simp only [mapIdx]; rw [ih (fun i hi => h i (by simpa [idxs] using hi))]
  | dia j A ih =>
      simp only [mapIdx]
      rw [h j (by simp [idxs]), ih (fun i hi => h i (by simp [idxs, hi]))]

theorem mem_idxs_mapIdx {f : Idx → Idx} {i : Idx} {S : ITy} (hi : i ∈ (S.mapIdx f).idxs) :
    ∃ j ∈ S.idxs, f j = i := by
  induction S with
  | base => simp [mapIdx, idxs] at hi
  | unit => simp [mapIdx, idxs] at hi
  | prod A B ihA ihB =>
      simp only [mapIdx, idxs, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨j, hj, rfl⟩ := ihA hi; exact ⟨j, by simp [idxs, hj], rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ihB hi; exact ⟨j, by simp [idxs, hj], rfl⟩
  | box A ih => simpa [mapIdx, idxs] using ih (by simpa [mapIdx, idxs] using hi)
  | dia k A ih =>
      simp only [mapIdx, idxs, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact ⟨k, by simp [idxs], rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ih hi; exact ⟨j, by simp [idxs, hj], rfl⟩

theorem idxAt_mapIdx (f : Idx → Idx) (S : ITy) (p : List Step) (h : S.erase.DiaAt p) :
    (S.mapIdx f).idxAt p = f (S.idxAt p) := by
  induction S generalizing p with
  | base => cases p <;> exact (h : False).elim
  | unit => cases p <;> exact (h : False).elim
  | prod A B ihA ihB =>
      rcases p with _ | ⟨s, p⟩
      · exact (h : False).elim
      · cases s
        · exact ihA p h
        · exact ihB p h
        · exact (h : False).elim
        · exact (h : False).elim
  | box A ih =>
      rcases p with _ | ⟨s, p⟩
      · exact (h : False).elim
      · cases s
        · exact (h : False).elim
        · exact (h : False).elim
        · exact ih p h
        · exact (h : False).elim
  | dia i A ih =>
      rcases p with _ | ⟨s, p⟩
      · rfl
      · cases s
        · exact (h : False).elim
        · exact (h : False).elim
        · exact (h : False).elim
        · exact ih p h

theorem idxAt_mem (S : ITy) (p : List Step) (h : S.erase.DiaAt p) : S.idxAt p ∈ S.idxs := by
  induction S generalizing p with
  | base => cases p <;> exact (h : False).elim
  | unit => cases p <;> exact (h : False).elim
  | prod A B ihA ihB =>
      rcases p with _ | ⟨s, p⟩
      · exact (h : False).elim
      · cases s
        · exact List.mem_append_left _ (ihA p h)
        · exact List.mem_append_right _ (ihB p h)
        · exact (h : False).elim
        · exact (h : False).elim
  | box A ih =>
      rcases p with _ | ⟨s, p⟩
      · exact (h : False).elim
      · cases s
        · exact (h : False).elim
        · exact (h : False).elim
        · exact ih p h
        · exact (h : False).elim
  | dia i A ih =>
      rcases p with _ | ⟨s, p⟩
      · exact List.mem_cons_self
      · cases s
        · exact (h : False).elim
        · exact (h : False).elim
        · exact (h : False).elim
        · exact List.mem_cons_of_mem _ (ih p h)

theorem erase_eq_base {S : ITy} (h : S.erase = .base) : S = .base := by
  cases S <;> simp_all [erase]

theorem mapIdx_injective {f : Idx → Idx} (hf : Function.Injective f) :
    Function.Injective (ITy.mapIdx f) := by
  intro S T h
  induction S generalizing T with
  | base => cases T <;> simp_all [mapIdx]
  | unit => cases T <;> simp_all [mapIdx]
  | prod A B ihA ihB =>
      cases T <;> simp only [mapIdx, reduceCtorEq, prod.injEq] at h
      rw [ihA h.1, ihB h.2]
  | box A ih =>
      cases T <;> simp only [mapIdx, reduceCtorEq, box.injEq] at h
      rw [ih h]
  | dia i A ih =>
      cases T <;> simp only [mapIdx, reduceCtorEq, dia.injEq] at h
      rw [hf h.1, ih h.2]

end ITy

/-! ## Contexts and the index translations -/

/-- Contexts as functions: a promotion HIDES or REVEALS slots, never shifts them. -/
abbrev Ctx := Nat → Option Ty

def unboxSlot : Option Ty → Option Ty
  | some (.box A) => some A
  | _ => none

theorem unboxSlot_eq_some {o : Option Ty} {A : Ty} : unboxSlot o = some A ↔ o = some (.box A) := by
  rcases o with _ | T
  · simp [unboxSlot]
  · cases T <;> simp [unboxSlot]

/-- The `□`-shadow: box-typed slots unboxed, everything else hidden. -/
def unboxCtx (Γ : Ctx) : Ctx := fun j => unboxSlot (Γ j)

/-- Inside `◇_x`: the box shadow, plus the witness `x` revealed at its realization type. -/
def diaCtx (Γ : Ctx) (x : Nat) (X : Ty) : Ctx := Function.update (unboxCtx Γ) x (some X)

/-- Under `pelim`: the two components at `0` (snd) and `1` (fst). -/
def cons2 (B A : Option Ty) (Γ : Ctx) : Ctx
  | 0 => B
  | 1 => A
  | j + 2 => Γ j

/-- Out of a `□`: every inner index came through one box layer. -/
def boxOut : Idx → Idx := Idx.pre .box

/-- Out of a `◇_x`: the witness came through its `◇`, every other variable through a `□`. -/
def diaOut (x : Nat) (i : Idx) : Idx := if i.var = x then i.pre .dia else i.pre .box

/-- Out of a `pelim p`: the components become paths into `p`. -/
def pelimOut (p : Nat) (i : Idx) : Idx :=
  match i.var with
  | 0 => ⟨p, .snd :: i.path⟩
  | 1 => ⟨p, .fst :: i.path⟩
  | j + 2 => ⟨j, i.path⟩

theorem strip_comp_boxOut : Idx.strip ∘ boxOut = id := rfl

theorem strip_comp_diaOut (x : Nat) : Idx.strip ∘ diaOut x = id := by
  funext i
  simp only [Function.comp, diaOut]
  split <;> rfl

theorem diaOut_injective (x : Nat) : Function.Injective (diaOut x) := by
  intro i j h
  have := congrArg Idx.strip h
  simpa [diaOut, apply_ite Idx.strip] using this

theorem boxOut_injective : Function.Injective boxOut := by
  intro i j h
  exact congrArg Idx.strip h

/-! ## Terms and typing -/

inductive Tm where
  | var (k : Nat)
  | unit
  | pair (a b : Tm)
  | boxtm (t : Tm)
  | diatm (x : Nat) (t : Tm)
  | pelim (p : Nat) (t : Tm)

inductive HasTy : Ctx → Tm → ITy → Prop where
  | var {Γ : Ctx} {k : Nat} : Γ k = some .base → HasTy Γ (.var k) .base
  | unit {Γ : Ctx} : HasTy Γ .unit .unit
  | pair {Γ : Ctx} {a b : Tm} {A B : ITy} :
      HasTy Γ a A → HasTy Γ b B → HasTy Γ (.pair a b) (.prod A B)
  | boxtm {Γ : Ctx} {t : Tm} {S : ITy} :
      HasTy (unboxCtx Γ) t S → HasTy Γ (.boxtm t) (.box (S.mapIdx boxOut))
  | diatm {Γ : Ctx} {x : Nat} {X : Ty} {t : Tm} {S : ITy} :
      Γ x = some (.dia X) → HasTy (diaCtx Γ x X) t S →
      HasTy Γ (.diatm x t) (.dia ⟨x, []⟩ (S.mapIdx (diaOut x)))
  | pelim {Γ : Ctx} {p : Nat} {A B : Ty} {t : Tm} {S : ITy} :
      Γ p = some (.prod A B) → HasTy (cons2 (some B) (some A) Γ) t S →
      HasTy Γ (.pelim p t) (S.mapIdx (pelimOut p))

def Tm.PelimFree : Tm → Prop
  | var _ => True
  | unit => True
  | pair a b => a.PelimFree ∧ b.PelimFree
  | boxtm t => t.PelimFree
  | diatm _ t => t.PelimFree
  | pelim _ _ => False

/-! ## Scoping: every index names a live variable, along a path to a `◇` -/

def Scoped (Γ : Ctx) (S : ITy) : Prop := ∀ i ∈ S.idxs, ∃ T, Γ i.var = some T ∧ T.DiaAt i.path

theorem HasTy.scoped {Γ : Ctx} {t : Tm} {S : ITy} (h : HasTy Γ t S) : Scoped Γ S := by
  induction h with
  | var => intro i hi; simp [ITy.idxs] at hi
  | unit => intro i hi; simp [ITy.idxs] at hi
  | pair _ _ ihA ihB =>
      intro i hi
      simp only [ITy.idxs, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ihA i hi
      · exact ihB i hi
  | boxtm _ ih =>
      intro i hi
      obtain ⟨j, hj, rfl⟩ := ITy.mem_idxs_mapIdx (by simpa [ITy.idxs] using hi)
      obtain ⟨T, hT, hD⟩ := ih j hj
      exact ⟨.box T, unboxSlot_eq_some.mp hT, hD⟩
  | @diatm Γ x X t S hx _ ih =>
      intro i hi
      simp only [ITy.idxs, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact ⟨_, hx, trivial⟩
      · obtain ⟨j, hj, rfl⟩ := ITy.mem_idxs_mapIdx hi
        obtain ⟨T, hT, hD⟩ := ih j hj
        by_cases hjx : j.var = x
        · have hv : diaOut x j = j.pre .dia := by simp [diaOut, hjx]
          rw [hv]
          simp only [diaCtx, Function.update_apply, hjx, if_true, Option.some.injEq] at hT
          subst hT
          exact ⟨_, by rw [show (j.pre Step.dia).var = x from hjx]; exact hx, hD⟩
        · have hv : diaOut x j = j.pre .box := by simp [diaOut, hjx]
          rw [hv]
          rw [diaCtx, Function.update_of_ne hjx] at hT
          exact ⟨.box T, unboxSlot_eq_some.mp hT, hD⟩
  | @pelim Γ p A B t S hp _ ih =>
      intro i hi
      obtain ⟨j, hj, rfl⟩ := ITy.mem_idxs_mapIdx hi
      obtain ⟨T, hT, hD⟩ := ih j hj
      rcases j with ⟨_ | _ | v, path⟩
      · simp only [cons2, Option.some.injEq] at hT
        subst hT
        exact ⟨_, hp, hD⟩
      · simp only [cons2, Option.some.injEq] at hT
        subst hT
        exact ⟨_, hp, hD⟩
      · exact ⟨T, hT, hD⟩

/-! ## Monotonicity: revealing slots preserves typing -/

def CtxLe (Γ Δ : Ctx) : Prop := ∀ j T, Γ j = some T → Δ j = some T

theorem CtxLe.unbox {Γ Δ : Ctx} (h : CtxLe Γ Δ) : CtxLe (unboxCtx Γ) (unboxCtx Δ) := by
  intro j T hj
  exact unboxSlot_eq_some.mpr (h _ _ (unboxSlot_eq_some.mp hj))

theorem HasTy.mono {Γ : Ctx} {t : Tm} {S : ITy} (h : HasTy Γ t S) :
    ∀ {Δ : Ctx}, CtxLe Γ Δ → HasTy Δ t S := by
  induction h with
  | var hk => intro Δ hle; exact .var (hle _ _ hk)
  | unit => intro Δ _; exact .unit
  | pair _ _ iha ihb => intro Δ hle; exact .pair (iha hle) (ihb hle)
  | boxtm _ ih => intro Δ hle; exact .boxtm (ih hle.unbox)
  | @diatm Γ x X t S hx _ ih =>
      intro Δ hle
      refine .diatm (hle _ _ hx) (ih ?_)
      intro j T hj
      by_cases hjx : j = x
      · subst hjx; simpa [diaCtx] using hj
      · rw [diaCtx, Function.update_of_ne hjx] at hj ⊢
        exact hle.unbox _ _ hj
  | pelim hp _ ih =>
      intro Δ hle
      refine .pelim (hle _ _ hp) (ih ?_)
      intro j T hj
      rcases j with _ | _ | j
      · exact hj
      · exact hj
      · exact hle _ _ hj

/-! ## Renaming -/

def lift2 (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | j + 2 => ρ j + 2

def Tm.rename (ρ : Nat → Nat) : Tm → Tm
  | var k => var (ρ k)
  | unit => unit
  | pair a b => pair (a.rename ρ) (b.rename ρ)
  | boxtm t => boxtm (t.rename ρ)
  | diatm x t => diatm (ρ x) (t.rename ρ)
  | pelim p t => pelim (ρ p) (t.rename (lift2 ρ))

theorem Tm.PelimFree.rename {t : Tm} (h : t.PelimFree) (ρ : Nat → Nat) : (t.rename ρ).PelimFree := by
  induction t generalizing ρ with
  | var => trivial
  | unit => trivial
  | pair a b iha ihb => exact ⟨iha h.1 ρ, ihb h.2 ρ⟩
  | boxtm t ih => exact ih h ρ
  | diatm x t ih => exact ih h ρ
  | pelim => exact h.elim

def RenOk (ρ : Nat → Nat) (Γ Δ : Ctx) : Prop := ∀ j T, Γ j = some T → Δ (ρ j) = some T

theorem HasTy.rename {Γ : Ctx} {t : Tm} {S : ITy} (h : HasTy Γ t S) :
    ∀ {ρ : Nat → Nat} {Δ : Ctx}, RenOk ρ Γ Δ → HasTy Δ (t.rename ρ) (S.mapIdx (Idx.ren ρ)) := by
  induction h with
  | var hk => intro ρ Δ hρ; exact .var (hρ _ _ hk)
  | unit => intro ρ Δ _; exact .unit
  | pair _ _ iha ihb => intro ρ Δ hρ; exact .pair (iha hρ) (ihb hρ)
  | @boxtm Γ t S _ ih =>
      intro ρ Δ hρ
      have hρ' : RenOk ρ (unboxCtx Γ) (unboxCtx Δ) := fun j T hj =>
        unboxSlot_eq_some.mpr (hρ _ _ (unboxSlot_eq_some.mp hj))
      have hty := HasTy.boxtm (ih hρ')
      have heq : (S.mapIdx (Idx.ren ρ)).mapIdx boxOut = (S.mapIdx boxOut).mapIdx (Idx.ren ρ) := by
        rw [ITy.mapIdx_mapIdx, ITy.mapIdx_mapIdx]; rfl
      rw [heq] at hty
      exact hty
  | @diatm Γ x X t S hx ht ih =>
      intro ρ Δ hρ
      have hxΔ := hρ _ _ hx
      have hρ' : RenOk ρ (diaCtx Γ x X) (diaCtx Δ (ρ x) X) := by
        intro j T hj
        by_cases hjx : j = x
        · subst hjx; simpa [diaCtx] using hj
        · rw [diaCtx, Function.update_of_ne hjx] at hj
          have hjΔ := hρ _ _ (unboxSlot_eq_some.mp hj)
          have hne : ρ j ≠ ρ x := fun he => by rw [he, hxΔ] at hjΔ; simp at hjΔ
          rw [diaCtx, Function.update_of_ne hne]
          exact unboxSlot_eq_some.mpr hjΔ
      have hty := HasTy.diatm hxΔ (ih hρ')
      have heq : (S.mapIdx (Idx.ren ρ)).mapIdx (diaOut (ρ x))
          = (S.mapIdx (diaOut x)).mapIdx (Idx.ren ρ) := by
        rw [ITy.mapIdx_mapIdx, ITy.mapIdx_mapIdx]
        apply ITy.mapIdx_congr
        intro i hi
        obtain ⟨T, hT, -⟩ := ht.scoped i hi
        by_cases hix : i.var = x
        · simp [diaOut, Idx.ren, Idx.pre, hix]
        · rw [diaCtx, Function.update_of_ne hix] at hT
          have hiΔ := hρ _ _ (unboxSlot_eq_some.mp hT)
          have hne : ρ i.var ≠ ρ x := fun he => by rw [he, hxΔ] at hiΔ; simp at hiΔ
          simp [diaOut, Idx.ren, Idx.pre, hix, hne]
      rw [heq] at hty
      exact hty
  | @pelim Γ p A B t S hp _ ih =>
      intro ρ Δ hρ
      have hρ' : RenOk (lift2 ρ) (cons2 (some B) (some A) Γ) (cons2 (some B) (some A) Δ) := by
        intro j T hj
        rcases j with _ | _ | j
        · exact hj
        · exact hj
        · exact hρ _ _ hj
      have hty := HasTy.pelim (hρ _ _ hp) (ih hρ')
      have heq : (S.mapIdx (Idx.ren (lift2 ρ))).mapIdx (pelimOut (ρ p))
          = (S.mapIdx (pelimOut p)).mapIdx (Idx.ren ρ) := by
        rw [ITy.mapIdx_mapIdx, ITy.mapIdx_mapIdx]
        congr 1
        funext ⟨v, path⟩
        rcases v with _ | _ | v <;> rfl
      rw [heq] at hty
      exact hty

/-! ## Canonical forms of pelim-free terms -/

theorem canon_box {Δ : Ctx} {s : Tm} {S : ITy} {T : Ty} (h : HasTy Δ s S) (hs : s.PelimFree)
    (hT : S.erase = .box T) :
    ∃ u U, s = .boxtm u ∧ S = .box (U.mapIdx boxOut) ∧ HasTy (unboxCtx Δ) u U ∧ u.PelimFree := by
  cases h with
  | boxtm hu => exact ⟨_, _, rfl, rfl, hu, hs⟩
  | pelim => exact hs.elim
  | var => simp [ITy.erase] at hT
  | unit => simp [ITy.erase] at hT
  | pair => simp [ITy.erase] at hT
  | diatm => simp [ITy.erase] at hT

theorem canon_dia {Δ : Ctx} {s : Tm} {S : ITy} {T : Ty} (h : HasTy Δ s S) (hs : s.PelimFree)
    (hT : S.erase = .dia T) :
    ∃ y Y u U, s = .diatm y u ∧ S = .dia ⟨y, []⟩ (U.mapIdx (diaOut y)) ∧ Δ y = some (.dia Y) ∧
      HasTy (diaCtx Δ y Y) u U ∧ u.PelimFree := by
  cases h with
  | diatm hy hu => exact ⟨_, _, _, _, rfl, rfl, hy, hu, hs⟩
  | pelim => exact hs.elim
  | var => simp [ITy.erase] at hT
  | unit => simp [ITy.erase] at hT
  | pair => simp [ITy.erase] at hT
  | boxtm => simp [ITy.erase] at hT

theorem canon_prod {Δ : Ctx} {s : Tm} {S : ITy} {A B : Ty} (h : HasTy Δ s S) (hs : s.PelimFree)
    (hT : S.erase = .prod A B) :
    ∃ a b A' B', s = .pair a b ∧ S = .prod A' B' ∧ HasTy Δ a A' ∧ HasTy Δ b B' ∧
      a.PelimFree ∧ b.PelimFree := by
  cases h with
  | pair ha hb => exact ⟨_, _, _, _, rfl, rfl, ha, hb, hs.1, hs.2⟩
  | pelim => exact hs.elim
  | var => simp [ITy.erase] at hT
  | unit => simp [ITy.erase] at hT
  | boxtm => simp [ITy.erase] at hT
  | diatm => simp [ITy.erase] at hT

/-! ## Simultaneous substitution

Each variable goes either to another position (`ren`) or to a pelim-free term together with its
indexed type (`tm`).  The index map a substitution induces reads a substituted variable's indices
off that stored type: `⟨v, p⟩ ↦ S.idxAt p`.  This is where `z ↦ x` happens. -/

inductive Sub where
  | ren (i : Nat)
  | tm (s : Tm) (S : ITy)

namespace Sub

def idx : Sub → List Step → Idx
  | ren i, p => ⟨i, p⟩
  | tm _ S, p => S.idxAt p

/-- The entry seen through one `□`. -/
def unbox : Sub → Sub
  | ren i => ren i
  | tm (.boxtm u) (.box U) => tm u (U.mapIdx Idx.strip)
  | tm _ _ => ren 0

def shift2 : Sub → Sub
  | ren i => ren (i + 2)
  | tm s S => tm (s.rename (· + 2)) (S.mapIdx (Idx.ren (· + 2)))

/-- The entry fits a slot of type `T` in the target context. -/
def Ok (Δ : Ctx) (T : Ty) : Sub → Prop
  | ren i => Δ i = some T
  | tm s S => HasTy Δ s S ∧ S.erase = T ∧ s.PelimFree

end Sub

def subIdx (σ : Nat → Sub) (i : Idx) : Idx := (σ i.var).idx i.path

def unboxSub (σ : Nat → Sub) : Nat → Sub := fun j => (σ j).unbox

def liftSub2 (σ : Nat → Sub) : Nat → Sub
  | 0 => .ren 0
  | 1 => .ren 1
  | j + 2 => (σ j).shift2

def pairSub (a : Tm) (A : ITy) (b : Tm) (B : ITy) (σ : Nat → Sub) : Nat → Sub
  | 0 => .tm b B
  | 1 => .tm a A
  | j + 2 => σ j

def SubOk (σ : Nat → Sub) (Γ Δ : Ctx) : Prop := ∀ j T, Γ j = some T → (σ j).Ok Δ T

def Tm.psubst : (Nat → Sub) → Tm → Tm
  | σ, .var k =>
      match σ k with
      | .ren i => .var i
      | .tm s _ => s
  | _, .unit => .unit
  | σ, .pair a b => .pair (Tm.psubst σ a) (Tm.psubst σ b)
  | σ, .boxtm t => .boxtm (Tm.psubst (unboxSub σ) t)
  | σ, .diatm x t =>
      match σ x with
      | .ren i => .diatm i (Tm.psubst (Function.update (unboxSub σ) x (.ren i)) t)
      -- modal β: the witness slot receives the substituted diaterm's body
      | .tm (.diatm y u) (.dia _ U) =>
          .diatm y (Tm.psubst (Function.update (unboxSub σ) x (.tm u (U.mapIdx Idx.strip))) t)
      | .tm _ _ => .unit
  | σ, .pelim p t =>
      match σ p with
      | .ren i => .pelim i (Tm.psubst (liftSub2 σ) t)
      -- pair β
      | .tm (.pair a b) (.prod A B) => Tm.psubst (pairSub a A b B σ) t
      | .tm _ _ => .unit

/-- Inside a `◇_y` of the target, a box slot of the source still fits, and its indices translate
    the same way on both sides. -/
theorem boxSlot_diaCtx {Γ Δ : Ctx} {σ : Nat → Sub} (hσ : SubOk σ Γ Δ) {x : Nat} {X : Ty}
    {y : Nat} {Y : Ty} (hy : Δ y = some (.dia Y)) {j : Nat} {T : Ty} (hjx : j ≠ x)
    (hj : diaCtx Γ x X j = some T) :
    ((unboxSub σ) j).Ok (diaCtx Δ y Y) T ∧
      ∀ p, T.DiaAt p → diaOut y (((unboxSub σ) j).idx p) = (σ j).idx (.box :: p) := by
  rw [diaCtx, Function.update_of_ne hjx] at hj
  have hokj := hσ _ _ (unboxSlot_eq_some.mp hj)
  simp only [unboxSub]
  cases hsj : σ j with
  | ren k =>
      rw [hsj] at hokj
      simp only [Sub.Ok] at hokj
      have hne : k ≠ y := fun he => by
        rw [he, hy] at hokj; simp at hokj
      refine ⟨?_, fun p _ => ?_⟩
      · show diaCtx Δ y Y k = some T
        rw [diaCtx, Function.update_of_ne hne]
        exact unboxSlot_eq_some.mpr hokj
      · simp [Sub.unbox, Sub.idx, diaOut, hne, Idx.pre]
  | tm s S' =>
      rw [hsj] at hokj
      simp only [Sub.Ok] at hokj
      obtain ⟨hs, he, hpf⟩ := hokj
      obtain ⟨u, U, rfl, rfl, hu, hupf⟩ := canon_box hs hpf he
      have hUe : U.erase = T := by simpa [ITy.erase] using he
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Sub.unbox, Sub.Ok, ITy.mapIdx_mapIdx, strip_comp_boxOut, ITy.mapIdx_id]
        refine ⟨hu.mono ?_, hUe, hupf⟩
        intro k K hk
        have hky : k ≠ y := fun he => by
          rw [he] at hk; simp [unboxCtx, hy, unboxSlot] at hk
        rw [diaCtx, Function.update_of_ne hky]
        exact hk
      · have hp' : U.erase.DiaAt p := hUe ▸ hp
        simp only [Sub.unbox, Sub.idx, ITy.idxAt, ITy.mapIdx_mapIdx, strip_comp_boxOut,
          ITy.mapIdx_id]
        rw [ITy.idxAt_mapIdx _ _ _ hp']
        obtain ⟨K, hK, -⟩ := hu.scoped _ (ITy.idxAt_mem U p hp')
        have hne : (U.idxAt p).var ≠ y := fun he => by
          rw [he] at hK; simp [unboxCtx, hy, unboxSlot] at hK
        simp [diaOut, hne, boxOut]

/-- ⭐**Substitution preserves typing**, with the type's indices mapped by the substitution. -/
theorem HasTy.psubst {Γ : Ctx} {t : Tm} {S : ITy} (h : HasTy Γ t S) :
    ∀ {σ : Nat → Sub} {Δ : Ctx}, SubOk σ Γ Δ → HasTy Δ (t.psubst σ) (S.mapIdx (subIdx σ)) := by
  induction h with
  | @var Γ k hk =>
      intro σ Δ hσ
      have hok := hσ _ _ hk
      simp only [Tm.psubst, ITy.mapIdx]
      cases hsk : σ k with
      | ren i =>
          rw [hsk] at hok
          exact .var hok
      | tm s S' =>
          rw [hsk] at hok
          simp only [Sub.Ok] at hok
          obtain ⟨hs, he, -⟩ := hok
          rw [ITy.erase_eq_base he] at hs
          exact hs
  | unit => intro σ Δ _; exact .unit
  | pair _ _ iha ihb => intro σ Δ hσ; exact .pair (iha hσ) (ihb hσ)
  | @boxtm Γ t S ht ih =>
      intro σ Δ hσ
      have hσ' : SubOk (unboxSub σ) (unboxCtx Γ) (unboxCtx Δ) := by
        intro j T hj
        have hok := hσ _ _ (unboxSlot_eq_some.mp hj)
        simp only [unboxSub]
        cases hsj : σ j with
        | ren i =>
            rw [hsj] at hok
            exact unboxSlot_eq_some.mpr hok
        | tm s S' =>
            rw [hsj] at hok
            simp only [Sub.Ok] at hok
            obtain ⟨hs, he, hpf⟩ := hok
            obtain ⟨u, U, rfl, rfl, hu, hupf⟩ := canon_box hs hpf he
            simp only [Sub.unbox, Sub.Ok, ITy.mapIdx_mapIdx, strip_comp_boxOut, ITy.mapIdx_id]
            exact ⟨hu, by simpa [ITy.erase] using he, hupf⟩
      have hty := HasTy.boxtm (ih hσ')
      have heq : (S.mapIdx (subIdx (unboxSub σ))).mapIdx boxOut
          = (S.mapIdx boxOut).mapIdx (subIdx σ) := by
        rw [ITy.mapIdx_mapIdx, ITy.mapIdx_mapIdx]
        apply ITy.mapIdx_congr
        intro i hi
        obtain ⟨T, hT, hD⟩ := ht.scoped i hi
        have hok := hσ _ _ (unboxSlot_eq_some.mp hT)
        show boxOut ((σ i.var).unbox.idx i.path) = (σ i.var).idx (.box :: i.path)
        cases hsj : σ i.var with
        | ren k => rfl
        | tm s S' =>
            rw [hsj] at hok
            simp only [Sub.Ok] at hok
            obtain ⟨hs, he, hpf⟩ := hok
            obtain ⟨u, U, rfl, rfl, -, -⟩ := canon_box hs hpf he
            have hD' : U.erase.DiaAt i.path := by
              have hUe : U.erase = T := by simpa [ITy.erase] using he
              rw [hUe]; exact hD
            simp only [Sub.unbox, Sub.idx, ITy.idxAt, ITy.mapIdx_mapIdx, strip_comp_boxOut,
              ITy.mapIdx_id]
            rw [ITy.idxAt_mapIdx _ _ _ hD']
      rw [heq] at hty
      exact hty
  | @diatm Γ x X t S hx ht ih =>
      intro σ Δ hσ
      have hok := hσ _ _ hx
      cases hsx : σ x with
      | ren i =>
          rw [hsx] at hok
          have hi : Δ i = some (.dia X) := hok
          have hσ' : SubOk (Function.update (unboxSub σ) x (.ren i)) (diaCtx Γ x X)
              (diaCtx Δ i X) := by
            intro j T hj
            by_cases hjx : j = x
            · subst hjx
              simp only [diaCtx, Function.update_self, Option.some.injEq] at hj
              subst hj
              simp [Sub.Ok, diaCtx]
            · rw [Function.update_of_ne hjx]
              exact (boxSlot_diaCtx hσ hi hjx hj).1
          have hty := HasTy.diatm hi (ih hσ')
          have heqT : ITy.dia ⟨i, []⟩ ((S.mapIdx (subIdx (Function.update (unboxSub σ) x
                (.ren i)))).mapIdx (diaOut i))
              = (ITy.dia ⟨x, []⟩ (S.mapIdx (diaOut x))).mapIdx (subIdx σ) := by
            simp only [ITy.mapIdx]
            congr 1
            · simp [subIdx, hsx, Sub.idx]
            · rw [ITy.mapIdx_mapIdx, ITy.mapIdx_mapIdx]
              apply ITy.mapIdx_congr
              intro j hj
              obtain ⟨T, hT, hD⟩ := ht.scoped j hj
              by_cases hjx : j.var = x
              · have hv : diaOut x j = j.pre .dia := by simp [diaOut, hjx]
                show diaOut i ((Function.update (unboxSub σ) x (.ren i) j.var).idx j.path)
                  = (σ (diaOut x j).var).idx (diaOut x j).path
                rw [hv, Function.update_apply, if_pos hjx]
                simp [Idx.pre, hjx, hsx, Sub.idx, diaOut]
              · have hv : diaOut x j = j.pre .box := by simp [diaOut, hjx]
                show diaOut i ((Function.update (unboxSub σ) x (.ren i) j.var).idx j.path)
                  = (σ (diaOut x j).var).idx (diaOut x j).path
                rw [hv, Function.update_of_ne hjx]
                exact (boxSlot_diaCtx hσ hi hjx hT).2 j.path hD
          rw [← heqT]
          simp only [Tm.psubst, hsx]
          exact hty
      | tm s S' =>
          rw [hsx] at hok
          simp only [Sub.Ok] at hok
          obtain ⟨hs, he, hpf⟩ := hok
          obtain ⟨y, Y, u, U, rfl, rfl, hy, hu, hupf⟩ := canon_dia hs hpf he
          have hUe : U.erase = X := by simpa [ITy.erase] using he
          have hσ' : SubOk (Function.update (unboxSub σ) x
              (.tm u ((U.mapIdx (diaOut y)).mapIdx Idx.strip))) (diaCtx Γ x X) (diaCtx Δ y Y) := by
            intro j T hj
            by_cases hjx : j = x
            · subst hjx
              simp only [diaCtx, Function.update_self, Option.some.injEq] at hj
              subst hj
              simp only [Function.update_self, Sub.Ok, ITy.mapIdx_mapIdx, strip_comp_diaOut,
                ITy.mapIdx_id]
              exact ⟨hu, hUe, hupf⟩
            · rw [Function.update_of_ne hjx]
              exact (boxSlot_diaCtx hσ hy hjx hj).1
          have hty := HasTy.diatm hy (ih hσ')
          have heqT : ITy.dia ⟨y, []⟩ ((S.mapIdx (subIdx (Function.update (unboxSub σ) x
                (.tm u ((U.mapIdx (diaOut y)).mapIdx Idx.strip))))).mapIdx (diaOut y))
              = (ITy.dia ⟨x, []⟩ (S.mapIdx (diaOut x))).mapIdx (subIdx σ) := by
            simp only [ITy.mapIdx]
            congr 1
            · simp [subIdx, hsx, Sub.idx, ITy.idxAt]
            · rw [ITy.mapIdx_mapIdx _ (diaOut y) S, ITy.mapIdx_mapIdx (diaOut x) (subIdx σ) S]
              apply ITy.mapIdx_congr
              intro j hj
              obtain ⟨T, hT, hD⟩ := ht.scoped j hj
              by_cases hjx : j.var = x
              · -- the witness slot: modal β
                have hv : diaOut x j = j.pre .dia := by simp [diaOut, hjx]
                have hTX : T = X := by
                  rw [diaCtx, Function.update_apply, if_pos hjx] at hT
                  exact (Option.some.inj hT).symm
                subst hTX
                have hD' : U.erase.DiaAt j.path := by rw [hUe]; exact hD
                show diaOut y ((Function.update (unboxSub σ) x
                    (.tm u ((U.mapIdx (diaOut y)).mapIdx Idx.strip)) j.var).idx j.path)
                  = (σ (diaOut x j).var).idx (diaOut x j).path
                rw [hv, Function.update_apply, if_pos hjx]
                simp only [Idx.pre, hjx, hsx, Sub.idx, ITy.idxAt, ITy.mapIdx_mapIdx,
                  strip_comp_diaOut, ITy.mapIdx_id]
                rw [ITy.idxAt_mapIdx _ _ _ hD']
              · have hv : diaOut x j = j.pre .box := by simp [diaOut, hjx]
                show diaOut y ((Function.update (unboxSub σ) x
                    (.tm u ((U.mapIdx (diaOut y)).mapIdx Idx.strip)) j.var).idx j.path)
                  = (σ (diaOut x j).var).idx (diaOut x j).path
                rw [hv, Function.update_of_ne hjx]
                exact (boxSlot_diaCtx hσ hy hjx hT).2 j.path hD
          rw [← heqT]
          simp only [Tm.psubst, hsx]
          exact hty
  | @pelim Γ p A B t S hp ht ih =>
      intro σ Δ hσ
      have hok := hσ _ _ hp
      cases hsp : σ p with
      | ren i =>
          rw [hsp] at hok
          have hi : Δ i = some (.prod A B) := hok
          have hσ' : SubOk (liftSub2 σ) (cons2 (some B) (some A) Γ) (cons2 (some B) (some A) Δ) := by
            intro j T hj
            rcases j with _ | _ | j
            · exact hj
            · exact hj
            · have hokj := hσ _ _ hj
              show (σ j).shift2.Ok (cons2 (some B) (some A) Δ) T
              cases hsj : σ j with
              | ren k => rw [hsj] at hokj; exact hokj
              | tm s S' =>
                  rw [hsj] at hokj
                  simp only [Sub.Ok] at hokj
                  obtain ⟨hs, he, hpf⟩ := hokj
                  simp only [Sub.shift2, Sub.Ok, ITy.erase_mapIdx]
                  exact ⟨hs.rename (fun _ _ hk => hk), he, hpf.rename _⟩
          have hty := HasTy.pelim hi (ih hσ')
          have heqT : (S.mapIdx (subIdx (liftSub2 σ))).mapIdx (pelimOut i)
              = (S.mapIdx (pelimOut p)).mapIdx (subIdx σ) := by
            rw [ITy.mapIdx_mapIdx, ITy.mapIdx_mapIdx]
            apply ITy.mapIdx_congr
            intro j hj
            obtain ⟨T, hT, hD⟩ := ht.scoped j hj
            rcases j with ⟨_ | _ | v, path⟩
            · simp [subIdx, liftSub2, pelimOut, Sub.idx, hsp]
            · simp [subIdx, liftSub2, pelimOut, Sub.idx, hsp]
            · have hokv := hσ _ _ hT
              show pelimOut i ((σ v).shift2.idx path) = (σ v).idx path
              cases hsv : σ v with
              | ren k => rfl
              | tm s S' =>
                  rw [hsv] at hokv
                  simp only [Sub.Ok] at hokv
                  obtain ⟨-, he, -⟩ := hokv
                  have hD' : S'.erase.DiaAt path := by rw [he]; exact hD
                  simp only [Sub.shift2, Sub.idx]
                  rw [ITy.idxAt_mapIdx _ _ _ hD']
                  rfl
          rw [← heqT]
          simp only [Tm.psubst, hsp]
          exact hty
      | tm s S' =>
          rw [hsp] at hok
          simp only [Sub.Ok] at hok
          obtain ⟨hs, he, hpf⟩ := hok
          obtain ⟨a, b, A', B', rfl, rfl, ha, hb, hapf, hbpf⟩ := canon_prod hs hpf he
          have hAe : A'.erase = A ∧ B'.erase = B := by simpa [ITy.erase] using he
          have hσ' : SubOk (pairSub a A' b B' σ) (cons2 (some B) (some A) Γ) Δ := by
            intro j T hj
            rcases j with _ | _ | j
            · simp only [cons2, Option.some.injEq] at hj
              subst hj
              exact ⟨hb, hAe.2, hbpf⟩
            · simp only [cons2, Option.some.injEq] at hj
              subst hj
              exact ⟨ha, hAe.1, hapf⟩
            · exact hσ _ _ hj
          have hty := ih hσ'
          have heqT : S.mapIdx (subIdx (pairSub a A' b B' σ))
              = (S.mapIdx (pelimOut p)).mapIdx (subIdx σ) := by
            rw [ITy.mapIdx_mapIdx]
            apply ITy.mapIdx_congr
            intro j _
            rcases j with ⟨_ | _ | v, path⟩
            · simp [subIdx, pairSub, pelimOut, Sub.idx, hsp, ITy.idxAt]
            · simp [subIdx, pairSub, pelimOut, Sub.idx, hsp, ITy.idxAt]
            · rfl
          rw [← heqT]
          simp only [Tm.psubst, hsp]
          exact hty

/-! ## The substitution-fitness facts, standalone (for the equality commutation below) -/

theorem SubOk.unbox {σ : Nat → Sub} {Γ Δ : Ctx} (hσ : SubOk σ Γ Δ) :
    SubOk (unboxSub σ) (unboxCtx Γ) (unboxCtx Δ) := by
  intro j T hj
  have hok := hσ _ _ (unboxSlot_eq_some.mp hj)
  simp only [unboxSub]
  cases hsj : σ j with
  | ren i =>
      rw [hsj] at hok
      exact unboxSlot_eq_some.mpr hok
  | tm s S' =>
      rw [hsj] at hok
      simp only [Sub.Ok] at hok
      obtain ⟨hs, he, hpf⟩ := hok
      obtain ⟨u, U, rfl, rfl, hu, hupf⟩ := canon_box hs hpf he
      simp only [Sub.unbox, Sub.Ok, ITy.mapIdx_mapIdx, strip_comp_boxOut, ITy.mapIdx_id]
      exact ⟨hu, by simpa [ITy.erase] using he, hupf⟩

theorem SubOk.diaRen {σ : Nat → Sub} {Γ Δ : Ctx} (hσ : SubOk σ Γ Δ) {x : Nat} {X : Ty} {i : Nat}
    (hi : Δ i = some (.dia X)) :
    SubOk (Function.update (unboxSub σ) x (.ren i)) (diaCtx Γ x X) (diaCtx Δ i X) := by
  intro j T hj
  by_cases hjx : j = x
  · subst hjx
    simp only [diaCtx, Function.update_self, Option.some.injEq] at hj
    subst hj
    simp [Sub.Ok, diaCtx]
  · rw [Function.update_of_ne hjx]
    exact (boxSlot_diaCtx hσ hi hjx hj).1

theorem SubOk.diaTm {σ : Nat → Sub} {Γ Δ : Ctx} (hσ : SubOk σ Γ Δ) {x : Nat} {X : Ty}
    {y : Nat} {Y : Ty} (hy : Δ y = some (.dia Y)) {u : Tm} {U : ITy}
    (hu : HasTy (diaCtx Δ y Y) u U) (hUe : U.erase = X) (hupf : u.PelimFree) :
    SubOk (Function.update (unboxSub σ) x (.tm u ((U.mapIdx (diaOut y)).mapIdx Idx.strip)))
      (diaCtx Γ x X) (diaCtx Δ y Y) := by
  intro j T hj
  by_cases hjx : j = x
  · subst hjx
    simp only [diaCtx, Function.update_self, Option.some.injEq] at hj
    subst hj
    simp only [Function.update_self, Sub.Ok, ITy.mapIdx_mapIdx, strip_comp_diaOut, ITy.mapIdx_id]
    exact ⟨hu, hUe, hupf⟩
  · rw [Function.update_of_ne hjx]
    exact (boxSlot_diaCtx hσ hy hjx hj).1

/-! ## Formulas, and equality defined by the extensionality equations -/

inductive Wff where
  | prim (a b : Tm)
  | top
  | conj (φ ψ : Wff)
  | imp (φ ψ : Wff)
  | box (φ : Wff)
  | boxx (x : Nat) (φ : Wff)

inductive WfWff : Ctx → Wff → Prop where
  | prim {Γ : Ctx} {a b : Tm} : HasTy Γ a .base → HasTy Γ b .base → WfWff Γ (.prim a b)
  | top {Γ : Ctx} : WfWff Γ .top
  | conj {Γ : Ctx} {φ ψ : Wff} : WfWff Γ φ → WfWff Γ ψ → WfWff Γ (.conj φ ψ)
  | imp {Γ : Ctx} {φ ψ : Wff} : WfWff Γ φ → WfWff Γ ψ → WfWff Γ (.imp φ ψ)
  | box {Γ : Ctx} {φ : Wff} : WfWff (unboxCtx Γ) φ → WfWff Γ (.box φ)
  | boxx {Γ : Ctx} {x : Nat} {X : Ty} {φ : Wff} :
      Γ x = some (.dia X) → WfWff (diaCtx Γ x X) φ → WfWff Γ (.boxx x φ)

/-- ⭐**The defined equality.**  The `◇` arm takes its witness from the LEFT term and never looks at
    the right one's: there is no different-witness (`⊥`) case, because typing makes it
    unstatable (`witness_eq`).  (Neutral `pelim` terms are not modelled — the junk arm.) -/
def eqf : Ty → Tm → Tm → Wff
  | .base, a, b => .prim a b
  | .unit, _, _ => .top
  | .prod A B, .pair a b, .pair c d => .conj (eqf A a c) (eqf B b d)
  | .box A, .boxtm t, .boxtm s => .box (eqf A t s)
  | .dia A, .diatm x t, .diatm _ s => .boxx x (eqf A t s)
  | _, _, _ => .top

theorem HasTy.diatm_inv {Γ : Ctx} {x : Nat} {t : Tm} {S : ITy} (h : HasTy Γ (.diatm x t) S) :
    ∃ X U, Γ x = some (.dia X) ∧ HasTy (diaCtx Γ x X) t U ∧
      S = .dia ⟨x, []⟩ (U.mapIdx (diaOut x)) := by
  cases h with
  | diatm hx ht => exact ⟨_, _, hx, ht, rfl⟩

/-- ⭐**Two `◇`-terms of the same type have the same witness.**  So an equation between
    different-witness `◇`-terms cannot even be written down. -/
theorem witness_eq {Γ : Ctx} {x y : Nat} {t s : Tm} {S : ITy}
    (ht : HasTy Γ (.diatm x t) S) (hs : HasTy Γ (.diatm y s) S) : x = y := by
  obtain ⟨_, _, _, _, rfl⟩ := ht.diatm_inv
  obtain ⟨_, _, _, _, h⟩ := hs.diatm_inv
  simp only [ITy.dia.injEq, Idx.mk.injEq] at h
  exact h.1.1

/-- The inner data of two same-typed `◇`-terms coincide: same witness, same witness type, same
    inner type.  No casts are needed anywhere. -/
theorem dia_same_inner {Γ : Ctx} {x : Nat} {X : Ty} {b : Tm} {S : ITy}
    (hx : Γ x = some (.dia X)) (hb : HasTy Γ b (.dia ⟨x, []⟩ (S.mapIdx (diaOut x))))
    (hpb : b.PelimFree) :
    ∃ s, b = .diatm x s ∧ HasTy (diaCtx Γ x X) s S ∧ s.PelimFree := by
  obtain ⟨y, Y, s, U, rfl, hS, hy, hs, hspf⟩ := canon_dia hb hpb rfl
  simp only [ITy.dia.injEq, Idx.mk.injEq, and_true] at hS
  obtain ⟨rfl, hSU⟩ := hS
  have hUS : U = S := (ITy.mapIdx_injective (diaOut_injective x) hSU).symm
  subst hUS
  rw [hx, Option.some.injEq, Ty.dia.injEq] at hy
  subst hy
  exact ⟨s, rfl, hs, hspf⟩

theorem box_same_inner {Γ : Ctx} {b : Tm} {S : ITy} (hb : HasTy Γ b (.box (S.mapIdx boxOut)))
    (hpb : b.PelimFree) :
    ∃ s, b = .boxtm s ∧ HasTy (unboxCtx Γ) s S ∧ s.PelimFree := by
  obtain ⟨s, U, rfl, hS, hs, hspf⟩ := canon_box hb hpb rfl
  simp only [ITy.box.injEq] at hS
  have hUS : U = S := (ITy.mapIdx_injective boxOut_injective hS).symm
  subst hUS
  exact ⟨s, rfl, hs, hspf⟩

theorem pair_same_inner {Γ : Ctx} {b : Tm} {A B : ITy} (hb : HasTy Γ b (.prod A B))
    (hpb : b.PelimFree) :
    ∃ c d, b = .pair c d ∧ HasTy Γ c A ∧ HasTy Γ d B ∧ c.PelimFree ∧ d.PelimFree := by
  obtain ⟨c, d, A', B', rfl, hS, hc, hd, hcpf, hdpf⟩ := canon_prod hb hpb rfl
  simp only [ITy.prod.injEq] at hS
  obtain ⟨rfl, rfl⟩ := hS
  exact ⟨c, d, rfl, hc, hd, hcpf, hdpf⟩

/-- The defined equality of two same-typed terms is a well-formed formula — the `◇` arm's `□_x`
    lands in the right context BECAUSE the witnesses agree. -/
theorem eqf_wf {Γ : Ctx} {a : Tm} {S : ITy} (ha : HasTy Γ a S) :
    ∀ {b : Tm}, HasTy Γ b S → a.PelimFree → b.PelimFree → WfWff Γ (eqf S.erase a b) := by
  induction ha with
  | var hk => intro b hb _ _; exact .prim (.var hk) hb
  | unit => intro b _ _ _; exact .top
  | pair _ _ iha ihb =>
      intro b hb hpa hpb
      obtain ⟨c, d, rfl, hc, hd, hcpf, hdpf⟩ := pair_same_inner hb hpb
      exact .conj (iha hc hpa.1 hcpf) (ihb hd hpa.2 hdpf)
  | boxtm _ ih =>
      intro b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := box_same_inner hb hpb
      simp only [ITy.erase, ITy.erase_mapIdx, eqf]
      exact .box (ih hs hpa hspf)
  | diatm hx _ ih =>
      intro b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := dia_same_inner hx hb hpb
      simp only [ITy.erase, ITy.erase_mapIdx, eqf]
      exact .boxx hx (ih hs hpa hspf)
  | pelim => intro _ _ hpa _; exact hpa.elim

/-! ## A minimal proof system; reflexivity and symmetry -/

inductive Pf : Wff → Prop where
  | primRefl (t : Tm) : Pf (.prim t t)
  | primSymm {a b : Tm} : Pf (.imp (.prim a b) (.prim b a))
  | topI : Pf .top
  | idimp {p : Wff} : Pf (.imp p p)
  | conjI {p q : Wff} : Pf p → Pf q → Pf (.conj p q)
  | conjCong {p p' q q' : Wff} :
      Pf (.imp p p') → Pf (.imp q q') → Pf (.imp (.conj p q) (.conj p' q'))
  | nec {p : Wff} : Pf p → Pf (.box p)
  | necx {x : Nat} {p : Wff} : Pf p → Pf (.boxx x p)
  | Kdist {p q : Wff} : Pf (.box (.imp p q)) → Pf (.imp (.box p) (.box q))
  | Kdistx {x : Nat} {p q : Wff} : Pf (.boxx x (.imp p q)) → Pf (.imp (.boxx x p) (.boxx x q))

theorem eqf_refl {Γ : Ctx} {a : Tm} {S : ITy} (ha : HasTy Γ a S) (hpa : a.PelimFree) :
    Pf (eqf S.erase a a) := by
  induction ha with
  | var => exact .primRefl _
  | unit => exact .topI
  | pair _ _ iha ihb => exact .conjI (iha hpa.1) (ihb hpa.2)
  | boxtm _ ih => simp only [ITy.erase, ITy.erase_mapIdx, eqf]; exact .nec (ih hpa)
  | diatm _ _ ih => simp only [ITy.erase, ITy.erase_mapIdx, eqf]; exact .necx (ih hpa)
  | pelim => exact hpa.elim

/-- ⭐**Symmetry, with no different-witness case.**  The `◇` case is `Kdistx ∘ necx` of the inner
    instance at the ONE witness both sides share. -/
theorem eqf_symm {Γ : Ctx} {a : Tm} {S : ITy} (ha : HasTy Γ a S) :
    ∀ {b : Tm}, HasTy Γ b S → a.PelimFree → b.PelimFree →
      Pf (.imp (eqf S.erase a b) (eqf S.erase b a)) := by
  induction ha with
  | var => intro _ _ _ _; exact .primSymm
  | unit => intro _ _ _ _; exact .idimp
  | pair _ _ iha ihb =>
      intro b hb hpa hpb
      obtain ⟨c, d, rfl, hc, hd, hcpf, hdpf⟩ := pair_same_inner hb hpb
      exact .conjCong (iha hc hpa.1 hcpf) (ihb hd hpa.2 hdpf)
  | boxtm _ ih =>
      intro b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := box_same_inner hb hpb
      simp only [ITy.erase, ITy.erase_mapIdx, eqf]
      exact .Kdist (.nec (ih hs hpa hspf))
  | diatm hx _ ih =>
      intro b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := dia_same_inner hx hb hpb
      simp only [ITy.erase, ITy.erase_mapIdx, eqf]
      exact .Kdistx (.necx (ih hs hpa hspf))
  | pelim => intro _ _ hpa _; exact hpa.elim

/-! ## Equality commutes with substitution

This is exactly what failed with `⊥` for different witnesses: a substitution that MERGED two
witnesses turned `⊥` into a formula that should have been `□_x(…)`.  Here it is a plain equation,
proved by induction — the `◇` arm is modal β on both sides at the one shared witness. -/

def Wff.psubst : (Nat → Sub) → Wff → Wff
  | σ, .prim a b => .prim (a.psubst σ) (b.psubst σ)
  | _, .top => .top
  | σ, .conj φ ψ => .conj (Wff.psubst σ φ) (Wff.psubst σ ψ)
  | σ, .imp φ ψ => .imp (Wff.psubst σ φ) (Wff.psubst σ ψ)
  | σ, .box φ => .box (Wff.psubst (unboxSub σ) φ)
  | σ, .boxx x φ =>
      match σ x with
      | .ren i => .boxx i (Wff.psubst (Function.update (unboxSub σ) x (.ren i)) φ)
      | .tm (.diatm y u) (.dia _ U) =>
          .boxx y (Wff.psubst (Function.update (unboxSub σ) x (.tm u (U.mapIdx Idx.strip))) φ)
      | .tm _ _ => .top

theorem eqf_psubst {Γ : Ctx} {a : Tm} {S : ITy} (ha : HasTy Γ a S) :
    ∀ {b : Tm}, HasTy Γ b S → a.PelimFree → b.PelimFree →
      ∀ {σ : Nat → Sub} {Δ : Ctx}, SubOk σ Γ Δ →
        (eqf S.erase a b).psubst σ = eqf S.erase (a.psubst σ) (b.psubst σ) := by
  induction ha with
  | var => intro _ _ _ _ _ _ _; rfl
  | unit => intro _ _ _ _ _ _ _; rfl
  | pair _ _ iha ihb =>
      intro b hb hpa hpb σ Δ hσ
      obtain ⟨c, d, rfl, hc, hd, hcpf, hdpf⟩ := pair_same_inner hb hpb
      simp only [ITy.erase, eqf, Wff.psubst, Tm.psubst]
      rw [iha hc hpa.1 hcpf hσ, ihb hd hpa.2 hdpf hσ]
  | boxtm _ ih =>
      intro b hb hpa hpb σ Δ hσ
      obtain ⟨s, rfl, hs, hspf⟩ := box_same_inner hb hpb
      simp only [ITy.erase, ITy.erase_mapIdx, eqf, Wff.psubst, Tm.psubst]
      rw [ih hs hpa hspf hσ.unbox]
  | @diatm Γ x X t S hx ht ih =>
      intro b hb hpa hpb σ Δ hσ
      obtain ⟨s, rfl, hs, hspf⟩ := dia_same_inner hx hb hpb
      have hok := hσ _ _ hx
      simp only [ITy.erase, ITy.erase_mapIdx, eqf, Wff.psubst, Tm.psubst]
      cases hsx : σ x with
      | ren i =>
          rw [hsx] at hok
          simp only [Sub.Ok] at hok
          simp only [eqf]
          rw [ih hs hpa hspf (hσ.diaRen hok)]
      | tm s' S' =>
          rw [hsx] at hok
          simp only [Sub.Ok] at hok
          obtain ⟨hs', he, hpf'⟩ := hok
          obtain ⟨y, Y, u, U, rfl, rfl, hy, hu, hupf⟩ := canon_dia hs' hpf' he
          simp only [eqf]
          rw [ih hs hpa hspf (hσ.diaTm hy hu (by simpa [ITy.erase] using he) hupf)]
  | pelim => intro _ _ hpa _ _ _ _; exact hpa.elim

end DiaIdx

#print axioms DiaIdx.HasTy.psubst
#print axioms DiaIdx.witness_eq
#print axioms DiaIdx.eqf_wf
#print axioms DiaIdx.eqf_refl
#print axioms DiaIdx.eqf_symm
#print axioms DiaIdx.eqf_psubst
