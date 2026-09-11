import Mathlib.Tactic

/-!
# Prototype — the ◇-witness carried in the TYPE

Isolated (no QML imports).  Tests the design in which a `◇`-term records its witness in its type,
`◇_x t : ◇_x A`, with every variable SELF-indexed, and a type index only ever arising from promotion
of exactly one variable.

**Two-step typing.**  Variables are DECLARED at plain types (`Ty`; contexts hold only these).  The
types of TERMS are ELABORATED: a plain type together with an index annotation over it
(`ITy T`, indexed by the plain type `T`).  Keeping the plain type as the family index means every
index translation leaves it unchanged definitionally — which is what lets the semantics interpret a
term at its plain type with no casts.

**Indices are access paths.**  An index `⟨v, p⟩` names the `◇`-node reached from variable `v` by the
steps `p` (`fst`/`snd` into products, `box`/`dia` into modal layers).  Promotions translate indices
outward by PREPENDING one step, which keeps levels apart: `z : ◇◇W` elaborates to
`◇_⟨z,[]⟩ ◇_⟨z,[dia]⟩ W`, and inside `◇_z` the realization value `z : ◇W` is `◇_⟨z,[]⟩ W` again.

Simplifications (orthogonal to the question):
* de Bruijn positions, and contexts are FUNCTIONS `Nat → Option Ty` — a promotion HIDES or
  REVEALS slots rather than shifting them, so positions are stable across modal layers;
* the box shadow is canonical (`unboxCtx`: box-typed slots unboxed, everything else hidden);
* `pelim p` binds the two components as fresh positions `0` (snd) and `1` (fst);
* only `.base`-typed variables are terms (faithful to the real grammar).
-/

namespace DiaIdx

/-! ## Plain types, access paths, and elaborated (indexed) types -/

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

/-- The elaborated type of a term: an index annotation over the plain type `T`. -/
inductive ITy : Ty → Type where
  | base : ITy .base
  | unit : ITy .unit
  | prod {A B : Ty} (a : ITy A) (b : ITy B) : ITy (.prod A B)
  | box {A : Ty} (a : ITy A) : ITy (.box A)
  | dia {A : Ty} (i : Idx) (a : ITy A) : ITy (.dia A)

namespace ITy

def mapIdx (f : Idx → Idx) : {T : Ty} → ITy T → ITy T
  | _, base => base
  | _, unit => unit
  | _, prod a b => prod (a.mapIdx f) (b.mapIdx f)
  | _, box a => box (a.mapIdx f)
  | _, dia i a => dia (f i) (a.mapIdx f)

def idxs : {T : Ty} → ITy T → List Idx
  | _, base => []
  | _, unit => []
  | _, prod a b => a.idxs ++ b.idxs
  | _, box a => a.idxs
  | _, dia i a => i :: a.idxs

/-- The index at the `◇`-node reached by a path (junk if the path does not lead to one). -/
def idxAt : {T : Ty} → ITy T → List Step → Idx
  | _, dia i _, [] => i
  | _, prod a _, .fst :: p => a.idxAt p
  | _, prod _ b, .snd :: p => b.idxAt p
  | _, box a, .box :: p => a.idxAt p
  | _, dia _ a, .dia :: p => a.idxAt p
  | _, _, _ => ⟨0, []⟩

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

theorem mapIdx_mapIdx (f g : Idx → Idx) {T : Ty} (S : ITy T) :
    (S.mapIdx f).mapIdx g = S.mapIdx (g ∘ f) := by
  induction S with
  | base => rfl
  | unit => rfl
  | prod a b iha ihb => simp [mapIdx, iha, ihb]
  | box a ih => simp [mapIdx, ih]
  | dia i a ih => simp [mapIdx, ih]

@[simp] theorem mapIdx_id {T : Ty} (S : ITy T) : S.mapIdx id = S := by
  induction S with
  | base => rfl
  | unit => rfl
  | prod a b iha ihb => simp [mapIdx, iha, ihb]
  | box a ih => simp [mapIdx, ih]
  | dia i a ih => simp [mapIdx, ih]

theorem mapIdx_congr {f g : Idx → Idx} {T : Ty} (S : ITy T) (h : ∀ i ∈ S.idxs, f i = g i) :
    S.mapIdx f = S.mapIdx g := by
  induction S with
  | base => rfl
  | unit => rfl
  | prod a b iha ihb =>
      simp only [mapIdx]
      rw [iha (fun i hi => h i (by simp [idxs, hi])), ihb (fun i hi => h i (by simp [idxs, hi]))]
  | box a ih => simp only [mapIdx]; rw [ih (fun i hi => h i (by simpa [idxs] using hi))]
  | dia j a ih =>
      simp only [mapIdx]
      rw [h j (by simp [idxs]), ih (fun i hi => h i (by simp [idxs, hi]))]

theorem mem_idxs_mapIdx {f : Idx → Idx} {i : Idx} {T : Ty} {S : ITy T}
    (hi : i ∈ (S.mapIdx f).idxs) : ∃ j ∈ S.idxs, f j = i := by
  induction S with
  | base => simp [mapIdx, idxs] at hi
  | unit => simp [mapIdx, idxs] at hi
  | prod a b iha ihb =>
      simp only [mapIdx, idxs, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨j, hj, rfl⟩ := iha hi; exact ⟨j, by simp [idxs, hj], rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ihb hi; exact ⟨j, by simp [idxs, hj], rfl⟩
  | box a ih => simpa [mapIdx, idxs] using ih (by simpa [mapIdx, idxs] using hi)
  | dia k a ih =>
      simp only [mapIdx, idxs, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact ⟨k, by simp [idxs], rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ih hi; exact ⟨j, by simp [idxs, hj], rfl⟩

theorem idxAt_mapIdx (f : Idx → Idx) {T : Ty} (S : ITy T) (p : List Step) :
    T.DiaAt p → (S.mapIdx f).idxAt p = f (S.idxAt p) := by
  induction S generalizing p with
  | base => intro h; cases p <;> exact (h : False).elim
  | unit => intro h; cases p <;> exact (h : False).elim
  | prod a b iha ihb =>
      intro h
      rcases p with _ | ⟨s, p⟩
      · exact (h : False).elim
      · cases s
        · exact iha p h
        · exact ihb p h
        · exact (h : False).elim
        · exact (h : False).elim
  | box a ih =>
      intro h
      rcases p with _ | ⟨s, p⟩
      · exact (h : False).elim
      · cases s
        · exact (h : False).elim
        · exact (h : False).elim
        · exact ih p h
        · exact (h : False).elim
  | dia i a ih =>
      intro h
      rcases p with _ | ⟨s, p⟩
      · rfl
      · cases s
        · exact (h : False).elim
        · exact (h : False).elim
        · exact (h : False).elim
        · exact ih p h

theorem idxAt_mem {T : Ty} (S : ITy T) (p : List Step) : T.DiaAt p → S.idxAt p ∈ S.idxs := by
  induction S generalizing p with
  | base => intro h; cases p <;> exact (h : False).elim
  | unit => intro h; cases p <;> exact (h : False).elim
  | prod a b iha ihb =>
      intro h
      rcases p with _ | ⟨s, p⟩
      · exact (h : False).elim
      · cases s
        · exact List.mem_append_left _ (iha p h)
        · exact List.mem_append_right _ (ihb p h)
        · exact (h : False).elim
        · exact (h : False).elim
  | box a ih =>
      intro h
      rcases p with _ | ⟨s, p⟩
      · exact (h : False).elim
      · cases s
        · exact (h : False).elim
        · exact (h : False).elim
        · exact ih p h
        · exact (h : False).elim
  | dia i a ih =>
      intro h
      rcases p with _ | ⟨s, p⟩
      · exact List.mem_cons_self
      · cases s
        · exact (h : False).elim
        · exact (h : False).elim
        · exact (h : False).elim
        · exact List.mem_cons_of_mem _ (ih p h)

theorem mapIdx_injective {f : Idx → Idx} (hf : Function.Injective f) {T : Ty} :
    Function.Injective (ITy.mapIdx f : ITy T → ITy T) := by
  intro S S' h
  induction S with
  | base => cases S'; rfl
  | unit => cases S'; rfl
  | prod a b iha ihb =>
      cases S' with
      | prod a' b' =>
          simp only [mapIdx, prod.injEq] at h
          rw [iha h.1, ihb h.2]
  | box a ih =>
      cases S' with
      | box a' =>
          simp only [mapIdx, box.injEq] at h
          rw [ih h]
  | dia i a ih =>
      cases S' with
      | dia i' a' =>
          simp only [mapIdx, dia.injEq] at h
          rw [hf h.1, ih h.2]

end ITy

/-! ## Contexts (plain types) and the index translations -/

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

/-! ## Terms and (elaborated) typing -/

inductive Tm where
  | var (k : Nat)
  | unit
  | pair (a b : Tm)
  | boxtm (t : Tm)
  | diatm (x : Nat) (X : Ty) (t : Tm)
  | pelim (p : Nat) (A B : Ty) (t : Tm)

/-- `HasTy Γ t T S`: in the plain context `Γ`, the term `t` has plain type `T` with elaborated
    annotation `S`. -/
inductive HasTy : Ctx → Tm → (T : Ty) → ITy T → Prop where
  | var {Γ : Ctx} {k : Nat} : Γ k = some .base → HasTy Γ (.var k) .base .base
  | unit {Γ : Ctx} : HasTy Γ .unit .unit .unit
  | pair {Γ : Ctx} {a b : Tm} {A B : Ty} {SA : ITy A} {SB : ITy B} :
      HasTy Γ a A SA → HasTy Γ b B SB → HasTy Γ (.pair a b) (.prod A B) (.prod SA SB)
  | boxtm {Γ : Ctx} {t : Tm} {A : Ty} {S : ITy A} :
      HasTy (unboxCtx Γ) t A S → HasTy Γ (.boxtm t) (.box A) (.box (S.mapIdx boxOut))
  | diatm {Γ : Ctx} {x : Nat} {X : Ty} {t : Tm} {A : Ty} {S : ITy A} :
      Γ x = some (.dia X) → HasTy (diaCtx Γ x X) t A S →
      HasTy Γ (.diatm x X t) (.dia A) (.dia ⟨x, []⟩ (S.mapIdx (diaOut x)))
  | pelim {Γ : Ctx} {p : Nat} {A B : Ty} {t : Tm} {T : Ty} {S : ITy T} :
      Γ p = some (.prod A B) → HasTy (cons2 (some B) (some A) Γ) t T S →
      HasTy Γ (.pelim p A B t) T (S.mapIdx (pelimOut p))

def Tm.PelimFree : Tm → Prop
  | var _ => True
  | unit => True
  | pair a b => a.PelimFree ∧ b.PelimFree
  | boxtm t => t.PelimFree
  | diatm _ _ t => t.PelimFree
  | pelim _ _ _ _ => False

/-! ## Scoping: every index names a live variable, along a path to a `◇` -/

def Scoped (Γ : Ctx) {T : Ty} (S : ITy T) : Prop :=
  ∀ i ∈ S.idxs, ∃ T', Γ i.var = some T' ∧ T'.DiaAt i.path

theorem HasTy.scoped {Γ : Ctx} {t : Tm} {T : Ty} {S : ITy T} (h : HasTy Γ t T S) : Scoped Γ S := by
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
  | @diatm Γ x X t A S hx _ ih =>
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
  | @pelim Γ p A B t T S hp _ ih =>
      intro i hi
      obtain ⟨j, hj, rfl⟩ := ITy.mem_idxs_mapIdx hi
      obtain ⟨T', hT, hD⟩ := ih j hj
      rcases j with ⟨_ | _ | v, path⟩
      · simp only [cons2, Option.some.injEq] at hT
        subst hT
        exact ⟨_, hp, hD⟩
      · simp only [cons2, Option.some.injEq] at hT
        subst hT
        exact ⟨_, hp, hD⟩
      · exact ⟨T', hT, hD⟩

/-! ## Monotonicity: revealing slots preserves typing -/

def CtxLe (Γ Δ : Ctx) : Prop := ∀ j T, Γ j = some T → Δ j = some T

theorem CtxLe.unbox {Γ Δ : Ctx} (h : CtxLe Γ Δ) : CtxLe (unboxCtx Γ) (unboxCtx Δ) := by
  intro j T hj
  exact unboxSlot_eq_some.mpr (h _ _ (unboxSlot_eq_some.mp hj))

theorem HasTy.mono {Γ : Ctx} {t : Tm} {T : Ty} {S : ITy T} (h : HasTy Γ t T S) :
    ∀ {Δ : Ctx}, CtxLe Γ Δ → HasTy Δ t T S := by
  induction h with
  | var hk => intro Δ hle; exact .var (hle _ _ hk)
  | unit => intro Δ _; exact .unit
  | pair _ _ iha ihb => intro Δ hle; exact .pair (iha hle) (ihb hle)
  | boxtm _ ih => intro Δ hle; exact .boxtm (ih hle.unbox)
  | @diatm Γ x X t A S hx _ ih =>
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
  | diatm x X t => diatm (ρ x) X (t.rename ρ)
  | pelim p A B t => pelim (ρ p) A B (t.rename (lift2 ρ))

theorem Tm.PelimFree.rename {t : Tm} (h : t.PelimFree) (ρ : Nat → Nat) : (t.rename ρ).PelimFree := by
  induction t generalizing ρ with
  | var => trivial
  | unit => trivial
  | pair a b iha ihb => exact ⟨iha h.1 ρ, ihb h.2 ρ⟩
  | boxtm t ih => exact ih h ρ
  | diatm x X t ih => exact ih h ρ
  | pelim => exact h.elim

def RenOk (ρ : Nat → Nat) (Γ Δ : Ctx) : Prop := ∀ j T, Γ j = some T → Δ (ρ j) = some T

theorem HasTy.rename {Γ : Ctx} {t : Tm} {T : Ty} {S : ITy T} (h : HasTy Γ t T S) :
    ∀ {ρ : Nat → Nat} {Δ : Ctx}, RenOk ρ Γ Δ →
      HasTy Δ (t.rename ρ) T (S.mapIdx (Idx.ren ρ)) := by
  induction h with
  | var hk => intro ρ Δ hρ; exact .var (hρ _ _ hk)
  | unit => intro ρ Δ _; exact .unit
  | pair _ _ iha ihb => intro ρ Δ hρ; exact .pair (iha hρ) (ihb hρ)
  | @boxtm Γ t A S _ ih =>
      intro ρ Δ hρ
      have hρ' : RenOk ρ (unboxCtx Γ) (unboxCtx Δ) := fun j T hj =>
        unboxSlot_eq_some.mpr (hρ _ _ (unboxSlot_eq_some.mp hj))
      have hty := HasTy.boxtm (ih hρ')
      have heq : (S.mapIdx (Idx.ren ρ)).mapIdx boxOut = (S.mapIdx boxOut).mapIdx (Idx.ren ρ) := by
        rw [ITy.mapIdx_mapIdx, ITy.mapIdx_mapIdx]; rfl
      rw [heq] at hty
      exact hty
  | @diatm Γ x X t A S hx ht ih =>
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
  | @pelim Γ p A B t T S hp _ ih =>
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

theorem canon_box {Δ : Ctx} {s : Tm} {A : Ty} {S : ITy (.box A)} (h : HasTy Δ s (.box A) S)
    (hs : s.PelimFree) :
    ∃ (u : Tm) (U : ITy A), s = .boxtm u ∧ S = .box (U.mapIdx boxOut) ∧ HasTy (unboxCtx Δ) u A U ∧
      u.PelimFree := by
  cases h with
  | boxtm hu => exact ⟨_, _, rfl, rfl, hu, hs⟩
  | pelim => exact hs.elim

theorem canon_dia {Δ : Ctx} {s : Tm} {A : Ty} {S : ITy (.dia A)} (h : HasTy Δ s (.dia A) S)
    (hs : s.PelimFree) :
    ∃ (y : Nat) (Y : Ty) (u : Tm) (U : ITy A), s = .diatm y Y u ∧ S = .dia ⟨y, []⟩ (U.mapIdx (diaOut y)) ∧
      Δ y = some (.dia Y) ∧ HasTy (diaCtx Δ y Y) u A U ∧ u.PelimFree := by
  cases h with
  | diatm hy hu => exact ⟨_, _, _, _, rfl, rfl, hy, hu, hs⟩
  | pelim => exact hs.elim

theorem canon_prod {Δ : Ctx} {s : Tm} {A B : Ty} {S : ITy (.prod A B)}
    (h : HasTy Δ s (.prod A B) S) (hs : s.PelimFree) :
    ∃ (a b : Tm) (SA : ITy A) (SB : ITy B), s = .pair a b ∧ S = .prod SA SB ∧ HasTy Δ a A SA ∧
      HasTy Δ b B SB ∧ a.PelimFree ∧ b.PelimFree := by
  cases h with
  | pair ha hb => exact ⟨_, _, _, _, rfl, rfl, ha, hb, hs.1, hs.2⟩
  | pelim => exact hs.elim

/-! ## Simultaneous substitution

Each variable goes either to another position (`ren`) or to a pelim-free term together with its
elaborated type (`tm`).  The index map a substitution induces reads a substituted variable's indices
off that stored type: `⟨v, p⟩ ↦ S.idxAt p`.  This is where `z ↦ x` happens. -/

inductive Sub where
  | ren (i : Nat)
  | tm (s : Tm) (T : Ty) (S : ITy T)

namespace Sub

def idx : Sub → List Step → Idx
  | ren i, p => ⟨i, p⟩
  | tm _ _ S, p => S.idxAt p

/-- The entry seen through one `□`. -/
def unbox : Sub → Sub
  | ren i => ren i
  | tm (.boxtm u) (.box A) (.box U) => tm u A (U.mapIdx Idx.strip)
  | tm _ _ _ => ren 0

def shift2 : Sub → Sub
  | ren i => ren (i + 2)
  | tm s T S => tm (s.rename (· + 2)) T (S.mapIdx (Idx.ren (· + 2)))

/-- The entry fits a slot of plain type `T` in the target context. -/
def Ok (Δ : Ctx) (T : Ty) : Sub → Prop
  | ren i => Δ i = some T
  | tm s T' S => T' = T ∧ HasTy Δ s T' S ∧ s.PelimFree

end Sub

def subIdx (σ : Nat → Sub) (i : Idx) : Idx := (σ i.var).idx i.path

def unboxSub (σ : Nat → Sub) : Nat → Sub := fun j => (σ j).unbox

def liftSub2 (σ : Nat → Sub) : Nat → Sub
  | 0 => .ren 0
  | 1 => .ren 1
  | j + 2 => (σ j).shift2

def pairSub (a : Tm) (A : Ty) (SA : ITy A) (b : Tm) (B : Ty) (SB : ITy B) (σ : Nat → Sub) :
    Nat → Sub
  | 0 => .tm b B SB
  | 1 => .tm a A SA
  | j + 2 => σ j

def SubOk (σ : Nat → Sub) (Γ Δ : Ctx) : Prop := ∀ j T, Γ j = some T → (σ j).Ok Δ T

def Tm.psubst : (Nat → Sub) → Tm → Tm
  | σ, .var k =>
      match σ k with
      | .ren i => .var i
      | .tm s _ _ => s
  | _, .unit => .unit
  | σ, .pair a b => .pair (Tm.psubst σ a) (Tm.psubst σ b)
  | σ, .boxtm t => .boxtm (Tm.psubst (unboxSub σ) t)
  | σ, .diatm x X t =>
      match σ x with
      | .ren i => .diatm i X (Tm.psubst (Function.update (unboxSub σ) x (.ren i)) t)
      -- modal β: the witness slot receives the substituted diaterm's body
      | .tm (.diatm y Y u) (.dia A) (.dia _ U) =>
          .diatm y Y
            (Tm.psubst (Function.update (unboxSub σ) x (.tm u A (U.mapIdx Idx.strip))) t)
      | .tm _ _ _ => .unit
  | σ, .pelim p A B t =>
      match σ p with
      | .ren i => .pelim i A B (Tm.psubst (liftSub2 σ) t)
      -- pair β
      | .tm (.pair a b) (.prod A B) (.prod SA SB) => Tm.psubst (pairSub a A SA b B SB σ) t
      | .tm _ _ _ => .unit

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
  | tm s T' S' =>
      rw [hsj] at hokj
      simp only [Sub.Ok] at hokj
      obtain ⟨rfl, hs, hpf⟩ := hokj
      obtain ⟨u, U, rfl, rfl, hu, hupf⟩ := canon_box hs hpf
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Sub.unbox, Sub.Ok, ITy.mapIdx_mapIdx, strip_comp_boxOut, ITy.mapIdx_id]
        refine ⟨by trivial, hu.mono ?_, hupf⟩
        intro k K hk
        have hky : k ≠ y := fun he => by
          rw [he] at hk; simp [unboxCtx, hy, unboxSlot] at hk
        rw [diaCtx, Function.update_of_ne hky]
        exact hk
      · simp only [Sub.unbox, Sub.idx, ITy.idxAt, ITy.mapIdx_mapIdx, strip_comp_boxOut,
          ITy.mapIdx_id]
        rw [ITy.idxAt_mapIdx _ _ _ hp]
        obtain ⟨K, hK, -⟩ := hu.scoped _ (ITy.idxAt_mem U p hp)
        have hne : (U.idxAt p).var ≠ y := fun he => by
          rw [he] at hK; simp [unboxCtx, hy, unboxSlot] at hK
        simp [diaOut, hne, boxOut]

theorem SubOk.unbox {σ : Nat → Sub} {Γ Δ : Ctx} (hσ : SubOk σ Γ Δ) :
    SubOk (unboxSub σ) (unboxCtx Γ) (unboxCtx Δ) := by
  intro j T hj
  have hok := hσ _ _ (unboxSlot_eq_some.mp hj)
  simp only [unboxSub]
  cases hsj : σ j with
  | ren i =>
      rw [hsj] at hok
      exact unboxSlot_eq_some.mpr hok
  | tm s T' S' =>
      rw [hsj] at hok
      simp only [Sub.Ok] at hok
      obtain ⟨rfl, hs, hpf⟩ := hok
      obtain ⟨u, U, rfl, rfl, hu, hupf⟩ := canon_box hs hpf
      simp only [Sub.unbox, Sub.Ok, ITy.mapIdx_mapIdx, strip_comp_boxOut, ITy.mapIdx_id]
      exact ⟨by trivial, hu, hupf⟩

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
    {y : Nat} {Y : Ty} (hy : Δ y = some (.dia Y)) {u : Tm} {U : ITy X}
    (hu : HasTy (diaCtx Δ y Y) u X U) (hupf : u.PelimFree) :
    SubOk (Function.update (unboxSub σ) x (.tm u X ((U.mapIdx (diaOut y)).mapIdx Idx.strip)))
      (diaCtx Γ x X) (diaCtx Δ y Y) := by
  intro j T hj
  by_cases hjx : j = x
  · subst hjx
    simp only [diaCtx, Function.update_self, Option.some.injEq] at hj
    subst hj
    simp only [Function.update_self, Sub.Ok, ITy.mapIdx_mapIdx, strip_comp_diaOut, ITy.mapIdx_id]
    exact ⟨by trivial, hu, hupf⟩
  · rw [Function.update_of_ne hjx]
    exact (boxSlot_diaCtx hσ hy hjx hj).1

/-- ⭐**Substitution preserves typing**, with the annotation's indices mapped by the substitution
    and the plain type unchanged. -/
theorem HasTy.psubst {Γ : Ctx} {t : Tm} {T : Ty} {S : ITy T} (h : HasTy Γ t T S) :
    ∀ {σ : Nat → Sub} {Δ : Ctx}, SubOk σ Γ Δ →
      HasTy Δ (t.psubst σ) T (S.mapIdx (subIdx σ)) := by
  induction h with
  | @var Γ k hk =>
      intro σ Δ hσ
      have hok := hσ _ _ hk
      simp only [Tm.psubst, ITy.mapIdx]
      cases hsk : σ k with
      | ren i =>
          rw [hsk] at hok
          exact .var hok
      | tm s T' S' =>
          rw [hsk] at hok
          simp only [Sub.Ok] at hok
          obtain ⟨rfl, hs, -⟩ := hok
          cases S'
          exact hs
  | unit => intro σ Δ _; exact .unit
  | pair _ _ iha ihb => intro σ Δ hσ; exact .pair (iha hσ) (ihb hσ)
  | @boxtm Γ t A S ht ih =>
      intro σ Δ hσ
      have hty := HasTy.boxtm (ih hσ.unbox)
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
        | tm s T' S' =>
            rw [hsj] at hok
            simp only [Sub.Ok] at hok
            obtain ⟨rfl, hs, hpf⟩ := hok
            obtain ⟨u, U, rfl, rfl, -, -⟩ := canon_box hs hpf
            simp only [Sub.unbox, Sub.idx, ITy.idxAt, ITy.mapIdx_mapIdx, strip_comp_boxOut,
              ITy.mapIdx_id]
            rw [ITy.idxAt_mapIdx _ _ _ hD]
      rw [heq] at hty
      exact hty
  | @diatm Γ x X t A S hx ht ih =>
      intro σ Δ hσ
      have hok := hσ _ _ hx
      cases hsx : σ x with
      | ren i =>
          rw [hsx] at hok
          have hi : Δ i = some (.dia X) := hok
          have hty := HasTy.diatm hi (ih (hσ.diaRen hi))
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
      | tm s T' S' =>
          rw [hsx] at hok
          simp only [Sub.Ok] at hok
          obtain ⟨rfl, hs, hpf⟩ := hok
          obtain ⟨y, Y, u, U, rfl, rfl, hy, hu, hupf⟩ := canon_dia hs hpf
          have hty := HasTy.diatm hy (ih (hσ.diaTm hy hu hupf))
          have heqT : ITy.dia ⟨y, []⟩ ((S.mapIdx (subIdx (Function.update (unboxSub σ) x
                (.tm u X ((U.mapIdx (diaOut y)).mapIdx Idx.strip))))).mapIdx (diaOut y))
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
                show diaOut y ((Function.update (unboxSub σ) x
                    (.tm u T ((U.mapIdx (diaOut y)).mapIdx Idx.strip)) j.var).idx j.path)
                  = (σ (diaOut x j).var).idx (diaOut x j).path
                rw [hv, Function.update_apply, if_pos hjx]
                simp only [Idx.pre, hjx, hsx, Sub.idx, ITy.idxAt, ITy.mapIdx_mapIdx,
                  strip_comp_diaOut, ITy.mapIdx_id]
                rw [ITy.idxAt_mapIdx _ _ _ hD]
              · have hv : diaOut x j = j.pre .box := by simp [diaOut, hjx]
                show diaOut y ((Function.update (unboxSub σ) x
                    (.tm u X ((U.mapIdx (diaOut y)).mapIdx Idx.strip)) j.var).idx j.path)
                  = (σ (diaOut x j).var).idx (diaOut x j).path
                rw [hv, Function.update_of_ne hjx]
                exact (boxSlot_diaCtx hσ hy hjx hT).2 j.path hD
          rw [← heqT]
          simp only [Tm.psubst, hsx]
          exact hty
  | @pelim Γ p A B t T S hp ht ih =>
      intro σ Δ hσ
      have hok := hσ _ _ hp
      cases hsp : σ p with
      | ren i =>
          rw [hsp] at hok
          have hi : Δ i = some (.prod A B) := hok
          have hσ' : SubOk (liftSub2 σ) (cons2 (some B) (some A) Γ)
              (cons2 (some B) (some A) Δ) := by
            intro j T' hj
            rcases j with _ | _ | j
            · exact hj
            · exact hj
            · have hokj := hσ _ _ hj
              show (σ j).shift2.Ok (cons2 (some B) (some A) Δ) T'
              cases hsj : σ j with
              | ren k => rw [hsj] at hokj; exact hokj
              | tm s T'' S' =>
                  rw [hsj] at hokj
                  simp only [Sub.Ok] at hokj
                  obtain ⟨he, hs, hpf⟩ := hokj
                  simp only [Sub.shift2, Sub.Ok]
                  exact ⟨he, hs.rename (fun _ _ hk => hk), hpf.rename _⟩
          have hty := HasTy.pelim hi (ih hσ')
          have heqT : (S.mapIdx (subIdx (liftSub2 σ))).mapIdx (pelimOut i)
              = (S.mapIdx (pelimOut p)).mapIdx (subIdx σ) := by
            rw [ITy.mapIdx_mapIdx, ITy.mapIdx_mapIdx]
            apply ITy.mapIdx_congr
            intro j hj
            obtain ⟨T', hT, hD⟩ := ht.scoped j hj
            rcases j with ⟨_ | _ | v, path⟩
            · simp [subIdx, liftSub2, pelimOut, Sub.idx, hsp]
            · simp [subIdx, liftSub2, pelimOut, Sub.idx, hsp]
            · have hokv := hσ _ _ hT
              show pelimOut i ((σ v).shift2.idx path) = (σ v).idx path
              cases hsv : σ v with
              | ren k => rfl
              | tm s T'' S' =>
                  rw [hsv] at hokv
                  simp only [Sub.Ok] at hokv
                  obtain ⟨rfl, -, -⟩ := hokv
                  simp only [Sub.shift2, Sub.idx]
                  rw [ITy.idxAt_mapIdx _ _ _ hD]
                  rfl
          rw [← heqT]
          simp only [Tm.psubst, hsp]
          exact hty
      | tm s T' S' =>
          rw [hsp] at hok
          simp only [Sub.Ok] at hok
          obtain ⟨rfl, hs, hpf⟩ := hok
          obtain ⟨a, b, SA, SB, rfl, rfl, ha, hb, hapf, hbpf⟩ := canon_prod hs hpf
          have hσ' : SubOk (pairSub a A SA b B SB σ) (cons2 (some B) (some A) Γ) Δ := by
            intro j T'' hj
            rcases j with _ | _ | j
            · simp only [cons2, Option.some.injEq] at hj
              subst hj
              exact ⟨rfl, hb, hbpf⟩
            · simp only [cons2, Option.some.injEq] at hj
              subst hj
              exact ⟨rfl, ha, hapf⟩
            · exact hσ _ _ hj
          have hty := ih hσ'
          have heqT : S.mapIdx (subIdx (pairSub a A SA b B SB σ))
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

/-! ## Formulas, and equality defined by the extensionality equations -/

inductive Wff where
  | prim (a b : Tm)
  | top
  | conj (φ ψ : Wff)
  | imp (φ ψ : Wff)
  | box (φ : Wff)
  | boxx (x : Nat) (X : Ty) (φ : Wff)

inductive WfWff : Ctx → Wff → Prop where
  | prim {Γ : Ctx} {a b : Tm} :
      HasTy Γ a .base .base → HasTy Γ b .base .base → WfWff Γ (.prim a b)
  | top {Γ : Ctx} : WfWff Γ .top
  | conj {Γ : Ctx} {φ ψ : Wff} : WfWff Γ φ → WfWff Γ ψ → WfWff Γ (.conj φ ψ)
  | imp {Γ : Ctx} {φ ψ : Wff} : WfWff Γ φ → WfWff Γ ψ → WfWff Γ (.imp φ ψ)
  | box {Γ : Ctx} {φ : Wff} : WfWff (unboxCtx Γ) φ → WfWff Γ (.box φ)
  | boxx {Γ : Ctx} {x : Nat} {X : Ty} {φ : Wff} :
      Γ x = some (.dia X) → WfWff (diaCtx Γ x X) φ → WfWff Γ (.boxx x X φ)

/-- ⭐**The defined equality**, by recursion on the PLAIN type.  The `◇` arm takes its witness
    from the LEFT term and never looks at the right one's: there is no different-witness (`⊥`)
    case, because typing makes it unstatable (`witness_eq`).  (Neutral `pelim` terms are not
    modelled — the junk arm.) -/
def eqf : Ty → Tm → Tm → Wff
  | .base, a, b => .prim a b
  | .unit, _, _ => .top
  | .prod A B, .pair a b, .pair c d => .conj (eqf A a c) (eqf B b d)
  | .box A, .boxtm t, .boxtm s => .box (eqf A t s)
  | .dia A, .diatm x X t, .diatm _ _ s => .boxx x X (eqf A t s)
  | _, _, _ => .top

theorem HasTy.diatm_inv {Γ : Ctx} {x : Nat} {X : Ty} {t : Tm} {A : Ty} {S : ITy (.dia A)}
    (h : HasTy Γ (.diatm x X t) (.dia A) S) :
    ∃ (U : ITy A), Γ x = some (.dia X) ∧ HasTy (diaCtx Γ x X) t A U ∧
      S = .dia ⟨x, []⟩ (U.mapIdx (diaOut x)) := by
  cases h with
  | diatm hx ht => exact ⟨_, hx, ht, rfl⟩

/-- ⭐**Two `◇`-terms of the same elaborated type have the same witness.**  So an equation between
    different-witness `◇`-terms cannot even be written down. -/
theorem witness_eq {Γ : Ctx} {x y : Nat} {X Y : Ty} {t s : Tm} {A : Ty} {S : ITy (.dia A)}
    (ht : HasTy Γ (.diatm x X t) (.dia A) S) (hs : HasTy Γ (.diatm y Y s) (.dia A) S) :
    x = y := by
  obtain ⟨_, _, _, rfl⟩ := ht.diatm_inv
  obtain ⟨_, _, _, h⟩ := hs.diatm_inv
  simp only [ITy.dia.injEq, Idx.mk.injEq] at h
  exact h.1.1

/-- The inner data of two same-typed `◇`-terms coincide: same witness, same witness type, same
    inner type.  No casts are needed anywhere. -/
theorem dia_same_inner {Γ : Ctx} {x : Nat} {X : Ty} {b : Tm} {A : Ty} {S : ITy A}
    (hx : Γ x = some (.dia X)) (hb : HasTy Γ b (.dia A) (.dia ⟨x, []⟩ (S.mapIdx (diaOut x))))
    (hpb : b.PelimFree) :
    ∃ s, b = .diatm x X s ∧ HasTy (diaCtx Γ x X) s A S ∧ s.PelimFree := by
  obtain ⟨y, Y, s, U, rfl, hS, hy, hs, hspf⟩ := canon_dia hb hpb
  simp only [ITy.dia.injEq, Idx.mk.injEq, and_true] at hS
  obtain ⟨rfl, hSU⟩ := hS
  have hUS : U = S := (ITy.mapIdx_injective (diaOut_injective x) hSU).symm
  subst hUS
  rw [hx, Option.some.injEq, Ty.dia.injEq] at hy
  subst hy
  exact ⟨s, rfl, hs, hspf⟩

theorem box_same_inner {Γ : Ctx} {b : Tm} {A : Ty} {S : ITy A}
    (hb : HasTy Γ b (.box A) (.box (S.mapIdx boxOut))) (hpb : b.PelimFree) :
    ∃ s, b = .boxtm s ∧ HasTy (unboxCtx Γ) s A S ∧ s.PelimFree := by
  obtain ⟨s, U, rfl, hS, hs, hspf⟩ := canon_box hb hpb
  simp only [ITy.box.injEq] at hS
  have hUS : U = S := (ITy.mapIdx_injective boxOut_injective hS).symm
  subst hUS
  exact ⟨s, rfl, hs, hspf⟩

theorem pair_same_inner {Γ : Ctx} {b : Tm} {A B : Ty} {SA : ITy A} {SB : ITy B}
    (hb : HasTy Γ b (.prod A B) (.prod SA SB)) (hpb : b.PelimFree) :
    ∃ c d, b = .pair c d ∧ HasTy Γ c A SA ∧ HasTy Γ d B SB ∧ c.PelimFree ∧ d.PelimFree := by
  obtain ⟨c, d, SA', SB', rfl, hS, hc, hd, hcpf, hdpf⟩ := canon_prod hb hpb
  simp only [ITy.prod.injEq] at hS
  obtain ⟨rfl, rfl⟩ := hS
  exact ⟨c, d, rfl, hc, hd, hcpf, hdpf⟩

/-- The defined equality of two same-typed terms is a well-formed formula — the `◇` arm's `□_x`
    lands in the right context BECAUSE the witnesses agree. -/
theorem eqf_wf {Γ : Ctx} {a : Tm} {T : Ty} {S : ITy T} (ha : HasTy Γ a T S) :
    ∀ {b : Tm}, HasTy Γ b T S → a.PelimFree → b.PelimFree → WfWff Γ (eqf T a b) := by
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
      simp only [eqf]
      exact .box (ih hs hpa hspf)
  | diatm hx _ ih =>
      intro b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := dia_same_inner hx hb hpb
      simp only [eqf]
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
  | necx {x : Nat} {X : Ty} {p : Wff} : Pf p → Pf (.boxx x X p)
  | Kdist {p q : Wff} : Pf (.box (.imp p q)) → Pf (.imp (.box p) (.box q))
  | Kdistx {x : Nat} {X : Ty} {p q : Wff} :
      Pf (.boxx x X (.imp p q)) → Pf (.imp (.boxx x X p) (.boxx x X q))

theorem eqf_refl {Γ : Ctx} {a : Tm} {T : Ty} {S : ITy T} (ha : HasTy Γ a T S)
    (hpa : a.PelimFree) : Pf (eqf T a a) := by
  induction ha with
  | var => exact .primRefl _
  | unit => exact .topI
  | pair _ _ iha ihb => exact .conjI (iha hpa.1) (ihb hpa.2)
  | boxtm _ ih => simp only [eqf]; exact .nec (ih hpa)
  | diatm _ _ ih => simp only [eqf]; exact .necx (ih hpa)
  | pelim => exact hpa.elim

/-- ⭐**Symmetry, with no different-witness case.**  The `◇` case is `Kdistx ∘ necx` of the inner
    instance at the ONE witness both sides share. -/
theorem eqf_symm {Γ : Ctx} {a : Tm} {T : Ty} {S : ITy T} (ha : HasTy Γ a T S) :
    ∀ {b : Tm}, HasTy Γ b T S → a.PelimFree → b.PelimFree →
      Pf (.imp (eqf T a b) (eqf T b a)) := by
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
      simp only [eqf]
      exact .Kdist (.nec (ih hs hpa hspf))
  | diatm hx _ ih =>
      intro b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := dia_same_inner hx hb hpb
      simp only [eqf]
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
  | σ, .boxx x X φ =>
      match σ x with
      | .ren i => .boxx i X (Wff.psubst (Function.update (unboxSub σ) x (.ren i)) φ)
      | .tm (.diatm y Y u) (.dia A) (.dia _ U) =>
          .boxx y Y (Wff.psubst (Function.update (unboxSub σ) x (.tm u A (U.mapIdx Idx.strip))) φ)
      | .tm _ _ _ => .top

theorem eqf_psubst {Γ : Ctx} {a : Tm} {T : Ty} {S : ITy T} (ha : HasTy Γ a T S) :
    ∀ {b : Tm}, HasTy Γ b T S → a.PelimFree → b.PelimFree →
      ∀ {σ : Nat → Sub} {Δ : Ctx}, SubOk σ Γ Δ →
        (eqf T a b).psubst σ = eqf T (a.psubst σ) (b.psubst σ) := by
  induction ha with
  | var => intro _ _ _ _ _ _ _; rfl
  | unit => intro _ _ _ _ _ _ _; rfl
  | pair _ _ iha ihb =>
      intro b hb hpa hpb σ Δ hσ
      obtain ⟨c, d, rfl, hc, hd, hcpf, hdpf⟩ := pair_same_inner hb hpb
      simp only [eqf, Wff.psubst, Tm.psubst]
      rw [iha hc hpa.1 hcpf hσ, ihb hd hpa.2 hdpf hσ]
  | boxtm _ ih =>
      intro b hb hpa hpb σ Δ hσ
      obtain ⟨s, rfl, hs, hspf⟩ := box_same_inner hb hpb
      simp only [eqf, Wff.psubst, Tm.psubst]
      rw [ih hs hpa hspf hσ.unbox]
  | @diatm Γ x X t A S hx ht ih =>
      intro b hb hpa hpb σ Δ hσ
      obtain ⟨s, rfl, hs, hspf⟩ := dia_same_inner hx hb hpb
      have hok := hσ _ _ hx
      simp only [eqf, Wff.psubst, Tm.psubst]
      cases hsx : σ x with
      | ren i =>
          rw [hsx] at hok
          simp only [Sub.Ok] at hok
          simp only [eqf]
          rw [ih hs hpa hspf (hσ.diaRen hok)]
      | tm s' T' S' =>
          rw [hsx] at hok
          simp only [Sub.Ok] at hok
          obtain ⟨rfl, hs', hpf'⟩ := hok
          obtain ⟨y, Y, u, U, rfl, rfl, hy, hu, hupf⟩ := canon_dia hs' hpf'
          simp only [eqf]
          rw [ih hs hpa hspf (hσ.diaTm hy hu hupf)]
  | pelim => intro _ _ hpa _ _ _ _; exact hpa.elim

end DiaIdx

#print axioms DiaIdx.HasTy.psubst
#print axioms DiaIdx.witness_eq
#print axioms DiaIdx.eqf_wf
#print axioms DiaIdx.eqf_refl
#print axioms DiaIdx.eqf_symm
#print axioms DiaIdx.eqf_psubst
