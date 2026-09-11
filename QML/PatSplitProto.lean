import Mathlib.Tactic

/-!
# Prototype — the pattern split (unifying max-unpairing and normal forms)

Isolated.  Tests one reusable operation for eliminating pair variables:

* a **pattern** says which product nodes of a context entry to destructure;
* `unpair` moves a formula into the split context, and the smart `pelim` moves it back, pushing
  the elimination inward and keeping, at each stuck `□`, exactly the FORCED part;
* maximal unpairing and normal forms are the same operation with different patterns.

Design choices of the prototype:
* **Components are named by ACCESS PATHS** (a root variable plus `fst`/`snd` steps), as in the
  witness annotations — so splitting allocates nothing and is order-free by construction;
* a context entry is a **split tree** whose leaves are typed (present) or hidden;
* the v11 box discipline: `□` can be formed only when no present leaf is a BOXY product
  (a product containing a box), and inside `□` only box-typed leaves stay visible;
* references (`prim a b`) may point THROUGH an unsplit product (a leaf elimination);
* normal forms put a `split (forced Γ)` node above EVERY `□` (trivial when nothing is forced), so
  normality needs no decision about triviality.

Not modelled here: `◇` witness paths (the second source of forcing), terms other than references.
-/

namespace PatSplit

/-! ## Types, paths, patterns, split trees -/

inductive Ty where
  | base
  | prod (A B : Ty)
  | box (A : Ty)
  | dia (A : Ty)
deriving DecidableEq

/-- Contains a box somewhere in its product structure (v11's `isBox`). -/
def Ty.boxy : Ty → Bool
  | .base => false
  | .prod A B => A.boxy || B.boxy
  | .box _ => true
  | .dia _ => false

/-- A product that contains a box: such an entry blocks `□`. -/
def Ty.boxyProd : Ty → Bool
  | .prod A B => A.boxy || B.boxy
  | _ => false

inductive Step where
  | fst
  | snd
deriving DecidableEq

/-- A name: a root variable and an access path into its product structure. -/
structure Name where
  root : Nat
  path : List Step
deriving DecidableEq

def Name.ext (a : Name) (s : Step) : Name := ⟨a.root, a.path ++ [s]⟩

/-- A split pattern for one entry. -/
inductive Pat where
  | stop
  | split (a b : Pat)
deriving DecidableEq

def Pat.join : Pat → Pat → Pat
  | .stop, q => q
  | p, .stop => p
  | .split a b, .split c d => .split (a.join c) (b.join d)

/-- A context entry: a split tree whose leaves are present (typed) or hidden. -/
inductive Entry where
  | leaf (o : Option Ty)
  | node (a b : Entry)
deriving DecidableEq

namespace Entry

/-- Apply a pattern: split product leaves where the pattern says so. -/
def refine : Entry → Pat → Entry
  | e, .stop => e
  | e, .split pa pb =>
      match e with
      | .leaf (some (.prod A B)) =>
          .node (refine (.leaf (some A)) pa) (refine (.leaf (some B)) pb)
      | .node a b => .node (refine a pa) (refine b pb)
      | e => e

def forcedTy : Ty → Pat
  | .prod A B => if (Ty.prod A B).boxy then .split (forcedTy A) (forcedTy B) else .stop
  | _ => .stop

/-- The FORCED pattern: split boxy products, and nothing else. -/
def forced : Entry → Pat
  | .leaf (some T) => forcedTy T
  | .leaf none => .stop
  | .node a b => .split (forced a) (forced b)

def mkNode : Entry → Entry → Entry
  | .leaf none, .leaf none => .leaf none
  | a, b => .node a b

/-- Into a `□`: box-typed leaves unboxed, everything else hidden (hidden subtrees collapse). -/
def unbox : Entry → Entry
  | .leaf (some (.box X)) => .leaf (some X)
  | .leaf _ => .leaf none
  | .node a b => mkNode (unbox a) (unbox b)

def NoBoxProd : Entry → Prop
  | .leaf (some T) => T.boxyProd = false
  | .leaf none => True
  | .node a b => NoBoxProd a ∧ NoBoxProd b

def _root_.PatSplit.Ty.follow : Ty → List Step → Option Ty
  | T, [] => some T
  | .prod A _, .fst :: q => A.follow q
  | .prod _ B, .snd :: q => B.follow q
  | _, _ :: _ => none

/-- The type at a path: through split nodes, then through the leaf's own product type. -/
def lookup : Entry → List Step → Option Ty
  | .leaf o, q => o.bind (fun T => T.follow q)
  | .node a _, .fst :: q => a.lookup q
  | .node _ b, .snd :: q => b.lookup q
  | .node _ _, [] => none

end Entry

/-! ## Split-tree lemmas -/

namespace Entry

@[simp] theorem refine_stop (e : Entry) : e.refine .stop = e := rfl

theorem refine_nonprod_leaf {o : Option Ty} (ho : ∀ A B, o ≠ some (.prod A B)) (p : Pat) :
    (Entry.leaf o).refine p = .leaf o := by
  cases p with
  | stop => rfl
  | split pa pb =>
      rcases o with _ | ⟨_ | ⟨A, B⟩ | _ | _⟩
      · rfl
      · rfl
      · exact absurd rfl (ho A B)
      · rfl
      · rfl

theorem refine_join (e : Entry) (p q : Pat) : (e.refine p).refine q = e.refine (p.join q) := by
  induction p generalizing e q with
  | stop => rfl
  | split pa pb iha ihb =>
      cases q with
      | stop => rfl
      | split qa qb =>
          rcases e with ⟨_ | ⟨_ | ⟨A, B⟩ | _ | _⟩⟩ | ⟨a, b⟩
          · rfl
          · rfl
          · simp only [refine, Pat.join, iha, ihb]
          · rfl
          · rfl
          · simp only [refine, Pat.join, iha, ihb]

theorem noBoxProd_forcedTy (T : Ty) : ((Entry.leaf (some T)).refine (forcedTy T)).NoBoxProd := by
  induction T with
  | base => rfl
  | prod A B ihA ihB =>
      by_cases hb : (Ty.prod A B).boxy = true
      · simp only [forcedTy, hb, if_true, refine, NoBoxProd]
        exact ⟨ihA, ihB⟩
      · simp only [forcedTy, hb, Bool.false_eq_true, if_false, refine_stop, NoBoxProd]
        simpa [Ty.boxyProd, Ty.boxy] using hb
  | box A _ => rfl
  | dia A _ => rfl

theorem noBoxProd_forced (e : Entry) : (e.refine e.forced).NoBoxProd := by
  induction e with
  | leaf o =>
      rcases o with _ | T
      · trivial
      · exact noBoxProd_forcedTy T
  | node a b iha ihb => exact ⟨iha, ihb⟩

/-- A non-boxy leaf, however it is refined, is invisible inside `□`. -/
theorem unbox_refine_nonboxy (T : Ty) (hT : T.boxy = false) (p : Pat) :
    ((Entry.leaf (some T)).refine p).unbox = .leaf none := by
  induction p generalizing T with
  | stop =>
      cases T with
      | box _ => simp [Ty.boxy] at hT
      | _ => rfl
  | split pa pb iha ihb =>
      cases T with
      | prod A B =>
          simp only [Ty.boxy, Bool.or_eq_false_iff] at hT
          simp only [refine, unbox, iha A hT.1, ihb B hT.2, mkNode]
      | box _ => simp [Ty.boxy] at hT
      | _ => rfl

theorem unbox_refine_leaf (T : Ty) (p : Pat) (h : ((Entry.leaf (some T)).refine p).NoBoxProd) :
    ((Entry.leaf (some T)).refine p).unbox = ((Entry.leaf (some T)).refine (forcedTy T)).unbox := by
  induction T generalizing p with
  | base => rw [refine_nonprod_leaf (by simp) p]; rfl
  | box X _ => rw [refine_nonprod_leaf (by simp) p]; rfl
  | dia X _ => rw [refine_nonprod_leaf (by simp) p]; rfl
  | prod A B ihA ihB =>
      by_cases hb : (Ty.prod A B).boxy = true
      · cases p with
        | stop => simp [NoBoxProd, Ty.boxyProd, Ty.boxy] at h hb; simp_all
        | split pa pb =>
            simp only [forcedTy, hb, if_true, refine, unbox] at h ⊢
            rw [ihA pa h.1, ihB pb h.2]
      · have hb' : (Ty.prod A B).boxy = false := by simpa using hb
        simp only [forcedTy, hb, Bool.false_eq_true, if_false, refine_stop]
        rw [unbox_refine_nonboxy _ hb' p]
        cases hbx : (Ty.prod A B) <;> simp_all [unbox]

/-- ⭐**Extra refinement is invisible inside `□`**: any refinement that permits `□` has the same
    box shadow as the FORCED one. -/
theorem unbox_refine_forced (e : Entry) (p : Pat) (h : (e.refine p).NoBoxProd) :
    (e.refine p).unbox = (e.refine e.forced).unbox := by
  induction e generalizing p with
  | leaf o =>
      rcases o with _ | T
      · rw [refine_nonprod_leaf (by simp) p, refine_nonprod_leaf (by simp) _]
      · exact unbox_refine_leaf T p h
  | node a b iha ihb =>
      cases p with
      | stop =>
          have ha := iha .stop h.1
          have hb := ihb .stop h.2
          simp only [refine_stop] at ha hb
          simp only [refine_stop, forced, refine, unbox, ha, hb]
      | split pa pb =>
          simp only [refine, forced, unbox] at h ⊢
          rw [iha pa h.1, ihb pb h.2]

/-- Refinement does not change which names are base-typed. -/
theorem lookup_refine_base (e : Entry) (p : Pat) (q : List Step) :
    (e.refine p).lookup q = some .base ↔ e.lookup q = some .base := by
  induction p generalizing e q with
  | stop => rfl
  | split pa pb iha ihb =>
      rcases e with ⟨_ | ⟨_ | ⟨A, B⟩ | _ | _⟩⟩ | ⟨a, b⟩
      · rfl
      · rfl
      · rcases q with _ | ⟨_ | _, q⟩
        · simp [refine, lookup, Ty.follow]
        · simp only [refine, lookup]
          rw [iha]; simp [lookup, Ty.follow]
        · simp only [refine, lookup]
          rw [ihb]; simp [lookup, Ty.follow]
      · rfl
      · rfl
      · rcases q with _ | ⟨_ | _, q⟩
        · simp [refine, lookup]
        · simp only [refine, lookup]; exact iha a q
        · simp only [refine, lookup]; exact ihb b q

end Entry

/-! ## Contexts -/

abbrev Ctx := Nat → Entry

def refineCtx (Γ : Ctx) (P : Nat → Pat) : Ctx := fun r => (Γ r).refine (P r)
def unboxCtx (Γ : Ctx) : Ctx := fun r => (Γ r).unbox
def forcedCtx (Γ : Ctx) : Nat → Pat := fun r => (Γ r).forced
def joinCtx (P Q : Nat → Pat) : Nat → Pat := fun r => (P r).join (Q r)
def NoBoxProdCtx (Γ : Ctx) : Prop := ∀ r, (Γ r).NoBoxProd
def refType (Γ : Ctx) (a : Name) : Option Ty := (Γ a.root).lookup a.path

theorem refineCtx_join (Γ : Ctx) (P Q : Nat → Pat) :
    refineCtx (refineCtx Γ P) Q = refineCtx Γ (joinCtx P Q) :=
  funext fun r => Entry.refine_join _ _ _

theorem noBoxProdCtx_forced (Γ : Ctx) : NoBoxProdCtx (refineCtx Γ (forcedCtx Γ)) :=
  fun r => Entry.noBoxProd_forced (Γ r)

theorem unboxCtx_refine_forced {Γ : Ctx} {P : Nat → Pat} (h : NoBoxProdCtx (refineCtx Γ P)) :
    unboxCtx (refineCtx Γ P) = unboxCtx (refineCtx Γ (forcedCtx Γ)) :=
  funext fun r => Entry.unbox_refine_forced (Γ r) (P r) (h r)

/-- Refining further and then forcing again lands on the same box shadow as forcing at once. -/
theorem unboxCtx_refine_forced_refine (Γ : Ctx) (P : Nat → Pat) :
    unboxCtx (refineCtx (refineCtx Γ P) (forcedCtx (refineCtx Γ P)))
      = unboxCtx (refineCtx Γ (forcedCtx Γ)) := by
  rw [refineCtx_join]
  apply unboxCtx_refine_forced
  rw [← refineCtx_join]
  exact noBoxProdCtx_forced _

theorem refType_refine_base (Γ : Ctx) (P : Nat → Pat) (a : Name) :
    refType (refineCtx Γ P) a = some .base ↔ refType Γ a = some .base :=
  Entry.lookup_refine_base _ _ _

/-! ## Formulas, typing, normal forms -/

inductive Wff where
  | prim (a b : Name)
  | top
  | conj (φ ψ : Wff)
  | imp (φ ψ : Wff)
  | box (φ : Wff)
  | split (P : Nat → Pat) (φ : Wff)

inductive WfWff : Ctx → Wff → Prop where
  | prim {Γ : Ctx} {a b : Name} :
      refType Γ a = some .base → refType Γ b = some .base → WfWff Γ (.prim a b)
  | top {Γ : Ctx} : WfWff Γ .top
  | conj {Γ : Ctx} {φ ψ : Wff} : WfWff Γ φ → WfWff Γ ψ → WfWff Γ (.conj φ ψ)
  | imp {Γ : Ctx} {φ ψ : Wff} : WfWff Γ φ → WfWff Γ ψ → WfWff Γ (.imp φ ψ)
  | box {Γ : Ctx} {φ : Wff} : NoBoxProdCtx Γ → WfWff (unboxCtx Γ) φ → WfWff Γ (.box φ)
  | split {Γ : Ctx} {P : Nat → Pat} {φ : Wff} :
      WfWff (refineCtx Γ P) φ → WfWff Γ (.split P φ)

/-- Normal forms: eliminations only directly above a `□`, with EXACTLY the forced pattern. -/
def Normal : Ctx → Wff → Prop
  | _, .prim _ _ => True
  | _, .top => True
  | Γ, .conj φ ψ => Normal Γ φ ∧ Normal Γ ψ
  | Γ, .imp φ ψ => Normal Γ φ ∧ Normal Γ ψ
  | _, .box _ => False
  | Γ, .split P (.box χ) => P = forcedCtx Γ ∧ Normal (unboxCtx (refineCtx Γ P)) χ
  | _, .split _ _ => False

/-! ## The two directions -/

/-- **Smart re-pairing**: from the context refined by `P` back to `Γ`.  Pushes inward; nested
    splits merge; at a `□` the pattern is REPLACED by the forced one. -/
def pelim (Γ : Ctx) : (Nat → Pat) → Wff → Wff
  | _, .prim a b => .prim a b
  | _, .top => .top
  | P, .conj φ ψ => .conj (pelim Γ P φ) (pelim Γ P ψ)
  | P, .imp φ ψ => .imp (pelim Γ P φ) (pelim Γ P ψ)
  | _, .box χ => .split (forcedCtx Γ) (.box χ)
  | P, .split Q φ => pelim Γ (joinCtx P Q) φ

/-- **Unpairing**: from `Γ` into the context refined by `P`. -/
def unpair (Γ : Ctx) (P : Nat → Pat) : Wff → Wff
  | .prim a b => .prim a b
  | .top => .top
  | .conj φ ψ => .conj (unpair Γ P φ) (unpair Γ P ψ)
  | .imp φ ψ => .imp (unpair Γ P φ) (unpair Γ P ψ)
  | .box χ => .box χ
  | .split _ φ => .split (forcedCtx (refineCtx Γ P)) φ

/-! ## Theorems -/

/-- ⭐**The forced restriction typechecks**: re-pairing a well-typed formula gives a well-typed
    formula. -/
theorem wf_pelim {Δ : Ctx} {φ : Wff} (h : WfWff Δ φ) :
    ∀ (Γ : Ctx) (P : Nat → Pat), Δ = refineCtx Γ P → WfWff Γ (pelim Γ P φ) := by
  induction h with
  | prim ha hb =>
      intro Γ P hΔ; subst hΔ
      exact .prim ((refType_refine_base _ _ _).mp ha) ((refType_refine_base _ _ _).mp hb)
  | top => intro _ _ _; exact .top
  | conj _ _ ih₁ ih₂ => intro Γ P hΔ; exact .conj (ih₁ Γ P hΔ) (ih₂ Γ P hΔ)
  | imp _ _ ih₁ ih₂ => intro Γ P hΔ; exact .imp (ih₁ Γ P hΔ) (ih₂ Γ P hΔ)
  | @box Δ χ hnb hχ _ =>
      intro Γ P hΔ; subst hΔ
      refine .split (.box (noBoxProdCtx_forced Γ) ?_)
      rw [← unboxCtx_refine_forced hnb]
      exact hχ
  | @split Δ Q ψ _ ih =>
      intro Γ P hΔ; subst hΔ
      exact ih Γ (joinCtx P Q) (refineCtx_join Γ P Q)

theorem normal_pelim (Γ : Ctx) : ∀ (φ : Wff) (P : Nat → Pat),
    Normal (refineCtx Γ P) φ → Normal Γ (pelim Γ P φ)
  | .prim _ _, _, _ => trivial
  | .top, _, _ => trivial
  | .conj φ ψ, P, h => ⟨normal_pelim Γ φ P h.1, normal_pelim Γ ψ P h.2⟩
  | .imp φ ψ, P, h => ⟨normal_pelim Γ φ P h.1, normal_pelim Γ ψ P h.2⟩
  | .box _, _, h => h.elim
  | .split Q (.box χ), P, h => by
      obtain ⟨rfl, hχ⟩ := h
      refine ⟨rfl, ?_⟩
      rw [← unboxCtx_refine_forced_refine Γ P]
      exact hχ
  | .split _ .top, _, h => h.elim
  | .split _ (.prim _ _), _, h => h.elim
  | .split _ (.conj _ _), _, h => h.elim
  | .split _ (.imp _ _), _, h => h.elim
  | .split _ (.split _ _), _, h => h.elim

theorem normal_unpair (Γ : Ctx) (P : Nat → Pat) : ∀ ψ : Wff,
    Normal Γ ψ → Normal (refineCtx Γ P) (unpair Γ P ψ)
  | .prim _ _, _ => trivial
  | .top, _ => trivial
  | .conj φ ψ, h => ⟨normal_unpair Γ P φ h.1, normal_unpair Γ P ψ h.2⟩
  | .imp φ ψ, h => ⟨normal_unpair Γ P φ h.1, normal_unpair Γ P ψ h.2⟩
  | .box _, h => h.elim
  | .split Q (.box χ), h => by
      obtain ⟨rfl, hχ⟩ := h
      refine ⟨rfl, ?_⟩
      rw [unboxCtx_refine_forced_refine Γ P]
      exact hχ
  | .split _ .top, h => h.elim
  | .split _ (.prim _ _), h => h.elim
  | .split _ (.conj _ _), h => h.elim
  | .split _ (.imp _ _), h => h.elim
  | .split _ (.split _ _), h => h.elim

/-- ⭐**β**: unpairing undoes re-pairing, syntactically. -/
theorem unpair_pelim (Γ : Ctx) : ∀ (φ : Wff) (P : Nat → Pat),
    Normal (refineCtx Γ P) φ → unpair Γ P (pelim Γ P φ) = φ
  | .prim _ _, _, _ => rfl
  | .top, _, _ => rfl
  | .conj φ ψ, P, h => by
      simp only [pelim, unpair, unpair_pelim Γ φ P h.1, unpair_pelim Γ ψ P h.2]
  | .imp φ ψ, P, h => by
      simp only [pelim, unpair, unpair_pelim Γ φ P h.1, unpair_pelim Γ ψ P h.2]
  | .box _, _, h => h.elim
  | .split Q (.box χ), P, h => by
      obtain ⟨rfl, -⟩ := h
      rfl
  | .split _ .top, _, h => h.elim
  | .split _ (.prim _ _), _, h => h.elim
  | .split _ (.conj _ _), _, h => h.elim
  | .split _ (.imp _ _), _, h => h.elim
  | .split _ (.split _ _), _, h => h.elim

/-- ⭐**η**: re-pairing undoes unpairing on normal forms, syntactically — the membership-transfer
    fact the canonical model's unpaired copies need. -/
theorem pelim_unpair (Γ : Ctx) (P : Nat → Pat) : ∀ ψ : Wff,
    Normal Γ ψ → pelim Γ P (unpair Γ P ψ) = ψ
  | .prim _ _, _ => rfl
  | .top, _ => rfl
  | .conj φ ψ, h => by
      simp only [unpair, pelim, pelim_unpair Γ P φ h.1, pelim_unpair Γ P ψ h.2]
  | .imp φ ψ, h => by
      simp only [unpair, pelim, pelim_unpair Γ P φ h.1, pelim_unpair Γ P ψ h.2]
  | .box _, h => h.elim
  | .split Q (.box χ), h => by
      obtain ⟨rfl, -⟩ := h
      rfl
  | .split _ .top, h => h.elim
  | .split _ (.prim _ _), h => h.elim
  | .split _ (.conj _ _), h => h.elim
  | .split _ (.imp _ _), h => h.elim
  | .split _ (.split _ _), h => h.elim

/-- ⭐**The pattern used to unpair does not matter for re-pairing** — maximal unpairing and forced
    unpairing re-pair to the same normal form. -/
theorem pelim_pat_irrel (Γ : Ctx) : ∀ (φ : Wff) (P P' : Nat → Pat), pelim Γ P φ = pelim Γ P' φ
  | .prim _ _, _, _ => rfl
  | .top, _, _ => rfl
  | .conj φ ψ, P, P' => by
      simp only [pelim, pelim_pat_irrel Γ φ P P', pelim_pat_irrel Γ ψ P P']
  | .imp φ ψ, P, P' => by
      simp only [pelim, pelim_pat_irrel Γ φ P P', pelim_pat_irrel Γ ψ P P']
  | .box _, _, _ => rfl
  | .split Q φ, P, P' => by
      simp only [pelim]
      exact pelim_pat_irrel Γ φ _ _

/-! ## The payoff test: equality built on the forced split commutes with every bijection -/

def eqRec (Γ : Ctx) : Ty → Name → Name → Wff
  | .base, a, b => .prim a b
  | .prod A B, a, b =>
      .conj (eqRec Γ A (a.ext .fst) (b.ext .fst)) (eqRec Γ B (a.ext .snd) (b.ext .snd))
  | .box A, a, b =>
      .split (forcedCtx Γ) (.box (eqRec (unboxCtx (refineCtx Γ (forcedCtx Γ))) A a b))
  | .dia _, _, _ => .top

theorem normal_eqRec : ∀ (T : Ty) (Γ : Ctx) (a b : Name), Normal Γ (eqRec Γ T a b)
  | .base, _, _, _ => trivial
  | .prod A B, Γ, a, b => ⟨normal_eqRec A Γ _ _, normal_eqRec B Γ _ _⟩
  | .box A, Γ, a, b => ⟨rfl, normal_eqRec A _ a b⟩
  | .dia _, _, _, _ => trivial

def Name.rename (ρ : Equiv.Perm ℕ) (a : Name) : Name := ⟨ρ a.root, a.path⟩
def renameCtx (ρ : Equiv.Perm ℕ) (Γ : Ctx) : Ctx := fun r => Γ (ρ.symm r)
def renamePat (ρ : Equiv.Perm ℕ) (P : Nat → Pat) : Nat → Pat := fun r => P (ρ.symm r)

def Wff.rename (ρ : Equiv.Perm ℕ) : Wff → Wff
  | .prim a b => .prim (a.rename ρ) (b.rename ρ)
  | .top => .top
  | .conj φ ψ => .conj (φ.rename ρ) (ψ.rename ρ)
  | .imp φ ψ => .imp (φ.rename ρ) (ψ.rename ρ)
  | .box φ => .box (φ.rename ρ)
  | .split P φ => .split (renamePat ρ P) (φ.rename ρ)

/-- ⭐**Order-free**: renaming the root variables by ANY bijection commutes with the defined
    equality — the property v11's sequential `firstPairVar` peel breaks. -/
theorem rename_eqRec (ρ : Equiv.Perm ℕ) : ∀ (T : Ty) (Γ : Ctx) (a b : Name),
    (eqRec Γ T a b).rename ρ = eqRec (renameCtx ρ Γ) T (a.rename ρ) (b.rename ρ)
  | .base, _, _, _ => rfl
  | .prod A B, Γ, a, b => by
      simp only [eqRec, Wff.rename, rename_eqRec ρ A, rename_eqRec ρ B]
      rfl
  | .box A, Γ, a, b => by
      simp only [eqRec, Wff.rename, rename_eqRec ρ A]
      rfl
  | .dia _, _, _, _ => rfl

end PatSplit

#print axioms PatSplit.wf_pelim
#print axioms PatSplit.unpair_pelim
#print axioms PatSplit.pelim_unpair
#print axioms PatSplit.pelim_pat_irrel
#print axioms PatSplit.rename_eqRec
