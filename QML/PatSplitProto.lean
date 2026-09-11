import Mathlib.Tactic

/-!
# Prototype — the pattern split (unifying max-unpairing and normal forms)

Isolated.  Tests one reusable operation for eliminating pair variables:

* a **pattern** says which product nodes of a context entry to destructure;
* `unpair` moves a formula into the split context, and the smart `pelim` moves it back, pushing
  the elimination inward and keeping, at each stuck modal node, exactly the FORCED part;
* maximal unpairing and normal forms are the same operation with different patterns.

Design choices of the prototype:
* **Components are named by ACCESS PATHS** (a root variable plus `fst`/`snd` steps), as in the
  witness annotations — so splitting allocates nothing and is order-free by construction;
* a context entry is a **split tree** whose leaves are typed (present) or hidden;
* the v11 box discipline: a modal node can be formed only when no present leaf is a BOXY product
  (a product containing a box), and inside it only box-typed leaves stay visible;
* the two sources of forcing: boxy products (every `□` and `□_x`), and the witness path of `□_x`
  (the witness must be an ENTRY, not a component of an unsplit product);
* references (`prim a b`) may point THROUGH an unsplit product (a leaf elimination);
* normal forms put a `split (forced …)` node above EVERY modal node (trivial when nothing is
  forced), so normality needs no decision about triviality.

Not modelled here: terms other than references.
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

/-- A product that contains a box: such an entry blocks modal nodes. -/
def Ty.boxyProd : Ty → Bool
  | .prod A B => A.boxy || B.boxy
  | _ => false

theorem Ty.boxyProd_of_boxy {T : Ty} (h : T.boxy = false) : T.boxyProd = false := by
  cases T <;> simp_all [Ty.boxy, Ty.boxyProd]

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

@[simp] theorem Pat.join_stop (p : Pat) : p.join .stop = p := by cases p <;> rfl

/-- The pattern that splits exactly along a path. -/
def Pat.path : List Step → Pat
  | [] => .stop
  | .fst :: q => .split (Pat.path q) .stop
  | .snd :: q => .split .stop (Pat.path q)

/-- A context entry: a split tree whose leaves are present (typed) or hidden. -/
inductive Entry where
  | leaf (o : Option Ty)
  | node (a b : Entry)
deriving DecidableEq

def Ty.follow : Ty → List Step → Option Ty
  | T, [] => some T
  | .prod A _, .fst :: q => A.follow q
  | .prod _ B, .snd :: q => B.follow q
  | _, _ :: _ => none

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

/-- The FORCED box pattern: split boxy products, and nothing else. -/
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

/-- Into a `◇_x` whose witness leaf is at path `q`: the box shadow, with the witness revealed at its
    realization type.  Along the witness path the tree stays OPEN (no collapse). -/
def unboxExcept : Entry → List Step → Ty → Entry
  | .leaf _, [], X => .leaf (some X)
  | .node a b, .fst :: q, X => .node (a.unboxExcept q X) b.unbox
  | .node a b, .snd :: q, X => .node a.unbox (b.unboxExcept q X)
  | e, _, _ => e.unbox

def NoBoxProd : Entry → Prop
  | .leaf (some T) => T.boxyProd = false
  | .leaf none => True
  | .node a b => NoBoxProd a ∧ NoBoxProd b

/-- The type at a path: through split nodes, then through the leaf's own product type. -/
def lookup : Entry → List Step → Option Ty
  | .leaf o, q => o.bind (fun T => T.follow q)
  | .node a _, .fst :: q => a.lookup q
  | .node _ b, .snd :: q => b.lookup q
  | .node _ _, [] => none

/-- The entry EXACTLY at a path (no looking inside an unsplit product). -/
def leafAt : Entry → List Step → Option Ty
  | .leaf o, [] => o
  | .leaf _, _ :: _ => none
  | .node a _, .fst :: q => a.leafAt q
  | .node _ b, .snd :: q => b.leafAt q
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

theorem forcedTy_of_not_boxy {T : Ty} (h : T.boxy = false) : forcedTy T = .stop := by
  cases T with
  | prod A B => simp only [forcedTy]; rw [if_neg (by simp_all [Ty.boxy])]
  | _ => rfl

theorem noBoxProd_refine (e : Entry) (p : Pat) (h : e.NoBoxProd) : (e.refine p).NoBoxProd := by
  induction p generalizing e with
  | stop => exact h
  | split pa pb iha ihb =>
      rcases e with ⟨_ | ⟨_ | ⟨A, B⟩ | _ | _⟩⟩ | ⟨a, b⟩
      · exact h
      · exact h
      · simp only [NoBoxProd, Ty.boxyProd, Bool.or_eq_false_iff] at h
        exact ⟨iha _ (Ty.boxyProd_of_boxy h.1), ihb _ (Ty.boxyProd_of_boxy h.2)⟩
      · exact h
      · exact h
      · exact ⟨iha a h.1, ihb b h.2⟩

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

/-- Refinement does not change which names have a non-product type. -/
theorem lookup_refine_nonprod (e : Entry) (p : Pat) (q : List Step) {T : Ty}
    (hT : ∀ A B, T ≠ .prod A B) : (e.refine p).lookup q = some T ↔ e.lookup q = some T := by
  induction p generalizing e q with
  | stop => rfl
  | split pa pb iha ihb =>
      rcases e with ⟨_ | ⟨_ | ⟨A, B⟩ | _ | _⟩⟩ | ⟨a, b⟩
      · rfl
      · rfl
      · rcases q with _ | ⟨_ | _, q⟩
        · change none = some T ↔ some (Ty.prod A B) = some T
          exact ⟨(fun h => by cases h), fun h => absurd (Option.some.inj h).symm (hT A B)⟩
        · exact iha (.leaf (some A)) q
        · exact ihb (.leaf (some B)) q
      · rfl
      · rfl
      · rcases q with _ | ⟨_ | _, q⟩
        · rfl
        · exact iha a q
        · exact ihb b q

theorem lookup_of_leafAt (q : List Step) : ∀ (e : Entry) {T : Ty},
    e.leafAt q = some T → e.lookup q = some T := by
  induction q with
  | nil =>
      intro e T h
      rcases e with ⟨_ | T'⟩ | ⟨a, b⟩
      · simp [leafAt] at h
      · simpa [leafAt, lookup, Ty.follow] using h
      · simp [leafAt] at h
  | cons s q ih =>
      intro e T h
      rcases e with ⟨o⟩ | ⟨a, b⟩
      · simp [leafAt] at h
      · cases s
        · exact ih a h
        · exact ih b h

/-- The witness-path forcing makes the witness an ENTRY. -/
theorem leafAt_refine_forcedPath (q : List Step) : ∀ (e : Entry) (X : Ty),
    e.lookup q = some (.dia X) → (e.refine (e.forced.join (Pat.path q))).leafAt q = some (.dia X) := by
  induction q with
  | nil =>
      intro e X h
      rcases e with ⟨_ | ⟨_ | ⟨A, B⟩ | _ | Y⟩⟩ | ⟨a, b⟩
      · simp [lookup] at h
      · simp [lookup, Ty.follow] at h
      · simp [lookup, Ty.follow] at h
      · simp [lookup, Ty.follow] at h
      · simp only [lookup, Option.bind, Ty.follow, Option.some.injEq, Ty.dia.injEq] at h
        subst h
        rfl
      · simp [lookup] at h
  | cons s q ih =>
      intro e X h
      rcases e with ⟨_ | ⟨_ | ⟨A, B⟩ | _ | Y⟩⟩ | ⟨a, b⟩
      · simp [lookup] at h
      · cases s <;> simp [lookup, Ty.follow] at h
      · cases s
        · have hA : (Entry.leaf (some A)).lookup q = some (.dia X) := h
          by_cases hb : (Ty.prod A B).boxy = true
          · simp only [forced, forcedTy, hb, if_true, Pat.path, Pat.join, Pat.join_stop, refine,
              leafAt]
            exact ih _ X hA
          · have hA' : A.boxy = false := by
              simp only [Ty.boxy, Bool.or_eq_true, not_or, Bool.not_eq_true] at hb; exact hb.1
            simp only [forced, forcedTy, hb, Bool.false_eq_true, if_false, Pat.path, Pat.join,
              refine, leafAt]
            have := ih _ X hA
            simpa only [forced, forcedTy_of_not_boxy hA', Pat.join] using this
        · have hB : (Entry.leaf (some B)).lookup q = some (.dia X) := h
          by_cases hb : (Ty.prod A B).boxy = true
          · simp only [forced, forcedTy, hb, if_true, Pat.path, Pat.join, refine, leafAt]
            exact ih _ X hB
          · have hB' : B.boxy = false := by
              simp only [Ty.boxy, Bool.or_eq_true, not_or, Bool.not_eq_true] at hb; exact hb.2
            simp only [forced, forcedTy, hb, Bool.false_eq_true, if_false, Pat.path, Pat.join,
              refine, leafAt]
            have := ih _ X hB
            simpa only [forced, forcedTy_of_not_boxy hB', Pat.join] using this
      · cases s <;> simp [lookup, Ty.follow] at h
      · cases s <;> simp [lookup, Ty.follow] at h
      · cases s
        · simp only [forced, Pat.path, Pat.join, Pat.join_stop, refine, leafAt]
          exact ih a X h
        · simp only [forced, Pat.path, Pat.join, refine, leafAt]
          exact ih b X h

/-- ⭐**Extra refinement is invisible inside `◇_x` too**: with the witness an entry, any
    refinement permitting the modal node has the same inner context as the forced one — and the
    witness path stays open on both sides. -/
theorem unboxExcept_refine_forced (q : List Step) : ∀ (e : Entry) (p : Pat) (X : Ty),
    (e.refine p).NoBoxProd → (e.refine p).leafAt q = some (.dia X) →
    (e.refine p).unboxExcept q X = (e.refine (e.forced.join (Pat.path q))).unboxExcept q X := by
  induction q with
  | nil =>
      intro e p X _ hl
      rcases e with ⟨_ | ⟨_ | ⟨A, B⟩ | _ | Y⟩⟩ | ⟨a, b⟩
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · cases p with
        | stop => simp [leafAt] at hl
        | split pa pb => simp [refine, leafAt] at hl
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · rw [refine_nonprod_leaf (by simp) p, refine_nonprod_leaf (by simp) _]
      · cases p with
        | stop => simp [leafAt] at hl
        | split pa pb => simp [refine, leafAt] at hl
  | cons s q ih =>
      intro e p X h hl
      rcases e with ⟨_ | ⟨_ | ⟨A, B⟩ | _ | Y⟩⟩ | ⟨a, b⟩
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · cases p with
        | stop => simp [leafAt] at hl
        | split pa pb =>
            have hA : A.boxy = false ∨ (Ty.prod A B).boxy = true := by
              cases hAb : A.boxy <;> simp [Ty.boxy, hAb]
            by_cases hb : (Ty.prod A B).boxy = true
            · cases s
              · simp only [refine, NoBoxProd, leafAt] at h hl
                simp only [forced, forcedTy, hb, if_true, Pat.path, Pat.join, Pat.join_stop,
                  refine, unboxExcept]
                exact congrArg₂ Entry.node (ih _ pa X h.1 hl) (unbox_refine_leaf B pb h.2)
              · simp only [refine, NoBoxProd, leafAt] at h hl
                simp only [forced, forcedTy, hb, if_true, Pat.path, Pat.join, Pat.join_stop,
                  refine, unboxExcept]
                exact congrArg₂ Entry.node (unbox_refine_leaf A pa h.1) (ih _ pb X h.2 hl)
            · have hb' : (Ty.prod A B).boxy = false := by simpa using hb
              simp only [Ty.boxy, Bool.or_eq_false_iff] at hb'
              cases s
              · simp only [refine, NoBoxProd, leafAt] at h hl
                simp only [forced, forcedTy, hb, Bool.false_eq_true, if_false, Pat.path,
                  Pat.join, refine, refine_stop, unboxExcept]
                have hih := ih _ pa X h.1 hl
                simp only [forced, forcedTy_of_not_boxy hb'.1, Pat.join] at hih
                exact congrArg₂ Entry.node hih
                  ((unbox_refine_nonboxy B hb'.2 pb).trans (unbox_refine_nonboxy B hb'.2 .stop).symm)
              · simp only [refine, NoBoxProd, leafAt] at h hl
                simp only [forced, forcedTy, hb, Bool.false_eq_true, if_false, Pat.path,
                  Pat.join, refine, refine_stop, unboxExcept]
                have hih := ih _ pb X h.2 hl
                simp only [forced, forcedTy_of_not_boxy hb'.2, Pat.join] at hih
                exact congrArg₂ Entry.node
                  ((unbox_refine_nonboxy A hb'.1 pa).trans (unbox_refine_nonboxy A hb'.1 .stop).symm)
                  hih
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · cases p with
        | stop =>
            cases s
            · simp only [refine_stop, NoBoxProd, leafAt] at h hl
              simp only [forced, Pat.path, Pat.join, Pat.join_stop, refine, refine_stop,
                unboxExcept]
              exact congrArg₂ Entry.node (ih a .stop X h.1 hl) (unbox_refine_forced b .stop h.2)
            · simp only [refine_stop, NoBoxProd, leafAt] at h hl
              simp only [forced, Pat.path, Pat.join, Pat.join_stop, refine, refine_stop,
                unboxExcept]
              exact congrArg₂ Entry.node (unbox_refine_forced a .stop h.1) (ih b .stop X h.2 hl)
        | split pa pb =>
            cases s
            · simp only [refine, NoBoxProd, leafAt] at h hl
              simp only [forced, Pat.path, Pat.join, Pat.join_stop, refine, unboxExcept]
              exact congrArg₂ Entry.node (ih a pa X h.1 hl) (unbox_refine_forced b pb h.2)
            · simp only [refine, NoBoxProd, leafAt] at h hl
              simp only [forced, Pat.path, Pat.join, Pat.join_stop, refine, unboxExcept]
              exact congrArg₂ Entry.node (unbox_refine_forced a pa h.1) (ih b pb X h.2 hl)

end Entry

/-! ## Contexts -/

abbrev Ctx := Nat → Entry

def refineCtx (Γ : Ctx) (P : Nat → Pat) : Ctx := fun r => (Γ r).refine (P r)
def unboxCtx (Γ : Ctx) : Ctx := fun r => (Γ r).unbox
def forcedCtx (Γ : Ctx) : Nat → Pat := fun r => (Γ r).forced
def joinCtx (P Q : Nat → Pat) : Nat → Pat := fun r => (P r).join (Q r)
def NoBoxProdCtx (Γ : Ctx) : Prop := ∀ r, (Γ r).NoBoxProd
def refType (Γ : Ctx) (a : Name) : Option Ty := (Γ a.root).lookup a.path
def entryType (Γ : Ctx) (a : Name) : Option Ty := (Γ a.root).leafAt a.path

/-- The witness path as a context pattern. -/
def pathCtx (x : Name) : Nat → Pat := fun r => if r = x.root then Pat.path x.path else .stop

/-- The forced pattern for `□_x`: boxy products, plus the witness path. -/
def forcedX (Γ : Ctx) (x : Name) : Nat → Pat := joinCtx (forcedCtx Γ) (pathCtx x)

/-- Into `◇_x`: box shadow everywhere, witness revealed at its realization type. -/
def diaCtx (Γ : Ctx) (x : Name) (X : Ty) : Ctx :=
  fun r => if r = x.root then (Γ r).unboxExcept x.path X else (Γ r).unbox

theorem refineCtx_join (Γ : Ctx) (P Q : Nat → Pat) :
    refineCtx (refineCtx Γ P) Q = refineCtx Γ (joinCtx P Q) :=
  funext fun r => Entry.refine_join _ _ _

theorem noBoxProdCtx_forced (Γ : Ctx) : NoBoxProdCtx (refineCtx Γ (forcedCtx Γ)) :=
  fun r => Entry.noBoxProd_forced (Γ r)

theorem noBoxProdCtx_forcedX (Γ : Ctx) (x : Name) : NoBoxProdCtx (refineCtx Γ (forcedX Γ x)) := by
  intro r
  show ((Γ r).refine ((Γ r).forced.join (pathCtx x r))).NoBoxProd
  rw [← Entry.refine_join]
  exact Entry.noBoxProd_refine _ _ (Entry.noBoxProd_forced (Γ r))

theorem unboxCtx_refine_forced {Γ : Ctx} {P : Nat → Pat} (h : NoBoxProdCtx (refineCtx Γ P)) :
    unboxCtx (refineCtx Γ P) = unboxCtx (refineCtx Γ (forcedCtx Γ)) :=
  funext fun r => Entry.unbox_refine_forced (Γ r) (P r) (h r)

theorem unboxCtx_refine_forced_refine (Γ : Ctx) (P : Nat → Pat) :
    unboxCtx (refineCtx (refineCtx Γ P) (forcedCtx (refineCtx Γ P)))
      = unboxCtx (refineCtx Γ (forcedCtx Γ)) := by
  rw [refineCtx_join]
  apply unboxCtx_refine_forced
  rw [← refineCtx_join]
  exact noBoxProdCtx_forced _

theorem refType_refine_nonprod (Γ : Ctx) (P : Nat → Pat) (a : Name) {T : Ty}
    (hT : ∀ A B, T ≠ .prod A B) : refType (refineCtx Γ P) a = some T ↔ refType Γ a = some T :=
  Entry.lookup_refine_nonprod _ _ _ hT

theorem entryType_forcedX {Γ : Ctx} {x : Name} {X : Ty} (h : refType Γ x = some (.dia X)) :
    entryType (refineCtx Γ (forcedX Γ x)) x = some (.dia X) := by
  show ((Γ x.root).refine ((Γ x.root).forced.join (pathCtx x x.root))).leafAt x.path = _
  simp only [pathCtx, if_true]
  exact Entry.leafAt_refine_forcedPath _ _ _ h

theorem diaCtx_refine_forced {Γ : Ctx} {P : Nat → Pat} {x : Name} {X : Ty}
    (h : NoBoxProdCtx (refineCtx Γ P)) (hx : entryType (refineCtx Γ P) x = some (.dia X)) :
    diaCtx (refineCtx Γ P) x X = diaCtx (refineCtx Γ (forcedX Γ x)) x X := by
  funext r
  simp only [diaCtx, refineCtx, forcedX, joinCtx, forcedCtx, pathCtx]
  by_cases hr : r = x.root
  · subst hr
    simp only [if_true]
    exact Entry.unboxExcept_refine_forced _ _ _ _ (h _) hx
  · simp only [hr, if_false, Pat.join_stop]
    exact Entry.unbox_refine_forced _ _ (h r)

theorem diaCtx_refine_forcedX_refine (Γ : Ctx) (P : Nat → Pat) {x : Name} {X : Ty}
    (hx : refType Γ x = some (.dia X)) :
    diaCtx (refineCtx (refineCtx Γ P) (forcedX (refineCtx Γ P) x)) x X
      = diaCtx (refineCtx Γ (forcedX Γ x)) x X := by
  have hx' : refType (refineCtx Γ P) x = some (.dia X) :=
    (refType_refine_nonprod Γ P x (by intro A B h; cases h)).mpr hx
  rw [refineCtx_join]
  apply diaCtx_refine_forced
  · rw [← refineCtx_join]; exact noBoxProdCtx_forcedX _ _
  · rw [← refineCtx_join]; exact entryType_forcedX hx'

/-! ## Formulas, typing, normal forms -/

inductive Wff where
  | prim (a b : Name)
  | top
  | conj (φ ψ : Wff)
  | imp (φ ψ : Wff)
  | box (φ : Wff)
  | boxx (x : Name) (X : Ty) (φ : Wff)
  | split (P : Nat → Pat) (φ : Wff)

inductive WfWff : Ctx → Wff → Prop where
  | prim {Γ : Ctx} {a b : Name} :
      refType Γ a = some .base → refType Γ b = some .base → WfWff Γ (.prim a b)
  | top {Γ : Ctx} : WfWff Γ .top
  | conj {Γ : Ctx} {φ ψ : Wff} : WfWff Γ φ → WfWff Γ ψ → WfWff Γ (.conj φ ψ)
  | imp {Γ : Ctx} {φ ψ : Wff} : WfWff Γ φ → WfWff Γ ψ → WfWff Γ (.imp φ ψ)
  | box {Γ : Ctx} {φ : Wff} : NoBoxProdCtx Γ → WfWff (unboxCtx Γ) φ → WfWff Γ (.box φ)
  | boxx {Γ : Ctx} {x : Name} {X : Ty} {φ : Wff} :
      entryType Γ x = some (.dia X) → NoBoxProdCtx Γ → WfWff (diaCtx Γ x X) φ →
      WfWff Γ (.boxx x X φ)
  | split {Γ : Ctx} {P : Nat → Pat} {φ : Wff} :
      WfWff (refineCtx Γ P) φ → WfWff Γ (.split P φ)

/-- Normal forms: eliminations only directly above a modal node, with EXACTLY the forced pattern. -/
def Normal : Ctx → Wff → Prop
  | _, .prim _ _ => True
  | _, .top => True
  | Γ, .conj φ ψ => Normal Γ φ ∧ Normal Γ ψ
  | Γ, .imp φ ψ => Normal Γ φ ∧ Normal Γ ψ
  | _, .box _ => False
  | _, .boxx _ _ _ => False
  | Γ, .split P (.box χ) => P = forcedCtx Γ ∧ Normal (unboxCtx (refineCtx Γ P)) χ
  | Γ, .split P (.boxx x X χ) =>
      refType Γ x = some (.dia X) ∧ P = forcedX Γ x ∧ Normal (diaCtx (refineCtx Γ P) x X) χ
  | _, .split _ _ => False

/-! ## The two directions -/

/-- **Smart re-pairing**: from the context refined by `P` back to `Γ`.  Pushes inward; nested
    splits merge; at a modal node the pattern is REPLACED by the forced one. -/
def pelim (Γ : Ctx) : (Nat → Pat) → Wff → Wff
  | _, .prim a b => .prim a b
  | _, .top => .top
  | P, .conj φ ψ => .conj (pelim Γ P φ) (pelim Γ P ψ)
  | P, .imp φ ψ => .imp (pelim Γ P φ) (pelim Γ P ψ)
  | _, .box χ => .split (forcedCtx Γ) (.box χ)
  | _, .boxx x X χ => .split (forcedX Γ x) (.boxx x X χ)
  | P, .split Q φ => pelim Γ (joinCtx P Q) φ

/-- **Unpairing**: from `Γ` into the context refined by `P`. -/
def unpair (Γ : Ctx) (P : Nat → Pat) : Wff → Wff
  | .prim a b => .prim a b
  | .top => .top
  | .conj φ ψ => .conj (unpair Γ P φ) (unpair Γ P ψ)
  | .imp φ ψ => .imp (unpair Γ P φ) (unpair Γ P ψ)
  | .box χ => .box χ
  | .boxx x X χ => .boxx x X χ
  | .split _ (.boxx x X φ) => .split (forcedX (refineCtx Γ P) x) (.boxx x X φ)
  | .split _ φ => .split (forcedCtx (refineCtx Γ P)) φ

/-! ## Theorems -/

/-- ⭐**The forced restriction typechecks**: re-pairing a well-typed formula gives a well-typed
    formula, for both sources of forcing. -/
theorem wf_pelim {Δ : Ctx} {φ : Wff} (h : WfWff Δ φ) :
    ∀ (Γ : Ctx) (P : Nat → Pat), Δ = refineCtx Γ P → WfWff Γ (pelim Γ P φ) := by
  induction h with
  | prim ha hb =>
      intro Γ P hΔ; subst hΔ
      have hT : ∀ A B, Ty.base ≠ .prod A B := by intro A B h; cases h
      exact .prim ((refType_refine_nonprod _ _ _ hT).mp ha)
        ((refType_refine_nonprod _ _ _ hT).mp hb)
  | top => intro _ _ _; exact .top
  | conj _ _ ih₁ ih₂ => intro Γ P hΔ; exact .conj (ih₁ Γ P hΔ) (ih₂ Γ P hΔ)
  | imp _ _ ih₁ ih₂ => intro Γ P hΔ; exact .imp (ih₁ Γ P hΔ) (ih₂ Γ P hΔ)
  | @box Δ χ hnb hχ _ =>
      intro Γ P hΔ; subst hΔ
      refine .split (.box (noBoxProdCtx_forced Γ) ?_)
      rw [← unboxCtx_refine_forced hnb]
      exact hχ
  | @boxx Δ x X χ hx hnb hχ _ =>
      intro Γ P hΔ; subst hΔ
      have hlook : refType Γ x = some (.dia X) :=
        (refType_refine_nonprod Γ P x (by intro A B h; cases h)).mp
          (Entry.lookup_of_leafAt _ _ hx)
      refine .split (.boxx (entryType_forcedX hlook) (noBoxProdCtx_forcedX Γ x) ?_)
      rw [← diaCtx_refine_forced hnb hx]
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
  | .boxx _ _ _, _, h => h.elim
  | .split Q (.box χ), P, h => by
      obtain ⟨rfl, hχ⟩ := h
      refine ⟨rfl, ?_⟩
      rw [← unboxCtx_refine_forced_refine Γ P]
      exact hχ
  | .split Q (.boxx x X χ), P, h => by
      obtain ⟨hx, rfl, hχ⟩ := h
      have hx' : refType Γ x = some (.dia X) :=
        (refType_refine_nonprod Γ P x (by intro A B h; cases h)).mp hx
      refine ⟨hx', rfl, ?_⟩
      rw [← diaCtx_refine_forcedX_refine Γ P hx']
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
  | .boxx _ _ _, h => h.elim
  | .split Q (.box χ), h => by
      obtain ⟨rfl, hχ⟩ := h
      refine ⟨rfl, ?_⟩
      rw [unboxCtx_refine_forced_refine Γ P]
      exact hχ
  | .split Q (.boxx x X χ), h => by
      obtain ⟨hx, rfl, hχ⟩ := h
      refine ⟨(refType_refine_nonprod Γ P x (by intro A B h; cases h)).mpr hx, rfl, ?_⟩
      rw [diaCtx_refine_forcedX_refine Γ P hx]
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
  | .boxx _ _ _, _, h => h.elim
  | .split Q (.box χ), P, h => by
      obtain ⟨rfl, -⟩ := h
      rfl
  | .split Q (.boxx x X χ), P, h => by
      obtain ⟨-, rfl, -⟩ := h
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
  | .boxx _ _ _, h => h.elim
  | .split Q (.box χ), h => by
      obtain ⟨rfl, -⟩ := h
      rfl
  | .split Q (.boxx x X χ), h => by
      obtain ⟨-, rfl, -⟩ := h
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
  | .boxx _ _ _, _, _ => rfl
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
  | .boxx x X φ => .boxx (x.rename ρ) X (φ.rename ρ)
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
#print axioms PatSplit.normal_pelim
#print axioms PatSplit.unpair_pelim
#print axioms PatSplit.pelim_unpair
#print axioms PatSplit.pelim_pat_irrel
#print axioms PatSplit.rename_eqRec
