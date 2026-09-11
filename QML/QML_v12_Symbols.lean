import Mathlib.Tactic

/-!
# QML v12 — foundations: types, names, annotations, contexts

The v12 redesign, combining the three prototypes (`DiaIdxProto`, `DiaIdxSem`, `PatSplitProto`):

* **Three kinds of names.**  FREE variables (`free n`, the former "user" variables), QUANTIFIER-BOUND
  variables (`bnd n`, canonical by binder depth), and PAIR-BOUND components (`comp v s`, canonical by
  an access path from the eliminated variable).  Nothing is allocated for pair components, so no
  order on names is needed anywhere — the v11 `ℕ` encoding and `firstPairVar` are gone.
* **Contexts are functions**, stored as root-keyed SPLIT TREES: a root variable holds a tree whose
  leaves are typed (present) or hidden; its components are reached by paths.  Promotions (`□`, `◇_x`)
  HIDE/REVEAL leaves rather than building existential inner contexts, and pattern splits REFINE trees
  in place.  A context also records the binder DEPTH, so the next quantifier slot is `bnd depth`.
* **Witness annotations.**  A term's type is a plain `VarType` together with an annotation indexed
  by it (`Ann T`), whose `◇`-nodes carry an access-path index `⟨root, path⟩`.

This file holds only the data and its algebra; terms, formulas and proofs build on it.
-/

namespace V12

/-! ## Plain types -/

inductive VarType where
  | Var
  | VTypeOne
  | VTypeProd (A B : VarType)
  | VTypeBox (A : VarType)
  | VTypeDia (A : VarType)
deriving DecidableEq

namespace VarType

/-- Contains a box somewhere in its product structure. -/
def boxy : VarType → Bool
  | .Var => false
  | .VTypeOne => false
  | .VTypeProd A B => A.boxy || B.boxy
  | .VTypeBox _ => true
  | .VTypeDia _ => false

/-- A product containing a box: such an entry blocks the formation of modal nodes. -/
def boxyProd : VarType → Bool
  | .VTypeProd A B => A.boxy || B.boxy
  | _ => false

theorem boxyProd_of_boxy {T : VarType} (h : T.boxy = false) : T.boxyProd = false := by
  cases T <;> simp_all [boxy, boxyProd]

end VarType

/-! ## Names -/

/-- A step into a product. -/
inductive PStep where
  | fst
  | snd
deriving DecidableEq

/-- The root of a name: a free or a quantifier-bound variable. -/
inductive Root where
  | free (n : ℕ)
  | bnd (n : ℕ)
deriving DecidableEq

/-- Variable symbols: free, quantifier-bound, or a pair-bound component of another symbol. -/
inductive VarSymb where
  | free (n : ℕ)
  | bnd (n : ℕ)
  | comp (v : VarSymb) (s : PStep)
deriving DecidableEq

/-- The free-variable symbols — what proof rules take from the user. -/
structure FreeSymb where
  idx : ℕ
deriving DecidableEq

def FreeSymb.toVar (u : FreeSymb) : VarSymb := .free u.idx

namespace VarSymb

def root : VarSymb → Root
  | .free n => .free n
  | .bnd n => .bnd n
  | .comp v _ => v.root

/-- The access path from the root, root-first. -/
def path : VarSymb → List PStep
  | .free _ => []
  | .bnd _ => []
  | .comp v s => v.path ++ [s]

def isFree : VarSymb → Bool
  | .free _ => true
  | _ => false

def ofRoot : Root → VarSymb
  | .free n => .free n
  | .bnd n => .bnd n

@[simp] theorem root_comp (v : VarSymb) (s : PStep) : (VarSymb.comp v s).root = v.root := rfl
@[simp] theorem path_comp (v : VarSymb) (s : PStep) : (VarSymb.comp v s).path = v.path ++ [s] := rfl
@[simp] theorem root_ofRoot (r : Root) : (VarSymb.ofRoot r).root = r := by cases r <;> rfl
@[simp] theorem path_ofRoot (r : Root) : (VarSymb.ofRoot r).path = [] := by cases r <;> rfl

/-- A name is determined by its root and its path. -/
theorem ext_root_path {v w : VarSymb} (hr : v.root = w.root) (hp : v.path = w.path) : v = w := by
  induction v generalizing w with
  | free n =>
      cases w with
      | free m => simp_all [root]
      | bnd m => simp [root] at hr
      | comp w' s => simp [path] at hp
  | bnd n =>
      cases w with
      | free m => simp [root] at hr
      | bnd m => simp_all [root]
      | comp w' s => simp [path] at hp
  | comp v' s ih =>
      cases w with
      | free m => simp [path] at hp
      | bnd m => simp [path] at hp
      | comp w' t =>
          simp only [root, path] at hr hp
          obtain ⟨hp', hst⟩ := List.append_inj' hp rfl
          simp only [List.cons.injEq, and_true] at hst
          rw [ih hr hp', hst]

end VarSymb

/-! ## Witness annotations -/

/-- A step of an annotation's access path: into a product, a box, or a diamond. -/
inductive Step where
  | fst
  | snd
  | box
  | dia
deriving DecidableEq

def PStep.toStep : PStep → Step
  | .fst => .fst
  | .snd => .snd

/-- An annotation index: the `◇`-node reached from the name `root` by `path`. -/
structure Idx where
  root : VarSymb
  path : List Step
deriving DecidableEq

def Idx.pre (s : Step) (i : Idx) : Idx := ⟨i.root, s :: i.path⟩
def Idx.strip (i : Idx) : Idx := ⟨i.root, i.path.tail⟩
def Idx.ren (f : VarSymb → VarSymb) (i : Idx) : Idx := ⟨f i.root, i.path⟩

@[simp] theorem Idx.strip_pre (s : Step) (i : Idx) : (i.pre s).strip = i := rfl

/-- The annotation over a plain type: a witness index at every `◇`. -/
inductive Ann : VarType → Type where
  | var : Ann .Var
  | one : Ann .VTypeOne
  | prod {A B : VarType} (a : Ann A) (b : Ann B) : Ann (.VTypeProd A B)
  | box {A : VarType} (a : Ann A) : Ann (.VTypeBox A)
  | dia {A : VarType} (i : Idx) (a : Ann A) : Ann (.VTypeDia A)
deriving DecidableEq

namespace Ann

def mapIdx (f : Idx → Idx) : {T : VarType} → Ann T → Ann T
  | _, var => var
  | _, one => one
  | _, prod a b => prod (a.mapIdx f) (b.mapIdx f)
  | _, box a => box (a.mapIdx f)
  | _, dia i a => dia (f i) (a.mapIdx f)

def idxs : {T : VarType} → Ann T → List Idx
  | _, var => []
  | _, one => []
  | _, prod a b => a.idxs ++ b.idxs
  | _, box a => a.idxs
  | _, dia i a => i :: a.idxs

/-- The index at the `◇`-node reached by a path (junk if the path does not lead to one). -/
def idxAt : {T : VarType} → Ann T → List Step → Idx
  | _, dia i _, [] => i
  | _, prod a _, .fst :: p => a.idxAt p
  | _, prod _ b, .snd :: p => b.idxAt p
  | _, box a, .box :: p => a.idxAt p
  | _, dia _ a, .dia :: p => a.idxAt p
  | _, _, _ => ⟨.free 0, []⟩

/-- The SELF annotation of a variable: every `◇`-node indexed by the variable itself along its
    path — how a declared variable elaborates to a term type. -/
def self (v : VarSymb) : (T : VarType) → Ann T
  | .Var => var
  | .VTypeOne => one
  | .VTypeProd A B => prod ((self v A).mapIdx (Idx.pre .fst)) ((self v B).mapIdx (Idx.pre .snd))
  | .VTypeBox A => box ((self v A).mapIdx (Idx.pre .box))
  | .VTypeDia A => dia ⟨v, []⟩ ((self v A).mapIdx (Idx.pre .dia))

end Ann

/-- The path leads to a `◇`-node. -/
def VarType.DiaAt : VarType → List Step → Prop
  | .VTypeDia _, [] => True
  | .VTypeProd A _, .fst :: p => A.DiaAt p
  | .VTypeProd _ B, .snd :: p => B.DiaAt p
  | .VTypeBox A, .box :: p => A.DiaAt p
  | .VTypeDia A, .dia :: p => A.DiaAt p
  | _, _ => False

namespace Ann

theorem mapIdx_mapIdx (f g : Idx → Idx) {T : VarType} (S : Ann T) :
    (S.mapIdx f).mapIdx g = S.mapIdx (g ∘ f) := by
  induction S with
  | var => rfl
  | one => rfl
  | prod a b iha ihb => simp [mapIdx, iha, ihb]
  | box a ih => simp [mapIdx, ih]
  | dia i a ih => simp [mapIdx, ih]

@[simp] theorem mapIdx_id {T : VarType} (S : Ann T) : S.mapIdx id = S := by
  induction S with
  | var => rfl
  | one => rfl
  | prod a b iha ihb => simp [mapIdx, iha, ihb]
  | box a ih => simp [mapIdx, ih]
  | dia i a ih => simp [mapIdx, ih]

theorem mapIdx_congr {f g : Idx → Idx} {T : VarType} (S : Ann T) (h : ∀ i ∈ S.idxs, f i = g i) :
    S.mapIdx f = S.mapIdx g := by
  induction S with
  | var => rfl
  | one => rfl
  | prod a b iha ihb =>
      simp only [mapIdx]
      rw [iha (fun i hi => h i (by simp [idxs, hi])), ihb (fun i hi => h i (by simp [idxs, hi]))]
  | box a ih => simp only [mapIdx]; rw [ih (fun i hi => h i (by simpa [idxs] using hi))]
  | dia j a ih =>
      simp only [mapIdx]
      rw [h j (by simp [idxs]), ih (fun i hi => h i (by simp [idxs, hi]))]

theorem mem_idxs_mapIdx {f : Idx → Idx} {i : Idx} {T : VarType} {S : Ann T}
    (hi : i ∈ (S.mapIdx f).idxs) : ∃ j ∈ S.idxs, f j = i := by
  induction S with
  | var => simp [mapIdx, idxs] at hi
  | one => simp [mapIdx, idxs] at hi
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

theorem idxAt_mapIdx (f : Idx → Idx) {T : VarType} (S : Ann T) (p : List Step) :
    T.DiaAt p → (S.mapIdx f).idxAt p = f (S.idxAt p) := by
  induction S generalizing p with
  | var => intro h; cases p <;> exact (h : False).elim
  | one => intro h; cases p <;> exact (h : False).elim
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

theorem idxAt_mem {T : VarType} (S : Ann T) (p : List Step) : T.DiaAt p → S.idxAt p ∈ S.idxs := by
  induction S generalizing p with
  | var => intro h; cases p <;> exact (h : False).elim
  | one => intro h; cases p <;> exact (h : False).elim
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

theorem mapIdx_injective {f : Idx → Idx} (hf : Function.Injective f) {T : VarType} :
    Function.Injective (Ann.mapIdx f : Ann T → Ann T) := by
  intro S S' h
  induction S with
  | var => cases S'; rfl
  | one => cases S'; rfl
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

end Ann

/-! ## Split patterns and split trees -/

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
def Pat.path : List PStep → Pat
  | [] => .stop
  | .fst :: q => .split (Pat.path q) .stop
  | .snd :: q => .split .stop (Pat.path q)

/-- The entry of one root variable: a split tree whose leaves are present (typed) or hidden. -/
inductive Entry where
  | leaf (o : Option VarType)
  | node (a b : Entry)
deriving DecidableEq

def VarType.follow : VarType → List PStep → Option VarType
  | T, [] => some T
  | .VTypeProd A _, .fst :: q => A.follow q
  | .VTypeProd _ B, .snd :: q => B.follow q
  | _, _ :: _ => none

namespace Entry

/-- Apply a pattern: split product leaves where the pattern says so. -/
def refine : Entry → Pat → Entry
  | e, .stop => e
  | e, .split pa pb =>
      match e with
      | .leaf (some (.VTypeProd A B)) =>
          .node (refine (.leaf (some A)) pa) (refine (.leaf (some B)) pb)
      | .node a b => .node (refine a pa) (refine b pb)
      | e => e

def forcedTy : VarType → Pat
  | .VTypeProd A B =>
      if (VarType.VTypeProd A B).boxy then .split (forcedTy A) (forcedTy B) else .stop
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
  | .leaf (some (.VTypeBox X)) => .leaf (some X)
  | .leaf _ => .leaf none
  | .node a b => mkNode (unbox a) (unbox b)

/-- Into a `◇_x` whose witness leaf is at path `q`: the box shadow, with the witness revealed at its
    realization type.  Along the witness path the tree stays OPEN. -/
def unboxExcept : Entry → List PStep → VarType → Entry
  | .leaf _, [], X => .leaf (some X)
  | .node a b, .fst :: q, X => .node (a.unboxExcept q X) b.unbox
  | .node a b, .snd :: q, X => .node a.unbox (b.unboxExcept q X)
  | e, _, _ => e.unbox

def NoBoxProd : Entry → Prop
  | .leaf (some T) => T.boxyProd = false
  | .leaf none => True
  | .node a b => NoBoxProd a ∧ NoBoxProd b

/-- The type at a path: through split nodes, then through the leaf's own product type. -/
def lookup : Entry → List PStep → Option VarType
  | .leaf o, q => o.bind (fun T => T.follow q)
  | .node a _, .fst :: q => a.lookup q
  | .node _ b, .snd :: q => b.lookup q
  | .node _ _, [] => none

/-- The entry EXACTLY at a path (no looking inside an unsplit product). -/
def leafAt : Entry → List PStep → Option VarType
  | .leaf o, [] => o
  | .leaf _, _ :: _ => none
  | .node a _, .fst :: q => a.leafAt q
  | .node _ b, .snd :: q => b.leafAt q
  | .node _ _, [] => none

/-- Set the leaf at a path (used to declare a variable). -/
def setLeaf : Entry → List PStep → Option VarType → Entry
  | .leaf _, [], o => .leaf o
  | .node _ _, [], o => .leaf o
  | .node a b, .fst :: q, o => .node (a.setLeaf q o) b
  | .node a b, .snd :: q, o => .node a (b.setLeaf q o)
  | e, _ :: _, _ => e

/-! ### Split-tree lemmas -/

@[simp] theorem refine_stop (e : Entry) : e.refine .stop = e := rfl

theorem refine_nonprod_leaf {o : Option VarType} (ho : ∀ A B, o ≠ some (.VTypeProd A B)) (p : Pat) :
    (Entry.leaf o).refine p = .leaf o := by
  cases p with
  | stop => rfl
  | split pa pb =>
      rcases o with _ | ⟨_ | _ | ⟨A, B⟩ | _ | _⟩
      · rfl
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
          rcases e with ⟨_ | ⟨_ | _ | ⟨A, B⟩ | _ | _⟩⟩ | ⟨a, b⟩
          · rfl
          · rfl
          · rfl
          · simp only [refine, Pat.join, iha, ihb]
          · rfl
          · rfl
          · simp only [refine, Pat.join, iha, ihb]

theorem forcedTy_of_not_boxy {T : VarType} (h : T.boxy = false) : forcedTy T = .stop := by
  cases T with
  | VTypeProd A B => simp only [forcedTy]; rw [if_neg (by simp_all [VarType.boxy])]
  | _ => rfl

theorem noBoxProd_refine (e : Entry) (p : Pat) (h : e.NoBoxProd) : (e.refine p).NoBoxProd := by
  induction p generalizing e with
  | stop => exact h
  | split pa pb iha ihb =>
      rcases e with ⟨_ | ⟨_ | _ | ⟨A, B⟩ | _ | _⟩⟩ | ⟨a, b⟩
      · exact h
      · exact h
      · exact h
      · simp only [NoBoxProd, VarType.boxyProd, Bool.or_eq_false_iff] at h
        exact ⟨iha _ (VarType.boxyProd_of_boxy h.1), ihb _ (VarType.boxyProd_of_boxy h.2)⟩
      · exact h
      · exact h
      · exact ⟨iha a h.1, ihb b h.2⟩

theorem noBoxProd_forcedTy (T : VarType) :
    ((Entry.leaf (some T)).refine (forcedTy T)).NoBoxProd := by
  induction T with
  | Var => rfl
  | VTypeOne => rfl
  | VTypeProd A B ihA ihB =>
      by_cases hb : (VarType.VTypeProd A B).boxy = true
      · simp only [forcedTy, hb, if_true, refine, NoBoxProd]
        exact ⟨ihA, ihB⟩
      · simp only [forcedTy, hb, Bool.false_eq_true, if_false, refine_stop, NoBoxProd]
        simpa [VarType.boxyProd, VarType.boxy] using hb
  | VTypeBox A _ => rfl
  | VTypeDia A _ => rfl

theorem noBoxProd_forced (e : Entry) : (e.refine e.forced).NoBoxProd := by
  induction e with
  | leaf o =>
      rcases o with _ | T
      · trivial
      · exact noBoxProd_forcedTy T
  | node a b iha ihb => exact ⟨iha, ihb⟩

theorem unbox_refine_nonboxy (T : VarType) (hT : T.boxy = false) (p : Pat) :
    ((Entry.leaf (some T)).refine p).unbox = .leaf none := by
  induction p generalizing T with
  | stop =>
      cases T with
      | VTypeBox _ => simp [VarType.boxy] at hT
      | _ => rfl
  | split pa pb iha ihb =>
      cases T with
      | VTypeProd A B =>
          simp only [VarType.boxy, Bool.or_eq_false_iff] at hT
          simp only [refine, unbox, iha A hT.1, ihb B hT.2, mkNode]
      | VTypeBox _ => simp [VarType.boxy] at hT
      | _ => rfl

theorem unbox_refine_leaf (T : VarType) (p : Pat)
    (h : ((Entry.leaf (some T)).refine p).NoBoxProd) :
    ((Entry.leaf (some T)).refine p).unbox = ((Entry.leaf (some T)).refine (forcedTy T)).unbox := by
  induction T generalizing p with
  | Var => rw [refine_nonprod_leaf (by simp) p]; rfl
  | VTypeOne => rw [refine_nonprod_leaf (by simp) p]; rfl
  | VTypeBox X _ => rw [refine_nonprod_leaf (by simp) p]; rfl
  | VTypeDia X _ => rw [refine_nonprod_leaf (by simp) p]; rfl
  | VTypeProd A B ihA ihB =>
      by_cases hb : (VarType.VTypeProd A B).boxy = true
      · cases p with
        | stop => simp [NoBoxProd, VarType.boxyProd, VarType.boxy] at h hb; simp_all
        | split pa pb =>
            simp only [forcedTy, hb, if_true, refine, unbox] at h ⊢
            rw [ihA pa h.1, ihB pb h.2]
      · have hb' : (VarType.VTypeProd A B).boxy = false := by simpa using hb
        simp only [forcedTy, hb, Bool.false_eq_true, if_false, refine_stop]
        rw [unbox_refine_nonboxy _ hb' p]
        rfl

/-- ⭐Extra refinement is invisible inside `□`. -/
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
          simp only [forced, refine, unbox, ha, hb]
      | split pa pb =>
          simp only [refine, forced, unbox] at h ⊢
          rw [iha pa h.1, ihb pb h.2]

theorem lookup_refine_nonprod (e : Entry) (p : Pat) (q : List PStep) {T : VarType}
    (hT : ∀ A B, T ≠ .VTypeProd A B) : (e.refine p).lookup q = some T ↔ e.lookup q = some T := by
  induction p generalizing e q with
  | stop => rfl
  | split pa pb iha ihb =>
      rcases e with ⟨_ | ⟨_ | _ | ⟨A, B⟩ | _ | _⟩⟩ | ⟨a, b⟩
      · rfl
      · rfl
      · rfl
      · rcases q with _ | ⟨_ | _, q⟩
        · change none = some T ↔ some (VarType.VTypeProd A B) = some T
          exact ⟨(fun h => by cases h), fun h => absurd (Option.some.inj h).symm (hT A B)⟩
        · exact iha (.leaf (some A)) q
        · exact ihb (.leaf (some B)) q
      · rfl
      · rfl
      · rcases q with _ | ⟨_ | _, q⟩
        · rfl
        · exact iha a q
        · exact ihb b q

theorem lookup_of_leafAt (q : List PStep) : ∀ (e : Entry) {T : VarType},
    e.leafAt q = some T → e.lookup q = some T := by
  induction q with
  | nil =>
      intro e T h
      rcases e with ⟨_ | T'⟩ | ⟨a, b⟩
      · simp [leafAt] at h
      · simpa [leafAt, lookup, VarType.follow] using h
      · simp [leafAt] at h
  | cons s q ih =>
      intro e T h
      rcases e with ⟨o⟩ | ⟨a, b⟩
      · simp [leafAt] at h
      · cases s
        · exact ih a h
        · exact ih b h

theorem leafAt_refine_forcedPath (q : List PStep) : ∀ (e : Entry) (X : VarType),
    e.lookup q = some (.VTypeDia X) →
      (e.refine (e.forced.join (Pat.path q))).leafAt q = some (.VTypeDia X) := by
  induction q with
  | nil =>
      intro e X h
      rcases e with ⟨_ | ⟨_ | _ | ⟨A, B⟩ | _ | Y⟩⟩ | ⟨a, b⟩
      · simp [lookup] at h
      · simp [lookup, VarType.follow] at h
      · simp [lookup, VarType.follow] at h
      · simp [lookup, VarType.follow] at h
      · simp [lookup, VarType.follow] at h
      · simp only [lookup, Option.bind, VarType.follow, Option.some.injEq,
          VarType.VTypeDia.injEq] at h
        subst h
        rfl
      · simp [lookup] at h
  | cons s q ih =>
      intro e X h
      rcases e with ⟨_ | ⟨_ | _ | ⟨A, B⟩ | _ | Y⟩⟩ | ⟨a, b⟩
      · simp [lookup] at h
      · cases s <;> simp [lookup, VarType.follow] at h
      · cases s <;> simp [lookup, VarType.follow] at h
      · cases s
        · have hA : (Entry.leaf (some A)).lookup q = some (.VTypeDia X) := h
          by_cases hb : (VarType.VTypeProd A B).boxy = true
          · simp only [forced, forcedTy, hb, if_true, Pat.path, Pat.join, Pat.join_stop, refine,
              leafAt]
            exact ih _ X hA
          · have hA' : A.boxy = false := by
              simp only [VarType.boxy, Bool.or_eq_true, not_or, Bool.not_eq_true] at hb; exact hb.1
            simp only [forced, forcedTy, hb, Bool.false_eq_true, if_false, Pat.path, Pat.join,
              refine, leafAt]
            have := ih _ X hA
            simpa only [forced, forcedTy_of_not_boxy hA', Pat.join] using this
        · have hB : (Entry.leaf (some B)).lookup q = some (.VTypeDia X) := h
          by_cases hb : (VarType.VTypeProd A B).boxy = true
          · simp only [forced, forcedTy, hb, if_true, Pat.path, Pat.join, refine, leafAt]
            exact ih _ X hB
          · have hB' : B.boxy = false := by
              simp only [VarType.boxy, Bool.or_eq_true, not_or, Bool.not_eq_true] at hb; exact hb.2
            simp only [forced, forcedTy, hb, Bool.false_eq_true, if_false, Pat.path, Pat.join,
              refine, leafAt]
            have := ih _ X hB
            simpa only [forced, forcedTy_of_not_boxy hB', Pat.join] using this
      · cases s <;> simp [lookup, VarType.follow] at h
      · cases s <;> simp [lookup, VarType.follow] at h
      · cases s
        · simp only [forced, Pat.path, Pat.join, Pat.join_stop, refine, leafAt]
          exact ih a X h
        · simp only [forced, Pat.path, Pat.join, refine, leafAt]
          exact ih b X h

/-- ⭐Extra refinement is invisible inside `◇_x` too, with the witness path kept open. -/
theorem unboxExcept_refine_forced (q : List PStep) : ∀ (e : Entry) (p : Pat) (X : VarType),
    (e.refine p).NoBoxProd → (e.refine p).leafAt q = some (.VTypeDia X) →
    (e.refine p).unboxExcept q X = (e.refine (e.forced.join (Pat.path q))).unboxExcept q X := by
  induction q with
  | nil =>
      intro e p X _ hl
      rcases e with ⟨_ | ⟨_ | _ | ⟨A, B⟩ | _ | Y⟩⟩ | ⟨a, b⟩
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
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
      rcases e with ⟨_ | ⟨_ | _ | ⟨A, B⟩ | _ | Y⟩⟩ | ⟨a, b⟩
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · cases p with
        | stop => simp [leafAt] at hl
        | split pa pb =>
            by_cases hb : (VarType.VTypeProd A B).boxy = true
            · cases s
              · simp only [refine, NoBoxProd, leafAt] at h hl
                simp only [forced, forcedTy, hb, if_true, Pat.path, Pat.join, Pat.join_stop,
                  refine, unboxExcept]
                exact congrArg₂ Entry.node (ih _ pa X h.1 hl) (unbox_refine_leaf B pb h.2)
              · simp only [refine, NoBoxProd, leafAt] at h hl
                simp only [forced, forcedTy, hb, if_true, Pat.path, Pat.join, Pat.join_stop,
                  refine, unboxExcept]
                exact congrArg₂ Entry.node (unbox_refine_leaf A pa h.1) (ih _ pb X h.2 hl)
            · have hb' : (VarType.VTypeProd A B).boxy = false := by simpa using hb
              simp only [VarType.boxy, Bool.or_eq_false_iff] at hb'
              cases s
              · simp only [refine, NoBoxProd, leafAt] at h hl
                simp only [forced, forcedTy, hb, Bool.false_eq_true, if_false, Pat.path,
                  Pat.join, refine, unboxExcept]
                have hih := ih _ pa X h.1 hl
                simp only [forced, forcedTy_of_not_boxy hb'.1, Pat.join] at hih
                exact congrArg₂ Entry.node hih
                  ((unbox_refine_nonboxy B hb'.2 pb).trans
                    (unbox_refine_nonboxy B hb'.2 .stop).symm)
              · simp only [refine, NoBoxProd, leafAt] at h hl
                simp only [forced, forcedTy, hb, Bool.false_eq_true, if_false, Pat.path,
                  Pat.join, refine, unboxExcept]
                have hih := ih _ pb X h.2 hl
                simp only [forced, forcedTy_of_not_boxy hb'.2, Pat.join] at hih
                exact congrArg₂ Entry.node
                  ((unbox_refine_nonboxy A hb'.1 pa).trans
                    (unbox_refine_nonboxy A hb'.1 .stop).symm)
                  hih
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · rw [refine_nonprod_leaf (by simp) p] at hl; simp [leafAt] at hl
      · cases p with
        | stop =>
            cases s
            · simp only [refine_stop, NoBoxProd, leafAt] at h hl
              simp only [forced, Pat.path, Pat.join, Pat.join_stop, refine, unboxExcept]
              exact congrArg₂ Entry.node (ih a .stop X h.1 hl) (unbox_refine_forced b .stop h.2)
            · simp only [refine_stop, NoBoxProd, leafAt] at h hl
              simp only [forced, Pat.path, Pat.join, Pat.join_stop, refine, unboxExcept]
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

/-- A context: for each root, its split tree; and the binder depth (the next quantifier slot is
    `bnd depth`). -/
@[ext] structure Ctx where
  tree : Root → Entry
  depth : ℕ

namespace Ctx

/-- The type of the name `v` as a context ENTRY (a present leaf). -/
def lookup (Γ : Ctx) (v : VarSymb) : Option VarType := (Γ.tree v.root).leafAt v.path

/-- The type reachable at `v`, possibly through an unsplit product (a leaf elimination). -/
def refType (Γ : Ctx) (v : VarSymb) : Option VarType := (Γ.tree v.root).lookup v.path

/-- The empty context. -/
def empty : Ctx := ⟨fun _ => .leaf none, 0⟩

/-- A free name is fresh: nothing of its root is present. -/
def FreshRoot (Γ : Ctx) (r : Root) : Prop := Γ.tree r = .leaf none

/-- Declare a variable at a fresh ROOT. -/
def insertRoot (Γ : Ctx) (r : Root) (T : VarType) : Ctx :=
  { Γ with tree := Function.update Γ.tree r (.leaf (some T)) }

def insertFree (Γ : Ctx) (u : FreeSymb) (T : VarType) : Ctx := Γ.insertRoot (.free u.idx) T

/-- The next quantifier slot. -/
def nextBnd (Γ : Ctx) : VarSymb := .bnd Γ.depth

/-- Go under a quantifier binder: declare its slot and deepen. -/
def insertBnd (Γ : Ctx) (T : VarType) : Ctx :=
  ⟨Function.update Γ.tree (.bnd Γ.depth) (.leaf (some T)), Γ.depth + 1⟩

def unbox (Γ : Ctx) : Ctx := { Γ with tree := fun r => (Γ.tree r).unbox }

def dia (Γ : Ctx) (x : VarSymb) (X : VarType) : Ctx :=
  { Γ with tree := fun r =>
      if r = x.root then (Γ.tree r).unboxExcept x.path X else (Γ.tree r).unbox }

def refine (Γ : Ctx) (P : Root → Pat) : Ctx := { Γ with tree := fun r => (Γ.tree r).refine (P r) }

def forced (Γ : Ctx) : Root → Pat := fun r => (Γ.tree r).forced

def pathPat (x : VarSymb) : Root → Pat := fun r => if r = x.root then Pat.path x.path else .stop

def forcedX (Γ : Ctx) (x : VarSymb) : Root → Pat := fun r => (Γ.forced r).join (pathPat x r)

def joinPat (P Q : Root → Pat) : Root → Pat := fun r => (P r).join (Q r)

def NoBoxProd (Γ : Ctx) : Prop := ∀ r, (Γ.tree r).NoBoxProd

/-! ### Context lemmas -/

@[simp] theorem refine_depth (Γ : Ctx) (P : Root → Pat) : (Γ.refine P).depth = Γ.depth := rfl
@[simp] theorem unbox_depth (Γ : Ctx) : Γ.unbox.depth = Γ.depth := rfl
@[simp] theorem dia_depth (Γ : Ctx) (x : VarSymb) (X : VarType) : (Γ.dia x X).depth = Γ.depth := rfl

/-- ⭐Splitting never changes the binder depth, so it can never make a slot be reused. -/
theorem nextBnd_refine (Γ : Ctx) (P : Root → Pat) : (Γ.refine P).nextBnd = Γ.nextBnd := rfl

theorem refine_join (Γ : Ctx) (P Q : Root → Pat) :
    (Γ.refine P).refine Q = Γ.refine (joinPat P Q) := by
  ext r
  · exact Entry.refine_join _ _ _
  · rfl

theorem noBoxProd_forced (Γ : Ctx) : (Γ.refine Γ.forced).NoBoxProd :=
  fun r => Entry.noBoxProd_forced (Γ.tree r)

theorem noBoxProd_forcedX (Γ : Ctx) (x : VarSymb) : (Γ.refine (Γ.forcedX x)).NoBoxProd := by
  intro r
  show ((Γ.tree r).refine ((Γ.tree r).forced.join (pathPat x r))).NoBoxProd
  rw [← Entry.refine_join]
  exact Entry.noBoxProd_refine _ _ (Entry.noBoxProd_forced (Γ.tree r))

theorem unbox_refine_forced {Γ : Ctx} {P : Root → Pat} (h : (Γ.refine P).NoBoxProd) :
    (Γ.refine P).unbox = (Γ.refine Γ.forced).unbox := by
  ext r
  · exact Entry.unbox_refine_forced (Γ.tree r) (P r) (h r)
  · rfl

theorem refType_refine_nonprod (Γ : Ctx) (P : Root → Pat) (v : VarSymb) {T : VarType}
    (hT : ∀ A B, T ≠ .VTypeProd A B) : (Γ.refine P).refType v = some T ↔ Γ.refType v = some T :=
  Entry.lookup_refine_nonprod _ _ _ hT

theorem lookup_forcedX {Γ : Ctx} {x : VarSymb} {X : VarType}
    (h : Γ.refType x = some (.VTypeDia X)) :
    (Γ.refine (Γ.forcedX x)).lookup x = some (.VTypeDia X) := by
  show ((Γ.tree x.root).refine ((Γ.tree x.root).forced.join (pathPat x x.root))).leafAt x.path = _
  simp only [pathPat, if_true]
  exact Entry.leafAt_refine_forcedPath _ _ _ h

theorem dia_refine_forced {Γ : Ctx} {P : Root → Pat} {x : VarSymb} {X : VarType}
    (h : (Γ.refine P).NoBoxProd) (hx : (Γ.refine P).lookup x = some (.VTypeDia X)) :
    (Γ.refine P).dia x X = (Γ.refine (Γ.forcedX x)).dia x X := by
  ext r
  · simp only [dia, refine, forcedX, forced, pathPat]
    by_cases hr : r = x.root
    · subst hr
      simp only [if_true]
      exact Entry.unboxExcept_refine_forced _ _ _ _ (h _) hx
    · simp only [hr, if_false, Pat.join_stop]
      exact Entry.unbox_refine_forced _ _ (h r)
  · rfl

end Ctx

end V12
