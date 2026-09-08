import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Common

/-!
# QML v11 — Symbols and contexts (locally-nameless foundation)

v11 reworks v10's naming discipline.  The one change everything else follows from:

**`VarSymb` has two constructors.**  `.mk` is user-facing — the only kind a user ever writes,
and the only kind that ever appears as a FREE variable.  `.bnd` is reserved for BOUND-variable
slots, chosen canonically from the context and never written by a user.

Since the two namespaces are disjoint by construction:

* a user variable can never be captured by a binder, so capture-avoidance side conditions of the
  form `new ∉ WFF.boundVars φ` become VACUOUS for user renamings — the `boundVars` machinery
  should ultimately be retirable;
* freshness need only be checked against the CONTEXT, never against "context ∪ bound variables";
* `WFF.ctx_ext`'s collision branches cannot fire when weakening by a user variable;
* two formulas built at the same context choose the SAME binder name, so α-variants do not arise.

This is locally-nameless in substance — free variables named, bound variables positional — while
keeping `VarCtx` a plain `Finset`, so none of v10's context machinery needs reworking.  The
guarantee is enforced at the PROOF-RULE boundary (rules take `UserSymb` and inject) rather than by
a predicate threaded through every lemma.
-/

/-! ## Variable types (unchanged from v10) -/

inductive VarType where
  | Var       : VarType
  | VTypeBox  : VarType → VarType
  | VTypeDia  : VarType → VarType
  | VTypeOne  : VarType                      -- nullary product / trivial dia witness
  | VTypeProd : VarType → VarType → VarType  -- binary product
  deriving DecidableEq

-- Bool test: does this type have `.VTypeBox` as its outermost constructor?
-- With pairs, this tests whether *any* of the outermost constructors are `.VTypeBox`.
def VarType.isBox : VarType → Bool
  | .VTypeBox _ => true
  | .VTypeProd V₁ V₂ => VarType.isBox V₁ ∨ VarType.isBox V₂
  | _           => false

-- Injective encoding of VarType to ℕ. Used to derive a LinearOrder on
-- (VarSymb × VarType), which is used by `VarCtx.firstPairVar` to extract a
-- pair-typed binder deterministically (via `Finset.sort`, avoiding the
-- noncomputable `Finset.toList`).

/-! ## Variable symbols — the v11 change -/

/-- Variable symbols.  `mk` is user-facing (free variables); `bnd` is reserved for bound slots
    and is never written by a user. -/
inductive VarSymb : Type where
  | mk  : ℕ → VarSymb
  | bnd : ℕ → VarSymb
  deriving DecidableEq

/-- The user-facing symbol type.  Proof rules take THIS and inject via `UserSymb.toVar`, which is
    what keeps reserved names out of user-supplied data without any invariant to maintain. -/
structure UserSymb where
  idx : ℕ
  deriving DecidableEq

/-- The injection `UserSymb ↪ VarSymb`. -/
def UserSymb.toVar (u : UserSymb) : VarSymb := .mk u.idx

theorem UserSymb.toVar_injective : Function.Injective UserSymb.toVar := by
  intro a b h
  cases a; cases b
  simp only [UserSymb.toVar, VarSymb.mk.injEq] at h
  simp [h]

/-- ⭐The disjointness fact the whole design rests on: a user symbol is never a bound symbol. -/
@[simp] theorem UserSymb.toVar_ne_bnd (u : UserSymb) (n : ℕ) : u.toVar ≠ VarSymb.bnd n := by
  simp [UserSymb.toVar]

@[simp] theorem VarSymb.bnd_ne_toVar (u : UserSymb) (n : ℕ) : VarSymb.bnd n ≠ u.toVar :=
  (UserSymb.toVar_ne_bnd u n).symm

/-- One ABOVE a bound symbol's index; user symbols contribute `0`.  Taking the `sup` of this and
    using it directly (no trailing `+1`) makes binder numbering start at `.bnd 0`. -/
def VarSymb.bndCeil : VarSymb → ℕ
  | .bnd n => n + 1
  | .mk _  => 0

/-- Index of a user symbol; bound symbols contribute `0`. -/
def VarSymb.usrIdx : VarSymb → ℕ
  | .mk n  => n
  | .bnd _ => 0

/-! ## Fresh user symbols -/

/-- A user symbol not occurring in `s`.  Note it scans only the `.mk` indices — `.bnd` symbols
    contribute `0` and so cannot force the choice upwards. -/
def UserSymb.fresh (s : Finset VarSymb) : UserSymb :=
  ⟨(s.image VarSymb.usrIdx).sup id + 1⟩

theorem UserSymb.fresh_not_mem (s : Finset VarSymb) : (UserSymb.fresh s).toVar ∉ s := by
  intro hmem
  have h1 : VarSymb.usrIdx (UserSymb.fresh s).toVar ∈ s.image VarSymb.usrIdx :=
    Finset.mem_image.mpr ⟨_, hmem, rfl⟩
  have h2 : VarSymb.usrIdx (UserSymb.fresh s).toVar ≤ (s.image VarSymb.usrIdx).sup id :=
    Finset.le_sup (f := id) h1
  simp only [UserSymb.fresh, UserSymb.toVar, VarSymb.usrIdx] at h2
  omega

/-! ## Variable contexts (unchanged from v10) -/

abbrev VarCtx := Σ' V : Finset (VarSymb × VarType), (∀ v ∈ V, ∀ w ∈ V, v.1 = w.1 → v.2 = w.2)

abbrev VarCtx_to_VarSymbs (V : VarCtx) : Finset VarSymb := V.1.image fun v ↦ v.1

def VarCtx_insert (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) : VarCtx := by
  refine ⟨insert x V.1, ?_⟩
  intro v v_im w w_im one_eq
  rcases Finset.mem_insert.mp v_im with rfl | hv_mem
  · rcases Finset.mem_insert.mp w_im with rfl | hw_mem
    · rfl
    · exfalso; apply hx
      exact Finset.mem_image.mpr ⟨w, hw_mem, one_eq.symm⟩
  · rcases Finset.mem_insert.mp w_im with rfl | hw_mem
    · exfalso; apply hx
      exact Finset.mem_image.mpr ⟨v, hv_mem, one_eq⟩
    · exact V.2 v hv_mem w hw_mem one_eq


-- Wrap every variable's type in VTypeBox
def VarCtx_box (V : VarCtx) : VarCtx := by
  refine ⟨V.1.image (fun ⟨v, S⟩ => (⟨v, S.VTypeBox⟩ : VarSymb × VarType)), ?_⟩
  intro v v_im w w_im one_eq
  have V_uniq := V.2
  rcases Finset.mem_image.mp v_im with ⟨⟨av, aS⟩, hav, hveq⟩
  rcases Finset.mem_image.mp w_im with ⟨⟨bv, bS⟩, hbw, hweq⟩
  have hav1 : av = v.1 := congrArg Prod.fst hveq
  have hbw1 : bv = w.1 := congrArg Prod.fst hweq
  have hab : aS = bS := V_uniq _ hav _ hbw (hav1.trans (one_eq.trans hbw1.symm))
  subst hveq; subst hweq
  exact congrArg VarType.VTypeBox hab


-- One designated witness gets VTypeDia; everything else gets VTypeBox
def VarCtx_dia (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) : VarCtx := by
  refine ⟨insert ⟨x.1, x.2.VTypeDia⟩ (VarCtx_box V).1, ?_⟩
  intro v v_im w w_im one_eq
  have box_uniq := (VarCtx_box V).2
  rcases Finset.mem_insert.mp v_im with rfl | hv_box
  · rcases Finset.mem_insert.mp w_im with rfl | hw_box
    · rfl
    · exfalso; apply hx
      rcases Finset.mem_image.mp hw_box with ⟨⟨bv, bS⟩, hbw, hweq⟩
      exact Finset.mem_image.mpr ⟨⟨bv, bS⟩, hbw, (congrArg Prod.fst hweq).trans one_eq.symm⟩
  · rcases Finset.mem_insert.mp w_im with rfl | hw_box
    · exfalso; apply hx
      rcases Finset.mem_image.mp hv_box with ⟨⟨av, aS⟩, hav, hveq⟩
      exact Finset.mem_image.mpr ⟨⟨av, aS⟩, hav, (congrArg Prod.fst hveq).trans one_eq⟩
    · exact box_uniq v hv_box w hw_box one_eq

/-! ## Further context helpers (verbatim from v10 — independent of the symbol change) -/

def VarCtx_insert_twice (x y : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hy : y.1 ∉ VarCtx_to_VarSymbs V)
    (hxy : x.1 ≠ y.1) : VarCtx := by
  refine ⟨insert x (insert y V.1), ?_⟩
  intro v v_im w w_im one_eq
  rcases Finset.mem_insert.mp v_im with rfl | hv_rest
  · -- v = x
    rcases Finset.mem_insert.mp w_im with rfl | hw_rest
    · rfl
    · rcases Finset.mem_insert.mp hw_rest with rfl | hw_mem
      · exact absurd one_eq hxy
      · exfalso; apply hx; exact Finset.mem_image.mpr ⟨w, hw_mem, one_eq.symm⟩
  · rcases Finset.mem_insert.mp hv_rest with rfl | hv_mem
    · -- v = y
      rcases Finset.mem_insert.mp w_im with rfl | hw_rest
      · exact absurd one_eq.symm hxy
      · rcases Finset.mem_insert.mp hw_rest with rfl | hw_mem
        · rfl
        · exfalso; apply hy; exact Finset.mem_image.mpr ⟨w, hw_mem, one_eq.symm⟩
    · -- v ∈ V.1
      rcases Finset.mem_insert.mp w_im with rfl | hw_rest
      · exfalso; apply hx; exact Finset.mem_image.mpr ⟨v, hv_mem, one_eq⟩
      · rcases Finset.mem_insert.mp hw_rest with rfl | hw_mem
        · exfalso; apply hy; exact Finset.mem_image.mpr ⟨v, hv_mem, one_eq⟩
        · exact V.2 v hv_mem w hw_mem one_eq

-- Two VarCtx values with equal first components are equal
lemma VarCtx_ext (V W : VarCtx) (h : V.1 = W.1) : V = W := by
  obtain ⟨v, pv⟩ := V
  obtain ⟨w, pw⟩ := W
  subst h
  exact congrArg (PSigma.mk v) (proof_irrel pv pw)

/-! ### Helper lemmas for context manipulation -/

-- Erase a typed variable from a VarCtx.
def VarCtx_erase (V : VarCtx) (x : VarSymb × VarType) : VarCtx :=
  ⟨V.1.erase x, fun v hv w hw heq =>
    V.2 v (Finset.erase_subset _ _ hv) w (Finset.erase_subset _ _ hw) heq⟩

-- After erasing ⟨v, T⟩ from V, the symbol v is fresh
-- (because V has at most one entry per first component).
lemma VarCtx_erase_fresh {V : VarCtx} {x : VarSymb × VarType} (hx : x ∈ V.1) :
    x.1 ∉ VarCtx_to_VarSymbs (VarCtx_erase V x) := fun hmem => by
  rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
  exact (Finset.mem_erase.mp hvin).1
    (Prod.ext hveq (V.2 ⟨v, S⟩ (Finset.erase_subset _ _ hvin) x hx hveq))

-- Inserting an erased element restores the original context.
lemma VarCtx_insert_erase {V : VarCtx} {x : VarSymb × VarType} (hx : x ∈ V.1)
    (hx_fresh : x.1 ∉ VarCtx_to_VarSymbs (VarCtx_erase V x)) :
    VarCtx_insert x (VarCtx_erase V x) hx_fresh = V :=
  VarCtx_ext _ _ (Finset.insert_erase hx)

-- VarCtx_to_VarSymbs distributes over insertion.
@[simp] lemma VarCtx_to_VarSymbs_insert (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) :
    VarCtx_to_VarSymbs (VarCtx_insert x V hx) = insert x.1 (VarCtx_to_VarSymbs V) :=
  Finset.image_insert _ _ _

-- Erasing only shrinks the set of symbols.
lemma VarCtx_to_VarSymbs_erase_subset {V : VarCtx} {x : VarSymb × VarType} {v : VarSymb}
    (hmem : v ∈ VarCtx_to_VarSymbs (VarCtx_erase V x)) : v ∈ VarCtx_to_VarSymbs V := by
  rcases Finset.mem_image.mp hmem with ⟨w, hw, hweq⟩
  exact Finset.mem_image.mpr ⟨w, Finset.erase_subset _ _ hw, hweq⟩

-- Combine a "different from the binder" and "fresh in the inner context"
-- to get freshness in the extended context.
lemma not_mem_VarSymbs_insert {x : VarSymb × VarType} {V : VarCtx}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V} {v : VarSymb}
    (hne : v ≠ x.1) (hfresh : v ∉ VarCtx_to_VarSymbs V) :
    v ∉ VarCtx_to_VarSymbs (VarCtx_insert x V hx) := by
  rw [VarCtx_to_VarSymbs_insert]
  exact fun hmem => (Finset.mem_insert.mp hmem).elim hne hfresh

-- Two insertions commute.
lemma VarCtx_insert_comm {a b : VarSymb × VarType} {V : VarCtx}
    {hb : b.1 ∉ VarCtx_to_VarSymbs V} {ha : a.1 ∉ VarCtx_to_VarSymbs V}
    (ha_b : a.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert b V hb))
    (hb_a : b.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert a V ha)) :
    VarCtx_insert a (VarCtx_insert b V hb) ha_b =
      VarCtx_insert b (VarCtx_insert a V ha) hb_a :=
  VarCtx_ext _ _ (Finset.insert_comm _ _ _)

-- Symbol freshness for `VarCtx_insert_twice`.
lemma not_mem_VarSymbs_insert_twice {v₁ v₂ : VarSymb × VarType} {V : VarCtx}
    {hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V} {hv₂ : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1} {v : VarSymb}
    (h_v_ne_v₁ : v ≠ v₁.1) (h_v_ne_v₂ : v ≠ v₂.1)
    (h_v_V : v ∉ VarCtx_to_VarSymbs V) :
    v ∉ VarCtx_to_VarSymbs (VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨w, hw, heq⟩
  rcases Finset.mem_insert.mp hw with rfl | hw2
  · exact h_v_ne_v₁ heq.symm
  · rcases Finset.mem_insert.mp hw2 with rfl | hw3
    · exact h_v_ne_v₂ heq.symm
    · exact h_v_V (Finset.mem_image.mpr ⟨w, hw3, heq⟩)

-- A single insertion commutes with a double insertion.
lemma VarCtx_insert_twice_insert_comm
    {a v₁ v₂ : VarSymb × VarType} {V : VarCtx}
    {ha_V : a.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁_V : v₁.1 ∉ VarCtx_to_VarSymbs V}
    {hv₂_V : v₂.1 ∉ VarCtx_to_VarSymbs V}
    {hv₁v₂ : v₁.1 ≠ v₂.1}
    (ha_twice : a.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert_twice v₁ v₂ V hv₁_V hv₂_V hv₁v₂))
    (hv₁_a : v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert a V ha_V))
    (hv₂_a : v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert a V ha_V)) :
    VarCtx_insert a (VarCtx_insert_twice v₁ v₂ V hv₁_V hv₂_V hv₁v₂) ha_twice =
    VarCtx_insert_twice v₁ v₂ (VarCtx_insert a V ha_V) hv₁_a hv₂_a hv₁v₂ :=
  VarCtx_ext _ _ (by
    change insert a (insert v₁ (insert v₂ V.1)) = insert v₁ (insert v₂ (insert a V.1))
    rw [Finset.insert_comm v₂ a, Finset.insert_comm v₁ a])

-- VarCtx_box distributes over insertion (at the underlying-Finset level).
@[simp] lemma VarCtx_box_fst_insert (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) :
    (VarCtx_box (VarCtx_insert x V hx)).1 =
      insert ⟨x.1, x.2.VTypeBox⟩ (VarCtx_box V).1 := by
  simp [VarCtx_box, VarCtx_insert, Finset.image_insert]

-- Unfolding equation for VarCtx_dia.
lemma VarCtx_dia_fst (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) :
    (VarCtx_dia x V hx).1 = insert ⟨x.1, x.2.VTypeDia⟩ (VarCtx_box V).1 := rfl

/-! ## The canonical bound name

`nextBnd V` is the bound symbol a binder formed AT context `V` receives.  It is a function of `V`
alone — not of the body — which is what makes two formulas built at the same context (e.g. the
antecedent and consequent of `congAll`) choose the SAME binder. -/

/-- The bound LEVEL of a context: one above every bound index it holds.  Binder slots are named
    by this, so it is the single number the whole scheme turns on. -/
def VarCtx.bndLevel (V : VarCtx) : ℕ :=
  ((VarCtx_to_VarSymbs V).image VarSymb.bndCeil).sup id

/-- The canonical bound symbol for a binder introduced at context `V`. -/
def VarCtx.nextBnd (V : VarCtx) : VarSymb := .bnd V.bndLevel

/-- `nextBnd` is fresh for its context. -/
theorem VarCtx.nextBnd_not_mem (V : VarCtx) :
    VarCtx.nextBnd V ∉ VarCtx_to_VarSymbs V := by
  intro hmem
  have h1 : VarSymb.bndCeil (VarCtx.nextBnd V) ∈ (VarCtx_to_VarSymbs V).image VarSymb.bndCeil :=
    Finset.mem_image.mpr ⟨_, hmem, rfl⟩
  have h2 : VarSymb.bndCeil (VarCtx.nextBnd V)
      ≤ ((VarCtx_to_VarSymbs V).image VarSymb.bndCeil).sup id :=
    Finset.le_sup (f := id) h1
  simp only [VarCtx.nextBnd, VarCtx.bndLevel, VarSymb.bndCeil] at h2
  omega

/-- ⭐**The stability property the redesign exists for.**  Weakening by a USER variable does not
    move the canonical bound name — `.mk` symbols contribute `0` to the `sup`.  This is what turns
    `hcomm` (`eqRec` commutes with weakening) into an equality, and what stops `WFF.ctx_ext`'s
    collision branch from ever firing on a user weakening. -/
theorem VarCtx.nextBnd_insert_user (u : UserSymb) (T : VarType) (V : VarCtx)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) :
    VarCtx.nextBnd (VarCtx_insert ⟨u.toVar, T⟩ V hu) = VarCtx.nextBnd V := by
  simp only [VarCtx.nextBnd, VarCtx.bndLevel, VarCtx_to_VarSymbs_insert, Finset.image_insert]
  congr 1
  have : VarSymb.bndCeil u.toVar = 0 := by simp [UserSymb.toVar, VarSymb.bndCeil]
  rw [this]
  simp [Finset.sup_insert]

/-- A canonical bound name is never a user symbol — so a user-supplied variable can never collide
    with a binder, whatever the context contains. -/
theorem VarCtx.nextBnd_ne_user (V : VarCtx) (u : UserSymb) :
    VarCtx.nextBnd V ≠ u.toVar := by
  simp [VarCtx.nextBnd]


/-! ## Inserting binder slots

A binder formed at `V` takes the slot `⟨V.nextBnd, T⟩`.  There is no name to supply and no
freshness obligation to discharge — `nextBnd_not_mem` settles it — which is what makes the
binder constructors of v11 nameless. -/

/-- Extend `V` by the canonical binder slot of type `T`. -/
def VarCtx.insertBnd (T : VarType) (V : VarCtx) : VarCtx :=
  VarCtx_insert ⟨V.nextBnd, T⟩ V (VarCtx.nextBnd_not_mem V)

/-- Extend `V` by two canonical binder slots — `pair_elim` consumes exactly two. -/
def VarCtx.insertBnd2 (T₁ T₂ : VarType) (V : VarCtx) : VarCtx :=
  VarCtx.insertBnd T₂ (VarCtx.insertBnd T₁ V)

@[simp] theorem VarCtx.symbs_insertBnd (T : VarType) (V : VarCtx) :
    VarCtx_to_VarSymbs (VarCtx.insertBnd T V)
      = insert V.nextBnd (VarCtx_to_VarSymbs V) := by
  simp [VarCtx.insertBnd]

/-- The two slots of `insertBnd2` are distinct: the inner one is fresh for the context the outer
    was chosen from, so their indices differ. -/
theorem VarCtx.nextBnd_insertBnd_ne (T : VarType) (V : VarCtx) :
    VarCtx.nextBnd (VarCtx.insertBnd T V) ≠ V.nextBnd := by
  intro h
  exact VarCtx.nextBnd_not_mem (VarCtx.insertBnd T V)
    (h ▸ (VarCtx.symbs_insertBnd T V ▸ Finset.mem_insert_self _ _))

/-- ⭐Binder slots are stable under USER weakening — the property `hcomm` needs, lifted from
    `nextBnd_insert_user` to the slot-insertion form. -/
theorem VarCtx.insertBnd_comm_user (u : UserSymb) (Tu : VarType) (V : VarCtx)
    (hu : u.toVar ∉ VarCtx_to_VarSymbs V) :
    VarCtx.nextBnd (VarCtx_insert ⟨u.toVar, Tu⟩ V hu) = VarCtx.nextBnd V :=
  VarCtx.nextBnd_insert_user u Tu V hu

/-! ## Recognising user symbols

`Term.rename` and friends only ever rename FREE variables, which are user symbols.  They take
`isUsr` hypotheses because the canonical binder slots must be preserved across the rename: erasing
`⟨old, T⟩` from a context and inserting `⟨new, T⟩` leaves `nextBnd` fixed exactly when both are
user symbols. -/

def VarSymb.isUsr : VarSymb → Bool
  | .mk _  => true
  | .bnd _ => false

@[simp] theorem UserSymb.isUsr_toVar (u : UserSymb) : u.toVar.isUsr = true := rfl

@[simp] theorem VarSymb.isUsr_bnd (n : ℕ) : (VarSymb.bnd n).isUsr = false := rfl

/-- A user symbol contributes nothing to the bound-index supremum. -/
theorem VarSymb.bndCeil_of_isUsr {v : VarSymb} (h : v.isUsr = true) : v.bndCeil = 0 := by
  cases v with
  | mk n => rfl
  | bnd n => simp [VarSymb.isUsr] at h

/-- ⭐`nextBnd` is unmoved by inserting a USER variable — the general form of
    `nextBnd_insert_user`, stated for a bare `VarSymb` carrying an `isUsr` proof. -/
theorem VarCtx.nextBnd_insert_isUsr (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hu : x.1.isUsr = true) :
    VarCtx.nextBnd (VarCtx_insert x V hx) = VarCtx.nextBnd V := by
  simp only [VarCtx.nextBnd, VarCtx.bndLevel, VarCtx_to_VarSymbs_insert, Finset.image_insert]
  congr 1
  rw [VarSymb.bndCeil_of_isUsr hu]
  simp [Finset.sup_insert]

/-- ⭐**Binder slots commute with inserting a user variable.**  This is what lets a rename descend
    under a `pair_elim`: erasing `⟨old,T⟩` from the inner context and rebuilding gives back
    *literally the same* canonical slots, because a user insert does not move `nextBnd`. -/
theorem VarCtx.insertBnd_comm_insert (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hu : x.1.isUsr = true) (T : VarType)
    (hx' : x.1 ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T V)) :
    VarCtx.insertBnd T (VarCtx_insert x V hx)
      = VarCtx_insert x (VarCtx.insertBnd T V) hx' := by
  apply VarCtx_ext
  change insert (⟨VarCtx.nextBnd (VarCtx_insert x V hx), T⟩ : VarSymb × VarType)
        (insert x V.1)
     = insert x (insert (⟨VarCtx.nextBnd V, T⟩ : VarSymb × VarType) V.1)
  rw [VarCtx.nextBnd_insert_isUsr x V hx hu]
  exact Finset.insert_comm _ _ _

/-- A user symbol is never the canonical bound name. -/
theorem VarCtx.ne_nextBnd_of_isUsr {v : VarSymb} (h : v.isUsr = true) (V : VarCtx) :
    v ≠ VarCtx.nextBnd V := by
  cases v with
  | mk n => simp [VarCtx.nextBnd]
  | bnd n => simp [VarSymb.isUsr] at h

/-- A user variable stays fresh for a context extended by a binder slot. -/
theorem VarCtx.notMem_insertBnd_of_isUsr {v : VarSymb} (h : v.isUsr = true) (T : VarType)
    {V : VarCtx} (hv : v ∉ VarCtx_to_VarSymbs V) :
    v ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T V) := by
  rw [VarCtx.symbs_insertBnd]
  exact fun hm => (Finset.mem_insert.mp hm).elim (VarCtx.ne_nextBnd_of_isUsr h V) hv

/-- ⭐The two-slot form: `pair_elim`'s binder pair commutes with a user insert.  This is what
    lets `Term.rename` descend into a `pair_elim` body and rebuild with the same slots. -/
theorem VarCtx.insertBnd2_comm_insert (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) (hu : x.1.isUsr = true) (T₁ T₂ : VarType)
    (hx' : x.1 ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd2 T₁ T₂ V)) :
    VarCtx.insertBnd2 T₁ T₂ (VarCtx_insert x V hx)
      = VarCtx_insert x (VarCtx.insertBnd2 T₁ T₂ V) hx' := by
  have h1 : x.1 ∉ VarCtx_to_VarSymbs (VarCtx.insertBnd T₁ V) :=
    VarCtx.notMem_insertBnd_of_isUsr hu T₁ hx
  have step1 : VarCtx.insertBnd T₁ (VarCtx_insert x V hx)
      = VarCtx_insert x (VarCtx.insertBnd T₁ V) h1 :=
    VarCtx.insertBnd_comm_insert x V hx hu T₁ h1
  change VarCtx.insertBnd T₂ (VarCtx.insertBnd T₁ (VarCtx_insert x V hx)) = _
  rw [step1]
  exact VarCtx.insertBnd_comm_insert x (VarCtx.insertBnd T₁ V) h1 hu T₂ hx'

/-! ## Shifting bound slots

When a BOUND slot is inserted into a context — which happens when substitution descends under a
binder — every existing slot at or above the insertion level must move up by one.  This is de
Bruijn shifting, and it is a different operation from `rename`: `rename` moves USER variables and
leaves slots fixed, `shiftBnd` moves slots and leaves user variables fixed.

Because binders always take `nextBnd`, insertions are always at the canonical next position, so the
offset is always `+1` at a known level — never arbitrary renumbering. -/

/-- Shift one symbol: bound indices at or above `k` move up by one; user symbols are untouched. -/
def VarSymb.shiftBnd (k : ℕ) : VarSymb → VarSymb
  | .mk n  => .mk n
  | .bnd i => .bnd (if k ≤ i then i + 1 else i)

@[simp] theorem VarSymb.shiftBnd_mk (k n : ℕ) :
    VarSymb.shiftBnd k (.mk n) = .mk n := rfl

@[simp] theorem VarSymb.shiftBnd_isUsr (k : ℕ) (v : VarSymb) :
    (VarSymb.shiftBnd k v).isUsr = v.isUsr := by
  cases v <;> simp [VarSymb.shiftBnd, VarSymb.isUsr]

/-- Shifting is injective — needed for the context-level image to stay well-formed. -/
theorem VarSymb.shiftBnd_injective (k : ℕ) : Function.Injective (VarSymb.shiftBnd k) := by
  intro a b h
  cases a with
  | mk m => cases b with
    | mk n => simpa [VarSymb.shiftBnd] using h
    | bnd j => simp [VarSymb.shiftBnd] at h
  | bnd i => cases b with
    | mk n => simp [VarSymb.shiftBnd] at h
    | bnd j =>
        simp only [VarSymb.shiftBnd, VarSymb.bnd.injEq] at h ⊢
        by_cases hi : k ≤ i <;> by_cases hj : k ≤ j <;>
          simp only [hi, hj, if_true, if_false] at h <;> omega

/-- A user symbol is fixed by shifting. -/
@[simp] theorem VarSymb.shiftBnd_of_isUsr {v : VarSymb} (h : v.isUsr = true) (k : ℕ) :
    VarSymb.shiftBnd k v = v := by
  cases v with
  | mk n => rfl
  | bnd i => simp [VarSymb.isUsr] at h

/-- Shift a whole context.  Well-formedness survives because `shiftBnd` is injective: two entries
    can only collide after shifting if they collided before. -/
def VarCtx.shiftBnd (k : ℕ) (V : VarCtx) : VarCtx := by
  refine ⟨V.1.image (fun p => (⟨VarSymb.shiftBnd k p.1, p.2⟩ : VarSymb × VarType)), ?_⟩
  intro v hv w hw hsym
  rcases Finset.mem_image.mp hv with ⟨⟨av, aS⟩, hain, haeq⟩
  rcases Finset.mem_image.mp hw with ⟨⟨bv, bS⟩, hbin, hbeq⟩
  subst haeq; subst hbeq
  simp only at hsym ⊢
  exact V.2 _ hain _ hbin (VarSymb.shiftBnd_injective k hsym)

@[simp] theorem VarCtx.shiftBnd_fst (k : ℕ) (V : VarCtx) :
    (VarCtx.shiftBnd k V).1
      = V.1.image (fun p => (⟨VarSymb.shiftBnd k p.1, p.2⟩ : VarSymb × VarType)) := rfl

/-- A user variable is fresh for the shifted context exactly when it was fresh before. -/
theorem VarCtx.notMem_shiftBnd_of_isUsr {v : VarSymb} (h : v.isUsr = true) (k : ℕ)
    {V : VarCtx} (hv : v ∉ VarCtx_to_VarSymbs V) :
    v ∉ VarCtx_to_VarSymbs (VarCtx.shiftBnd k V) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨p, hpin, hpeq⟩
  rcases Finset.mem_image.mp hpin with ⟨q, hqin, hqeq⟩
  subst hqeq
  have hv' : VarSymb.shiftBnd k q.1 = v := hpeq
  have hq : q.1.isUsr = true := by
    have hiso := VarSymb.shiftBnd_isUsr k q.1
    rw [hv'] at hiso
    rw [← hiso]; exact h
  exact hv (Finset.mem_image.mpr ⟨q, hqin, by
    rwa [VarSymb.shiftBnd_of_isUsr hq k] at hv'⟩)

-- Sanity check: binder numbering now starts at `.bnd 0`.
example : VarCtx.nextBnd ⟨∅, by simp⟩ = VarSymb.bnd 0 := by
  simp [VarCtx.nextBnd, VarCtx.bndLevel]

-- And a context holding only a user variable still starts at `.bnd 0`.
example (n : ℕ) (T : VarType) :
    VarCtx.nextBnd ⟨{(⟨VarSymb.mk n, T⟩ : VarSymb × VarType)},
      by
      intro v hv w hw _; rw [Finset.mem_singleton] at hv hw; subst hv; subst hw; rfl⟩ = VarSymb.bnd 0 := by
  simp [VarCtx.nextBnd, VarCtx.bndLevel, VarSymb.bndCeil]

/-! ## Lifting past a binder

Inserting a BOUND slot cannot be factored as "shift the term, then weaken": after shifting, a
term's slots are canonical for the EXTENDED context, so it is no longer well-typed at the old one
(`pair_elim`'s `w₁eq` pins slots to the base context).  Weakening first fails too, since the new
slot collides with the term's existing one.  So it is a single operation — the de Bruijn lift. -/

/-- Lift a context past a binder inserted at level `k`: shift everything at or above `k` up, then
    put the new slot in at `k`. -/
def VarCtx.liftAt (k : ℕ) (T : VarType) (V : VarCtx) : VarCtx :=
  VarCtx_insert ⟨VarSymb.bnd k, T⟩ (VarCtx.shiftBnd k V) (by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨p, hpin, hpeq⟩
    rcases Finset.mem_image.mp hpin with ⟨q, hqin, hqeq⟩
    subst hqeq
    have : VarSymb.shiftBnd k q.1 = VarSymb.bnd k := hpeq
    cases hq : q.1 with
    | mk n => rw [hq] at this; simp [VarSymb.shiftBnd] at this
    | bnd i =>
        rw [hq] at this
        simp only [VarSymb.shiftBnd, VarSymb.bnd.injEq] at this
        by_cases hik : k ≤ i <;> simp only [hik, if_true, if_false] at this <;> omega)

@[simp] theorem VarCtx.liftAt_fst (k : ℕ) (T : VarType) (V : VarCtx) :
    (VarCtx.liftAt k T V).1
      = insert (⟨VarSymb.bnd k, T⟩ : VarSymb × VarType) (VarCtx.shiftBnd k V).1 := rfl

@[simp] theorem VarCtx.symbs_shiftBnd (k : ℕ) (V : VarCtx) :
    VarCtx_to_VarSymbs (VarCtx.shiftBnd k V)
      = (VarCtx_to_VarSymbs V).image (VarSymb.shiftBnd k) := by
  ext v
  simp only [VarCtx_to_VarSymbs, VarCtx.shiftBnd_fst, Finset.mem_image]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q.1, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨⟨VarSymb.shiftBnd k q.1, q.2⟩, ⟨q, hq, rfl⟩, rfl⟩

/-- `bndLevel` as a `sup`, for rewriting. -/
theorem VarCtx.bndLevel_eq (V : VarCtx) :
    VarCtx.bndLevel V = (VarCtx_to_VarSymbs V).sup VarSymb.bndCeil := by
  simp [VarCtx.bndLevel, Finset.sup_image]

/-- ⭐The arithmetic core of lifting: inserting a slot at level `k ≤ bndLevel V` raises the level
    by exactly one. -/
theorem VarCtx.bndLevel_liftAt (k : ℕ) (T : VarType) (V : VarCtx)
    (hk : k ≤ VarCtx.bndLevel V) :
    VarCtx.bndLevel (VarCtx.liftAt k T V) = VarCtx.bndLevel V + 1 := by
  have hsymbs : VarCtx_to_VarSymbs (VarCtx.liftAt k T V)
      = insert (VarSymb.bnd k) ((VarCtx_to_VarSymbs V).image (VarSymb.shiftBnd k)) := by
    simp [VarCtx.liftAt]
  rw [VarCtx.bndLevel_eq, hsymbs, Finset.sup_insert, Finset.sup_image]
  apply le_antisymm
  · apply sup_le
    · simp only [VarSymb.bndCeil]; omega
    · apply Finset.sup_le
      intro v hv
      have hle : VarSymb.bndCeil v ≤ VarCtx.bndLevel V := by
        rw [VarCtx.bndLevel_eq]; exact Finset.le_sup hv
      have : (VarSymb.bndCeil ∘ VarSymb.shiftBnd k) v ≤ VarSymb.bndCeil v + 1 := by
        cases v with
        | mk n => simp [Function.comp, VarSymb.shiftBnd, VarSymb.bndCeil]
        | bnd i => by_cases h : k ≤ i <;>
            simp [Function.comp, VarSymb.shiftBnd, VarSymb.bndCeil, h]
      omega
  · rcases Nat.eq_or_lt_of_le hk with heq | hlt
    · exact le_trans (by simp only [VarSymb.bndCeil]; omega) le_sup_left
    · -- `k < bndLevel V`, so the maximising slot has index ≥ k and shifts up.
      have hne : (VarCtx_to_VarSymbs V).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        rw [VarCtx.bndLevel_eq, hemp] at hlt
        simp at hlt
      obtain ⟨v, hv, hveq⟩ := Finset.exists_mem_eq_sup _ hne VarSymb.bndCeil
      have hvlev : VarSymb.bndCeil v = VarCtx.bndLevel V := by
        rw [VarCtx.bndLevel_eq]; exact hveq.symm
      cases v with
      | mk n => rw [← hvlev] at hlt; simp [VarSymb.bndCeil] at hlt
      | bnd i =>
          have hik : k ≤ i := by
            simp only [VarSymb.bndCeil] at hvlev; omega
          refine le_trans ?_ (le_sup_right (a := VarSymb.bndCeil (VarSymb.bnd k)))
          refine le_trans ?_ (Finset.le_sup (f := VarSymb.bndCeil ∘ VarSymb.shiftBnd k) hv)
          simp only [Function.comp, VarSymb.shiftBnd, VarSymb.bndCeil, hik, if_true]
          simp only [VarSymb.bndCeil] at hvlev
          omega

/-- Shifting preserves non-membership — immediate from injectivity. -/
theorem VarCtx.notMem_shiftBnd (k : ℕ) {x : VarSymb} {V : VarCtx}
    (hx : x ∉ VarCtx_to_VarSymbs V) :
    VarSymb.shiftBnd k x ∉ VarCtx_to_VarSymbs (VarCtx.shiftBnd k V) := by
  rw [VarCtx.symbs_shiftBnd]
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨w, hw, heq⟩
  exact hx (VarSymb.shiftBnd_injective k heq ▸ hw)

/-- Shifting distributes over insertion. -/
theorem VarCtx.shiftBnd_insert (k : ℕ) (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) :
    VarCtx.shiftBnd k (VarCtx_insert x V hx)
      = VarCtx_insert ⟨VarSymb.shiftBnd k x.1, x.2⟩ (VarCtx.shiftBnd k V)
          (VarCtx.notMem_shiftBnd k hx) := by
  apply VarCtx_ext
  change (insert x V.1).image (fun p => (⟨VarSymb.shiftBnd k p.1, p.2⟩ : VarSymb × VarType))
       = insert (⟨VarSymb.shiftBnd k x.1, x.2⟩ : VarSymb × VarType)
           (V.1.image (fun p => (⟨VarSymb.shiftBnd k p.1, p.2⟩ : VarSymb × VarType)))
  rw [Finset.image_insert]

/-- ⭐**Binder slots commute with a lift.**  This is what `Term.liftAt`'s `pair_elim` arm needs:
    lifting the base context and then adding a slot is the same as adding the slot and lifting. -/
theorem VarCtx.insertBnd_liftAt (k : ℕ) (T T' : VarType) (V : VarCtx)
    (hk : k ≤ VarCtx.bndLevel V) :
    VarCtx.insertBnd T' (VarCtx.liftAt k T V)
      = VarCtx.liftAt k T (VarCtx.insertBnd T' V) := by
  apply VarCtx_ext
  have hL : VarCtx.nextBnd (VarCtx.liftAt k T V) = VarSymb.bnd (VarCtx.bndLevel V + 1) := by
    simp [VarCtx.nextBnd, VarCtx.bndLevel_liftAt k T V hk]
  have hshift : VarSymb.shiftBnd k (VarCtx.nextBnd V) = VarSymb.bnd (VarCtx.bndLevel V + 1) := by
    simp only [VarCtx.nextBnd, VarSymb.shiftBnd, VarSymb.bnd.injEq]
    simp [hk]
  change insert (⟨VarCtx.nextBnd (VarCtx.liftAt k T V), T'⟩ : VarSymb × VarType)
           (insert (⟨VarSymb.bnd k, T⟩ : VarSymb × VarType) (VarCtx.shiftBnd k V).1)
       = insert (⟨VarSymb.bnd k, T⟩ : VarSymb × VarType)
           (VarCtx.shiftBnd k (VarCtx_insert ⟨VarCtx.nextBnd V, T'⟩ V
              (VarCtx.nextBnd_not_mem V))).1
  rw [hL, VarCtx.shiftBnd_insert]
  change insert (⟨VarSymb.bnd (VarCtx.bndLevel V + 1), T'⟩ : VarSymb × VarType)
           (insert (⟨VarSymb.bnd k, T⟩ : VarSymb × VarType) (VarCtx.shiftBnd k V).1)
       = insert (⟨VarSymb.bnd k, T⟩ : VarSymb × VarType)
           (insert (⟨VarSymb.shiftBnd k (VarCtx.nextBnd V), T'⟩ : VarSymb × VarType)
             (VarCtx.shiftBnd k V).1)
  rw [hshift]
  exact Finset.insert_comm _ _ _

/-- Adding a binder slot raises the level by one. -/
theorem VarCtx.bndLevel_insertBnd (T : VarType) (V : VarCtx) :
    VarCtx.bndLevel (VarCtx.insertBnd T V) = VarCtx.bndLevel V + 1 := by
  rw [VarCtx.bndLevel_eq, VarCtx.bndLevel_eq]
  have : VarCtx_to_VarSymbs (VarCtx.insertBnd T V)
      = insert (VarCtx.nextBnd V) (VarCtx_to_VarSymbs V) := VarCtx.symbs_insertBnd T V
  rw [this, Finset.sup_insert]
  have hceil : VarSymb.bndCeil (VarCtx.nextBnd V)
      = (VarCtx_to_VarSymbs V).sup VarSymb.bndCeil + 1 := by
    simp [VarCtx.nextBnd, VarSymb.bndCeil, VarCtx.bndLevel_eq]
  rw [hceil]
  omega

/-- ⭐The two-slot form, for `pair_elim`. -/
theorem VarCtx.insertBnd2_liftAt (k : ℕ) (T T₁ T₂ : VarType) (V : VarCtx)
    (hk : k ≤ VarCtx.bndLevel V) :
    VarCtx.insertBnd2 T₁ T₂ (VarCtx.liftAt k T V)
      = VarCtx.liftAt k T (VarCtx.insertBnd2 T₁ T₂ V) := by
  have hk1 : k ≤ VarCtx.bndLevel (VarCtx.insertBnd T₁ V) := by
    rw [VarCtx.bndLevel_insertBnd]; omega
  change VarCtx.insertBnd T₂ (VarCtx.insertBnd T₁ (VarCtx.liftAt k T V)) = _
  rw [VarCtx.insertBnd_liftAt k T T₁ V hk, VarCtx.insertBnd_liftAt k T T₂ _ hk1]
  rfl

/-! ## Context maps

Slot names are functions of the context, so ANY change of context forces every binder's slot to be
recomputed from its new base.  A uniform "shift by one" does not do this: a `pair_elim` removes `z`
from its base context, so different nodes sit at different levels and move by different amounts.

The operation that IS correct is to rebuild along a **context map** — an injective, type-preserving
map on symbols — extending it at each binder by (old slot ↦ new slot).  Weakening, renaming and
lifting are all instances. -/

/-- An injective, type-preserving map of `V`'s symbols into `V'`. -/
structure CtxMap (V V' : VarCtx) where
  f : VarSymb → VarSymb
  inj : ∀ a ∈ VarCtx_to_VarSymbs V, ∀ b ∈ VarCtx_to_VarSymbs V, f a = f b → a = b
  maps : ∀ p ∈ V.1, (⟨f p.1, p.2⟩ : VarSymb × VarType) ∈ V'.1

/-- Update a map at one point. -/
def VarSymb.update (f : VarSymb → VarSymb) (a b : VarSymb) : VarSymb → VarSymb :=
  fun v => if v = a then b else f v

@[simp] theorem VarSymb.update_self (f : VarSymb → VarSymb) (a b : VarSymb) :
    VarSymb.update f a b a = b := by simp [VarSymb.update]

@[simp] theorem VarSymb.update_of_ne (f : VarSymb → VarSymb) {a b v : VarSymb} (h : v ≠ a) :
    VarSymb.update f a b v = f v := by simp [VarSymb.update, h]

/-- Extend a context map past a binder: the old slot goes to the new one. -/
def CtxMap.extendBnd {V V' : VarCtx} (m : CtxMap V V') (T : VarType) :
    CtxMap (VarCtx.insertBnd T V) (VarCtx.insertBnd T V') where
  f := VarSymb.update m.f V.nextBnd V'.nextBnd
  inj := by
    have key : ∀ c ∈ VarCtx_to_VarSymbs V,
        VarSymb.update m.f V.nextBnd V'.nextBnd c = m.f c := by
      intro c hc
      have hne : c ≠ V.nextBnd := by
        intro h; subst h; exact VarCtx.nextBnd_not_mem V hc
      exact VarSymb.update_of_ne _ hne
    have hfresh : ∀ c ∈ VarCtx_to_VarSymbs V, m.f c ≠ V'.nextBnd := by
      intro c hc hcon
      rcases Finset.mem_image.mp hc with ⟨p, hp, hpeq⟩
      apply VarCtx.nextBnd_not_mem V'
      refine Finset.mem_image.mpr ⟨⟨m.f p.1, p.2⟩, m.maps p hp, ?_⟩
      simp only
      rw [hpeq]; exact hcon
    intro a ha b hb hab
    rw [VarCtx.symbs_insertBnd] at ha hb
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · rfl
      · rw [VarSymb.update_self, key b hb'] at hab
        exact absurd hab.symm (hfresh b hb')
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · rw [VarSymb.update_self, key a ha'] at hab
        exact absurd hab (hfresh a ha')
      · rw [key a ha', key b hb'] at hab
        exact m.inj a ha' b hb' hab
  maps := by
    intro p hp
    change p ∈ insert (⟨V.nextBnd, T⟩ : VarSymb × VarType) V.1 at hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · simp only [VarSymb.update_self]
      exact Finset.mem_insert_self _ _
    · have hne : p.1 ≠ V.nextBnd := by
        intro h
        exact VarCtx.nextBnd_not_mem V (h ▸ Finset.mem_image.mpr ⟨p, hp', rfl⟩)
      rw [VarSymb.update_of_ne _ hne]
      exact Finset.mem_insert_of_mem (m.maps p hp')

/-- A context map that is also ONTO.  The modal arms need this: a `boxterm`'s inner context is
    determined by the outer one (`h_no_box_extras` pins it), so to rebuild the term the target's
    box-typed part must be exactly the image — which a merely injective map does not give.
    Renaming and shifting are bijections; WEAKENING is not, and is handled separately. -/
structure CtxBij (V V' : VarCtx) extends CtxMap V V' where
  onto : ∀ p ∈ V'.1, ∃ q ∈ V.1, (⟨toCtxMap.f q.1, q.2⟩ : VarSymb × VarType) = p

/-- Extend a bijection past a binder. -/
def CtxBij.extendBnd {V V' : VarCtx} (m : CtxBij V V') (T : VarType) :
    CtxBij (VarCtx.insertBnd T V) (VarCtx.insertBnd T V') where
  toCtxMap := m.toCtxMap.extendBnd T
  onto := by
    intro p hp
    change p ∈ insert (⟨V'.nextBnd, T⟩ : VarSymb × VarType) V'.1 at hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · refine ⟨⟨V.nextBnd, T⟩, Finset.mem_insert_self _ _, ?_⟩
      simp [CtxMap.extendBnd]
    · obtain ⟨q, hq, hqeq⟩ := m.onto p hp'
      refine ⟨q, Finset.mem_insert_of_mem hq, ?_⟩
      have hne : q.1 ≠ V.nextBnd := by
        intro h
        exact VarCtx.nextBnd_not_mem V (h ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      simpa [CtxMap.extendBnd, VarSymb.update_of_ne _ hne] using hqeq

/-- Restrict a bijection along an erase.  This is what `pair_elim`'s arm needs: the node's base
    context is the ambient one minus the pair variable `z`, on both sides. -/
def CtxBij.eraseAt {V V' : VarCtx} (m : CtxBij V V') (x : VarSymb × VarType) (hx : x ∈ V.1) :
    CtxBij (VarCtx_erase V x) (VarCtx_erase V' ⟨m.toCtxMap.f x.1, x.2⟩) where
  f := m.toCtxMap.f
  inj := by
    intro a ha b hb hab
    exact m.toCtxMap.inj a (VarCtx_to_VarSymbs_erase_subset ha)
      b (VarCtx_to_VarSymbs_erase_subset hb) hab
  maps := by
    intro p hp
    have hpV : p ∈ V.1 := Finset.erase_subset _ _ hp
    have hpx : p ≠ x := (Finset.mem_erase.mp hp).1
    refine Finset.mem_erase.mpr ⟨?_, m.toCtxMap.maps p hpV⟩
    intro hcon
    apply hpx
    obtain ⟨h1, h2⟩ := Prod.mk.inj hcon
    have hp1 : p.1 = x.1 := m.toCtxMap.inj p.1 (Finset.mem_image.mpr ⟨p, hpV, rfl⟩)
      x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩) h1
    exact Prod.ext hp1 h2
  onto := by
    intro p hp
    have hpV' : p ∈ V'.1 := Finset.erase_subset _ _ hp
    have hpx : p ≠ ⟨m.toCtxMap.f x.1, x.2⟩ := (Finset.mem_erase.mp hp).1
    obtain ⟨q, hq, hqeq⟩ := m.onto p hpV'
    refine ⟨q, Finset.mem_erase.mpr ⟨?_, hq⟩, hqeq⟩
    intro hcon
    exact hpx (by rw [← hqeq, hcon])

/-- Restrict a bijection whose SOURCE is an insertion.  Stated this way (rather than via
    `eraseAt` plus a transport) because the freshness proof `hz` depends on `pe_V`, which makes
    the rewrite motive ill-typed. -/
def CtxBij.restrictInsert {pe_V V' : VarCtx} {z : VarSymb} {T : VarType}
    (hz : z ∉ VarCtx_to_VarSymbs pe_V)
    (m : CtxBij (VarCtx_insert ⟨z, T⟩ pe_V hz) V') :
    CtxBij pe_V (VarCtx_erase V' ⟨m.toCtxMap.f z, T⟩) where
  f := m.toCtxMap.f
  inj := by
    intro a ha b hb hab
    refine m.toCtxMap.inj a ?_ b ?_ hab <;>
      · rw [VarCtx_to_VarSymbs_insert]
        exact Finset.mem_insert_of_mem (by assumption)
  maps := by
    intro p hp
    have hpins : p ∈ (VarCtx_insert ⟨z, T⟩ pe_V hz).1 := Finset.mem_insert_of_mem hp
    refine Finset.mem_erase.mpr ⟨?_, m.toCtxMap.maps p hpins⟩
    intro hcon
    obtain ⟨h1, _⟩ := Prod.mk.inj hcon
    have hpz : p.1 = z := by
      refine m.toCtxMap.inj p.1 ?_ z ?_ h1
      · rw [VarCtx_to_VarSymbs_insert]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      · rw [VarCtx_to_VarSymbs_insert]
        exact Finset.mem_insert_self _ _
    exact hz (hpz ▸ Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  onto := by
    intro p hp
    have hpV' : p ∈ V'.1 := Finset.erase_subset _ _ hp
    have hpne : p ≠ ⟨m.toCtxMap.f z, T⟩ := (Finset.mem_erase.mp hp).1
    obtain ⟨q, hq, hqeq⟩ := m.onto p hpV'
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact absurd hqeq.symm hpne
    · exact ⟨q, hq', hqeq⟩

/-! ## Images of sub-contexts

A `boxterm`'s inner context is a sub-context of the ambient one (every `⟨v,T⟩` inside appears as
`⟨v, □T⟩` outside), so a bijection on the ambient context carries it to a determined image. -/

/-- The image of a sub-context under a context bijection. -/
def CtxBij.imageCtx {V V' : VarCtx} (m : CtxBij V V') (U : VarCtx)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V) : VarCtx := by
  refine ⟨U.1.image (fun p => (⟨m.toCtxMap.f p.1, p.2⟩ : VarSymb × VarType)), ?_⟩
  intro a ha b hb hab
  rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
  simp only at hab ⊢
  have hpq : p.1 = q.1 :=
    m.toCtxMap.inj p.1 (hU _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
      q.1 (hU _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)) hab
  exact U.2 p hp q hq hpq

@[simp] theorem CtxBij.imageCtx_fst {V V' : VarCtx} (m : CtxBij V V') (U : VarCtx)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V) :
    (m.imageCtx U hU).1
      = U.1.image (fun p => (⟨m.toCtxMap.f p.1, p.2⟩ : VarSymb × VarType)) := rfl

/-- The bijection from a sub-context onto its image. -/
def CtxBij.toImage {V V' : VarCtx} (m : CtxBij V V') (U : VarCtx)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V) :
    CtxBij U (m.imageCtx U hU) where
  f := m.toCtxMap.f
  inj := fun a ha b hb hab => m.toCtxMap.inj a (hU a ha) b (hU b hb) hab
  maps := fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩
  onto := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, hqeq⟩
    exact ⟨q, hq, hqeq⟩

/-- A `boxterm`'s inner context has all its symbols in the ambient context. -/
theorem VarCtx.symbs_of_box_sub {U V : VarCtx} (hsub : (VarCtx_box U).1 ⊆ V.1) :
    ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  exact Finset.mem_image.mpr ⟨⟨p.1, p.2.VTypeBox⟩,
    hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩), rfl⟩

/-- Extend a sub-context bijection by one mapped point — for `diaterm`, whose witness `x` is a
    PROMOTED FREE variable sitting on top of the inner context. -/
def CtxBij.extendPoint {V V' : VarCtx} (m : CtxBij V V') (U : VarCtx)
    (hU : ∀ v ∈ VarCtx_to_VarSymbs U, v ∈ VarCtx_to_VarSymbs V)
    (x : VarSymb × VarType) (hxV : x.1 ∈ VarCtx_to_VarSymbs V)
    (hx : x.1 ∉ VarCtx_to_VarSymbs U)
    (hx' : m.toCtxMap.f x.1 ∉ VarCtx_to_VarSymbs (m.imageCtx U hU)) :
    CtxBij (VarCtx_insert x U hx)
      (VarCtx_insert ⟨m.toCtxMap.f x.1, x.2⟩ (m.imageCtx U hU) hx') where
  f := m.toCtxMap.f
  inj := by
    intro a ha b hb hab
    rw [VarCtx_to_VarSymbs_insert] at ha hb
    have hmem : ∀ c, c ∈ insert x.1 (VarCtx_to_VarSymbs U) → c ∈ VarCtx_to_VarSymbs V := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact hxV
      · exact hU c hc'
    exact m.toCtxMap.inj a (hmem a ha) b (hmem b hb) hab
  maps := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp', rfl⟩)
  onto := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact ⟨x, Finset.mem_insert_self _ _, rfl⟩
    · rcases Finset.mem_image.mp hp' with ⟨q, hq, hqeq⟩
      exact ⟨q, Finset.mem_insert_of_mem hq, hqeq⟩

/-! ## Renaming as a bijection

Renaming one free variable is just a context BIJECTION, so it needs no separate traversal —
`Term.mapCtx` along `CtxBij.renameOne` does it.  Note this needs no `isUsr` hypothesis: those
existed only to keep binder slots FIXED, and `mapCtx` recomputes them instead. -/

/-- Swap one variable's name: `V + ⟨old,T⟩  ≅  V + ⟨new,T⟩`. -/
def CtxBij.renameOne {V : VarCtx} (old new : VarSymb) (T : VarType)
    (hold : old ∉ VarCtx_to_VarSymbs V) (hnew : new ∉ VarCtx_to_VarSymbs V) :
    CtxBij (VarCtx_insert ⟨old, T⟩ V hold) (VarCtx_insert ⟨new, T⟩ V hnew) where
  f := VarSymb.update id old new
  inj := by
    intro a ha b hb hab
    rw [VarCtx_to_VarSymbs_insert] at ha hb
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · rfl
      · have hbne : b ≠ a := fun h => hold (h ▸ hb')
        rw [VarSymb.update_self, VarSymb.update_of_ne _ hbne] at hab
        exact absurd (hab ▸ hb' : new ∈ VarCtx_to_VarSymbs V) hnew
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · have hane : a ≠ b := fun h => hold (h ▸ ha')
        rw [VarSymb.update_self, VarSymb.update_of_ne _ hane] at hab
        exact absurd (hab ▸ ha' : new ∈ VarCtx_to_VarSymbs V) hnew
      · have hane : a ≠ old := fun h => hold (h ▸ ha')
        have hbne : b ≠ old := fun h => hold (h ▸ hb')
        rwa [VarSymb.update_of_ne _ hane, VarSymb.update_of_ne _ hbne] at hab
  maps := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · simp only [VarSymb.update_self]
      exact Finset.mem_insert_self _ _
    · have hne : p.1 ≠ old := fun h => hold (h ▸ Finset.mem_image.mpr ⟨p, hp', rfl⟩)
      rw [VarSymb.update_of_ne _ hne]
      exact Finset.mem_insert_of_mem hp'
  onto := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact ⟨⟨old, T⟩, Finset.mem_insert_self _ _, by simp [VarSymb.update_self]⟩
    · refine ⟨p, Finset.mem_insert_of_mem hp', ?_⟩
      have hne : p.1 ≠ old := fun h => hold (h ▸ Finset.mem_image.mpr ⟨p, hp', rfl⟩)
      rw [VarSymb.update_of_ne _ hne]
      rfl
