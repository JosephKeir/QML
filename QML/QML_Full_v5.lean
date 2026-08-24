import Mathlib

/-!
# Quantified Modal Logic: Natural Deduction (v4)

Redesign from v3. Key changes:

  · `VarCtx` changed from `List (VarSymb × VarType)` to `Finset (VarSymb × VarType)`.
    The `exch` structural rule is thereby eliminated (Finset context has no ordering).
    `wk` remains as a Term constructor; it is needed because modal context changes
    (boxterm/diaterm) produce specific Finset shapes that may need to be enlarged.

  · `GlobalTerm σ τ` is a new context-free term type indexed by `VarType`.
    `Term.toGlobal` maps any term to its global representative, making `wk`
    transparent. `DecidableEq (GlobalTerm σ τ)` derives trivially and is the basis
    for term equality in substitution and equality elimination.
    α-equivalence for `pair_elim` binders is handled by `GlobalTerm.AlphaEq`.
    The `pair_elim` scrutinee is a `GlobalTerm σ (.VTypeProd v₁.2 v₂.2)`, enforcing
    that only pair-typed terms can be destructured.

  · `DecidableEq (Term σ V S)` is dropped. Term equality uses `Term.toGlobal`.

  · `box_VarCtx` and `dia_VarCtx` are now Finset operations:
        box_VarCtx V  = V.image (fun ⟨v,S⟩ => ⟨v, S.VTypeBox⟩)
        dia_VarCtx x V = insert ⟨x.1, x.2.VTypeDia⟩ (box_VarCtx V)

  · Modal terms are formed exclusively via `boxterm` and `diaterm`:
        boxterm : Term σ V S             → Term σ (box_VarCtx V) (VTypeBox S)
        diaterm : Term σ (insert x V) S  → Term σ (dia_VarCtx x V) (VTypeDia S)
-/

/-! ## Modalities (kept for documentation; not used in core v4 definitions) -/

inductive Modality : Type where
  | box : Modality
  | dia : Modality
  deriving DecidableEq

/-! ## Signature -/

structure Signature where
  FuncSyms  : Type
  RelSyms   : Type
  funcArity : FuncSyms → ℕ
  relArity  : RelSyms  → ℕ
  [decEqF   : DecidableEq FuncSyms]
  [decEqR   : DecidableEq RelSyms]

attribute [instance] Signature.decEqF Signature.decEqR

/-! ## Variable Types -/

inductive VarType where
  | Var     : VarType
  | VTypeBox  : VarType → VarType
  | VTypeDia  : VarType → VarType
  | VTypeOne  : VarType                      -- nullary product / trivial dia witness
  | VTypeProd : VarType → VarType → VarType  -- binary product
  deriving DecidableEq

-- Bool test: does this type have `.VTypeBox` as its outermost constructor?
-- With pairs, this tests to see if *any* of the outermost constructors are `.VTypeBox`.
def VarType.isBox : VarType → Bool
  | .VTypeBox _ => true
  | .VTypeProd V₁ V₂ => VarType.isBox V₁ ∨ VarType.isBox V₂
  | _           => false

-- Injective encoding of VarType to ℕ. Used to derive a LinearOrder on
-- (VarSymb × VarType), which is used by `VarCtx.firstPairVar` to extract a
-- pair-typed binder deterministically (via `Finset.sort`, avoiding the
-- noncomputable `Finset.toList`).
-- Encoding: constructor index determines value mod 5, recursive arguments are
-- packed into the higher bits via `Nat.pair`.
def VarType.encode : VarType → ℕ
  | .Var            => 0
  | .VTypeOne       => 1
  | .VTypeBox a     => 5 * a.encode + 2
  | .VTypeDia a     => 5 * a.encode + 3
  | .VTypeProd a b  => 5 * Nat.pair a.encode b.encode + 4

theorem VarType.encode_injective : Function.Injective VarType.encode := by
  intro a
  induction a with
  | Var =>
      intro b heq
      cases b with
      | Var => rfl
      | VTypeOne => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeBox _ => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeDia _ => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeProd _ _ => exact absurd heq (by simp only [VarType.encode]; omega)
  | VTypeOne =>
      intro b heq
      cases b with
      | Var => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeOne => rfl
      | VTypeBox _ => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeDia _ => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeProd _ _ => exact absurd heq (by simp only [VarType.encode]; omega)
  | VTypeBox a ih =>
      intro b heq
      cases b with
      | Var => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeOne => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeBox a' =>
          have h_inner : a.encode = a'.encode := by
            have : VarType.encode (.VTypeBox a) = VarType.encode (.VTypeBox a') := heq
            simp [VarType.encode] at this; omega
          exact congrArg _ (ih h_inner)
      | VTypeDia _ => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeProd _ _ => exact absurd heq (by simp only [VarType.encode]; omega)
  | VTypeDia a ih =>
      intro b heq
      cases b with
      | Var => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeOne => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeBox _ => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeDia a' =>
          have h_inner : a.encode = a'.encode := by
            have : VarType.encode (.VTypeDia a) = VarType.encode (.VTypeDia a') := heq
            simp [VarType.encode] at this; omega
          exact congrArg _ (ih h_inner)
      | VTypeProd _ _ => exact absurd heq (by simp only [VarType.encode]; omega)
  | VTypeProd a b iha ihb =>
      intro c heq
      cases c with
      | Var => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeOne => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeBox _ => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeDia _ => exact absurd heq (by simp only [VarType.encode]; omega)
      | VTypeProd a' b' =>
          have hpair : Nat.pair a.encode b.encode = Nat.pair a'.encode b'.encode := by
            have h_unfolded :
                5 * Nat.pair a.encode b.encode + 4 = 5 * Nat.pair a'.encode b'.encode + 4 := heq
            omega
          have h_un := congrArg Nat.unpair hpair
          simp only [Nat.unpair_pair, Prod.ext_iff] at h_un
          rw [iha h_un.1, ihb h_un.2]

/-! ## Variable Symbols -/

inductive VarSymb : Type where
  | mk : ℕ → VarSymb
  deriving DecidableEq

def VarSymb.toNat : VarSymb → ℕ
  | .mk n => n

-- Produce a VarSymb not in `s` by taking one larger than every nat used in `s`.
def VarSymb.fresh (s : Finset VarSymb) : VarSymb :=
  .mk ((s.image VarSymb.toNat).sup id + 1)

lemma VarSymb.fresh_not_mem (s : Finset VarSymb) : VarSymb.fresh s ∉ s := by
  intro hmem
  have h1 : (VarSymb.fresh s).toNat ∈ s.image VarSymb.toNat :=
    Finset.mem_image.mpr ⟨_, hmem, rfl⟩
  have h2 : (VarSymb.fresh s).toNat ≤ (s.image VarSymb.toNat).sup id :=
    Finset.le_sup (f := id) h1
  simp only [VarSymb.fresh, VarSymb.toNat] at h2
  omega

/-! ## Variable Contexts -/

-- A finite set of the available variables, paired with their types.
-- Variable symbols are required to have a unique associated type.
abbrev VarCtx := Σ' V : Finset (VarSymb × VarType), (∀ v ∈ V, ∀ w ∈ V, v.1 = w.1 → v.2 = w.2)

-- Extract the set of variable sybols
abbrev VarCtx_to_VarSymbs (V : VarCtx) : Finset VarSymb := V.1.image fun v ↦ v.1

-- Wrap every variable's type in VTypeBox
def box_VarCtx (V : VarCtx) : VarCtx := by
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
def dia_VarCtx (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) : VarCtx := by
  refine ⟨insert ⟨x.1, x.2.VTypeDia⟩ (box_VarCtx V).1, ?_⟩
  intro v v_im w w_im one_eq
  have box_uniq := (box_VarCtx V).2
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


/-! ## Terms -/

mutual
  inductive Func (σ : Signature) : VarCtx → ℕ → Type where
    | F    : {f : σ.FuncSyms // σ.funcArity f = n} → Func σ V n
    | eval : Func σ V (Nat.succ n) → Term σ V .Var → Func σ V n
    deriving DecidableEq

-- `Term σ V S`: a term of VarType S with free variables drawn from VarCtx V.
  inductive Term (σ : Signature) : VarCtx → VarType → Type where
    | var       : {v : VarSymb // ⟨v, S⟩ ∈ V.1} → Term σ V S
    | func      : Func σ V 0 → Term σ V .Var
    | boxterm   : Term σ V S → (hsub : (box_VarCtx V).1 ⊆ W.1) →
                  (h_no_box_extras :
                    ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (box_VarCtx V).1) →
                  Term σ W S.VTypeBox
    | diaterm   : (x : VarSymb × VarType) → (hx : x.1 ∉ VarCtx_to_VarSymbs V) →
                  Term σ (VarCtx_insert x V hx) S →
                  (hsub : (dia_VarCtx x V hx).1 ⊆ W.1) →
                  (h_no_box_extras :
                    ∀ p ∈ W.1, VarType.isBox p.2 = true → p ∈ (dia_VarCtx x V hx).1) →
                  Term σ W S.VTypeDia
    | unit      : Term σ V .VTypeOne
    | pair      : Term σ V S → Term σ V T → Term σ V (.VTypeProd S T)
    | pair_elim : (v₁ v₂ : VarSymb × VarType) → (z : VarSymb) →
                  (hv₁ : v₁.1 ∉ VarCtx_to_VarSymbs V) → (hv₂: v₂.1 ∉ VarCtx_to_VarSymbs V) →
                  (hv₁v₂ : v₁.1 ≠ v₂.1) → (hz : z ∉ VarCtx_to_VarSymbs V) →
                  VarCtx_insert_twice v₁ v₂ V hv₁ hv₂ hv₁v₂ = W₁ →
                  VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V hz = W₂ →
                  Term σ W₁ S →
                  Term σ W₂ S
  deriving DecidableEq
end

-- Two VarCtx values with equal first components are equal
private lemma VarCtx_ext (V W : VarCtx) (h : V.1 = W.1) : V = W := by
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

-- box_VarCtx distributes over insertion (at the underlying-Finset level).
@[simp] lemma box_VarCtx_fst_insert (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) :
    (box_VarCtx (VarCtx_insert x V hx)).1 =
      insert ⟨x.1, x.2.VTypeBox⟩ (box_VarCtx V).1 := by
  simp [box_VarCtx, VarCtx_insert, Finset.image_insert]

-- Unfolding equation for dia_VarCtx.
lemma dia_VarCtx_fst (x : VarSymb × VarType) (V : VarCtx)
    (hx : x.1 ∉ VarCtx_to_VarSymbs V) :
    (dia_VarCtx x V hx).1 = insert ⟨x.1, x.2.VTypeDia⟩ (box_VarCtx V).1 := rfl

-- `box_VarCtx` is injective: if two contexts have equal box-wraps, they're equal.
lemma box_VarCtx_inj {V₁ V₂ : VarCtx} (h : box_VarCtx V₁ = box_VarCtx V₂) :
    V₁ = V₂ := by
  apply VarCtx_ext
  have h1 : (box_VarCtx V₁).1 = (box_VarCtx V₂).1 := congrArg PSigma.fst h
  have h_fn_inj :
      Function.Injective (fun (p : VarSymb × VarType) =>
        (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType)) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext hab.1 (VarType.VTypeBox.inj hab.2)
  exact Finset.image_injective h_fn_inj h1

-- Collect the bound variable symbols inside a function/term.
-- Used to require that `new` doesn't clash with any binder when renaming.
mutual
  def Func.boundVars {σ : Signature} {V : VarCtx} {N : ℕ} :
      Func σ V N → Finset VarSymb
    | .F _ => ∅
    | .eval g t => Func.boundVars g ∪ Term.boundVars t

  def Term.boundVars {σ : Signature} {V : VarCtx} {S : VarType} :
      Term σ V S → Finset VarSymb
    | .var _ => ∅
    | .func f => Func.boundVars f
    | .boxterm inner_t _ _ => Term.boundVars inner_t
    | .diaterm x _ inner_t _ _ => insert x.1 (Term.boundVars inner_t)
    | .unit => ∅
    | .pair t1 t2 => Term.boundVars t1 ∪ Term.boundVars t2
    | .pair_elim v₁ v₂ z _ _ _ _ _ _ inner_term =>
        insert v₁.1 (insert v₂.1 (insert z (Term.boundVars inner_term)))
end

-- Count the number of constructors in a function/term. Unlike the auto-derived
-- `sizeOf`, this is invariant under variable renaming: it depends only on the
-- skeletal structure of the term, not on the (possibly varying) sizes of the
-- VarSymb / VarType / proof arguments. Used as the termination measure for
-- `Term.canonicalize`, whose `pair_elim` arm recurses on a body that has been
-- renamed via `Term.rename`.
mutual
  def Func.numNodes {σ : Signature} {V : VarCtx} {N : ℕ} :
      Func σ V N → ℕ
    | .F _      => 1
    | .eval g t => 1 + Func.numNodes g + Term.numNodes t

  def Term.numNodes {σ : Signature} {V : VarCtx} {S : VarType} :
      Term σ V S → ℕ
    | .var _                          => 1
    | .func f                         => 1 + Func.numNodes f
    | .boxterm inner_t _ _            => 1 + Term.numNodes inner_t
    | .diaterm _ _ inner_t _ _        => 1 + Term.numNodes inner_t
    | .unit                           => 1
    | .pair t1 t2                     => 1 + Term.numNodes t1 + Term.numNodes t2
    | .pair_elim _ _ _ _ _ _ _ _ _ b  => 1 + Term.numNodes b
end

-- Rename a variable symbol to another variable symbol inside a function/term
mutual
  def Func.rename {σ : Signature} (old new : VarSymb) (repl_type : VarType)
      (V W : VarCtx) (N : Nat)
      (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
      (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
      (f : Func σ W N) (new_not_bound : new ∉ Func.boundVars f)
      : Func σ (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) N := by
    match f, new_not_bound with
    | .F h, _ => exact .F h
    | .eval g t, h_nb =>
        have h_nb_g : new ∉ Func.boundVars g :=
          fun hmem => h_nb (Finset.mem_union_left _ hmem)
        have h_nb_t : new ∉ Term.boundVars t :=
          fun hmem => h_nb (Finset.mem_union_right _ hmem)
        exact .eval (Func.rename old new repl_type V W _ old_fresh new_fresh Wdef g h_nb_g)
                    (Term.rename old new repl_type V W _ old_fresh new_fresh Wdef t h_nb_t)

  def Term.rename {σ : Signature} (old new : VarSymb) (repl_type : VarType)
      (V W : VarCtx) (S : VarType)
      (old_fresh : old ∉ VarCtx_to_VarSymbs V) (new_fresh : new ∉ VarCtx_to_VarSymbs V)
      (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
      (old_term : Term σ W S) (new_not_bound : new ∉ Term.boundVars old_term)
      : Term σ (VarCtx_insert ⟨new, repl_type⟩ V new_fresh) S := by
    match old_term, new_not_bound with
    | .var ⟨v, veq⟩, _ =>
      if h_v_old : v = old then
        have old_in_W : ⟨old, repl_type⟩ ∈ W.1 := by rw [Wdef]; exact Finset.mem_insert_self _ _
        have hS : S = repl_type := W.2 ⟨v, S⟩ veq ⟨old, repl_type⟩ old_in_W h_v_old
        -- Put the type-equality cast on the membership proof (a Prop), not on
        -- the term, so the returned term is `.var ⟨new, _⟩` syntactically and
        -- `Term.boundVars` reduces cleanly.
        exact .var ⟨new, hS ▸ Finset.mem_insert_self _ _⟩
      else
        have hv_V : ⟨v, S⟩ ∈ V.1 := by
          rw [Wdef] at veq
          rcases Finset.mem_insert.mp veq with heq | hv
          · exact absurd (congrArg Prod.fst heq) h_v_old
          · exact hv
        exact .var ⟨v, Finset.mem_insert_of_mem hv_V⟩
    | .func f, h_nb =>
        exact .func (Func.rename old new repl_type V W _ old_fresh new_fresh Wdef f h_nb)
    | .boxterm inner_t box_context_sub h_box_no_extras, h_nb =>
        rename_i inner_ctx inner_termtype
        rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩
        · -- Var
          refine .boxterm inner_t ?_ (by
            -- New W = insert ⟨new, .Var⟩ V; the added entry is non-box, so the
            -- predicate transfers from the original W via Wdef.
            intro p hp h_box
            rcases Finset.mem_insert.mp hp with h_eq | hp_V
            · subst h_eq; simp [VarType.isBox] at h_box
            · exact h_box_no_extras p (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V)
                h_box)
          have : (box_VarCtx inner_ctx).1 ⊆ V.1 := by
            intro x x_in_box_inner
            rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub x_in_box_inner) with xold | xV
            · rcases xold ▸ Finset.mem_image.mp x_in_box_inner with ⟨w, weq⟩
              have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
              simp only [reduceCtorEq, and_false] at this
            · exact xV
          exact (Finset.subset_insert_iff_of_notMem fun a ↦
            new_fresh (Finset.mem_image.mpr ⟨_, this a, rfl⟩)).mpr this
        · -- VTypeBox: recurse into inner_t if old is bound in inner_ctx, else pass through
          if h : ⟨old, innertype⟩ ∈ inner_ctx.1 then
            let innerCtx' := VarCtx_erase inner_ctx ⟨old, innertype⟩
            have oldinner_fresh : old ∉ VarCtx_to_VarSymbs innerCtx' := VarCtx_erase_fresh h
            have innerCtx_eq : inner_ctx =
                VarCtx_insert ⟨old, innertype⟩ innerCtx' oldinner_fresh :=
              (VarCtx_insert_erase h oldinner_fresh).symm
            have hbox_sub : (box_VarCtx innerCtx').1 ⊆ V.1 := by
              intro y hy
              have hy_inner : y ∈ (box_VarCtx inner_ctx).1 := by
                rcases Finset.mem_image.mp hy with ⟨w, hvin, hveq⟩
                exact Finset.mem_image.mpr ⟨w, Finset.erase_subset _ _ hvin, hveq⟩
              rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub hy_inner) with rfl | hV
              · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, hvin, hveq⟩
                simp only [Prod.mk.injEq] at hveq
                exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, innertype⟩,
                  hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin, rfl⟩)).elim
              · exact hV
            have newinner_fresh : new ∉ VarCtx_to_VarSymbs innerCtx' := fun hmem => by
              rcases Finset.mem_image.mp hmem with ⟨w, hvin, hveq⟩
              exact new_fresh (Finset.mem_image.mpr ⟨⟨w.1, w.2.VTypeBox⟩,
                hbox_sub (Finset.mem_image.mpr ⟨w, hvin, rfl⟩), hveq⟩)
            let renamed_t := Term.rename old new innertype innerCtx' inner_ctx inner_termtype
                                         oldinner_fresh newinner_fresh innerCtx_eq inner_t h_nb
            refine .boxterm renamed_t ?_ (by
              -- New W has ⟨new, innertype.VTypeBox⟩ as the only added box-typed
              -- entry, and that exact entry is in box_VarCtx (insert ⟨new, innertype⟩ innerCtx').
              -- Other box-typed entries in V transfer from box_VarCtx inner_ctx via
              -- h_box_no_extras (after erasing the now-renamed ⟨old, innertype⟩).
              intro p hp h_box
              rw [box_VarCtx_fst_insert]
              rcases Finset.mem_insert.mp hp with h_eq | hp_V
              · subst h_eq
                exact Finset.mem_insert_self _ _
              · have hp1_ne_old : p.1 ≠ old := fun h_eq =>
                  old_fresh (Finset.mem_image.mpr ⟨p, hp_V, h_eq⟩)
                have hp_W : p ∈ W.1 := by
                  rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
                have hp_box_inner : p ∈ (box_VarCtx inner_ctx).1 :=
                  h_box_no_extras p hp_W h_box
                rcases Finset.mem_image.mp hp_box_inner with ⟨⟨v, S⟩, hvS_in, hvS_eq⟩
                have hp_eq_v : p.1 = v := (Prod.mk.inj hvS_eq).1.symm
                have hv_ne_old : v ≠ old := hp_eq_v ▸ hp1_ne_old
                apply Finset.mem_insert_of_mem
                refine Finset.mem_image.mpr ⟨⟨v, S⟩, ?_, hvS_eq⟩
                change ⟨v, S⟩ ∈ (inner_ctx.1.erase _)
                exact Finset.mem_erase.mpr ⟨fun h_eq => hv_ne_old (Prod.mk.inj h_eq).1, hvS_in⟩)
            rw [box_VarCtx_fst_insert]
            exact Finset.insert_subset_insert _ hbox_sub
          else
            -- Under the new no-box-extras constraint, this branch is impossible
            -- (the original W contains ⟨old, .VTypeBox innertype⟩, forcing
            -- ⟨old, innertype⟩ ∈ inner_ctx via h_box_no_extras). We still build
            -- a syntactic boxterm so that downstream `boundVars` reduces; the
            -- impossibility is discharged into the h_no_box_extras proof obligation.
            refine .boxterm inner_t ?_ (by
              exfalso
              have h_old_in_W : (⟨old, innertype.VTypeBox⟩ : VarSymb × VarType) ∈ W.1 := by
                rw [Wdef]; exact Finset.mem_insert_self _ _
              have h_in_box : (⟨old, innertype.VTypeBox⟩ : VarSymb × VarType)
                                ∈ (box_VarCtx inner_ctx).1 :=
                h_box_no_extras _ h_old_in_W rfl
              rcases Finset.mem_image.mp h_in_box with ⟨⟨v, S⟩, hvin, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin))
            have hbox_old_not : ⟨old, innertype.VTypeBox⟩ ∉ (box_VarCtx inner_ctx).1 := by
              intro hmem
              rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
              simp only [Prod.mk.injEq] at hveq
              exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin)
            have hsub : (box_VarCtx inner_ctx).1 ⊆ V.1 := by
              intro y hy
              rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub hy) with rfl | hV
              · exact absurd hy hbox_old_not
              · exact hV
            exact Finset.Subset.trans hsub (Finset.subset_insert _ _)
        -- remaining cases are all the same: VTypeDia, VTyprProd and VTypeOne
        -- For h_no_box_extras: .VTypeDia/.VTypeOne discharge via simp (isBox=false).
        -- .VTypeProd may have isBox=true via recursion through box components;
        -- in that case use h_box_no_extras on ⟨old, repl_type⟩ for contradiction
        -- (box_VarCtx inner_ctx has only .VTypeBox-outer entries).
        all_goals refine .boxterm inner_t ?_ (by
          intro p hp h_box
          rcases Finset.mem_insert.mp hp with h_eq | hp_V
          · subst h_eq
            first
            | (simp [VarType.isBox] at h_box) <;> done
            | (exfalso
               rename_i V1' V2'
               have h_old_W : (⟨old, V1'.VTypeProd V2'⟩ : VarSymb × VarType) ∈ W.1 := by
                 rw [Wdef]; exact Finset.mem_insert_self _ _
               have h_old_in_box := h_box_no_extras _ h_old_W h_box
               rcases Finset.mem_image.mp h_old_in_box with ⟨⟨_, _⟩, _, hveq⟩
               simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq)
          · exact h_box_no_extras p
              (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V) h_box)
        all_goals have : (box_VarCtx inner_ctx).1 ⊆ V.1 := by
          { intro x x_in_box_inner
            rcases Finset.mem_insert.mp (Wdef ▸ box_context_sub x_in_box_inner) with xold | xV
            · rcases xold ▸ Finset.mem_image.mp x_in_box_inner with ⟨w, weq⟩
              have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
              simp only [reduceCtorEq, and_false] at this
            · exact xV
          }
        all_goals exact (Finset.subset_insert_iff_of_notMem fun a ↦
          new_fresh (Finset.mem_image.mpr ⟨_, this a, rfl⟩)).mpr this
    | .diaterm x hx inner_t dia_ctx_sub h_dia_no_extras, h_nb =>
        rename_i inner_ctx inner_type
        match repl_type with
        | .Var | .VTypeOne | .VTypeProd _ _ =>
            -- repl_type is none of VTypeBox/VTypeDia, so ⟨old, repl_type⟩ can't appear
            -- in dia_VarCtx; everything else in dia_VarCtx lies in V.
            refine .diaterm x hx inner_t ?_ (by
              intro p hp h_box
              rcases Finset.mem_insert.mp hp with h_eq | hp_V
              · subst h_eq
                first
                | (simp [VarType.isBox] at h_box) <;> done
                | (exfalso
                   rename_i V1' V2'
                   have h_old_W : (⟨old, V1'.VTypeProd V2'⟩ : VarSymb × VarType) ∈ W.1 := by
                     rw [Wdef]; exact Finset.mem_insert_self _ _
                   have h_old_in_dia := h_dia_no_extras _ h_old_W h_box
                   rcases Finset.mem_insert.mp h_old_in_dia with hxeq | hbox
                   · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
                   · rcases Finset.mem_image.mp hbox with ⟨⟨_, _⟩, _, hveq⟩
                     simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq)
              · exact h_dia_no_extras p
                  (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V) h_box)
            intro y y_in_dia_inner
            rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub y_in_dia_inner) with yold | yV
            · subst yold
              rcases Finset.mem_insert.mp y_in_dia_inner with heq | hmem
              · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
              · rcases Finset.mem_image.mp hmem with ⟨w, weq⟩
                have := Prod.eq_iff_fst_eq_snd_eq.mp weq.2
                simp only [reduceCtorEq, and_false] at this
            · exact Finset.mem_insert_of_mem yV
        | .VTypeBox repl_inner_type =>
            -- VTypeBox: recurse into inner_t if old is bound in inner_ctx, else pass through
            if h : ⟨old, repl_inner_type⟩ ∈ inner_ctx.1 then
              let innerCtx' := VarCtx_erase inner_ctx ⟨old, repl_inner_type⟩
              have oldinner_fresh : old ∉ VarCtx_to_VarSymbs innerCtx' :=
                VarCtx_erase_fresh h
              have hx_ne_old : x.1 ≠ old := fun heq =>
                hx (Finset.mem_image.mpr ⟨⟨old, repl_inner_type⟩, h, heq.symm⟩)
              have hx' : x.1 ∉ VarCtx_to_VarSymbs innerCtx' :=
                fun hmem => hx (VarCtx_to_VarSymbs_erase_subset hmem)
              have hbox_sub : (box_VarCtx innerCtx').1 ⊆ V.1 := by
                intro y hy
                have hy_inner_box : y ∈ (box_VarCtx inner_ctx).1 := by
                  rcases Finset.mem_image.mp hy with ⟨w, hvin, hveq⟩
                  exact Finset.mem_image.mpr ⟨w, Finset.erase_subset _ _ hvin, hveq⟩
                have hy_dia : y ∈ (dia_VarCtx x inner_ctx hx).1 :=
                  Finset.mem_insert_of_mem hy_inner_box
                rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy_dia) with rfl | hV
                · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, hvin, hveq⟩
                  simp only [Prod.mk.injEq] at hveq
                  exact (oldinner_fresh (Finset.mem_image.mpr ⟨⟨old, repl_inner_type⟩,
                    hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin, rfl⟩)).elim
                · exact hV
              have hx1_in_V : ⟨x.1, x.2.VTypeDia⟩ ∈ V.1 := by
                have hx_in_dia : ⟨x.1, x.2.VTypeDia⟩ ∈ (dia_VarCtx x inner_ctx hx).1 :=
                  Finset.mem_insert_self _ _
                rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hx_in_dia) with heq | hV
                · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
                · exact hV
              have hnew_ne_x : new ≠ x.1 := fun heq =>
                new_fresh (Finset.mem_image.mpr
                  ⟨⟨x.1, x.2.VTypeDia⟩, hx1_in_V, heq.symm⟩)
              have newinner_fresh : new ∉ VarCtx_to_VarSymbs innerCtx' := fun hmem => by
                rcases Finset.mem_image.mp hmem with ⟨w, hvin, hveq⟩
                exact new_fresh (Finset.mem_image.mpr ⟨⟨w.1, w.2.VTypeBox⟩,
                  hbox_sub (Finset.mem_image.mpr ⟨w, hvin, rfl⟩), hveq⟩)
              have oldinnerX_fresh :=
                not_mem_VarSymbs_insert (x := x) (hx := hx') hx_ne_old.symm oldinner_fresh
              have newinnerX_fresh :=
                not_mem_VarSymbs_insert (x := x) (hx := hx') hnew_ne_x newinner_fresh
              have hx_target :=
                not_mem_VarSymbs_insert (x := ⟨new, repl_inner_type⟩)
                  (hx := newinner_fresh) hnew_ne_x.symm hx'
              have innerCtx_eq : VarCtx_insert x inner_ctx hx =
                  VarCtx_insert ⟨old, repl_inner_type⟩
                                (VarCtx_insert x innerCtx' hx') oldinnerX_fresh :=
                VarCtx_ext _ _ <| by
                  change insert x inner_ctx.1 =
                       insert ⟨old, repl_inner_type⟩ (insert x innerCtx'.1)
                  rw [← Finset.insert_erase h]; exact Finset.insert_comm _ _ _
              have h_nb_inner : new ∉ Term.boundVars inner_t :=
                fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
              let renamed_t := Term.rename old new repl_inner_type
                                 (VarCtx_insert x innerCtx' hx')
                                 (VarCtx_insert x inner_ctx hx)
                                 inner_type
                                 oldinnerX_fresh newinnerX_fresh innerCtx_eq inner_t h_nb_inner
              have ctx_swap :
                  VarCtx_insert ⟨new, repl_inner_type⟩
                                (VarCtx_insert x innerCtx' hx') newinnerX_fresh =
                  VarCtx_insert x
                    (VarCtx_insert ⟨new, repl_inner_type⟩ innerCtx' newinner_fresh)
                    hx_target :=
                VarCtx_insert_comm _ _
              refine .diaterm x hx_target (ctx_swap ▸ renamed_t) ?_ (by
                intro p hp h_box
                rw [dia_VarCtx_fst, box_VarCtx_fst_insert]
                rcases Finset.mem_insert.mp hp with h_eq | hp_V
                · subst h_eq
                  exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                · have hp1_ne_old : p.1 ≠ old := fun h_eq =>
                    old_fresh (Finset.mem_image.mpr ⟨p, hp_V, h_eq⟩)
                  have hp_W : p ∈ W.1 := by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
                  have hp_dia_inner : p ∈ (dia_VarCtx x inner_ctx hx).1 :=
                    h_dia_no_extras p hp_W h_box
                  rw [dia_VarCtx_fst] at hp_dia_inner
                  rcases Finset.mem_insert.mp hp_dia_inner with hpx | hp_box_inner
                  · subst hpx; simp [VarType.isBox] at h_box
                  · rcases Finset.mem_image.mp hp_box_inner with ⟨⟨v, S⟩, hvS_in, hvS_eq⟩
                    have hp_eq_v : p.1 = v := (Prod.mk.inj hvS_eq).1.symm
                    have hv_ne_old : v ≠ old := hp_eq_v ▸ hp1_ne_old
                    apply Finset.mem_insert_of_mem
                    apply Finset.mem_insert_of_mem
                    refine Finset.mem_image.mpr ⟨⟨v, S⟩, ?_, hvS_eq⟩
                    change ⟨v, S⟩ ∈ inner_ctx.1.erase _
                    exact Finset.mem_erase.mpr
                      ⟨fun h_eq => hv_ne_old (Prod.mk.inj h_eq).1, hvS_in⟩)
              rw [dia_VarCtx_fst, box_VarCtx_fst_insert]
              intro y hy
              rcases Finset.mem_insert.mp hy with rfl | hy'
              · exact Finset.mem_insert_of_mem hx1_in_V
              rcases Finset.mem_insert.mp hy' with rfl | hy''
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hbox_sub hy'')
            else
              -- Impossible under no-box-extras: ⟨old, .VTypeBox repl_inner_type⟩ ∈ W
              -- is box-typed, so h_dia_no_extras forces it into dia_VarCtx; it can't
              -- be the dia binder (wrong type), so it's in box_VarCtx inner_ctx, i.e.
              -- ⟨old, repl_inner_type⟩ ∈ inner_ctx — contradicting `h`.
              refine .diaterm x hx inner_t ?_ (by
                exfalso
                have h_old_in_W : (⟨old, repl_inner_type.VTypeBox⟩ : VarSymb × VarType) ∈ W.1 := by
                  rw [Wdef]; exact Finset.mem_insert_self _ _
                have h_in_dia : (⟨old, repl_inner_type.VTypeBox⟩ : VarSymb × VarType)
                                  ∈ (dia_VarCtx x inner_ctx hx).1 :=
                  h_dia_no_extras _ h_old_in_W rfl
                rcases Finset.mem_insert.mp h_in_dia with hxeq | hbox
                · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
                · rcases Finset.mem_image.mp hbox with ⟨⟨v, S⟩, hvin, hveq⟩
                  simp only [Prod.mk.injEq] at hveq
                  exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin))
              have hdia_old_not :
                  ⟨old, repl_inner_type.VTypeBox⟩ ∉ (dia_VarCtx x inner_ctx hx).1 := by
                intro hmem
                rcases Finset.mem_insert.mp hmem with heq | hbox
                · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at heq
                · rcases Finset.mem_image.mp hbox with ⟨⟨v, S⟩, hvin, hveq⟩
                  simp only [Prod.mk.injEq] at hveq
                  exact h (hveq.1 ▸ VarType.VTypeBox.inj hveq.2 ▸ hvin)
              have hsub : (dia_VarCtx x inner_ctx hx).1 ⊆ V.1 := by
                intro y hy
                rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy) with rfl | hV
                · exact absurd hy hdia_old_not
                · exact hV
              exact Finset.Subset.trans hsub (Finset.subset_insert _ _)
        | .VTypeDia repl_inner_type =>
            -- VTypeDia: if x is the bound variable being renamed, rebind to ⟨new, repl_inner_type⟩
            -- and rename inside inner_t; otherwise pass through.
            if h_x : x = ⟨old, repl_inner_type⟩ then
              -- Avoid `subst h_x` so the recursive call still sees `inner_t` as a
              -- structural sub-term of `old_term`.
              have hx_eq_old : x.1 = old := congrArg Prod.fst h_x
              have hx_old : old ∉ VarCtx_to_VarSymbs inner_ctx := hx_eq_old ▸ hx
              have hbox_sub : (box_VarCtx inner_ctx).1 ⊆ V.1 := by
                intro y hy
                have hy_dia : y ∈ (dia_VarCtx x inner_ctx hx).1 :=
                  Finset.mem_insert_of_mem hy
                rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy_dia) with rfl | hV
                · rcases Finset.mem_image.mp hy with ⟨⟨v, S⟩, _, hveq⟩
                  simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
                · exact hV
              have hnew_fresh_inner : new ∉ VarCtx_to_VarSymbs inner_ctx := fun hmem => by
                rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin, hveq⟩
                exact new_fresh (Finset.mem_image.mpr ⟨⟨v, S.VTypeBox⟩,
                  hbox_sub (Finset.mem_image.mpr ⟨⟨v, S⟩, hvin, rfl⟩), hveq⟩)
              have Wdef_inner : VarCtx_insert x inner_ctx hx =
                  VarCtx_insert ⟨old, repl_inner_type⟩ inner_ctx hx_old :=
                VarCtx_ext _ _ (by
                  change insert x inner_ctx.1 = insert ⟨old, repl_inner_type⟩ inner_ctx.1
                  rw [h_x])
              have h_nb_inner : new ∉ Term.boundVars inner_t :=
                fun hmem => h_nb (Finset.mem_insert_of_mem hmem)
              let renamed_t := Term.rename old new repl_inner_type
                                 inner_ctx
                                 (VarCtx_insert x inner_ctx hx)
                                 inner_type
                                 hx_old hnew_fresh_inner Wdef_inner inner_t h_nb_inner
              refine .diaterm ⟨new, repl_inner_type⟩ hnew_fresh_inner renamed_t ?_ (by
                -- New W adds ⟨new, repl_inner_type.VTypeDia⟩ which is non-box.
                -- Box-typed entries in V transfer from h_dia_no_extras (and the
                -- single dia entry there is also non-box).
                intro p hp h_box
                rw [dia_VarCtx_fst]
                rcases Finset.mem_insert.mp hp with h_eq | hp_V
                · subst h_eq; simp [VarType.isBox] at h_box
                · have hp_W : p ∈ W.1 := by
                    rw [Wdef]; exact Finset.mem_insert_of_mem hp_V
                  have hp_dia_inner : p ∈ (dia_VarCtx x inner_ctx hx).1 :=
                    h_dia_no_extras p hp_W h_box
                  rw [dia_VarCtx_fst] at hp_dia_inner
                  rcases Finset.mem_insert.mp hp_dia_inner with hpx | hp_box
                  · subst hpx; simp [VarType.isBox] at h_box
                  · exact Finset.mem_insert_of_mem hp_box)
              rw [dia_VarCtx_fst]
              exact Finset.insert_subset_insert _ hbox_sub
            else
              refine .diaterm x hx inner_t ?_ (by
                intro p hp h_box
                rcases Finset.mem_insert.mp hp with h_eq | hp_V
                · subst h_eq; simp [VarType.isBox] at h_box
                · exact h_dia_no_extras p
                    (by rw [Wdef]; exact Finset.mem_insert_of_mem hp_V) h_box)
              intro y hy
              rcases Finset.mem_insert.mp (Wdef ▸ dia_ctx_sub hy) with rfl | hyV
              · exfalso
                rcases Finset.mem_insert.mp hy with hxeq | hbox
                · apply h_x
                  simp only [Prod.mk.injEq] at hxeq
                  exact Prod.ext hxeq.1.symm (VarType.VTypeDia.inj hxeq.2).symm
                · rcases Finset.mem_image.mp hbox with ⟨⟨v, S⟩, _, hveq⟩
                  simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
              · exact Finset.mem_insert_of_mem hyV
    | .unit, _ => exact .unit
    | .pair t1 t2, h_nb =>
        have h_nb_1 : new ∉ Term.boundVars t1 :=
          fun hmem => h_nb (Finset.mem_union_left _ hmem)
        have h_nb_2 : new ∉ Term.boundVars t2 :=
          fun hmem => h_nb (Finset.mem_union_right _ hmem)
        exact .pair (Term.rename old new repl_type V W _ old_fresh new_fresh Wdef t1 h_nb_1)
                    (Term.rename old new repl_type V W _ old_fresh new_fresh Wdef t2 h_nb_2)
    | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁_eq w₂_eq inner_term, h_nb =>
        rename_i pe_V pe_W₁
        -- `pe_V` is the constructor's inner context (before binders v₁, v₂, z);
        -- `pe_W₁ = insert_twice v₁ v₂ pe_V` is the inner-term context.
        -- W has two decompositions: W = insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ pe_V (via w₂_eq)
        -- and W = insert ⟨old, repl_type⟩ V (via Wdef). The renamed variable is either
        -- the bound `z` (Case A) or a free variable inside `pe_V` (recurse case).
        -- Extract freshness implied by `h_nb`: `new` is distinct from each binder
        -- (v₁.1, v₂.1, z) and doesn't appear bound inside `inner_term`.
        have h_v₁_ne_new : v₁.1 ≠ new := fun heq =>
          h_nb (Finset.mem_insert.mpr (Or.inl heq.symm))
        have h_v₂_ne_new : v₂.1 ≠ new := fun heq =>
          h_nb (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inl heq.symm))))
        have h_z_ne_new : z ≠ new := fun heq =>
          h_nb (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inl heq.symm))))))
        have h_nb_inner : new ∉ Term.boundVars inner_term := fun hmem =>
          h_nb (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inr hmem))))))
        by_cases h_case :
            (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
        · -- Case A: the bound `z` (with type .VTypeProd v₁.2 v₂.2) IS ⟨old, repl_type⟩.
          -- Rebind `z` to `new`; `inner_term` lives in W₁ = insert_twice v₁ v₂ pe_V
          -- and never references `old`, so it's preserved. We AVOID `subst` here
          -- and push the equalities onto Prop-level proofs only, so the resulting
          -- `.pair_elim` is not wrapped in `Eq.rec` — this lets `Term.boundVars`
          -- reduce through it (needed for the boundVars-preservation lemma).
          have h_z_eq : z = old := congrArg Prod.fst h_case
          have h_repl_eq : (VarType.VTypeProd v₁.2 v₂.2) = repl_type :=
            congrArg Prod.snd h_case
          -- Show pe_V = V by canceling the common insert via `h_case`.
          have h_pe_V_eq_V : pe_V = V := by
            apply VarCtx_ext
            have h_not_in_pe : (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                                ∉ pe_V.1 :=
              fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            have h_not_in_V_old : (⟨old, repl_type⟩ : VarSymb × VarType) ∉ V.1 :=
              fun h => old_fresh (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            have h_not_in_V : (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                               ∉ V.1 := h_case ▸ h_not_in_V_old
            have h_set : insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                              pe_V.1
                       = insert ⟨z, .VTypeProd v₁.2 v₂.2⟩ V.1 := by
              have orig : insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                              pe_V.1
                        = insert ⟨old, repl_type⟩ V.1 :=
                congrArg PSigma.fst (w₂_eq.trans Wdef)
              rw [← h_case] at orig
              exact orig
            change pe_V.1 = V.1
            rw [← Finset.erase_insert h_not_in_pe, h_set,
                Finset.erase_insert h_not_in_V]
          -- Transport freshness proofs (Prop level) from pe_V to V.
          have hv₁_V : v₁.1 ∉ VarCtx_to_VarSymbs V := h_pe_V_eq_V ▸ hv₁
          have hv₂_V : v₂.1 ∉ VarCtx_to_VarSymbs V := h_pe_V_eq_V ▸ hv₂
          have w₁_eq_V : VarCtx_insert_twice v₁ v₂ V hv₁_V hv₂_V hv₁v₂ = pe_W₁ :=
            h_pe_V_eq_V ▸ w₁_eq
          -- `w₂_eq_V` aligns the constructor's `W₂` slot to the target context.
          have w₂_eq_V :
              VarCtx_insert ⟨new, .VTypeProd v₁.2 v₂.2⟩ V new_fresh =
              VarCtx_insert ⟨new, repl_type⟩ V new_fresh :=
            congrArg (fun T => VarCtx_insert ⟨new, T⟩ V new_fresh) h_repl_eq
          exact .pair_elim v₁ v₂ new hv₁_V hv₂_V hv₁v₂ new_fresh
            w₁_eq_V w₂_eq_V inner_term
        · -- Recurse case: z's typed pair is NOT ⟨old, repl_type⟩, so ⟨old, repl_type⟩
          -- must live in `pe_V`. Erase it, rename `old → new` inside `inner_term`,
          -- and rebuild the `pair_elim` with the same binders v₁, v₂, z.
          have h_old_in_pe_V : ⟨old, repl_type⟩ ∈ pe_V.1 := by
            have h_old_in_W : ⟨old, repl_type⟩ ∈ W.1 := by
              rw [Wdef]; exact Finset.mem_insert_self _ _
            rw [← w₂_eq] at h_old_in_W
            rcases Finset.mem_insert.mp h_old_in_W with h_eq | h_pe_V
            · exact absurd h_eq.symm h_case
            · exact h_pe_V
          -- Build the "stripped" inner context pe_V' = pe_V \ {⟨old, repl_type⟩}.
          let pe_V' := VarCtx_erase pe_V ⟨old, repl_type⟩
          have old_fresh_pe_V' : old ∉ VarCtx_to_VarSymbs pe_V' :=
            VarCtx_erase_fresh h_old_in_pe_V
          have hv₁' : v₁.1 ∉ VarCtx_to_VarSymbs pe_V' :=
            fun hmem => hv₁ (VarCtx_to_VarSymbs_erase_subset hmem)
          have hv₂' : v₂.1 ∉ VarCtx_to_VarSymbs pe_V' :=
            fun hmem => hv₂ (VarCtx_to_VarSymbs_erase_subset hmem)
          have hz' : z ∉ VarCtx_to_VarSymbs pe_V' :=
            fun hmem => hz (VarCtx_to_VarSymbs_erase_subset hmem)
          -- Since ⟨old, _⟩ ∈ pe_V but v₁.1, v₂.1 ∉ pe_V, the binders differ from `old`.
          have h_v₁_ne_old : v₁.1 ≠ old := fun heq =>
            hv₁ (Finset.mem_image.mpr ⟨_, h_old_in_pe_V, heq.symm⟩)
          have h_v₂_ne_old : v₂.1 ≠ old := fun heq =>
            hv₂ (Finset.mem_image.mpr ⟨_, h_old_in_pe_V, heq.symm⟩)
          -- `new` is fresh in pe_V': any element of pe_V' is in W \ {⟨z,_⟩}, hence in V.
          have new_fresh_pe_V' : new ∉ VarCtx_to_VarSymbs pe_V' := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨⟨v, S⟩, hvin_pe_V', hveq⟩
            have hvin_W : (⟨v, S⟩ : VarSymb × VarType) ∈ W.1 := by
              rw [← w₂_eq]; exact Finset.mem_insert_of_mem (Finset.erase_subset _ _ hvin_pe_V')
            rw [Wdef] at hvin_W
            rcases Finset.mem_insert.mp hvin_W with h_eq | h_inV
            · exact (Finset.mem_erase.mp hvin_pe_V').1 h_eq
            · exact new_fresh (Finset.mem_image.mpr ⟨⟨v, S⟩, h_inV, hveq⟩)
          -- The recursive inner contexts: with v₁, v₂ on top of pe_V' (old erased).
          let pe_W₁_inner := VarCtx_insert_twice v₁ v₂ pe_V' hv₁' hv₂' hv₁v₂
          have old_fresh_pe_W₁_inner : old ∉ VarCtx_to_VarSymbs pe_W₁_inner :=
            not_mem_VarSymbs_insert_twice h_v₁_ne_old.symm h_v₂_ne_old.symm old_fresh_pe_V'
          have new_fresh_pe_W₁_inner : new ∉ VarCtx_to_VarSymbs pe_W₁_inner :=
            not_mem_VarSymbs_insert_twice h_v₁_ne_new.symm h_v₂_ne_new.symm new_fresh_pe_V'
          -- `pe_W₁` decomposes as `insert ⟨old, repl_type⟩ pe_W₁_inner`: bring `old`
          -- out by commuting it past the v₁, v₂ insertions.
          have Wdef_inner : pe_W₁ =
              VarCtx_insert ⟨old, repl_type⟩ pe_W₁_inner old_fresh_pe_W₁_inner := by
            apply VarCtx_ext
            rw [← w₁_eq]
            change insert v₁ (insert v₂ pe_V.1) =
                   insert ⟨old, repl_type⟩ (insert v₁ (insert v₂ pe_V'.1))
            rw [← Finset.insert_erase h_old_in_pe_V,
                Finset.insert_comm v₂ ⟨old, repl_type⟩,
                Finset.insert_comm v₁ ⟨old, repl_type⟩]
            rfl
          let renamed_t := Term.rename old new repl_type
                             pe_W₁_inner pe_W₁ S
                             old_fresh_pe_W₁_inner new_fresh_pe_W₁_inner
                             Wdef_inner inner_term h_nb_inner
          -- Build the new pair_elim's inner context: pe_V_new = insert ⟨new, _⟩ pe_V'.
          have hv₁_new : v₁.1 ∉ VarCtx_to_VarSymbs
              (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V') :=
            not_mem_VarSymbs_insert (x := ⟨new, repl_type⟩)
              (hx := new_fresh_pe_V') h_v₁_ne_new hv₁'
          have hv₂_new : v₂.1 ∉ VarCtx_to_VarSymbs
              (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V') :=
            not_mem_VarSymbs_insert (x := ⟨new, repl_type⟩)
              (hx := new_fresh_pe_V') h_v₂_ne_new hv₂'
          have hz_new : z ∉ VarCtx_to_VarSymbs
              (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V') :=
            not_mem_VarSymbs_insert (x := ⟨new, repl_type⟩)
              (hx := new_fresh_pe_V') h_z_ne_new hz'
          -- Transport `renamed_t` from `insert ⟨new, _⟩ (insert_twice v₁ v₂ pe_V')`
          -- to `insert_twice v₁ v₂ (insert ⟨new, _⟩ pe_V')` — pure commutativity.
          have ctx_swap : VarCtx_insert ⟨new, repl_type⟩
                            pe_W₁_inner new_fresh_pe_W₁_inner =
              VarCtx_insert_twice v₁ v₂
                (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V')
                hv₁_new hv₂_new hv₁v₂ :=
            VarCtx_insert_twice_insert_comm new_fresh_pe_W₁_inner hv₁_new hv₂_new
          -- Outer context equation: insert ⟨z, _⟩ pe_V_new = insert ⟨new, _⟩ V,
          -- derived by erasing ⟨old, repl_type⟩ from both decompositions of W and
          -- commuting `z` and `new`.
          have w₂_eq_new :
              VarCtx_insert ⟨z, .VTypeProd v₁.2 v₂.2⟩
                (VarCtx_insert ⟨new, repl_type⟩ pe_V' new_fresh_pe_V') hz_new =
              VarCtx_insert ⟨new, repl_type⟩ V new_fresh := by
            apply VarCtx_ext
            change insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                     (insert ⟨new, repl_type⟩ pe_V'.1) =
                   insert ⟨new, repl_type⟩ V.1
            have h_old_not_in_V : (⟨old, repl_type⟩ : VarSymb × VarType) ∉ V.1 :=
              fun h => old_fresh (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            have h_W_set : insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V.1
                         = insert ⟨old, repl_type⟩ V.1 :=
              congrArg PSigma.fst (w₂_eq.trans Wdef)
            have h_erased :
                insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V'.1 = V.1 := by
              have step : (insert (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V.1).erase
                            ⟨old, repl_type⟩ = V.1 := by
                rw [h_W_set, Finset.erase_insert h_old_not_in_V]
              rwa [Finset.erase_insert_of_ne h_case] at step
            rw [← h_erased, Finset.insert_comm]
          exact .pair_elim v₁ v₂ z hv₁_new hv₂_new hv₁v₂ hz_new rfl
            w₂_eq_new (ctx_swap ▸ renamed_t)
end

-- Term.boundVars is invariant under VarCtx-equality casts.
lemma Term.boundVars_ctx_cast {σ : Signature} {V V' : VarCtx} {S : VarType}
    (h : V = V') (t : Term σ V S) :
    Term.boundVars (h ▸ t) = Term.boundVars t := by
  cases h; rfl

-- Term.numNodes is invariant under VarCtx-equality casts.
lemma Term.numNodes_ctx_cast {σ : Signature} {V V' : VarCtx} {S : VarType}
    (h : V = V') (t : Term σ V S) :
    Term.numNodes (h ▸ t) = Term.numNodes t := by
  cases h; rfl

-- Bound-vars preservation for renaming: every binder of `Term.rename ... t` is
-- either `new` itself or was already a binder of `t`. By mutual structural
-- induction on the term, mirroring `Term.rename`'s case structure.
mutual
  theorem Func.boundVars_rename_subset {σ : Signature}
      (old new : VarSymb) (repl_type : VarType) (V W : VarCtx) (N : Nat)
      (old_fresh : old ∉ VarCtx_to_VarSymbs V)
      (new_fresh : new ∉ VarCtx_to_VarSymbs V)
      (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
      (f : Func σ W N) (h_nb : new ∉ Func.boundVars f) :
      Func.boundVars (Func.rename old new repl_type V W N
                        old_fresh new_fresh Wdef f h_nb)
        ⊆ insert new (Func.boundVars f) := by
    match f, h_nb with
    | .F _, _ =>
        exact Finset.empty_subset _
    | .eval g t, h_nb_eval =>
        have h_nb_g : new ∉ Func.boundVars g :=
          fun hmem => h_nb_eval (Finset.mem_union_left _ hmem)
        have h_nb_t : new ∉ Term.boundVars t :=
          fun hmem => h_nb_eval (Finset.mem_union_right _ hmem)
        have ih_g := Func.boundVars_rename_subset old new repl_type V W _
                       old_fresh new_fresh Wdef g h_nb_g
        have ih_t := Term.boundVars_rename_subset old new repl_type V W _
                       old_fresh new_fresh Wdef t h_nb_t
        intro x hx
        rcases Finset.mem_union.mp hx with hg | ht
        · rcases Finset.mem_insert.mp (ih_g hg) with rfl | hg'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hg')
        · rcases Finset.mem_insert.mp (ih_t ht) with rfl | ht'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ht')

  theorem Term.boundVars_rename_subset {σ : Signature}
      (old new : VarSymb) (repl_type : VarType) (V W : VarCtx) (S : VarType)
      (old_fresh : old ∉ VarCtx_to_VarSymbs V)
      (new_fresh : new ∉ VarCtx_to_VarSymbs V)
      (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
      (t : Term σ W S) (h_nb : new ∉ Term.boundVars t) :
      Term.boundVars (Term.rename old new repl_type V W S
                        old_fresh new_fresh Wdef t h_nb)
        ⊆ insert new (Term.boundVars t) := by
    match t, h_nb with
    | .unit, _ =>
        -- Term.rename of .unit returns .unit; boundVars = ∅.
        exact Finset.empty_subset _
    | .var ⟨v, veq⟩, _ =>
        -- Both branches return `.var _`, which has empty boundVars.
        unfold Term.rename
        split_ifs with h_v_old
        · exact Finset.empty_subset _
        · exact Finset.empty_subset _
    | .func f, h_nb_func =>
        -- Term.rename returns .func (Func.rename ... f h_nb_func);
        -- boundVars (.func _) = Func.boundVars _; use Func IH.
        have ih := Func.boundVars_rename_subset old new repl_type V W _
                     old_fresh new_fresh Wdef f h_nb_func
        intro x hx
        exact ih hx
    | .pair t1 t2, h_nb_pair =>
        -- Term.rename returns .pair (rename t1) (rename t2);
        -- boundVars = ∪; chain Term IH on both halves.
        have h_nb_1 : new ∉ Term.boundVars t1 :=
          fun hmem => h_nb_pair (Finset.mem_union_left _ hmem)
        have h_nb_2 : new ∉ Term.boundVars t2 :=
          fun hmem => h_nb_pair (Finset.mem_union_right _ hmem)
        have ih_1 := Term.boundVars_rename_subset old new repl_type V W _
                       old_fresh new_fresh Wdef t1 h_nb_1
        have ih_2 := Term.boundVars_rename_subset old new repl_type V W _
                       old_fresh new_fresh Wdef t2 h_nb_2
        intro x hx
        rcases Finset.mem_union.mp hx with h1 | h2
        · rcases Finset.mem_insert.mp (ih_1 h1) with rfl | h1'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h1')
        · rcases Finset.mem_insert.mp (ih_2 h2) with rfl | h2'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h2')
    | .boxterm inner_t _ _, h_nb_box =>
        unfold Term.rename
        rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩ <;> dsimp only
        · intro x hx
          exact Finset.mem_insert_of_mem hx
        · split_ifs with h
          · intro x hx
            exact (Term.boundVars_rename_subset old new innertype
                     (VarCtx_erase _ ⟨old, innertype⟩) _ _ _ _ _ inner_t h_nb_box) hx
          · intro x hx
            exact Finset.mem_insert_of_mem hx
        all_goals (intro x hx; exact Finset.mem_insert_of_mem hx)
    | .diaterm x _ inner_t _ _, h_nb_dia =>
        -- 5 sub-cases via rcases. Var/VTypeOne/VTypeProd: passthrough.
        -- VTypeBox: if-then-else (recurse or passthrough).
        -- VTypeDia: if-then-else (case A rebinds dia binder to new, or passthrough).
        rename_i dia_V dia_S
        unfold Term.rename
        rcases repl_type with _ | repl_inner | repl_inner | _ | ⟨_, _⟩ <;> dsimp only
        · -- Var: passthrough.
          intro y hy
          exact Finset.mem_insert_of_mem hy
        · -- VTypeBox: if-then-else; rebound by inner Term.rename call.
          split_ifs with h
          · -- recurse: result is `.diaterm x _ (ctx_swap ▸ renamed_t) _`.
            intro y hy
            simp only [Term.boundVars] at hy
            rw [Term.boundVars_ctx_cast] at hy
            have h_nb_inner : new ∉ Term.boundVars inner_t :=
              fun hmem => h_nb_dia (Finset.mem_insert_of_mem hmem)
            rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            · rcases Finset.mem_insert.mp
                (Term.boundVars_rename_subset old new repl_inner
                   (VarCtx_insert x (VarCtx_erase _ ⟨old, repl_inner⟩) _) _ _ _ _ _
                   inner_t h_nb_inner hy') with rfl | hy''
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy'')
          · -- passthrough.
            intro y hy
            exact Finset.mem_insert_of_mem hy
        · -- VTypeDia: if-then-else; case A rebinds x.
          split_ifs with h_x
          · -- case A: result is `.diaterm ⟨new, repl_inner⟩ _ renamed_t _`.
            intro y hy
            simp only [Term.boundVars] at hy
            have h_nb_inner : new ∉ Term.boundVars inner_t :=
              fun hmem => h_nb_dia (Finset.mem_insert_of_mem hmem)
            rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact Finset.mem_insert_self _ _
            · rcases Finset.mem_insert.mp
                (Term.boundVars_rename_subset old new repl_inner _ _ _ _ _ _
                   inner_t h_nb_inner hy') with rfl | hy''
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy'')
          · -- passthrough.
            intro y hy
            exact Finset.mem_insert_of_mem hy
        · -- VTypeOne: passthrough.
          intro y hy
          exact Finset.mem_insert_of_mem hy
        · -- VTypeProd: passthrough.
          intro y hy
          exact Finset.mem_insert_of_mem hy
    | .pair_elim v₁ v₂ z _ _ _ _ _ _ inner_term, h_nb_pe =>
        unfold Term.rename
        by_cases h_case :
            (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
        · -- Case A: result is `.pair_elim v₁ v₂ new hv₁_V hv₂_V hv₁v₂ new_fresh
          -- w₁_eq_V w₂_eq_V inner_term`. boundVars = insert v₁.1 (insert v₂.1
          -- (insert new (boundVars inner_term))). Original boundVars = insert v₁.1
          -- (insert v₂.1 (insert z (boundVars inner_term))).
          rw [dif_pos h_case]
          intro y hy
          simp only [Term.boundVars] at hy
          rcases Finset.mem_insert.mp hy with rfl | hy1
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          rcases Finset.mem_insert.mp hy1 with rfl | hy2
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          rcases Finset.mem_insert.mp hy2 with rfl | hy3
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy3)))
        · -- Recurse: result is `.pair_elim v₁ v₂ z ... (ctx_swap ▸ renamed_t)`.
          rw [dif_neg h_case]
          intro y hy
          simp only [Term.boundVars] at hy
          rw [Term.boundVars_ctx_cast] at hy
          have h_nb_inner : new ∉ Term.boundVars inner_term :=
            fun hmem => h_nb_pe
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem hmem)))
          rcases Finset.mem_insert.mp hy with rfl | hy1
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          rcases Finset.mem_insert.mp hy1 with rfl | hy2
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          rcases Finset.mem_insert.mp hy2 with rfl | hy3
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
          · rcases Finset.mem_insert.mp
              (Term.boundVars_rename_subset _ _ _ _ _ _ _ _ _
                inner_term h_nb_inner hy3) with rfl | hy4
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem
                    (Finset.mem_insert_of_mem hy4)))
end

-- `numNodes` preservation for renaming: `Term.rename` (resp. `Func.rename`)
-- only swaps VarSymbs, never adds or removes constructor nodes. Mirrors the
-- case structure of `Term.rename` / `Func.rename`. This is the key lemma that
-- lets `Term.canonicalize` use `Term.numNodes t` as its termination measure:
-- the pair_elim arm recurses on a body that's been renamed twice, and we need
-- `numNodes` (which is rename-invariant) to see the decrease.
mutual
  theorem Func.numNodes_rename {σ : Signature}
      (old new : VarSymb) (repl_type : VarType) (V W : VarCtx) (N : Nat)
      (old_fresh : old ∉ VarCtx_to_VarSymbs V)
      (new_fresh : new ∉ VarCtx_to_VarSymbs V)
      (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
      (f : Func σ W N) (h_nb : new ∉ Func.boundVars f) :
      Func.numNodes (Func.rename old new repl_type V W N
                       old_fresh new_fresh Wdef f h_nb)
        = Func.numNodes f := by
    match f, h_nb with
    | .F _, _ => rfl
    | .eval g t, h_nb_eval =>
        have h_nb_g : new ∉ Func.boundVars g :=
          fun hmem => h_nb_eval (Finset.mem_union_left _ hmem)
        have h_nb_t : new ∉ Term.boundVars t :=
          fun hmem => h_nb_eval (Finset.mem_union_right _ hmem)
        have ih_g := Func.numNodes_rename old new repl_type V W _
                       old_fresh new_fresh Wdef g h_nb_g
        have ih_t := Term.numNodes_rename old new repl_type V W _
                       old_fresh new_fresh Wdef t h_nb_t
        show 1 + Func.numNodes _ + Term.numNodes _
             = 1 + Func.numNodes g + Term.numNodes t
        omega

  theorem Term.numNodes_rename {σ : Signature}
      (old new : VarSymb) (repl_type : VarType) (V W : VarCtx) (S : VarType)
      (old_fresh : old ∉ VarCtx_to_VarSymbs V)
      (new_fresh : new ∉ VarCtx_to_VarSymbs V)
      (Wdef : W = VarCtx_insert ⟨old, repl_type⟩ V old_fresh)
      (t : Term σ W S) (h_nb : new ∉ Term.boundVars t) :
      Term.numNodes (Term.rename old new repl_type V W S
                       old_fresh new_fresh Wdef t h_nb)
        = Term.numNodes t := by
    match t, h_nb with
    | .unit, _ => rfl
    | .var ⟨v, veq⟩, _ =>
        unfold Term.rename
        split_ifs <;> rfl
    | .func f, h_nb_func =>
        have ih := Func.numNodes_rename old new repl_type V W _
                     old_fresh new_fresh Wdef f h_nb_func
        show 1 + Func.numNodes _ = 1 + Func.numNodes f
        omega
    | .pair t1 t2, h_nb_pair =>
        have h_nb_1 : new ∉ Term.boundVars t1 :=
          fun hmem => h_nb_pair (Finset.mem_union_left _ hmem)
        have h_nb_2 : new ∉ Term.boundVars t2 :=
          fun hmem => h_nb_pair (Finset.mem_union_right _ hmem)
        have ih_1 := Term.numNodes_rename old new repl_type V W _
                       old_fresh new_fresh Wdef t1 h_nb_1
        have ih_2 := Term.numNodes_rename old new repl_type V W _
                       old_fresh new_fresh Wdef t2 h_nb_2
        show 1 + Term.numNodes _ + Term.numNodes _
             = 1 + Term.numNodes t1 + Term.numNodes t2
        omega
    | .boxterm inner_t hsub h_no_extras, h_nb_box =>
        rename_i inner_ctx inner_termtype
        unfold Term.rename
        rcases repl_type with _ | innertype | _ | _ | ⟨_, _⟩ <;> dsimp only
        · rfl
        · split_ifs with h
          · show 1 + Term.numNodes _ = 1 + Term.numNodes inner_t
            congr 1
            exact Term.numNodes_rename old new innertype
              (VarCtx_erase inner_ctx ⟨old, innertype⟩) inner_ctx inner_termtype
              (VarCtx_erase_fresh h) _ _ inner_t h_nb_box
          · rfl
        · rfl
        · rfl
        · rfl
    | .diaterm x hx inner_t hsub h_no_extras, h_nb_dia =>
        rename_i inner_ctx inner_type
        unfold Term.rename
        rcases repl_type with _ | repl_inner | repl_inner | _ | ⟨_, _⟩ <;> dsimp only
        · rfl
        · split_ifs with h
          · show 1 + Term.numNodes _ = 1 + Term.numNodes inner_t
            congr 1
            rw [Term.numNodes_ctx_cast]
            have h_nb_inner : new ∉ Term.boundVars inner_t :=
              fun hmem => h_nb_dia (Finset.mem_insert_of_mem hmem)
            exact Term.numNodes_rename old new repl_inner
              (VarCtx_insert x (VarCtx_erase inner_ctx ⟨old, repl_inner⟩) _)
              (VarCtx_insert x inner_ctx hx) inner_type _ _ _ inner_t h_nb_inner
          · rfl
        · split_ifs with h_x
          · show 1 + Term.numNodes _ = 1 + Term.numNodes inner_t
            congr 1
            have h_nb_inner : new ∉ Term.boundVars inner_t :=
              fun hmem => h_nb_dia (Finset.mem_insert_of_mem hmem)
            exact Term.numNodes_rename old new repl_inner inner_ctx
              (VarCtx_insert x inner_ctx hx) inner_type _ _ _ inner_t h_nb_inner
          · rfl
        · rfl
        · rfl
    | .pair_elim v₁ v₂ z hv₁ hv₂ hv₁v₂ hz w₁_eq w₂_eq inner_term, h_nb_pe =>
        rename_i pe_V pe_W₁
        unfold Term.rename
        by_cases h_case :
            (⟨z, .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨old, repl_type⟩
        · rw [dif_pos h_case]
          rfl
        · rw [dif_neg h_case]
          show 1 + Term.numNodes _ = 1 + Term.numNodes inner_term
          congr 1
          rw [Term.numNodes_ctx_cast]
          have h_nb_inner : new ∉ Term.boundVars inner_term :=
            fun hmem => h_nb_pe
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem hmem)))
          exact Term.numNodes_rename old new repl_type
            (VarCtx_insert_twice v₁ v₂ (VarCtx_erase pe_V ⟨old, repl_type⟩) _ _ _)
            pe_W₁ _ _ _ _ inner_term h_nb_inner
end

-- Replace a bound pair variable `z : V1 × V2` with two fresh component variables
-- `v1 : V1` and `v2 : V2`. Whenever `z` is used as a value it is replaced by the
-- pair `(v1, v2)`; whenever a `pair_elim` consumes `z`, it is dropped and the
-- inner term's binders are renamed to v1, v2.
mutual
  def Func.unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
      (V W₁ W₂ : VarCtx) (N : ℕ)
      (hz : z ∉ VarCtx_to_VarSymbs V)
      (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
      (hv1v2 : v1 ≠ v2)
      (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
      (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
      (input : Func σ W₁ N)
      (h_v1_nb : v1 ∉ Func.boundVars input)
      (h_v2_nb : v2 ∉ Func.boundVars input)
      : Func σ W₂ N := by
    match input, h_v1_nb, h_v2_nb with
    | .F h, _, _ => exact .F h
    | .eval g t, hf1, hf2 =>
        have hg1 : v1 ∉ Func.boundVars g :=
          fun hmem => hf1 (Finset.mem_union_left _ hmem)
        have hg2 : v2 ∉ Func.boundVars g :=
          fun hmem => hf2 (Finset.mem_union_left _ hmem)
        have ht1 : v1 ∉ Term.boundVars t :=
          fun hmem => hf1 (Finset.mem_union_right _ hmem)
        have ht2 : v2 ∉ Term.boundVars t :=
          fun hmem => hf2 (Finset.mem_union_right _ hmem)
        exact .eval
          (Func.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def g hg1 hg2)
          (Term.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def t ht1 ht2)

  def Term.unpair {σ : Signature} (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
      (V W₁ W₂ : VarCtx) (S : VarType)
      (hz : z ∉ VarCtx_to_VarSymbs V)
      (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
      (hv1v2 : v1 ≠ v2)
      (W₁def : W₁ = VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz)
      (W₂def : W₂ = VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2)
      (input : Term σ W₁ S)
      (h_v1_nb : v1 ∉ Term.boundVars input)
      (h_v2_nb : v2 ∉ Term.boundVars input)
      : Term σ W₂ S := by
    match input, h_v1_nb, h_v2_nb with
    | .var ⟨v, veq⟩, _, _ =>
        -- If `v = z`, then by VarCtx uniqueness `S = V1.VTypeProd V2`, so we
        -- replace the variable with the pair `(v1, v2)`. Otherwise `v` already
        -- lives in `V` and we just rebind it in the output context.
        if h_v_z : v = z then
          have hz_in_W : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
            rw [W₁def]; exact Finset.mem_insert_self _ _
          have hS : S = V1.VTypeProd V2 :=
            W₁.2 ⟨v, S⟩ veq ⟨z, V1.VTypeProd V2⟩ hz_in_W h_v_z
          rw [hS, W₂def]
          exact .pair
            (.var ⟨v1, Finset.mem_insert_self _ _⟩)
            (.var ⟨v2, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩)
        else
          have hv_V : (⟨v, S⟩ : VarSymb × VarType) ∈ V.1 := by
            rw [W₁def] at veq
            rcases Finset.mem_insert.mp veq with heq | hv
            · exact absurd (congrArg Prod.fst heq) h_v_z
            · exact hv
          exact .var ⟨v, by
            rw [W₂def]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv_V)⟩
    | .func f, h1, h2 =>
        exact .func
          (Func.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def f h1 h2)
    | .boxterm inner_t hsub h_box_no_extras_orig, _, _ =>
        -- `z` cannot appear in `box_VarCtx inner_ctx` (its type is .VTypeProd,
        -- not a box), so the inner term doesn't reference `z` and is preserved
        -- as-is. With the new recursive `isBox` (which propagates through
        -- .VTypeProd), if V1 or V2 is box-typed then ⟨z, V1.VTypeProd V2⟩ in W₁
        -- is itself box-detected. `h_box_no_extras_orig` then forces it into
        -- `box_VarCtx inner_ctx` — impossible by constructor mismatch.
        refine .boxterm inner_t ?_ (by
          intro p hp h_box
          rw [W₂def] at hp
          rcases Finset.mem_insert.mp hp with h_eq | hp'
          · subst h_eq
            exfalso
            have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_self _ _
            have hz_box : (V1.VTypeProd V2).isBox = true := by
              simp [VarType.isBox, h_box]
            have hz_in_box := h_box_no_extras_orig _ hz_in_W1 hz_box
            rcases Finset.mem_image.mp hz_in_box with ⟨⟨_, _⟩, _, hveq⟩
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
          · rcases Finset.mem_insert.mp hp' with h_eq2 | hp_V
            · subst h_eq2
              exfalso
              have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
                rw [W₁def]; exact Finset.mem_insert_self _ _
              have hz_box : (V1.VTypeProd V2).isBox = true := by
                simp [VarType.isBox, h_box]
              have hz_in_box := h_box_no_extras_orig _ hz_in_W1 hz_box
              rcases Finset.mem_image.mp hz_in_box with ⟨⟨_, _⟩, _, hveq⟩
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
            · have hp_W1 : p ∈ W₁.1 := by
                rw [W₁def]; exact Finset.mem_insert_of_mem hp_V
              exact h_box_no_extras_orig p hp_W1 h_box)
        intro y hy
        rw [W₂def]
        have hy_W : y ∈ W₁.1 := hsub hy
        rw [W₁def] at hy_W
        rcases Finset.mem_insert.mp hy_W with hyz | hyV
        · subst hyz
          rcases Finset.mem_image.mp hy with ⟨_, _, hweq⟩
          simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hweq
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hyV)
    | .diaterm x hx inner_t hsub h_dia_no_extras_orig, _, _ =>
        -- Same argument as boxterm: ⟨z, V1.VTypeProd V2⟩ in W₁ is box-detected
        -- under the new recursive isBox when V1 or V2 is box; h_dia_no_extras
        -- then forces it into dia_VarCtx, but neither the x-binder (.VTypeDia)
        -- nor the box_VarCtx (.VTypeBox-outer) entries match its .VTypeProd
        -- outer constructor.
        refine .diaterm x hx inner_t ?_ (by
          intro p hp h_box
          rw [W₂def] at hp
          rcases Finset.mem_insert.mp hp with h_eq | hp'
          · subst h_eq
            exfalso
            have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_self _ _
            have hz_box : (V1.VTypeProd V2).isBox = true := by
              simp [VarType.isBox, h_box]
            have hz_in_dia := h_dia_no_extras_orig _ hz_in_W1 hz_box
            rcases Finset.mem_insert.mp hz_in_dia with hxeq | hbox
            · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
            · rcases Finset.mem_image.mp hbox with ⟨⟨_, _⟩, _, hveq⟩
              simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
          · rcases Finset.mem_insert.mp hp' with h_eq2 | hp_V
            · subst h_eq2
              exfalso
              have hz_in_W1 : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
                rw [W₁def]; exact Finset.mem_insert_self _ _
              have hz_box : (V1.VTypeProd V2).isBox = true := by
                simp [VarType.isBox, h_box]
              have hz_in_dia := h_dia_no_extras_orig _ hz_in_W1 hz_box
              rcases Finset.mem_insert.mp hz_in_dia with hxeq | hbox
              · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
              · rcases Finset.mem_image.mp hbox with ⟨⟨_, _⟩, _, hveq⟩
                simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hveq
            · have hp_W1 : p ∈ W₁.1 := by
                rw [W₁def]; exact Finset.mem_insert_of_mem hp_V
              exact h_dia_no_extras_orig p hp_W1 h_box)
        intro y hy
        rw [W₂def]
        have hy_W : y ∈ W₁.1 := hsub hy
        rw [W₁def] at hy_W
        rcases Finset.mem_insert.mp hy_W with hyz | hyV
        · subst hyz
          rcases Finset.mem_insert.mp hy with hxeq | hbox
          · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hxeq
          · rcases Finset.mem_image.mp hbox with ⟨_, _, hweq⟩
            simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hweq
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hyV)
    | .unit, _, _ => exact .unit
    | .pair t1 t2, h1, h2 =>
        have h1_t1 : v1 ∉ Term.boundVars t1 :=
          fun hmem => h1 (Finset.mem_union_left _ hmem)
        have h1_t2 : v1 ∉ Term.boundVars t2 :=
          fun hmem => h1 (Finset.mem_union_right _ hmem)
        have h2_t1 : v2 ∉ Term.boundVars t1 :=
          fun hmem => h2 (Finset.mem_union_left _ hmem)
        have h2_t2 : v2 ∉ Term.boundVars t2 :=
          fun hmem => h2 (Finset.mem_union_right _ hmem)
        exact .pair
          (Term.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def t1 h1_t1 h2_t1)
          (Term.unpair z V1 V2 v1 v2 V W₁ W₂ _ hz hv1 hv2 hv1v2 W₁def W₂def t2 h1_t2 h2_t2)
    | .pair_elim v₁ v₂ z' hv₁ hv₂ hv₁v₂_inner hz' w₁_eq w₂_eq inner_term, h1, h2 =>
        rename_i pe_V pe_W₁
        -- Extract freshness conditions from h1/h2 (v1, v2 avoid the binders and
        -- the bound variables of inner_term).
        have h_v1_nb_inner : v1 ∉ Term.boundVars inner_term := fun hmem =>
          h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
        have h_v2_nb_inner : v2 ∉ Term.boundVars inner_term := fun hmem =>
          h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert.mpr (Or.inr hmem))))))
        by_cases h_case :
            (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) = ⟨z, V1.VTypeProd V2⟩
        · -- Case A: the pair_elim's bound `z'` IS our `z`. Drop the pair_elim
          -- and rename the inner binders v₁.1 → v1 and v₂.1 → v2 inside.
          have h_z'_eq : z' = z := congrArg Prod.fst h_case
          have h_type_eq : (VarType.VTypeProd v₁.2 v₂.2) = V1.VTypeProd V2 :=
            congrArg Prod.snd h_case
          subst z'
          obtain ⟨rfl, rfl⟩ := VarType.VTypeProd.inj h_type_eq
          -- Cancel the shared insert ⟨z, v₁.2.VTypeProd v₂.2⟩ to get pe_V = V.
          have h_pe_V_eq_V : pe_V = V := by
            apply VarCtx_ext
            have h_W_eq : insert (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) pe_V.1
                       = insert ⟨z, v₁.2.VTypeProd v₂.2⟩ V.1 :=
              congrArg PSigma.fst (w₂_eq.trans W₁def)
            have h_not_in_pe : (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∉ pe_V.1 :=
              fun h => hz' (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            have h_not_in_V : (⟨z, v₁.2.VTypeProd v₂.2⟩ : VarSymb × VarType) ∉ V.1 :=
              fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            change pe_V.1 = V.1
            rw [← Finset.erase_insert h_not_in_pe, h_W_eq, Finset.erase_insert h_not_in_V]
          subst pe_V
          -- Now hv₁ : v₁.1 ∉ V, hv₂ : v₂.1 ∉ V, and inner_term lives in
          -- insert_twice v₁ v₂ V. Rename v₁.1 → v1 then v₂.1 → v2.
          have h_v1_ne_v₂_1 : v1 ≠ v₂.1 := fun heq =>
            h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
          have h_v2_ne_v₁_1 : v2 ≠ v₁.1 := fun heq =>
            h2 (Finset.mem_insert.mpr (Or.inl heq))
          have h_v1_fresh_in_iv₂ :
              v1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂) :=
            not_mem_VarSymbs_insert h_v1_ne_v₂_1 hv1
          have h_v₁1_fresh_in_iv₂ :
              v₁.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v₂ V hv₂) :=
            not_mem_VarSymbs_insert hv₁v₂_inner hv₁
          have w₁_decomp : pe_W₁ =
              VarCtx_insert v₁ (VarCtx_insert v₂ V hv₂) h_v₁1_fresh_in_iv₂ :=
            w₁_eq.symm.trans (VarCtx_ext _ _ rfl)
          let renamed_1 := Term.rename v₁.1 v1 v₁.2 (VarCtx_insert v₂ V hv₂) pe_W₁ S
                             h_v₁1_fresh_in_iv₂ h_v1_fresh_in_iv₂ w₁_decomp
                             inner_term h_v1_nb_inner
          -- Now rename v₂.1 → v2 in `renamed_1`.
          have h_v2_fresh_in_iv1 :
              v2 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) :=
            not_mem_VarSymbs_insert hv1v2.symm hv2
          have h_v₂1_fresh_in_iv1 :
              v₂.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) :=
            not_mem_VarSymbs_insert h_v1_ne_v₂_1.symm hv₂
          have ctx_swap_1 :
              VarCtx_insert ⟨v1, v₁.2⟩ (VarCtx_insert v₂ V hv₂) h_v1_fresh_in_iv₂ =
              VarCtx_insert v₂ (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) h_v₂1_fresh_in_iv1 :=
            VarCtx_insert_comm h_v1_fresh_in_iv₂ h_v₂1_fresh_in_iv1
          -- `v2 ∉ Term.boundVars renamed_1` via the preservation lemma:
          -- renaming bound vars ⊆ insert v1 (boundVars inner_term); v2 is
          -- neither v1 (hv1v2.symm) nor in boundVars inner_term (h_v2_nb_inner).
          have h_v2_nb_renamed_1 : v2 ∉ Term.boundVars renamed_1 := fun hmem => by
            have h_sub := Term.boundVars_rename_subset v₁.1 v1 v₁.2
              (VarCtx_insert v₂ V hv₂) pe_W₁ S
              h_v₁1_fresh_in_iv₂ h_v1_fresh_in_iv₂ w₁_decomp
              inner_term h_v1_nb_inner
            rcases Finset.mem_insert.mp (h_sub hmem) with heq | hin
            · exact hv1v2.symm heq
            · exact h_v2_nb_inner hin
          let renamed_2 := Term.rename v₂.1 v2 v₂.2 (VarCtx_insert ⟨v1, v₁.2⟩ V hv1)
                             (VarCtx_insert ⟨v1, v₁.2⟩ (VarCtx_insert v₂ V hv₂) h_v1_fresh_in_iv₂)
                             S h_v₂1_fresh_in_iv1 h_v2_fresh_in_iv1 ctx_swap_1
                             renamed_1 h_v2_nb_renamed_1
          -- Transport from `insert ⟨v2, v₂.2⟩ (insert ⟨v1, v₁.2⟩ V) _`
          -- to `insert_twice ⟨v1, v₁.2⟩ ⟨v2, v₂.2⟩ V` (a single Finset.insert_comm).
          have ctx_final :
              VarCtx_insert ⟨v2, v₂.2⟩ (VarCtx_insert ⟨v1, v₁.2⟩ V hv1) h_v2_fresh_in_iv1 =
              VarCtx_insert_twice ⟨v1, v₁.2⟩ ⟨v2, v₂.2⟩ V hv1 hv2 hv1v2 :=
            VarCtx_ext _ _ (by
              change insert ⟨v2, v₂.2⟩ (insert (⟨v1, v₁.2⟩ : VarSymb × VarType) V.1) =
                     insert ⟨v1, v₁.2⟩ (insert ⟨v2, v₂.2⟩ V.1)
              exact Finset.insert_comm _ _ _)
          rw [W₂def]
          exact ctx_final ▸ renamed_2
        · -- Recurse case: ⟨z, V1.VTypeProd V2⟩ must lie in pe_V.
          have h_z_in_pe_V :
              (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ pe_V.1 := by
            have h_z_in_W₁ : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [W₁def]; exact Finset.mem_insert_self _ _
            rw [← w₂_eq] at h_z_in_W₁
            rcases Finset.mem_insert.mp h_z_in_W₁ with h_eq | h_pe_V
            · exact absurd h_eq.symm h_case
            · exact h_pe_V
          -- Erase z from pe_V to get pe_V', then recurse on inner_term in the
          -- decomposed context insert ⟨z, _⟩ (insert_twice v₁ v₂ pe_V').
          let pe_V' := VarCtx_erase pe_V ⟨z, V1.VTypeProd V2⟩
          have hz_pe_V' : z ∉ VarCtx_to_VarSymbs pe_V' :=
            VarCtx_erase_fresh h_z_in_pe_V
          have hv₁_pe_V' : v₁.1 ∉ VarCtx_to_VarSymbs pe_V' :=
            fun hmem => hv₁ (VarCtx_to_VarSymbs_erase_subset hmem)
          have hv₂_pe_V' : v₂.1 ∉ VarCtx_to_VarSymbs pe_V' :=
            fun hmem => hv₂ (VarCtx_to_VarSymbs_erase_subset hmem)
          have h_z_ne_v₁_1 : z ≠ v₁.1 := fun heq =>
            hv₁ (heq ▸ Finset.mem_image.mpr ⟨_, h_z_in_pe_V, rfl⟩)
          have h_z_ne_v₂_1 : z ≠ v₂.1 := fun heq =>
            hv₂ (heq ▸ Finset.mem_image.mpr ⟨_, h_z_in_pe_V, rfl⟩)
          -- Recurse-base inner V: insert_twice v₁ v₂ pe_V'.
          let V_inner := VarCtx_insert_twice v₁ v₂ pe_V' hv₁_pe_V' hv₂_pe_V' hv₁v₂_inner
          have hz_V_inner : z ∉ VarCtx_to_VarSymbs V_inner :=
            not_mem_VarSymbs_insert_twice h_z_ne_v₁_1 h_z_ne_v₂_1 hz_pe_V'
          -- v1, v2 fresh in V_inner (from h1/h2 and the recurse-case derivations).
          have h_v1_ne_v₁_1 : v1 ≠ v₁.1 := fun heq =>
            h1 (Finset.mem_insert.mpr (Or.inl heq))
          have h_v1_ne_v₂_1 : v1 ≠ v₂.1 := fun heq =>
            h1 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
          have h_v2_ne_v₁_1 : v2 ≠ v₁.1 := fun heq =>
            h2 (Finset.mem_insert.mpr (Or.inl heq))
          have h_v2_ne_v₂_1 : v2 ≠ v₂.1 := fun heq =>
            h2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq))))
          have h_v1_pe_V' : v1 ∉ VarCtx_to_VarSymbs pe_V' := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨⟨v, S'⟩, hvin', hveq⟩
            have hvin_W₁ : (⟨v, S'⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [← w₂_eq]
              exact Finset.mem_insert_of_mem (Finset.erase_subset _ _ hvin')
            rw [W₁def] at hvin_W₁
            rcases Finset.mem_insert.mp hvin_W₁ with h_eq | h_inV
            · exact (Finset.mem_erase.mp hvin').1 h_eq
            · exact hv1 (Finset.mem_image.mpr ⟨⟨v, S'⟩, h_inV, hveq⟩)
          have h_v2_pe_V' : v2 ∉ VarCtx_to_VarSymbs pe_V' := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨⟨v, S'⟩, hvin', hveq⟩
            have hvin_W₁ : (⟨v, S'⟩ : VarSymb × VarType) ∈ W₁.1 := by
              rw [← w₂_eq]
              exact Finset.mem_insert_of_mem (Finset.erase_subset _ _ hvin')
            rw [W₁def] at hvin_W₁
            rcases Finset.mem_insert.mp hvin_W₁ with h_eq | h_inV
            · exact (Finset.mem_erase.mp hvin').1 h_eq
            · exact hv2 (Finset.mem_image.mpr ⟨⟨v, S'⟩, h_inV, hveq⟩)
          have hv1_V_inner : v1 ∉ VarCtx_to_VarSymbs V_inner :=
            not_mem_VarSymbs_insert_twice h_v1_ne_v₁_1 h_v1_ne_v₂_1 h_v1_pe_V'
          have hv2_V_inner : v2 ∉ VarCtx_to_VarSymbs V_inner :=
            not_mem_VarSymbs_insert_twice h_v2_ne_v₁_1 h_v2_ne_v₂_1 h_v2_pe_V'
          -- Decomposition pe_W₁ = insert ⟨z, V1.VTypeProd V2⟩ V_inner _.
          have W₁_inner_def : pe_W₁ =
              VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_inner hz_V_inner := by
            apply VarCtx_ext
            rw [← w₁_eq]
            change insert v₁ (insert v₂ pe_V.1) =
                   insert ⟨z, V1.VTypeProd V2⟩ (insert v₁ (insert v₂ pe_V'.1))
            rw [← Finset.insert_erase h_z_in_pe_V,
                Finset.insert_comm v₂ ⟨z, V1.VTypeProd V2⟩,
                Finset.insert_comm v₁ ⟨z, V1.VTypeProd V2⟩]
            rfl
          -- Target context: insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_inner.
          let W₂_inner :=
            VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_inner hv1_V_inner hv2_V_inner hv1v2
          let recursed := Term.unpair z V1 V2 v1 v2 V_inner pe_W₁ W₂_inner S
                            hz_V_inner hv1_V_inner hv2_V_inner hv1v2
                            W₁_inner_def rfl inner_term h_v1_nb_inner h_v2_nb_inner
          -- Build the new pair_elim. Its inner V is `insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ pe_V'`,
          -- which we'll call pe_V_new.
          let pe_V_new :=
            VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ pe_V' h_v1_pe_V' h_v2_pe_V' hv1v2
          have hv₁_new : v₁.1 ∉ VarCtx_to_VarSymbs pe_V_new :=
            not_mem_VarSymbs_insert_twice h_v1_ne_v₁_1.symm h_v2_ne_v₁_1.symm hv₁_pe_V'
          have hv₂_new : v₂.1 ∉ VarCtx_to_VarSymbs pe_V_new :=
            not_mem_VarSymbs_insert_twice h_v1_ne_v₂_1.symm h_v2_ne_v₂_1.symm hv₂_pe_V'
          have hz'_new : z' ∉ VarCtx_to_VarSymbs pe_V_new := by
            have h_z'_in_V : (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ V.1 := by
              have h_z'_in_W₁ : (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) ∈ W₁.1 := by
                rw [← w₂_eq]; exact Finset.mem_insert_self _ _
              rw [W₁def] at h_z'_in_W₁
              rcases Finset.mem_insert.mp h_z'_in_W₁ with h_eq | h_inV
              · exact absurd h_eq h_case
              · exact h_inV
            have h_z'_ne_v1 : z' ≠ v1 := fun heq =>
              hv1 (heq ▸ Finset.mem_image.mpr ⟨_, h_z'_in_V, rfl⟩)
            have h_z'_ne_v2 : z' ≠ v2 := fun heq =>
              hv2 (heq ▸ Finset.mem_image.mpr ⟨_, h_z'_in_V, rfl⟩)
            have h_z'_pe_V' : z' ∉ VarCtx_to_VarSymbs pe_V' :=
              fun hmem => hz' (VarCtx_to_VarSymbs_erase_subset hmem)
            exact not_mem_VarSymbs_insert_twice h_z'_ne_v1 h_z'_ne_v2 h_z'_pe_V'
          -- The recursed term's context equals `insert_twice v₁ v₂ pe_V_new`,
          -- which is the constructor's `W₁` slot.
          have ctx_eq : W₂_inner =
              VarCtx_insert_twice v₁ v₂ pe_V_new hv₁_new hv₂_new hv₁v₂_inner :=
            VarCtx_ext _ _ (by
              change insert (⟨v1, V1⟩ : VarSymb × VarType)
                       (insert ⟨v2, V2⟩ (insert v₁ (insert v₂ pe_V'.1))) =
                     insert v₁ (insert v₂ (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ pe_V'.1)))
              rw [Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) v₁,
                  Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) v₁,
                  Finset.insert_comm (⟨v2, V2⟩ : VarSymb × VarType) v₂,
                  Finset.insert_comm (⟨v1, V1⟩ : VarSymb × VarType) v₂])
          -- Outer w₂_eq: insert ⟨z', _⟩ pe_V_new = W₂.
          have w₂_eq_new :
              VarCtx_insert ⟨z', .VTypeProd v₁.2 v₂.2⟩ pe_V_new hz'_new = W₂ := by
            rw [W₂def]
            apply VarCtx_ext
            change insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                     (insert ⟨v1, V1⟩ (insert ⟨v2, V2⟩ pe_V'.1)) =
                   insert (⟨v1, V1⟩ : VarSymb × VarType) (insert ⟨v2, V2⟩ V.1)
            have h_W_set : insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V.1
                         = insert ⟨z, V1.VTypeProd V2⟩ V.1 :=
              congrArg PSigma.fst (w₂_eq.trans W₁def)
            have h_V_eq : V.1 = insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V'.1 := by
              have step :
                  (insert (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType) pe_V.1).erase
                    ⟨z, V1.VTypeProd V2⟩ = V.1 := by
                rw [h_W_set, Finset.erase_insert
                  (fun h => hz (Finset.mem_image.mpr ⟨_, h, rfl⟩))]
              rw [Finset.erase_insert_of_ne h_case] at step
              exact step.symm
            rw [h_V_eq,
                Finset.insert_comm
                  (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                  (⟨v1, V1⟩ : VarSymb × VarType),
                Finset.insert_comm
                  (⟨z', .VTypeProd v₁.2 v₂.2⟩ : VarSymb × VarType)
                  (⟨v2, V2⟩ : VarSymb × VarType)]
          exact w₂_eq_new ▸ .pair_elim v₁ v₂ z' hv₁_new hv₂_new hv₁v₂_inner hz'_new
                                       rfl rfl (ctx_eq ▸ recursed)
end

-- Sum of nested VTypeProd depths in a type. Used as part of the termination
-- measure for `Term.subst`: each `unpair` step on a pair-typed binder strictly
-- decreases the total `pairDepth` of the surrounding `VarCtx`.
def VarType.pairDepth : VarType → ℕ
  | .Var            => 0
  | .VTypeBox a     => a.pairDepth
  | .VTypeDia a     => a.pairDepth
  | .VTypeOne       => 0
  | .VTypeProd a b  => 1 + a.pairDepth + b.pairDepth

def VarCtx.pairDepth (V : VarCtx) : ℕ :=
  V.1.sum (fun p => p.2.pairDepth)

-- box_VarCtx preserves pairDepth: each ⟨v, T⟩ becomes ⟨v, T.VTypeBox⟩, and
-- with the recursive `pairDepth` definition, `T.VTypeBox.pairDepth = T.pairDepth`.
lemma VarCtx.pairDepth_box_VarCtx (V : VarCtx) :
    (box_VarCtx V).pairDepth = V.pairDepth := by
  show ((box_VarCtx V).1).sum (fun p => p.2.pairDepth)
       = V.1.sum (fun p => p.2.pairDepth)
  rw [show (box_VarCtx V).1
        = V.1.image (fun p => (⟨p.1, p.2.VTypeBox⟩ : VarSymb × VarType)) from rfl]
  rw [Finset.sum_image]
  · rfl
  · -- injectivity of the box-wrap function on V.1
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext hab.1 (VarType.VTypeBox.inj hab.2)

-- Key termination lemma (boxterm): if `box_VarCtx V_inner ⊆ V`, then
-- `V_inner.pairDepth ≤ V.pairDepth`. Enables lex `(V.pairDepth, sizeOf t)`
-- termination for the boxterm modal-interior descent.
lemma VarCtx.pairDepth_le_of_box_subset {V_inner V : VarCtx}
    (h : (box_VarCtx V_inner).1 ⊆ V.1) :
    V_inner.pairDepth ≤ V.pairDepth := by
  rw [← VarCtx.pairDepth_box_VarCtx V_inner]
  exact Finset.sum_le_sum_of_subset h

-- Companion lemma (diaterm): if `dia_VarCtx x V_inner hx ⊆ V`, then
-- `(VarCtx_insert x V_inner hx).pairDepth ≤ V.pairDepth`. The inner-extended
-- context for `tt` is `VarCtx_insert x V_inner hx`, and its pairDepth equals
-- that of `dia_VarCtx x V_inner hx` (both add `x.2.pairDepth + V_inner.pairDepth`).
lemma VarCtx.pairDepth_le_of_dia_subset {x : VarSymb × VarType} {V_inner V : VarCtx}
    {hx : x.1 ∉ VarCtx_to_VarSymbs V_inner}
    (h : (dia_VarCtx x V_inner hx).1 ⊆ V.1) :
    (VarCtx_insert x V_inner hx).pairDepth ≤ V.pairDepth := by
  -- Show (VarCtx_insert x V_inner hx).pairDepth = (dia_VarCtx x V_inner hx).pairDepth
  -- then conclude via subset.
  have h_eq : (VarCtx_insert x V_inner hx).pairDepth
              = (dia_VarCtx x V_inner hx).pairDepth := by
    show (insert x V_inner.1).sum (fun p => p.2.pairDepth)
       = (insert (⟨x.1, x.2.VTypeDia⟩ : VarSymb × VarType) (box_VarCtx V_inner).1).sum
            (fun p => p.2.pairDepth)
    have hx_typed : x ∉ V_inner.1 := fun hmem =>
      hx (Finset.mem_image.mpr ⟨x, hmem, rfl⟩)
    have hx_typed_box : (⟨x.1, x.2.VTypeDia⟩ : VarSymb × VarType) ∉ (box_VarCtx V_inner).1 := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨⟨w, T⟩, _, hweq⟩
      simp only [Prod.mk.injEq] at hweq
      exact VarType.noConfusion hweq.2
    rw [Finset.sum_insert hx_typed, Finset.sum_insert hx_typed_box]
    show x.2.pairDepth + V_inner.pairDepth
       = (x.2.VTypeDia).pairDepth + (box_VarCtx V_inner).pairDepth
    rw [VarCtx.pairDepth_box_VarCtx]
    simp [VarType.pairDepth]
  rw [h_eq]
  exact Finset.sum_le_sum_of_subset h

-- Lemma: unpairing strictly decreases pairDepth (replacing one VTypeProd-typed
-- binder of pairDepth `1 + a + b` with two binders of pairDepth `a` and `b`).
-- Used by `Term.substMU`'s `decreasing_by` to justify the recursive call on
-- the smaller context.
lemma VarCtx.pairDepth_unpair_lt {V : VarCtx} {z : VarSymb} {V1 V2 : VarType}
    (hzmem : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1)
    {v1 v2 : VarSymb}
    (hv1 : v1 ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z, V1.VTypeProd V2⟩))
    (hv2 : v2 ∉ VarCtx_to_VarSymbs (VarCtx_erase V ⟨z, V1.VTypeProd V2⟩))
    (hv1v2 : v1 ≠ v2) :
    (VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩
       (VarCtx_erase V ⟨z, V1.VTypeProd V2⟩) hv1 hv2 hv1v2).pairDepth
      < V.pairDepth := by
  -- Let V' = V.erase ⟨z, V1×V2⟩
  set V_minus_z := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩ with hVmz
  set f : VarSymb × VarType → ℕ := fun p => p.2.pairDepth with hf
  -- v1, v2 (typed) are not in V_minus_z.1
  have hv1_not_in : (⟨v1, V1⟩ : VarSymb × VarType) ∉ V_minus_z.1 := fun h =>
    hv1 (Finset.mem_image.mpr ⟨_, h, rfl⟩)
  have hv2_not_in : (⟨v2, V2⟩ : VarSymb × VarType) ∉ V_minus_z.1 := fun h =>
    hv2 (Finset.mem_image.mpr ⟨_, h, rfl⟩)
  have hv1_ne_v2_typed : (⟨v1, V1⟩ : VarSymb × VarType) ≠ ⟨v2, V2⟩ := fun h =>
    hv1v2 (congrArg Prod.fst h)
  have hv1_not_in_outer :
      (⟨v1, V1⟩ : VarSymb × VarType) ∉ insert (⟨v2, V2⟩ : VarSymb × VarType) V_minus_z.1 :=
    fun h => (Finset.mem_insert.mp h).elim hv1_ne_v2_typed (fun h' => hv1_not_in h')
  -- Compute LHS via two sum_insert peels.
  show (insert (⟨v1, V1⟩ : VarSymb × VarType)
          (insert (⟨v2, V2⟩ : VarSymb × VarType) V_minus_z.1)).sum f < V.1.sum f
  rw [Finset.sum_insert hv1_not_in_outer, Finset.sum_insert hv2_not_in]
  -- Goal: f ⟨v1,V1⟩ + (f ⟨v2,V2⟩ + V_minus_z.1.sum f) < V.1.sum f
  -- Express V.1.sum f as f ⟨z, V1×V2⟩ + V_minus_z.1.sum f.
  have h_V_sum : V.1.sum f = f ⟨z, V1.VTypeProd V2⟩ + V_minus_z.1.sum f := by
    rw [hVmz]
    show V.1.sum f = f ⟨z, V1.VTypeProd V2⟩ + (V.1.erase _).sum f
    rw [← Finset.add_sum_erase V.1 f hzmem]
  rw [h_V_sum]
  -- f ⟨a, T⟩ = T.pairDepth; (V1.VTypeProd V2).pairDepth = 1 + V1.pairDepth + V2.pairDepth.
  simp only [hf, VarType.pairDepth]
  omega

-- Companion to `pairDepth_unpair_lt`, specialised to the shape pair_elim's
-- `w2eq` gives us: `V = VarCtx_insert ⟨z, V1 × V2⟩ V_inner hz`. Used by
-- `Term.substChildren`'s pair_elim arm to justify the recursive `substMU`
-- call on the unpaired context `V_inner + {v1c, v2c}`.
lemma VarCtx.pairDepth_pair_elim_lt {V V_inner : VarCtx}
    {z : VarSymb} {V1 V2 : VarType} {hz : z ∉ VarCtx_to_VarSymbs V_inner}
    (w2eq : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_inner hz = V)
    {v1c v2c : VarSymb}
    (hv1c : v1c ∉ VarCtx_to_VarSymbs V_inner)
    (hv2c : v2c ∉ VarCtx_to_VarSymbs V_inner)
    (hv1c_ne_v2c : v1c ≠ v2c) :
    (VarCtx_insert_twice ⟨v1c, V1⟩ ⟨v2c, V2⟩ V_inner hv1c hv2c hv1c_ne_v2c).pairDepth
      < V.pairDepth := by
  set f : VarSymb × VarType → ℕ := fun p => p.2.pairDepth with hf
  have hv1c_typed : (⟨v1c, V1⟩ : VarSymb × VarType) ∉ V_inner.1 := fun h =>
    hv1c (Finset.mem_image.mpr ⟨_, h, rfl⟩)
  have hv2c_typed : (⟨v2c, V2⟩ : VarSymb × VarType) ∉ V_inner.1 := fun h =>
    hv2c (Finset.mem_image.mpr ⟨_, h, rfl⟩)
  have hv1c_ne_v2c_typed : (⟨v1c, V1⟩ : VarSymb × VarType) ≠ ⟨v2c, V2⟩ := fun h =>
    hv1c_ne_v2c (congrArg Prod.fst h)
  have hv1c_not_in_iv2c :
      (⟨v1c, V1⟩ : VarSymb × VarType) ∉ insert (⟨v2c, V2⟩ : VarSymb × VarType) V_inner.1 :=
    fun h => (Finset.mem_insert.mp h).elim hv1c_ne_v2c_typed (fun h' => hv1c_typed h')
  have hz_typed : (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∉ V_inner.1 := fun h =>
    hz (Finset.mem_image.mpr ⟨_, h, rfl⟩)
  -- Compute LHS via two sum_insert peels.
  show (insert (⟨v1c, V1⟩ : VarSymb × VarType)
          (insert (⟨v2c, V2⟩ : VarSymb × VarType) V_inner.1)).sum f
       < V.1.sum f
  rw [Finset.sum_insert hv1c_not_in_iv2c, Finset.sum_insert hv2c_typed]
  -- Express V's sum: V.1 = insert ⟨z, V1×V2⟩ V_inner.1 (via w2eq).
  rw [← w2eq]
  show f ⟨v1c, V1⟩ + (f ⟨v2c, V2⟩ + V_inner.1.sum f)
       < (insert (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) V_inner.1).sum f
  rw [Finset.sum_insert hz_typed]
  simp only [hf, VarType.pairDepth]
  omega

-- Boolean test: is this a pair (VTypeProd) type?
def VarType.isPair : VarType → Bool
  | .VTypeProd _ _ => true
  | _              => false

-- Predicate: V contains a pair-typed (VTypeProd) binder.
def VarCtx.hasPairVar (V : VarCtx) : Prop :=
  ∃ (z : VarSymb) (V1 V2 : VarType),
    (⟨z, V1.VTypeProd V2⟩ : VarSymb × VarType) ∈ V.1

instance (V : VarCtx) : Decidable V.hasPairVar :=
  decidable_of_iff (∃ p ∈ V.1, p.2.isPair = true) <| by
    constructor
    · rintro ⟨⟨s, T⟩, hmem, h⟩
      match T, h with
      | .VTypeProd a b, _ => exact ⟨s, a, b, hmem⟩
    · rintro ⟨z, V1, V2, hmem⟩
      exact ⟨⟨z, V1.VTypeProd V2⟩, hmem, rfl⟩

-- Constructive search for a pair-typed element in a list.
def List.findPairTyped (l : List (VarSymb × VarType)) :
    Option { p : VarSymb × VarType × VarType //
             (⟨p.1, p.2.1.VTypeProd p.2.2⟩ : VarSymb × VarType) ∈ l } :=
  match l with
  | [] => none
  | (z, T) :: rest =>
    match T with
    | .VTypeProd V1 V2 =>
        some ⟨(z, V1, V2), List.mem_cons_self⟩
    | _ =>
        match List.findPairTyped rest with
        | none => none
        | some ⟨p, hmem⟩ =>
            some ⟨p, List.mem_cons_of_mem _ hmem⟩

-- A computable linear order on VarCtx entries, used by `VarCtx.firstPairVar`
-- to extract a pair-typed binder via `Finset.sort` (avoiding noncomputable
-- `Finset.toList`). Defined by lifting through an injective encoding to ℕ.
private def varCtxEntryEncode (p : VarSymb × VarType) : ℕ :=
  Nat.pair p.1.toNat p.2.encode

private theorem varCtxEntryEncode_injective : Function.Injective varCtxEntryEncode := by
  intro a b heq
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  cases a1 with | mk an =>
  cases b1 with | mk bn =>
  simp only [varCtxEntryEncode, VarSymb.toNat] at heq
  have h_un := congrArg Nat.unpair heq
  simp only [Nat.unpair_pair] at h_un
  obtain ⟨h_n, h_enc⟩ := Prod.mk.inj h_un
  subst h_n
  rw [VarType.encode_injective h_enc]

instance : LinearOrder (VarSymb × VarType) :=
  LinearOrder.lift' varCtxEntryEncode varCtxEntryEncode_injective

-- Extraction of a pair-typed binder from V. Uses `Finset.sort` with the
-- linear order above to deterministically enumerate V's entries in encoding
-- order, then picks the first pair-typed one.
def VarCtx.firstPairVar (V : VarCtx) :
    Option { p : VarSymb × VarType × VarType //
             (⟨p.1, p.2.1.VTypeProd p.2.2⟩ : VarSymb × VarType) ∈ V.1 } :=
  let sorted := V.1.sort (· ≤ ·)
  match h : sorted.findPairTyped with
  | none => none
  | some ⟨p, hmem⟩ =>
      some ⟨p, by
        have h_sorted_perm : sorted.Perm V.1.toList := by
          change (V.1.sort (· ≤ ·)).Perm V.1.toList
          exact Finset.sort_perm_toList _ _
        exact Finset.mem_toList.mp (h_sorted_perm.mem_iff.mp hmem)⟩

-- Inverse of Term.unpair: re-pair the two component variables `v1, v2` into a
-- single pair-typed binder `z`. Thin wrapper around the `pair_elim` constructor.
def Term.repair {σ : Signature} (z : VarSymb) (V1 V2 : VarType) (v1 v2 : VarSymb)
    (V W₁ W₂ : VarCtx) (S : VarType)
    (hv1 : v1 ∉ VarCtx_to_VarSymbs V) (hv2 : v2 ∉ VarCtx_to_VarSymbs V)
    (hv1v2 : v1 ≠ v2) (hz : z ∉ VarCtx_to_VarSymbs V)
    (W₁def : VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V hv1 hv2 hv1v2 = W₁)
    (W₂def : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V hz = W₂)
    (input : Term σ W₁ S)
    : Term σ W₂ S :=
  .pair_elim ⟨v1, V1⟩ ⟨v2, V2⟩ z hv1 hv2 hv1v2 hz W₁def W₂def input

-- Canonicalise the genuinely-bound variables (pair_elim's v₁, v₂) to fresh
-- deterministic symbols, so that α-equivalent terms have equal canonical forms
-- and we can use derived `DecidableEq` for α-aware equality checking.
--
-- `diaterm`'s `x` and `pair_elim`'s `z` are FREE in the outer context (they
-- appear in `V` as `⟨x.1, x.2.VTypeDia⟩` and `⟨z, _×_⟩` respectively), so
-- canonicalize leaves them alone.
--
-- The accumulator `avoid` records every symbol we must not pick when choosing
-- fresh canonical names. Invariants:
--   · `VarCtx_to_VarSymbs V ⊆ avoid` — never collide with free vars
--   · `Term.boundVars t ⊆ avoid` — never collide with binders still inside t
--
-- KNOWN SORRY (TODO option C — fused canonicalize). The current implementation
-- uses `Term.rename` twice in the pair_elim arm, then recurses on the renamed
-- body. The recursion target `body₂` has the same `numNodes` as `body` (which
-- is a strict subterm of `t`), but Lean's auto termination checker can't see
-- this without a `numNodes_rename` lemma (which would mirror the ~190-line
-- `boundVars_rename_subset` proof). The cleaner long-term fix is to FUSE the
-- rename + canonicalize into a single structural pass on `body`, threading a
-- `sub : VarSymb → VarSymb` substitution that grows at each nested binder.
-- That redesign removes the need for `numNodes_rename` entirely. Sketch:
--   def Term.canonicalize_subst (sub : VarSymb → VarSymb) (avoid : Finset VarSymb)
--       {V V' : VarCtx} (h_sub : ∀ p ∈ V.1, ⟨sub p.1, p.2⟩ ∈ V'.1)
--       (h_V' : VarCtx_to_VarSymbs V' ⊆ avoid)
--       (t : Term σ V S) (h_bv : Term.boundVars t ⊆ avoid) : Term σ V' S
-- with the wrapper `canonicalize t := canonicalize_subst id avoid (V := V) ... t`.
mutual
  def Term.canonicalize {σ : Signature} {V : VarCtx} {S : VarType}
      (avoid : Finset VarSymb) (t : Term σ V S)
      (h_V : VarCtx_to_VarSymbs V ⊆ avoid)
      (h_bv : Term.boundVars t ⊆ avoid)
      : Term σ V S := by
    match t with
    | .var v => exact .var v
    | .func f => exact .func (Func.canonicalize avoid f h_V h_bv)
    | .unit => exact .unit
    | .pair t1 t2 =>
        have h_bv1 : Term.boundVars t1 ⊆ avoid :=
          fun x hx => h_bv (Finset.mem_union_left _ hx)
        have h_bv2 : Term.boundVars t2 ⊆ avoid :=
          fun x hx => h_bv (Finset.mem_union_right _ hx)
        exact .pair (Term.canonicalize avoid t1 h_V h_bv1)
                    (Term.canonicalize avoid t2 h_V h_bv2)
    | .boxterm tt hsub h_box_no_extras =>
        rename_i V_inner _
        have h_V_inner : VarCtx_to_VarSymbs V_inner ⊆ avoid := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨⟨v, S_v⟩, hvin, hveq⟩
          subst hveq
          apply h_V
          refine Finset.mem_image.mpr ⟨⟨v, S_v.VTypeBox⟩, ?_, rfl⟩
          exact hsub (Finset.mem_image.mpr ⟨⟨v, S_v⟩, hvin, rfl⟩)
        exact .boxterm (Term.canonicalize avoid tt h_V_inner h_bv) hsub h_box_no_extras
    | .diaterm x hx tt hsub h_dia_no_extras =>
        rename_i V_inner _
        have h_V_extended : VarCtx_to_VarSymbs (VarCtx_insert x V_inner hx) ⊆ avoid := by
          intro y hy
          rw [VarCtx_to_VarSymbs_insert] at hy
          rcases Finset.mem_insert.mp hy with rfl | hy'
          · apply h_V
            refine Finset.mem_image.mpr ⟨⟨x.1, x.2.VTypeDia⟩, ?_, rfl⟩
            exact hsub (by rw [dia_VarCtx_fst]; exact Finset.mem_insert_self _ _)
          · rcases Finset.mem_image.mp hy' with ⟨⟨v, S_v⟩, hvin, hveq⟩
            subst hveq
            apply h_V
            refine Finset.mem_image.mpr ⟨⟨v, S_v.VTypeBox⟩, ?_, rfl⟩
            exact hsub (by
              rw [dia_VarCtx_fst]
              exact Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨⟨v, S_v⟩, hvin, rfl⟩))
        have h_bv_tt : Term.boundVars tt ⊆ avoid :=
          fun y hy => h_bv (Finset.mem_insert_of_mem hy)
        exact .diaterm x hx (Term.canonicalize avoid tt h_V_extended h_bv_tt) hsub
                       h_dia_no_extras
    | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body =>
        rename_i V_inner W₁
        -- v1.1, v2.1 are genuine binders; rename to canonical fresh names.
        -- Extract pieces of boundVars t ⊆ avoid:
        --   boundVars t = insert v1.1 (insert v2.1 (insert z (boundVars body)))
        have hv1_in : v1.1 ∈ avoid := h_bv (Finset.mem_insert_self _ _)
        have hv2_in : v2.1 ∈ avoid :=
          h_bv (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have h_body_bv : Term.boundVars body ⊆ avoid := fun y hy =>
          h_bv (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem hy)))
        -- VarSymbs V_inner ⊆ avoid (from V = V_inner + z via w2eq, and h_V).
        have h_Vi : VarCtx_to_VarSymbs V_inner ⊆ avoid := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨w, hwin, hweq⟩
          apply h_V
          refine Finset.mem_image.mpr ⟨w, ?_, hweq⟩
          rw [← w2eq]; exact Finset.mem_insert_of_mem hwin
        -- Pick the two canonical names.
        let v1c := VarSymb.fresh avoid
        have hv1c_avoid : v1c ∉ avoid := VarSymb.fresh_not_mem avoid
        let avoid₁ : Finset VarSymb := insert v1c avoid
        let v2c := VarSymb.fresh avoid₁
        have hv2c_avoid₁ : v2c ∉ avoid₁ := VarSymb.fresh_not_mem avoid₁
        have hv2c_ne_v1c : v2c ≠ v1c :=
          fun h => hv2c_avoid₁ (h ▸ Finset.mem_insert_self _ _)
        have hv2c_avoid : v2c ∉ avoid :=
          fun h => hv2c_avoid₁ (Finset.mem_insert_of_mem h)
        have hv1c_ne_v2c : v1c ≠ v2c := fun h => hv2c_ne_v1c h.symm
        -- Freshness derivations.
        have hv1c_Vi : v1c ∉ VarCtx_to_VarSymbs V_inner :=
          fun h => hv1c_avoid (h_Vi h)
        have hv2c_Vi : v2c ∉ VarCtx_to_VarSymbs V_inner :=
          fun h => hv2c_avoid (h_Vi h)
        have hv1c_ne_v1 : v1c ≠ v1.1 :=
          fun h => hv1c_avoid (h ▸ hv1_in)
        have hv1c_ne_v2 : v1c ≠ v2.1 :=
          fun h => hv1c_avoid (h ▸ hv2_in)
        have hv2c_ne_v2 : v2c ≠ v2.1 :=
          fun h => hv2c_avoid (h ▸ hv2_in)
        have hv2_ne_v1c : v2.1 ≠ v1c := fun h => hv1c_ne_v2 h.symm
        -- Freshness of v1, v1c in VarCtx_insert v2 V_inner.
        have hv1_in_iv2 : v1.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v2 V_inner hv2) :=
          not_mem_VarSymbs_insert hv1v2 hv1
        have hv1c_in_iv2 : v1c ∉ VarCtx_to_VarSymbs (VarCtx_insert v2 V_inner hv2) :=
          not_mem_VarSymbs_insert hv1c_ne_v2 hv1c_Vi
        -- Wdef1: W₁ = VarCtx_insert ⟨v1.1, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1_in_iv2.
        have Wdef1 : W₁ =
            VarCtx_insert ⟨v1.1, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1_in_iv2 := by
          rw [← w1eq]; apply VarCtx_ext; rfl
        have hv1c_nb_body : v1c ∉ Term.boundVars body :=
          fun h => hv1c_avoid (h_body_bv h)
        -- First rename: body in W₁, v1.1 → v1c.
        let body₁ : Term σ
            (VarCtx_insert ⟨v1c, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1c_in_iv2) S :=
          Term.rename v1.1 v1c v1.2 (VarCtx_insert v2 V_inner hv2) W₁ S
            hv1_in_iv2 hv1c_in_iv2 Wdef1 body hv1c_nb_body
        -- For the second rename, swap insertion order via VarCtx_insert_comm.
        have hv2_in_iv1c : v2.1 ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) :=
          not_mem_VarSymbs_insert hv2_ne_v1c hv2
        have hv2c_in_iv1c : v2c ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) :=
          not_mem_VarSymbs_insert hv2c_ne_v1c hv2c_Vi
        -- The body₁ context expressed with v2 on the outside (via comm).
        have Wdef2 :
            (VarCtx_insert ⟨v1c, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1c_in_iv2)
              = VarCtx_insert ⟨v2.1, v2.2⟩
                  (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) hv2_in_iv1c :=
          VarCtx_insert_comm hv1c_in_iv2 hv2_in_iv1c
        -- v2c ∉ boundVars body₁ (from boundVars_rename_subset).
        have h_body₁_bv : Term.boundVars body₁ ⊆ insert v1c (Term.boundVars body) :=
          Term.boundVars_rename_subset v1.1 v1c v1.2
            (VarCtx_insert v2 V_inner hv2) W₁ S
            hv1_in_iv2 hv1c_in_iv2 Wdef1 body hv1c_nb_body
        have hv2c_nb_body₁ : v2c ∉ Term.boundVars body₁ := by
          intro h
          rcases Finset.mem_insert.mp (h_body₁_bv h) with heq | h'
          · exact hv2c_ne_v1c heq
          · exact hv2c_avoid (h_body_bv h')
        -- Second rename: body₁ → body₂ replacing v2.1 with v2c.
        let body₂ : Term σ
            (VarCtx_insert ⟨v2c, v2.2⟩ (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) hv2c_in_iv1c) S :=
          Term.rename v2.1 v2c v2.2
            (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi)
            (VarCtx_insert ⟨v1c, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1c_in_iv2) S
            hv2_in_iv1c hv2c_in_iv1c Wdef2 body₁ hv2c_nb_body₁
        -- Recursive canonicalize on body₂.
        let avoid₂ : Finset VarSymb := insert v2c avoid₁
        have h_V_canon : VarCtx_to_VarSymbs
            (VarCtx_insert ⟨v2c, v2.2⟩ (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) hv2c_in_iv1c)
            ⊆ avoid₂ := by
          intro y hy
          rw [VarCtx_to_VarSymbs_insert] at hy
          rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact Finset.mem_insert_self _ _
          · rw [VarCtx_to_VarSymbs_insert] at hy'
            rcases Finset.mem_insert.mp hy' with rfl | hy''
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (h_Vi hy''))
        have h_body₂_bv_step : Term.boundVars body₂ ⊆ insert v2c (Term.boundVars body₁) :=
          Term.boundVars_rename_subset v2.1 v2c v2.2
            (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi)
            (VarCtx_insert ⟨v1c, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1c_in_iv2) S
            hv2_in_iv1c hv2c_in_iv1c Wdef2 body₁ hv2c_nb_body₁
        have h_bv_canon : Term.boundVars body₂ ⊆ avoid₂ := by
          intro y hy
          rcases Finset.mem_insert.mp (h_body₂_bv_step hy) with rfl | h'
          · exact Finset.mem_insert_self _ _
          · rcases Finset.mem_insert.mp (h_body₁_bv h') with rfl | h''
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (h_body_bv h''))
        let body_canon := Term.canonicalize avoid₂ body₂ h_V_canon h_bv_canon
        -- Re-assemble. new_w1eq aligns the body's context with the
        -- VarCtx_insert_twice expected by pair_elim.
        have new_w1eq :
            VarCtx_insert_twice ⟨v1c, v1.2⟩ ⟨v2c, v2.2⟩ V_inner hv1c_Vi hv2c_Vi hv1c_ne_v2c
              = VarCtx_insert ⟨v2c, v2.2⟩
                  (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) hv2c_in_iv1c := by
          apply VarCtx_ext
          exact Finset.insert_comm _ _ _
        exact .pair_elim ⟨v1c, v1.2⟩ ⟨v2c, v2.2⟩ z
                hv1c_Vi hv2c_Vi hv1c_ne_v2c hz
                new_w1eq w2eq body_canon
  termination_by Term.numNodes t
  decreasing_by
    -- Most cases: structural subterm, `decreasing_tactic` handles via sizeOf-
    -- on-numNodes. The pair_elim recurse goal is `Term.numNodes (rename …
    -- (rename … body …) …) < (.pair_elim … body).numNodes`; `Term.numNodes_rename`
    -- rewrites both rename applications to `body.numNodes`, then `omega` closes.
    all_goals first
      | decreasing_tactic
      | (simp only [Term.numNodes, Term.numNodes_rename]; omega)

  def Func.canonicalize {σ : Signature} {V : VarCtx} {N : ℕ}
      (avoid : Finset VarSymb) (f : Func σ V N)
      (h_V : VarCtx_to_VarSymbs V ⊆ avoid)
      (h_bv : Func.boundVars f ⊆ avoid)
      : Func σ V N := by
    match f with
    | .F h => exact .F h
    | .eval g t =>
        have h_bv_g : Func.boundVars g ⊆ avoid :=
          fun x hx => h_bv (Finset.mem_union_left _ hx)
        have h_bv_t : Term.boundVars t ⊆ avoid :=
          fun x hx => h_bv (Finset.mem_union_right _ hx)
        exact .eval (Func.canonicalize avoid g h_V h_bv_g)
                    (Term.canonicalize avoid t h_V h_bv_t)
  termination_by Func.numNodes f
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (simp only [Func.numNodes]; omega)
end

-- Term-for-term substitution at a fixed context.
--
-- `t.subst t_old t_new` replaces every occurrence of `t_old` inside `t` with
-- `t_new`. The strategy is "maximally unpair" the outer context: peel every
-- pair-typed variable in `V` into two component variables (in `t`, `t_old` and
-- `t_new` coordinately), substitute structurally on the now pair-free form,
-- then re-pair to land back in `V`.
--
-- Type-based dispatch: at the boxterm/diaterm level we descend into the modal
-- interior only when the modal types match and the inner contexts agree
-- (i.e. the boxterm/diaterm has been weakened the same way on all three sides).
--
-- First cut: handles the context-preserving structural cases (var, func, unit,
-- pair). The context-changing cases (boxterm, diaterm, pair_elim body) leave
-- their inner unchanged for now; the maximal-unpair / type-based descent is
-- TODO.
--
-- TODO — maximal-unpair preprocessing. Foundations are in place:
--   · `VarType.isPair`, `VarCtx.hasPairVar` + `Decidable` instance — detect
--     whether V contains a VTypeProd-typed binder
--   · `VarType.pairDepth`, `VarCtx.pairDepth` — termination measure
--   · `Term.unpair` / `Func.unpair` — single-step unpair (already exists)
--   · `Term.repair` — inverse, wraps a body in a `pair_elim` (already exists)
--   · `VarSymb.fresh` — deterministic fresh-symbol generator
-- Planned redesign of `Term.subst` (wrap around the current α-aware body):
--   if V.hasPairVar then
--     · extract z, V1, V2 + membership proof (deterministically, e.g. via
--       V.1.toList.find?-style search)
--     · pick fresh component symbols v1, v2 from
--         VarCtx_to_VarSymbs V ∪ Term.boundVars t ∪ Term.boundVars t_old
--           ∪ Term.boundVars t_new
--     · compute V_minus_z := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩
--     · unpair t, t_old, t_new in lock-step (same v1, v2) → t', t_old', t_new'
--       in V' := VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_minus_z _ _ _
--     · recurse: result' := Term.subst t' t_old' t_new'  (V'.pairDepth < V.pairDepth)
--     · re-pair: result := Term.repair z V1 V2 v1 v2 V_minus_z V' V _ _ _ _ rfl rfl result'
--   else
--     · existing α-aware structural sub (canonicalize-based equality check)
-- Termination: `termination_by VarCtx.pairDepth V`. Needs a lemma showing the
-- unpair step strictly decreases pairDepth (one VTypeProd consumed, two
-- smaller-depth components produced).
-- Unified termination: lex `(V.pairDepth, sizeOf t, phase)` where phase ∈ {0,1,2}
-- discriminates between the four mutually-recursive functions.
--
--   • `Term.substMU` (phase 2) — outermost. Strips one pair-typed binder via
--     `Term.unpair`, recurses on V' with strictly smaller `pairDepth`. At a
--     pair-free V (firstPairVar = none), delegates to `Term.subst` (same V,
--     same t, phase ↓: 2 → 1).
--
--   • `Term.subst` (phase 1) — α-aware equality test, delegates the structural
--     recursion to `Term.substChildren` (same V, same t, phase ↓: 1 → 0).
--
--   • `Term.substChildren` (phase 0) — pattern-matches on `t` and recurses on
--     subterms via `Term.subst` (sizeOf decreases at same V); at the boxterm/
--     diaterm interior calls `Term.substMU` on the inner context `V_inner`
--     (pairDepth ≤, with strict sizeOf decrease when equal — see
--     `VarCtx.pairDepth_le_of_box_subset` / `_dia_subset`).
--
--   • `Func.substTerm` (phase 0) — structural on `Func`, with `Term.subst` on
--     the embedded `Term`. sizeOf decreases at same V.
mutual
  -- α-aware equality: canonicalize `t` and `t_old` with the SAME `avoid` set
  -- so both pick the same canonical names at each binder, then compare the
  -- (DecidableEq-able) canonical forms structurally.
  def Term.subst {σ : Signature} {V : VarCtx} {S S' : VarType}
      (t : Term σ V S) (t_old t_new : Term σ V S') : Term σ V S := by
    by_cases hS : S = S'
    · cases hS
      let avoid : Finset VarSymb :=
        VarCtx_to_VarSymbs V ∪ Term.boundVars t ∪ Term.boundVars t_old
      have h_V : VarCtx_to_VarSymbs V ⊆ avoid := fun x hx =>
        Finset.mem_union_left _ (Finset.mem_union_left _ hx)
      have h_bv_t : Term.boundVars t ⊆ avoid := fun x hx =>
        Finset.mem_union_left _ (Finset.mem_union_right _ hx)
      have h_bv_t_old : Term.boundVars t_old ⊆ avoid := fun x hx =>
        Finset.mem_union_right _ hx
      exact if Term.canonicalize avoid t h_V h_bv_t
             = Term.canonicalize avoid t_old h_V h_bv_t_old
        then t_new
        else Term.substChildren t t_old t_new
    · exact Term.substChildren t t_old t_new
  termination_by (V.pairDepth, sizeOf t, 1)
  decreasing_by
    all_goals (refine Prod.Lex.right _ (Prod.Lex.right _ ?_); decide)

  def Term.substChildren {σ : Signature} {V : VarCtx} {S S' : VarType}
      (t : Term σ V S) (t_old t_new : Term σ V S') : Term σ V S := by
    match t with
    | .var v          => exact .var v
    | .func f         => exact .func (Func.substTerm f t_old t_new)
    | .unit           => exact .unit
    | .pair t1 t2     =>
        exact .pair (Term.subst t1 t_old t_new) (Term.subst t2 t_old t_new)
    | @Term.boxterm _ V_inner_t _ _ tt hsub h_no_extras =>
        -- Type-based modal descent: if S = S' (both VTypeBox S_inner) and t_old,
        -- t_new are also `.boxterm` constructors with the SAME inner context as
        -- tt, recursively substitute inside tt via substMU. Otherwise leave
        -- unchanged. Termination: V_inner_t.pairDepth ≤ V.pairDepth (by
        -- `pairDepth_le_of_box_subset hsub`); when equal, sizeOf tt < sizeOf t.
        by_cases hS : S = S'
        · cases hS
          match t_old, t_new with
          | @Term.boxterm _ V_inner_old _ _ tt_old _ _,
            @Term.boxterm _ V_inner_new _ _ tt_new _ _ =>
              if h_old : V_inner_t.1 = V_inner_old.1 then
                if h_new : V_inner_t.1 = V_inner_new.1 then
                  have h_V_old : V_inner_t = V_inner_old := VarCtx_ext _ _ h_old
                  have h_V_new : V_inner_t = V_inner_new := VarCtx_ext _ _ h_new
                  exact .boxterm
                    (Term.substMU tt (h_V_old.symm ▸ tt_old) (h_V_new.symm ▸ tt_new))
                    hsub h_no_extras
                else exact .boxterm tt hsub h_no_extras
              else exact .boxterm tt hsub h_no_extras
          | _, _ => exact .boxterm tt hsub h_no_extras
        · exact .boxterm tt hsub h_no_extras
    | @Term.diaterm _ V_inner_t _ _ xv hx tt hsub h_no_extras =>
        -- Diaterm descent: like boxterm, but tt lives in (V_inner_t + xv).
        -- Termination via `pairDepth_le_of_dia_subset hsub` on the inner
        -- context `VarCtx_insert xv V_inner_t hx`.
        by_cases hS : S = S'
        · cases hS
          match t_old, t_new with
          | @Term.diaterm _ V_inner_old _ _ xv_old hx_old tt_old _ _,
            @Term.diaterm _ V_inner_new _ _ xv_new hx_new tt_new _ _ =>
              if h_old : (VarCtx_insert xv V_inner_t hx).1
                       = (VarCtx_insert xv_old V_inner_old hx_old).1 then
                if h_new : (VarCtx_insert xv V_inner_t hx).1
                         = (VarCtx_insert xv_new V_inner_new hx_new).1 then
                  have eq_old : VarCtx_insert xv V_inner_t hx
                              = VarCtx_insert xv_old V_inner_old hx_old :=
                    VarCtx_ext _ _ h_old
                  have eq_new : VarCtx_insert xv V_inner_t hx
                              = VarCtx_insert xv_new V_inner_new hx_new :=
                    VarCtx_ext _ _ h_new
                  exact .diaterm xv hx
                    (Term.substMU tt (eq_old.symm ▸ tt_old) (eq_new.symm ▸ tt_new))
                    hsub h_no_extras
                else exact .diaterm xv hx tt hsub h_no_extras
              else exact .diaterm xv hx tt hsub h_no_extras
          | _, _ => exact .diaterm xv hx tt hsub h_no_extras
        · exact .diaterm xv hx tt hsub h_no_extras
    | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body =>
        -- α-rename body's binders v1.1, v2.1 to fresh v1c, v2c (avoiding
        -- boundVars of t, t_old, t_new and the outer VarCtx), then unpair
        -- t_old, t_new at z using v1c, v2c to bring them into body's
        -- (renamed) context, then recursively substitute via `Term.substMU`.
        -- The recursive context `W' = V_inner + {v1c, v2c}` has pairDepth
        -- strictly less than V's (one VTypeProd binder peeled — see
        -- `VarCtx.pairDepth_pair_elim_lt`), so the lex measure's first
        -- coord decreases.
        rename_i V_inner W₁
        -- We refer to the pair_elim form explicitly (rather than via `t`) in
        -- types of subsequent `have`s. The match refines `t` in pre-existing
        -- parameter types, but Lean's elaborator does NOT propagate the
        -- refinement to types of locally-declared `have`s — so `Term.boundVars t`
        -- in a fresh `have`'s type stays unreduced. Using the explicit
        -- constructor form makes iota-reduction kick in for elaboration.
        let pe_t : Term σ V S :=
          Term.pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body
        let avoid : Finset VarSymb :=
          VarCtx_to_VarSymbs V ∪ Term.boundVars pe_t
            ∪ Term.boundVars t_old ∪ Term.boundVars t_new
        let v1c := VarSymb.fresh avoid
        have hv1c_avoid : v1c ∉ avoid := VarSymb.fresh_not_mem avoid
        let avoid₁ : Finset VarSymb := insert v1c avoid
        let v2c := VarSymb.fresh avoid₁
        have hv2c_avoid₁ : v2c ∉ avoid₁ := VarSymb.fresh_not_mem avoid₁
        have hv2c_ne_v1c : v2c ≠ v1c :=
          fun h => hv2c_avoid₁ (h ▸ Finset.mem_insert_self _ _)
        have hv2c_avoid : v2c ∉ avoid :=
          fun h => hv2c_avoid₁ (Finset.mem_insert_of_mem h)
        have hv1c_ne_v2c : v1c ≠ v2c := fun h => hv2c_ne_v1c h.symm
        -- Component avoid-subsets.
        have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun x hx =>
          Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
        -- h_avoid_pe_t uses `Term.boundVars pe_t` (the explicit constructor
        -- form) rather than `Term.boundVars t`; the former iota-reduces, the
        -- latter doesn't (Lean's match refinement leaves locally-declared
        -- types referring to the original variable `t`).
        have h_avoid_pe_t : Term.boundVars pe_t ⊆ avoid := fun x hx =>
          Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
        have h_avoid_t_old : Term.boundVars t_old ⊆ avoid := fun x hx =>
          Finset.mem_union_left _ (Finset.mem_union_right _ hx)
        have h_avoid_t_new : Term.boundVars t_new ⊆ avoid := fun x hx =>
          Finset.mem_union_right _ hx
        -- V_inner.symbols ⊆ avoid (via w2eq: V = V_inner + z).
        have h_Vi : VarCtx_to_VarSymbs V_inner ⊆ avoid := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨w, hwin, hweq⟩
          apply h_avoid_V
          refine Finset.mem_image.mpr ⟨w, ?_, hweq⟩
          rw [← w2eq]; exact Finset.mem_insert_of_mem hwin
        have hv1c_Vi : v1c ∉ VarCtx_to_VarSymbs V_inner :=
          fun h => hv1c_avoid (h_Vi h)
        have hv2c_Vi : v2c ∉ VarCtx_to_VarSymbs V_inner :=
          fun h => hv2c_avoid (h_Vi h)
        -- boundVars pe_t = insert v1.1 (insert v2.1 (insert z (boundVars body)))
        -- by iota on the explicit pair_elim form.
        have hv1_in : v1.1 ∈ avoid := h_avoid_pe_t (Finset.mem_insert_self _ _)
        have hv2_in : v2.1 ∈ avoid := h_avoid_pe_t
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have h_body_bv : Term.boundVars body ⊆ avoid := fun y hy =>
          h_avoid_pe_t (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem hy)))
        -- v1c, v2c distinct from v1.1, v2.1 (since v1.1, v2.1 ∈ avoid).
        have hv1c_ne_v2 : v1c ≠ v2.1 := fun h => hv1c_avoid (h ▸ hv2_in)
        have hv2_ne_v1c : v2.1 ≠ v1c := fun h => hv1c_ne_v2 h.symm
        -- Rename setup, mirroring `Term.canonicalize`'s pair_elim arm.
        have hv1_in_iv2 : v1.1 ∉ VarCtx_to_VarSymbs (VarCtx_insert v2 V_inner hv2) :=
          not_mem_VarSymbs_insert hv1v2 hv1
        have hv1c_in_iv2 : v1c ∉ VarCtx_to_VarSymbs (VarCtx_insert v2 V_inner hv2) :=
          not_mem_VarSymbs_insert hv1c_ne_v2 hv1c_Vi
        have Wdef1 : W₁ =
            VarCtx_insert ⟨v1.1, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1_in_iv2 := by
          rw [← w1eq]; apply VarCtx_ext; rfl
        have hv1c_nb_body : v1c ∉ Term.boundVars body :=
          fun h => hv1c_avoid (h_body_bv h)
        -- First rename: v1.1 → v1c.
        let body₁ : Term σ
            (VarCtx_insert ⟨v1c, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1c_in_iv2) S :=
          Term.rename v1.1 v1c v1.2 (VarCtx_insert v2 V_inner hv2) W₁ S
            hv1_in_iv2 hv1c_in_iv2 Wdef1 body hv1c_nb_body
        -- Swap insertion order for second rename.
        have hv2_in_iv1c : v2.1 ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) :=
          not_mem_VarSymbs_insert hv2_ne_v1c hv2
        have hv2c_in_iv1c : v2c ∉ VarCtx_to_VarSymbs
            (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) :=
          not_mem_VarSymbs_insert hv2c_ne_v1c hv2c_Vi
        have Wdef2 :
            (VarCtx_insert ⟨v1c, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1c_in_iv2)
              = VarCtx_insert ⟨v2.1, v2.2⟩
                  (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) hv2_in_iv1c :=
          VarCtx_insert_comm hv1c_in_iv2 hv2_in_iv1c
        have h_body₁_bv : Term.boundVars body₁ ⊆ insert v1c (Term.boundVars body) :=
          Term.boundVars_rename_subset v1.1 v1c v1.2
            (VarCtx_insert v2 V_inner hv2) W₁ S
            hv1_in_iv2 hv1c_in_iv2 Wdef1 body hv1c_nb_body
        have hv2c_nb_body₁ : v2c ∉ Term.boundVars body₁ := by
          intro h
          rcases Finset.mem_insert.mp (h_body₁_bv h) with heq | h'
          · exact hv2c_ne_v1c heq
          · exact hv2c_avoid (h_body_bv h')
        -- Second rename: v2.1 → v2c.
        let body₂ : Term σ
            (VarCtx_insert ⟨v2c, v2.2⟩ (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) hv2c_in_iv1c) S :=
          Term.rename v2.1 v2c v2.2
            (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi)
            (VarCtx_insert ⟨v1c, v1.2⟩ (VarCtx_insert v2 V_inner hv2) hv1c_in_iv2) S
            hv2_in_iv1c hv2c_in_iv1c Wdef2 body₁ hv2c_nb_body₁
        -- Realign body₂'s context to the VarCtx_insert_twice form.
        let W' : VarCtx :=
          VarCtx_insert_twice ⟨v1c, v1.2⟩ ⟨v2c, v2.2⟩ V_inner hv1c_Vi hv2c_Vi hv1c_ne_v2c
        have W'_eq : W' =
            VarCtx_insert ⟨v2c, v2.2⟩
              (VarCtx_insert ⟨v1c, v1.2⟩ V_inner hv1c_Vi) hv2c_in_iv1c := by
          apply VarCtx_ext; exact Finset.insert_comm _ _ _
        -- Unpair t_old, t_new at z using v1c, v2c (fresh by hv1c_avoid /
        -- hv2c_avoid w.r.t. boundVars).
        have hv1c_nb_t_old : v1c ∉ Term.boundVars t_old :=
          fun h => hv1c_avoid (h_avoid_t_old h)
        have hv2c_nb_t_old : v2c ∉ Term.boundVars t_old :=
          fun h => hv2c_avoid (h_avoid_t_old h)
        have hv1c_nb_t_new : v1c ∉ Term.boundVars t_new :=
          fun h => hv1c_avoid (h_avoid_t_new h)
        have hv2c_nb_t_new : v2c ∉ Term.boundVars t_new :=
          fun h => hv2c_avoid (h_avoid_t_new h)
        let t_old' : Term σ W' S' :=
          Term.unpair z v1.2 v2.2 v1c v2c V_inner V W' S'
            hz hv1c_Vi hv2c_Vi hv1c_ne_v2c w2eq.symm rfl t_old
            hv1c_nb_t_old hv2c_nb_t_old
        let t_new' : Term σ W' S' :=
          Term.unpair z v1.2 v2.2 v1c v2c V_inner V W' S'
            hz hv1c_Vi hv2c_Vi hv1c_ne_v2c w2eq.symm rfl t_new
            hv1c_nb_t_new hv2c_nb_t_new
        -- Recursively substitute in the renamed body (cast to W' via W'_eq.symm).
        let body_subbed : Term σ W' S :=
          Term.substMU (W'_eq.symm ▸ body₂) t_old' t_new'
        -- Reconstruct pair_elim with v1c, v2c.
        exact .pair_elim ⟨v1c, v1.2⟩ ⟨v2c, v2.2⟩ z
                hv1c_Vi hv2c_Vi hv1c_ne_v2c hz
                rfl w2eq body_subbed
  termination_by (V.pairDepth, sizeOf t, 0)
  decreasing_by
    all_goals first
      -- structural sizeOf decrease on subterms of `.pair` / `.func` (same V).
      | (refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_); decreasing_tactic)
      -- boxterm modal descent: pairDepth ≤, with strict sizeOf when equal.
      | (have h_le := VarCtx.pairDepth_le_of_box_subset hsub
         rcases Nat.lt_or_eq_of_le h_le with h_lt | h_eq
         · exact Prod.Lex.left _ _ h_lt
         · rw [h_eq]
           refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
           decreasing_tactic)
      -- diaterm modal descent: analogous to boxterm.
      | (have h_le := VarCtx.pairDepth_le_of_dia_subset hsub
         rcases Nat.lt_or_eq_of_le h_le with h_lt | h_eq
         · exact Prod.Lex.left _ _ h_lt
         · rw [h_eq]
           refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_)
           decreasing_tactic)
      -- pair_elim body descent: W'.pairDepth < V.pairDepth (one binder peeled).
      | (exact Prod.Lex.left _ _
           (VarCtx.pairDepth_pair_elim_lt w2eq hv1c_Vi hv2c_Vi hv1c_ne_v2c))

  def Func.substTerm {σ : Signature} {V : VarCtx} {N : ℕ} {S' : VarType}
      (f : Func σ V N) (t_old t_new : Term σ V S') : Func σ V N := by
    match f with
    | .F h      => exact .F h
    | .eval g t => exact .eval (Func.substTerm g t_old t_new) (Term.subst t t_old t_new)
  termination_by (V.pairDepth, sizeOf f, 0)
  decreasing_by
    all_goals (refine Prod.Lex.right _ (Prod.Lex.left _ _ ?_); decreasing_tactic)

  -- Maximal-Unpair preprocessing wrapper. When V contains a VTypeProd binder
  -- z, picks fresh component symbols v1, v2, lock-step unpairs t/t_old/t_new
  -- from V to V' = (V \ {z}) ∪ {v1, v2}, recursively substitutes in V'
  -- (strictly smaller pairDepth), and re-pairs the result with `pair_elim`.
  -- When V is pair-free, delegates to the α-aware `Term.subst`.
  def Term.substMU {σ : Signature} {V : VarCtx} {S S' : VarType}
      (t : Term σ V S) (t_old t_new : Term σ V S') : Term σ V S := by
    match h_pv : V.firstPairVar with
    | none =>
        exact Term.subst t t_old t_new
    | some ⟨(z, V1, V2), hzmem⟩ =>
        let V_minus_z := VarCtx_erase V ⟨z, V1.VTypeProd V2⟩
        have hz_fresh : z ∉ VarCtx_to_VarSymbs V_minus_z :=
          VarCtx_erase_fresh hzmem
        have Vdef : VarCtx_insert ⟨z, V1.VTypeProd V2⟩ V_minus_z hz_fresh = V :=
          VarCtx_insert_erase hzmem hz_fresh
        let avoid : Finset VarSymb :=
          VarCtx_to_VarSymbs V
            ∪ Term.boundVars t ∪ Term.boundVars t_old ∪ Term.boundVars t_new
        let v1 : VarSymb := VarSymb.fresh avoid
        have hv1_avoid : v1 ∉ avoid := VarSymb.fresh_not_mem avoid
        let v2 : VarSymb := VarSymb.fresh (insert v1 avoid)
        have hv2_avoid_v1 : v2 ∉ insert v1 avoid :=
          VarSymb.fresh_not_mem (insert v1 avoid)
        have hv2_avoid : v2 ∉ avoid := fun h =>
          hv2_avoid_v1 (Finset.mem_insert_of_mem h)
        have hv1v2_ne : v1 ≠ v2 := fun h =>
          hv2_avoid_v1 (h ▸ Finset.mem_insert_self _ _)
        have h_avoid_V : VarCtx_to_VarSymbs V ⊆ avoid := fun x hx =>
          Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
        have h_avoid_t : Term.boundVars t ⊆ avoid := fun x hx =>
          Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
        have h_avoid_t_old : Term.boundVars t_old ⊆ avoid := fun x hx =>
          Finset.mem_union_left _ (Finset.mem_union_right _ hx)
        have h_avoid_t_new : Term.boundVars t_new ⊆ avoid := fun x hx =>
          Finset.mem_union_right _ hx
        have hv1_V : v1 ∉ VarCtx_to_VarSymbs V := fun h => hv1_avoid (h_avoid_V h)
        have hv2_V : v2 ∉ VarCtx_to_VarSymbs V := fun h => hv2_avoid (h_avoid_V h)
        have hv1_Vmz : v1 ∉ VarCtx_to_VarSymbs V_minus_z := fun h =>
          hv1_V (VarCtx_to_VarSymbs_erase_subset h)
        have hv2_Vmz : v2 ∉ VarCtx_to_VarSymbs V_minus_z := fun h =>
          hv2_V (VarCtx_to_VarSymbs_erase_subset h)
        have hv1_nb_t : v1 ∉ Term.boundVars t := fun h => hv1_avoid (h_avoid_t h)
        have hv2_nb_t : v2 ∉ Term.boundVars t := fun h => hv2_avoid (h_avoid_t h)
        have hv1_nb_t_old : v1 ∉ Term.boundVars t_old := fun h =>
          hv1_avoid (h_avoid_t_old h)
        have hv2_nb_t_old : v2 ∉ Term.boundVars t_old := fun h =>
          hv2_avoid (h_avoid_t_old h)
        have hv1_nb_t_new : v1 ∉ Term.boundVars t_new := fun h =>
          hv1_avoid (h_avoid_t_new h)
        have hv2_nb_t_new : v2 ∉ Term.boundVars t_new := fun h =>
          hv2_avoid (h_avoid_t_new h)
        let V' : VarCtx :=
          VarCtx_insert_twice ⟨v1, V1⟩ ⟨v2, V2⟩ V_minus_z hv1_Vmz hv2_Vmz hv1v2_ne
        let t' : Term σ V' S :=
          Term.unpair z V1 V2 v1 v2 V_minus_z V V' S
            hz_fresh hv1_Vmz hv2_Vmz hv1v2_ne Vdef.symm rfl t hv1_nb_t hv2_nb_t
        let t_old' : Term σ V' S' :=
          Term.unpair z V1 V2 v1 v2 V_minus_z V V' S'
            hz_fresh hv1_Vmz hv2_Vmz hv1v2_ne Vdef.symm rfl t_old
            hv1_nb_t_old hv2_nb_t_old
        let t_new' : Term σ V' S' :=
          Term.unpair z V1 V2 v1 v2 V_minus_z V V' S'
            hz_fresh hv1_Vmz hv2_Vmz hv1v2_ne Vdef.symm rfl t_new
            hv1_nb_t_new hv2_nb_t_new
        let result' : Term σ V' S := Term.substMU t' t_old' t_new'
        exact .pair_elim ⟨v1, V1⟩ ⟨v2, V2⟩ z hv1_Vmz hv2_Vmz hv1v2_ne hz_fresh
                rfl Vdef result'
  termination_by (V.pairDepth, sizeOf t, 2)
  decreasing_by
    all_goals first
      -- `none` branch: substMU → subst at same (V, t), phase 1 < 2.
      | (refine Prod.Lex.right _ (Prod.Lex.right _ ?_); decide)
      -- `some` branch: substMU → substMU at strictly smaller pairDepth.
      | (exact Prod.Lex.left _ _
           (VarCtx.pairDepth_unpair_lt hzmem hv1_Vmz hv2_Vmz hv1v2_ne))
end

/-! ## Context Restriction (substitute a variable with a term) -/

-- Given `s : Term σ V S` and `t : Term σ (V + ⟨x, S⟩) S'`, produce a
-- `Term σ V S'` by replacing every occurrence of the variable `x` in `t` with
-- the term `s`. This is the QML analogue of `QML_FOL.lean`'s `ctx_rest_term`,
-- extended to handle modalities and pairing.
--
-- Design (mirroring `Term.subst` / `Term.substMU`):
--   • The structural pass `Term.ctx_rest_term` walks `t` directly, replacing
--     `.var x` with `s` and structurally recursing through `.func`/`.pair`.
--   • At a `.boxterm` (resp. `.diaterm`) interior, if `x ∉ V_inner` the body
--     never references `x`, so we descend trivially. If `x ∈ V_inner` (which
--     forces `S = T.VTypeBox` / `T.VTypeDia`), the inner substitute is the
--     `.inner` field of `s` — `s` itself must be a `.boxterm` / `.diaterm`,
--     since after maximal-unpair preprocessing those are the only ways to
--     construct a term of box / dia type in a pair-free context.
--   • `.pair_elim` is unreachable in a pair-free outer context (its scrutinee
--     `z` has pair type, but no binder of `V_ext` does); the wrapper
--     `Term.ctx_rest_term_MU` performs maximal-unpair preprocessing.
--
-- For now the modal-interior recurse and pair_elim cases are `sorry`d while
-- we settle on the exact handling for box-typed `.var` and pair_elim shapes.
mutual
  def Func.ctx_rest_term {σ : Signature} {V : VarCtx} {N : ℕ}
      {x : VarSymb} {S : VarType}
      (hx : x ∉ VarCtx_to_VarSymbs V)
      (s : Term σ V S)
      (f : Func σ (VarCtx_insert ⟨x, S⟩ V hx) N) : Func σ V N := by
    match f with
    | .F h      => exact .F h
    | .eval g t =>
        exact .eval (Func.ctx_rest_term hx s g) (Term.ctx_rest_term hx s t)

  def Term.ctx_rest_term {σ : Signature} {V : VarCtx}
      {x : VarSymb} {S S' : VarType}
      (hx : x ∉ VarCtx_to_VarSymbs V)
      (s : Term σ V S)
      (t : Term σ (VarCtx_insert ⟨x, S⟩ V hx) S') : Term σ V S' := by
    match t with
    | .var ⟨w, hw⟩ =>
        -- hw : ⟨w, S'⟩ ∈ insert ⟨x, S⟩ V.1
        by_cases h_eq : (⟨w, S'⟩ : VarSymb × VarType) = ⟨x, S⟩
        · -- w = x and S' = S; replace with s.
          have hS_eq : S' = S := congrArg Prod.snd h_eq
          subst hS_eq
          exact s
        · -- ⟨w, S'⟩ ∈ V.1.
          exact .var ⟨w, (Finset.mem_insert.mp hw).resolve_left h_eq⟩
    | .func f =>
        exact .func (Func.ctx_rest_term hx s f)
    | .unit =>
        exact .unit
    | .pair t1 t2 =>
        exact .pair (Term.ctx_rest_term hx s t1) (Term.ctx_rest_term hx s t2)
    | @Term.boxterm _ V_inner _ _ tt hsub h_no_extras =>
        -- Case-analyse on whether `x` is in `V_inner`'s symbols. If not, the
        -- box interior doesn't reference `x`; just adjust hsub / h_no_extras
        -- to drop ⟨x, S⟩.
        by_cases h_x_in : x ∈ VarCtx_to_VarSymbs V_inner
        · -- x ∈ V_inner: forces S = T.VTypeBox (where T = x's inner type),
          -- and the recursive substitute for inner x is `s.inner` when `s`
          -- is itself a `.boxterm`. TODO: implement.
          --
          -- Implementation notes (we paused here — see chat):
          --   • Can't `rcases Finset.mem_image.mp h_x_in with ⟨⟨_, T⟩, ...⟩`
          --     to extract T computationally — `Exists` lives in Prop and
          --     can't eliminate into Type. Need either:
          --       (a) `cases S with | VTypeBox T => ... | _ => exfalso ...`
          --           (works but the non-box branches all need a Prop-level
          --           contradiction proof from h_x_in + h_no_extras).
          --       (b) Use `Decidable` membership on V_inner.1 filtered by
          --           first component = x, picking the unique witness.
          --   • Once T is extracted, prove V_s = V_inner_minus_x via the
          --     already-added `box_VarCtx_inj` and a Finset extensionality
          --     argument chaining hsub / h_no_extras / s_hsub / s_h_no_extras.
          --     The proof body is ~30 lines (sketched in chat history).
          sorry
        · -- x ∉ V_inner: trivial passthrough.
          have hsub' : (box_VarCtx V_inner).1 ⊆ V.1 := by
            intro p hp
            rcases Finset.mem_insert.mp (hsub hp) with h_eq | h_V
            · subst h_eq
              exfalso
              rcases Finset.mem_image.mp hp with ⟨w, hw, hweq⟩
              exact h_x_in
                (Finset.mem_image.mpr ⟨w, hw, (Prod.mk.inj hweq).1⟩)
            · exact h_V
          have h_no_extras' :
              ∀ p ∈ V.1, VarType.isBox p.2 = true → p ∈ (box_VarCtx V_inner).1 :=
            fun p hp h_box => h_no_extras p (Finset.mem_insert_of_mem hp) h_box
          exact .boxterm tt hsub' h_no_extras'
    | @Term.diaterm _ V_inner _ _ xv hxv tt hsub h_no_extras =>
        -- Three sub-cases: xv.1 = x (x is the dia binder); xv.1 ≠ x with
        -- x ∉ V_inner (trivial passthrough); xv.1 ≠ x with x ∈ V_inner
        -- (recursive descent — `s` must be `.diaterm` analogously). TODO.
        sorry
    | .pair_elim v1 v2 z hv1 hv2 hv1v2 hz w1eq w2eq body =>
        -- Unreachable when V_ext is pair-free (max-unpair guarantees this).
        -- TODO: either prove unreachable via a precondition, or handle.
        sorry
end

/-
-- Plan: finish term replacement, then make a function to split apart a product into a term
-- in a context with two variables, then write a term subst function using that.


/-! ## Global Terms -/

-- Context-free terms for equality comparison. No VarCtx parameter, no `wk`.
-- Mirrors the QML_FOL.lean pattern: a mutual inductive with a `GlobalFunc σ n`
-- spine avoids function-type fields, allowing `deriving DecidableEq` on both types.
--
-- `GlobalFunc σ n` is an n-ary function symbol, possibly partially applied.
-- `GlobalTerm σ` is a fully-applied (0-ary) function, variable, or compound term.
--
-- Term equality for substitution: a ≈ b ↔ a.toGlobal = b.toGlobal.
-- α-equivalence for `pair_elim` binders is handled by `GlobalTerm.AlphaEq`.
mutual
  inductive GlobalFunc (σ : Signature) : ℕ → Type where
    | F    : {f : σ.FuncSyms // σ.funcArity f = n} → GlobalFunc σ n
    | eval : GlobalFunc σ (Nat.succ n) → GlobalTerm σ .Var → GlobalFunc σ n
    deriving DecidableEq

  inductive GlobalTerm (σ : Signature) : VarType → Type where
    | var       : VarSymb → (τ : VarType) → GlobalTerm σ τ
    | func      : GlobalFunc σ 0 → GlobalTerm σ .Var
    | boxterm   : GlobalTerm σ S → GlobalTerm σ S.VTypeBox
    | diaterm   : GlobalTerm σ S → GlobalTerm σ S.VTypeDia
    | unit      : GlobalTerm σ .VTypeOne
    | pair      : GlobalTerm σ S → GlobalTerm σ T → GlobalTerm σ (.VTypeProd S T)
    | pair_elim : (v₁ v₂ : VarSymb × VarType) →
                  GlobalTerm σ (.VTypeProd v₁.2 v₂.2) →
                  GlobalTerm σ τ → GlobalTerm σ τ
    deriving DecidableEq
end

-- Build a fully-applied GlobalFunc from a function symbol and its arguments.
private def applyGlobalArgs {σ : Signature} :
    {n : ℕ} → GlobalFunc σ n → (Fin n → GlobalTerm σ .Var) → GlobalFunc σ 0
  | 0,   g, _ => g
  | _+1, g, k => applyGlobalArgs (.eval g (k 0)) (fun i => k i.succ)

-- Map a term to its global representative.
-- `wk` is transparent: `toGlobal (wk v t) = toGlobal t`.
-- The variable's VarType index S is recorded in the `var` case (from the implicit index).
def Term.toGlobal {σ : Signature} {V : VarCtx} {S : VarType} : Term σ V S → GlobalTerm σ S
  | .var ⟨v, _⟩              => .var v S
  | .func f k                => .func (applyGlobalArgs (.F ⟨f, rfl⟩) (fun i => (k i).toGlobal))
  | .boxterm t _             => .boxterm t.toGlobal
  | .diaterm _ _ t _         => .diaterm t.toGlobal
  | .unit                    => .unit
  | .pair t₁ t₂              => .pair t₁.toGlobal t₂.toGlobal
  | .pair_elim v₁ v₂ z _ b => .pair_elim v₁ v₂ (.var z (.VTypeProd v₁.2 v₂.2)) b.toGlobal

/-! ## Variable Renaming on GlobalTerm -/

-- Rename all occurrences of `old` to `⟨new_sym, old.2⟩`, stopping at pair_elim binders
-- that shadow `old`. Type-preserving: the renamed variable keeps its type. Correct under
-- the Barendregt convention.
mutual
  def GlobalTerm.rename {σ : Signature} (old : VarSymb × VarType) (new_sym : VarSymb) :
      GlobalTerm σ τ → GlobalTerm σ τ
    | .var v τ_v  => .var (if (v, τ_v) = old then new_sym else v) τ_v
    | .func g     => .func (GlobalFunc.rename old new_sym g)
    | .boxterm t  => .boxterm (t.rename old new_sym)
    | .diaterm t  => .diaterm (t.rename old new_sym)
    | .unit       => .unit
    | .pair t₁ t₂ => .pair (t₁.rename old new_sym) (t₂.rename old new_sym)
    | .pair_elim v₁ v₂ t b =>
        let t' := t.rename old new_sym
        if old = v₁ ∨ old = v₂ then .pair_elim v₁ v₂ t' b
        else .pair_elim v₁ v₂ t' (b.rename old new_sym)

  def GlobalFunc.rename {σ : Signature} {n : ℕ} (old : VarSymb × VarType) (new_sym : VarSymb) :
      GlobalFunc σ n → GlobalFunc σ n
    | .F f      => .F f
    | .eval g t => .eval (g.rename old new_sym) (t.rename old new_sym)
end

/-! ## Substitution -/

-- Internal implementation on GlobalTerm, used by Term.substTerm and pair_β.
-- At each node: if the whole term equals `target` (checked after a type-index equality
-- test), return `replacement`; otherwise recurse into subterms. Variables are atomic.
-- Under the Barendregt convention no binder-shadowing check is needed.
mutual
  def GlobalTerm.substTerm {σ : Signature} {τ τ_body : VarType}
      (t : GlobalTerm σ τ_body)
      (target : GlobalTerm σ τ) (replacement : GlobalTerm σ τ) :
      GlobalTerm σ τ_body :=
    if h : τ_body = τ then
      if h ▸ t = target then h.symm ▸ replacement
      else match t with
        | .var v τ_v          => .var v τ_v
        | .func g             => .func (g.substTerm target replacement)
        | .boxterm t'         => .boxterm (t'.substTerm target replacement)
        | .diaterm t'         => .diaterm (t'.substTerm target replacement)
        | .unit               => .unit
        | .pair t₁ t₂         => .pair (t₁.substTerm target replacement)
                                       (t₂.substTerm target replacement)
        | .pair_elim v₁ v₂ scrut b =>
            .pair_elim v₁ v₂ (scrut.substTerm target replacement)
                              (b.substTerm target replacement)
    else match t with
      | .var v τ_v            => .var v τ_v
      | .func g               => .func (g.substTerm target replacement)
      | .boxterm t'           => .boxterm (t'.substTerm target replacement)
      | .diaterm t'           => .diaterm (t'.substTerm target replacement)
      | .unit                 => .unit
      | .pair t₁ t₂           => .pair (t₁.substTerm target replacement)
                                       (t₂.substTerm target replacement)
      | .pair_elim v₁ v₂ scrut b =>
          .pair_elim v₁ v₂ (scrut.substTerm target replacement)
                            (b.substTerm target replacement)

  def GlobalFunc.substTerm {σ : Signature} {n : ℕ} {τ : VarType}
      (g : GlobalFunc σ n) (target : GlobalTerm σ τ) (replacement : GlobalTerm σ τ) :
      GlobalFunc σ n :=
    match g with
    | .F f       => .F f
    | .eval g' t => .eval (g'.substTerm target replacement) (t.substTerm target replacement)
end

-- Replaces a product-typed variable `z_sym : v₁.2 × v₂.2` in a term with the
-- pair of component variables `(v₁, v₂)`, threading the context change.
-- Two cases matter: `.wk ⟨z_sym,_⟩ t'` → `.wk v₁ (.wk v₂ t')`;
-- `.var ⟨z_sym,_⟩` → `.pair (.var v₁) (.var v₂)`. Box/dia contexts never
-- contain VTypeProd-typed variables (box_VarCtx maps all types to VTypeBox),
-- so those arms are vacuous; pair_elim scrutinee case is a semantic no-op
-- (GlobalTerm.pair_elim always has variable scrutinees, so no subterm of the
-- body's toGlobal can ever equal x'.toGlobal there).
def Term.substPairVar {σ : Signature} {V : VarCtx} {S : VarType}
    (z_sym : VarSymb) (v₁ v₂ : VarSymb × VarType)
    (t : Term σ (insert ⟨z_sym, .VTypeProd v₁.2 v₂.2⟩ V) S)
    : Term σ (insert v₁ (insert v₂ V)) S := by
  match t with
  | .var ⟨v, hv⟩ =>
      if heq : (⟨v, S⟩ : VarSymb × VarType) = ⟨z_sym, .VTypeProd v₁.2 v₂.2⟩ then
        have hS : S = .VTypeProd v₁.2 v₂.2 := congrArg Prod.snd heq
        exact hS ▸ .pair (.var ⟨v₁.1, Finset.mem_insert_self _ _⟩)
                          (.var ⟨v₂.1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩)
      else
        exact .var ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                        ((Finset.mem_insert.mp hv).resolve_left heq))⟩
  | .func f k   => exact .func f (fun i => (k i).substPairVar z_sym v₁ v₂)
  | .unit       => exact .unit
  | .pair t₁ t₂ => exact .pair (t₁.substPairVar z_sym v₁ v₂) (t₂.substPairVar z_sym v₁ v₂)
  | .pair_elim w₁ w₂ z _ W₁eq _ t_unpaired => if zeq : z = z_sym ∧ w₁.2 = v₁.2 ∧ w₂.2 = v₂.2
                                then
                                zeq.2.2 ▸ (W₁eq.symm ▸ t_unpaired)
                                else
  | .boxterm _  => sorry
    -- simp_all [box_VarCtx, Finset.ext_iff, Finset.mem_insert, Finset.mem_image]
  | .diaterm _ _ _ => sorry
    --simp_all [dia_VarCtx, box_VarCtx, Finset.ext_iff,
                                  Finset.mem_insert, Finset.mem_image]

-- Public API: `t.substTerm x y` replaces every subterm of `t` whose global
-- representative equals `x.toGlobal` with `y`. All three are Terms in the same
-- context; equality is decided by mapping to GlobalTerm. Variable substitution
-- is the special case `x = Term.var v`.
def Term.substTerm {σ : Signature} {V : VarCtx} {S S' : VarType}
    (t : Term σ V S) (x : Term σ V S') (y : Term σ V S') : Term σ V S :=
  if h : S = S' then
    if h ▸ t.toGlobal = x.toGlobal then h.symm ▸ y
    else match t with
      | .var v                   => .var v
      | .func f k                => .func f (fun i => (k i).substTerm x y)
      | .boxterm t'              => .boxterm t'
      | .diaterm xv hx t'        => .diaterm xv hx t'
      | .unit                    => .unit
      | .pair t₁ t₂              => .pair (t₁.substTerm x y) (t₂.substTerm x y)
      | .pair_elim v₁ v₂ z hz b  =>
          .pair_elim v₁ v₂ z hz (b.substTerm (.wk v₁ (.wk v₂ x)) (.wk v₁ (.wk v₂ y)))
      | .wk v t'                 => .wk v t'
  else match t with
    | .var v                   => .var v
    | .func f k                => .func f (fun i => (k i).substTerm x y)
    | .boxterm t'              => .boxterm t'
    | .diaterm xv hx t'        => .diaterm xv hx t'
    | .unit                    => .unit
    | .pair t₁ t₂              => .pair (t₁.substTerm x y) (t₂.substTerm x y)
    | .pair_elim v₁ v₂ z hz b  =>
          .pair_elim v₁ v₂ z hz (b.substTerm (.wk v₁ (.wk v₂ x)) (.wk v₁ (.wk v₂ y)))
    | .wk v t'                 => .wk v t'

/-! ## α-Equivalence on GlobalTerm -/

-- α-equivalence: structural congruence everywhere; pair_elim binders (v₁, v₂)
-- may differ by a consistent renaming of the body, and scrutinees must be α-equivalent.
-- Sound under the Barendregt convention.
mutual
  inductive GlobalTerm.AlphaEq {σ : Signature} :
      {τ : VarType} → GlobalTerm σ τ → GlobalTerm σ τ → Prop where
    | var (v : VarSymb) (τ : VarType) :
        GlobalTerm.AlphaEq (.var v τ) (.var v τ)
    | func {g₁ g₂ : GlobalFunc σ 0} :
        GlobalFunc.AlphaEq g₁ g₂ → GlobalTerm.AlphaEq (.func g₁) (.func g₂)
    | boxterm {S : VarType} {t₁ t₂ : GlobalTerm σ S} :
        GlobalTerm.AlphaEq t₁ t₂ → GlobalTerm.AlphaEq (.boxterm t₁) (.boxterm t₂)
    | diaterm {S : VarType} {t₁ t₂ : GlobalTerm σ S} :
        GlobalTerm.AlphaEq t₁ t₂ → GlobalTerm.AlphaEq (.diaterm t₁) (.diaterm t₂)
    | unit : GlobalTerm.AlphaEq .unit .unit
    | pair {S T : VarType} {s₁ s₂ : GlobalTerm σ S} {t₁ t₂ : GlobalTerm σ T} :
        GlobalTerm.AlphaEq s₁ s₂ → GlobalTerm.AlphaEq t₁ t₂ →
        GlobalTerm.AlphaEq (.pair s₁ t₁) (.pair s₂ t₂)
    | pair_elim
        {v₁ v₂ v₁' v₂' : VarSymb × VarType} {τ : VarType}
        {t  : GlobalTerm σ (.VTypeProd v₁.2  v₂.2 )}
        {t' : GlobalTerm σ (.VTypeProd v₁'.2 v₂'.2)}
        {b b' : GlobalTerm σ τ} :
        (h₁ : v₁.2 = v₁'.2) → (h₂ : v₂.2 = v₂'.2) →
        GlobalTerm.AlphaEq (h₁ ▸ h₂ ▸ t) t' →
        GlobalTerm.AlphaEq (b.rename v₁ v₁'.1 |>.rename v₂ v₂'.1) b' →
        GlobalTerm.AlphaEq (.pair_elim v₁ v₂ t b) (.pair_elim v₁' v₂' t' b')

  inductive GlobalFunc.AlphaEq {σ : Signature} :
      {n : ℕ} → GlobalFunc σ n → GlobalFunc σ n → Prop where
    | F {n : ℕ} (f : {f : σ.FuncSyms // σ.funcArity f = n}) :
        GlobalFunc.AlphaEq (.F f) (.F f)
    | eval {n : ℕ} {g₁ g₂ : GlobalFunc σ (n + 1)} {t₁ t₂ : GlobalTerm σ .Var} :
        GlobalFunc.AlphaEq g₁ g₂ → GlobalTerm.AlphaEq t₁ t₂ →
        GlobalFunc.AlphaEq (.eval g₁ t₁) (.eval g₂ t₂)
end

/-! ## Term Conversion -/

-- `GlobalTerm.Conv s t`: the least congruence on global terms containing the β/η rules.
--
-- β/η rules:
--   unit_η           : any term of type VTypeOne converts to .unit
--   pair_β           : "let (v₁,v₂) = (s,t) in b" reduces to b[v₁:=s][v₂:=t]
--   pair_η           : "let (v₁,v₂) = t in (v₁,v₂)" is just t (for any pair-typed t)
--   pair_elim_cong   : congruence under the body of a pair_elim
--   pair_elim_t_cong : congruence under the scrutinee of a pair_elim
mutual
  inductive GlobalTerm.Conv {σ : Signature} :
      {τ : VarType} → GlobalTerm σ τ → GlobalTerm σ τ → Prop where
    | unit_η           : GlobalTerm.Conv t .unit
    | pair_β           {v₁ v₂ : VarSymb × VarType} {τ : VarType}
                       {s : GlobalTerm σ v₁.2} {t : GlobalTerm σ v₂.2} {b : GlobalTerm σ τ} :
                       GlobalTerm.Conv (.pair_elim v₁ v₂ (.pair s t) b)
                                       (b.substTerm (.var v₁.1 v₁.2) s
                                          |>.substTerm (.var v₂.1 v₂.2) t)
    | pair_η           : GlobalTerm.Conv
                           (.pair_elim v₁ v₂ t (.pair (.var v₁.1 v₁.2) (.var v₂.1 v₂.2)))
                           t
    | func_cong        : GlobalFunc.Conv g₁ g₂ →
                         GlobalTerm.Conv (.func g₁) (.func g₂)
    | boxterm_cong     : GlobalTerm.Conv t₁ t₂ →
                         GlobalTerm.Conv (.boxterm t₁) (.boxterm t₂)
    | diaterm_cong     : GlobalTerm.Conv t₁ t₂ →
                         GlobalTerm.Conv (.diaterm t₁) (.diaterm t₂)
    | pair_l           : GlobalTerm.Conv s s' →
                         GlobalTerm.Conv (.pair s t) (.pair s' t)
    | pair_r           : GlobalTerm.Conv t t' →
                         GlobalTerm.Conv (.pair s t) (.pair s t')
    | pair_elim_cong   : GlobalTerm.Conv b b' →
                         GlobalTerm.Conv (.pair_elim v₁ v₂ t b) (.pair_elim v₁ v₂ t b')
    | pair_elim_t_cong {v₁ v₂ : VarSymb × VarType} {τ : VarType}
                       {t t' : GlobalTerm σ (.VTypeProd v₁.2 v₂.2)} {b : GlobalTerm σ τ} :
                       GlobalTerm.Conv t t' →
                       GlobalTerm.Conv (.pair_elim v₁ v₂ t b) (.pair_elim v₁ v₂ t' b)
    | refl  : GlobalTerm.Conv t t
    | symm  : GlobalTerm.Conv s t → GlobalTerm.Conv t s
    | trans : GlobalTerm.Conv s t → GlobalTerm.Conv t u → GlobalTerm.Conv s u

  inductive GlobalFunc.Conv {σ : Signature} :
      {n : ℕ} → GlobalFunc σ n → GlobalFunc σ n → Prop where
    | F    : GlobalFunc.Conv (.F f) (.F f)
    | eval : GlobalFunc.Conv g₁ g₂ → GlobalTerm.Conv t₁ t₂ →
             GlobalFunc.Conv (.eval g₁ t₁) (.eval g₂ t₂)
    | refl  : GlobalFunc.Conv g g
    | symm  : GlobalFunc.Conv g₁ g₂ → GlobalFunc.Conv g₂ g₁
    | trans : GlobalFunc.Conv g₁ g₂ → GlobalFunc.Conv g₂ g₃ → GlobalFunc.Conv g₁ g₃
end

-- Two terms are convertible when their global representatives are convertible.
def Term.Conv {σ : Signature} {V : VarCtx} {S : VarType} (t₁ t₂ : Term σ V S) : Prop :=
  GlobalTerm.Conv t₁.toGlobal t₂.toGlobal

/-! ## Relation Symbols -/

-- `RelSymb σ V n`: an n-ary relation symbol, partially applied to terms over V.
-- DecidableEq is not derived here; it will be handled via GlobalTerm-based equality
-- once the overall equality design is settled.
inductive RelSymb (σ : Signature) (V : VarCtx) : ℕ → Type where
  | R    : {r : σ.RelSyms // σ.relArity r = n} → RelSymb σ V n
  | eval : RelSymb σ V (Nat.succ n) → (S : VarType) → Term σ V S → RelSymb σ V n

-- Two relation symbols are convertible when they share the same function symbol
-- and all term arguments are pairwise convertible (at the same VarType).
inductive RelSymb.Conv {σ : Signature} {V : VarCtx} :
    {n : ℕ} → RelSymb σ V n → RelSymb σ V n → Prop where
  | R    : RelSymb.Conv (.R f) (.R f)
  | eval {n : ℕ} {p q : RelSymb σ V (n+1)} {S : VarType} {t s : Term σ V S} :
           RelSymb.Conv p q → Term.Conv t s →
           RelSymb.Conv (.eval p S t) (.eval q S s)
  | refl  : RelSymb.Conv r r
  | symm  : RelSymb.Conv p q → RelSymb.Conv q p
  | trans : RelSymb.Conv p q → RelSymb.Conv q r → RelSymb.Conv p r

/-! ## Well-Formed Formulas -/

-- `WFF σ V`: a formula whose free variables lie in V.
--
-- `box φ` : □φ.  φ lives in V; the result lives in box_VarCtx V.
-- `dia x φ`: ◇(∃x.φ).  φ lives in insert x V; the result lives in dia_VarCtx x V.
--   Use x.2 = VTypeOne for the propositional case (trivial witness).
-- `wk v φ` : weakening.  φ lives in V; the result lives in insert v V.
--
-- DecidableEq is not derived here pending the GlobalTerm-based equality design.
inductive WFF (σ : Signature) : VarCtx → Type where
  | atom : RelSymb σ V 0 → WFF σ V
  | top  : WFF σ V
  | bot  : WFF σ V
  | and  : WFF σ V → WFF σ V → WFF σ V
  | or   : WFF σ V → WFF σ V → WFF σ V
  | imp  : WFF σ V → WFF σ V → WFF σ V
  | all  : (x : VarSymb × VarType) → WFF σ (insert x V) → WFF σ V
  | ex   : (x : VarSymb × VarType) → WFF σ (insert x V) → WFF σ V
  | eq   : Term σ V S → Term σ V S → WFF σ V
  | box  : WFF σ V → WFF σ (box_VarCtx V)
  | dia  : (x : VarSymb × VarType) → x ∉ V → WFF σ (insert x V) → WFF σ (dia_VarCtx x V)
  | wk   : (v : VarSymb × VarType) → WFF σ V → WFF σ (insert v V)

namespace WFF

variable {σ : Signature}

def neg (φ : WFF σ V) : WFF σ V := imp φ bot

/-! ## Notation -/

infixr:35 " →ₘ "  => WFF.imp
infixl:65 " ∧ₘ "  => WFF.and
infixl:60 " ∨ₘ "  => WFF.or
prefix:75 "¬ₘ "   => WFF.neg
notation  "⊤ₘ"    => WFF.top
notation  "⊥ₘ"    => WFF.bot
notation  "∀ₘ"    => WFF.all
notation  "∃ₘ"    => WFF.ex
prefix:80 "□ₘ "   => WFF.box
-- ◇ₘ takes an explicit witness: ◇ₘ x φ
notation  "◇ₘ"    => WFF.dia

/-! ## Well-Scopedness -/

-- A formula is Scoped if every quantifier and dia witness binds a variable that
-- is not already present in the relevant context at the point of binding.
def Scoped : WFF σ V → Prop
  | .atom _ | .top | .bot | .eq _ _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ   => φ.Scoped ∧ ψ.Scoped
  | .all x φ                        => x ∉ V ∧ φ.Scoped
  | .ex  x φ                        => x ∉ V ∧ φ.Scoped
  | .box φ                          => φ.Scoped
  | .dia _ _ φ                      => φ.Scoped
  | .wk _ φ                         => φ.Scoped

/-! ## Formula Depth (termination measure) -/

def depth : WFF σ V → ℕ
  | .atom _ | .top | .bot | .eq _ _ => 0
  | .and φ ψ | .or φ ψ | .imp φ ψ   => φ.depth + ψ.depth + 1
  | .all _ φ | .ex _ φ              => φ.depth + 1
  | .box φ   | .dia _ _ φ | .wk _ φ  => φ.depth + 1

lemma depth_cast {V W : VarCtx} (h : V = W) (φ : WFF σ V) :
    depth (h ▸ φ) = depth φ := by subst h; rfl

lemma Scoped_cast {V W : VarCtx} (h : V = W) (φ : WFF σ V) :
    Scoped (h ▸ φ) = Scoped φ := by subst h; rfl

/-! ## Formula Conversion -/

-- The least congruence on formulas that lifts `Term.Conv`.
inductive Conv : {V : VarCtx} → WFF σ V → WFF σ V → Prop where
  | atom  : RelSymb.Conv p q → Conv (.atom p) (.atom q)
  | and_l : Conv φ φ' → Conv (.and φ ψ) (.and φ' ψ)
  | and_r : Conv ψ ψ' → Conv (.and φ ψ) (.and φ  ψ')
  | or_l  : Conv φ φ' → Conv (.or  φ ψ) (.or  φ' ψ)
  | or_r  : Conv ψ ψ' → Conv (.or  φ ψ) (.or  φ  ψ')
  | imp_l : Conv φ φ' → Conv (.imp φ ψ) (.imp φ' ψ)
  | imp_r : Conv ψ ψ' → Conv (.imp φ ψ) (.imp φ  ψ')
  | eq_l  : Term.Conv s s' → Conv (.eq s t) (.eq s' t)
  | eq_r  : Term.Conv t t' → Conv (.eq s t) (.eq s  t')
  | all   {x : VarSymb × VarType} {φ ψ : WFF σ (insert x V)} :
      Conv φ ψ → Conv (.all x φ) (.all x ψ)
  | ex    {x : VarSymb × VarType} {φ ψ : WFF σ (insert x V)} :
      Conv φ ψ → Conv (.ex  x φ) (.ex  x ψ)
  | box   {V' : VarCtx} {φ ψ : WFF σ V'} :
      Conv φ ψ → Conv (V := box_VarCtx V') (.box φ) (.box ψ)
  | dia   {V' : VarCtx} {x : VarSymb × VarType} {h : x ∉ V'} {φ ψ : WFF σ (insert x V')} :
      Conv φ ψ → Conv (V := dia_VarCtx x V') (.dia x h φ) (.dia x h ψ)
  | wk    {V' : VarCtx} {v : VarSymb × VarType} {φ ψ : WFF σ V'} :
      Conv φ ψ → Conv (V := insert v V') (.wk v φ) (.wk v ψ)
  | refl  : Conv φ φ
  | symm  : Conv φ ψ → Conv ψ φ
  | trans : Conv φ ψ → Conv ψ χ → Conv φ χ

end WFF

/-!
## Still to port from v2/v3

  · Term weakening as an admissible function (Term.weaken : V ⊆ W → Term σ V S → Term σ W S)
  · Substitution (subst source target φ — replace toGlobal(source) by target in φ)
  · Pair β via substitution: when a term of the form `pair s t` is substituted for a
    product variable z, any `pair_elim v₁ v₂ z b` in scope should reduce to `b` with
    v₁ and v₂ replaced by the appropriate components. This requires general term
    substitution (GlobalTerm.subst) and a corresponding Conv or proof rule.
  · Context extension / restriction helpers
  · Proof system (natural deduction):
      - Classical propositional rules (ax, weak, conv, and/or/imp/top/bot/lem)
      - Equality rules (eq_intro, eq_elim)
      - Quantifier rules (all_intro, all_elim, ex_intro, ex_elim)
      - Modal rules:
          K_box : Proof σ V Γ φ
                  → Proof σ (box_VarCtx V) (Γ.image (□ₘ ∘ box_lift)) (□ₘ (box_lift φ))
          K_dia : analogous rule for ◇ₘ, one witness at a time
-/
-/
