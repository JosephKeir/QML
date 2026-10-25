import QML.QML_v12m_GKeep
import QML.QML_v12m_GLevel

/-!
# QML v12m — the growing tree: shape templates and the canonical shapes

Under T + 4 with the strong forms the canonical shape of an address depends on its origin
(`docs/v12-modal-extensions.md` §3 4, "(B) on paper: shape templates" and "(B) in Lean").  One
**construction step** `CStep ρ` reads the templates in a family `ρ`:

* a `□` address has along each arrow the shape of its value there (`boxEnt`), edge by edge: an
  edge's entry for its kept item is an address, whose value along the rest it is, or a lifted
  term, whose shape at the child is read at the rest of the arrow (`unT`); along the empty path,
  its contents here, by recursion on the type;
* a `◇`-root that is **lifted** has the pull-back of its lifted term's shape (`liftDia`); one that
  is the **image** of a `◇`-root of the parent inherits that root's shape kept along the edge
  (`diaT`, by recursion on the node); every other `◇` address has the generic shape (`genDia`).

Templates read only the child's language at the lift, whose roots are below the lifted root
(`lev_lift`).  So ⭐`cEnv`, **the canonical shapes**, is one step with the templates read in the
canonical shapes of lower addresses, by well-founded recursion on the level (`levA`).  It is
well-formed (`cEnv_wf`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Lifted terms -/

omit [ModalSys] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A lifted term, when it is a term of `◇A`. -/
def LTerm.diaOf (A : VarType) :
    (e : LTerm σ) → Option (Σ a : Ann (.VTypeDia A), Term σ (ctxOf e.1) (.VTypeDia A) a)
  | ⟨_, .VTypeDia A', b, τ⟩ => if h : A' = A then by subst h; exact some ⟨b, τ⟩ else none
  | _ => none

/-- An edge with a term entry is an edge of the limit. -/
theorem gborn_of_inr {k : Node} {v : VarSymb} {e : LTerm σ} (h : fmapL hF M₀ k v = .inr e) :
    GBorn hF M₀ k := by
  obtain ⟨m, hk, -⟩ := fmapL_committed h
  exact ⟨m, hk⟩

theorem gborn_parent {c : ℕ} {p : Node} (h : GBorn hF M₀ (c :: p)) : GBorn hF M₀ p :=
  gborn_of_suffix h (List.suffix_cons c p)

/-- A root's kept item is lifted along an edge out of `s`. -/
def Lifted (s : GW hF M₀) (z : ℕ) : Prop :=
  ∃ c e, fmapL hF M₀ (c :: s.1) (.step (.root (.free z)) .keep) = .inr e

/-- The child a lifted root is lifted from. -/
noncomputable def Lifted.child {s : GW hF M₀} {z : ℕ} (h : Lifted s z) : GW hF M₀ :=
  ⟨h.choose :: s.1, gborn_of_inr h.choose_spec.choose_spec⟩

/-- The term a lifted root is lifted to. -/
noncomputable def Lifted.ent {s : GW hF M₀} {z : ℕ} (h : Lifted s z) : LTerm σ :=
  h.choose_spec.choose

/-! ## Shape families -/

variable (hF M₀) in
/-- A shape for every address at every type, at every world. -/
abbrev ShFam : Type := (t : GW hF M₀) → VarSymb → (T : VarType) → GShape hF M₀ t T

/-- The shape environment reading each address through a family. -/
abbrev famEnv (ρ : ShFam hF M₀) (Γ : Ctx) (t : GW hF M₀) :
    Model.ShEnv (garrows hF M₀) (fun _ => VarSymb) Γ t :=
  fun v T _ => ρ t v T

/-- A default shape, well-formed at a level list: default leaves throughout. -/
def dsh : List Bool → (s : GW hF M₀) → (T : VarType) → GShape hF M₀ s T
  | _, _, .Var => .var
  | _, _, .VTypeOne => .one
  | lw, s, .VTypeProd A C => .prod (dsh lw s A) (dsh lw s C)
  | lw, s, .VTypeBox A => .box (dsh (lw ++ [true]) s A)
  | lw, s, .VTypeDia A => .dia (dleaf lw s) (dsh (lw ++ [false]) s A)

/-- The generic shape of a `◇` address: a root possibility named by the address. -/
def genDia (s : GW hF M₀) (v : VarSymb) (A : VarType) : GShape hF M₀ s (.VTypeDia A) :=
  .dia (.root v []) (rootSh s v [.dia] A)

/-! ## The templates -/

/-- The pull-back to the root `z` of `s` of a lifted term's shape, read in `ρ` at the child `t`. -/
noncomputable def liftDiaAt (ρ : ShFam hF M₀) (s : GW hF M₀) (z : ℕ) (t : GW hF M₀)
    (e : LTerm σ) (A : VarType) : GShape hF M₀ s (.VTypeDia A) :=
  match e.diaOf A with
  | some ⟨_, τ⟩ =>
      pbShp hF M₀ (t := t) (.root (.free z)) [] (Model.termShp (famEnv ρ (ctxOf e.1) t) 0 τ)
  | none => genDia s (.root (.free z)) A

/-- ⭐**The template of a lifted `◇`-root**: the pull-back to the root of its lifted term's shape,
    read in `ρ` at the child. -/
noncomputable def liftDia (ρ : ShFam hF M₀) {s : GW hF M₀} {z : ℕ} (h : Lifted s z)
    (A : VarType) : GShape hF M₀ s (.VTypeDia A) :=
  liftDiaAt ρ s z h.child h.ent A

open Classical in
/-- ⭐**The shape of a `◇`-root**: a lifted root's template; an image of a parent's `◇`-root, that
    root's shape kept along the edge; else generic.  By recursion on the node. -/
noncomputable def diaT (ρ : ShFam hF M₀) :
    (p : Node) → (hp : GBorn hF M₀ p) → VarSymb → (A : VarType) →
      GShape hF M₀ ⟨p, hp⟩ (.VTypeDia A)
  | [], hp, v, A =>
      if h : ∃ z, v = .root (.free z) ∧ Lifted ⟨[], hp⟩ z then liftDia ρ h.choose_spec.2 A
      else genDia ⟨[], hp⟩ v A
  | c :: p, hp, v, A =>
      if h : ∃ z, v = .root (.free z) ∧ Lifted ⟨c :: p, hp⟩ z then liftDia ρ h.choose_spec.2 A
      else if h' : ∃ u, fmapL hF M₀ (c :: p) (.step (.root (.free u)) .keep) = .inl v then
        (diaT ρ p (gborn_parent hp) (.root (.free h'.choose)) A).map
          (Arrows.Leaf.keepAlong hF (edgeAcc (s := ⟨p, gborn_parent hp⟩) (t := ⟨c :: p, hp⟩) rfl))
      else genDia ⟨c :: p, hp⟩ v A

/-! ## Reading a family at an arrow -/

/-- A leaf read at an arrow: a family's member there (a root has none; a default). -/
def evalLeaf {t : GW hF M₀} : GLeaf hF M₀ t → (b : (garrows hF M₀).Acc t) → GLeaf hF M₀ b.1
  | .fam f, b => f b
  | .root _ _, _ => .root (.root (.free 0)) []

/-- ⭐A shape whose top-level leaves are families, read at an arrow: the inverse of
    transposition (`unT_transpose`). -/
def unT {t : GW hF M₀} (b : (garrows hF M₀).Acc t) :
    {A : VarType} → GShape hF M₀ t A → GShape hF M₀ b.1 A
  | _, .var => .var
  | _, .one => .one
  | _, .prod S S' => .prod (unT b S) (unT b S')
  | _, .box S => .box (unT b S)
  | _, .dia ℓ S => .dia (evalLeaf ℓ b) (unT b S)

theorem unT_transpose {t : GW hF M₀} (b : (garrows hF M₀).Acc t) :
    ∀ {A : VarType} (g : (a : (garrows hF M₀).Acc t) → GShape hF M₀ a.1 A),
      unT b (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb) g) = g b
  | .Var, g => Model.shp_var_eq _ _
  | .VTypeOne, g => Shp.one_eq _ _
  | .VTypeProd _ _, g => by
      simp only [Arrows.transposeShp, unT]
      rw [unT_transpose b, unT_transpose b]
      exact (Shp.prod_eta _).symm
  | .VTypeBox _, g => by
      simp only [Arrows.transposeShp, unT]
      rw [unT_transpose b]
      exact (Shp.box_eta _).symm
  | .VTypeDia _, g => by
      simp only [Arrows.transposeShp, unT, evalLeaf]
      rw [unT_transpose b]
      exact (Shp.dia_eta _).symm

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A lifted term, when it is a term of `□A`. -/
def LTerm.boxOf (A : VarType) :
    (e : LTerm σ) → Option (Σ a : Ann (.VTypeBox A), Term σ (ctxOf e.1) (.VTypeBox A) a)
  | ⟨_, .VTypeBox A', b, τ⟩ => if h : A' = A then by subst h; exact some ⟨b, τ⟩ else none
  | _ => none

/-- ⭐**A `□` address's value along a path**, its shape read by `g` at the end: along the empty
    path, its contents here; along an edge whose entry for its kept item is an address, that
    address's value along the rest; along an edge to which it is lifted, the lifted term's shape at
    the child, read in `ρ`, at the rest of the path (`unT`). -/
noncomputable def boxEnt (ρ : ShFam hF M₀) {A : VarType}
    (g : (t : GW hF M₀) → VarSymb → GShape hF M₀ t A) :
    (s : GW hF M₀) → VarSymb → (P : List ℕ) → (t : GW hF M₀) → t.1 = nodeOf s.1 P →
      GShape hF M₀ t A
  | _, v, [], t, _ => g t (.step v .here)
  | s, v, c :: Q, t, h =>
      match fmapL hF M₀ (c :: s.1) (.step v .keep) with
      | .inl y => boxEnt ρ g (stepW s c (born_step h)) y Q t h
      | .inr e =>
          if hQ : PathOk Q then
            match e.boxOf A with
            | some ⟨_, τ⟩ =>
                unT ⟨t, ⟨⟨Q, hQ, h⟩⟩⟩ (Model.termShp
                  (famEnv ρ (ctxOf e.1) (stepW s c (born_step h))) 0 τ).inner
            | none => dsh [] t A
          else dsh [] t A

/-- ⭐**One construction step**: the canonical shapes, with the lifted templates read in `ρ`.  By
    recursion on the type. -/
noncomputable def CStep (ρ : ShFam hF M₀) :
    (T : VarType) → (s : GW hF M₀) → VarSymb → GShape hF M₀ s T
  | .Var, _, _ => .var
  | .VTypeOne, _, _ => .one
  | .VTypeProd A C, s, v => .prod (CStep ρ A s (.step v .fst)) (CStep ρ C s (.step v .snd))
  | .VTypeBox A, s, v =>
      .box (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb) fun a =>
        boxEnt ρ (fun t w => CStep ρ A t w) s v (pathOf a.2.down) a.1 (pathOf_eq a.2.down))
  | .VTypeDia A, s, v => diaT ρ s.1 s.2 v A

/-! ## The canonical shapes -/

/-- The level of an address: its root's. -/
noncomputable def levA (s : GW hF M₀) (v : VarSymb) : ℕ :=
  match v.rt with
  | .free r => lev s r
  | .bnd _ => 0

/-- ⭐**The canonical shapes**: one construction step, the templates read in the canonical shapes
    of lower addresses.  By well-founded recursion on the level. -/
noncomputable def cEnv (s : GW hF M₀) (v : VarSymb) (T : VarType) : GShape hF M₀ s T :=
  CStep (fun t w W => if levA t w < levA s v then cEnv t w W else dsh [] t W) T s v
termination_by levA s v

/-! ## Well-formedness -/

theorem dsh_wf : ∀ (lw : List Bool) (s : GW hF M₀) (T : VarType),
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw (dsh lw s T)
  | _, _, .Var => trivial
  | _, _, .VTypeOne => trivial
  | lw, s, .VTypeProd A C => ⟨dsh_wf lw s A, dsh_wf lw s C⟩
  | lw, s, .VTypeBox A => dsh_wf (lw ++ [true]) s A
  | lw, s, .VTypeDia A => ⟨dleaf_wf lw s, dsh_wf (lw ++ [false]) s A⟩

theorem genDia_wf (s : GW hF M₀) (v : VarSymb) (A : VarType) :
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (genDia s v A) :=
  ⟨(Arrows.Leaf.wf_root _ []).mpr ⟨rfl, by simp, trivial, ⟨.VTypeDia A, A, rfl⟩⟩,
    rootSh_wf s v A [.dia] [false] rfl rfl (Step.BoxOK_snoc_dia [] [] rfl trivial)
        (.VTypeDia A) rfl⟩

/-- Keeping a shape's leaves along an arrow keeps it well-formed. -/
theorem shWF_map_keepAlong {s : GW hF M₀} (a : (garrows hF M₀).Acc s) :
    ∀ (lw : List Bool) {T : VarType} (S : GShape hF M₀ s T),
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw S →
        Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw
          (S.map (Arrows.Leaf.keepAlong hF a))
  | _, _, .var, _ => trivial
  | _, _, .one, _ => trivial
  | lw, _, .prod S S', h => ⟨shWF_map_keepAlong a lw S h.1, shWF_map_keepAlong a lw S' h.2⟩
  | lw, _, .box S, h => shWF_map_keepAlong a (lw ++ [true]) S h
  | lw, _, .dia ℓ S, h =>
      ⟨Arrows.Leaf.wf_keepAlong hF lw a ℓ h.1, shWF_map_keepAlong a (lw ++ [false]) S h.2⟩

/-- Reading a shape below a `□` at an arrow keeps it well-formed one level up. -/
theorem shWF_unT {t : GW hF M₀} (b : (garrows hF M₀).Acc t) :
    ∀ (lw : List Bool) {A : VarType} (S : GShape hF M₀ t A),
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) (true :: lw) S →
        Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw (unT b S)
  | _, _, .var, _ => trivial
  | _, _, .one, _ => trivial
  | lw, _, .prod S S', h => ⟨shWF_unT b lw S h.1, shWF_unT b lw S' h.2⟩
  | lw, _, .box S, h => shWF_unT b (lw ++ [true]) S h
  | lw, _, .dia ℓ S, h => by
      refine ⟨?_, shWF_unT b (lw ++ [false]) S h.2⟩
      match ℓ, h.1 with
      | .root _ _, h₁ => exact absurd ((Arrows.Leaf.wf_root _ _).mp h₁).2 (by simp)
      | .fam _, h₁ => exact h₁ b

theorem shWF_unT_inner {t : GW hF M₀} (b : (garrows hF M₀).Acc t) {A : VarType}
    (S : GShape hF M₀ t (.VTypeBox A))
    (h : Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] S) :
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (unT b S.inner) := by
  rw [Shp.box_eta S] at h
  exact shWF_unT b [] _ h

/-- A family well-formed at every address gives well-formed environments. -/
theorem famEnv_wf {ρ : ShFam hF M₀}
    (hρ : ∀ t v T, Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (ρ t v T))
    (Γ : Ctx) (t : GW hF M₀) : (famEnv ρ Γ t).WF [] :=
  fun v T _ => hρ t v T

theorem liftDia_wf {ρ : ShFam hF M₀}
    (hρ : ∀ t v T, Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (ρ t v T))
    {s : GW hF M₀} {z : ℕ} (h : Lifted s z) (A : VarType) :
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (liftDia ρ h A) := by
  unfold liftDia liftDiaAt
  split
  · exact pbShp_wf _ [] _ (Model.shWF_termShp (famEnv_wf hρ _ _) _)
  · exact genDia_wf _ _ _

theorem diaT_wf {ρ : ShFam hF M₀}
    (hρ : ∀ t v T, Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (ρ t v T)) :
    ∀ (p : Node) (hp : GBorn hF M₀ p) (v : VarSymb) (A : VarType),
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (diaT ρ p hp v A)
  | [], hp, v, A => by
      unfold diaT
      split
      · exact liftDia_wf hρ _ A
      · exact genDia_wf _ _ _
  | c :: p, hp, v, A => by
      unfold diaT
      split
      · exact liftDia_wf hρ _ A
      · split
        · exact shWF_map_keepAlong _ [] _ (diaT_wf hρ p _ _ A)
        · exact genDia_wf _ _ _

theorem boxEnt_wf {ρ : ShFam hF M₀}
    (hρ : ∀ t v T, Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (ρ t v T))
    {A : VarType} {g : (t : GW hF M₀) → VarSymb → GShape hF M₀ t A}
    (hg : ∀ t w, Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (g t w)) :
    ∀ (s : GW hF M₀) (v : VarSymb) (P : List ℕ) (t : GW hF M₀) (h : t.1 = nodeOf s.1 P),
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (boxEnt ρ g s v P t h)
  | _, _, [], t, _ => hg t _
  | s, v, c :: Q, t, h => by
      unfold boxEnt
      split
      · exact boxEnt_wf hρ hg _ _ Q t h
      · split
        · split
          · exact shWF_unT_inner _ _ (Model.shWF_termShp (famEnv_wf hρ _ _) _)
          · exact dsh_wf [] t A
        · exact dsh_wf [] t A

/-- ⭐**Each construction step is well-formed**, from a well-formed family. -/
theorem cStep_wf {ρ : ShFam hF M₀}
    (hρ : ∀ t v T, Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (ρ t v T)) :
    ∀ (T : VarType) (s : GW hF M₀) (v : VarSymb),
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (CStep ρ T s v)
  | .Var, _, _ => trivial
  | .VTypeOne, _, _ => trivial
  | .VTypeProd A C, s, v => ⟨cStep_wf hρ A s _, cStep_wf hρ C s _⟩
  | .VTypeBox A, s, v => by
      exact Model.shWF_transpose true [] _ fun a =>
        boxEnt_wf hρ (fun t w => cStep_wf hρ A t w) s v _ a.1 _
  | .VTypeDia A, s, v => diaT_wf hρ s.1 s.2 v A

/-- ⭐**The canonical shapes are well-formed.** -/
theorem cEnv_wf (s : GW hF M₀) (v : VarSymb) (T : VarType) :
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (cEnv s v T) := by
  rw [cEnv]
  refine cStep_wf (fun t w W => ?_) T s v
  split
  · exact cEnv_wf t w W
  · exact dsh_wf [] t W
termination_by levA s v

end GArrow

end V12M
