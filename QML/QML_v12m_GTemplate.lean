import QML.QML_v12m_GKeep

/-!
# QML v12m — the growing tree: the canonical shapes

Under T possible objects carry shapes (`docs/v12-modal-extensions.md` §3 4, "Phase 2b").  The
canonical shape of an address is its **address shape**: the tree of its η-annotation with each
`◇`-node labelled by the label of the address there (`gLab`).  Kept along an arrow, a root
possibility's labels move by the leaf-valued root action (`gKeep`), so a lifted root needs no
template of its own.

* `annSh`: the shape of an annotation, its indices' labels at its `◇`-nodes;
* ⭐`cEnv`, **the canonical shapes**: the address shape of a declared address;
* ⭐`cEnv_wf`: they are well-formed; ⭐`cEnv_dia_generic`: a possible address's is generic.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

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

/-! ## Address shapes -/

/-- ⭐**The shape of an annotation**: its tree, each `◇`-node labelled by its index's label. -/
noncomputable def annSh (t : GW hF M₀) : {T : VarType} → Ann T → GShape hF M₀ t T
  | _, .var => .var
  | _, .one => .one
  | _, .prod a b => .prod (annSh t a) (annSh t b)
  | _, .box a => .box (annSh t a)
  | _, .dia i a => .dia (gLab t i) (annSh t a)

open Classical in
/-- ⭐**The canonical shapes**: under T over a maximal theory, a declared address's address
    shape (its η-annotation's); a default shape otherwise. -/
noncomputable def cEnv (s : GW hF M₀) (v : VarSymb) (T : VarType) : GShape hF M₀ s T :=
  if ModalSys.T = true ∧ Theory.IsMCS M₀ ∧ DeclAt s v T then annSh s (Ann.eta v T)
  else dsh [] s T

theorem cEnv_decl (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {v : VarSymb}
    {T : VarType} (hd : DeclAt s v T) : cEnv s v T = annSh s (Ann.eta v T) :=
  if_pos ⟨hT, hM₀, hd⟩

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

/-! ## Well-formedness -/

theorem dsh_wf : ∀ (lw : List Bool) (s : GW hF M₀) (T : VarType),
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw (dsh lw s T)
  | _, _, .Var => trivial
  | _, _, .VTypeOne => trivial
  | lw, s, .VTypeProd A C => ⟨dsh_wf lw s A, dsh_wf lw s C⟩
  | lw, s, .VTypeBox A => dsh_wf (lw ++ [true]) s A
  | lw, s, .VTypeDia A => ⟨dleaf_wf lw s, dsh_wf (lw ++ [false]) s A⟩

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

/-- A family well-formed at every address gives well-formed environments. -/
theorem famEnv_wf {ρ : ShFam hF M₀}
    (hρ : ∀ t v T, Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (ρ t v T))
    (Γ : Ctx) (t : GW hF M₀) : (famEnv ρ Γ t).WF [] :=
  fun v T _ => hρ t v T

/-- The type of a projection of a declared address. -/
theorem declAt_ext {s : GW hF M₀} {v : VarSymb} {U : VarType} (hd : DeclAt s v U)
    {q : List Step} (hq : PPath q) {T : VarType} (hw : Step.walkTy U q = some T) :
    DeclAt s (v.ext q) T := by
  obtain ⟨i, hi⟩ := hd
  refine ⟨i, ?_⟩
  rw [Ctx.ref_ext_ppath _ q v hq, hi, Option.bind_some, ← walkTy_ppath U hq]
  exact hw

/-- ⭐**The label of a position of a declared address is well-formed** at the position's level
    kinds, when the `□` levels are spelled by `keep`s. -/
theorem gLab_wf (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {v : VarSymb}
    {U : VarType} (hd : DeclAt s v U) (hv : PPath v.path) {π : List Step} {A : VarType}
    (hw : Step.walkTy U π = some (.VTypeDia A)) {lw : List Bool}
    (hl : Step.levels π = lw.length)
    (hk : ∀ j, lw[j]? = some true → lvlStep j π = some .keep) :
    Arrows.Leaf.WF lw (gLab s (v.ext π)) := by
  by_cases h0 : Step.levels π = 0
  · have hπ := ppath_of_levels0 h0
    have hpre : PPath (v.ext π).path := by
      rw [VarSymb.ext_path]
      exact fun x hx => (List.mem_append.mp hx).elim (hv x) (hπ x)
    rw [gLab_ppath _ hpre]
    obtain rfl : lw = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact (Arrows.Leaf.wf_root _ []).mpr ⟨rfl, by simp, trivial,
      ⟨.VTypeDia .VTypeOne, .VTypeOne, rfl⟩⟩
  · obtain ⟨π₀, st, r, rfl, hπ₀, hst⟩ := split_first π (by omega)
    have hpre : PPath (v.ext π₀).path := by
      rw [VarSymb.ext_path]
      exact fun x hx => (List.mem_append.mp hx).elim (hv x) (hπ₀ x)
    have hlv : ∀ j, lvlStep j (π₀ ++ st :: r) = lvlStep j (st :: r) := fun j => by
      rw [lvlStep_append, levels_pp hπ₀, if_neg (by omega), Nat.sub_zero]
    rw [Step.walkTy_append, walkTy_ppath U hπ₀] at hw
    obtain ⟨U₀, hU₀, hw₀⟩ := Option.bind_eq_some_iff.mp hw
    have hd₀ : DeclAt s (v.ext π₀) U₀ := declAt_ext hd hπ₀ ((walkTy_ppath U hπ₀).trans hU₀)
    have hlr : Step.levels (π₀ ++ st :: r) = 1 + Step.levels r := by
      rw [Step.levels_append, levels_pp hπ₀, Step.levels_cons, if_neg (by simp [hst])]
      omega
    rw [VarSymb.ext_append]
    cases st with
    | fst => cases hst
    | snd => cases hst
    | here => cases hst
    | box =>
        have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
        obtain ⟨W, hW, -⟩ := Option.bind_eq_some_iff.mp hw₀
        change (if ModalSys.keepOnly = true then none else U₀.step .box) = some W at hW
        rw [if_pos hko] at hW
        cases hW
    | dia =>
        rw [show (v.ext π₀).ext (Step.dia :: r) = (VarSymb.step (v.ext π₀) .dia).ext r from rfl,
          gLab_dia _ hpre]
        have hlev : Step.levels (Step.dia :: r) = lw.length := by
          rw [← hl, hlr, Step.levels_cons, if_neg (by decide)]
        have hhead : lw.head? ≠ some true := fun hh => by
          have := hk 0 (by
            cases lw with
            | nil => cases hh
            | cons c l => simpa using hh)
          rw [hlv, lvlStep_lvl_zero (by decide)] at this
          cases this
        have hbox : Step.BoxOK lw (Step.dia :: r) := boxOK_of_lvl _ lw fun j hj e => by
          have := hk j hj
          rw [hlv, e] at this
          cases this
        exact (Arrows.Leaf.wf_root _ _).mpr ⟨hlev, hhead, hbox, ⟨U₀, A, hw₀⟩⟩
    | keep =>
        rw [show (v.ext π₀).ext (Step.keep :: r) = (VarSymb.step (v.ext π₀) .keep).ext r from rfl,
          gLab_keep _ hpre]
        cases lw with
        | nil => simp at hl; omega
        | cons c lw' =>
            intro b
            refine gMem_wf hT hM₀ (Step.levels r) _ _ ⟨hpre, U₀, A, hd₀, hw₀⟩ rfl
              (by simp at hl; omega) (boxOK_of_lvl _ lw' fun j hj e => ?_)
            have := hk (j + 1) (by simpa using hj)
            rw [hlv, lvlStep_lvl_succ rfl, e] at this
            cases this

/-- The address shape of a position of a declared address is well-formed. -/
theorem annSh_eta_wf (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    {v : VarSymb} {U : VarType} (hd : DeclAt s v U) (hv : PPath v.path) :
    ∀ (T : VarType) (π : List Step) (lw : List Bool), Step.walkTy U π = some T →
      Step.levels π = lw.length → (∀ j, lw[j]? = some true → lvlStep j π = some .keep) →
      Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) lw
        (annSh s (Ann.eta (v.ext π) T))
  | .Var, _, _, _, _, _ => trivial
  | .VTypeOne, _, _, _, _, _ => trivial
  | .VTypeProd A C, π, lw, hw, hl, hk => by
      have hlv : ∀ (st : Step), st.isProj = true → ∀ j, lw[j]? = some true →
          lvlStep j (π ++ [st]) = some .keep := fun st hs j hj => by
        rw [lvlStep_append, if_pos (by rw [hl]; exact (List.getElem?_eq_some_iff.mp hj).1)]
        exact hk j hj
      have hl' : ∀ (st : Step), st.isProj = true → Step.levels (π ++ [st]) = lw.length :=
        fun st hs => by rw [Step.levels_append, hl]; simp [Step.levels, hs]
      refine ⟨?_, ?_⟩
      · have := annSh_eta_wf hT hM₀ hd hv A (π ++ [.fst]) lw
          (by rw [Step.walkTy_append, hw]; rfl) (hl' .fst rfl) (hlv .fst rfl)
        rwa [VarSymb.ext_append_single] at this
      · have := annSh_eta_wf hT hM₀ hd hv C (π ++ [.snd]) lw
          (by rw [Step.walkTy_append, hw]; rfl) (hl' .snd rfl) (hlv .snd rfl)
        rwa [VarSymb.ext_append_single] at this
  | .VTypeBox A, π, lw, hw, hl, hk => by
      have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      have := annSh_eta_wf hT hM₀ hd hv A (π ++ [.keep, .here]) (lw ++ [true])
        (by
          rw [Step.walkTy_append, hw, Option.bind_some, walkTy_keep rfl, walkTy_here hT]
          rfl)
        (by rw [Step.levels_append, hl]; simp [Step.levels, Step.isProj])
        (fun j hj => by
          rw [lvlStep_append]
          by_cases hjl : j < lw.length
          · rw [if_pos (by rw [hl]; exact hjl)]
            exact hk j (by rwa [List.getElem?_append_left hjl] at hj)
          · rw [if_neg (by omega)]
            have hj' : j - lw.length = 0 := by
              rw [List.getElem?_append_right (by omega)] at hj
              by_contra hne
              rw [List.getElem?_eq_none (by simp; omega)] at hj
              cases hj
            rw [hl, hj', lvlStep_lvl_zero rfl])
      change Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) (lw ++ [true])
        (annSh s (Ann.eta (v.ext π).inner A))
      rw [VarSymb.inner_keepOnly hko]
      rw [VarSymb.ext_append] at this
      exact this
  | .VTypeDia A, π, lw, hw, hl, hk => by
      refine ⟨gLab_wf hT hM₀ hd hv hw hl hk, ?_⟩
      have := annSh_eta_wf hT hM₀ hd hv A (π ++ [.dia]) (lw ++ [false])
        (by rw [Step.walkTy_append, hw]; rfl)
        (by rw [Step.levels_append, hl]; simp [Step.levels, Step.isProj])
        (fun j hj => by
          rw [lvlStep_append]
          by_cases hjl : j < lw.length
          · rw [if_pos (by rw [hl]; exact hjl)]
            exact hk j (by rwa [List.getElem?_append_left hjl] at hj)
          · exfalso
            rw [List.getElem?_append_right (by omega)] at hj
            by_cases hj0 : j - lw.length = 0
            · rw [hj0] at hj
              cases hj
            · rw [List.getElem?_eq_none (by simp; omega)] at hj
              cases hj)
      rwa [VarSymb.ext_append_single] at this

/-- ⭐**The canonical shapes are well-formed.** -/
theorem cEnv_wf (s : GW hF M₀) (v : VarSymb) (T : VarType) :
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (cEnv s v T) := by
  unfold cEnv
  split
  · rename_i h
    obtain ⟨hT, hM₀, hd⟩ := h
    obtain ⟨i, hi⟩ := id hd
    exact annSh_eta_wf hT hM₀ hd (reach_ppath hi).1 T [] [] rfl rfl (fun _ h => by cases h)
  · exact dsh_wf [] s T

/-! ## Possible addresses read generically -/

/-- Inside a possible root's content, address shapes are generic. -/
theorem annSh_rootSh {s : GW hF M₀} {y : VarSymb} (hy : PPath y.path) :
    ∀ (T : VarType) (π : List Step), annSh s (Ann.eta (y.ext (.dia :: π)) T) =
      rootSh s y (.dia :: π) T
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, π => by
      change Shp.prod (annSh s (Ann.eta (.step (y.ext (.dia :: π)) .fst) A))
        (annSh s (Ann.eta (.step (y.ext (.dia :: π)) .snd) C)) = _
      rw [← VarSymb.ext_append_single, ← VarSymb.ext_append_single, List.cons_append,
        List.cons_append, annSh_rootSh hy A, annSh_rootSh hy C]
      rfl
  | .VTypeBox A, π => by
      change Shp.box (annSh s (Ann.eta (y.ext (.dia :: π)).inner A)) =
        Shp.box (rootSh s y ((.dia :: π) ++ Step.innerPath) A)
      by_cases hk : ModalSys.keepOnly = true
      · rw [VarSymb.inner_keepOnly hk, show Step.innerPath = [.keep, .here] from if_pos hk,
          show ((y.ext (.dia :: π)).step .keep).step .here = y.ext (.dia :: (π ++ [.keep, .here]))
            by rw [← List.cons_append, VarSymb.ext_append]; rfl,
          annSh_rootSh hy A]
        rfl
      · rw [VarSymb.inner_box (Bool.eq_false_iff.mpr hk),
          show Step.innerPath = [.box] from if_neg hk,
          show (y.ext (.dia :: π)).step .box = y.ext (.dia :: (π ++ [.box]))
            by rw [← List.cons_append, VarSymb.ext_append]; rfl,
          annSh_rootSh hy A]
        rfl
  | .VTypeDia A, π => by
      change Shp.dia (gLab s (y.ext (.dia :: π))) (annSh s (Ann.eta (.step (y.ext (.dia :: π))
        .dia) A)) = _
      rw [← VarSymb.ext_append_single, List.cons_append, annSh_rootSh hy A,
        show y.ext (.dia :: π) = (VarSymb.step y .dia).ext π from rfl, gLab_dia _ hy]
      rfl

/-- ⭐**A possible address's canonical shape is generic** (`genDia`). -/
theorem cEnv_dia_generic (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    {y : VarSymb} {X : VarType} (hd : DeclAt s y (.VTypeDia X)) :
    cEnv s y (.VTypeDia X) = genDia s y X := by
  obtain ⟨i, hi⟩ := id hd
  have hy := (reach_ppath hi).1
  rw [cEnv_decl hT hM₀ hd]
  change Shp.dia (gLab s y) (annSh s (Ann.eta (.step y .dia) X)) = _
  rw [gLab_ppath _ hy, show VarSymb.step y .dia = y.ext (.dia :: []) from rfl, annSh_rootSh hy]
  rfl

end GArrow

end V12M
