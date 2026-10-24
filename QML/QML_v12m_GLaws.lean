import QML.QML_v12m_GShapeTr

/-!
# QML v12m — the growing tree: the laws of the canonical shapes

The canonical shapes satisfy the laws the shaped model needs (`docs/v12-modal-extensions.md` §3 4,
"(B) in Lean"): along every path, the environment pulled back from the canonical shapes at the
path's end is the path's component of the canonical environment pushed into `□`.  This file has
the shape algebra the laws are stated in:

* `unT_transpose`, `transpose_unT`: reading a family at an arrow inverts transposition;
* `unT_termShp`: a term's shape one level in, read at an arrow, is its shape in the environment
  read at the arrow;
* `keepSh`: an object of a keepable type kept along an arrow — a possible one's labels restricted
  (`keepAlong`), a necessary one's family reindexed (`restrictBox`); `unT_keep`: it is the
  arrow's component of `GFunc.keep`'s shape; `keepSh_comp`: keeping along two arrows is keeping
  along their composite.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Reading families at an arrow -/

omit [ModalSys] [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem Shp.map_congr_allL {L L' : Type} {Q : L → Prop} {g g' : L → L'}
    (h : ∀ ℓ, Q ℓ → g ℓ = g' ℓ) : ∀ {A : VarType} (S : Shp L A), S.AllL Q → S.map g = S.map g'
  | _, .var, _ => rfl
  | _, .one, _ => rfl
  | _, .prod a b, hS => by
      simp only [Shp.map]
      rw [Shp.map_congr_allL h a hS.1, Shp.map_congr_allL h b hS.2]
  | _, .box a, hS => by
      simp only [Shp.map]
      rw [Shp.map_congr_allL h a hS]
  | _, .dia ℓ a, hS => by
      simp only [Shp.map]
      rw [h ℓ hS.1, Shp.map_congr_allL h a hS.2]

theorem unT_map {t : GW hF M₀} (b : (garrows hF M₀).Acc t)
    {g : GLeaf hF M₀ t → GLeaf hF M₀ t} :
    ∀ {A : VarType} (S : GShape hF M₀ t A), unT b (S.map g) = S.map fun ℓ => evalLeaf (g ℓ) b
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod S S' => by
      simp only [Shp.map, unT]
      rw [unT_map b S, unT_map b S']
  | _, .box S => by
      simp only [Shp.map, unT]
      rw [unT_map b S]
  | _, .dia ℓ S => by
      simp only [Shp.map, unT]
      rw [unT_map b S]

/-- The composite of two arrows. -/
abbrev accTrans {s : GW hF M₀} (a : (garrows hF M₀).Acc s) (b : (garrows hF M₀).Acc a.1) :
    (garrows hF M₀).Acc s :=
  ⟨b.1, ⟨gtrans a.2.down b.2.down⟩⟩

/-- Transposing a shape read along composite arrows: each leaf becomes the family of its reads. -/
theorem transpose_unT_trans {s : GW hF M₀} (a : (garrows hF M₀).Acc s) :
    ∀ {A : VarType} (S : GShape hF M₀ s A),
      Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb)
          (fun b => unT (accTrans a b) S) =
        S.map fun ℓ => .fam fun b => evalLeaf ℓ (accTrans a b)
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod S S' => by
      simp only [Arrows.transposeShp, unT, Shp.map, Shp.fst, Shp.snd]
      rw [transpose_unT_trans a S, transpose_unT_trans a S']
  | _, .box S => by
      simp only [Arrows.transposeShp, unT, Shp.map, Shp.inner]
      rw [transpose_unT_trans a S]
  | _, .dia ℓ S => by
      simp only [Arrows.transposeShp, unT, Shp.map, Shp.label, Shp.body]
      rw [transpose_unT_trans a S]

/-- ⭐A shape whose top-level leaves are families is the transposition of its reads. -/
theorem transpose_unT {s : GW hF M₀} :
    ∀ {A : VarType} (S : GShape hF M₀ s A), S.AllL IsFam →
      Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb) (fun b => unT b S) = S
  | _, .var, _ => rfl
  | _, .one, _ => rfl
  | _, .prod S S', h => by
      simp only [Arrows.transposeShp, unT, Shp.fst, Shp.snd]
      rw [transpose_unT S h.1, transpose_unT S' h.2]
  | _, .box S, h => by
      simp only [Arrows.transposeShp, unT, Shp.inner]
      rw [transpose_unT S h]
  | _, .dia ℓ S, h => by
      simp only [Arrows.transposeShp, unT, Shp.label, Shp.body]
      rw [transpose_unT S h.2]
      match ℓ, h.1 with
      | .fam _, _ => rfl

/-- ⭐**A term's shape one level in, read at an arrow, is its shape in the environment read at the
    arrow**, when the environment's top-level leaves are families. -/
theorem unT_termShp {Γ : Ctx} {t : GW hF M₀} (τ : GEnv hF M₀ Γ t)
    (hτ : ∀ v T h, (τ v T h).AllL IsFam) (b : (garrows hF M₀).Acc t) (j : ℕ) {T : VarType}
    {a : Ann T} (X : Term σ Γ T a) :
    unT b (Model.termShp τ (j + 1) X) =
      Model.termShp (fun v T h => unT b (τ v T h)) j X := by
  rw [Model.termShp_transpose τ (fun b v T h => unT b (τ v T h)) j
    (fun v T h => (transpose_unT _ (hτ v T h)).symm) X, unT_transpose]

/-! ## Keeping along an arrow -/

/-- A necessary object's shape restricted along an arrow: its family read at composite arrows. -/
def restrictBox {s : GW hF M₀} (a : (garrows hF M₀).Acc s) {B : VarType}
    (S : GShape hF M₀ s (.VTypeBox B)) : GShape hF M₀ a.1 (.VTypeBox B) :=
  .box (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb)
    fun b => unT (accTrans a b) S.inner)

/-- ⭐**An object of a keepable type kept along an arrow**: a possible one's labels restricted, a
    necessary one's family reindexed. -/
noncomputable def keepSh {s : GW hF M₀} (a : (garrows hF M₀).Acc s) :
    (U : VarType) → GShape hF M₀ s U → GShape hF M₀ a.1 U
  | .VTypeDia _, S => S.map (Arrows.Leaf.keepAlong hF a)
  | .VTypeBox _, S => restrictBox a S
  | U, _ => dsh [] a.1 U

theorem unT_dkeep {s : GW hF M₀} (a : (garrows hF M₀).Acc s) {B : VarType}
    (S : GShape hF M₀ s (.VTypeDia B)) :
    unT a ((GFunc.shp (σ := σ) (GFunc.dkeep hF) 0 S).inner) =
      S.map (Arrows.Leaf.keepAlong hF a) := by
  match S with
  | .dia ℓ S' =>
      simp only [GFunc.shp, Shp.inner, Shp.label, Shp.body, Shp.map, unT]
      rw [unT_map]
      rfl

theorem unT_dup {s : GW hF M₀} (a : (garrows hF M₀).Acc s) {B : VarType}
    (S : GShape hF M₀ s (.VTypeBox B)) (hS : S.inner.AllL IsFam) :
    unT a ((GFunc.shp (σ := σ) (GFunc.dup hF) 0 S).inner) = restrictBox a S := by
  simp only [GFunc.shp, Shp.inner, unT, restrictBox]
  rw [unT_map, transpose_unT_trans]
  refine congrArg Shp.box (Shp.map_congr_allL (fun ℓ hℓ => ?_) _ hS)
  match ℓ, hℓ with
  | .fam _, _ => rfl

/-- ⭐**Keeping is the arrow's component of `GFunc.keep`'s shape.** -/
theorem unT_keep {s : GW hF M₀} (a : (garrows hF M₀).Acc s) {U : VarType}
    (hk : U.keepable = true) (S : GShape hF M₀ s U)
    (hS : Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] S) :
    unT a ((GFunc.shp (σ := σ) (GFunc.keep hF hk) 0 S).inner) = keepSh a U S := by
  cases U with
  | VTypeDia B => exact unT_dkeep a S
  | VTypeBox B =>
      refine unT_dup a S ?_
      rw [Shp.box_eta S] at hS
      exact allL_isFam_of_wf [] _ hS
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd _ _ => cases hk

/-- ⭐**Keeping along two arrows is keeping along their composite.** -/
theorem keepSh_comp {s : GW hF M₀} (a : (garrows hF M₀).Acc s) (b : (garrows hF M₀).Acc a.1)
    {U : VarType} (hk : U.keepable = true) (S : GShape hF M₀ s U) :
    keepSh b U (keepSh a U S) = keepSh (accTrans a b) U S := by
  cases U with
  | VTypeDia B =>
      change (S.map _).map _ = S.map _
      rw [Shp.map_map]
      exact Shp.map_congr (fun ℓ => Arrows.Leaf.keepAlong_comp hF a b ℓ) S
  | VTypeBox B =>
      change Shp.box _ = Shp.box _
      refine congrArg Shp.box (congrArg _ (funext fun c => ?_))
      change unT (accTrans b c) (Arrows.transposeShp (F := garrows hF M₀)
        (Root := fun _ => VarSymb) fun d => unT (accTrans a d) S.inner) = _
      rw [unT_transpose]
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd _ _ => cases hk

/-! ## The canonical shapes at reachable addresses -/

/-- ⭐The canonical environment of a language below a stage reads every reachable address as the
    address's canonical shape. -/
theorem cEnv_ref (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {i : ℕ}
    {l : List VarType} (hl : (ctxOf l).Le (ctxOf (glat s i))) :
    ∀ (v : VarSymb) {T : VarType} (h : (ctxOf l).ref v = some T),
      (famEnv cEnv (ctxOf l) s).ref 0 v h = cEnv s v T
  | .root _, _, _ => rfl
  | .step v st, T, h => by
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, (ctxOf l).ref v = some U := by
          rw [Ctx.ref_step_proj _ v hs] at h
          cases hU : (ctxOf l).ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [Model.ShEnv.ref_proj _ 0 hs hU h, cEnv_ref hT hM₀ hl v hU,
          cEnv_eq hT hM₀ ⟨i, hl.ref hU⟩, cEnv_eq hT hM₀ ⟨i, hl.ref h⟩, cStep_proj]
      · rw [Ctx.ref_step_nonproj _ v hs, ctxOf_step] at h
        cases h

theorem rootSh_keep {s : GW hF M₀} (a : (garrows hF M₀).Acc s) (v : VarSymb) :
    ∀ (π : List Step) (A : VarType), (rootSh s v π A).map (Arrows.Leaf.keepAlong hF a) =
      rootSh a.1 (Arrows.RootKeep.keep (F := garrows hF M₀) (Root := fun _ => VarSymb) hF v a) π A
  | _, .Var => rfl
  | _, .VTypeOne => rfl
  | π, .VTypeProd A C => by
      simp only [rootSh, Shp.map]
      rw [rootSh_keep a v _ A, rootSh_keep a v _ C]
  | π, .VTypeBox A => by
      simp only [rootSh, Shp.map]
      rw [rootSh_keep a v _ A]
  | π, .VTypeDia A => by
      simp only [rootSh, Shp.map]
      rw [rootSh_keep a v _ A]
      rfl

/-- Keeping a generic shape gives the generic shape of the kept root. -/
theorem genDia_keep {s : GW hF M₀} (a : (garrows hF M₀).Acc s) (v : VarSymb) (A : VarType) :
    (genDia s v A).map (Arrows.Leaf.keepAlong hF a) =
      genDia a.1
        (Arrows.RootKeep.keep (F := garrows hF M₀) (Root := fun _ => VarSymb) hF v a) A := by
  simp only [genDia, Shp.map]
  rw [rootSh_keep]
  rfl

/-- A possible root has no other reachable address. -/
theorem ref_dia_root {l : List VarType} {r : ℕ} {B : VarType}
    (hr : (ctxOf l).ref (.root (.free r)) = some (.VTypeDia B)) :
    ∀ (u : VarSymb) {T : VarType}, (ctxOf l).ref u = some T → u.rt = .free r →
      u = .root (.free r)
  | .root _, _, _, hu => by cases hu; rfl
  | .step v st, T, h, hu => by
      exfalso
      by_cases hs : st.isProj = true
      · rw [Ctx.ref_step_proj _ v hs] at h
        cases hU : (ctxOf l).ref v with
        | none => rw [hU] at h; cases h
        | some U =>
            have hv := ref_dia_root hr v hU hu
            subst hv
            rw [hr] at hU
            cases hU
            rw [hr] at h
            cases st <;> simp_all [VarType.step, Step.isProj]
      · rw [Ctx.ref_step_nonproj _ v hs, ctxOf_step] at h
        cases h

/-- A possible root's kept item goes to a root. -/
theorem root_keep_img (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {i r : ℕ} {X : VarType} (hr : (ctxOf (glat s i)).ref (.root (.free r)) = some (.VTypeDia X))
    {y : VarSymb} (hy : fmapL hF M₀ t.1 (.step (.root (.free r)) .keep) = .inl y) :
    ∃ z, y = .root (.free z) := by
  have hitem : (ctxOf (glat s i)).kView none (.step (.root (.free r)) .keep) = some (.VTypeDia X) :=
    Ctx.boxIn_keep_of' hF hr rfl
  obtain ⟨m, hk, ⟨U, hU⟩⟩ := gcommitted_box hM₀ hc hitem
  have hbox : (ctxOf ((gnet hF M₀ m).fcl t.1)).boxIn (.step (.root (.free r)) .keep) = some U := by
    cases hkd : (gnet hF M₀ m).kind t.1 with
    | none => rw [hkd] at hU; exact hU
    | some x => rw [hkd] at hU; exact hU
  obtain ⟨-, hu, -⟩ := Ctx.boxIn_keep hbox
  have hk' : (gnet hF M₀ m).Live (c :: s.1) := hc ▸ hk
  obtain ⟨hsuf, -⟩ := (good_gnet hF hM₀ m).fwd c s.1 hk'
  rw [← hc] at hsuf
  have hdU : DeclAt s (.root (.free r)) U := ⟨m - gbirth hF M₀ s.2, by
    rw [glat_round s hk'.1]; exact (ctxOf_le_of_suffix hsuf).ref hu⟩
  obtain rfl := DeclAt.unique hM₀ hdU ⟨i, hr⟩
  rw [fmapL_at hM₀ hk ⟨_, hU⟩] at hy
  rw [hc] at hk hU hy
  exact (origOk_gnet hF hM₀ m).rootKeep c s.1 hk r X hU y hy

/-! ## Along an edge: images -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A keepable address's kept item in the `□` view. -/
theorem item_keep (hF : ModalSys.Four = true) {Γ : Ctx} {u : VarSymb} {U : VarType}
    (hu : Γ.ref u = some U) (hk : U.keepable = true) : Γ.kView none (.step u .keep) = some U :=
  Ctx.boxIn_keep_of' hF hu hk

/-- `diaT` at an address neither lifted nor an image of a root is generic. -/
theorem diaT_eq_genDia {ρ : ShFam hF M₀} {s : GW hF M₀} {v : VarSymb} {B : VarType}
    (hnl : ¬ ∃ z, v = .root (.free z) ∧ Lifted s z)
    (hni : ∀ c p, s.1 = c :: p →
      ¬ ∃ u, fmapL hF M₀ s.1 (.step (.root (.free u)) .keep) = .inl v) :
    diaT ρ s.1 s.2 v B = genDia s v B := by
  obtain ⟨sn, sb⟩ := s
  cases sn with
  | nil =>
      unfold diaT
      rw [dif_neg hnl]
  | cons c p =>
      unfold diaT
      rw [dif_neg hnl, dif_neg (hni c p rfl)]

/-- A root whose kept item is committed is declared at the parent, at a keepable type. -/
theorem committed_root_decl (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {u : ℕ} (h : GCommitted hF M₀ t.1 (.step (.root (.free u)) .keep)) :
    ∃ V, DeclAt s (.root (.free u)) V ∧ V.keepable = true := by
  obtain ⟨m, hk, ⟨U, hU⟩⟩ := h
  have hbox : (ctxOf ((gnet hF M₀ m).fcl t.1)).boxIn (.step (.root (.free u)) .keep) = some U := by
    cases hkd : (gnet hF M₀ m).kind t.1 with
    | none => rw [hkd] at hU; exact hU
    | some x => rw [hkd] at hU; exact hU
  obtain ⟨-, hu, hku⟩ := Ctx.boxIn_keep hbox
  have hk' : (gnet hF M₀ m).Live (c :: s.1) := hc ▸ hk
  obtain ⟨hsuf, -⟩ := (good_gnet hF hM₀ m).fwd c s.1 hk'
  rw [← hc] at hsuf
  exact ⟨U, ⟨m - gbirth hF M₀ s.2, by
    rw [glat_round s hk'.1]; exact (ctxOf_le_of_suffix hsuf).ref hu⟩, hku⟩

/-- An item whose entry is a declared address is committed. -/
theorem committed_of_decl {t : GW hF M₀} {w y : VarSymb} {U : VarType}
    (hy : fmapL hF M₀ t.1 (.step w .keep) = .inl y) (hd : DeclAt t y U) :
    GCommitted hF M₀ t.1 (.step w .keep) := by
  classical
  by_contra hn
  have hn' : ¬ ∃ m, (gnet hF M₀ m).Live t.1 ∧ ∃ T, (ctxOf ((gnet hF M₀ m).fcl t.1)).kView
      ((gnet hF M₀ m).kind t.1) (.step w .keep) = some T := hn
  rw [fmapL, dif_neg hn'] at hy
  cases hy
  obtain ⟨i, hi⟩ := hd
  rw [Ctx.ref_step_nonproj _ _ (by decide), ctxOf_step] at hi
  cases hi

/-- A possible address whose image is a root's image is that root. -/
theorem src_of_dia (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {i : ℕ} {u : VarSymb} {B : VarType} (hu : (ctxOf (glat s i)).ref u = some (.VTypeDia B))
    {y : VarSymb} (hy : fmapL hF M₀ t.1 (.step u .keep) = .inl y) {u' : ℕ}
    (hu' : fmapL hF M₀ t.1 (.step (.root (.free u')) .keep) = .inl y) :
    u = .root (.free u') := by
  have hcom := gcommitted_box hM₀ hc (item_keep hF hu rfl)
  obtain ⟨hdy, -⟩ := keep_img hM₀ hc ⟨i, hu⟩ rfl hy
  have hc2 := committed_of_decl hu' hdy
  obtain ⟨tn, tb⟩ := t
  change tn = c :: s.1 at hc
  subst hc
  have hrt := fmapL_inj hM₀ hc2 hcom hu' hy rfl
  obtain ⟨V, ⟨j, hj⟩, hkV⟩ := committed_root_decl hM₀ (t := ⟨c :: s.1, tb⟩) rfl hc2
  obtain ⟨hdy', -⟩ := keep_img hM₀ (t := ⟨c :: s.1, tb⟩) rfl ⟨j, hj⟩ hkV hu'
  obtain rfl := DeclAt.unique hM₀ hdy' hdy
  exact ref_dia_root (DeclAt.at_le hM₀ hj (le_max_right i j)) u
    (DeclAt.at_le hM₀ hu (le_max_left i j)) hrt.symm

/-- A possible non-root address is the image of no root. -/
theorem not_img_of_nonroot (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {i : ℕ} {u : VarSymb}
    {B : VarType} (hu : (ctxOf (glat s i)).ref u = some (.VTypeDia B))
    (hroot : ¬ ∃ r, u = .root (.free r)) :
    ∀ c₀ p₀, s.1 = c₀ :: p₀ →
      ¬ ∃ u', fmapL hF M₀ s.1 (.step (.root (.free u')) .keep) = .inl u := by
  rintro c₀ p₀ hs ⟨u', hu'⟩
  obtain ⟨sn, sb⟩ := s
  change sn = c₀ :: p₀ at hs
  subst hs
  have hc2 := committed_of_decl hu' ⟨i, hu⟩
  obtain ⟨V, ⟨j, hj⟩, hkV⟩ := committed_root_decl hM₀ (s := ⟨p₀, gborn_parent sb⟩)
    (t := ⟨c₀ :: p₀, sb⟩) rfl hc2
  obtain ⟨hdu, -⟩ := keep_img hM₀ (s := ⟨p₀, gborn_parent sb⟩) (t := ⟨c₀ :: p₀, sb⟩)
    rfl ⟨j, hj⟩ hkV hu'
  obtain rfl := DeclAt.unique hM₀ hdu ⟨i, hu⟩
  obtain ⟨z, hz⟩ := root_keep_img hM₀ (s := ⟨p₀, gborn_parent sb⟩) (t := ⟨c₀ :: p₀, sb⟩)
    rfl hj hu'
  exact hroot ⟨z, hz⟩

/-- ⭐**(B1) A possible address's image along an edge has its shape kept along the edge.** -/
theorem edge_dia_inl (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {i : ℕ} {u : VarSymb} {B : VarType}
    (hu : (ctxOf (glat s i)).ref u = some (.VTypeDia B)) {y : VarSymb}
    (hy : fmapL hF M₀ t.1 (.step u .keep) = .inl y) :
    cEnv t y (.VTypeDia B) =
      (cEnv s u (.VTypeDia B)).map (Arrows.Leaf.keepAlong hF (edgeAcc hc)) := by
  obtain ⟨hdy, -⟩ := keep_img hM₀ hc ⟨i, hu⟩ rfl hy
  have hcom := gcommitted_box hM₀ hc (item_keep hF hu rfl)
  rw [cEnv_eq hT hM₀ hdy, cEnv_eq hT hM₀ ⟨i, hu⟩]
  change diaT cEnv t.1 t.2 y B = (diaT cEnv s.1 s.2 u B).map _
  have hnl : ¬ ∃ z, y = .root (.free z) ∧ Lifted t z := by
    rintro ⟨z, rfl, ⟨c', e, he⟩⟩
    obtain ⟨tn, tb⟩ := t
    change tn = c :: s.1 at hc
    subst hc
    exact fmapL_imgNL hM₀ hcom hy rfl c' e he
  by_cases hroot : ∃ r, u = .root (.free r)
  · obtain ⟨r, rfl⟩ := hroot
    obtain ⟨tn, tb⟩ := t
    change tn = c :: s.1 at hc
    subst hc
    have hex : ∃ u', fmapL hF M₀ (c :: s.1) (.step (.root (.free u')) .keep) = .inl y := ⟨r, hy⟩
    conv_lhs => unfold diaT
    rw [dif_neg hnl, dif_pos hex]
    have hch : hex.choose = r := by
      have := src_of_dia hM₀ (t := ⟨c :: s.1, tb⟩) rfl hu hy hex.choose_spec
      injection this with h
      injection h with h
      exact h.symm
    rw [hch]
  · have hni : ∀ c₀ p₀, t.1 = c₀ :: p₀ →
        ¬ ∃ u', fmapL hF M₀ t.1 (.step (.root (.free u')) .keep) = .inl y :=
      fun _ _ _ ⟨u', hu'⟩ => hroot ⟨u', src_of_dia hM₀ hc hu hy hu'⟩
    have hnl' : ¬ ∃ z, u = .root (.free z) ∧ Lifted s z := fun ⟨z, hz, _⟩ => hroot ⟨z, hz⟩
    rw [diaT_eq_genDia hnl hni, diaT_eq_genDia hnl' (not_img_of_nonroot hM₀ hu hroot),
      genDia_keep, rootKeep_edge, wit_of_inl (reach_ppath hu).1 hy]

/-- ⭐**(B2) A necessary address's image along an edge has its family restricted along the
    edge.** -/
theorem edge_box_inl (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {i : ℕ} {u : VarSymb} {B : VarType}
    (hu : (ctxOf (glat s i)).ref u = some (.VTypeBox B)) {y : VarSymb}
    (hy : fmapL hF M₀ t.1 (.step u .keep) = .inl y) :
    cEnv t y (.VTypeBox B) = restrictBox (edgeAcc hc) (cEnv s u (.VTypeBox B)) := by
  obtain ⟨hdy, -⟩ := keep_img hM₀ hc ⟨i, hu⟩ rfl hy
  rw [cEnv_eq hT hM₀ hdy, cEnv_eq hT hM₀ ⟨i, hu⟩]
  obtain ⟨tn, tb⟩ := t
  change tn = c :: s.1 at hc
  subst hc
  refine congrArg Shp.box (congrArg _ (funext fun b => ?_))
  change _ = unT (accTrans (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl) b)
    (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb) fun b' =>
      boxEnt cEnv (fun t w => CStep cEnv B t w) s u (pathOf b'.2.down) b'.1 (pathOf_eq b'.2.down))
  rw [unT_transpose]
  have hp : pathOf (accTrans (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl) b).2.down =
      c :: pathOf b.2.down := by
    change pathOf (gtrans (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl).2.down b.2.down) = _
    rw [pathOf_trans (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl).2.down b.2.down,
      pathOf_of (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl).2.down (P := [c]) rfl]
    rfl
  rw [boxEnt_path cEnv _ s u hp b.1 _ (pathOf_eq b.2.down)]
  simp only [boxEnt, hy]
  rfl

/-- A lifted term's language is below a stage of the child. -/
theorem lift_le (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {w : VarSymb} {e : LTerm σ} (he : fmapL hF M₀ t.1 w = .inr e) :
    ∃ j, (ctxOf e.1).Le (ctxOf (glat t j)) := by
  classical
  obtain ⟨m, hk, ⟨T, hT⟩⟩ := fmapL_committed he
  have hfa := fmapL_at hM₀ hk ⟨T, hT⟩
  obtain ⟨-, -, hf, -⟩ := (good_gnet hF hM₀ m).fwd c s.1 (hc ▸ hk)
  rw [← hc] at hf
  have h := hf _ T (kView_lastProj hT) hT
  rw [← hfa, he] at h
  obtain ⟨l, U, a, τ⟩ := e
  change (if h : (ctxOf l).Le (ctxOf ((gnet hF M₀ m).st t.1).l) then
    SubE.tm (Term.mono h τ) else SubE.hide).OkRef T at h
  split_ifs at h with hle
  · exact ⟨m - gbirth hF M₀ t.2, by rw [glat_round t hk]; exact hle⟩
  · exact h.elim

/-- A lifted root's lift data is the edge's. -/
theorem lifted_eq (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1)
    {z : ℕ} {e : LTerm σ} (he : fmapL hF M₀ t.1 (.step (.root (.free z)) .keep) = .inr e)
    (h : Lifted s z) : h.child = t ∧ h.ent = e := by
  rw [hc] at he
  have hcc := fmapL_lift1 hM₀ h.choose_spec.choose_spec he
  have hch : h.child = t := Subtype.ext (by
    change h.choose :: s.1 = t.1
    rw [hcc, hc])
  refine ⟨hch, ?_⟩
  have key : ∀ c' (_ : c' = c) (e' : LTerm σ),
      fmapL hF M₀ (c' :: s.1) (.step (.root (.free z)) .keep) = .inr e' → e' = e := by
    intro c' hc' e' h'
    subst hc'
    rw [he] at h'
    exact (Sum.inr.inj h').symm
  exact key _ hcc _ h.choose_spec.choose_spec

/-- A lifted root's template is its edge's pull-back. -/
theorem cEnv_lifted (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {i z : ℕ} {B : VarType}
    (hu : (ctxOf (glat s i)).ref (.root (.free z)) = some (.VTypeDia B)) {e : LTerm σ}
    (he : fmapL hF M₀ t.1 (.step (.root (.free z)) .keep) = .inr e) :
    cEnv s (.root (.free z)) (.VTypeDia B) = liftDiaAt cEnv s z t e B := by
  have hL : Lifted s z := ⟨c, e, hc ▸ he⟩
  have key : ∀ z' (hz' : z' = z) (hL' : Lifted s z'),
      liftDiaAt cEnv s z' hL'.child hL'.ent B = liftDiaAt cEnv s z t e B := by
    intro z' hz' hL'
    subst hz'
    obtain ⟨h₁, h₂⟩ := lifted_eq hM₀ hc he hL'
    rw [h₁, h₂]
  rw [cEnv_eq hT hM₀ ⟨i, hu⟩]
  change diaT cEnv s.1 s.2 (.root (.free z)) B = _
  have hex : ∃ z', VarSymb.root (.free z) = .root (.free z') ∧ Lifted s z' := ⟨z, rfl, hL⟩
  have hz : hex.choose = z := by
    have := hex.choose_spec.1
    injection this with h
    injection h with h
    exact h.symm
  obtain ⟨sn, sb⟩ := s
  cases sn with
  | nil =>
      unfold diaT
      rw [dif_pos hex]
      exact key _ hz _
  | cons c₀ p₀ =>
      unfold diaT
      rw [dif_pos hex]
      exact key _ hz _

/-- ⭐**A lifted possible root kept along its lift edge has its lifted term's shape.** -/
theorem edge_dia_inr (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {i z : ℕ} {B : VarType}
    (hu : (ctxOf (glat s i)).ref (.root (.free z)) = some (.VTypeDia B)) {e : LTerm σ}
    (he : fmapL hF M₀ t.1 (.step (.root (.free z)) .keep) = .inr e)
    {b : Ann (.VTypeDia B)} {τ : Term σ (ctxOf e.1) (.VTypeDia B) b}
    (hd : e.diaOf B = some ⟨b, τ⟩) :
    (cEnv s (.root (.free z)) (.VTypeDia B)).map (Arrows.Leaf.keepAlong hF (edgeAcc hc)) =
      Model.termShp (famEnv cEnv (ctxOf e.1) t) 0 τ := by
  obtain ⟨j, hl⟩ := lift_le hM₀ hc he
  rw [cEnv_lifted hT hM₀ hc hu he]
  exact liftDiaAt_keep (fun t v T => cEnv_wf t v T) hc (cEnv_ref hT hM₀ hl)
    (fun v X hv => by
      rw [cEnv_eq hT hM₀ ⟨j, hl.ref hv⟩]
      exact cStep_top cEnv t v X) he hd

/-- ⭐**A lifted necessary root restricted along its lift edge has its lifted term's shape.** -/
theorem edge_box_inr (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {i z : ℕ} {B : VarType}
    (hu : (ctxOf (glat s i)).ref (.root (.free z)) = some (.VTypeBox B)) {e : LTerm σ}
    (he : fmapL hF M₀ t.1 (.step (.root (.free z)) .keep) = .inr e)
    {b : Ann (.VTypeBox B)} {τ : Term σ (ctxOf e.1) (.VTypeBox B) b}
    (hd : e.boxOf B = some ⟨b, τ⟩) :
    restrictBox (edgeAcc hc) (cEnv s (.root (.free z)) (.VTypeBox B)) =
      Model.termShp (famEnv cEnv (ctxOf e.1) t) 0 τ := by
  have hXwf : Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) []
      (Model.termShp (famEnv cEnv (ctxOf e.1) t) 0 τ) :=
    Model.shWF_termShp (lw := []) (famEnv_wf (fun t v T => cEnv_wf t v T) (ctxOf e.1) t) τ
  rw [Shp.box_eta (Model.termShp _ _ τ)] at hXwf ⊢
  have hXfam := allL_isFam_of_wf [] _ hXwf
  rw [cEnv_eq hT hM₀ ⟨i, hu⟩]
  obtain ⟨tn, tb⟩ := t
  change tn = c :: s.1 at hc
  subst hc
  refine congrArg Shp.box ?_
  conv_rhs => rw [← transpose_unT _ hXfam]
  refine congrArg _ (funext fun b' => ?_)
  change unT (accTrans (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl) b')
    (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb) fun b'' =>
      boxEnt cEnv (fun t w => CStep cEnv B t w) s (.root (.free z)) (pathOf b''.2.down) b''.1
        (pathOf_eq b''.2.down)) = _
  rw [unT_transpose]
  have hp : pathOf (accTrans (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl) b').2.down =
      c :: pathOf b'.2.down := by
    change pathOf (gtrans (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl).2.down b'.2.down) = _
    rw [pathOf_trans (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl).2.down b'.2.down,
      pathOf_of (edgeAcc (s := s) (t := ⟨c :: s.1, tb⟩) rfl).2.down (P := [c]) rfl]
    rfl
  rw [boxEnt_path cEnv _ s _ hp b'.1 _ (pathOf_eq b'.2.down)]
  simp only [boxEnt, he, dif_pos (pathOf_ok b'.2.down), hd]
  rfl

/-- ⭐(B1)/(B2): **an address's image along an edge is the address kept along it.** -/
theorem edge_inl (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {i : ℕ} {u : VarSymb} {U : VarType}
    (hu : (ctxOf (glat s i)).ref u = some U) (hk : U.keepable = true) {y : VarSymb}
    (hy : fmapL hF M₀ t.1 (.step u .keep) = .inl y) :
    cEnv t y U = keepSh (edgeAcc hc) U (cEnv s u U) := by
  cases U with
  | VTypeDia B => exact edge_dia_inl hT hM₀ hc hu hy
  | VTypeBox B => exact edge_box_inl hT hM₀ hc hu hy
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd _ _ => cases hk

/-! ## Along an edge: the entry -/

/-- ⭐**An edge's entry for a kept item reads as the item kept along the edge.** -/
theorem edge_entry (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) (i : ℕ) {u : VarSymb} {U : VarType}
    (hu : (ctxOf (glat s i)).ref u = some U) (hk : U.keepable = true)
    (hok : (eS σ (ctxOf (glat t (glstg s t i))) (fmapL hF M₀ t.1) (.step u .keep)).OkRef U) :
    Model.entryShp (famEnv cEnv (ctxOf (glat t (glstg s t i))) t) 0
        (eS σ _ (fmapL hF M₀ t.1) (.step u .keep)) hok =
      keepSh (edgeAcc hc) U (cEnv s u U) := by
  set Δ := ctxOf (glat t (glstg s t i))
  have hθ : eS σ Δ (fmapL hF M₀ t.1) (.step u .keep) =
      entOf Δ (fmapL hF M₀ t.1 (.step u .keep)) := eS_item _ rfl
  rw [Model.entryShp_congr _ 0 hθ hok (hθ ▸ hok)]
  suffices key : ∀ (x : LEnt σ), fmapL hF M₀ t.1 (.step u .keep) = x →
      ∀ (hx : (entOf Δ x).OkRef U), Model.entryShp (famEnv cEnv Δ t) 0 (entOf Δ x) hx =
        keepSh (edgeAcc hc) U (cEnv s u U) from key _ rfl _
  intro x hfm hx
  cases x with
  | inl y =>
      change (famEnv cEnv Δ t).ref 0 y hx = _
      rw [cEnv_ref hT hM₀ (Ctx.Le.refl _)]
      exact edge_inl hT hM₀ hc hu hk hfm
  | inr e =>
      have hfm' := hfm
      rw [hc] at hfm'
      obtain ⟨z, hz⟩ := fmapL_term hM₀ hfm'
      obtain rfl : u = .root (.free z) := (VarSymb.step.inj hz).1
      obtain ⟨l, T, a, τ⟩ := e
      by_cases hle : (ctxOf l).Le Δ
      · have he : entOf Δ (.inr ⟨l, T, a, τ⟩) = .tm (Term.mono hle τ) := by
          simp only [entOf, dif_pos hle]
        have hx₂ : (SubE.tm (Term.mono hle τ) : SubE σ Δ).OkRef U := he ▸ hx
        rw [Model.entryShp_congr _ 0 he hx hx₂]
        have hTU : T = U := hx₂
        subst hTU
        change Model.termShp _ 0 (Term.mono hle τ) = _
        rw [Model.termShp_mono (Γ := ctxOf l) (Γ' := Δ) (h := hle) (ρ := famEnv cEnv (ctxOf l) t)
          (ρ' := famEnv cEnv Δ t) (fun _ _ _ => rfl) 0]
        cases T with
        | VTypeDia B =>
            exact (edge_dia_inr hT hM₀ hc hu hfm (b := a) (τ := τ)
              (by simp [LTerm.diaOf])).symm
        | VTypeBox B =>
            exact (edge_box_inr hT hM₀ hc hu hfm (b := a) (τ := τ)
              (by simp [LTerm.boxOf])).symm
        | Var => cases hk
        | VTypeOne => cases hk
        | VTypeProd _ _ => cases hk
      · have he : entOf Δ (.inr ⟨l, T, a, τ⟩) = .hide := by
          simp only [entOf, dif_neg hle]
        have hh : (SubE.hide : SubE σ Δ).OkRef U := he ▸ hx
        exact hh.elim

/-! ## Along a path -/

theorem unT_eq_map {t : GW hF M₀} (b : (garrows hF M₀).Acc t) :
    ∀ {A : VarType} (S : GShape hF M₀ t A), unT b S = S.map fun ℓ => evalLeaf ℓ b
  | _, .var => rfl
  | _, .one => rfl
  | _, .prod S S' => by
      simp only [unT, Shp.map]
      rw [unT_eq_map b S, unT_eq_map b S']
  | _, .box S => by
      simp only [unT, Shp.map]
      rw [unT_eq_map b S]
  | _, .dia ℓ S => by
      simp only [unT, Shp.map]
      rw [unT_eq_map b S]

/-- Collapsing the top level of a shape of families reads it at the identity arrow. -/
theorem collapse_unT (hT : ModalSys.T = true) {t : GW hF M₀} {A : VarType}
    (S : GShape hF M₀ t A) (hS : S.AllL IsFam) :
    S.map (Arrows.Leaf.collapse hT 0) = unT ((garrows hF M₀).reflAcc hT t) S := by
  rw [unT_eq_map]
  refine Shp.map_congr_allL (fun ℓ hℓ => ?_) S hS
  match ℓ, hℓ with
  | .fam _, _ => rfl

/-- An entry read in an environment read at an arrow is the entry one level in, read there. -/
theorem entryShp_unT {Δ : Ctx} {t : GW hF M₀} (τ : GEnv hF M₀ Δ t)
    (hτ : ∀ v T h, (τ v T h).AllL IsFam) (b : (garrows hF M₀).Acc t) :
    ∀ (e : SubE σ Δ) {T : VarType} (h : e.OkRef T),
      Model.entryShp (fun v T h => unT b (τ v T h)) 0 e h = unT b (Model.entryShp τ 1 e h)
  | .ren w, T, h => by
      change Model.ShEnv.ref _ 0 w h = unT b (Model.ShEnv.ref τ 1 w h)
      rw [← Model.termShp_eta (σ := σ) _ 0 w h, ← Model.termShp_eta (σ := σ) τ 1 w h,
        unT_termShp τ hτ b 0]
  | .tm s, T, h => by
      cases h
      exact (unT_termShp τ hτ b 0 s).symm
  | .hide, _, h => h.elim

theorem restrictBox_wf {s : GW hF M₀} (a : (garrows hF M₀).Acc s) {B : VarType}
    (S : GShape hF M₀ s (.VTypeBox B))
    (hS : Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] S) :
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (restrictBox a S) := by
  rw [Shp.box_eta S] at hS
  exact Model.shWF_transpose true [] _ fun b => shWF_unT _ [] _ hS

theorem keepSh_wf {s : GW hF M₀} (a : (garrows hF M₀).Acc s) {U : VarType}
    (S : GShape hF M₀ s U)
    (hS : Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] S) :
    Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [] (keepSh a U S) := by
  cases U with
  | VTypeDia B => exact shWF_map_keepAlong a [] S hS
  | VTypeBox B => exact restrictBox_wf a S hS
  | Var => exact dsh_wf [] _ _
  | VTypeOne => exact dsh_wf [] _ _
  | VTypeProd _ _ => exact dsh_wf [] _ _

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- An item of a `□` view under T and 4 is a kept item. -/
theorem box_item (hF : ModalSys.Four = true) (hT : ModalSys.T = true) {Γ : Ctx} {w : VarSymb}
    {W : VarType} (hw : Γ.boxIn w = some W) :
    ∃ u, w = .step u .keep ∧ Γ.ref u = some W ∧ W.keepable = true := by
  have hk : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  match w, hw with
  | .step u .keep, hw =>
      obtain ⟨-, hu, hku⟩ := Ctx.boxIn_keep hw
      exact ⟨u, rfl, hu, hku⟩
  | .step u .box, hw =>
      change (if ModalSys.keepOnly then none else _) = _ at hw
      rw [if_pos hk] at hw
      cases hw
  | .root _, hw => cases hw
  | .step _ .fst, hw => cases hw
  | .step _ .snd, hw => cases hw
  | .step _ .dia, hw => cases hw
  | .step _ .here, hw => cases hw

/-- The canonical environment pushed into `□`, at a kept item, is the item's shape kept. -/
theorem boxPush_keep (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {i : ℕ}
    {u : VarSymb} {W : VarType} (hk : W.keepable = true)
    (hw : (ctxOf (glat s i)).boxIn (.step u .keep) = some W) :
    (famEnv cEnv (ctxOf (glat s i)) s).boxPush 0 (.step u .keep) W hw =
      (GFunc.shp (σ := σ) (GFunc.keep hF hk) 0 (cEnv s u W)).inner := by
  change (GFunc.shp (GFunc.keep (σ := σ) (Ctx.boxIn_keep hw).1 (Ctx.boxIn_keep hw).2.2) 0
    ((famEnv cEnv (ctxOf (glat s i)) s).ref 0 u (Ctx.boxIn_keep hw).2.1)).inner = _
  rw [cEnv_ref hT hM₀ (Ctx.Le.refl _)]

/-- ⭐**The laws of the canonical shapes**: along every path, the environment pulled back from
    the canonical shapes at the end is the path's component of the canonical environment pushed
    into `□`. -/
theorem comp_pull (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ),
      pullP hM₀ P s t h hP i (famEnv cEnv (ctxOf (glat t (pstg s t P h i))) t) =
        fun w W hw => unT ⟨t, ⟨⟨P, hP, h⟩⟩⟩
          ((famEnv cEnv (ctxOf (glat s i)) s).boxPush 0 w W hw)
  | [], s, t, h, hP, i => by
      obtain rfl : t = s := gw_eq h
      funext w W hw
      change ((Model.ShEnv.boxPush (famEnv cEnv (ctxOf (glat t i)) t) 0) w W hw).map
        (Arrows.Leaf.collapse hP.T_of_nil 0) = _
      have hwf := Model.ShEnv.wf_boxPush' (k := 0)
        (famEnv_wf (fun t v T => cEnv_wf t v T) (ctxOf (glat t i)) t) rfl w W hw
      rw [collapse_unT hP.T_of_nil _ (allL_isFam_of_wf [] _ hwf)]
  | [c], s, t, h, _, i => by
      funext w W hw
      obtain ⟨u, rfl, hu, hk⟩ := box_item hF hT hw
      rw [boxPush_keep hT hM₀ hk hw, unT_keep _ hk _ (cEnv_wf s u W)]
      exact edge_entry hT hM₀ h i hu hk _
  | c :: c' :: P, s, t, h, _, i => by
      funext w W hw
      obtain ⟨u, rfl, hu, hk⟩ := box_item hF hT hw
      rw [boxPush_keep hT hM₀ hk hw, unT_keep _ hk _ (cEnv_wf s u W)]
      set t₁ := stepW s c (born_step h)
      set ρ₁ := famEnv cEnv (ctxOf (glat t₁ (glstg s t₁ i))) t₁
      have ih : pullP hM₀ (c' :: P) t₁ t h pathOk_cons (glstg s t₁ i)
          (famEnv cEnv (ctxOf (glat t (pstg s t (c :: c' :: P) h i))) t) =
            fun w W hw => unT ⟨t, ⟨⟨c' :: P, pathOk_cons, h⟩⟩⟩ (ρ₁.boxPush 0 w W hw) :=
        comp_pull hT hM₀ (c' :: P) t₁ t h pathOk_cons (glstg s t₁ i)
      unfold pullP shiftPull
      rw [ih]
      set θ := eS σ (ctxOf (glat t₁ (glstg s t₁ i))) (fmapL hF M₀ (c :: s.1))
      change Model.ShEnv.ref _ 0 (.step (.step u .keep) .keep) _ = _
      rw [Model.ShEnv.ref_nonproj _ _ (by decide)]
      unfold Model.substShEnv
      have hok : (θ (.step u .keep)).OkRef W :=
        ok_eS_kView (gentOk_box hM₀ (t := t₁) ⟨c, rfl⟩ i) _ W rfl (item_keep hF hu hk)
      rw [Model.entryShp_congr _ 0
        (show θ.box (.step (.step u .keep) .keep) = (θ (.step u .keep)).keepE from rfl) _
        (SubE.okRef_keepE' hF hk hok)]
      have hτ : ∀ v T h', ((ρ₁.boxPush 0) v T h').AllL IsFam := fun v T h' =>
        allL_isFam_of_wf [] _ (Model.ShEnv.wf_boxPush' (k := 0)
          (famEnv_wf (fun t v T => cEnv_wf t v T) _ t₁) rfl v T h')
      rw [entryShp_unT _ hτ]
      have hkeep : Model.entryShp (ρ₁.boxPush 0) 1 (θ (.step u .keep)).keepE
          (SubE.okRef_keepE' hF hk hok) =
          (GFunc.shp (σ := σ) (GFunc.keep hF hk) 0 (Model.entryShp ρ₁ 0 _ hok)).inner := by
        cases W with
        | VTypeBox B => exact Model.entryShp_keepE ρ₁ 0 hF hok
        | VTypeDia B =>
            exact Model.entryShp_keepE_dia (lw := []) ρ₁
              (famEnv_wf (fun t v T => cEnv_wf t v T) _ t₁) hF hok
        | Var => cases hk
        | VTypeOne => cases hk
        | VTypeProd _ _ => cases hk
      have he : Model.entryShp ρ₁ 0 (θ (.step u .keep)) hok =
          keepSh (edgeAcc (s := s) (t := t₁) rfl) W (cEnv s u W) :=
        edge_entry hT hM₀ (t := t₁) rfl i hu hk hok
      rw [hkeep,
        unT_keep _ hk _ (entryShp_wf (famEnv_wf (fun t v T => cEnv_wf t v T) _ t₁) _ hok),
        he]
      exact keepSh_comp (edgeAcc (s := s) (t := t₁) rfl) _ hk _

/-- ⭐**A `□` body's translation along a path has its shape inside `□`, read at the path's
    arrow.** -/
theorem termShp_pTr (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (P : List ℕ)
    (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ) {A : VarType} {a : Ann A}
    (X : Term σ ((ctxOf (glat s i)).kView none) A a) :
    Model.termShp (famEnv cEnv (ctxOf (glat t (pstg s t P h i))) t) 0 (pTr hM₀ s t P h hP i X).2 =
      unT ⟨t, ⟨⟨P, hP, h⟩⟩⟩
        (Model.termShp ((famEnv cEnv (ctxOf (glat s i)) s).boxPush 0) 1 X) := by
  rw [pTr_pullP hM₀ P s t h hP i _ (famEnv_wf (fun t v T => cEnv_wf t v T) _ t),
    comp_pull hT hM₀ P s t h hP i]
  exact (unT_termShp _ (fun v T h' => allL_isFam_of_wf [] _ (Model.ShEnv.wf_boxPush' (k := 0)
    (famEnv_wf (fun t v T => cEnv_wf t v T) _ s) rfl v T h')) _ 0 X).symm

/-- ⭐**The canonical environment pushed into `□`**: a body's shape inside `□` is the transposed
    family of its translations' shapes. -/
theorem termShp_boxPush (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) (i : ℕ)
    {A : VarType} {a : Ann A} (X : Term σ ((ctxOf (glat s i)).kView none) A a) :
    Model.termShp ((famEnv cEnv (ctxOf (glat s i)) s).boxPush 0) 1 X =
      Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb) fun b =>
        Model.termShp (famEnv cEnv (ctxOf (glat b.1 (pstg s b.1 (pathOf b.2.down)
            (pathOf_eq b.2.down) i))) b.1) 0
          (pTr hM₀ s b.1 (pathOf b.2.down) (pathOf_eq b.2.down) (pathOf_ok b.2.down) i X).2 := by
  have hwf : Model.ShWF (F := garrows hF M₀) (Root := fun _ => VarSymb) [true]
      (Model.termShp ((famEnv cEnv (ctxOf (glat s i)) s).boxPush 0) 1 X) :=
    Model.shWF_termShp (lw := [true]) (Model.ShEnv.wf_boxPush' (k := 0)
      (famEnv_wf (fun t v T => cEnv_wf t v T) (ctxOf (glat s i)) s) rfl) X
  conv_lhs => rw [← transpose_unT _ (allL_isFam_of_wf [] _ hwf)]
  refine congrArg _ (funext fun b => ?_)
  rw [termShp_pTr hT hM₀]

end GArrow

end V12M
