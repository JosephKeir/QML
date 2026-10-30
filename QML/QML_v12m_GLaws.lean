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

and the laws:

* along an edge, an entry for a kept item reads as the item kept along the edge (`edge_entry`):
  both sides are the address shapes of the entry's indices (`entry_shOf`, `keepSh_shOf`), by
  the translation's form (`keptTr_form`);
* ⭐`comp_pull`: along every path, the pulled-back canonical environment is the path's component
  of the canonical environment pushed into `□` (by induction on the path);
* ⭐`termShp_pTr`, `termShp_boxPush`: a `□` body's translation has its shape inside `□`, read at
  the arrow; `termShp_pTr_keep` at a kept item; `termShp_pTr_keepDia`, the keep law for possible
  terms.
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

/-! ## Shapes indexed by positions -/

/-- A shape of a type, its leaf at each spelled position given by `L` (T + 4 spelling: a `□` is
    entered by `keep.here`). -/
noncomputable def shOf (t : GW hF M₀) : (T : VarType) → (List Step → GLeaf hF M₀ t) →
    GShape hF M₀ t T
  | .Var, _ => .var
  | .VTypeOne, _ => .one
  | .VTypeProd A C, L => .prod (shOf t A fun π => L (.fst :: π)) (shOf t C fun π => L (.snd :: π))
  | .VTypeBox A, L => .box (shOf t A fun π => L (.keep :: .here :: π))
  | .VTypeDia A, L => .dia (L []) (shOf t A fun π => L (.dia :: π))

/-- Shapes indexed by positions agree when their leaves agree at the typed positions. -/
theorem shOf_congr (hT : ModalSys.T = true) {t : GW hF M₀} :
    ∀ (T : VarType) (L L' : List Step → GLeaf hF M₀ t),
      (∀ π X, Step.walkTy T π = some (.VTypeDia X) → L π = L' π) → shOf t T L = shOf t T L'
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, L, L', h => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [shOf_congr hT A _ _ fun π X hπ => h (.fst :: π) X hπ,
        shOf_congr hT C _ _ fun π X hπ => h (.snd :: π) X hπ]
  | .VTypeBox A, L, L', h => by
      change Shp.box _ = Shp.box _
      rw [shOf_congr hT A _ _ fun π X hπ => h (.keep :: .here :: π) X
        (by rw [walkTy_keep rfl, walkTy_here hT]; exact hπ)]
  | .VTypeDia A, L, L', h => by
      change Shp.dia _ _ = Shp.dia _ _
      rw [h [] A rfl, shOf_congr hT A _ _ fun π X hπ => h (.dia :: π) X hπ]

theorem shOf_map {t : GW hF M₀} {t' : GW hF M₀} (g : GLeaf hF M₀ t → GLeaf hF M₀ t') :
    ∀ (T : VarType) (L : List Step → GLeaf hF M₀ t),
      (shOf t T L).map g = shOf t' T fun π => g (L π)
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, L => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [shOf_map g A, shOf_map g C]
  | .VTypeBox A, L => by
      change Shp.box _ = Shp.box _
      rw [shOf_map g A]
  | .VTypeDia A, L => by
      change Shp.dia _ _ = Shp.dia _ _
      rw [shOf_map g A]

theorem unT_shOf {t : GW hF M₀} (b : (garrows hF M₀).Acc t) :
    ∀ (T : VarType) (L : List Step → GLeaf hF M₀ t),
      unT b (shOf t T L) = shOf b.1 T fun π => evalLeaf (L π) b
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, L => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [unT_shOf b A, unT_shOf b C]
  | .VTypeBox A, L => by
      change Shp.box _ = Shp.box _
      rw [unT_shOf b A]
  | .VTypeDia A, L => by
      change Shp.dia _ _ = Shp.dia _ _
      rw [unT_shOf b A]

theorem transpose_shOf {t : GW hF M₀} :
    ∀ (T : VarType) (L : (a : (garrows hF M₀).Acc t) → List Step → GLeaf hF M₀ a.1),
      Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb)
          (fun a => shOf a.1 T (L a)) = shOf t T fun π => .fam fun a => L a π
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, L =>
      congrArg₂ Shp.prod (transpose_shOf A fun a π => L a (.fst :: π))
        (transpose_shOf C fun a π => L a (.snd :: π))
  | .VTypeBox A, L => congrArg Shp.box (transpose_shOf A fun a π => L a (.keep :: .here :: π))
  | .VTypeDia A, L => congrArg₂ Shp.dia rfl (transpose_shOf A fun a π => L a (.dia :: π))

/-- ⭐**An address shape is indexed by the address's positions** (T + 4). -/
theorem annSh_eta (hko : ModalSys.keepOnly = true) {t : GW hF M₀} :
    ∀ (T : VarType) (w : VarSymb), annSh t (Ann.eta w T) = shOf t T fun π => gLab t (w.ext π)
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, w => by
      change Shp.prod (annSh t (Ann.eta (.step w .fst) A)) (annSh t (Ann.eta (.step w .snd) C)) = _
      rw [annSh_eta hko A, annSh_eta hko C]
      rfl
  | .VTypeBox A, w => by
      change Shp.box (annSh t (Ann.eta w.inner A)) = _
      rw [VarSymb.inner_keepOnly hko, annSh_eta hko A]
      rfl
  | .VTypeDia A, w => by
      change Shp.dia (gLab t w) (annSh t (Ann.eta (.step w .dia) A)) = _
      rw [annSh_eta hko A]
      rfl

/-! ## The canonical shapes at reachable addresses -/

/-- Collapsing the top of a kept address's label reads it at the world. -/
theorem collapse_gLab (hT : ModalSys.T = true) {s : GW hF M₀} {v : VarSymb} (hv : PPath v.path)
    (q : List Step) :
    Arrows.Leaf.collapse hT 0 (gLab s ((VarSymb.step v .keep).ext q)) = gLab s (v.ext q) := by
  rw [gLab_keep _ hv]
  change gMem s s (pathOf (grefl hT s)) (pathOf_eq _) _ = _
  rw [gMem_path (pathOf_refl hT s) _ rfl, gMem_kept_nil _ _ _ hv]

/-- A projection of an address shape is the address shape of the projection. -/
theorem proj_annSh (hT : ModalSys.T = true) {s : GW hF M₀} {v : VarSymb} (hv : PPath v.path)
    {U T : VarType} {st : Step} (hs : st.isProj = true) (h : U.step st = some T) :
    GFunc.shp (GFunc.proj (σ := σ) hs h) 0 (annSh s (Ann.eta v U)) =
      annSh s (Ann.eta (.step v st) T) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  cases U <;> cases st <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · rename_i X
    obtain ⟨hT', rfl⟩ := VarType.step_here h
    change (annSh s (Ann.eta v.inner X)).map (Arrows.Leaf.collapse hT' 0) = _
    rw [annSh_eta hko, annSh_eta hko, shOf_map]
    congr 1
    funext π
    rw [VarSymb.inner_keepOnly hko,
      show ((VarSymb.step v .keep).step .here).ext π = (VarSymb.step v .keep).ext (.here :: π)
        from rfl, collapse_gLab hT' hv]
    rfl

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
          cEnv_decl hT hM₀ ⟨i, hl.ref hU⟩, cEnv_decl hT hM₀ ⟨i, hl.ref h⟩]
        exact proj_annSh hT (reach_ppath (hl.ref hU)).1 hs _
      · rw [Ctx.ref_step_nonproj _ v hs, ctxOf_step] at h
        cases h

/-- ⭐**A declared address kept into `□`**: its canonical shape kept is the kept address's
    address shape. -/
theorem boxPush_cEnv (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀}
    {u : VarSymb} {U : VarType} (hd : DeclAt s u U) (hk : U.keepable = true) :
    (GFunc.shp (σ := σ) (GFunc.keep hF hk) 0 (cEnv s u U)).inner =
      annSh s (Ann.eta (.step u .keep) U) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨i, hi⟩ := id hd
  have hu := (reach_ppath hi).1
  rw [cEnv_decl hT hM₀ hd]
  cases U with
  | VTypeDia A =>
      change Shp.dia (Arrows.Leaf.dk hF 0 (gLab s u))
        ((annSh s (Ann.eta (.step u .dia) A)).map (Arrows.Leaf.dkB hF 0)) = _
      rw [annSh_eta hko, annSh_eta hko, shOf_map]
      change Shp.dia _ _ = Shp.dia _ _
      congr 1
      · change Arrows.Leaf.fam _ = gLab s ((VarSymb.step u .keep).ext [])
        rw [gLab_keep _ hu]
        congr 1
        funext b
        rw [keepAlong_eq hT hM₀]
        exact gKA_gLab (q := []) hT hM₀ ⟨hu, _, A, hd, rfl⟩ (fun _ h => by cases h) b
      · refine shOf_congr hT A _ _ fun π X hπ => ?_
        change Arrows.Leaf.fam _ = gLab s ((VarSymb.step u .keep).ext (.dia :: π))
        rw [gLab_keep _ hu]
        congr 1
        funext b
        rw [keepAlong_eq hT hM₀]
        exact gKA_gLab (q := .dia :: π) hT hM₀ ⟨hu, _, X, hd, by rw [walkTy_keep rfl]; exact hπ⟩
          (noProjHead_cons rfl π) b
  | VTypeBox A =>
      change Shp.box ((annSh s (Ann.eta u.inner A)).map (Arrows.Leaf.shift hF 0)) =
        Shp.box (annSh s (Ann.eta (VarSymb.step u .keep).inner A))
      rw [annSh_eta hko, annSh_eta hko, shOf_map]
      congr 1
      refine shOf_congr hT A _ _ fun π X hπ => ?_
      rw [VarSymb.inner_keepOnly hko, VarSymb.inner_keepOnly hko,
        show ((VarSymb.step u .keep).step .here).ext π = (VarSymb.step u .keep).ext (.here :: π)
          from rfl,
        show (((VarSymb.step u .keep).step .keep).step .here).ext π =
          (VarSymb.step u .keep).ext (.keep :: .here :: π) from rfl,
        gLab_keep _ hu, gLab_keep _ hu]
      change Arrows.Leaf.fam _ = _
      congr 1
      funext b
      rw [gMem_dk hT hM₀ _ _ ⟨hu, _, X, hd,
        by rw [walkTy_keep rfl, walkTy_here hT]; exact hπ⟩]
      congr 1
      funext b'
      exact gMem_path (pathOf_trans b.2.down b'.2.down) _ _ _
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd _ _ => cases hk

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- A keepable address's kept item in the `□` view. -/
theorem item_keep (hF : ModalSys.Four = true) {Γ : Ctx} {u : VarSymb} {U : VarType}
    (hu : Γ.ref u = some U) (hk : U.keepable = true) : Γ.kView none (.step u .keep) = some U :=
  Ctx.boxIn_keep_of' hF hu hk

/-! ## Along an edge -/

/-- Where an edge sends a typed position of a declared address, and the address kept. -/
theorem edge_point (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {c : ℕ}
    (hb : GBorn hF M₀ (c :: s.1)) {u : VarSymb} {U : VarType} (hd : DeclAt s u U)
    {π : List Step} {X : VarType} (hπ : Step.walkTy U (.keep :: π) = some (.VTypeDia X)) :
    ∃ w q', entIdx (fmapL hF M₀ (c :: s.1) (.step u .keep)) π = w.ext q' ∧
      entIdx (fmapL hF M₀ (c :: s.1) (.step u .keep)) (.keep :: π) =
        (VarSymb.step w .keep).ext q' ∧ PPath w.path ∧ Step.levels q' = Step.levels π := by
  obtain ⟨w, n, X₁, X₁', R, tl, rfl, hlX, -, hw, htl, hform⟩ := keptTr_form hT hM₀ s c hb hd hπ
  obtain ⟨h₁, h₂, -⟩ := hform n R (fun h => (htl h).2.2) X hπ
  exact ⟨w, _, h₁, h₂, hw, (levels_form hlX).symm⟩

/-- The arrow of an edge has the edge's path. -/
theorem pathOf_edge {s t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: s.1) :
    pathOf (edgeAcc (s := s) hc).2.down = [c] :=
  pathOf_of _ hc

/-- ⭐**A declared address kept along an edge** is indexed by its kept positions' images. -/
theorem keepSh_shOf (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} {c : ℕ}
    (hc : t.1 = c :: s.1) {u : VarSymb} {U : VarType} (hd : DeclAt s u U)
    (hk : U.keepable = true) :
    keepSh (edgeAcc hc) U (cEnv s u U) =
      shOf t U fun π => gLab t (entIdx (fmapL hF M₀ t.1 (.step u .keep)) π) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨i, hi⟩ := id hd
  have hu := (reach_ppath hi).1
  obtain ⟨tn, hb⟩ := t
  change tn = c :: s.1 at hc
  subst hc
  rw [cEnv_decl hT hM₀ hd, annSh_eta hko]
  cases U with
  | VTypeDia A =>
      change (shOf s _ _).map _ = _
      rw [shOf_map]
      refine shOf_congr hT _ _ _ fun π X hπ => ?_
      have hπ' : Step.walkTy (.VTypeDia A) (.keep :: π) = some (.VTypeDia X) :=
        (walkTy_keep rfl π).trans hπ
      rw [keepAlong_eq hT hM₀, gKA_gLab hT hM₀ ⟨hu, _, X, hd, hπ'⟩ (noProjHead_of_dia hπ),
        gMem_path (pathOf_edge rfl) _ rfl]
      obtain ⟨w, q', h₁, h₂, hw, hl⟩ := edge_point hT hM₀ hb hd hπ'
      rw [h₁, gMem_tr s _ c [] rfl hu hw h₂ hl, gMem_kept_nil _ _ _ hw]
  | VTypeBox A =>
      change Shp.box (Arrows.transposeShp (F := garrows hF M₀) (Root := fun _ => VarSymb)
        fun b => unT (accTrans (edgeAcc (s := s) (t := ⟨c :: s.1, hb⟩) rfl) b) (shOf s A fun π =>
          gLab s (u.ext (.keep :: .here :: π)))) = Shp.box _
      simp only [unT_shOf]
      rw [transpose_shOf]
      congr 1
      refine shOf_congr hT _ _ _ fun π X hπ => ?_
      have hπ' : Step.walkTy (.VTypeBox A) (.keep :: .here :: π) = some (.VTypeDia X) := by
        rw [walkTy_keep rfl, walkTy_here hT]
        exact hπ
      obtain ⟨w, q', -, h₂, hw, hl⟩ := edge_point hT hM₀ hb hd hπ'
      rw [h₂, gLab_keep _ hw]
      congr 1
      funext b
      rw [show u.ext (.keep :: .here :: π) = (VarSymb.step u .keep).ext (.here :: π) from rfl,
        gLab_keep _ hu]
      change gMem s b.1 (pathOf (gtrans (edgeAcc (s := s) (t := ⟨c :: s.1, hb⟩) rfl).2.down
        b.2.down)) _ _ = _
      have hp : pathOf (gtrans (edgeAcc (s := s) (t := ⟨c :: s.1, hb⟩) rfl).2.down b.2.down) =
          c :: pathOf b.2.down := by
        rw [pathOf_trans (edgeAcc (s := s) (t := ⟨c :: s.1, hb⟩) rfl).2.down b.2.down,
          pathOf_edge (s := s) (t := (⟨c :: s.1, hb⟩ : GW hF M₀)) (c := c) rfl]
        rfl
      rw [gMem_path hp _ (pathOf_eq b.2.down),
        gMem_tr s b.1 c _ _ hu hw h₂ hl]
      rfl
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd _ _ => cases hk

/-- ⭐**A view's items kept into `□`** have the address shapes of their kept addresses. -/
theorem itemsTm_shp (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {t : GW hF M₀}
    {l : List VarType} {j : ℕ} (hl : (ctxOf l).Le (ctxOf (glat t j))) :
    ∀ (L : List (VarSymb × VarType)) (hL : ∀ e ∈ L, (ctxOf l).boxIn.ref e.1 = some e.2),
      (∀ e ∈ L, ∃ w, e.1 = .step w .keep ∧ (ctxOf l).ref w = some e.2 ∧ e.2.keepable = true) →
      Model.termShp (((famEnv cEnv (ctxOf l) t)).boxPush 0) 1 (itemsTm (σ := σ) L hL).2 =
        shOf t (itemsTy L) fun π => gLab t ((itemsAnnF L id).idxAt π)
  | [], _, _ => rfl
  | e :: L, hL, hK => by
      have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      obtain ⟨w, hw₁, hw₂, hw₃⟩ := hK e List.mem_cons_self
      change Shp.prod (Model.termShp _ 1 (Term.eta e.1 e.2 _))
        (Model.termShp _ 1 (itemsTm (σ := σ) L _).2) = Shp.prod _ _
      rw [Model.termShp_eta,
        itemsTm_shp hT hM₀ hl L _ fun e' he' => hK e' (List.mem_cons_of_mem _ he')]
      refine congrArg₂ Shp.prod ?_ rfl
      obtain ⟨e₁, e₂⟩ := e
      change e₁ = .step w .keep at hw₁
      subst hw₁
      dsimp only
      rw [Model.ShEnv.ref_nonproj _ _ (by decide)]
      change (GFunc.shp (σ := σ) (GFunc.keep hF _) 0
        ((famEnv cEnv (ctxOf l) t).ref 0 w _)).inner = _
      rw [cEnv_ref hT hM₀ hl, boxPush_cEnv hT hM₀ ⟨j, hl.ref hw₂⟩ hw₃, annSh_eta hko]
      refine shOf_congr hT _ _ _ fun π X hπ => ?_
      change gLab t ((VarSymb.step w .keep).ext π) = gLab t ((Ann.eta _ e₂).idxAt π)
      rw [Ann.idxAt_eta π _ e₂ X hπ]
      rfl

/-- ⭐**An edge's entry for a declared address's kept item** is indexed by the entry's indices. -/
theorem entry_shOf (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) {t : GW hF M₀} {j : ℕ}
    {u : VarSymb} {U : VarType} (hk : U.keepable = true)
    (hx : (entOf (ctxOf (glat t j)) (fmapL hF M₀ t.1 (.step u .keep))).OkRef U) :
    Model.entryShp (famEnv cEnv (ctxOf (glat t j)) t) 0
        (entOf (ctxOf (glat t j)) (fmapL hF M₀ t.1 (.step u .keep))) hx =
      shOf t U fun π => gLab t (entIdx (fmapL hF M₀ t.1 (.step u .keep)) π) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  set Δ := ctxOf (glat t j)
  suffices key : ∀ (x : LEnt σ), fmapL hF M₀ t.1 (.step u .keep) = x →
      ∀ (hx : (entOf Δ x).OkRef U), Model.entryShp (famEnv cEnv Δ t) 0 (entOf Δ x) hx =
        shOf t U fun π => gLab t (entIdx x π) from key _ rfl hx
  intro x hfm hx
  cases x with
  | inl y =>
      change (famEnv cEnv Δ t).ref 0 y hx = _
      rw [cEnv_ref hT hM₀ (Ctx.Le.refl _), cEnv_decl hT hM₀ ⟨j, hx⟩, annSh_eta hko]
      rfl
  | inr τ =>
      obtain ⟨e₀, hsuf, hadm, -, -, hτ⟩ := fmapL_adm hfm
      obtain ⟨L, T₀, a₀, t₀⟩ := τ
      have hle : (ctxOf L).Le Δ := by
        by_contra hn
        rw [show entOf Δ (.inr ⟨L, T₀, a₀, t₀⟩) = .hide from dif_neg hn] at hx
        exact hx
      have he : entOf Δ (.inr ⟨L, T₀, a₀, t₀⟩) = .tm (Term.mono hle t₀) := dif_pos hle
      have hx₂ : (SubE.tm (Term.mono hle t₀) : SubE σ Δ).OkRef U := he ▸ hx
      rw [Model.entryShp_congr _ 0 he hx hx₂]
      have hTU : T₀ = U := hx₂
      subst hTU
      change Model.termShp _ 0 (Term.mono hle t₀) = _
      rw [Model.termShp_mono (Γ := ctxOf L) (Γ' := Δ) (h := hle) (ρ := famEnv cEnv (ctxOf L) t)
        (ρ' := famEnv cEnv Δ t) (fun _ _ _ => rfl) 0]
      obtain ⟨l', T', a', t'⟩ := e₀
      have h₂ := eq_of_heq (Sigma.mk.inj hτ).2
      obtain ⟨rfl, h₃⟩ := Sigma.mk.inj h₂
      obtain ⟨rfl, h₄⟩ := Sigma.mk.inj (eq_of_heq h₃)
      have hsl : (ctxOf l').Le (ctxOf L) := ctxOf_le_of_suffix hsuf
      rw [eq_of_heq h₄, Model.termShp_mono (h := hsl) (ρ := famEnv cEnv (ctxOf l') t)
        (ρ' := famEnv cEnv (ctxOf L) t) (fun _ _ _ => rfl) 0]
      have hl' : (ctxOf l').Le Δ := hsl.trans hle
      simp only [entIdx]
      rcases LiftAdm.of_T hF hT hadm with hbt | ⟨z, Z, hz, he₀⟩ | ⟨-, z, Z, hz, he₀⟩
      · -- the `□` view tuple
        change (⟨l', _, _, t'⟩ : LTerm σ) = boxTuple hF l' at hbt
        unfold boxTuple at hbt
        obtain ⟨rfl, h₅⟩ := Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hbt).2)
        obtain ⟨rfl, h₆⟩ := Sigma.mk.inj (eq_of_heq h₅)
        rw [eq_of_heq h₆]
        change Shp.box (Model.termShp _ 1 _) = _
        rw [itemsTm_shp hT hM₀ hl' _ _ (boxItems_kept hko l')]
        change Shp.box _ = Shp.box _
        congr 1
        refine shOf_congr hT _ _ _ fun π X hπ => ?_
        obtain ⟨k, hkl, r, rfl, hr⟩ := items_walk _ π X hπ
        obtain ⟨w, hw₁, -, -⟩ := boxItems_kept hko l' _ (List.getElem_mem hkl)
        rw [show Ann.box (itemsTm (σ := σ) (boxItems l') (boxItems_ref hF l')).1 =
          BTann id (boxItems l') by rw [itemsTm_ann]; rfl]
        dsimp only
        rw [bt_keep, bt_item _ _ k hkl r hr, items_idxAt _ _ k hkl, Ann.idxAt_eta r _ _ X hr]
        simp only [id]
        rw [hw₁, VarSymb.shift_level_zero (by decide), collapse_kept]
      · -- an η-lift
        change (⟨l', _, _, t'⟩ : LTerm σ) = etaTerm l' z Z hz at he₀
        unfold etaTerm at he₀
        obtain ⟨rfl, h₅⟩ := Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he₀).2)
        obtain ⟨rfl, h₆⟩ := Sigma.mk.inj (eq_of_heq h₅)
        rw [eq_of_heq h₆, Model.termShp_eta, cEnv_ref hT hM₀ hl', cEnv_decl hT hM₀ ⟨_, hl'.ref hz⟩,
          annSh_eta hko]
        exact shOf_congr hT _ _ _ fun π X hπ => by rw [Ann.idxAt_eta π z _ X hπ]
      · -- a view tuple
        change (⟨l', _, _, t'⟩ : LTerm σ) = viewTuple hF l' z Z hz at he₀
        unfold viewTuple at he₀
        obtain ⟨rfl, h₅⟩ := Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he₀).2)
        obtain ⟨rfl, h₆⟩ := Sigma.mk.inj (eq_of_heq h₅)
        rw [eq_of_heq h₆, Model.termShp_diatm _ 0 hz]
        have hd : DeclAt t z (.VTypeDia Z) := ⟨_, hl'.ref hz⟩
        have hag : Model.ShEnv.Agree (Ctx.le_boxIn_diaIn (ctxOf l') z)
            ((famEnv cEnv (ctxOf l') t).boxPush 0) ((famEnv cEnv (ctxOf l') t).diaPush 0 z hz) :=
          fun v T hv => by
            match v, hv with
            | .step u .keep, _ => rfl
            | .step u .box, _ => rfl
            | .root _, hv => cases hv
            | .step _ .fst, hv => cases hv
            | .step _ .snd, hv => cases hv
            | .step _ .dia, hv => cases hv
            | .step _ .here, hv => cases hv
        change Shp.dia _ (Shp.prod (Model.termShp _ 1 (Term.eta _ Z _))
          (Model.termShp _ 1 (Term.mono _ _))) = _
        rw [Model.termShp_eta, Model.termShp_mono hag 1,
          itemsTm_shp hT hM₀ hl' _ _ (boxItems_kept hko l'),
          Model.ShEnv.ref_nonproj _ _ (by decide)]
        change Shp.dia ((famEnv cEnv (ctxOf l') t).ref 0 z hz).label
          (Shp.prod ((famEnv cEnv (ctxOf l') t).ref 0 z hz).body _) = _
        rw [cEnv_ref hT hM₀ hl', cEnv_decl hT hM₀ hd]
        change Shp.dia (gLab t z) (Shp.prod (annSh t (Ann.eta (.step z .dia) Z)) _) =
          Shp.dia _ (Shp.prod _ _)
        rw [annSh_eta hko]
        refine congrArg₂ Shp.dia rfl (congrArg₂ Shp.prod ?_ ?_)
        · exact shOf_congr hT _ _ _ fun π X hπ => by
            change _ = gLab t ((Ann.eta (.step z .dia) Z).idxAt π)
            rw [Ann.idxAt_eta π _ Z X hπ]
        · change _ = shOf t _ fun π =>
            gLab t ((itemsTm (σ := σ) (boxItems l') (boxItems_ref hF l')).1.idxAt π)
          rw [itemsTm_ann]

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
  rw [Model.entryShp_congr _ 0 hθ hok (hθ ▸ hok), entry_shOf hT hM₀ hk,
    keepSh_shOf hT hM₀ hc ⟨i, hu⟩ hk]

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

/-- ⭐**(C2)/(RC) at a kept item**: a keepable address's kept item, translated along a path, has
    the address's shape kept along the path's arrow — a possible address's labels restricted, a
    necessary address's family reindexed. -/
theorem termShp_pTr_keep (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (P : List ℕ)
    (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ) {u : VarSymb}
    {U : VarType} (hu : (ctxOf (glat s i)).ref u = some U) (hk : U.keepable = true) :
    Model.termShp (famEnv cEnv (ctxOf (glat t (pstg s t P h i))) t) 0
        (pTr hM₀ s t P h hP i (Term.eta (.step u .keep) U (Ctx.ref_keep_of' hF hu hk))).2 =
      keepSh ⟨t, ⟨⟨P, hP, h⟩⟩⟩ U (cEnv s u U) := by
  rw [termShp_pTr hT hM₀, Model.termShp_eta, Model.ShEnv.ref_nonproj _ _ (by decide)]
  rw [boxPush_keep hT hM₀ hk (item_keep hF hu hk), unT_keep _ hk _ (cEnv_wf s u U)]

/-- ⭐**The keep law for possible terms**: a possible term kept into `□` (its witness kept, its body
    shifted, `SubE.keepE_dia`) and translated along a path has the term's shape with its labels
    restricted along the path's arrow. -/
theorem termShp_pTr_keepDia (hT : ModalSys.T = true) (hM₀ : Theory.IsMCS M₀) (P : List ℕ)
    (s t : GW hF M₀) (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ) {y : VarSymb}
    (hy : ∃ X, (ctxOf (glat s i)).ref y = some (.VTypeDia X)) {A : VarType} {a : Ann A}
    (b : Term σ ((ctxOf (glat s i)).diaIn y) A a) :
    Model.termShp (famEnv cEnv (ctxOf (glat t (pstg s t P h i))) t) 0
        (pTr hM₀ s t P h hP i (Term.diatm (.step y .keep) (Ctx.exists_keep_dia hF hy)
          (Term.shift (Ctx.shifts_diaIn_keep hF _ y) b))).2 =
      (Model.termShp (famEnv cEnv (ctxOf (glat s i)) s) 0 (Term.diatm y hy b)).map
        (Arrows.Leaf.keepAlong (F := garrows hF M₀) (Root := fun _ => VarSymb) hF
          ⟨t, ⟨⟨P, hP, h⟩⟩⟩) := by
  rw [termShp_pTr hT hM₀, ← unT_dkeep (σ := σ) ⟨t, ⟨⟨P, hP, h⟩⟩⟩]
  congr 1
  have hk := Model.entryShp_keepE_dia (lw := []) (famEnv cEnv (ctxOf (glat s i)) s)
    (famEnv_wf (fun t v T => cEnv_wf t v T) _ s) hF (e := .tm (Term.diatm y hy b)) rfl
  rw [Model.entryShp_congr _ _ (SubE.keepE_dia y hy b hF) _ rfl] at hk
  exact hk

end GArrow

end V12M
