import QML.QML_v12m_GCluLabel

/-!
# QML v12m — 5 on the growing tree: the cluster's shapes

Under T possible objects carry shapes.  The cluster stores a term's shape at the root, computed
symbolically (`Model.termShp`) from the root's address shapes (`annC`, `cE`).

* `annC`: an annotation's shape, each `◇`-node labelled by its index's label (`cLab`);
* ⭐`CPushed.ref`: the root's environment pushed into views reads every reachable address as its
  address shape, by the label edit laws of `GCluLabel`;
* ⭐`cLab_inj`: labels are injective on addresses of one level.  Keep-first addresses are compared
  along a late edge (`glate`): a lifted root can name another address's value along an edge, so
  not every edge separates them;
* ⭐`ann_eq_of_termShpC`: tags determine annotations, at the root.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Shapes indexed by positions -/

/-- A shape of a type, its leaf at each spelled position given by `L` (a `□` is entered by
    `keep.here`). -/
noncomputable def cShOf (g : GW hF M₀) : (T : VarType) → (List Step → CLeaf hF M₀ g) →
    CShape hF M₀ g T
  | .Var, _ => .var
  | .VTypeOne, _ => .one
  | .VTypeProd A C, L => .prod (cShOf g A fun π => L (.fst :: π)) (cShOf g C fun π => L (.snd :: π))
  | .VTypeBox A, L => .box (cShOf g A fun π => L (.keep :: .here :: π))
  | .VTypeDia A, L => .dia (L []) (cShOf g A fun π => L (.dia :: π))

theorem cShOf_congr (hT : ModalSys.T = true) {g : GW hF M₀} :
    ∀ (T : VarType) (L L' : List Step → CLeaf hF M₀ g),
      (∀ π X, Step.walkTy T π = some (.VTypeDia X) → L π = L' π) → cShOf g T L = cShOf g T L'
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, L, L', h => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [cShOf_congr hT A _ _ fun π X hπ => h (.fst :: π) X hπ,
        cShOf_congr hT C _ _ fun π X hπ => h (.snd :: π) X hπ]
  | .VTypeBox A, L, L', h => by
      change Shp.box _ = Shp.box _
      rw [cShOf_congr hT A _ _ fun π X hπ => h (.keep :: .here :: π) X
        (by rw [walkTy_keep rfl, walkTy_here hT]; exact hπ)]
  | .VTypeDia A, L, L', h => by
      change Shp.dia _ _ = Shp.dia _ _
      rw [h [] A rfl, cShOf_congr hT A _ _ fun π X hπ => h (.dia :: π) X hπ]

theorem cShOf_map {g g' : GW hF M₀} (m : CLeaf hF M₀ g → CLeaf hF M₀ g') :
    ∀ (T : VarType) (L : List Step → CLeaf hF M₀ g),
      (cShOf g T L).map m = cShOf g' T fun π => m (L π)
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, L => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [cShOf_map m A, cShOf_map m C]
  | .VTypeBox A, L => by
      change Shp.box _ = Shp.box _
      rw [cShOf_map m A]
  | .VTypeDia A, L => by
      change Shp.dia _ _ = Shp.dia _ _
      rw [cShOf_map m A]

/-- ⭐**The shape of an annotation**: its tree, each `◇`-node labelled by its index's label. -/
noncomputable def annC (g : GW hF M₀) : {T : VarType} → Ann T → CShape hF M₀ g T
  | _, .var => .var
  | _, .one => .one
  | _, .prod a b => .prod (annC g a) (annC g b)
  | _, .box a => .box (annC g a)
  | _, .dia i a => .dia (cLab i g) (annC g a)

/-- An address shape is indexed by the address's positions (T + 4). -/
theorem annC_eta (hko : ModalSys.keepOnly = true) {g : GW hF M₀} :
    ∀ (T : VarType) (w : VarSymb), annC g (Ann.eta w T) = cShOf g T fun π => cLab (w.ext π) g
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, w => by
      change Shp.prod (annC g (Ann.eta (.step w .fst) A)) (annC g (Ann.eta (.step w .snd) C)) = _
      rw [annC_eta hko A, annC_eta hko C]
      rfl
  | .VTypeBox A, w => by
      change Shp.box (annC g (Ann.eta w.inner A)) = _
      rw [VarSymb.inner_keepOnly hko, annC_eta hko A]
      rfl
  | .VTypeDia A, w => by
      change Shp.dia (cLab w g) (annC g (Ann.eta (.step w .dia) A)) = _
      rw [annC_eta hko A]
      rfl

/-! ## Addresses of a level -/

/-- `y` is a position of an address declared at `g`, at `j` levels and of type `T`. -/
def CFormAt (g : GW hF M₀) (j : ℕ) (y : VarSymb) (T : VarType) : Prop :=
  ∃ (v : VarSymb) (U : VarType) (π : List Step), DeclAt g v U ∧ PPath v.path ∧
    y = v.ext π ∧ Step.walkTy U π = some T ∧ Step.levels π = j

/-- `y` is a position of a declared root address, at `j` levels and of type `T`. -/
abbrev CForm (j : ℕ) (y : VarSymb) (T : VarType) : Prop := CFormAt (groot hF M₀) j y T

theorem CFormAt.proj {g : GW hF M₀} {j : ℕ} {y : VarSymb} {U T : VarType}
    (h : CFormAt g j y U) {st : Step} (hs : st.isProj = true) (hst : U.step st = some T) :
    CFormAt g j (.step y st) T := by
  obtain ⟨v, U₀, π, hd, hv, rfl, hw, hn⟩ := h
  refine ⟨v, U₀, π ++ [st], hd, hv, (VarSymb.ext_append_single v π st).symm, ?_, ?_⟩
  · rw [Step.walkTy_append, hw, Option.bind_some]
    cases st with
    | fst => exact Option.bind_eq_some_iff.mpr ⟨T, hst, rfl⟩
    | snd => exact Option.bind_eq_some_iff.mpr ⟨T, hst, rfl⟩
    | here => exact Option.bind_eq_some_iff.mpr ⟨T, hst, rfl⟩
    | box => cases hs
    | dia => cases hs
    | keep => cases hs
  · rw [Step.levels_append, hn]
    simp [Step.levels, hs]

theorem CFormAt.keep {g : GW hF M₀} {j : ℕ} {y : VarSymb} {U : VarType} (h : CFormAt g j y U)
    (hk : U.keepable = true) : CFormAt g (j + 1) (.step y .keep) U := by
  obtain ⟨v, U₀, π, hd, hv, rfl, hw, hn⟩ := h
  refine ⟨v, U₀, π ++ [.keep], hd, hv, (VarSymb.ext_append_single v π _).symm, ?_, ?_⟩
  · rw [Step.walkTy_append, hw, Option.bind_some, walkTy_keep hk]
    rfl
  · rw [Step.levels_append, hn]
    simp [Step.levels, Step.isProj]

theorem CFormAt.dia {g : GW hF M₀} {j : ℕ} {y : VarSymb} {X : VarType}
    (h : CFormAt g j y (.VTypeDia X)) : CFormAt g (j + 1) (.step y .dia) X := by
  obtain ⟨v, U₀, π, hd, hv, rfl, hw, hn⟩ := h
  refine ⟨v, U₀, π ++ [.dia], hd, hv, (VarSymb.ext_append_single v π _).symm, ?_, ?_⟩
  · rw [Step.walkTy_append, hw, Option.bind_some]
    rfl
  · rw [Step.levels_append, hn]
    simp [Step.levels, Step.isProj]

/-! ## The root's addresses under keeping and projecting -/

section Root

variable (hV : ModalSys.Five = true) (hS : ModalSys.fourL = true)
  (hW : ModalSys.fourLW = true) (hM₀ : Theory.IsMCS M₀) (hT : ModalSys.T = true)

/-- At the root, a world's address reading is the address. -/
theorem rorig_root : rorig (groot hF M₀) = id := rfl

/-- The root's own addresses are read as they are. -/
theorem preIx_root (z : VarSymb) : preIx (groot hF M₀) z = z := by
  by_cases h0 : Step.levels z.path = 0
  · have hz := ppath_of_levels0 h0
    rw [preIx_ppath _ hz]
    rfl
  · obtain ⟨q, st, r, hq, hq₀, hst⟩ := split_first z.path (by omega)
    have e : z = (VarSymb.step ((VarSymb.root z.rt).ext q) st).ext r := by
      conv_lhs => rw [VarSymb.eq_root_ext z, hq, VarSymb.ext_append]
      rfl
    have hp : PPath ((VarSymb.root z.rt).ext q).path := by
      rw [VarSymb.ext_path]
      simpa [VarSymb.path] using hq₀
    rw [e, preIx_lvl _ hp hst]
    rfl

theorem cNext_root (v : VarSymb) (r : List Step) : cNext (groot hF M₀) v r = v.ext r :=
  preIx_root _

include hV hS hW hM₀ hT in
/-- ⭐**An address's shape kept** at its level is the kept address's shape. -/
theorem keep_annC {j : ℕ} {y : VarSymb} {U : VarType} {g : GW hF M₀}
    (hf : CForm (hF := hF) (M₀ := M₀) j y U) (hF' : ModalSys.Four = true)
    (hk : U.keepable = true) :
    (GFunc.shp (σ := σ) (GFunc.keep hF' hk) j (annC g (Ann.eta y U))).inner =
      annC g (Ann.eta (.step y .keep) U) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨v, U₀, π, hd, hv, rfl, hw, hn⟩ := hf
  cases U with
  | VTypeDia A =>
      change Shp.dia (Arrows.Leaf.dk hF' j (cLab (v.ext π) _))
        ((annC _ (Ann.eta (.step (v.ext π) .dia) A)).map (Arrows.Leaf.dkB hF' j)) =
        Shp.dia (cLab (.step (v.ext π) .keep) _)
          (annC _ (Ann.eta (.step (.step (v.ext π) .keep) .dia) A))
      rw [annC_eta hko, annC_eta hko, cShOf_map,
        cLab_dk hV hS hW hM₀ hT j hd hv hw hn, VarSymb.ext_append_single]
      refine congrArg _ (cShOf_congr hT A _ _ fun π' X hπ => ?_)
      have := cLab_dkB hV hS hW hM₀ hT hπ j hd hv hw hn g
      rw [VarSymb.ext_append, VarSymb.ext_append] at this
      exact this
  | VTypeBox A =>
      change Shp.box ((annC _ (Ann.eta (v.ext π).inner A)).map (Arrows.Leaf.shift hF' j)) =
        Shp.box (annC _ (Ann.eta (VarSymb.step (v.ext π) .keep).inner A))
      rw [annC_eta hko, annC_eta hko, cShOf_map]
      refine congrArg _ (cShOf_congr hT A _ _ fun π' X hπ => ?_)
      have := cLab_shift hV hS hW hM₀ hT hπ j hd hv hw hn g
      rw [VarSymb.ext_append, VarSymb.ext_append] at this
      rw [VarSymb.inner_keepOnly hko, VarSymb.inner_keepOnly hko]
      exact this
  | Var => cases hk
  | VTypeOne => cases hk
  | VTypeProd _ _ => cases hk

include hV hS hW hM₀ hT in
/-- A projection of an address's shape is the projection's shape, below the first level at any
    anchor: at the first level a `here` reads the anchor's own arrow. -/
theorem proj_annC {j : ℕ} {y : VarSymb} {U T : VarType} {g : GW hF M₀}
    (h0 : j = 0 → g = groot hF M₀)
    (hf : CForm (hF := hF) (M₀ := M₀) j y U) {st : Step} (hs : st.isProj = true)
    (h : U.step st = some T) :
    GFunc.shp (GFunc.proj (σ := σ) hs h) j (annC g (Ann.eta y U)) =
      annC g (Ann.eta (.step y st) T) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  cases U <;> cases st <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · rename_i X
    obtain ⟨hT', rfl⟩ := VarType.step_here h
    change (annC _ (Ann.eta y.inner X)).map (Arrows.Leaf.collapse hT' j) = _
    rw [annC_eta hko, annC_eta hko, cShOf_map]
    refine cShOf_congr hT _ _ _ fun π' Y hπ => ?_
    obtain ⟨v, U₀, π, hd, hv, rfl, hw, hn⟩ := hf
    rw [VarSymb.inner_keepOnly hko,
      show ((VarSymb.step (v.ext π) .keep).step .here).ext π' =
        (v.ext π).ext (.keep :: .here :: π') from rfl,
      show (VarSymb.step (v.ext π) .here).ext π' = (v.ext π).ext (.here :: π') from rfl]
    cases j with
    | zero =>
        obtain rfl := h0 rfl
        have hπ₀ := ppath_of_levels0 hn
        rw [cLab_collapse_zero hV hS hW hM₀ hT' hπ (declAt_ext hd hπ₀ hw) (ppath_ext hv hπ₀),
          cNext_root]
    | succ n =>
        have := cLab_collapse hV hS hW hM₀ hT' hπ n hd hv hw hn g
        rwa [VarSymb.ext_append, VarSymb.ext_append] at this

end Root

/-! ## The root's environment, pushed -/

variable (hF M₀) in
/-- ⭐**The root's shape environment**: every address has its address shape. -/
noncomputable abbrev cE (Γ : Ctx) :
    Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Γ (groot hF M₀) :=
  fun v T _ => annC _ (Ann.eta v T)

variable (hF M₀) in
/-- The root's environment at a stage, pushed into views. -/
inductive CPushed (i : ℕ) :
    (Δ : Ctx) → Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀) → ℕ → Prop
  | base : CPushed i (ctxOf (glat (groot hF M₀) i)) (cE hF M₀ _) 0
  | box {Δ : Ctx} {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀)} {j : ℕ} :
      CPushed i Δ τ j → CPushed i Δ.boxIn (τ.boxPush j) (j + 1)
  | dia {Δ : Ctx} {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀)} {j : ℕ}
      {x : VarSymb} {X : VarType} (hx : Δ.ref x = some (.VTypeDia X)) :
      CPushed i Δ τ j → CPushed i (Δ.diaIn x) (τ.diaPush j x hx) (j + 1)

/-- A pushed environment reads every reachable address as a position of a declared root address,
    at its address shape. -/
def CInv {Δ : Ctx} (τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀))
    (j : ℕ) : Prop :=
  ∀ (y : VarSymb) {T : VarType} (h : Δ.ref y = some T),
    CForm (hF := hF) (M₀ := M₀) j y T ∧ τ.ref j y h = annC _ (Ann.eta y T)

section Pushed

variable (hV : ModalSys.Five = true) (hS : ModalSys.fourL = true)
  (hW : ModalSys.fourLW = true) (hM₀ : Theory.IsMCS M₀) (hT : ModalSys.T = true)

include hV hS hW hM₀ hT in
/-- What holds of a context's declared addresses holds of its reachable ones. -/
theorem cInv_of_items {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀)} {j : ℕ}
    (hitem : ∀ (v : VarSymb) (T : VarType) (h : Δ v = some T),
      CForm (hF := hF) (M₀ := M₀) j v T ∧ τ v T h = annC _ (Ann.eta v T)) : CInv τ j
  | .root r, T, h => by
      have h' : Δ (.root r) = some T := by rwa [Ctx.ref_nonproj _ rfl] at h
      exact hitem _ T h'
  | .step v st, T, h => by
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Δ.ref v = some U := by
          rw [Ctx.ref_step_proj _ v hs] at h
          cases hU : Δ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        have hst : U.step st = some T := by
          rw [Ctx.ref_step_proj _ v hs, hU] at h
          exact h
        obtain ⟨hf, he⟩ := cInv_of_items hitem v hU
        refine ⟨hf.proj hs hst, ?_⟩
        rw [Model.ShEnv.ref_proj _ j hs hU h, he]
        exact proj_annC hV hS hW hM₀ hT (fun _ => rfl) hf hs _
      · have h' : Δ (.step v st) = some T := by rwa [Ctx.ref_step_nonproj _ v hs] at h
        rw [Model.ShEnv.ref_nonproj _ j hs h]
        exact hitem _ T h'

include hV hS hW hM₀ hT in
/-- Pushing into `□` keeps the invariant at its items. -/
theorem cInv_box_item {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀)} {j : ℕ}
    (hI : CInv τ j) (v : VarSymb) (T : VarType) (h : Δ.boxIn v = some T) :
    CForm (hF := hF) (M₀ := M₀) (j + 1) v T ∧ τ.boxPush j v T h = annC _ (Ann.eta v T) := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  match v, h with
  | .step u .keep, h =>
      obtain ⟨hF', hu, hk⟩ := Ctx.boxIn_keep h
      obtain ⟨hf, he⟩ := hI u hu
      refine ⟨hf.keep hk, ?_⟩
      change (GFunc.shp (GFunc.keep hF' hk) j (τ.ref j u hu)).inner = _
      rw [he]
      exact keep_annC hV hS hW hM₀ hT hf hF' hk
  | .step u .box, h =>
      have := (Ctx.boxIn_box h).1
      rw [hko] at this
      cases this
  | .root _, h => cases h
  | .step _ .fst, h => cases h
  | .step _ .snd, h => cases h
  | .step _ .dia, h => cases h
  | .step _ .here, h => cases h

include hV hS hW hM₀ hT in
/-- ⭐**A pushed environment reads every reachable address as its address shape.** -/
theorem CPushed.ref {i : ℕ} {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀)} {j : ℕ}
    (hP : CPushed hF M₀ i Δ τ j) : CInv τ j := by
  induction hP with
  | base =>
      refine cInv_of_items hV hS hW hM₀ hT fun v T h => ?_
      obtain ⟨r, rfl⟩ := ctxOf_decl h
      exact ⟨⟨.root (.free r), T, [], ⟨i, by rw [Ctx.ref_nonproj _ rfl]; exact h⟩, ppath_nil,
        rfl, rfl, rfl⟩, rfl⟩
  | @box Δ τ j _ ih =>
      exact cInv_of_items hV hS hW hM₀ hT fun v T h =>
        cInv_box_item hV hS hW hM₀ hT ih v T h
  | @dia Δ τ j x X hx _ ih =>
      refine cInv_of_items hV hS hW hM₀ hT fun v T h => ?_
      by_cases hvx : v = .step x .dia
      · subst hvx
        obtain rfl := Ctx.diaIn_step_dia hx h
        obtain ⟨hf, he⟩ := ih x hx
        refine ⟨hf.dia, ?_⟩
        change (τ.ref j x hx).body = _
        rw [he]
        rfl
      · match v, h, hvx with
        | .step u .keep, h, _ =>
            have h' : Δ.boxIn (.step u .keep) = some T := h
            exact cInv_box_item hV hS hW hM₀ hT ih _ T h'
        | .step u .box, h, _ =>
            have h' : Δ.boxIn (.step u .box) = some T := h
            exact cInv_box_item hV hS hW hM₀ hT ih _ T h'
        | .step u .dia, h, hvx =>
            change (if u = x then _ else none) = some T at h
            split_ifs at h with hux
            exact absurd (by rw [hux]) hvx
        | .root _, h, _ => cases h
        | .step _ .fst, h, _ => cases h
        | .step _ .snd, h, _ => cases h
        | .step _ .here, h, _ => cases h

end Pushed

/-! ## Labels are injective -/

/-- A root's address, read at a world: the inverse of `preIx`, its name before its first level
    step, the rest kept. -/
noncomputable def postIx (s : GW hF M₀) (y : VarSymb) : VarSymb :=
  match splitLevel y.path with
  | some (q, st, r) => (VarSymb.step (rnm s ((VarSymb.root y.rt).ext q)) st).ext r
  | none => rnm s y

theorem postIx_ppath (s : GW hF M₀) {y : VarSymb} (hy : PPath y.path) : postIx s y = rnm s y := by
  unfold postIx
  rw [splitLevel_ppath_none hy]

theorem postIx_lvl (s : GW hF M₀) {y : VarSymb} (hy : PPath y.path) {st : Step}
    (hs : st.isProj = false) (r : List Step) :
    postIx s ((VarSymb.step y st).ext r) = (VarSymb.step (rnm s y) st).ext r := by
  unfold postIx
  rw [show ((VarSymb.step y st).ext r).path = y.path ++ st :: r by
      rw [VarSymb.ext_path]
      change (y.path ++ [st]) ++ r = _
      simp,
    splitLevel_ppath hy hs]
  simp only [VarSymb.ext_rt]
  rw [show (VarSymb.step y st).rt = y.rt from rfl, VarSymb.root_ext_path]

section Inj

variable (hV : ModalSys.Five = true) (hS : ModalSys.fourL = true)
  (hW : ModalSys.fourLW = true) (hM₀ : Theory.IsMCS M₀) (hT : ModalSys.T = true)

include hF hV hS hW hM₀ hT in
/-- ⭐**`cNext` remembers the address it read at the world**: `postIx` undoes it. -/
theorem postIx_cNext (b : GW hF M₀) {v : VarSymb} {U : VarType}
    (hd : DeclAt (groot hF M₀) v U) (hk : U.keepable = true) {r : List Step} {A : VarType}
    (hw : Step.walkTy U r = some (.VTypeDia A)) :
    postIx b (cNext b v r) = (rnm b v).ext r := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  obtain ⟨j, hj⟩ := id (declAt_rnm hV hM₀ b hd hk)
  have hpz := (reach_ppath hj).1
  by_cases h0 : Step.levels r = 0
  · have hr := ppath_of_levels0 h0
    have hdz : DeclAt b ((rnm b v).ext r) (.VTypeDia A) := declAt_ext ⟨j, hj⟩ hr hw
    have hdo := declAt_rorig hV hS hW hM₀ b hdz rfl
    obtain ⟨i, hi⟩ := id hdo
    unfold cNext
    rw [preIx_ppath _ (ppath_ext hpz hr), postIx_ppath _ (reach_ppath hi).1]
    exact rnm_rorig hV hS hW hM₀ b hdz rfl rfl
  · obtain ⟨π₀, st, r', rfl, hπ₀, hst⟩ := split_first r (by omega)
    rw [Step.walkTy_append, walkTy_ppath U hπ₀] at hw
    obtain ⟨U₁, hU₁, hw₀⟩ := Option.bind_eq_some_iff.mp hw
    have hdz : DeclAt b ((rnm b v).ext π₀) U₁ :=
      declAt_ext ⟨j, hj⟩ hπ₀ ((walkTy_ppath U hπ₀).trans hU₁)
    have hkU₁ : U₁.keepable = true := by
      obtain ⟨W', hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
      cases st with
      | fst => cases hst
      | snd => cases hst
      | here => cases hst
      | box =>
          change (if ModalSys.keepOnly = true then none else U₁.step .box) = some W' at hW'
          rw [if_pos hko] at hW'
          cases hW'
      | dia =>
          cases U₁ with
          | VTypeDia _ => rfl
          | _ => cases hW'
      | keep => exact Step.typeStep_level_keepable rfl hW'
    have heU₁ : U₁.etaInj = true := etaInj_of_walkTy _ hw₀
    have hdo := declAt_rorig hV hS hW hM₀ b hdz hkU₁
    obtain ⟨i, hi⟩ := id hdo
    unfold cNext
    rw [VarSymb.ext_append,
      show ((rnm b v).ext π₀).ext (st :: r') =
        (VarSymb.step ((rnm b v).ext π₀) st).ext r' from rfl,
      preIx_lvl _ (ppath_ext hpz hπ₀) hst, postIx_lvl _ (reach_ppath hi).1 hst,
      rnm_rorig hV hS hW hM₀ b hdz hkU₁ heU₁]

omit hM₀ in
include hF hV in
/-- Along a child of the root, an address's name is what the edge's entry names. -/
theorem rnm_child {t : GW hF M₀} {c : ℕ} (hc : t.1 = c :: (groot hF M₀).1) {v z : VarSymb}
    (he : fmapL hF M₀ t.1 (.step v .keep) = .inl z) : rnm t v = z := by
  obtain ⟨k, hk⟩ := t
  change k = [c] at hc
  subst hc
  have hn := nm_spec hV (⟨[c], hk⟩ : GW hF M₀) v
  have hz : nm (⟨[c], hk⟩ : GW hF M₀) v = z := by
    rcases hn with e | ⟨L, T, hz', e⟩
    · exact Sum.inl.inj (e.symm.trans he)
    · rw [he] at e
      cases e
  exact hz

include hF hV hS hW hM₀ hT in
/-- ⭐**Labels are injective** on the positions of one level, at every anchor.  A keep-first
    address is read along a late edge, whose entries are images. -/
theorem cLab_inj (j : ℕ) : ∀ {y y' : VarSymb} {A A' : VarType},
    CForm (hF := hF) (M₀ := M₀) j y (.VTypeDia A) →
    CForm (hF := hF) (M₀ := M₀) j y' (.VTypeDia A') → ∀ g : GW hF M₀,
    cLab y g = cLab y' g → y = y' := by
  have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
  induction j with
  | zero =>
      rintro y y' A A' ⟨v, U, π, hd, hv, rfl, hw, hn⟩ ⟨v', U', π', hd', hv', rfl, hw', hn'⟩ g h
      rw [cLab_ppath (ppath_ext hv (ppath_of_levels0 hn)),
        cLab_ppath (ppath_ext hv' (ppath_of_levels0 hn'))] at h
      injection h
  | succ j IH =>
      rintro y y' A A' ⟨v, U, π, hd, hv, rfl, hw, hn⟩ ⟨v', U', π', hd', hv', rfl, hw', hn'⟩ g h
      obtain ⟨π₀, st, r, rfl, hπ₀, hst⟩ := split_first π (by omega)
      obtain ⟨π₀', st', r', rfl, hπ₀', hst'⟩ := split_first π' (by omega)
      have hlr : Step.levels r = j := by
        rw [Step.levels_append, levels_pp hπ₀, Step.levels_cons, if_neg (by simp [hst])] at hn
        omega
      have hlr' : Step.levels r' = j := by
        rw [Step.levels_append, levels_pp hπ₀', Step.levels_cons, if_neg (by simp [hst'])] at hn'
        omega
      have hpre := ppath_ext hv hπ₀
      have hpre' := ppath_ext hv' hπ₀'
      rw [Step.walkTy_append, walkTy_ppath U hπ₀] at hw
      rw [Step.walkTy_append, walkTy_ppath U' hπ₀'] at hw'
      obtain ⟨U₁, hU₁, hw₀⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨U₁', hU₁', hw₀'⟩ := Option.bind_eq_some_iff.mp hw'
      have hd₀ : DeclAt (groot hF M₀) (v.ext π₀) U₁ :=
        declAt_ext hd hπ₀ ((walkTy_ppath U hπ₀).trans hU₁)
      have hd₀' : DeclAt (groot hF M₀) (v'.ext π₀') U₁' :=
        declAt_ext hd' hπ₀' ((walkTy_ppath U' hπ₀').trans hU₁')
      have ek : v.ext (π₀ ++ st :: r) = (VarSymb.step (v.ext π₀) st).ext r := by
        rw [VarSymb.ext_append]
        rfl
      have ek' : v'.ext (π₀' ++ st' :: r') = (VarSymb.step (v'.ext π₀') st').ext r' := by
        rw [VarSymb.ext_append]
        rfl
      rw [ek, ek'] at h ⊢
      have hbox' : ∀ {W : VarType} {U₂ : VarType},
          Step.typeStep U₂ .box = some W → False := by
        intro W U₂ hW'
        change (if ModalSys.keepOnly = true then none else U₂.step .box) = some W at hW'
        rw [if_pos hko] at hW'
        cases hW'
      cases st with
      | fst => cases hst
      | snd => cases hst
      | here => cases hst
      | box =>
          obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
          exact (hbox' hW').elim
      | dia =>
          cases st' with
          | fst => cases hst'
          | snd => cases hst'
          | here => cases hst'
          | box =>
              obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀'
              exact (hbox' hW').elim
          | dia =>
              rw [cLab_dia hpre, cLab_dia hpre'] at h
              injection h with _ h₁ h₂
              injection h₂ with _ h₃
              rw [h₁, h₃]
          | keep =>
              obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀'
              have hkU₁' : U₁'.keepable = true := Step.typeStep_level_keepable rfl hW'
              have hr' : Step.walkTy U₁' r' = some (.VTypeDia A') :=
                (walkTy_keep hkU₁' r').symm.trans hw₀'
              rw [cLab_dia hpre, cLab_keep_of hV hS hW hM₀ hT hd₀' hpre' hkU₁' hr' g] at h
              cases h
      | keep =>
          obtain ⟨W, hW', -⟩ := Option.bind_eq_some_iff.mp hw₀
          have hkU₁ : U₁.keepable = true := Step.typeStep_level_keepable rfl hW'
          have hr : Step.walkTy U₁ r = some (.VTypeDia A) := (walkTy_keep hkU₁ r).symm.trans hw₀
          cases st' with
          | fst => cases hst'
          | snd => cases hst'
          | here => cases hst'
          | box =>
              obtain ⟨W', hW'', -⟩ := Option.bind_eq_some_iff.mp hw₀'
              exact (hbox' hW'').elim
          | dia =>
              rw [cLab_keep_of hV hS hW hM₀ hT hd₀ hpre hkU₁ hr g, cLab_dia hpre'] at h
              cases h
          | keep =>
              obtain ⟨W', hW'', -⟩ := Option.bind_eq_some_iff.mp hw₀'
              have hkU₁' : U₁'.keepable = true := Step.typeStep_level_keepable rfl hW''
              have hr' : Step.walkTy U₁' r' = some (.VTypeDia A') :=
                (walkTy_keep hkU₁' r').symm.trans hw₀'
              rw [cLab_keep_of hV hS hW hM₀ hT hd₀ hpre hkU₁ hr g,
                cLab_keep_of hV hS hW hM₀ hT hd₀' hpre' hkU₁' hr' g] at h
              obtain ⟨i₁, hi₁⟩ := hd₀
              obtain ⟨i₂, hi₂⟩ := hd₀'
              have hi₁' := DeclAt.at_le hM₀ hi₁ (le_max_left i₁ i₂)
              have hi₂' := DeclAt.at_le hM₀ hi₂ (le_max_right i₁ i₂)
              obtain ⟨t, c, hc, L, hsuf, hg⟩ := glate hT hM₀ (groot hF M₀) (max i₁ i₂)
              have hR : CR t := ⟨[c], .inl pathOk_cons, hc⟩
              have hm := congrFun (Arrows.Leaf.fam.inj h) ⟨t, ⟨hR⟩⟩
              beta_reduce at hm
              obtain ⟨w₁, U₂, π₂, hd₂, hv₂, hlπ₂, hw₂, hf₂⟩ :
                  CForm (hF := hF) (M₀ := M₀) j (cNext t (v.ext π₀) r) (.VTypeDia A) := by
                obtain ⟨v₁, U₃, π₃, hd₃, hv₃, hw₃, hlπ₃, -, e₃⟩ :=
                  cNext_cases hV hS hW hM₀ hT t ⟨_, hi₁⟩ hkU₁ hr rfl
                exact ⟨v₁, U₃, π₃, hd₃, hv₃, e₃, hw₃, hlπ₃.trans hlr⟩
              have hF₂ : CForm (hF := hF) (M₀ := M₀) j (cNext t (v'.ext π₀') r')
                  (.VTypeDia A') := by
                obtain ⟨v₁, U₃, π₃, hd₃, hv₃, hw₃, hlπ₃, -, e₃⟩ :=
                  cNext_cases hV hS hW hM₀ hT t ⟨_, hi₂⟩ hkU₁' hr' rfl
                exact ⟨v₁, U₃, π₃, hd₃, hv₃, e₃, hw₃, hlπ₃.trans hlr'⟩
              have e := IH ⟨w₁, U₂, π₂, hd₂, hv₂, hlπ₂, hw₂, hf₂⟩ hF₂ t hm
              have e₂ := congrArg (postIx t) e
              rw [postIx_cNext hV hS hW hM₀ hT t ⟨_, hi₁⟩ hkU₁ hr,
                postIx_cNext hV hS hW hM₀ hT t ⟨_, hi₂⟩ hkU₁' hr'] at e₂
              have hki : ∀ {u : VarSymb} {T : VarType},
                  (ctxOf (glat (groot hF M₀) (max i₁ i₂))).ref u = some T → T.keepable = true →
                  fmapL hF M₀ t.1 (.step u .keep) =
                    .inl (gchildMap L none (.step u .keep)) := fun hu hkT =>
                hg _ _ (Ctx.boxIn_keep_of' hF hu hkT)
              rw [rnm_child hV hc (hki hi₁' hkU₁), rnm_child hV hc (hki hi₂' hkU₁')] at e₂
              refine late_inj hT hF hsuf hg hi₁' hkU₁ hi₂' hkU₁' ?_
              rw [eIdx_item _ (reach_ppath hi₁').1 rfl, eIdx_item _ (reach_ppath hi₂').1 rfl,
                hki hi₁' hkU₁, hki hi₂' hkU₁']
              exact e₂

include hF hV hS hW hM₀ hT in
/-- ⭐⭐**Shapes determine annotations** in a pushed root environment. -/
theorem ann_eq_of_termShpC {i : ℕ} : ∀ {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀)} {j : ℕ},
    CPushed hF M₀ i Δ τ j → ∀ {A : VarType} {a a' : Ann A} (t : Term σ Δ A a)
      (t' : Term σ Δ A a'), Model.termShp τ j t = Model.termShp τ j t' → a = a'
  | _, _, _, _, _, _, _, .var _ _, .var _ _, _ => rfl
  | _, _, _, _, _, _, _, .var _ _, .func _, _ => rfl
  | _, _, _, _, _, _, _, .func _, .var _ _, _ => rfl
  | _, _, _, _, _, _, _, .func _, .func _, _ => rfl
  | _, _, _, _, _, _, _, .unit, .unit, _ => rfl
  | _, _, _, hP, _, _, _, .pair t₁ t₂, .pair t₁' t₂', h => by
      change Shp.prod _ _ = Shp.prod _ _ at h
      injection h with _ _ h₁ h₂
      rw [ann_eq_of_termShpC hP t₁ t₁' h₁, ann_eq_of_termShpC hP t₂ t₂' h₂]
  | _, _, _, hP, _, _, _, .boxtm u, .boxtm u', h => by
      change Shp.box _ = Shp.box _ at h
      injection h with _ h₁
      rw [ann_eq_of_termShpC hP.box u u' h₁]
  | Δ, τ, j, hP, _, _, _, .diatm x hx u, .diatm x' hx' u', h => by
      obtain ⟨X, hr⟩ := id hx
      obtain ⟨X', hr'⟩ := id hx'
      rw [Model.termShp_diatm τ j hr hx u, Model.termShp_diatm τ j hr' hx' u'] at h
      injection h with _ hl hb
      have hI := hP.ref hV hS hW hM₀ hT
      obtain ⟨hf, he⟩ := hI x hr
      obtain ⟨hf', he'⟩ := hI x' hr'
      rw [he, he'] at hl
      obtain rfl := cLab_inj hV hS hW hM₀ hT j hf hf' _ hl
      obtain rfl : X = X' := by
        rw [hr] at hr'
        injection hr' with e
        injection e
      rw [ann_eq_of_termShpC (hP.dia hr) u u' hb]

include hF hV hS hW hM₀ hT in
/-- ⭐**In a pushed root environment a term's shape is its annotation's.** -/
theorem termShp_annC {i : ℕ} : ∀ {Δ : Ctx}
    {τ : Model.ShEnv (carrows hF M₀) (fun _ => VarSymb) Δ (groot hF M₀)} {j : ℕ},
    CPushed hF M₀ i Δ τ j → ∀ {A : VarType} {a : Ann A} (t : Term σ Δ A a),
      Model.termShp τ j t = annC (groot hF M₀) a
  | _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, .unit => rfl
  | _, _, _, hP, _, _, .pair t₁ t₂ => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [termShp_annC hP t₁, termShp_annC hP t₂]
  | _, _, _, hP, _, _, .boxtm u => by
      change Shp.box _ = Shp.box _
      rw [termShp_annC hP.box u]
  | Δ, τ, j, hP, _, _, .diatm x hx u => by
      obtain ⟨X, hr⟩ := id hx
      rw [Model.termShp_diatm τ j hr hx u, termShp_annC (hP.dia hr) u,
        ((hP.ref hV hS hW hM₀ hT) x hr).2]
      rfl

include hF hV hS hW hM₀ hT in
/-- The address shape of a position of a declared root address is well-formed. -/
theorem annC_eta_wf {v : VarSymb} {U : VarType} (hd : DeclAt (groot hF M₀) v U)
    (hv : PPath v.path) (g : GW hF M₀) :
    ∀ (T : VarType) (π : List Step) (lw : List Bool), Step.walkTy U π = some T →
      Step.levels π = lw.length → (∀ j, lw[j]? = some true → lvlStep j π = some .keep) →
      Model.ShWF (F := carrows hF M₀) (Root := fun _ => VarSymb) lw
        (annC g (Ann.eta (v.ext π) T))
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
      · have := annC_eta_wf hd hv g A (π ++ [.fst]) lw
          (by rw [Step.walkTy_append, hw]; rfl) (hl' .fst rfl) (hlv .fst rfl)
        rwa [VarSymb.ext_append_single] at this
      · have := annC_eta_wf hd hv g C (π ++ [.snd]) lw
          (by rw [Step.walkTy_append, hw]; rfl) (hl' .snd rfl) (hlv .snd rfl)
        rwa [VarSymb.ext_append_single] at this
  | .VTypeBox A, π, lw, hw, hl, hk => by
      have hko : ModalSys.keepOnly = true := by simp [ModalSys.keepOnly, hT, hF]
      have := annC_eta_wf hd hv g A (π ++ [.keep, .here]) (lw ++ [true])
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
      change Model.ShWF (F := carrows hF M₀) (Root := fun _ => VarSymb) (lw ++ [true])
        (annC g (Ann.eta (v.ext π).inner A))
      rw [VarSymb.inner_keepOnly hko]
      rw [VarSymb.ext_append] at this
      exact this
  | .VTypeDia A, π, lw, hw, hl, hk => by
      refine ⟨cLab_wf hV hS hW hM₀ hT _ hd hv hw rfl hl hk g, ?_⟩
      have := annC_eta_wf hd hv g A (π ++ [.dia]) (lw ++ [false])
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

include hF hV hS hW hM₀ hT in
/-- ⭐**The root's environment is well-formed.** -/
theorem cE_wf (i : ℕ) : (cE hF M₀ (ctxOf (glat (groot hF M₀) i))).WF [] := by
  intro v T h
  obtain ⟨r, rfl⟩ := ctxOf_decl h
  have hr : (ctxOf (glat (groot hF M₀) i)).ref (.root (.free r)) = some T := by
    rw [Ctx.ref_nonproj _ rfl]
    exact h
  exact annC_eta_wf hV hS hW hM₀ hT ⟨i, hr⟩ ppath_nil _ T [] [] rfl rfl
    (fun _ hj => by simp at hj)

include hF hV hS hW hM₀ hT in
/-- ⭐**An applied map moves the annotation's shape as it moves shapes**, at the root. -/
theorem annC_applyG {R : ℕ} {B C : VarType} (g : GFunc σ B C) {b : Ann B}
    (t : Term σ (ctxOf (glat (groot hF M₀) R)) B b) :
    annC (groot hF M₀) (Canon.applyG g t).1 = GFunc.shp g 0 (annC (groot hF M₀) b) := by
  rw [← termShp_annC hV hS hW hM₀ hT (CPushed.base (i := R)) t,
    ← termShp_annC hV hS hW hM₀ hT (CPushed.base (i := R)) (Canon.applyG g t).2]
  exact Canon.termShp_applyG g t _ 0 (lw := []) rfl fun _ => cE_wf hV hS hW hM₀ hT R

end Inj

end GArrow

end V12M
