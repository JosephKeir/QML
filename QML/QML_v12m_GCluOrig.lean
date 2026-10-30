import QML.QML_v12m_GCluDia

/-!
# QML v12m — 5 on the growing tree: canonical preimages along paths

The cluster model reads every world's modal facts at the root, through preimages
(`docs/v12-modal-extensions.md` §3 5, the cluster model's R1).  `exists_pre` gives some preimage
per stage; the model needs **one**, as a function, so that denotations through it are well
defined and stage changes are weakenings.

* `orig`: one origin per child address along an edge, for every stage at once; ⭐`exists_stage`;
* `estg`: the chosen parent stage for a child stage;
* `pstgO`, `porig`, `PPreOk`: stages and origins along a path, composed edge by edge;
* `preWP`, `preWPX`: the path preimage of a formula of a `□` view and of a `◇_x` view, one
  substitution; ⭐`preWP_cons`, ⭐`preWPX_cons`: it is the edge's preimage of the rest's;
* ⭐`box_pathO_iff`, ⭐`dia_pathO_iff`: uniformity along a path for the canonical preimage;
* ⭐`fmapL_names`: under 5 every entry names an address; ⭐`orig_names`: the origin of a named
  address is its namer, at η-faithful types (R4 at addresses).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Origins along an edge -/

open Classical in
/-- ⭐**The origin of a child's address along its edge**: a parent address of a keepable type
    naming it, if there is one (names by origin, `glorigin`; unique at η-faithful types,
    `names_unique`).  One map for every stage of the child. -/
noncomputable def orig (s t : GW hF M₀) (z : VarSymb) : VarSymb :=
  if h : ∃ (i : ℕ) (v : VarSymb) (U : VarType), (ctxOf (glat s i)).ref v = some U ∧
      U.keepable = true ∧ Names t v z then h.choose_spec.choose else z

theorem orig_spec {s t : GW hF M₀} {z : VarSymb}
    (h : ∃ (i : ℕ) (v : VarSymb) (U : VarType), (ctxOf (glat s i)).ref v = some U ∧
      U.keepable = true ∧ Names t v z) :
    ∃ (i : ℕ) (U : VarType), (ctxOf (glat s i)).ref (orig s t z) = some U ∧
      U.keepable = true ∧ Names t (orig s t z) z := by
  unfold orig
  rw [dif_pos h]
  exact ⟨h.choose, h.choose_spec.choose_spec⟩

/-- ⭐**Every stage of a child has the origins as its preimage**, at a stage of the parent
    committed no earlier than it (`exists_pre` with the map fixed). -/
theorem exists_stage (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (j : ℕ) :
    ∃ i : ℕ, j ≤ glstg s t i ∧ PreOk s t i (glat t j) (orig s t) := by
  classical
  have hor : ∀ z T, (ctxOf (glat t j)).ref z = some T → T.keepable = true →
      ∃ i : ℕ, (ctxOf (glat s i)).ref (orig s t z) = some T ∧ Names t (orig s t z) z := by
    intro z T hz hkp
    have hl : T.liftable = true := by
      cases T <;> simp_all [VarType.liftable, VarType.keepable]
    obtain ⟨i, v, U, hv, hkU, hn⟩ := glorigin hV hT hM₀ h j hz hl
    obtain ⟨i', U', hv', hkU', hn'⟩ := orig_spec ⟨i, v, U, hv, hkU, hn⟩
    obtain rfl := names_type hM₀ h hv' hkU' hn' hz
    exact ⟨i', hv', hn'⟩
  let P : VarSymb → Prop := fun z =>
    ∃ T, (ctxOf (glat t j)).ref z = some T ∧ T.keepable = true
  let iz : VarSymb → ℕ := fun z =>
    if hz : P z then (hor z _ hz.choose_spec.1 hz.choose_spec.2).choose else 0
  obtain ⟨N, hN⟩ := ((Ctx.Fin.reach (ctxOf_fin (glat t j))).image iz).bddAbove
  refine ⟨max N (gbirth hF M₀ t.2 + j), ?_, ?_⟩
  · have := (glstg_spec hM₀ h (max N (gbirth hF M₀ t.2 + j))).1
    omega
  · intro z T hz hkp
    have hP : P z := ⟨T, hz, hkp⟩
    have hc := (hor z _ hP.choose_spec.1 hP.choose_spec.2).choose_spec
    have hTT : hP.choose = T := Option.some.inj (hP.choose_spec.1.symm.trans hz)
    have hiz : iz z ≤ max N (gbirth hF M₀ t.2 + j) :=
      (hN ⟨z, by simp [hz], rfl⟩).trans (le_max_left _ _)
    simp only [iz, dif_pos hP] at hiz
    refine ⟨?_, hc.2⟩
    rw [← hTT]
    exact (ctxOf_le_of_suffix (glat_suffix hM₀ s hiz)).ref hc.1

open Classical in
/-- The chosen parent stage for a child stage: one where the origins are a preimage. -/
noncomputable def estg (s t : GW hF M₀) (j : ℕ) : ℕ :=
  if h : ∃ i : ℕ, j ≤ glstg s t i ∧ PreOk s t i (glat t j) (orig s t) then h.choose else 0

theorem estg_spec (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) (j : ℕ) :
    j ≤ glstg s t (estg s t j) ∧ PreOk s t (estg s t j) (glat t j) (orig s t) := by
  have he := exists_stage hV hT hS hW hM₀ h j
  unfold estg
  rw [dif_pos he]
  exact he.choose_spec

/-! ## Along a path -/

/-- The chosen ancestor stage for a descendant's stage, edge by edge. -/
noncomputable def pstgO : (P : List ℕ) → (s t : GW hF M₀) → t.1 = nodeOf s.1 P → ℕ → ℕ
  | [], _, _, _, j => j
  | c :: P, s, t, hP, j =>
      estg s (stepW s c (born_step hP)) (pstgO P (stepW s c (born_step hP)) t hP j)

/-- The origins along a path, composed edge by edge. -/
noncomputable def porig : (P : List ℕ) → (s t : GW hF M₀) → t.1 = nodeOf s.1 P →
    VarSymb → VarSymb
  | [], _, _, _ => id
  | c :: P, s, t, hP =>
      orig s (stepW s c (born_step hP)) ∘ porig P (stepW s c (born_step hP)) t hP

/-- The path origins keep the type of every reachable keepable address of a stage. -/
def PPreOk (P : List ℕ) (s t : GW hF M₀) (hP : t.1 = nodeOf s.1 P) (j : ℕ) : Prop :=
  ∀ z T, (ctxOf (glat t j)).ref z = some T → T.keepable = true →
    (ctxOf (glat s (pstgO P s t hP j))).ref (porig P s t hP z) = some T

theorem pPreOk (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (hP : t.1 = nodeOf s.1 P) (j : ℕ), PPreOk P s t hP j
  | [], s, t, hP, j, z, T, hz, _ => by
      obtain rfl : t = s := gw_eq hP
      exact hz
  | c :: P, s, t, hP, j, z, T, hz, hkp =>
      ((estg_spec hV hT hS hW hM₀ ⟨c, rfl⟩ _).2 _ T
        (pPreOk hV hT hS hW hM₀ P (stepW s c (born_step hP)) t hP j z T hz hkp) hkp).1

/-! ## Preimages of formulas along a path -/

/-- The path preimage of a formula of a descendant's `□` view, in the ancestor's `□` view. -/
noncomputable def preWP (hk : ModalSys.keepOnly = false) {P : List ℕ} {s t : GW hF M₀}
    {hP : t.1 = nodeOf s.1 P} {j : ℕ} (hpo : PPreOk P s t hP j)
    (ψ : WFF σ (ctxOf (glat t j)).boxIn 0) :
    WFF σ (ctxOf (glat s (pstgO P s t hP j))).boxIn 0 :=
  WFF.subst (eIdx (ofRen (preI (porig P s t hP))))
    (eS σ (ctxOf (glat s (pstgO P s t hP j))).boxIn (ofRen (preI (porig P s t hP))))
    (ok_eS_kView (k := none) (entOk_ofRen (itemOk_preI hk hpo)))
    (coh_eS_kView (k := none) (entOk_ofRen (itemOk_preI hk hpo)))
    Ctx.NoSlots.slots Ctx.NoSlots.slots ψ

/-- The path preimage of a formula of a descendant's `◇_x` view, in the ancestor's
    `◇_{porig x}` view. -/
noncomputable def preWPX (hk : ModalSys.keepOnly = false) {P : List ℕ} {s t : GW hF M₀}
    {hP : t.1 = nodeOf s.1 P} {j : ℕ} (hpo : PPreOk P s t hP j) {x : VarSymb} {X : VarType}
    (hx : (ctxOf (glat t j)).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (glat t j)).diaIn x) 0) :
    WFF σ ((ctxOf (glat s (pstgO P s t hP j))).diaIn (porig P s t hP x)) 0 :=
  WFF.subst (eIdx (ofRen (preIX (porig P s t hP) x)))
    (eS σ ((ctxOf (glat s (pstgO P s t hP j))).diaIn (porig P s t hP x))
      (ofRen (preIX (porig P s t hP) x)))
    (ok_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hk hx hpo)))
    (coh_eS_kView (k := some x) (entOk_ofRen (itemOk_preIX hk hx hpo)))
    Ctx.NoSlots.slots Ctx.NoSlots.slots ψ

omit [ModalSys] in
theorem preI_comp (f g : VarSymb → VarSymb) (v : VarSymb) :
    preI f (preI g v) = preI (f ∘ g) v := by
  rcases v with _ | ⟨u, st⟩
  · rfl
  · cases st <;> rfl

/-- The `◇_x` item maps compose, on the items of the view. -/
theorem preIX_comp (f g : VarSymb → VarSymb) {l : List VarType} {x v : VarSymb}
    {T : VarType} (hl : v.lastProj = false) (hv : (ctxOf l).diaIn x v = some T) :
    preIX f (g x) (preIX g x v) = preIX (f ∘ g) x v := by
  by_cases hvx : v = .step x .dia
  · subst hvx
    unfold preIX
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    rfl
  · have hb := diaIn_boxIn_of_ne' hv hvx
    unfold preIX
    rw [if_neg hvx, if_neg hvx, preI_comp, if_neg]
    match v, hb with
    | .step _ .box, _ => simp [preI]
    | .step _ .keep, _ => simp [preI]
    | .root _, hb => cases hb
    | .step _ .fst, hb => cases hb
    | .step _ .snd, hb => cases hb
    | .step _ .dia, hb => cases hb
    | .step _ .here, hb => cases hb

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Two renamings in a row are one, when the first sends items to items. -/
theorem sim_eS_ren_comp {Γ Δ₁ Δ₂ : Ctx} {ι : VarSymb → VarSymb} (f g h : VarSymb → VarSymb)
    (hθ : Subst.Ok Δ₁ (eS σ Δ₂ (ofRen f))) (hc : Subst.Coh ι Δ₁ (eS σ Δ₂ (ofRen f)))
    (hg : ∀ u st T, st.isProj = false → Γ (.step u st) = some T → ∃ u' st',
      g (.step u st) = .step u' st' ∧ st'.isProj = false ∧ h (.step u st) = f (.step u' st')) :
    Subst.Sim Γ (eS σ Δ₂ (ofRen h)) ((eS σ Δ₁ (ofRen g)).comp (eS σ Δ₂ (ofRen f)) hθ hc) := by
  refine Subst.sim_of fun v T hl hv => ?_
  match v, hl, hv with
  | .root _, _, _ => exact .refl _
  | .step u st, hl, hv =>
      obtain ⟨u', st', e, hst', eh⟩ := hg u st T hl hv
      change SubE.Sim T (eS σ Δ₂ (ofRen h) (.step u st))
        ((eS σ Δ₁ (ofRen g) (.step u st)).comp _ _ _)
      rw [eS_item _ hl, eS_item _ hl]
      change SubE.Sim T (.ren (h (.step u st))) ((eS σ Δ₂ (ofRen f)).at (g (.step u st)))
      rw [e, eh, Subst.at_nonproj _ (v := .step u' st') hst', eS_item _ hst']
      exact .refl _

omit [ModalSys] in
theorem preI_step (f : VarSymb → VarSymb) (u : VarSymb) (st : Step) :
    ∃ u', preI f (.step u st) = .step u' st := by
  cases st <;> exact ⟨_, rfl⟩

/-- ⭐**The path preimage is the first edge's preimage of the rest's.** -/
theorem preWP_cons (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false) {c : ℕ} {P : List ℕ}
    {s t : GW hF M₀} (hP : t.1 = nodeOf s.1 (c :: P)) (j : ℕ)
    (ψ : WFF σ (ctxOf (glat t j)).boxIn 0) :
    preWP hk (pPreOk hV hT hS hW hM₀ (c :: P) s t hP j) ψ =
      preW hk (estg_spec hV hT hS hW hM₀ (s := s) (t := stepW s c (born_step hP)) ⟨c, rfl⟩
          (pstgO P (stepW s c (born_step hP)) t hP j)).2
        (preWP hk (pPreOk hV hT hS hW hM₀ P (stepW s c (born_step hP)) t hP j) ψ) := by
  unfold preWP preW
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
    fun u st _ hst _ => ?_) ψ).symm
  obtain ⟨u', e⟩ := preI_step (porig P (stepW s c (born_step hP)) t hP) u st
  exact ⟨u', st, e, hst, by rw [← e, preI_comp]; rfl⟩

/-- ⭐**The path preimage of a `◇_x` view is the first edge's preimage of the rest's.** -/
theorem preWPX_cons (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false) {c : ℕ} {P : List ℕ}
    {s t : GW hF M₀} (hP : t.1 = nodeOf s.1 (c :: P)) (j : ℕ) {x : VarSymb} {X : VarType}
    (hx : (ctxOf (glat t j)).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (glat t j)).diaIn x) 0) :
    preWPX hk (pPreOk hV hT hS hW hM₀ (c :: P) s t hP j) hx ψ =
      preWX hk (estg_spec hV hT hS hW hM₀ (s := s) (t := stepW s c (born_step hP)) ⟨c, rfl⟩
          (pstgO P (stepW s c (born_step hP)) t hP j)).2
        (pPreOk hV hT hS hW hM₀ P (stepW s c (born_step hP)) t hP j x _ hx rfl)
        (preWPX hk (pPreOk hV hT hS hW hM₀ P (stepW s c (born_step hP)) t hP j) hx ψ) := by
  unfold preWPX preWX
  refine (WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ (sim_eS_ren_comp _ _ _ _ _
    fun u st _ hst hv => ?_) ψ).symm
  have hc := preIX_comp (orig s (stepW s c (born_step hP)))
    (porig P (stepW s c (born_step hP)) t hP) (v := .step u st) hst hv
  by_cases hvx : VarSymb.step u st = .step x .dia
  · have e : preIX (porig P (stepW s c (born_step hP)) t hP) x (.step u st) =
        .step (porig P (stepW s c (born_step hP)) t hP x) .dia := by
      unfold preIX
      rw [if_pos hvx]
    refine ⟨_, .dia, e, rfl, ?_⟩
    rw [← e, hc]
    rfl
  · obtain ⟨u', e'⟩ := preI_step (porig P (stepW s c (born_step hP)) t hP) u st
    have e : preIX (porig P (stepW s c (born_step hP)) t hP) x (.step u st) = .step u' st := by
      unfold preIX
      rw [if_neg hvx, e']
    refine ⟨u', st, e, hst, ?_⟩
    rw [← e, hc]
    rfl

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Along the empty path the preimage is the identity. -/
theorem preWP_nil {l : List VarType} (ψ : WFF σ (ctxOf l).boxIn 0)
    (hθ : Subst.Ok (ctxOf l).boxIn (eS σ (ctxOf l).boxIn (ofRen (preI id))))
    (hc : Subst.Coh (eIdx (ofRen (σ := σ) (preI id))) (ctxOf l).boxIn
      (eS σ (ctxOf l).boxIn (ofRen (preI id)))) :
    WFF.subst (eIdx (ofRen (σ := σ) (preI id))) (eS σ (ctxOf l).boxIn (ofRen (preI id))) hθ hc
      Ctx.NoSlots.slots Ctx.NoSlots.slots ψ = ψ := by
  rw [WFF.subst_congr _ (Subst.idS σ _) hθ (Subst.ok_idS_le (Ctx.Le.refl _)) hc
      (Subst.coh_idS_le (Ctx.Le.refl _)) _ _ ?_ ψ, subst_idS_le (Ctx.Le.refl _) ψ,
    WFF.mono_refl]
  refine Subst.sim_of fun v T hl hv => ?_
  match v, hl with
  | .root _, _ => cases hv
  | .step u st, hl =>
      rw [eS_item _ hl]
      obtain ⟨u', e⟩ := preI_step id u st
      change SubE.Sim T (.ren (preI id (.step u st))) (.ren (.step u st))
      rw [show preI id (.step u st) = .step u st by cases st <;> rfl]
      exact .refl _

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- Along the empty path the `◇_x` preimage is the identity. -/
theorem preWPX_nil {l : List VarType} {x : VarSymb} (ψ : WFF σ ((ctxOf l).diaIn x) 0)
    (hθ : Subst.Ok ((ctxOf l).diaIn x) (eS σ ((ctxOf l).diaIn x) (ofRen (preIX id x))))
    (hc : Subst.Coh (eIdx (ofRen (σ := σ) (preIX id x))) ((ctxOf l).diaIn x)
      (eS σ ((ctxOf l).diaIn x) (ofRen (preIX id x)))) :
    WFF.subst (eIdx (ofRen (σ := σ) (preIX id x))) (eS σ ((ctxOf l).diaIn x)
      (ofRen (preIX id x))) hθ hc Ctx.NoSlots.slots Ctx.NoSlots.slots ψ = ψ := by
  rw [WFF.subst_congr _ (Subst.idS σ _) hθ (Subst.ok_idS_le (Ctx.Le.refl _)) hc
      (Subst.coh_idS_le (Ctx.Le.refl _)) _ _ ?_ ψ, subst_idS_le (Ctx.Le.refl _) ψ,
    WFF.mono_refl]
  refine Subst.sim_of fun v T hl hv => ?_
  match v, hl with
  | .root _, _ => cases hv
  | .step u st, hl =>
      rw [eS_item _ hl]
      change SubE.Sim T (.ren (preIX id x (.step u st))) (.ren (.step u st))
      rw [show preIX id x (.step u st) = .step u st by
        unfold preIX
        split_ifs with h
        · exact h.symm
        · cases st <;> rfl]
      exact .refl _

/-! ## Uniformity along a path, for the canonical preimage -/

/-- ⭐**Cluster uniformity along a path, canonically** (`docs/v12-modal-extensions.md` §3 5): a
    descendant's `□ψ` holds exactly when `□` of its path preimage holds at the ancestor's chosen
    stage. -/
theorem box_pathO_iff (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (hP : t.1 = nodeOf s.1 P) (j : ℕ)
      (ψ : WFF σ (ctxOf (glat t j)).boxIn 0),
      WFF.box (preWP hk (pPreOk hV hT hS hW hM₀ P s t hP j) ψ) ∈ gMs s (pstgO P s t hP j) ↔
        WFF.box ψ ∈ gMs t j
  | [], s, t, hP, j, ψ => by
      obtain rfl : t = s := gw_eq hP
      exact iff_of_eq (congrArg (fun φ => WFF.box φ ∈ gMs t j) (preWP_nil ψ _ _))
  | c :: P, s, t, hP, j, ψ => by
      have hch : GCh hF M₀ s (stepW s c (born_step hP)) := ⟨c, rfl⟩
      have hes := estg_spec hV hT hS hW hM₀ hch (pstgO P (stepW s c (born_step hP)) t hP j)
      have hle := ctxOf_le_of_suffix (glat_suffix hM₀ (stepW s c (born_step hP)) hes.1)
      rw [preWP_cons hV hT hS hW hM₀ hk hP j ψ]
      refine (box_pre_iff hM₀ hk hV hch _ hle hes.2 _).trans ?_
      rw [← box_pathO_iff hV hT hS hW hM₀ hk P (stepW s c (born_step hP)) t hP j ψ]
      exact (gMs_mono_iff hM₀ (stepW s c (born_step hP)) hes.1 (WFF.box
        (preWP hk (pPreOk hV hT hS hW hM₀ P (stepW s c (born_step hP)) t hP j) ψ))).symm

/-- ⭐**`◇`-uniformity along a path, canonically**: a descendant's `◇_x ψ` holds exactly when
    `◇` at the witness's path origin, of the body's path preimage, holds at the ancestor's chosen
    stage. -/
theorem dia_pathO_iff (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hS : ModalSys.FourStrong = true) (hW : ModalSys.FourStrongW = true)
    (hM₀ : Theory.IsMCS M₀) (hk : ModalSys.keepOnly = false) :
    ∀ (P : List ℕ) (s t : GW hF M₀) (hP : t.1 = nodeOf s.1 P) (j : ℕ) {x : VarSymb}
      {X : VarType} (hx : (ctxOf (glat t j)).ref x = some (.VTypeDia X))
      (ψ : WFF σ ((ctxOf (glat t j)).diaIn x) 0),
      WFF.dia (porig P s t hP x) ⟨X, pPreOk hV hT hS hW hM₀ P s t hP j x _ hx rfl⟩
          (preWPX hk (pPreOk hV hT hS hW hM₀ P s t hP j) hx ψ) ∈ gMs s (pstgO P s t hP j) ↔
        WFF.dia x ⟨X, hx⟩ ψ ∈ gMs t j
  | [], s, t, hP, j, x, X, hx, ψ => by
      obtain rfl : t = s := gw_eq hP
      exact iff_of_eq (congrArg (fun φ => WFF.dia x ⟨X, hx⟩ φ ∈ gMs t j) (preWPX_nil ψ _ _))
  | c :: P, s, t, hP, j, x, X, hx, ψ => by
      have hch : GCh hF M₀ s (stepW s c (born_step hP)) := ⟨c, rfl⟩
      have hes := estg_spec hV hT hS hW hM₀ hch (pstgO P (stepW s c (born_step hP)) t hP j)
      have hle := ctxOf_le_of_suffix (glat_suffix hM₀ (stepW s c (born_step hP)) hes.1)
      have hx' := pPreOk hV hT hS hW hM₀ P (stepW s c (born_step hP)) t hP j x _ hx rfl
      rw [preWPX_cons hV hT hS hW hM₀ hk hP j hx ψ]
      refine (dia_pre_iff hM₀ hk hV hch _ hle hes.2 hx' _).trans ?_
      rw [← dia_pathO_iff hV hT hS hW hM₀ hk P (stepW s c (born_step hP)) t hP j hx ψ]
      exact (gMs_mono_iff hM₀ (stepW s c (born_step hP)) hes.1 (WFF.dia _ ⟨X, hx'⟩
        (preWPX hk (pPreOk hV hT hS hW hM₀ P (stepW s c (born_step hP)) t hP j) hx ψ))).symm

/-! ## Origins invert naming (R4, at addresses) -/

/-- ⭐**Under 5 every entry names an address**: forward images are addresses, and lifts are
    η-terms of addresses (names by origin, `AdmEnt`). -/
theorem fmapL_names (hV : ModalSys.Five = true) (k : Node) (v : VarSymb) :
    ∃ z, NamesE (fmapL hF M₀ k v) z := by
  rcases h : fmapL hF M₀ k v with z | ⟨L, Te, ae, te⟩
  · exact ⟨z, .inl rfl⟩
  · obtain ⟨⟨l, T, a, t⟩, hsuf, -, -, h5, he⟩ := fmapL_adm h
    obtain ⟨z, T', hz, e5⟩ := h5 hV
    clear h5
    dsimp only at hsuf hz he
    obtain ⟨-, e5'⟩ := Sigma.mk.inj_iff.mp e5
    clear e5
    obtain ⟨rfl, e6⟩ := Sigma.mk.inj_iff.mp (eq_of_heq e5')
    clear e5'
    obtain ⟨rfl, e7⟩ := Sigma.mk.inj_iff.mp (eq_of_heq e6)
    clear e6
    have e8 : t = Term.eta (σ := σ) z T hz := eq_of_heq e7
    subst e8
    refine ⟨z, .inr ⟨L, _, (ctxOf_le_of_suffix hsuf).ref hz, ?_⟩⟩
    rw [he, Term.mono_eta]

/-- A named address's type is the namer's, at the child's stage that commits the namer's. -/
theorem names_ref' (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) {i : ℕ}
    {v z : VarSymb} {U : VarType} (hv : (ctxOf (glat s i)).ref v = some U)
    (hkp : U.keepable = true) (hn : Names t v z) :
    (ctxOf (glat t (glstg s t i))).ref z = some U := by
  rcases hn with he | ⟨L, T', hz', he⟩
  · have hok := gentOk_box hM₀ h i (.step v .keep) U rfl (Ctx.boxIn_keep_of' hF hv hkp)
    rw [he] at hok
    exact hok
  · obtain ⟨rfl, hz'', -⟩ := entOf_names_tm hM₀ h i hv hkp hz' he
    exact hz''

/-- ⭐**The origin of a named address is its namer**, at η-faithful types (`names_unique`). -/
theorem orig_names (hV : ModalSys.Five = true) (hT : ModalSys.T = false)
    (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (h : GCh hF M₀ s t) {i : ℕ} {v z : VarSymb}
    {U : VarType} (hv : (ctxOf (glat s i)).ref v = some U) (hkp : U.keepable = true)
    (hU : U.etaInj = true) (hn : Names t v z) : orig s t z = v := by
  obtain ⟨i', U', hv', hkU', hn'⟩ := orig_spec ⟨i, v, U, hv, hkp, hn⟩
  obtain rfl := names_type hM₀ h hv' hkU' hn' (names_ref' hM₀ h hv hkp hn)
  exact (names_unique hV hT hM₀ h hv hkp hv' hkU' hU hU hn hn').symm

end GArrow

end V12M
