import QML.QML_v12m_GCluFunc
import QML.QML_v12m_RetUnliftC
import QML.QML_v12m_BCanonModel

/-!
# QML v12m — 5 on the growing tree: the cluster model

The K45 cluster model (`docs/v12-modal-extensions.md` §3 5, "`GCluModel`: the fields checked
against `GCanonModel`"), as `GCanonModel`/`GCanonLift` for the growing tree.

* The frame (`carrows`, `cframe`): every world's arrows are the root's — `R s t :⇔ t` is a strict
  descendant of the root — so composition and 5's arrow across keep the target, and every arrow
  law holds by proof irrelevance.
* The carriers are the definable raw objects (`CDefinable`), the function algebra acts by
  `crawEval` (`cops`, `ceval_toDom`); `necDup`, `posKeep` and `posSide` read an object along every
  arrow as itself.
* `cposFull`, `cposShape_wf`: under T a possible object's shape, stored at the root and moved to
  the world (`CLeaf.rean`), is its annotation's; the operations move it (`shp_rean`,
  `cdiaMap_shape`, `cstrength_shape`, `ckeep_shape`).
* `cposSerial` (strong D), `ckeepLift` (strong 4), `cInd` and `cposRet_exists` (strong T), and
  ⭐`cmodel`: the model, every law of 4 and 5 by definition or by R4.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

theorem CluFlags.T_of_shaped (hX : CluFlags) (h : ModalSys.shaped = true) : ModalSys.T = true := by
  by_cases hB : ModalSys.BStrong = true
  · exact hX.bT hB
  · simpa [ModalSys.shaped, hB] using h

/-! ## Moving shapes between anchors -/

theorem CLeaf.rean_rean {g : GW hF M₀} (s t : GW hF M₀) (l : CLeaf hF M₀ g) :
    CLeaf.rean t (CLeaf.rean s l) = CLeaf.rean t l :=
  match g, l with
  | _, .root _ _ => rfl
  | _, .fam _ => rfl

theorem CLeaf.rean_self {g : GW hF M₀} (l : CLeaf hF M₀ g) : CLeaf.rean g l = l :=
  match g, l with
  | _, .root _ _ => rfl
  | _, .fam _ => rfl

theorem cshape_rean_rean {g : GW hF M₀} {T : VarType} (a : CShape hF M₀ g T) (s t : GW hF M₀) :
    (a.map (CLeaf.rean s)).map (CLeaf.rean t) = a.map (CLeaf.rean t) := by
  rw [Shp.map_map]
  exact Shp.map_congr (fun l => CLeaf.rean_rean s t l) _

theorem cshape_rean_self {g : GW hF M₀} {T : VarType} (a : CShape hF M₀ g T) :
    a.map (CLeaf.rean g) = a :=
  (Shp.map_congr (fun l => CLeaf.rean_self l) a).trans (Shp.map_id a)

/-- A family of shapes is one shape, whatever the anchor. -/
theorem transpose_rean (g t : GW hF M₀) : ∀ {A : VarType}
    (f : (a : CAcc hF M₀) → CShape hF M₀ a.1 A),
    (Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb) (w := g) f).map
        (CLeaf.rean t) =
      Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb) (w := t) f
  | .Var, _ => rfl
  | .VTypeOne, _ => rfl
  | .VTypeProd A C, f => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [transpose_rean g t (A := A), transpose_rean g t (A := C)]
  | .VTypeBox A, f => by
      change Shp.box _ = Shp.box _
      rw [transpose_rean g t (A := A)]
  | .VTypeDia A, f => by
      change Shp.dia _ _ = Shp.dia _ _
      rw [transpose_rean g t (A := A)]
      rfl

/-- Below the anchor's level a leaf operation does not see the anchor. -/
theorem rean_collapse (hT : ModalSys.T = true) (t : GW hF M₀) (i : ℕ) {g : GW hF M₀}
    (l : CLeaf hF M₀ g) :
    CLeaf.rean t (Arrows.Leaf.collapse hT (i + 1) l) =
      Arrows.Leaf.collapse hT (i + 1) (CLeaf.rean t l) :=
  match g, l with
  | _, .root _ _ => rfl
  | _, .fam _ => rfl

theorem rean_shift (hF' : ModalSys.Four = true) (t : GW hF M₀) (i : ℕ) {g : GW hF M₀}
    (l : CLeaf hF M₀ g) :
    CLeaf.rean t (Arrows.Leaf.shift hF' (i + 1) l) =
      Arrows.Leaf.shift hF' (i + 1) (CLeaf.rean t l) :=
  match g, l with
  | _, .root _ _ => rfl
  | _, .fam _ => rfl

theorem rean_dk (hF' : ModalSys.Four = true) (t : GW hF M₀) (i : ℕ) {g : GW hF M₀}
    (l : CLeaf hF M₀ g) :
    CLeaf.rean t (Arrows.Leaf.dk hF' (i + 1) l) = Arrows.Leaf.dk hF' (i + 1) (CLeaf.rean t l) :=
  match g, l with
  | _, .root _ _ => rfl
  | _, .fam _ => rfl

theorem rean_dkB (hF' : ModalSys.Four = true) (t : GW hF M₀) (i : ℕ) {g : GW hF M₀}
    (l : CLeaf hF M₀ g) :
    CLeaf.rean t (Arrows.Leaf.dkB hF' (i + 1) l) = Arrows.Leaf.dkB hF' (i + 1) (CLeaf.rean t l) :=
  match g, l with
  | _, .root _ _ => rfl
  | _, .fam _ => rfl

/-- ⭐**Below the anchor's level a map moves a shape as it moves the shape's move.** -/
theorem shp_rean (t : GW hF M₀) {g : GW hF M₀} : ∀ {A B : VarType} (f : GFunc σ A B) (j : ℕ)
    (a : CShape hF M₀ g A),
    (GFunc.shp f (j + 1) a).map (CLeaf.rean t) = GFunc.shp f (j + 1) (a.map (CLeaf.rean t))
  | _, _, .id _, _, _ => rfl
  | _, _, .comp f₂ f₁, j, a => by
      change (GFunc.shp f₂ (j + 1) (GFunc.shp f₁ (j + 1) a)).map _ =
        GFunc.shp f₂ (j + 1) (GFunc.shp f₁ (j + 1) _)
      rw [shp_rean t f₂ j, shp_rean t f₁ j]
  | _, _, .fst, _, .prod _ _ => rfl
  | _, _, .snd, _, .prod _ _ => rfl
  | _, _, .pair f₁ f₂, j, a => by
      change Shp.prod _ _ = Shp.prod _ _
      rw [shp_rean t f₁ j, shp_rean t f₂ j]
  | _, _, .unit _, _, _ => rfl
  | _, _, .func _ _, _, _ => rfl
  | _, _, .boxMap f, j, .box a => congrArg Shp.box (shp_rean t f (j + 1) a)
  | _, _, .boxPair _ _, _, .prod (.box _) (.box _) => rfl
  | _, _, .boxUnit, _, _ => rfl
  | _, _, .diaMap f, j, .dia _ a => congrArg (Shp.dia _) (shp_rean t f (j + 1) a)
  | _, _, .strength _ _, _, .prod (.box _) (.dia _ _) => rfl
  | _, _, .extract hT, j, .box a => by
      change (a.map (Arrows.Leaf.collapse hT (j + 1))).map (CLeaf.rean t) =
        (a.map (CLeaf.rean t)).map (Arrows.Leaf.collapse hT (j + 1))
      rw [Shp.map_map, Shp.map_map]
      exact Shp.map_congr (fun l => rean_collapse hT t j l) _
  | _, _, .dup hF', j, .box a => by
      change Shp.box (Shp.box ((a.map (Arrows.Leaf.shift hF' (j + 1))).map (CLeaf.rean t))) =
        Shp.box (Shp.box ((a.map (CLeaf.rean t)).map (Arrows.Leaf.shift hF' (j + 1))))
      rw [Shp.map_map, Shp.map_map]
      exact congrArg (fun z => Shp.box (Shp.box z))
        (Shp.map_congr (fun l => rean_shift hF' t j l) _)
  | _, _, .dkeep hF', j, .dia l a => by
      change Shp.box (Shp.dia _ ((a.map (Arrows.Leaf.dkB hF' (j + 1))).map (CLeaf.rean t))) =
        Shp.box (Shp.dia _ ((a.map (CLeaf.rean t)).map (Arrows.Leaf.dkB hF' (j + 1))))
      rw [Shp.map_map, Shp.map_map, rean_dk]
      exact congrArg (fun z => Shp.box (Shp.dia _ z))
        (Shp.map_congr (fun l => rean_dkB hF' t j l) _)

theorem leafWF_rean (t : GW hF M₀) {g : GW hF M₀} (lw : List Bool) (l : CLeaf hF M₀ g)
    (h : Arrows.Leaf.WF lw l) : Arrows.Leaf.WF lw (CLeaf.rean t l) :=
  match g, lw, l, h with
  | _, _, .root _ _, h => h
  | _, [], .fam _, h => h
  | _, _ :: _, .fam _, h => h

/-- Moving a shape keeps it well-formed. -/
theorem shWF_rean (t : GW hF M₀) {g : GW hF M₀} : ∀ {A : VarType} (lw : List Bool)
    (a : CShape hF M₀ g A),
    Model.ShWF (F := carrows hF M₀) (Root := fun _ => VarSymb) lw a →
      Model.ShWF (F := carrows hF M₀) (Root := fun _ => VarSymb) lw (a.map (CLeaf.rean t))
  | _, _, .var, _ => trivial
  | _, _, .one, _ => trivial
  | _, lw, .prod a b, h => ⟨shWF_rean t lw a h.1, shWF_rean t lw b h.2⟩
  | _, lw, .box a, h => shWF_rean t (lw ++ [true]) a h
  | _, lw, .dia l a, h => ⟨leafWF_rean t lw l h.1, shWF_rean t (lw ++ [false]) a h.2⟩

/-! ## The frame -/

variable (hM₀ : Theory.IsMCS M₀)

/-- ⭐**Weak B on the cluster**: if the root reaches anything, it reaches everything.  Under T by
    `rpath`.  With T off and `¬□⊥ ∈ M₀` the root has its self-arrow.  With `□⊥ ∈ M₀` a first step
    of a path would be a child holding `⊥`, so the root reaches nothing: KB5's dead end. -/
theorem csymm (hM₀ : Theory.IsMCS M₀) (hX : CluFlags) (hB : ModalSys.B = true) {w v : GW hF M₀}
    (hv : CR v) : CR w := by
  by_cases hT : ModalSys.T = true
  · exact (carrows hF M₀).refl hT w
  have hT' : ModalSys.T = false := Bool.eq_false_iff.mpr hT
  by_cases hne : (WFF.box (Γ := ctxOf l₀) .bot).neg ∈ M₀
  · have hl : GNetSt.LoopOn M₀ := ⟨hB, ⟨hF, hX.five, hX.fourS, hX.fourSW, hT'⟩, hne⟩
    rcases hp : rpath w with _ | ⟨c, P⟩
    · exact ⟨[], .inr ⟨rfl, hl⟩, by have := rpath_eq w; rwa [hp] at this⟩
    · exact ⟨rpath w, .inl (by rw [hp]; exact pathOk_cons), rpath_eq w⟩
  · exfalso
    have hbot : WFF.box (Γ := ctxOf l₀) .bot ∈ M₀ := by
      by_contra hn
      exact hne (hM₀.neg_mem_iff.mpr hn)
    obtain ⟨P, hP, h⟩ := hv
    cases P with
    | nil =>
        rcases hP with hP | hP
        · exact hT hP.T_of_nil
        · exact hne hP.2.2.2
    | cons c P =>
        have hψ : WFF.box (Γ := (ctxOf (glat (groot hF M₀) 0))) .bot ∈
            ((gnet hF M₀ (gbirth hF M₀ (groot hF M₀).2 + 0)).st []).M :=
          ((ext_gnet hF hM₀ (Nat.zero_le _)).grows [] trivial).sub _ hbot
        have ht := gltr hM₀ (s := groot hF M₀) (t := stepW (groot hF M₀) c (born_step h))
          ⟨c, rfl⟩ 0 .bot hψ
        exact ((good_gnet hF hM₀ _).mcs _
          (live_gbirth hF hM₀ (born_step h) (Nat.le_add_right _ _))).bot_not_mem ht

variable (hF) in
/-- ⭐**The cluster frame.** -/
noncomputable def cframe (hX : CluFlags) : Frame.{0, 0} σ where
  toArrows := carrows hF M₀
  actual := groot hF M₀
  serial := fun hD _ => (gserial hM₀ hD (groot hF M₀)).imp fun _ ⟨h⟩ => ⟨CR.of_GR h⟩
  symm := fun hB {_ v} h => ⟨csymm hM₀ hX hB (v := v) h⟩
  homeUnique := fun _ => ⟨fun _ _ => rfl⟩
  side := fun _ {_ _ _} _ b => b
  side_inj := fun _ {_ _ _ _} _ _ _ h => h
  side_side := fun _ {_ _ _ _} _ _ _ => rfl
  trans_side := fun _ _ {_ _ _} _ _ => rfl
  side_trans := fun _ _ {_ _ _ _} _ _ _ => rfl
  side_refl := fun _ _ {_ _} _ => rfl
  D s := (gw hM₀ s).D
  Nec A s := {o : CRDom hM₀ (.VTypeBox A) s // CDefinable hM₀ hX (.VTypeBox A) s o}
  Pos A s := {o : CRDom hM₀ (.VTypeDia A) s // CDefinable hM₀ hX (.VTypeDia A) s o}
  funcInterp f s args := (gw hM₀ s).canonFunc f args
  relInterp r s args := (gw hM₀ s).canonRel r args

/-! ## Carriers -/

/-- A definable raw object as a frame object. -/
def ctoDom (hX : CluFlags) : (A : VarType) → (s : GW hF M₀) → (o : CRDom hM₀ A s) →
    CDefinable hM₀ hX A s o → (cframe hF hM₀ hX).Dom A s
  | .Var, _, o, _ => o
  | .VTypeOne, _, _, _ => PUnit.unit
  | .VTypeProd A C, s, o, h =>
      (ctoDom hX A s o.1 (cdefinable_fst hX h), ctoDom hX C s o.2 (cdefinable_snd hX h))
  | .VTypeBox A, s, o, h =>
      (Subtype.mk o h :
        {o : CRDom hM₀ (.VTypeBox A) s // CDefinable hM₀ hX (.VTypeBox A) s o})
  | .VTypeDia A, s, o, h =>
      (Subtype.mk o h :
        {o : CRDom hM₀ (.VTypeDia A) s // CDefinable hM₀ hX (.VTypeDia A) s o})

/-- A frame object as a raw object. -/
def cfromDom (hX : CluFlags) : (A : VarType) → (s : GW hF M₀) → (cframe hF hM₀ hX).Dom A s →
    CRDom hM₀ A s
  | .Var, _, d => d
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A C, s, d =>
      (cfromDom hX A s (d : (cframe hF hM₀ hX).Dom A s × (cframe hF hM₀ hX).Dom C s).1,
        cfromDom hX C s (d : (cframe hF hM₀ hX).Dom A s × (cframe hF hM₀ hX).Dom C s).2)
  | .VTypeBox A, s, d =>
      (d : {o : CRDom hM₀ (.VTypeBox A) s // CDefinable hM₀ hX (.VTypeBox A) s o}).1
  | .VTypeDia A, s, d =>
      (d : {o : CRDom hM₀ (.VTypeDia A) s // CDefinable hM₀ hX (.VTypeDia A) s o}).1

theorem cdefinable_fromDom (hX : CluFlags) : ∀ (A : VarType) (s : GW hF M₀)
    (d : (cframe hF hM₀ hX).Dom A s), CDefinable hM₀ hX A s (cfromDom hM₀ hX A s d)
  | .Var, _, d => cdefinable_var hX d
  | .VTypeOne, _, _ => cdefinable_unit hX _
  | .VTypeProd A C, s, d =>
      cdefinable_pair hX
        (cdefinable_fromDom hX A s
          (d : (cframe hF hM₀ hX).Dom A s × (cframe hF hM₀ hX).Dom C s).1)
        (cdefinable_fromDom hX C s
          (d : (cframe hF hM₀ hX).Dom A s × (cframe hF hM₀ hX).Dom C s).2)
  | .VTypeBox A, s, d =>
      (d : {o : CRDom hM₀ (.VTypeBox A) s // CDefinable hM₀ hX (.VTypeBox A) s o}).2
  | .VTypeDia A, s, d =>
      (d : {o : CRDom hM₀ (.VTypeDia A) s // CDefinable hM₀ hX (.VTypeDia A) s o}).2

theorem cfromDom_toDom (hX : CluFlags) : ∀ (A : VarType) (s : GW hF M₀) (o : CRDom hM₀ A s)
    (h : CDefinable hM₀ hX A s o), cfromDom hM₀ hX A s (ctoDom hM₀ hX A s o h) = o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, o, h =>
      Prod.ext (cfromDom_toDom hX A s o.1 (cdefinable_fst hX h))
        (cfromDom_toDom hX C s o.2 (cdefinable_snd hX h))
  | .VTypeBox _, _, _, _ => rfl
  | .VTypeDia _, _, _, _ => rfl

theorem ctoDom_fromDom (hX : CluFlags) : ∀ (A : VarType) (s : GW hF M₀)
    (d : (cframe hF hM₀ hX).Dom A s),
    ctoDom hM₀ hX A s (cfromDom hM₀ hX A s d) (cdefinable_fromDom hM₀ hX A s d) = d
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A C, s, d =>
      Prod.ext
        (ctoDom_fromDom hX A s (d : (cframe hF hM₀ hX).Dom A s × (cframe hF hM₀ hX).Dom C s).1)
        (ctoDom_fromDom hX C s (d : (cframe hF hM₀ hX).Dom A s × (cframe hF hM₀ hX).Dom C s).2)
  | .VTypeBox _, _, _ => rfl
  | .VTypeDia _, _, _ => rfl

variable {hM₀}

theorem ctoDom_inj (hX : CluFlags) {A : VarType} {s : GW hF M₀} {o o' : CRDom hM₀ A s}
    {h : CDefinable hM₀ hX A s o} {h' : CDefinable hM₀ hX A s o'}
    (e : ctoDom hM₀ hX A s o h = ctoDom hM₀ hX A s o' h') : o = o' := by
  rw [← cfromDom_toDom hM₀ hX A s o h, ← cfromDom_toDom hM₀ hX A s o' h', e]

theorem ctoDom_congr (hX : CluFlags) {A : VarType} {s : GW hF M₀} {o o' : CRDom hM₀ A s}
    (e : o = o') (h : CDefinable hM₀ hX A s o) (h' : CDefinable hM₀ hX A s o') :
    ctoDom hM₀ hX A s o h = ctoDom hM₀ hX A s o' h' := by
  subst e
  rfl

variable (hM₀)

/-- Evaluation of necessary objects. -/
def cnecEval (hX : CluFlags) {A : VarType} {s : GW hF M₀} (n : (cframe hF hM₀ hX).Nec A s) :
    (cframe hF hM₀ hX).NecSec A s :=
  fun a => ctoDom hM₀ hX A a.1 (n.1 a) (cdefinable_box_apply hX n.2 a)

/-- Evaluation of possible objects. -/
def cposEval (hX : CluFlags) {A : VarType} {s : GW hF M₀} (p : (cframe hF hM₀ hX).Pos A s) :
    (cframe hF hM₀ hX).PosSec A s :=
  ⟨p.1.E, fun a => ctoDom hM₀ hX A a.1.1 (p.1.c a) (cdefinable_dia_apply hX p.2 a)⟩

theorem cnecEval_injective (hX : CluFlags) {A : VarType} {s : GW hF M₀} :
    Function.Injective (cnecEval hM₀ hX (A := A) (s := s)) := by
  intro n n' h
  apply Subtype.ext
  funext a
  exact ctoDom_inj hX (congrFun h a)

/-- ⭐Evaluation of possible objects, in full: the section and, when shaped, the shape. -/
def cposFull (hX : CluFlags) {A : VarType} {s : GW hF M₀} (p : (cframe hF hM₀ hX).Pos A s) :
    (cframe hF hM₀ hX).PosSec A s × (ModalSys.shaped = true → CShape hF M₀ s (.VTypeDia A)) :=
  (cposEval hM₀ hX p, fun hSh => crawShape (hX.T_of_shaped hSh) p.1)

/-- A possible object is its section and, when shaped, its shape. -/
theorem cposFull_injective (hX : CluFlags) {A : VarType} {s : GW hF M₀} :
    Function.Injective (cposFull hM₀ hX (A := A) (s := s)) := by
  rintro ⟨⟨E, c, τ⟩, hp⟩ ⟨⟨E', c', τ'⟩, hp'⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [cposFull, cposEval] at h₁ h₂
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h₁
  have hc' := eq_of_heq hc
  apply Subtype.ext
  refine CRPos.congr_cont (funext fun a => ctoDom_inj hX (congrFun hc' a)) fun hT => ?_
  have e : (τ hT).map (CLeaf.rean s) = (τ' hT).map (CLeaf.rean s) :=
    congrFun h₂ (ModalSys.shaped_of_T hT)
  have e' := congrArg (Shp.map (CLeaf.rean (groot hF M₀))) e
  rwa [cshape_rean_rean, cshape_rean_rean, cshape_rean_self, cshape_rean_self] at e'

/-- ⭐**The shapes are well-formed**: a possible object is a root term's denotation (R4), whose
    shape is the term's annotation's (`crawShape_cden`), the term's shape in the root's
    environment (`termShp_annC`). -/
theorem cposShape_wf (hX : CluFlags) (hT : ModalSys.T = true) {A : VarType} {s : GW hF M₀}
    (p : (cframe hF hM₀ hX).Pos A s) :
    Model.ShWF (F := carrows hF M₀) (Root := fun _ => VarSymb) [] (crawShape hT p.1) := by
  obtain ⟨i, a, t, ht⟩ := (cdefinable_dia_iff hX s p.1).mp p.2
  have e : crawShape hT (s := groot hF M₀) (A := .VTypeDia A) p.1 = annC (groot hF M₀) a := by
    rw [← ht, crawShape_cden hX hM₀ hT, show preIx (groot hF M₀) = id from funext preIx_root,
      Ann.mapIdx_id]
  have hw : Model.ShWF (F := carrows hF M₀) (Root := fun _ => VarSymb) []
      (annC (groot hF M₀) a) := by
    rw [← termShp_annC hX.five hX.fourS hX.fourSW hM₀ hT (CPushed.base (i := i)) t]
    exact Model.shWF_termShp (lw := []) (cE_wf hX.five hX.fourS hX.fourSW hM₀ hT i) t
  have e' : crawShape hT (s := s) (A := .VTypeDia A) p.1 =
      (crawShape hT (s := groot hF M₀) (A := .VTypeDia A) p.1).map (CLeaf.rean s) :=
    (cshape_rean_rean _ _ _).symm
  rw [e', e]
  exact shWF_rean s [] _ hw

variable (hF) in
/-- ⭐**The function algebra on the carriers**; `posSide` is `posKeep`, 4's keep being the
    identity. -/
noncomputable def cops (hX : CluFlags) : (cframe hF hM₀ hX).Ops where
  necMap g n := ⟨crawEval hM₀ hX (.boxMap g) _ n.1, cdefinable_rawEval hX (.boxMap g) n.2⟩
  necPair a b := ⟨crawEval hM₀ hX (.boxPair _ _) _
      ((a.1, b.1) : CRDom hM₀ (.VTypeProd (.VTypeBox _) (.VTypeBox _)) _),
    cdefinable_rawEval hX (.boxPair _ _) (cdefinable_pair hX a.2 b.2)⟩
  necUnit := ⟨crawEval hM₀ hX .boxUnit _ (PUnit.unit : CRDom hM₀ .VTypeOne _),
    cdefinable_rawEval hX .boxUnit (cdefinable_unit hX _)⟩
  posMap g p := ⟨crawEval hM₀ hX (.diaMap g) _ p.1, cdefinable_rawEval hX (.diaMap g) p.2⟩
  posStrength n p := ⟨crawEval hM₀ hX (.strength _ _) _
      ((n.1, p.1) : CRDom hM₀ (.VTypeProd (.VTypeBox _) (.VTypeDia _)) _),
    cdefinable_rawEval hX (.strength _ _) (cdefinable_pair hX n.2 p.2)⟩
  necExtract hT n := ctoDom hM₀ hX _ _ (crawEval hM₀ hX (.extract hT) _ n.1)
    (cdefinable_rawEval hX (.extract hT) n.2)
  necDup hF' n := ⟨crawEval hM₀ hX (.dup hF') _ n.1, cdefinable_rawEval hX (.dup hF') n.2⟩
  posKeep hF' p := ⟨crawEval hM₀ hX (.dkeep hF') _ p.1, cdefinable_rawEval hX (.dkeep hF') p.2⟩
  posSide _ p := ⟨crawEval hM₀ hX (.dkeep hF) _ p.1, cdefinable_rawEval hX (.dkeep hF) p.2⟩

/-- ⭐Evaluating a map on a frame object is evaluating it on the raw object. -/
theorem ceval_toDom (hX : CluFlags) : ∀ {A C : VarType} (g : GFunc σ A C) (s : GW hF M₀)
    (o : CRDom hM₀ A s) (h : CDefinable hM₀ hX A s o),
    GFunc.eval (cops hF hM₀ hX) g s (ctoDom hM₀ hX A s o h) =
      ctoDom hM₀ hX C s (crawEval hM₀ hX g s o) (cdefinable_rawEval hX g h)
  | _, _, .id _, _, _, _ => rfl
  | _, _, .comp g f, s, o, h =>
      (congrArg (GFunc.eval (cops hF hM₀ hX) g s) (ceval_toDom hX f s o h)).trans
        (ceval_toDom hX g s _ _)
  | _, _, .fst, _, _, _ => rfl
  | _, _, .snd, _, _, _ => rfl
  | _, _, .pair f g, s, o, h => Prod.ext (ceval_toDom hX f s o h) (ceval_toDom hX g s o h)
  | _, _, .unit _, _, _, _ => rfl
  | _, _, .func f args, s, o, h =>
      congrArg ((gw hM₀ s).canonFunc f) (funext fun k => ceval_toDom hX (args k) s o h)
  | _, _, .boxMap _, _, _, _ => rfl
  | _, _, .boxPair _ _, _, _, _ => rfl
  | _, _, .boxUnit, _, _, _ => rfl
  | _, _, .diaMap _, _, _, _ => rfl
  | _, _, .strength _ _, _, _, _ => rfl
  | _, _, .extract _, _, _, _ => rfl
  | _, _, .dup _, _, _, _ => rfl
  | _, _, .dkeep _, _, _, _ => rfl

/-! ## Strong D, and strong 4 -/

/-- ⭐Under strong D every world has a possible object of type `𝟙` with a nonempty extent: the
    root's Henkin witness for the axiom, whose extent has the child made for its witness
    (`glexX`), read at the world (R4). -/
theorem cposSerial (hX : CluFlags) (hDS : ModalSys.DStrong = true) (s : GW hF M₀) :
    ∃ p : (cframe hF hM₀ hX).Pos .VTypeOne s, Nonempty (cposEval hM₀ hX p).1 := by
  have hax : (WFF.somePoss : WFF σ ((gw hM₀ (groot hF M₀)).ctx 0) 0) ∈
      (gw hM₀ (groot hF M₀)).M 0 :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.D_ex hDS⟩
  obtain ⟨j, _, _, t, hmem⟩ := (gw hM₀ (groot hF M₀)).exW_term hax
  match t with
  | .diatm x hx u =>
      obtain ⟨X, hX'⟩ := id hx
      obtain ⟨t', ⟨c, hc⟩, hk, -, -, -⟩ := glexX hM₀ (groot hF M₀) j x X hX' .top (by
        have e : (WFF.instantiate Ctx.NoSlots.slots (Term.diatm x hx u)
            (WFF.mono ((ctxOf_le_of_suffix ((gw hM₀ (groot hF M₀)).suf (Nat.zero_le j))).insert
              (.bnd 0) (.VTypeDia .VTypeOne))
              (.dia (.root (.bnd 0)) ⟨.VTypeOne, Ctx.ref_insert_root _ (.bnd 0) _⟩ .top))) =
            WFF.dia x ⟨X, hX'⟩ .top := rfl
        rw [← e]
        exact hmem)
      have hR : CR t' := ⟨[c], .inl pathOk_cons, hc⟩
      refine ⟨⟨cden hM₀ hX (groot hF M₀) j (Ctx.Le.refl _) (.diatm x hx u),
          cdefinable_dia_of_root hX s _ (cdefinable_den hX _ _)⟩, ⟨⟨⟨t', ⟨hR⟩⟩, ?_⟩⟩⟩
      by_cases hT : ModalSys.T = true
      · have key : ∀ (P : List ℕ) (h : t'.1 = nodeOf (groot hF M₀).1 P), P = [c] →
            GMem hM₀ (groot hF M₀) t' P h x := by
          rintro _ h rfl
          exact .inl (grealised_wit hM₀ hT ⟨c, hc⟩ hk j hX')
        exact key _ _ (cpath_of hR hc)
      · exact .inr ⟨Bool.eq_false_iff.mpr hT, inExt_cpath hR (P := [c]) (h := hc) hk⟩

/-- ⭐**Strong 4 on the carriers**: along any arrow, an object of a liftable type at its end is
    the object itself kept at its source — definable there by R4. -/
theorem ckeepLift (hX : CluFlags) (hF' : ModalSys.Four = true) {T : VarType}
    (hl : T.liftable = true) {w : GW hF M₀} (a : (cframe hF hM₀ hX).Acc w)
    (o : (cframe hF hM₀ hX).Dom T a.1) :
    ∃ m : (cframe hF hM₀ hX).Dom T w,
      cnecEval hM₀ hX (GFunc.eval (cops hF hM₀ hX)
        (GFunc.keep (σ := σ) hF' (VarType.keepable_of_liftable hl)) w m) a = o := by
  match T, hl, o with
  | .VTypeBox A, _, o =>
      exact ⟨⟨o.1, (cdefinable_box_iff hX w o.1).mpr ((cdefinable_box_iff hX a.1 o.1).mp o.2)⟩,
        Subtype.ext rfl⟩
  | .VTypeDia A, _, o =>
      exact ⟨⟨o.1, (cdefinable_dia_iff hX w o.1).mpr ((cdefinable_dia_iff hX a.1 o.1).mp o.2)⟩,
        Subtype.ext rfl⟩
  | .Var, hl, _ => cases hl
  | .VTypeOne, hl, _ => cases hl
  | .VTypeProd _ _, hl, _ => cases hl

/-! ## The shapes of the operations -/

/-- When shaped, a frame object's shape is its raw object's. -/
theorem cdomShape_toDom (hX : CluFlags) (hSh : ModalSys.shaped = true) :
    ∀ (A : VarType) (s : GW hF M₀) (o : CRDom hM₀ A s) (h : CDefinable hM₀ hX A s o),
      Frame.domShape (cnecEval hM₀ hX) (fun q => (cposFull hM₀ hX q).2 hSh)
          (ctoDom hM₀ hX A s o h) = crawShape (hX.T_of_shaped hSh) o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, o, h =>
      congrArg₂ Shp.prod (cdomShape_toDom hX hSh A s o.1 (cdefinable_fst hX h))
        (cdomShape_toDom hX hSh C s o.2 (cdefinable_snd hX h))
  | .VTypeBox A, _, o, h =>
      congrArg Shp.box (congrArg Arrows.transposeShp (funext fun a =>
        cdomShape_toDom hX hSh A a.1 (o a) (cdefinable_box_apply hX h a)))
  | .VTypeDia _, _, _, _ => rfl

/-- A mapped possible object's shape. -/
theorem cdiaMap_shape (hX : CluFlags) (hT : ModalSys.T = true) {A B : VarType} (f : GFunc σ A B)
    {s : GW hF M₀} (p : CRDom hM₀ (.VTypeDia A) s) :
    crawShape hT (crawEval hM₀ hX (.diaMap f) s p) =
      .dia (crawShape hT p).label (GFunc.shp f 1 (crawShape hT p).body) := by
  change (Shp.dia (p.tag hT).label (GFunc.shp f 1 (p.tag hT).body)).map (CLeaf.rean s) =
    .dia ((p.tag hT).map (CLeaf.rean s)).label (GFunc.shp f 1 ((p.tag hT).map (CLeaf.rean s)).body)
  generalize p.tag hT = τ
  cases τ with
  | dia l a => exact congrArg (Shp.dia _) (shp_rean s f 0 a)

/-- A possible object's shape with a necessary object riding along. -/
theorem cstrength_shape (hX : CluFlags) (hT : ModalSys.T = true) {A B : VarType} {s : GW hF M₀}
    (n : CRDom hM₀ (.VTypeBox A) s) (p : CRDom hM₀ (.VTypeDia B) s) :
    crawShape hT (crawEval hM₀ hX (.strength A B) s
        ((n, p) : CRDom hM₀ (.VTypeProd (.VTypeBox A) (.VTypeDia B)) s)) =
      .dia (crawShape hT p).label
        (.prod (Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb) (w := s)
          fun a => crawShape hT (n a)) (crawShape hT p).body) := by
  change (Shp.dia (p.tag hT).label
      (.prod (Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb)
        (w := groot hF M₀) fun a => crawShape hT (n a)) (p.tag hT).body)).map (CLeaf.rean s) =
    .dia ((p.tag hT).map (CLeaf.rean s)).label
      (.prod (Arrows.transposeShp (F := carrows hF M₀) (Root := fun _ => VarSymb) (w := s)
        fun a => crawShape hT (n a)) ((p.tag hT).map (CLeaf.rean s)).body)
  generalize p.tag hT = τ
  cases τ with
  | dia l a =>
      change Shp.dia _ (Shp.prod _ _) = Shp.dia _ (Shp.prod _ _)
      rw [transpose_rean]
      rfl

/-- A possible object kept along an arrow has its shape moved along the arrow. -/
theorem ckeep_shape (hT : ModalSys.T = true) (hF' : ModalSys.Four = true) {A : VarType}
    {s : GW hF M₀} (a : (carrows hF M₀).Acc s) (p : CRDom hM₀ (.VTypeDia A) s) :
    crawShape hT (s := a.1) (A := .VTypeDia A) p =
      (crawShape hT (s := s) (A := .VTypeDia A) p).map (Arrows.Leaf.keepAlong hF' a) := by
  rw [Shp.map_congr (fun l => keepAlong_rean hF' a l)]
  exact (cshape_rean_rean _ _ _).symm

/-! ## Strong T, and indistinguishability -/

/-- ⭐**Canonical indistinguishability**: objects with representatives the world's theory cannot
    tell apart (`gInd`). -/
def cInd (hX : CluFlags) {A : VarType} {s : GW hF M₀} (o o' : (cframe hF hM₀ hX).Dom A s) : Prop :=
  ∃ u u' : Canon.DTerm (gw hM₀ s).sys (gw hM₀ s).T A,
    cden hM₀ hX s u.i (Ctx.Le.refl _) u.t = cfromDom hM₀ hX A s o ∧
      cden hM₀ hX s u'.i (Ctx.Le.refl _) u'.t = cfromDom hM₀ hX A s o' ∧ u.Rel u'

/-- Every object is definable, so it is related to itself. -/
theorem cInd_refl (hX : CluFlags) {A : VarType} {s : GW hF M₀} (o : (cframe hF hM₀ hX).Dom A s) :
    cInd hM₀ hX o o := by
  obtain ⟨i, a, t, ht⟩ := cdefinable_fromDom hM₀ hX A s o
  exact ⟨⟨i, a, t⟩, ⟨i, a, t⟩, ht, ht, Canon.DTerm.Rel.refl _⟩

variable {hM₀}

/-- A term and its lift to a later stage denote alike. -/
theorem cden_lift (hX : CluFlags) {s : GW hF M₀} {i K : ℕ} (h : i ≤ K) {A : VarType} {a : Ann A}
    (t : Term σ (ctxOf (glat s i)) A a) :
    cden hM₀ hX s K (Ctx.Le.refl _) (Term.mono (gle hM₀ s h) t) =
      cden hM₀ hX s i (Ctx.Le.refl _) t := by
  rw [cden_mono]
  exact cden_congr hX _ _ _ _ _ _

/-- ⭐The realised content of the witness's own content address is the datum's content. -/
theorem cden_grealT_eta (hX : CluFlags) {s : GW hF M₀} {x : VarSymb}
    (hr : (gw hM₀ s).Realised x) {k : ℕ}
    (hx : ∃ X, (ctxOf (glat s k)).ref x = some (.VTypeDia X))
    (hdia : ((ctxOf (glat s k)).diaIn x).ref (.step x .dia) = some hr.data.A) :
    cden hM₀ hX s _ (Ctx.Le.refl _)
        (grealT hr (Ctx.Le.refl _) hx (Term.eta (.step x .dia) hr.data.A hdia)).2 =
      cden hM₀ hX s hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀ := by
  have hdecl : (ctxOf (glat s (max k hr.data.i₀))).ref x = some (.VTypeDia hr.data.A) :=
    hr.data.hdeclOf _ (hx.imp fun _ h => (gle hM₀ s (le_max_left _ _)).ref h)
  have hmono : (⟨_, Term.mono (((Ctx.Le.refl _).trans (gle hM₀ s (le_max_left _ _))).diaIn x)
      (Term.eta (.step x .dia) hr.data.A hdia)⟩ : Σ z : Ann hr.data.A,
        Term σ ((ctxOf (glat s (max k hr.data.i₀))).diaIn x) hr.data.A z) =
      ⟨_, Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl)⟩ := by
    rw [Term.mono_eta]
  simp only [grealT]
  rw [cden_sigma hX _ (Canon.Term.realiseAtA_sigma hr.data.hT x hdecl _ hmono),
    cden_sigma hX _ (Term.realiseAtA_eta hr.data.hT x hdecl
      (Term.mono (gle hM₀ s (le_max_right _ _)) hr.data.t₀)),
    cden_mono]
  exact cden_congr hX _ _ _ _ _ _

variable (hM₀)

/-- ⭐**Strong T: every object of a domain is, up to `cInd`, the content along the world's own
    arrow of a possible object** (`gposRet_exists_canon`, the own arrow's content by
    `cden_own_content`). -/
theorem cposRet_exists (hX : CluFlags) {A : VarType} {s : GW hF M₀} (hT : ModalSys.T = true)
    (hS : ModalSys.TStrong = true) (o : (cframe hF hM₀ hX).Dom A s) :
    ∃ (p : (cframe hF hM₀ hX).Pos A s)
      (hm : (cframe hF hM₀ hX).reflAcc hT s ∈ (cposEval hM₀ hX p).1),
      cInd hM₀ hX ((cposEval hM₀ hX p).2 ⟨(cframe hF hM₀ hX).reflAcc hT s, hm⟩) o := by
  obtain ⟨i, a', t, ht⟩ := cdefinable_fromDom hM₀ hX A s o
  obtain ⟨i', hi, y, hy, hmem⟩ := (gw hM₀ s).retW hT hS i t
  have hr : (gw hM₀ s).Realised y :=
    (gw hM₀ s).datum_of_here hT hy (Term.eta (.step y .dia) A (Ctx.ref_diaIn_of hy)) _ hmem
  obtain rfl : hr.data.A = A := by
    have := (hr.data.hdeclOf i' ⟨A, hy⟩).symm.trans hy
    simpa using this
  have hR : CR s := (carrows hF M₀).refl hT s
  have hm := (cden_own_mem hX hM₀ hT s hr.data.i₀ hr.data.hd₀
    (Term.eta (.step y .dia) hr.data.A (Ctx.ref_diaIn_of hr.data.hd₀)) hR).mpr hr
  refine ⟨⟨cden hM₀ hX s hr.data.i₀ (Ctx.Le.refl _)
      (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀), cdefinable_den hX _ _⟩, hm, _,
      ⟨i', _, Term.mono (gle hM₀ s hi) t⟩, ?_, ?_,
      grel_here hT ⟨_, hy⟩ (Term.eta (.step y .dia) hr.data.A (Ctx.ref_diaIn_of hy)) _ hr hmem⟩
  · have hc : ctoDom hM₀ hX _ s (cden hM₀ hX s hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀)
        (cdefinable_den hX _ _) =
        (cposEval hM₀ hX ⟨cden hM₀ hX s hr.data.i₀ (Ctx.Le.refl _)
          (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀), cdefinable_den hX _ _⟩).2
          ⟨(cframe hF hM₀ hX).reflAcc hT s, hm⟩ :=
      ctoDom_congr hX (((cden_own_content hX hM₀ s hr.data.i₀ hr.data.hd₀ _ hR hm hr).trans
        (cden_grealT_eta hX hr ⟨_, hr.data.hd₀⟩ (Ctx.ref_diaIn_of hr.data.hd₀))).symm) _ _
    rw [cden_grealT_eta hX hr ⟨_, hy⟩ (Ctx.ref_diaIn_of hy), ← hc, cfromDom_toDom]
  · exact (cden_lift hX hi t).trans ht

/-! ## Comes back -/

/-- A carrier's round-trip data on the cluster frame (`Model.carrierData`). -/
noncomputable def cData (hX : CluFlags) : (L : BLeg) → {A : VarType} → {s : GW hF M₀} →
    (cframe hF hM₀ hX).Dom (L.carrier A) s →
    Σ S : Set ((cframe hF hM₀ hX).Acc s),
      (a : S) → (b : (cframe hF hM₀ hX).Acc a.1.1) → (cframe hF hM₀ hX).Dom A b.1
  | .nec, A, s, c =>
      ⟨Set.univ, fun a b => cnecEval hM₀ hX
        (cnecEval hM₀ hX (c : (cframe hF hM₀ hX).Nec (.VTypeBox A) s) a.1) b⟩
  | .pos, A, _, c =>
      ⟨(cposEval hM₀ hX (c : (cframe hF hM₀ hX).Pos (.VTypeBox A) _)).1,
        fun a b => cnecEval hM₀ hX
          ((cposEval hM₀ hX (c : (cframe hF hM₀ hX).Pos (.VTypeBox A) _)).2 a) b⟩

/-- A carrier's shape on the cluster frame (`Model.carrierTag`). -/
noncomputable def cTag (hX : CluFlags) : (L : BLeg) → {A : VarType} → {s : GW hF M₀} →
    (cframe hF hM₀ hX).Dom (L.carrier A) s →
    Option (Shp ((cframe hF hM₀ hX).Leaf (fun _ => VarSymb) s) (.VTypeDia (.VTypeBox A)))
  | .nec, _, _, _ => none
  | .pos, A, _, c =>
      if h : ModalSys.shaped = true then
        some (crawShape (hX.T_of_shaped h) (c : (cframe hF hM₀ hX).Pos (.VTypeBox A) _).1)
      else none

/-- The model's indistinguishability, before the model. -/
abbrev cIndM (hX : CluFlags) {A : VarType} {s : GW hF M₀} (o o' : (cframe hF hM₀ hX).Dom A s) :
    Prop :=
  (ModalSys.T = true → cInd hM₀ hX o o') ∧ (ModalSys.T = false → o = o')

/-- ⭐**Canonical "comes back as"**: the round trip, and at a `◇` content a `Back` atom of the theory
    with these data and this witness, as `BArrow`'s.  The round trip is part of the definition, so
    `Model.Ret_fwd` is free and the truth lemma's `Back` case proves it for an atom
    (`Proof.back_of_tie`). -/
def cRet (hX : CluFlags) {A : VarType} {s : GW hF M₀}
    (ℓ : Option (Shp ((cframe hF hM₀ hX).Leaf (fun _ => VarSymb) s) (.VTypeDia (.VTypeBox A))))
    (S : Set ((cframe hF hM₀ hX).Acc s))
    (val : (a : S) → (b : (cframe hF hM₀ hX).Acc a.1.1) → (cframe hF hM₀ hX).Dom A b.1)
    (o : (cframe hF hM₀ hX).Dom A s) : Prop :=
  Nonempty S ∧ (∀ a : S, ∃ r : (cframe hF hM₀ hX).R a.1.1 s, cIndM hM₀ hX (val a ⟨s, ⟨r⟩⟩) o) ∧
    (A.diaFree = true ∨ ∃ (hS : ModalSys.BStrong = true) (i : ℕ) (L : BLeg) (c : Ann (L.carrier A))
      (ct : Term σ (ctxOf (glat s i)) (L.carrier A) c) (a : Ann A)
      (t : Term σ (ctxOf (glat s i)) A a),
      WFF.back hS L ct t ∈ (gw hM₀ s).M i ∧
      cData hM₀ hX L (ctoDom hM₀ hX _ s (cden hM₀ hX s i (Ctx.Le.refl _) ct)
        (cdefinable_den hX _ _)) = ⟨S, val⟩ ∧
      cTag hM₀ hX L (ctoDom hM₀ hX _ s (cden hM₀ hX s i (Ctx.Le.refl _) ct)
        (cdefinable_den hX _ _)) = ℓ ∧
      ctoDom hM₀ hX A s (cden hM₀ hX s i (Ctx.Le.refl _) t) (cdefinable_den hX _ _) = o)

variable {hM₀} in
/-- ⭐A `□`-term's value along a world's own arrow is the term collapsed. -/
theorem cden_boxtm_own (hX : CluFlags) (hT : ModalSys.T = true) (s : GW hF M₀) (i : ℕ)
    {A : VarType} {a : Ann A} (b : Term σ (ctxOf (glat s i)).boxIn A a)
    (hR : CR s) :
    cden hM₀ hX s i (Ctx.Le.refl _) (.boxtm b) ⟨s, ⟨hR⟩⟩ =
      cden hM₀ hX s i (Ctx.Le.refl _) (Term.collapse (Ctx.collapses_boxIn_self hT _) b) := by
  simp only [cden]
  rw [dif_pos (cpathOk hT _), cden_collapse hX hM₀ hT s i, Term.mono_refl]

/-- ⭐**Every object comes back** (`Model.backRet_exists`): `B_strong`'s carrier names a value, and
    the kept carrier of that value (`Proof.back_kept`) makes the round trip on raw objects, a kept
    object being read along an arrow as itself (`cden_applyG`).  An atom's round trip needs the
    truth lemma; a kept carrier's does not. -/
theorem cbackRet_exists (hX : CluFlags) (hS : ModalSys.BStrong = true) {A : VarType}
    {s : GW hF M₀} (o : (cframe hF hM₀ hX).Dom A s) :
    ∃ c : (cframe hF hM₀ hX).Nec (.VTypeBox A) s,
      cRet hM₀ hX none (Set.univ : Set ((cframe hF hM₀ hX).Acc s))
        (fun a b => cnecEval hM₀ hX (cnecEval hM₀ hX c a.1) b) o := by
  have hT := hX.bT hS
  obtain ⟨i, a, t, ht⟩ := cdefinable_fromDom hM₀ hX A s o
  have hdia : (OutLeg.nec : OutLeg (ctxOf (glat s i))).dia (.top : WFF σ _ 0) ∈ (gw hM₀ s).M i :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => absurd h List.not_mem_nil) ⟨Proof.dia_top hT⟩
  have hex : BData.WFF.backEx hS t ∈ (gw hM₀ s).M i :=
    BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hdia)
      ⟨BData.Proof.backEx hS t _ (ctxOf_fresh le_rfl) (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨j, hij, cb, c, hm⟩ := (gw hM₀ s).exW_term hex
  have hm' : WFF.back hS .nec c (Term.mono (gle hM₀ s hij) t) ∈ (gw hM₀ s).M j := by
    convert hm using 1
    refine Eq.symm ((congrArg (WFF.instantiate _ _) ?_).trans
      (BData.WFF.instantiate_backAt_slot hS (Term.mono (gle hM₀ s hij) t) _))
    refine WFF.back_congr' hS .nec (Term.mono_eta _ _ _ _) ?_
    simp only [Term.mono_mono]
  clear hm
  match cb, c, hm' with
  | _, .boxtm (.boxtm v), hm' =>
    let n := Term.collapse (Ctx.collapses_boxIn_self hT _) v
    let κ := Term.boxtm (Term.boxtm (Term.shift (Ctx.shifts_boxIn_boxIn hF _) n))
    have hk : WFF.back hS .nec κ (Term.mono (gle hM₀ s hij) t) ∈ (gw hM₀ s).M j :=
      BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
        rw [List.mem_singleton.mp hψ]; exact hm')
        ⟨Proof.back_kept hS hT hF v _ (Proof.lookup List.mem_cons_self)⟩
    have hrel := BWorld.back_here_rel (gw hM₀ s) hS hT v _ hm'
    have hκ : cden hM₀ hX s j (Ctx.Le.refl _) κ =
        fun _ => cden hM₀ hX s j (Ctx.Le.refl _) (Term.boxtm n) :=
      cden_applyG hX (.dup hF) (Term.boxtm n) s j (Ctx.Le.refl _)
    have hR : CR s := (carrows hF M₀).refl hT s
    have hval : cden hM₀ hX s j (Ctx.Le.refl _) (Term.mono (gle hM₀ s hij) t) =
        cfromDom hM₀ hX A s o := (cden_lift hX hij t).trans ht
    refine ⟨⟨_, cdefinable_den hX _ _⟩, ⟨⟨⟨⟨s, ⟨hR⟩⟩, trivial⟩⟩, fun b => ⟨hR, ?_⟩,
      .inr ⟨hS, j, .nec, _, κ, _, _, hk, rfl, rfl,
        (ctoDom_congr hX hval _ _).trans (ctoDom_fromDom hM₀ hX A s o)⟩⟩⟩
    refine ⟨fun _ => ⟨⟨j, _, Term.collapse (Ctx.collapses_boxIn_self hT _) n⟩,
      ⟨j, _, Term.mono (gle hM₀ s hij) t⟩, ?_, hval, hrel⟩,
      fun hnT => absurd (hT.symm.trans hnT) (by decide)⟩
    change _ = cfromDom hM₀ hX A s (ctoDom hM₀ hX A s _ _)
    rw [cfromDom_toDom]
    exact (cden_boxtm_own hX hT s j n hR).symm.trans (congrFun (congrFun hκ.symm b.1) ⟨s, ⟨hR⟩⟩)

/-- ⭐**Witnessed ways home are free** (`Model.posBack_exists`): strong T's realiser at the target,
    the same possible object at the source, carriers being shared (R4). -/
theorem cposBack_exists (hX : CluFlags) (hS : ModalSys.BStrong = true)
    (hW : ModalSys.BStrongW = true) {A : VarType} {w v : GW hF M₀}
    (b : (cframe hF hM₀ hX).R v w) (o : (cframe hF hM₀ hX).Dom A w) :
    ∃ (p : (cframe hF hM₀ hX).Pos A v)
      (hm : (⟨w, ⟨b⟩⟩ : (cframe hF hM₀ hX).Acc v) ∈ (cposFull hM₀ hX p).1.1),
      cIndM hM₀ hX ((cposFull hM₀ hX p).1.2 ⟨⟨w, ⟨b⟩⟩, hm⟩) o := by
  have hT := hX.bT hS
  obtain ⟨p, hm, hp⟩ := cposRet_exists hM₀ hX hT (hX.bW hS hW) o
  exact ⟨⟨p.1, (cdefinable_dia_iff hX v p.1).mpr ((cdefinable_dia_iff hX w p.1).mp p.2)⟩, hm,
    fun _ => hp, fun hnT => absurd (hT.symm.trans hnT) (by decide)⟩

/-! ## The model -/

variable (hF) in
/-- ⭐**The cluster model** (5 and both lifts of 4 on; T and D either way; weak B under T). -/
noncomputable def cmodel (hX : CluFlags) : Model.{0, 0} σ where
  frame := cframe hF hM₀ hX
  necEval := cnecEval hM₀ hX
  nec_inj := fun h => cnecEval_injective hM₀ hX h
  RootPoss _ := VarSymb
  rootKeep := (instRootKeepC hF M₀).keep
  rootKeepLaws := instRootKeepLawsC hF M₀
  posFull p := cposFull hM₀ hX p
  posFull_inj := fun h => cposFull_injective hM₀ hX h
  posShape_wf := fun hS {_} {_} p => cposShape_wf hM₀ hX (hX.T_of_shaped hS) p
  ops := cops hF hM₀ hX
  necMap_eval g _ a := (ceval_toDom hM₀ hX g a.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_full g _ := Prod.ext
    (congrArg (Sigma.mk _) (funext fun a => (ceval_toDom hM₀ hX g a.1.1 _ _).symm))
    (funext fun hS => cdiaMap_shape hM₀ hX (hX.T_of_shaped hS) g _)
  posStrength_full n p := Prod.ext rfl (funext fun hS =>
    (cstrength_shape hM₀ hX (hX.T_of_shaped hS) n.1 p.1).trans
      (congrArg (fun z => Shp.dia _ (Shp.prod z _)) (congrArg Arrows.transposeShp (funext fun s =>
        (cdomShape_toDom hM₀ hX hS _ s.1 (n.1 s) (cdefinable_box_apply hX n.2 s)).symm))))
  necExtract_eval _ _ := rfl
  necDup_eval _ _ _ _ := rfl
  keepLift hF' _ hl _ a o := ckeepLift hM₀ hX hF' hl a o
  posKeep_full hF' x a := Prod.ext rfl (funext fun hS =>
    ckeep_shape (hM₀ := hM₀) (hX.T_of_shaped hS) hF' a x.1)
  posSide_ext _ x _ := by
    ext b
    exact ⟨fun hb => ⟨b, hb, rfl⟩, fun ⟨c, hc, e⟩ => by rw [← e]; exact hc⟩
  posSide_content _ _ _ _ _ _ := rfl
  posSerial hDS s := cposSerial hM₀ hX hDS s
  Ind o o' := (ModalSys.T = true → cInd hM₀ hX o o') ∧ (ModalSys.T = false → o = o')
  Ind_refl o := ⟨fun _ => cInd_refl hM₀ hX o, fun _ => rfl⟩
  necSide_exists _ _ {_} {w} a n :=
    ⟨⟨n.1, (cdefinable_box_iff hX w n.1).mpr ((cdefinable_box_iff hX a.1 n.1).mp n.2)⟩,
      fun _ => ⟨fun _ => cInd_refl hM₀ hX _, fun _ => rfl⟩⟩
  posRet_exists hT hS a := by
    obtain ⟨p, hm, hp⟩ := cposRet_exists hM₀ hX hT hS a
    exact ⟨p, hm, fun _ => hp, fun hT' => absurd (hT.symm.trans hT') (by decide)⟩
  Ret ℓ S val o := cRet hM₀ hX ℓ S val o
  Ret_fwd _ _ _ _ _ h := ⟨h.1, h.2.1⟩
  Ret_conv _ hA _ _ _ _ h := ⟨h.1, h.2, .inl hA⟩
  backRet_exists hS _ o := cbackRet_exists hM₀ hX hS o
  posBack_exists hS hW b o := cposBack_exists hM₀ hX hS hW b o

end GArrow

end V12M
