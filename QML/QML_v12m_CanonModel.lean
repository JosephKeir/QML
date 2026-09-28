import QML.QML_v12m_CanonFunc
import QML.QML_v12m_CanonExist

/-!
# QML v12m — the canonical model

The **frame**: the worlds, accessibility (reflexive under T, serial under D — every world has a
successor, `exists_succ`, which is why the frame needs a countable signature), the base domains,
and as carriers the definable raw objects (`Nec A w`, `Pos A w`).  A frame object of any type
corresponds to a definable raw object (`toDom`, `fromDom`); a necessary object evaluates at each
successor to its raw value there, a possible one to its extent with its raw contents.  Evaluation
is injective because the correspondence is.  The function algebra acts by raw evaluation (`ops`),
and evaluating a map on a frame object is evaluating it on the raw object (`eval_toDom`), which
gives the evaluation laws.

⭐`Canon.model w₀`: the canonical model, pointed at `w₀`.
-/

namespace V12M

variable [ModalSys]

namespace Canon

variable {σ : Signature} {N₀ : ℕ}

-- Seriality under D needs a successor for every world, which is a Henkin construction, so the
-- canonical frame is built over a countable signature — the setting of completeness anyway.
variable [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoB]

/-- ⭐The canonical frame, pointed at a world. -/
noncomputable def frame (w₀ : World σ N₀) : Frame.{0, 0} σ where
  W := World σ N₀
  actual := w₀
  R := Canon.R
  refl := fun hT w => R.refl hT w
  trans := fun hF => R.trans hF
  serial := fun hD w => (exists_succ hD w).imp fun _ ha => ⟨R.of_acc ha⟩
  symm := fun hB => (ModalSys.NoB.absurd hB).elim
  refl_trans := fun _ _ _ _ _ => rfl
  trans_refl := fun _ _ _ _ _ => rfl
  trans_assoc := fun _ _ _ _ _ _ _ _ => rfl
  D w := w.D
  Nec A w := {o : RDom (.VTypeBox A) w // Definable (.VTypeBox A) w o}
  Pos A w := {o : RDom (.VTypeDia A) w // Definable (.VTypeDia A) w o}
  funcInterp f w args := canonFunc w f args
  relInterp r w args := canonRel w r args

variable (w₀ : World σ N₀)

/-- A definable raw object as a frame object. -/
def toDom : (A : VarType) → (w : World σ N₀) → (o : RDom A w) → Definable A w o →
    (frame w₀).Dom A w
  | .Var, _, o, _ => o
  | .VTypeOne, _, _, _ => PUnit.unit
  | .VTypeProd A B, w, o, h =>
      (toDom A w o.1 (definable_fst h), toDom B w o.2 (definable_snd h))
  | .VTypeBox A, w, o, h =>
      (Subtype.mk o h : {o : RDom (.VTypeBox A) w // Definable (.VTypeBox A) w o})
  | .VTypeDia A, w, o, h =>
      (Subtype.mk o h : {o : RDom (.VTypeDia A) w // Definable (.VTypeDia A) w o})

/-- A frame object as a raw object. -/
def fromDom : (A : VarType) → (w : World σ N₀) → (frame w₀).Dom A w → RDom A w
  | .Var, _, d => d
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A B, w, d =>
      (fromDom A w (d : (frame w₀).Dom A w × (frame w₀).Dom B w).1,
        fromDom B w (d : (frame w₀).Dom A w × (frame w₀).Dom B w).2)
  | .VTypeBox A, w, d =>
      (d : {o : RDom (.VTypeBox A) w // Definable (.VTypeBox A) w o}).1
  | .VTypeDia A, w, d =>
      (d : {o : RDom (.VTypeDia A) w // Definable (.VTypeDia A) w o}).1

theorem definable_fromDom : ∀ (A : VarType) (w : World σ N₀) (d : (frame w₀).Dom A w),
    Definable A w (fromDom w₀ A w d)
  | .Var, _, d => definable_var d
  | .VTypeOne, _, _ => definable_unit _
  | .VTypeProd A B, w, d =>
      definable_pair (definable_fromDom A w (d : (frame w₀).Dom A w × (frame w₀).Dom B w).1)
        (definable_fromDom B w (d : (frame w₀).Dom A w × (frame w₀).Dom B w).2)
  | .VTypeBox A, w, d => (d : {o : RDom (.VTypeBox A) w // Definable (.VTypeBox A) w o}).2
  | .VTypeDia A, w, d => (d : {o : RDom (.VTypeDia A) w // Definable (.VTypeDia A) w o}).2

theorem fromDom_toDom : ∀ (A : VarType) (w : World σ N₀) (o : RDom A w) (h : Definable A w o),
    fromDom w₀ A w (toDom w₀ A w o h) = o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A B, w, o, h =>
      Prod.ext (fromDom_toDom A w o.1 (definable_fst h)) (fromDom_toDom B w o.2 (definable_snd h))
  | .VTypeBox _, _, _, _ => rfl
  | .VTypeDia _, _, _, _ => rfl

theorem toDom_fromDom : ∀ (A : VarType) (w : World σ N₀) (d : (frame w₀).Dom A w),
    toDom w₀ A w (fromDom w₀ A w d) (definable_fromDom w₀ A w d) = d
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A B, w, d =>
      Prod.ext (toDom_fromDom A w (d : (frame w₀).Dom A w × (frame w₀).Dom B w).1)
        (toDom_fromDom B w (d : (frame w₀).Dom A w × (frame w₀).Dom B w).2)
  | .VTypeBox _, _, _ => rfl
  | .VTypeDia _, _, _ => rfl

theorem toDom_inj {A : VarType} {w : World σ N₀} {o o' : RDom A w} {h : Definable A w o}
    {h' : Definable A w o'} (e : toDom w₀ A w o h = toDom w₀ A w o' h') : o = o' := by
  rw [← fromDom_toDom w₀ A w o h, ← fromDom_toDom w₀ A w o' h', e]

theorem toDom_congr {A : VarType} {w : World σ N₀} {o o' : RDom A w} (e : o = o')
    (h : Definable A w o) (h' : Definable A w o') : toDom w₀ A w o h = toDom w₀ A w o' h' := by
  subst e
  rfl

/-- Evaluation of necessary objects. -/
def necEval {A : VarType} {w : World σ N₀} (n : (frame w₀).Nec A w) :
    (frame w₀).NecSec A w :=
  fun w' => toDom w₀ A w'.1 (n.1 w') (definable_box_apply n.2 w')

/-- Evaluation of possible objects. -/
def posEval {A : VarType} {w : World σ N₀} (p : (frame w₀).Pos A w) :
    (frame w₀).PosSec A w :=
  ⟨p.1.1, fun w' => toDom w₀ A w'.1.1 (p.1.2 w') (definable_dia_apply p.2 w')⟩

theorem necEval_injective {A : VarType} {w : World σ N₀} :
    Function.Injective (necEval w₀ (A := A) (w := w)) := by
  intro n n' h
  apply Subtype.ext
  funext w'
  exact toDom_inj w₀ (congrFun h w')

theorem posEval_injective {A : VarType} {w : World σ N₀} :
    Function.Injective (posEval w₀ (A := A) (w := w)) := by
  rintro ⟨⟨E, c⟩, hp⟩ ⟨⟨E', c'⟩, hp'⟩ h
  simp only [posEval] at h
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h
  have hc' := eq_of_heq hc
  apply Subtype.ext
  exact congrArg (Sigma.mk E) (funext fun w' => toDom_inj w₀ (congrFun hc' w'))

/-- The function algebra on the carriers. -/
noncomputable def ops : (frame w₀).Ops where
  necMap g n := ⟨rawEval (.boxMap g) _ n.1, definable_rawEval (.boxMap g) n.2⟩
  necPair a b := ⟨rawEval (.boxPair _ _) _
      ((a.1, b.1) : RDom (.VTypeProd (.VTypeBox _) (.VTypeBox _)) _),
    definable_rawEval (.boxPair _ _) (definable_pair a.2 b.2)⟩
  necUnit := ⟨rawEval .boxUnit _ (PUnit.unit : RDom .VTypeOne _),
    definable_rawEval .boxUnit (definable_unit _)⟩
  posMap g p := ⟨rawEval (.diaMap g) _ p.1, definable_rawEval (.diaMap g) p.2⟩
  posStrength n p := ⟨rawEval (.strength _ _) _
      ((n.1, p.1) : RDom (.VTypeProd (.VTypeBox _) (.VTypeDia _)) _),
    definable_rawEval (.strength _ _) (definable_pair n.2 p.2)⟩
  necExtract hT n :=
    toDom w₀ _ _ (rawEval (.extract hT) _ n.1) (definable_rawEval (.extract hT) n.2)
  necDup hF n := ⟨rawEval (.dup hF) _ n.1, definable_rawEval (.dup hF) n.2⟩

/-- ⭐Evaluating a map on a frame object is evaluating it on the raw object. -/
theorem eval_toDom : ∀ {A B : VarType} (g : GFunc σ A B) (w : World σ N₀) (o : RDom A w)
    (h : Definable A w o),
    GFunc.eval (ops w₀) g w (toDom w₀ A w o h) =
      toDom w₀ B w (rawEval g w o) (definable_rawEval g h)
  | _, _, .id _, _, _, _ => rfl
  | _, _, .comp g f, w, o, h =>
      (congrArg (GFunc.eval (ops w₀) g w) (eval_toDom f w o h)).trans (eval_toDom g w _ _)
  | _, _, .fst, _, _, _ => rfl
  | _, _, .snd, _, _, _ => rfl
  | _, _, .pair f g, w, o, h => Prod.ext (eval_toDom f w o h) (eval_toDom g w o h)
  | _, _, .unit _, _, _, _ => rfl
  | _, _, .func f args, w, o, h =>
      congrArg (canonFunc w f) (funext fun k => eval_toDom (args k) w o h)
  | _, _, .boxMap _, _, _, _ => rfl
  | _, _, .boxPair _ _, _, _, _ => rfl
  | _, _, .boxUnit, _, _, _ => rfl
  | _, _, .diaMap _, _, _, _ => rfl
  | _, _, .strength _ _, _, _, _ => rfl
  | _, _, .extract _, _, _, _ => rfl
  | _, _, .dup _, _, _, _ => rfl

/-! ## Strong D: some possible object has a nonempty extent -/

/-- ⭐Under strong D every world has a possible object of type `𝟙` with a nonempty extent: the
    witness `z` of `exists_extent`, with the unit as content.  Its raw extent is `extent w z` by
    `rden`'s definition. -/
theorem posSerial_canon (hDS : ModalSys.DStrong = true) (w : World σ N₀) :
    ∃ p : (frame w₀).Pos .VTypeOne w, Nonempty (posEval w₀ p).1 := by
  obtain ⟨i, z, hz, w', hw'⟩ := exists_extent hDS w
  exact ⟨⟨rden w i (Ctx.Le.refl _) (Term.diatm z hz .unit), definable_rden _ _⟩, ⟨⟨w', hw'⟩⟩⟩

/-! ## Strong T: every object is the content of a possible object here -/

/-- ⭐Every object of a domain is the content, at the world itself, of a possible object.  Naming
    (`Canon.exists_name`) turns a term denoting the object into a **declared address** denoting it,
    and the world realises some witness by that address (`World.realW`).  The possible object is
    that witness's η-expansion; `self_mem_extent` puts the world in its extent and
    `rden_eta_of_real` says its content there is what the address denotes. -/
theorem posRet_exists_canon {A : VarType} {w : World σ N₀} (hT : ModalSys.T = true)
    (hS : ModalSys.TStrong = true) (hA : A.diaFree = true) (a : (frame w₀).Dom A w) :
    ∃ (p : (frame w₀).Pos A w) (hm : (frame w₀).reflAcc hT w ∈ (posEval w₀ p).1),
      (posEval w₀ p).2 ⟨(frame w₀).reflAcc hT w, hm⟩ = a := by
  obtain ⟨i, a', t, ht⟩ := definable_fromDom w₀ A w a
  obtain ⟨i₁, -, c', hc', hname⟩ := exists_name hA t
  obtain ⟨c, d, hsome, hdA, hdb, hile⟩ := w.realW hT hS i₁ hA (.root (.free c')) hc'
  subst hdA
  have hr := World.realised_of_real hsome
  have hdecl : (w.L.ctx (d.i₀.1, d.i₀.2 + 1)).ref (.root (.free c)) = some (.VTypeDia d.A) :=
    d.hdecl _ (Nat.lt_succ_self _)
  refine ⟨⟨rden w (d.i₀.1, d.i₀.2 + 1) (Ctx.Le.refl _)
      (Term.eta (.root (.free c)) (.VTypeDia d.A) hdecl), definable_rden _ _⟩,
    self_mem_extent hr, ?_⟩
  refine Eq.trans ?_ (toDom_fromDom w₀ d.A w a)
  refine toDom_congr w₀ ?_ _ _
  rw [← ht]
  refine (rden_eta_of_real hsome hdecl).trans (Eq.trans ?_ hname)
  refine (rden_sigma (Ctx.Le.refl _) (Term.eta_congr hdb d.A d.hb₀ (hdb ▸ d.hb₀))).trans ?_
  exact (rden_eta_le (w.L.ctx_le hile) (Ctx.Le.refl _) (Ctx.Le.refl _)
    (.root (.free c')) d.A hc' ((w.L.ctx_le hile).ref hc')).symm


/-- ⭐The canonical model. -/
noncomputable def model : Model.{0, 0} σ where
  frame := frame w₀
  necEval := necEval w₀
  nec_inj := fun h => necEval_injective w₀ h
  posEval := posEval w₀
  pos_inj := fun h => posEval_injective w₀ h
  ops := ops w₀
  necMap_eval g _ w' := (eval_toDom w₀ g w'.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_eval g _ := congrArg (Sigma.mk _) (funext fun w' => (eval_toDom w₀ g w'.1.1 _ _).symm)
  posStrength_eval _ _ := rfl
  necExtract_eval _ _ := rfl
  necDup_eval _ _ _ _ := rfl
  posRet_exists hT hS hA a := posRet_exists_canon w₀ hT hS hA a
  posSerial hDS w := posSerial_canon w₀ hDS w

end Canon

end V12M
