import QML.QML_v12m_CanonFunc
import QML.QML_v12m_CanonExist
import QML.QML_v12m_CanonInterch

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

/-- ⭐**A `Here` atom about a possible object makes its witness realised.**  `here_beta` at the unit
    reduces the atom to realisedness, `here_name` names the witness's content, and the witnessed
    theory declares the name: a `RealDatum`. -/
theorem realised_of_here (hT : ModalSys.T = true) {w : World σ N₀} {x : VarSymb} {i : ℕ × ℕ}
    {X : VarType} (hx : (w.L.ctx i).ref x = some (.VTypeDia X)) {B : VarType} {β : Ann B}
    (bd : Term σ ((w.L.ctx i).diaIn x) B β) {a : Ann B} (t : Term σ (w.L.ctx i) B a)
    (h : (⟨i, WFF.here hT (Term.diatm x ⟨X, hx⟩ bd) t⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    w.Realised x :=
  w.realised_of_datum (datum_of_here w.exW hT hx bd t h).some

-- Seriality under D needs a successor for every world, which is a Henkin construction, so the
-- canonical frame is built over a countable signature — the setting of completeness anyway.
variable [Countable σ.FuncSyms] [Countable σ.RelSyms] [ModalSys.NoB]

/-- ⭐The canonical frame, pointed at a world. -/
noncomputable def frame (w₀ : World σ N₀) : Frame.{0, 0} σ where
  toArrows := arrows σ N₀
  actual := w₀
  serial := fun hD w => (exists_succ hD w).imp fun _ ha => ⟨R.of_acc ha⟩
  symm := fun hB => (ModalSys.NoB.absurd hB).elim
  homeUnique := fun _ => ⟨fun _ _ => rfl⟩
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

/-- ⭐Evaluation of possible objects, in full: the section and, under T, the stored shape. -/
def posFull {A : VarType} {w : World σ N₀} (p : (frame w₀).Pos A w) :
    (frame w₀).PosSec A w × (ModalSys.T = true → CShape w (.VTypeDia A)) :=
  (posEval w₀ p, p.1.3)

/-- A possible object is its section and, under T, its shape. -/
theorem posFull_injective {A : VarType} {w : World σ N₀} :
    Function.Injective (posFull w₀ (A := A) (w := w)) := by
  rintro ⟨⟨E, c, τ⟩, hp⟩ ⟨⟨E', c', τ'⟩, hp'⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [posFull] at h₁ h₂
  simp only [posEval] at h₁
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h₁
  have hc' := eq_of_heq hc
  apply Subtype.ext
  exact RPos.congr_cont (funext fun w' => toDom_inj w₀ (congrFun hc' w')) (congrFun h₂)

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

/-- Under T, a frame object's shape is its raw object's. -/
theorem domShape_toDom (hT : ModalSys.T = true) : ∀ (A : VarType) (w : World σ N₀)
    (o : RDom A w) (h : Definable A w o),
    Frame.domShape (necEval w₀) (fun q => (posFull w₀ q).2 hT) (toDom w₀ A w o h) = rawShape hT o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A B, w, o, h =>
      congrArg₂ Shp.prod (domShape_toDom hT A w o.1 (definable_fst h))
        (domShape_toDom hT B w o.2 (definable_snd h))
  | .VTypeBox A, _, o, h =>
      congrArg Shp.box (congrArg Arrows.transposeShp (funext fun s =>
        domShape_toDom hT A s.1 (o s) (definable_box_apply h s)))
  | .VTypeDia _, _, _, _ => rfl

/-! ## Strong D: some possible object has a nonempty extent -/

/-- ⭐Under strong D every world has a possible object of type `𝟙` with a nonempty extent: the
    witness `z` of `exists_extent`, with the unit as content.  Its raw extent is `extent w z` by
    `rden`'s definition. -/
theorem posSerial_canon (hDS : ModalSys.DStrong = true) (w : World σ N₀) :
    ∃ p : (frame w₀).Pos .VTypeOne w, Nonempty (posEval w₀ p).1 := by
  obtain ⟨i, z, hz, w', hw'⟩ := exists_extent hDS w
  exact ⟨⟨rden w i (Ctx.Le.refl _) (Term.diatm z hz .unit), definable_rden _ _⟩, ⟨⟨w', hw'⟩⟩⟩

/-! ## Strong T: every object is the content of a possible object here -/

/-- ⭐**Canonical indistinguishability** (docs §10.33): two objects with representatives the theory
    cannot tell apart (`DTerm.Rel`) — co-named possible objects over different witnesses are
    related without being equal. -/
def Ind {A : VarType} {w : World σ N₀} (o o' : (frame w₀).Dom A w) : Prop :=
  ∃ s s' : DTerm w.L.sys w.T A, rden w s.i (Ctx.Le.refl _) s.t = fromDom w₀ A w o ∧
    rden w s'.i (Ctx.Le.refl _) s'.t = fromDom w₀ A w o' ∧ s.Rel s'

/-- Every object is definable, so it is related to itself. -/
theorem Ind_refl {A : VarType} {w : World σ N₀} (o : (frame w₀).Dom A w) : Ind w₀ o o := by
  obtain ⟨i, a, t, ht⟩ := definable_fromDom w₀ A w o
  exact ⟨⟨i, a, t⟩, ⟨i, a, t⟩, ht, ht, DTerm.Rel.refl _⟩

/-- ⭐**Every object of a domain is, up to `Ind`, the content at the world itself of a possible
    object** — at every type, `◇` included (§10.41).  The object is some term's denotation; the
    theory has a `Here` atom for that term about some witness (`World.retW`), which makes the
    witness realised (`realised_of_here`); the witness's η-expansion has the world in its extent
    (`self_mem_extent`) with the realised datum's content there (`rden_eta_realised`); and that
    content is co-named with the term (the datum's own atom and the chain's), so the two have
    related representatives (`DTerm.rel_of_coname`).  No naming, so no `◇`-freeness. -/
theorem posRet_exists_canon {A : VarType} {w : World σ N₀} (hT : ModalSys.T = true)
    (hS : ModalSys.TStrong = true) (a : (frame w₀).Dom A w) :
    ∃ (p : (frame w₀).Pos A w) (hm : (frame w₀).reflAcc hT w ∈ (posEval w₀ p).1),
      Ind w₀ ((posEval w₀ p).2 ⟨(frame w₀).reflAcc hT w, hm⟩) a := by
  obtain ⟨i, a', t, ht⟩ := definable_fromDom w₀ A w a
  obtain ⟨i', hi, y, hy, hmem⟩ := w.retW hT hS i t
  have hr : w.Realised y :=
    realised_of_here hT hy (Term.eta (.step y .dia) A (Ctx.ref_diaIn_of hy)) _ hmem
  obtain rfl : hr.data.A = A := by
    have := (hr.data.hdeclOf i' ⟨A, hy⟩).symm.trans hy
    simpa using this
  -- both atoms at one stage, about one subject
  set K := hr.data.i₀ ⊔ i'
  have hdK : (w.L.ctx K).ref y = some (.VTypeDia hr.data.A) :=
    (w.L.ctx_le (le_sup_right : i' ≤ K)).ref hy
  have h₁ := hr.data.hhereAt w.mcs K le_sup_left hdK
  have h₂ := (World.mem_lift (w := w) (le_sup_right : i' ≤ K)).mp hmem
  rw [WFF.mono_hereAt_of_le hT _ _ _ hdK, Term.mono_mono] at h₂
  have hrel := DTerm.rel_of_coname hT _ h₁ h₂
  have hiK : i ≤ K := hi.trans le_sup_right
  refine ⟨⟨rden w hr.data.i₀ (Ctx.Le.refl _) (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀),
      definable_rden _ _⟩, self_mem_extent hr,
    ⟨hr.data.i₀, _, hr.data.t₀⟩, ⟨i, a', t⟩, ?_, ht, ?_⟩
  · have hc : toDom w₀ _ w (rden w hr.data.i₀ (Ctx.Le.refl _) hr.data.t₀) (definable_rden _ _) =
        (posEval w₀ ⟨rden w hr.data.i₀ (Ctx.Le.refl _)
          (Term.eta y (.VTypeDia hr.data.A) hr.data.hd₀), definable_rden _ _⟩).2
          ⟨(frame w₀).reflAcc hT w, self_mem_extent hr⟩ :=
      toDom_congr w₀ (rden_eta_realised hr hr.data.hd₀).symm _ _
    rw [← hc, fromDom_toDom]
  · exact (DTerm.rel_lift _ le_sup_left).trans
      (hrel.trans (DTerm.rel_lift (⟨i, a', t⟩ : DTerm w.L.sys w.T _) hiK).symm)

/-- ⭐The canonical model. -/
noncomputable def model : Model.{0, 0} σ where
  frame := frame w₀
  necEval := necEval w₀
  nec_inj := fun h => necEval_injective w₀ h
  RootPoss _ := VarSymb
  posFull p := ((posFull w₀ p).1, fun hSh => (posFull w₀ p).2 (ModalSys.NoB.T_of_shaped hSh))
  posFull_inj := fun h => posFull_injective w₀ (Prod.ext (congrArg Prod.fst h :)
    (funext fun hT => congrFun (congrArg Prod.snd h) (ModalSys.shaped_of_T hT)))
  ops := ops w₀
  necMap_eval g _ w' := (eval_toDom w₀ g w'.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_full g _ := Prod.ext
    (congrArg (Sigma.mk _) (funext fun w' => (eval_toDom w₀ g w'.1.1 _ _).symm)) rfl
  posStrength_full n _ := Prod.ext rfl (funext fun hSh =>
    congrArg (fun z => Shp.dia _ (Shp.prod z _)) (congrArg Arrows.transposeShp (funext fun s =>
      (domShape_toDom w₀ (ModalSys.NoB.T_of_shaped hSh) _ s.1 (n.1 s)
        (definable_box_apply n.2 s)).symm)))
  necExtract_eval _ _ := rfl
  necDup_eval _ _ _ _ := rfl
  posRet_exists hT hS a := posRet_exists_canon w₀ hT hS a
  posSerial hDS w := posSerial_canon w₀ hDS w
  backRet_exists hS := (ModalSys.NoB.absurdStrong hS).elim
  Ind o o' := Ind w₀ o o'
  Ind_refl o := Ind_refl w₀ o

end Canon

end V12M
