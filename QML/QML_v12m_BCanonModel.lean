import QML.QML_v12m_BCanonFunc

/-!
# QML v12m — B's canonical model: the model

The frame of `BData`: its worlds, its symmetric accessibility (so the frame condition for B holds
by construction), serial under D (from `ex` at `□⊥`), the base domains, and as carriers the
definable raw objects.  The model evaluates them as raw objects; the function algebra acts by
`rawEval`.  Strong D's condition comes from its axiom, a Henkin witness and `exX`
(`posSerial_canon`).

⭐`BData.model`: the canonical model.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoTFour] (B : BData σ)

/-- Under D every world has an arrow out: `□⊥` fails, since `D_box` refutes it. -/
theorem serial_canon (hD : ModalSys.D = true) (s : B.W) : ∃ t, Nonempty (B.R s t) := by
  have hnot : WFF.box (.bot : WFF σ ((B.w s).ctx 0).boxIn 0) ∉ (B.w s).M 0 := fun h =>
    ((B.w s).mcs 0).bot_not_mem (BWorld.mem_of_provable (Δ := [.box .bot])
      (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact h)
      ⟨Proof.D_box hD (Proof.lookup List.mem_cons_self)⟩)
  obtain ⟨t, h, _⟩ := B.ex s 0 .bot hnot
  exact ⟨t, ⟨h⟩⟩

/-- ⭐The canonical frame. -/
noncomputable def frame : Frame.{0, 0} σ where
  W := B.W
  actual := B.actual
  R := B.R
  refl := fun hT => (noT hT).elim
  trans := fun hF => (noFour hF).elim
  serial := fun hD s => B.serial_canon hD s
  symm := fun _ {_ _} h => ⟨B.symm h⟩
  refl_trans := fun hT => (noT hT).elim
  trans_refl := fun hT => (noT hT).elim
  trans_assoc := fun hF => (noFour hF).elim
  D s := (B.w s).D
  Nec A s := {o : B.RDom (.VTypeBox A) s // B.Definable (.VTypeBox A) s o}
  Pos A s := {o : B.RDom (.VTypeDia A) s // B.Definable (.VTypeDia A) s o}
  funcInterp f s args := (B.w s).canonFunc f args
  relInterp r s args := (B.w s).canonRel r args

/-- A definable raw object as a frame object. -/
def toDom : (A : VarType) → (s : B.W) → (o : B.RDom A s) → B.Definable A s o →
    B.frame.Dom A s
  | .Var, _, o, _ => o
  | .VTypeOne, _, _, _ => PUnit.unit
  | .VTypeProd A C, s, o, h =>
      (toDom A s o.1 (definable_fst h), toDom C s o.2 (definable_snd h))
  | .VTypeBox A, s, o, h =>
      (Subtype.mk o h : {o : B.RDom (.VTypeBox A) s // B.Definable (.VTypeBox A) s o})
  | .VTypeDia A, s, o, h =>
      (Subtype.mk o h : {o : B.RDom (.VTypeDia A) s // B.Definable (.VTypeDia A) s o})

/-- A frame object as a raw object. -/
def fromDom : (A : VarType) → (s : B.W) → B.frame.Dom A s → B.RDom A s
  | .Var, _, d => d
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A C, s, d =>
      (fromDom A s (d : B.frame.Dom A s × B.frame.Dom C s).1,
        fromDom C s (d : B.frame.Dom A s × B.frame.Dom C s).2)
  | .VTypeBox A, s, d =>
      (d : {o : B.RDom (.VTypeBox A) s // B.Definable (.VTypeBox A) s o}).1
  | .VTypeDia A, s, d =>
      (d : {o : B.RDom (.VTypeDia A) s // B.Definable (.VTypeDia A) s o}).1

theorem definable_fromDom : ∀ (A : VarType) (s : B.W) (d : B.frame.Dom A s),
    B.Definable A s (B.fromDom A s d)
  | .Var, _, d => definable_var d
  | .VTypeOne, _, _ => definable_unit _
  | .VTypeProd A C, s, d =>
      definable_pair (definable_fromDom A s (d : B.frame.Dom A s × B.frame.Dom C s).1)
        (definable_fromDom C s (d : B.frame.Dom A s × B.frame.Dom C s).2)
  | .VTypeBox A, s, d => (d : {o : B.RDom (.VTypeBox A) s // B.Definable (.VTypeBox A) s o}).2
  | .VTypeDia A, s, d => (d : {o : B.RDom (.VTypeDia A) s // B.Definable (.VTypeDia A) s o}).2

theorem fromDom_toDom : ∀ (A : VarType) (s : B.W) (o : B.RDom A s) (h : B.Definable A s o),
    B.fromDom A s (B.toDom A s o h) = o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A C, s, o, h =>
      Prod.ext (fromDom_toDom A s o.1 (definable_fst h)) (fromDom_toDom C s o.2 (definable_snd h))
  | .VTypeBox _, _, _, _ => rfl
  | .VTypeDia _, _, _, _ => rfl

theorem toDom_fromDom : ∀ (A : VarType) (s : B.W) (d : B.frame.Dom A s),
    B.toDom A s (B.fromDom A s d) (B.definable_fromDom A s d) = d
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A C, s, d =>
      Prod.ext (toDom_fromDom A s (d : B.frame.Dom A s × B.frame.Dom C s).1)
        (toDom_fromDom C s (d : B.frame.Dom A s × B.frame.Dom C s).2)
  | .VTypeBox _, _, _ => rfl
  | .VTypeDia _, _, _ => rfl

variable {B}

theorem toDom_inj {A : VarType} {s : B.W} {o o' : B.RDom A s} {h : B.Definable A s o}
    {h' : B.Definable A s o'} (e : B.toDom A s o h = B.toDom A s o' h') : o = o' := by
  rw [← B.fromDom_toDom A s o h, ← B.fromDom_toDom A s o' h', e]

theorem toDom_congr {A : VarType} {s : B.W} {o o' : B.RDom A s} (e : o = o')
    (h : B.Definable A s o) (h' : B.Definable A s o') : B.toDom A s o h = B.toDom A s o' h' := by
  subst e
  rfl

variable (B)

/-- Evaluation of necessary objects. -/
def necEval {A : VarType} {s : B.W} (n : B.frame.Nec A s) : B.frame.NecSec A s :=
  fun a => B.toDom A a.1 (n.1 a) (definable_box_apply n.2 a)

/-- Evaluation of possible objects. -/
def posEval {A : VarType} {s : B.W} (p : B.frame.Pos A s) : B.frame.PosSec A s :=
  ⟨p.1.1, fun a => B.toDom A a.1.1 (p.1.2 a) (definable_dia_apply p.2 a)⟩

theorem necEval_injective {A : VarType} {s : B.W} :
    Function.Injective (B.necEval (A := A) (s := s)) := by
  intro n n' h
  apply Subtype.ext
  funext a
  exact toDom_inj (congrFun h a)

theorem posEval_injective {A : VarType} {s : B.W} :
    Function.Injective (B.posEval (A := A) (s := s)) := by
  rintro ⟨⟨E, c⟩, hp⟩ ⟨⟨E', c'⟩, hp'⟩ h
  simp only [posEval] at h
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h
  have hc' := eq_of_heq hc
  apply Subtype.ext
  exact congrArg (Sigma.mk E) (funext fun a => toDom_inj (congrFun hc' a))

/-- The function algebra on the carriers. -/
noncomputable def ops : B.frame.Ops where
  necMap g n := ⟨B.rawEval (.boxMap g) _ n.1, definable_rawEval (.boxMap g) n.2⟩
  necPair a b := ⟨B.rawEval (.boxPair _ _) _
      ((a.1, b.1) : B.RDom (.VTypeProd (.VTypeBox _) (.VTypeBox _)) _),
    definable_rawEval (.boxPair _ _) (definable_pair a.2 b.2)⟩
  necUnit := ⟨B.rawEval .boxUnit _ (PUnit.unit : B.RDom .VTypeOne _),
    definable_rawEval .boxUnit (definable_unit _)⟩
  posMap g p := ⟨B.rawEval (.diaMap g) _ p.1, definable_rawEval (.diaMap g) p.2⟩
  posStrength n p := ⟨B.rawEval (.strength _ _) _
      ((n.1, p.1) : B.RDom (.VTypeProd (.VTypeBox _) (.VTypeDia _)) _),
    definable_rawEval (.strength _ _) (definable_pair n.2 p.2)⟩
  necExtract hT _ := (noT hT).elim
  necDup hF _ := (noFour hF).elim

/-- ⭐Evaluating a map on a frame object is evaluating it on the raw object. -/
theorem eval_toDom : ∀ {A C : VarType} (g : GFunc σ A C) (s : B.W) (o : B.RDom A s)
    (h : B.Definable A s o),
    GFunc.eval B.ops g s (B.toDom A s o h) = B.toDom C s (B.rawEval g s o) (definable_rawEval g h)
  | _, _, .id _, _, _, _ => rfl
  | _, _, .comp g f, s, o, h =>
      (congrArg (GFunc.eval B.ops g s) (eval_toDom f s o h)).trans (eval_toDom g s _ _)
  | _, _, .fst, _, _, _ => rfl
  | _, _, .snd, _, _, _ => rfl
  | _, _, .pair f g, s, o, h => Prod.ext (eval_toDom f s o h) (eval_toDom g s o h)
  | _, _, .unit _, _, _, _ => rfl
  | _, _, .func f args, s, o, h =>
      congrArg ((B.w s).canonFunc f) (funext fun k => eval_toDom (args k) s o h)
  | _, _, .boxMap _, _, _, _ => rfl
  | _, _, .boxPair _ _, _, _, _ => rfl
  | _, _, .boxUnit, _, _, _ => rfl
  | _, _, .diaMap _, _, _, _ => rfl
  | _, _, .strength _ _, _, _, _ => rfl
  | _, _, .extract hT, _, _, _ => (noT hT).elim
  | _, _, .dup hF, _, _, _ => (noFour hF).elim

/-! ## Strong D -/

/-- ⭐Under strong D every world has a possible object of type `𝟙` with a nonempty extent: the
    axiom's Henkin witness is a possible term `◇_x u`, whose extent is `x`'s, which `exX` makes
    nonempty. -/
theorem posSerial_canon (hDS : ModalSys.DStrong = true) (s : B.W) :
    ∃ p : B.frame.Pos .VTypeOne s, Nonempty (B.posEval p).1 := by
  have hax : (WFF.somePoss : WFF σ ((B.w s).ctx 0) 0) ∈ (B.w s).M 0 :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.D_ex hDS⟩
  obtain ⟨j, _, _, t, hmem⟩ := (B.w s).exW hax
  match t with
  | .diatm x hx u =>
      obtain ⟨X, hX⟩ := hx
      obtain ⟨t', hk, _⟩ := B.exX s j x X hX .top (by
        have e : (WFF.instantiate Ctx.NoSlots.slots (Term.diatm x ⟨X, hX⟩ u)
            (WFF.mono ((ctxOf_le_of_suffix ((B.w s).suf (Nat.zero_le j))).insert (.bnd 0)
              (.VTypeDia .VTypeOne))
              (.dia (.root (.bnd 0)) ⟨.VTypeOne, Ctx.ref_insert_root _ (.bnd 0) _⟩ .top))) =
            WFF.dia x ⟨X, hX⟩ .top := rfl
        rw [← e]
        exact hmem)
      refine ⟨⟨B.rden s j (Ctx.Le.refl _) (.diatm x ⟨X, hX⟩ u), definable_rden _ _⟩,
        ⟨⟨⟨t', ⟨B.kdR hk⟩⟩, ⟨X, hk⟩⟩⟩⟩

/-- ⭐The canonical model. -/
noncomputable def model : Model.{0, 0} σ where
  frame := B.frame
  necEval := B.necEval
  nec_inj := fun h => B.necEval_injective h
  posEval := B.posEval
  RootPoss _ := PUnit
  shape hT := (noT hT).elim
  pos_inj := fun h _ => B.posEval_injective h
  ops := B.ops
  necMap_eval g _ a := (B.eval_toDom g a.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_eval g _ := congrArg (Sigma.mk _) (funext fun a => (B.eval_toDom g a.1.1 _ _).symm)
  posStrength_eval _ _ := rfl
  shape_posMap hT := (noT hT).elim
  shape_posStrength hT := (noT hT).elim
  necExtract_eval hT _ := (noT hT).elim
  necDup_eval hF _ _ _ := (noFour hF).elim
  posRet_exists hT _ _ := (noT hT).elim
  posSerial hDS s := B.posSerial_canon hDS s

end BData

end BArrow

end V12M
