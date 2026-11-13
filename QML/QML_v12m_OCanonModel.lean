import QML.QML_v12m_OCanonDom

/-!
# QML v12m — the canonical tree with `Opt` on: the model

* ⭐`exists_diaO`: a possible formula `◇_x χ` holds at some child in `x`'s extent.  The bridge makes
  it `◇ ◇⁰_x χ`, so a `□`-failure child has `◇⁰_x χ`; that child decides `x`, and `◇⁰_x χ` rules out
  its absence, so `x` is opened there, and `◇⁰_x χ` with `x` opened is `χ` (`Proof.opt_out`).
* The **frame**: the worlds, `AccO` as accessibility (serial under D, `exists_succO`), the base
  domains, and as carriers the definable raw objects.  T, 4, B and 5 are off under `Opt`.
* ⭐`OCanon.model w₀`: the canonical model, pointed at `w₀`.  No shapes, no `Ret`, and
  `Ind` is equality.
-/

namespace V12M

variable [ModalSys]

namespace OCanon

open Canon

variable {σ : Signature} {N₀ : ℕ}

variable (hO : ModalSys.Opt = true) [Countable σ.FuncSyms] [Countable σ.RelSyms]

/-! ## Possible formulas have children in the extent -/

/-- ⭐**A possible formula holds at a child in its witness's extent.** -/
theorem exists_diaO (w : World σ N₀) {i : ℕ × ℕ} {x : VarSymb}
    (hx : ∃ X, (w.L.ctx i).ref x = some (.VTypeDia X)) (χ : WFF σ ((w.L.ctx i).diaIn x) 0)
    (hχ : (⟨i, .dia x hx χ⟩ : w.L.sys.Sentence σ) ∈ w.T) :
    ∃ (w' : SuccO hO w) (hm : w' ∈ extentO w x),
      (⟨childStage i, WFF.mono (extentO_le hm (Ctx.Le.refl _) hx) χ⟩ :
        w'.1.L.sys.Sentence σ) ∈ w'.1.T := by
  obtain ⟨X, hX⟩ := hx
  have hwit : (w.L.ctx i).boxIn.wit x = some X := Ctx.boxIn_wit.mpr ⟨hO, hX⟩
  have hdo : (⟨i, WFF.diaOpt hO x ⟨X, hX⟩ χ⟩ : w.L.sys.Sentence σ) ∈ w.T :=
    World.mem_of_provable (Δ := [_]) (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hχ)
      ⟨Proof.dia_opt hO x ⟨X, hX⟩ (Proof.lookup List.mem_cons_self)⟩
  obtain ⟨w', ha, hnot⟩ := exists_box_failO hO w _ (w.mcs.neg_mem_iff.mp hdo)
  set M := max i.1 i.2
  have hM : (w.L.ctx i).boxIn.Le (bview w M) := (le_diag_max w i).boxIn
  have hw' : (w'.L.ctx (childStage i)).wit x = some X :=
    (ha.wit M x).trans (hM.wit x X hwit)
  -- the child has `◇⁰_x χ`
  have hpos : (⟨childStage i, WFF.optx hO .arrow x ⟨X, hw'⟩
      (WFF.mono ((ha.boxIn_le i).optIn x) (WFF.mono (Ctx.le_diaIn_boxIn_optIn hO hX) χ))⟩ :
      w'.L.sys.Sentence σ) ∈ w'.T := by
    by_contra h
    exact hnot (w'.mcs.neg_mem_iff.mpr h)
  -- so `x` is opened there
  have hm : (⟨w', ⟨ha⟩⟩ : SuccO hO w) ∈ extentO w x := by
    rcases ha.decides M x X hw' with hd | hneg
    · exact ⟨M, X, hM.wit x X hwit, hd⟩
    · exfalso
      refine w'.mcs.bot_not_mem (i := childStage i) (World.mem_of_provable (Δ := [_, _])
        (fun ψ hψ => ?_) ⟨.imp_elim (Proof.lookup List.mem_cons_self)
          (Proof.weak _ (Proof.K_opt hO .arrow x ⟨X, hw'⟩ (Δ₁ := []) (Δ₂ := []) (φ := .top)
            (ψ := WFF.mono ((ha.boxIn_le i).optIn x)
              (WFF.mono (Ctx.le_diaIn_boxIn_optIn hO hX) χ)) .top_intro))⟩)
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hneg
      · rw [List.mem_singleton.mp hψ]
        exact hpos
  refine ⟨⟨w', ⟨ha⟩⟩, hm, World.mem_of_provable (Δ := [_]) (fun ψ hψ => ?_)
    ⟨Proof.opt_out hO .arrow x ⟨X, hw'⟩ (Proof.lookup List.mem_cons_self)⟩⟩
  rw [List.mem_singleton.mp hψ, WFF.mono_mono]
  rw [WFF.mono_mono] at hpos
  exact hpos

/-- A possible formula in the theory has a child in its witness's extent — stated for any formula
    that *is* a `◇_z`. -/
theorem exists_extentO_of_mem (w : World σ N₀) {i : ℕ × ℕ} (φ : WFF σ (w.L.ctx i) 0)
    (hφ : (⟨i, φ⟩ : w.L.sys.Sentence σ) ∈ w.T) (hdia : ∃ z hz χ, φ = .dia z hz χ) :
    ∃ (z : VarSymb) (_ : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X)) (w' : SuccO hO w),
      w' ∈ extentO w z := by
  obtain ⟨z, hz, χ, rfl⟩ := hdia
  obtain ⟨w', hw', -⟩ := exists_diaO hO w hz χ hφ
  exact ⟨z, hz, w', hw'⟩

/-- ⭐Under strong D every world has a witness with a child in its extent: the axiom
    `∃x:◇𝟙. ◇_x ⊤`, its Henkin witness, and `exists_diaO`. -/
theorem exists_extentO (hDS : ModalSys.DStrong = true) (w : World σ N₀) :
    ∃ (i : ℕ × ℕ) (z : VarSymb) (_ : ∃ X, (w.L.ctx i).ref z = some (.VTypeDia X))
      (w' : SuccO hO w), w' ∈ extentO w z := by
  have hax : (⟨(0, 0), WFF.somePoss⟩ : w.L.sys.Sentence σ) ∈ w.T :=
    World.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.D_ex hDS⟩
  obtain ⟨i', _, _, _, hmem⟩ := w.exW_term hax
  exact ⟨i', exists_extentO_of_mem hO w _ hmem ⟨_, _, _, rfl⟩⟩

/-! ## The frame -/

/-- ⭐The canonical frame with `Opt` on, pointed at a world: arrows are proper `Opt` children. -/
noncomputable def frameO (w₀ : World σ N₀) : Frame.{0, 0} σ where
  W := World σ N₀
  R := AccO hO
  refl := fun hT => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  trans := fun hF => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  refl_trans := fun hT => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  trans_refl := fun hT => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  trans_assoc := fun hF => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  actual := w₀
  serial := fun hD w => (exists_succO hO hD w).imp fun _ ha => ⟨ha⟩
  symm := fun hB => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_B hB)).elim
  homeUnique := fun _ => ⟨fun _ _ => rfl⟩
  side := fun hV => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
  side_inj := fun hV => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
  side_side := fun hV => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
  trans_side := fun hF => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  side_trans := fun hF => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  side_refl := fun hT => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  side_loop := fun _ hV => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
  D w := w.D
  Nec A w := {o : RDomO hO (.VTypeBox A) w // DefinableO hO (.VTypeBox A) w o}
  Pos A w := {o : RDomO hO (.VTypeDia A) w // DefinableO hO (.VTypeDia A) w o}
  funcInterp f w args := canonFunc w f args

variable (w₀ : World σ N₀)

/-- A definable raw object as a frame object. -/
def toDomO : (A : VarType) → (w : World σ N₀) → (o : RDomO hO A w) → DefinableO hO A w o →
    (frameO hO w₀).Dom A w
  | .Var, _, o, _ => o
  | .VTypeOne, _, _, _ => PUnit.unit
  | .VTypeProd A B, w, o, h =>
      (toDomO A w o.1 (definableO_fst h), toDomO B w o.2 (definableO_snd h))
  | .VTypeBox A, w, o, h =>
      (Subtype.mk o h : {o : RDomO hO (.VTypeBox A) w // DefinableO hO (.VTypeBox A) w o})
  | .VTypeDia A, w, o, h =>
      (Subtype.mk o h : {o : RDomO hO (.VTypeDia A) w // DefinableO hO (.VTypeDia A) w o})

/-- A frame object as a raw object. -/
def fromDomO : (A : VarType) → (w : World σ N₀) → (frameO hO w₀).Dom A w → RDomO hO A w
  | .Var, _, d => d
  | .VTypeOne, _, _ => PUnit.unit
  | .VTypeProd A B, w, d =>
      (fromDomO A w (d : (frameO hO w₀).Dom A w × (frameO hO w₀).Dom B w).1,
        fromDomO B w (d : (frameO hO w₀).Dom A w × (frameO hO w₀).Dom B w).2)
  | .VTypeBox A, w, d =>
      (d : {o : RDomO hO (.VTypeBox A) w // DefinableO hO (.VTypeBox A) w o}).1
  | .VTypeDia A, w, d =>
      (d : {o : RDomO hO (.VTypeDia A) w // DefinableO hO (.VTypeDia A) w o}).1

theorem definableO_fromDom : ∀ (A : VarType) (w : World σ N₀) (d : (frameO hO w₀).Dom A w),
    DefinableO hO A w (fromDomO hO w₀ A w d)
  | .Var, _, d => definableO_var d
  | .VTypeOne, _, _ => definableO_unit _
  | .VTypeProd A B, w, d =>
      definableO_pair
        (definableO_fromDom A w (d : (frameO hO w₀).Dom A w × (frameO hO w₀).Dom B w).1)
        (definableO_fromDom B w (d : (frameO hO w₀).Dom A w × (frameO hO w₀).Dom B w).2)
  | .VTypeBox A, w, d =>
      (d : {o : RDomO hO (.VTypeBox A) w // DefinableO hO (.VTypeBox A) w o}).2
  | .VTypeDia A, w, d =>
      (d : {o : RDomO hO (.VTypeDia A) w // DefinableO hO (.VTypeDia A) w o}).2

theorem fromDomO_toDomO : ∀ (A : VarType) (w : World σ N₀) (o : RDomO hO A w)
    (h : DefinableO hO A w o), fromDomO hO w₀ A w (toDomO hO w₀ A w o h) = o
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeProd A B, w, o, h =>
      Prod.ext (fromDomO_toDomO A w o.1 (definableO_fst h))
        (fromDomO_toDomO B w o.2 (definableO_snd h))
  | .VTypeBox _, _, _, _ => rfl
  | .VTypeDia _, _, _, _ => rfl

theorem toDomO_fromDomO : ∀ (A : VarType) (w : World σ N₀) (d : (frameO hO w₀).Dom A w),
    toDomO hO w₀ A w (fromDomO hO w₀ A w d) (definableO_fromDom hO w₀ A w d) = d
  | .Var, _, _ => rfl
  | .VTypeOne, _, _ => rfl
  | .VTypeProd A B, w, d =>
      Prod.ext (toDomO_fromDomO A w (d : (frameO hO w₀).Dom A w × (frameO hO w₀).Dom B w).1)
        (toDomO_fromDomO B w (d : (frameO hO w₀).Dom A w × (frameO hO w₀).Dom B w).2)
  | .VTypeBox _, _, _ => rfl
  | .VTypeDia _, _, _ => rfl

theorem toDomO_inj {A : VarType} {w : World σ N₀} {o o' : RDomO hO A w}
    {h : DefinableO hO A w o} {h' : DefinableO hO A w o'}
    (e : toDomO hO w₀ A w o h = toDomO hO w₀ A w o' h') : o = o' := by
  rw [← fromDomO_toDomO hO w₀ A w o h, ← fromDomO_toDomO hO w₀ A w o' h', e]

theorem toDomO_congr {A : VarType} {w : World σ N₀} {o o' : RDomO hO A w} (e : o = o')
    (h : DefinableO hO A w o) (h' : DefinableO hO A w o') :
    toDomO hO w₀ A w o h = toDomO hO w₀ A w o' h' := by
  subst e
  rfl

/-- Evaluation of necessary objects. -/
def necEvalO {A : VarType} {w : World σ N₀} (n : (frameO hO w₀).Nec A w) :
    (frameO hO w₀).NecSec A w :=
  fun w' => toDomO hO w₀ A w'.1 (n.1 w') (definableO_box_apply n.2 w')

/-- Evaluation of possible objects. -/
def posEvalO {A : VarType} {w : World σ N₀} (p : (frameO hO w₀).Pos A w) :
    (frameO hO w₀).PosSec A w :=
  ⟨p.1.1, fun w' => toDomO hO w₀ A w'.1.1 (p.1.2 w') (definableO_dia_apply p.2 w')⟩

theorem necEvalO_injective {A : VarType} {w : World σ N₀} :
    Function.Injective (necEvalO hO w₀ (A := A) (w := w)) := by
  intro n n' h
  apply Subtype.ext
  funext w'
  exact toDomO_inj hO w₀ (congrFun h w')

theorem posEvalO_injective {A : VarType} {w : World σ N₀} :
    Function.Injective (posEvalO hO w₀ (A := A) (w := w)) := by
  rintro ⟨⟨E, c⟩, hp⟩ ⟨⟨E', c'⟩, hp'⟩ h
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h
  have hc' := eq_of_heq hc
  apply Subtype.ext
  exact congrArg (Sigma.mk E) (funext fun w' => toDomO_inj hO w₀ (congrFun hc' w'))

/-- The function algebra on the carriers. -/
noncomputable def opsO : (frameO hO w₀).Ops where
  necMap g n := ⟨rawEvalO hO (.boxMap g) _ n.1, definableO_rawEval (.boxMap g) n.2⟩
  necPair a b := ⟨rawEvalO hO (.boxPair _ _) _
      ((a.1, b.1) : RDomO hO (.VTypeProd (.VTypeBox _) (.VTypeBox _)) _),
    definableO_rawEval (.boxPair _ _) (definableO_pair a.2 b.2)⟩
  necUnit := ⟨rawEvalO hO .boxUnit _ (PUnit.unit : RDomO hO .VTypeOne _),
    definableO_rawEval .boxUnit (definableO_unit _)⟩
  posMap g p := ⟨rawEvalO hO (.diaMap g) _ p.1, definableO_rawEval (.diaMap g) p.2⟩
  posStrength n p := ⟨rawEvalO hO (.strength _ _) _
      ((n.1, p.1) : RDomO hO (.VTypeProd (.VTypeBox _) (.VTypeDia _)) _),
    definableO_rawEval (.strength _ _) (definableO_pair n.2 p.2)⟩
  necExtract hT := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  necDup hF := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  posKeep hF := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  posSide hV := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim

/-- ⭐Evaluating a map on a frame object is evaluating it on the raw object. -/
theorem eval_toDomO : ∀ {A B : VarType} (g : GFunc σ A B) (w : World σ N₀) (o : RDomO hO A w)
    (h : DefinableO hO A w o),
    GFunc.eval (opsO hO w₀) g w (toDomO hO w₀ A w o h) =
      toDomO hO w₀ B w (rawEvalO hO g w o) (definableO_rawEval g h)
  | _, _, .id _, _, _, _ => rfl
  | _, _, .comp g f, w, o, h =>
      (congrArg (GFunc.eval (opsO hO w₀) g w) (eval_toDomO f w o h)).trans (eval_toDomO g w _ _)
  | _, _, .fst, _, _, _ => rfl
  | _, _, .snd, _, _, _ => rfl
  | _, _, .pair f g, w, o, h => Prod.ext (eval_toDomO f w o h) (eval_toDomO g w o h)
  | _, _, .unit _, _, _, _ => rfl
  | _, _, .func f args, w, o, h =>
      congrArg (canonFunc w f) (funext fun k => eval_toDomO (args k) w o h)
  | _, _, .boxMap _, _, _, _ => rfl
  | _, _, .boxPair _ _, _, _, _ => rfl
  | _, _, .boxUnit, _, _, _ => rfl
  | _, _, .diaMap _, _, _, _ => rfl
  | _, _, .strength _ _, _, _, _ => rfl
  | _, _, .extract hT, _, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  | _, _, .dup hF, _, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  | _, _, .dkeep hF, _, _, _ => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim

/-- ⭐Under strong D every world has a possible object of type `𝟙` with a nonempty extent. -/
theorem posSerialO (hDS : ModalSys.DStrong = true) (w : World σ N₀) :
    ∃ p : (frameO hO w₀).Pos .VTypeOne w, Nonempty (posEvalO hO w₀ p).1 := by
  obtain ⟨i, z, hz, w', hw'⟩ := exists_extentO hO hDS w
  exact ⟨⟨rdenO hO w i (Ctx.Le.refl _) (Term.diatm z hz .unit), definableO_rden _ _⟩,
    ⟨⟨w', hw'⟩⟩⟩

/-- No root possibilities, and none kept: 4 is off. -/
def rootKeepO (hF : ModalSys.Four = true) {w : (frameO hO w₀).W} (_ : PEmpty.{1})
    (_ : (frameO hO w₀).Acc w) : PEmpty.{1} :=
  (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim

/-- ⭐**The canonical model with `Opt` on.**  Shapes, `Ret` and the 4/5 operations are off with the
    flags that need them; `Ind` is equality. -/
noncomputable def model : Model.{0, 0} σ where
  frame := frameO hO w₀
  relInterp r w args := canonRel w r args
  necEval := necEvalO hO w₀
  nec_inj := fun h => necEvalO_injective hO w₀ h
  RootPoss _ := PEmpty
  rootKeep := fun hF {_} r a p => .root (rootKeepO hO w₀ hF r a) p
  rootKeepLaws := Arrows.RootKeepLaws.ofRoot (F := (frameO hO w₀).toArrows)
    (Root := fun _ => PEmpty) (rootKeepO hO w₀)
    (fun hF => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim)
    (fun hT => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim)
  posFull p := (posEvalO hO w₀ p,
    fun hS => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_shaped hS)).elim)
  posFull_inj := fun h => posEvalO_injective hO w₀ (congrArg Prod.fst h)
  posShape_wf := fun hS => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_shaped hS)).elim
  ops := opsO hO w₀
  necMap_eval g _ w' := (eval_toDomO hO w₀ g w'.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_full g _ := Prod.ext
    (congrArg (Sigma.mk _) (funext fun w' => (eval_toDomO hO w₀ g w'.1.1 _ _).symm))
    (funext fun hS => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_shaped hS)).elim)
  posStrength_full _ _ := Prod.ext rfl
    (funext fun hS => (ModalSys.opt_absurd hO (ModalSys.noOpt_of_shaped hS)).elim)
  necExtract_eval hT := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  necDup_eval hF := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  keepLift hF := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  posKeep_full hF := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Four hF)).elim
  posSide_ext hV := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
  posSerial hDS w := posSerialO hO w₀ hDS w
  Ind o o' := o = o'
  Ind_refl _ := rfl
  posSide_content hV := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
  necSide_exists hV := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_Five hV)).elim
  posRet_exists hT := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_T hT)).elim
  Ret _ _ _ _ := False
  Ret_fwd := by intro _ _ _ _ _ _ _ h; exact h.elim
  Ret_conv hS := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hS)).elim
  backRet_exists hS := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hS)).elim
  posBack_exists hS := (ModalSys.opt_absurd hO (ModalSys.noOpt_of_BStrong hS)).elim

end OCanon

end V12M
