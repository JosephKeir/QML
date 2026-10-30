import QML.QML_v12m_GCluFunc

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
* `cposSerial` (strong D), `ckeepLift` (strong 4) and ⭐`cmodel`: the model, every law of 4
  and 5 by definition or by R4.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

theorem CluFlags.absT (hX : CluFlags) (hT : ModalSys.T = true) : False := by
  rw [hX.noT] at hT
  cases hT

theorem CluFlags.absB (hX : CluFlags) (hB : ModalSys.B = true) : False := by
  rw [hX.noB] at hB
  cases hB

theorem CluFlags.absBS (hX : CluFlags) (hB : ModalSys.BStrong = true) : False := by
  rw [hX.noBStrong] at hB
  cases hB

theorem CluFlags.absShaped (hX : CluFlags) (h : ModalSys.shaped = true) : False := by
  simp [ModalSys.shaped, hX.noT, hX.noBStrong] at h

/-! ## The frame -/

variable (hM₀ : Theory.IsMCS M₀)

variable (hF) in
/-- ⭐**The cluster frame.** -/
noncomputable def cframe (hX : CluFlags) : Frame.{0, 0} σ where
  toArrows := carrows hF M₀
  actual := groot hF M₀
  serial := fun hD _ => gserial hM₀ hD (groot hF M₀)
  symm := fun hB => (hX.absB hB).elim
  homeUnique := fun _ => ⟨fun _ _ => rfl⟩
  side := fun _ {_ _ _} _ b => b
  side_inj := fun _ {_ _ _ _} _ _ _ h => h
  side_side := fun _ {_ _ _ _} _ _ _ => rfl
  trans_side := fun _ _ {_ _ _} _ _ => rfl
  side_trans := fun _ _ {_ _ _ _} _ _ _ => rfl
  side_refl := fun hT => (hX.absT hT).elim
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

theorem cposEval_injective (hX : CluFlags) {A : VarType} {s : GW hF M₀} :
    Function.Injective (cposEval hM₀ hX (A := A) (s := s)) := by
  rintro ⟨⟨E, c⟩, hp⟩ ⟨⟨E', c'⟩, hp'⟩ h
  simp only [cposEval] at h
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.mp h
  have hc' := eq_of_heq hc
  apply Subtype.ext
  exact congrArg (CRPos.mk E) (funext fun a => ctoDom_inj hX (congrFun hc' a))

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
  necExtract hT _ := (hX.absT hT).elim
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
  | _, _, .extract hT, _, _, _ => (hX.absT hT).elim
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
      have hR : GR (groot hF M₀) t' := ⟨[c], pathOk_cons, hc⟩
      exact ⟨⟨cden hM₀ hX (groot hF M₀) j (Ctx.Le.refl _) (.diatm x hx u),
          cdefinable_dia_of_root hX s _ (cdefinable_den hX _ _)⟩,
        ⟨⟨⟨t', ⟨hR⟩⟩, inExt_pathOf hR (P := [c]) (h := hc) hk⟩⟩⟩

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

/-! ## The model -/

variable (hF) in
/-- ⭐**The K45 cluster model** (5 and both lifts of 4 on, T and B off; D either way). -/
noncomputable def cmodel (hX : CluFlags) : Model.{0, 0} σ where
  frame := cframe hF hM₀ hX
  necEval := cnecEval hM₀ hX
  nec_inj := fun h => cnecEval_injective hM₀ hX h
  RootPoss _ := VarSymb
  rootKeep := (instRootKeepC hF M₀).keep
  rootKeepLaws := instRootKeepLawsC hF M₀
  posFull p := (cposEval hM₀ hX p, fun hS => (hX.absShaped hS).elim)
  posFull_inj := fun h => cposEval_injective hM₀ hX (congrArg Prod.fst h)
  posShape_wf := fun hS => (hX.absShaped hS).elim
  ops := cops hF hM₀ hX
  necMap_eval g _ a := (ceval_toDom hM₀ hX g a.1 _ _).symm
  necPair_eval _ _ _ := rfl
  posMap_full g _ := Prod.ext
    (congrArg (Sigma.mk _) (funext fun a => (ceval_toDom hM₀ hX g a.1.1 _ _).symm))
    (funext fun hS => (hX.absShaped hS).elim)
  posStrength_full _ _ := Prod.ext rfl (funext fun hS => (hX.absShaped hS).elim)
  necExtract_eval hT _ := (hX.absT hT).elim
  necDup_eval _ _ _ _ := rfl
  keepLift hF' _ hl _ a o := ckeepLift hM₀ hX hF' hl a o
  posKeep_full _ _ _ := Prod.ext rfl (funext fun hS => (hX.absShaped hS).elim)
  posSide_ext _ x _ := by
    ext b
    exact ⟨fun hb => ⟨b, hb, rfl⟩, fun ⟨c, hc, e⟩ => by rw [← e]; exact hc⟩
  posSide_content _ _ _ _ _ _ := rfl
  posSerial hDS s := cposSerial hM₀ hX hDS s
  Ind o o' := o = o'
  Ind_refl _ := rfl
  necSide_exists _ _ {_} {w} a n :=
    ⟨⟨n.1, (cdefinable_box_iff hX w n.1).mpr ((cdefinable_box_iff hX a.1 n.1).mp n.2)⟩,
      fun _ => rfl⟩
  posRet_exists hT _ _ := (hX.absT hT).elim
  Ret _ _ _ := False
  Ret_fwd hS := (hX.absBS hS).elim
  Ret_conv hS := (hX.absBS hS).elim
  backRet_exists hS := (hX.absBS hS).elim
  posBack_exists hS := (hX.absBS hS).elim

end GArrow

end V12M
