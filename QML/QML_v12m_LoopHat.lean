import QML.QML_v12m_BackSyntax

/-!
# QML v12m — the hat, and U with objects

`WFF.loopHat φ` is `φ` one view in with its slot kept: the old items shifted, the slot `c` read as
`c.keep`.  `WFF.loopHatX` is the same along a witness: `x.dia` becomes `x.keep.dia`, as the shift
sends it.  ⭐`WFF.fiveRefl` is the statement of `Proof.five_refl`, U with objects:

* along `□`: `□∀k. (□φ̂(k) → φ(k))`;
* along `◇_x`: `□_x∀k. (□_{x.keep}φ̂(k) → φ(k))`.

K45 proves U for formulas over outer parameters (`Proof.five_refute`).  What it cannot reach is an
object born at the far world (docs, "The countermodel check").
-/

namespace V12M

variable [ModalSys]

section Hat

variable {σ : Signature} {T : VarType}

/-- The types of tuples of keepable objects. -/
def VarType.tup : VarType → Bool
  | .VTypeBox _ => true
  | .VTypeDia _ => true
  | .VTypeOne => true
  | .VTypeProd A B => VarType.tup A && VarType.tup B
  | .Var => false

/-- The annotation of `Term.keepOf`. -/
def keepAnn : VarSymb → (T : VarType) → Ann T
  | _, .Var => .var
  | _, .VTypeOne => .one
  | w, .VTypeProd A B => .prod (keepAnn (.step w .fst) A) (keepAnn (.step w .snd) B)
  | w, .VTypeBox A => Ann.eta (.step w .keep) (.VTypeBox A)
  | w, .VTypeDia A => Ann.eta (.step w .keep) (.VTypeDia A)

/-- ⭐A tuple of objects, kept: the tuple of its components' `keep` steps. -/
def Term.keepOf (hF : ModalSys.Four = true) {Γ : Ctx} : (T : VarType) → T.tup = true →
    (w : VarSymb) → Γ.ref w = some T → Term σ Γ.boxIn T (keepAnn w T)
  | .VTypeOne, _, _, _ => .unit
  | .VTypeProd A B, ht, w, h =>
      have hAB : A.tup = true ∧ B.tup = true := by simpa [VarType.tup] using ht
      .pair (Term.keepOf hF A hAB.1 (.step w .fst) (Ctx.ref_fst_of h))
        (Term.keepOf hF B hAB.2 (.step w .snd) (Ctx.ref_snd_of h))
  | .VTypeBox A, _, w, h => Term.eta (.step w .keep) (.VTypeBox A) (Ctx.ref_keep_of' hF h rfl)
  | .VTypeDia A, _, w, h => Term.eta (.step w .keep) (.VTypeDia A) (Ctx.ref_keep_of' hF h rfl)

theorem Ctx.shifts_loop (hF : ModalSys.Four = true) (Γ : Ctx) [Γ.NoSlots] (T : VarType) :
    Ctx.Shifts 0 (Γ.boxIn.insert (.bnd 0) T) (Γ.boxIn.boxIn.insert (.bnd 0) T) :=
  (Ctx.shifts_boxIn_boxIn hF Γ).insert ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).rootFresh (le_refl 0)) T

/-- ⭐`φ` one view in with its slot kept: the old items shifted, the slot `c″` read as `c″.keep`. -/
def WFF.loopHat {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (hT : T.tup = true)
    (φ : WFF σ (Γ.boxIn.insert (.bnd 0) T) 1) : WFF σ (Γ.boxIn.insert (.bnd 0) T).boxIn 1 :=
  have hle : Γ.boxIn.boxIn.Le (Γ.boxIn.insert (.bnd 0) T).boxIn :=
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root T).boxIn
  have hfr := (Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).rootFresh (le_refl 0)
  WFF.subst (Subst.singleIdx (.bnd 0) (.tm (Term.keepOf hF T hT (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))))
    (Subst.single (.bnd 0) (.tm (Term.keepOf hF T hT (.root (.bnd 0))
      (Ctx.ref_insert_root Γ.boxIn (.bnd 0) T))))
    (Subst.ok_single hle rfl) (Subst.coh_single hfr hle rfl)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn.boxIn)).insert T)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T).boxIn
    (WFF.shift (Ctx.shifts_loop hF Γ T) ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert T) φ)

/-- The slot kept, in `x.keep`'s view of the body's context. -/
abbrev Term.keptSlotX (hF : ModalSys.Four = true) (hT : T.tup = true) (Γ : Ctx) [Γ.NoSlots]
    (x : VarSymb) :=
  Term.mono (Ctx.le_boxIn_diaIn ((Γ.diaIn x).insert (.bnd 0) T) (.step x .keep))
    (Term.keepOf (σ := σ) hF T hT (.root (.bnd 0)) (Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) T))

/-- The `□` view sits under the body's context along `x`. -/
theorem Ctx.le_boxIn_body (Γ : Ctx) [Γ.NoSlots] (x : VarSymb) (T : VarType) :
    Γ.boxIn.Le ((Γ.diaIn x).insert (.bnd 0) T) :=
  (Ctx.le_boxIn_diaIn Γ x).trans (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root T)

theorem Ctx.shifts_loopX (hF : ModalSys.Four = true) (Γ : Ctx) [Γ.NoSlots] (x : VarSymb)
    (T : VarType) :
    Ctx.Shifts 0 ((Γ.diaIn x).insert (.bnd 0) T)
      ((Γ.boxIn.diaIn (.step x .keep)).insert (.bnd 0) T) :=
  (Ctx.shifts_diaIn_keep hF Γ x).insert
    ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).rootFresh (le_refl 0)) T

/-- ⭐`WFF.loopHat` along a witness: a body along `◇_x`, shifted into `x.keep`'s view with its slot
    kept. -/
def WFF.loopHatX {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (hT : T.tup = true) (x : VarSymb)
    (φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) T) 1) :
    WFF σ (((Γ.diaIn x).insert (.bnd 0) T).diaIn (.step x .keep)) 1 :=
  have hle : (Γ.boxIn.diaIn (.step x .keep)).Le
      (((Γ.diaIn x).insert (.bnd 0) T).diaIn (.step x .keep)) :=
    (Ctx.le_boxIn_body Γ x T).diaIn _
  have hfr := (Ctx.NoSlots.slots (Γ := Γ.boxIn.diaIn (.step x .keep))).rootFresh (le_refl 0)
  WFF.subst (Subst.singleIdx (.bnd 0) (.tm (Term.keptSlotX (σ := σ) hF hT Γ x)))
    (Subst.single (.bnd 0) (.tm (Term.keptSlotX hF hT Γ x)))
    (Subst.ok_single hle rfl) (Subst.coh_single hfr hle rfl)
    ((Ctx.NoSlots.slots (Γ := Γ.boxIn.diaIn (.step x .keep))).insert T)
    (((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T).diaIn _)
    (WFF.shift (Ctx.shifts_loopX hF Γ x T) ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert T) φ)

/-- `x.keep` is declared in the body's context along `x`. -/
theorem Ctx.exists_keep_body (hF : ModalSys.Four = true) {Γ : Ctx} [Γ.NoSlots] {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (T : VarType) :
    ∃ X, ((Γ.diaIn x).insert (.bnd 0) T).ref (.step x .keep) = some (.VTypeDia X) :=
  (Ctx.exists_keep_dia hF hx).imp fun _ h => (Ctx.le_boxIn_body Γ x T).ref h

/-- ⭐**U with objects** (docs, "The proposed rule"): what `Proof.five_refl` states, along `□` and
    along `◇_x`. -/
def WFF.fiveRefl {Γ : Ctx} [Γ.NoSlots] (hF : ModalSys.Four = true) (hT : T.tup = true) :
    (O : OutLeg Γ) → WFF σ (O.view.insert (.bnd 0) T) 1 → WFF σ Γ 0
  | .nec, φ => .box (.all T (.imp (.box (WFF.loopHat hF hT φ)) φ))
  | .pos x hx, φ => WFF.boxx x hx (.all T (.imp
      (WFF.boxx (.step x .keep) (Ctx.exists_keep_body hF hx T) (WFF.loopHatX hF hT x φ)) φ))

end Hat

end V12M
