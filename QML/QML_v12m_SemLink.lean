import QML.QML_v12m_SemBack
import QML.QML_v12m_LinkSyntax

/-!
# QML v12m — links: soundness of weak 5 without 4

A formula closed apart from its hole means what it means of the hole's value alone
(`Model.sat_holeAt`).  So the link rules' soundness is about the objects moved across:

* ⭐`Model.sideOf_side`, `Model.sideOf_loop`: moved across twice is moved across once, and along
  the loop is itself, up to `Ind` in a model proper (`IndInvariant.posSide_side`, `posSide_loop`;
  equalities where `Ind` is, `posSide_side_eq`, `posSide_loop_eq`);
* ⭐`Model.sat_fiveDiaL`, `Model.sat_fiveDiaBackL`, `Model.sat_fiveBoxL`: the rules
  `Proof.five_diaL`, `Proof.five_dia_backL`, `Proof.five_boxL`.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature}

variable {M : Model.{u, v} σ}

theorem Env.ref_extend_root {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) (r : Root) {T : VarType}
    (o : M.frame.Dom T w) : (env.extend r o).ref (.root r) (Ctx.ref_insert_root _ _ _) = o :=
  Env.extend_root env r o _

/-- ⭐`◇_d χ(d.dia)` for a link's slot `d`: some arrow of the extent of `d`'s value, with `χ` of
    the content there. -/
theorem sat_sideDia {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {A : VarType}
    (χ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1) {v : M.frame.W} (env : M.Env Γ.boxIn v)
    (o : M.frame.Pos A v) :
    M.sat (env.extend (.bnd d) (show M.frame.Dom (.VTypeDia A) v from o)) (WFF.sideDia hs χ) ↔
      ∃ c : (M.posEval o).1, M.holeSat χ ((M.posEval o).2 c) := by
  constructor
  · rintro ⟨X, h, c, H⟩
    obtain rfl : A = X := by
      rw [Ctx.ref_insert_root] at h
      cases h
      rfl
    have hr := Env.ref_extend_root env (.bnd d) (show M.frame.Dom (.VTypeDia A) v from o)
    rw [sat_holeAt, interp_eta, Env.ref_dia] at H
    revert c H
    rw [hr]
    exact fun c H => ⟨c, H⟩
  · rintro ⟨c, H⟩
    have hr := Env.ref_extend_root env (.bnd d) (show M.frame.Dom (.VTypeDia A) v from o)
    refine ⟨A, Ctx.ref_insert_root _ _ _, ⟨c.1, by rw [hr]; exact c.2⟩, ?_⟩
    rw [sat_holeAt, interp_eta, Env.ref_dia]
    convert H using 4
    rw [hr]

/-! ## The rules -/

variable (hV : ModalSys.Five = true) (hN : ModalSys.Four = false)

include hN in
/-- ⭐**Moved across `a`, then across `side a b`, is moved across `b`**, up to `Ind`, in a model
    proper (`IndInvariant.posSide_side`), componentwise: what `five_boxL` and the gather read. -/
theorem sideOf_side (hM : M.IndInvariant) (hS : ModalSys.shaped = false) :
    ∀ (D : DShape) {w : M.frame.W} (x : M.frame.Dom D.ty w) (a b : M.frame.Acc w),
      M.Ind (M.sideOf hV D (M.sideOf hV D x a) (M.frame.sideAcc hV a b)) (M.sideOf hV D x b)
  | .one, _, _, _, _ => M.Ind_refl _
  | .dia _, _, p, a, b => hM.posSide_side hV hN hS p a b
  | .prod D E, _, x, a, b => hM.pair (sideOf_side hM hS D x.1 a b) (sideOf_side hM hS E x.2 a b)

include hN in
/-- ⭐**The loop moves the possible objects of a reached world to themselves**, up to `Ind`, in a
    model proper (`IndInvariant.posSide_loop`), componentwise: what `five_reflL` reads. -/
theorem sideOf_loop (hM : M.IndInvariant) (hS : ModalSys.shaped = false) :
    ∀ (D : DShape) {w : M.frame.W} (a : M.frame.Acc w) (x : M.frame.Dom D.ty a.1),
      M.Ind (M.sideOf hV D x (M.frame.sideAcc hV a a)) x
  | .one, _, _, _ => M.Ind_refl _
  | .dia _, _, a, p => hM.posSide_loop hV hN hS a p
  | .prod D E, _, a, x => hM.pair (sideOf_loop hM hS D a x.1) (sideOf_loop hM hS E a x.2)

/-- ⭐`Proof.five_diaL` is sound: `y`'s arrow `b`, moved across `a`, is in the moved extent, with
    `h`'s value there (`posSide_ext`, `posSide_content`, `dia_beta`). -/
theorem sat_fiveDiaL (hM : M.IndInvariant) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
    (env : M.Env Γ w) (y : VarSymb)
    (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {A : VarType} {a : Ann A}
    (h : Term σ (Γ.diaIn y) A a) (χ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (H : M.sat env (.dia y hy (WFF.holeAt Ctx.NoSlots.slots h χ))) :
    M.sat env (.link hV hN (D := .dia A) (Term.diatm y hy h)
      (WFF.sideDia Ctx.NoSlots.slots χ)) := by
  obtain ⟨Y, hr, b, Hb⟩ := H
  rw [sat_holeAt] at Hb
  intro a'
  have hp := dia_beta env hy hr h
  refine (sat_sideDia Ctx.NoSlots.slots χ (env.boxPush a')
    (M.necEval (M.ops.posSide hV (interp env (Term.diatm y hy h))) a')).mpr ?_
  have hb : b.1 ∈ (M.posEval (interp env (Term.diatm y hy h))).1 := by rw [hp]; exact b.2
  have hc : M.frame.sideAcc hV a' b.1 ∈ (M.posFull (M.necEval (M.ops.posSide hV
      (interp env (Term.diatm y hy h))) a')).1.1 := by
    rw [M.posSide_ext]
    exact ⟨_, hb, rfl⟩
  refine ⟨⟨_, hc⟩, (holeSat_ind hM χ (M.posSide_content hV _ a' b.1 hb hc)).mpr ?_⟩
  rw [(posSec_of_eq hp).2 b.1 hb b.2]
  exact Hb

/-- ⭐`Proof.five_dia_backL` is sound: an arrow of the moved extent is an arrow of `y`'s moved
    across, with the same content. -/
theorem sat_fiveDiaBackL (hM : M.IndInvariant) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
    (env : M.Env Γ w) (y : VarSymb)
    (hy : ∃ Y, Γ.ref y = some (.VTypeDia Y)) {A : VarType} {a : Ann A}
    (h : Term σ (Γ.diaIn y) A a) (χ : WFF σ (Ctx.empty.insert (.bnd 0) A) 1)
    (H : M.sat env (WFF.neg (.link hV hN (D := .dia A) (Term.diatm y hy h)
      (WFF.neg (WFF.sideDia Ctx.NoSlots.slots χ))))) :
    M.sat env (.dia y hy (WFF.holeAt Ctx.NoSlots.slots h χ)) := by
  by_contra hno
  apply H
  intro a' ha
  obtain ⟨⟨c, hc⟩, Hc⟩ := (sat_sideDia Ctx.NoSlots.slots χ (env.boxPush a')
    (M.necEval (M.ops.posSide hV (interp env (Term.diatm y hy h))) a')).mp ha
  obtain ⟨Y, hr⟩ := hy
  have hp := dia_beta env ⟨Y, hr⟩ hr h
  have hc' := hc
  change c ∈ (M.posFull _).1.1 at hc'
  rw [M.posSide_ext] at hc'
  obtain ⟨b, hb, rfl⟩ := hc'
  apply hno
  refine ⟨Y, hr, ⟨b, (posSec_of_eq hp).1 ▸ hb⟩, ?_⟩
  rw [sat_holeAt]
  have H' := (holeSat_ind hM χ (M.posSide_content hV _ a' b hb hc)).mp Hc
  rw [(posSec_of_eq hp).2 b hb ((posSec_of_eq hp).1 ▸ hb)] at H'
  exact H'

/-- ⭐`Proof.five_boxL` is sound: any arrow `b` is the premise's arrow `a` followed by the arrow
    across, and what is moved across twice is moved across once (`sideOf_side`). -/
theorem sat_fiveBoxL (hM : M.IndInvariant) (hS : ModalSys.shaped = false) {Γ : Ctx}
    [Γ.NoSlots] {w : M.frame.W}
    (env : M.Env Γ w) {D : DShape} {a : Ann D.ty} (t : Term σ Γ D.ty a)
    (χ : WFF σ (Ctx.empty.insert (.bnd 0) D.ty) 1)
    (H : M.sat env (WFF.neg (.link hV hN t (WFF.neg (WFF.linkHole hV hN
      (Ctx.NoSlots.slots (Γ := Γ).boxIn.insert _)
      (Term.eta (.root (.bnd 0)) D.ty (Ctx.ref_insert_root _ _ _)) χ))))) :
    M.sat env (WFF.linkHole hV hN Ctx.NoSlots.slots t χ) := by
  intro b
  by_contra hb
  apply H
  intro a' ha
  have h₁ := ha (M.frame.sideAcc hV a' b)
  rw [sat_holeAt, interp_eta, Env.ref_extend_root, interp_eta, Env.ref_extend_root] at h₁
  apply hb
  rw [sat_holeAt, interp_eta, Env.ref_extend_root]
  exact (holeSat_ind hM χ (sideOf_side hV hN hM hS D _ a' b)).mp h₁

/-! ## The gather -/

/-- What `linkHoleN` says: along every arrow `c`, `χ` of `n`'s value there beside the slot. -/
theorem sat_linkHoleN {Γ : Ctx} {d : ℕ} (hs : Γ.SlotsFrom d) {w : M.frame.W} (env : M.Env Γ w)
    {B : VarType} (n : VarSymb) (hn : Γ.ref n = some (.VTypeBox B)) {D : DShape} {a : Ann D.ty}
    (t : Term σ Γ D.ty a) (χ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd B D.ty)) 1) :
    M.sat env (WFF.linkHoleN hV hN hs n hn t χ) ↔
      ∀ c : M.frame.Acc w,
        M.holeSat χ (M.necEval (env.ref n hn) c, M.sideOf hV D (interp env t) c) := by
  refine forall_congr' fun c => ?_
  rw [sat_holeAt]
  change M.holeSat χ (interp _ (Term.mono _ _), interp _ (Term.eta _ _ _)) ↔ _
  rw [interp_mono (Env.agree_extend _ hs.boxIn.root _), interp_eta, interp_eta,
    Env.ref_inner _ c hn, Env.ref_extend_root]

/-- ⭐`Proof.five_gatherL` is sound: the premise's arrow `a` and object `n`; the law gathers `n`
    into `m` (`necSide_exists`), whose values are `n`'s along the arrows across up to `Ind`, which
    a model proper does not see (`holeSat_ind`); and what is moved across twice is moved across
    once (`sideOf_side`). -/
theorem sat_fiveGatherL (hM : M.IndInvariant) (hS : ModalSys.shaped = false)
    (h5 : ModalSys.FiveStrong = true) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w)
    (O : OutLeg Γ) {B : VarType} {D : DShape} {a : Ann D.ty} (t : Term σ Γ D.ty a)
    (χ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd B D.ty)) 1)
    (H : M.sat env (O.linkDia hV hN t (.ex (.VTypeBox B) (WFF.linkHoleN hV hN
      (((OutLeg.slotsFrom Ctx.NoSlots.slots O).insert _).insert _) (.root (.bnd 1))
      (Ctx.ref_insert_root _ _ _)
      (Term.mono (Ctx.le_insert ((OutLeg.slotsFrom Ctx.NoSlots.slots O).insert _).root _)
        (Term.eta (.root (.bnd 0)) D.ty (Ctx.ref_insert_root _ _ _))) χ)))) :
    M.sat env (.ex (.VTypeBox B) (WFF.linkHoleN hV hN (Ctx.NoSlots.slots.insert _)
      (.root (.bnd 0)) (Ctx.ref_insert_root _ _ _)
      (Term.mono (Ctx.le_insert Ctx.NoSlots.slots.root _) t) χ)) := by
  -- The body at the premise's arrow, read off as the object `n` and its values.
  have body : ∀ {Γ' : Ctx} (hs' : Γ'.SlotsFrom 0) {v : M.frame.W} (e : M.Env Γ' v)
      (x : M.frame.Dom D.ty v),
      M.sat (e.extend (.bnd 0) x) (.ex (.VTypeBox B) (WFF.linkHoleN hV hN
        ((hs'.insert _).insert _) (.root (.bnd 1)) (Ctx.ref_insert_root _ _ _)
        (Term.mono (Ctx.le_insert (hs'.insert _).root _)
          (Term.eta (.root (.bnd 0)) D.ty (Ctx.ref_insert_root _ _ _))) χ)) →
      ∃ n : M.frame.Nec B v, ∀ c : M.frame.Acc v,
        M.holeSat χ (M.necEval n c, M.sideOf hV D x c) := by
    intro Γ' hs' v e x ⟨n, hn⟩
    rw [sat_linkHoleN] at hn
    refine ⟨n, fun c => ?_⟩
    have h := hn c
    rwa [Env.ref_extend_root, interp_mono (Env.agree_extend _ (hs'.insert _).root _), interp_eta,
      Env.ref_extend_root] at h
  have key : ∃ (a : M.frame.Acc w) (n : M.frame.Nec B a.1), ∀ c : M.frame.Acc a.1,
      M.holeSat χ (M.necEval n c, M.sideOf hV D (M.sideOf hV D (interp env t) a) c) := by
    cases O with
    | nec =>
        by_contra hno
        refine H fun a ha => hno ?_
        obtain ⟨n, hn⟩ := body (Ctx.NoSlots.slots (Γ := Γ.boxIn)) (env.boxPush a) _ ha
        exact ⟨a, n, hn⟩
    | pos y hy =>
        obtain ⟨Y, hr, b, hb⟩ := H
        obtain ⟨n, hn⟩ := body (Ctx.NoSlots.slots (Γ := Γ.diaIn y)) (env.diaPush y hr b) _ hb
        exact ⟨b.1, n, hn⟩
  obtain ⟨a', n, hn⟩ := key
  obtain ⟨m, hm⟩ := M.necSide_exists hV h5 a' n
  refine ⟨m, (sat_linkHoleN _ _ _ _ _ _ _ _).mpr fun b => ?_⟩
  rw [Env.ref_extend_root, interp_mono (Env.agree_extend _ Ctx.NoSlots.slots.root _)]
  refine (holeSat_ind hM χ (hM.pair (hm b) (M.Ind_refl _))).mpr ?_
  exact (holeSat_ind hM χ (hM.pair (M.Ind_refl _) (sideOf_side hV hN hM hS D _ a' b))).mp
    (hn (M.frame.sideAcc hV a' b))

/-! ## U with objects -/

theorem Env.ref_extend_extend {Γ : Ctx} {w : M.frame.W} (env : M.Env Γ w) {r r' : Root}
    (hrr : r ≠ r') {T T' : VarType} (o : M.frame.Dom T w) (o' : M.frame.Dom T' w)
    (h : ((Γ.insert r T).insert r' T').ref (.root r) = some T) :
    ((env.extend r o).extend r' o').ref (.root r) h = o := by
  change ((env.extend r o).extend r' o') (.root r) T h = o
  rw [Env.extend_ne _ _ _ _ (fun e => hrr (by cases e; rfl)) (by simp [Ctx.insert])]
  exact Env.extend_root _ _ _ _

/-- ⭐`Proof.five_reflL` is sound: at a reached world `a.1`, the loop `side a a` is an arrow; a
    necessary object's value along it is the witness, and the possible objects moved along it are
    themselves (`sideOf_loop`). -/
theorem sat_fiveReflL (hM : M.IndInvariant) (hS : ModalSys.shaped = false) {w : M.frame.W}
    (env : M.Env Ctx.empty w)
    {B : VarType} {D : DShape} (χ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd B D.ty)) 1) :
    M.sat env (WFF.fiveReflL hV hN χ) := by
  intro a k q hk
  rw [sat_linkHoleN] at hk
  have h := hk (M.frame.sideAcc hV a a)
  rw [Env.ref_extend_extend _ (by decide), interp_eta, Env.ref_extend_root] at h
  change ∃ o : M.frame.Dom B a.1, _
  refine ⟨M.necEval k (M.frame.sideAcc hV a a), ?_⟩
  rw [sat_holeAt]
  change M.holeSat χ (interp _ (Term.eta _ _ _), interp _ (Term.eta _ _ _))
  rw [interp_eta, interp_eta, Env.ref_extend_root, Env.ref_extend_extend _ (by decide)]
  exact (holeSat_ind hM χ (hM.pair (M.Ind_refl _) (sideOf_loop hV hN hM hS D a _))).mp h

end Model

end V12M
