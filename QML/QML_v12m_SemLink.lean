import QML.QML_v12m_SemBack
import QML.QML_v12m_LinkSyntax

/-!
# QML v12m — links: soundness of weak 5 without 4

A formula closed apart from its hole means what it means of the hole's value alone
(`Model.sat_holeAt`).  So the link rules' soundness is about the objects moved across:

* ⭐`Model.sideOf_side`: moved across `a` and then across `side a b` is moved across `b`
  (`side_side`), with shapes off;
* ⭐`Model.sat_fiveDiaL`, `Model.sat_fiveDiaBackL`, `Model.sat_fiveBoxL`: the rules
  `Proof.five_diaL`, `Proof.five_dia_backL`, `Proof.five_boxL`.
-/

namespace V12M

variable [ModalSys]

namespace Model

variable {σ : Signature}

/-- Two sections are equal when their extents are and their contents agree. -/
theorem posSec_ext' {F : Frame.{u, v} σ} {A : VarType} {w : F.W} {X Y : F.PosSec A w}
    (hE : X.1 = Y.1) (hf : ∀ a (h : a ∈ X.1) (h' : a ∈ Y.1), X.2 ⟨a, h⟩ = Y.2 ⟨a, h'⟩) :
    X = Y := by
  obtain ⟨E, f⟩ := X
  obtain ⟨E', f'⟩ := Y
  obtain rfl : E = E' := hE
  exact congrArg (Sigma.mk E) (funext fun ⟨a, h⟩ => hf a h h)

theorem posSec_of_eq {F : Frame.{u, v} σ} {A : VarType} {w : F.W} {X Y : F.PosSec A w}
    (h : X = Y) : X.1 = Y.1 ∧ ∀ a (h : a ∈ X.1) (h' : a ∈ Y.1), X.2 ⟨a, h⟩ = Y.2 ⟨a, h'⟩ := by
  subst h
  exact ⟨rfl, fun _ _ _ => rfl⟩

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

/-! ## Moved across twice -/

theorem sideAcc_side (hV : ModalSys.Five = true) {w : M.frame.W} (a b e : M.frame.Acc w) :
    M.frame.sideAcc hV (M.frame.sideAcc hV a b) (M.frame.sideAcc hV a e) =
      M.frame.sideAcc hV b e := by
  change (⟨e.1, ⟨M.frame.side hV (M.frame.side hV a.2.down b.2.down)
    (M.frame.side hV a.2.down e.2.down)⟩⟩ : M.frame.Acc b.1) =
      ⟨e.1, ⟨M.frame.side hV b.2.down e.2.down⟩⟩
  rw [M.frame.side_side]

/-- ⭐**Moved across `a`, then across `side a b`, is moved across `b`** (`side_side`), shapes off:
    what `five_boxL` reads. -/
theorem sideOf_side (hV : ModalSys.Five = true) (hS : ModalSys.shaped = false) :
    ∀ (D : DShape) {w : M.frame.W} (x : M.frame.Dom D.ty w) (a b : M.frame.Acc w),
      M.sideOf hV D (M.sideOf hV D x a) (M.frame.sideAcc hV a b) = M.sideOf hV D x b
  | .one, _, _, _, _ => rfl
  | .dia A, w, p, a, b => by
      change M.necEval (M.ops.posSide hV (M.necEval (M.ops.posSide hV p) a))
        (M.frame.sideAcc hV a b) = M.necEval (M.ops.posSide hV p) b
      refine M.pos_inj (posSec_ext' ?_ ?_) (fun h => absurd (hS.symm.trans h) Bool.false_ne_true)
      · change (M.posFull _).1.1 = (M.posFull _).1.1
        rw [M.posSide_ext, M.posSide_ext, M.posSide_ext, Set.image_image]
        exact Set.image_congr fun e _ => sideAcc_side hV a b e
      · intro c h h'
        have h₀ := h'
        change c ∈ (M.posFull _).1.1 at h₀
        rw [M.posSide_ext] at h₀
        obtain ⟨e, he, rfl⟩ := h₀
        have hq : M.frame.sideAcc hV a e ∈
            (M.posFull (M.necEval (M.ops.posSide hV p) a)).1.1 := by
          rw [M.posSide_ext]
          exact ⟨e, he, rfl⟩
        rw [M.posSide_content hV p b e he h']
        have key : ∀ (c' : M.frame.Acc b.1) (_ : M.frame.sideAcc hV (M.frame.sideAcc hV a b)
            (M.frame.sideAcc hV a e) = c') (hc : c' ∈ (M.posEval (M.necEval (M.ops.posSide hV
              (M.necEval (M.ops.posSide hV p) a)) (M.frame.sideAcc hV a b))).1),
            HEq ((M.posEval _).2 ⟨c', hc⟩) ((M.posFull p).1.2 ⟨e, he⟩) := by
          rintro c' rfl hc
          exact heq_of_eq ((M.posSide_content hV _ _ _ hq hc).trans
            (M.posSide_content hV p a e he hq))
        exact eq_of_heq (key _ (sideAcc_side hV a b e) h)
  | .prod D E, w, x, a, b => by
      change (M.sideOf hV D (M.sideOf hV D x.1 a) (M.frame.sideAcc hV a b),
        M.sideOf hV E (M.sideOf hV E x.2 a) (M.frame.sideAcc hV a b)) =
        (M.sideOf hV D x.1 b, M.sideOf hV E x.2 b)
      rw [sideOf_side hV hS D, sideOf_side hV hS E]

/-! ## The rules -/

variable (hV : ModalSys.Five = true) (hN : ModalSys.Four = false)

/-- ⭐`Proof.five_diaL` is sound: `y`'s arrow `b`, moved across `a`, is in the moved extent, with
    `h`'s value there (`posSide_ext`, `posSide_content`, `dia_beta`). -/
theorem sat_fiveDiaL {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w) (y : VarSymb)
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
  refine ⟨⟨_, hc⟩, ?_⟩
  rw [M.posSide_content hV _ a' b.1 hb hc, (posSec_of_eq hp).2 b.1 hb b.2]
  exact Hb

/-- ⭐`Proof.five_dia_backL` is sound: an arrow of the moved extent is an arrow of `y`'s moved
    across, with the same content. -/
theorem sat_fiveDiaBackL {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W} (env : M.Env Γ w) (y : VarSymb)
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
  have e := (M.posSide_content hV _ a' b hb hc).trans
    ((posSec_of_eq hp).2 b hb ((posSec_of_eq hp).1 ▸ hb))
  rw [e] at Hc
  exact Hc

/-- ⭐`Proof.five_boxL` is sound: any arrow `b` is the premise's arrow `a` followed by the arrow
    across, and what is moved across twice is moved across once (`sideOf_side`). -/
theorem sat_fiveBoxL (hS : ModalSys.shaped = false) {Γ : Ctx} [Γ.NoSlots] {w : M.frame.W}
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
  rw [sat_holeAt, interp_eta, Env.ref_extend_root, interp_eta, Env.ref_extend_root,
    sideOf_side hV hS] at h₁
  apply hb
  rw [sat_holeAt, interp_eta, Env.ref_extend_root]
  exact h₁

end Model

end V12M
