import QML.QML_v12m_BRetChildXD

/-!
# QML v12m — forgetting a witness of a returning possibility

A witnessed returning possibility is a returning possibility (docs §11.20): an arrow of `x`'s extent
is an arrow, and a body that ignores the returned possible part holds of the necessary part alone.
Both are derived, as mixed K-laws: a unit along the atom's leg carries the negated conclusion out,
and a unit at the far world brings the conclusion back to clash with it.

* `Proof.retS_refute_lift`: an atom along any leg whose lifted body the `□` view refutes is
  absurd.
* ⭐`Proof.retx_forget`: **leg forgetting** at a necessary object,
  `◇_x[d ↦ t] Φ ⊢ ◇[d ↦ t] Φ` for `Φ` over the `□` view (`ret_unit` along `x`, then plain
  `ret_unit`).
* ⭐`Proof.retD_forget`: **forgetting a possible part** on the plain leg,
  `◇[⟨d, e⟩ ↦ ⟨y, z⟩] Φ(d) ⊢ ◇[d ↦ y] Φ(d)` (`ret_unitD`, then leg forgetting along the part).
* ⭐`Proof.retxS_forget`: leg forgetting at the witnessed shape (`ret_unitD` along `x`, then
  `ret_unitW` along the part).
* ⭐`Proof.retxD_forget`: forgetting a possible part along `x`,
  `◇_x[⟨d, e⟩ ↦ ⟨y, z⟩] Φ(d) ⊢ ◇_x[d ↦ y] Φ(d)` (`ret_unitWD`, then `ret_unitD` along the part —
  the reason `ret_unitD` takes any leg).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-- An atom along any leg, at any shape, whose body lifted from the `□` view the `□` view refutes,
    is absurd. -/
def Proof.retS_refute_lift {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) (O : OutLeg Γ) (S : RShape) {a : Ann S.flat}
    (t : Term σ Γ S.flat a) (Ξ : WFF σ (Γ.boxIn.insert (.bnd 0) S.ty) 1)
    (q : Proof σ Γ.boxIn [WFF.ex S.ty Ξ] .bot)
    (p : Proof σ Γ Δ (O.retS hS S t (O.lift Ξ))) : Proof σ Γ Δ .bot := by
  cases O with
  | nec => exact Proof.retS_refute hS S t Ξ (Proof.imp_intro q) p
  | pos x hx =>
      exact Proof.retxS_refute hS hx S t _ (Proof.mono (Ctx.le_boxIn_diaIn Γ x) q) p

/-- The plain K-law's far world, in the `□` view: `Ψ ∧ unitBody(kTheta)` has no instance — `Ψ`
    holding there, `ret_unit` would bring it back against the carried negation. -/
def Proof.kTheta_refute {Γ : Ctx} [Γ.Presented] (hS : ModalSys.BStrong = true) {A C : VarType}
    {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    Proof σ Γ.boxIn [WFF.ex (.VTypeBox A)
      (WFF.and (kPsi sb θΨ) (WFF.unitBody hS sb (kTheta hS θΨ)))] .bot := by
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ)) :=
    (Ctx.Presented.fresh_bound _ le_rfl).boxIn
  have hu' : (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ)) (.VTypeBox A)).RootFresh
      (.free (Ctx.Presented.bound Γ + 1)) :=
    ((Ctx.Presented.fresh_bound _ (Nat.le_succ _)).boxIn).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  refine Proof.ex_elim _ (.VTypeBox A) hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsi sb θΨ) (WFF.unitBody hS sb (kTheta hS θΨ)))) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  exact Proof.ret_absurd hS _ _ hu' (Proof.ret_unit hS .nec _ _ _ θΨ
    (Proof.conv (openFree_unitBody_kTheta hu hS sb θΨ)
      (Proof.and_elim_r (φ := WFF.openFree _ hu Ctx.NoSlots.slots (kPsi sb θΨ))
        (Proof.lookup List.mem_cons_self)))
    (Proof.conv (openFree_kPsi hu sb θΨ)
      (Proof.and_elim_l (Proof.lookup List.mem_cons_self))))

/-- ⭐**Leg forgetting** at a necessary object (docs §11.17): `◇_x[d ↦ t] Φ ⊢ ◇[d ↦ t] Φ` for a
    body over the `□` view.  Were the plain atom false, `ret_unit` along `x` would carry its
    negation out (`kTheta`), and the far world refutes that (`Proof.kTheta_refute`). -/
def Proof.retx_forget {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {A C : VarType} {a : Ann A} (t : Term σ Γ A a) {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1)
    (p : Proof σ Γ Δ (WFF.retx hS x hx t ((OutLeg.pos x hx).lift (kPsi sb θΨ)))) :
    Proof σ Γ Δ (WFF.ret hS t (kPsi sb θΨ)) := by
  refine Proof.byContra ?_
  have P1 := Proof.ret_unit hS (.pos x hx) t _ sb (kTheta hS θΨ)
    (Proof.ofSubset (fun _ h => List.mem_cons_of_mem _ h) p)
    (Proof.conv (holeRead_kTheta hS t sb θΨ).symm (Proof.lookup List.mem_cons_self))
  exact Proof.retS_refute_lift hS (.pos x hx) (.box A) t _ (Proof.kTheta_refute hS sb θΨ) P1

/-- ⭐**Leg forgetting at a node**, for any body over the `□` view. -/
noncomputable def Proof.retx_forget_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {x : VarSymb} (hx : ∃ X, (ctxOf l).ref x = some (.VTypeDia X))
    {B : VarType} {b : Ann B} (t : Term σ (ctxOf l) B b)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (.VTypeBox B)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retx hS x hx t ((OutLeg.pos x hx).lift Φ))) :
    Proof σ (ctxOf l) Δ (WFF.ret hS t Φ) :=
  Proof.conv (by rw [kPsi_pack2]) (Proof.retx_forget hS hx t (tupT l).2
    (pack2 l (.VTypeBox B) Φ) (Proof.conv (by rw [kPsi_pack2]) p))

/-! ## Forgetting a possible part, on the plain leg -/

/-- The body `Φ(d)` of `◇[d ↦ y] Φ`, read of a witnessed object's necessary part: `θΨ` at a home
    necessary object `sb` and the slot's first component. -/
def kPsiF {Γ : Ctx} [Γ.NoSlots] {A C : VarType} (X : VarType) {c : Ann C}
    (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (RShape.wit (.box A) X).ty) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _)
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root _) sb)
      (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox A)
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ (.bnd 0) _))))
    θΨ

/-- The negated conclusion as a hole formula over a witnessed value `⟨y, z⟩` and a necessary
    object `s`: `¬◇[e ↦ y] θΨ(s.box, e)` (`kTheta` at the value's first component). -/
def kThetaF (hS : ModalSys.BStrong = true) {A C : VarType} (X : VarType)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1 :=
  WFF.neg (WFF.ret hS
    (Term.eta (.step (.step (.root (.bnd 0)) .fst) .fst) A
      (Ctx.ref_fst_of (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).boxIn).insert (.VTypeBox A))
      (Term.pair
        (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner C
          ((Ctx.le_insert ((Ctx.slotsFrom_empty.insert _).boxIn.root) (.VTypeBox A)).ref
            (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
              (.VTypeProd (.VTypeProd A X) (.VTypeBox C)))))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

/-- The hole formula read, at any depth, at a witnessed value and a necessary object `□s`. -/
theorem holeAt_kThetaF {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C X : VarType} {a : Ann A} (y : Term σ Δ A a) {b : Ann X} (z : Term σ Δ X b) {c : Ann C}
    (s : Term σ Δ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.holeAt hs (Term.pair (Term.pair y z) (Term.boxtm s)) (kThetaF hS X θΨ) =
      WFF.neg (WFF.ret hS y (WFF.holeAt (hs.boxIn.insert _)
        (Term.pair (Term.mono (Ctx.le_insert hs.boxIn.root _) s)
          (Term.eta (.root (.bnd d)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kThetaF
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0)
      (.tm (Term.pair (Term.pair y z) (Term.boxtm s)))).at (.root (.bnd 0)) =
      .tm (Term.pair (Term.pair y z) (Term.boxtm s)) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  refine congrArg (fun φ => WFF.imp φ WFF.bot) (WFF.ret_congr hS ?_ ?_)
  · exact Term.subst_eta_tm _ _ _ _ _ _ y
      (by rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
    · refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
      rfl
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) d _ _)

/-- At home, the hole formula read at the witnessed value and the home object is the negated
    conclusion. -/
theorem holeRead_kThetaF {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {A C X : VarType} {a : Ann A} (y : Term σ Γ A a) {b : Ann X} (z : Term σ Γ X b) {c : Ann C}
    (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.holeRead (Term.pair (Term.pair y z) (Term.boxtm sb)) (kThetaF hS X θΨ) =
      WFF.neg (WFF.ret hS y (kPsi sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaF]
  rfl

/-- `kPsi` at `kTheta` is the negated unit. -/
theorem kPsi_kTheta {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A C : VarType}
    {a : Ann A} (s : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    kPsi s (kTheta hS θΨ) = WFF.neg (WFF.unitBody hS s θΨ) := by
  unfold kPsi
  refine (holeAt_kTheta _ hS _ (Term.eta (VarSymb.root (.bnd 0)).inner C
    (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) θΨ).trans ?_
  unfold WFF.unitBody
  refine congrArg WFF.neg (WFF.ret_congr hS rfl ?_)
  refine WFF.holeAt_congr _ (sig_pair ?_ rfl) θΨ
  exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

section OpenF

variable {Γ : Ctx} [Γ.NoSlots] {u : ℕ} (hu : Γ.boxIn.RootFresh (.free u))

omit [ModalSys.NoFour] in
/-- Opening `kPsiF` at `u` reads `θΨ` at the home object and `u`'s necessary part. -/
theorem openFree_kPsiF {A C X : VarType} {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (kPsiF X sb θΨ) =
      WFF.holeRead (Term.pair (Term.mono (Ctx.le_insert hu.root _) sb)
        (Term.eta (.step (.root (.free u)) .fst) (.VTypeBox A)
          (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))) θΨ := by
  have h0 : ((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box A) X).ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  unfold kPsiF WFF.openFree
  rw [WFF.subst_holeAt, WFF.holeRead_eq_holeAt]
  exact WFF.holeAt_congr _ (sig_pair (subst_toFree_mono_sig hu sb)
    (Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl))) θΨ

/-- Opening the unit along the possible part, carrying `kThetaF`: a returning possibility along
    `u`'s possible part whose body is, lifted, the negated plain unit at `u`'s necessary part. -/
theorem openFree_unitBodyD_kThetaF (hS : ModalSys.BStrong = true) {A C X : VarType}
    {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.unitBodyD (Γ := Γ) hS sb (kThetaF hS X θΨ)) =
      WFF.retx hS (.step (.root (.free u)) .snd) ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
        (Term.mono (Ctx.le_insert hu.root _) sb)
        ((OutLeg.pos (.step (.root (.free u)) .snd)
            ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩).lift
          (kPsi (Γ := Γ.boxIn.insert (.free u) (RShape.wit (.box A) X).ty)
            (Term.eta (VarSymb.step (.root (.free u)) .fst).inner A
              (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
            (kTheta hS θΨ))) := by
  have hu0 := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box A) X).ty
  have hsnd := Ctx.ref_snd_of hu0
  have hθ := Subst.ok_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn))
    (RShape.wit (.box A) X).ty hu.root
  have hc := Subst.coh_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn)) Subst.coh_idRen
    (Ctx.NoSlots.slots (Γ := Γ.boxIn)) (RShape.wit (.box A) X).ty hu.root
  have h0 : ((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box A) X).ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  have hw : (((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box A) X).ty
      hu.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .step (.root (.free u)) .snd := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hsl := ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insertFree u
    (RShape.wit (.box A) X).ty).diaIn (.step (.root (.free u)) .snd)
  unfold WFF.openFree WFF.unitBodyD
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.step (.root (.free u)) .snd) rfl
    ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ hsl (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (subst_toFree_mono_sig hu sb) ?_
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root Γ.boxIn (.free u) (RShape.wit (.box A) X).ty
  refine (WFF.holeAt_congr _ (sig_pair (sig_pair
    (Term.subst_eta_renAt _ _ _ A _ (VarSymb.step (.root (.free u)) .fst).inner _
      ((Ctx.le_insert hsl.root (.VTypeBox C)).ref ((Ctx.le_boxIn_diaIn _ _).ref
        (Ctx.ref_inner (Ctx.ref_fst_of hT)))) ?_)
    (Term.subst_eta_renAt _ _ _ X _ (.step (.step (.root (.free u)) .snd) .dia) _
      ((Ctx.le_insert hsl.root (.VTypeBox C)).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of hT))) ?_))
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.dia_eq_box_mono (Δ₁ := Γ.boxIn.insert (.bnd 0) (RShape.wit (.box A) X).ty) _ _ _ _ _
        (Ctx.ref_inner (Ctx.ref_fst_of hu0)),
      Subst.box_at_inner_ren _ (w := .step (.root (.free u)) .fst)
        (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  · refine (holeAt_kThetaF _ hS _ _ (Term.eta (VarSymb.root (.bnd 0)).inner C
      (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) θΨ).trans ?_
    rw [kPsi_kTheta]
    change _ = WFF.neg (WFF.mono _ (WFF.unitBody hS _ θΨ))
    unfold WFF.unitBody
    change _ = WFF.neg (WFF.ret hS (Term.mono _ (Term.mono _ _)) (WFF.mono _ (WFF.holeAt _ _ θΨ)))
    rw [WFF.mono_holeAt _ _ (((Ctx.NoSlots.slots (Γ := (Γ.boxIn.insert (.free u)
      (RShape.wit (.box A) X).ty).diaIn (.step (.root (.free u)) .snd))).insert _).boxIn.insert _)]
    refine congrArg WFF.neg (WFF.ret_congr hS ?_ ?_)
    · rw [Term.mono_mono, Term.mono_eta]
    · refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
      · exact congrArg (Sigma.mk _) (by rw [Term.mono_eta, Term.mono_eta])
      · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm

end OpenF

/-- The far world of possible-part forgetting, in the `□` view: `Φ` of the necessary part, with the
    negation carried out along the possible part, has no instance — leg forgetting along the part
    reduces it to the plain unit's clash. -/
def Proof.kThetaF_refute {Γ : Ctx} [Γ.Presented] (hS : ModalSys.BStrong = true)
    {A C X : VarType} {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    Proof σ Γ.boxIn [WFF.ex (RShape.wit (.box A) X).ty
      (WFF.and (kPsiF X sb θΨ) (WFF.unitBodyD hS sb (kThetaF hS X θΨ)))] .bot := by
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ.boxIn)) :=
    Ctx.Presented.fresh_bound _ le_rfl
  have hu' : (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ.boxIn))
      (RShape.wit (.box A) X).ty).RootFresh (.free (Ctx.Presented.bound Γ.boxIn + 1)) :=
    (Ctx.Presented.fresh_bound _ (Nat.le_succ _)).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  refine Proof.ex_elim _ (RShape.wit (.box A) X).ty hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsiF X sb θΨ) (WFF.unitBodyD hS sb (kThetaF hS X θΨ)))) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  exact Proof.ret_absurd hS _ _ hu' (Proof.ret_unit hS .nec _ _ _ θΨ
    (Proof.conv (by rw [kPsi_kTheta]; rfl) (Proof.retx_forget hS _ _ _ (kTheta hS θΨ)
      (Proof.conv (openFree_unitBodyD_kThetaF hu hS sb θΨ)
        (Proof.and_elim_r (φ := WFF.openFree _ hu Ctx.NoSlots.slots (kPsiF X sb θΨ))
          (Proof.lookup List.mem_cons_self)))))
    (Proof.conv (openFree_kPsiF hu sb θΨ) (Proof.and_elim_l (Proof.lookup List.mem_cons_self))))

/-- ⭐**Forgetting a possible part** on the plain leg (docs §11.20):
    `◇[⟨d, e⟩ ↦ ⟨y, z⟩] Φ(d) ⊢ ◇[d ↦ y] Φ(d)`.  Were the conclusion false, `ret_unitD` would carry
    its negation out along the possible part (`kThetaF`), and the far world refutes that
    (`Proof.kThetaF_refute`). -/
def Proof.retD_forget {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {A C X : VarType} {a : Ann A} (y : Term σ Γ A a) {b : Ann X}
    (z : Term σ Γ X b) {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1)
    (p : Proof σ Γ Δ (WFF.retS hS (.wit (.box A) X) (Term.pair y z) (kPsiF X sb θΨ))) :
    Proof σ Γ Δ (WFF.ret hS y (kPsi sb θΨ)) := by
  refine Proof.byContra ?_
  have P1 := Proof.ret_unitD hS .nec (Term.pair y z) _ sb (kThetaF hS X θΨ)
    (Proof.ofSubset (fun _ h => List.mem_cons_of_mem _ h) p)
    (Proof.conv (holeRead_kThetaF hS y z sb θΨ).symm (Proof.lookup List.mem_cons_self))
  exact Proof.retS_refute_lift hS .nec (.wit (.box A) X) _ _ (Proof.kThetaF_refute hS sb θΨ) P1

/-! ## Forgetting the leg, at the witnessed shape -/

/-- The K-law with a possible part, its far world in the `□` view: `Ψ ∧ unitBodyD(kThetaD)` has no
    instance — `Ψ` holding there, `ret_unitW` along the returned part would bring it back against
    the carried negation. -/
def Proof.kThetaD_refute {Γ : Ctx} [Γ.Presented] (hS : ModalSys.BStrong = true)
    {A C X : VarType} {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    Proof σ Γ.boxIn [WFF.ex (RShape.wit (.box C) X).ty
      (WFF.and (kPsiD sb θΨ) (WFF.unitBodyD hS sb (kThetaD hS θΨ)))] .bot := by
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ.boxIn)) :=
    Ctx.Presented.fresh_bound _ le_rfl
  have hu' : (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ.boxIn))
      (RShape.wit (.box C) X).ty).RootFresh (.free (Ctx.Presented.bound Γ.boxIn + 1)) :=
    (Ctx.Presented.fresh_bound _ (Nat.le_succ _)).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  refine Proof.ex_elim _ (RShape.wit (.box C) X).ty hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsiD sb θΨ) (WFF.unitBodyD hS sb (kThetaD hS θΨ)))) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  exact Proof.retx_absurd hS _ _ _ hu' (Proof.ret_unitW hS _ _ _ _ _ θΨ
    (Proof.conv (openFree_unitBodyD_kThetaD hu hS sb θΨ)
      (Proof.and_elim_r (φ := WFF.openFree _ hu Ctx.NoSlots.slots (kPsiD sb θΨ))
        (Proof.lookup List.mem_cons_self)))
    (Proof.conv (openFree_kPsiD hu sb θΨ) (Proof.and_elim_l (Proof.lookup List.mem_cons_self))))

/-- ⭐**Leg forgetting at the witnessed shape** (docs §11.20):
    `◇_x[⟨d, e⟩ ↦ t] Φ ⊢ ◇[⟨d, e⟩ ↦ t] Φ` for `Φ` over the `□` view.  Were the conclusion false,
    `ret_unitD` along `x` would carry its negation out along the possible part (`kThetaD`), and the
    far world refutes that (`Proof.kThetaD_refute`). -/
def Proof.retxS_forget {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    {A C X : VarType} {c : Ann (.VTypeProd C X)} (t : Term σ Γ (.VTypeProd C X) c) {a : Ann A}
    (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1)
    (p : Proof σ Γ Δ (WFF.retxS hS x hx (.wit (.box C) X) t
      ((OutLeg.pos x hx).lift (kPsiD sb θΨ)))) :
    Proof σ Γ Δ (WFF.retS hS (.wit (.box C) X) t (kPsiD sb θΨ)) := by
  refine Proof.byContra ?_
  have P1 := Proof.ret_unitD hS (.pos x hx) t _ sb (kThetaD hS θΨ)
    (Proof.ofSubset (fun _ h => List.mem_cons_of_mem _ h) p)
    (Proof.conv (holeRead_kThetaD hS t sb θΨ).symm (Proof.lookup List.mem_cons_self))
  exact Proof.retS_refute_lift hS (.pos x hx) (.wit (.box C) X) t _
    (Proof.kThetaD_refute hS sb θΨ) P1

/-- ⭐**Leg forgetting at the witnessed shape, at a node**, for any body over the `□` view. -/
def Proof.retxS_forget_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {x : VarSymb} (hx : ∃ X, (ctxOf l).ref x = some (.VTypeDia X))
    {C X : VarType} {c : Ann (.VTypeProd C X)} (t : Term σ (ctxOf l) (.VTypeProd C X) c)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retxS hS x hx (.wit (.box C) X) t ((OutLeg.pos x hx).lift Φ))) :
    Proof σ (ctxOf l) Δ (WFF.retS hS (.wit (.box C) X) t Φ) :=
  Proof.conv (by rw [kPsiD_pack2]) (Proof.retxS_forget hS hx t (tupT l).2
    (pack2 l (RShape.wit (.box C) X).ty Φ) (Proof.conv (by rw [kPsiD_pack2]) p))

/-! ## Forgetting a possible part, along a witness -/

/-- The body `Φ(d)` of `◇_x[d ↦ y] Φ` over `x`'s view, read of a witnessed object's necessary
    part: `θΨ` at a home necessary object `sb`, `x`'s content and the slot's first component. -/
def kPsiXF {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {X A C : VarType} (Xe : VarType)
    (hX : Γ.ref x = some (.VTypeDia X)) {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF σ ((Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _)
    (Term.pair
      (Term.pair
        (Term.mono ((Ctx.le_boxIn_diaIn Γ x).trans
          (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _)) sb)
        (Term.eta (x.step .dia) X
          ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _).ref
            (Ctx.ref_diaIn_of hX))))
      (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox C)
        (Ctx.ref_fst_of (Ctx.ref_insert_root _ (.bnd 0) _))))
    θΨ

/-- The negated conclusion as a hole formula over a witnessed value `⟨y, z⟩` and a witnessed
    object `⟨□s, e⟩`: `¬◇_e[d ↦ y] θΨ(⟨s.box, e.dia⟩, d)` (`kThetaW` at the value's first
    component). -/
def kThetaWF (hS : ModalSys.BStrong = true) {A C X : VarType} (Xe : VarType)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty)) 1 :=
  WFF.neg (WFF.retxS hS (.step (.step (.root (.bnd 0)) .snd) .snd) ⟨X, kThetaW_ref⟩ (.box C)
    (Term.eta (.step (.step (.root (.bnd 0)) .fst) .fst) C
      (Ctx.ref_fst_of (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).diaIn _).insert (.VTypeBox C))
      (Term.pair
        (Term.pair
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .fst).inner A
            ((Ctx.le_insert (((Ctx.slotsFrom_empty.insert _).diaIn _).root) (.VTypeBox C)).ref
              ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_snd_of
                (Ctx.ref_insert_root Ctx.empty (.bnd 0)
                  (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty))))))))
          (Term.eta (.step (.step (.step (.root (.bnd 0)) .snd) .snd) .dia) X
            ((Ctx.le_insert (((Ctx.slotsFrom_empty.insert _).diaIn _).root) (.VTypeBox C)).ref
              (Ctx.ref_diaIn_of kThetaW_ref))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox C) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

/-- The hole formula read, at any depth, at a witnessed value and a witnessed object `⟨□s, v⟩`. -/
theorem holeAt_kThetaWF {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C X Xe : VarType} {c : Ann C} (y : Term σ Δ C c) {b : Ann Xe} (z : Term σ Δ Xe b)
    {a : Ann A} (s : Term σ Δ.boxIn A a) {v : VarSymb} (hv : Δ.ref v = some (.VTypeDia X))
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.holeAt hs (Term.pair (Term.pair y z) (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv)))))
        (kThetaWF hS Xe θΨ) =
      WFF.neg (WFF.retxS hS v ⟨X, hv⟩ (.box C) y (WFF.holeAt ((hs.diaIn v).insert _)
        (Term.pair
          (Term.pair (Term.mono ((Ctx.le_boxIn_diaIn Δ v).trans
              (Ctx.le_insert (hs.diaIn v).root _)) s)
            (Term.eta (v.step .dia) X
              ((Ctx.le_insert (hs.diaIn v).root _).ref (Ctx.ref_diaIn_of hv))))
          (Term.eta (.root (.bnd d)) (.VTypeBox C) (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kThetaWF
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair (Term.pair y z)
      (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))).at
      (.root (.bnd 0)) = .tm (Term.pair (Term.pair y z) (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  have hθ : Subst.Ok (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty))
      (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair (Term.pair y z)
        (Term.pair (Term.boxtm s)
          (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))) :=
    Subst.ok_single (Ctx.empty_le Δ) rfl
  have hc := Subst.coh_single (σ := σ) (r := .bnd 0)
    (T := .VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty) (Ctx.RootFresh.empty _)
    (Ctx.empty_le Δ)
    (e := .tm (Term.pair (Term.pair y z) (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv)))))) rfl
  have hw : ((Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair (Term.pair y z)
      (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))).at
      (.step (.step (.root (.bnd 0)) .snd) .snd)).idxAlong [] = v := by
    rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  refine congrArg (fun φ => WFF.imp φ WFF.bot) ?_
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ v rfl ⟨X, hv⟩ (hs.diaIn v)
    (Subst.ok_dia hθ ⟨X, kThetaW_ref⟩ hw) (Subst.coh_dia hθ hc ⟨X, kThetaW_ref⟩)]
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · exact Term.subst_eta_tm _ _ _ _ _ _ y
      (by rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ ?_) ?_) θΨ
    · refine (Term.subst_eta_tm _ _ _ _ _ _ (Term.mono (Ctx.le_insert (hs.diaIn v).root _)
        (Term.mono (Ctx.le_boxIn_diaIn Δ v) s)) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.dia_eq_box_mono (Δ₁ := Ctx.empty.insert (.bnd 0) _) _ _ v _ _
            (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty
              (.bnd 0) (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty))))),
          Subst.box_at_inner_boxtm _ (by
            rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]; rfl)]
        rfl
      · exact congrArg (Sigma.mk _) (by rw [Term.mono_mono])
    · refine (Term.subst_eta_tm _ _ _ _ _ _ (Term.mono (Ctx.le_insert (hs.diaIn v).root _)
        (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
        dsimp only [Subst.dia]
        rw [if_pos rfl, Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
        change SubE.mono _ (SubE.diaBody v (SubE.tm (Term.diatm v _
          (Term.eta (v.step .dia) X _)))) = _
        rw [SubE.diaBody_diatm]
        rfl
      · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) d _ _)

/-- At home, the hole formula read at the witnessed value, the home object and `x` is the negated
    conclusion along `x`. -/
theorem holeRead_kThetaWF {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {x : VarSymb}
    {X A C Xe : VarType} (hX : Γ.ref x = some (.VTypeDia X)) {c : Ann C} (y : Term σ Γ C c)
    {b : Ann Xe} (z : Term σ Γ Xe b) {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.holeRead (Term.pair (Term.pair y z) (Term.pair (Term.boxtm sb)
        (Term.diatm x ⟨X, hX⟩ (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)))))
        (kThetaWF hS Xe θΨ) =
      WFF.neg (WFF.retx hS x ⟨X, hX⟩ y (kPsiX hX sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaWF _ hS y z sb hX]
  rfl

section OpenXF

variable {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {X A C Xe : VarType}
  (hX : Γ.ref x = some (.VTypeDia X)) {u : ℕ} (hu : (Γ.diaIn x).RootFresh (.free u))

omit [ModalSys.NoFour] in
/-- Opening `kPsiXF` at `u` reads `θΨ` at the home object, `x`'s content and `u`'s necessary
    part. -/
theorem openFree_kPsiXF {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (kPsiXF Xe hX sb θΨ) =
      WFF.holeRead (Term.pair
        (Term.pair (Term.mono (Ctx.le_insert hu.root _) (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb))
          (Term.mono (Ctx.le_insert hu.root _) (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))))
        (Term.eta (.step (.root (.free u)) .fst) (.VTypeBox C)
          (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))) θΨ := by
  have h0 : ((Subst.idRen (σ := σ) (Γ.diaIn x)).toFree 0 u (RShape.wit (.box C) Xe).ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  unfold kPsiXF WFF.openFree
  rw [WFF.subst_holeAt, WFF.holeRead_eq_holeAt]
  refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ ?_) ?_) θΨ
  · rw [← Term.mono_mono]
    exact subst_toFree_mono_sig hu (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb)
  · refine (Term.subst_eta_renAt _ _ _ _ _ _ _
      ((Ctx.le_insert hu.root _).ref (Ctx.ref_diaIn_of hX)) ?_).trans
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm)
    rw [Subst.at_nonproj _ rfl, Subst.toFree_ne _ _ _ _ (fun h => by cases h)]
    rfl
  · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl)

/-- Opening the doubly witnessed unit carrying `kThetaWF`: a returning possibility along `u`'s
    possible part, with `x` returned, whose body is, lifted, the negated unit along the possible
    part at `u`'s necessary part. -/
theorem openFree_unitBodyWD_kThetaWF (hS : ModalSys.BStrong = true) {a : Ann A}
    (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.unitBodyWD (Γ := Γ) hS sb
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) (kThetaWF hS Xe θΨ)) =
      WFF.retxS hS (.step (.root (.free u)) .snd)
        ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ (.wit (.box A) X)
        (Term.pair (Term.mono (Ctx.le_insert hu.root _) (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb))
          (Term.mono (Ctx.le_insert hu.root _) (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))))
        ((OutLeg.pos (.step (.root (.free u)) .snd)
            ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩).lift
          (WFF.neg (WFF.unitBodyD
            (Γ := (Γ.diaIn x).insert (.free u) (RShape.wit (.box C) Xe).ty) hS
            (Term.eta (VarSymb.step (.root (.free u)) .fst).inner C
              (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
            θΨ))) := by
  have hu0 := Ctx.ref_insert_root (Γ.diaIn x) (.bnd 0) (RShape.wit (.box C) Xe).ty
  have hsnd := Ctx.ref_snd_of hu0
  have hθ := Subst.ok_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.diaIn x))
    (RShape.wit (.box C) Xe).ty hu.root
  have hc := Subst.coh_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.diaIn x))
    Subst.coh_idRen (Ctx.NoSlots.slots (Γ := Γ.diaIn x)) (RShape.wit (.box C) Xe).ty hu.root
  have h0 : ((Subst.idRen (σ := σ) (Γ.diaIn x)).toFree 0 u (RShape.wit (.box C) Xe).ty
      hu.root).at (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  have hw : (((Subst.idRen (σ := σ) (Γ.diaIn x)).toFree 0 u (RShape.wit (.box C) Xe).ty
      hu.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .step (.root (.free u)) .snd := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hsl := ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insertFree u
    (RShape.wit (.box C) Xe).ty).diaIn (.step (.root (.free u)) .snd)
  unfold WFF.openFree WFF.unitBodyWD
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.step (.root (.free u)) .snd) rfl
    ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ hsl (Subst.ok_dia hθ ⟨Xe, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨Xe, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ (subst_toFree_mono_sig hu _)) ?_
  · rw [← Term.mono_mono]
    exact subst_toFree_mono_sig hu (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb)
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root (Γ.diaIn x) (.free u) (RShape.wit (.box C) Xe).ty
  have hT' := Ctx.ref_insert_root
    ((((Γ.diaIn x).insert (.free u) (RShape.wit (.box C) Xe).ty).diaIn
      (.step (.root (.free u)) .snd))) (.bnd 0) (RShape.wit (.box A) X).ty
  refine (WFF.holeAt_congr _ (sig_pair (sig_pair
    (Term.subst_eta_renAt _ _ _ C _ (VarSymb.step (.root (.free u)) .fst).inner _
      ((Ctx.le_insert hsl.root (RShape.wit (.box A) X).ty).ref ((Ctx.le_boxIn_diaIn _ _).ref
        (Ctx.ref_inner (Ctx.ref_fst_of hT)))) ?_)
    (Term.subst_eta_renAt _ _ _ Xe _ (.step (.step (.root (.free u)) .snd) .dia) _
      ((Ctx.le_insert hsl.root (RShape.wit (.box A) X).ty).ref
        (Ctx.ref_diaIn_of (Ctx.ref_snd_of hT))) ?_))
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.dia_eq_box_mono (Δ₁ := (Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty)
        _ _ _ _ _ (Ctx.ref_inner (Ctx.ref_fst_of hu0)),
      Subst.box_at_inner_ren _ (w := .step (.root (.free u)) .fst)
        (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  · refine (holeAt_kThetaWF _ hS _ _ (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner A
      (Ctx.ref_inner (Ctx.ref_fst_of hT'))) (Ctx.ref_snd_of hT') θΨ).trans ?_
    change _ = WFF.neg (WFF.mono _ (WFF.unitBodyD hS _ θΨ))
    unfold WFF.unitBodyD
    change _ = WFF.neg (WFF.retxS hS _ _ (.box C) (Term.mono _ (Term.mono _ _))
      (WFF.mono _ (WFF.holeAt _ _ θΨ)))
    rw [WFF.mono_holeAt _ _ ((((Ctx.NoSlots.slots (Γ := (((Γ.diaIn x).insert (.free u)
      (RShape.wit (.box C) Xe).ty).diaIn (.step (.root (.free u)) .snd)))).insert _).diaIn
      _).insert _)]
    refine congrArg WFF.neg (WFF.retxS_congr hS _ _ _ ?_ ?_)
    · exact (congrArg (Sigma.mk _) ((congrArg (Term.mono _) (Term.mono_eta _ _ _ _)).trans
        (Term.mono_eta _ _ _ _))).symm
    · refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ ?_) ?_) θΨ
      · exact (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)).trans
          (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)).symm
      · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
      · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm

end OpenXF

/-- The far world of possible-part forgetting along `x`, in `x`'s view: `Φ` of the necessary
    part, with the negation carried out along the possible part (`x` returned), has no instance —
    `ret_unitD` along the possible part brings `Φ` back against it. -/
def Proof.kThetaWF_refute {Γ : Ctx} [Γ.Presented] (hS : ModalSys.BStrong = true) {x : VarSymb}
    {X A C Xe : VarType} (hX : Γ.ref x = some (.VTypeDia X)) {a : Ann A}
    (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    Proof σ (Γ.diaIn x) [WFF.ex (RShape.wit (.box C) Xe).ty
      (WFF.and (kPsiXF Xe hX sb θΨ) (WFF.unitBodyWD hS sb
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) (kThetaWF hS Xe θΨ)))] .bot := by
  have hu : (Γ.diaIn x).RootFresh (.free (Ctx.Presented.bound (Γ.diaIn x))) :=
    Ctx.Presented.fresh_bound _ le_rfl
  have hu' : ((Γ.diaIn x).insert (.free (Ctx.Presented.bound (Γ.diaIn x)))
      (RShape.wit (.box C) Xe).ty).RootFresh (.free (Ctx.Presented.bound (Γ.diaIn x) + 1)) :=
    (Ctx.Presented.fresh_bound _ (Nat.le_succ _)).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  refine Proof.ex_elim _ (RShape.wit (.box C) Xe).ty hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.and (kPsiXF Xe hX sb θΨ) (WFF.unitBodyWD hS sb
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) (kThetaWF hS Xe θΨ)))) (ψ := .bot)
    (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
      (Proof.lookup List.mem_cons_self)) ?_
  exact Proof.retxS_absurd hS _ _ _ _ hu' (Proof.ret_unitD hS (.pos _ _) _ _ _ θΨ
    (Proof.conv (openFree_unitBodyWD_kThetaWF hX hu hS sb θΨ)
      (Proof.and_elim_r (φ := WFF.openFree _ hu Ctx.NoSlots.slots (kPsiXF Xe hX sb θΨ))
        (Proof.lookup List.mem_cons_self)))
    (Proof.conv (openFree_kPsiXF hX hu sb θΨ) (Proof.and_elim_l (Proof.lookup List.mem_cons_self))))

/-- ⭐**Forgetting a possible part along a witness** (docs §11.20):
    `◇_x[⟨d, e⟩ ↦ ⟨y, z⟩] Φ(d) ⊢ ◇_x[d ↦ y] Φ(d)`.  Were the conclusion false, `ret_unitWD` would
    carry its negation out along the possible part with `x` returned (`kThetaWF`), and the far
    world refutes that by `ret_unitD` along the part (`Proof.kThetaWF_refute`). -/
def Proof.retxD_forget {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {x : VarSymb} {X A C Xe : VarType}
    (hX : Γ.ref x = some (.VTypeDia X)) {c : Ann C} (y : Term σ Γ C c) {b : Ann Xe}
    (z : Term σ Γ Xe b) {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1)
    (p : Proof σ Γ Δ (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) (Term.pair y z)
      (kPsiXF Xe hX sb θΨ))) :
    Proof σ Γ Δ (WFF.retx hS x ⟨X, hX⟩ y (kPsiX hX sb θΨ)) := by
  refine Proof.byContra ?_
  have P1 := Proof.ret_unitWD hS ⟨X, hX⟩ (Term.pair y z) _ sb
    (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) (kThetaWF hS Xe θΨ)
    (Proof.ofSubset (fun _ h => List.mem_cons_of_mem _ h) p)
    (Proof.conv (holeRead_kThetaWF hS hX y z sb θΨ).symm (Proof.lookup List.mem_cons_self))
  exact Proof.retxS_refute hS ⟨X, hX⟩ (.wit (.box C) Xe) _ _
    (Proof.kThetaWF_refute hS hX sb θΨ) P1

end BArrow

end V12M
