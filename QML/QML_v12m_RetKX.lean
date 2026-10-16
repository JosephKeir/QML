import QML.QML_v12m_RetK
import QML.QML_v12m_BRetW

/-!
# QML v12m — the K-law of the returning possibility along a witness

`◇_x[d ↦ t] Φ, ¬◇_x[d ↦ t] Ψ ⊢ ◇_x[d ↦ t](Φ ∧ ¬Ψ)` (docs §11.20), for a body `Ψ` over `x`'s view
given by a home necessary object `sb`, `x`'s content and the slot (`kPsiX`; at a network node
every body has this form, `pack2X`).  It mirrors `Proof.ret_K`, with the witnessed units:
1. at home, `ret_unitW` carries the negated premise out, `x` returning as the possible part `e`
   (`kThetaW θΨ`);
2. at the far world, `ret_unitD` along `e` brings `Ψ` back, and the conjuncts clash
   (`retS_absurd`).

This settles the first open paper check of §11.20 (the ∨ law along `x`) and makes the child of a
returning-possibility atom along `x` consistent.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-- The body `Ψ(e)` over `x`'s view, as a hole formula `θΨ` read at a home necessary object `sb`,
    `x`'s content and the slot. -/
def kPsiX {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {X A C : VarType}
    (hX : Γ.ref x = some (.VTypeDia X)) {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF σ ((Γ.diaIn x).insert (.bnd 0) (.VTypeBox C)) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _)
    (Term.pair
      (Term.pair
        (Term.mono ((Ctx.le_boxIn_diaIn Γ x).trans
          (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _)) sb)
        (Term.eta (x.step .dia) X
          ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _).ref
            (Ctx.ref_diaIn_of hX))))
      (Term.eta (.root (.bnd 0)) (.VTypeBox C) (Ctx.ref_insert_root _ (.bnd 0) _)))
    θΨ

omit [ModalSys.NoFour] in
theorem kThetaW_ref {A C X : VarType} :
    (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty)).ref
      (.step (.step (.root (.bnd 0)) .snd) .snd) = some (.VTypeDia X) :=
  Ctx.ref_snd_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))

/-- The negated premise as a hole formula over a value `y` and a witnessed object `⟨□s, e⟩`:
    `¬◇_e[d ↦ y] θΨ(⟨s.box, e.dia⟩, d)`. -/
def kThetaW (hS : ModalSys.BStrong = true) {A C X : VarType}
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty)) 1 :=
  WFF.neg (WFF.retxS hS (.step (.step (.root (.bnd 0)) .snd) .snd) ⟨X, kThetaW_ref⟩ (.box C)
    (Term.eta (.step (.root (.bnd 0)) .fst) C (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).diaIn _).insert (.VTypeBox C))
      (Term.pair
        (Term.pair
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .fst).inner A
            ((Ctx.le_insert (((Ctx.slotsFrom_empty.insert _).diaIn _).root) (.VTypeBox C)).ref
              ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_snd_of
                (Ctx.ref_insert_root Ctx.empty (.bnd 0)
                  (.VTypeProd C (RShape.wit (.box A) X).ty))))))))
          (Term.eta (.step (.step (.step (.root (.bnd 0)) .snd) .snd) .dia) X
            ((Ctx.le_insert (((Ctx.slotsFrom_empty.insert _).diaIn _).root) (.VTypeBox C)).ref
              (Ctx.ref_diaIn_of kThetaW_ref))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox C) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

/-- The hole formula read, at any depth, at a value and a witnessed object `⟨□s, v⟩` for a
    possible variable `v`. -/
theorem holeAt_kThetaW {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C X : VarType} {c : Ann C} (w : Term σ Δ C c) {a : Ann A} (s : Term σ Δ.boxIn A a)
    {v : VarSymb} (hv : Δ.ref v = some (.VTypeDia X))
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.holeAt hs (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv)))))
        (kThetaW hS θΨ) =
      WFF.neg (WFF.retxS hS v ⟨X, hv⟩ (.box C) w (WFF.holeAt ((hs.diaIn v).insert _)
        (Term.pair
          (Term.pair (Term.mono ((Ctx.le_boxIn_diaIn Δ v).trans
              (Ctx.le_insert (hs.diaIn v).root _)) s)
            (Term.eta (v.step .dia) X
              ((Ctx.le_insert (hs.diaIn v).root _).ref (Ctx.ref_diaIn_of hv))))
          (Term.eta (.root (.bnd d)) (.VTypeBox C) (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kThetaW
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.pair (Term.boxtm s)
      (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))).at
      (.root (.bnd 0)) = .tm (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  have hθ : Subst.Ok (Ctx.empty.insert (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty))
      (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))) :=
    Subst.ok_single (Ctx.empty_le Δ) rfl
  have hc := Subst.coh_single (σ := σ) (r := .bnd 0)
    (T := .VTypeProd C (RShape.wit (.box A) X).ty) (Ctx.RootFresh.empty _) (Ctx.empty_le Δ)
    (e := .tm (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv)))))) rfl
  have hw : ((Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.pair (Term.boxtm s)
      (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))).at
      (.step (.step (.root (.bnd 0)) .snd) .snd)).idxAlong [] = v := by
    rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  refine congrArg (fun φ => WFF.imp φ WFF.bot) ?_
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ v rfl ⟨X, hv⟩ (hs.diaIn v)
    (Subst.ok_dia hθ ⟨X, kThetaW_ref⟩ hw) (Subst.coh_dia hθ hc ⟨X, kThetaW_ref⟩)]
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · exact Term.subst_eta_tm _ _ _ _ _ _ w (by rw [Subst.at_proj _ _ rfl, h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ ?_) ?_) θΨ
    · refine (Term.subst_eta_tm _ _ _ _ _ _ (Term.mono (Ctx.le_insert (hs.diaIn v).root _)
        (Term.mono (Ctx.le_boxIn_diaIn Δ v) s)) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.dia_eq_box_mono (Δ₁ := Ctx.empty.insert (.bnd 0) _) _ _ v _ _
            (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty
              (.bnd 0) (.VTypeProd C (RShape.wit (.box A) X).ty))))),
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

/-- At home, the hole formula read at the value, the home object and `x` is the negated premise
    along `x`. -/
theorem holeRead_kThetaW {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {x : VarSymb}
    {X A C : VarType} (hX : Γ.ref x = some (.VTypeDia X)) {c : Ann C} (y : Term σ Γ C c)
    {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.holeRead (Term.pair y (Term.pair (Term.boxtm sb)
        (Term.diatm x ⟨X, hX⟩ (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)))))
        (kThetaW hS θΨ) =
      WFF.neg (WFF.retx hS x ⟨X, hX⟩ y (kPsiX hX sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaW _ hS y sb hX]
  rfl

section Open

variable {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {X A C : VarType}
  (hX : Γ.ref x = some (.VTypeDia X)) {u : ℕ} (hu : (Γ.diaIn x).RootFresh (.free u))

omit [ModalSys.NoFour] in
/-- Opening the body `kPsiX` at `u` reads `θΨ` at the home object, `x`'s content and `□u.box`. -/
theorem openFree_kPsiX {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (kPsiX hX sb θΨ) =
      WFF.holeRead (Term.pair
        (Term.pair (Term.mono (Ctx.le_insert hu.root (.VTypeBox C))
            (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb))
          (Term.mono (Ctx.le_insert hu.root (.VTypeBox C))
            (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))))
        (Term.boxtm (Term.eta (VarSymb.root (.free u)).inner C
          (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))))) θΨ := by
  unfold kPsiX WFF.openFree
  rw [WFF.subst_holeAt, WFF.holeRead_eq_holeAt]
  refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ ?_) ?_) θΨ
  · rw [← Term.mono_mono]
    exact subst_toFree_mono_sig hu (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb)
  · refine (Term.subst_eta_renAt _ _ _ _ _ _ _
      ((Ctx.le_insert hu.root _).ref (Ctx.ref_diaIn_of hX)) ?_).trans
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm)
    rw [Subst.at_nonproj _ rfl, Subst.toFree_ne _ _ _ _ (fun h => by cases h)]
    rfl
  · exact Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_insert_root _ _ _)
      (Subst.toFree_root _ _ _ _ _)

/-- Opening the witnessed unit's conjunct of the home step at `u`: a returning possibility with
    the witness as its possible part, whose body is the negated unit along that part
    (`unitBodyD`), at `u`'s content. -/
theorem openFree_unitBodyW_kThetaW (hS : ModalSys.BStrong = true) {a : Ann A}
    (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.unitBodyW (Γ := Γ) hS sb
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) (kThetaW hS θΨ)) =
      WFF.retS hS (.wit (.box A) X)
        (Term.pair (Term.mono (Ctx.le_insert hu.root (.VTypeBox C))
            (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb))
          (Term.mono (Ctx.le_insert hu.root (.VTypeBox C))
            (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))))
        (WFF.neg (WFF.unitBodyD (Γ := (Γ.diaIn x).insert (.free u) (.VTypeBox C)) hS
          (Term.eta (VarSymb.root (.free u)).inner C
            (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) θΨ)) := by
  unfold WFF.openFree WFF.unitBodyW
  refine WFF.retS_congr hS _ (sig_pair ?_ (subst_toFree_mono_sig hu _)) ?_
  · rw [← Term.mono_mono]
    exact subst_toFree_mono_sig hu (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb)
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root
    ((Γ.diaIn x).insert (.free u) (.VTypeBox C)).boxIn (.bnd 0) (RShape.wit (.box A) X).ty
  refine (WFF.holeAt_congr _ (sig_pair
    (Term.subst_eta_renAt _ _ _ _ _ (VarSymb.root (.free u)).inner _
      ((Ctx.le_insert (Ctx.NoSlots.slots
        (Γ := ((Γ.diaIn x).insert (.free u) (.VTypeBox C)).boxIn)).root _).ref
        (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) ?_)
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ hT
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.box_at_inner_ren _ (by
        change Subst.toFree _ _ _ _ _ (.root (.bnd 0)) = _
        exact Subst.toFree_root _ _ _ _ _)]
    rfl
  · refine (holeAt_kThetaW _ hS _ (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner A
      (Ctx.ref_inner (Ctx.ref_fst_of hT))) (Ctx.ref_snd_of hT) θΨ).trans ?_
    refine congrArg WFF.neg (WFF.retxS_congr hS _ _ _ ?_ ?_)
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
    · refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ rfl) rfl) θΨ
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

end Open

/-- ⭐**The K-law of the returning possibility along a witness** (docs §11.20):
    `◇_x[d ↦ t] Φ, ¬◇_x[d ↦ t] Ψ ⊢ ◇_x[d ↦ t](Φ ∧ ¬Ψ)`, for `Ψ` given by a home necessary object,
    `x`'s content and a hole formula.  At home `ret_unitW` carries the negated premise out with
    `x` as the returning possible part (`kThetaW`); at the far world, if `Ψ` held, `ret_unitD`
    along that part would bring it back to clash with it (`Proof.retS_absurd`). -/
def Proof.retx_K {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {x : VarSymb} {X : VarType} (hX : Γ.ref x = some (.VTypeDia X)) {C : VarType} {c : Ann C}
    (y : Term σ Γ C c) (Φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) (.VTypeBox C)) 1) {A : VarType}
    {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1)
    (p : Proof σ Γ Δ (WFF.retx hS x ⟨X, hX⟩ y Φ))
    (q : Proof σ Γ Δ (WFF.neg (WFF.retx hS x ⟨X, hX⟩ y (kPsiX hX sb θΨ)))) :
    Proof σ Γ Δ (WFF.retx hS x ⟨X, hX⟩ y (WFF.and Φ (WFF.neg (kPsiX hX sb θΨ)))) := by
  have P1 := Proof.ret_unitW hS ⟨X, hX⟩ y Φ sb (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
    (kThetaW hS θΨ) p (Proof.conv (holeRead_kThetaW hS hX y sb θΨ).symm q)
  refine Proof.ret_monoS hS (.pos x ⟨X, hX⟩) (S := .box C) y _ _ P1
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.boxxK (Δ := []) ⟨X, hX⟩ ?_))
  have hu : (Γ.diaIn x).RootFresh (.free (Ctx.Presented.bound (Γ.diaIn x))) :=
    Ctx.Presented.fresh_bound _ le_rfl
  have hu' : ((Γ.diaIn x).insert (.free (Ctx.Presented.bound (Γ.diaIn x))) (.VTypeBox C)).RootFresh
      (.free (Ctx.Presented.bound (Γ.diaIn x) + 1)) :=
    (Ctx.Presented.fresh_bound _ (Nat.le_succ _)).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  have := Proof.all_intro (Δ := []) (Ctx.Presented.bound (Γ.diaIn x)) (.VTypeBox C) hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.imp (WFF.and Φ (WFF.unitBodyW hS sb (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
        (kThetaW hS θΨ))) (WFF.and Φ (WFF.neg (kPsiX hX sb θΨ)))))
    (Proof.imp_intro (Proof.and_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.imp_intro ?_)))
  · rwa [WFF.bindFree_openFree] at this
  exact Proof.retS_absurd hS _ _ _ hu' (Proof.ret_unitD hS .nec _ _ _ θΨ
    (Proof.conv (openFree_unitBodyW_kThetaW hX hu hS sb θΨ)
      (Proof.and_elim_r (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
    (Proof.conv (openFree_kPsiX hX hu sb θΨ) (Proof.lookup List.mem_cons_self)))

/-- At a node every body over `x`'s view is a hole formula at the roots' items, `x`'s content and
    the slot (`pack2X`). -/
theorem kPsiX_pack2X {l : List VarType} {x : VarSymb} {X B : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Θ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox B)) 1) :
    kPsiX (Γ := ctxOf l) hX (tupT l).2 (pack2X (.VTypeBox B) hX Θ) = Θ :=
  (holeAt_tupT_pack2X (Ctx.Le.refl _) hX Θ).trans (WFF.mono_refl _ Θ)

/-- ⭐**The K-law along a witness at a node**, for any body. -/
noncomputable def Proof.retx_K_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X)) {B : VarType} {b : Ann B}
    (t : Term σ (ctxOf l) B b) (Φ Θ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox B)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retx hS x ⟨X, hX⟩ t Φ))
    (q : Proof σ (ctxOf l) Δ (WFF.neg (WFF.retx hS x ⟨X, hX⟩ t Θ))) :
    Proof σ (ctxOf l) Δ (WFF.retx hS x ⟨X, hX⟩ t (WFF.and Φ (WFF.neg Θ))) :=
  Proof.conv (by rw [kPsiX_pack2X]) (Proof.retx_K hS hX t Φ (tupT l).2
    (pack2X (.VTypeBox B) hX Θ) p (Proof.conv (by rw [kPsiX_pack2X]) q))

/-! ## Along a witness, at an object with companions (docs §11.21, stage 3b) -/

/-- `kThetaW` at an object with companions `co`. -/
def kThetaWC (hS : ModalSys.BStrong = true) {A C X : VarType} (co : List (List Step))
    (ho : C.CompOk co)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty)) 1 :=
  WFF.neg (WFF.retxS hS (.step (.step (.root (.bnd 0)) .snd) .snd)
    ⟨X, Ctx.ref_snd_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))⟩ (.nec (.boxC C co ho))
    (Term.eta (.step (.root (.bnd 0)) .fst) (C.compsFlat co)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).diaIn _).insert (.VTypeBox C))
      (Term.pair
        (Term.pair
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .fst).inner A
            ((Ctx.le_insert (((Ctx.slotsFrom_empty.insert _).diaIn _).root) (.VTypeBox C)).ref
              ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_snd_of
                (Ctx.ref_insert_root Ctx.empty (.bnd 0)
                  (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty))))))))
          (Term.eta (.step (.step (.step (.root (.bnd 0)) .snd) .snd) .dia) X
            ((Ctx.le_insert (((Ctx.slotsFrom_empty.insert _).diaIn _).root) (.VTypeBox C)).ref
              (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)))))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox C) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

theorem holeAt_kThetaWC {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C X : VarType} (co : List (List Step)) (ho : C.CompOk co) {c : Ann (C.compsFlat co)}
    (w : Term σ Δ (C.compsFlat co) c) {a : Ann A} (s : Term σ Δ.boxIn A a)
    {v : VarSymb} (hv : Δ.ref v = some (.VTypeDia X))
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.holeAt hs (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv)))))
        (kThetaWC hS co ho θΨ) =
      WFF.neg (WFF.retxS hS v ⟨X, hv⟩ (.nec (.boxC C co ho)) w
        (WFF.holeAt ((hs.diaIn v).insert _)
        (Term.pair
          (Term.pair (Term.mono ((Ctx.le_boxIn_diaIn Δ v).trans
              (Ctx.le_insert (hs.diaIn v).root _)) s)
            (Term.eta (v.step .dia) X
              ((Ctx.le_insert (hs.diaIn v).root _).ref (Ctx.ref_diaIn_of hv))))
          (Term.eta (.root (.bnd d)) (.VTypeBox C) (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kThetaWC
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.pair (Term.boxtm s)
      (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))).at
      (.root (.bnd 0)) = .tm (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  have hθ : Subst.Ok
      (Ctx.empty.insert (.bnd 0) (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty))
      (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))) :=
    Subst.ok_single (Ctx.empty_le Δ) rfl
  have hc := Subst.coh_single (σ := σ) (r := .bnd 0)
    (T := .VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty) (Ctx.RootFresh.empty _)
    (Ctx.empty_le Δ)
    (e := .tm (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv)))))) rfl
  have hw : ((Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.pair (Term.boxtm s)
      (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))).at
      (.step (.step (.root (.bnd 0)) .snd) .snd)).idxAlong [] = v := by
    rw [Subst.at_proj _ _ rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  refine congrArg (fun φ => WFF.imp φ WFF.bot) ?_
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ v rfl ⟨X, hv⟩ (hs.diaIn v)
    (Subst.ok_dia hθ ⟨X, Ctx.ref_snd_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, Ctx.ref_snd_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))⟩)]
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · exact Term.subst_eta_tm _ _ _ _ _ _ w (by rw [Subst.at_proj _ _ rfl, h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ ?_) ?_) θΨ
    · refine (Term.subst_eta_tm _ _ _ _ _ _ (Term.mono (Ctx.le_insert (hs.diaIn v).root _)
        (Term.mono (Ctx.le_boxIn_diaIn Δ v) s)) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.dia_eq_box_mono (Δ₁ := Ctx.empty.insert (.bnd 0) _) _ _ v _ _
            (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty
              (.bnd 0) (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty))))),
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

theorem holeRead_kThetaWC {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {x : VarSymb}
    {X A C : VarType} (hX : Γ.ref x = some (.VTypeDia X)) (co : List (List Step))
    (ho : C.CompOk co) {c : Ann (C.compsFlat co)} (y : Term σ Γ (C.compsFlat co) c)
    {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.holeRead (Term.pair y (Term.pair (Term.boxtm sb)
        (Term.diatm x ⟨X, hX⟩ (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)))))
        (kThetaWC hS co ho θΨ) =
      WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.nec (.boxC C co ho)) y (kPsiX hX sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaWC _ hS co ho y sb hX]
  rfl

section OpenC

variable {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {X A C : VarType}
  (hX : Γ.ref x = some (.VTypeDia X)) {u : ℕ} (hu : (Γ.diaIn x).RootFresh (.free u))

/-- Opening the witnessed companion unit's conjunct of the home step at `u`. -/
theorem openFree_unitBodyWC_kThetaWC (hS : ModalSys.BStrong = true) (co : List (List Step))
    (ho : C.CompOk co) {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.unitBodyWC (Γ := Γ) hS co ho sb
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) [] (Or.inl rfl)
        (kThetaWC hS co ho θΨ)) =
      WFF.retS hS (.wit (.box A) X)
        (Term.pair (Term.mono (Ctx.le_insert hu.root (.VTypeBox C))
            (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb))
          (Term.mono (Ctx.le_insert hu.root (.VTypeBox C))
            (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))))
        (WFF.neg (WFF.unitBodyDC (Γ := (Γ.diaIn x).insert (.free u) (.VTypeBox C)) hS
          [] (Or.inl rfl)
          (Term.eta (VarSymb.root (.free u)).inner C
            (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) co ho θΨ)) := by
  unfold WFF.openFree WFF.unitBodyWC
  refine WFF.retS_congr hS _ (sig_pair ?_ (subst_toFree_mono_sig hu _)) ?_
  · rw [← Term.mono_mono]
    exact subst_toFree_mono_sig hu (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb)
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root
    ((Γ.diaIn x).insert (.free u) (.VTypeBox C)).boxIn (.bnd 0) (RShape.wit (.box A) X).ty
  refine (WFF.holeAt_congr _ (sig_pair
    (Term.subst_compsSlot _ _ (Ctx.ref_insert_root (Γ.diaIn x) (.free u) (.VTypeBox C))
      (Ctx.le_insert (Ctx.NoSlots.slots
        (Γ := ((Γ.diaIn x).insert (.free u) (.VTypeBox C)).boxIn)).root _) _ _ _
      (fun q _ hq _ => ?_) co ho)
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ hT
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by
        rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
      Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q (by
        change Subst.toFree _ _ _ _ _ (.root (.bnd 0)) = _
        exact Subst.toFree_root _ _ _ _ _) hq)]
    rfl
  · refine (holeAt_kThetaWC _ hS co ho _ (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner A
      (Ctx.ref_inner (Ctx.ref_fst_of hT))) (Ctx.ref_snd_of hT) θΨ).trans ?_
    refine congrArg WFF.neg (WFF.retxS_congr hS _ _ _ ?_ ?_)
    · exact (mono_compsSlot (Ctx.ref_insert_root (Γ.diaIn x) (.free u) (.VTypeBox C))
        (Ctx.Le.refl _) _ co ho).symm.trans
        (sig_mono _ (compsVal_eta (Ctx.ref_insert_root (Γ.diaIn x) (.free u) (.VTypeBox C))
          co ho).symm)
    · refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ rfl) rfl) θΨ
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

end OpenC

/-- ⭐**The K-law along a witness at an object with companions**: `Proof.retx_K` with the
    witnessed unit's outer object and the far unit's inner object carrying the companions. -/
def Proof.retx_KC {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {x : VarSymb} {X : VarType} (hX : Γ.ref x = some (.VTypeDia X)) {C : VarType}
    (co : List (List Step)) (ho : C.CompOk co) {c : Ann (C.compsFlat co)}
    (y : Term σ Γ (C.compsFlat co) c) (Φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) (.VTypeBox C)) 1)
    {A : VarType} {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd A X) (.VTypeBox C))) 1)
    (p : Proof σ Γ Δ (WFF.retxS hS x ⟨X, hX⟩ (.nec (.boxC C co ho)) y Φ))
    (q : Proof σ Γ Δ (WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.nec (.boxC C co ho)) y
      (kPsiX hX sb θΨ)))) :
    Proof σ Γ Δ (WFF.retxS hS x ⟨X, hX⟩ (.nec (.boxC C co ho)) y
      (WFF.and Φ (WFF.neg (kPsiX hX sb θΨ)))) := by
  have P1 := Proof.ret_unitWC hS ⟨X, hX⟩ co ho y Φ sb
    (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) [] (Or.inl rfl)
    (kThetaWC hS co ho θΨ) p (Proof.conv (holeRead_kThetaWC hS hX co ho y sb θΨ).symm q)
  refine Proof.ret_monoS hS (.pos x ⟨X, hX⟩) (S := .nec (.boxC C co ho)) y _ _ P1
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.boxxK (Δ := []) ⟨X, hX⟩ ?_))
  have hu : (Γ.diaIn x).RootFresh (.free (Ctx.Presented.bound (Γ.diaIn x))) :=
    Ctx.Presented.fresh_bound _ le_rfl
  have hu' : ((Γ.diaIn x).insert (.free (Ctx.Presented.bound (Γ.diaIn x))) (.VTypeBox C)).RootFresh
      (.free (Ctx.Presented.bound (Γ.diaIn x) + 1)) :=
    (Ctx.Presented.fresh_bound _ (Nat.le_succ _)).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  have := Proof.all_intro (Δ := []) (Ctx.Presented.bound (Γ.diaIn x)) (.VTypeBox C) hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.imp (WFF.and Φ (WFF.unitBodyWC hS co ho sb
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) [] (Or.inl rfl)
        (kThetaWC hS co ho θΨ))) (WFF.and Φ (WFF.neg (kPsiX hX sb θΨ)))))
    (Proof.imp_intro (Proof.and_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.imp_intro ?_)))
  · rwa [WFF.bindFree_openFree] at this
  exact Proof.retS_absurd hS _ _ _ hu' (Proof.ret_unitDC hS .nec [] (Or.inl rfl) _ _ _ co ho θΨ
    (Proof.conv (openFree_unitBodyWC_kThetaWC hX hu hS co ho sb θΨ)
      (Proof.and_elim_r (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
    (Proof.conv (openFree_kPsiX hX hu sb θΨ) (Proof.lookup List.mem_cons_self)))

/-- The K-law along a witness at a node, at an object with companions, for any body. -/
noncomputable def Proof.retx_KC_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X)) {B : VarType} (co : List (List Step))
    (ho : B.CompOk co) {b : Ann (B.compsFlat co)}
    (t : Term σ (ctxOf l) (B.compsFlat co) b)
    (Φ Θ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (.VTypeBox B)) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retxS hS x ⟨X, hX⟩ (.nec (.boxC B co ho)) t Φ))
    (q : Proof σ (ctxOf l) Δ (WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.nec (.boxC B co ho)) t Θ))) :
    Proof σ (ctxOf l) Δ (WFF.retxS hS x ⟨X, hX⟩ (.nec (.boxC B co ho)) t
      (WFF.and Φ (WFF.neg Θ))) :=
  Proof.conv (by rw [kPsiX_pack2X]) (Proof.retx_KC hS hX co ho t Φ (tupT l).2
    (pack2X (.VTypeBox B) hX Θ) p (Proof.conv (by rw [kPsiX_pack2X]) q))

end BArrow

end V12M
