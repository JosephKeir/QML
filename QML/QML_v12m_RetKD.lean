import QML.QML_v12m_RetKX

/-!
# QML v12m — the K-law of the returning possibility with a possible part

`◇[⟨d, e⟩ ↦ t] Φ, ¬◇[⟨d, e⟩ ↦ t] Ψ ⊢ ◇[⟨d, e⟩ ↦ t](Φ ∧ ¬Ψ)` (docs §11.20), at the witnessed shape
`□C × ◇X` (`e ⇝ t.2`, the witness of the way home), for `Ψ` given by a home necessary object and
a hole formula (`kPsiD`; at a network node every body has this form, `pack2`).  It is
`Proof.retx_K` with the witnessed units swapped:
1. at home, `ret_unitD` carries the negated premise out along the returned possible part `e₁`
   (`kThetaD θΨ`);
2. at the far world, `Ψ` is exactly `ret_unitW`'s premise along `e₁`, which brings it back home
   with `e₁` as the possible part, and the conjuncts clash (`retx_absurd`).

This settles the first open paper check of §11.20 along a possible part, and makes the
back-witness child consistent.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-- The body `Ψ(⟨d, e⟩)` at the witnessed shape, as a hole formula `θΨ` read at a home necessary
    object `sb` and the slot. -/
def kPsiD {Γ : Ctx} [Γ.NoSlots] {A C X : VarType} {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _)
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root _) sb)
      (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
    θΨ

/-- The negated premise as a hole formula over a value `t` and a necessary object `s`:
    `¬◇[⟨d, e⟩ ↦ t] θΨ(s.box, ⟨d, e⟩)`. -/
def kThetaD (hS : ModalSys.BStrong = true) {A C X : VarType}
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (.VTypeProd C X) (.VTypeBox A))) 1 :=
  WFF.neg (WFF.retS hS (.wit (.box C) X)
    (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeProd C X)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).boxIn).insert (RShape.wit (.box C) X).ty)
      (Term.pair
        (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner A
          ((Ctx.le_insert ((Ctx.slotsFrom_empty.insert _).boxIn.root) _).ref
            (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
              (.VTypeProd (.VTypeProd C X) (.VTypeBox A)))))))
        (Term.eta (.root (.bnd 1)) _ (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

/-- The hole formula read, at any depth, at a value and a necessary object `□s`. -/
theorem holeAt_kThetaD {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C X : VarType} {c : Ann (.VTypeProd C X)} (w : Term σ Δ (.VTypeProd C X) c) {a : Ann A}
    (s : Term σ Δ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF.holeAt hs (Term.pair w (Term.boxtm s)) (kThetaD hS θΨ) =
      WFF.neg (WFF.retS hS (.wit (.box C) X) w (WFF.holeAt (hs.boxIn.insert _)
        (Term.pair (Term.mono (Ctx.le_insert hs.boxIn.root _) s)
          (Term.eta (.root (.bnd d)) _ (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kThetaD
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.boxtm s)))).at
      (.root (.bnd 0)) = .tm (Term.pair w (Term.boxtm s)) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  refine congrArg (fun φ => WFF.imp φ WFF.bot) (WFF.retS_congr hS _ ?_ ?_)
  · exact Term.subst_eta_tm _ _ _ _ _ _ w (by rw [Subst.at_proj _ _ rfl, h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
    · refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
      rfl
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) d _ _)

/-- At home, the hole formula read at the value and the home object is the negated premise. -/
theorem holeRead_kThetaD {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {A C X : VarType} {c : Ann (.VTypeProd C X)} (t : Term σ Γ (.VTypeProd C X) c) {a : Ann A}
    (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF.holeRead (Term.pair t (Term.boxtm sb)) (kThetaD hS θΨ) =
      WFF.neg (WFF.retS hS (.wit (.box C) X) t (kPsiD sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaD]
  rfl

section Open

variable {Γ : Ctx} [Γ.NoSlots] {u : ℕ} (hu : Γ.boxIn.RootFresh (.free u))

omit [ModalSys.NoFour] in
/-- Opening the body `kPsiD` at `u` reads `θΨ` at the home object and `u`. -/
theorem openFree_kPsiD {A C X : VarType} {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (kPsiD sb θΨ) =
      WFF.holeRead (Term.pair (Term.mono (Ctx.le_insert hu.root _) sb)
        (Term.eta (.root (.free u)) (RShape.wit (.box C) X).ty (Ctx.ref_insert_root _ _ _)))
        θΨ := by
  unfold kPsiD WFF.openFree
  rw [WFF.subst_holeAt, WFF.holeRead_eq_holeAt]
  exact WFF.holeAt_congr _ (sig_pair (subst_toFree_mono_sig hu sb)
    (Term.subst_eta_renAt _ _ _ _ (.root (.bnd 0)) (.root (.free u)) _ _
      (by exact Subst.toFree_root _ _ _ _ _))) θΨ

/-- Opening the unit's conjunct along the possible part at `u`: a returning possibility along
    `u`'s possible part, whose body is the negated witnessed unit (`unitBodyW`) at `u`'s
    necessary object and content. -/
theorem openFree_unitBodyD_kThetaD (hS : ModalSys.BStrong = true) {A C X : VarType} {a : Ann A}
    (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.unitBodyD (Γ := Γ) hS sb (kThetaD hS θΨ)) =
      WFF.retx hS (.step (.root (.free u)) .snd)
        ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
        (Term.mono (Ctx.le_insert hu.root _) sb)
        (WFF.neg (WFF.unitBodyW (Γ := Γ.boxIn.insert (.free u) (RShape.wit (.box C) X).ty) hS
          (Term.eta (VarSymb.step (.root (.free u)) .fst).inner C
            (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
          (Term.eta (.step (.step (.root (.free u)) .snd) .dia) X
            (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
          θΨ)) := by
  have hu0 := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu0
  have hθ := Subst.ok_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn))
    (RShape.wit (.box C) X).ty hu.root
  have hc := Subst.coh_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn)) Subst.coh_idRen
    (Ctx.NoSlots.slots (Γ := Γ.boxIn)) (RShape.wit (.box C) X).ty hu.root
  have h0 : ((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box C) X).ty hu.root).at
      (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  have hw : (((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box C) X).ty
      hu.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .step (.root (.free u)) .snd := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hsl := ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insertFree u
    (RShape.wit (.box C) X).ty).diaIn (.step (.root (.free u)) .snd)
  unfold WFF.openFree WFF.unitBodyD
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.step (.root (.free u)) .snd) rfl
    ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ hsl (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (subst_toFree_mono_sig hu sb) ?_
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root Γ.boxIn (.free u) (RShape.wit (.box C) X).ty
  refine (WFF.holeAt_congr _ (sig_pair (sig_pair
    (Term.subst_eta_renAt _ _ _ C _ (VarSymb.step (.root (.free u)) .fst).inner _
      ((Ctx.le_insert hsl.root (.VTypeBox A)).ref ((Ctx.le_boxIn_diaIn _ _).ref
        (Ctx.ref_inner (Ctx.ref_fst_of hT)))) ?_)
    (Term.subst_eta_renAt _ _ _ X _ (.step (.step (.root (.free u)) .snd) .dia) _
      ((Ctx.le_insert hsl.root (.VTypeBox A)).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of hT))) ?_))
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.dia_eq_box_mono (Δ₁ := Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) _ _ _ _ _
        (Ctx.ref_inner (Ctx.ref_fst_of hu0)),
      Subst.box_at_inner_ren _ (w := .step (.root (.free u)) .fst)
        (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  · refine (holeAt_kThetaD _ hS _ (Term.eta (VarSymb.root (.bnd 0)).inner A
      (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) θΨ).trans ?_
    refine congrArg WFF.neg (WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_)
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
    · refine WFF.holeAt_congr _ (sig_pair ?_ rfl) θΨ
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

end Open

/-- ⭐**The K-law of the returning possibility with a possible part** (docs §11.20):
    `◇[⟨d, e⟩ ↦ t] Φ, ¬◇[⟨d, e⟩ ↦ t] Ψ ⊢ ◇[⟨d, e⟩ ↦ t](Φ ∧ ¬Ψ)`.  At home `ret_unitD` carries
    the negated premise out along the returned possible part (`kThetaD`); at the far world, if
    `Ψ` held, `ret_unitW` along that part would bring it back to clash with it
    (`Proof.retx_absurd`). -/
def Proof.retD_K {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {C X : VarType} {c : Ann (.VTypeProd C X)} (t : Term σ Γ (.VTypeProd C X) c)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1) {A : VarType}
    {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1)
    (p : Proof σ Γ Δ (WFF.retS hS (.wit (.box C) X) t Φ))
    (q : Proof σ Γ Δ (WFF.neg (WFF.retS hS (.wit (.box C) X) t (kPsiD sb θΨ)))) :
    Proof σ Γ Δ (WFF.retS hS (.wit (.box C) X) t (WFF.and Φ (WFF.neg (kPsiD sb θΨ)))) := by
  have P1 := Proof.ret_unitD hS .nec t Φ sb (kThetaD hS θΨ) p
    (Proof.conv (holeRead_kThetaD hS t sb θΨ).symm q)
  refine Proof.ret_monoS hS .nec (S := .wit (.box C) X) t _ _ P1
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) ?_))
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ.boxIn)) :=
    Ctx.Presented.fresh_bound _ le_rfl
  have hu' : (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ.boxIn))
      (RShape.wit (.box C) X).ty).RootFresh (.free (Ctx.Presented.bound Γ.boxIn + 1)) :=
    (Ctx.Presented.fresh_bound _ (Nat.le_succ _)).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  have := Proof.all_intro (Δ := []) (Ctx.Presented.bound Γ.boxIn) (RShape.wit (.box C) X).ty hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.imp (WFF.and Φ (WFF.unitBodyD hS sb (kThetaD hS θΨ)))
        (WFF.and Φ (WFF.neg (kPsiD sb θΨ)))))
    (Proof.imp_intro (Proof.and_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.imp_intro ?_)))
  · rwa [WFF.bindFree_openFree] at this
  exact Proof.retx_absurd hS _ _ _ hu' (Proof.ret_unitW hS _ _ _ _ _ θΨ
    (Proof.conv (openFree_unitBodyD_kThetaD hu hS sb θΨ)
      (Proof.and_elim_r (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
    (Proof.conv (openFree_kPsiD hu sb θΨ) (Proof.lookup List.mem_cons_self)))

/-- At a node every body at the witnessed shape is a hole formula at the roots' items and the
    slot (`pack2`). -/
theorem kPsiD_pack2 {l : List VarType} {C X : VarType}
    (Θ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1) :
    kPsiD (Γ := ctxOf l) (tupT l).2 (pack2 l (RShape.wit (.box C) X).ty Θ) = Θ :=
  (holeAt_tupT_pack2 (Ctx.Le.refl _) Θ).trans (WFF.mono_refl _ Θ)

/-- ⭐**The K-law with a possible part at a node**, for any body. -/
def Proof.retD_K_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {C X : VarType} {c : Ann (.VTypeProd C X)}
    (t : Term σ (ctxOf l) (.VTypeProd C X) c)
    (Φ Θ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retS hS (.wit (.box C) X) t Φ))
    (q : Proof σ (ctxOf l) Δ (WFF.neg (WFF.retS hS (.wit (.box C) X) t Θ))) :
    Proof σ (ctxOf l) Δ (WFF.retS hS (.wit (.box C) X) t (WFF.and Φ (WFF.neg Θ))) :=
  Proof.conv (by rw [kPsiD_pack2]) (Proof.retD_K hS t Φ (tupT l).2
    (pack2 l (RShape.wit (.box C) X).ty Θ) p (Proof.conv (by rw [kPsiD_pack2]) q))

/-! ## With a possible part, at an object with companions (docs §11.21, stage 3b) -/

/-- `kThetaD` at an object with companions `co`. -/
def kThetaDC (hS : ModalSys.BStrong = true) {A C X : VarType} (co : List (List Step))
    (ho : C.CompOk co)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A))) 1 :=
  WFF.neg (WFF.retS hS (.wit (.boxC C co ho) X)
    (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeProd (C.compsFlat co) X)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).boxIn).insert (RShape.wit (.box C) X).ty)
      (Term.pair
        (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner A
          ((Ctx.le_insert ((Ctx.slotsFrom_empty.insert _).boxIn.root) _).ref
            (Ctx.ref_inner (Ctx.ref_snd_of (Ctx.ref_insert_root Ctx.empty (.bnd 0)
              (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A)))))))
        (Term.eta (.root (.bnd 1)) _ (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

theorem holeAt_kThetaDC {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C X : VarType} (co : List (List Step)) (ho : C.CompOk co)
    {c : Ann (.VTypeProd (C.compsFlat co) X)} (w : Term σ Δ (.VTypeProd (C.compsFlat co) X) c)
    {a : Ann A} (s : Term σ Δ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF.holeAt hs (Term.pair w (Term.boxtm s)) (kThetaDC hS co ho θΨ) =
      WFF.neg (WFF.retS hS (.wit (.boxC C co ho) X) w (WFF.holeAt (hs.boxIn.insert _)
        (Term.pair (Term.mono (Ctx.le_insert hs.boxIn.root _) s)
          (Term.eta (.root (.bnd d)) _ (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kThetaDC
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.boxtm s)))).at
      (.root (.bnd 0)) = .tm (Term.pair w (Term.boxtm s)) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  refine congrArg (fun φ => WFF.imp φ WFF.bot) (WFF.retS_congr hS _ ?_ ?_)
  · exact Term.subst_eta_tm _ _ _ _ _ _ w (by rw [Subst.at_proj _ _ rfl, h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
    · refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
      rfl
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) d _ _)

theorem holeRead_kThetaDC {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true)
    {A C X : VarType} (co : List (List Step)) (ho : C.CompOk co)
    {c : Ann (.VTypeProd (C.compsFlat co) X)} (t : Term σ Γ (.VTypeProd (C.compsFlat co) X) c)
    {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF.holeRead (Term.pair t (Term.boxtm sb)) (kThetaDC hS co ho θΨ) =
      WFF.neg (WFF.retS hS (.wit (.boxC C co ho) X) t (kPsiD sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaDC]
  rfl

section OpenC

variable {Γ : Ctx} [Γ.NoSlots] {u : ℕ} (hu : Γ.boxIn.RootFresh (.free u))

/-- Opening the companion unit's conjunct along the possible part at `u`. -/
theorem openFree_unitBodyDC_kThetaDC (hS : ModalSys.BStrong = true) {A C X : VarType}
    (co : List (List Step)) (ho : C.CompOk co) {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots
        (WFF.unitBodyDC (Γ := Γ) hS co ho sb [] (Or.inl rfl) (kThetaDC hS co ho θΨ)) =
      WFF.retx hS (.step (.root (.free u)) .snd)
        ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩
        (Term.mono (Ctx.le_insert hu.root _) sb)
        (WFF.neg (WFF.unitBodyWC (Γ := Γ.boxIn.insert (.free u) (RShape.wit (.box C) X).ty) hS
          [] (Or.inl rfl)
          (Term.eta (VarSymb.step (.root (.free u)) .fst).inner C
            (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
          (Term.eta (.step (.step (.root (.free u)) .snd) .dia) X
            (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
          co ho θΨ)) := by
  have hu0 := Ctx.ref_insert_root Γ.boxIn (.bnd 0) (RShape.wit (.box C) X).ty
  have hsnd := Ctx.ref_snd_of hu0
  have hθ := Subst.ok_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn))
    (RShape.wit (.box C) X).ty hu.root
  have hc := Subst.coh_toFree (σ := σ) (d := 0) (Subst.ok_idRen (Δ := Γ.boxIn)) Subst.coh_idRen
    (Ctx.NoSlots.slots (Γ := Γ.boxIn)) (RShape.wit (.box C) X).ty hu.root
  have h0 : ((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box C) X).ty hu.root).at
      (.root (.bnd 0)) = .ren (.root (.free u)) := by
    rw [Subst.at_nonproj _ rfl]
    exact Subst.toFree_root _ _ _ _ _
  have hw : (((Subst.idRen (σ := σ) Γ.boxIn).toFree 0 u (RShape.wit (.box C) X).ty
      hu.root).at (.step (.root (.bnd 0)) .snd)).idxAlong [] = .step (.root (.free u)) .snd := by
    rw [Subst.at_proj _ _ rfl, h0]
    rfl
  have hsl := ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insertFree u
    (RShape.wit (.box C) X).ty).diaIn (.step (.root (.free u)) .snd)
  unfold WFF.openFree WFF.unitBodyDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ (.step (.root (.free u)) .snd) rfl
    ⟨X, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ hsl (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (subst_toFree_mono_sig hu sb) ?_
  rw [WFF.subst_holeAt]
  have hT := Ctx.ref_insert_root Γ.boxIn (.free u) (RShape.wit (.box C) X).ty
  refine (WFF.holeAt_congr _ (sig_pair (sig_pair
    (Term.subst_compsSlot _ _ (Ctx.ref_fst_of hT)
      ((Ctx.le_boxIn_diaIn _ _).trans (Ctx.le_insert hsl.root (.VTypeBox A))) _ _ _
      (fun q _ hq hr => ?_) co ho)
    (Term.subst_eta_renAt _ _ _ X _ (.step (.step (.root (.free u)) .snd) .dia) _
      ((Ctx.le_insert hsl.root (.VTypeBox A)).ref (Ctx.ref_diaIn_of (Ctx.ref_snd_of hT))) ?_))
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by
        rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
      Subst.dia_eq_box_mono (Δ₁ := Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) _ _ _ _ _
        (Ctx.ref_inner hr),
      Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q (by rw [Subst.at_proj _ _ rfl, h0]; rfl) hq)]
    rfl
  · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
    dsimp only [Subst.dia]
    rw [if_pos rfl, Subst.at_proj _ _ rfl, h0]
    rfl
  · refine (holeAt_kThetaDC _ hS co ho _ (Term.eta (VarSymb.root (.bnd 0)).inner A
      (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) θΨ).trans ?_
    refine congrArg WFF.neg (WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_)
    · exact (mono_compsSlot (Ctx.ref_fst_of hT) (Ctx.Le.refl _) _ co ho).symm.trans
        (sig_mono _ (compsVal_eta (Ctx.ref_fst_of hT) co ho).symm)
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
    · refine WFF.holeAt_congr _ (sig_pair ?_ rfl) θΨ
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

end OpenC

/-- ⭐**The K-law with a possible part, at an object with companions**: `Proof.retD_K` with the
    first unit's outer object and the far unit's inner object carrying the companions. -/
def Proof.retD_KC {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {C X : VarType} (co : List (List Step)) (ho : C.CompOk co)
    {c : Ann (.VTypeProd (C.compsFlat co) X)} (t : Term σ Γ (.VTypeProd (C.compsFlat co) X) c)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1) {A : VarType}
    {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (RShape.wit (.box C) X).ty)) 1)
    (p : Proof σ Γ Δ (WFF.retS hS (.wit (.boxC C co ho) X) t Φ))
    (q : Proof σ Γ Δ (WFF.neg (WFF.retS hS (.wit (.boxC C co ho) X) t (kPsiD sb θΨ)))) :
    Proof σ Γ Δ (WFF.retS hS (.wit (.boxC C co ho) X) t (WFF.and Φ (WFF.neg (kPsiD sb θΨ)))) := by
  have P1 := Proof.ret_unitDC hS .nec co ho t Φ sb [] (Or.inl rfl) (kThetaDC hS co ho θΨ) p
    (Proof.conv (holeRead_kThetaDC hS co ho t sb θΨ).symm q)
  refine Proof.ret_monoS hS .nec (S := .wit (.boxC C co ho) X) t _ _ P1
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) ?_))
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ.boxIn)) :=
    Ctx.Presented.fresh_bound _ le_rfl
  have hu' : (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ.boxIn))
      (RShape.wit (.box C) X).ty).RootFresh (.free (Ctx.Presented.bound Γ.boxIn + 1)) :=
    (Ctx.Presented.fresh_bound _ (Nat.le_succ _)).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  have := Proof.all_intro (Δ := []) (Ctx.Presented.bound Γ.boxIn) (RShape.wit (.box C) X).ty hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.imp (WFF.and Φ (WFF.unitBodyDC hS co ho sb [] (Or.inl rfl) (kThetaDC hS co ho θΨ)))
        (WFF.and Φ (WFF.neg (kPsiD sb θΨ)))))
    (Proof.imp_intro (Proof.and_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.imp_intro ?_)))
  · rwa [WFF.bindFree_openFree] at this
  exact Proof.retx_absurd hS _ _ _ hu' (Proof.ret_unitWC hS _ [] (Or.inl rfl) _ _ _ _ co ho θΨ
    (Proof.conv (openFree_unitBodyDC_kThetaDC hu hS co ho sb θΨ)
      (Proof.and_elim_r (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
    (Proof.conv (openFree_kPsiD hu sb θΨ) (Proof.lookup List.mem_cons_self)))

/-- The K-law with a possible part at a node, at an object with companions, for any body. -/
def Proof.retD_KC_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {C X : VarType} (co : List (List Step)) (ho : C.CompOk co)
    {c : Ann (.VTypeProd (C.compsFlat co) X)}
    (t : Term σ (ctxOf l) (.VTypeProd (C.compsFlat co) X) c)
    (Φ Θ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retS hS (.wit (.boxC C co ho) X) t Φ))
    (q : Proof σ (ctxOf l) Δ (WFF.neg (WFF.retS hS (.wit (.boxC C co ho) X) t Θ))) :
    Proof σ (ctxOf l) Δ (WFF.retS hS (.wit (.boxC C co ho) X) t (WFF.and Φ (WFF.neg Θ))) :=
  Proof.conv (by rw [kPsiD_pack2]) (Proof.retD_KC hS co ho t Φ (tupT l).2
    (pack2 l (RShape.wit (.box C) X).ty Θ) p (Proof.conv (by rw [kPsiD_pack2]) q))

end BArrow

end V12M
