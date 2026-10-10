import QML.QML_v12m_RetKD

/-!
# QML v12m — the K-law of the doubly witnessed returning possibility

`◇_x[⟨d, e⟩ ↦ t] Φ, ¬◇_x[⟨d, e⟩ ↦ t] Ψ ⊢ ◇_x[⟨d, e⟩ ↦ t](Φ ∧ ¬Ψ)` (docs §11.20), the fourth form:
along `x`, at the witnessed shape `□C × ◇X` (`e ⇝ t.2`, the witness of the way home), for `Ψ`
given by a home necessary object, `x`'s content and a hole formula (`kPsiXD`; at a network node
every body has this form, `pack2X`).  The form is its own mirror, so one unit serves both ends:
1. at home, `ret_unitWD` carries the negated premise out, `x` returning as the possible part `e₁`
   (`kThetaWD θΨ`);
2. at the far world, `Ψ` is `ret_unitWD`'s premise along `e₁`, which brings it back home with `e₁`
   as the leg and `x` as the possible part, and the conjuncts clash (`retxS_absurd`).

This makes the child of a doubly witnessed atom consistent.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-- A returning possibility along a witness, at any shape, with a contradictory body is absurd. -/
def Proof.retxS_absurd {Γ : Ctx} [Γ.NoSlots] {Δ : List (WFF σ Γ 0)}
    (hS : ModalSys.BStrong = true) {x : VarSymb} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (S : RShape) {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (U : WFF σ ((Γ.diaIn x).insert (.bnd 0) S.ty) 1) {u : ℕ} (hu : Γ.RootFresh (.free u))
    (p : Proof σ Γ Δ (WFF.retxS hS x hx S t (WFF.and (WFF.neg U) U))) : Proof σ Γ Δ .bot := by
  have hd := Proof.ret_diaS hS (.pos x hx) t _ p
  have q : Proof σ (Γ.diaIn x) [WFF.ex S.ty (WFF.and (WFF.neg U) U)] .bot := by
    refine Proof.ex_elim u S.ty (hu.diaIn x)
      (φ := WFF.openFree u (hu.diaIn x) Ctx.NoSlots.slots (WFF.and (WFF.neg U) U)) (ψ := .bot)
      (Proof.conv (congrArg (WFF.ex _) (WFF.bindFree_openFree _ _ _ _).symm)
        (Proof.lookup List.mem_cons_self)) ?_
    exact Proof.imp_elim (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.and_elim_r (Proof.lookup List.mem_cons_self))
  exact Proof.dia_bot x hx (Proof.imp_elim (Proof.ofSubset (fun _ h => by simp at h)
    (Proof.imp_intro (Proof.K_dia x hx (Δ₁ := []) (Δ₂ := []) q))) hd)

/-- The body `Ψ(⟨d, e⟩)` over `x`'s view at the witnessed shape, as a hole formula `θΨ` read at a
    home necessary object `sb`, `x`'s content and the slot. -/
def kPsiXD {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {X A C Xe : VarType}
    (hX : Γ.ref x = some (.VTypeDia X)) {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd A X) (RShape.wit (.box C) Xe).ty)) 1) :
    WFF σ ((Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.diaIn x)).insert _)
    (Term.pair
      (Term.pair
        (Term.mono ((Ctx.le_boxIn_diaIn Γ x).trans
          (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _)) sb)
        (Term.eta (x.step .dia) X
          ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.diaIn x)).root _).ref
            (Ctx.ref_diaIn_of hX))))
      (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)))
    θΨ

/-- The negated premise as a hole formula over a value `y` and a witnessed object `⟨□s, e₁⟩`:
    `¬◇_{e₁}[⟨d, e⟩ ↦ y] θΨ(⟨s.box, e₁.dia⟩, ⟨d, e⟩)`. -/
def kThetaWD (hS : ModalSys.BStrong = true) {A C X Xe : VarType}
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd A X) (RShape.wit (.box C) Xe).ty)) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty)) 1 :=
  WFF.neg (WFF.retxS hS (.step (.step (.root (.bnd 0)) .snd) .snd) ⟨X, kThetaW_ref⟩
    (.wit (.box C) Xe)
    (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeProd C Xe)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).diaIn _).insert (RShape.wit (.box C) Xe).ty)
      (Term.pair
        (Term.pair
          (Term.eta (VarSymb.step (.step (.root (.bnd 0)) .snd) .fst).inner A
            ((Ctx.le_insert (((Ctx.slotsFrom_empty.insert _).diaIn _).root)
              (RShape.wit (.box C) Xe).ty).ref
              ((Ctx.le_boxIn_diaIn _ _).ref (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_snd_of
                (Ctx.ref_insert_root Ctx.empty (.bnd 0)
                  (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty))))))))
          (Term.eta (.step (.step (.step (.root (.bnd 0)) .snd) .snd) .dia) X
            ((Ctx.le_insert (((Ctx.slotsFrom_empty.insert _).diaIn _).root)
              (RShape.wit (.box C) Xe).ty).ref (Ctx.ref_diaIn_of kThetaW_ref))))
        (Term.eta (.root (.bnd 1)) (RShape.wit (.box C) Xe).ty (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

/-- The hole formula read, at any depth, at a value and a witnessed object `⟨□s, v⟩` for a
    possible variable `v`. -/
theorem holeAt_kThetaWD {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C X Xe : VarType} {c : Ann (.VTypeProd C Xe)} (w : Term σ Δ (.VTypeProd C Xe) c)
    {a : Ann A} (s : Term σ Δ.boxIn A a) {v : VarSymb} (hv : Δ.ref v = some (.VTypeDia X))
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd A X) (RShape.wit (.box C) Xe).ty)) 1) :
    WFF.holeAt hs (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv)))))
        (kThetaWD hS θΨ) =
      WFF.neg (WFF.retxS hS v ⟨X, hv⟩ (.wit (.box C) Xe) w (WFF.holeAt ((hs.diaIn v).insert _)
        (Term.pair
          (Term.pair (Term.mono ((Ctx.le_boxIn_diaIn Δ v).trans
              (Ctx.le_insert (hs.diaIn v).root _)) s)
            (Term.eta (v.step .dia) X
              ((Ctx.le_insert (hs.diaIn v).root _).ref (Ctx.ref_diaIn_of hv))))
          (Term.eta (.root (.bnd d)) _ (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kThetaWD
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.pair (Term.boxtm s)
      (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))).at
      (.root (.bnd 0)) = .tm (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  have hθ : Subst.Ok (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty))
      (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair w (Term.pair (Term.boxtm s)
        (Term.diatm v ⟨X, hv⟩ (Term.eta (v.step .dia) X (Ctx.ref_diaIn_of hv))))))) :=
    Subst.ok_single (Ctx.empty_le Δ) rfl
  have hc := Subst.coh_single (σ := σ) (r := .bnd 0)
    (T := .VTypeProd (.VTypeProd C Xe) (RShape.wit (.box A) X).ty) (Ctx.RootFresh.empty _)
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

/-- At home, the hole formula read at the value, the home object and `x` is the negated premise
    along `x`. -/
theorem holeRead_kThetaWD {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {x : VarSymb}
    {X A C Xe : VarType} (hX : Γ.ref x = some (.VTypeDia X)) {c : Ann (.VTypeProd C Xe)}
    (y : Term σ Γ (.VTypeProd C Xe) c) {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd A X) (RShape.wit (.box C) Xe).ty)) 1) :
    WFF.holeRead (Term.pair y (Term.pair (Term.boxtm sb)
        (Term.diatm x ⟨X, hX⟩ (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)))))
        (kThetaWD hS θΨ) =
      WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) y (kPsiXD hX sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaWD _ hS y sb hX]
  rfl

section Open

variable {Γ : Ctx} [Γ.NoSlots] {x : VarSymb} {X A C Xe : VarType}
  (hX : Γ.ref x = some (.VTypeDia X)) {u : ℕ} (hu : (Γ.diaIn x).RootFresh (.free u))

omit [ModalSys.NoFour] in
/-- Opening the body `kPsiXD` at `u` reads `θΨ` at the home object, `x`'s content and `u`. -/
theorem openFree_kPsiXD {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd A X) (RShape.wit (.box C) Xe).ty)) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (kPsiXD hX sb θΨ) =
      WFF.holeRead (Term.pair
        (Term.pair (Term.mono (Ctx.le_insert hu.root _) (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb))
          (Term.mono (Ctx.le_insert hu.root _) (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))))
        (Term.eta (.root (.free u)) (RShape.wit (.box C) Xe).ty (Ctx.ref_insert_root _ _ _)))
        θΨ := by
  unfold kPsiXD WFF.openFree
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

/-- Opening the doubly witnessed unit's conjunct of the home step at `u`: a returning possibility
    along `u`'s possible part, with the witness `x` as its possible part, whose body is the negated
    unit (`unitBodyWD`) at `u`'s necessary object and content. -/
theorem openFree_unitBodyWD_kThetaWD (hS : ModalSys.BStrong = true) {a : Ann A}
    (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd A X) (RShape.wit (.box C) Xe).ty)) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.unitBodyWD (Γ := Γ) hS sb
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX)) (kThetaWD hS θΨ)) =
      WFF.retxS hS (.step (.root (.free u)) .snd)
        ⟨Xe, Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _)⟩ (.wit (.box A) X)
        (Term.pair (Term.mono (Ctx.le_insert hu.root _) (Term.mono (Ctx.le_boxIn_diaIn Γ x) sb))
          (Term.mono (Ctx.le_insert hu.root _) (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))))
        (WFF.neg (WFF.unitBodyWD (Γ := (Γ.diaIn x).insert (.free u) (RShape.wit (.box C) Xe).ty)
          hS
          (Term.eta (VarSymb.step (.root (.free u)) .fst).inner C
            (Ctx.ref_inner (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
          (Term.eta (.step (.step (.root (.free u)) .snd) .dia) Xe
            (Ctx.ref_diaIn_of (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
          θΨ)) := by
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
  · refine (holeAt_kThetaWD _ hS _ (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner A
      (Ctx.ref_inner (Ctx.ref_fst_of hT'))) (Ctx.ref_snd_of hT') θΨ).trans ?_
    refine congrArg WFF.neg (WFF.retxS_congr hS _ _ _ (sig_pair ?_ ?_) ?_)
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
    · refine WFF.holeAt_congr _ (sig_pair (sig_pair ?_ rfl) rfl) θΨ
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

end Open

/-- ⭐**The K-law of the doubly witnessed returning possibility** (docs §11.20):
    `◇_x[⟨d, e⟩ ↦ t] Φ, ¬◇_x[⟨d, e⟩ ↦ t] Ψ ⊢ ◇_x[⟨d, e⟩ ↦ t](Φ ∧ ¬Ψ)`.  At home `ret_unitWD` carries
    the negated premise out with `x` as the returning possible part (`kThetaWD`); at the far
    world, if `Ψ` held, `ret_unitWD` along the returned part would bring it back to clash with it
    (`Proof.retxS_absurd`). -/
def Proof.retxD_K {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {x : VarSymb} {X : VarType} (hX : Γ.ref x = some (.VTypeDia X)) {C Xe : VarType}
    {c : Ann (.VTypeProd C Xe)} (y : Term σ Γ (.VTypeProd C Xe) c)
    (Φ : WFF σ ((Γ.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty) 1) {A : VarType}
    {a : Ann A} (sb : Term σ Γ.boxIn A a)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd A X) (RShape.wit (.box C) Xe).ty)) 1)
    (p : Proof σ Γ Δ (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) y Φ))
    (q : Proof σ Γ Δ (WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) y (kPsiXD hX sb θΨ)))) :
    Proof σ Γ Δ (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) y
      (WFF.and Φ (WFF.neg (kPsiXD hX sb θΨ)))) := by
  have P1 := Proof.ret_unitWD hS ⟨X, hX⟩ y Φ sb (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
    (kThetaWD hS θΨ) p (Proof.conv (holeRead_kThetaWD hS hX y sb θΨ).symm q)
  refine Proof.ret_monoS hS (.pos x ⟨X, hX⟩) (S := .wit (.box C) Xe) y _ _ P1
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.boxxK (Δ := []) ⟨X, hX⟩ ?_))
  have hu : (Γ.diaIn x).RootFresh (.free (Ctx.Presented.bound (Γ.diaIn x))) :=
    Ctx.Presented.fresh_bound _ le_rfl
  have hu' : ((Γ.diaIn x).insert (.free (Ctx.Presented.bound (Γ.diaIn x)))
      (RShape.wit (.box C) Xe).ty).RootFresh (.free (Ctx.Presented.bound (Γ.diaIn x) + 1)) :=
    (Ctx.Presented.fresh_bound _ (Nat.le_succ _)).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  have := Proof.all_intro (Δ := []) (Ctx.Presented.bound (Γ.diaIn x)) (RShape.wit (.box C) Xe).ty
    hu (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.imp (WFF.and Φ (WFF.unitBodyWD hS sb (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hX))
        (kThetaWD hS θΨ))) (WFF.and Φ (WFF.neg (kPsiXD hX sb θΨ)))))
    (Proof.imp_intro (Proof.and_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.imp_intro ?_)))
  · rwa [WFF.bindFree_openFree] at this
  exact Proof.retxS_absurd hS _ _ _ _ hu' (Proof.ret_unitWD hS _ _ _ _ _ θΨ
    (Proof.conv (openFree_unitBodyWD_kThetaWD hX hu hS sb θΨ)
      (Proof.and_elim_r (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
    (Proof.conv (openFree_kPsiXD hX hu sb θΨ) (Proof.lookup List.mem_cons_self)))

/-- At a node every body over `x`'s view at the witnessed shape is a hole formula at the roots'
    items, `x`'s content and the slot (`pack2X`). -/
theorem kPsiXD_pack2X {l : List VarType} {x : VarSymb} {X C Xe : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X))
    (Θ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty) 1) :
    kPsiXD (Γ := ctxOf l) hX (tupT l).2 (pack2X (RShape.wit (.box C) Xe).ty hX Θ) = Θ :=
  (holeAt_tupT_pack2X (Ctx.Le.refl _) hX Θ).trans (WFF.mono_refl _ Θ)

/-- ⭐**The doubly witnessed K-law at a node**, for any body. -/
noncomputable def Proof.retxD_K_node (hS : ModalSys.BStrong = true) {l : List VarType}
    {Δ : List (WFF σ (ctxOf l) 0)} {x : VarSymb} {X : VarType}
    (hX : (ctxOf l).ref x = some (.VTypeDia X)) {C Xe : VarType} {c : Ann (.VTypeProd C Xe)}
    (t : Term σ (ctxOf l) (.VTypeProd C Xe) c)
    (Φ Θ : WFF σ (((ctxOf l).diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty) 1)
    (p : Proof σ (ctxOf l) Δ (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) t Φ))
    (q : Proof σ (ctxOf l) Δ (WFF.neg (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) t Θ))) :
    Proof σ (ctxOf l) Δ (WFF.retxS hS x ⟨X, hX⟩ (.wit (.box C) Xe) t (WFF.and Φ (WFF.neg Θ))) :=
  Proof.conv (by rw [kPsiXD_pack2X]) (Proof.retxD_K hS hX t Φ (tupT l).2
    (pack2X (RShape.wit (.box C) Xe).ty hX Θ) p (Proof.conv (by rw [kPsiXD_pack2X]) q))

end BArrow

end V12M
