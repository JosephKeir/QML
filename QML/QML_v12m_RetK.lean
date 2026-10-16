import QML.QML_v12m_BRet

/-!
# QML v12m — the K-law of the returning possibility

`◇[d ↦ t] Φ, ¬◇[d ↦ t] Ψ ⊢ ◇[d ↦ t](Φ ∧ ¬Ψ)` (docs §11.17, §11.20), for a body `Ψ` given by a
home necessary object `sb` and a hole formula `θΨ` (`kPsi`; at a network node every body has this
form, `pack2`).  Two units:
1. at home, `ret_unit` carries the negated premise out, as the hole formula `kTheta θΨ`;
2. at the far world, `ret_unit` brings `Ψ` back, and the two conjuncts clash (`ret_absurd`).

This is what makes the child of a returning-possibility atom consistent: its seed is the atom's
body with the dual box's contents.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-- The body `Ψ(e)`, as a hole formula `θΨ` read at a home necessary object `sb` and the slot. -/
def kPsi {Γ : Ctx} [Γ.NoSlots] {A C : VarType} {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1 :=
  WFF.holeAt ((Ctx.NoSlots.slots (Γ := Γ.boxIn)).insert _)
    (Term.pair (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ.boxIn)).root _) sb)
      (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _)))
    θΨ

/-- The negated premise as a hole formula over a value `y` and a necessary object `s`:
    `¬◇[e ↦ y] θΨ(s.box, e)`. -/
def kTheta (hS : ModalSys.BStrong = true) {A C : VarType}
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd A (.VTypeBox C))) 1 :=
  WFF.neg (WFF.ret hS
    (Term.eta (.step (.root (.bnd 0)) .fst) A (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).boxIn).insert (.VTypeBox A))
      (Term.pair
        (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner C
          ((Ctx.le_insert ((Ctx.slotsFrom_empty.insert _).boxIn.root) (.VTypeBox A)).ref
            (Ctx.ref_inner (Ctx.ref_snd_of
              (Ctx.ref_insert_root Ctx.empty (.bnd 0) (.VTypeProd A (.VTypeBox C)))))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

/-- The hole formula read, at any depth, at a value and a necessary object `□s`. -/
theorem holeAt_kTheta {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C : VarType} {a : Ann A} (y : Term σ Δ A a) {c : Ann C} (s : Term σ Δ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.holeAt hs (Term.pair y (Term.boxtm s)) (kTheta hS θΨ) =
      WFF.neg (WFF.ret hS y (WFF.holeAt (hs.boxIn.insert _)
        (Term.pair (Term.mono (Ctx.le_insert hs.boxIn.root _) s)
          (Term.eta (.root (.bnd d)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kTheta
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair y (Term.boxtm s)))).at
      (.root (.bnd 0)) = .tm (Term.pair y (Term.boxtm s)) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  refine congrArg (fun φ => WFF.imp φ WFF.bot) (WFF.ret_congr hS ?_ ?_)
  · exact Term.subst_eta_tm _ _ _ _ _ _ y (by rw [Subst.at_proj _ _ rfl, h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
    · refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
      rfl
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) d _ _)

/-- At home, the hole formula read at the value and the home object is the negated premise. -/
theorem holeRead_kTheta {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A C : VarType}
    {a : Ann A} (t : Term σ Γ A a) {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.holeRead (Term.pair t (Term.boxtm sb)) (kTheta hS θΨ) =
      WFF.neg (WFF.ret hS t (kPsi sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kTheta]
  rfl

section Open

variable {Γ₀ : Ctx} [Γ₀.NoSlots] {u : ℕ} (hu : Γ₀.RootFresh (.free u))

omit [ModalSys.NoFour] in
/-- Opening a binder leaves a term from below it alone. -/
theorem subst_toFree_mono_sig {T : VarType} {B : VarType} {b : Ann B} (sb : Term σ Γ₀ B b) :
    (⟨_, Term.subst (VarSymb.slotToFree id 0 u) ((Subst.idRen Γ₀).toFree 0 u T hu.root)
        (Subst.ok_toFree Subst.ok_idRen T hu.root)
        (Subst.coh_toFree Subst.ok_idRen Subst.coh_idRen Ctx.NoSlots.slots T hu.root)
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := Γ₀)).root T) sb)⟩ :
        Σ c, Term σ (Γ₀.insert (.free u) T) B c) =
      ⟨_, Term.mono (Ctx.le_insert hu.root T) sb⟩ := by
  rw [Term.subst_mono]
  refine Term.subst_ren _ _ _ _ (Subst.at_ren_of fun v U hlp hv => ?_) sb
  have hvr : v ≠ .root (.bnd 0) := fun e => by
    subst e
    rw [(Ctx.NoSlots.slots (Γ := Γ₀)).root] at hv
    cases hv
  rw [Subst.toFree_ne _ _ _ _ hvr]
  change ((Subst.idRen Γ₀) v).mono _ = _
  rw [← Subst.at_nonproj (Subst.idRen Γ₀) hlp, Subst.at_idRen]
  rfl

omit [ModalSys.NoFour] in
/-- Opening the body `kPsi` at `u` reads `θΨ` at the home object and `u`. -/
theorem openFree_kPsi {Γ : Ctx} [Γ.NoSlots] (hu : Γ.boxIn.RootFresh (.free u)) {A C : VarType}
    {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (kPsi sb θΨ) =
      WFF.holeRead (Term.pair (Term.mono (Ctx.le_insert hu.root _) sb)
        (Term.eta (.root (.free u)) (.VTypeBox A) (Ctx.ref_insert_root _ _ _))) θΨ := by
  unfold kPsi WFF.openFree
  rw [WFF.subst_holeAt, WFF.holeRead_eq_holeAt]
  exact WFF.holeAt_congr _ (sig_pair (subst_toFree_mono_sig hu sb)
    (Term.subst_eta_renAt _ _ _ _ _ _ _ _ (by
      change Subst.toFree _ _ _ _ _ (.root (.bnd 0)) = _
      exact Subst.toFree_root _ _ _ _ _))) θΨ

/-- Opening the unit's conjunct of the home step at `u`: a returning possibility whose body is the
    negation of the unit at the far world, at `u`'s content. -/
theorem openFree_unitBody_kTheta {Γ : Ctx} [Γ.NoSlots] (hu : Γ.boxIn.RootFresh (.free u))
    (hS : ModalSys.BStrong = true) {A C : VarType} {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots (WFF.unitBody (Γ := Γ) hS sb (kTheta hS θΨ)) =
      WFF.ret hS (Term.mono (Ctx.le_insert hu.root _) sb)
        (WFF.neg (WFF.unitBody (Γ := Γ.boxIn.insert (.free u) (.VTypeBox A)) hS
          (Term.eta (VarSymb.root (.free u)).inner A
            (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) θΨ)) := by
  unfold WFF.openFree WFF.unitBody
  refine WFF.ret_congr hS (subst_toFree_mono_sig hu sb) ?_
  rw [WFF.subst_holeAt]
  refine (WFF.holeAt_congr _ (sig_pair
    (Term.subst_eta_renAt _ _ _ _ _ (VarSymb.root (.free u)).inner _
      ((Ctx.le_insert (Ctx.NoSlots.slots
        (Γ := (Γ.boxIn.insert (.free u) (.VTypeBox A)).boxIn)).root _).ref
        (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) ?_)
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
      Subst.box_at_inner_ren _ (by
        change Subst.toFree _ _ _ _ _ (.root (.bnd 0)) = _
        exact Subst.toFree_root _ _ _ _ _)]
    rfl
  · refine (holeAt_kTheta _ hS _ (Term.eta (VarSymb.root (.bnd 0)).inner C
      (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) θΨ).trans ?_
    refine congrArg WFF.neg (WFF.ret_congr hS ?_ ?_)
    · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm
    · refine WFF.holeAt_congr _ (sig_pair ?_ rfl) θΨ
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

end Open

/-- ⭐**The K-law of the returning possibility** (docs §11.17, §11.20):
    `◇[d ↦ t] Φ, ¬◇[d ↦ t] Ψ ⊢ ◇[d ↦ t](Φ ∧ ¬Ψ)`, for `Ψ` given by a home necessary object and a
    hole formula.  At home `ret_unit` carries the negated premise out (`kTheta`); at the far world,
    if `Ψ` held, `ret_unit` would bring it back to clash with it (`Proof.ret_absurd`). -/
def Proof.ret_K {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {A C : VarType} {a : Ann A} (t : Term σ Γ A a)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1)
    (p : Proof σ Γ Δ (WFF.ret hS t Φ)) (q : Proof σ Γ Δ (WFF.neg (WFF.ret hS t (kPsi sb θΨ)))) :
    Proof σ Γ Δ (WFF.ret hS t (WFF.and Φ (WFF.neg (kPsi sb θΨ)))) := by
  have P1 := Proof.ret_unit hS .nec t Φ sb (kTheta hS θΨ) p
    (Proof.conv (holeRead_kTheta hS t sb θΨ).symm q)
  refine Proof.ret_mono hS .nec t _ _ P1
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) ?_))
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ)) :=
    (Ctx.Presented.fresh_bound _ le_rfl).boxIn
  have hu' : (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ)) (.VTypeBox A)).RootFresh
      (.free (Ctx.Presented.bound Γ + 1)) :=
    ((Ctx.Presented.fresh_bound _ (Nat.le_succ _)).boxIn).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  have core : Proof σ (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ)) (.VTypeBox A))
      [WFF.openFree _ hu Ctx.NoSlots.slots (kPsi sb θΨ),
        WFF.openFree _ hu Ctx.NoSlots.slots (WFF.and Φ (WFF.unitBody hS sb (kTheta hS θΨ)))]
      .bot :=
    Proof.ret_absurd hS _ _ hu' (Proof.ret_unit hS .nec _ _ _ θΨ
      (Proof.conv (openFree_unitBody_kTheta hu hS sb θΨ)
        (Proof.and_elim_r (φ := WFF.openFree _ hu Ctx.NoSlots.slots Φ)
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
      (Proof.conv (openFree_kPsi hu sb θΨ) (Proof.lookup List.mem_cons_self)))
  have := Proof.all_intro (Δ := []) (Ctx.Presented.bound Γ) (.VTypeBox A) hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.imp (WFF.and Φ (WFF.unitBody hS sb (kTheta hS θΨ))) (WFF.and Φ (WFF.neg (kPsi sb θΨ)))))
    (Proof.imp_intro (Proof.and_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.imp_intro core)))
  rwa [WFF.bindFree_openFree] at this

/-! ## The K-law at an object with companions (docs §11.21, stage 3b)

The same derivation, with the first unit's outer object carrying the companions `co` and the second
unit's inner object carrying them too.  The two meet because the companions' contents of an
η-expanded necessary object are the companions' items (`compsVal_eta`). -/

omit [ModalSys.NoFour] in
/-- Along a companion path, an η-expanded entry's projections are η-expansions. -/
theorem Subst.at_ext_eta (hT : ModalSys.T = true) {Δ : Ctx} (θ : Subst σ Δ) (p : List Step) :
    ∀ {A : VarType} {v x : VarSymb} (hx : Δ.ref x = some A) {C : VarType}, A.compAt p = some C →
      ∀ (h' : Δ.ref (x.ext p) = some (.VTypeBox C)), θ.at v = .tm (Term.eta x A hx) →
      θ.at (v.ext p) = .tm (Term.eta (x.ext p) (.VTypeBox C) h') := by
  induction p with
  | nil =>
      intro A v x hx C hC h' hv
      cases A <;> simp only [VarType.compAt, reduceCtorEq, Option.some.injEq] at hC
      subst hC
      exact hv
  | cons s q ih =>
      intro A v x hx C hC h' hv
      cases A <;> cases s <;> simp only [VarType.compAt, reduceCtorEq] at hC
      · exact ih (Ctx.ref_fst_of hx) hC h' (by rw [Subst.at_proj θ v rfl, hv]; rfl)
      · exact ih (Ctx.ref_snd_of hx) hC h' (by rw [Subst.at_proj θ v rfl, hv]; rfl)
      · exact ih (Ctx.ref_here_of hT hx) hC h'
          (by rw [Subst.at_proj θ v rfl, hv]; exact SubE.proj_here_eta hT hx)

/-- The contents of an η-expanded necessary object's companion: the companion's item. -/
theorem compVal_eta {Γ : Ctx} {u : VarSymb} {A : VarType} (hu : Γ.ref u = some (.VTypeBox A))
    (p : List Step) {ps : List (List Step)} (h : A.CompOk (p :: ps)) :
    compVal (σ := σ) (Term.eta u.inner A (Ctx.ref_inner hu)) p h =
      ⟨_, Term.eta ((VarSymb.step u .here).ext p).inner ((A.compAt p).getD .VTypeOne)
        (Ctx.ref_inner (h.ref_head hu))⟩ := by
  obtain ⟨hT, hall⟩ := h.resolve_left (List.cons_ne_nil _ _)
  have hC : A.compAt p = some ((A.compAt p).getD .VTypeOne) := by
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall p List.mem_cons_self)
    rw [hC]
    rfl
  let θ := Subst.single (σ := σ) (Δ := Γ) (.bnd 0)
    (.tm (Term.boxtm (Term.eta u.inner A (Ctx.ref_inner hu))))
  have h0 : θ.at (.step (.root (.bnd 0)) .here) =
      .tm (Term.eta (.step u .here) A (Ctx.ref_here_of hT hu)) := by
    rw [Subst.at_proj θ _ rfl, Subst.at_single_root]
    exact SubE.proj_here_eta hT hu
  have h1 := Subst.at_ext_eta hT θ p (Ctx.ref_here_of hT hu) hC (h.ref_head hu) h0
  exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ h1)

omit [ModalSys.NoFour] in
theorem mono_compsSlot {Δ Δ' Δ'' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') (hle' : Δ'.Le Δ'') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs),
      (⟨_, Term.mono hle' (compsSlot (σ := σ) hu hle cs h).2⟩ :
        Σ a, Term σ Δ'' (C.compsFlat cs) a) = compsSlot hu (hle.trans hle') cs h
  | [], _ => congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)
  | _ :: ps, h => sig_pair (mono_compsSlot hu hle hle' ps h.tail)
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))

/-- An η-expanded necessary object's value with companions is the slot's. -/
theorem compsVal_eta {Γ : Ctx} {u : VarSymb} {A : VarType} (hu : Γ.ref u = some (.VTypeBox A)) :
    ∀ (cs : List (List Step)) (h : A.CompOk cs),
      compsVal (σ := σ) (Term.eta u.inner A (Ctx.ref_inner hu)) cs h =
        compsSlot hu (Ctx.Le.refl _) cs h
  | [], _ => rfl
  | p :: ps, h => sig_pair (compsVal_eta hu ps h.tail) (compVal_eta hu p h)

/-- `kTheta` at an object with companions: `¬◇^{co}[e ↦ y] θΨ(s.box, e)`. -/
def kThetaC (hS : ModalSys.BStrong = true) {A C : VarType} (co : List (List Step))
    (ho : A.CompOk co)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (A.compsFlat co) (.VTypeBox C))) 1 :=
  WFF.neg (WFF.retS hS (.nec (.boxC A co ho))
    (Term.eta (.step (.root (.bnd 0)) .fst) (A.compsFlat co)
      (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))
    (WFF.holeAt (((Ctx.slotsFrom_empty.insert _).boxIn).insert (.VTypeBox A))
      (Term.pair
        (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner C
          ((Ctx.le_insert ((Ctx.slotsFrom_empty.insert _).boxIn.root) (.VTypeBox A)).ref
            (Ctx.ref_inner (Ctx.ref_snd_of
              (Ctx.ref_insert_root Ctx.empty (.bnd 0)
                (.VTypeProd (A.compsFlat co) (.VTypeBox C)))))))
        (Term.eta (.root (.bnd 1)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 1) _)))
      θΨ))

theorem holeAt_kThetaC {Δ : Ctx} {d : ℕ} (hs : Δ.SlotsFrom d) (hS : ModalSys.BStrong = true)
    {A C : VarType} (co : List (List Step)) (ho : A.CompOk co) {a : Ann (A.compsFlat co)}
    (y : Term σ Δ (A.compsFlat co) a) {c : Ann C} (s : Term σ Δ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.holeAt hs (Term.pair y (Term.boxtm s)) (kThetaC hS co ho θΨ) =
      WFF.neg (WFF.retS hS (.nec (.boxC A co ho)) y (WFF.holeAt (hs.boxIn.insert _)
        (Term.pair (Term.mono (Ctx.le_insert hs.boxIn.root _) s)
          (Term.eta (.root (.bnd d)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd d) _)))
        θΨ)) := by
  unfold WFF.holeAt kThetaC
  have h0 : (Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm (Term.pair y (Term.boxtm s)))).at
      (.root (.bnd 0)) = .tm (Term.pair y (Term.boxtm s)) := by
    change Subst.single _ _ (.root (.bnd 0)) = _
    exact if_pos rfl
  refine congrArg (fun φ => WFF.imp φ WFF.bot) (WFF.retS_congr hS _ ?_ ?_)
  · exact Term.subst_eta_tm _ _ _ _ _ _ y (by rw [Subst.at_proj _ _ rfl, h0]; rfl)
  · rw [WFF.subst_holeAt]
    refine WFF.holeAt_congr _ (sig_pair ?_ ?_) θΨ
    · refine Term.subst_eta_tm _ _ _ _ _ _ _ ?_
      rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
        Subst.box_at_inner_boxtm _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl)]
      rfl
    · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) d _ _)

theorem holeRead_kThetaC {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) {A C : VarType}
    (co : List (List Step)) (ho : A.CompOk co) {a : Ann (A.compsFlat co)}
    (t : Term σ Γ (A.compsFlat co) a) {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.holeRead (Term.pair t (Term.boxtm sb)) (kThetaC hS co ho θΨ) =
      WFF.neg (WFF.retS hS (.nec (.boxC A co ho)) t (kPsi sb θΨ)) := by
  rw [WFF.holeRead_eq_holeAt, holeAt_kThetaC]
  rfl

/-- Opening the companion unit's conjunct of the home step at `u`. -/
theorem openFree_unitBodyC_kThetaC {Γ : Ctx} [Γ.NoSlots] {u : ℕ}
    (hu : Γ.boxIn.RootFresh (.free u)) (hS : ModalSys.BStrong = true) {A C : VarType}
    (co : List (List Step)) (ho : A.CompOk co) {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1) :
    WFF.openFree u hu Ctx.NoSlots.slots
        (WFF.unitBodyC (Γ := Γ) hS co ho sb [] (Or.inl rfl) (kThetaC hS co ho θΨ)) =
      WFF.ret hS (Term.mono (Ctx.le_insert hu.root _) sb)
        (WFF.neg (WFF.unitBodyC (Γ := Γ.boxIn.insert (.free u) (.VTypeBox A)) hS [] (Or.inl rfl)
          (Term.eta (VarSymb.root (.free u)).inner A
            (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) co ho θΨ)) := by
  unfold WFF.openFree WFF.unitBodyC
  refine WFF.retS_congr hS _ (subst_toFree_mono_sig hu sb) ?_
  rw [WFF.subst_holeAt]
  refine (WFF.holeAt_congr _ (sig_pair
    (Term.subst_compsSlot _ _ (Ctx.ref_insert_root Γ.boxIn (.free u) (.VTypeBox A))
      (Ctx.le_insert (Ctx.NoSlots.slots
        (Γ := (Γ.boxIn.insert (.free u) (.VTypeBox A)).boxIn)).root _) _ _ _
      (fun q _ hq _ => ?_) co ho)
    (Term.subst_eta_renAt _ _ _ _ _ (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _)
      (Subst.under_at_slot _ (0 + 1) 0 _ _))) _).trans ?_
  · rw [Subst.at_under_ne _ _ _ (by
        rw [VarSymb.inner_rt, VarSymb.ext_rt]; exact fun h => by cases h),
      Subst.box_at_inner_ren _ (Subst.at_ext_ren _ q (by
        change Subst.toFree _ _ _ _ _ (.root (.bnd 0)) = _
        exact Subst.toFree_root _ _ _ _ _) hq)]
    rfl
  · refine (holeAt_kThetaC _ hS co ho _ (Term.eta (VarSymb.root (.bnd 0)).inner C
      (Ctx.ref_inner (Ctx.ref_insert_root _ _ _))) θΨ).trans ?_
    refine congrArg WFF.neg (WFF.retS_congr hS _ ?_ ?_)
    · exact (mono_compsSlot (Ctx.ref_insert_root Γ.boxIn (.free u) (.VTypeBox A))
        (Ctx.Le.refl _) _ co ho).symm.trans
        (sig_mono _ (compsVal_eta (Ctx.ref_insert_root Γ.boxIn (.free u) (.VTypeBox A)) co ho).symm)
    · refine WFF.holeAt_congr _ (sig_pair ?_ rfl) θΨ
      exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)

/-- ⭐**The K-law at an object with companions**:
    `◇^{co}[d ↦ t] Φ, ¬◇^{co}[d ↦ t] Ψ ⊢ ◇^{co}[d ↦ t](Φ ∧ ¬Ψ)`, as `Proof.ret_K`: the first unit
    has the companions on its outer object, the second on its inner one. -/
def Proof.ret_KC {Γ : Ctx} [Γ.Presented] {Δ : List (WFF σ Γ 0)} (hS : ModalSys.BStrong = true)
    {A C : VarType} (co : List (List Step)) (ho : A.CompOk co) {a : Ann (A.compsFlat co)}
    (t : Term σ Γ (A.compsFlat co) a)
    (Φ : WFF σ (Γ.boxIn.insert (.bnd 0) (.VTypeBox A)) 1) {c : Ann C} (sb : Term σ Γ.boxIn C c)
    (θΨ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd C (.VTypeBox A))) 1)
    (p : Proof σ Γ Δ (WFF.retS hS (.nec (.boxC A co ho)) t Φ))
    (q : Proof σ Γ Δ (WFF.neg (WFF.retS hS (.nec (.boxC A co ho)) t (kPsi sb θΨ)))) :
    Proof σ Γ Δ (WFF.retS hS (.nec (.boxC A co ho)) t (WFF.and Φ (WFF.neg (kPsi sb θΨ)))) := by
  have P1 := Proof.ret_unitC hS .nec co ho t Φ sb [] (Or.inl rfl) (kThetaC hS co ho θΨ) p
    (Proof.conv (holeRead_kThetaC hS co ho t sb θΨ).symm q)
  refine Proof.ret_monoS hS .nec (S := .nec (.boxC A co ho)) t _ _ P1
    (Proof.ofSubset (fun _ h => absurd h List.not_mem_nil) (Proof.K_box (Δ := []) ?_))
  have hu : Γ.boxIn.RootFresh (.free (Ctx.Presented.bound Γ)) :=
    (Ctx.Presented.fresh_bound _ le_rfl).boxIn
  have hu' : (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ)) (.VTypeBox A)).RootFresh
      (.free (Ctx.Presented.bound Γ + 1)) :=
    ((Ctx.Presented.fresh_bound _ (Nat.le_succ _)).boxIn).insert_ne
      (fun h => absurd (Root.free.inj h) (by omega)) _
  have core : Proof σ (Γ.boxIn.insert (.free (Ctx.Presented.bound Γ)) (.VTypeBox A))
      [WFF.openFree _ hu Ctx.NoSlots.slots (kPsi sb θΨ),
        WFF.openFree _ hu Ctx.NoSlots.slots
          (WFF.and Φ (WFF.unitBodyC hS co ho sb [] (Or.inl rfl) (kThetaC hS co ho θΨ)))]
      .bot :=
    Proof.ret_absurd hS _ _ hu' (Proof.ret_unitC hS .nec [] (Or.inl rfl) _ _ _ co ho θΨ
      (Proof.conv (openFree_unitBodyC_kThetaC hu hS co ho sb θΨ)
        (Proof.and_elim_r (φ := WFF.openFree _ hu Ctx.NoSlots.slots Φ)
          (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
      (Proof.conv (openFree_kPsi hu sb θΨ) (Proof.lookup List.mem_cons_self)))
  have := Proof.all_intro (Δ := []) (Ctx.Presented.bound Γ) (.VTypeBox A) hu
    (φ := WFF.openFree _ hu Ctx.NoSlots.slots
      (WFF.imp (WFF.and Φ (WFF.unitBodyC hS co ho sb [] (Or.inl rfl) (kThetaC hS co ho θΨ)))
        (WFF.and Φ (WFF.neg (kPsi sb θΨ)))))
    (Proof.imp_intro (Proof.and_intro (Proof.and_elim_l (Proof.lookup List.mem_cons_self))
      (Proof.imp_intro core)))
  rwa [WFF.bindFree_openFree] at this

end BArrow

end V12M
