import QML.QML_v12m_BStepWC

/-!
# V12M strong B under T: the step along a doubly witnessed arrow, with companions

The source's root `A` is committed to the target along an arrow whose way back lies in the
target's witness `e`'s extent (`RetInvWDB` for one more root).  The chain is the witnessed one
(`chainBW_consistent`) at the leg `.pos e`; the source's `∃`-introduction is read along `e`
(`liftBodyWD_ex_flat_mem`), and the reverse invariant comes from `ret_unitWDC`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The source's `∃`-introduction along `e` -/

/-- `liftBodyWD` is `liftBodyXAt` along `e` at the pair of the roots' necessary object and the
    source's witness. -/
theorem liftBodyWD_eq_liftBodyXAt {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (Φ : WFF σ (bodyCtxWD cls clt e X) 1) :
    liftBodyWD hs himgt hx he hcxv Φ = liftBodyXAt himgt he hcxv (Term.pair
      (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) cls).2))
      (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx))) Φ :=
  rfl

section FlatRootWD

variable {lv cls clt : List VarType} {A : VarType} {x : VarSymb} {X : VarType} {e : VarSymb}
  {E : VarType} {cxv : ℕ}

/-- The middle substitution along `e` at the witnessed shape. -/
abbrev midSWDB (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (A : VarType)
    (imgt : ℕ → ℕ) (e : VarSymb) (cxv : ℕ) :
    Subst σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox (A.bcB false))) :=
  ((arrowXS σ (ctxOf lv) imgt e cxv).mono
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)).set (.bnd 0)
    (.tm (midTermWB hs hx A).2)

theorem ok_midSWDB (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) :
    Subst.Ok (((ctxOf clt).diaIn e).insert (.bnd 0)
      (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
        (pairComps ((bcT cls).compsAllB ModalSys.T) [])
        (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty)
      (midSWDB (σ := σ) hs hx A imgt e cxv) :=
  Subst.ok_set (Subst.ok_mono (ok_arrowXS himgt he hcxv) _) rfl

theorem coh_midSWDB (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) :
    Subst.Coh (Subst.setIdx (arrowXIdx imgt e cxv) (.bnd 0) (.tm (midTermWB (σ := σ) hs hx A).2))
      (((ctxOf clt).diaIn e).insert (.bnd 0)
        (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
          (pairComps ((bcT cls).compsAllB ModalSys.T) [])
          (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty)
      (midSWDB (σ := σ) hs hx A imgt e cxv) :=
  Subst.coh_set (Subst.ok_mono (ok_arrowXS himgt he hcxv) _)
    (Subst.coh_mono (coh_arrowXS himgt he hcxv) _)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn e)).rootFresh (le_refl 0)) rfl

/-- ⭐**A new component's doubly witnessed body is an `∃`-introduction of the older roots' one**,
    for any new component `□w`: `liftBodyW_ex_pairUpS_memB` along `e`. -/
theorem liftBodyWD_ex_pairUpS_memB {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) {w₀ : Ann (A.bcB false)}
    (w : Term σ (ctxOf lv).boxIn (A.bcB false) w₀)
    (Ψ : WFF σ (((ctxOf clt).diaIn e).insert (.bnd 0)
      (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
        (pairComps ((bcT cls).compsAllB ModalSys.T) [])
        (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty) 1)
    (h : liftBodyXAt himgt he hcxv (Term.pair (Term.boxtm (Term.pair
      (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) cls).2) w))
      (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx))) Ψ ∈ M) :
    liftBodyWD hs himgt hx he hcxv (WFF.ex (.VTypeBox (A.bcB false))
      (WFF.pairUpS (.wit (tupShape ModalSys.T rfl cls) X) (A.bcB false)
        (packCCW (σ := σ) cls A X).2 Ψ)) ∈ M := by
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact h, ⟨?_⟩⟩
  refine Proof.ex_intro _ (Term.boxtm w) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  refine Eq.symm ?_
  unfold WFF.instantiate WFF.substRoot WFF.pairUpS
  have hfr : (ctxOf lv) (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := ctxOf lv)).root
  rw [WFF.subst_comp _ _ (midSWDB hs hx A imgt e cxv) _ _ _ _ (ok_midSWDB hs hx himgt he hcxv)
    (coh_midSWDB hs hx himgt he hcxv) _ _ _ ?simA]
  case simA =>
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
          (pairComps ((bcT cls).compsAllB ModalSys.T) [])
          (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty := by
        change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
        rw [if_pos rfl] at hv
        exact (Option.some.inj hv).symm
      dsimp only [Subst.comp]
      rw [show midSWDB (σ := σ) hs hx A imgt e cxv (.root (.bnd 0)) =
        .tm (midTermWB hs hx A).2 from Subst.set_root _ _ _, Subst.set_root]
      dsimp only [SubE.comp]
      have h0 : (((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)).under
          (0 + 1) 0 (.VTypeBox (A.bcB false)) hfr).at (.root (.bnd 0)) =
          .tm (Term.mono (Ctx.le_insert hfr _)
            (Term.pair (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
              (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx)))) := by
        rw [Subst.at_under_ne _ _ _ (fun h => by cases h)]
        change SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))) = _
        rw [Subst.set_root]
        rfl
      refine SubE.sim_tm_sigma (Eq.symm ((Term.subst_holeAt_sig _ _ _ _ _).trans ?_))
      refine Term.holeAt_congr_sig (sig_pair (sig_pair
        (Term.subst_eta_tm _ _ _ _ _ _ _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl))
        (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_insert_root _ (.bnd 0) _)
          (Subst.under_at_slot _ (0 + 1) 0 _ hfr)))
        (Term.subst_eta_tm _ _ _ _ _ _ _ (by rw [Subst.at_proj _ _ rfl, h0]; rfl))) _
    · dsimp only [Subst.comp]
      rw [show midSWDB (σ := σ) hs hx A imgt e cxv v =
        SubE.mono _ (arrowXS σ (ctxOf lv) imgt e cxv v) from Subst.set_ne _ _ hvr,
        Subst.set_ne _ _ hvr]
      dsimp only [Subst.idS, SubE.comp]
      rw [Subst.at_nonproj _ hlp]
      dsimp only [Subst.under]
      have hv1 : v ≠ .root (.bnd (0 + 1)) := by
        rcases bodyXT_item hv hvr with ⟨u, rfl, _⟩ | ⟨rfl, _⟩ <;> exact fun h => by cases h
      rw [if_neg hv1, Subst.set_ne _ _ hvr]
      exact .refl _
  unfold liftBodyXAt
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ψ
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
        (pairComps ((bcT cls).compsAllB ModalSys.T) [])
        (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [show midSWDB (σ := σ) hs hx A imgt e cxv (.root (.bnd 0)) = .tm (midTermWB hs hx A).2
      from Subst.set_root _ _ _, Subst.set_root]
    dsimp only [SubE.comp]
    have hsg : (Subst.single (σ := σ) (.bnd 0) (.tm (Term.boxtm w))).at (.root (.bnd 0)) =
        .tm (Term.boxtm w) := by
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
    refine SubE.sim_tm_sigma (Eq.symm ((Term.subst_holeAt_sig _ _ _ _ _).trans ?_))
    refine (Term.holeAt_congr_sig (sig_pair (sig_pair (Term.subst_single_mono_sig _ _)
      (Term.subst_eta_tm _ _ _ _ _ _ _ hsg)) (Term.subst_single_mono_sig _ _)) _).trans ?_
    exact (liftObj_wit_pair (ShapeMap.packCC (σ := σ) (bcT cls) (A.bcB false) _ []
      (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl)) _ _).trans
      (sig_pair (holeAt_packCC_obj (csX := (bcT cls).compsAllB ModalSys.T) (csY := [])
        (hX := VarType.compOk_compsAllB _ rfl _) (hY := Or.inl rfl) _ _) rfl)
  · dsimp only [Subst.comp]
    rw [show midSWDB (σ := σ) hs hx A imgt e cxv v =
      SubE.mono _ (arrowXS σ (ctxOf lv) imgt e cxv v) from Subst.set_ne _ _ hvr,
      Subst.set_ne _ _ hvr]
    rcases bodyXT_item hv hvr with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
    · obtain ⟨r, hr, _, _⟩ := ref_rt hu
      change SubE.Sim U (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
      rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
      exact .refl _
    · rw [show arrowXS σ (ctxOf lv) imgt e cxv (e.step Step.dia) = .ren (.root (.free cxv)) from
        if_pos rfl]
      change SubE.Sim U (.ren (.root (.free cxv))) ((Subst.single _ _).at (.root (.free cxv)))
      rw [Subst.single_at_ne (fun h => by cases h)]
      exact .refl _

end FlatRootWD

/-- ⭐**The source's `∃`-introduction for its root along a doubly witnessed arrow, under T.** -/
theorem liftBodyWD_ex_flat_mem {lv cl clt : List VarType} {A : VarType} {x : VarSymb}
    {X : VarType} {e : VarSymb} {E : VarType} {cxv : ℕ} {M : Set (WFF σ (ctxOf lv) 0)}
    (hM : Theory.IsMCS M) (hs' : (A :: cl) <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E)
    (Φ : WFF σ (bodyCtxWD (A :: cl) clt e X) 1)
    (h : liftBodyWD hs' himgt (ref_old_of_ref hx) he hcxv Φ ∈ M) :
    liftBodyWD ((List.suffix_cons A cl).trans hs') himgt hx he hcxv
      (WFF.ex (.VTypeBox (A.bcB false))
        (WFF.pairUpS (.wit (tupShape ModalSys.T rfl cl) X) (A.bcB false)
          (packCCW (σ := σ) cl A X).2 (flatBodyW A X Φ))) ∈ M := by
  have hr := (ctxOf_le_of_suffix hs').ref (ctxOf_ref_new A cl)
  refine liftBodyWD_ex_pairUpS_memB hM ((List.suffix_cons A cl).trans hs') himgt hx he hcxv
    (flatB (σ := σ) (.root (.free cl.length)) A hr).2 (flatBodyW A X Φ) ?_
  rw [liftBodyXAt_bodyRepl]
  refine ((liftBodyXAt_congr himgt he hcxv ?_ Φ).trans
    (liftBodyWD_eq_liftBodyXAt hs' himgt _ he hcxv Φ).symm) ▸ h
  exact (liftObj_wit_pair (tupCG (σ := σ) (bcT cl) A ModalSys.T rfl) _ _).trans
    (sig_pair ((holeAt_tupCG_obj (bcT cl) A _ _ hr _ rfl).trans (tupT_cons_mono hs').symm) rfl)

/-! ## The step along a doubly witnessed arrow -/

section StepWDB

variable (hS : ModalSys.BStrong = true) {ts tt : NodeSt σ} {A : VarType} {cl clt : List VarType}
  {img imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ} {e : VarSymb} {E : VarType}
  {cxv : ℕ}

/-- The returning possibility along `e` a doubly witnessed body over the roots with `A` becomes
    in the grown target, with companions. -/
def retAtomWDB (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (Φ : WFF σ (bodyCtxWD (A :: cl) clt e X) 1) : WFF σ (ctxOf (A.bc :: tt.l)) 0 :=
  WFF.retxS hS e ⟨E, (ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).ref he⟩
    (.wit (tupShape ModalSys.T rfl (A :: cl)) X)
    (Term.pair (tupCompsImg (A :: cl) (extImg img cl.length tt.l.length) (imgOk_ext himg) _
        (VarType.compOk_compsAllB _ rfl _)).2
      (Term.eta (.root (.free cxw)) X ((ctxOf_le_append [A.bc] tt.l).ref hcxw)))
    (WFF.mono (((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).diaIn e).insert
      (.bnd 0) _) Φ)

/-- ⭐**One doubly witnessed body's atom is consistent with the grown target**: the witnessed
    chain (`chainBW_consistent`) along `e`. -/
theorem retAtomWDB_consistent (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Ψ : WFF σ (bodyCtxWD cl clt e X) 1,
      liftBodyWD ((List.suffix_cons A cl).trans hs') himgt hx he hcxv Ψ ∈ ts.M →
        WFF.retxS hS e ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ (.wit (tupShape ModalSys.T rfl cl) X)
          (Term.pair (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2
            (Term.eta (.root (.free cxw)) X hcxw))
          (WFF.mono (((ctxOf_le_of_suffix ht).diaIn e).insert (.bnd 0) _) Ψ) ∈ tt.M)
    (Φ : WFF σ (bodyCtxWD (A :: cl) clt e X) 1)
    (hΦ : liftBodyWD hs' himgt (ref_old_of_ref hx) he hcxv Φ ∈ ts.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
      {retAtomWDB hS himg ht hcxw he Φ}) := by
  have hc := chainBW_consistent hS A himg X (Term.eta (.root (.free cxw)) X hcxw)
    (.pos e ⟨E, (ctxOf_le_of_suffix ht).ref he⟩) ((ctxOf_le_of_suffix ht).diaIn e) Φ hw.1
    (Theory.Derives.of_mem (hinv _ (liftBodyWD_ex_flat_mem hv hs' himgt hx he hcxv Φ hΦ)))
  refine consistent_mono hc (Set.union_subset_union subset_rfl fun y hy => ?_)
  rw [Set.mem_singleton_iff.mp hy]
  exact Set.mem_singleton_iff.mpr (WFF.retxS_congr hS e _ _
    (sig_pair rfl (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm)) rfl)

/-- What the target gains when the source's root `A` is committed along a doubly witnessed arrow,
    with companions. -/
def retSetWDB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E) :
    Set (WFF σ (ctxOf (A.bc :: tt.l)) 0) :=
  {φ | ∃ Φ, liftBodyWD hs' himgt (ref_old_of_ref hx) he hcxv Φ ∈ ts.M ∧
    φ = retAtomWDB hS himg ht hcxw he Φ}

/-- Finitely many of the gained atoms reduce to one, at the conjunction of their bodies. -/
theorem ret_listWDB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E) (hv : Theory.IsMCS ts.M)
    (S : Set (WFF σ (ctxOf (A.bc :: tt.l)) 0)) :
    ∀ L : List (WFF σ (ctxOf (A.bc :: tt.l)) 0),
      (∀ δ ∈ L, δ ∈ S ∨ δ ∈ retSetWDB hS hs' himgt himg ht hx hcxw he hcxv) →
      ∃ Φ, liftBodyWD hs' himgt (ref_old_of_ref hx) he hcxv Φ ∈ ts.M ∧
        ∀ δ ∈ L, Theory.Derives (S ∪ {retAtomWDB hS himg ht hcxw he Φ}) δ
  | [], _ => ⟨.top, hv.top_mem, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Φ₀, hΦ₀, hL⟩ := ret_listWDB hs' himgt himg ht hx hcxw he hcxv hv S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := ctxOf_fresh (l := A.bc :: tt.l) le_rfl
      rcases h δ List.mem_cons_self with hS' | ⟨Φ₁, hΦ₁, rfl⟩
      · refine ⟨Φ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS')
        · exact hL d hd
      · have hand : ∀ Φ', Proof σ _ [retAtomWDB hS himg ht hcxw he (Φ₀.and Φ₁)]
              (retAtomWDB hS himg ht hcxw he Φ') →
            Theory.Derives (S ∪ {retAtomWDB hS himg ht hcxw he (Φ₀.and Φ₁)})
              (retAtomWDB hS himg ht hcxw he Φ') :=
          fun Φ' p => ⟨[_], fun y hy => by
            rw [List.mem_singleton.mp hy]; exact Or.inr rfl, ⟨p⟩⟩
        have h₀ := hand Φ₀ (Proof.ret_monoS hS (.pos e _) _ _ _
          (Proof.lookup List.mem_cons_self) (Proof.boxx_all_and_left _ _ _ hu))
        have h₁ := hand Φ₁ (Proof.ret_monoS hS (.pos e _) _ _ _
          (Proof.lookup List.mem_cons_self) (Proof.boxx_all_and_right _ _ _ hu))
        refine ⟨Φ₀.and Φ₁, hv.closed ⟨[_, _], fun y hy => ?_,
          ⟨Proof.and_intro (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hΦ₀
          · rw [List.mem_singleton.mp hy]; exact hΦ₁
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · refine Derives.trans (fun y hy => ?_) (hL d hd)
          rcases hy with hy | hy
          · exact Theory.Derives.of_mem (Or.inl hy)
          · rw [Set.mem_singleton_iff.mp hy]; exact h₀

/-- ⭐**The gained atoms along a doubly witnessed arrow are consistent with the target.** -/
theorem retSetWDB_consistent (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Ψ : WFF σ (bodyCtxWD cl clt e X) 1,
      liftBodyWD ((List.suffix_cons A cl).trans hs') himgt hx he hcxv Ψ ∈ ts.M →
        WFF.retxS hS e ⟨E, (ctxOf_le_of_suffix ht).ref he⟩ (.wit (tupShape ModalSys.T rfl cl) X)
          (Term.pair (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2
            (Term.eta (.root (.free cxw)) X hcxw))
          (WFF.mono (((ctxOf_le_of_suffix ht).diaIn e).insert (.bnd 0) _) Ψ) ∈ tt.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
      retSetWDB hS hs' himgt himg ht hx hcxw he hcxv) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨Φ, hΦ, hder⟩ := ret_listWDB hS hs' himgt himg ht hx hcxw he hcxv hv _ L hL
  exact retAtomWDB_consistent hS hs' himgt himg ht hx hcxw he hcxv hv hw hinv Φ hΦ
    (Derives.trans (fun y hy => hder y hy) ⟨L, fun y hy => hy, p⟩)

/-- The target grown by the image of the source's root `A` along a doubly witnessed arrow, with
    companions. -/
noncomputable def retStepWDB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E) : NodeSt σ :=
  ⟨A.bc :: tt.l, complete (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
    retSetWDB hS hs' himgt himg ht hx hcxw he hcxv)⟩

/-- ⭐**One realisation step along a doubly witnessed arrow, with companions.** -/
theorem retStepWDB_ok (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvWDB hS ModalSys.T rfl ts tt cl img clt imgt x X cxw e E cxv) :
    Theory.IsMCS (retStepWDB hS hs' himgt himg ht hx hcxw he hcxv).M ∧
      Grows tt (retStepWDB hS hs' himgt himg ht hx hcxw he hcxv) ∧
      RetInvWDB hS ModalSys.T rfl ts (retStepWDB hS hs' himgt himg ht hx hcxw he hcxv) (A :: cl)
        (extImg img cl.length tt.l.length) clt imgt x X cxw e E cxv := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hinv
  have hcons := retSetWDB_consistent hS hs' himgt himg ht hx hcxw he hcxv hv hw h
  obtain ⟨hsub, hmcs⟩ := complete_spec hcons
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩,
    hs', imgOk_ext himg, ht.trans (List.suffix_cons _ _), himgt, ref_old_of_ref hx,
    (ctxOf_le_append [A.bc] tt.l).ref hcxw, he, hcxv, fun Φ hΦ => ?_⟩
  exact hsub (Or.inr ⟨Φ, hΦ, rfl⟩)

end StepWDB

/-! ## Cross-arrow preservation along a doubly witnessed arrow -/

omit [ModalSys.NoFour] in
/-- Weakening the doubly witnessed companion unit's conjunct weakens its terms. -/
theorem WFF.mono_unitBodyWDC {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {x : VarSymb} {C Xe A X : VarType} (co : List (List Step))
    (ho : C.CompOk co) {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) Xe) (RShape.wit (.box A) X).ty)) 1) :
    WFF.mono ((h.diaIn x).insert (.bnd 0) (RShape.wit (.box C) Xe).ty)
        (WFF.unitBodyWDC hS co ho sb u cs hcs θ) =
      WFF.unitBodyWDC hS co ho (Term.mono h.boxIn sb) (Term.mono (h.diaIn x) u) cs hcs θ := by
  unfold WFF.unitBodyWDC
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ ?_) ?_
  · rw [mono_compsVal h sb cs hcs]
    change (⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩ : Σ c, _) =
      ⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩
    rw [Term.mono_mono, Term.mono_mono]
  · change (⟨_, Term.mono _ (Term.mono _ u)⟩ : Σ c, _) = ⟨_, Term.mono _ (Term.mono _ u)⟩
    rw [Term.mono_mono, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _
      ((((Ctx.NoSlots.slots (Γ := Γ'.diaIn x)).insert _).diaIn _).insert _)]
    exact WFF.holeAt_congr _ (sig_pair (sig_pair ((mono_compsSlot _ _ _ co ho).trans
      (compsSlot_home _ _ _ _ co ho)) (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)))
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))) θ

/-- ⭐The doubly witnessed companion unit's conjunct at the reverse arrow's items and `e`'s content,
    with a body packed along `x` by `packC2X`, read at the source: the reverse arrow's returning
    possibility along `x` at the witnessed shape with companions. -/
theorem liftBodyWD_unitBodyWDC {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : VarSymb} {E : VarType}
    (he : (ctxOf clt).ref e = some (.VTypeDia E)) {cxv : ℕ}
    (hcxv : (ctxOf lv).ref (.root (.free cxv)) = some E) (hS : ModalSys.BStrong = true)
    (co : List (List Step)) (hco : (bcT cls).CompOk co) (cs : List (List Step))
    (hcs : (bcT clt).CompOk cs) (Φ : WFF σ (bodyCtxWD clt cls x E) 1) :
    liftBodyWD hs himgt hx he hcxv (WFF.unitBodyWDC (Γ := ctxOf clt) hS co hco (tupT clt).2
        (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of he)) cs hcs (packC2X cls co hx _ Φ)) =
      WFF.retxS hS x ⟨X, (ctxOf_le_of_suffix hs).ref hx⟩ (.wit (.boxC (bcT clt) cs hcs) E)
        (Term.pair (tupCompsImg clt imgt himgt cs hcs).2 (Term.eta (.root (.free cxv)) E hcxv))
        (WFF.mono (((ctxOf_le_of_suffix hs).diaIn x).insert (.bnd 0) _) Φ) := by
  have hle := ctxOf_le_of_suffix hs
  have hu := Ctx.ref_insert_root ((ctxOf clt).diaIn e) (.bnd 0)
    (RShape.wit (.box (bcT cls)) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ : Subst.Ok (bodyCtxWD cls clt e X)
      ((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.ok_set (ok_arrowXS himgt he hcxv) rfl
  have hc : Subst.Coh (Subst.setIdx (arrowXIdx imgt e cxv) (.bnd 0) (liftEntryW hs hx))
      (bodyCtxWD cls clt e X) ((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.coh_set (ok_arrowXS himgt he hcxv) (coh_arrowXS himgt he hcxv)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn e)).rootFresh (le_refl 0)) rfl
  have hw : (((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .snd)).idxAlong [] = x := rfl
  have hfst : ((arrowXS σ (ctxOf lv) imgt e cxv).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .fst) =
      .tm (Term.boxtm (Term.mono hle.boxIn (tupT cls).2)) := by
    rw [Subst.at_proj _ _ rfl]
    change (Subst.set _ _ _ (.root (.bnd 0))).proj .fst = _
    rw [Subst.set_root]
    rfl
  unfold liftBodyWD WFF.unitBodyWDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ x rfl ⟨X, hle.ref hx⟩
    ((Ctx.NoSlots.slots (Γ := ctxOf lv)).diaIn x) (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ (sig_pair ?_ ?_) ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf lv) imgt) _ (ok_arrowS himgt) _
      (coh_arrowS himgt) ?_ _).trans (subst_arrow_compsVal clt himgt cs hcs)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [Term.subst_mono]
    refine Term.subst_eta_renAt _ _ _ _ _ _ _ _ ?_
    rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ (fun h => by cases h)]
    exact if_pos rfl
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_packC2X _ hx _ _ _ (P' := Term.mono
      (((Ctx.le_boxIn_diaIn _ x).trans (hle.diaIn x)).trans
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)) (tupT cls).2)
      ((getP_subst _ _ _ _ _ (compsSlot_read_fst _ _ _ _)).trans (some_of_sig ?_)) Φ).trans ?_
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)
          (Term.mono (Ctx.le_boxIn_diaIn _ x) (Term.mono hle.boxIn (tupT cls).2))) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.dia_eq_box_mono (Δ₁ := ((ctxOf clt).diaIn e).insert (.bnd 0) _) _ _ x _ _
            (Ctx.ref_inner (Ctx.ref_fst_of hu)), Subst.box_at_inner_boxtm _ hfst]
        rfl
      · exact congrArg (Sigma.mk _) (by rw [Term.mono_mono, Term.mono_mono])
    · refine (WFF.holeAt_congr _ (sig_pair (sig_pair rfl ?_) ?_) _).trans
        (holeAt_tupT_pack2X (hle.diaIn x) hx Φ)
      · refine (Term.subst_eta_tm _ _ _ _ _ _
          (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)
            (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx)))) ?_).trans ?_
        · rw [Subst.at_under_ne _ _ _ (fun h => by cases h), Subst.at_nonproj _ rfl]
          dsimp only [Subst.dia]
          rw [if_pos rfl, Subst.at_proj _ _ rfl]
          change SubE.mono _ (SubE.diaBody x ((Subst.set _ _ _ (.root (.bnd 0))).proj .snd)) = _
          rw [Subst.set_root]
          change SubE.mono _ (SubE.diaBody x (SubE.tm (Term.diatm x _
            (Term.eta (x.step .dia) X _)))) = _
          rw [SubE.diaBody_diatm]
          rfl
        · exact congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)
      · exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ (0 + 1) 0 _ _)

/-- ⭐**Cross-arrow preservation along a doubly witnessed arrow, under T**: committing the
    source's root `A` keeps the reverse arrow's invariant with companions, over the extended list
    (`ret_unitWDC`, as `retStepWD_rev`). -/
theorem retStepWDB_rev (hS : ModalSys.BStrong = true) {ts tt : NodeSt σ} {A : VarType}
    {cl clt : List VarType} {img imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cxw : ℕ}
    {e : VarSymb} {E : VarType} {cxv : ℕ} (hs' : (A :: cl) <:+ ts.l)
    (himgt : ImgOk clt (ctxOf ts.l) imgt) (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcxw : (ctxOf tt.l).ref (.root (.free cxw)) = some X)
    (he : (ctxOf clt).ref e = some (.VTypeDia E))
    (hcxv : (ctxOf ts.l).ref (.root (.free cxv)) = some E)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvWDB hS ModalSys.T rfl ts tt cl img clt imgt x X cxw e E cxv) :
    RetInvWDB hS ModalSys.T rfl (retStepWDB hS hs' himgt himg ht hx hcxw he hcxv) ts clt imgt
      (A :: cl) (extImg img cl.length tt.l.length) e E cxv x X cxw := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := hinv
  obtain ⟨hsub, hmcs⟩ :=
    complete_spec (retSetWDB_consistent hS hs' himgt himg ht hx hcxw he hcxv hv hw h)
  have ht' : clt <:+ A.bc :: tt.l := ht.trans (List.suffix_cons _ _)
  have hle := ctxOf_le_of_suffix ht'
  have hx' : (ctxOf (A :: cl)).ref x = some (.VTypeDia X) := ref_old_of_ref hx
  have hcxw' := (ctxOf_le_append [A.bc] tt.l).ref hcxw
  have he'' : ∃ Y, (ctxOf (A.bc :: tt.l)).ref e = some (.VTypeDia Y) := ⟨E, hle.ref he⟩
  refine ⟨ht', himgt, hs', imgOk_ext himg, he, hcxv, hx', hcxw', fun Φ hΦ => ?_⟩
  by_contra hn
  have hneg := hv.neg_mem_iff.mpr hn
  have hΨ : liftBodyWD hs' himgt hx' he hcxv (WFF.neg (WFF.unitBodyWDC (Γ := ctxOf clt) hS
      ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
      (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of he))
      ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
      (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ))) ∈ ts.M := by
    change WFF.neg (liftBodyWD hs' himgt hx' he hcxv _) ∈ ts.M
    rw [liftBodyWD_unitBodyWDC]
    exact hneg
  have hret := hsub (Or.inr ⟨_, hΨ, rfl⟩)
  have p₁ : Proof σ (ctxOf (A.bc :: tt.l))
      [retAtomWDB hS himg ht hcxw he (WFF.neg (WFF.unitBodyWDC (Γ := ctxOf clt) hS
        ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
        (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of he))
        ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
        (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ)))]
      (WFF.retxS hS e he'' (.wit (tupShape ModalSys.T rfl (A :: cl)) X)
        (Term.pair (tupCompsImg (A :: cl) (extImg img cl.length tt.l.length) (imgOk_ext himg) _
            (VarType.compOk_compsAllB _ rfl _)).2 (Term.eta (.root (.free cxw)) X hcxw'))
        (WFF.neg (WFF.unitBodyWDC hS ((bcT (A :: cl)).compsAllB ModalSys.T)
          (VarType.compOk_compsAllB _ rfl _) (Term.mono hle.boxIn (tupT clt).2)
          (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of (hle.ref he)))
          ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
          (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    unfold retAtomWDB
    refine congrArg (WFF.retxS hS e _ _ _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyWDC hle, Term.mono_eta]
  have p₂ : Proof σ (ctxOf (A.bc :: tt.l)) [liftBodyWD ht' (imgOk_ext himg) he hx' hcxw' Φ]
      (WFF.holeRead (Term.pair (Term.pair (tupCompsImg (A :: cl)
          (extImg img cl.length tt.l.length) (imgOk_ext himg) _
          (VarType.compOk_compsAllB _ rfl _)).2 (Term.eta (.root (.free cxw)) X hcxw'))
        (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT clt).2))
          (Term.diatm e he'' (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of (hle.ref he))))))
        (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ)) :=
    Proof.conv ((holeRead_packC2X (imgOk_ext himg) _ _ hx' _ _ Φ).trans
      (holeRead_tupImgT_pack2WD ht' (imgOk_ext himg) he hx' hcxw' Φ)).symm
      (Proof.lookup List.mem_cons_self)
  have p₃ : Proof σ (ctxOf (A.bc :: tt.l))
      [retAtomWDB hS himg ht hcxw he (WFF.neg (WFF.unitBodyWDC (Γ := ctxOf clt) hS
        ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
        (Term.eta (e.step .dia) E (Ctx.ref_diaIn_of he))
        ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
        (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ))),
        liftBodyWD ht' (imgOk_ext himg) he hx' hcxw' Φ] .bot :=
    Proof.retxS_absurd hS he'' _ _ _ (ctxOf_fresh (l := A.bc :: tt.l) le_rfl)
      (Proof.ret_unitWDC hS he'' ((bcT (A :: cl)).compsAllB ModalSys.T)
        (VarType.compOk_compsAllB _ rfl _) _ _
        (Term.mono hle.boxIn (tupT clt).2) _ ((bcT clt).compsAllB ModalSys.T)
        (VarType.compOk_compsAllB _ rfl _) _
        (Proof.ofSubset (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_self) p₁)
        (Proof.ofSubset (fun y hy => by
          rw [List.mem_singleton.mp hy]; exact List.mem_cons_of_mem _ List.mem_cons_self) p₂))
  exact hmcs.1 ⟨[_, _], fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hret
    · rw [List.mem_singleton.mp hy]; exact hΦ, ⟨p₃⟩⟩

end BArrow

end V12M
