import QML.QML_v12m_BStepC

/-!
# V12M strong B under T: the step along the way home along `x`, with companions

The child's root `A` is committed to the parent along `x` (`RetInvXB` for one more root).  The
chain is the plain step's (`chainB_consistent`) at the leg `.pos x`; only the source's
`∃`-introduction is new, read along the witness arrow (`liftBodyX_ex_flat_mem`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## The source's `∃`-introduction along `x` -/

/-- A witness body read at the child with its bound object any necessary term `Xo`. -/
noncomputable def liftBodyXAt {lv clt : List VarType} {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) {Z : VarType} {xo : Ann Z}
    (Xo : Term σ (ctxOf lv) Z xo)
    (Φ : WFF σ (((ctxOf clt).diaIn x).insert (.bnd 0) Z) 1) : WFF σ (ctxOf lv) 0 :=
  WFF.subst (Subst.setIdx (arrowXIdx imgt x cx) (.bnd 0) (.tm Xo))
    ((arrowXS σ (ctxOf lv) imgt x cx).set (.bnd 0) (.tm Xo))
    (Subst.ok_set (ok_arrowXS himgt hx hcx) rfl)
    (Subst.coh_set (ok_arrowXS himgt hx hcx) (coh_arrowXS himgt hx hcx)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).insert _) Ctx.NoSlots.slots Φ

theorem liftBodyX_eq_liftBodyXAt {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (Φ : WFF σ (bodyCtxX cls clt x) 1) :
    liftBodyX hs himgt hx hcx Φ = liftBodyXAt himgt hx hcx
      (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) cls).2)) Φ :=
  rfl

/-- A witness body read at a re-read slot. -/
theorem liftBodyXAt_bodyRepl {lv clt : List VarType} {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) {Z Z' : VarType} {xo : Ann Z}
    (Xo : Term σ (ctxOf lv) Z xo) {o : Ann Z'}
    (O : Term σ (Ctx.empty.insert (.bnd 0) Z) Z' o)
    (Φ : WFF σ (((ctxOf clt).diaIn x).insert (.bnd 0) Z') 1) :
    liftBodyXAt himgt hx hcx Xo
        (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) O) Φ) =
      liftBodyXAt himgt hx hcx (Term.holeAt Xo O) Φ :=
  subst_set_bodyRepl _ (ok_arrowXS himgt hx hcx) (coh_arrowXS himgt hx hcx) _ Xo O Φ

/-- `liftBodyXAt` depends on its object only as a dependent pair. -/
theorem liftBodyXAt_congr {lv clt : List VarType} {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) {Z : VarType} {xo xo' : Ann Z}
    {Xo : Term σ (ctxOf lv) Z xo} {Xo' : Term σ (ctxOf lv) Z xo'}
    (h : (⟨xo, Xo⟩ : Σ c, Term σ (ctxOf lv) Z c) = ⟨xo', Xo'⟩)
    (Φ : WFF σ (((ctxOf clt).diaIn x).insert (.bnd 0) Z) 1) :
    liftBodyXAt himgt hx hcx Xo Φ = liftBodyXAt himgt hx hcx Xo' Φ := by
  cases h
  rfl

/-- A non-slot variable of a witness body's context, for any slot type, is an item or `x`'s
    content. -/
theorem bodyXT_item {clt : List VarType} {x v : VarSymb} {T U : VarType}
    (hv : (((ctxOf clt).diaIn x).insert (.bnd 0) T) v = some U) (hvr : v ≠ .root (.bnd 0)) :
    (∃ u, v = .step u .box ∧ (ctxOf clt).ref u = some (.VTypeBox U)) ∨
      (v = .step x .dia ∧ (ctxOf clt).ref x = some (.VTypeDia U)) := by
  change (if v = VarSymb.root (.bnd 0) then _ else ((ctxOf clt).diaIn x) v) = _ at hv
  rw [if_neg hvr] at hv
  exact diaIn_item hv

section FlatRootX

variable {lv cls clt : List VarType} {B : VarType} {x : VarSymb} {X : VarType} {cx : ℕ}

/-- The middle substitution along `x` for a new slot of type `□B`. -/
abbrev midSXB (hs : cls <:+ lv) (B : VarType) (imgt : ℕ → ℕ) (x : VarSymb) (cx : ℕ) :
    Subst σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox B)) :=
  ((arrowXS σ (ctxOf lv) imgt x cx).mono
    (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)).set (.bnd 0)
    (.tm (midTermB hs B).2)

theorem ok_midSXB (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) :
    Subst.Ok (((ctxOf clt).diaIn x).insert (.bnd 0) (.VTypeBox (.VTypeProd (bcT cls) B)))
      (midSXB (σ := σ) hs B imgt x cx) :=
  Subst.ok_set (Subst.ok_mono (ok_arrowXS himgt hx hcx) _) rfl

theorem coh_midSXB (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) :
    Subst.Coh (Subst.setIdx (arrowXIdx imgt x cx) (.bnd 0) (.tm (midTermB (σ := σ) hs B).2))
      (((ctxOf clt).diaIn x).insert (.bnd 0) (.VTypeBox (.VTypeProd (bcT cls) B)))
      (midSXB (σ := σ) hs B imgt x cx) :=
  Subst.coh_set (Subst.ok_mono (ok_arrowXS himgt hx hcx) _)
    (Subst.coh_mono (coh_arrowXS himgt hx hcx) _)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).diaIn x)).rootFresh (le_refl 0)) rfl

/-- ⭐**A new component's witness body is an `∃`-introduction of the older roots' one**, for any
    new component: `liftBody_ex_pairUp_memB` along `x`. -/
theorem liftBodyX_ex_pairUp_memB {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) {w₀ : Ann B}
    (w : Term σ (ctxOf lv).boxIn B w₀)
    (Ψ : WFF σ (((ctxOf clt).diaIn x).insert (.bnd 0) (.VTypeBox (.VTypeProd (bcT cls) B))) 1)
    (h : liftBodyXAt himgt hx hcx (Term.boxtm (Term.pair
      (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) cls).2) w)) Ψ ∈ M) :
    liftBodyX hs himgt hx hcx (WFF.ex (.VTypeBox B) (WFF.pairUp Ψ)) ∈ M := by
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact h, ⟨?_⟩⟩
  refine Proof.ex_intro _ (Term.boxtm w) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  refine Eq.symm ?_
  unfold WFF.instantiate WFF.substRoot WFF.pairUp
  have hfr : (ctxOf lv) (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := ctxOf lv)).root
  rw [WFF.subst_comp _ _ (midSXB hs B imgt x cx) _ _ _ _ (ok_midSXB hs himgt hx hcx)
    (coh_midSXB hs himgt hx hcx) _ _ _ ?simA]
  case simA =>
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = .VTypeBox (.VTypeProd (bcT cls) B) := by
        change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
        rw [if_pos rfl] at hv
        exact (Option.some.inj hv).symm
      dsimp only [Subst.comp]
      rw [show midSXB (σ := σ) hs B imgt x cx (.root (.bnd 0)) = .tm (midTermB hs B).2 from
        Subst.set_root _ _ _, Subst.set_root]
      have h0 : (((arrowXS σ (ctxOf lv) imgt x cx).set (.bnd 0) (liftEntry hs)).under (0 + 1) 0
          (.VTypeBox B) hfr).at (.root (.bnd 0)) =
          .tm (Term.boxtm (Term.mono ((Ctx.le_insert hfr _).boxIn)
            (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))) := by
        rw [Subst.at_under_ne _ _ _ (fun h => by cases h)]
        change SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))) = _
        rw [Subst.set_root]
        rfl
      dsimp only [SubE.comp]
      exact SubE.sim_tm_sigma (sig_boxtm (sig_pair
        (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h0))
        (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) _))
          (Subst.box_at_inner_ren _ (Subst.under_at_slot _ (0 + 1) 0 _ hfr))))).symm
    · dsimp only [Subst.comp]
      rw [show midSXB (σ := σ) hs B imgt x cx v =
        SubE.mono _ (arrowXS σ (ctxOf lv) imgt x cx v) from Subst.set_ne _ _ hvr,
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
    obtain rfl : U = .VTypeBox (.VTypeProd (bcT cls) B) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [show midSXB (σ := σ) hs B imgt x cx (.root (.bnd 0)) = .tm (midTermB hs B).2 from
      Subst.set_root _ _ _]
    dsimp only [SubE.comp]
    have hsg : (Subst.single (σ := σ) (.bnd 0) (.tm (Term.boxtm w))).at (.root (.bnd 0)) =
        .tm (Term.boxtm w) := by
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
    have hsim : Subst.Sim (ctxOf cls).boxIn
        (Subst.single (σ := σ) (Δ := ctxOf lv) (.bnd 0) (.tm (Term.boxtm w))).box
        (Subst.idS σ (ctxOf lv).boxIn) := by
      refine Subst.sim_of fun v U _ hv => ?_
      obtain ⟨u, rfl, hu⟩ := boxIn_item hv
      obtain ⟨r, hr, _, _⟩ := ref_rt hu
      change SubE.Sim U ((Subst.single _ _).at u).unbox (.ren (.step u .box))
      rw [Subst.single_at_ne (by rw [hr]; exact fun h => by cases h)]
      change SubE.Sim U (.ren u.inner) _
      rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
      exact .refl _
    try rw [Subst.set_root]
    refine SubE.sim_tm_sigma (sig_boxtm (sig_pair ?_
      (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ hsg)))).symm
    try rw [Term.mono_mono]
    rw [Term.subst_mono]
    exact (Term.subst_congr _ _ _ (Subst.ok_idS_le (ctxOf_le_of_suffix hs).boxIn) _
      (Subst.coh_idS_le (ctxOf_le_of_suffix hs).boxIn) hsim _).trans
      (Term.subst_idS_mono (ctxOf_le_of_suffix hs).boxIn _ _ _)
  · dsimp only [Subst.comp]
    rw [show midSXB (σ := σ) hs B imgt x cx v =
      SubE.mono _ (arrowXS σ (ctxOf lv) imgt x cx v) from Subst.set_ne _ _ hvr,
      Subst.set_ne _ _ hvr]
    rcases bodyXT_item hv hvr with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
    · obtain ⟨r, hr, _, _⟩ := ref_rt hu
      change SubE.Sim U (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
      rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
      exact .refl _
    · rw [show arrowXS σ (ctxOf lv) imgt x cx (x.step Step.dia) = .ren (.root (.free cx)) from
        if_pos rfl]
      change SubE.Sim U (.ren (.root (.free cx))) ((Subst.single _ _).at (.root (.free cx)))
      rw [Subst.single_at_ne (fun h => by cases h)]
      exact .refl _

end FlatRootX

/-- ⭐**The child's `∃`-introduction for its root, along `x`, under T**: a witness body over the
    roots with `A`, true at the child, gives `∃e. pairUp (flatBody Φ)` over the older roots,
    witnessed by `A`'s flat object. -/
theorem liftBodyX_ex_flat_mem {lv cl clt : List VarType} {A : VarType} {x : VarSymb}
    {X : VarType} {cx : ℕ} {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs' : (A :: cl) <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (Φ : WFF σ (bodyCtxX (A :: cl) clt x) 1)
    (h : liftBodyX hs' himgt hx hcx Φ ∈ M) :
    liftBodyX ((List.suffix_cons A cl).trans hs') himgt hx hcx
      (WFF.ex (.VTypeBox (A.bcB false)) (WFF.pairUp (flatBody A Φ))) ∈ M := by
  have hr := (ctxOf_le_of_suffix hs').ref (ctxOf_ref_new A cl)
  refine liftBodyX_ex_pairUp_memB hM ((List.suffix_cons A cl).trans hs') himgt hx hcx
    (flatB (σ := σ) (.root (.free cl.length)) A hr).2 (flatBody A Φ) ?_
  rw [liftBodyXAt_bodyRepl,
    liftBodyXAt_congr himgt hx hcx (holeAt_tupCG_obj (bcT cl) A _ _ hr _ rfl),
    ← liftBodyXAt_congr himgt hx hcx (tupT_cons_mono hs')]
  exact h

/-! ## The step along `x` -/

section StepXB

variable (hS : ModalSys.BStrong = true) {tk tp : NodeSt σ} {A : VarType} {cls clt : List VarType}
  {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}

/-- The returning possibility along `x` a witness body over the child's roots with `A` becomes
    in the grown parent, with companions. -/
def retAtomXB (himgs : ImgOk cls (ctxOf tp.l) imgs) (ht : clt <:+ tp.l)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtxX (A :: cls) clt x) 1) :
    WFF σ (ctxOf (A.bc :: tp.l)) 0 :=
  (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).ref hx⟩ :
      OutLeg (ctxOf (A.bc :: tp.l))).retS hS (.nec (tupShape ModalSys.T rfl (A :: cls)))
    (tupCompsImg (A :: cls) (extImg imgs cls.length tp.l.length) (imgOk_ext himgs) _
      (VarType.compOk_compsAllB _ rfl _)).2
    (WFF.mono (((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).diaIn x).insert
      (.bnd 0) _) Φ)

/-- ⭐**One witness body's atom along `x` is consistent with the grown parent**: the plain
    step's chain at the leg `.pos x` (`chainB_consistent`). -/
theorem retAtomXB_consistent (hs' : (A :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M)
    (hinv : ∀ Ψ : WFF σ (bodyCtxX cls clt x) 1,
      liftBodyX ((List.suffix_cons A cls).trans hs') himgt hx hcx Ψ ∈ tk.M →
        (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩ : OutLeg (ctxOf tp.l)).retS hS
          (.nec (tupShape ModalSys.T rfl cls))
          (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB _ rfl _)).2
          (WFF.mono (((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _) Ψ) ∈ tp.M)
    (Φ : WFF σ (bodyCtxX (A :: cls) clt x) 1) (hΦ : liftBodyX hs' himgt hx hcx Φ ∈ tk.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] tp.l) '' tp.M ∪
      {retAtomXB hS himgs ht hx Φ}) :=
  chainB_consistent hS A himgs (.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩)
    ((ctxOf_le_of_suffix ht).diaIn x) Φ hp.1
    (Theory.Derives.of_mem (hinv _ (liftBodyX_ex_flat_mem hk hs' himgt hx hcx Φ hΦ)))

/-- What the parent gains when the child's root `A` is committed along `x`, with companions. -/
def retSetXB (hs' : (A :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) : Set (WFF σ (ctxOf (A.bc :: tp.l)) 0) :=
  {φ | ∃ Φ, liftBodyX hs' himgt hx hcx Φ ∈ tk.M ∧ φ = retAtomXB hS himgs ht hx Φ}

/-- Finitely many of the gained atoms reduce to one, at the conjunction of their bodies. -/
theorem ret_listXB (hs' : (A :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M) (S : Set (WFF σ (ctxOf (A.bc :: tp.l)) 0)) :
    ∀ L : List (WFF σ (ctxOf (A.bc :: tp.l)) 0),
      (∀ δ ∈ L, δ ∈ S ∨ δ ∈ retSetXB hS hs' himgt hx hcx himgs ht) →
      ∃ Φ, liftBodyX hs' himgt hx hcx Φ ∈ tk.M ∧
        ∀ δ ∈ L, Theory.Derives (S ∪ {retAtomXB hS himgs ht hx Φ}) δ
  | [], _ => ⟨.top, hk.top_mem, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Φ₀, hΦ₀, hL⟩ := ret_listXB hs' himgt hx hcx himgs ht hk S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := ctxOf_fresh (l := A.bc :: tp.l) le_rfl
      rcases h δ List.mem_cons_self with hS' | ⟨Φ₁, hΦ₁, rfl⟩
      · refine ⟨Φ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS')
        · exact hL d hd
      · have hand : ∀ Φ', Proof σ _ [retAtomXB hS himgs ht hx (Φ₀.and Φ₁)]
              (retAtomXB hS himgs ht hx Φ') →
            Theory.Derives (S ∪ {retAtomXB hS himgs ht hx (Φ₀.and Φ₁)})
              (retAtomXB hS himgs ht hx Φ') :=
          fun Φ' p => ⟨[_], fun y hy => by
            rw [List.mem_singleton.mp hy]; exact Or.inr rfl, ⟨p⟩⟩
        have h₀ := hand Φ₀ (Proof.ret_monoS hS (.pos x _) _ _ _
          (Proof.lookup List.mem_cons_self) (Proof.boxx_all_and_left _ _ _ hu))
        have h₁ := hand Φ₁ (Proof.ret_monoS hS (.pos x _) _ _ _
          (Proof.lookup List.mem_cons_self) (Proof.boxx_all_and_right _ _ _ hu))
        refine ⟨Φ₀.and Φ₁, hk.closed ⟨[_, _], fun y hy => ?_,
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

/-- ⭐**The gained atoms along `x` are consistent with the parent.** -/
theorem retSetXB_consistent (hs' : (A :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M)
    (hinv : ∀ Ψ : WFF σ (bodyCtxX cls clt x) 1,
      liftBodyX ((List.suffix_cons A cls).trans hs') himgt hx hcx Ψ ∈ tk.M →
        (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix ht).ref hx⟩ : OutLeg (ctxOf tp.l)).retS hS
          (.nec (tupShape ModalSys.T rfl cls))
          (tupCompsImg cls imgs himgs _ (VarType.compOk_compsAllB _ rfl _)).2
          (WFF.mono (((ctxOf_le_of_suffix ht).diaIn x).insert (.bnd 0) _) Ψ) ∈ tp.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] tp.l) '' tp.M ∪
      retSetXB hS hs' himgt hx hcx himgs ht) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨Φ, hΦ, hder⟩ := ret_listXB hS hs' himgt hx hcx himgs ht hk _ L hL
  exact retAtomXB_consistent hS hs' himgt hx hcx himgs ht hk hp hinv Φ hΦ
    (Derives.trans (fun y hy => hder y hy) ⟨L, fun y hy => hy, p⟩)

/-- The parent grown by the image of the child's root `A` along `x`, with companions. -/
noncomputable def retStepXB (hs' : (A :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) : NodeSt σ :=
  ⟨A.bc :: tp.l, complete (WFF.mono (ctxOf_le_append [A.bc] tp.l) '' tp.M ∪
    retSetXB hS hs' himgt hx hcx himgs ht)⟩

/-- ⭐**One realisation step along `x`, with companions**: the grown parent is maximal
    consistent, extends the old one, and the invariant along `x` holds for one more root. -/
theorem retStepXB_ok (hs' : (A :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M)
    (hinv : RetInvXB hS ModalSys.T rfl tk tp cls imgs clt imgt x X cx) :
    Theory.IsMCS (retStepXB hS hs' himgt hx hcx himgs ht).M ∧
      Grows tp (retStepXB hS hs' himgt hx hcx himgs ht) ∧
      RetInvXB hS ModalSys.T rfl tk (retStepXB hS hs' himgt hx hcx himgs ht) (A :: cls)
        (extImg imgs cls.length tp.l.length) clt imgt x X cx := by
  obtain ⟨_, _, _, _, _, _, h⟩ := hinv
  have hcons := retSetXB_consistent hS hs' himgt hx hcx himgs ht hk hp h
  obtain ⟨hsub, hmcs⟩ := complete_spec hcons
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩,
    hs', imgOk_ext himgs, ht.trans (List.suffix_cons _ _), himgt, hx, hcx, fun Φ hΦ => ?_⟩
  exact hsub (Or.inr ⟨Φ, hΦ, rfl⟩)

end StepXB

/-! ## The forward arrow under T: cross-arrow preservation along `x` -/

omit [ModalSys.NoFour] in
/-- Weakening the witnessed companion unit's conjunct weakens its terms. -/
theorem WFF.mono_unitBodyWC {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {x : VarSymb} {C A X : VarType} (co : List (List Step))
    (ho : C.CompOk co) {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) {b₀ : Ann X}
    (u : Term σ (Γ.diaIn x) X b₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (C.compsFlat co) (RShape.wit (.box A) X).ty)) 1) :
    WFF.mono ((h.diaIn x).insert (.bnd 0) (.VTypeBox C)) (WFF.unitBodyWC hS co ho sb u cs hcs θ) =
      WFF.unitBodyWC hS co ho (Term.mono h.boxIn sb) (Term.mono (h.diaIn x) u) cs hcs θ := by
  unfold WFF.unitBodyWC
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
  · rw [mono_compsVal h sb cs hcs]
    change (⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩ : Σ c, _) =
      ⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩
    rw [Term.mono_mono, Term.mono_mono]
  · change (⟨_, Term.mono _ (Term.mono _ u)⟩ : Σ c, _) = ⟨_, Term.mono _ (Term.mono _ u)⟩
    rw [Term.mono_mono, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _ ((((Ctx.NoSlots.slots (Γ := Γ'.diaIn x)).insert _).boxIn).insert _)]
    exact WFF.holeAt_congr _ (sig_pair ((mono_compsSlot _ _ _ co ho).trans
      (compsSlot_home _ _ _ _ co ho)) (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))) θ

/-- ⭐The witnessed companion unit's conjunct at the forward arrow's items and the witness, with
    a body packed by `packC2`, read at the child: the forward arrow's returning possibility at
    the witnessed tuple shape with companions, valued at the images and `cx`. -/
theorem liftBodyX_unitBodyWC {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf clt).ref x = some (.VTypeDia X)) {cx : ℕ}
    (hcx : (ctxOf lv).ref (.root (.free cx)) = some X) (hS : ModalSys.BStrong = true)
    (co : List (List Step)) (hco : (bcT cls).CompOk co) (cs : List (List Step))
    (hcs : (bcT clt).CompOk cs) (Φ : WFF σ (bodyCtxW clt cls X) 1) :
    liftBodyX hs himgt hx hcx (WFF.unitBodyWC (Γ := ctxOf clt) hS co hco (tupT clt).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx)) cs hcs
        (packC2 cls co (RShape.wit (.box (bcT clt)) X).ty Φ)) =
      WFF.retS hS (.wit (.boxC (bcT clt) cs hcs) X)
        (Term.pair (tupCompsImg clt imgt himgt cs hcs).2 (Term.eta (.root (.free cx)) X hcx))
        (WFF.mono ((ctxOf_le_of_suffix hs).boxIn.insert (.bnd 0) _) Φ) := by
  unfold liftBodyX WFF.unitBodyWC
  refine WFF.retS_congr hS _ (sig_pair ?_ ?_) ?_
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
    refine (WFF.holeAt_packC2 _ _ _ (P' := Term.mono (((ctxOf_le_of_suffix hs).boxIn).trans
      (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).boxIn)).root _)) (tupT cls).2)
      ((getP_subst _ _ _ _ _ (compsSlot_read_fst _ _ _ _)).trans (some_of_sig ?_)) Φ).trans ?_
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).boxIn)).root _)
          (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2)) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.box_at_inner_boxtm _ (by
            change Subst.set _ _ _ (.root (.bnd 0)) = _
            exact Subst.set_root _ _ _)]
        rfl
      · rw [Term.mono_mono]
    · refine (WFF.holeAt_congr _ (sig_pair rfl ?_) _).trans
        (holeAt_tupT_pack2 (ctxOf_le_of_suffix hs).boxIn Φ)
      exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ _ _ _ _)

/-- ⭐**Cross-arrow preservation along `x`, under T**: committing the child's root `A` to the
    parent keeps the forward arrow's invariant with companions, over the extended list.  Were the
    forward returning possibility for `Φ` to fail at the child, its negation would be a body along
    `x` (`liftBodyX_unitBodyWC`), so the grown parent would have `◇_x[d ↦ y] ¬U`; `Φ`, read there,
    is `θ(y, □sb, x)` (`holeRead_packC2`), and `ret_unitWC` gives `◇_x[d ↦ y](¬U ∧ U)`, which is
    absurd (`Proof.retxS_absurd`). -/
theorem retStepXB_rev (hS : ModalSys.BStrong = true) {tk tp : NodeSt σ} {A : VarType}
    {cls clt : List VarType} {imgs imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hs' : (A :: cls) <:+ tk.l) (himgt : ImgOk clt (ctxOf tk.l) imgt)
    (hx : (ctxOf clt).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tk.l).ref (.root (.free cx)) = some X) (himgs : ImgOk cls (ctxOf tp.l) imgs)
    (ht : clt <:+ tp.l) (hk : Theory.IsMCS tk.M) (hp : Theory.IsMCS tp.M)
    (hinv : RetInvXB hS ModalSys.T rfl tk tp cls imgs clt imgt x X cx) :
    RetInvWB hS ModalSys.T rfl (retStepXB hS hs' himgt hx hcx himgs ht) tk clt imgt (A :: cls)
      (extImg imgs cls.length tp.l.length) x X cx := by
  obtain ⟨_, _, _, _, _, _, h⟩ := hinv
  obtain ⟨hsub, hmcs⟩ := complete_spec (retSetXB_consistent hS hs' himgt hx hcx himgs ht hk hp h)
  have ht' : clt <:+ A.bc :: tp.l := ht.trans (List.suffix_cons _ _)
  have hle := ctxOf_le_of_suffix ht'
  have hx'' : ∃ X', (ctxOf (A.bc :: tp.l)).ref x = some (.VTypeDia X') := ⟨X, hle.ref hx⟩
  refine ⟨ht', himgt, hs', imgOk_ext himgs, hx, hcx, fun Φ hΦ => ?_⟩
  by_contra hn
  have hneg := hk.neg_mem_iff.mpr hn
  have hΨ : liftBodyX hs' himgt hx hcx (WFF.neg (WFF.unitBodyWC (Γ := ctxOf clt) hS
      ((bcT (A :: cls)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
      (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx))
      ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
      (packC2 (A :: cls) ((bcT (A :: cls)).compsAllB ModalSys.T)
        (RShape.wit (.box (bcT clt)) X).ty Φ))) ∈ tk.M := by
    change WFF.neg (liftBodyX hs' himgt hx hcx _) ∈ tk.M
    rw [liftBodyX_unitBodyWC]
    exact hneg
  have hret := hsub (Or.inr ⟨_, hΨ, rfl⟩)
  have p₁ : Proof σ (ctxOf (A.bc :: tp.l))
      [retAtomXB hS himgs ht hx (WFF.neg (WFF.unitBodyWC (Γ := ctxOf clt) hS
        ((bcT (A :: cls)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx))
        ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
        (packC2 (A :: cls) ((bcT (A :: cls)).compsAllB ModalSys.T)
          (RShape.wit (.box (bcT clt)) X).ty Φ)))]
      (WFF.retxS hS x hx'' (.nec (tupShape ModalSys.T rfl (A :: cls)))
        (tupCompsImg (A :: cls) (extImg imgs cls.length tp.l.length) (imgOk_ext himgs) _
          (VarType.compOk_compsAllB _ rfl _)).2
        (WFF.neg (WFF.unitBodyWC hS ((bcT (A :: cls)).compsAllB ModalSys.T)
          (VarType.compOk_compsAllB _ rfl _) (Term.mono hle.boxIn (tupT clt).2)
          (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx)))
          ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
          (packC2 (A :: cls) ((bcT (A :: cls)).compsAllB ModalSys.T)
            (RShape.wit (.box (bcT clt)) X).ty Φ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    unfold retAtomXB
    refine congrArg (WFF.retxS hS x _ _ _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyWC hle, Term.mono_eta]
  have p₂ : Proof σ (ctxOf (A.bc :: tp.l)) [liftBodyW ht' (imgOk_ext himgs) hx Φ]
      (WFF.holeRead (Term.pair (tupCompsImg (A :: cls) (extImg imgs cls.length tp.l.length)
          (imgOk_ext himgs) _ (VarType.compOk_compsAllB _ rfl _)).2
        (Term.pair (Term.boxtm (Term.mono hle.boxIn (tupT clt).2))
          (Term.diatm x hx'' (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of (hle.ref hx))))))
        (packC2 (A :: cls) ((bcT (A :: cls)).compsAllB ModalSys.T)
          (RShape.wit (.box (bcT clt)) X).ty Φ)) :=
    Proof.conv ((holeRead_packC2 (imgOk_ext himgs) _ _ _ Φ).trans
      (holeRead_tupImgT_pack2 (imgOk_ext himgs) _ Φ)).symm (Proof.lookup List.mem_cons_self)
  have p₃ : Proof σ (ctxOf (A.bc :: tp.l))
      [retAtomXB hS himgs ht hx (WFF.neg (WFF.unitBodyWC (Γ := ctxOf clt) hS
        ((bcT (A :: cls)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
        (Term.eta (x.step .dia) X (Ctx.ref_diaIn_of hx))
        ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
        (packC2 (A :: cls) ((bcT (A :: cls)).compsAllB ModalSys.T)
          (RShape.wit (.box (bcT clt)) X).ty Φ))),
        liftBodyW ht' (imgOk_ext himgs) hx Φ] .bot :=
    Proof.retxS_absurd hS hx'' _ _ _ (ctxOf_fresh (l := A.bc :: tp.l) le_rfl)
      (Proof.ret_unitWC hS hx'' _ _ _ _ (Term.mono hle.boxIn (tupT clt).2) _ _ _ _
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
