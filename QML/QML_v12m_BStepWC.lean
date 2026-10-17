import QML.QML_v12m_BStepXC

/-!
# V12M strong B under T: the steps at a witnessed shape, with companions

The parent's root `A` is committed to the child along a witness arrow (`RetInvWB` for one more
root).  The chain is the plain step's at the witnessed shape `.wit (tupShape cl) X`: every value
is the plain chain's paired with the witness's content (`stepW₅_eq`), and the bodies go through
`pairUpS` (`bodySplit_mono_pairUpS`).  It is stated along any leg (`chainBW_consistent`), for
the doubly witnessed step too.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## Values at a witnessed shape -/

omit [ModalSys.NoFour] in
/-- A map at a witnessed shape, on a value: the map on the necessary part, the witness's content
    kept. -/
theorem liftVal_wit_pair {Γ : Ctx} {N T : NShape} {X : VarType} (F : ShapeMap σ N T)
    {a : Ann N.flat} {x : Ann X} (v : Term σ Γ N.flat a) (e : Term σ Γ X x) :
    (⟨_, Term.holeAt (Term.pair v e) (ShapeMap.liftVal (σ := σ) (.wit N X) F).2⟩ :
      Σ c, Term σ Γ ((RShape.wit N X).withNec T).flat c) =
      ⟨_, Term.pair (Term.holeAt v F.val.2) e⟩ := by
  refine sig_pair ?_ (Term.holeAt_pair_snd _ _)
  exact (Term.holeAt_holeAt_sig _ _ _).trans (Term.holeAt_congr_sig (Term.holeAt_pair_fst _ _) _)

omit [ModalSys.NoFour] in
/-- Naming a companion at a witnessed shape, on a value: the companion joins the necessary
    part, the witness's content kept. -/
theorem compTm_wit_pair {Γ : Ctx} [Γ.NoSlots] (A : VarType) (cs : List (List Step))
    (h : A.CompOk cs) (p : List Step) (h' : A.CompOk (p :: cs)) (N : NShape) {X : VarType}
    {a : Ann (A.compsFlat cs)} {x : Ann X} {b : Ann ((A.compAt p).getD .VTypeOne)}
    (t : Term σ Γ (A.compsFlat cs) a) (e : Term σ Γ X x)
    (u : Term σ Γ ((A.compAt p).getD .VTypeOne) b) :
    (⟨_, (RShape.compTm A cs h p h' (.wit N X) (Term.pair t e) u).2⟩ :
      Σ c, Term σ Γ ((RShape.wit N X).withNec (.boxC A (p :: cs) h')).flat c) =
      ⟨_, Term.pair (Term.pair t u) e⟩ := by
  dsimp only [RShape.compTm]
  rw [Term.holeRead_eq_holeAt]
  exact sig_pair (sig_pair (Term.holeAt_pair_fst_fst _ _ _) (Term.holeAt_pair_snd _ _))
    (Term.holeAt_pair_fst_snd _ _ _)

omit [ModalSys.NoFour] in
theorem compTm_congr_sig {Γ : Ctx} [Γ.NoSlots] (A : VarType) (cs : List (List Step))
    (h : A.CompOk cs) (p : List Step) (h' : A.CompOk (p :: cs)) (S : RShape)
    {a a' : Ann (S.withNec (.boxC A cs h)).flat} {t : Term σ Γ (S.withNec (.boxC A cs h)).flat a}
    {t' : Term σ Γ (S.withNec (.boxC A cs h)).flat a'}
    (ht : (⟨a, t⟩ : Σ c, Term σ Γ (S.withNec (.boxC A cs h)).flat c) = ⟨a', t'⟩)
    {b : Ann ((A.compAt p).getD .VTypeOne)} (u : Term σ Γ ((A.compAt p).getD .VTypeOne) b) :
    (⟨_, (RShape.compTm A cs h p h' S t u).2⟩ :
      Σ c, Term σ Γ (S.withNec (.boxC A (p :: cs) h')).flat c) =
      ⟨_, (RShape.compTm A cs h p h' S t' u).2⟩ := by
  cases ht
  rfl

omit [ModalSys.NoFour] in
theorem valQ_congr_sig (S : RShape) (A : VarType) (cs : List (List Step)) (h : A.CompOk cs)
    {l : List VarType} {a a' : Ann (S.withNec (.boxC A cs h)).flat}
    {t : Term σ (ctxOf l) (S.withNec (.boxC A cs h)).flat a}
    {t' : Term σ (ctxOf l) (S.withNec (.boxC A cs h)).flat a'}
    (ht : (⟨a, t⟩ : Σ c, Term σ (ctxOf l) (S.withNec (.boxC A cs h)).flat c) = ⟨a', t'⟩)
    (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)) :
    (⟨_, (valQ (σ := σ) S A cs h t Q hQ).2⟩ :
      Σ c, Term σ (ctxOf (compsTys A Q ++ l)) (S.withNec (.boxC A (Q ++ cs) hQ)).flat c) =
      ⟨_, (valQ S A cs h t' Q hQ).2⟩ := by
  cases ht
  rfl

omit [ModalSys.NoFour] in
/-- Naming companions at a witnessed shape: the plain naming, the witness's content weakened. -/
theorem valQ_wit (N : NShape) (X A : VarType) (cs : List (List Step)) (h : A.CompOk cs)
    {l : List VarType} {a : Ann (A.compsFlat cs)} {x : Ann X}
    (t : Term σ (ctxOf l) (A.compsFlat cs) a) (e : Term σ (ctxOf l) X x) :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)),
      (⟨_, (valQ (σ := σ) (.wit N X) A cs h (Term.pair t e) Q hQ).2⟩ :
        Σ c, Term σ (ctxOf (compsTys A Q ++ l)) (RShape.wit (.boxC A (Q ++ cs) hQ) X).flat c) =
        ⟨_, Term.pair (valQ (.nec N) A cs h t Q hQ).2 (Term.mono (legQ_le A Q) e)⟩
  | [], _ => by
      change (⟨_, Term.pair t e⟩ : Σ c, _) = ⟨_, Term.pair t (Term.mono (Ctx.Le.refl _) e)⟩
      rw [Term.mono_refl]
  | q :: Q, hQ => by
      refine (compTm_congr_sig A (Q ++ cs) hQ.tail q hQ (.wit N X)
        (sig_mono (ctxOf_le_append [((A.compAt q).getD .VTypeOne)] _)
          (valQ_wit N X A cs h t e Q hQ.tail)) _).trans
        ((compTm_wit_pair A (Q ++ cs) hQ.tail q hQ N _ _ _).trans (sig_pair rfl ?_))
      exact congrArg (Sigma.mk _) (Term.mono_mono _ _ _)

omit [ModalSys.NoFour] in
theorem WFF.bodyRepl_congr_sig {V : Ctx} [V.NoSlots] {A B : VarType} {b b' : Ann B}
    {X : Term σ (V.insert (.bnd 0) A) B b} {X' : Term σ (V.insert (.bnd 0) A) B b'}
    (h : (⟨b, X⟩ : Σ c, Term σ (V.insert (.bnd 0) A) B c) = ⟨b', X'⟩)
    (Φ : WFF σ (V.insert (.bnd 0) B) 1) : WFF.bodyRepl X Φ = WFF.bodyRepl X' Φ := by
  cases h
  rfl

omit [ModalSys.NoFour] in
/-- Selecting companions at a witnessed shape leaves a body as it was. -/
theorem WFF.bodyRepl_liftObj_wit_subC {V : Ctx} [V.NoSlots] (A : VarType)
    (cs cs' : List (List Step)) (h : A.CompOk cs) (h' : A.CompOk cs') (hsub : ∀ p ∈ cs', p ∈ cs)
    (X : VarType) (Φ : WFF σ (V.insert (.bnd 0) (RShape.wit (.boxC A cs' h') X).ty) 1) :
    WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
      (ShapeMap.liftObj (σ := σ) (.wit (.boxC A cs h) X)
        (ShapeMap.subC A cs cs' h h' hsub)).2) Φ = Φ := by
  have e : (⟨_, (ShapeMap.liftObj (σ := σ) (.wit (.boxC A cs h) X)
      (ShapeMap.subC A cs cs' h h' hsub)).2⟩ : Σ c, Term σ (Ctx.empty.insert (.bnd 0)
        (RShape.wit (.boxC A cs h) X).ty) (RShape.wit (.boxC A cs' h') X).ty c) =
      ⟨_, Term.eta (.root (.bnd 0)) (RShape.wit (.boxC A cs h) X).ty
        (Ctx.ref_insert_root _ _ _)⟩ := by
    dsimp only [ShapeMap.liftObj, ShapeMap.obj]
    exact sig_pair (Term.holeAt_eta_root _) rfl
  rw [WFF.bodyRepl_congr_sig (sig_mono _ e)]
  exact WFF.bodyRepl_eta Φ

/-! ## Naming companions at a witnessed shape, along a leg -/

omit [ModalSys.NoFour] in
/-- `compsS_consistent_leg` at a witnessed shape. -/
theorem compsS_consistent_legW (hS : ModalSys.BStrong = true) (N : NShape) (X A : VarType)
    (cs : List (List Step)) (h : A.CompOk cs) {l : List VarType} (O : OutLeg (ctxOf l))
    {a : Ann (RShape.wit (.boxC A cs h) X).flat}
    (t : Term σ (ctxOf l) (RShape.wit (.boxC A cs h) X).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (RShape.wit (.boxC A cs h) X).ty) 1)
    {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.Consistent M)
    (hex : Theory.Derives M (O.retS hS (.wit (.boxC A cs h) X) t Φ)) :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)),
      Theory.Consistent (WFF.mono (legQ_le A Q) '' M ∪
        {(O.mono (legQ_le A Q)).retS hS (.wit (.boxC A (Q ++ cs) hQ) X)
          (valQ (.wit N X) A cs h t Q hQ).2
          (WFF.mono ((O.le_view_mono (legQ_le A Q)).insert (.bnd 0) _) Φ)})
  | [], hQ => by
      rw [show WFF.mono (legQ_le A (l := l) []) '' M = M from by
        ext x
        simp only [Set.mem_image]
        exact ⟨fun ⟨y, hy, e⟩ => by rw [← e, WFF.mono_refl]; exact hy,
          fun hx => ⟨x, hx, WFF.mono_refl _ _⟩⟩]
      have e : (O.mono (legQ_le A (l := l) [])).retS hS (.wit (.boxC A ([] ++ cs) hQ) X)
          (valQ (.wit N X) A cs h t [] hQ).2
          (WFF.mono ((O.le_view_mono (legQ_le A (l := l) [])).insert (.bnd 0) _) Φ) =
          O.retS hS (.wit (.boxC A cs h) X) t Φ := by
        cases O <;> exact congrArg _ (WFF.mono_refl _ _)
      rw [e]
      exact consistent_union_derives hM hex
  | q :: Q, hQ => by
      have ih := compsS_consistent_legW hS N X A cs h O t Φ hM hex Q hQ.tail
      have hc := compS_consistent ih hS (O.mono (legQ_le A Q)) (.wit N X) q hQ
        (valQ (.wit N X) A cs h t Q hQ.tail).2
        (WFF.mono ((O.le_view_mono (legQ_le A Q)).insert (.bnd 0) _) Φ)
        (Theory.Derives.of_mem (Or.inr rfl)) (ctxOf_fresh (l := compsTys A Q ++ l) le_rfl)
      refine consistent_mono hc (Set.union_subset_union ?_ ?_)
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨WFF.mono (legQ_le A Q) x, Or.inl ⟨x, hx, rfl⟩, ?_⟩
        rw [WFF.mono_mono]
      · intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        refine Set.mem_singleton_iff.mpr ?_
        cases O with
        | nec =>
            change WFF.retS hS _ _ _ = WFF.retS hS _ _ (WFF.mono _ (WFF.bodyRepl
              (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _))
              (WFF.mono _ Φ)))
            rw [WFF.bodyRepl_eta', WFF.mono_mono]
            rfl
        | pos y hy =>
            change WFF.retxS hS _ _ _ _ _ = WFF.retxS hS _ _ _ _ (WFF.mono _ (WFF.bodyRepl
              (Term.eta (.root (.bnd 0)) _ (Ctx.ref_insert_root _ (.bnd 0) _))
              (WFF.mono _ Φ)))
            rw [WFF.bodyRepl_eta', WFF.mono_mono]
            rfl

/-! ## The chain's values at a witnessed shape -/

section ChainValsW

variable {lt cl : List VarType} {img : ℕ → ℕ} (A : VarType) (himg : ImgOk cl (ctxOf lt) img)
  {X : VarType} {xc : Ann X} (c : Term σ (ctxOf lt) X xc)

/-- The value after `ret_extS` at the witnessed shape. -/
def stepW₁ : Σ a, Term σ (ctxOf (A.bcB false :: lt))
    ((RShape.wit (tupShape ModalSys.T rfl cl) X).ext (A.bcB false)).flat a :=
  (RShape.wit (tupShape ModalSys.T rfl cl) X).extTm
    (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false)
      (Term.pair (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2 c))
    (Term.eta (.root (.free lt.length)) (A.bcB false) (ctxOf_ref_new _ _))

theorem stepW₁_eq : (⟨_, (stepW₁ A himg c).2⟩ : Σ a, Term σ (ctxOf (A.bcB false :: lt))
    ((RShape.wit (tupShape ModalSys.T rfl cl) X).ext (A.bcB false)).flat a) =
    ⟨_, Term.pair (stepV₁ (σ := σ) A himg).2
      (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false) c)⟩ :=
  RShape.extTm_wit (σ := σ) (N := tupShape ModalSys.T rfl cl)
    (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false)
      (tupCompsImg (σ := σ) cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2)
    (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false) c)
    (Term.eta (.root (.free lt.length)) (A.bcB false) (ctxOf_ref_new _ _))

/-- The value after packing at the witnessed shape. -/
def stepW₂ : Σ a, Term σ (ctxOf (A.bcB false :: lt))
    (RShape.wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
      (pairComps ((bcT cl).compsAllB ModalSys.T) [])
      (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).flat a :=
  ⟨_, Term.holeRead (stepW₁ A himg c).2
    (ShapeMap.liftVal (σ := σ) ((RShape.wit (tupShape ModalSys.T rfl cl) X).ext (A.bcB false))
      (ShapeMap.packCC (σ := σ) (bcT cl) (A.bcB false) _ []
        (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))).2⟩

theorem stepW₂_eq : (⟨_, (stepW₂ A himg c).2⟩ : Σ a, Term σ (ctxOf (A.bcB false :: lt))
    (RShape.wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
      (pairComps ((bcT cl).compsAllB ModalSys.T) [])
      (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).flat a) =
    ⟨_, Term.pair (stepV₂ (σ := σ) A himg).2
    (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false) c)⟩ := by
  unfold stepW₂ stepV₂
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  exact (Term.holeAt_congr_sig (stepW₁_eq A himg c) _).trans (liftVal_wit_pair _ _ _)

/-- The value after naming the flat contents' companions at the witnessed shape. -/
def stepW₃ :=
  valQ (.wit (tupShape ModalSys.T rfl cl) X) (VarType.VTypeProd (bcT cl) (A.bcB false))
    (pairComps ((bcT cl).compsAllB ModalSys.T) [])
    (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))
    (stepW₂ (σ := σ) A himg c).2 (stepQ A) (stepQ_ok cl A)

theorem stepW₃_eq : (⟨_, (stepW₃ A himg c).2⟩ : Σ a, Term σ (ctxOf (compsTys
    (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A) ++ A.bcB false :: lt))
    (RShape.wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
      (stepQ A ++ pairComps ((bcT cl).compsAllB ModalSys.T) []) (stepQ_ok cl A)) X).flat a) =
    ⟨_, Term.pair (stepV₃ (σ := σ) A himg).2
    (Term.mono (legQ_le _ (stepQ A))
      (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false) c))⟩ :=
  (valQ_congr_sig _ _ _ _ (stepW₂_eq A himg c) _ _).trans (valQ_wit _ _ _ _ _ _ _ _ _)

/-- ⭐The value of a step's chain at the witnessed shape. -/
def stepW₅ : Σ a, Term σ (ctxOf (compsTys (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A) ++
    A.bcB false :: lt)) (RShape.wit (tupShape ModalSys.T rfl (A :: cl)) X).flat a :=
  ⟨_, Term.holeRead (Term.holeRead (stepW₃ (σ := σ) A himg c).2
    (ShapeMap.liftVal (σ := σ) (.wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
        (stepQ A ++ pairComps ((bcT cl).compsAllB ModalSys.T) []) (stepQ_ok cl A)) X)
      (ShapeMap.subC (σ := σ) (VarType.VTypeProd (bcT cl) (A.bcB false)) _
        ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T) (stepQ_ok cl A)
        (VarType.compOk_compsAllB _ rfl _) (stepQ_sub cl A))).2)
    (ShapeMap.liftVal (σ := σ) (.wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
        ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T)
        (VarType.compOk_compsAllB _ rfl _)) X)
      (tupCG (σ := σ) (bcT cl) A ModalSys.T rfl)).2⟩

/-- ⭐The chain at the witnessed shape is the plain chain, paired with the witness's content. -/
theorem stepW₅_eq : (⟨_, (stepW₅ A himg c).2⟩ : Σ a, Term σ (ctxOf (compsTys
    (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A) ++ A.bcB false :: lt))
    (RShape.wit (tupShape ModalSys.T rfl (A :: cl)) X).flat a) =
    ⟨_, Term.pair (stepV₅ (σ := σ) A himg).2
    (Term.mono (legQ_le _ (stepQ A))
      (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false) c))⟩ := by
  unfold stepW₅ stepV₅
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt,
    Term.holeRead_eq_holeAt]
  exact (Term.holeAt_congr_sig ((Term.holeAt_congr_sig (stepW₃_eq A himg c) _).trans
    (liftVal_wit_pair _ _ _)) _).trans (liftVal_wit_pair _ _ _)

end ChainValsW

/-! ## The chain of a step at a witnessed shape, along any leg -/

/-- The packing map of the chain at the witnessed shape. -/
abbrev packCCW (cl : List VarType) (A X : VarType) :=
  ShapeMap.liftObj (σ := σ) ((RShape.wit (tupShape ModalSys.T rfl cl) X).ext (A.bcB false))
    (ShapeMap.packCC (σ := σ) (bcT cl) (A.bcB false) _ [] (VarType.compOk_compsAllB _ rfl _)
      (Or.inl rfl))

/-- The source's root's tuple from its flat contents, at the witnessed shape. -/
abbrev flatBodyW {V : Ctx} [V.NoSlots] {cl : List VarType} (A X : VarType)
    (Φ : WFF σ (V.insert (.bnd 0) (RShape.wit (tupShape ModalSys.T rfl (A :: cl)) X).ty) 1) :
    WFF σ (V.insert (.bnd 0) (RShape.wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
      ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T)
      (VarType.compOk_compsAllB _ rfl _)) X).ty) 1 :=
  WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
    (ShapeMap.liftObj (σ := σ) (.wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
        ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T)
        (VarType.compOk_compsAllB _ rfl _)) X)
      (tupCG (σ := σ) (bcT cl) A ModalSys.T rfl)).2) Φ

variable (hS : ModalSys.BStrong = true)

/-- ⭐**The chain of a step at a witnessed shape, along any leg**: `chainB_consistent` with the
    witness's content `c` carried along. -/
theorem chainBW_consistent {lt cl : List VarType} {img : ℕ → ℕ} (A : VarType)
    (himg : ImgOk cl (ctxOf lt) img) (X : VarType) {xc : Ann X} (c : Term σ (ctxOf lt) X xc)
    (O : OutLeg (ctxOf lt)) {V₀ : Ctx} [V₀.NoSlots] (hV : V₀.Le O.view)
    (Φ : WFF σ (V₀.insert (.bnd 0) (RShape.wit (tupShape ModalSys.T rfl (A :: cl)) X).ty) 1)
    {M : Set (WFF σ (ctxOf lt) 0)} (hM : Theory.Consistent M)
    (hex : Theory.Derives M (O.retS hS (.wit (tupShape ModalSys.T rfl cl) X)
      (Term.pair (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2 c)
      (WFF.mono (hV.insert (.bnd 0) _) (WFF.ex (.VTypeBox (A.bcB false))
        (WFF.pairUpS (.wit (tupShape ModalSys.T rfl cl) X) (A.bcB false)
          (packCCW (σ := σ) cl A X).2 (flatBodyW A X Φ)))))) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] lt) '' M ∪
      {(O.mono (ctxOf_le_append [A.bc] lt)).retS hS
        (.wit (tupShape ModalSys.T rfl (A :: cl)) X)
        (Term.pair (tupCompsImg (A :: cl) (extImg img cl.length lt.length) (imgOk_ext himg) _
          (VarType.compOk_compsAllB _ rfl _)).2 (Term.mono (ctxOf_le_append [A.bc] lt) c))
        (WFF.mono ((hV.trans (O.le_view_mono (ctxOf_le_append [A.bc] lt))).insert (.bnd 0) _)
          Φ)}) := by
  have hu : (ctxOf lt).RootFresh (.free lt.length) := ctxOf_fresh le_rfl
  have hc₁ := retExtS_consistent hM hS O (.wit (tupShape ModalSys.T rfl cl) X) _
    (WFF.mono ((hV.insert (.bnd 0) _).insert (.bnd 1) _)
      (WFF.pairUpS (.wit (tupShape ModalSys.T rfl cl) X) (A.bcB false)
        (packCCW (σ := σ) cl A X).2 (flatBodyW A X Φ))) hex hu
  have hc₂ := consistent_step hc₁ (Proof.ret_map hS (O.mono (ctxOf_le_append [A.bcB false] lt))
    (S := (RShape.wit (tupShape ModalSys.T rfl cl) X).ext (A.bcB false))
    (ShapeMap.packCC (σ := σ) (bcT cl) (A.bcB false) _ [] (VarType.compOk_compsAllB _ rfl _)
      (Or.inl rfl)) (stepW₁ A himg c).2
    (WFF.mono ((O.le_view_mono (ctxOf_le_append [A.bcB false] lt)).insert (.bnd 0) _)
      (WFF.mono (hV.insert (.bnd 0) _) (flatBodyW A X Φ)))
    (Proof.conv (by
      refine OutLeg.retS_congr hS _ _ rfl ?_
      rw [WFF.bodySplit_mono_pairUpS hV,
        WFF.mono_bodyRepl (O.le_view_mono (ctxOf_le_append [A.bcB false] lt)), Term.mono_mono]
      try rw [WFF.mono_mono]
      try rfl) (Proof.lookup List.mem_cons_self)))
  have hc₃ := compsS_consistent_legW hS (tupShape ModalSys.T rfl cl) X
    (VarType.VTypeProd (bcT cl) (A.bcB false)) (pairComps ((bcT cl).compsAllB ModalSys.T) [])
    (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))
    (O.mono (ctxOf_le_append [A.bcB false] lt)) (stepW₂ A himg c).2
    (WFF.mono ((O.le_view_mono (ctxOf_le_append [A.bcB false] lt)).insert (.bnd 0) _)
      (WFF.mono (hV.insert (.bnd 0) _) (flatBodyW A X Φ))) hc₂
    (Theory.Derives.of_mem (Or.inr rfl)) (stepQ A) (stepQ_ok cl A)
  have hc₄ := consistent_step hc₃ (Proof.ret_map hS
    ((O.mono (ctxOf_le_append [A.bcB false] lt)).mono (legQ_le _ (stepQ A)))
    (S := .wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
      (stepQ A ++ pairComps ((bcT cl).compsAllB ModalSys.T) []) (stepQ_ok cl A)) X)
    (ShapeMap.subC (σ := σ) (VarType.VTypeProd (bcT cl) (A.bcB false)) _
      ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T) (stepQ_ok cl A)
      (VarType.compOk_compsAllB _ rfl _) (stepQ_sub cl A)) _ _
    (Proof.conv (OutLeg.retS_congr hS _ _ rfl
      (WFF.bodyRepl_liftObj_wit_subC (VarType.VTypeProd (bcT cl) (A.bcB false))
        (stepQ A ++ pairComps ((bcT cl).compsAllB ModalSys.T) [])
        ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T) (stepQ_ok cl A)
        (VarType.compOk_compsAllB _ rfl _) (stepQ_sub cl A) X _).symm)
      (Proof.lookup List.mem_cons_self)))
  have hle₂ : V₀.Le ((O.mono (ctxOf_le_append [A.bcB false] lt)).mono
      (legQ_le (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A))).view :=
    hV.trans ((O.le_view_mono _).trans ((O.mono _).le_view_mono _))
  have hc₅ := consistent_step hc₄ (Proof.ret_map hS
    ((O.mono (ctxOf_le_append [A.bcB false] lt)).mono (legQ_le _ (stepQ A)))
    (S := .wit (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
      ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T)
      (VarType.compOk_compsAllB _ rfl _)) X)
    (tupCG (σ := σ) (bcT cl) A ModalSys.T rfl) _
    (WFF.mono (hle₂.insert (.bnd 0) _) Φ)
    (Proof.conv (by
      refine OutLeg.retS_congr hS _ _ rfl ?_
      dsimp only [flatBodyW]
      rw [WFF.mono_mono, WFF.mono_mono, WFF.mono_bodyRepl, Term.mono_mono]
      exact hle₂) (Proof.lookup List.mem_cons_self)))
  refine consistent_of_subst hc₅ (Subst.single (.free lt.length) (.tm (stepARR A himg).2))
    (Subst.ok_single (stepLe lt cl A) rfl)
    (Subst.coh_single (ctxOf_fresh le_rfl) (stepLe lt cl A) rfl) Ctx.NoSlots.slots ?_
  rintro x (⟨y, hy, rfl⟩ | hx)
  · erw [subst_single_mono (stepLe lt cl A)]
    exact Or.inl (Or.inl (Or.inl ⟨_, Or.inl (Or.inl ⟨y, hy, rfl⟩), by rw [WFF.mono_mono]⟩))
  · rw [Set.mem_singleton_iff.mp hx]
    refine Or.inr (Set.mem_singleton_iff.mpr ?_)
    refine (subst_single_retS hS (stepLe lt cl A) O _ _
      (.wit (tupShape ModalSys.T rfl (A :: cl)) X) _ hV Φ).trans ?_
    have hval := (sig_pair (stepV₅_eq A himg)
      ((subst_single_mono_tm (stepLe lt cl A) (e := .tm (stepARR A himg).2)
        (Subst.ok_single (stepLe lt cl A) rfl)
        (Subst.coh_single (ctxOf_fresh le_rfl) (stepLe lt cl A) rfl)
        (ctxOf_le_append [A.bc] lt) c).trans
        (congrArg (Sigma.mk _) (Term.mono_mono _ _ c).symm))).trans (stepW₅_eq A himg c).symm
    clear hc₁ hc₂ hc₃ hc₄ hc₅ hex
    cases O with
    | nec => exact WFF.retS_congr hS _ hval rfl
    | pos y hy => exact WFF.retxS_congr hS y _ _ hval rfl

/-! ## The source's `∃`-introduction at a witnessed shape -/

omit [ModalSys.NoFour] in
/-- A map at a witnessed shape, on an object: the map on the necessary part, the possible part
    kept. -/
theorem liftObj_wit_pair {Γ : Ctx} {N T : NShape} {X : VarType} (F : ShapeMap σ N T)
    {a : Ann N.ty} {x : Ann (.VTypeDia X)} (v : Term σ Γ N.ty a) (e : Term σ Γ (.VTypeDia X) x) :
    (⟨_, Term.holeAt (Term.pair v e) (ShapeMap.liftObj (σ := σ) (.wit N X) F).2⟩ :
      Σ c, Term σ Γ ((RShape.wit N X).withNec T).ty c) =
      ⟨_, Term.pair (Term.holeAt v F.obj.2) e⟩ := by
  refine sig_pair ?_ (Term.holeAt_pair_snd _ _)
  exact (Term.holeAt_holeAt_sig _ _ _).trans (Term.holeAt_congr_sig (Term.holeAt_pair_fst _ _) _)

/-- `liftBodyW` is `liftBodyAt` at the pair of the roots' necessary object and the witness. -/
theorem liftBodyW_eq_liftBodyAt {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtxW cls clt X) 1) :
    liftBodyW hs himgt hx Φ = liftBodyAt himgt (Term.pair
      (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) cls).2))
      (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx))) Φ :=
  rfl

section FlatRootW

variable {lv cls clt : List VarType} {A : VarType} {x : VarSymb} {X : VarType}

/-- The middle term at the witnessed shape: the older roots' entry with a new slot `□(A's flat
    contents)` as companion, packed with companions. -/
def midTermWB (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (A : VarType) :
    Σ a, Term σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox (A.bcB false)))
      (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
        (pairComps ((bcT cls).compsAllB ModalSys.T) [])
        (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty a :=
  ⟨_, Term.holeAt
    (Term.pair
      (Term.pair
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)
          (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2)))
        (Term.eta (.root (.bnd 0)) (.VTypeBox (A.bcB false)) (Ctx.ref_insert_root _ (.bnd 0) _)))
      (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)
        (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx))))
    (packCCW (σ := σ) cls A X).2⟩

/-- The middle substitution at the witnessed shape. -/
abbrev midSWB (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (A : VarType)
    (imgt : ℕ → ℕ) : Subst σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox (A.bcB false))) :=
  ((arrowS σ (ctxOf lv) imgt).mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)).set
    (.bnd 0) (.tm (midTermWB hs hx A).2)

theorem ok_midSWB (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) :
    Subst.Ok ((ctxOf clt).boxIn.insert (.bnd 0)
      (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
        (pairComps ((bcT cls).compsAllB ModalSys.T) [])
        (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty)
      (midSWB (σ := σ) hs hx A imgt) :=
  Subst.ok_set (Subst.ok_mono (ok_arrowS himgt) _) rfl

theorem coh_midSWB (hs : cls <:+ lv) (hx : (ctxOf cls).ref x = some (.VTypeDia X))
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) :
    Subst.Coh (Subst.setIdx (arrowIdx imgt) (.bnd 0) (.tm (midTermWB (σ := σ) hs hx A).2))
      ((ctxOf clt).boxIn.insert (.bnd 0)
        (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
          (pairComps ((bcT cls).compsAllB ModalSys.T) [])
          (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty)
      (midSWB (σ := σ) hs hx A imgt) :=
  Subst.coh_set (Subst.ok_mono (ok_arrowS himgt) _) (Subst.coh_mono (coh_arrowS himgt) _)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl

/-- ⭐**A new component's witness body is an `∃`-introduction of the older roots' one**, at the
    witnessed shape, for any new component `□w`: packing with companions sends
    `⟨⟨□ā, □w⟩, x⟩` to `⟨□⟨ā, w⟩, x⟩`. -/
theorem liftBodyW_ex_pairUpS_memB {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {w₀ : Ann (A.bcB false)}
    (w : Term σ (ctxOf lv).boxIn (A.bcB false) w₀)
    (Ψ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0)
      (RShape.wit (.boxC (VarType.VTypeProd (bcT cls) (A.bcB false))
        (pairComps ((bcT cls).compsAllB ModalSys.T) [])
        (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))) X).ty) 1)
    (h : liftBodyAt himgt (Term.pair (Term.boxtm (Term.pair
      (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) cls).2) w))
      (Term.eta x (.VTypeDia X) ((ctxOf_le_of_suffix hs).ref hx))) Ψ ∈ M) :
    liftBodyW hs himgt hx (WFF.ex (.VTypeBox (A.bcB false))
      (WFF.pairUpS (.wit (tupShape ModalSys.T rfl cls) X) (A.bcB false)
        (packCCW (σ := σ) cls A X).2 Ψ)) ∈ M := by
  refine hM.closed ⟨[_], fun y hy => by rw [List.mem_singleton.mp hy]; exact h, ⟨?_⟩⟩
  refine Proof.ex_intro _ (Term.boxtm w) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  refine Eq.symm ?_
  unfold WFF.instantiate WFF.substRoot WFF.pairUpS
  have hfr : (ctxOf lv) (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := ctxOf lv)).root
  rw [WFF.subst_comp _ _ (midSWB hs hx A imgt) _ _ _ _ (ok_midSWB hs hx himgt)
    (coh_midSWB hs hx himgt) _ _ _ ?simA]
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
      rw [show midSWB (σ := σ) hs hx A imgt (.root (.bnd 0)) = .tm (midTermWB hs hx A).2 from
        Subst.set_root _ _ _, Subst.set_root]
      dsimp only [SubE.comp]
      have h0 : (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).under (0 + 1) 0
          (.VTypeBox (A.bcB false)) hfr).at (.root (.bnd 0)) =
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
    · obtain ⟨u, rfl, hu⟩ := body_itemT hv hvr
      dsimp only [Subst.comp]
      rw [show midSWB (σ := σ) hs hx A imgt (.step u .box) =
        SubE.mono _ (arrowS σ (ctxOf lv) imgt (.step u .box)) from Subst.set_ne _ _ hvr,
        Subst.set_ne _ _ hvr]
      dsimp only [Subst.idS, SubE.comp]
      rw [Subst.at_nonproj _ hlp]
      dsimp only [Subst.under]
      rw [if_neg (fun h => by cases h), Subst.set_ne _ _ hvr]
      exact .refl _
  unfold liftBodyAt
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
    rw [show midSWB (σ := σ) hs hx A imgt (.root (.bnd 0)) = .tm (midTermWB hs hx A).2 from
      Subst.set_root _ _ _, Subst.set_root]
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
  · obtain ⟨u, rfl, hu⟩ := body_itemT hv hvr
    obtain ⟨r, hr, _, _⟩ := ref_rt hu
    dsimp only [Subst.comp]
    rw [show midSWB (σ := σ) hs hx A imgt (.step u .box) =
      SubE.mono _ (arrowS σ (ctxOf lv) imgt (.step u .box)) from Subst.set_ne _ _ hvr,
      Subst.set_ne _ _ hvr]
    change SubE.Sim U (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
    rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
    exact .refl _

end FlatRootW

/-- ⭐**The source's `∃`-introduction for its root along a witness arrow, under T**: a witness
    body over the roots with `A`, true at the parent, gives `∃e. pairUpS (flatBodyW Φ)` over the
    older roots, witnessed by `A`'s flat object. -/
theorem liftBodyW_ex_flat_mem {lv cl clt : List VarType} {A : VarType} {x : VarSymb}
    {X : VarType} {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M) (hs' : (A :: cl) <:+ lv)
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X)) (Φ : WFF σ (bodyCtxW (A :: cl) clt X) 1)
    (h : liftBodyW hs' himgt (ref_old_of_ref hx) Φ ∈ M) :
    liftBodyW ((List.suffix_cons A cl).trans hs') himgt hx
      (WFF.ex (.VTypeBox (A.bcB false))
        (WFF.pairUpS (.wit (tupShape ModalSys.T rfl cl) X) (A.bcB false)
          (packCCW (σ := σ) cl A X).2 (flatBodyW A X Φ))) ∈ M := by
  have hr := (ctxOf_le_of_suffix hs').ref (ctxOf_ref_new A cl)
  refine liftBodyW_ex_pairUpS_memB hM ((List.suffix_cons A cl).trans hs') himgt hx
    (flatB (σ := σ) (.root (.free cl.length)) A hr).2 (flatBodyW A X Φ) ?_
  rw [liftBodyAt_bodyRepl]
  refine ((liftBodyAt_congr himgt ?_ Φ).trans (liftBodyW_eq_liftBodyAt hs' himgt _ Φ).symm) ▸ h
  exact (liftObj_wit_pair (tupCG (σ := σ) (bcT cl) A ModalSys.T rfl) _ _).trans
    (sig_pair ((holeAt_tupCG_obj (bcT cl) A _ _ hr _ rfl).trans (tupT_cons_mono hs').symm) rfl)

/-! ## The step along a witness arrow -/

section StepWB

variable {ts tt : NodeSt σ} {A : VarType} {cl clt : List VarType} {img imgt : ℕ → ℕ}
  {x : VarSymb} {X : VarType} {cx : ℕ}

/-- The returning possibility a witness body over the roots with `A` becomes in the grown child,
    with companions: valued at the images with companions and `cx`. -/
def retAtomWB (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (Φ : WFF σ (bodyCtxW (A :: cl) clt X) 1) : WFF σ (ctxOf (A.bc :: tt.l)) 0 :=
  WFF.retS hS (.wit (tupShape ModalSys.T rfl (A :: cl)) X)
    (Term.pair (tupCompsImg (A :: cl) (extImg img cl.length tt.l.length) (imgOk_ext himg) _
        (VarType.compOk_compsAllB _ rfl _)).2
      (Term.eta (.root (.free cx)) X ((ctxOf_le_append [A.bc] tt.l).ref hcx)))
    (WFF.mono ((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).boxIn.insert (.bnd 0) _) Φ)

/-- ⭐**One witness body's atom is consistent with the grown child**: the witnessed chain
    (`chainBW_consistent`) along the plain leg. -/
theorem retAtomWB_consistent (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Ψ : WFF σ (bodyCtxW cl clt X) 1,
      liftBodyW ((List.suffix_cons A cl).trans hs') himgt hx Ψ ∈ ts.M →
        WFF.retS hS (.wit (tupShape ModalSys.T rfl cl) X)
          (Term.pair (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2
            (Term.eta (.root (.free cx)) X hcx))
          (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Ψ) ∈ tt.M)
    (Φ : WFF σ (bodyCtxW (A :: cl) clt X) 1)
    (hΦ : liftBodyW hs' himgt (ref_old_of_ref hx) Φ ∈ ts.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
      {retAtomWB hS himg ht hcx Φ}) := by
  have hc := chainBW_consistent hS A himg X (Term.eta (.root (.free cx)) X hcx) .nec
    (ctxOf_le_of_suffix ht).boxIn Φ hw.1
    (Theory.Derives.of_mem (hinv _ (liftBodyW_ex_flat_mem hv hs' himgt hx Φ hΦ)))
  refine consistent_mono hc (Set.union_subset_union subset_rfl fun y hy => ?_)
  rw [Set.mem_singleton_iff.mp hy]
  exact Set.mem_singleton_iff.mpr (WFF.retS_congr hS _
    (sig_pair rfl (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _).symm)) rfl)

/-- What the child gains when the parent's root `A` is committed along a witness arrow, with
    companions. -/
def retSetWB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X) :
    Set (WFF σ (ctxOf (A.bc :: tt.l)) 0) :=
  {φ | ∃ Φ, liftBodyW hs' himgt (ref_old_of_ref hx) Φ ∈ ts.M ∧ φ = retAtomWB hS himg ht hcx Φ}

/-- Finitely many of the gained atoms reduce to one, at the conjunction of their bodies. -/
theorem ret_listWB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X) (hv : Theory.IsMCS ts.M)
    (S : Set (WFF σ (ctxOf (A.bc :: tt.l)) 0)) :
    ∀ L : List (WFF σ (ctxOf (A.bc :: tt.l)) 0),
      (∀ δ ∈ L, δ ∈ S ∨ δ ∈ retSetWB hS hs' himgt himg ht hx hcx) →
      ∃ Φ, liftBodyW hs' himgt (ref_old_of_ref hx) Φ ∈ ts.M ∧
        ∀ δ ∈ L, Theory.Derives (S ∪ {retAtomWB hS himg ht hcx Φ}) δ
  | [], _ => ⟨.top, hv.top_mem, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Φ₀, hΦ₀, hL⟩ := ret_listWB hs' himgt himg ht hx hcx hv S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := ctxOf_fresh (l := A.bc :: tt.l) le_rfl
      rcases h δ List.mem_cons_self with hS' | ⟨Φ₁, hΦ₁, rfl⟩
      · refine ⟨Φ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS')
        · exact hL d hd
      · have hand : ∀ Φ', Proof σ _ [retAtomWB hS himg ht hcx (Φ₀.and Φ₁)]
              (retAtomWB hS himg ht hcx Φ') →
            Theory.Derives (S ∪ {retAtomWB hS himg ht hcx (Φ₀.and Φ₁)})
              (retAtomWB hS himg ht hcx Φ') :=
          fun Φ' p => ⟨[_], fun y hy => by
            rw [List.mem_singleton.mp hy]; exact Or.inr rfl, ⟨p⟩⟩
        have h₀ := hand Φ₀ (Proof.ret_monoS hS .nec _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.box_all_and_left _ _ hu))
        have h₁ := hand Φ₁ (Proof.ret_monoS hS .nec _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.box_all_and_right _ _ hu))
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

/-- ⭐**The gained atoms along a witness arrow are consistent with the child.** -/
theorem retSetWB_consistent (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Ψ : WFF σ (bodyCtxW cl clt X) 1,
      liftBodyW ((List.suffix_cons A cl).trans hs') himgt hx Ψ ∈ ts.M →
        WFF.retS hS (.wit (tupShape ModalSys.T rfl cl) X)
          (Term.pair (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2
            (Term.eta (.root (.free cx)) X hcx))
          (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Ψ) ∈ tt.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
      retSetWB hS hs' himgt himg ht hx hcx) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨Φ, hΦ, hder⟩ := ret_listWB hS hs' himgt himg ht hx hcx hv _ L hL
  exact retAtomWB_consistent hS hs' himgt himg ht hx hcx hv hw hinv Φ hΦ
    (Derives.trans (fun y hy => hder y hy) ⟨L, fun y hy => hy, p⟩)

/-- The child grown by the image of the parent's root `A` along a witness arrow, with
    companions. -/
noncomputable def retStepWB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X) : NodeSt σ :=
  ⟨A.bc :: tt.l, complete (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
    retSetWB hS hs' himgt himg ht hx hcx)⟩

/-- ⭐**One realisation step along a witness arrow, with companions**: the grown child is
    maximal consistent, extends the old one, and the forward invariant holds for one more root. -/
theorem retStepWB_ok (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvWB hS ModalSys.T rfl ts tt cl img clt imgt x X cx) :
    Theory.IsMCS (retStepWB hS hs' himgt himg ht hx hcx).M ∧
      Grows tt (retStepWB hS hs' himgt himg ht hx hcx) ∧
      RetInvWB hS ModalSys.T rfl ts (retStepWB hS hs' himgt himg ht hx hcx) (A :: cl)
        (extImg img cl.length tt.l.length) clt imgt x X cx := by
  obtain ⟨_, _, _, _, _, _, h⟩ := hinv
  have hcons := retSetWB_consistent hS hs' himgt himg ht hx hcx hv hw h
  obtain ⟨hsub, hmcs⟩ := complete_spec hcons
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩,
    hs', imgOk_ext himg, ht.trans (List.suffix_cons _ _), himgt, ref_old_of_ref hx,
    (ctxOf_le_append [A.bc] tt.l).ref hcx, fun Φ hΦ => ?_⟩
  exact hsub (Or.inr ⟨Φ, hΦ, rfl⟩)

end StepWB

/-! ## The reverse arrow along `x` under T: cross-arrow preservation along a witness arrow -/

/-- A body packed along `x` into a hole formula over the roots' tuple **with companions**, `x`'s
    content and a slot: `pack2X`, the tuple read off its value with companions. -/
noncomputable def packC2X (cls : List VarType) (co : List (List Step)) {x : VarSymb}
    {X : VarType} (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (U : VarType)
    (Φ : WFF σ (((ctxOf cls).diaIn x).insert (.bnd 0) U) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd ((bcT cls).compsFlat co) X) U)) 1 :=
  WFF.holeAt (Ctx.slotsFrom_empty.insert _)
    (Term.pair
      (Term.pair
        (Term.eta ((VarSymb.step (.step (.root (.bnd 0)) .fst) .fst).ext (compsFst co)) (bcT cls)
          (Ctx.ref_compsFst co (Ctx.ref_fst_of (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))))
        (Term.eta (.step (.step (.root (.bnd 0)) .fst) .snd) X
          (Ctx.ref_snd_of (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _)))))
      (Term.eta (.step (.root (.bnd 0)) .snd) U (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
    (pack2X U hx Φ)

/-- `packC2X` read at a pair is `pack2X` read with the first component's own value. -/
theorem WFF.holeAt_packC2X {Γ : Ctx} {d : ℕ} (hΓ : Γ.SlotsFrom d) {cls : List VarType}
    {co : List (List Step)} {x : VarSymb} {X U : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {p : Ann ((bcT cls).compsFlat co)}
    (P : Term σ Γ ((bcT cls).compsFlat co) p) {e : Ann X} (E : Term σ Γ X e) {q : Ann U}
    (Q : Term σ Γ U q) {p' : Ann (bcT cls)} {P' : Term σ Γ (bcT cls) p'}
    (hP : P.getP (compsFst co) = some ⟨_, p', P'⟩)
    (Φ : WFF σ (((ctxOf cls).diaIn x).insert (.bnd 0) U) 1) :
    WFF.holeAt hΓ (Term.pair (Term.pair P E) Q) (packC2X cls co hx U Φ) =
      WFF.holeAt hΓ (Term.pair (Term.pair P' E) Q) (pack2X U hx Φ) := by
  unfold packC2X
  refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _ (sig_pair (sig_pair ?_
    (Term.holeAt_pair_fst_snd _ _ _)) (Term.holeAt_pair_snd _ _)) _)
  refine sig_of_some ((getP_nil _).symm.trans ((getP_holeAt_eta _ (.fst :: .fst :: compsFst co)
    (FS_cons (Or.inl rfl) (FS_cons (Or.inl rfl) (FS_compsFst _))) rfl _ []).trans ?_))
  rw [List.append_nil]
  exact (getP_pair_fst _ _ _).trans ((getP_pair_fst _ _ _).trans hP)

/-- `packC2X` read at the images' tuple with companions: `pack2X` read at the images' tuple. -/
theorem holeRead_packC2X {cls : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk cls Δ img) (co : List (List Step)) (hco : (bcT cls).CompOk co) {x : VarSymb}
    {X U : VarType} (hx : (ctxOf cls).ref x = some (.VTypeDia X)) {e : Ann X}
    (E : Term σ Δ X e) {q : Ann U} (Q : Term σ Δ U q)
    (Φ : WFF σ (((ctxOf cls).diaIn x).insert (.bnd 0) U) 1) :
    WFF.holeRead (Term.pair (Term.pair (tupCompsImg cls img himg co hco).2 E) Q)
        (packC2X cls co hx U Φ) =
      WFF.holeRead (Term.pair (Term.pair (tupImgT cls img himg).2 E) Q) (pack2X U hx Φ) := by
  rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt]
  exact WFF.holeAt_packC2X _ hx _ _ _ (tupCompsImg_read_fst _ _ _ _ _) Φ

omit [ModalSys.NoFour] in
/-- Weakening the companion unit's conjunct along a possible part weakens its object. -/
theorem WFF.mono_unitBodyDC {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {C X A : VarType} (co : List (List Step)) (ho : C.CompOk co)
    {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0)
      (.VTypeProd (.VTypeProd (C.compsFlat co) X) (.VTypeBox A))) 1) :
    WFF.mono (h.boxIn.insert (.bnd 0) (RShape.wit (.box C) X).ty)
        (WFF.unitBodyDC hS co ho sb cs hcs θ) =
      WFF.unitBodyDC hS co ho (Term.mono h.boxIn sb) cs hcs θ := by
  unfold WFF.unitBodyDC
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · rw [mono_compsVal h sb cs hcs]
    change (⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩ : Σ c, _) =
      ⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩
    rw [Term.mono_mono, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _
      ((((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).insert _).diaIn _).insert _)]
    exact WFF.holeAt_congr _ (sig_pair (sig_pair ((mono_compsSlot _ _ _ co ho).trans
      (compsSlot_home _ _ _ _ co ho)) (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)))
      (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))) θ

/-- ⭐The companion unit's conjunct along the possible part, at the reverse arrow's items and a
    body packed along `x` by `packC2X`, read at the parent: the reverse arrow's returning
    possibility along `x` with companions. -/
theorem liftBodyW_unitBodyDC {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {x : VarSymb} {X : VarType}
    (hx : (ctxOf cls).ref x = some (.VTypeDia X)) (hS : ModalSys.BStrong = true)
    (co : List (List Step)) (hco : (bcT cls).CompOk co) (cs : List (List Step))
    (hcs : (bcT clt).CompOk cs)
    (Φ : WFF σ (((ctxOf cls).diaIn x).insert (.bnd 0) (.VTypeBox (bcT clt))) 1) :
    liftBodyW hs himgt hx (WFF.unitBodyDC (Γ := ctxOf clt) hS co hco (tupT clt).2 cs hcs
        (packC2X cls co hx _ Φ)) =
      (OutLeg.pos x ⟨X, (ctxOf_le_of_suffix hs).ref hx⟩ : OutLeg (ctxOf lv)).retS hS
        (.nec (.boxC (bcT clt) cs hcs)) (tupCompsImg clt imgt himgt cs hcs).2
        (WFF.mono (((ctxOf_le_of_suffix hs).diaIn x).insert (.bnd 0) _) Φ) := by
  have hle := ctxOf_le_of_suffix hs
  have hu := Ctx.ref_insert_root (ctxOf clt).boxIn (.bnd 0)
    (RShape.wit (.box (bcT cls)) X).ty
  have hsnd := Ctx.ref_snd_of hu
  have hθ : Subst.Ok (bodyCtxW cls clt X)
      ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.ok_set (ok_arrowS himgt) rfl
  have hc : Subst.Coh (Subst.setIdx (arrowIdx imgt) (.bnd 0) (liftEntryW hs hx))
      (bodyCtxW cls clt X) ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)) :=
    Subst.coh_set (ok_arrowS himgt) (coh_arrowS himgt)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl
  have hw : (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .snd)).idxAlong [] = x := rfl
  have hfst : ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntryW hs hx)).at
      (.step (.root (.bnd 0)) .fst) =
      .tm (Term.boxtm (Term.mono hle.boxIn (tupT cls).2)) := by
    rw [Subst.at_proj _ _ rfl]
    change (Subst.set _ _ _ (.root (.bnd 0))).proj .fst = _
    rw [Subst.set_root]
    rfl
  unfold liftBodyW WFF.unitBodyDC
  rw [WFF.subst_retxS_at _ _ _ _ _ _ _ _ _ _ _ x rfl ⟨X, hle.ref hx⟩
    ((Ctx.NoSlots.slots (Γ := ctxOf lv)).diaIn x) (Subst.ok_dia hθ ⟨X, hsnd⟩ hw)
    (Subst.coh_dia hθ hc ⟨X, hsnd⟩)]
  refine WFF.retxS_congr hS _ _ _ ?_ ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf lv) imgt) _ (ok_arrowS himgt) _
      (coh_arrowS himgt) ?_ _).trans (subst_arrow_compsVal clt himgt cs hcs)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_packC2X _ hx _ _ _ (P' := Term.mono
      (((Ctx.le_boxIn_diaIn _ x).trans (hle.diaIn x)).trans
        (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)) (tupT cls).2)
      ((getP_subst _ _ _ _ _ (compsSlot_read_fst _ _ _ _)).trans (some_of_sig ?_)) Φ).trans ?_
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).diaIn x)).root _)
          (Term.mono (Ctx.le_boxIn_diaIn _ x) (Term.mono hle.boxIn (tupT cls).2))) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.dia_eq_box_mono (Δ₁ := (ctxOf clt).boxIn.insert (.bnd 0) _) _ _ x _ _
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

/-- ⭐**Cross-arrow preservation along a witness arrow, under T**: committing the parent's root
    `A` along the forward witness arrow keeps the way home's invariant along `x` with companions,
    over the extended list (`ret_unitDC`, as `retStepW_rev`). -/
theorem retStepWB_rev {ts tt : NodeSt σ} {A : VarType} {cl clt : List VarType}
    {img imgt : ℕ → ℕ} {x : VarSymb} {X : VarType} {cx : ℕ}
    (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvWB hS ModalSys.T rfl ts tt cl img clt imgt x X cx) :
    RetInvXB hS ModalSys.T rfl (retStepWB hS hs' himgt himg ht hx hcx) ts clt imgt (A :: cl)
      (extImg img cl.length tt.l.length) x X cx := by
  obtain ⟨_, _, _, _, _, _, h⟩ := hinv
  obtain ⟨hsub, hmcs⟩ :=
    complete_spec (retSetWB_consistent hS hs' himgt himg ht hx hcx hv hw h)
  have ht' : clt <:+ A.bc :: tt.l := ht.trans (List.suffix_cons _ _)
  have hx' : (ctxOf (A :: cl)).ref x = some (.VTypeDia X) := ref_old_of_ref hx
  have hcx' := (ctxOf_le_append [A.bc] tt.l).ref hcx
  refine ⟨ht', himgt, hs', imgOk_ext himg, hx', hcx', fun Φ hΦ => ?_⟩
  by_contra hn
  have hneg := hv.neg_mem_iff.mpr hn
  have hΨ : liftBodyW hs' himgt hx' (WFF.neg (WFF.unitBodyDC (Γ := ctxOf clt) hS
      ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
      ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
      (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ))) ∈ ts.M := by
    change WFF.neg (liftBodyW hs' himgt hx' _) ∈ ts.M
    rw [liftBodyW_unitBodyDC]
    exact hneg
  have hret := hsub (Or.inr ⟨_, hΨ, rfl⟩)
  have p₁ : Proof σ (ctxOf (A.bc :: tt.l))
      [retAtomWB hS himg ht hcx (WFF.neg (WFF.unitBodyDC (Γ := ctxOf clt) hS
        ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
        ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
        (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ)))]
      (WFF.retS hS (.wit (tupShape ModalSys.T rfl (A :: cl)) X)
        (Term.pair (tupCompsImg (A :: cl) (extImg img cl.length tt.l.length) (imgOk_ext himg) _
            (VarType.compOk_compsAllB _ rfl _)).2 (Term.eta (.root (.free cx)) X hcx'))
        (WFF.neg (WFF.unitBodyDC hS ((bcT (A :: cl)).compsAllB ModalSys.T)
          (VarType.compOk_compsAllB _ rfl _)
          (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2)
          ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
          (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    unfold retAtomWB
    refine congrArg (WFF.retS hS _ _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyDC (ctxOf_le_of_suffix ht')]
  have p₂ : Proof σ (ctxOf (A.bc :: tt.l)) [liftBodyX ht' (imgOk_ext himg) hx' hcx' Φ]
      (WFF.holeRead (Term.pair (Term.pair (tupCompsImg (A :: cl)
          (extImg img cl.length tt.l.length) (imgOk_ext himg) _
          (VarType.compOk_compsAllB _ rfl _)).2 (Term.eta (.root (.free cx)) X hcx'))
        (Term.boxtm (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2)))
        (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ)) :=
    Proof.conv ((holeRead_packC2X (imgOk_ext himg) _ _ hx' _ _ Φ).trans
      (holeRead_tupImgT_pack2X (imgOk_ext himg) hx' hcx' _ Φ)).symm
      (Proof.lookup List.mem_cons_self)
  have p₃ : Proof σ (ctxOf (A.bc :: tt.l))
      [retAtomWB hS himg ht hcx (WFF.neg (WFF.unitBodyDC (Γ := ctxOf clt) hS
        ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
        ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
        (packC2X (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) hx' _ Φ))),
        liftBodyX ht' (imgOk_ext himg) hx' hcx' Φ] .bot :=
    Proof.ret_absurdS hS _ _ _ (ctxOf_fresh (l := A.bc :: tt.l) le_rfl)
      (Proof.ret_unitDC hS .nec ((bcT (A :: cl)).compsAllB ModalSys.T)
        (VarType.compOk_compsAllB _ rfl _) _ _
        (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2) ((bcT clt).compsAllB ModalSys.T)
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
